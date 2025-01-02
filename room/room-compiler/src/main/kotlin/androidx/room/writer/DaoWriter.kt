/*
 * Copyright (C) 2016 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package androidx.room.writer

import androidx.room.compiler.codegen.CodeLanguage
import androidx.room.compiler.codegen.VisibilityModifier
import androidx.room.compiler.codegen.XClassName
import androidx.room.compiler.codegen.XCodeBlock
import androidx.room.compiler.codegen.XFunSpec
import androidx.room.compiler.codegen.XFunSpec.Builder.Companion.applyTo
import androidx.room.compiler.codegen.XPropertySpec
import androidx.room.compiler.codegen.XTypeName
import androidx.room.compiler.codegen.XTypeSpec
import androidx.room.compiler.codegen.XTypeSpec.Builder.Companion.applyTo
import androidx.room.compiler.codegen.buildCodeBlock
import androidx.room.compiler.codegen.compat.XConverters.applyToJavaPoet
import androidx.room.compiler.codegen.compat.XConverters.applyToKotlinPoet
import androidx.room.compiler.processing.PropertySpecHelper
import androidx.room.compiler.processing.XElement
import androidx.room.compiler.processing.XMethodElement
import androidx.room.compiler.processing.XProcessingEnv
import androidx.room.compiler.processing.XType
import androidx.room.ext.CommonTypeNames
import androidx.room.ext.RoomMemberNames
import androidx.room.ext.RoomTypeNames.DELETE_OR_UPDATE_ADAPTER
import androidx.room.ext.RoomTypeNames.INSERT_ADAPTER
import androidx.room.ext.RoomTypeNames.RAW_QUERY
import androidx.room.ext.RoomTypeNames.ROOM_DB
import androidx.room.ext.RoomTypeNames.ROOM_SQL_QUERY
import androidx.room.ext.RoomTypeNames.UPSERT_ADAPTER
import androidx.room.ext.capitalize
import androidx.room.processor.OnConflictProcessor
import androidx.room.solver.CodeGenScope
import androidx.room.solver.KotlinBoxedPrimitiveMethodDelegateBinder
import androidx.room.solver.KotlinDefaultMethodDelegateBinder
import androidx.room.solver.types.getRequiredTypeConverters
import androidx.room.vo.Dao
import androidx.room.vo.DeleteOrUpdateShortcutMethod
import androidx.room.vo.InsertMethod
import androidx.room.vo.KotlinBoxedPrimitiveMethodDelegate
import androidx.room.vo.KotlinDefaultMethodDelegate
import androidx.room.vo.RawQueryMethod
import androidx.room.vo.ReadQueryMethod
import androidx.room.vo.ShortcutEntity
import androidx.room.vo.TransactionMethod
import androidx.room.vo.UpdateMethod
import androidx.room.vo.UpsertMethod
import androidx.room.vo.WriteQueryMethod
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.KModifier
import com.squareup.kotlinpoet.jvm.jvmName
import java.util.Locale

/** Creates the implementation for a class annotated with Dao. */
class DaoWriter(
    val dao: Dao,
    private val dbElement: XElement,
    writerContext: WriterContext,
) : TypeWriter(writerContext) {
    private val declaredDao = dao.element.type
    private val className = dao.implTypeName
    override val packageName = className.packageName

    // TODO nothing prevents this from conflicting, we should fix.
    private val dbProperty: XPropertySpec =
        XPropertySpec.builder(DB_PROPERTY_NAME, ROOM_DB, VisibilityModifier.PRIVATE).build()

    private val companionTypeBuilder = lazy { XTypeSpec.companionObjectBuilder() }

    companion object {
        const val GET_LIST_OF_TYPE_CONVERTERS_METHOD = "getRequiredConverters"

        const val DB_PROPERTY_NAME = "__db"

        private fun shortcutEntityFieldNamePart(shortcutEntity: ShortcutEntity): String {
            fun typeNameToFieldName(typeName: XClassName): String {
                return typeName.simpleNames.last()
            }
            return if (shortcutEntity.isPartialEntity) {
                typeNameToFieldName(shortcutEntity.dataClass.className) +
                    "As" +
                    typeNameToFieldName(shortcutEntity.entityClassName)
            } else {
                typeNameToFieldName(shortcutEntity.entityClassName)
            }
        }
    }

    override fun createTypeSpecBuilder(): XTypeSpec.Builder {
        val builder = XTypeSpec.classBuilder(className)

        val preparedQueries = dao.queryMethods.filterIsInstance<WriteQueryMethod>()

        val shortcutMethods = buildList {
            addAll(createInsertMethods())
            addAll(createDeleteMethods())
            addAll(createUpdateMethods())
            addAll(createTransactionMethods())
            addAll(createUpsertMethods())
        }

        builder.apply {
            addOriginatingElement(dbElement)
            setVisibility(
                if (dao.element.isInternal()) {
                    VisibilityModifier.INTERNAL
                } else {
                    VisibilityModifier.PUBLIC
                }
            )
            if (dao.element.isInterface()) {
                addSuperinterface(dao.typeName)
            } else {
                superclass(dao.typeName)
            }
            addProperty(dbProperty)

            setPrimaryConstructor(
                createConstructor(shortcutMethods, dao.constructorParamType != null)
            )

            shortcutMethods.forEach { addFunction(it.functionImpl) }
            dao.queryMethods.filterIsInstance<ReadQueryMethod>().forEach { method ->
                addFunction(createSelectMethod(method))
                if (method.isProperty) {
                    // DAO function is a getter from a Kotlin property, generate property override.
                    applyToKotlinPoet {
                        addProperty(
                            PropertySpecHelper.overriding(method.element, declaredDao)
                                .getter(
                                    FunSpec.getterBuilder()
                                        .addCode("return %L()", method.element.name)
                                        .build()
                                )
                                .build()
                        )
                    }
                }
            }
            preparedQueries.forEach { addFunction(createPreparedQueryMethod(it)) }
            dao.rawQueryMethods.forEach { addFunction(createRawQueryMethod(it)) }
            applyTo(CodeLanguage.JAVA) {
                dao.kotlinDefaultMethodDelegates.forEach {
                    addFunction(createDefaultImplMethodDelegate(it))
                }
                dao.kotlinBoxedPrimitiveMethodDelegates.forEach {
                    addFunction(createBoxedPrimitiveBridgeMethodDelegate(it))
                }
            }
            // Keep this the last one to be generated because used custom converters will
            // register fields with a payload which we collect in dao to report used
            // Type Converters.
            addConverterListMethod(this)
            applyTo(CodeLanguage.KOTLIN) {
                if (companionTypeBuilder.isInitialized()) {
                    addType(companionTypeBuilder.value.build())
                }
            }
        }
        return builder
    }

    private fun addConverterListMethod(typeSpecBuilder: XTypeSpec.Builder) {
        // For Java a static method is created
        typeSpecBuilder.applyTo(CodeLanguage.JAVA) { addFunction(createConverterListMethod()) }
        // For Kotlin a function in the companion object is created
        companionTypeBuilder.value.applyTo(CodeLanguage.KOTLIN) {
            addFunction(createConverterListMethod())
        }
    }

    private fun createConverterListMethod(): XFunSpec {
        val body = buildCodeBlock { language ->
            val requiredTypeConverters = getRequiredTypeConverters()
            if (requiredTypeConverters.isEmpty()) {
                when (language) {
                    CodeLanguage.JAVA ->
                        addStatement("return %T.emptyList()", CommonTypeNames.COLLECTIONS)
                    CodeLanguage.KOTLIN -> addStatement("return emptyList()")
                }
            } else {
                val placeholders = requiredTypeConverters.joinToString(",") { "%L" }
                val requiredTypeConvertersLiterals =
                    requiredTypeConverters
                        .map {
                            when (language) {
                                CodeLanguage.JAVA -> XCodeBlock.ofJavaClassLiteral(it)
                                CodeLanguage.KOTLIN -> XCodeBlock.ofKotlinClassLiteral(it)
                            }
                        }
                        .toTypedArray()
                when (language) {
                    CodeLanguage.JAVA ->
                        addStatement(
                            "return %T.asList($placeholders)",
                            CommonTypeNames.ARRAYS,
                            *requiredTypeConvertersLiterals
                        )
                    CodeLanguage.KOTLIN ->
                        addStatement(
                            "return listOf($placeholders)",
                            *requiredTypeConvertersLiterals
                        )
                }
            }
        }
        return XFunSpec.builder(GET_LIST_OF_TYPE_CONVERTERS_METHOD, VisibilityModifier.PUBLIC)
            .applyToJavaPoet { addModifiers(javax.lang.model.element.Modifier.STATIC) }
            .applyTo { language ->
                returns(
                    CommonTypeNames.LIST.parametrizedBy(
                        when (language) {
                            CodeLanguage.JAVA -> CommonTypeNames.JAVA_CLASS
                            CodeLanguage.KOTLIN -> CommonTypeNames.KOTLIN_CLASS
                        }.parametrizedBy(XTypeName.ANY_WILDCARD)
                    )
                )
            }
            .addCode(body)
            .build()
    }

    private fun createTransactionMethods(): List<PreparedStmtQuery> {
        return dao.transactionMethods.map {
            PreparedStmtQuery(emptyMap(), createTransactionMethodBody(it))
        }
    }

    private fun createTransactionMethodBody(method: TransactionMethod): XFunSpec {
        val scope = CodeGenScope(this)
        method.methodBinder.executeAndReturn(
            parameterNames = method.parameterNames,
            daoName = dao.typeName,
            daoImplName = dao.implTypeName,
            dbProperty = dbProperty,
            scope = scope
        )
        return overrideWithoutAnnotations(method.element, declaredDao)
            .addCode(scope.generate())
            .build()
    }

    private fun createConstructor(
        shortcutMethods: List<PreparedStmtQuery>,
        callSuper: Boolean
    ): XFunSpec {
        val body = buildCodeBlock {
            addStatement("this.%N = %L", dbProperty, dbProperty.name)
            shortcutMethods
                .asSequence()
                .filterNot { it.fields.isEmpty() }
                .map { it.fields.values }
                .flatten()
                .groupBy { it.first.name }
                .map { it.value.first() }
                .forEach { (propertySpec, initExpression) ->
                    addStatement("this.%L = %L", propertySpec.name, initExpression)
                }
        }
        return XFunSpec.constructorBuilder(VisibilityModifier.PUBLIC)
            .apply {
                addParameter(typeName = dao.constructorParamType ?: ROOM_DB, name = dbProperty.name)
                if (callSuper) {
                    callSuperConstructor(XCodeBlock.of("%L", dbProperty.name))
                }
                addCode(body)
            }
            .build()
    }

    private fun createSelectMethod(method: ReadQueryMethod): XFunSpec {
        return overrideWithoutAnnotations(method.element, declaredDao)
            .applyToKotlinPoet {
                // TODO: Update XPoet to better handle this case.
                if (method.isProperty) {
                    // When the DAO function is from a Kotlin property, we'll still generate
                    // a DAO function, but it won't be an override and it'll be private, to be
                    // called from the overridden property's getter.
                    modifiers.remove(KModifier.OVERRIDE)
                    modifiers.removeAll(
                        listOf(KModifier.PUBLIC, KModifier.INTERNAL, KModifier.PROTECTED)
                    )
                    addModifiers(KModifier.PRIVATE)

                    // For JVM emit a @JvmName to avoid same-signature conflict with
                    // actual property.
                    if (
                        context.targetPlatforms.size == 1 &&
                            context.targetPlatforms.contains(XProcessingEnv.Platform.JVM)
                    ) {
                        jvmName("_private${method.element.name.capitalize(Locale.US)}")
                    }
                }
            }
            .addCode(createQueryMethodBody(method))
            .build()
    }

    private fun createRawQueryMethod(method: RawQueryMethod): XFunSpec {
        return overrideWithoutAnnotations(method.element, declaredDao)
            .addCode(
                if (
                    method.runtimeQueryParam == null ||
                        method.queryResultBinder.usesCompatQueryWriter
                ) {
                    compatCreateRawQueryMethodBody(method)
                } else {
                    createRawQueryMethodBody(method)
                }
            )
            .build()
    }

    private fun createRawQueryMethodBody(method: RawQueryMethod): XCodeBlock {
        val scope = CodeGenScope(this@DaoWriter)
        val sqlQueryVar = scope.getTmpVar("_sql")
        val rawQueryParamName =
            if (method.runtimeQueryParam!!.isSupportQuery()) {
                val rawQueryVar = scope.getTmpVar("_rawQuery")
                scope.builder.addLocalVariable(
                    name = rawQueryVar,
                    typeName = RAW_QUERY,
                    assignExpr =
                        XCodeBlock.of(
                            format = "%T.copyFrom(%L).toRoomRawQuery()",
                            ROOM_SQL_QUERY,
                            method.runtimeQueryParam.paramName
                        )
                )
                rawQueryVar
            } else {
                method.runtimeQueryParam.paramName
            }

        scope.builder.addLocalVal(
            sqlQueryVar,
            CommonTypeNames.STRING,
            "%L.%L",
            rawQueryParamName,
            XCodeBlock.ofString(java = "getSql()", kotlin = "sql")
        )

        if (method.returnsValue) {
            method.queryResultBinder.convertAndReturn(
                sqlQueryVar = sqlQueryVar,
                dbProperty = dbProperty,
                bindStatement = { stmtVar ->
                    this.builder.addStatement(
                        "%L.getBindingFunction().invoke(%L)",
                        rawQueryParamName,
                        stmtVar
                    )
                },
                returnTypeName = method.returnType.asTypeName(),
                inTransaction = method.inTransaction,
                scope = scope
            )
        }
        return scope.generate()
    }

    /** Used by the Non-KMP Paging3 binders and the Paging2 binders. */
    private fun compatCreateRawQueryMethodBody(method: RawQueryMethod): XCodeBlock =
        XCodeBlock.builder()
            .apply {
                val scope = CodeGenScope(this@DaoWriter)
                val roomSQLiteQueryVar: String
                val queryParam = method.runtimeQueryParam
                if (queryParam?.isSupportQuery() == true) {
                    queryParam.paramName
                } else if (queryParam?.isString() == true) {
                    roomSQLiteQueryVar = scope.getTmpVar("_statement")
                    addLocalVariable(
                        name = roomSQLiteQueryVar,
                        typeName = ROOM_SQL_QUERY,
                        assignExpr =
                            XCodeBlock.of(
                                "%M(%L, 0)",
                                RoomMemberNames.ROOM_SQL_QUERY_ACQUIRE,
                                queryParam.paramName
                            ),
                    )
                } else {
                    // try to generate compiling code. we would've already reported this error
                    roomSQLiteQueryVar = scope.getTmpVar("_statement")
                    addLocalVariable(
                        name = roomSQLiteQueryVar,
                        typeName = ROOM_SQL_QUERY,
                        assignExpr =
                            XCodeBlock.of(
                                "%M(%S, 0)",
                                RoomMemberNames.ROOM_SQL_QUERY_ACQUIRE,
                                "missing query parameter"
                            ),
                    )
                }
                val rawQueryParamName = method.runtimeQueryParam?.paramName
                if (rawQueryParamName != null) {
                    if (method.returnsValue) {
                        method.queryResultBinder.convertAndReturn(
                            sqlQueryVar = rawQueryParamName,
                            dbProperty = dbProperty,
                            bindStatement = { stmtVar ->
                                this.builder.addStatement(
                                    "%L.getBindingFunction().invoke(%L)",
                                    rawQueryParamName,
                                    stmtVar
                                )
                            },
                            returnTypeName = method.returnType.asTypeName(),
                            inTransaction = method.inTransaction,
                            scope = scope
                        )
                    }
                }
                add(scope.generate())
            }
            .build()

    private fun createPreparedQueryMethod(method: WriteQueryMethod): XFunSpec {
        return overrideWithoutAnnotations(method.element, declaredDao)
            .addCode(createPreparedQueryMethodBody(method))
            .build()
    }

    /**
     * Groups all insert methods based on the insert statement they will use then creates all field
     * specs, EntityInsertAdapterWriter and actual insert methods.
     */
    private fun createInsertMethods(): List<PreparedStmtQuery> {
        return dao.insertMethods.map { insertMethod ->
            val onConflict = OnConflictProcessor.onConflictText(insertMethod.onConflict)
            val entities = insertMethod.entities

            val fields =
                entities.mapValues {
                    val spec = getOrCreateProperty(InsertMethodProperty(it.value, onConflict))
                    val impl =
                        EntityInsertAdapterWriter.create(it.value, onConflict)
                            .createAnonymous(this@DaoWriter)
                    spec to impl
                }
            val methodImpl =
                overrideWithoutAnnotations(insertMethod.element, declaredDao)
                    .apply { addCode(createInsertMethodBody(insertMethod, fields)) }
                    .build()
            PreparedStmtQuery(fields, methodImpl)
        }
    }

    private fun createInsertMethodBody(
        method: InsertMethod,
        insertAdapters: Map<String, Pair<XPropertySpec, XTypeSpec>>
    ): XCodeBlock {
        if (insertAdapters.isEmpty() || method.methodBinder == null) {
            return XCodeBlock.builder().build()
        }
        val scope = CodeGenScope(writer = this)
        ShortcutQueryParameterWriter.addNullCheckValidation(scope, method.parameters)
        method.methodBinder.convertAndReturn(
            parameters = method.parameters,
            adapters = insertAdapters,
            dbProperty = dbProperty,
            scope = scope
        )
        return scope.generate()
    }

    /** Creates EntityUpdateAdapter for each delete method. */
    private fun createDeleteMethods(): List<PreparedStmtQuery> {
        return createShortcutMethods(dao.deleteMethods, "delete") { _, entity ->
            EntityDeleteAdapterWriter.create(entity).createAnonymous(this@DaoWriter)
        }
    }

    /** Creates EntityUpdateAdapter for each @Update method. */
    private fun createUpdateMethods(): List<PreparedStmtQuery> {
        return createShortcutMethods(dao.updateMethods, "update") { update, entity ->
            val onConflict = OnConflictProcessor.onConflictText(update.onConflictStrategy)
            EntityUpdateAdapterWriter.create(entity, onConflict).createAnonymous(this@DaoWriter)
        }
    }

    private fun <T : DeleteOrUpdateShortcutMethod> createShortcutMethods(
        methods: List<T>,
        methodPrefix: String,
        implCallback: (T, ShortcutEntity) -> XTypeSpec
    ): List<PreparedStmtQuery> {
        return methods.mapNotNull { method ->
            val entities = method.entities
            if (entities.isEmpty()) {
                null
            } else {
                val onConflict =
                    if (method is UpdateMethod) {
                        OnConflictProcessor.onConflictText(method.onConflictStrategy)
                    } else {
                        ""
                    }
                val fields =
                    entities.mapValues {
                        val spec =
                            getOrCreateProperty(
                                DeleteOrUpdateAdapterProperty(it.value, methodPrefix, onConflict)
                            )
                        val impl = implCallback(method, it.value)
                        spec to impl
                    }
                val methodSpec =
                    overrideWithoutAnnotations(method.element, declaredDao)
                        .apply { addCode(createDeleteOrUpdateMethodBody(method, fields)) }
                        .build()
                PreparedStmtQuery(fields, methodSpec)
            }
        }
    }

    private fun createDeleteOrUpdateMethodBody(
        method: DeleteOrUpdateShortcutMethod,
        adapters: Map<String, Pair<XPropertySpec, XTypeSpec>>
    ): XCodeBlock {
        if (adapters.isEmpty() || method.methodBinder == null) {
            return XCodeBlock.builder().build()
        }
        val scope = CodeGenScope(writer = this)
        ShortcutQueryParameterWriter.addNullCheckValidation(scope, method.parameters)
        method.methodBinder.convertAndReturn(
            parameters = method.parameters,
            adapters = adapters,
            dbProperty = dbProperty,
            scope = scope
        )
        return scope.generate()
    }

    /**
     * Groups all upsert methods based on the upsert statement they will use then creates all field
     * specs, EntityUpsertAdapterWriter and actual upsert methods.
     */
    private fun createUpsertMethods(): List<PreparedStmtQuery> {
        return dao.upsertMethods.map { upsertMethod ->
            val entities = upsertMethod.entities
            val fields =
                entities.mapValues {
                    val spec = getOrCreateProperty(UpsertAdapterProperty(it.value))
                    val impl =
                        EntityUpsertAdapterWriter.create(it.value)
                            .createConcrete(it.value, this@DaoWriter)
                    spec to impl
                }
            val methodImpl =
                overrideWithoutAnnotations(upsertMethod.element, declaredDao)
                    .apply { addCode(createUpsertMethodBody(upsertMethod, fields)) }
                    .build()
            PreparedStmtQuery(fields, methodImpl)
        }
    }

    private fun createUpsertMethodBody(
        method: UpsertMethod,
        upsertAdapters: Map<String, Pair<XPropertySpec, XCodeBlock>>
    ): XCodeBlock {
        if (upsertAdapters.isEmpty() || method.methodBinder == null) {
            return XCodeBlock.builder().build()
        }
        val scope = CodeGenScope(writer = this)
        ShortcutQueryParameterWriter.addNullCheckValidation(scope, method.parameters)
        method.methodBinder.convertAndReturn(
            parameters = method.parameters,
            adapters = upsertAdapters,
            dbProperty = dbProperty,
            scope = scope
        )
        return scope.generate()
    }

    private fun createPreparedQueryMethodBody(method: WriteQueryMethod): XCodeBlock {
        val scope = CodeGenScope(this)
        val queryWriter = QueryWriter(method)
        val sqlVar = scope.getTmpVar("_sql")
        val listSizeArgs = queryWriter.prepareQuery(sqlVar, scope)
        method.preparedQueryResultBinder.executeAndReturn(
            sqlQueryVar = sqlVar,
            dbProperty = dbProperty,
            bindStatement = { stmtVar -> queryWriter.bindArgs(stmtVar, listSizeArgs, this) },
            returnTypeName = method.returnType.asTypeName(),
            scope = scope
        )
        return scope.generate()
    }

    private fun createQueryMethodBody(method: ReadQueryMethod): XCodeBlock {
        val scope = CodeGenScope(this)
        val queryWriter = QueryWriter(method)
        val sqlStringVar = scope.getTmpVar("_sql")

        val (sqlVar, listSizeArgs) =
            if (method.queryResultBinder.usesCompatQueryWriter) {
                val roomSQLiteQueryVar = scope.getTmpVar("_statement")
                queryWriter.prepareReadAndBind(sqlStringVar, roomSQLiteQueryVar, scope)
                roomSQLiteQueryVar to emptyList()
            } else {
                sqlStringVar to queryWriter.prepareQuery(sqlStringVar, scope)
            }

        val bindStatement: (CodeGenScope.(String) -> Unit)? =
            if (queryWriter.parameters.isNotEmpty()) {
                { stmtVar -> queryWriter.bindArgs(stmtVar, listSizeArgs, this) }
            } else {
                null
            }

        method.queryResultBinder.convertAndReturn(
            sqlQueryVar = sqlVar,
            dbProperty = dbProperty,
            bindStatement = bindStatement,
            returnTypeName = method.returnType.asTypeName(),
            inTransaction = method.inTransaction,
            scope = scope
        )

        return scope.generate()
    }

    // TODO(b/251459654): Handle @JvmOverloads in delegating functions with Kotlin codegen.
    private fun createDefaultImplMethodDelegate(method: KotlinDefaultMethodDelegate): XFunSpec {
        val scope = CodeGenScope(this)
        return overrideWithoutAnnotations(method.element, declaredDao)
            .apply {
                KotlinDefaultMethodDelegateBinder.executeAndReturn(
                    daoName = dao.typeName,
                    daoImplName = dao.implTypeName,
                    methodName = method.element.jvmName,
                    returnType = method.element.returnType,
                    parameterNames = method.element.parameters.map { it.name },
                    scope = scope
                )
                addCode(scope.generate())
            }
            .build()
    }

    private fun createBoxedPrimitiveBridgeMethodDelegate(
        method: KotlinBoxedPrimitiveMethodDelegate
    ): XFunSpec {
        val scope = CodeGenScope(this)
        return overrideWithoutAnnotations(method.element, declaredDao)
            .apply {
                KotlinBoxedPrimitiveMethodDelegateBinder.execute(
                    methodName = method.element.jvmName,
                    returnType = method.element.returnType,
                    parameters =
                        method.concreteMethod.parameters.map { it.type.asTypeName() to it.name },
                    scope = scope
                )
                addCode(scope.generate())
            }
            .build()
    }

    private fun overrideWithoutAnnotations(elm: XMethodElement, owner: XType): XFunSpec.Builder {
        return XFunSpec.overridingBuilder(elm, owner)
    }

    /**
     * Represents a query statement prepared in Dao implementation.
     *
     * @param fields This map holds all the member properties necessary for this query. The key is
     *   the corresponding parameter name in the defining query method. The value is a pair from the
     *   property declaration to definition.
     * @param functionImpl The body of the query method implementation.
     */
    data class PreparedStmtQuery(
        val fields: Map<String, Pair<XPropertySpec, Any>>,
        val functionImpl: XFunSpec
    ) {
        companion object {
            // The key to be used in `fields` where the method requires a field that is not
            // associated with any of its parameters
            const val NO_PARAM_FIELD = "-"
        }
    }

    private class InsertMethodProperty(
        val shortcutEntity: ShortcutEntity,
        val onConflictText: String,
    ) :
        SharedPropertySpec(
            baseName = "insertAdapterOf${shortcutEntityFieldNamePart(shortcutEntity)}",
            type = INSERT_ADAPTER.parametrizedBy(shortcutEntity.dataClass.typeName)
        ) {
        override fun getUniqueKey(): String {
            return "${shortcutEntity.dataClass.typeName}-${shortcutEntity.entityTypeName}" +
                onConflictText
        }

        override fun prepare(writer: TypeWriter, builder: XPropertySpec.Builder) {}
    }

    class DeleteOrUpdateAdapterProperty(
        val shortcutEntity: ShortcutEntity,
        val methodPrefix: String,
        val onConflictText: String,
    ) :
        SharedPropertySpec(
            baseName = "${methodPrefix}AdapterOf${shortcutEntityFieldNamePart(shortcutEntity)}",
            type = DELETE_OR_UPDATE_ADAPTER.parametrizedBy(shortcutEntity.dataClass.typeName)
        ) {
        override fun prepare(writer: TypeWriter, builder: XPropertySpec.Builder) {}

        override fun getUniqueKey(): String {
            return "${shortcutEntity.dataClass.typeName}-${shortcutEntity.entityTypeName}" +
                "$methodPrefix$onConflictText"
        }
    }

    class UpsertAdapterProperty(val shortcutEntity: ShortcutEntity) :
        SharedPropertySpec(
            baseName = "upsertAdapterOf${shortcutEntityFieldNamePart(shortcutEntity)}",
            type = UPSERT_ADAPTER.parametrizedBy(shortcutEntity.dataClass.typeName)
        ) {
        override fun getUniqueKey(): String {
            return "${shortcutEntity.dataClass.typeName}-${shortcutEntity.entityTypeName}"
        }

        override fun prepare(writer: TypeWriter, builder: XPropertySpec.Builder) {}
    }
}
