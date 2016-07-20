This is the fifth version (v0.5) of Circus2ZCSP, a translator to link a Circus specification to CSP || Z.

# Usage
- `$java -jar circus2zcsp.jar spec.tex [spec1.tex [...]] [-d] [-v] [-V]`

## help
Invoke without arguments will print help information
- `$java -jar circus2zcsp.jar`
- or `$java -jar circus2zcsp.jar -h`

        usage: java -jar circus2zcsp.jar spec.tex [spec1.tex [...]] [-d] [-v] [-V]
        
        Circus2ZCSP is a translator to link one (or more) Circus specification to its
        corresponding model in Z || CSP, which is sequentially model-checked by ProB.
        Options:
            -d,--verbose      run in debug mode
            -v,--version      show version
            -V,--Versions     show detailed versions information
        For any problems, please contac <ky582@york.ac.uk> or <ye.randall@gmail.com>

## debug mode
Invoke with -d option will make the tool run in the debug mode and more information provided
- `$java -jar circus2zcsp.jar -d circus_spec.tex`

## show current version
- `$java -jar circus2zcsp.jar -v`

        Current Circus2ZCSP version: 0.3

## show version history
- `$java -jar circus2zcsp.jar -V`

# Versions History
## v0.5
### Release Notes

        ==> 0.5
        This is the fifth release built on July 20th, 2016. It is capable of translating
         all constructs in the reactive buffer, the steam boiler cases, and the ESEL cas
        e.
        -------------------------------------- New ------------------------------------
        1. Add translator version and date information in the header of output CSP and Z
        .------------------------------------- Fixed -----------------------------------
        ------------------------------------ Changed ----------------------------------
        ----------------------------------- Limitations -------------------------------
        1. External choice of actions are only available to "prefixed" actions (such as
        basic actions, prefixing, guarded commands), and compound CSP actions of these "
        prefixed" actions.
        2. Parallel composition and interleaving for actions are not supported if both a
        ctions share variables in scope.
        3. Operator template is not supported.
        4. Reflexive-transitive closure (*) is not supported.
        5. For schemas as predicate, it may have duplicate predicates from the declarati
        onpart. It will not cause problems but make the model larger if there are many s
        chema references in the schema.

## v0.4
### Release Notes

        ==> 0.4
        This is the fourth release built on July 13th, 2016. It is capable of translatin
        g all constructs in the reactive buffer, the steam boiler cases, and the ESEL ca
        se.
        -------------------------------------- New ------------------------------------
        ------------------------------------- Fixed -----------------------------------
        1. PredicateListExpansionVisitor: include predicates from the declaration part i
        nto the final predicate.
        ------------------------------------ Changed ----------------------------------
        1. Move rewrite of schema as predicate (CircusSchemasAsPredicateVisitor) after
        Stage 1 Rewrite then we don't have to cope with generic constructs since they ha
        ve been rewritten in th Stage 1.
        ----------------------------------- Limitations -------------------------------
        1. External choice of actions are only available to "prefixed" actions (such as
        basic actions, prefixing, guarded commands), and compound CSP actions of these "
        prefixed" actions.
        2. Parallel composition and interleaving for actions are not supported if both a
        ctions share variables in scope.
        3. Operator template is not supported.
        4. Reflexive-transitive closure (*) is not supported.
        5. For schemas as predicate, it may have duplicate predicates from the declarati
        onpart. It will not cause problems but make the model larger if there are many s
        chema references in the schema.


## v0.3
### Release Notes

        ==> 0.3
        This is the third release built on June 30th, 2016. It is capable of translating
         all constructs in the reactive buffer, the steam boiler cases, and the ESEL cas
        e.
        -------------------------------------- New ------------------------------------
        ------------------------------------- Fixed -----------------------------------
        ------------------------------------ Changed ----------------------------------
        1. Check if a schema that corresponding a schema expression as action shall be
           an operational schema.
        ----------------------------------- Limitations -------------------------------
        1. External choice of actions are only available to "prefixed" actions (such as
        basic actions, prefixing, guarded commands), and compound CSP actions of these "
        prefixed" actions.
        2. Parallel composition and interleaving for actions are not supported if both a
        ctions share variables in scope.
        3. Operator template is not supported.
        4. Reflexive-transitive closure (*) is not supported.


## v0.2
### Release Notes

        ==> 0.2
        This is the second release built on May 13th, 2016. It is capable of translating
         all constructs in the reactive buffer, the steam boiler cases, and the ESEL cas
        e.
        -------------------------------------- New ------------------------------------
        1. Add support of iterated parallel and interleaving of actions for the case if
        their actions have disjoint variables in scope
        2. Add support of iterated parallel of processes
        ------------------------------------- Fixed -----------------------------------
        1. Add parenthesis around translated freetype constructor d~1: d.1 => (d.1) in c
        sp
        2. The problem that freetype is not translated to CSP though this type is used i
        n the behavioural part
        ------------------------------------ Changed ----------------------------------
        1. The processing of u'=u (u - variables not in frame) in schema expression as a
        ction
            1.1 if v' is included in its declaration part, then this v is regarded in fr
        ame
            1.2 if v' is nto included in its declaration part (though v might be include
        d), then this v is regarded not in frame
        2. The logic to include parent sections
            2.1 use a stack to keep dependency order of all sections
            2.2 assemble all sections into a big section according to their dependency o
        rder
        ----------------------------------- Limitations -------------------------------
        1. External choice of actions are only available to "prefixed" actions (such as
        basic actions, prefixing, guarded commands), and compound CSP actions of these "
        prefixed" actions.
        2. Parallel composition and interleaving for actions are not supported if both a
        ctions share variables in scope.
        3. Operator template is not supported.
        4. Reflexive-transitive closure (*) is not supported.

## v0.1
### Release Notes 

        ==> 0.1
        This is the first release.
        It is capable of translating all constructs in the reactive buffer and the steam
         boiler cases.
        Limitations:
            1. External choice of actions are only available to "prefixed" actions (such
         as basic actions, prefixing, guarded commands), and compound CSP actions of the
        se "prefixed" actions.
            2. Parallel composition and interleaving for actions are not supported if bo
        th actions share variables in scope.
            3. Operator template is not supported.
            4. Reflexive-transitive closure (*) is not supported.
