class CtVariable {

}

class CtParameter extends CtVariable {

}

class CtLambda extends CtExecutable {


}
class CtMethod extends CtExecutable {

}

class CtConstructor extends CtExecutable{

}

class Test {

    virtual void error (Objec a)
    static
        presumes this::Test<> * a::CtVariable<>CtParameter<>C achieves err this::Test<> * a::Objec<>;
    {
        Str b = (Str) a;
    }