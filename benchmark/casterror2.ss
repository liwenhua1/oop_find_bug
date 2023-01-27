
class Ctelement{
    virtual Ctelement getparent()
    static 
        presumes this::Ctelement<> achieves this::Ctelement<>*res::Ctelement<>CtExecutable<>;
    dynamic
        presumes this::Ctelement<> achieves this::Ctelement<>*res::Ctelement<>CtExecutable<>;
    {

    }
}

class CtVariable extends Ctelement{

    inherit Ctelement getparent()
    static 
        presumes this::CtVariable<> achieves this::CtVariable<>*res::Ctelement<>CtExecutable<>;
    dynamic
        presumes this::Ctelement<>CtVariable<> achieves this::Ctelement<>CtVariable<>*res::Ctelement<>CtExecutable<>;
    {

    }

}

class CtParameter extends CtVariable {
    inherit Ctelement getparent()
    static 
        presumes this::CtParameter<> achieves this::CtParameter<>*res::Ctelement<>CtExecutable<>;
    dynamic
        presumes this::Ctelement<>CtVariable<>CtParameter<> achieves this::Ctelement<>CtVariable<>CtParameter<>*res::Ctelement<>CtExecutable<>;
    {

    }
}

class CtLambda extends CtExecutable {


}
class CtMethod extends CtExecutable {

}

class CtExecutable extends Ctelement{

}

class Test {

    virtual void casterror(CtVariable a) 
    static 
        presumes this::Test<> * a::CtVariable<>CtParameter<> achieves err this::Test<> * a::CtVariable<>CtParameter<> * s::Ctelement<>CtExecutable<>;
        
    {
      int y = a instanceof CtParameter;
      if (y) {
            Object s = a.getparent();
            int x = s instanceof CtLambda;
            if (x) {} else 
            {CtMethod z = (CtMethod) s;}

     }
      
    }
}