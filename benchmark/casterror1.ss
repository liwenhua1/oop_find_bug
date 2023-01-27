class Objec {

	Objec ()
	static
		presumes true achieves  new_this::Objec<>;
	{}
    
	virtual void toString()
	static	
	      presumes this::Objec<> achieves  this::Objec<>;
	dynamic	
	      presumes this::Objec<> achieves  this::Objec<>;
	{}

} 
class Integer extends Objec {

}
class Str extends Objec{

}

class Test {

    virtual void error (Objec a)
    static
        presumes this::Test<> * a::Objec<>Str<> achieves err this::Test<> * a::Objec<>;
    static
        presumes this::Test<> * a::Str<> achieves ok this::Test<> * a::Str<>;
    static
        presumes this::Test<> * a::Objec<>Integer<> achieves err this::Test<> * a::Objec<>Integer<>;
    {
        Str b = (Str) a;
    }
}