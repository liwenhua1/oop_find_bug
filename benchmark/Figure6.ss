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

class Super {
	virtual Obj foo () 
	static
		presumes this::Super<> achieves this::Super<> * res::Objec<>;
	dynamic
		presumes this::Super<> achieves this::Super<> * res::Objec<>;
	{
		Objec o = new Objec ();
		return o;
	}
}


class Sub extends Super {
	
	override Obj foo ()
	static
		presumes this::Sub<> achieves this::Sub<> & res = null;
	dynamic
	    presumes this::Sub<> achieves this::Sub<> & res = null; 
	dynamic
		presumes this::Super<> achieves this::Super<> * res::Objec<>; 	
	{
		int temp;
		return temp;}

	virtual void test (Super a)
	static 
		 presumes this::Sub<> * a::Super<> achieves ok this::Sub<> * a::Super<> * m::Objec<>;
	static 
		 presumes this::Sub<> * a::Sub<> achieves err this::Sub<> * a::Sub<> & m = null;
    dynamic 
		 presumes this::Sub<> * a::Super<> achieves ok this::Sub<> * a::Super<> * m::Objec<>;
    dynamic 
		 presumes this::Sub<> * a::Sub<> achieves err this::Sub<> * a::Sub<> & m = null;
	
	{
		Objec m = a.foo();
		m.toString();
		
	}

	virtual void buggy (Sub b)
	static 
	        presumes this::Sub<> * b::Sub<> achieves err this::Sub<> * b::Sub<> ;
	dynamic 
	        presumes this::Sub<> * b::Sub<> achieves err this::Sub<> * b::Sub<> ;
	{
		this.test(b);
	}
}
