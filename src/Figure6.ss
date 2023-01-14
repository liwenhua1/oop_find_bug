class Super {
	virtual OBject foo () 
	static
		presumes this::Cnt<val:v> achieves this::Cnt<val:v+1> or this::Cnt<val:v+2>;
	dynamic
		presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		Object o;
		o = new Object ();
		return o;
	}
}


class Sub extends Super {
	
	override Object foo ()
	static presumes this::FastCnt<val:v, bak:w> achieves this::FastCnt<val:v+2>;
	dynamic presumes this::Cnt<val:v>FastCnt<bak:w> achieves this::Cnt<val:v+1>FastCnt<bak:w+2>; 
	{return null;}

	virtual void test (Super a)
	static presumes this::FastCnt<val:v, bak:w> achieves this::FastCnt<val:v+2>;
	dynamic presumes this::Cnt<val:v>FastCnt<bak:w> achieves this::Cnt<val:v+1>FastCnt<bak:w+2>; 
	{
		m = a.foo();
		m.toString();
	}

	virtual void buggy (Sub b)
	static presumes this::FastCnt<val:v, bak:w> achieves this::FastCnt<val:v+2>;
	dynamic presumes this::Cnt<val:v>FastCnt<bak:w> achieves this::Cnt<val:v+1>FastCnt<bak:w+2>; 
	{
		test(b);
	}
}
