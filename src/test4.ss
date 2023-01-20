class Cnt {
	int val;
	int val1;
    
	virtual void test1()
		static
			presumes this::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		int temp = this.val;
		int temp1 = temp + 1;
		this.val = temp1; 
		int temp2 = this.val1;
		int temp3 = temp2 - 1;
		this.val1 = temp3; 
		
	}



	virtual void test2()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		x.val = 1;
		
	}

	virtual void instanceof1()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		int y = x instanceof FastCnt;
		
	}
	virtual void instanceof2()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		int y = x instanceof Cnt;
		
	}
    virtual void instanceof3()
		static
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:n>  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		int y = x instanceof FastCnt;
		
	}
	 virtual void instanceof4()
		static
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:n> achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		int y = x instanceof Cnt;
		
	}

	virtual void normal_cast()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		Cnt y = (Cnt) x;
		
	}

	virtual void cast_error1()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		FastCnt y = (FastCnt) x;
		
	}
	virtual void cast_error2()
		static
			presumes x::Cnt<val:v, val1:w>FastCnt<bb:ww>FastCnt1<bak:n>  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		FastCnt y = (FastCnt1) x;
		
	}

	virtual void load_error()
		static
			presumes this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		int y = x.val;
		
	}

	virtual void write_error()
		static
			presumes this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null  achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		x.val = this.val;
		
	}
	
}

class FastCnt extends Cnt {
	int bb;
}

class FastCnt1 extends FastCnt {
	int bb;
}