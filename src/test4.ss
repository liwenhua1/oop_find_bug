class Cnt {
	int val;
	int val1;
    
	virtual void test1()
		static
			presumes this::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1, val1:w-1> ;
		dynamic
			presumes this::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1, val1:w-1> ;
	{
		int temp = this.val;
		int temp1 = temp+1;
		this.val = temp1; 
		int temp2 = this.val1;
		int temp3 = temp2 - 1;
		this.val1 = temp3; 
		
	}



	virtual void test2()
		static
			presumes x::Cnt<val:v, val1:w>  achieves x::Cnt<val:1, val1:w> ;
		dynamic
			presumes x::Cnt<val:v, val1:w>  achieves x::Cnt<val:1, val1:w> ;
	{    

		 x.val = 1;
		
	}

	virtual void instanceof1()
		static
			presumes x::Cnt<val:v, val1:w>  achieves x::Cnt<val:v, val1:w> & res=0;
		dynamic
			presumes x::Cnt<val:v, val1:w>  achieves x::Cnt<val:v, val1:w> & res=0;
	{
		int y = x instanceof FastCnt;
		return y;
		
	}
	virtual void instanceof2()
		static
			presumes x::Cnt<val:v, val1:w>  achieves x::Cnt<val:v, val1:w> & res=1;
		dynamic
			presumes x::Cnt<val:v, val1:w>  achieves x::Cnt<val:v, val1:w> & res=1;
	{
		int y = x instanceof Cnt;
		return y;
		
	}
    virtual void instanceof3()
		static
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:n>  achieves x::FastCnt<val:v, val1:w, bak:n> & res = 1;
		dynamic
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:n>  achieves x::FastCnt<val:v, val1:w, bak:n> & res = 1;
	{
		int y = x instanceof FastCnt;
		return y;
		
	}
	 virtual void instanceof4()
		static
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:n>  achieves x::Cnt<val:v, val1:w> & res = 1;
		dynamic
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:n>  achieves x::Cnt<val:v, val1:w> & res = 1;
	{
		int y = x instanceof Cnt;
		
	}

	virtual void normal_cast()
		static
			presumes x::Cnt<val:v, val1:w>  achieves x::Cnt<val:v, val1:w> & res = x;
		dynamic
			presumes x::Cnt<val:v, val1:w>  achieves x::Cnt<val:v, val1:w> & res = x;
	{
		Cnt y = (Cnt) x;
		return y;
	}

	virtual void cast_error1()
		static
			presumes x::Cnt<val:v, val1:w>  achieves err x::Cnt<val:v, val1:w> ;
		dynamic
			presumes x::Cnt<val:v, val1:w>  achieves err x::Cnt<val:v, val1:w> ;
	{
		FastCnt y = (FastCnt) x;
		return y;
		
	}
	virtual void cast_error2()
		static
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:z>  achieves err x::Cnt<val:v, val1:w>;
		dynamic
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:z>  achieves err x::Cnt<val:v, val1:w>;
	{
		FastCnt y = (FastCnt) x;
		return y;
	}

	virtual void load_error()
		static
			presumes this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null  achieves err this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null;
		dynamic
			presumes this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null  achieves err this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null;
	{
		int y = x.val;
		return y;
	}

	virtual void write_error()
		static
			presumes this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null  achieves err this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null;
		dynamic
			presumes this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null  achieves err this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null;
	{
		int temp = this.val;
		x.val = temp;
		return temp;
	}
	
}

class FastCnt extends Cnt {
	int bak;
}

