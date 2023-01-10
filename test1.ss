class Cnt {
	int val;

	void tick()
		static
			presumes this::Cnt<val:v> achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		int temp = this.val;
		int temp1 = temp + 1;
		this.val = temp1; 
	}
}
