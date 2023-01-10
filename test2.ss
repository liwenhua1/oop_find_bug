class Cnt {
	int val;
	int val1;

	void tick()
		static
			presumes this::Cnt<val:v, val1:w> achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v, val1:w> achieves err this::Cnt<val1:w> & v+1<=w<=v+2;
	{
		int temp = this.val;
		int temp1 = temp + 1;
		this.val = temp1; 
		int temp = this.val1;
		int temp1 = temp - 1;
		this.val1 = temp1; 
	}
}
