class AbstractHistogram {
	
}

class Cnt {
    int val;
	virtual bool equals (Object other) 
	static presumes this::Cnt<val:v> * other::AbstractHistogram<> achieves err this::Cnt<val:v> * other::AbstractHistogram<> ;
	dynamic presumes this::Cnt<val:v> * other::AbstractHistogram<> achieves err this::Cnt<val:v> * other::AbstractHistogram<> ;

	{   int y = other instanceof AbstractHistogram;
		if (y) {
			DoubleHistogram otherHistogram = (DoubleHistogram) other;
		}
	}

}

