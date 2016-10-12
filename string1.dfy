// Eoin Houlihan - 13323304
// Aisling Norris - 13325467

method isPrefix(pre: string, str: string) returns (res: bool)
{
	if (|pre| == 0)
	{
		// Empty string is a prefix of every string
		return true;
	}

	if (|str| < |pre|)
	{
		return false;
	}

	return str[..|pre| - 1] == pre;
}

method isSubstring(sub: string, str: string) returns (res: bool)
{
	if (|sub| == 0)
	{
		// Empty string is a substring of every string
		return true;
	}
	
	if (|str| < |sub|)
	{
		return false;
	}

	var i := 0;

	while (i < |str|)
	{
		var index := (i + |sub|) - 1;
		if (|str[i..]| < |sub|)
		{
			return false;
		}
		if (str[i..index] == sub)
		{
			return true;
		}
		i := i + 1;
	}
	return false;
}
