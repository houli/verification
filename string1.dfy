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
		if (|str[i..]| < |sub|)
		{
			return false;
		}

		var index := (i + |sub|) - 1;
		if (str[i..index] == sub)
		{
			return true;
		}
		i := i + 1;
	}
	return false;
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
{
	if (k == 0)
	{
		// Both strings contain the empty string as a substring
		return true;
	}

	var i := 0;
	while (i < |str1|)
	{
		if (|str1[i..]| < k)
		{
			return false;
		}

		var index := (i + k) - 1;
		var found := isSubstring(str1[i..index], str2);
		if (found)
		{
			return true;
		}
		i := i + 1;
	}
	return false;
}
