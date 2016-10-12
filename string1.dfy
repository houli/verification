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
	var i := 0;
	while (i < |str|)
	{
		var prefix := isPrefix(sub, str[i..]);
		if (prefix)
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

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
{
	// Every two strings have a common substring of length zero
	len := 0;
	var i := 1;

	while (i < |str1|)
	{
		var found := haveCommonKSubstring(i, str1, str2);
		if (found)
		{
			len := i;
		}
		i := i + 1;
	}
	return len;
}
