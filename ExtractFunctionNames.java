/*
 * extract possible function names from a .m file
 * input argument: the file name
*/

import java.io.*;
import java.util.HashSet;
import java.util.regex.*;

public class ExtractFunctionNames {

	static String readFile(String file) throws IOException {
		File f = new File(file);
		byte[] buffer = new byte[(int) f.length()];
		DataInputStream in = new DataInputStream(new FileInputStream(f));
		in.readFully(buffer);
		in.close();
		return new String(buffer);
	}

	public static void main(String[] args) throws IOException {
		Pattern p = Pattern.compile("[A-Z][a-zA-Z0-9]*");
		Matcher m = p.matcher(readFile(args[0]));
		
		HashSet<String> s = new HashSet<String>();
		while (m.find()) s.add(m.group());
		
		System.out.println(s);
	}
}
