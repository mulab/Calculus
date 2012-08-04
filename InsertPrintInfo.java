/*
 * insert debug info into Int functions of a .m file
 * 
 * input arguments:
 * the 1st argument is the directory
 * the 2nd argument is the filename
 * 
 * the .m file should follow the following format:
 * 1. In the definitions of Int function \r\n should follow the ":=" and "/;",
 *    but no \r\n should appear after the "/;"s in the condition of a definition.
 * 2. After each definition of Int, at least 2 \r\n's should appear
*/

import java.io.*;
import java.util.regex.*;
import java.util.Stack;

public class InsertPrintInfo {
	
	static String readFile(String file) throws IOException {
		File f = new File(file);
		byte[] buffer = new byte[(int) f.length()];
		DataInputStream in = new DataInputStream(new FileInputStream(f));
		in.readFully(buffer);
		in.close();
		return new String(buffer);
	}
	
	static void writeFile(String file, String txt) throws IOException {
		FileWriter writer = new FileWriter(file);
		writer.write(txt);
		writer.close();
	}
	
	static int bracketDisMatch(String str) {
		Stack<String> stack = new Stack<String>();
		for (int i = 0; i < str.length(); i++)
			switch (str.charAt(i)) {
			case '{':
				stack.push("{");
				break;
			case '}':
				if (!stack.empty() && stack.peek().equals("{"))
					stack.pop();
				else return (!stack.empty() && stack.peek().equals("(") ? i : -i);
				break;
			case '(':
				stack.push("(");
				break;
			case ')':
				if (!stack.empty() && stack.peek().equals("("))
					stack.pop();
				else return (!stack.empty() && stack.peek().equals("(") ? i : -i);
				break;
			case '[':
				stack.push("[");
				break;
			case ']':
				if (!stack.empty() && stack.peek().equals("["))
					stack.pop();
				else return (!stack.empty() && stack.peek().equals("(") ? i : -i);
				break;
			}
		return (stack.empty() ? 0 : (stack.peek().equals("(") ? str.length() : -str.length()));
	}
	
	static String replace(String str, String src, String dst) {
		int idx = str.indexOf(src);
		int end = idx+src.length();
		return str.substring(0,idx)+dst+str.substring(end);
	}
	
	public static void main(String[] args) throws IOException {
		String filePath = args[0]+System.getProperty("file.separator")+args[1];
		String str = readFile(filePath);
		
		Pattern p_set = Pattern.compile("Int\\[.*?\\] :=\\r\\n(?<def>.*?)\\r\\n(?:(?:\\r\\n)|$)", Pattern.DOTALL);
		Pattern p_def = Pattern.compile("(?<act>.*) /;\\r\\n", Pattern.DOTALL);
		Matcher m_set = p_set.matcher(str);
		int cnt = 0;
		while (m_set.find()) {
			String set = m_set.group();
			System.out.println((++cnt)+":\n"+set);
			String def = m_set.group("def");
			Matcher m_def = p_def.matcher(def);
			if (m_def.find()) {
				String act = m_def.group("act"), tmp;
				if (bracketDisMatch(act) == 0) {
					tmp = "(Print[\"Int("+cnt+"th)@"+args[1]+"\"];\r\n"+act+")";
					tmp = replace(def, act, tmp);
				}
				else {
					if (def.endsWith(";"))
						tmp = "(Print[\"Int("+cnt+"th)@"+args[1]+"\"];\r\n"+def.substring(0, def.length()-1)+");";
					else
						tmp = "(Print[\"Int("+cnt+"th)@"+args[1]+"\"];\r\n"+def+")";
					int pos = bracketDisMatch(tmp);
					if (pos != 0) {
						if (pos > 0) {
							tmp = tmp.substring(0, pos)+")"+tmp.substring(pos);
							if (tmp.endsWith(");")) tmp = tmp.substring(0, tmp.length()-2)+";";
							else tmp = tmp.substring(0, tmp.length()-1);
						}
						System.out.print(pos+" You'd better to verify manually. [Enter]");
						BufferedReader stdin = new BufferedReader(new InputStreamReader(System.in));
						stdin.readLine();
					}
				}
				tmp = replace(set, def, tmp);
				System.out.println(tmp);
				str = replace(str, set, tmp);
			}
			else System.out.println("!!!");
			m_set.region(m_set.end(), m_set.regionEnd());
		}
		
		str = str.replaceAll("\\(\\*.{14,}?\\*\\)", "");
		str = str.replaceAll("(\\r\\n){3,}", "\r\n\r\n");
		
		writeFile(filePath, str);
	}
}