/*
 The MIT License (MIT)

Copyright (c) 2014 Pierre Lindenbaum PhD

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
 */
package com.github.lindenb.java2graph;

import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.JarInputStream;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Pattern;

import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;

interface Filter<T>
	{
	boolean accept(T data);
	}

enum Relation
	{
	SUPER,
	IMPLEMENTS,
	DECLARES,
	RETURNS,
	ARGUMENT
	};

/** Wrapper around a java class */
class ClassWrapper
	{
	/** unique id generator */
	private static int ID_GENERATOR=0;

	/** unique id */
	private int id= (++ID_GENERATOR);
	/** the class observed */
	private Class<?> clazz;
	/** did we already processed this class ? */
	private boolean visited=false;
	/** was selected by the user */
	 boolean userTarget=false;
	/** distance to user Target */
	 int distancdeToUserTarget=Integer.MAX_VALUE;
	
	ClassWrapper(Class<?> clazz)
		{
		this.clazz=clazz;
		}
	
	public Class<?> getWrappedClass()
		{
		return this.clazz;
		}
	
	public int getId()
		{
		return id;
		}
	
	public boolean isVisited() {
		return visited;
		}
	
	public void setVisited(boolean visited) {
		this.visited = visited;
		}
	
	@Override
	public int hashCode()
		{
		return getWrappedClass().hashCode();
		}
	
	@Override
	public boolean equals(Object obj)
		{
		if(obj==this) return true;
		if(obj==null || getClass()!=obj.getClass()) return false;
		return ClassWrapper.class.cast(obj).getWrappedClass()==getWrappedClass();
		}
	
	public boolean isInterface()
		{
		return this.clazz.isInterface();
		}
	
	@Override
	public String toString()
		{
		return this.clazz.getName();
		}
	} 



/**
 * Defines a Link between to classes
 * @author lindenb
 *
 */
class Link
	{
	private ClassWrapper from;
	private ClassWrapper to;
	private Relation label;
	private Set<String> methodsName=null;
	Link(ClassWrapper from,ClassWrapper to,Relation label)
		{
		this.from=from;
		this.to=to;
		this.label=label;
		}
	
	public ClassWrapper getFrom()
		{
		return from;
		}
	
	public ClassWrapper getTo()
		{
		return to;
		}
	
	Set<String> getMethods()
		{
		if(methodsName==null) methodsName=new TreeSet<String>();
		return methodsName;
		}
	
	public Relation getRelation() {
		return label;
		}
	
	@Override
	public boolean equals(Object obj) {
		if(obj==this) return true;
		if(obj==null || getClass()!=obj.getClass()) return false;
		return 	Link.class.cast(obj).from.equals(this.from) &&
				Link.class.cast(obj).to.equals(this.to)
				;
		}
	
	@Override
	public int hashCode() {
		return from.hashCode()*31+to.hashCode();
		}
	
	@Override
	public String toString() {
		return getFrom().toString() +
				" -["+getRelation()+"]-> " +
				getTo().toString();
		}
	
	
	
	}


/**
 * Java2Graph
 * Reference: http://plindenbaum.blogspot.fr/2008/10/javadoc-is-not-enough-java2dia.html
 * prints a java hierarchy for javaclasses to the dot format
 * @author Pierre Lindenbaum PhD @yokofakun
 *
 */
public class Java2Graph
	{
	/** logger */
	private static final Logger LOG=Logger.getLogger("java2graph");

	/** final printer */
	private AbstractGraphPrinter graphPrinter=new DotGraphPrinter();
	
	private abstract class AbstractGraphPrinter
		{
		public abstract void print(PrintStream out) throws Exception;
		}
	
	private class GexfPrinter
		extends AbstractGraphPrinter
		{
		XMLStreamWriter w;
		
		
		private void gexfAttDecl(
				String key,
				String type
				)throws XMLStreamException
				{
				w.writeEmptyElement("attribute");
				w.writeAttribute("id", key);
				w.writeAttribute("title", key.replace('_', ' '));
				w.writeAttribute("type", type);
				}
		private void gexfAtt(String key,String value)
				throws XMLStreamException
				{
				if(value==null) return;
				w.writeStartElement("attvalue");
				w.writeAttribute("for", key);
				w.writeAttribute("value", value);
				w.writeEndElement();
				}
		
		@Override
		public void print(PrintStream out) throws Exception
			{
			XMLOutputFactory xmlfactory= XMLOutputFactory.newInstance();
			this.w= xmlfactory.createXMLStreamWriter(out,"UTF-8");
			
			w.writeStartDocument("UTF-8","1.0");
			w.writeStartElement("gexf");
			w.writeAttribute("xmlns", "http://www.gexf.net/1.2draft");
			w.writeAttribute("xmlns:viz","http://www.gexf.net/1.2draft/viz");
			w.writeAttribute("version", "1.2");
			
			
			/* meta */
			w.writeStartElement("meta");
				w.writeStartElement("creator");
				  w.writeCharacters(Java2Graph.class.getCanonicalName());
				w.writeEndElement();
				w.writeStartElement("description");
				  w.writeCharacters("java2 DOT Graph");
				w.writeEndElement();
			w.writeEndElement();
			
			/* graph */
			w.writeStartElement("graph");
			w.writeAttribute("mode", "static");
			w.writeAttribute("defaultedgetype", "directed");
			
			
			
			/* attributes */
			w.writeStartElement("attributes");
			w.writeAttribute("class","node");
			w.writeAttribute("mode","static");
			gexfAttDecl("simpleName","string");
			gexfAttDecl("canonicalName","string");
			gexfAttDecl("defaultName","string");
			gexfAttDecl("package","string");
			gexfAttDecl("classOrInterface","string");
			w.writeEndElement();//attributes
			
			/* nodes */
			w.writeStartElement("nodes");
			for(ClassWrapper c: Java2Graph.this.classes)
				{
				if(!c.isVisited()) continue;
				if(Java2Graph.this.limitDistance>0 && c.distancdeToUserTarget>Java2Graph.this.limitDistance)
					{
					continue;
					}
				w.writeStartElement("node");
				w.writeAttribute("id", "N"+c.getId());
				w.writeAttribute("label", c.getWrappedClass().getSimpleName()==null?
						c.getWrappedClass().toString():
							c.getWrappedClass().getSimpleName()
						);
				
				w.writeEmptyElement("viz:color");
				if(c.isInterface())
					{
					w.writeAttribute("r", "161");
					w.writeAttribute("g", "83");
					w.writeAttribute("b", "83");
					}
				else
					{
					w.writeAttribute("r", "83");
					w.writeAttribute("g", "101");
					w.writeAttribute("b", "161");
					}
				
				w.writeStartElement("attvalues");
				gexfAtt("simpleName",String.valueOf(c.getWrappedClass().getSimpleName()));
				gexfAtt("canonicalName",String.valueOf(c.getWrappedClass().getCanonicalName()));
				gexfAtt("defaultName",String.valueOf(c.getWrappedClass().getName()));

				Package pack=c.getWrappedClass().getPackage();
				if(pack==null)
					{
					gexfAtt("package","(default)");
					}
				else
					{
					gexfAtt("package",pack.getName());
					}
				w.writeEndElement();//attvalues
				
				gexfAtt("classOrInterface",c.isInterface()?"interface":"class");
				
				w.writeEndElement();
				}
	
			w.writeEndElement();//nodes
			
			/* edges */
			int relid=0;
			w.writeStartElement("edges");
			for(Link L: Java2Graph.this.links)
				{
				if(!L.getFrom().isVisited() ||	 !L.getTo().isVisited() ) continue;
				if(Java2Graph.this.limitDistance>0 &&
					(
					L.getTo().distancdeToUserTarget>Java2Graph.this.limitDistance ||
					L.getFrom().distancdeToUserTarget>Java2Graph.this.limitDistance
					))
					{
					continue;
					}
				
				
				w.writeEmptyElement("edge");
				w.writeAttribute("id", "E"+(++relid));
				w.writeAttribute("type", "directed");
				w.writeAttribute("source","N"+L.getFrom().getId());
				w.writeAttribute("target","N"+L.getTo().getId());
				w.writeAttribute("label",L.getRelation().name());
				}
			w.writeEndElement();//edges

			w.writeEndElement();//graph
			
			w.writeEndElement();//gexf
			w.writeEndDocument();
			w.flush();
			
			
			}
		}
	
	private class DotGraphPrinter
		extends AbstractGraphPrinter
		{
		PrintStream out;
		
		public void print(PrintStream out) throws Exception
			{
			LOG.info("printing to dot");
			this.out=out;
			
			out.println("digraph G{");
			
			for(ClassWrapper c: Java2Graph.this.classes)
				{
				if(!c.isVisited()) continue;
				if(Java2Graph.this.limitDistance>0 && c.distancdeToUserTarget>Java2Graph.this.limitDistance)
					{
					continue;
					}
				this.dot(c);
				}
			for(Link L: Java2Graph.this.links)
				{
				this.dot(L);
				}
			out.println("}");
			out.flush();
			}
		private void dot(Link L)
			{
			if(!L.getFrom().isVisited() ||	 !L.getTo().isVisited() ) return;
			if(Java2Graph.this.limitDistance>0 &&
				(
				L.getTo().distancdeToUserTarget>Java2Graph.this.limitDistance ||
				L.getFrom().distancdeToUserTarget>Java2Graph.this.limitDistance
				))
				{
				return;
				}
			
			out.print("id"+L.getFrom().getId()+"->id"+L.getTo().getId()+"[");
			switch(L.getRelation())
				{
				case IMPLEMENTS: out.print("color=red,fontcolor=red,arrowType=onormal,"); break;
				case DECLARES: out.print("color=green,fontcolor=green,"); break;
				case SUPER:out.print("color=black,fontcolor=black,arrowType=normal,"); break;
				case RETURNS:out.print("color=black,fontcolor=orange,arrowType=normal,"); break;
				case ARGUMENT:out.print("color=black,fontcolor=blue,arrowType=normal,"); break;
				default:System.err.println("???? dot type not handled "+L.getRelation());break;
				}
			if(L.getRelation()==Relation.RETURNS || L.getRelation()==Relation.ARGUMENT )
				{
				out.print("label=\"");
				for(String m: L.getMethods())
					{
					out.print(m+" ");
					}
				out.print("\"");
				}
			else
				
				{
				out.print("label=\""+L.getRelation().name().toLowerCase()+"\"");
				}
			out.println("]");
			}
		
		private void dot(ClassWrapper C)
			{
			out.print("id"+C.getId()+"[shape=rectangle,style=filled,");
			if(C.isInterface())
				{
				out.println("fillcolor=khaki,");
				}
			else
				{
				out.println("fillcolor=gray77,");
				}
			out.print("label=\""+C.getWrappedClass().getName()+"\"");
			out.println("]");
			}
		}

	
	
	
	
		
		

	
	/** all the files */
	private ArrayList<File> files=new ArrayList<File>();
	/** all the classes that may be observed */
	private HashSet<ClassWrapper> classes= new HashSet<ClassWrapper>();
	/** all the links between the classes */
	private HashSet<Link> links= new HashSet<Link>();
	/** ignore pattern */
	private List<Filter<Class<?>>> discardClassFilters= new ArrayList<Filter<Class<?>>>();
	
	/** are we using any.any$any classes ? */ 
	private boolean usingDeclaredClasses=true;
	/** are we using interfaces ? */
	private boolean usingInterfaces=true;
	/** are we looking for classes implementing interfaces */
	private boolean usingClassesImplementingInterfaces=true;
	/** use private inner classes */
	private boolean usePrivateDeclaredClasses=false;
	/** distance max to class targeted by user -1= no restriction*/
	private int limitDistance=-1;
	/** use method signatures */
	private boolean useMethodReturnType=false;
	/** use method signatures */
	private boolean useMethodArguments=false;
	/** use Annotations */
	private boolean useAnnotations=false;
	
	/** empty private cstor */
	private Java2Graph()
		{
		
		}
	
	/** add a file in the list of jar files */
	private void addFile(File jarFile) throws IOException
		{
		if(!jarFile.exists())
			{
			LOG.warning(jarFile.toString()+" doesn't exists");
			return;
			}
		
		if(jarFile.isDirectory())
			{
			for(File fc: jarFile.listFiles(new FileFilter()
				{
				@Override
				public boolean accept(File f) {
					return f.isDirectory() || (f.isFile() && f.getName().endsWith(".jar"));
					}
				}))
				{
				LOG.info("Adding file "+jarFile);
				this.addFile(fc);
				}
			return;
			}
		
		this.files.add(jarFile);
		}
	
	/** finds a class Wrapper by its name */
	private ClassWrapper findByName(String s)
		{
		for(ClassWrapper cw: this.classes)
			{
			if(cw.getWrappedClass().getName().equals(s))
				{
				return cw;
				}
			}
		try {
			Class<?> c=Class.forName(s);
			LOG.info("adding class "+c);
			ClassWrapper cw= new ClassWrapper(c);
			this.classes.add(cw);
			return cw;
		} catch (Exception e) {
			LOG.warning(s+" not found");
			return null;
			}
		}

	
	/** finds a class Wrapper by its delegated class */
	private ClassWrapper findByClass(Class<?> c)
		{
		if(c==null) return null;
		for(ClassWrapper cw: this.classes)
			{
			if(cw.getWrappedClass()==c) return cw;
			}
		ClassWrapper cw= new ClassWrapper(c);
		this.classes.add(cw);
		return cw;
		}
	

	
	/** workhorse. recursive call for this class wrapper */
	private void recursive(ClassWrapper cw,int distance)
		{
		if(cw==null) return;
		
		for(Filter<Class<?>> filter:this.discardClassFilters)
			{
			if((!filter.accept(cw.getWrappedClass())))
				{
				return;
				}
			}
		
		if(distance< cw.distancdeToUserTarget) cw.distancdeToUserTarget=distance;
		if(cw.isVisited()) return;
		LOG.info("running for "+cw.getWrappedClass());
		HashSet<ClassWrapper> nextToBeProcessed= new HashSet<ClassWrapper>();
		//System.err.println("Found "+cw);
		cw.setVisited(true);
		Class<?> wrappedClass= cw.getWrappedClass();
	
		Class<?> superClass= wrappedClass.getSuperclass();
		if(superClass!=null && superClass!=Object.class)
			{
			ClassWrapper cw2= this.findByClass(superClass);
			if(cw2!=null)
				{
				this.links.add(new Link(cw,cw2,Relation.SUPER));
				nextToBeProcessed.add(cw2);
				}
			}
	
		if(usingInterfaces)
			{
			for(Class<?> eInterface:wrappedClass.getInterfaces())
				{
				ClassWrapper cwInterface = findByClass(eInterface);
				if(cwInterface==null) continue;
					
				/* this interface comes from parent ? */
				ClassWrapper parentClass= findByClass(superClass);
				if(parentClass==null) continue;
				for(Class<?> parentInterface:parentClass.getWrappedClass().getInterfaces())
					{
					if(parentInterface==eInterface)
						{
						eInterface=null;
						break;
						}
					}
				
				if(eInterface==null) continue;
				
				
				Link L=new Link(cw,cwInterface,
						(wrappedClass.isInterface()?Relation.SUPER:Relation.IMPLEMENTS));
				this.links.add(L);
				nextToBeProcessed.add(cwInterface);
				}
			
			if(usingClassesImplementingInterfaces && wrappedClass.isInterface())
				{
				for(ClassWrapper cw2:this.classes)
					{
					for(Class<?> eInterface:cw2.getWrappedClass().getInterfaces())
						{
						if(eInterface==wrappedClass)
							{
							Link L=new Link(cw2,cw,Relation.IMPLEMENTS);
							this.links.add(L);
							nextToBeProcessed.add(cw2);
							}
						}
					}
				}
			
			if(this.useMethodReturnType || this.useMethodArguments)
				{
				for(Method method:cw.getWrappedClass().getDeclaredMethods())
					{
					if(method.getName().contains("$")) continue;
					if(Modifier.isPrivate(method.getModifiers())) continue;
					for(int step=0;step<2;++step)
						{
						HashSet<Class<?>> classesInvolved1=new HashSet<Class<?>>();
						
						if(step==0 && this.useMethodReturnType)
							{
							classesInvolved1.add(method.getReturnType());
							}
						if(step==1 && this.useMethodArguments)
							{
							classesInvolved1.addAll(Arrays.asList(method.getParameterTypes()));
							}
						else
							{
							continue;
							}
						
						for(Class<?> clazz: classesInvolved1)
							{
							if(clazz.isArray())
								{
								clazz=clazz.getComponentType();
								}
							if(clazz.isPrimitive() || clazz==String.class) continue;
							
							if(clazz==Object.class) continue;
							if(clazz==Short.class) continue;
							if(clazz==Integer.class) continue;
							if(clazz==Long.class) continue;
							if(clazz==Byte.class) continue;
							if(clazz==Boolean.class) continue;
							if(clazz.getPackage()!=null)
								{
								if(clazz.getPackage().getName().startsWith("java.")) continue;
								if(clazz.getPackage().getName().startsWith("javax.")) continue;
								}
							ClassWrapper cw2=findByClass(clazz);
							if(cw2==null) continue;
							Link L=new Link(cw,cw2,
									step==0?Relation.RETURNS:Relation.ARGUMENT
									);
							L.getMethods().add((Modifier.isStatic(method.getModifiers())?"*":"")+method.getName());
							this.links.add(L);
							nextToBeProcessed.add(cw2);
							}
						}
					
					}
				}
			
			}
		
		if(usingDeclaredClasses)
			{
			Class<?> subclasses[];
			
			if(usePrivateDeclaredClasses)
				{
				subclasses=wrappedClass.getDeclaredClasses();
				}
			else
				{
				try
					{
					subclasses=wrappedClass.getClasses();
					}
				catch(Throwable err)
					{
					subclasses=new Class[0];
					}	
				}
			for(Class<?> d:subclasses)
				{
				ClassWrapper cw2= findByClass(d);
				if(cw2!=null)
					{
					this.links.add(new Link(cw,cw2,Relation.DECLARES));
					nextToBeProcessed.add(cw2);
					}
				}
			}
		
		for(ClassWrapper child: this.classes)
			{
			Class<?> parentClass3= child.getWrappedClass().getSuperclass();
			if(parentClass3==null) continue;
			
			if(parentClass3!=wrappedClass)
				{
				continue;
				}
			LOG.info("parent of "+child+" is "+parentClass3);
			ClassWrapper cw3= findByClass(parentClass3);
			if(cw3!=null)
				{
				Link L=new Link(child,cw,Relation.SUPER);
				this.links.add(L);
				nextToBeProcessed.add(child);
				}
			}
		for(ClassWrapper cw2:nextToBeProcessed)
			{
			recursive(cw2,distance+1);
			}
		}
	
	private void run(HashSet<String> setOfClasses) throws IOException
			{
			LOG.info("run for "+setOfClasses);
				
			ArrayList<URL> urls=new ArrayList<URL>();
			for(File f:this.files)
			 	{
				urls.add(f.toURI().toURL()); 
			 	}
			    
			/* setup class loaded */
		    URLClassLoader cl= new URLClassLoader(
		    		urls.toArray(new URL[urls.size()]),
		    		ClassLoader.getSystemClassLoader()
		    		);
		   
		    
		    //loop over each file
		    for(File f:this.files)
		    	{
		    	LOG.info("Scanning "+f);
		    	JarFile jf= new JarFile(f);
		    	Enumeration<JarEntry> e=jf.entries();
		    	//loop over each entry of this jar file
		    	while(e.hasMoreElements())
		    		{
		    		JarEntry je=e.nextElement();
		    		if(!je.getName().endsWith(".class")) continue;
		    		
		    		String className=je.getName();
		    		className=className.substring(0,className.length()-6);
		    		className=className.replace('/','.');
		    		int sub= className.indexOf('$');
		    		if(sub!=-1 && usingDeclaredClasses==false) continue;
		    		//ignore anonymous classes
		    		if(sub!=-1 && Character.isDigit(className.charAt(sub+1))) continue;
		    		
		    		if(jf==null) continue;
		    		try
			    		{
			    		Class<?> c=cl.loadClass(className);
			    		for(Filter<Class<?>> filter:this.discardClassFilters)
			    			{
			    			if(!filter.accept(c))
			    				{
			    				c=null;
			    				break;
			    				}
			    			}
			    		if(c==null) continue;
			    		//System.err.println(c.getName());
			    		classes.add(new ClassWrapper(c));
			    		}
		    		catch(IllegalAccessError err)
		    			{
		    			LOG.warning("#cannot access \""+className+"\" message:"+err.getMessage());
		    			}
		    		catch(NoClassDefFoundError err)
		    			{
		    			LOG.warning("#class def not found : \""+className+"\" message:"+err.getMessage());
		    			}
		    		catch(ClassNotFoundException err)
		    			{
		    			LOG.warning("#class not found : \""+className+"\" message:"+err.getMessage());
		    			}
		    		catch(java.lang.SecurityException err)
		    			{
		    			LOG.warning("#class not found : \""+className+"\" message:"+err.getMessage());
		    			}
		    		}
		    	jf.close();
		    	}
		    
		    for(String x: setOfClasses)
			    {
			    ClassWrapper cw=findByName( x );
			    if(cw==null)
			    	{
			    	System.err.println("Cannot find class "+x);
			    	continue;
			    	}
			    cw.userTarget=true;
			    recursive(cw,0);
			    }
		    cl.close();
			}
	
	private static final Set<String> COMMON_IGNORE=new HashSet<String>()
			{{{
			add("java.lang.Comparable");
			add("java.util.Comparator");
			add("java.lang.Enum");
			add("java.io.Serializable");
			add("java.io.Closeable");
			add("java.lang.Cloneable");
			add("java.lang.Throwable");
			add("java.lang.Exception");
			add("java.lang.RuntimeException");
			}}};
	
			
	private void usage()
		{
		System.err.println("Pierre Lindenbaum PhD. 2014");
		System.err.println(" -h this screen");
		System.err.println(" -cp <dir0:jar1:jar2:dir1:...> add a jar in the jar list. If directory, will add all the *ar files");
		System.err.println(" -r <regex> add a pattern of classes to be ignored. Can be used muliple times");
		System.err.println(" -R <package name> ignore the package starting with this string. Can be used muliple times");
		System.err.println(" -i ignore interfaces");
		System.err.println(" -p use *private* inner classes.");
		System.err.println(" -m ignore classes iMplementing interfaces");
		System.err.println(" -d ignore declared-classes (classes with $ in the name)");
		System.err.println(" -o <file> output file");
		System.err.println(" -L <level> Log Level. optional");
		System.err.println(" -G graphviz output");
		System.err.println(" -D dot output");
		System.err.println(" -x (int) max distance to classe(s) defined by user. Default: unlimited");
		System.err.println(" -C ignore common classes: "+COMMON_IGNORE.toString());
		System.err.println(" -M use methods return type");
		System.err.println(" -A use methods arguments");
		System.err.println("\n jar1 class-1  jar 2 jar 3 class-2 ... class-n");
		}
	
	private static class FilterIgnore
	implements Filter<Class<?>>
		{
		String name;
		FilterIgnore(String name)
			{
			this.name=name;
			}
		@Override
		public boolean accept(Class<?> data) {
			return !data.getName().equals(name);
			}
		}

	
	private static class FilterIgnorePackageStartingWith
		implements Filter<Class<?>>
		{
		String prefix;
		FilterIgnorePackageStartingWith(String prefix)
			{
			this.prefix=prefix;
			}
		@Override
		public boolean accept(Class<?> data) {
			return !data.getName().startsWith(prefix);
			}
		}
	
	private static class FilterIgnoreRegex
	implements Filter<Class<?>>
		{
		Pattern regex;
		FilterIgnoreRegex(Pattern regex)
			{
			this.regex=regex;
			}
		@Override
		public boolean accept(Class<?> data) {
			return !regex.matcher(data.getName()).matches();
			}
		}


	
	
	/** main loop */
	private void run(String[] args)
		{
		try {
			/** parse command line */
			int optind=0;
			File output=null;
		    while(optind<args.length)
				{
				if(args[optind].equals("-h"))
					{
					usage();
					return;
					}
				else if (args[optind].equals("-G"))
					{
					this.graphPrinter=new GexfPrinter();
					}
				else if (args[optind].equals("-p"))
					{
					this.usePrivateDeclaredClasses=true;
					}
				else if (args[optind].equals("-M"))
					{
					this.useMethodReturnType=true;
					}
				else if (args[optind].equals("-A"))
					{
					this.useMethodArguments=true;
					}
				else if (args[optind].equals("-D"))
					{
					this.graphPrinter=new DotGraphPrinter();
					}
				else if (args[optind].equals("-cp") && optind+1< args.length)
					{
					String tokens[]=args[++optind].split("[:]");
					for(String s:tokens)
						{
						s=s.trim();
						if(s.length()==0) continue;
						File file= new File(s);
						
						this.addFile(file);	
						}
					}
				else if (args[optind].equals("-L") && optind+1 < args.length)
					{
					LOG.setLevel(Level.parse(args[++optind]));
					}
				else if (args[optind].equals("-x") && optind+1 < args.length)
					{
					this.limitDistance=Integer.parseInt(args[++optind]);
					}
				else if (args[optind].equals("-r") && optind+1 < args.length)
					{
					this.discardClassFilters.add(new FilterIgnoreRegex(Pattern.compile(args[++optind])));
					}
				else if (args[optind].equals("-R") && optind+1 < args.length)
					{
					this.discardClassFilters.add(new FilterIgnorePackageStartingWith(args[++optind]));
					}
				else if (args[optind].equals("-C") )
					{
					for(String className:COMMON_IGNORE)
						this.discardClassFilters.add(new FilterIgnore(className));
					}
				else if (args[optind].equals("-o"))
					{
					output=new File(args[++optind]);
					}
				else if (args[optind].equals("-i"))
					{
					this.usingInterfaces=false;
					}
				else if (args[optind].equals("-d"))
					{
					this.usingDeclaredClasses=false;
					}
				else if (args[optind].equals("-m"))
					{
					this.usingClassesImplementingInterfaces=false;
					}
				else if (args[optind].equals("-p"))
					{
					this.usePrivateDeclaredClasses=true;
					}
				 else if (args[optind].equals("--"))
				     {
				     ++optind;
				     break;
				     }
				else if (args[optind].startsWith("-"))
				     {
				     System.err.println("bad argument " + args[optind]);
				     System.exit(-1);
				     }
				else
				     {
				     break;
				     }
				++optind;
				}
		    if(optind==args.length)
		    	{
		    	System.err.println("classes missing");
		    	usage();
		    	return;
		    	}
		    HashSet<String> setOfClasses=new HashSet<String>();
		    while(optind< args.length)
		    	{
		    	String filename=args[optind++];
		    	if(filename.endsWith(".jar"))
		    		{
		    		LOG.info("using all classes from "+filename);
		    		File archiveFile=new File(filename);
		    		this.addFile(archiveFile);	
		    		JarInputStream jarFile = new JarInputStream(new FileInputStream(archiveFile));
		    		JarEntry jarEntry;

    			     while(true) {
    			       jarEntry=jarFile.getNextJarEntry ();
    			       if(jarEntry == null){
    			        break;
    			       	}
    			       String entryName=jarEntry.getName();
    			       if(!entryName.endsWith(".class")) continue;
    			       entryName=entryName.substring(0,entryName.length()-6);//remove '.class'
    			       if(entryName.indexOf('-')!=-1) continue; 
    			       if(entryName.indexOf('$')!=-1) continue;
    			       entryName=entryName.replace("/", ".");
    			       setOfClasses.add(entryName);
    			     	}
    			     jarFile.close();
		    		}
		    	else 
			    	{
			    	String className=filename;	
			    	
			    	if(className.contains("/"))
			    		{	
			    		if(className.endsWith(".java"))
			    			{	
			    			className=className.substring(0,className.length()-5);
			    			}
			    		className=className.replace('/', '.');
			    		}
			    	setOfClasses.add(className);
			    	}
		    	}
		   this.run(setOfClasses);
			  LOG.info("COUNT(Classes) : "+this.classes.size());
			  LOG.info("COUNT(LINKS) : "+this.links.size());

			  
		    PrintStream out= System.out;
		    if(output!=null)
		    	{
		    	out= new PrintStream(output);
		    	}
		    graphPrinter.print(out);
		    out.flush();
		    if(output!=null) out.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public static void main(String[] args)
		{
		LOG.setLevel(Level.OFF);
		Java2Graph app=new Java2Graph();
		app.run(args);
		}
	
}