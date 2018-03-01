open System.IO
open System.Xml
open System.Text.RegularExpressions
open System.Text
open System

//
// Document model
//

type MemberType =
    | Namespace
    | Type
    | Method
    | Property
    | Field
    | Event
    | Unrecognized
    
type DescriptionNode = { Name: string; Description: string option }
type NameReferenceNode = { Name: string }
type ReferenceNode = { Reference: string; Description: string option }

type TextNode =
    | Paragraph of TextNode list
    | Code of string
    | InlineCode of string
    | TypeParamRef of NameReferenceNode
    | ParamRef of NameReferenceNode
    | See of ReferenceNode
    | Text of string

type MemberNode =
    | Summary of TextNode list
    | Remarks of TextNode list
    | Example of TextNode list
    | Value of TextNode list
    | Returns of TextNode list
    | TypeParam of DescriptionNode
    | Param of DescriptionNode
    | Exception of ReferenceNode
    | OtherMember of string

type Member = { Id: string; Name: string; Type: MemberType; Nodes: MemberNode list }

type SimpleMember = { Id: string; FullName: string; Name: string; Type: MemberType; Description: MemberNode list }
type MethodMember =
    {
        Id: string
        FullName: string
        Name: string
        Description: MemberNode list
        GenericParameters: Map<string, DescriptionNode>
        Parameters: DescriptionNode list
        ParametersString: string
    }
type TypeMember =
    {
        Id: string
        FullName: string
        Name: string
        Description: MemberNode list
        GenericParameters: Map<string, DescriptionNode>
        Methods: MethodMember list
        Properties: SimpleMember list
        Fields: SimpleMember list
        Events: SimpleMember list
    }

type AssemblyDescription = { Name: string; Description: string option }

type Document =
    {
        Assembly: AssemblyDescription
        Types: TypeMember list
    }

//
// XML parsing
//

let tryGetAttribute (node: XmlNode) (name: string) =
    match node.Attributes.[name] with
    | null -> Option.None
    | attr -> Some attr.Value

let getNodeType (nodeName: string) =
    match nodeName.Substring(0, 2) with
    | "N:" -> MemberType.Namespace
    | "T:" -> MemberType.Type
    | "F:" -> MemberType.Field
    | "P:" -> MemberType.Property
    | "M:" -> MemberType.Method
    | "E:" -> MemberType.Event
    | _    -> MemberType.Unrecognized

let rec parseTextNode (ns: string) (node: XmlNode) =
    let tryCreateNode attr f =
        tryGetAttribute node attr
        |> Option.map f
        |> Option.defaultValue (Text node.InnerText)
    let trimText str =
        if System.String.IsNullOrWhiteSpace(str) then "" else str.Trim().Replace("\r\n", " ").Replace("\r", " ").Replace("\n", " ")
    let getPrettyName (str: string) =
        str.Substring(2).Replace(ns + ".", "")

    match node.Name.ToLower() with
    | "para" -> Paragraph [for child in node.ChildNodes do yield parseTextNode ns child]
    | "code" -> Code node.InnerText
    | "c" -> InlineCode node.InnerText
    | "see" -> tryCreateNode "cref" (fun cref -> See { Reference=cref; Description=Some (getPrettyName cref) })
    | "typeparamref" -> tryCreateNode "name" (fun name -> TypeParamRef { Name=name })
    | "paramref" -> tryCreateNode "name" (fun name -> ParamRef { Name=name })
    | _ -> Text (trimText node.InnerText)

let parseMemberNode (ns: string) (node: XmlNode) =
    let tryCreateNode attr f =
        tryGetAttribute node attr
        |> Option.map f
        |> Option.defaultValue (OtherMember node.InnerText)

    match node.Name.ToLower() with
    | "summary" -> Summary [for child in node.ChildNodes do yield parseTextNode ns child]
    | "remarks" -> Remarks [for child in node.ChildNodes do yield parseTextNode ns child]
    | "example" -> Example [for child in node.ChildNodes do yield parseTextNode ns child]
    | "value" -> Value [for child in node.ChildNodes do yield parseTextNode ns child]
    | "typeparam" -> tryCreateNode "name" (fun name -> TypeParam { Name=name; Description=Option.ofObj node.InnerText })
    | "param" -> tryCreateNode "name" (fun name -> Param { Name=name; Description=Option.ofObj node.InnerText })
    | "exception" -> tryCreateNode "cref" (fun cref -> Exception { Reference=cref; Description=Option.ofObj node.InnerText })
    | "returns" -> Returns [for child in node.ChildNodes do yield parseTextNode ns child]
    | _ -> OtherMember node.InnerText

let getMember (ns: string) (node: XmlNode) =
    let createMember n =
        {
            Type=getNodeType n
            Name=n.Substring(2)
            Id=n
            Nodes=[for x in node.ChildNodes do yield parseMemberNode ns x]
        }
    tryGetAttribute node "name"
    |> Option.map createMember

let getMethodParameters nodes =
    nodes
    |> Seq.choose (function | Param desc -> Some desc | _ -> None)
    |> Seq.toList

let getTypeParameters prefix nodes =
    nodes
    |> Seq.choose (function | TypeParam desc -> Some desc | _ -> None)
    |> Seq.mapi (fun i t -> sprintf "%s%i" prefix i, t)
    |> Map.ofSeq

let getMethod (typeGenericParams: Map<string, DescriptionNode>) (mem: Member) =
    let replaceTokens tokens str =
        tokens |> Map.fold (fun (s: string) (key: string) (desc: DescriptionNode) -> s.Replace(key, desc.Name)) str
    let r = Regex("\\.(?<name>\\w+)(``(\\d+))?(?<params>(\\(.*\\))|$)", RegexOptions.Compiled)
    let m = r.Match(mem.Name)
    let genericParams = getTypeParameters "``" mem.Nodes
    let paramsString = m.Groups.["params"].Value |> replaceTokens genericParams |> replaceTokens typeGenericParams
    {
        Id=mem.Id
        FullName=mem.Name
        Name=m.Groups.["name"].Value
        GenericParameters=genericParams
        Parameters=getMethodParameters mem.Nodes
        ParametersString=paramsString
        Description=mem.Nodes
    }

let getSimpleMember memberType (mem: Member) =
    let r = Regex("\\.(?<name>\\w+)$", RegexOptions.Compiled)
    let m = r.Match(mem.Name)
    {
        Id=mem.Id
        FullName=mem.Name
        Name=m.Groups.["name"].Value
        Type=memberType
        Description=mem.Nodes
    }
    
let formatGenericParams (typeParams: Map<string, DescriptionNode>) (methodParams: Map<string, DescriptionNode> option) (name: string) =
    let name' =
        methodParams
        |> Option.map (fun ps -> name.Replace(sprintf "``%i" ps.Count, sprintf "&lt;%s&gt;" (String.concat "," (ps |> Map.toSeq |> Seq.map (fun (_, v) -> v.Name)))))
        |> Option.defaultValue name
    name'.Replace(sprintf "`%i" typeParams.Count, sprintf "&lt;%s&gt;" (String.concat "," (typeParams |> Map.toSeq |> Seq.map (fun (_, v) -> v.Name))))

let getType (t: Member) (methods: Member seq option) (properties: Member seq option) (fields: Member seq option) (events: Member seq option) =
    let genericParams = getTypeParameters "`" t.Nodes
    { 
        Id=t.Id
        FullName=t.Name
        Name=formatGenericParams genericParams None t.Name
        Description=t.Nodes
        GenericParameters=genericParams
        Methods=(defaultArg methods Seq.empty) |> Seq.map (fun m -> getMethod genericParams m) |> Seq.toList
        Properties=(defaultArg properties Seq.empty) |> Seq.map (fun m -> getSimpleMember MemberType.Property m) |> Seq.toList
        Fields=(defaultArg fields Seq.empty) |> Seq.map (fun m -> getSimpleMember MemberType.Field m) |> Seq.toList
        Events=(defaultArg events Seq.empty) |> Seq.map (fun m -> getSimpleMember MemberType.Event m) |> Seq.toList
    }

let getTypeMembers typeName members : Member seq option =
    members |> Option.map (Seq.filter (fun m -> m.Name.StartsWith(typeName + ".")))

let parseDocument (document: XmlDocument) (ns: string) =
    let doc = document.SelectSingleNode("doc")
    let assemblyNode = doc.SelectSingleNode("assembly")
    let assemblyName = assemblyNode.SelectSingleNode("name").InnerText
    let memberNodes = doc.SelectNodes("members/member")
    let members = [for node in memberNodes do yield getMember ns node] |> Seq.choose id |> Seq.groupBy (fun m -> m.Type) |> Map.ofSeq
    let methods = members.TryFind MemberType.Method
    let properties = members.TryFind MemberType.Property
    let fields = members.TryFind MemberType.Field
    let events = members.TryFind MemberType.Event
    let types =
        members.[MemberType.Type]
        |> Seq.map (fun t -> getType
                                t
                                (methods |> getTypeMembers t.Name)
                                (properties |> getTypeMembers t.Name)
                                (fields |> getTypeMembers t.Name)
                                (events |> getTypeMembers t.Name))
    {
        Assembly={ Name=assemblyName; Description=None }
        Types=types |> List.ofSeq
    }

//
// Convert to markdown
//

let createMarkdown doc =
    let escape (str: string) =
        str.Replace("`", "\\`")
    let urlEncode (str: string) =
        System.Web.HttpUtility.UrlEncode(str)

    let rec node2txt (t: TypeMember) (m: MethodMember option) = function
        | Paragraph ns -> Environment.NewLine + (String.concat "" (List.map (node2txt t m) ns)) + Environment.NewLine
        | Code c -> c // TODO
        | InlineCode c -> sprintf "`%s`" c
        | TypeParamRef r -> sprintf "[<c>%s</c>](#%s)" r.Name r.Name
        | ParamRef r -> sprintf "[<c>%s</c>](#%s)" r.Name r.Name
        | See r -> sprintf "[<c>%s</c>](#%s)" (escape (defaultArg r.Description (r.Reference |> formatGenericParams t.GenericParameters (m |> Option.map (fun x -> x.GenericParameters))))) (urlEncode r.Reference)
        | Text t -> t

    let nodes2txt prefix t m ns = (String.concat " " (prefix :: (ns |> List.map (node2txt t m)))) + Environment.NewLine

    let convertDescription t m desc =
        desc |> List.map (function
            | Summary s -> nodes2txt "" t m s
            | Remarks s -> nodes2txt "*Remarks:*" t m s
            | Example s -> nodes2txt "*Example:*" t m s
            | Returns s -> nodes2txt "*Returns:*" t m s
            | Value s -> nodes2txt "*Value:*" t m s
            | _ -> "")
    
    let addGenericParameters (builder: StringBuilder) header (ps: Map<string, DescriptionNode>) =
        if ps.IsEmpty
        then ()
        else builder
                .AppendLine(sprintf "%s" header)
                .AppendLine("|Name|Description|")
                .AppendLine("|---|---|") |> ignore
        ps |> Map.iter (fun _ p -> builder.AppendLine(sprintf "|%s|%s|" p.Name (defaultArg p.Description "")) |> ignore)
        builder.AppendLine() |> ignore
    
    let addMethodParameters (builder: StringBuilder) (ps: DescriptionNode list) =
        if ps.IsEmpty
        then ()
        else builder
                .AppendLine("##### Parameters")
                .AppendLine("|Name|Description|")
                .AppendLine("|---|---|") |> ignore
        ps |> List.iter (fun p -> builder.AppendLine(sprintf "|%s|%s|" p.Name (defaultArg p.Description "")) |> ignore)
        builder.AppendLine() |> ignore

    let addMethod (builder: StringBuilder) (t: TypeMember) (m: MethodMember) =
        builder.AppendLine(sprintf "#### Method <a name=\"%s\"><code>%s</code></a>" (urlEncode m.Id) m.Name) |> ignore
        m.Description |> convertDescription t (Some m) |> List.iter (builder.AppendLine >> ignore)
        builder.AppendLine() |> ignore
        addGenericParameters builder "##### Generic parameters" m.GenericParameters
        addMethodParameters builder m.Parameters
    
    let addElement (builder: StringBuilder) (t: TypeMember) (m: SimpleMember) =
        let memberName =
            match m.Type with
            | Property -> "Property"
            | Field -> "Field"
            | Event -> "Event"
            | other -> other.ToString()
        builder.AppendLine(sprintf "#### %s <a name=\"%s\"><code>%s</code></a>" memberName (urlEncode m.Id) m.Name) |> ignore
        m.Description |> convertDescription t None |> List.iter (builder.AppendLine >> ignore)
        builder.AppendLine() |> ignore

    let addType (builder: StringBuilder) (t: TypeMember) =
        builder.AppendLine(sprintf "## Type <a name=\"%s\"><code>%s</code></a>" (urlEncode t.Id) t.Name) |> ignore
        t.Description
        |> convertDescription t None
        |> List.iter (builder.AppendLine >> ignore)

        // Generic parameters
        addGenericParameters builder "### Generic parameters" t.GenericParameters

        // Methods
        match t.Methods.IsEmpty with
        | false ->
            builder.AppendLine("### Methods") |> ignore
            t.Methods |> List.iter (addMethod builder t)
            builder.AppendLine() |> ignore
        | _ -> ()
        
        // Properties
        match t.Properties.IsEmpty with
        | false ->
            builder.AppendLine("### Properties") |> ignore
            t.Properties |> List.iter (addElement builder t)
            builder.AppendLine() |> ignore
        | _ -> ()

        // Fields
        match t.Fields.IsEmpty with
        | false ->
            builder.AppendLine("### Fields") |> ignore
            t.Fields |> List.iter (addElement builder t)
            builder.AppendLine() |> ignore
        | _ -> ()

        // Events
        match t.Events.IsEmpty with
        | false ->
            builder.AppendLine("### Events") |> ignore
            t.Events |> List.iter (addElement builder t)
            builder.AppendLine() |> ignore
        | _ -> ()                

    let builder = StringBuilder()
    builder
        .AppendLine(sprintf "# Assembly <code>%s</code>" doc.Assembly.Name)
        .AppendLine(sprintf "%s" (defaultArg doc.Assembly.Description "")) |> ignore
    for t in doc.Types do addType builder t
    builder.ToString()

let parse name ns =
    let xmldoc = new XmlDocument()
    xmldoc.LoadXml(File.ReadAllText(name))
    let doc = parseDocument xmldoc ns
    let markdown = createMarkdown doc
    printf "%A" markdown
    File.WriteAllText(name + ".md", markdown)

[<EntryPoint>]
let main argv =
    let name = argv.[0]
    let ns = argv.[1]
    parse name ns
    0 // return an integer exit code
