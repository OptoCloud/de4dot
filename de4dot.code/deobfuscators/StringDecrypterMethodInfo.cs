namespace de4dot.code {
    /// <summary>
    /// Identifies a string decrypter method by its metadata token. When RequireGenericString
    /// is true, the method is a generic method (e.g., !!0 Method&lt;T&gt;(int32)) that must be
    /// instantiated as Method&lt;string&gt; before invocation. This is used by .NET Reactor v6.x
    /// generic constant decrypters.
    /// </summary>
    public sealed class StringDecrypterMethodInfo {
        public StringDecrypterMethodInfo(int methodToken, bool requireGenericString) {
            MethodToken = methodToken;
            RequireGenericString = requireGenericString;
        }

        public int MethodToken { get; }
        public bool RequireGenericString { get; }
    }
}