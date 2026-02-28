namespace de4dot.code {
    public sealed class StringDecrypterMethodInfo {
        public StringDecrypterMethodInfo(int methodToken, bool requireGenericString) {
            MethodToken = methodToken;
            RequireGenericString = requireGenericString;
        }

        public int MethodToken { get; }
        public bool RequireGenericString { get; }
    }
}