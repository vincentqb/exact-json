module

public import ExactJSON.Shapes
public import ExactJSON.Derive
public import ExactJSON.Lawful
meta import ExactJSON.Derive

@[expose] public section

namespace ExactJSON.Example

deriving instance ExactJSON.ToValue, ExactJSON.FromValue, ExactJSON.LawfulValue for Point
deriving instance ExactJSON.ToValue, ExactJSON.FromValue, ExactJSON.LawfulValue for Shape
deriving instance ExactJSON.ToValue, ExactJSON.FromValue, ExactJSON.LawfulValue for Envelope

end ExactJSON.Example
