module

public import ExactJSON.Shapes
public import ExactJSON.Derive
meta import ExactJSON.Derive

@[expose] public section

namespace ExactJSON.Example

deriving instance ExactJSON.ToValue, ExactJSON.FromValue for Point
deriving instance ExactJSON.ToValue, ExactJSON.FromValue for Shape
deriving instance ExactJSON.ToValue, ExactJSON.FromValue for Envelope

end ExactJSON.Example
