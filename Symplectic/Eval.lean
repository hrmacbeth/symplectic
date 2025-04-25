import Mathlib.Geometry.Manifold.MFDeriv.Basic

open Manifold

noncomputable section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- For a function `f : M → F` on a manifold `M`, `eval X f` gives the derivative of the function
`f` in the direction of the tangent vector `X`. -/
def eval {x : M} (X : TangentSpace I x) (f : M → F) : F := mfderiv I 𝓘(𝕜, F) f x X
