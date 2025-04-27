import Mathlib

noncomputable section

variable
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Given linear maps `a : E →L[ℝ] ℝ` and `b : F →L[ℝ] ℝ`, the tensor product `a ⊗ b` of these maps,
considered as a bilinear map `E →L[ℝ] F →L[ℝ] ℝ`. -/
def ContinuousLinearMap.tensor (a : E →L[ℝ] ℝ) (b : F →L[ℝ] ℝ) : E →L[ℝ] F →L[ℝ] ℝ :=
  let v : ℝ →L[ℝ] F →L[ℝ] ℝ := (ContinuousLinearMap.lsmul ℝ ℝ (E := F →L[ℝ] ℝ)).flip b
  ContinuousLinearMap.compL ℝ E _ _ v a

/-- The wedge product `a ∧ b`, i.e. `a ⊗ b - b ⊗ a`, of two linear maps `a : E →L[ℝ] ℝ` and
`b : E →L[ℝ] ℝ`. -/
def ContinuousLinearMap.wedge (a b : E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  a.tensor b - b.tensor a
