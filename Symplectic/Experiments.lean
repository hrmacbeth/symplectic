import Mathlib

open Manifold

notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable
  -- E a real Banach space
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

  -- M a smooth manifold modelled on E
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


/-! ### Trivial bundle -/

-- trivial bundle ℝ
#check Bundle.Trivial M ℝ

#synth VectorBundle ℝ ℝ (Bundle.Trivial M ℝ)

#synth ContMDiffVectorBundle ∞ ℝ (Bundle.Trivial M ℝ) 𝓘(ℝ, E)

/-! ### Tangent bundle -/

-- Let `T[E]M` denote the tangent bundle of `M`
notation3 "T[" E "]" M => (TangentSpace 𝓘(ℝ, E) : M → Type)

-- the tangent bundle is a vector bundle
#synth VectorBundle ℝ E (T[E]M)

-- in fact a smooth vector bundle
#synth ContMDiffVectorBundle ∞ E (T[E]M) 𝓘(ℝ, E)

/-! ### Cotangent bundle -/

-- Hom-bundle: bundle of linear maps from $TM$ to $ℝ$
-- i.e. cotangent bundle!
#check Bundle.ContinuousLinearMap (RingHom.id ℝ) (T[E]M) (Bundle.Trivial M ℝ)

-- Let `T*[E]M` denote the cotangent bundle of `M`
notation3 "T*[" E "]" M => Bundle.ContinuousLinearMap (RingHom.id ℝ) (T[E]M) (Bundle.Trivial M ℝ)

-- the cotangent bundle is a vector bundle
#synth VectorBundle ℝ (E →L[ℝ] ℝ) (T*[E]M)

-- one more check: *smooth* vector bundle
#synth ContMDiffVectorBundle ∞ (E →L[ℝ] ℝ) (T*[E]M) 𝓘(ℝ, E)

-- Let η be a 1-form on `M`
-- i.e. a smooth section of the vector bundle Hom(TM, ℝ)
variable (η : Cₛ^∞⟮𝓘(ℝ, E); E →L[ℝ] ℝ, (T*[E]M)⟯)

#check η

/-! ### Bundle of 2-tensors -/

-- Let `T^2[E]M` denote the bundle of covariant 2-tensors on `M`
notation3 "T^2[" E "]" M => Bundle.ContinuousLinearMap (RingHom.id ℝ) (T[E]M) (T*[E]M)

-- Let ω be a 2-tensor on `M`
-- i.e. a smooth section of the vector bundle Hom(TM, Hom(TM, ℝ))
variable (ω : Cₛ^∞⟮𝓘(ℝ, E); E →L[ℝ] E →L[ℝ] ℝ, (T^2[E]M)⟯)

#check ω
