import Mathlib
import Symplectic.Eval

noncomputable section

open Manifold VectorField

notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable
  -- E a real Banach space
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

  -- M a smooth manifold modelled on E
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


-- Let `T[E]M` denote the tangent bundle of `M`
notation3 "T[" E "]" M => (TangentSpace 𝓘(ℝ, E) : M → Type)

-- Let `T*[E]M` denote the cotangent bundle of `M`
notation3 "T*[" E "]" M => Bundle.ContinuousLinearMap (RingHom.id ℝ) (T[E]M) (Bundle.Trivial M ℝ)

-- Let `T^2[E]M` denote the bundle of covariant 2-tensors on `M`
notation3 "T^2[" E "]" M => Bundle.ContinuousLinearMap (RingHom.id ℝ) (T[E]M) (T*[E]M)


-- Let η be a 1-form on `M`
-- i.e. a smooth section of the vector bundle Hom(TM, ℝ)
variable (η : Cₛ^∞⟮𝓘(ℝ, E); E →L[ℝ] ℝ, (T*[E]M)⟯)

-- Let ω be a 2-tensor on `M`
-- i.e. a smooth section of the vector bundle Hom(TM, Hom(TM, ℝ))
variable (ω : Cₛ^∞⟮𝓘(ℝ, E); E →L[ℝ] E →L[ℝ] ℝ, T^2[E]M⟯)


structure IsSymplecticForm : Prop where
  alternating : ∀ p : M, ∀ X : (T[E]M) p, ω p X X = 0
  nondegenerate : ∀ p : M, Function.Bijective (ω p : E → (E →L[ℝ] ℝ))
  closed : ∀ (X Y Z : Cₛ^∞⟮𝓘(ℝ, E); E, (T[E]M)⟯), ∀ p : M,
    eval (X p) (fun q ↦ ω q (Y q) (Z q))
    - eval (Y p) (fun q ↦ ω q (X q) (Z q))
    + eval (Z p) (fun q ↦ ω q (X q) (Y q))
    + ω p (mlieBracket _ X Y p) (Z p)
    - ω p (mlieBracket _ X Z p) (Y p)
    + ω p (mlieBracket _ Y Z p) (X p) = 0

theorem IsSymplecticForm.eval_swap (h : IsSymplecticForm ω) :
    ∀ p : M, ∀ X Y : (T[E]M) p, ω p X Y = - ω p Y X := by
  sorry

variable
  -- F a real Banach space
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- N a smooth manifold modelled on F
  {N : Type} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

variable (f : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, E) N M ∞)

/-- The pullback of a smooth 1-form `η` along a smooth map `f : N → M`. -/
def ContMDiffSection.pullback1 : Cₛ^∞⟮𝓘(ℝ, F); F →L[ℝ] ℝ, T*[F]N⟯ where
  toFun (x : N) := η (f x) ∘L mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) f x
  contMDiff_toFun := sorry

/-- The pullback of a smooth 2-tensor `ω` along a smooth map `f : N → M`. -/
def ContMDiffSection.pullback2 : Cₛ^∞⟮𝓘(ℝ, F); F →L[ℝ] F →L[ℝ] ℝ, T^2[F]N⟯ where
  toFun (x : N) :=
    have : (T*[E]M) (f x) →L[ℝ] (T*[F]N) x :=
      (ContinuousLinearMap.compL ℝ F E ℝ).flip (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) f x)
    this ∘L (ω (f x) ∘L mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) f x)
  contMDiff_toFun := sorry
