import Mathlib

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
  closed : ∀ X Y Z, ∀ p,
    -- TODO fill in Z(ω(X,Y)) + .... here
    ω p (mlieBracket 𝓘(ℝ, E) X Y p) (Z p)
    - ω p (mlieBracket 𝓘(ℝ, E) X Z p) (Y p)
    + ω p (mlieBracket 𝓘(ℝ, E) Y Z p) (X p) = 0

theorem IsSymplecticForm.eval_swap (h : IsSymplecticForm ω) :
    ∀ p : M, ∀ X Y : (T[E]M) p, ω p X Y = - ω p Y X :=
  sorry
