import Mathlib
import Symplectic.ContinuousLinearMap
import Symplectic.Eval

noncomputable section

open VectorField TopologicalSpace
open scoped Manifold Real

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

/-- A symplectic form on a manifold `M` is a 2-tensor which is alternating, nondegenerate and
closed. -/
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

variable {ω f} in
/-- If `f : N → M` is a smooth immersion, then the pullback of a symplectic form `ω` on `M` to `N`
is a symplectic form on `N`. -/
theorem IsSymplecticForm.pullback (h : IsSymplecticForm ω)
    (hf : ∀ p, Function.Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) f p)) :
    IsSymplecticForm (ω.pullback2 f) where
  alternating := sorry
  nondegenerate := sorry
  closed := sorry

/-- Given manifolds `N` and `M` equipped with 2-tensors `Ω`, `ω` respectively, a smooth map
`f : N → M` is a *symplectic map* if `ω` pulls back to `Ω`. -/
def ContMDiffMap.IsSymplecticMap
    (Ω : Cₛ^∞⟮𝓘(ℝ, F); F →L[ℝ] F →L[ℝ] ℝ, T^2[F]N⟯)
    (ω : Cₛ^∞⟮𝓘(ℝ, E); E →L[ℝ] E →L[ℝ] ℝ, T^2[E]M⟯) : Prop :=
  ω.pullback2 f = Ω

/-- The standard symplectic form on `ℝ^{Fin n × Fin 2}`. -/
def StdSymplecticForm (n : ℕ) :
    (EuclideanSpace ℝ (Fin n × Fin 2)) →L[ℝ] (EuclideanSpace ℝ (Fin n × Fin 2)) →L[ℝ] ℝ :=
  ∑ i, (EuclideanSpace.proj (i, 0)).wedge (EuclideanSpace.proj (i, 1))

/-- Given a bilinear map on a normed space `E`, the associated 2-tensor field on `E` considered as a
manifold. -/
def ContMDiffSection.constant2 (T : E →L[ℝ] E →L[ℝ] ℝ) :
    Cₛ^∞⟮𝓘(ℝ, E); E →L[ℝ] E →L[ℝ] ℝ, (T^2[E]E)⟯ where
  toFun (x : E) := T
  contMDiff_toFun := sorry

-- The standard symplectic form on `ℝ^{Fin n × Fin 2}`, considered as a 2-tensor on that manifold.
notation "ω[" n "]" => ContMDiffSection.constant2 (StdSymplecticForm n)

/-- The standard symplectic form on `ℝ^{Fin n × Fin 2}` is a symplectic form, in the sense of
satisfying the definition `IsSymplecticForm`. -/
theorem StdSymplecticForm.isSymplecticForm (n : ℕ) : IsSymplecticForm ω[n] where
  alternating := sorry
  nondegenerate := sorry
  closed := sorry

variable (E) in
/-- The inclusion map of an open set `U` in a manifold into that manifold, as a smooth map. -/
def ContMDiffMap.val (U : Opens M) : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, E) U M ∞ where
  val := Subtype.val
  property := contMDiff_subtype_val

/-- The restriction of a smooth 1-form `η` on `M` to an open set `U`. -/
def ContMDiffSection.restrict1 (U : Opens M) : Cₛ^∞⟮𝓘(ℝ, E); E →L[ℝ] ℝ, T*[E]U⟯ :=
  η.pullback1 (ContMDiffMap.val E U)

/-- The restriction of a smooth 2-tensor `ω` on `M` to an open set `U`. -/
def ContMDiffSection.restrict2 (U : Opens M) : Cₛ^∞⟮𝓘(ℝ, E); E →L[ℝ] E →L[ℝ] ℝ, T^2[E]U⟯ :=
  ω.pullback2 (ContMDiffMap.val E U)

variable {ω} in
/-- The restriction of a symplectic form `ω` on `M` to an open set `U` is a symplectic form on `U`.
-/
theorem IsSymplecticForm.restrict (h : IsSymplecticForm ω) (U : Opens M) :
    IsSymplecticForm (ω.restrict2 U) :=
  h.pullback sorry

/-- The symplectic ball `π * (x₀ ^ 2 + y₀ ^ 2 + x₁ ^ 2 + ...) < R` in `ℝ^{Fin n × Fin 2}`. -/
def SymplecticBall (n : ℕ) (R : ℝ) : Opens (EuclideanSpace ℝ (Fin n × Fin 2)) where
  carrier := { p | π * ∑ i, p i ^ 2 < R }
  is_open' := sorry

/-- The symplectic cylinder `π * (x₀ ^ 2 + y₀ ^ 2) < R` in `ℝ^{Fin n × Fin 2}`. -/
def SymplecticCylinder (n : ℕ) [NeZero n] (R : ℝ) : Opens (EuclideanSpace ℝ (Fin n × Fin 2)) where
  carrier := { p | π * ∑ i, p (0, i) ^ 2 < R }
  is_open' := sorry

/-- **Gromov's nonsqueezing theorem**: if a smooth map `f` from the symplectic `r`-ball to the
symplectic `R`-cylinder preserves the standard symplectic form, then `r ≤ R`. -/
theorem gromovNonsqueezing {n : ℕ} [NeZero n] {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {f : ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n × Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n × Fin 2))
      (SymplecticBall n r) (SymplecticCylinder n R) ∞}
    (hf : f.IsSymplecticMap (ω[n].restrict2 (SymplecticBall n r))
      (ω[n].restrict2 (SymplecticCylinder n R))) :
    r ≤ R := by
  sorry
