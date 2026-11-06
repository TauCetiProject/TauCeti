/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

/-!
# Almost complex structures of finite regularity

`TauCeti.ContMDiffAlmostComplexStructure I n M` is a `Cⁿ` section of the tangent
endomorphism bundle whose square is minus the identity in every fibre. The regularity
parameter `n : ℕ∞` includes continuous structures and the smooth endpoint.

`TauCeti.ContMDiffAlmostComplexStructure.smoothEquiv` identifies the infinite-regularity
carrier with the existing `SmoothAlmostComplexStructure`. Forgetting regularity preserves the
underlying section and commutes with evaluation. Applying a structure to a vector field along a
map preserves every regularity order at most that of the structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (almost complex structures) and Appendix B (finite regularity).
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A `Cⁿ` tangent endomorphism whose square is minus the identity in every fibre.
The ambient manifold is smooth; the structure need only have regularity `n`. -/
structure ContMDiffAlmostComplexStructure (I : ModelWithCorners ℝ E H) (n : ℕ∞) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- The underlying endomorphism section with its specified regularity. -/
  toEndomorphism :
    ContMDiffSection I (E →L[ℝ] E) n
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
  /-- The defining identity holds at every point, not just on a chosen open set. -/
  square_neg : ∀ x, (toEndomorphism x).comp (toEndomorphism x) = -ContinuousLinearMap.id ℝ _

namespace ContMDiffAlmostComplexStructure

variable {n m l : ℕ∞} {J K : ContMDiffAlmostComplexStructure I n M}

/-- The endomorphism section determines the almost complex structure. -/
theorem toEndomorphism_injective : Function.Injective
    (toEndomorphism : ContMDiffAlmostComplexStructure I n M →
      ContMDiffSection I (E →L[ℝ] E) n
        (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)) := by
  rintro ⟨J, hJ⟩ ⟨K, hK⟩ h
  subst h
  rfl

/-- Evaluate the structure at a point and then at a tangent vector. -/
instance : CoeFun (ContMDiffAlmostComplexStructure I n M) fun _ =>
    (x : M) → TangentSpace I x → TangentSpace I x :=
  ⟨fun J x ↦ J.toEndomorphism x⟩

/-- The underlying real-linear almost complex structure on a tangent fibre. -/
def almostComplexStructureAt (J : ContMDiffAlmostComplexStructure I n M) (x : M) :
    AlmostComplexStructure (TangentSpace I x) where
  toLinearMap := (J.toEndomorphism x).toLinearMap
  square_neg := by
    ext v
    exact congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace I x ↦ A v) (J.square_neg x)

@[simp]
theorem almostComplexStructureAt_toLinearMap (J : ContMDiffAlmostComplexStructure I n M)
    (x : M) :
    (J.almostComplexStructureAt x).toLinearMap = (J.toEndomorphism x).toLinearMap := (rfl)

/-- Evaluating the fibrewise structure agrees with evaluating the bundled section. -/
theorem almostComplexStructureAt_apply (J : ContMDiffAlmostComplexStructure I n M) (x : M)
    (v : TangentSpace I x) : J.almostComplexStructureAt x v = J x v := (rfl)

/-- Applying the structure twice negates a tangent vector. -/
@[simp]
theorem apply_apply (J : ContMDiffAlmostComplexStructure I n M) (x : M)
    (v : TangentSpace I x) : J x (J x v) = -v :=
  (J.almostComplexStructureAt x).apply_apply v

/-- Each fibrewise endomorphism is injective. -/
theorem injective (J : ContMDiffAlmostComplexStructure I n M) (x : M) :
    Function.Injective (J x) := (J.almostComplexStructureAt x).injective

/-- Each fibrewise endomorphism is surjective. -/
theorem surjective (J : ContMDiffAlmostComplexStructure I n M) (x : M) :
    Function.Surjective (J x) := (J.almostComplexStructureAt x).surjective

/-- Equality is detected on tangent vectors. -/
@[ext]
theorem ext (h : ∀ (x : M) (v : TangentSpace I x), J x v = K x v) : J = K := by
  apply toEndomorphism_injective
  ext x v
  exact h x v

/-- Forget higher regularity without changing any fibrewise endomorphism. -/
def ofLE (J : ContMDiffAlmostComplexStructure I n M) (h : m ≤ n) :
    ContMDiffAlmostComplexStructure I m M where
  toEndomorphism := ⟨J.toEndomorphism, J.toEndomorphism.contMDiff.of_le (by exact_mod_cast h)⟩
  square_neg := J.square_neg

@[simp]
theorem ofLE_toEndomorphism_apply (J : ContMDiffAlmostComplexStructure I n M) (h : m ≤ n)
    (x : M) : (J.ofLE h).toEndomorphism x = J.toEndomorphism x := (rfl)

/-- Forgetting regularity leaves the action on tangent vectors unchanged. -/
theorem ofLE_apply (J : ContMDiffAlmostComplexStructure I n M) (h : m ≤ n) (x : M)
    (v : TangentSpace I x) : J.ofLE h x v = J x v := (rfl)

@[simp]
theorem ofLE_refl (J : ContMDiffAlmostComplexStructure I n M) : J.ofLE le_rfl = J := by
  ext x v
  rfl

@[simp]
theorem ofLE_ofLE (J : ContMDiffAlmostComplexStructure I n M) (h : m ≤ n) (h' : l ≤ m) :
    (J.ofLE h).ofLE h' = J.ofLE (h'.trans h) := by
  ext x v
  rfl

/-- Regularity forgetting is injective because it retains the entire section. -/
theorem ofLE_injective (h : m ≤ n) :
    Function.Injective (fun J : ContMDiffAlmostComplexStructure I n M ↦ J.ofLE h) := by
  intro J K hJK
  ext x v
  exact congrArg (fun L : ContMDiffAlmostComplexStructure I m M ↦ L x v) hJK

/-- At infinite regularity, retain the existing smooth almost complex structure carrier. -/
def toSmooth (J : ContMDiffAlmostComplexStructure I ⊤ M) : SmoothAlmostComplexStructure I M where
  toEndomorphism := J.toEndomorphism
  square_neg := J.square_neg

@[simp]
theorem toSmooth_toEndomorphism (J : ContMDiffAlmostComplexStructure I ⊤ M) :
    J.toSmooth.toEndomorphism = J.toEndomorphism := (rfl)

end ContMDiffAlmostComplexStructure

namespace SmoothAlmostComplexStructure

/-- View a smooth structure at any specified regularity. -/
def toContMDiff (J : SmoothAlmostComplexStructure I M) (n : ℕ∞) :
    ContMDiffAlmostComplexStructure I n M where
  toEndomorphism := ⟨J.toEndomorphism, J.toEndomorphism.contMDiff.of_le (by simp)⟩
  square_neg := J.square_neg

@[simp]
theorem toContMDiff_toEndomorphism_apply (J : SmoothAlmostComplexStructure I M) (n : ℕ∞)
    (x : M) : (J.toContMDiff n).toEndomorphism x = J.toEndomorphism x := (rfl)

/-- Changing the regularity of a smooth structure leaves its pointwise action unchanged. -/
theorem toContMDiff_apply (J : SmoothAlmostComplexStructure I M) (n : ℕ∞) (x : M)
    (v : TangentSpace I x) : J.toContMDiff n x v = J x v := (rfl)

@[simp]
theorem toContMDiff_ofLE (J : SmoothAlmostComplexStructure I M) {m n : ℕ∞} (h : m ≤ n) :
    (J.toContMDiff n).ofLE h = J.toContMDiff m := by
  ext x v
  rfl

@[simp]
theorem toContMDiff_toSmooth (J : SmoothAlmostComplexStructure I M) :
    (J.toContMDiff ⊤).toSmooth = J := by
  ext x v
  rfl

end SmoothAlmostComplexStructure

namespace ContMDiffAlmostComplexStructure

variable {n m : ℕ∞}

@[simp]
theorem toSmooth_toContMDiff (J : ContMDiffAlmostComplexStructure I ⊤ M) :
    J.toSmooth.toContMDiff ⊤ = J := by
  ext x v
  rfl

/-- The infinite-regularity carrier is equivalent to the native smooth carrier. -/
def smoothEquiv : ContMDiffAlmostComplexStructure I ⊤ M ≃ SmoothAlmostComplexStructure I M where
  toFun := toSmooth
  invFun := fun J ↦ J.toContMDiff ⊤
  left_inv := toSmooth_toContMDiff
  right_inv := SmoothAlmostComplexStructure.toContMDiff_toSmooth

@[simp]
theorem smoothEquiv_apply (J : ContMDiffAlmostComplexStructure I ⊤ M) :
    smoothEquiv J = J.toSmooth := (rfl)

@[simp]
theorem smoothEquiv_symm_apply (J : SmoothAlmostComplexStructure I M) :
    smoothEquiv.symm J = J.toContMDiff ⊤ := (rfl)

/-- Negation preserves the specified regularity and the square identity. -/
def neg (J : ContMDiffAlmostComplexStructure I n M) : ContMDiffAlmostComplexStructure I n M where
  toEndomorphism := -J.toEndomorphism
  square_neg := by
    intro x
    ext v
    simp

instance : Neg (ContMDiffAlmostComplexStructure I n M) := ⟨neg⟩

@[simp]
theorem neg_toEndomorphism (J : ContMDiffAlmostComplexStructure I n M) :
    (-J).toEndomorphism = -J.toEndomorphism := (rfl)

@[simp]
theorem neg_neg (J : ContMDiffAlmostComplexStructure I n M) : -(-J) = J := by
  ext x v
  simp

@[simp]
theorem ofLE_neg (J : ContMDiffAlmostComplexStructure I n M) (h : m ≤ n) :
    (-J).ofLE h = -(J.ofLE h) := by
  ext x v
  rfl

/-- A continuous linear complex structure defines a constant structure at every regularity. -/
def const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ∞) (Jc : V →L[ℝ] V) (hJc : ∀ v, Jc (Jc v) = -v) :
    ContMDiffAlmostComplexStructure (modelWithCornersSelf ℝ V) n V :=
  (SmoothAlmostComplexStructure.const Jc hJc).toContMDiff n

@[simp]
theorem const_toEndomorphism_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ∞) (Jc : V →L[ℝ] V) (hJc : ∀ v, Jc (Jc v) = -v) (x : V) :
    (const n Jc hJc).toEndomorphism x = Jc := by
  exact SmoothAlmostComplexStructure.const_toEndomorphism_apply Jc hJc x

section ModelSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A `Cⁿ` field of continuous linear maps squaring to minus the identity defines a `Cⁿ`
almost complex structure on the model manifold. The field may depend on the base point. -/
def ofModel (A : V → V →L[ℝ] V) (hA : ContDiff ℝ n A)
    (hAA : ∀ x v, A x (A x v) = -v) :
    ContMDiffAlmostComplexStructure (modelWithCornersSelf ℝ V) n V where
  toEndomorphism := ⟨A, by
    intro x
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [inCoordinates_tangent_bundle_core_model_space] using hA.contMDiff x⟩
  square_neg x := by
    ext v
    exact hAA x v

@[simp]
theorem ofModel_toEndomorphism_apply (A : V → V →L[ℝ] V) (hA : ContDiff ℝ n A)
    (hAA : ∀ x v, A x (A x v) = -v) (x : V) :
    (ofModel A hA hAA).toEndomorphism x = A x := (rfl)

/-- On a model manifold, the endomorphism field of a `Cⁿ` structure is a `Cⁿ` map of
normed spaces. This is the converse to `ofModel`. -/
theorem contDiff_toEndomorphism
    (J : ContMDiffAlmostComplexStructure (modelWithCornersSelf ℝ V) n V) :
    ContDiff ℝ n (show V → V →L[ℝ] V from fun x ↦ J.toEndomorphism x) := by
  rw [← contMDiff_iff_contDiff]
  intro x
  have h := ((contMDiffAt_hom_bundle _).1 (J.toEndomorphism.contMDiff x)).2
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  exact (inCoordinates_tangent_bundle_core_model_space
    (I := modelWithCornersSelf ℝ V) (I' := modelWithCornersSelf ℝ V) x y x y
    (J.toEndomorphism y)).symm

end ModelSpace

/-- Applying a `Cⁿ` structure to a `Cᵐ` vector field along a `Cᵐ` map preserves regularity
whenever `m ≤ n`. This includes `m = 0`. -/
theorem contMDiff_apply {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N]
    (J : ContMDiffAlmostComplexStructure I n M) (hmn : m ≤ n)
    {b : N → M} (hb : ContMDiff I' I m b) {V : ∀ y : N, TangentSpace I (b y)}
    (hV : ContMDiff I' I.tangent m (fun y ↦ TotalSpace.mk' E (b y) (V y))) :
    ContMDiff I' I.tangent m (fun y ↦ TotalSpace.mk' E (b y) (J (b y) (V y))) :=
  (((J.ofLE hmn).toEndomorphism.contMDiff).comp hb).clm_bundle_apply hV

end ContMDiffAlmostComplexStructure

end TauCeti
