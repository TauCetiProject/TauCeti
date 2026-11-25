/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.StrictHopfAlgebroid
public import TauCeti.RingTheory.GradedAlgebra.Polynomial
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The even homological grading of the strict Weierstrass Hopf algebroid

Both `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and `A[r, s, t]` carry nonnegative `GradedAlgebra` structures in
even homological degrees `|aᵢ| = 2i` (`Strict.baseGrading`) and `(|r|, |s|, |t|) = (4, 2, 6)`
(`Strict.arrowGrading`, `Strict.tensorGrading`). All odd-degree pieces vanish, all Hopf-algebroid
maps preserve degrees, and `rightUnit`, `coproduct` and `conjugation` reflect homogeneity.

The combined polynomial-extension gradings `arrowGrading` and `tensorGrading`, their mapping
criteria, and the homogeneity-reflection lemmas adapt `CoordinateChange.Grading`,
`CoordinateChange.Coproduct`, and `CoordinateChange.Homogeneous` under `TauCeti.RingTheory`.

## Main definitions and results

* `WeierstrassCurve.map_toLaurent_toPolynomial_eq_scaling` and
  `WeierstrassCurve.VariableChange.map_toLaurent_toPolynomial_eq_scaling_mul_mul_inv`: applying
  `toLaurent ∘ toPolynomial 𝒜` scales a graded Weierstrass curve by `T (-w)` and conjugates a
  graded change of variables by `scaling _ (T (-w))`.
* `Strict.baseDegree`, `strictCoordDegree`, `baseGrading`, `arrowGrading`, `tensorGrading` and
  odd-degree vanishing (`*_eq_bot_of_odd`).
* `Strict.rightUnit_mem_arrowGrading_iff`, `Strict.counit_mem_baseGrading`,
  `Strict.coproduct_mem_tensorGrading_iff`, `Strict.conjugation_mem_arrowGrading_iff`,
  `WeierstrassCurve.isIntegralModularForm_iff_mem_baseGrading_and_strictRightUnit`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti.GradedAlgebra

/-- Applying `toLaurent ∘ toPolynomial 𝒜` to a Weierstrass curve whose coefficients `aᵢ` lie in
degree `w * i` scales its constant base change by `T (-w)`. -/
theorem map_toLaurent_toPolynomial_eq_scaling {B σ : Type*} [CommRing B] [SetLike σ B]
    [AddSubmonoidClass σ B] (𝒜 : ℕ → σ) [GradedRing 𝒜] (w : ℕ) {W : WeierstrassCurve B}
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (w * coefficientWeight i)) :
    W.map (Polynomial.toLaurent.comp (toPolynomial 𝒜)) =
      VariableChange.scaling _
        (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹ •
        W.map LaurentPolynomial.C := by
  have hspec : (W.map (Polynomial.toLaurent.comp (toPolynomial 𝒜))).specialize =
      (VariableChange.scaling _
        (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹ •
          W.map LaurentPolynomial.C).specialize := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ ?_
    rw [specialize_map, RingHom.comp_apply, RingHom.comp_apply, toPolynomial_of_mem (hW i),
      Polynomial.toLaurent_C_mul_T, VariableChange.scaling_apply, specialize_mk_smul,
      MvPolynomial.aeval_X, specialize_map, RingHom.comp_apply]
    simp only [inv_inv, val_unitOfInvertible, LaurentPolynomial.T_pow,
      mul_comm (LaurentPolynomial.C _)]
    congr 2; push_cast; ring
  rw [← map_specialize (W.map _), hspec, map_specialize]

/-- Applying `toLaurent ∘ toPolynomial 𝒜` to a Weierstrass change of variables `C = (u, r, s, t)`
with `u ∈ 𝒜 0`, `r ∈ 𝒜 (w * 2)`, `s ∈ 𝒜 w`, `t ∈ 𝒜 (w * 3)` conjugates its constant base change by
`scaling _ (T (-w))`. -/
theorem VariableChange.map_toLaurent_toPolynomial_eq_scaling_mul_mul_inv {B σ : Type*} [CommRing B]
    [SetLike σ B] [AddSubmonoidClass σ B] (𝒜 : ℕ → σ) [GradedRing 𝒜] (w : ℕ)
    {C : VariableChange B} (hu : (C.u : B) ∈ 𝒜 0) (hr : C.r ∈ 𝒜 (w * 2)) (hs : C.s ∈ 𝒜 w)
    (ht : C.t ∈ 𝒜 (w * 3)) :
    C.map (Polynomial.toLaurent.comp (toPolynomial 𝒜)) =
      VariableChange.scaling _
        (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹ *
        C.map LaurentPolynomial.C *
        (VariableChange.scaling _
          (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹)⁻¹ := by
  rw [← _root_.map_inv]
  ext
  · simp [VariableChange.mul_def, toPolynomial_of_mem hu]
  · simp [VariableChange.mul_def, toPolynomial_of_mem hr, Polynomial.toLaurent_C_mul_T,
      LaurentPolynomial.T_pow, mul_comm (2 : ℤ)]
  · simp [VariableChange.mul_def, toPolynomial_of_mem hs, Polynomial.toLaurent_C_mul_T,
      mul_comm (LaurentPolynomial.T _) (LaurentPolynomial.C _)]
  · simp [VariableChange.mul_def, toPolynomial_of_mem ht, Polynomial.toLaurent_C_mul_T,
      LaurentPolynomial.T_pow, mul_comm (3 : ℤ)]

end WeierstrassCurve

open WeierstrassCurve MvPolynomial TauCeti.WeierstrassChange
open TauCeti.WeierstrassChange.StrictChangeRing

namespace TauCeti.WeierstrassHopfAlgebroid.Strict

/-! ### Grading on `A = ℤ[a₁, a₂, a₃, a₄, a₆]` -/

/-- The homological degree `2 * i` of the Weierstrass coefficient `aᵢ` (`2, 4, 6, 8, 12`). -/
def baseDegree (i : Coeff) : ℕ := 2 * coefficientWeight i
@[simp] theorem baseDegree_apply (i : Coeff) : baseDegree i = 2 * coefficientWeight i := (rfl)

/-- The homological degrees `4, 2, 6` of the strict change-of-variables coordinates `r, s, t`. -/
def strictCoordDegree : Fin 3 → ℕ := ![4, 2, 6]
@[simp] theorem strictCoordDegree_zero : strictCoordDegree 0 = 4 := (rfl)
@[simp] theorem strictCoordDegree_one : strictCoordDegree 1 = 2 := (rfl)
@[simp] theorem strictCoordDegree_two : strictCoordDegree 2 = 6 := (rfl)

private theorem even_strictCoordDegree (i : Fin 3) : Even (strictCoordDegree i) := by
  fin_cases i <;> decide

/-- The even homological grading on `A = ℤ[a₁, a₂, a₃, a₄, a₆]`, placing `aᵢ` in degree `2i`. -/
def baseGrading (n : ℕ) : Submodule ℤ (MvPolynomial Coeff ℤ) :=
  weightedHomogeneousSubmodule ℤ baseDegree n

/-- Definitional characterization of `baseGrading` as the weighted homogeneous submodule for
`baseDegree`. -/
theorem baseGrading_def (n : ℕ) :
    baseGrading n = weightedHomogeneousSubmodule ℤ baseDegree n := (rfl)

theorem mem_baseGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
    p ∈ baseGrading n ↔ p.IsWeightedHomogeneous baseDegree n :=
  mem_weightedHomogeneousSubmodule ℤ baseDegree n p
@[simp] theorem X_mem_baseGrading (i : Coeff) : X i ∈ baseGrading (2 * coefficientWeight i) :=
  isWeightedHomogeneous_X ℤ baseDegree i
-- Marked `@[no_expose]` so `baseGrading` stays unexposed while reusing `weightedGradedAlgebra`.
/-- The ring `A = ℤ[a₁, ⋯, a₆]` is graded by even homological degrees `|aᵢ| = 2i`. -/
@[no_expose] instance : GradedAlgebra baseGrading := MvPolynomial.weightedGradedAlgebra ℤ baseDegree

private theorem weight_baseDegree (d : Coeff →₀ ℕ) :
    Finsupp.weight baseDegree d = 2 * Finsupp.weight coefficientWeight d := by
  simp only [Finsupp.weight_apply, Finsupp.sum, baseDegree_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Membership in `baseGrading (2 * k)` is weighted homogeneity of modular weight `k`. -/
theorem mem_baseGrading_two_mul_iff {k : ℕ} {p : MvPolynomial Coeff ℤ} :
    p ∈ baseGrading (2 * k) ↔ p.IsWeightedHomogeneous coefficientWeight k := by
  rw [mem_baseGrading_iff]
  refine ⟨fun h d hd ↦ ?_, fun h d hd ↦ by rw [weight_baseDegree, h hd]⟩
  have hd' := h hd; rw [weight_baseDegree] at hd'; omega

/-- Every odd-degree graded piece of `A = ℤ[a₁, ⋯, a₆]` vanishes. -/
theorem baseGrading_eq_bot_of_odd {n : ℕ} (hn : Odd n) : baseGrading n = ⊥ :=
  WeightedHomogeneousSubmodule.eq_bot_of_odd (fun _ ↦ even_two_mul _) hn

/-- A ring homomorphism out of `A = ℤ[a₁, ⋯, a₆]` is graded (with degree shift `e`) iff it sends
each Weierstrass coefficient generator `X i` into degree `e (2 * coefficientWeight i)`. -/
theorem baseGrading_map_mem_iff {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀]
    [AddSubgroupClass σ C₀] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (f : MvPolynomial Coeff ℤ →+* C₀) :
    (∀ ⦃n⦄ ⦃p⦄, p ∈ baseGrading n → f p ∈ 𝒜 (e n)) ↔
      ∀ i : Coeff, f (X i) ∈ 𝒜 (e (2 * coefficientWeight i)) :=
  WeightedHomogeneousSubmodule.map_mem_iff baseDegree 𝒜 e f

/-! ### Combined grading on `A[r, s, t]` -/

/-- The combined even homological grading on `A[r, s, t]`, with `|aᵢ| = 2i` and
`(|r|, |s|, |t|) = (4, 2, 6)`. -/
def arrowGrading (n : ℕ) : Submodule ℤ ArrowRing :=
  WeightedHomogeneousSubmodule.extensionGrading strictCoordDegree baseDegree AlgEquiv.refl n

/-- Membership in `arrowGrading n` via `aeval` on weighted homogeneous polynomials in `(r, s, t)`
and the included Weierstrass coefficients `C (X j)`. -/
theorem mem_arrowGrading_iff_aeval {n : ℕ} {x : ArrowRing} :
    x ∈ arrowGrading n ↔ ∃ p : MvPolynomial (Fin 3 ⊕ Coeff) ℤ,
      p.IsWeightedHomogeneous (Sum.elim strictCoordDegree baseDegree) n ∧
      aeval (Sum.elim X (fun j ↦ C (X j))) p = x := by
  rw [arrowGrading, WeightedHomogeneousSubmodule.mem_extensionGrading_iff_aeval]
  simp only [AlgEquiv.coe_refl, id_eq]

instance : SetLike.GradedMonoid arrowGrading := by unfold arrowGrading; infer_instance
theorem isInternal_arrowGrading : DirectSum.IsInternal arrowGrading :=
  WeightedHomogeneousSubmodule.isInternal_extensionGrading _ _ _
instance : GradedAlgebra arrowGrading := isInternal_arrowGrading.gradedAlgebra
@[simp] theorem X_mem_arrowGrading (i : Fin 3) : X i ∈ arrowGrading (strictCoordDegree i) :=
  WeightedHomogeneousSubmodule.X_mem_extensionGrading _ _ _ i

/-- A ring homomorphism out of `A[r, s, t]` is graded (with degree shift `e`) iff it is graded on
constants `C p` from `A` and sends each strict coordinate `X i` into `𝒜 (e (strictCoordDegree i))`.
-/
theorem arrowGrading_map_mem_iff {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀]
    [AddSubgroupClass σ C₀] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (f : ArrowRing →+* C₀) :
    (∀ ⦃n⦄ ⦃x⦄, x ∈ arrowGrading n → f x ∈ 𝒜 (e n)) ↔
      (∀ ⦃n⦄ ⦃p⦄, p ∈ baseGrading n → f (C p) ∈ 𝒜 (e n)) ∧
        ∀ i : Fin 3, f (X i) ∈ 𝒜 (e (strictCoordDegree i)) :=
  WeightedHomogeneousSubmodule.extensionGrading_map_mem_iff _ _ _ baseGrading
    (fun {_ _} ↦ mem_baseGrading_iff) 𝒜 e f

theorem C_mem_arrowGrading {n : ℕ} {p : MvPolynomial Coeff ℤ} (hp : p ∈ baseGrading n) :
    C p ∈ arrowGrading n :=
  WeightedHomogeneousSubmodule.C_mem_extensionGrading (fun {_ _} ↦ mem_baseGrading_iff) hp
@[simp] theorem C_mem_arrowGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
    C p ∈ arrowGrading n ↔ p ∈ baseGrading n :=
  WeightedHomogeneousSubmodule.C_mem_extensionGrading_iff _ _ _ baseGrading
    (fun {_ _} ↦ mem_baseGrading_iff)

/-- The counit preserves homological degrees. -/
theorem counit_mem_baseGrading {n : ℕ} {x : ArrowRing} (hx : x ∈ arrowGrading n) :
    counit x ∈ baseGrading n :=
  (arrowGrading_map_mem_iff baseGrading (.id ℕ) counit).mpr
    ⟨fun _ _ hp ↦ by simpa using hp, fun _ ↦ by simp [zero_mem]⟩ hx

/-- Every odd-degree graded piece of `A[r, s, t]` vanishes. -/
theorem arrowGrading_eq_bot_of_odd {n : ℕ} (hn : Odd n) : arrowGrading n = ⊥ :=
  WeightedHomogeneousSubmodule.extensionGrading_eq_bot_of_odd even_strictCoordDegree
    (fun _ ↦ even_two_mul _) _ hn

/-- The strict right unit preserves homological degrees. -/
theorem rightUnit_mem_arrowGrading {n : ℕ} {p : MvPolynomial Coeff ℤ} (hp : p ∈ baseGrading n) :
    rightUnit p ∈ arrowGrading n := by
  refine (baseGrading_map_mem_iff arrowGrading (.id ℕ) rightUnit).mpr (fun i ↦ ?_) hp
  refine TauCeti.GradedAlgebra.toPolynomial_eq_monomial_iff.mp <| Polynomial.toLaurent_injective ?_
  let ω : ArrowRing →+* LaurentPolynomial ArrowRing :=
    Polynomial.toLaurent.comp (TauCeti.GradedAlgebra.toPolynomial arrowGrading)
  let u : (LaurentPolynomial ArrowRing)ˣ :=
    (unitOfInvertible (LaurentPolynomial.T (2 : ℤ)))⁻¹
  have hω : Polynomial.toLaurent
      (TauCeti.GradedAlgebra.toPolynomial arrowGrading (rightUnit (X i))) =
      (ω.comp rightUnit) (X i) := rfl
  have hC : (universalChange (MvPolynomial Coeff ℤ)).map ω =
      VariableChange.scaling _ u *
        (universalChange (MvPolynomial Coeff ℤ)).map LaurentPolynomial.C *
        (VariableChange.scaling _ u)⁻¹ :=
    VariableChange.map_toLaurent_toPolynomial_eq_scaling_mul_mul_inv arrowGrading 2
      (by simpa using SetLike.one_mem_graded arrowGrading) (by simpa using X_mem_arrowGrading 0)
      (by simpa using X_mem_arrowGrading 1) (by simpa using X_mem_arrowGrading 2)
  have hW : WeierstrassCurve.map Universal.curve (ω.comp C) =
      VariableChange.scaling _ u •
        WeierstrassCurve.map Universal.curve (LaurentPolynomial.C.comp C) := by
    rw [← WeierstrassCurve.map_map, ← WeierstrassCurve.map_map]
    exact WeierstrassCurve.map_toLaurent_toPolynomial_eq_scaling arrowGrading 2 fun j ↦ by
      rw [WeierstrassCurve.specialize_map, Universal.specialize_curve]
      exact C_mem_arrowGrading (X_mem_baseGrading j)
  rw [hω, comp_rightUnit, hC, hW, ← mul_smul, inv_mul_cancel_right, mul_smul,
    ← map_comp_rightUnit, VariableChange.scaling_apply,
    isWeightedHomogeneous_iff_forall_specialize_mk_smul.mp
      (isWeightedHomogeneous_X ℤ coefficientWeight i),
    WeierstrassCurve.specialize_map, Universal.specialize_curve, RingHom.comp_apply,
    RingHom.comp_apply, RingHom.id_apply, Polynomial.toLaurent_C_mul_T]
  simp only [u, inv_inv, val_unitOfInvertible, LaurentPolynomial.T_pow, AddMonoidHom.id_apply,
    mul_comm (LaurentPolynomial.C _)]
  congr 2; push_cast; ring

/-- The strict right unit preserves and reflects homological degrees. -/
@[simp] theorem rightUnit_mem_arrowGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
    rightUnit p ∈ arrowGrading n ↔ p ∈ baseGrading n :=
  ⟨fun hx ↦ by simpa only [← RingHom.comp_apply, counit_comp_rightUnit, RingHom.id_apply] using
    counit_mem_baseGrading hx, rightUnit_mem_arrowGrading⟩

/-- The strict conjugation preserves homological degrees. -/
theorem conjugation_mem_arrowGrading {n : ℕ} {x : ArrowRing} (hx : x ∈ arrowGrading n) :
    conjugation x ∈ arrowGrading n := by
  refine (arrowGrading_map_mem_iff arrowGrading (.id ℕ) conjugation).mpr
    ⟨fun _ _ hp ↦ by simpa using rightUnit_mem_arrowGrading hp, fun i ↦ ?_⟩ hx
  fin_cases i
  · simpa using neg_mem (X_mem_arrowGrading 0)
  · simpa using neg_mem (X_mem_arrowGrading 1)
  · simpa using sub_mem (SetLike.mul_mem_graded (X_mem_arrowGrading 0) (X_mem_arrowGrading 1))
      (X_mem_arrowGrading 2)

/-- The strict conjugation preserves and reflects homological degrees. -/
@[simp] theorem conjugation_mem_arrowGrading_iff {n : ℕ} {x : ArrowRing} :
    conjugation x ∈ arrowGrading n ↔ x ∈ arrowGrading n :=
  ⟨fun hx ↦ by simpa using conjugation_mem_arrowGrading hx, conjugation_mem_arrowGrading⟩

/-! ### Grading on `A[r, s, t] ⊗_A A[r, s, t]` and the coproduct -/

/-- The combined even homological grading on `A[r, s, t] ⊗_A A[r, s, t]`, placing both `r, s, t`
and `r', s', t'` in degrees `4, 2, 6` and `aᵢ` in degree `2i`. -/
def tensorGrading (n : ℕ) : Submodule ℤ (StrictChangeRing ArrowRing) :=
  WeightedHomogeneousSubmodule.extensionGrading strictCoordDegree
    (Sum.elim strictCoordDegree baseDegree)
    (WeightedHomogeneousSubmodule.extensionEquiv ℤ (Fin 3) Coeff AlgEquiv.refl) n

/-- Membership in `tensorGrading n` via `aeval` on weighted homogeneous polynomials in
`(r', s', t')`, `(r, s, t)`, and the included Weierstrass coefficients `C (C (X j))`. -/
theorem mem_tensorGrading_iff_aeval {n : ℕ} {x : StrictChangeRing ArrowRing} :
    x ∈ tensorGrading n ↔ ∃ p : MvPolynomial (Fin 3 ⊕ (Fin 3 ⊕ Coeff)) ℤ,
      p.IsWeightedHomogeneous
        (Sum.elim strictCoordDegree (Sum.elim strictCoordDegree baseDegree)) n ∧
      aeval (Sum.elim X (Sum.elim (fun j ↦ C (X j)) (fun j ↦ C (C (X j))))) p = x := by
  rw [tensorGrading, WeightedHomogeneousSubmodule.mem_extensionGrading_iff_aeval]
  have h : (fun j : Fin 3 ⊕ Coeff ↦ (C : ArrowRing →+* StrictChangeRing ArrowRing)
      (WeightedHomogeneousSubmodule.extensionEquiv ℤ (Fin 3) Coeff AlgEquiv.refl (X j))) =
      Sum.elim (fun j ↦ C (X j)) (fun j ↦ C (C (X j))) := by ext j; cases j <;> simp
  rw [h]

instance : SetLike.GradedMonoid tensorGrading := by unfold tensorGrading; infer_instance
theorem isInternal_tensorGrading : DirectSum.IsInternal tensorGrading :=
  WeightedHomogeneousSubmodule.isInternal_extensionGrading _ _ _
instance : GradedAlgebra tensorGrading := isInternal_tensorGrading.gradedAlgebra
@[simp] theorem X_mem_tensorGrading (i : Fin 3) : X i ∈ tensorGrading (strictCoordDegree i) :=
  WeightedHomogeneousSubmodule.X_mem_extensionGrading _ _ _ i
theorem C_mem_tensorGrading {n : ℕ} {x : ArrowRing} (hx : x ∈ arrowGrading n) :
    C x ∈ tensorGrading n :=
  WeightedHomogeneousSubmodule.C_mem_extensionGrading
    WeightedHomogeneousSubmodule.extensionEquiv_mem_extensionGrading_iff hx
@[simp] theorem C_mem_tensorGrading_iff {n : ℕ} {x : ArrowRing} :
    C x ∈ tensorGrading n ↔ x ∈ arrowGrading n :=
  WeightedHomogeneousSubmodule.C_mem_extensionGrading_iff _ _ _ arrowGrading
    WeightedHomogeneousSubmodule.extensionEquiv_mem_extensionGrading_iff

/-- A ring homomorphism out of `A[r, s, t] ⊗_A A[r, s, t]` is graded (with degree shift `e`) iff it
is graded on the left factor `C x` and sends each right-factor generator `X i` into
`𝒜 (e (strictCoordDegree i))`. -/
theorem tensorGrading_map_mem_iff {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀]
    [AddSubgroupClass σ C₀] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (f : StrictChangeRing ArrowRing →+* C₀) :
    (∀ ⦃n⦄ ⦃x⦄, x ∈ tensorGrading n → f x ∈ 𝒜 (e n)) ↔
      (∀ ⦃n⦄ ⦃x⦄, x ∈ arrowGrading n → f (C x) ∈ 𝒜 (e n)) ∧
        ∀ i : Fin 3, f (X i) ∈ 𝒜 (e (strictCoordDegree i)) :=
  WeightedHomogeneousSubmodule.extensionGrading_map_mem_iff _ _ _ arrowGrading
    WeightedHomogeneousSubmodule.extensionEquiv_mem_extensionGrading_iff 𝒜 e f

private theorem pushoutLift_counit_id_mem_arrowGrading {n : ℕ} {x : StrictChangeRing ArrowRing}
    (hx : x ∈ tensorGrading n) :
    pushoutLift rightUnit ⟨(C.comp counit, RingHom.id ArrowRing), by
        rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩ x ∈
      arrowGrading n :=
  (tensorGrading_map_mem_iff arrowGrading (.id ℕ) _).mpr
    ⟨fun _ _ hy ↦ by simpa using C_mem_arrowGrading (counit_mem_baseGrading hy),
      fun _ ↦ by simp⟩ hx

/-- The right pushout inclusion `MvPolynomial.map rightUnit` preserves homological degrees. -/
theorem map_rightUnit_mem_tensorGrading {n : ℕ} {x : ArrowRing} (hx : x ∈ arrowGrading n) :
    MvPolynomial.map rightUnit x ∈ tensorGrading n :=
  (arrowGrading_map_mem_iff tensorGrading (.id ℕ) (MvPolynomial.map rightUnit)).mpr
    ⟨fun _ _ hp ↦ by simpa using C_mem_tensorGrading (rightUnit_mem_arrowGrading hp),
      fun _ ↦ by simp⟩ hx

/-- `MvPolynomial.map rightUnit` preserves and reflects homological degrees. -/
@[simp] theorem map_rightUnit_mem_tensorGrading_iff {n : ℕ} {x : ArrowRing} :
    MvPolynomial.map rightUnit x ∈ tensorGrading n ↔ x ∈ arrowGrading n :=
  ⟨fun hx ↦ by simpa using pushoutLift_counit_id_mem_arrowGrading hx,
    map_rightUnit_mem_tensorGrading⟩

/-- Every odd-degree graded piece of `A[r, s, t] ⊗_A A[r, s, t]` vanishes. -/
theorem tensorGrading_eq_bot_of_odd {n : ℕ} (hn : Odd n) : tensorGrading n = ⊥ :=
  WeightedHomogeneousSubmodule.extensionGrading_eq_bot_of_odd even_strictCoordDegree
    (fun i ↦ i.casesOn even_strictCoordDegree fun _ ↦ even_two_mul _) _ hn

/-- The strict coproduct preserves homological degrees. -/
theorem coproduct_mem_tensorGrading {n : ℕ} {x : ArrowRing} (hx : x ∈ arrowGrading n) :
    coproduct x ∈ tensorGrading n := by
  refine (arrowGrading_map_mem_iff tensorGrading (.id ℕ) coproduct).mpr
    ⟨fun _ _ hp ↦ by simpa using C_mem_tensorGrading (C_mem_arrowGrading hp), fun i ↦ ?_⟩ hx
  fin_cases i
  · simpa using add_mem (C_mem_tensorGrading (X_mem_arrowGrading 0)) (X_mem_tensorGrading 0)
  · simpa using add_mem (C_mem_tensorGrading (X_mem_arrowGrading 1)) (X_mem_tensorGrading 1)
  · simpa using add_mem (add_mem (C_mem_tensorGrading (X_mem_arrowGrading 2))
      (X_mem_tensorGrading 2))
      (SetLike.mul_mem_graded (C_mem_tensorGrading (X_mem_arrowGrading 1)) (X_mem_tensorGrading 0))

/-- The strict coproduct preserves and reflects homological degrees. -/
@[simp] theorem coproduct_mem_tensorGrading_iff {n : ℕ} {x : ArrowRing} :
    coproduct x ∈ tensorGrading n ↔ x ∈ arrowGrading n :=
  ⟨fun hx ↦ by simpa only [← RingHom.comp_apply, pushoutLift_counit_id_comp_coproduct,
      RingHom.id_apply] using pushoutLift_counit_id_mem_arrowGrading hx,
    coproduct_mem_tensorGrading⟩

end TauCeti.WeierstrassHopfAlgebroid.Strict

namespace WeierstrassCurve

open MvPolynomial TauCeti.WeierstrassHopfAlgebroid

/-- Integral modular forms of weight `k` are the elements of `Strict.baseGrading (2 * k)` fixed by
`Strict.rightUnit`. -/
theorem isIntegralModularForm_iff_mem_baseGrading_and_strictRightUnit
    {k : ℕ} {f : MvPolynomial Coeff ℤ} :
    IsIntegralModularForm k f ↔ f ∈ Strict.baseGrading (2 * k) ∧ Strict.rightUnit f = C f := by
  rw [Strict.mem_baseGrading_two_mul_iff, isIntegralModularForm_iff_strictRightUnit]

end WeierstrassCurve
