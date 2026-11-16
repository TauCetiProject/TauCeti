/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.StrictHopfAlgebroid
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
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
@[expose] def baseGrading (n : ℕ) : Submodule ℤ (MvPolynomial Coeff ℤ) :=
  weightedHomogeneousSubmodule ℤ baseDegree n

theorem mem_baseGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
    p ∈ baseGrading n ↔ p.IsWeightedHomogeneous baseDegree n :=
  mem_weightedHomogeneousSubmodule ℤ baseDegree n p
@[simp] theorem X_mem_baseGrading (i : Coeff) : X i ∈ baseGrading (2 * coefficientWeight i) :=
  isWeightedHomogeneous_X ℤ baseDegree i
instance : GradedAlgebra baseGrading := MvPolynomial.weightedGradedAlgebra ℤ baseDegree

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
  rw [arrowGrading, WeightedHomogeneousSubmodule.mem_extensionGrading_iff_aeval]; rfl

instance : SetLike.GradedMonoid arrowGrading :=
  WeightedHomogeneousSubmodule.gradedMonoid_extensionGrading _ _ _
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

private theorem intCast_mul_mem {n : ℕ} (k : ℤ) {x : ArrowRing} (hx : x ∈ arrowGrading n) :
    (k : ArrowRing) * x ∈ arrowGrading n := by
  simpa [zsmul_eq_mul] using Submodule.smul_mem _ k hx

/-- The strict right unit preserves homological degrees. -/
theorem rightUnit_mem_arrowGrading {n : ℕ} {p : MvPolynomial Coeff ℤ} (hp : p ∈ baseGrading n) :
    rightUnit p ∈ arrowGrading n := by
  refine (baseGrading_map_mem_iff arrowGrading (.id ℕ) rightUnit).mpr (fun i ↦ ?_) hp
  have hr : (X 0 : ArrowRing) ∈ arrowGrading 4 := X_mem_arrowGrading 0
  have hs : (X 1 : ArrowRing) ∈ arrowGrading 2 := X_mem_arrowGrading 1
  have ht : (X 2 : ArrowRing) ∈ arrowGrading 6 := X_mem_arrowGrading 2
  have ha (j : Coeff) (m : ℕ) (hm : 2 * coefficientWeight j = m := by simp) :
      (C (X j) : ArrowRing) ∈ arrowGrading m := hm ▸ C_mem_arrowGrading (X_mem_baseGrading j)
  cases i
  · simpa using add_mem (ha .A₁ 2) (intCast_mul_mem 2 hs)
  · simpa using sub_mem (add_mem (sub_mem (ha .A₂ 4) (SetLike.mul_mem_graded hs (ha .A₁ 2)))
      (intCast_mul_mem 3 hr)) (by simpa using SetLike.pow_mem_graded 2 hs)
  · simpa using add_mem (add_mem (ha .A₃ 6) (SetLike.mul_mem_graded hr (ha .A₁ 2)))
      (intCast_mul_mem 2 ht)
  · simpa [mul_assoc] using sub_mem (add_mem (sub_mem (add_mem
      (sub_mem (ha .A₄ 8) (SetLike.mul_mem_graded hs (ha .A₃ 6)))
      (intCast_mul_mem 2 (SetLike.mul_mem_graded hr (ha .A₂ 4))))
      (SetLike.mul_mem_graded (add_mem ht (SetLike.mul_mem_graded hr hs)) (ha .A₁ 2)))
      (intCast_mul_mem 3 (by simpa using SetLike.pow_mem_graded 2 hr)))
      (intCast_mul_mem 2 (SetLike.mul_mem_graded hs ht))
  · simpa using sub_mem (sub_mem (sub_mem (add_mem (add_mem (add_mem (ha .A₆ 12)
      (SetLike.mul_mem_graded hr (ha .A₄ 8)))
      (SetLike.mul_mem_graded (by simpa using SetLike.pow_mem_graded 2 hr) (ha .A₂ 4)))
      (by simpa using SetLike.pow_mem_graded 3 hr)) (SetLike.mul_mem_graded ht (ha .A₃ 6)))
      (by simpa using SetLike.pow_mem_graded 2 ht))
      (SetLike.mul_mem_graded (SetLike.mul_mem_graded hr ht) (ha .A₁ 2))

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

instance : SetLike.GradedMonoid tensorGrading :=
  WeightedHomogeneousSubmodule.gradedMonoid_extensionGrading _ _ _
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

/-- The right pushout inclusion `MvPolynomial.map rightUnit` preserves homological degrees. -/
theorem map_rightUnit_mem_tensorGrading {n : ℕ} {x : ArrowRing} (hx : x ∈ arrowGrading n) :
    MvPolynomial.map rightUnit x ∈ tensorGrading n :=
  (arrowGrading_map_mem_iff tensorGrading (.id ℕ) (MvPolynomial.map rightUnit)).mpr
    ⟨fun _ _ hp ↦ by simpa using C_mem_tensorGrading (rightUnit_mem_arrowGrading hp),
      fun _ ↦ by simp⟩ hx

/-- `MvPolynomial.map rightUnit` preserves and reflects homological degrees. -/
@[simp] theorem map_rightUnit_mem_tensorGrading_iff {n : ℕ} {x : ArrowRing} :
    MvPolynomial.map rightUnit x ∈ tensorGrading n ↔ x ∈ arrowGrading n := by
  refine ⟨fun hx ↦ ?_, map_rightUnit_mem_tensorGrading⟩
  have h := pushoutLift_mem
    (p := ⟨(C.comp counit, RingHom.id ArrowRing), by
      rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩)
    (tensorGrading_map_mem_iff arrowGrading (.id ℕ) _) X_mem_arrowGrading
    (fun _ _ hy ↦ C_mem_arrowGrading (counit_mem_baseGrading hy)) (fun _ _ hy ↦ hy) hx
  rwa [pushoutLift_map, RingHom.id_apply, AddMonoidHom.id_apply] at h

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
    coproduct x ∈ tensorGrading n ↔ x ∈ arrowGrading n := by
  refine ⟨fun hx ↦ ?_, coproduct_mem_tensorGrading⟩
  have h := pushoutLift_mem
    (p := ⟨(C.comp counit, RingHom.id ArrowRing), by
      rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩)
    (tensorGrading_map_mem_iff arrowGrading (.id ℕ) _) X_mem_arrowGrading
    (fun _ _ hy ↦ C_mem_arrowGrading (counit_mem_baseGrading hy)) (fun _ _ hy ↦ hy) hx
  rwa [← RingHom.comp_apply, pushoutLift_counit_id_comp_coproduct, RingHom.id_apply,
    AddMonoidHom.id_apply] at h

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
