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

Unlike the full coordinate ring `A[u, u⁻¹, r, s, t]`, where `u⁻¹` has negative weight, both
`A = ℤ[a₁, a₂, a₃, a₄, a₆]` and the strict coordinate ring `A[r, s, t]` of
`TauCeti.WeierstrassHopfAlgebroid.Strict` are nonnegatively graded and concentrated in even
homological degrees:
* `aᵢ` has modular weight `i` and homological degree `2i` (`Strict.baseGrading`);
* `r, s, t` have modular weights `2, 1, 3` and homological degrees `4, 2, 6`
  (`Strict.arrowGrading`, `Strict.tensorGrading`).

Retaining homological parity rather than halving internal degrees matches the homological grading
of `(L, L[b₁, b₂, …])` (`|xᵢ| = |bᵢ| = 2i`) and keeps odd homological degrees identically zero
(`Strict.baseGrading_eq_bot_of_odd`, `Strict.arrowGrading_eq_bot_of_odd`,
`Strict.tensorGrading_eq_bot_of_odd`). All structure maps of `(A, A[r, s, t])` preserve this
grading, and the right unit, coproduct and conjugation reflect homogeneity.

## Main definitions

* `TauCeti.WeierstrassHopfAlgebroid.Strict.baseDegree`, `strictCoordDegree`: the homological
  degree assignments `aᵢ ↦ 2i` and `(r, s, t) ↦ (4, 2, 6)`.
* `TauCeti.WeierstrassHopfAlgebroid.Strict.baseGrading`, `arrowGrading`, `tensorGrading`: the
  `GradedAlgebra` structures on `A`, `A[r, s, t]` and `A[r, s, t] ⊗_A A[r, s, t]`.

## Main results

* `Strict.baseGrading_eq_bot_of_odd`, `Strict.arrowGrading_eq_bot_of_odd`,
  `Strict.tensorGrading_eq_bot_of_odd`: all odd-degree pieces vanish.
* `Strict.rightUnit_mem_arrowGrading_iff`, `Strict.counit_mem_baseGrading`,
  `Strict.coproduct_mem_tensorGrading_iff`, `Strict.conjugation_mem_arrowGrading_iff`: all
  Hopf-algebroid structure maps preserve homological degrees.
* `WeierstrassCurve.isIntegralModularForm_iff_mem_baseGrading_and_strictRightUnit`: integral
  modular forms of weight `k` are the elements of `Strict.baseGrading (2 * k)` fixed by
  `Strict.rightUnit`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §3.
-/

public section

noncomputable section

open WeierstrassCurve MvPolynomial TauCeti.WeierstrassChange
open TauCeti.WeierstrassChange.StrictChangeRing

namespace TauCeti.WeierstrassHopfAlgebroid.Strict

/-! ### Grading on `A = ℤ[a₁, a₂, a₃, a₄, a₆]` -/

/-- The homological degree `2 * i` of the Weierstrass coefficient `aᵢ` (`2, 4, 6, 8, 12`). -/
def baseDegree (i : Coeff) : ℕ :=
  2 * coefficientWeight i

@[simp]
theorem baseDegree_apply (i : Coeff) : baseDegree i = 2 * coefficientWeight i :=
  (rfl)

/-- The homological degrees `4, 2, 6` of the strict change-of-variables coordinates `r, s, t`,
twice their modular weights `2, 1, 3`. -/
def strictCoordDegree : Fin 3 → ℕ :=
  ![4, 2, 6]

@[simp] theorem strictCoordDegree_zero : strictCoordDegree 0 = 4 := (rfl)
@[simp] theorem strictCoordDegree_one : strictCoordDegree 1 = 2 := (rfl)
@[simp] theorem strictCoordDegree_two : strictCoordDegree 2 = 6 := (rfl)

/-- The even homological grading on `A = ℤ[a₁, a₂, a₃, a₄, a₆]`, placing `aᵢ` in degree `2i`. -/
def baseGrading (n : ℕ) : Submodule ℤ (MvPolynomial Coeff ℤ) :=
  weightedHomogeneousSubmodule ℤ baseDegree n

theorem mem_baseGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
    p ∈ baseGrading n ↔ p.IsWeightedHomogeneous baseDegree n :=
  mem_weightedHomogeneousSubmodule ℤ baseDegree n p

@[simp]
theorem X_mem_baseGrading (i : Coeff) : X i ∈ baseGrading (2 * coefficientWeight i) :=
  isWeightedHomogeneous_X ℤ baseDegree i

instance : SetLike.GradedMonoid baseGrading :=
  WeightedHomogeneousSubmodule.gradedMonoid (R := ℤ) (w := baseDegree)

theorem isInternal_baseGrading : DirectSum.IsInternal baseGrading := by
  let := MvPolynomial.weightedGradedAlgebra (R := ℤ) (w := baseDegree)
  exact DirectSum.Decomposition.isInternal (weightedHomogeneousSubmodule ℤ baseDegree)

instance : GradedAlgebra baseGrading :=
  isInternal_baseGrading.gradedAlgebra

private theorem weight_baseDegree (d : Coeff →₀ ℕ) :
    Finsupp.weight baseDegree d = 2 * Finsupp.weight coefficientWeight d := by
  simp only [Finsupp.weight_apply, Finsupp.sum, baseDegree_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- In even homological degree `2k`, membership in `baseGrading (2 * k)` is weighted homogeneity of
modular weight `k` for `coefficientWeight`. -/
theorem mem_baseGrading_two_mul_iff {k : ℕ} {p : MvPolynomial Coeff ℤ} :
    p ∈ baseGrading (2 * k) ↔ p.IsWeightedHomogeneous coefficientWeight k := by
  rw [mem_baseGrading_iff]
  refine ⟨fun h d hd ↦ ?_, fun h d hd ↦ ?_⟩
  · have hd' := h hd
    rw [weight_baseDegree] at hd'
    omega
  · rw [weight_baseDegree, h hd]

/-- Every odd-degree graded piece of `A = ℤ[a₁, ⋯, a₆]` vanishes: retaining homological parity
avoids spurious odd-degree classes. -/
theorem baseGrading_eq_bot_of_odd {n : ℕ} (hn : Odd n) : baseGrading n = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [Submodule.mem_bot]
  ext d
  simp only [AddMonoidAlgebra.coeff_zero]
  by_contra hd
  have hw := (mem_baseGrading_iff.mp hp) hd
  have heven : Even (Finsupp.weight baseDegree d) := by
    rw [weight_baseDegree]
    exact even_two_mul _
  rw [hw] at heven
  exact (Nat.not_even_iff_odd.mpr hn) heven

/-- A ring homomorphism out of `A = ℤ[a₁, ⋯, a₆]` preserves regraded homological degrees if and
only if each `aᵢ` maps into degree `2i`. -/
theorem baseGrading_map_mem_iff {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀]
    [AddSubgroupClass σ C₀] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (f : MvPolynomial Coeff ℤ →+* C₀) :
    (∀ ⦃n⦄ ⦃p⦄, p ∈ baseGrading n → f p ∈ 𝒜 (e n)) ↔
      ∀ i : Coeff, f (X i) ∈ 𝒜 (e (2 * coefficientWeight i)) :=
  WeightedHomogeneousSubmodule.map_mem_iff baseDegree 𝒜 e f

/-! ### Combined grading on `A[r, s, t]` -/

/-- The polynomial presentation `ℤ[r, s, t, a₁, ⋯, a₆] ≃ₐ[ℤ] A[r, s, t]`. -/
private def arrowPolynomialEquiv : MvPolynomial (Fin 3 ⊕ Coeff) ℤ ≃ₐ[ℤ] ArrowRing :=
  sumAlgEquiv ℤ (Fin 3) Coeff

private theorem arrowPolynomialEquiv_X (i : Fin 3 ⊕ Coeff) :
    arrowPolynomialEquiv (X i) = Sum.elim X (fun j ↦ C (X j)) i := by
  cases i <;> simp [arrowPolynomialEquiv]

/-- The combined even homological grading on `A[r, s, t]`, with `|aᵢ| = 2i` and
`|r| = 4`, `|s| = 2`, `|t| = 6`. -/
def arrowGrading (n : ℕ) : Submodule ℤ ArrowRing :=
  (weightedHomogeneousSubmodule ℤ (Sum.elim strictCoordDegree baseDegree) n).map
    arrowPolynomialEquiv.toLinearMap

instance : SetLike.GradedMonoid arrowGrading :=
  WeightedHomogeneousSubmodule.gradedMonoid_map _ arrowPolynomialEquiv

theorem isInternal_arrowGrading : DirectSum.IsInternal arrowGrading :=
  WeightedHomogeneousSubmodule.isInternal_map _ arrowPolynomialEquiv

instance : GradedAlgebra arrowGrading :=
  isInternal_arrowGrading.gradedAlgebra

@[simp]
theorem X_mem_arrowGrading (i : Fin 3) : X i ∈ arrowGrading (strictCoordDegree i) :=
  ⟨X (.inl i), isWeightedHomogeneous_X _ _ _, arrowPolynomialEquiv_X _⟩

/-- A ring homomorphism out of `A[r, s, t]` preserves regraded homological degrees if and only if
its restriction to `A` does and `r, s, t` map to degrees `4, 2, 6`. -/
theorem arrowGrading_map_mem_iff {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀]
    [AddSubgroupClass σ C₀] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (f : ArrowRing →+* C₀) :
    (∀ ⦃n⦄ ⦃x⦄, x ∈ arrowGrading n → f x ∈ 𝒜 (e n)) ↔
      (∀ ⦃n⦄ ⦃p⦄, p ∈ baseGrading n → f (C p) ∈ 𝒜 (e n)) ∧
        ∀ i : Fin 3, f (X i) ∈ 𝒜 (e (strictCoordDegree i)) := by
  refine ⟨fun h ↦ ⟨fun _ _ hp ↦ ?_, fun i ↦ h (X_mem_arrowGrading i)⟩, ?_⟩
  · refine (baseGrading_map_mem_iff 𝒜 e (f.comp C)).mpr (fun j ↦ ?_) hp
    exact h ⟨X (.inr j), isWeightedHomogeneous_X _ _ _, arrowPolynomialEquiv_X _⟩
  · rintro ⟨hC, hX⟩ n x ⟨p, hp, rfl⟩
    refine (WeightedHomogeneousSubmodule.map_mem_iff _ 𝒜 e
      (f.comp arrowPolynomialEquiv.toRingHom)).mpr (fun i ↦ ?_) hp
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv, arrowPolynomialEquiv_X]
    cases i with
    | inl i => exact hX i
    | inr j => exact hC (X_mem_baseGrading j)

theorem C_mem_arrowGrading {n : ℕ} {p : MvPolynomial Coeff ℤ} (hp : p ∈ baseGrading n) :
    C p ∈ arrowGrading n :=
  (baseGrading_map_mem_iff arrowGrading (.id ℕ) C).mpr
    (fun j ↦ ⟨X (.inr j), isWeightedHomogeneous_X _ _ _, arrowPolynomialEquiv_X _⟩) hp

/-- The counit preserves homological degrees. -/
theorem counit_mem_baseGrading {n : ℕ} {x : ArrowRing} (hx : x ∈ arrowGrading n) :
    counit x ∈ baseGrading n :=
  (arrowGrading_map_mem_iff baseGrading (.id ℕ) counit).mpr
    ⟨fun _ _ hp ↦ by simpa using hp, fun i ↦ by simp [zero_mem]⟩ hx

@[simp]
theorem C_mem_arrowGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
    C p ∈ arrowGrading n ↔ p ∈ baseGrading n :=
  ⟨fun hx ↦ by simpa using counit_mem_baseGrading hx, C_mem_arrowGrading⟩

/-- Every odd-degree graded piece of `A[r, s, t]` vanishes. -/
theorem arrowGrading_eq_bot_of_odd {n : ℕ} (hn : Odd n) : arrowGrading n = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨p, hp, rfl⟩
  rw [Submodule.mem_bot]
  suffices p = 0 by simp [this]
  ext d
  simp only [AddMonoidAlgebra.coeff_zero]
  by_contra hd
  have hw := (mem_weightedHomogeneousSubmodule ℤ _ n p).mp hp hd
  have heven : Even (Finsupp.weight (Sum.elim strictCoordDegree baseDegree) d) := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    refine Finset.even_sum _ fun i _ ↦ Even.mul_left ?_ _
    rcases i with i | j
    · fin_cases i <;> decide
    · exact even_two_mul _
  rw [hw] at heven
  exact (Nat.not_even_iff_odd.mpr hn) heven

/-- The strict right unit preserves homological degrees. -/
theorem rightUnit_mem_arrowGrading {n : ℕ} {p : MvPolynomial Coeff ℤ} (hp : p ∈ baseGrading n) :
    rightUnit p ∈ arrowGrading n := by
  refine (baseGrading_map_mem_iff arrowGrading (.id ℕ) rightUnit).mpr (fun i ↦ ?_) hp
  have hr : (X 0 : ArrowRing) ∈ arrowGrading 4 := X_mem_arrowGrading 0
  have hs : (X 1 : ArrowRing) ∈ arrowGrading 2 := X_mem_arrowGrading 1
  have ht : (X 2 : ArrowRing) ∈ arrowGrading 6 := X_mem_arrowGrading 2
  have ha₁ : (C (X .A₁) : ArrowRing) ∈ arrowGrading 2 := by
    simpa using C_mem_arrowGrading (X_mem_baseGrading .A₁)
  have ha₂ : (C (X .A₂) : ArrowRing) ∈ arrowGrading 4 := by
    simpa using C_mem_arrowGrading (X_mem_baseGrading .A₂)
  have ha₃ : (C (X .A₃) : ArrowRing) ∈ arrowGrading 6 := by
    simpa using C_mem_arrowGrading (X_mem_baseGrading .A₃)
  have ha₄ : (C (X .A₄) : ArrowRing) ∈ arrowGrading 8 := by
    simpa using C_mem_arrowGrading (X_mem_baseGrading .A₄)
  have ha₆ : (C (X .A₆) : ArrowRing) ∈ arrowGrading 12 := by
    simpa using C_mem_arrowGrading (X_mem_baseGrading .A₆)
  cases i
  · simpa [zsmul_eq_mul] using add_mem ha₁ (Submodule.smul_mem _ 2 hs)
  · have h3r : 3 * (X 0 : ArrowRing) ∈ arrowGrading 4 := by
      simpa [zsmul_eq_mul] using Submodule.smul_mem _ (3 : ℤ) hr
    simpa using sub_mem (add_mem (sub_mem ha₂ (SetLike.mul_mem_graded hs ha₁)) h3r)
      (by simpa using SetLike.pow_mem_graded 2 hs)
  · have h2t : 2 * (X 2 : ArrowRing) ∈ arrowGrading 6 := by
      simpa [zsmul_eq_mul] using Submodule.smul_mem _ (2 : ℤ) ht
    simpa using add_mem (add_mem ha₃ (SetLike.mul_mem_graded hr ha₁)) h2t
  · have h2ra₂ : 2 * (X 0 : ArrowRing) * C (X .A₂) ∈ arrowGrading 8 := by
      simpa [zsmul_eq_mul, mul_assoc] using
        Submodule.smul_mem _ (2 : ℤ) (SetLike.mul_mem_graded hr ha₂)
    have h3r2 : 3 * (X 0 : ArrowRing) ^ 2 ∈ arrowGrading 8 := by
      simpa [zsmul_eq_mul] using Submodule.smul_mem _ (3 : ℤ) (SetLike.pow_mem_graded 2 hr)
    have h2st : 2 * (X 1 : ArrowRing) * X 2 ∈ arrowGrading 8 := by
      simpa [zsmul_eq_mul, mul_assoc] using
        Submodule.smul_mem _ (2 : ℤ) (SetLike.mul_mem_graded hs ht)
    simpa using
      sub_mem (add_mem (sub_mem (add_mem (sub_mem ha₄ (SetLike.mul_mem_graded hs ha₃)) h2ra₂)
        (SetLike.mul_mem_graded (add_mem ht (SetLike.mul_mem_graded hr hs)) ha₁)) h3r2) h2st
  · have hr2a₂ : (X 0 : ArrowRing) ^ 2 * C (X .A₂) ∈ arrowGrading 12 := by
      simpa using SetLike.mul_mem_graded (SetLike.pow_mem_graded 2 hr) ha₂
    have hr3 : (X 0 : ArrowRing) ^ 3 ∈ arrowGrading 12 := by
      simpa using SetLike.pow_mem_graded 3 hr
    have ht2 : (X 2 : ArrowRing) ^ 2 ∈ arrowGrading 12 := by
      simpa using SetLike.pow_mem_graded 2 ht
    have hrta₁ : (X 0 : ArrowRing) * X 2 * C (X .A₁) ∈ arrowGrading 12 := by
      simpa using SetLike.mul_mem_graded (SetLike.mul_mem_graded hr ht) ha₁
    simpa using
      sub_mem (sub_mem (sub_mem (add_mem (add_mem (add_mem ha₆ (SetLike.mul_mem_graded hr ha₄))
        hr2a₂) hr3) (SetLike.mul_mem_graded ht ha₃)) ht2) hrta₁

@[simp]
theorem rightUnit_mem_arrowGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
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

@[simp]
theorem conjugation_mem_arrowGrading_iff {n : ℕ} {x : ArrowRing} :
    conjugation x ∈ arrowGrading n ↔ x ∈ arrowGrading n :=
  ⟨fun hx ↦ by simpa using conjugation_mem_arrowGrading hx, conjugation_mem_arrowGrading⟩

/-! ### Grading on `A[r, s, t] ⊗_A A[r, s, t]` and the coproduct -/

/-- The polynomial presentation of `A[r, s, t] ⊗_A A[r, s, t] = A[r, s, t][r', s', t']`. -/
private def tensorPolynomialEquiv :
    MvPolynomial (Fin 3 ⊕ (Fin 3 ⊕ Coeff)) ℤ ≃ₐ[ℤ] StrictChangeRing ArrowRing :=
  (sumAlgEquiv ℤ (Fin 3) (Fin 3 ⊕ Coeff)).trans (mapAlgEquiv (Fin 3) arrowPolynomialEquiv)

private theorem tensorPolynomialEquiv_X (i : Fin 3 ⊕ (Fin 3 ⊕ Coeff)) :
    tensorPolynomialEquiv (X i) =
      Sum.elim X (Sum.elim (fun j ↦ C (X j)) (fun j ↦ C (C (X j)))) i := by
  rcases i with i | (i | j) <;> simp [tensorPolynomialEquiv, mapAlgEquiv_apply,
    arrowPolynomialEquiv_X]

/-- The combined even homological grading on `A[r, s, t] ⊗_A A[r, s, t]`, placing both families of
strict coordinates `r, s, t` and `r', s', t'` in degrees `4, 2, 6` and `aᵢ` in degree `2i`. -/
def tensorGrading (n : ℕ) : Submodule ℤ (StrictChangeRing ArrowRing) :=
  (weightedHomogeneousSubmodule ℤ
    (Sum.elim strictCoordDegree (Sum.elim strictCoordDegree baseDegree)) n).map
      tensorPolynomialEquiv.toLinearMap

instance : SetLike.GradedMonoid tensorGrading :=
  WeightedHomogeneousSubmodule.gradedMonoid_map _ tensorPolynomialEquiv

theorem isInternal_tensorGrading : DirectSum.IsInternal tensorGrading :=
  WeightedHomogeneousSubmodule.isInternal_map _ tensorPolynomialEquiv

instance : GradedAlgebra tensorGrading :=
  isInternal_tensorGrading.gradedAlgebra

@[simp]
theorem X_mem_tensorGrading (i : Fin 3) : X i ∈ tensorGrading (strictCoordDegree i) :=
  ⟨X (.inl i), isWeightedHomogeneous_X _ _ _, tensorPolynomialEquiv_X _⟩

theorem C_mem_tensorGrading {n : ℕ} {x : ArrowRing} (hx : x ∈ arrowGrading n) :
    C x ∈ tensorGrading n := by
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨rename Sum.inr p, ?_, ?_⟩
  · rw [rename_eq_aeval]
    exact hp.aeval fun i ↦ isWeightedHomogeneous_X _ _ (Sum.inr i)
  · have he : tensorPolynomialEquiv.toAlgHom.comp (rename Sum.inr) =
        (IsScalarTower.toAlgHom ℤ ArrowRing (StrictChangeRing ArrowRing)).comp
          arrowPolynomialEquiv.toAlgHom := by
      ext i
      rcases i with i | j <;> simp [tensorPolynomialEquiv_X, arrowPolynomialEquiv_X]
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.toLinearMap_apply,
      IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq] using DFunLike.congr_fun he p

/-- A ring homomorphism out of `A[r, s, t] ⊗_A A[r, s, t]` preserves regraded homological degrees
if and only if its restriction to the left factor does and `r', s', t'` map to degrees `4, 2, 6`. -/
theorem tensorGrading_map_mem_iff {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀]
    [AddSubgroupClass σ C₀] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (f : StrictChangeRing ArrowRing →+* C₀) :
    (∀ ⦃n⦄ ⦃x⦄, x ∈ tensorGrading n → f x ∈ 𝒜 (e n)) ↔
      (∀ ⦃n⦄ ⦃x⦄, x ∈ arrowGrading n → f (C x) ∈ 𝒜 (e n)) ∧
        ∀ i : Fin 3, f (X i) ∈ 𝒜 (e (strictCoordDegree i)) := by
  refine ⟨fun h ↦ ⟨fun _ _ hx ↦ h (C_mem_tensorGrading hx), fun i ↦ h (X_mem_tensorGrading i)⟩, ?_⟩
  rintro ⟨hC, hX⟩ n x ⟨p, hp, rfl⟩
  refine (WeightedHomogeneousSubmodule.map_mem_iff _ 𝒜 e
    (f.comp tensorPolynomialEquiv.toRingHom)).mpr (fun i ↦ ?_) hp
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv, tensorPolynomialEquiv_X]
  rcases i with i | (i | j)
  · exact hX i
  · exact hC (X_mem_arrowGrading i)
  · exact hC (C_mem_arrowGrading (X_mem_baseGrading j))

/-- The pushout homomorphism of two composable graded maps out of `A[r, s, t]` is graded. -/
theorem pushoutLift_mem {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀] [AddSubgroupClass σ C₀]
    [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (p : {p : (ArrowRing →+* C₀) × (ArrowRing →+* C₀) // p.1.comp rightUnit = p.2.comp C})
    (h₁ : ∀ ⦃n⦄ ⦃x⦄, x ∈ arrowGrading n → p.1.1 x ∈ 𝒜 (e n))
    (h₂ : ∀ ⦃n⦄ ⦃x⦄, x ∈ arrowGrading n → p.1.2 x ∈ 𝒜 (e n))
    {n : ℕ} {x : StrictChangeRing ArrowRing} (hx : x ∈ tensorGrading n) :
    pushoutLift rightUnit p x ∈ 𝒜 (e n) :=
  (tensorGrading_map_mem_iff 𝒜 e (pushoutLift rightUnit p)).mpr
    ⟨fun _ _ hy ↦ by simpa using h₁ hy, fun i ↦ by simpa using h₂ (X_mem_arrowGrading i)⟩ hx

/-- Every odd-degree graded piece of `A[r, s, t] ⊗_A A[r, s, t]` vanishes. -/
theorem tensorGrading_eq_bot_of_odd {n : ℕ} (hn : Odd n) : tensorGrading n = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨p, hp, rfl⟩
  rw [Submodule.mem_bot]
  suffices p = 0 by simp [this]
  ext d
  simp only [AddMonoidAlgebra.coeff_zero]
  by_contra hd
  have hw := (mem_weightedHomogeneousSubmodule ℤ _ n p).mp hp hd
  have heven :
      Even (Finsupp.weight (Sum.elim strictCoordDegree (Sum.elim strictCoordDegree baseDegree)) d)
      := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    refine Finset.even_sum _ fun i _ ↦ Even.mul_left ?_ _
    rcases i with i | (i | j)
    · fin_cases i <;> decide
    · fin_cases i <;> decide
    · exact even_two_mul _
  rw [hw] at heven
  exact (Nat.not_even_iff_odd.mpr hn) heven

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

@[simp]
theorem coproduct_mem_tensorGrading_iff {n : ℕ} {x : ArrowRing} :
    coproduct x ∈ tensorGrading n ↔ x ∈ arrowGrading n := by
  refine ⟨fun hx ↦ ?_, coproduct_mem_tensorGrading⟩
  have h := pushoutLift_mem arrowGrading (.id ℕ)
    ⟨(C.comp counit, RingHom.id ArrowRing), by
      rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩
    (fun _ _ hy ↦ C_mem_arrowGrading (counit_mem_baseGrading hy)) (fun _ _ hy ↦ hy) hx
  simpa only [← RingHom.comp_apply, pushoutLift_counit_id_comp_coproduct, RingHom.id_apply,
    AddMonoidHom.id_apply] using h

end TauCeti.WeierstrassHopfAlgebroid.Strict

namespace WeierstrassCurve

open MvPolynomial TauCeti.WeierstrassHopfAlgebroid

/-- Restated in homological degree `2k`, the integral modular forms of weight `k` are the
elements of `Strict.baseGrading (2 * k)` fixed by `Strict.rightUnit`. -/
theorem isIntegralModularForm_iff_mem_baseGrading_and_strictRightUnit
    {k : ℕ} {f : MvPolynomial Coeff ℤ} :
    IsIntegralModularForm k f ↔ f ∈ Strict.baseGrading (2 * k) ∧ Strict.rightUnit f = C f := by
  rw [Strict.mem_baseGrading_two_mul_iff, isIntegralModularForm_iff_strictRightUnit]

end WeierstrassCurve
