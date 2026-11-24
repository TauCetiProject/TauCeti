/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The grading of a trivial square-zero extension

The trivial square-zero extension `R ⊕ M` (Mathlib's `TrivSqZeroExt R M`) is `ℤ`-graded with `R`
in degree `0`, `M` in degree `1` and nothing in any other degree.  Since `M · M = 0` would land in
degree `2`, this is a graded algebra, and when `R` is commutative and `M` is symmetric it is
graded-commutative.

## Main definitions

* `TauCeti.trivSqZeroExtGrading`: the grading of `R ⊕ M` with `R` in degree `0` and `M` in
  degree `1`.

## Main results

* `TauCeti.instGradedAlgebraTrivSqZeroExtGrading`: `R ⊕ M` is a graded algebra.
* `TauCeti.mul_eq_negOnePow_smul_mul_of_mem_trivSqZeroExtGrading`: `R ⊕ M` is graded-commutative.
-/

public section

open DirectSum

@[inherit_doc] local notation "tsze" => TrivSqZeroExt

namespace TauCeti

open TrivSqZeroExt

section Grading

variable (S R M : Type*) [CommSemiring S] [Semiring R] [AddCommMonoid M] [Module S R]
  [Module S M]

/-- The grading of the trivial square-zero extension `R ⊕ M` with `R` in degree `0`, `M` in degree
`1`, and nothing in any other degree: the degree-`n` piece consists of the `x` whose `R`-component
vanishes unless `n = 0` and whose `M`-component vanishes unless `n = 1`. -/
def trivSqZeroExtGrading (n : ℤ) : Submodule S (tsze R M) where
  carrier := {x | (n ≠ 0 → x.fst = 0) ∧ (n ≠ 1 → x.snd = 0)}
  add_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨fun hn ↦ by simp [hx₁ hn, hy₁ hn], fun hn ↦ by simp [hx₂ hn, hy₂ hn]⟩
  zero_mem' := ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  smul_mem' := by
    rintro s x ⟨hx₁, hx₂⟩
    exact ⟨fun hn ↦ by simp [hx₁ hn], fun hn ↦ by simp [hx₂ hn]⟩

variable {S R M}

/-- An element has degree `n` when its `R`-component vanishes unless `n = 0` and its
`M`-component vanishes unless `n = 1`. -/
theorem mem_trivSqZeroExtGrading_iff {n : ℤ} {x : tsze R M} :
    x ∈ trivSqZeroExtGrading S R M n ↔ (n ≠ 0 → x.fst = 0) ∧ (n ≠ 1 → x.snd = 0) :=
  Iff.rfl

/-- The elements of degree `0` are those with zero `M`-component. -/
@[simp]
theorem mem_trivSqZeroExtGrading_zero_iff {x : tsze R M} :
    x ∈ trivSqZeroExtGrading S R M 0 ↔ x.snd = 0 := by
  simp [mem_trivSqZeroExtGrading_iff]

/-- The elements of degree `1` are those with zero `R`-component. -/
@[simp]
theorem mem_trivSqZeroExtGrading_one_iff {x : tsze R M} :
    x ∈ trivSqZeroExtGrading S R M 1 ↔ x.fst = 0 := by
  simp [mem_trivSqZeroExtGrading_iff]

/-- Every degree other than `0` and `1` is zero. -/
theorem trivSqZeroExtGrading_eq_bot {n : ℤ} (h₀ : n ≠ 0) (h₁ : n ≠ 1) :
    trivSqZeroExtGrading S R M n = ⊥ := by
  ext x
  simp only [mem_trivSqZeroExtGrading_iff, h₀, h₁, ne_eq, not_false_eq_true, forall_const,
    Submodule.mem_bot]
  exact ⟨fun h ↦ ext h.1 h.2, fun h ↦ by simp [h]⟩

/-- `R` sits in degree `0`. -/
theorem inl_mem_trivSqZeroExtGrading_zero (r : R) : inl r ∈ trivSqZeroExtGrading S R M 0 := by
  simp

/-- `M` sits in degree `1`. -/
theorem inr_mem_trivSqZeroExtGrading_one (m : M) : inr m ∈ trivSqZeroExtGrading S R M 1 := by
  simp

/-- A homogeneous element of nonzero degree has zero `R`-component. -/
theorem fst_eq_zero_of_mem_trivSqZeroExtGrading {n : ℤ} {x : tsze R M}
    (hx : x ∈ trivSqZeroExtGrading S R M n) (hn : n ≠ 0) : x.fst = 0 :=
  (mem_trivSqZeroExtGrading_iff.mp hx).1 hn

/-- A homogeneous element of degree other than `1` has zero `M`-component. -/
theorem snd_eq_zero_of_mem_trivSqZeroExtGrading {n : ℤ} {x : tsze R M}
    (hx : x ∈ trivSqZeroExtGrading S R M n) (hn : n ≠ 1) : x.snd = 0 :=
  (mem_trivSqZeroExtGrading_iff.mp hx).2 hn

variable (S R M) in
/-- The `R`-component of an element of `R ⊕ M`, as an element of degree `0`. -/
private def projZero : tsze R M →ₗ[S] trivSqZeroExtGrading S R M 0 where
  toFun x := ⟨inl x.fst, inl_mem_trivSqZeroExtGrading_zero _⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' s x := Subtype.ext (by simp)

private theorem coe_projZero (x : tsze R M) : (projZero S R M x : tsze R M) = inl x.fst :=
  rfl

variable (S R M) in
/-- The `M`-component of an element of `R ⊕ M`, as an element of degree `1`. -/
private def projOne : tsze R M →ₗ[S] trivSqZeroExtGrading S R M 1 where
  toFun x := ⟨inr x.snd, inr_mem_trivSqZeroExtGrading_one _⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' s x := Subtype.ext (by simp)

private theorem coe_projOne (x : tsze R M) : (projOne S R M x : tsze R M) = inr x.snd :=
  rfl

variable (S R M) in
/-- The homogeneous decomposition of `R ⊕ M`: an element is its `R`-component in degree `0` plus
its `M`-component in degree `1`. -/
private def decomposeGrading : tsze R M →ₗ[S] ⨁ n, trivSqZeroExtGrading S R M n :=
  lof S ℤ (fun n ↦ trivSqZeroExtGrading S R M n) 0 ∘ₗ projZero S R M +
    lof S ℤ (fun n ↦ trivSqZeroExtGrading S R M n) 1 ∘ₗ projOne S R M

/-- Reassembling the homogeneous decomposition of `R ⊕ M` gives back the element. -/
private theorem coeLinearMap_comp_decomposeGrading :
    coeLinearMap (trivSqZeroExtGrading S R M) ∘ₗ decomposeGrading S R M = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    simp [decomposeGrading, coe_projZero, coe_projOne, inl_fst_add_inr_snd_eq]

/-- Decomposing a sum of homogeneous elements of `R ⊕ M` recovers the summands. -/
private theorem decomposeGrading_comp_coeLinearMap :
    decomposeGrading S R M ∘ₗ coeLinearMap (trivSqZeroExtGrading S R M) = LinearMap.id := by
  refine DirectSum.linearMap_ext _ fun n ↦ LinearMap.ext fun ⟨x, hx⟩ ↦ ?_
  simp only [LinearMap.comp_apply, coeLinearMap_lof, LinearMap.id_comp, decomposeGrading,
    LinearMap.add_apply]
  by_cases h₀ : n = 0
  · subst h₀
    have h₁ : projOne S R M x = 0 :=
      Subtype.ext (by simp [coe_projOne, mem_trivSqZeroExtGrading_zero_iff.mp hx])
    have h₂ : projZero S R M x = ⟨x, hx⟩ :=
      Subtype.ext (ext rfl (mem_trivSqZeroExtGrading_zero_iff.mp hx).symm)
    rw [h₁, h₂, map_zero, add_zero]
  by_cases h₁ : n = 1
  · subst h₁
    have h₂ : projZero S R M x = 0 :=
      Subtype.ext (by simp [coe_projZero, mem_trivSqZeroExtGrading_one_iff.mp hx])
    have h₃ : projOne S R M x = ⟨x, hx⟩ :=
      Subtype.ext (ext (mem_trivSqZeroExtGrading_one_iff.mp hx).symm rfl)
    rw [h₂, h₃, map_zero, zero_add]
  · obtain rfl : x = 0 := by simpa [trivSqZeroExtGrading_eq_bot h₀ h₁] using hx
    simp [(Submodule.mk_eq_zero _ hx).mpr rfl]

@[no_expose]
instance : Decomposition (trivSqZeroExtGrading S R M) :=
  Decomposition.ofLinearMap _ (decomposeGrading S R M) coeLinearMap_comp_decomposeGrading
    decomposeGrading_comp_coeLinearMap

/-- The degree-`0` component of an element of `R ⊕ M` is its `R`-component. -/
@[simp]
theorem _root_.TrivSqZeroExt.coe_decompose_trivSqZeroExtGrading_zero (x : tsze R M) :
    (decompose (trivSqZeroExtGrading S R M) x 0 : tsze R M) = inl x.fst := by
  conv_lhs => rw [← inl_fst_add_inr_snd_eq x]
  simp [decompose_of_mem_same _ (inl_mem_trivSqZeroExtGrading_zero _),
    decompose_of_mem_ne _ (inr_mem_trivSqZeroExtGrading_one _) one_ne_zero]

/-- The degree-`1` component of an element of `R ⊕ M` is its `M`-component. -/
@[simp]
theorem _root_.TrivSqZeroExt.coe_decompose_trivSqZeroExtGrading_one (x : tsze R M) :
    (decompose (trivSqZeroExtGrading S R M) x 1 : tsze R M) = inr x.snd := by
  conv_lhs => rw [← inl_fst_add_inr_snd_eq x]
  simp [decompose_of_mem_ne _ (inl_mem_trivSqZeroExtGrading_zero _) zero_ne_one,
    decompose_of_mem_same _ (inr_mem_trivSqZeroExtGrading_one _)]

end Grading

section GradedAlgebra

variable {S R M : Type*} [CommSemiring S] [Semiring R] [AddCommMonoid M] [Algebra S R]
  [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower S R M]
  [IsScalarTower S Rᵐᵒᵖ M]

/-- The trivial square-zero extension `R ⊕ M`, with `R` in degree `0` and `M` in degree `1`, is a
graded algebra: `M · M = 0` lands in degree `2`, where there is nothing. -/
instance instGradedAlgebraTrivSqZeroExtGrading : GradedAlgebra (trivSqZeroExtGrading S R M) where
  one_mem := by simp
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨hx₁, hx₂⟩ := mem_trivSqZeroExtGrading_iff.mp hx
    obtain ⟨hy₁, hy₂⟩ := mem_trivSqZeroExtGrading_iff.mp hy
    refine mem_trivSqZeroExtGrading_iff.mpr ⟨fun hij ↦ ?_, fun hij ↦ ?_⟩
    · by_cases hi : i = 0
      · simp [hy₁ (by omega)]
      · simp [hx₁ hi]
    · rw [snd_mul]
      by_cases hi : i = 0
      · subst hi
        simp [hy₂ (by omega), hx₂ (by omega)]
      · by_cases hi' : i = 1
        · subst hi'
          simp [hx₁ (by omega), hy₁ (by omega)]
        · simp [hx₁ hi, hx₂ hi']

end GradedAlgebra

section Comm

variable {S R M : Type*} [CommSemiring S] [CommRing R] [AddCommGroup M] [Module S R]
  [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

/-- The trivial square-zero extension `R ⊕ M` of a commutative ring by a symmetric module, graded
with `R` in degree `0` and `M` in degree `1`, is graded-commutative: two homogeneous elements
commute up to the Koszul sign. -/
theorem mul_eq_negOnePow_smul_mul_of_mem_trivSqZeroExtGrading {p q : ℤ} {x y : tsze R M}
    (hx : x ∈ trivSqZeroExtGrading S R M p) (hy : y ∈ trivSqZeroExtGrading S R M q) :
    x * y = (p * q).negOnePow • (y * x) := by
  by_cases hpq : Even (p * q)
  · rw [Int.negOnePow_even _ hpq, one_smul, mul_comm]
  · have hp : p ≠ 0 := by rintro rfl; simp at hpq
    have hq : q ≠ 0 := by rintro rfl; simp at hpq
    have hxy : ∀ {a b : tsze R M}, a.fst = 0 → b.fst = 0 → a * b = 0 := fun ha hb ↦
      ext (by simp [ha]) (by simp [ha, hb])
    have hx₁ := fst_eq_zero_of_mem_trivSqZeroExtGrading hx hp
    have hy₁ := fst_eq_zero_of_mem_trivSqZeroExtGrading hy hq
    rw [hxy hx₁ hy₁, hxy hy₁ hx₁, smul_zero]

end Comm

end TauCeti
