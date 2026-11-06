/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.EngelSubalgebra
public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.Geometry.Symplectic.AlmostComplex
import Mathlib.LinearAlgebra.Center
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import TauCeti.Algebra.Lie.OfAssociative
import TauCeti.Algebra.Lie.SkewAdjoint
import TauCeti.LinearAlgebra.End.SquareZero

/-!
# The symplectic Lie algebra of a symplectic plane

Let `(V, ω)` be a two-dimensional real symplectic vector space. This file records the linear
algebra of `V` and of its symplectic Lie algebra `sp(V, ω)`, Mathlib's
`skewAdjointLieSubalgebra ω`, viewed as a Lie subalgebra of `Module.End ℝ V` for the commutator
bracket.

## Main results

* `TauCeti.SymplecticForm.not_linearIndependent_of_apply_eq_zero`: two vectors pairing trivially
  under `ω` are linearly dependent.
* `TauCeti.SymplecticForm.exists_eq_smul_one_of_apply_left`: an endomorphism self-adjoint for `ω`
  is a homothety.
* `TauCeti.SymplecticForm.eq_zero_of_smul_one_mem`: the only homothety in `sp(V, ω)` is `0`.
* `TauCeti.SymplecticForm.exists_mul_self_eq_smul_one`: the square of an element of `sp(V, ω)` is
  a homothety.
* `TauCeti.SymplecticForm.exists_eq_smul_of_commute`: the centralizer in `sp(V, ω)` of a nonzero
  element `A` is the line spanned by `A`.
* `TauCeti.SymplecticForm.lie_eq_zero_of_lie_lie_eq_zero`: if `A² ≠ 0`, then `ad A` has no Jordan
  block of size two at the eigenvalue `0`.
* `TauCeti.SymplecticForm.engel_le_lieSpan_singleton`: if `A² ≠ 0`, the Engel subalgebra of `A`
  is the line spanned by `A`.
* `TauCeti.SymplecticForm.not_isCartanSubalgebra_lieSpan_singleton`: if `A² = 0`, the line spanned
  by `A` is not a Cartan subalgebra.
-/

public section

open LieSubalgebra Module

-- `sp(V, ω)` is a Lie subalgebra of `Module.End ℝ V` for the commutator bracket, as in Mathlib's
-- `Mathlib.Algebra.Lie.SkewAdjoint`.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

/-- In dimension two, two vectors pairing trivially under `ω` are linearly dependent. -/
theorem not_linearIndependent_of_apply_eq_zero (hV : finrank ℝ V = 2) {v w : V}
    (h : ω v w = 0) : ¬LinearIndependent ℝ ![v, w] := by
  intro hli
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV])
  have hb : ∀ i, ω.toBilinForm v (b i) = 0 := by
    intro i
    fin_cases i
    · simp [b]
    · simpa [b] using h
  have hv : ω.toBilinForm v = 0 := b.ext fun i ↦ by simpa using hb i
  have : v = 0 := ω.nondegenerate.1 v fun w ↦ by simp [hv]
  exact hli.ne_zero 0 (by simpa using this)

/-- In dimension two, an endomorphism self-adjoint for `ω` is a homothety. -/
theorem exists_eq_smul_one_of_apply_left (hV : finrank ℝ V = 2) {S : Module.End ℝ V}
    (hS : ∀ v w, ω (S v) w = ω v (S w)) : ∃ c : ℝ, S = c • 1 := by
  refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent fun v ↦ ?_
  refine not_linearIndependent_of_apply_eq_zero (ω := ω) hV ?_
  have h₂ := ω.neg_eq v (S v)
  have h₃ := hS v v
  linarith

/-- A homothety is skew-adjoint for `ω` only when it vanishes. -/
theorem eq_zero_of_smul_one_mem [Nontrivial V] {c : ℝ}
    (hc : c • (1 : Module.End ℝ V) ∈ skewAdjointLieSubalgebra ω.toBilinForm) : c = 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ : ∃ w, ω v w ≠ 0 := by
    by_contra! h
    exact hv (ω.nondegenerate.1 v h)
  have h := skewAdjointLieSubalgebra.apply_left ⟨_, hc⟩ v w
  beta_reduce at h
  simp only [LinearMap.smul_apply, one_apply_eq_self, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at h
  have : 2 * c * ω v w = 0 := by linarith
  simpa [hw] using this

/-- In dimension two, the square of an element of `sp(V, ω)` is a homothety. -/
theorem exists_mul_self_eq_smul_one (hV : finrank ℝ V = 2)
    (A : skewAdjointLieSubalgebra ω.toBilinForm) :
    ∃ c : ℝ, (A : Module.End ℝ V) * A = c • 1 := by
  refine exists_eq_smul_one_of_apply_left (ω := ω) hV fun v w ↦ ?_
  have h₁ := skewAdjointLieSubalgebra.apply_left A ((A : Module.End ℝ V) v) w
  have h₂ := skewAdjointLieSubalgebra.apply_left A v ((A : Module.End ℝ V) w)
  simp only [mul_apply_eq_comp]
  beta_reduce at h₁ h₂ ⊢
  rw [h₁, h₂, neg_neg]

/-- In dimension two, an element of `sp(V, ω)` commuting with a nonzero element `A` of `sp(V, ω)`
is a multiple of `A`. -/
theorem exists_eq_smul_of_commute (hV : finrank ℝ V = 2)
    {A B : skewAdjointLieSubalgebra ω.toBilinForm} (hA : A ≠ 0)
    (hAB : Commute (A : Module.End ℝ V) B) : ∃ t : ℝ, B = t • A := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  -- `A` is not a homothety, so some `v` is not an eigenvector of `A`.
  obtain ⟨v, hv⟩ : ∃ v, LinearIndependent ℝ ![v, (A : Module.End ℝ V) v] := by
    by_contra! h
    obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent h
    have hc0 : c = 0 := eq_zero_of_smul_one_mem (hc ▸ A.2)
    exact hA (Subtype.ext (by simpa [hc0] using hc))
  let b := basisOfLinearIndependentOfCardEqFinrank hv (by simp [hV])
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = (A : Module.End ℝ V) v := by simp [b]
  -- Write `B v = a v + t A v`; then `B = a + t A` on the basis `v, A v`.
  have hBv := b.sum_repr ((B : Module.End ℝ V) v)
  rw [Fin.sum_univ_two, hb0, hb1] at hBv
  set a := b.repr ((B : Module.End ℝ V) v) 0
  set t := b.repr ((B : Module.End ℝ V) v) 1
  have hBeq : (B : Module.End ℝ V) - t • (A : Module.End ℝ V) = a • 1 := by
    refine b.ext fun i ↦ ?_
    fin_cases i
    · simp only [Fin.zero_eta, hb0, LinearMap.sub_apply, LinearMap.smul_apply,
        one_apply_eq_self]
      rw [← hBv]
      abel
    · simp only [Fin.mk_one, hb1, LinearMap.sub_apply, LinearMap.smul_apply,
        one_apply_eq_self]
      rw [← mul_apply_eq_comp, ← hAB.eq, mul_apply_eq_comp, ← hBv]
      simp only [map_add, map_smul]
      abel
  have ha : a = 0 := eq_zero_of_smul_one_mem (by
    rw [← hBeq]
    exact sub_mem B.2 (Submodule.smul_mem _ t A.2))
  refine ⟨t, Subtype.ext ?_⟩
  rw [ha, zero_smul, sub_eq_zero] at hBeq
  simpa using hBeq

/-- In dimension two, if `A ∈ sp(V, ω)` squares to a nonzero homothety `c`, then `ad A` has no
Jordan block of size two at the eigenvalue `0`: `⁅A, ⁅A, B⁆⁆ = 0` implies `⁅A, B⁆ = 0`. -/
theorem lie_eq_zero_of_lie_lie_eq_zero (hV : finrank ℝ V = 2)
    {A B : skewAdjointLieSubalgebra ω.toBilinForm} {c : ℝ} (hc : c ≠ 0)
    (hA : (A : Module.End ℝ V) * A = c • 1) (hB : ⁅A, ⁅A, B⁆⁆ = 0) : ⁅A, B⁆ = 0 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hA0 : A ≠ 0 := by
    rintro rfl
    exact hc (by simpa using hA.symm)
  -- `C = ⁅A, B⁆` commutes with `A`, so `C = t A`; and `A C + C A = A² B - B A² = 0` while
  -- `A C + C A = 2 t c`.
  obtain ⟨t, ht⟩ := exists_eq_smul_of_commute hV hA0 (commute_coe_iff.2 hB)
  have hsum : (A : Module.End ℝ V) * (⁅A, B⁆ : skewAdjointLieSubalgebra ω.toBilinForm) +
      ((⁅A, B⁆ : skewAdjointLieSubalgebra ω.toBilinForm) : Module.End ℝ V) * A = 0 := by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def]
    have : (A : Module.End ℝ V) * (A * B - B * A) + (A * B - B * A) * A =
        (A * A) * B - B * (A * A) := by noncomm_ring
    rw [this, hA, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, sub_self]
  rw [ht, SetLike.val_smul, mul_smul_comm, smul_mul_assoc, hA, smul_smul, ← add_smul] at hsum
  have ht0 : t = 0 := by
    have : t * c = 0 := by linarith [(smul_eq_zero.1 hsum).resolve_right one_ne_zero]
    exact (mul_eq_zero.1 this).resolve_right hc
  rw [ht, ht0, zero_smul]

/-- In dimension two, if `A ∈ sp(V, ω)` squares to a nonzero homothety, then its Engel subalgebra
is the line spanned by `A`. -/
theorem engel_le_lieSpan_singleton (hV : finrank ℝ V = 2)
    {A : skewAdjointLieSubalgebra ω.toBilinForm} {c : ℝ} (hc : c ≠ 0)
    (hA : (A : Module.End ℝ V) * A = c • 1) :
    engel ℝ A ≤ lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm) {A} := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hA0 : A ≠ 0 := by
    rintro rfl
    exact hc (by simpa using hA.symm)
  have hpow : ∀ n B, ((LieAlgebra.ad ℝ _ A) ^ (n + 1)) B = 0 → ⁅A, B⁆ = 0 := by
    intro n
    induction n with
    | zero => intro B hB; simpa using hB
    | succ n ih =>
      intro B hB
      rw [pow_succ, mul_apply_eq_comp] at hB
      exact lie_eq_zero_of_lie_lie_eq_zero hV hc hA (by simpa using ih _ hB)
  intro B hB
  obtain ⟨n, hn⟩ := (mem_engel_iff ℝ A B).1 hB
  rw [← LieSubalgebra.mem_toSubmodule, coe_lieSpan_eq_span_of_forall_lie_eq_zero (by simp)]
  cases n with
  | zero => simp only [pow_zero, one_apply_eq_self] at hn; simp [hn]
  | succ n =>
    obtain ⟨t, rfl⟩ := exists_eq_smul_of_commute hV hA0 (commute_coe_iff.2 (hpow n B hn))
    exact Submodule.smul_mem _ t (Submodule.subset_span rfl)

/-- In dimension two, the line spanned by an element `A ∈ sp(V, ω)` with `A² = 0` is not a Cartan
subalgebra: it is properly contained in its normalizer. -/
theorem not_isCartanSubalgebra_lieSpan_singleton (hV : finrank ℝ V = 2)
    {A : skewAdjointLieSubalgebra ω.toBilinForm} (hA : (A : Module.End ℝ V) * A = 0) :
    ¬(lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm) {A}).IsCartanSubalgebra := by
  intro hcartan
  obtain ⟨v, u, hli, hu, s, hv⟩ := Module.End.exists_linearIndependent_of_mul_self_eq_zero _ hV hA
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV])
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  -- The endomorphism `B` with `B v = -v`, `B u = u` lies in `sp(V, ω)` and `⁅B, A⁆ = 2 A`.
  let B : Module.End ℝ V := b.constr ℝ ![-v, u]
  have hBv : B v = -v := by simpa [hb0, B] using b.constr_basis ℝ ![-v, u] 0
  have hBu : B u = u := by simpa [hb1, B] using b.constr_basis ℝ ![-v, u] 1
  have hBmem : B ∈ skewAdjointLieSubalgebra ω.toBilinForm := by
    refine (LinearMap.mem_skewAdjointSubmodule B).2 fun x y ↦ ?_
    have : ω.toBilinForm.compl₁₂ B LinearMap.id =
        -ω.toBilinForm.compl₁₂ LinearMap.id B := by
      refine LinearMap.ext_basis b b fun i j ↦ ?_
      fin_cases i <;> fin_cases j <;>
        simp [hb0, hb1, hBv, hBu, ← ω.neg_eq u v]
    simpa using LinearMap.congr_fun₂ this x y
  let B' : skewAdjointLieSubalgebra ω.toBilinForm := ⟨B, hBmem⟩
  have hBA : ⁅B', A⁆ = (2 : ℝ) • A := by
    refine Subtype.ext (b.ext fun i ↦ ?_)
    fin_cases i
    · simp [B', LieRing.of_associative_ring_bracket, hb0, hv, hBv, hBu, two_smul]
    · simp [B', LieRing.of_associative_ring_bracket, hb1, hu, hBu]
  have hspan : ((lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm) {A}) :
      Submodule ℝ (skewAdjointLieSubalgebra ω.toBilinForm)) = Submodule.span ℝ {A} :=
    coe_lieSpan_eq_span_of_forall_lie_eq_zero (by simp)
  have hnorm : B' ∈ (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm) {A}).normalizer := by
    refine (mem_normalizer_iff _ _).2 fun y hy ↦ ?_
    rw [← LieSubalgebra.mem_toSubmodule, hspan] at hy ⊢
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [lie_smul, hBA, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self A)
  rw [hcartan.self_normalizing, ← LieSubalgebra.mem_toSubmodule, hspan] at hnorm
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hnorm
  have := congrArg (fun C : skewAdjointLieSubalgebra ω.toBilinForm ↦ (C : Module.End ℝ V) u) ht
  simp [B', hu, hBu] at this
  exact hli.ne_zero 1 (by simpa using this.symm)

end TauCeti.SymplecticForm
