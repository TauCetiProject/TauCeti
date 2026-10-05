/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Polynomial.Degree.Support
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Graded modules over a polynomial ring

This file records the basic behavior of the action of `k[X]` on an internally `ℤ`-graded module on
which `X` lowers degree by a fixed `d`, and equips `k[X]` itself with the internal grading that
places `X ^ n` in degree `-n`.

## Main definitions

* `TauCeti.Polynomial.negDegreeGrading`: the grading of `k[X]` placing `X ^ n` in degree `-n`.

## Main results

* `TauCeti.InternalGrading.X_pow_smul_mem_piece`: if `X` lowers degree by `d`, then `X ^ n` lowers
  degree by `n * d`.
* `TauCeti.InternalGrading.bddAbove_setOf_piece_ne_bot`: a finitely generated graded `k[X]`-module
  on which `X` lowers degree has no nonzero homogeneous elements above some degree.
* `TauCeti.InternalGrading.coe_decompose_smul_of_mem`: when `X` lowers degree by a nonzero `d`, the
  homogeneous components of `a • x`, for `x` homogeneous, are the terms `a.coeff n • X ^ n • x`.
* `TauCeti.InternalGrading.coe_decompose_smul_of_support_le`: at an upper bound for the support,
  polynomial multiplication acts on the component by the constant coefficient.
* `TauCeti.InternalGrading.smul_injective_of_coeff_zero_ne_zero`: a polynomial with nonzero constant
  coefficient acts injectively when the coefficients form a domain and the module is torsion-free
  over them.
* `TauCeti.Polynomial.mem_negDegreeGrading_piece`: membership in a homogeneous piece is
  characterized coefficientwise.
* `TauCeti.Polynomial.X_smul_mem_negDegreeGrading_piece`: multiplication by `X` lowers degree by
  one.
* `TauCeti.Polynomial.X_pow_mem_negDegreeGrading_piece`: `X ^ n` has degree `-n`.
-/

public section

open Polynomial

namespace TauCeti

namespace InternalGrading

variable {k M : Type*} [CommSemiring k]
  [AddCommMonoid M] [Module k M] [Module k[X] M] [IsScalarTower k k[X] M]
  {G : InternalGrading k M} {d : ℕ}

omit [IsScalarTower k k[X] M] in
/-- If `X` lowers degree by `d`, then `X ^ n` lowers degree by `n * d`. -/
theorem X_pow_smul_mem_piece
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) (n : ℕ)
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) : (X ^ n : k[X]) • x ∈ G.piece (p - n * d) := by
  induction n generalizing p x with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ, mul_smul]
    convert ih (hX hx) using 2
    push_cast
    ring

/-- A finitely generated graded `k[X]`-module on which `X` lowers degree has no nonzero homogeneous
elements above some degree: every element is a `k[X]`-combination of the finitely many homogeneous
components of a finite generating set, and multiplication by a polynomial never raises degree. -/
theorem bddAbove_setOf_piece_ne_bot [Module.Finite k[X] M]
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) :
    BddAbove {p | G.piece p ≠ ⊥} := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k[X]) (M := M)
  -- `D` bounds the degrees of the homogeneous components of the generators.
  obtain ⟨D, hD⟩ : BddAbove (⋃ g ∈ s, ((DirectSum.decompose G.piece g).support : Set ℤ)) :=
    (s.finite_toSet.biUnion fun g _ ↦ Finset.finite_toSet _).bddAbove
  -- `L` is the span of the homogeneous elements of degree at most `D`.
  let L : Submodule k M := ⨆ q : Set.Iic D, G.piece q
  have hXL : ∀ y ∈ L, (X : k[X]) • y ∈ L := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y ↦ (X : k[X]) • y ∈ L) hy
      (fun q y hy ↦ ?_) (by simp) fun y z hy hz ↦ by simpa only [smul_add] using L.add_mem hy hz
    exact Submodule.mem_iSup_of_mem ⟨(q : ℤ) - d, by grind⟩ (hX hy)
  have hXnL : ∀ n : ℕ, ∀ y ∈ L, (X ^ n : k[X]) • y ∈ L := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => exact fun y hy ↦ by simpa only [pow_succ, mul_smul] using ih _ (hXL y hy)
  have hAL : ∀ (a : k[X]), ∀ y ∈ L, a • y ∈ L := by
    intro a
    induction a using Polynomial.induction_on' with
    | add a b ha hb => exact fun y hy ↦ by simpa only [add_smul] using L.add_mem (ha y hy) (hb y hy)
    | monomial n c =>
      intro y hy
      rw [← C_mul_X_pow_eq_monomial, mul_smul, ← algebraMap_eq, algebraMap_smul]
      exact L.smul_mem c (hXnL n y hy)
  let L' : Submodule k[X] M := { L.toAddSubmonoid with smul_mem' := hAL }
  have hL : ∀ y : M, y ∈ L := by
    have hsL : Submodule.span k[X] (s : Set M) ≤ L' := by
      refine Submodule.span_le.mpr fun g hg ↦ ?_
      rw [← DirectSum.sum_support_decompose G.piece g]
      refine L.sum_mem fun q hq ↦ Submodule.mem_iSup_of_mem ⟨q, ?_⟩ (DirectSum.decompose _ g q).2
      exact hD (Set.mem_biUnion hg hq)
    exact fun y ↦ hsL (hs ▸ Submodule.mem_top)
  refine ⟨D, fun p hp ↦ ?_⟩
  by_contra! hDp
  refine hp (eq_bot_iff.mpr fun x hx ↦ ?_)
  refine Submodule.disjoint_def.mp (G.isInternal.submodule_iSupIndep p) x hx ?_
  refine (iSup_le fun q ↦ ?_ : L ≤ ⨆ j, ⨆ (_ : j ≠ p), G.piece j) (hL x)
  exact le_iSup₂_of_le (q : ℤ) (q.2.trans_lt hDp).ne le_rfl

/-- If `X` lowers degree by `d ≠ 0`, the terms `a.coeff n • X ^ n • x` of `a • x`, for `x`
homogeneous of degree `p`, lie in the pairwise distinct degrees `p - n * d`; so the component of
`a • x` in degree `p - n * d` is the `n`-th of them. -/
theorem coe_decompose_smul_of_mem (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d))
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) (a : k[X]) (n : ℕ) :
    (DirectSum.decompose G.piece (a • x) (p - n * d) : M) = a.coeff n • (X ^ n : k[X]) • x := by
  classical
  have hterm : ∀ l : ℕ, (C (a.coeff l) * X ^ l) • x = a.coeff l • (X ^ l : k[X]) • x := by
    intro l
    rw [mul_smul, ← algebraMap_eq, algebraMap_smul]
  have hmem : ∀ l : ℕ, a.coeff l • (X ^ l : k[X]) • x ∈ G.piece (p - l * d) :=
    fun l ↦ Submodule.smul_mem _ _ (X_pow_smul_mem_piece hX l hx)
  conv_lhs => rw [a.as_sum_support_C_mul_X_pow, Finset.sum_smul, DirectSum.decompose_sum]
  simp only [hterm]
  rw [DFinsupp.finsetSum_apply, Submodule.coe_sum, Finset.sum_eq_single n]
  · exact DirectSum.decompose_of_mem_same _ (hmem n)
  · intro l _ hl
    refine DirectSum.decompose_of_mem_ne _ (hmem l) fun h ↦ hl ?_
    have : (l : ℤ) * d = n * d := by omega
    exact_mod_cast mul_right_cancel₀ (by exact_mod_cast hd) this
  · intro hn
    rw [notMem_support_iff.mp hn, zero_smul, DirectSum.decompose_zero, DirectSum.zero_apply,
      ZeroMemClass.coe_zero]

/-- At an upper bound for the degrees of the nonzero components of `x`, polynomial multiplication
acts on the component by its constant coefficient, provided `X` strictly lowers degree. -/
theorem coe_decompose_smul_of_support_le (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d))
    {p : ℤ} {x : M} (hx : ∀ q, p < q → (DirectSum.decompose G.piece x q : M) = 0)
    (a : k[X]) :
    (DirectSum.decompose G.piece (a • x) p : M) =
      a.coeff 0 • (DirectSum.decompose G.piece x p : M) := by
  classical
  have hpow (n : ℕ) :
      (DirectSum.decompose G.piece ((X ^ n : k[X]) • x) p : M) =
        (X ^ n : k[X]) • (DirectSum.decompose G.piece x (p + n * d) : M) := by
    have hf : LinearMap.IsHomogeneous (_root_.LinearMap.lsmul k[X] M (X ^ n))
        G.piece G.piece (-(n : ℤ) * d) := by
      apply LinearMap.isHomogeneous_def.mpr
      intro q y hy
      simpa only [neg_mul, sub_eq_add_neg, _root_.LinearMap.lsmul_apply] using
        X_pow_smul_mem_piece hX n hy
    have key := hf.map_decompose (p + n * d) x
    have hi : p + (n : ℤ) * (d : ℤ) + (-(n : ℤ)) * (d : ℤ) = p := by ring
    simp only [_root_.LinearMap.lsmul_apply] at key
    rw [hi] at key
    exact key.symm
  have hterm (n : ℕ) : (C (a.coeff n) * X ^ n) • x =
      a.coeff n • (X ^ n : k[X]) • x := by
    rw [mul_smul, ← algebraMap_eq, algebraMap_smul]
  conv_lhs => rw [a.as_sum_support_C_mul_X_pow, Finset.sum_smul, DirectSum.decompose_sum]
  simp only [hterm, DirectSum.decompose_smul]
  rw [DFinsupp.finsetSum_apply, Submodule.coe_sum, Finset.sum_eq_single 0]
  · simp [DirectSum.smul_apply]
  · intro n _ hn
    rw [DirectSum.smul_apply, SetLike.val_smul, hpow, hx]
    · simp
    · have : 0 < (n : ℤ) * d := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)
        (by exact_mod_cast Nat.pos_of_ne_zero hd)
      omega
  · intro ha
    simp [notMem_support_iff.mp ha]

end InternalGrading

namespace InternalGrading

variable {k M : Type*} [CommRing k] [IsDomain k] [AddCommGroup M]
  [Module k M] [Module k[X] M] [IsScalarTower k k[X] M] [Module.IsTorsionFree k M]
  {G : InternalGrading k M} {d : ℕ}

/-- A polynomial with nonzero constant coefficient acts injectively on a module graded over a
coefficient domain, if the module is torsion-free over the coefficients and `X` strictly lowers
degree. Polynomial torsion in the module is permitted. -/
theorem smul_injective_of_coeff_zero_ne_zero (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d))
    {a : k[X]} (ha : a.coeff 0 ≠ 0) : Function.Injective (fun x : M ↦ a • x) := by
  classical
  have hzero : ∀ x : M, a • x = 0 → x = 0 := by
    intro x hax
    by_contra hx
    have hs : (DirectSum.decompose G.piece x).support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hs
      have hz := DFinsupp.support_eq_empty.mp hs
      exact hx ((DirectSum.decompose G.piece).injective
        (hz.trans (DirectSum.decompose_zero G.piece).symm))
    -- The largest nonzero component detects multiplication by the constant coefficient.
    let p := (DirectSum.decompose G.piece x).support.max' hs
    have hp : (DirectSum.decompose G.piece x p : M) ≠ 0 := by
      have hp' := DFinsupp.mem_support_iff.mp (Finset.max'_mem _ hs)
      exact fun h ↦ hp' (Subtype.ext h)
    have htop : ∀ q, p < q → (DirectSum.decompose G.piece x q : M) = 0 := by
      intro q hq
      by_contra h
      have hmem : q ∈ (DirectSum.decompose G.piece x).support :=
        DFinsupp.mem_support_iff.mpr (fun hz ↦ h (congrArg Subtype.val hz))
      exact (not_le_of_gt hq) (Finset.le_max' _ q hmem)
    have key := coe_decompose_smul_of_support_le hd hX htop a
    rw [hax, DirectSum.decompose_zero] at key
    exact hp ((smul_eq_zero.mp key.symm).resolve_left ha)
  intro x y hxy
  exact sub_eq_zero.mp (hzero (x - y) (by simp [smul_sub, hxy]))

end InternalGrading

namespace Polynomial

variable (k : Type*) [CommSemiring k]

/-- The grading of the polynomial ring `k[X]` placing the monomial `X ^ n` in degree `-n`, so that
multiplication by `X` lowers degree by one. -/
noncomputable def negDegreeGrading : InternalGrading k k[X] :=
  InternalGrading.map
    ⟨AddMonoidAlgebra.gradeBy k ⇑(-Nat.castAddMonoidHom ℤ), AddMonoidAlgebra.gradeBy.isInternal _⟩
    (toFinsuppIsoLinear k).symm

variable {k}

/-- A polynomial has degree `p` in `negDegreeGrading` exactly when each of its monomials `X ^ n`
has `-n = p`. -/
@[simp]
theorem mem_negDegreeGrading_piece {p : ℤ} {x : k[X]} :
    x ∈ (negDegreeGrading k).piece p ↔ ∀ n, x.coeff n ≠ 0 → -(n : ℤ) = p := by
  rw [negDegreeGrading, InternalGrading.mem_map_piece_iff]
  simp [AddMonoidAlgebra.mem_gradeBy_iff, Set.subset_def, toFinsupp_apply]

/-- Multiplication by `X` lowers the degree of `negDegreeGrading` by one. -/
theorem X_smul_mem_negDegreeGrading_piece {p : ℤ} {x : k[X]}
    (hx : x ∈ (negDegreeGrading k).piece p) :
    (X : k[X]) • x ∈ (negDegreeGrading k).piece (p - 1) := by
  rw [mem_negDegreeGrading_piece] at hx ⊢
  intro n hn
  rw [smul_eq_mul] at hn
  cases n with
  | zero => simp at hn
  | succ n =>
    have := hx n (by rwa [coeff_X_mul] at hn)
    push_cast
    omega

/-- The monomial `X ^ n` has degree `-n` in `negDegreeGrading`. -/
theorem X_pow_mem_negDegreeGrading_piece (n : ℕ) :
    (X ^ n : k[X]) ∈ (negDegreeGrading k).piece (-n) := by
  rw [mem_negDegreeGrading_piece]
  intro m hm
  rw [coeff_X_pow] at hm
  split_ifs at hm with h
  · rw [h]
  · exact absurd rfl hm

end Polynomial

end TauCeti
