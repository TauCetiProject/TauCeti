/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import TauCeti.Algebra.Module.GradedModule.Polynomial
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.Algebra.Module.Torsion.Basic

/-!
# Maximal non-torsion degree of a graded `k[X]`-module

Let `M` be a `ℤ`-graded module over a polynomial ring `k[X]` in which `X` lowers degree by a fixed
`d`. The degrees of the homogeneous elements of `M` that are not torsion form a set
`G.nonTorsionDegrees`. Its supremum `G.maxNonTorsionDegree` is attained, and hence is its maximal
non-torsion degree, when `M` is finitely generated and not torsion (for instance, it is `s` for
`M` the tower `k[X]` shifted so that `1` sits in degree `s`, direct sum a torsion module). This is
the algebraic invariant through which the
concordance invariant `τ` of a knot is defined: `τ(K)` is minus the maximal Alexander grading of a
homogeneous non-torsion element of the unblocked grid homology `GH⁻(K)`, a finitely generated
graded module over `𝔽[U]` on which `U` lowers the Alexander grading by one.

The file shows that the invariant is well behaved without appeal to the structure theorem for
graded `k[X]`-modules:

* over a field, when `X` lowers degree by a nonzero `d`, a homogeneous element is torsion exactly
  when a power of `X` kills it
  (`InternalGrading.mem_torsion_iff_exists_X_pow_smul_eq_zero`), because the terms `c • X ^ n • x`
  of `a • x` lie in pairwise distinct degrees; so `G.nonTorsionDegrees` are the degrees of the
  homogeneous elements no power of `X` kills
  (`InternalGrading.mem_nonTorsionDegrees_iff_forall_X_pow_smul_ne_zero`);
* a finitely generated graded `k[X]`-module has no nonzero homogeneous elements above some degree
  (`InternalGrading.bddAbove_setOf_piece_ne_bot`), so the supremum is attained as soon as `M` is
  not torsion (`InternalGrading.isGreatest_maxNonTorsionDegree`);
* a homogeneous map of degree `δ` that reflects torsion raises the invariant by at least `δ`
  (`InternalGrading.maxNonTorsionDegree_add_le`). This applies in particular when the map has a
  left inverse up to multiplication by a nonzerodivisor such as a power of `X`
  (`Submodule.comap_torsion_le_of_comp_eq_smul`), the shape of the bounds on `τ` coming from
  crossing changes and cobordisms; a graded isomorphism preserves the invariant
  (`InternalGrading.maxNonTorsionDegree_eq_of_linearEquiv`).

Finally, the polynomial ring itself, graded by minus the exponent, has the invariant `0`
(`Polynomial.maxNonTorsionDegree_negDegreeGrading`).

## Main definitions

* `TauCeti.InternalGrading.nonTorsionDegrees`: the degrees of homogeneous non-torsion elements.
* `TauCeti.InternalGrading.maxNonTorsionDegree`: their supremum.
* `TauCeti.Polynomial.negDegreeGrading`: the grading of `k[X]` placing `X ^ n` in degree `-n`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 6: the definition of `τ` as minus the maximal Alexander grading
  of a homogeneous non-torsion element of `GH⁻`, and the crossing-change maps whose composites are
  multiplication by `U`, from which the unknotting-number bound on `τ` follows.
-/

public section

open Polynomial

namespace TauCeti

namespace InternalGrading

section Defs

variable {k M : Type*} [CommSemiring k] [AddCommMonoid M] [Module k M] [Module k[X] M]

/-- The degrees in which a graded `k[X]`-module has a homogeneous element that is not torsion. -/
def nonTorsionDegrees (G : InternalGrading k M) : Set ℤ :=
  {p | ∃ x ∈ G.piece p, x ∉ Submodule.torsion k[X] M}

/-- The maximal non-torsion degree of a graded `k[X]`-module: the supremum of the degrees of its
homogeneous non-torsion elements. It is only meaningful when that set is nonempty and bounded
above, which holds for a finitely generated module that is not torsion and on which `X` lowers
degree (`InternalGrading.isGreatest_maxNonTorsionDegree`). -/
noncomputable def maxNonTorsionDegree (G : InternalGrading k M) : ℤ :=
  sSup G.nonTorsionDegrees

/-- The maximal non-torsion degree is the supremum of the degrees of homogeneous non-torsion
elements. -/
theorem maxNonTorsionDegree_def (G : InternalGrading k M) :
    G.maxNonTorsionDegree = sSup G.nonTorsionDegrees :=
  (rfl)

/-- Membership in `G.nonTorsionDegrees`. -/
@[simp]
theorem mem_nonTorsionDegrees {G : InternalGrading k M} {p : ℤ} :
    p ∈ G.nonTorsionDegrees ↔ ∃ x ∈ G.piece p, x ∉ Submodule.torsion k[X] M :=
  Iff.rfl

/-- Shifting a grading by `c` subtracts `c` from every non-torsion degree. -/
@[simp]
theorem nonTorsionDegrees_shift (G : InternalGrading k M) (c : ℤ) :
    (G.shift c).nonTorsionDegrees = OrderIso.addRight (-c) '' G.nonTorsionDegrees := by
  ext p
  simp only [mem_nonTorsionDegrees, shift_piece, Set.mem_image]
  constructor
  · rintro ⟨x, hx, hxt⟩
    refine ⟨p + c, ⟨x, hx, hxt⟩, ?_⟩
    simp only [OrderIso.addRight_apply]
    omega
  · rintro ⟨q, ⟨x, hx, hxt⟩, rfl⟩
    refine ⟨x, ?_, hxt⟩
    have hqc : OrderIso.addRight (-c) q + c = q := by
      simp only [OrderIso.addRight_apply]
      omega
    rw [hqc]
    exact hx

/-- The maximal non-torsion degree decreases by `c` when the grading is shifted by `c`. -/
theorem maxNonTorsionDegree_shift (G : InternalGrading k M) (c : ℤ)
    (hne : G.nonTorsionDegrees.Nonempty) (hbdd : BddAbove G.nonTorsionDegrees) :
    (G.shift c).maxNonTorsionDegree = G.maxNonTorsionDegree - c := by
  rw [maxNonTorsionDegree_def, nonTorsionDegrees_shift, ← OrderIso.map_csSup' _ hne hbdd,
    OrderIso.addRight_apply, maxNonTorsionDegree_def, sub_eq_add_neg]

/-- A graded `k[X]`-module has a homogeneous non-torsion element exactly when it is not torsion:
if every homogeneous component of `x` is torsion, then so is their sum `x`. -/
@[simp]
theorem nonTorsionDegrees_nonempty_iff (G : InternalGrading k M) :
    G.nonTorsionDegrees.Nonempty ↔ ¬Module.IsTorsion k[X] M := by
  classical
  constructor
  · rintro ⟨p, x, -, hx⟩ hM
    exact hx ((Submodule.mem_torsion_iff x).mpr (@hM x))
  · intro hM
    obtain ⟨x, hx⟩ : ∃ x : M, x ∉ Submodule.torsion k[X] M := by
      by_contra! h
      exact hM fun ⦃x⦄ ↦ (Submodule.mem_torsion_iff x).mp (h x)
    by_contra hG
    refine hx (DirectSum.sum_support_decompose G.piece x ▸ Submodule.sum_mem _ fun p _ ↦ ?_)
    by_contra hp
    exact hG ⟨p, _, (DirectSum.decompose G.piece x p).2, hp⟩

end Defs

section Degree

variable {k M N : Type*} [CommSemiring k]
  [AddCommMonoid M] [Module k M] [Module k[X] M] [IsScalarTower k k[X] M]
  [AddCommMonoid N] [Module k N] [Module k[X] N] [IsScalarTower k k[X] N]
  {G : InternalGrading k M} {H : InternalGrading k N} {d : ℕ}

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

/-- In a finitely generated graded `k[X]`-module on which `X` lowers degree, the degrees of the
homogeneous non-torsion elements are bounded above. -/
theorem bddAbove_nonTorsionDegrees [Module.Finite k[X] M]
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) :
    BddAbove G.nonTorsionDegrees := by
  refine BddAbove.mono ?_ (bddAbove_setOf_piece_ne_bot hX)
  rintro p ⟨x, hx, hxt⟩ hp
  apply hxt
  rw [hp, Submodule.mem_bot] at hx
  exact hx ▸ Submodule.zero_mem _

/-- The maximal non-torsion degree of a finitely generated graded `k[X]`-module that is not
torsion is attained: it is the largest degree of a homogeneous non-torsion element. -/
theorem isGreatest_maxNonTorsionDegree [Module.Finite k[X] M]
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d))
    (hM : ¬Module.IsTorsion k[X] M) :
    IsGreatest G.nonTorsionDegrees G.maxNonTorsionDegree :=
  ⟨Int.csSup_mem (G.nonTorsionDegrees_nonempty_iff.mpr hM) (bddAbove_nonTorsionDegrees hX),
    fun _ hp ↦ le_csSup (bddAbove_nonTorsionDegrees hX) hp⟩

/-- Every degree of a homogeneous non-torsion element is at most the maximal non-torsion degree. -/
theorem le_maxNonTorsionDegree [Module.Finite k[X] M]
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) {p : ℤ}
    (hp : p ∈ G.nonTorsionDegrees) : p ≤ G.maxNonTorsionDegree :=
  le_csSup (bddAbove_nonTorsionDegrees hX) hp

omit [IsScalarTower k k[X] M] [IsScalarTower k k[X] N] in
/-- A homogeneous map of degree `δ` that reflects torsion carries a homogeneous non-torsion element
of degree `p` to one of degree `p + δ`. -/
theorem add_mem_nonTorsionDegrees {f : M →ₗ[k[X]] N} {δ : ℤ}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece δ)
    (hft : (Submodule.torsion k[X] N).comap f ≤ Submodule.torsion k[X] M) {p : ℤ}
    (hp : p ∈ G.nonTorsionDegrees) : p + δ ∈ H.nonTorsionDegrees := by
  obtain ⟨x, hx, hxt⟩ := hp
  exact ⟨f x, hf.map_mem hx, fun h ↦ hxt (hft h)⟩

/-- A homogeneous map of degree `δ` between finitely generated graded `k[X]`-modules that reflects
torsion raises the maximal non-torsion degree by at least `δ`. By
`Submodule.comap_torsion_le_of_comp_eq_smul`, torsion is reflected as soon as the map has a left
inverse up to multiplication by a power of `X`. -/
theorem maxNonTorsionDegree_add_le [Module.Finite k[X] M] [Module.Finite k[X] N]
    (hXM : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d))
    (hXN : ∀ ⦃p : ℤ⦄ ⦃x : N⦄, x ∈ H.piece p → (X : k[X]) • x ∈ H.piece (p - d))
    (hM : ¬Module.IsTorsion k[X] M) {f : M →ₗ[k[X]] N} {δ : ℤ}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece δ)
    (hft : (Submodule.torsion k[X] N).comap f ≤ Submodule.torsion k[X] M) :
    G.maxNonTorsionDegree + δ ≤ H.maxNonTorsionDegree :=
  le_maxNonTorsionDegree hXN
    (add_mem_nonTorsionDegrees hf hft (isGreatest_maxNonTorsionDegree hXM hM).1)

omit [IsScalarTower k k[X] M] [IsScalarTower k k[X] N] in
/-- A graded isomorphism of graded `k[X]`-modules preserves the maximal non-torsion degree. -/
theorem maxNonTorsionDegree_eq_of_linearEquiv (e : M ≃ₗ[k[X]] N)
    (he : LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0)
    (he' : LinearMap.IsHomogeneous e.symm.toLinearMap H.piece G.piece 0) :
    G.maxNonTorsionDegree = H.maxNonTorsionDegree := by
  rw [maxNonTorsionDegree_def, maxNonTorsionDegree_def]
  congr 1
  ext p
  constructor
  · rintro ⟨x, hx, hxt⟩
    refine ⟨e.toLinearMap x, by simpa only [add_zero] using he.map_mem hx, fun het ↦ hxt ?_⟩
    exact Submodule.comap_torsion_le_of_comp_eq_smul (f := e.toLinearMap)
      (g := e.symm.toLinearMap) (one_mem _) (by simp) het
  · rintro ⟨y, hy, hyt⟩
    refine ⟨e.symm.toLinearMap y, by simpa only [add_zero] using he'.map_mem hy, fun het ↦ hyt ?_⟩
    exact Submodule.comap_torsion_le_of_comp_eq_smul (f := e.symm.toLinearMap)
      (g := e.toLinearMap) (one_mem _) (by simp) het

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

end Degree

section Field

variable {k M : Type*} [Field k]
  [AddCommGroup M] [Module k M] [Module k[X] M] [IsScalarTower k k[X] M]
  {G : InternalGrading k M} {d : ℕ}

/-- Over a field, a homogeneous element of a graded `k[X]`-module on which `X` lowers degree by a
nonzero `d` is torsion exactly when some power of `X` kills it. -/
theorem mem_torsion_iff_exists_X_pow_smul_eq_zero (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d))
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) :
    x ∈ Submodule.torsion k[X] M ↔ ∃ n : ℕ, (X ^ n : k[X]) • x = 0 := by
  constructor
  · intro h
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).mp h
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    refine ⟨a.natDegree, ?_⟩
    have key := coe_decompose_smul_of_mem hd hX hx a a.natDegree
    rw [Submonoid.smul_def] at hax
    rw [hax, DirectSum.decompose_zero] at key
    exact (smul_eq_zero.mp key.symm).resolve_left (leadingCoeff_ne_zero.mpr ha0)
  · rintro ⟨n, hn⟩
    exact (Submodule.mem_torsion_iff x).mpr
      ⟨⟨X ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero X_ne_zero) n⟩, hn⟩

/-- Over a field, the degrees of homogeneous non-torsion elements are the degrees of the
homogeneous elements that no power of `X` kills. -/
theorem mem_nonTorsionDegrees_iff_forall_X_pow_smul_ne_zero (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) {p : ℤ} :
    p ∈ G.nonTorsionDegrees ↔ ∃ x ∈ G.piece p, ∀ n : ℕ, (X ^ n : k[X]) • x ≠ 0 := by
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
  rw [mem_torsion_iff_exists_X_pow_smul_eq_zero hd hX hx, not_exists]

end Field

end InternalGrading

namespace Polynomial

variable {k : Type*} [CommSemiring k] [IsDomain k]

/-- The degrees of the homogeneous non-torsion elements of `k[X]`, graded by `negDegreeGrading`,
are the nonpositive integers: every nonzero homogeneous element is a nonzero multiple of a
monomial `X ^ n`, of degree `-n`. -/
@[simp]
theorem nonTorsionDegrees_negDegreeGrading :
    (negDegreeGrading k).nonTorsionDegrees = Set.Iic 0 := by
  ext p
  rw [InternalGrading.mem_nonTorsionDegrees, Set.mem_Iic]
  constructor
  · rintro ⟨x, hx, hxt⟩
    by_contra! hp
    refine hxt ?_
    obtain rfl : x = 0 := by
      ext n
      by_contra hn
      have := mem_negDegreeGrading_piece.mp hx n hn
      omega
    exact Submodule.zero_mem _
  · intro hp
    refine ⟨X ^ (-p).toNat, ?_, fun h ↦ ?_⟩
    · simp [Int.toNat_of_nonneg (neg_nonneg.mpr hp)]
    · obtain ⟨⟨a, ha⟩, h⟩ := (Submodule.mem_torsion_iff _).mp h
      rw [Submonoid.smul_def, smul_eq_mul] at h
      exact pow_ne_zero _ X_ne_zero ((mul_eq_zero.mp h).resolve_left (nonZeroDivisors.ne_zero ha))

/-- The top of the tower `k[X]`, graded by `negDegreeGrading`, sits in degree `0`. -/
@[simp]
theorem maxNonTorsionDegree_negDegreeGrading : (negDegreeGrading k).maxNonTorsionDegree = 0 := by
  rw [InternalGrading.maxNonTorsionDegree_def, nonTorsionDegrees_negDegreeGrading, csSup_Iic]

end Polynomial

end TauCeti
