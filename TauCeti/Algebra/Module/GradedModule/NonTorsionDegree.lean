/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

* when the coefficients `k` form a domain over which `M` is torsion-free and `X` lowers degree by
  a nonzero `d`, a homogeneous element is torsion exactly when a power of `X` kills it
  (`InternalGrading.mem_torsion_iff_exists_X_pow_smul_eq_zero`), because the terms `c • X ^ n • x`
  of `a • x` lie in pairwise distinct degrees; so `G.nonTorsionDegrees` are the degrees of the
  homogeneous elements no power of `X` kills
  (`InternalGrading.mem_nonTorsionDegrees_iff_forall_X_pow_smul_ne_zero`);
* in a finitely generated graded `k[X]`-module on which `X` lowers degree, the non-torsion degrees
  are bounded above (`InternalGrading.bddAbove_nonTorsionDegrees`), so the supremum is attained as
  soon as `M` is not torsion (`InternalGrading.isGreatest_maxNonTorsionDegree`);
* a homogeneous map of degree `δ` that reflects torsion raises the invariant by at least `δ`, as
  long as both modules are finitely generated, `X` lowers degree on each of them, and the source
  is not torsion (`InternalGrading.maxNonTorsionDegree_add_le`). This applies in particular when
  the map has a left inverse up to multiplication by a nonzerodivisor such as a power of `X`
  (`TauCeti.Submodule.comap_torsion_le_of_comp_eq_smul`), the shape of the bounds on `τ` coming from
  crossing changes and cobordisms; a graded isomorphism preserves the invariant
  (`InternalGrading.maxNonTorsionDegree_eq_of_linearEquiv`).

Finally, the polynomial ring itself, graded by minus the exponent, has the invariant `0`
(`Polynomial.maxNonTorsionDegree_negDegreeGrading`).

## Main definitions

* `TauCeti.InternalGrading.nonTorsionDegrees`: the degrees of homogeneous non-torsion elements.
* `TauCeti.InternalGrading.maxNonTorsionDegree`: their supremum.

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
@[simp]
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

/-- A homogeneous map of degree `δ` that reflects torsion raises the maximal non-torsion degree by
at least `δ`, provided both modules are finitely generated, `X` lowers degree on each of them (by
`dM` on the source and by `dN` on the target), and the source is not torsion, so that its maximal
non-torsion degree is attained. By `Submodule.comap_torsion_le_of_comp_eq_smul`, torsion is
reflected as soon as the map has a left inverse up to multiplication by a power of `X`. -/
theorem maxNonTorsionDegree_add_le [Module.Finite k[X] M] [Module.Finite k[X] N] {dM dN : ℕ}
    (hXM : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - dM))
    (hXN : ∀ ⦃p : ℤ⦄ ⦃x : N⦄, x ∈ H.piece p → (X : k[X]) • x ∈ H.piece (p - dN))
    (hM : ¬Module.IsTorsion k[X] M) {f : M →ₗ[k[X]] N} {δ : ℤ}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece δ)
    (hft : (Submodule.torsion k[X] N).comap f ≤ Submodule.torsion k[X] M) :
    G.maxNonTorsionDegree + δ ≤ H.maxNonTorsionDegree :=
  le_maxNonTorsionDegree hXN
    (add_mem_nonTorsionDegrees hf hft (isGreatest_maxNonTorsionDegree hXM hM).1)

omit [IsScalarTower k k[X] M] [IsScalarTower k k[X] N] in
/-- A graded isomorphism of graded `k[X]`-modules preserves the maximal non-torsion degree. -/
theorem maxNonTorsionDegree_eq_of_linearEquiv (e : M ≃ₗ[k[X]] N)
    (he : LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0) :
    G.maxNonTorsionDegree = H.maxNonTorsionDegree := by
  let ep : (p : ℤ) → G.piece p →+ H.piece p := fun p =>
    { toFun := fun x => ⟨e.toLinearMap (x : M), by
        simpa only [add_zero] using he.map_mem x.2⟩
      map_zero' := Subtype.ext (map_zero e.toLinearMap)
      map_add' := fun x y =>
        Subtype.ext (map_add e.toLinearMap (x : M) (y : M)) }
  have hcomm :
      (DirectSum.coeAddMonoidHom H.piece).comp (DirectSum.map ep) =
        e.toAddEquiv.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom G.piece) := by
    apply DirectSum.addHom_ext
    intro p x
    simp [ep]
  have hmap_surj : Function.Surjective (DirectSum.map ep) := by
    intro y
    obtain ⟨x, hx⟩ := G.isInternal.surjective
      (e.symm (DirectSum.coeAddMonoidHom H.piece y))
    refine ⟨x, H.isInternal.injective ?_⟩
    have hc := DFunLike.congr_fun hcomm x
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hx] at hc
    exact hc.trans (e.apply_symm_apply _)
  have hep_surj : ∀ p, Function.Surjective (ep p) :=
    (DirectSum.map_surjective ep).mp hmap_surj
  have he' : LinearMap.IsHomogeneous e.symm.toLinearMap H.piece G.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p y hy
    obtain ⟨x, hx⟩ := hep_surj p ⟨y, hy⟩
    have hx' : e.toLinearMap (x : M) = y := by
      have := congrArg Subtype.val hx
      dsimp only [ep] at this
      exact this
    have hxy : e.symm.toLinearMap y = (x : M) := by
      calc
        _ = e.symm.toLinearMap (e.toLinearMap (x : M)) := congrArg _ hx'.symm
        _ = _ := e.symm_apply_apply _
    simp only [add_zero]
    rw [hxy]
    exact x.2
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

end Degree

section Domain

variable {k M : Type*} [CommSemiring k] [IsDomain k]
  [AddCommMonoid M] [Module k M] [Module k[X] M] [IsScalarTower k k[X] M]
  [Module.IsTorsionFree k M]
  {G : InternalGrading k M} {d : ℕ}

/-- When the coefficients `k` form a domain over which `M` is torsion-free, a homogeneous element
of a graded `k[X]`-module on which `X` lowers degree by a nonzero `d` is torsion exactly when some
power of `X` kills it. -/
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

/-- When the coefficients `k` form a domain over which `M` is torsion-free, the degrees of the
homogeneous non-torsion elements are the degrees of the homogeneous elements that no power of `X`
kills. -/
theorem mem_nonTorsionDegrees_iff_forall_X_pow_smul_ne_zero (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) {p : ℤ} :
    p ∈ G.nonTorsionDegrees ↔ ∃ x ∈ G.piece p, ∀ n : ℕ, (X ^ n : k[X]) • x ≠ 0 := by
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
  rw [mem_torsion_iff_exists_X_pow_smul_eq_zero hd hX hx, not_exists]

end Domain

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
