/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Positive
import Mathlib.Algebra.Module.Submodule.Union
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Weyl translates of vectors that are not multiples of roots

Let `P` be a finite crystallographic reduced root system over a linearly ordered field, with a base
`b`. Every root is a combination of the simple roots whose coefficients are all of one sign. This
file proves a converse for the Weyl orbit: if a nonzero vector `x` is not a multiple of any root,
then some Weyl translate of `x` has a strictly positive and a strictly negative coefficient with
respect to the simple roots. In particular that translate lies neither in the positive root cone
`Q⁺` nor in its negative.

This is the root-system input to Serre's theorem that the Lie algebra presented by the Serre
relations of a Cartan matrix is finite-dimensional: the weights of the presented algebra other
than `0` lie in `Q⁺ ∪ -Q⁺` and are permuted by the Weyl group together with their weight spaces,
so the weight space of a weight that is not a multiple of a root vanishes.

## The argument

Write `B` for the canonical Weyl-invariant form `RootPairing.RootForm`, which is positive definite
on a root system over an ordered field.

* Because `x` is not a multiple of the root `α`, the vector `B(x, x) α - B(α, x) x` is nonzero and
  `B`-orthogonal to `x`, and it is not orthogonal to `α`. Since a vector space over an infinite
  field is not a finite union of proper subspaces, some single vector `v` orthogonal to `x` is
  orthogonal to no root (`RootPairing.exists_isRegularWeight_rootForm_eq_zero`). Such a `v` is a
  regular weight.
* A Weyl-group element `w` moves `v` into the open dominant chamber, so `B(αᵢ, w v) > 0` for every
  simple root `αᵢ`, while `B(w x, w v) = B(x, v) = 0`. Expanding `w x = ∑ cᵢ αᵢ`, the sum
  `∑ cᵢ B(αᵢ, w v)` vanishes with positive weights `B(αᵢ, w v)` and not all `cᵢ` zero, so the
  `cᵢ` take both signs.

## Main results

* `RootPairing.exists_isRegularWeight_rootForm_eq_zero`: a vector that is not a multiple of any
  root is orthogonal, for the canonical form, to a regular weight.
* `RootPairing.exists_weylGroup_repr_smul_pos_and_neg`: a nonzero vector that is not a multiple of
  any root has a Weyl translate with coefficients of both signs in the basis of simple roots.
* `RootPairing.exists_weylGroup_smul_notMem_posRootCone_and_neg_notMem`: such a translate lies
  neither in the positive root cone nor in its negative.
* `RootPairing.exists_weylGroup_smul_eq_smul_root_or_notMem_posRootCone`: the Weyl orbit of every
  nonzero vector meets the line of a simple root or the complement of `Q⁺ ∪ -Q⁺`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §18.3.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, Appendix.
-/

public section

namespace RootPairing

open TauCeti

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsRootSystem]

section RootForm

variable [Fintype ι]

/-- **A vector that is not a multiple of any root is orthogonal to a regular weight**: for the
canonical form `B` of a finite root system over a linearly ordered field, there is a regular
weight `v` with `B(x, v) = 0`. -/
theorem exists_isRegularWeight_rootForm_eq_zero {x : M}
    (hx : ∀ (i : ι) (c : R), x ≠ c • P.root i) :
    ∃ v : M, IsRegularWeight P v ∧ P.RootForm x v = 0 := by
  have : Infinite R := Infinite.of_injective ((↑) : ℕ → R) Nat.cast_injective
  have hsymm (y z : M) : P.RootForm y z = P.RootForm z y := P.rootForm_symmetric.eq y z
  have haniso (y : M) (hy : P.RootForm y y = 0) : y = 0 := P.rootForm_anisotropic y hy
  -- For each root `α`, the vector `B(x, x) α - B(α, x) x` is orthogonal to `x` but not to `α`.
  obtain ⟨v, hv, hvroot⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
    (LinearMap.ker (P.RootForm x)) (fun i ↦ P.RootForm (P.root i)) fun i ↦ by
      have hxx : P.RootForm x x ≠ 0 := fun h ↦ hx i 0 (by rw [zero_smul]; exact haniso x h)
      set u := P.RootForm x x • P.root i - P.RootForm (P.root i) x • x with hu
      have hxu : P.RootForm x u = 0 := by
        simp only [hu, map_sub, map_smul, smul_eq_mul, hsymm x (P.root i)]
        ring
      refine ⟨u, hxu, fun hαu ↦ ?_⟩
      -- Otherwise `u` would be isotropic, hence zero, and `x` a multiple of `α`.
      have huu : P.RootForm u u = 0 := by
        nth_rw 1 [hu]
        simp [hαu, hxu]
      have hu0 : P.RootForm x x • P.root i = P.RootForm (P.root i) x • x :=
        sub_eq_zero.mp (haniso u huu)
      by_cases hαx : P.RootForm (P.root i) x = 0
      · rw [hαx, zero_smul, smul_eq_zero] at hu0
        exact hu0.elim hxx (P.ne_zero i)
      · refine hx i (P.RootForm x x / P.RootForm (P.root i) x) ?_
        rw [div_eq_inv_mul, mul_smul, hu0, smul_smul, inv_mul_cancel₀ hαx, one_smul]
  refine ⟨v, (isRegularWeight_iff P v).mpr fun i hi ↦ hvroot i ?_, hv⟩
  -- A coroot functional vanishing at `v` makes `v` orthogonal to the corresponding root.
  have h := P.toInvariantForm.two_mul_apply_root v i
  rw [toInvariantForm_form, hi, zero_mul, mul_eq_zero, hsymm] at h
  exact h.resolve_left two_ne_zero

end RootForm

variable [Finite ι] [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **A vector that is not a multiple of a root has a Weyl translate of mixed sign.** For a
nonzero vector `x` of a finite crystallographic reduced root system over a linearly ordered field
that is not a multiple of any root, some Weyl translate of `x` has a positive and a negative
coefficient in the basis of simple roots of the base `b`. -/
theorem exists_weylGroup_repr_smul_pos_and_neg {x : M} (hx₀ : x ≠ 0)
    (hx : ∀ (i : ι) (c : R), x ≠ c • P.root i) :
    ∃ w : P.weylGroup, (∃ i, 0 < b.toWeightBasis.repr (w • x) i) ∧
      ∃ j, b.toWeightBasis.repr (w • x) j < 0 := by
  let := Fintype.ofFinite ι
  have hsymm (y z : M) : P.RootForm y z = P.RootForm z y := P.rootForm_symmetric.eq y z
  obtain ⟨v, hreg, hxv⟩ := P.exists_isRegularWeight_rootForm_eq_zero hx
  -- Move `v` into the open dominant chamber.
  obtain ⟨w, hw⟩ := exists_mem_dominantChamber P b v
  have hwv : w • v ∈ openDominantChamber P b :=
    mem_openDominantChamber_of_isRegularWeight P b hw ((isRegularWeight_smul P w v).mpr hreg)
  -- Every simple root then pairs positively with `w • v`.
  have hpos (i : b.support) : 0 < P.RootForm (P.root i) (w • v) := by
    have h := P.toInvariantForm.two_mul_apply_root (w • v) i
    have hαα : 0 < P.RootForm (P.root i) (P.root i) :=
      (P.zero_le_rootForm _).lt_of_ne fun h' ↦ P.ne_zero i (P.rootForm_anisotropic _ h'.symm)
    rw [toInvariantForm_form, hsymm] at h
    nlinarith [(mem_openDominantChamber P b _).mp hwv i i.2]
  -- Expanding `w • x` in the simple roots, `B(w • x, w • v) = 0` is a vanishing positive-weighted
  -- sum of its coefficients.
  set c := b.toWeightBasis.repr (w • x)
  have hsum : ∑ i, c i * P.RootForm (P.root i) (w • v) = 0 := by
    have hexp := b.toWeightBasis.sum_repr (w • x)
    have hinv := InvariantForm.apply_weylGroup_smul P (B := P.toInvariantForm) w x v
    rw [toInvariantForm_form] at hinv
    rw [← hinv, ← hexp, map_sum] at hxv
    simpa [c] using hxv
  have hne : c ≠ 0 := by
    simpa [c] using (smul_ne_zero_iff_ne w).mpr hx₀
  -- A vanishing positive-weighted sum of nonzero coefficients has a positive coefficient.
  have hexists (d : b.support →₀ R) (hd : ∑ i, d i * P.RootForm (P.root i) (w • v) = 0)
      (hd₀ : d ≠ 0) : ∃ i, 0 < d i := by
    by_contra! h
    refine hd₀ (Finsupp.ext fun i ↦ ?_)
    have := (Finset.sum_eq_zero_iff_of_nonpos fun j _ ↦
      mul_nonpos_of_nonpos_of_nonneg (h j) (hpos j).le).mp hd i (Finset.mem_univ i)
    simpa [(hpos i).ne'] using this
  obtain ⟨j, hj⟩ := hexists (-c)
    (by simp only [Finsupp.neg_apply, neg_mul, Finset.sum_neg_distrib, hsum, neg_zero])
    (neg_ne_zero.mpr hne)
  exact ⟨w, hexists c hsum hne, j, by simpa using hj⟩

/-- **A vector that is not a multiple of a root has a Weyl translate outside `Q⁺ ∪ -Q⁺`.** For a
nonzero vector `x` of a finite crystallographic reduced root system over a linearly ordered field
that is not a multiple of any root, some Weyl translate of `x` lies neither in the positive root
cone of the base `b` nor in its negative. -/
theorem exists_weylGroup_smul_notMem_posRootCone_and_neg_notMem {x : M} (hx₀ : x ≠ 0)
    (hx : ∀ (i : ι) (c : R), x ≠ c • P.root i) :
    ∃ w : P.weylGroup, w • x ∉ posRootCone P b ∧ -(w • x) ∉ posRootCone P b := by
  obtain ⟨w, ⟨i, hi⟩, j, hj⟩ := P.exists_weylGroup_repr_smul_pos_and_neg b hx₀ hx
  refine ⟨w, fun h ↦ (toWeightBasis_repr_nonneg_of_mem_posRootCone h j).not_gt hj, fun h ↦ ?_⟩
  have := toWeightBasis_repr_nonneg_of_mem_posRootCone h i
  rw [map_neg, Finsupp.neg_apply, neg_nonneg] at this
  exact this.not_gt hi

/-- **The Weyl orbit of a nonzero vector meets a simple-root line or leaves `Q⁺ ∪ -Q⁺`.** For a
nonzero vector `x` of a finite crystallographic reduced root system over a linearly ordered field,
either some Weyl translate of `x` is a multiple of a simple root of the base `b`, or some Weyl
translate of `x` lies neither in the positive root cone nor in its negative. -/
theorem exists_weylGroup_smul_eq_smul_root_or_notMem_posRootCone {x : M} (hx₀ : x ≠ 0) :
    (∃ w : P.weylGroup, ∃ i ∈ b.support, ∃ c : R, w • x = c • P.root i) ∨
      ∃ w : P.weylGroup, w • x ∉ posRootCone P b ∧ -(w • x) ∉ posRootCone P b := by
  by_cases h : ∃ (j : ι) (c : R), x = c • P.root j
  · -- A multiple of a root is carried to a multiple of a simple root, as the root is.
    obtain ⟨j, c, rfl⟩ := h
    obtain ⟨i, hi, w, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b j
    refine .inl ⟨w⁻¹, i, hi, c, ?_⟩
    rw [← P.weylGroup_apply_root, smul_comm, inv_smul_smul]
  · push Not at h
    exact .inr (P.exists_weylGroup_smul_notMem_posRootCone_and_neg_notMem b hx₀ h)

end RootPairing
