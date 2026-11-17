/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Bases
import Mathlib.Algebra.Module.Submodule.Union
import TauCeti.LinearAlgebra.RootSystem.Inversions.Exchange
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# Making an integral coweight dominant and uniqueness in a Weyl orbit

Let `P` be a reduced crystallographic root system over a field of characteristic zero, and let
`x` be a coweight on which every root takes an integer value. This file proves that some base of
`P` makes `x` dominant: every simple root takes a natural-number value at `x`
(`RootPairing.exists_base_forall_exists_nat_root'_apply`).

The coefficient field carries no order, so the usual argument through Weyl chambers is not
available directly. The base is instead built with Mathlib's `IsAddIndecomposable.baseOf`, as in
the proof of `RootPairing.nonempty_base`.

Since the Weyl group acts simply transitively on the bases
(`RootPairing.Base.existsUnique_map_eq`), the base may instead be fixed in advance and the coweight
moved: some element of the Weyl group carries `x` to a coweight that is dominant for the given base
(`RootPairing.Base.exists_forall_exists_nat_root'_coweightEquiv_apply`).

The dominant representative in a Weyl orbit is also **unique**, over any integral domain of
characteristic zero (`RootPairing.Base.coweightEquiv_eq_self_of_forall_exists_nat_root'`): by
induction on the number of inversions of `w`, if both `x` and `w.coweightEquiv x` take
natural-number values on the simple roots of `b`, any simple inversion `i` of `w` forces
`P.root' i (w.coweightEquiv x)` to be simultaneously a natural number and the negative of a natural
number, hence zero; composing with the simple coreflection in `i` preserves `w.coweightEquiv x`
and drops the inversion count by one. Together, existence and uniqueness show that every integral
coweight has a unique dominant representative in its Weyl orbit
(`RootPairing.Base.existsUnique_coweightEquiv_forall_exists_nat_root'`). For integral coweights
this is the counterpart, over a field of characteristic zero carrying no order, of the
ordered-field fundamental-domain theorem `TauCeti.existsUnique_mem_orbit_inter_dominantChamber`.

In the Lie-theoretic application `x` is the neutral element `h` of an `sl₂` triple lying in a
splitting Cartan subalgebra: its roots take integer values, and a base making `h` dominant puts the
nilpositive element of the triple into the positive nilradical.

## Main results

* `RootPairing.exists_base_forall_exists_nat_root'_apply`: a coweight on which every root takes an
  integer value is dominant for some base.
* `RootPairing.Base.exists_forall_exists_nat_root'_coweightEquiv_apply`: such a coweight is
  carried by the Weyl group to a coweight that is dominant for a given base.
* `RootPairing.Base.coweightEquiv_eq_self_of_forall_exists_nat_root'` and
  `RootPairing.Base.eq_of_coweightEquiv_eq_of_forall_exists_nat_root'`: a dominant integral coweight
  is the unique dominant integral coweight in its Weyl orbit, over any integral domain of
  characteristic zero.
* `RootPairing.Base.existsUnique_coweightEquiv_forall_exists_nat_root'`: every integral coweight
  has a unique dominant representative in its Weyl orbit.

## References

* J.-P. Serre, *Algèbres de Lie semi-simples complexes*, Benjamin, 1966, Ch. V, §8.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Ch. V, §3.
-/

public section

open Module IsAddIndecomposable

namespace RootPairing

variable {ι R M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N] [Field R] [CharZero R]
  [Module R M] [Module R N] (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced]

/-- **An integral coweight is dominant for some base.** If every root takes an integer value at
the coweight `x`, then some base of `P` makes `x` dominant: every simple root takes a natural
value at `x`. -/
theorem exists_base_forall_exists_nat_root'_apply (x : N) (hx : ∀ i, ∃ z : ℤ, P.root' i x = z) :
    ∃ b : P.Base, ∀ i ∈ b.support, ∃ n : ℕ, P.root' i x = n := by
  -- Pairing with `x`, followed by a `ℚ`-linear retraction of `R` onto `ℚ`, is an additive map `g`
  -- taking the integer value `⟨α, x⟩` at each root `α`. It may vanish on some roots, so it is
  -- scaled and perturbed by a functional `f₀` vanishing on no root: with `n` larger than every
  -- `|f₀ α|`, the map `f = n • g + f₀` vanishes on no root, and is positive on a root only if `g`
  -- is nonnegative there. The simple roots of `baseOf f` are positive for `f`, hence take natural
  -- values at `x`.
  choose z hz using hx
  -- a `ℚ`-linear retraction of `R` onto `ℚ` turns pairing with `x` into a `ℚ`-valued map
  obtain ⟨π, hπ⟩ := (Algebra.linearMap ℚ R).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ R).injective)
  let g : M →+ ℚ := π.toAddMonoidHom.comp (P.toLinearMap.flip x).toAddMonoidHom
  have hg (i : ι) : g (P.root i) = z i := by
    have := LinearMap.congr_fun hπ (z i : ℚ)
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, eq_ratCast,
      Rat.cast_intCast, LinearMap.id_coe, id_eq] at this
    simpa [g, root', hz] using this
  -- a functional vanishing on no root, used to break the ties where `g` vanishes
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  obtain ⟨f₀, hf₀⟩ : ∃ f : Dual ℚ M, ∀ i, f (P.root i) ≠ 0 :=
    exists_dual_forall_apply_ne_zero P.root <| by simp [P.ne_zero]
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hn⟩ := exists_nat_gt (∑ i, |f₀ (P.root i)|)
  have hlt (i : ι) : |f₀ (P.root i)| < n :=
    (Finset.single_le_sum (fun j _ ↦ abs_nonneg (f₀ (P.root j))) (Finset.mem_univ i)).trans_lt hn
  let f : M →+ ℚ := n • g + (f₀ : M →+ ℚ)
  have hf (i : ι) : f (P.root i) = n * z i + f₀ (P.root i) := by
    simp [f, hg]
  -- `f` vanishes on no root, and is positive on a root only where `g` is nonnegative
  have hf0 (i : ι) : f (P.root i) ≠ 0 := by
    have := abs_lt.mp (hlt i)
    rcases lt_trichotomy (z i) 0 with h | h | h
    · have : (z i : ℚ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
      rw [hf]; nlinarith
    · simpa [hf, h] using hf₀ i
    · have : (1 : ℚ) ≤ z i := by exact_mod_cast h
      rw [hf]; nlinarith
  have hpos (i : ι) (hi : 0 < f (P.root i)) : 0 ≤ z i := by
    by_contra! h
    have : (z i : ℚ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
    have := abs_lt.mp (hlt i)
    rw [hf] at hi
    nlinarith
  let := P.indexNeg
  let b : P.Base := Base.mk' P (baseOf P.root f) (P.linearIndepOn_root_baseOf f hf0)
    fun i ↦ mem_or_neg_mem_closure_baseOf P.root f i (hf0 i) (by simp)
  refine ⟨b, fun i hi ↦ ⟨(z i).toNat, ?_⟩⟩
  have hi' : i ∈ baseOf P.root f := by simpa [b, Base.mk'] using hi
  rw [hz i, ← Int.cast_natCast, Int.toNat_of_nonneg (hpos i (baseOf_subset_pos P.root f hi'))]

variable {P} in
/-- **An integral coweight is Weyl-conjugate to a dominant one.** Fix a base `b`. If every root
takes an integer value at the coweight `x`, then some element `w` of the Weyl group carries `x`,
through its action `RootPairing.Equiv.coweightEquiv` on coweights, to a coweight at which every
simple root of `b` takes a natural value. -/
theorem Base.exists_forall_exists_nat_root'_coweightEquiv_apply (b : P.Base) (x : N)
    (hx : ∀ i, ∃ z : ℤ, P.root' i x = z) :
    ∃ w : P.weylGroup, ∀ i ∈ b.support, ∃ n : ℕ, P.root' i ((w : P.Aut).coweightEquiv x) = n := by
  classical
  -- a base `b'` making `x` dominant, and the Weyl group element carrying `b'` onto `b`
  obtain ⟨b', hb'⟩ := P.exists_base_forall_exists_nat_root'_apply x hx
  obtain ⟨w, hw, -⟩ := b'.existsUnique_map_eq b
  refine ⟨w⁻¹, fun i hi ↦ ?_⟩
  rw [← hw, Base.support_map_eq, Finset.mem_image] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  obtain ⟨n, hn⟩ := hb' j hj
  refine ⟨n, ?_⟩
  rw [← hn, ← (w : P.Aut).root'_coweightEquiv j x]
  simp

end RootPairing

namespace RootPairing.Base

open TauCeti

section Unique

variable {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N] [CommRing R] [CharZero R]
  [Module R M] [Module R N] {P : RootPairing ι R M N} (b : P.Base)

private theorem exists_nat_root'_of_mem_posRoots {x : N}
    (hx : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i x = n) {i : ι} (hi : i ∈ posRoots P b) :
    ∃ n : ℕ, P.root' i x = n := by
  classical
  obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp (root_mem_posRootCone_of_mem_posRoots P b hi)
  choose g hg using hx
  refine ⟨∑ j ∈ b.support.attach, f j.1 * g j.1 j.2, ?_⟩
  have hval : P.toLinearMap (P.root i) x = ∑ j ∈ b.support, f j • P.toLinearMap (P.root j) x := by
    rw [hf, map_sum, LinearMap.sum_apply]
    simp [map_nsmul, LinearMap.smul_apply]
  rw [root', hval, ← Finset.sum_attach b.support]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [nsmul_eq_mul, ← root', hg j.1 j.2]

private theorem exists_nat_neg_root'_of_mem_negRoots {x : N}
    (hx : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i x = n) {i : ι} (hi : i ∈ negRoots P b) :
    ∃ m : ℕ, P.root' i x = -(m : R) := by
  have hpos : P.reflectionPerm i i ∈ posRoots P b :=
    (mem_posRoots P b _).mpr ((isPos_reflectionPerm_self_iff_mem_negRoots P b i).mpr hi)
  obtain ⟨m, hm⟩ := exists_nat_root'_of_mem_posRoots b hx hpos
  refine ⟨m, ?_⟩
  have hneg : P.root' (P.reflectionPerm i i) x = -P.root' i x := by
    simp [root', RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  rw [hneg] at hm
  exact neg_eq_iff_eq_neg.mp hm

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

private theorem coweightEquiv_eq_self_aux (n : ℕ) (w : P.weylGroup)
    (hn : (inversions P b w).ncard ≤ n) {x : N}
    (hx : ∀ i ∈ b.support, ∃ m : ℕ, P.root' i x = m)
    (hw : ∀ i ∈ b.support, ∃ m : ℕ, P.root' i ((w : P.Aut).coweightEquiv x) = m) :
    (w : P.Aut).coweightEquiv x = x := by
  induction n generalizing w with
  | zero =>
    have hempty : inversions P b w = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).mp (Nat.le_zero.mp hn)
    rw [eq_one_of_inversions_eq_empty hempty]
    simp
  | succ n ih =>
    rcases eq_or_ne w 1 with rfl | hne
    · simp
    obtain ⟨i, hi, hiw⟩ := exists_mem_support_mem_inversions_of_ne_one P b hne
    have hneg : P.weylGroupToPerm w i ∈ negRoots P b :=
      (mem_negRoots P b _).mpr ((mem_inversions P b w i).mp hiw).2
    -- `P.root' i (w.coweightEquiv x) = P.root' (w i) x` is both `≥ 0` and `≤ 0` in `ℕ`, hence `0`.
    have heval : P.root' i ((w : P.Aut).coweightEquiv x) =
        P.root' (P.weylGroupToPerm w i) x := by
      have h := (w : P.Aut).root'_coweightEquiv i ((w : P.Aut).coweightEquiv x)
      simpa using h.symm
    obtain ⟨a, ha⟩ := hw i hi
    obtain ⟨c, hc⟩ := exists_nat_neg_root'_of_mem_negRoots b hx hneg
    have hzero_sum : ((a + c : ℕ) : R) = 0 := by
      push_cast
      rw [← ha, heval, hc, neg_add_cancel]
    have ha0 : a = 0 := by
      have h := Nat.cast_eq_zero.mp hzero_sum
      omega
    have hri : P.root' i ((w : P.Aut).coweightEquiv x) = 0 := by
      rw [ha, ha0, Nat.cast_zero]
    -- The simple coreflection in `i` fixes `w.coweightEquiv x` and lowers the inversion count.
    have hmul : ((w * RootPairing.weylGroup.ofIdx P i : P.weylGroup) : P.Aut).coweightEquiv x =
        (w : P.Aut).coweightEquiv x := by
      have hcomp : ((w * RootPairing.weylGroup.ofIdx P i : P.weylGroup) : P.Aut).coweightEquiv =
          (w : P.Aut).coweightEquiv ≪≫ₗ
            ((RootPairing.weylGroup.ofIdx P i : P.weylGroup) : P.Aut).coweightEquiv := by
        simp [RootPairing.Equiv.mul_eq_comp]
      rw [hcomp, LinearEquiv.trans_apply]
      have hcorefl : ((RootPairing.weylGroup.ofIdx P i : P.weylGroup) : P.Aut).coweightEquiv =
          P.coreflection i :=
        RootPairing.Equiv.reflection_coweightEquiv P i
      rw [hcorefl, RootPairing.coreflection_apply, hri, zero_smul, sub_zero]
    have hcount := ncard_inversions_mul_ofIdx_of_mem P w b hi hiw
    rw [← hmul]
    exact ih (w * RootPairing.weylGroup.ofIdx P i) (by omega) fun j hj ↦ by
      rw [hmul]
      exact hw j hj

/-- **A Weyl-group element carrying a dominant integral coweight to a dominant integral coweight
fixes it.** This holds over any integral domain of characteristic zero, with no order on the
coefficient ring. -/
theorem coweightEquiv_eq_self_of_forall_exists_nat_root' (w : P.weylGroup) {x : N}
    (hx : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i x = n)
    (hw : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i ((w : P.Aut).coweightEquiv x) = n) :
    (w : P.Aut).coweightEquiv x = x :=
  coweightEquiv_eq_self_aux b (inversions P b w).ncard w le_rfl hx hw

/-- **Two dominant integral coweights in the same Weyl orbit are equal.** -/
theorem eq_of_coweightEquiv_eq_of_forall_exists_nat_root' {w : P.weylGroup} {x y : N}
    (hxy : (w : P.Aut).coweightEquiv x = y)
    (hx : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i x = n)
    (hy : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i y = n) :
    x = y := by
  rw [← hxy]
  exact (coweightEquiv_eq_self_of_forall_exists_nat_root' b w hx (hxy.symm ▸ hy)).symm

end Unique

/-- **Every integral coweight has a unique dominant representative in its Weyl orbit.** Over a field
of characteristic zero carrying no order, this is the integral counterpart of
`TauCeti.existsUnique_mem_orbit_inter_dominantChamber`. -/
theorem existsUnique_coweightEquiv_forall_exists_nat_root' {ι R M N : Type*} [Finite ι]
    [AddCommGroup M] [AddCommGroup N] [Field R] [CharZero R] [Module R M] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (x : N) (hx : ∀ i, ∃ z : ℤ, P.root' i x = z) :
    ∃! y : N, (∃ w : P.weylGroup, (w : P.Aut).coweightEquiv x = y) ∧
      ∀ i ∈ b.support, ∃ n : ℕ, P.root' i y = n := by
  obtain ⟨w, hw⟩ := b.exists_forall_exists_nat_root'_coweightEquiv_apply x hx
  refine ⟨(w : P.Aut).coweightEquiv x, ⟨⟨w, rfl⟩, hw⟩, ?_⟩
  rintro y ⟨⟨v, rfl⟩, hy⟩
  have hrel : ((v⁻¹ * w : P.weylGroup) : P.Aut).coweightEquiv ((v : P.Aut).coweightEquiv x) =
      (w : P.Aut).coweightEquiv x := by
    have hcomp : ((v⁻¹ * w : P.weylGroup) : P.Aut).coweightEquiv =
        ((v⁻¹ : P.weylGroup) : P.Aut).coweightEquiv ≪≫ₗ (w : P.Aut).coweightEquiv := by
      simp [RootPairing.Equiv.mul_eq_comp]
    rw [hcomp, LinearEquiv.trans_apply, Subgroup.coe_inv]
    simp
  exact b.eq_of_coweightEquiv_eq_of_forall_exists_nat_root' hrel hy hw

end RootPairing.Base
