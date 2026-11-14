/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Bases
import Mathlib.Algebra.Module.Submodule.Union
import TauCeti.LinearAlgebra.RootSystem.Weyl.DominantIntegral

/-!
# Making an integral coweight dominant

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
(`RootPairing.Base.exists_forall_exists_nat_root'_coweightEquiv_apply`). For integral coweights
this is the counterpart, over a field of characteristic zero carrying no order, of the
ordered-field statement `RootPairing.exists_mem_dominantChamber`.

Passing to the dual root pairing `P.flip` identifies coweights with weights and simple roots with
simple coroots, so `TauCeti.weylGroup_smul_eq_self_of_dominantIntegral` shows—already over any
characteristic-zero domain—that a dominant integral coweight is the unique dominant coweight in its
Weyl orbit (`RootPairing.Base.coweightEquiv_eq_self_of_forall_exists_nat_root'_apply`). Together
with existence, every integral coweight of a reduced crystallographic root system over a field of
characteristic zero has a unique dominant representative in its Weyl orbit
(`RootPairing.Base.existsUnique_coweightEquiv_eq_and_forall_exists_nat_root'_apply`).

In the Lie-theoretic application `x` is the neutral element `h` of an `sl₂` triple lying in a
splitting Cartan subalgebra: its roots take integer values, a base making `h` dominant puts the
nilpositive element of the triple into the positive nilradical, and uniqueness shows that at most
one element in the Weyl orbit of `h` is dominant for a fixed base.

## Main results

* `RootPairing.Base.coweightEquiv_eq_self_of_forall_exists_nat_root'_apply` and
  `RootPairing.Base.coweightEquiv_eq_coweightEquiv_of_forall_exists_nat_root'_apply`: a dominant
  integral coweight is the only dominant integral coweight in its Weyl orbit.
* `RootPairing.exists_base_forall_exists_nat_root'_apply`: a coweight on which every root takes an
  integer value is dominant for some base.
* `RootPairing.Base.exists_forall_exists_nat_root'_coweightEquiv_apply` and
  `RootPairing.Base.existsUnique_coweightEquiv_eq_and_forall_exists_nat_root'_apply`: such a
  coweight is carried by the Weyl group to a unique coweight that is dominant for a given base.

## References

* J.-P. Serre, *Algèbres de Lie semi-simples complexes*, Benjamin, 1966, Ch. V, §8.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.3 and
  §13.2.
-/

public section

open Module IsAddIndecomposable

namespace RootPairing

section Uniqueness

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- Every Weyl-group element acts on coweights as a Weyl-group element of the dual root pairing
`P.flip` acts on weights. -/
private theorem exists_weylGroup_flip_smul_eq_coweightEquiv (w : P.weylGroup) :
    ∃ v : P.flip.weylGroup, ∀ x : N, v • x = (w : P.Aut).coweightEquiv x := by
  obtain ⟨w, hw⟩ := w
  suffices w.coweightEquiv ∈
      MonoidHom.range ((Equiv.weightHom P.flip).domRestrict P.flip.weylGroup) by
    obtain ⟨v, hv⟩ := this
    exact ⟨v, fun x ↦ DFunLike.congr_fun hv x⟩
  induction hw using weylGroup.induction with
  | mem i =>
    refine ⟨weylGroup.ofIdx P.flip i, LinearEquiv.ext fun x ↦ ?_⟩
    simp [reflection_apply, coreflection_apply]
  | one => exact ⟨1, by ext x; simp⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    have hmul : (g₁ * g₂).coweightEquiv = g₂.coweightEquiv * g₁.coweightEquiv := by
      ext x
      simp
    exact hmul ▸ mul_mem ih₂ ih₁

/-- **A dominant integral coweight is the only dominant integral coweight in its Weyl orbit.** If
every simple root of `b` takes a natural value at both `x` and `(w : P.Aut).coweightEquiv x` for
`w ∈ P.weylGroup`, then `(w : P.Aut).coweightEquiv x = x`. -/
theorem Base.coweightEquiv_eq_self_of_forall_exists_nat_root'_apply (b : P.Base)
    {w : P.weylGroup} {x : N}
    (hx : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i x = n)
    (hwx : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i ((w : P.Aut).coweightEquiv x) = n) :
    (w : P.Aut).coweightEquiv x = x := by
  have := P.flip_isReduced
  obtain ⟨v, hv⟩ := exists_weylGroup_flip_smul_eq_coweightEquiv w
  rw [← hv x]
  refine TauCeti.weylGroup_smul_eq_self_of_dominantIntegral (P := P.flip) (b := b.flip) ?_ ?_
  · intro i hi
    rw [Base.flip_support] at hi
    simpa only [coroot', root', flip_toLinearMap, flip_coroot, LinearMap.flip_flip] using hx i hi
  · intro i hi
    rw [Base.flip_support] at hi
    simpa only [hv, coroot', root', flip_toLinearMap, flip_coroot, LinearMap.flip_flip] using
      hwx i hi

/-- **Two dominant Weyl translates of a coweight coincide.** If `(v : P.Aut).coweightEquiv x` and
`(w : P.Aut).coweightEquiv x` both take natural values at every simple root of `b`, then they are
equal. -/
theorem Base.coweightEquiv_eq_coweightEquiv_of_forall_exists_nat_root'_apply (b : P.Base)
    {v w : P.weylGroup} {x : N}
    (hv : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i ((v : P.Aut).coweightEquiv x) = n)
    (hw : ∀ i ∈ b.support, ∃ n : ℕ, P.root' i ((w : P.Aut).coweightEquiv x) = n) :
    (v : P.Aut).coweightEquiv x = (w : P.Aut).coweightEquiv x := by
  have hrel : (((v⁻¹ * w : P.weylGroup) : P.Aut).coweightEquiv ((v : P.Aut).coweightEquiv x)) =
      (w : P.Aut).coweightEquiv x := by
    simp
  exact (b.coweightEquiv_eq_self_of_forall_exists_nat_root'_apply hv (hrel ▸ hw)).symm.trans hrel

end Uniqueness

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

variable {P} in
/-- **An integral coweight has a unique dominant representative in its Weyl orbit.** Fix a base
`b`. If every root takes an integer value at the coweight `x`, then there is a unique coweight `y`
in the Weyl orbit of `x` at which every simple root of `b` takes a natural value. -/
theorem Base.existsUnique_coweightEquiv_eq_and_forall_exists_nat_root'_apply (b : P.Base) (x : N)
    (hx : ∀ i, ∃ z : ℤ, P.root' i x = z) :
    ∃! y : N, (∃ w : P.weylGroup, (w : P.Aut).coweightEquiv x = y) ∧
      ∀ i ∈ b.support, ∃ n : ℕ, P.root' i y = n := by
  obtain ⟨w, hw⟩ := b.exists_forall_exists_nat_root'_coweightEquiv_apply x hx
  refine ⟨(w : P.Aut).coweightEquiv x, ⟨⟨w, rfl⟩, hw⟩, ?_⟩
  rintro _ ⟨⟨v, rfl⟩, hv⟩
  exact b.coweightEquiv_eq_coweightEquiv_of_forall_exists_nat_root'_apply hv hw

end RootPairing
