/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Bases
import Mathlib.Algebra.Module.Submodule.Union

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

In the Lie-theoretic application `x` is the neutral element `h` of an `sl₂` triple lying in a
splitting Cartan subalgebra: its roots take integer values, and a base making `h` dominant puts the
nilpositive element of the triple into the positive nilradical.

## Main results

* `RootPairing.exists_base_forall_exists_nat_root'_apply`: a coweight on which every root takes an
  integer value is dominant for some base.
* `RootPairing.Base.exists_forall_exists_nat_root'_coweightEquiv_apply`: such a coweight is
  carried by the Weyl group to a coweight that is dominant for a given base.

## References

* J.-P. Serre, *Algèbres de Lie semi-simples complexes*, Benjamin, 1966, Ch. V, §8.
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
