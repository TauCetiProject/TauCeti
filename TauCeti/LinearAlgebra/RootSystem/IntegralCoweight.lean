/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.Algebra.Module.Submodule.Union

/-!
# A base for which an integral coweight is dominant

Let `P` be a reduced crystallographic root system over a field of characteristic zero, and let
`x` be a coweight on which every root takes an integer value. This file proves that some base of
`P` makes `x` dominant: every simple root takes a natural-number value at `x`
(`RootPairing.exists_base_forall_exists_nat_root'_apply`).

The coefficient field carries no order, so the usual argument through Weyl chambers is not
available directly. The base is instead built with Mathlib's `IsAddIndecomposable.baseOf`, as in
the proof of `RootPairing.nonempty_base`.

In the Lie-theoretic application `x` is the neutral element `h` of an `sl₂` triple lying in a
splitting Cartan subalgebra: its roots take integer values, and a base making `h` dominant puts the
nilpositive element of the triple into the positive nilradical.

## Main results

* `RootPairing.exists_base_forall_exists_nat_root'_apply`: a coweight on which every root takes an
  integer value is dominant for some base.

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

end RootPairing
