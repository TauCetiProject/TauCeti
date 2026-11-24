/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import TauCeti.RingTheory.Flat.Pi

/-!
# Checks for products of flat modules

Over a noetherian ring, in particular over `ℤ`, an arbitrary product of flat modules is flat, and a
nonempty product of faithfully flat modules is faithfully flat.

Coherence cannot be dropped. Let `k` be a nontrivial commutative ring and `R = k ⊕ V` the trivial
square-zero extension by the free module `V` on `x₀, x₁, …`, so that `V² = 0`. In `∏ₙ R` the
vector `(x₁, x₂, …)` is killed by `x₀`. If the product were flat, the equational criterion would
write it as `∑ⱼ aⱼ yⱼ` with finitely many `aⱼ` killed by `x₀`, that is `aⱼ ∈ V`; every coordinate of
such a sum lies in the span of the `aⱼ`, which misses `xₙ₊₁` for `n` large. So `∏ₙ R` is a product
of free modules that is not flat, and `R` is not coherent (Chase, Theorem 2.1).

## References

* S. U. Chase, *Direct products of modules*, Trans. Amer. Math. Soc. 97 (1960), Theorem 2.1.
-/

namespace TauCeti.FlatPiChecks

/-- An arbitrary product of copies of `ℤ` is flat, and faithfully flat when nonempty. -/
example (ι : Type*) [Nonempty ι] : Module.Flat ℤ (ι → ℤ) ∧ Module.FaithfullyFlat ℤ (ι → ℤ) :=
  ⟨inferInstance, inferInstance⟩

/-- Over a noetherian ring a product of flat modules is flat, for an arbitrary index. -/
example (R : Type*) [CommRing R] [IsNoetherianRing R] (ι : Type*) (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)] :
    Module.Flat R (∀ i, M i) :=
  inferInstance

/-- Over the trivial square-zero extension `k ⊕ V` of a nontrivial commutative ring `k` by a free
module `V` of countable rank, the product `∏ₙ (k ⊕ V)` of free modules is not flat, so `k ⊕ V` is
not a coherent ring. -/
example (k : Type*) [CommRing k] [Nontrivial k] :
    ¬ Module.Flat (TrivSqZeroExt k (ℕ →₀ k)) (ℕ → TrivSqZeroExt k (ℕ →₀ k)) ∧
      ¬ IsCoherentRing (TrivSqZeroExt k (ℕ →₀ k)) := by
  classical
  have hflat : ¬ Module.Flat (TrivSqZeroExt k (ℕ →₀ k)) (ℕ → TrivSqZeroExt k (ℕ →₀ k)) := by
    intro _
    -- the relation `x₀ • (x₁, x₂, …) = 0`
    let x₀ : TrivSqZeroExt k (ℕ →₀ k) := .inr (Finsupp.single 0 1)
    let v : ℕ → TrivSqZeroExt k (ℕ →₀ k) := fun n ↦ .inr (Finsupp.single (n + 1) 1)
    have hrel : ∑ _ : Unit, x₀ • v = 0 := by
      ext n : 1
      simp [x₀, v]
    obtain ⟨m, a, y, hv, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (f := fun _ : Unit ↦ x₀) (x := fun _ ↦ v) hrel
    -- every coefficient `a () j` is killed by `x₀`, so it lies in `V`
    have hfst (j : Fin m) : (a () j).fst = 0 := by
      simpa [x₀] using congrArg (fun r : TrivSqZeroExt k (ℕ →₀ k) ↦ r.snd 0) (ha j)
    -- choose `n` with `n + 1` outside the supports of the coefficients
    let S := Finset.univ.biUnion fun j ↦ (a () j).snd.support
    have hS (j : Fin m) : (a () j).snd (S.sup id + 1) = 0 := by
      refine Finsupp.notMem_support_iff.mp fun h ↦ ?_
      have hmem : S.sup id + 1 ∈ S := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩
      have : S.sup id + 1 ≤ S.sup id := Finset.le_sup (f := id) hmem
      omega
    have := congrArg (fun r : TrivSqZeroExt k (ℕ →₀ k) ↦ r.snd (S.sup id + 1))
      (congrFun (hv ()) (S.sup id))
    simp [v, Finset.sum_apply, TrivSqZeroExt.snd_sum, hfst, hS] at this
  exact ⟨hflat, fun _ ↦ hflat inferInstance⟩

end TauCeti.FlatPiChecks
