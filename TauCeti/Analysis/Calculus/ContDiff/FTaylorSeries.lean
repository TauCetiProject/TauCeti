/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import TauCeti.Analysis.Calculus.FDeriv.Submodule

/-!
# Taylor derivatives in a closed subspace

A Taylor derivative series of a function valued in a closed subspace remains
in that subspace at every order at which the series is defined. The proof uses
the closed-subspace derivative criterion at each successive order. In particular,
Taylor derivatives can be lifted through a closed linear isometric inclusion.
-/

public section

open Filter Set
open scoped ContDiff

variable {𝕜 D F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : D → F} {q : D → FormalMultilinearSeries 𝕜 D F}
  {S : Submodule 𝕜 F}

/-- Taylor derivatives of a function valued in a closed subspace take values there too. -/
theorem HasFTaylorSeriesUpTo.apply_mem_of_range_subset
    (hq : HasFTaylorSeriesUpTo n f q) (hS : IsClosed (S : Set F))
    (hf : range f ⊆ S) (m : ℕ) (hm : m ≤ n) (x : D) (v : Fin m → D) : q x m v ∈ S := by
  let R (m : ℕ) : Submodule 𝕜 (D [×m]→L[𝕜] F) :=
    { carrier := {a | ∀ v, a v ∈ S}
      zero_mem' := fun _ ↦ S.zero_mem
      add_mem' := fun ha hb v ↦ S.add_mem (ha v) (hb v)
      smul_mem' := fun c _ ha v ↦ S.smul_mem c (ha v) }
  have hR (m : ℕ) : IsClosed (R m : Set (D [×m]→L[𝕜] F)) := by
    -- Unfold the carrier so closedness follows from the evaluation preimages.
    change IsClosed {a : D [×m]→L[𝕜] F | ∀ v, a v ∈ S}
    simp only [ofPred_forall]
    exact isClosed_iInter fun v ↦ hS.preimage (continuous_eval_const v)
  induction m generalizing x with
  | zero =>
    rw [hq.zero_eq']
    exact hf ⟨x, rfl⟩
  | succ m ih =>
    have hmn : (m : WithTop ℕ∞) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hm
    have hv := (hq.fderiv m hmn x).apply_mem_of_eventually_sub_mem (hR m)
      (Eventually.of_forall fun y ↦ (R m).sub_mem
        (ih (le_of_lt hmn) y) (ih (le_of_lt hmn) x)) (v 0)
    simpa only [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]
      using hv (Fin.tail v)
