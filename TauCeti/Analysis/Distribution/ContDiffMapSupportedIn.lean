/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import TauCeti.Analysis.Calculus.Jet.Continuous

/-!
# Basic facts about functions supported in a compact set

Elementary properties of the space `𝓓^{n}_{K}(E, F)` of `C^n` functions `E → F` supported in a
compact set `K`, together with the continuous linear `m`-jet restriction map into
`TauCeti.JetSpace E F K m`.

## Main results

* `ContDiffMapSupportedIn.differentiable`: for `1 ≤ n`, the elements of `𝓓^{n}_{K}(E, F)` are
  differentiable.
* `ContDiffMapSupportedIn.structureMapCLM_apply_eq_zero_of_notMem`: the structure maps, that is
  the derivatives of `f ∈ 𝓓^{n}_{K}(E, F)`, vanish off `K`.
* `ContDiffMapSupportedIn.jetRestrictionCLM`: continuous linear `m`-jet restriction map from
  `𝓓^{n}_{L}(E, F)` into `TauCeti.JetSpace E F K m` when `m ≤ n`.
-/

public section

open TopologicalSpace
open scoped BoundedContinuousFunction ContDiff Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {n : ℕ∞} {K : Compacts E}

/-- For `1 ≤ n`, a `C^n` function supported in `K` is differentiable. -/
protected theorem differentiable (hn : 1 ≤ n) (f : 𝓓^{n}_{K}(E, F)) : Differentiable ℝ f :=
  f.contDiff.differentiable (by exact_mod_cast (one_ne_zero.bot_lt.trans_le hn).ne')

section StructureMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The structure maps vanish off `K`. -/
theorem structureMapCLM_apply_eq_zero_of_notMem (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) {x : E}
    (hx : x ∉ K) : structureMapCLM 𝕜 n i f x = 0 := by
  rw [structureMapCLM_apply]
  split_ifs
  · exact f.iteratedFDeriv_zero_on_compl hx
  · simp

end StructureMap

/-- Continuous linear `m`-jet restriction from `𝓓^{n}_{L}(E, F)` into `TauCeti.JetSpace E F K m`
whenever `m ≤ n`. -/
noncomputable def jetRestrictionCLM (K : Set E) (m : ℕ) {n : ℕ∞} (_hm : (m : ℕ∞) ≤ n)
    (L : Compacts E) :
    𝓓^{n}_{L}(E, F) →L[ℝ] TauCeti.JetSpace E F K m :=
  (TauCeti.JetSpace.evalEquiv (E := E) (F := F) (K := K)
      (m := m)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun k : Fin (m + 1) ↦
      BoundedContinuousFunction.compContinuousCLM (E [×(k : ℕ)]→L[ℝ] F) ℝ
        ⟨Subtype.val, continuous_subtypeVal⟩ ∘L ContDiffMapSupportedIn.structureMapCLM ℝ n k

@[simp]
theorem eval_jetRestrictionCLM (K : Set E) (m : ℕ) {n : ℕ∞} (hm : (m : ℕ∞) ≤ n) (L : Compacts E)
    (φ : 𝓓^{n}_{L}(E, F)) (k : Fin (m + 1)) (x : K) :
    (jetRestrictionCLM K m hm L φ).eval k x = iteratedFDeriv ℝ (k : ℕ) (φ : E → F) x.val := by
  have hk : ((k : ℕ) : ℕ∞) ≤ n := (Nat.cast_le.2 k.is_le).trans hm
  rw [jetRestrictionCLM, ContinuousLinearMap.comp_apply]
  simp [TauCeti.JetSpace.eval_evalEquiv_symm, hk]

end ContDiffMapSupportedIn
