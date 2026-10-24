/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Montel.Precompact
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Montel's selection theorem

A locally bounded sequence of holomorphic maps on an open set `Ω ⊆ ℂ` into a proper complex
normed space has a subsequence converging locally uniformly on `Ω` to a holomorphic map. This
normal-family compactness supports extremal arguments such as the Riemann mapping theorem, where
the target is `ℂ`. It also supplies the subsequence selection used by Vitali's theorem in
`Conformal/Vitali.lean`.

`Conformal/Montel/Precompact.lean` proves that the continuous restrictions form a relatively
compact subset of `C(↥Ω, E)` with its compact-open topology, and characterizes this compactness by
local boundedness. This file extracts a convergent subsequence and identifies its holomorphic
limit.

An open subset of `ℂ` is locally compact and second countable, hence hemicompact: its compact
subsets admit a countable cofinal family. Thus the compact-open topology on `C(↥Ω, E)` is first
countable, and `IsCompact.tendsto_subseq` extracts a convergent subsequence.
`ContinuousMap.tendsto_iff_tendstoLocallyUniformly` identifies its convergence with locally uniform
convergence, and `TendstoLocallyUniformlyOn.differentiableOn` gives holomorphy of the limit.

## Main results

* `TauCeti.montel`: a locally bounded sequence of holomorphic maps into a proper complex normed
  space has a locally uniformly convergent subsequence with holomorphic limit.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
* The Montel equicontinuity argument in the Riemann mapping formalization
  [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505).
-/

public section

open Complex Metric Filter Topology Set BoundedContinuousFunction

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Ω : Set ℂ} {F : ℕ → ℂ → E}

/-- **Montel's selection theorem.** A locally bounded sequence of holomorphic maps on an open
set `Ω ⊆ ℂ` into a proper complex normed space `E` has a subsequence converging locally uniformly
on `Ω` to a holomorphic map.

Over `ℂ`, properness of the target is equivalent to finite-dimensionality; in particular, the
result applies to scalar-valued holomorphic maps. -/
theorem montel [ProperSpace E] (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hb : IsLocallyBoundedOn F Ω) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → E), StrictMono φ ∧ DifferentiableOn ℂ g Ω ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop Ω := by
  classical
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  set f : ℕ → C(Ω, E) := fun n => ⟨Ω.domRestrict (F n), ((hF n).continuousOn).domRestrict⟩
  -- The relative compactness of the restricted family, from `Conformal/Montel/Precompact.lean`.
  have hcpt : IsCompact (closure (Set.range f)) :=
    isCompact_closure_range_of_isLocallyBoundedOn hΩ hF hb fun _ => rfl
  obtain ⟨a, -, φ, hφ, hconv⟩ := hcpt.tendsto_subseq (x := f) fun n => subset_closure ⟨n, rfl⟩
  -- Compact-open convergence is locally uniform convergence; extend the limit off `Ω` by zero.
  have hlim : ((fun z => if hz : z ∈ Ω then a ⟨z, hz⟩ else 0) ∘ (Subtype.val : Ω → ℂ))
      = fun x : Ω => a x := by
    funext x
    simp [x.2]
  have hconvOn : TendstoLocallyUniformlyOn (fun n => F (φ n))
      (fun z => if hz : z ∈ Ω then a ⟨z, hz⟩ else 0) atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, hlim]
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv
  exact ⟨φ, _, hφ, hconvOn.differentiableOn (Eventually.of_forall fun n => hF (φ n)) hΩ, hconvOn⟩

end TauCeti
