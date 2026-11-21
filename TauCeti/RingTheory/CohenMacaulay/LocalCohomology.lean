/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LocalCohomology.AnnihilatorProduct
public import TauCeti.RingTheory.CohenMacaulay.Basic
import TauCeti.RingTheory.Depth.LocalCohomology

/-!
# Local cohomology of Cohen–Macaulay modules

Let `M` be a finite Cohen–Macaulay module over a Noetherian local ring `(R, 𝔪)`. Because its
depth equals the dimension of its support (when `M` is nonzero), all local cohomology modules
`H^j_𝔪(M)` vanish strictly below `supportDim R M`. Consequently, the local-cohomology annihilator
product `localCohomology.annihilatorProduct (IsLocalRing.maximalIdeal R) M d` is the unit ideal
for every cutoff `d : ℕ` with `d ≤ supportDim R M` (and for every `d` when `M = 0`).

## Main results

* `Module.IsCohenMacaulay.isZero_localCohomology`: `H^j_𝔪(M) = 0` for `j < supportDim R M`.
* `Module.IsCohenMacaulay.annihilatorProduct_eq_top`: `a_𝔪(M, d) = ⊤` for `d ≤ supportDim R M`.
-/

public section

universe u

open CategoryTheory Limits IsLocalRing

namespace Module.IsCohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- For a finite Cohen–Macaulay module `M` over a Noetherian local ring `(R, 𝔪)`, the local
cohomology module `H^j_𝔪(M)` vanishes for every `j : ℕ` strictly below `supportDim R M`. -/
theorem isZero_localCohomology (h : IsCohenMacaulay R M) {j : ℕ}
    (hj : (j : WithBot ℕ∞) < supportDim R M) :
    IsZero ((localCohomology (maximalIdeal R) j).obj (ModuleCat.of R M)) := by
  have : Nontrivial M := (supportDim_ne_bot_iff_nontrivial R M).mp (ne_bot_of_gt hj)
  rw [← h.depth_eq] at hj
  exact localCohomology.isZero_obj_of_lt_depth (maximalIdeal R) (ModuleCat.of R M)
    (by exact_mod_cast hj)

/-- For a finite Cohen–Macaulay module `M` over a Noetherian local ring `(R, 𝔪)`, the
local-cohomology annihilator product `a_𝔪(M, d)` is the unit ideal whenever `d ≤ supportDim R M`. -/
theorem annihilatorProduct_eq_top (h : IsCohenMacaulay R M) {d : ℕ}
    (hd : (d : WithBot ℕ∞) ≤ supportDim R M) :
    localCohomology.annihilatorProduct (maximalIdeal R) M d = ⊤ := by
  refine localCohomology.annihilatorProduct_eq_top_of_forall_isZero _ _ fun j hj ↦ ?_
  exact h.isZero_localCohomology ((by exact_mod_cast hj : (j : WithBot ℕ∞) < d).trans_le hd)

end Module.IsCohenMacaulay
