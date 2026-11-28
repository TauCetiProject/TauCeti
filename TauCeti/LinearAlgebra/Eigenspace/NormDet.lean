/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Norm bounds on mapped determinants via eigenvalues

Let `u : Module.End 𝕜 L` be an endomorphism of a finite-dimensional vector space over a field `𝕜`
whose characteristic polynomial splits, and let `f : 𝕜 →+* K` be a ring homomorphism into a normed
field `K`. Writing `u.det` as the product of the roots of `u.charpoly` gives
`‖f u.det‖ = (u.charpoly.roots.map fun α ↦ ‖f α‖).prod` (`TauCeti.norm_map_det_eq_prod_roots`).

Consequently, if every eigenvalue `α` of `u` satisfies `‖f α‖ ≤ B`, then
`‖f u.det‖ ≤ B ^ Module.finrank 𝕜 L` (`TauCeti.norm_map_det_le_pow_of_splits`, and
`TauCeti.norm_map_det_le_pow` when `𝕜` is algebraically closed).

## Main results

* `TauCeti.norm_map_det_eq_prod_roots`: `‖f u.det‖` is the product of `‖f α‖` over the roots of
  `u.charpoly`.
* `TauCeti.norm_map_det_le_pow_of_splits`: eigenvalue norm bound implies `‖f u.det‖ ≤ B ^ finrank`.
* `TauCeti.norm_map_det_le_pow`: specialization to an algebraically closed base field `𝕜`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/New/OneLift/LiftVolumeHeight.lean`
(`New.norm_map_det_le_pow`).
-/

public section

namespace TauCeti

variable {𝕜 K L : Type*} [Field 𝕜] [NormedField K] [AddCommGroup L] [Module 𝕜 L]
  [Module.Finite 𝕜 L]

/-- If the characteristic polynomial of `u : Module.End 𝕜 L` splits, then for any ring homomorphism
`f : 𝕜 →+* K` into a normed field, `‖f u.det‖` equals the product of `‖f α‖` over the roots of
`u.charpoly`. -/
theorem norm_map_det_eq_prod_roots (f : 𝕜 →+* K) (u : Module.End 𝕜 L) (hs : u.charpoly.Splits) :
    ‖f u.det‖ = (u.charpoly.roots.map fun α ↦ ‖f α‖).prod := by
  let N : 𝕜 →* ℝ := (normHom (α := K)).toMonoidHom.comp f.toMonoidHom
  change N u.det = (u.charpoly.roots.map N).prod
  rw [Module.End.det_eq_prod_roots_charpoly_of_splits hs, map_multiset_prod]

/-- If the characteristic polynomial of `u : Module.End 𝕜 L` splits and `‖f α‖ ≤ B` for every
eigenvalue `α` of `u`, then `‖f u.det‖ ≤ B ^ Module.finrank 𝕜 L`. -/
theorem norm_map_det_le_pow_of_splits (f : 𝕜 →+* K) (u : Module.End 𝕜 L) (hs : u.charpoly.Splits)
    {B : ℝ} (heigen : ∀ (α : 𝕜) (z : L), u.HasEigenvector α z → ‖f α‖ ≤ B) :
    ‖f u.det‖ ≤ B ^ Module.finrank 𝕜 L := by
  let N : 𝕜 →* ℝ := (normHom (α := K)).toMonoidHom.comp f.toMonoidHom
  rw [norm_map_det_eq_prod_roots f u hs, ← u.charpoly_natDegree, hs.natDegree_eq_card_roots]
  refine Multiset.prod_map_le_pow_card (f := N) (fun α _ ↦ norm_nonneg (f α)) fun α hα ↦ ?_
  obtain ⟨z, hz⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly u α).mpr
    (Polynomial.isRoot_of_mem_roots hα)).exists_hasEigenvector
  exact heigen α z hz

/-- Over an algebraically closed field `𝕜`, if `‖f α‖ ≤ B` for every eigenvalue `α` of
`u : Module.End 𝕜 L`, then `‖f u.det‖ ≤ B ^ Module.finrank 𝕜 L`. -/
theorem norm_map_det_le_pow [IsAlgClosed 𝕜] (f : 𝕜 →+* K) (u : Module.End 𝕜 L) {B : ℝ}
    (heigen : ∀ (α : 𝕜) (z : L), u.HasEigenvector α z → ‖f α‖ ≤ B) :
    ‖f u.det‖ ≤ B ^ Module.finrank 𝕜 L :=
  norm_map_det_le_pow_of_splits f u (IsAlgClosed.splits u.charpoly) heigen

end TauCeti
