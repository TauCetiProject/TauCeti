/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.Local.HalfPlane
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Local.SmoothCoefficients

/-!
# Local Sobolev classes on half-discs under `Cᵏ` coefficients

`TauCeti.MemWkpLoc.contDiffOn_clm_apply` lets a field of continuous linear maps that is `Cᵏ` on an
open neighbourhood of a set act on the local Sobolev class of order `k` there. On a relatively open
subset `Ω ∩ {0 ≤ im}` of the closed upper half-plane, a coefficient is often only given up to the
real axis, as the coordinate changes of a vector bundle over a surface with boundary are. This file
shows that a field `A` of continuous linear maps that is `Cᵏ` on `Ω ∩ {0 ≤ im}` preserves the class
of order `k` on every subset of it
(`TauCeti.MemWkpLoc.contDiffOn_clm_apply_inter_setOf_im_nonneg`): the statement is local
(`TauCeti.memWkpLoc_iff_locally`), and near each point `A` agrees with a field that is `Cᵏ` on an
open neighbourhood of the point (`TauCeti.exists_contDiffOn_eqOn_inter_setOf_im_nonneg`).

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_clm_apply_inter_setOf_im_nonneg`: fields of continuous linear maps
  of class `Cᵏ` up to the real axis preserve the half-disc classes of order `k`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p : ENNReal} {k : ℕ}

/-- **Fields of continuous linear maps of class `Cᵏ` up to the real axis.** Let `A` be a field of
continuous linear maps between finite-dimensional spaces that is `Cᵏ` on the relatively open
subset `Ω ∩ {0 ≤ im}` of the closed upper half-plane, for an open `Ω`. Then `z ↦ A z (u z)` lies
in the local Sobolev class of order `k` on every subset `U` of `Ω ∩ {0 ≤ im}` on which `u`
does. -/
theorem MemWkpLoc.contDiffOn_clm_apply_inter_setOf_im_nonneg [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G] {Ω U : Set ℂ} (hΩ : IsOpen Ω) {A : ℂ → F →L[ℝ] G} {u : ℂ → F}
    (hu : MemWkpLoc p U k u) (hA : ContDiffOn ℝ k A (Ω ∩ {z | 0 ≤ z.im}))
    (hU : U ⊆ Ω ∩ {z | 0 ≤ z.im}) : MemWkpLoc p U k (fun z ↦ A z (u z)) := by
  refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
  obtain ⟨W, hW, hzW, A', hA', hA'A⟩ := exists_contDiffOn_eqOn_inter_setOf_im_nonneg hΩ hA (hU hz)
  refine ⟨U ∩ W, inter_mem_nhdsWithin _ (hW.mem_nhds hzW), ?_⟩
  refine ((hu.mono inter_subset_left).contDiffOn_clm_apply (Ω := ⟨W, hW⟩) hA' le_rfl
    inter_subset_right).congr fun y hy ↦ ?_
  rw [← hA'A ⟨hU hy.1, hy.2⟩]

end TauCeti
