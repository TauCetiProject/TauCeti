/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Coordinates
public import TauCeti.Analysis.Sobolev.Local.Wkp
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.Analysis.Sobolev.WeakDeriv.Chain
import TauCeti.Analysis.Sobolev.Wkp.Chain

/-!
# Local Sobolev classes on half-discs and the scalar spaces `W^{k,p}`

For an open planar set `Ω`, the relatively open subset `U = Ω ∩ {0 ≤ im}` of the closed upper
half-plane carries the local Sobolev class `TauCeti.MemWkpLoc p U k`: iterated weak derivatives on
the interior `Ω ∩ {0 < im}` of `U`, with `Lᵖ` bounds on every compact subset of `U`, including
compact sets reaching the real axis. This file compares that class with the library's scalar
Sobolev spaces `TauCeti.Wkp`, as `TauCeti.Analysis.Sobolev.Local.Wkp` does for open sets.

The relatively compact pieces of `U` are the upper halves `W⁺ = W ∩ {0 < im}`
(`TopologicalSpace.Opens.upperHalf W`) of the open sets `W` whose closure is compact and contained
in `Ω`; such a `W` may meet the real axis. Because the real axis is a null set, `Lᵖ` membership on
the compact sets of `U` is the same as `Lᵖ` membership on all those upper halves
(`TauCeti.memLpLoc_inter_setOf_im_nonneg_iff`). The comparison theorem
`TauCeti.memWkpLoc_inter_setOf_im_nonneg_iff_forall_wkp` then says that a real function lies in
`MemWkpLoc p U k` exactly when its restriction to every such `W⁺` is represented by an element of
`Wkp volume W⁺ p k`, and `TauCeti.MemWkpLoc.exists_wkp_upperHalf_iteratedGradient_ae_eq`
matches the highest recorded derivative with the iterated weak gradients of `u` on
`Ω ∩ {0 < im}`. The converse direction first obtains the iterated weak gradients on the interior
from the open-set comparison, then identifies them on each `W⁺` with the derivatives of the given
Sobolev representative, by uniqueness of weak derivatives, to get the `Lᵖ` bounds up to the axis.

For the half-disc `D_r(c) ∩ {0 ≤ im}` the comparison runs over the smaller half-discs
`D_s(c) ∩ {0 < im}`, `s < r` (`TauCeti.memWkpLoc_ball_inter_setOf_im_nonneg_iff`); in particular a
member restricts to `D_{r/2}(c) ∩ {0 < im}`. Maps into a finite-dimensional space are compared
coordinatewise (`Module.Basis.memWkpLoc_inter_setOf_im_nonneg_iff_forall_wkp`).

## Main declarations

* `TauCeti.MemWkpLoc.exists_wkp_upperHalf_iteratedGradient_ae_eq`,
  `TauCeti.MemWkpLoc.exists_wkp_upperHalf`: a member is represented by an element of `Wkp`
  on every upper half.
* `TauCeti.memWkpLoc_inter_setOf_im_nonneg_of_forall_wkp`,
  `TauCeti.memWkpLoc_inter_setOf_im_nonneg_iff_forall_wkp`: the comparison.
* `TauCeti.memWkpLoc_ball_inter_setOf_im_nonneg_iff`,
  `TauCeti.MemWkpLoc.exists_wkp_ball_half_inter_setOf_im_pos`: half-discs.
* `Module.Basis.memWkpLoc_inter_setOf_im_nonneg_iff_forall_wkp`: the vector-valued form.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces on half-discs).
* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

open Metric Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal

namespace TauCeti

variable {p : ℝ≥0∞} {Ω : Opens ℂ} {k : ℕ}

/-- An open set whose closure lies in the upper half of `Ω` has closure in `Ω` and is its own
upper half. -/
private theorem closure_subset_upperHalf {W : Opens ℂ}
    (hWΩ : closure (W : Set ℂ) ⊆ Ω.upperHalf) :
    closure (W : Set ℂ) ⊆ Ω ∧ W ≤ W.upperHalf :=
  ⟨hWΩ.trans (Opens.coe_upperHalf Ω ▸ inter_subset_left),
    fun _ hz => Opens.mem_upperHalf.2 ⟨hz, (Opens.mem_upperHalf.1 (hWΩ (subset_closure hz))).2⟩⟩

variable [Fact (1 ≤ p)]

/-- **Half-disc Sobolev functions are Sobolev on upper halves, with matching derivatives.** Let
`u` be real and locally `Lᵖ` on `Ω ∩ {0 ≤ im}`, with iterated weak gradients `G 0, …, G n` on
`Ω ∩ {0 < im}`, each locally `Lᵖ` on `Ω ∩ {0 ≤ im}`, as in
`TauCeti.memWkpLoc_succ_iff_exists_iteratedGradient_interior`. On the upper half
`W ∩ {0 < im}` of every open `W` whose closure is compact and contained in `Ω`, `u` is
represented by an element of `Wkp volume (W ∩ {0 < im}) p (n + 1)` whose highest recorded
derivative is `G n`. -/
theorem MemWkpLoc.exists_wkp_upperHalf_iteratedGradient_ae_eq (n : ℕ) {u : ℂ → ℝ}
    (hu : MemLpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) u)
    {G : (i : ℕ) → ℂ → IteratedGradient ℂ i}
    (h0 : HasWeakFDerivOn volume Ω.upperHalf u (fun z => innerSL ℝ (G 0 z)))
    (hG : ∀ i < n, HasWeakFDerivOn volume Ω.upperHalf (G i) (G (i + 1)))
    (hGp : ∀ i ≤ n, MemLpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) (G i)) {W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ v : Wkp volume W.upperHalf p (n + 1),
      Wkp.value (n + 1) v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u ∧
      Wkp.iteratedGradient n v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] G n := by
  have hWΩ' : W.upperHalf ≤ Ω.upperHalf :=
    Opens.upperHalf_mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ))
  obtain ⟨v, hv, htop, -⟩ := Wkp.exists_value_iteratedGradient_ae_eq_of_chain n
    (memLpLoc_inter_setOf_im_nonneg_iff.1 hu W hWc hWΩ) (h0.mono hWΩ')
    (fun i hi => (hG i hi).mono hWΩ')
    (fun i hi => memLpLoc_inter_setOf_im_nonneg_iff.1 (hGp i hi) W hWc hWΩ)
  exact ⟨v, hv, htop⟩

/-- **A half-disc Sobolev function is Sobolev on upper halves.** If
`u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k` is real, then on the upper half `W ∩ {0 < im}` of every open
`W` whose closure is compact and contained in `Ω`, `u` is represented by an element of
`Wkp volume (W ∩ {0 < im}) p k`. The set `W` may meet the real axis. -/
theorem MemWkpLoc.exists_wkp_upperHalf {u : ℂ → ℝ}
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k u) {W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ v : Wkp volume W.upperHalf p k,
      Wkp.value k v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u := by
  cases k with
  | zero =>
    have hW := memLpLoc_inter_setOf_im_nonneg_iff.1 (memWkpLoc_zero_iff.1 hu) W hWc hWΩ
    exact ⟨hW.toLp u, by rw [Wkp.value_zero]; exact hW.coeFn_toLp⟩
  | succ n =>
    obtain ⟨hu, G, h0, hG, hGp⟩ := (memWkpLoc_succ_iff_exists_iteratedGradient_interior n).1 hu
    rw [Opens.interior_inter_setOf_im_nonneg_eq_upperHalf] at h0 hG
    obtain ⟨v, hv, -⟩ :=
      MemWkpLoc.exists_wkp_upperHalf_iteratedGradient_ae_eq n hu h0 hG hGp hWc hWΩ
    exact ⟨v, hv⟩

/-- **Half-disc Sobolev membership from Sobolev membership on upper halves.** If the restriction
of a real function `u` to the upper half `W ∩ {0 < im}` of every open `W` whose closure is compact
and contained in `Ω` is represented by an element of `Wkp volume (W ∩ {0 < im}) p k`, then
`u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k`. -/
theorem memWkpLoc_inter_setOf_im_nonneg_of_forall_wkp {u : ℂ → ℝ}
    (h : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ v : Wkp volume W.upperHalf p k,
        Wkp.value k v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k u := by
  have hup : MemLpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) u :=
    memLpLoc_inter_setOf_im_nonneg_iff.2 fun W hWc hWΩ => by
      obtain ⟨v, hv⟩ := h W hWc hWΩ
      exact (Lp.memLp (Wkp.value k v)).ae_eq hv
  cases k with
  | zero => exact memWkpLoc_zero_iff.2 hup
  | succ n =>
    -- On the interior, the open-set comparison supplies the iterated weak gradients.
    have hint : MemWkpLoc p Ω.upperHalf (n + 1) u :=
      memWkpLoc_of_forall_wkp fun W hWc hWΩ => by
        obtain ⟨hWΩ', hWW⟩ := closure_subset_upperHalf hWΩ
        obtain ⟨v, hv⟩ := h W hWc hWΩ'
        exact ⟨Wkp.restrictL hWW (n + 1) v, (Wkp.value_restrictL_ae hWW (n + 1) v).trans
          (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hWW) hv)⟩
    obtain ⟨-, G, h0, hG, -⟩ := (memWkpLoc_succ_iff_exists_iteratedGradient n).1 hint
    -- On each upper half, they agree with the derivatives of the given representative.
    have hGp : ∀ i ≤ n, MemLpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) (G i) :=
      fun i hi => memLpLoc_inter_setOf_im_nonneg_iff.2 fun W hWc hWΩ => by
        obtain ⟨v, hv⟩ := h W hWc hWΩ
        obtain ⟨G', h0', hG', hGp', -, -⟩ := Wkp.exists_iteratedGradient_chain n v
        have hWΩ' : W.upperHalf ≤ Ω.upperHalf :=
          Opens.upperHalf_mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ))
        exact (hGp' i hi).ae_eq (ae_eq_of_iteratedGradient_chain n (h0'.congr_ae hv) hG'
          (h0.mono hWΩ') (fun j hj => (hG j hj).mono hWΩ') i hi)
    refine (memWkpLoc_succ_iff_exists_iteratedGradient_interior n).2 ⟨hup, G, ?_, ?_, hGp⟩
    · rwa [Opens.interior_inter_setOf_im_nonneg_eq_upperHalf]
    · rwa [Opens.interior_inter_setOf_im_nonneg_eq_upperHalf]

/-- **Comparison with `Wkp` on half-discs.** A real function lies in
`MemWkpLoc p (Ω ∩ {0 ≤ im}) k` exactly when its restriction to the upper half `W ∩ {0 < im}` of
every open `W` whose closure is compact and contained in `Ω` is represented by an element of
`Wkp volume (W ∩ {0 < im}) p k`. The sets `W` may meet the real axis, so the `Lᵖ` bounds reach
it. -/
theorem memWkpLoc_inter_setOf_im_nonneg_iff_forall_wkp {u : ℂ → ℝ} :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k u ↔
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∃ v : Wkp volume W.upperHalf p k,
          Wkp.value k v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u :=
  ⟨fun hu _ hWc hWΩ => hu.exists_wkp_upperHalf hWc hWΩ,
    memWkpLoc_inter_setOf_im_nonneg_of_forall_wkp⟩

/-- The open disc of radius `r` about `c`, as an open set. -/
private abbrev disc (c : ℂ) (r : ℝ) : Opens ℂ := ⟨ball c r, isOpen_ball⟩

/-- **The comparison on a half-disc.** A real function lies in
`MemWkpLoc p (D_r(c) ∩ {0 ≤ im}) k` exactly when its restriction to every upper half-disc
`D_s(c) ∩ {0 < im}` with `s < r` is represented by an element of
`Wkp volume (D_s(c) ∩ {0 < im}) p k`. -/
theorem memWkpLoc_ball_inter_setOf_im_nonneg_iff {c : ℂ} {r : ℝ} {u : ℂ → ℝ} :
    MemWkpLoc p (ball c r ∩ {z : ℂ | 0 ≤ z.im}) k u ↔ ∀ s < r,
      ∃ v : Wkp volume (Opens.upperHalf ⟨ball c s, isOpen_ball⟩) p k,
        Wkp.value k v =ᵐ[volume.restrict (ball c s ∩ {z : ℂ | 0 < z.im})] u := by
  have he : ∀ s, volume.restrict ((disc c s).upperHalf : Set ℂ) =
      volume.restrict (ball c s ∩ {z : ℂ | 0 < z.im}) := fun s => by
    rw [Opens.coe_upperHalf]
    rfl
  refine ⟨fun hu s hs => ?_,
    fun h => memWkpLoc_inter_setOf_im_nonneg_of_forall_wkp (Ω := disc c r) fun W _ hWΩ => ?_⟩
  · obtain ⟨v, hv⟩ := hu.exists_wkp_upperHalf (Ω := disc c r) (W := disc c s)
      ((isCompact_closedBall c s).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall)
      (closure_ball_subset_closedBall.trans (closedBall_subset_ball hs))
    exact ⟨v, hv.filter_mono (ae_mono (he s).ge)⟩
  · obtain ⟨s, hs, hWs⟩ := exists_lt_subset_ball isClosed_closure hWΩ
    obtain ⟨v, hv⟩ := h s hs
    replace hv := hv.filter_mono (ae_mono (he s).le)
    have hWs' : W.upperHalf ≤ (disc c s).upperHalf :=
      Opens.upperHalf_mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWs))
    exact ⟨Wkp.restrictL hWs' k v, (Wkp.value_restrictL_ae hWs' k v).trans
      (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hWs') hv)⟩

/-- **The library check on `D_{r/2}(c) ∩ {0 < im}`.** The restriction to the upper half-disc
`D_{r/2}(c) ∩ {0 < im}` of a real member of `MemWkpLoc p (D_r(c) ∩ {0 ≤ im}) k` is represented by
an element of `Wkp volume (D_{r/2}(c) ∩ {0 < im}) p k`. The converse direction, from all the upper
half-discs `D_s(c) ∩ {0 < im}` with `s < r`, is `TauCeti.memWkpLoc_ball_inter_setOf_im_nonneg_iff`.
-/
theorem MemWkpLoc.exists_wkp_ball_half_inter_setOf_im_pos {c : ℂ} {r : ℝ} (hr : 0 < r)
    {u : ℂ → ℝ} (hu : MemWkpLoc p (ball c r ∩ {z : ℂ | 0 ≤ z.im}) k u) :
    ∃ v : Wkp volume (Opens.upperHalf ⟨ball c (r / 2), isOpen_ball⟩) p k,
      Wkp.value k v =ᵐ[volume.restrict (ball c (r / 2) ∩ {z : ℂ | 0 < z.im})] u :=
  memWkpLoc_ball_inter_setOf_im_nonneg_iff.1 hu (r / 2) (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Finite ι]

/-- **The vector-valued comparison on half-discs.** A map into a finite-dimensional real space lies
in `MemWkpLoc p (Ω ∩ {0 ≤ im}) k` exactly when, for each coordinate in a basis and the upper half
`W ∩ {0 < im}` of every open `W` whose closure is compact and contained in `Ω`, the restriction of
that coordinate is represented by an element of `Wkp volume (W ∩ {0 < im}) p k`. -/
theorem _root_.Module.Basis.memWkpLoc_inter_setOf_im_nonneg_iff_forall_wkp
    (b : Module.Basis ι ℝ E) {f : ℂ → E} :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k f ↔
      ∀ i, ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∃ v : Wkp volume W.upperHalf p k,
          Wkp.value k v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)]
            fun z => b.repr (f z) i := by
  rw [b.memWkpLoc_iff]
  exact forall_congr' fun i => TauCeti.memWkpLoc_inter_setOf_im_nonneg_iff_forall_wkp

end TauCeti
