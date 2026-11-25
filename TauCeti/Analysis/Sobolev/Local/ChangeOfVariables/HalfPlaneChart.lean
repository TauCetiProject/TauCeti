/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.LinearAlgebra.Determinant
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables.Higher
import TauCeti.Analysis.Sobolev.Local.HalfPlane
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Local.SmoothCoefficients

/-!
# Local Sobolev classes under changes of half-plane chart

The charts of a manifold modelled on the closed upper half-plane, such as a surface with boundary,
differ by maps between relatively open subsets `Ω ∩ {0 ≤ im}` and `Ω' ∩ {0 ≤ im}` of the closed
upper half-plane that are `Cⁿ` in both directions up to the real axis. They are not defined on
open subsets of `ℂ`, so the planar change of variables `TauCeti.MemWkpLoc.comp_contDiffOn_halfPlane`
does not apply to them directly.

This file shows that such a map `e`, given as a partial equivalence of `ℂ`, preserves the
half-disc classes `TauCeti.MemWkpLoc p (V ∩ {0 ≤ im}) k` of every order `k ≤ n`
(`TauCeti.MemWkpLoc.comp_partialEquiv_halfPlane`), and that a field of continuous linear maps of
class `Cᵏ` up to the real axis preserves the class of order `k` on subsets of
`Ω ∩ {0 ≤ im}` (`TauCeti.MemWkpLoc.contDiffOn_clm_apply_inter_setOf_im_nonneg`). Coordinate
changes of a vector bundle over a surface with boundary are of the second kind.

## The argument

Both statements are local (`TauCeti.memWkpLoc_iff_locally`), and near each point a map that is
`Cⁿ` up to the real axis agrees with a map that is `Cⁿ` on an open neighbourhood of the point
(`TauCeti.exists_contDiffOn_eqOn_inter_setOf_im_nonneg`), so the results for open sets apply. For
the change of variables, the extension `Φ` of `e` also needs an invertible derivative near the
point. Extending `e.symm` in the same way to `Ψ`, the composite `Ψ ∘ Φ` is the identity on a
neighbourhood of the point in the closed upper half-plane, where derivatives are unique since the
half-plane is convex with nonempty interior. So the derivative of `Ψ` is a left inverse of that of
`Φ` at the point (`TauCeti.exists_contDiffOn_eqOn_det_fderiv_ne_zero`).

## Main declarations

* `TauCeti.exists_contDiffOn_eqOn_det_fderiv_ne_zero`: near each point, a partial equivalence of
  relatively open subsets of the closed upper half-plane, `Cⁿ` in both directions, agrees with a
  `Cⁿ` map with invertible derivative on an open neighbourhood of the point.
* `TauCeti.MemWkpLoc.comp_partialEquiv_halfPlane`: such maps preserve the half-disc classes.
* `TauCeti.MemWkpLoc.contDiffOn_clm_apply_inter_setOf_im_nonneg`: fields of continuous linear
  maps of class `Cᵏ` up to the real axis preserve the half-disc classes of order `k`.

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

variable {e : PartialEquiv ℂ ℂ} {Ω Ω' : Set ℂ} {n : ℕ}

/-- If `Ψ ∘ Φ` is the identity on a set `S` containing `z₀` within which derivatives at `z₀` are
unique, and `Φ` and `Ψ` are differentiable at `z₀` and `Φ z₀`, then the derivative of `Φ` at `z₀`
is invertible. -/
private theorem det_fderiv_ne_zero_of_eqOn_comp_id {Φ Ψ : ℂ → ℂ} {S : Set ℂ} {z₀ : ℂ}
    (huniq : UniqueDiffWithinAt ℝ S z₀) (hΦ : DifferentiableAt ℝ Φ z₀)
    (hΨ : DifferentiableAt ℝ Ψ (Φ z₀)) (hid : EqOn (Ψ ∘ Φ) id S) (hz₀ : z₀ ∈ S) :
    (fderiv ℝ Φ z₀).det ≠ 0 := by
  have hcomp : (fderiv ℝ Ψ (Φ z₀)).comp (fderiv ℝ Φ z₀) = ContinuousLinearMap.id ℝ ℂ :=
    huniq.eq (hΨ.hasFDerivAt.comp z₀ hΦ.hasFDerivAt).hasFDerivWithinAt
      ((hasFDerivWithinAt_id z₀ S).congr (fun z hz ↦ hid hz) (hid hz₀))
  intro h
  have h1 : LinearMap.det (fderiv ℝ Ψ (Φ z₀) : ℂ →ₗ[ℝ] ℂ) *
      LinearMap.det (fderiv ℝ Φ z₀ : ℂ →ₗ[ℝ] ℂ) = 1 := by
    rw [← LinearMap.det_comp, ← ContinuousLinearMap.toLinearMap_comp, hcomp,
      ContinuousLinearMap.coe_id, LinearMap.det_id]
  rw [show LinearMap.det (fderiv ℝ Φ z₀ : ℂ →ₗ[ℝ] ℂ) = 0 from h, mul_zero] at h1
  exact zero_ne_one h1

/-- **Extending a change of half-plane chart across the real axis.** Let `e` be a partial
equivalence between the relatively open subsets `Ω ∩ {0 ≤ im}` and `Ω' ∩ {0 ≤ im}` of the closed
upper half-plane, for open `Ω` and `Ω'`, that is `Cⁿ` in both directions, `n ≥ 1`. Near each point
of its source, `e` agrees with a map that is `Cⁿ` with invertible derivative on an open
neighbourhood `U ⊆ Ω` of the point. -/
theorem exists_contDiffOn_eqOn_det_fderiv_ne_zero (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hs : e.source = Ω ∩ {z | 0 ≤ z.im}) (ht : e.target = Ω' ∩ {z | 0 ≤ z.im})
    (he : ContDiffOn ℝ n e e.source) (he' : ContDiffOn ℝ n e.symm e.target) {z₀ : ℂ}
    (hz₀ : z₀ ∈ e.source) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ⊆ Ω ∧ ∃ Φ : ℂ → ℂ, ContDiffOn ℝ n Φ U ∧
      (∀ z ∈ U, (fderiv ℝ Φ z).det ≠ 0) ∧ EqOn Φ e (e.source ∩ U) := by
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  rw [hs] at he hz₀
  rw [ht] at he'
  obtain ⟨W, hW, hz₀W, Φ, hΦ, hΦe⟩ := exists_contDiffOn_eqOn_inter_setOf_im_nonneg hΩ he hz₀
  have hez₀ : e z₀ ∈ Ω' ∩ {z | 0 ≤ z.im} := ht ▸ e.map_source (hs ▸ hz₀)
  obtain ⟨W', hW', hz₀W', Ψ, hΨ, hΨe⟩ := exists_contDiffOn_eqOn_inter_setOf_im_nonneg hΩ' he' hez₀
  have hΦz₀ : Φ z₀ = e z₀ := hΦe ⟨hz₀, hz₀W⟩
  -- On a neighbourhood of `z₀` in the closed upper half-plane, `Ψ ∘ Φ` is the identity.
  set S : Set ℂ := (Ω ∩ {z | 0 ≤ z.im}) ∩ (W ∩ Φ ⁻¹' W')
  have hSo : IsOpen (W ∩ Φ ⁻¹' W') := hΦ.continuousOn.isOpen_inter_preimage hW hW'
  have hid : EqOn (Ψ ∘ Φ) id S := fun z hz ↦ by
    have hz' : z ∈ e.source := hs ▸ hz.1
    have hΦz : Φ z = e z := hΦe ⟨hz.1, hz.2.1⟩
    simp only [Function.comp_apply, id, hΦz]
    rw [hΨe ⟨ht ▸ e.map_source hz', hΦz ▸ hz.2.2⟩, e.left_inv hz']
  -- Derivatives are unique within `S`, a neighbourhood of `z₀` in the closed upper half-plane.
  have huniq : UniqueDiffWithinAt ℝ S z₀ := by
    have hH : UniqueDiffWithinAt ℝ {z : ℂ | 0 ≤ z.im} z₀ :=
      uniqueDiffWithinAt_convex (convex_halfSpace_im_ge 0)
        ⟨Complex.I, mem_interior_iff_mem_nhds.2 (mem_of_superset
          ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp))
          fun z hz ↦ le_of_lt hz)⟩ (subset_closure hz₀.2)
    refine hH.mono_nhds (nhdsWithin_le_iff.2 ?_)
    exact inter_mem (inter_mem (mem_nhdsWithin_of_mem_nhds (hΩ.mem_nhds hz₀.1))
      self_mem_nhdsWithin) (mem_nhdsWithin_of_mem_nhds (hSo.mem_nhds ⟨hz₀W, by
        rw [mem_preimage, hΦz₀]; exact hz₀W'⟩))
  have hdet₀ := det_fderiv_ne_zero_of_eqOn_comp_id huniq
    ((hΦ.differentiableOn hn0) z₀ hz₀W |>.differentiableAt (hW.mem_nhds hz₀W))
    (hΦz₀ ▸ ((hΨ.differentiableOn hn0) _ hz₀W').differentiableAt (hW'.mem_nhds hz₀W')) hid
    ⟨hz₀, hz₀W, by rw [mem_preimage, hΦz₀]; exact hz₀W'⟩
  -- The determinant of the derivative of `Φ` is continuous on `W`, so nonzero near `z₀`.
  have hdetc : ContinuousOn (fun z ↦ (fderiv ℝ Φ z).det) W :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hΦ.continuousOn_fderiv_of_isOpen hW (by exact_mod_cast hn))
  refine ⟨Ω ∩ (W ∩ (fun z ↦ (fderiv ℝ Φ z).det) ⁻¹' {0}ᶜ),
    hΩ.inter (hdetc.isOpen_inter_preimage hW isOpen_compl_singleton), ⟨hz₀.1, hz₀W, hdet₀⟩,
    inter_subset_left, Φ, hΦ.mono fun z hz ↦ hz.2.1, fun z hz ↦ hz.2.2, fun z hz ↦ ?_⟩
  exact hΦe ⟨hs ▸ hz.1, hz.2.2.1⟩

/-- **Changes of half-plane chart preserve the half-disc classes.** Let `e` be a partial
equivalence between the relatively open subsets `Ω ∩ {0 ≤ im}` and `Ω' ∩ {0 ≤ im}` of the closed
upper half-plane, for open `Ω` and `Ω'`, that is `Cⁿ` in both directions, `n ≥ 1`, as a change of
chart of a `Cⁿ` manifold modelled on the closed upper half-plane is. For `1 ≤ p ≤ ∞`, an order
`k ≤ n`, an open `V` and a map `u` into a finite-dimensional space in the half-disc class
`MemWkpLoc p (V ∩ {0 ≤ im}) k`, the map `u ∘ e` lies in the local class on the points of the source
of `e` that it maps into `V`. -/
theorem MemWkpLoc.comp_partialEquiv_halfPlane [Fact (1 ≤ p)] [FiniteDimensional ℝ F]
    (hn : 1 ≤ n) (hkn : k ≤ n) (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hs : e.source = Ω ∩ {z | 0 ≤ z.im}) (ht : e.target = Ω' ∩ {z | 0 ≤ z.im})
    (he : ContDiffOn ℝ n e e.source) (he' : ContDiffOn ℝ n e.symm e.target) {V : Set ℂ}
    (hV : IsOpen V) {u : ℂ → F} (hu : MemWkpLoc p (V ∩ {z | 0 ≤ z.im}) k u) :
    MemWkpLoc p (e.source ∩ e ⁻¹' V) k (fun z ↦ u (e z)) := by
  refine memWkpLoc_iff_locally.2 fun z₀ hz₀ ↦ ?_
  obtain ⟨U, hU, hz₀U, hUΩ, Φ, hΦ, hdet, hΦe⟩ :=
    exists_contDiffOn_eqOn_det_fderiv_ne_zero hn hΩ hΩ' hs ht he he' hz₀.1
  -- Shrink `U` so that `Φ` maps it into `V`.
  set U₁ : Set ℂ := U ∩ Φ ⁻¹' V
  have hU₁ : IsOpen U₁ := hΦ.continuousOn.isOpen_inter_preimage hU hV
  have hU₁s : U₁ ∩ {z | 0 ≤ z.im} ⊆ e.source := fun z hz ↦ hs ▸ ⟨hUΩ hz.1.1, hz.2⟩
  have hΦe₁ : EqOn Φ e (U₁ ∩ {z | 0 ≤ z.im}) := fun z hz ↦ hΦe ⟨hU₁s hz, hz.1.1⟩
  have hmaps : MapsTo Φ (U₁ ∩ {z | 0 ≤ z.im}) (V ∩ {z | 0 ≤ z.im}) := fun z hz ↦ by
    refine ⟨hz.1.2, ?_⟩
    rw [hΦe₁ hz]
    exact ((ht ▸ e.map_source (hU₁s hz)) : e z ∈ Ω' ∩ {z | 0 ≤ z.im}).2
  have hcomp : MemWkpLoc p (U₁ ∩ {z | 0 ≤ z.im}) k (fun z ↦ u (Φ z)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hinj : InjOn Φ (U₁ ∩ {z | 0 ≤ z.im}) := fun z hz w hw h ↦
        e.injOn (hU₁s hz) (hU₁s hw) (by rw [← hΦe₁ hz, ← hΦe₁ hw, h])
      exact hu.comp_contDiffOn_diffeo zero_le_one hU₁
        ((hΦ.mono inter_subset_left).of_le (by exact_mod_cast hn)) hinj
        (fun z hz ↦ hdet z hz.1.1) inter_subset_left hmaps
    · exact hu.comp_contDiffOn_halfPlane hk (U := ⟨U₁, hU₁⟩) (V := ⟨V, hV⟩)
        ((hΦ.mono inter_subset_left).of_le (by exact_mod_cast hkn))
        (fun z hz ↦ hdet z hz.1) hmaps
  refine ⟨U₁ ∩ {z | 0 ≤ z.im}, ?_, hcomp.congr fun z hz ↦ by rw [← hΦe₁ hz]⟩
  refine mem_nhdsWithin.2 ⟨U₁, hU₁, ⟨hz₀U, ?_⟩, fun z hz ↦ ⟨hz.1, (hs ▸ hz.2.1).2⟩⟩
  rw [mem_preimage, hΦe ⟨hz₀.1, hz₀U⟩]
  exact hz₀.2

end TauCeti
