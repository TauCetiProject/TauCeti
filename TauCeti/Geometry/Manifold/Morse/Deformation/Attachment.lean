/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Deformation
public import TauCeti.Topology.Homotopy.Extension.Pushout
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Moving an attachment across regular collars

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and write
`M_t = {f ≤ t}`. Suppose that some space `D` is attached to `M_s` along a closed cofibration
`A → D` and an attaching map `α : A → M_s`, and that the result is homotopy equivalent to a larger
sublevel `M_t`, by a homotopy equivalence which is the inclusion on `M_s`. If `a ≤ s` and `t ≤ b`
and the collars `f⁻¹[a, s]` and `f⁻¹[t, b]` are compact and contain no critical point of `f`, then
`M_b` is homotopy equivalent to `D` attached to `M_a` along `r ∘ α`, for a retraction `r` of
`M_s` onto `M_a`, by a homotopy equivalence which is the inclusion on `M_a`
(`TauCeti.exists_homotopyEquiv_pushout_comp_sublevelRetraction`).

This is the common last step of the attachment theorems of Morse and Morse–Bott theory, which
attach cells or disc bundles along a narrow band around a critical level and then widen the band to
arbitrary regular levels (`TauCeti.IsMorse.exists_homotopyEquiv_sigmaDiskAdjunctionSpace`, and
`IsNondegenerateCriticalSubmanifold.exists_homotopyEquiv_pushout_negativeDiscBundle` in the
namespace `TauCeti.SmoothEmbedding`).
The inclusion `M_t → M_b` is a homotopy equivalence (`TauCeti.exists_sublevelHomotopyEquiv`); the
retraction `r` is a homotopy equivalence with homotopy inverse the inclusion
(`TauCeti.exists_sublevelDeformation`), and attaching along a cofibration is homotopy invariant
under a change of base (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_pushout`).

## Main results

* `TauCeti.exists_homotopyEquiv_pushout_comp_sublevelRetraction`: an attachment to `M_s`
  homotopy equivalent to `M_t` moves to an attachment to `M_a` homotopy equivalent to `M_b` across
  regular collars `f⁻¹[a, s]` and `f⁻¹[t, b]`.
* `TauCeti.exists_homotopyEquiv_pushout_comp_sublevelRetraction_of_isCompact_preimage_Icc`: the
  same, for a compact band `f⁻¹[a, b]` whose critical values all lie in `(s, t)`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1 and Remark 3.3.
-/

public section

noncomputable section

open Set Topology CategoryTheory Limits
open scoped ContDiff Manifold ContinuousMap

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {a b s t : ℝ}

/-- **Moving an attachment across regular collars.** Let `j : A → D` be an embedding whose image
has the homotopy extension property, and `α : A → M_s` an attaching map, and suppose that
`M_s ∪_α D` is homotopy equivalent to `M_t` by a homotopy equivalence which is the inclusion on
`M_s`. If `a ≤ s` and `t ≤ b` and the collars `f⁻¹[a, s]` and `f⁻¹[t, b]` are compact and contain
no critical point of `f`, there is a retraction `r` of `M_s` onto `M_a` such that `M_a ∪_{r ∘ α} D`
is homotopy equivalent to `M_b` by a homotopy equivalence which is the inclusion on `M_a`. -/
theorem exists_homotopyEquiv_pushout_comp_sublevelRetraction (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (has : a ≤ s) (hcas : IsCompact (f ⁻¹' Icc a s))
    (hregas : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0) (htb : t ≤ b)
    (hctb : IsCompact (f ⁻¹' Icc t b))
    (hregtb : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) {A D : TopCat.{u}} (j : A ⟶ D)
    (hj : IsEmbedding j) (hA : HasHomotopyExtensionProperty (range j))
    (α : A ⟶ TopCat.of {x | f x ≤ s}) (e : ↑(pushout j α) ≃ₕ {x | f x ≤ t})
    (he : ∀ z, (e (pushout.inr j α z) : M) = z) :
    ∃ r : C({x | f x ≤ s}, {x | f x ≤ a}), (∀ x : {x | f x ≤ s}, f x ≤ a → (r x : M) = x) ∧
      ∃ E : ↑(pushout j (α ≫ TopCat.ofHom r)) ≃ₕ {x | f x ≤ b},
        ∀ z, (E (pushout.inr j (α ≫ TopCat.ofHom r) z) : M) = z := by
  -- The retraction `r` of `M_s` onto `M_a` is a homotopy equivalence with homotopy inverse the
  -- inclusion.
  obtain ⟨r, hr, ⟨R⟩⟩ := exists_sublevelDeformation hf has hcas hregas
  rw [sublevelInclusion_eq_inclusion] at hr R
  set er := (ContinuousMap.HomotopyEquiv.ofDeformationRetraction (.inclusion _) r hr
    (ContinuousMap.HomotopicRel.homotopic ⟨R⟩)).symm
  have her : α ≫ TopCat.ofHom r = α ≫ TopCat.ofHom er.toFun :=
    congrArg (α ≫ TopCat.ofHom ·) (ContinuousMap.ext
      (ContinuousMap.HomotopyEquiv.ofDeformationRetraction_symm_apply _ r hr _)).symm
  -- The inclusion `M_t → M_b` across the collar `f⁻¹[t, b]`.
  obtain ⟨e₂, he₂⟩ := exists_sublevelHomotopyEquiv hf htb hctb hregtb
  -- Change the base of the attachment from `M_s` to `M_a` along `r`.
  obtain ⟨E, -, hE⟩ := er.exists_homotopyEquiv_pushout j hj hA α
  refine ⟨r, fun x hx ↦ ?_, ?_⟩
  · have h := hr ⟨x, hx⟩
    rw [show ContinuousMap.inclusion _ (⟨x, hx⟩ : {y | f y ≤ a}) = x from
      Subtype.ext (ContinuousMap.inclusion_apply_coe _ _)] at h
    rw [h]
  rw [her]
  refine ⟨E.symm.trans (e.trans e₂), fun z ↦ ?_⟩
  rw [ContinuousMap.HomotopyEquiv.trans_apply, ContinuousMap.HomotopyEquiv.trans_apply, he₂, hE,
    he]
  simp [er]

/-- **Moving an attachment across the regular collars of a compact band.** Let `j : A → D` be an
embedding whose image has the homotopy extension property, and `α : A → M_s` an attaching map, and
suppose that `M_s ∪_α D` is homotopy equivalent to `M_t` by a homotopy equivalence which is the
inclusion on `M_s`. If `a ≤ s ≤ t ≤ b`, the band `f⁻¹[a, b]` is compact and every critical point
of `f` in it has value in `(s, t)`, there is a retraction `r` of `M_s` onto `M_a` such that
`M_a ∪_{r ∘ α} D` is homotopy equivalent to `M_b` by a homotopy equivalence which is the inclusion
on `M_a`. -/
theorem exists_homotopyEquiv_pushout_comp_sublevelRetraction_of_isCompact_preimage_Icc
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x ∈ Ioo s t) {A D : TopCat.{u}}
    (j : A ⟶ D) (hj : IsEmbedding j) (hA : HasHomotopyExtensionProperty (range j))
    (α : A ⟶ TopCat.of {x | f x ≤ s}) (e : ↑(pushout j α) ≃ₕ {x | f x ≤ t})
    (he : ∀ z, (e (pushout.inr j α z) : M) = z) :
    ∃ r : C({x | f x ≤ s}, {x | f x ≤ a}), (∀ x : {x | f x ≤ s}, f x ≤ a → (r x : M) = x) ∧
      ∃ E : ↑(pushout j (α ≫ TopCat.ofHom r)) ≃ₕ {x | f x ≤ b},
        ∀ z, (E (pushout.inr j (α ≫ TopCat.ofHom r) z) : M) = z := by
  have hsub {s' t' : ℝ} (hs : a ≤ s') (ht : t' ≤ b) : IsCompact (f ⁻¹' Icc s' t') :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc hs ht))
  -- Critical points of `f` in the band lie strictly between the collars.
  have hcrit' {x} (h0 : mfderiv I 𝓘(ℝ) f x = 0) (hax : a ≤ f x) (hxb : f x ≤ b) :
      f x ∈ Ioo s t :=
    hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) ⟨hax, hxb⟩
  exact exists_homotopyEquiv_pushout_comp_sublevelRetraction hf has (hsub le_rfl (hst.trans htb))
    (fun x hax hxs h0 ↦ (hcrit' h0 hax (hxs.trans (hst.trans htb))).1.not_ge hxs) htb
    (hsub (has.trans hst) le_rfl)
    (fun x htx hxb h0 ↦ (hcrit' h0 ((has.trans hst).trans htx) hxb).2.not_ge htx) j hj hA α e he

end TauCeti
