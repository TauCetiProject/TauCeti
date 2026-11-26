/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Gray
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
import TauCeti.Geometry.Manifold.ContMDiff.Subtype.Cutoff

/-!
# Gray stability on closed manifolds, as a diffeotopy

Let `M` be a compact manifold without boundary and let `α_t` be a smooth family of one-forms on
`M`, represented by a smooth one-form `α` on `ℝ × M` whose slices `α_t = ι_t^* α` are the forms of
the family. **Gray's stability theorem** says that if `α_t` is a contact form for every
`t ∈ [0, 1]`, then there is a diffeotopy `Φ` of `M` (`TauCeti.Diffeotopy`), a smooth motion of `M`
through diffeomorphisms starting at the identity, which carries the contact structures into each
other up to a positive multiplier:

`Φ_t^* α_t = g_t α_0` with `g_t > 0`, for every `t ∈ [0, 1]`

(`TauCeti.SmoothForm.exists_diffeotopy_mpullback_eq_pos_smul`). So every time slice `Φ_t` is a
contactomorphism from `ker α_0` to `ker α_t` carrying the coorientation given by `α_0` to that
given by `α_t` (`TauCeti.SmoothForm.exists_diffeotopy_preservesCoorientation`). A positive
multiplier cannot be avoided: for `α_t = (1 + t) α_0` the contact volume `∫ α_t ∧ (dα_t)ⁿ` grows
with `t`, while a diffeomorphism preserves it up to sign.

When every slice of `α` is a contact form, the diffeotopy is the time-dependent flow of the Gray
vector field from time `0` (`TauCeti.SmoothForm.grayDiffeotopy`), whose time slices are Gray's
isotopy `TauCeti.SmoothForm.grayDiffeomorph` from time `0`
(`TauCeti.SmoothForm.timeSlice_grayDiffeotopy`). They rescale the forms by
`exp (∫₀ᵗ μ_u ∘ φ_{0,u} du)`, where `μ_u = (∂_t α_u)(R_{α_u})`
(`TauCeti.SmoothForm.mpullback_timeSlice_grayDiffeotopy_apply`).

Only the times `t ∈ [0, 1]` are assumed to give contact forms. Since `M` is compact, the slices are
then contact forms for all times of an open neighbourhood `U` of `[0, 1]`
(`TauCeti.SmoothForm.isOpen_setOf_isContactForm_mpullback_prodMk`). A smooth map `ρ : ℝ → U` which
is the identity near `[0, 1]` (`TopologicalSpace.Opens.exists_contMDiff_eventuallyEq_id`)
reparametrizes the family to `α_(ρ t)`, all of whose slices are contact forms and which agrees
with `α_t` for `t ∈ [0, 1]` (`TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap_id`). Gray's
diffeotopy of the reparametrized family is the diffeotopy of the theorem.

## Main definitions

* `TauCeti.SmoothForm.grayDiffeotopy`: Gray's diffeotopy of a smooth family of contact forms on a
  compact manifold.

## Main results

* `TauCeti.SmoothForm.mpullback_timeSlice_grayDiffeotopy_apply`: Gray's diffeotopy rescales the
  forms by an explicit positive factor.
* `TauCeti.SmoothForm.preservesCoorientation_timeSlice_grayDiffeotopy`: its time slices are
  coorientation-preserving contactomorphisms.
* `TauCeti.SmoothForm.exists_diffeotopy_mpullback_eq_pos_smul`: Gray's stability theorem on a
  compact manifold, for a family of one-forms which are contact forms for `t ∈ [0, 1]`.
* `TauCeti.SmoothForm.exists_diffeotopy_preservesCoorientation`: the same, in terms of
  coorientation-preserving contactomorphisms.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof.
* J. W. Gray, *Some global properties of contact structures*, Ann. of Math. 69 (1959), 421–450.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1}

/-! ### Gray's diffeotopy of a family of contact forms -/

section Diffeotopy

variable (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)

/-- **Gray's diffeotopy.** On a compact manifold without boundary, the time-dependent flow of the
Gray vector field of a smooth family of contact forms `α_t`, from time `0` to times `t ∈ [0, 1]`,
as a diffeotopy. Its time slices are Gray's isotopy from time `0`
(`TauCeti.SmoothForm.timeSlice_grayDiffeotopy`), and they pull `α_t` back to a positive multiple of
`α_0` (`TauCeti.SmoothForm.mpullback_timeSlice_grayDiffeotopy_apply`). -/
def grayDiffeotopy : Diffeotopy I ∞ M :=
  timeDependentFlowDiffeotopy (n := ⊤) le_top (contMDiff_grayVectorField hc)
    (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc)

/-- Gray's diffeotopy at time `t` is Gray's isotopy from time `0` to time `t`. -/
@[simp]
theorem grayDiffeotopy_apply (p : unitInterval × M) :
    grayDiffeotopy hc p = grayDiffeomorph hc 0 p.1 p.2 :=
  (timeDependentFlowDiffeotopy_apply _ _ _ p).trans (grayDiffeomorph_apply hc 0 p.1 p.2).symm

/-- The time-`t` slice of Gray's diffeotopy is Gray's isotopy from time `0` to time `t`. -/
theorem timeSlice_grayDiffeotopy (t : unitInterval) :
    ⇑((grayDiffeotopy hc).timeSlice t) = grayDiffeomorph hc 0 t :=
  funext fun x ↦ (Diffeotopy.timeSlice_apply _ t x).trans (grayDiffeotopy_apply hc (t, x))

/-- **Gray's stability theorem, as a diffeotopy.** The time-`t` slice `φ_t` of Gray's diffeotopy
rescales the forms: `φ_t^* α_t = exp (∫₀ᵗ μ_u ∘ φ_u du) α_0`, where `μ_u = (∂_t α_u)(R_{α_u})` is
the Gray rate. -/
theorem mpullback_timeSlice_grayDiffeotopy_apply (t : unitInterval) (x : M) :
    (mpullback ((grayDiffeotopy hc).timeSlice t) ((grayDiffeotopy hc).timeSlice t).contMDiff
        (mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id) α)).val x =
      Real.exp (∫ u in (0 : ℝ)..t, α.grayRate (u, grayDiffeomorph hc 0 u x)) •
        (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).val x := by
  rw [coe_mpullback, timeSlice_grayDiffeotopy, ← coe_mpullback]
  exact mpullback_grayDiffeomorph_apply hc 0 t x

/-- The time slices of Gray's diffeotopy are contactomorphisms from `ker α_0` to `ker α_t`,
carrying the coorientation given by `α_0` to that given by `α_t`. -/
theorem preservesCoorientation_timeSlice_grayDiffeotopy (t : unitInterval) :
    ((grayDiffeotopy hc).timeSlice t).PreservesCoorientation
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α)
      (mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id) α) :=
  Diffeomorph.preservesCoorientation_def.2 fun x ↦
    ⟨_, Real.exp_pos _, mpullback_timeSlice_grayDiffeotopy_apply hc t x⟩

end Diffeotopy

/-! ### Families which are contact on `[0, 1]` -/

/-- **Gray's stability theorem on a closed manifold.** Let `M` be compact, Hausdorff and without
boundary, and let `α` be a smooth one-form on `ℝ × M` whose slice `α_t = ι_t^* α` is a contact form
for every `t ∈ [0, 1]`. Then there are a diffeotopy `Φ` of `M` and a positive function `g` with
`Φ_t^* α_t = g_t α_0` for every `t ∈ [0, 1]`. The slices at other times are not assumed to be
contact forms. -/
theorem exists_diffeotopy_mpullback_eq_pos_smul
    (hc : ∀ t ∈ Icc (0 : ℝ) 1,
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    ∃ Φ : Diffeotopy I ∞ M, ∃ g : unitInterval → M → ℝ, (∀ t x, 0 < g t x) ∧
      ∀ (t : unitInterval) (x : M),
        TauCeti.mpullback I I (fun y ↦ Φ (t, y))
            (mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id) α).val x =
          g t x • (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).val x := by
  -- The slices are contact forms at the times of an open neighbourhood of `[0, 1]`; reparametrize
  -- time by a smooth map `ρ` into that neighbourhood which is the identity on `[0, 1]`.
  let U : TopologicalSpace.Opens ℝ := ⟨_, isOpen_setOf_isContactForm_mpullback_prodMk α⟩
  obtain ⟨g, hg, hgid⟩ :=
    U.exists_contMDiff_eventuallyEq_id (convex_Icc 0 1) isCompact_Icc
      (nonempty_Icc.2 zero_le_one) hc
  set ρ : ℝ → ℝ := fun t ↦ (g t : ℝ)
  have hρ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ := contMDiff_subtypeVal.comp hg
  let β := mpullback (Prod.map ρ id) (hρ.prodMap contMDiff_id) α
  have hβ (t : ℝ) : mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β =
      mpullback (Prod.mk (ρ t)) (contMDiff_const.prodMk contMDiff_id) α :=
    mpullback_prodMk_mpullback_prodMap_id α hρ t
  have hβc (t : ℝ) :
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).IsContactForm :=
    hβ t ▸ (g t).property
  -- On `[0, 1]` the reparametrized family is the original one.
  have hβα {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β =
        mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α := by
    rw [hβ t, show ρ t = t from (hgid t ht).self_of_nhds]
  refine ⟨grayDiffeotopy hβc, fun t x ↦ Real.exp
      (∫ u in (0 : ℝ)..t, β.grayRate (u, grayDiffeomorph hβc 0 u x)),
    fun t x ↦ Real.exp_pos _, fun t x ↦ ?_⟩
  have h := mpullback_timeSlice_grayDiffeotopy_apply hβc t x
  rw [hβα t.property, hβα unitInterval.zero_mem, coe_mpullback,
    funext (Diffeotopy.timeSlice_apply _ t)] at h
  exact h

/-- **Gray's stability theorem on a closed manifold, coorientation form.** Under the hypotheses of
`TauCeti.SmoothForm.exists_diffeotopy_mpullback_eq_pos_smul`, there is a diffeotopy of `M` whose
time-`t` slice, for every `t ∈ [0, 1]`, is a contactomorphism from `ker α_0` to `ker α_t` carrying
the coorientation given by `α_0` to that given by `α_t`. -/
theorem exists_diffeotopy_preservesCoorientation
    (hc : ∀ t ∈ Icc (0 : ℝ) 1,
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    ∃ Φ : Diffeotopy I ∞ M, ∀ t : unitInterval, (Φ.timeSlice t).PreservesCoorientation
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α)
      (mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id) α) := by
  obtain ⟨Φ, g, hg, hΦ⟩ := exists_diffeotopy_mpullback_eq_pos_smul hc
  exact ⟨Φ, fun t ↦ Diffeomorph.preservesCoorientation_def.2 fun x ↦
    ⟨g t x, hg t x, by rw [coe_mpullback, funext (Diffeotopy.timeSlice_apply Φ t)]; exact hΦ t x⟩⟩

end TauCeti.SmoothForm
