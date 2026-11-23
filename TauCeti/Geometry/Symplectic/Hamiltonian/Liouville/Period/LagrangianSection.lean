/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Section
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Twisted

/-!
# Sections of a regular Lagrangian torus fibration and one-forms on its base

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
with period lattice `Λ_b ⊆ T*_b B`. Fix a smooth section `s` of `π` and its section map
`Φ_s : T*B → M`, `Φ_s(ξ) = (-ξ) • s(b)` (`IsLagrangianTorusFibration.sectionMap`). This file
describes the other sections of `π` through `Φ_s`: the sections of the form `Φ_s ∘ α` are the
one-forms `α` on `B` modulo `Λ`, the Lagrangian ones being those with `dα = s^* σ`. Every
section of `π` has this form locally, with lifts unique up to `Λ`; a global section need not
have a global lift.

A one-form `α` on `B` moves `s` to the section

`s_α = Φ_s ∘ α : b ↦ (-α_b) • s(b)` (`IsLagrangianTorusFibration.sectionMapGraph`),

the image under `Φ_s` of the graph of `α`. Then:

* `s_0 = s` (`IsLagrangianTorusFibration.sectionMapGraph_zero`), and `s_α = s_β` exactly when
  `α_b - β_b ∈ Λ_b` at every `b`
  (`IsLagrangianTorusFibration.sectionMapGraph_eq_sectionMapGraph_iff`).
* Moving the reference section translates the section map: `Φ_(s_α)(ξ) = Φ_s(ξ + α_b)` for a
  covector `ξ` at `b` (`IsLagrangianTorusFibration.sectionMap_sectionMapGraph`). Hence moving
  first by `α` and then by `β` is moving by `β + α`
  (`IsLagrangianTorusFibration.sectionMapGraph_sectionMapGraph`): the one-forms on `B` act on
  the sections of `π`, and two of them act alike exactly when they differ by periods.
* **The pullback formula.** `s_α^* σ = s^* σ - dα`
  (`IsLagrangianTorusFibration.mpullback_sectionMapGraph`). So `s_α` is a Lagrangian section
  exactly when `dα = s^* σ` (`IsLagrangianTorusFibration.isLagrangianMap_sectionMapGraph_iff`),
  and if `s` is Lagrangian, exactly when `α` is closed
  (`IsLagrangianTorusFibration.isLagrangianMap_sectionMapGraph_iff_isClosed`).
* **Every section is locally of this form.** A smooth section `s'` of `π` over an open set `V`
  lifts near each point of `V` along the local diffeomorphism `Φ_s` to a smooth local section
  `a` of `T*B` (`IsLagrangianTorusFibration.exists_contMDiffOn_sectionMap_eq`), and then
  `s'^* σ = a^* ω + s^* σ` pointwise, `ω = -dλ` being the canonical form of `T*B`
  (`IsLagrangianTorusFibration.eval₂_mfderiv_of_sectionMap_eventuallyEq`). The lift is unique up
  to the period lattice (`IsLagrangianTorusFibration.sectionMap_mk_eq_sectionMap_mk_iff`).

So, relative to a Lagrangian section `s`, a local smooth section `s'` of `π` is Lagrangian near a
point exactly when its local lifts `a` pull `ω` back to zero there, and these lifts are determined
up to `Λ`; for global one-forms this condition says that the one-form is closed. This is the
description of the Lagrangian sections through the sheaf `Z¹/Λ` of closed one-forms modulo the
period lattice, by which Duistermaat defines the Lagrangian class of the fibration, its
obstruction to having a global Lagrangian section.

The fact that a section of a Lagrangian fibration is a Lagrangian map as soon as it is isotropic
is `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianFibration.isLagrangianMap_iff_isIsotropicMap`.

## Main definitions

* `IsLagrangianTorusFibration.sectionMapGraph`: the section `Φ_s ∘ α` moved by a one-form `α`.

## Main results

* `IsLagrangianTorusFibration.sectionMapGraph_eq_sectionMapGraph_iff`: two one-forms move `s` to
  the same section exactly when they differ by periods.
* `IsLagrangianTorusFibration.sectionMap_sectionMapGraph`,
  `IsLagrangianTorusFibration.sectionMapGraph_sectionMapGraph`: change of the reference section.
* `IsLagrangianTorusFibration.mpullback_sectionMapGraph`: `(Φ_s ∘ α)^* σ = s^* σ - dα`.
* `IsLagrangianTorusFibration.isLagrangianMap_sectionMapGraph_iff_isClosed`: relative to a
  Lagrangian section, `Φ_s ∘ α` is Lagrangian exactly when `α` is closed.
* `IsLagrangianTorusFibration.exists_contMDiffOn_sectionMap_eq`: local sections lift through
  `Φ_s`.
* `IsLagrangianTorusFibration.eval₂_mfderiv_of_sectionMap_eventuallyEq`: the pointwise pullback
  formula for such a lift.

All in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (Lagrangian sections, the sheaf of closed one-forms modulo the period
  lattice and the Lagrangian class).
-/

public section

noncomputable section

open Bundle (TotalSpace)
open Function Set Module Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

namespace IsLagrangianTorusFibration

variable [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space B]
  (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed) {s : B → M}
  (hs : ∀ b, π (s b) = b)

/-! ### Moving a section by a one-form -/

/-- **The section moved by a one-form.** For a section `s` of `π` and a smooth one-form `α` on
`B`, the section `b ↦ Φ_s(α_b) = (-α_b) • s(b)`, the image of the graph of `α` under the section
map `Φ_s`. -/
def sectionMapGraph (α : SmoothForm J B ℝ 1) (b : B) : M :=
  h.sectionMap hσc hs (TotalSpace.mk' (F →L[ℝ] ℝ) b (SmoothForm.degreeOneEquiv α b))

/-- The section moved by `α` is the section map on the graph of `α`. -/
theorem sectionMapGraph_apply (α : SmoothForm J B ℝ 1) (b : B) :
    h.sectionMapGraph hσc hs α b =
      h.sectionMap hσc hs (TotalSpace.mk' (F →L[ℝ] ℝ) b (SmoothForm.degreeOneEquiv α b)) :=
  (rfl)

/-- **The section moved by a one-form is a section.** -/
theorem proj_sectionMapGraph (α : SmoothForm J B ℝ 1) (b : B) :
    π (h.sectionMapGraph hσc hs α b) = b :=
  h.proj_sectionMap hσc hs _

/-- **Moving by the zero form does not move the section.** -/
@[simp]
theorem sectionMapGraph_zero : h.sectionMapGraph hσc hs 0 = s :=
  funext fun b ↦ by rw [sectionMapGraph_apply, map_zero]; exact h.sectionMap_mk_zero hσc hs b

/-- **Two one-forms move a section to the same section exactly when they differ by periods**:
`Φ_s ∘ α = Φ_s ∘ β` if and only if `α_b - β_b` lies in the period lattice `Λ_b` for every `b`. -/
theorem sectionMapGraph_eq_sectionMapGraph_iff (α β : SmoothForm J B ℝ 1) :
    h.sectionMapGraph hσc hs α = h.sectionMapGraph hσc hs β ↔
      ∀ b, SmoothForm.degreeOneEquiv (α - β) b ∈ h.periodLattice hσc b := by
  simp only [funext_iff, sectionMapGraph_apply]
  refine forall_congr' fun b ↦ (h.sectionMap_mk_eq_sectionMap_mk_iff hσc hs b _ _).trans ?_
  rw [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  -- The two sides subtract in `F →L[ℝ] ℝ` and in `TangentSpace J b →L[ℝ] ℝ`, the same space.
  exact Iff.rfl

/-- **Changing the reference section translates the section map.** The section map of the section
`Φ_s ∘ α` moved by `α` sends a covector `ξ` at `b` to `Φ_s(ξ + α_b)`. -/
theorem sectionMap_sectionMapGraph (α : SmoothForm J B ℝ 1) (b : B)
    (ξ : TangentSpace J b →L[ℝ] ℝ) :
    h.sectionMap hσc (h.proj_sectionMapGraph hσc hs α) (TotalSpace.mk' (F →L[ℝ] ℝ) b ξ) =
      h.sectionMap hσc hs
        (TotalSpace.mk' (F →L[ℝ] ℝ) b (ξ + SmoothForm.degreeOneEquiv α b)) := by
  refine Eq.trans ?_ (h.sectionMap_mk_add hσc hs b ξ (SmoothForm.degreeOneEquiv α b)).symm
  -- The point `Φ_s ∘ α` at `b` is by definition `Φ_s(α_b)`.
  exact h.sectionMap_mk hσc (h.proj_sectionMapGraph hσc hs α) b ξ

/-- **Moving by `α` and then by `β` is moving by `β + α`.** The smooth one-forms on `B` act on the
sections of `π` through the section maps. -/
theorem sectionMapGraph_sectionMapGraph (α β : SmoothForm J B ℝ 1) :
    h.sectionMapGraph hσc (h.proj_sectionMapGraph hσc hs α) β =
      h.sectionMapGraph hσc hs (β + α) :=
  funext fun b ↦ (h.sectionMap_sectionMapGraph hσc hs α b _).trans <| by
    rw [sectionMapGraph_apply, map_add, ContMDiffSection.coe_add, Pi.add_apply]

variable [BoundarylessManifold J B]

/-- **The section moved by a smooth one-form is smooth** when `s` is. -/
theorem contMDiff_sectionMapGraph (hsm : ContMDiff J I ∞ s) (α : SmoothForm J B ℝ 1) :
    ContMDiff J I ∞ (h.sectionMapGraph hσc hs α) :=
  (h.contMDiff_sectionMap hσc hs hsm).comp (SmoothForm.degreeOneEquiv α).contMDiff

/-! ### The pullback of the symplectic form -/

/-- **The pullback formula for a section lifted through the section map.** Let `a` be a local
section of `T*B → B` near `b`, differentiable at `b`, and let `s'` agree with `Φ_s ∘ a` near `b`.
Then on tangent vectors `v` and `w` at `b`,

`σ(ds' v, ds' w) = ω(da v, da w) + σ(ds v, ds w)`,

where `ω = -dλ` is the canonical symplectic form of `T*B`. -/
theorem eval₂_mfderiv_of_sectionMap_eventuallyEq (hsm : ContMDiff J I ∞ s)
    {a : B → CotangentBundle J B} {s' : B → M} {b : B}
    (ha : MDifferentiableAt J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) a b)
    (hproj : ∀ᶠ b' in 𝓝 b, (a b').proj = b')
    (heq : h.sectionMap hσc hs ∘ a =ᶠ[𝓝 b] s') (v w : TangentSpace J b) :
    SmoothBundleForm.eval₂ σ (s' b) (mfderiv J I s' b v) (mfderiv J I s' b w) =
      SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm J B) (a b)
          (mfderiv J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) a b v)
          (mfderiv J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) a b w) +
        SmoothBundleForm.eval₂ σ (s b) (mfderiv J I s b v) (mfderiv J I s b w) := by
  have hΦ : MDifferentiableAt (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) (a b) :=
    (h.contMDiff_sectionMap hσc hs hsm (a b)).mdifferentiableAt (by simp)
  -- The projection after `a` is the identity near `b`, so `dπ ∘ da = id` at `b`.
  have hπa (u : TangentSpace J b) :
      mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J TotalSpace.proj (a b)
        (mfderiv J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) a b u) = u := by
    rw [← mfderiv_comp_apply b ((Bundle.contMDiff_proj
      (fun x : B ↦ TangentSpace J x →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero) ha,
      (show TotalSpace.proj ∘ a =ᶠ[𝓝 b] id from hproj).mfderiv_eq, mfderiv_id]
    -- `EventuallyEq.mfderiv_eq` composes with `tangentSpaceCast`, the identification of the
    -- tangent spaces at `(a b).proj` and `b`, which is the identity map.
    rfl
  have hab : (a b).proj = b := hproj.self_of_nhds
  have hs'b : h.sectionMap hσc hs (a b) = s' b := heq.self_of_nhds
  have hds' (u : TangentSpace J b) : mfderiv J I s' b u =
      mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) (a b)
        (mfderiv J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) a b u) := by
    rw [← mfderiv_comp_apply b hΦ ha, heq.mfderiv_eq]
    -- `EventuallyEq.mfderiv_eq` composes with `tangentSpaceCast`, the identification of the
    -- tangent spaces at `s' b` and `Φ_s (a b)`, which is the identity map.
    rfl
  rw [hds', hds', ← hs'b, h.eval₂_mfderiv_sectionMap hσc hs hsm, hπa, hπa]
  -- The base point of `a b` is `b`; `v` and `w` are tangent vectors at `b`, so generalize them
  -- before rewriting the base point.
  revert v w
  rw [hab]
  exact fun _ _ ↦ rfl

/-- **The pullback formula**: moving a smooth section `s` by a smooth one-form `α` changes the
pullback of `σ` by `-dα`,

`(Φ_s ∘ α)^* σ = s^* σ - dα`. -/
theorem mpullback_sectionMapGraph (hsm : ContMDiff J I ∞ s) (α : SmoothForm J B ℝ 1) :
    SmoothForm.mpullback (h.sectionMapGraph hσc hs α) (h.contMDiff_sectionMapGraph hσc hs hsm α)
        σ =
      SmoothForm.mpullback s hsm σ - mextDerivₗ J 1 α := by
  -- `Φ_s` pulls `σ` back to the twisted form `ω + π^*(s^* σ)`, which the graph of `α` pulls
  -- back to `s^* σ - dα`.
  have hpull := SmoothForm.mpullback_mpullback
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] ℝ) b (SmoothForm.degreeOneEquiv α b))
    (h.sectionMap hσc hs) (SmoothForm.degreeOneEquiv α).contMDiff
    (h.contMDiff_sectionMap hσc hs hsm) σ
  rw [h.mpullback_sectionMap hσc hs hsm, ← CotangentBundle.twistedSymplecticForm_def,
    CotangentBundle.mpullback_section_twistedSymplecticForm] at hpull
  exact hpull.symm

/-- **The moved section pulls `σ` back to zero exactly when `dα = s^* σ`.** -/
theorem mpullback_sectionMapGraph_eq_zero_iff (hsm : ContMDiff J I ∞ s)
    (α : SmoothForm J B ℝ 1) :
    SmoothForm.mpullback (h.sectionMapGraph hσc hs α) (h.contMDiff_sectionMapGraph hσc hs hsm α)
        σ = 0 ↔
      mextDerivₗ J 1 α = SmoothForm.mpullback s hsm σ := by
  rw [h.mpullback_sectionMapGraph hσc hs hsm, sub_eq_zero, eq_comm]

/-- **The moved section is Lagrangian exactly when `dα = s^* σ`.** -/
theorem isLagrangianMap_sectionMapGraph_iff (hsm : ContMDiff J I ∞ s) (α : SmoothForm J B ℝ 1) :
    hσ.IsLagrangianMap J (h.sectionMapGraph hσc hs α) ↔
      mextDerivₗ J 1 α = SmoothForm.mpullback s hsm σ := by
  rw [h.isLagrangianMap_iff_isIsotropicMap (h.proj_sectionMapGraph hσc hs α)
      ((h.contMDiff_sectionMapGraph hσc hs hsm α).mdifferentiable (by simp)),
    isIsotropicMap_iff_mpullback_eq_zero (h.contMDiff_sectionMapGraph hσc hs hsm α),
    h.mpullback_sectionMapGraph_eq_zero_iff hσc hs hsm]

/-- **Relative to a Lagrangian section, the Lagrangian sections are the closed one-forms.** If the
smooth section `s` pulls `σ` back to zero, then `Φ_s ∘ α` is a Lagrangian map exactly when `α` is
closed. -/
theorem isLagrangianMap_sectionMapGraph_iff_isClosed (hsm : ContMDiff J I ∞ s)
    (hsσ : SmoothForm.mpullback s hsm σ = 0) (α : SmoothForm J B ℝ 1) :
    hσ.IsLagrangianMap J (h.sectionMapGraph hσc hs α) ↔ α.IsClosed := by
  rw [h.isLagrangianMap_sectionMapGraph_iff hσc hs hsm, hsσ,
    SmoothForm.isClosed_iff_mextDerivₗ_eq_zero]

/-! ### Every section is locally moved from `s` -/

/-- **Local sections lift through the section map.** Let `s'` be a smooth section of `π` over an
open set `V`. Near every point of `V` there is a smooth local section `a` of `T*B → B` with
`Φ_s ∘ a = s'`. -/
theorem exists_contMDiffOn_sectionMap_eq (hsm : ContMDiff J I ∞ s) {s' : B → M} {V : Set B}
    (hV : IsOpen V) (hs'm : ContMDiffOn J I ∞ s' V) (hs' : ∀ b ∈ V, π (s' b) = b) {b₀ : B}
    (hb₀ : b₀ ∈ V) :
    ∃ U ⊆ V, IsOpen U ∧ b₀ ∈ U ∧ ∃ a : B → CotangentBundle J B,
      ContMDiffOn J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ a U ∧
        ∀ b ∈ U, (a b).proj = b ∧ h.sectionMap hσc hs (a b) = s' b := by
  obtain ⟨ξ₀, hξ₀⟩ := h.surjective_sectionMap hσc hs (s' b₀)
  -- A local inverse `ψ` of `Φ_s` near `ξ₀`, defined on an open neighbourhood of `s' b₀`.
  have hΦ := h.isLocalDiffeomorph_sectionMap hσc hs hsm ξ₀
  set ψ := hΦ.localInverse
  refine ⟨V ∩ s' ⁻¹' ψ.source, inter_subset_left,
    hs'm.continuousOn.isOpen_inter_preimage hV ψ.open_source,
    ⟨hb₀, mem_preimage.2 (hξ₀ ▸ hΦ.localInverse_mem_source)⟩, ψ ∘ s', ?_, fun b hb ↦ ?_⟩
  · exact hΦ.contMDiffOn_localInverse.comp (hs'm.mono inter_subset_left)
      fun b hb ↦ hb.2
  · have hΦψ : h.sectionMap hσc hs (ψ (s' b)) = s' b := hΦ.localInverse_right_inv hb.2
    refine ⟨?_, hΦψ⟩
    rw [comp_apply, ← h.proj_sectionMap hσc hs (ψ (s' b)), hΦψ, hs' b hb.1]

end IsLagrangianTorusFibration

end TauCeti.SmoothTwoForm.IsNondegenerate
