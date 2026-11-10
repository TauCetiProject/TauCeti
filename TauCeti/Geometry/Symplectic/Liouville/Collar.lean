/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Basic
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Liouville.ContactType
public import TauCeti.Geometry.Symplectic.Liouville.Scaling
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The local Liouville flow out of a hypersurface

Let `Z` be a smooth vector field on a manifold `M` which is the Liouville field of a one-form `α`,
`ι_Z dα = α`, and let `ι : S → M` be a smooth map, typically the inclusion of a hypersurface. No
completeness of `Z` is assumed. The **local Liouville flow map** is `Φ(t, s) = φₜ(ι s)`, where `φ`
is the maximal flow of `Z` (`TauCeti.flowOf`). It is defined on the open set
`D = {(t, s) | φₜ(ι s) is defined}` of `ℝ × S`, which contains `{0} × S`; its slice over each `s`
is an open interval around `0` whose length varies with `s`. On this domain:

* `Φ` pulls `α` back to the symplectization form `eᵗ ι^* α`
  (`TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`), and `dα` back to `d(eᵗ ι^* α)`
  (`TauCeti.mpullback_flowOf_comp_mextDeriv_apply`). In the convention `ω = -dλ` of an exact
  symplectic manifold, whose Liouville field satisfies `ι_Z ω = -λ`, this says
  `Φ^*(-λ) = eᵗ (-λ)|_S` and `Φ^* ω = d(eᵗ (-λ)|_S)`, taking `α = -λ`.
* If `ι^* α` is a contact form, then `Φ` pulls `dα` back to the symplectic form `d(eᵗ ι^* α)`, so
  its differential is injective at every point of `D` (`TauCeti.injective_mfderiv_flowOf_comp`).
  When `S` has one dimension less than `M`, `Φ` is therefore a local diffeomorphism at every point
  of `D` (`TauCeti.isLocalDiffeomorphAt_flowOf_comp`).
* If moreover `S` is compact and `ι` is injective, then `Φ` is injective and a local
  diffeomorphism on an open neighbourhood of `{0} × S` in `D`
  (`TauCeti.exists_isOpen_injOn_flowOf_comp`): it is a diffeomorphism from a collar of
  `{0} × S` onto an open neighbourhood of the image of `ι`.

A hypersurface transverse to the Liouville field of a nondegenerate `dα` carries the contact form
`ι^* α` (`TauCeti.IsContactType.isContactForm_mpullback`), so for such a hypersurface the local
Liouville flow map is a local diffeomorphism on its whole domain
(`TauCeti.isLocalDiffeomorphAt_flowOf_comp_of_isTransverseAlong`). For a complete Liouville field,
the identity `Φ^* α = eᵗ ι^* α` holds on all of `ℝ × S`
(`TauCeti.mpullback_globalFlow_comp_eq_symplectization`). Injectivity near `{0} × S` for a
noncompact embedded hypersurface is not treated here.

## Main results

* `TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`: `Φ^* α = eᵗ ι^* α` on `D`.
* `TauCeti.mpullback_flowOf_comp_mextDeriv_apply`: `Φ^* dα = d(eᵗ ι^* α)` on `D`.
* `TauCeti.injective_mfderiv_flowOf_comp`: for a contact form `ι^* α`, `Φ` is an immersion on `D`.
* `TauCeti.isLocalDiffeomorphAt_flowOf_comp`,
  `TauCeti.isLocalDiffeomorphAt_flowOf_comp_of_isTransverseAlong`: for a hypersurface, `Φ` is a
  local diffeomorphism at every point of `D`.
* `TauCeti.exists_isOpen_injOn_flowOf_comp`: the collar of a compact hypersurface.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.4 (hypersurfaces of contact type).
-/

public section

open Set Bundle Filter Module
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {Z : (x : M) → TangentSpace I x}
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  (hZ : ContMDiff I I.tangent ∞ (T% Z)) {ι : S → M} (hι : ContMDiff J I ∞ ι)
include hZ hι

/-- The domain `{(t, s) | φₜ(ι s) is defined}` of the local Liouville flow map is open. -/
private theorem isOpen_setOf_mem_flowDomain_comp :
    IsOpen {p : ℝ × S | (p.1, ι p.2) ∈ flowDomain Z} :=
  (isOpen_flowDomain (hZ.of_le (by simp))).preimage
    (continuous_fst.prodMk (hι.continuous.comp continuous_snd))

/-- The local flow map `(t, s) ↦ φₜ(ι s)` is smooth near every point of its domain. -/
private theorem contMDiffAt_flowOf_comp_uncurry {p : ℝ × S} (hp : (p.1, ι p.2) ∈ flowDomain Z) :
    ContMDiffAt (𝓘(ℝ).prod J) I ∞ (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) p :=
  contMDiffAt_flowOf_comp le_top hZ contMDiffAt_fst (hι.contMDiffAt.comp p contMDiffAt_snd) hp

variable [IsManifold J ∞ S] {α : SmoothForm I M ℝ 1}

/-- **The local Liouville flow map pulls the primitive back to the symplectization form.** Let the
smooth vector field `Z` be the Liouville field of the one-form `α`, `ι_Z dα = α`, and let
`ι : S → M` be smooth. At every point of its domain, the local flow map `(t, s) ↦ φₜ(ι s)` pulls `α`
back to the symplectization form `eᵗ ι^* α` of the restricted form. -/
theorem mpullback_flowOf_comp_apply_eq_symplectization (hZα : (mextDeriv α.1).interior Z = α.1)
    {p : ℝ × S} (hp : (p.1, ι p.2) ∈ flowDomain Z) :
    mpullback (𝓘(ℝ).prod J) I (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) α.1 p =
      (SmoothForm.mpullback ι hι α).symplectization.1 p := by
  -- The local flow rescales the primitive: `(φₜ^* α)_x = eᵗ α_x`.
  have hscale := mpullback_flowOf_apply_eq_exp_smul_of_interior_eq (hZ.of_le (by simp))
    α.mdifferentiable rfl hZα hp
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  have hs := congrArg (fun β ↦ β ![mfderiv J I ι p.2 w.2]) hscale
  simp only [mpullback_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    Matrix.cons_val_fin_one, ← Matrix.vec_single_eq_const] at hs
  -- Differentiate the flow map, then use that `α` is linear and vanishes on `Z`.
  rw [mpullback_apply, SmoothForm.symplectization_apply, SmoothForm.mpullback_apply]
  simp only [Matrix.cons_val_fin_one, ← Matrix.vec_single_eq_const,
    mfderiv_flowOf_comp_apply (hZ.of_le (by simp)) (hι.contMDiffAt.of_le (by simp)) hp,
    ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_smul,
    RoughForm.apply_eq_zero_of_interior_eq hZα, smul_zero, zero_add,
    Manifold.tangentSpaceProdEquiv_apply, hs]

/-- **The local Liouville flow map pulls `dα` back to `d(eᵗ ι^* α)`.** Let the smooth vector field
`Z` be the Liouville field of the one-form `α`, `ι_Z dα = α`, and let `ι : S → M` be smooth. At
every point of its domain, the local flow map `(t, s) ↦ φₜ(ι s)` pulls `dα` back to the exterior
derivative of the symplectization form `eᵗ ι^* α`. -/
theorem mpullback_flowOf_comp_mextDeriv_apply (hZα : (mextDeriv α.1).interior Z = α.1)
    {p : ℝ × S} (hp : (p.1, ι p.2) ∈ flowDomain Z) :
    mpullback (𝓘(ℝ).prod J) I (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) (mextDeriv α.1) p =
      mextDeriv (SmoothForm.mpullback ι hι α).symplectization.1 p := by
  rw [mpullback_mextDeriv_at ((contMDiffAt_flowOf_comp_uncurry hZ hι hp).of_le (by simp))
    ((α.contMDiff _).of_le (by simp))]
  -- The two one-forms agree on the open domain of the flow map, a neighbourhood of `p`.
  refine mextDeriv_congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_setOf_mem_flowDomain_comp hZ hι).mem_nhds hp] with q hq
  exact mpullback_flowOf_comp_apply_eq_symplectization hZ hι hZα hq

/-- **The local Liouville flow map is an immersion.** Let the smooth vector field `Z` be the
Liouville field of the one-form `α`, `ι_Z dα = α`, and let `ι : S → M` be smooth with `ι^* α` a
contact form. Then the local flow map `(t, s) ↦ φₜ(ι s)` has injective differential at every point
of its domain, since it pulls `dα` back to the symplectic form `d(eᵗ ι^* α)`. -/
theorem injective_mfderiv_flowOf_comp (hZα : (mextDeriv α.1).interior Z = α.1)
    (hα : (SmoothForm.mpullback ι hι α).IsContactForm) {p : ℝ × S}
    (hp : (p.1, ι p.2) ∈ flowDomain Z) :
    Function.Injective (mfderiv (𝓘(ℝ).prod J) I (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) p) := by
  have hnd := SmoothTwoForm.isNondegenerate_iff_separatingLeft.1
    (SmoothForm.isNondegenerate_mextDerivₗ_symplectization_iff.2 hα) p
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ hnd v fun w ↦ ?_
  rw [SmoothBundleForm.eval₂_apply, mextDerivₗ_apply,
    ← mpullback_flowOf_comp_mextDeriv_apply hZ hι hZα hp, mpullback_apply_pair, hv]
  exact (mextDeriv α.1 _).map_coord_zero 0 rfl

/-- **The local Liouville flow map is a local diffeomorphism.** Let the smooth vector field `Z` be
the Liouville field of the one-form `α`, `ι_Z dα = α`, and let `ι : S → M` be smooth from a
boundaryless manifold of one dimension less, with `ι^* α` a contact form. Then the local flow map
`(t, s) ↦ φₜ(ι s)` is a local diffeomorphism at every point of its domain. -/
theorem isLocalDiffeomorphAt_flowOf_comp [FiniteDimensional ℝ E'] [J.Boundaryless]
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hZα : (mextDeriv α.1).interior Z = α.1)
    (hα : (SmoothForm.mpullback ι hι α).IsContactForm) {p : ℝ × S}
    (hp : (p.1, ι p.2) ∈ flowDomain Z) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod J) I ∞ (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) p := by
  have hdim' : finrank ℝ (TangentSpace (𝓘(ℝ).prod J) p) = finrank ℝ (TangentSpace I
      (flowOf Z p.1 (ι p.2))) := by
    -- The tangent spaces are the model spaces `ℝ × E'` and `E`.
    change finrank ℝ (ℝ × E') = finrank ℝ E
    rw [← hdim, Module.finrank_prod, Module.finrank_self, add_comm]
  have hinj := injective_mfderiv_flowOf_comp hZ hι hZα hα hp
  exact isLocalDiffeomorphAt_of_mfderiv_eq
    (fun q hq ↦ (contMDiffAt_flowOf_comp_uncurry hZ hι hq).contMDiffWithinAt)
    (isOpen_setOf_mem_flowDomain_comp hZ hι) hp BoundarylessManifold.isInteriorPoint (by simp)
    (e := (LinearMap.linearEquivOfInjective _ hinj hdim').toContinuousLinearEquiv)
    (ContinuousLinearMap.ext fun w ↦ LinearMap.linearEquivOfInjective_apply hinj hdim' w)

/-- **The Liouville collar of a compact hypersurface.** Let the smooth vector field `Z` be the
Liouville field of the one-form `α`, `ι_Z dα = α`, and let `ι : S → M` be a smooth injective map
from a compact boundaryless manifold of one dimension less, with `ι^* α` a contact form. Then on
some open neighbourhood `U` of `{0} × S`, contained in the domain of the flow, the local flow map
`(t, s) ↦ φₜ(ι s)` is injective and a local diffeomorphism, that is, a diffeomorphism of `U` onto
an open subset of `M`. -/
theorem exists_isOpen_injOn_flowOf_comp [FiniteDimensional ℝ E'] [J.Boundaryless] [CompactSpace S]
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hZα : (mextDeriv α.1).interior Z = α.1)
    (hα : (SmoothForm.mpullback ι hι α).IsContactForm) (hιi : Function.Injective ι) :
    ∃ U : Set (ℝ × S), IsOpen U ∧ {0} ×ˢ univ ⊆ U ∧ U ⊆ {p | (p.1, ι p.2) ∈ flowDomain Z} ∧
      InjOn (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) U ∧
      IsLocalDiffeomorphOn (𝓘(ℝ).prod J) I ∞ (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) U := by
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := hZ.of_le (by simp)
  set D := {p : ℝ × S | (p.1, ι p.2) ∈ flowDomain Z}
  have hD : ({0} : Set ℝ) ×ˢ (univ : Set S) ⊆ D := by
    rintro ⟨t, y⟩ ⟨rfl, -⟩
    exact mem_flowDomain_zero hZ1 (ι y)
  -- On `{0} × S` the flow map is `ι`, so it is injective there.
  obtain ⟨U, hUo, hsU, hinj, hloc⟩ := Set.InjOn.exists_isOpen_superset_isLocalDiffeomorphOn
    (f := fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2))
    (by
      rintro ⟨_, a⟩ ⟨rfl, -⟩ ⟨_, b⟩ ⟨rfl, -⟩ hab
      simp only [flowOf_zero hZ1] at hab
      rw [hιi hab])
    (isCompact_singleton.prod isCompact_univ)
    fun p hp ↦ isLocalDiffeomorphAt_flowOf_comp hZ hι hdim hZα hα (hD hp)
  exact ⟨U ∩ D, hUo.inter (isOpen_setOf_mem_flowDomain_comp hZ hι), subset_inter hsU hD,
    inter_subset_right, hinj.mono inter_subset_left, fun p ↦ hloc ⟨p, p.2.1⟩⟩

/-- **The Liouville collar of a transverse hypersurface is locally diffeomorphic.** Let the smooth
vector field `Z` be the Liouville field of the one-form `α`, `ι_Z dα = α`, with `dα`
nondegenerate, and let `ι : S → M` be a smooth immersion of a boundaryless manifold of one dimension
less, to which `Z` is transverse. Then `ι^* α` is a contact form, and the local flow map
`(t, s) ↦ φₜ(ι s)` is a local diffeomorphism at every point of its domain. -/
theorem isLocalDiffeomorphAt_flowOf_comp_of_isTransverseAlong [FiniteDimensional ℝ E']
    [J.Boundaryless] (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hσ : SmoothTwoForm.IsNondegenerate (mextDerivₗ I 1 α)) (hZα : (mextDeriv α.1).interior Z = α.1)
    (hιs : ∀ s, Function.Injective (mfderiv J I ι s)) (hZι : IsTransverseAlong J Z ι)
    {p : ℝ × S} (hp : (p.1, ι p.2) ∈ flowDomain Z) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod J) I ∞ (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) p := by
  have hct : IsContactType J (mextDerivₗ I 1 α).1 α.1 ι := isContactType_iff.2
    ⟨univ, isOpen_univ, subset_univ _, fun _ _ ↦ by rw [mextDerivₗ_apply], Z, hZ.contMDiffOn,
      fun x _ ↦ by rw [mextDerivₗ_apply, hZα], hZι⟩
  exact isLocalDiffeomorphAt_flowOf_comp hZ hι hdim hZα
    (hct.isContactForm_mpullback hσ hι hιs hdim) hp

end TauCeti
