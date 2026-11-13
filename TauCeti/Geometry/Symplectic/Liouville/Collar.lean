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
public import TauCeti.Topology.MetricSpace.InjectiveNeighborhood
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
* If moreover `ι` is a topological embedding, then `Φ` is injective and a local diffeomorphism
  on a collar `{(t, s) | |t| < ε s}` of `{0} × S` inside `D`, whose width `ε` is a positive
  continuous function on `S` (`TauCeti.exists_continuous_pos_injOn_flowOf_comp`). So `Φ` is a
  diffeomorphism from this collar onto an open neighbourhood of the image of `ι`. No compactness
  of `S` is needed, only that `S` and `M` are pseudometrizable, as second countable Hausdorff
  manifolds are.
* If `S` is compact and `ι` is injective, the width can be taken constant: `Φ` is injective and a
  local diffeomorphism on `(-ε, ε) × S` for some `ε > 0`
  (`TauCeti.exists_pos_injOn_flowOf_comp`).

A hypersurface transverse to the Liouville field of a nondegenerate `dα` carries the contact form
`ι^* α` (`TauCeti.IsContactType.isContactForm_mpullback`), so for such a hypersurface the local
Liouville flow map is a local diffeomorphism on its whole domain
(`TauCeti.isLocalDiffeomorphAt_flowOf_comp_of_isTransverseAlong`). For a complete Liouville field,
the identity `Φ^* α = eᵗ ι^* α` holds on all of `ℝ × S`
(`TauCeti.mpullback_globalFlow_comp_eq_symplectization`).

## Main results

* `TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`: `Φ^* α = eᵗ ι^* α` on `D`.
* `TauCeti.mpullback_flowOf_comp_mextDeriv_apply`: `Φ^* dα = d(eᵗ ι^* α)` on `D`.
* `TauCeti.injective_mfderiv_flowOf_comp`: for a contact form `ι^* α`, `Φ` is an immersion on `D`.
* `TauCeti.isLocalDiffeomorphAt_flowOf_comp`,
  `TauCeti.isLocalDiffeomorphAt_flowOf_comp_of_isTransverseAlong`: for a hypersurface, `Φ` is a
  local diffeomorphism at every point of `D`.
* `TauCeti.exists_continuous_pos_injOn_flowOf_comp`: the collar of variable width of an embedded
  hypersurface.
* `TauCeti.exists_pos_injOn_flowOf_comp`: the collar of uniform width of a compact hypersurface.

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
  filter_upwards [(isOpen_setOf_mem_flowDomain (hZ.of_le (by simp)) continuous_fst
      (hι.continuous.comp continuous_snd)).mem_nhds hp] with q hq
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
    (isOpen_setOf_mem_flowDomain (hZ.of_le (by simp)) continuous_fst
      (hι.continuous.comp continuous_snd)) hp BoundarylessManifold.isInteriorPoint (by simp)
    (e := (LinearMap.linearEquivOfInjective _ hinj hdim').toContinuousLinearEquiv)
    (ContinuousLinearMap.ext fun w ↦ LinearMap.linearEquivOfInjective_apply hinj hdim' w)

/-- **The Liouville collar of a compact hypersurface has uniform width.** Let the smooth vector
field `Z` be the Liouville field of the one-form `α`, `ι_Z dα = α`, and let `ι : S → M` be a smooth
injective map from a compact boundaryless manifold of one dimension less, with `ι^* α` a contact
form. Then for some `ε > 0` the flow `φₜ(ι s)` is defined for `|t| < ε`, and on the collar
`(-ε, ε) × S` the local flow map `(t, s) ↦ φₜ(ι s)` is injective and a local diffeomorphism, that
is, a diffeomorphism onto an open subset of `M`. -/
theorem exists_pos_injOn_flowOf_comp [FiniteDimensional ℝ E'] [J.Boundaryless] [CompactSpace S]
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hZα : (mextDeriv α.1).interior Z = α.1)
    (hα : (SmoothForm.mpullback ι hι α).IsContactForm) (hιi : Function.Injective ι) :
    ∃ ε > 0, Ioo (-ε) ε ×ˢ univ ⊆ {p : ℝ × S | (p.1, ι p.2) ∈ flowDomain Z} ∧
      InjOn (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) (Ioo (-ε) ε ×ˢ univ) ∧
      IsLocalDiffeomorphOn (𝓘(ℝ).prod J) I ∞ (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2))
        (Ioo (-ε) ε ×ˢ univ) := by
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
      simp only [flowOf_zero Z] at hab
      rw [hιi hab])
    (isCompact_singleton.prod isCompact_univ)
    fun p hp ↦ isLocalDiffeomorphAt_flowOf_comp hZ hι hdim hZα hα (hD hp)
  -- By the tube lemma, the open set `U ∩ D` contains a product `u × S` with `u` a neighbourhood
  -- of `0`, and hence a collar of uniform width.
  obtain ⟨u, v, hu, -, h0u, hSv, huv⟩ := generalized_tube_lemma isCompact_singleton isCompact_univ
    (hUo.inter (isOpen_setOf_mem_flowDomain (hZ.of_le (by simp)) continuous_fst
      (hι.continuous.comp continuous_snd))) (subset_inter hsU hD)
  obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.mp hu 0 (h0u rfl)
  have hsub : Ioo (-ε) ε ×ˢ (univ : Set S) ⊆ U ∩ D := fun p hp ↦
    huv ⟨hεu (by simpa [Real.ball_eq_Ioo] using hp.1), hSv (mem_univ _)⟩
  exact ⟨ε, hε, fun p hp ↦ (hsub hp).2, hinj.mono fun p hp ↦ (hsub hp).1,
    fun p ↦ hloc ⟨p, (hsub p.2).1⟩⟩

/-- **The Liouville collar of a noncompact hypersurface.** Let the smooth vector field `Z` be the
Liouville field of the one-form `α`, `ι_Z dα = α`, and let `ι : S → M` be a smooth topological
embedding of a boundaryless manifold of one dimension less, with `ι^* α` a contact form. Then for
some positive continuous width `ε : S → ℝ` the flow `φₜ(ι s)` is defined for `|t| < ε s`, and on
the collar `{(t, s) | |t| < ε s}` of `{0} × S` the local flow map `(t, s) ↦ φₜ(ι s)` is injective
and a local diffeomorphism, that is, a diffeomorphism onto an open subset of `M`.

No compactness of `S` is needed. The embedding hypothesis is necessary: the collar map is a
homeomorphism onto its open image and restricts to `ι` on `{0} × S`. -/
theorem exists_continuous_pos_injOn_flowOf_comp [FiniteDimensional ℝ E'] [J.Boundaryless]
    [TopologicalSpace.PseudoMetrizableSpace M] [TopologicalSpace.PseudoMetrizableSpace S]
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hZα : (mextDeriv α.1).interior Z = α.1)
    (hα : (SmoothForm.mpullback ι hι α).IsContactForm) (hιe : Topology.IsInducing ι) :
    ∃ ε : C(S, ℝ), (∀ s, 0 < ε s) ∧
      {p : ℝ × S | |p.1| < ε p.2} ⊆ {p : ℝ × S | (p.1, ι p.2) ∈ flowDomain Z} ∧
      InjOn (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) {p : ℝ × S | |p.1| < ε p.2} ∧
      IsLocalDiffeomorphOn (𝓘(ℝ).prod J) I ∞ (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2))
        {p : ℝ × S | |p.1| < ε p.2} := by
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := hZ.of_le (by simp)
  set D := {p : ℝ × S | (p.1, ι p.2) ∈ flowDomain Z}
  have hloc : IsLocalDiffeomorphOn (𝓘(ℝ).prod J) I ∞ (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) D :=
    fun p ↦ isLocalDiffeomorphAt_flowOf_comp hZ hι hdim hZα hα p.2
  -- The section `s ↦ (0, s)` is mapped to `ι`, which induces the topology of `S`; so the flow map
  -- is an open embedding on an open neighbourhood `U ⊆ D` of `{0} × S`.
  obtain ⟨U, hUo, hsU, hUD, hemb⟩ :=
    hloc.isLocalHomeomorphOn.exists_isOpenEmbedding_near_section
      (isOpen_setOf_mem_flowDomain (hZ.of_le (by simp)) continuous_fst
        (hι.continuous.comp continuous_snd)) (s := fun y : S ↦ ((0 : ℝ), y))
      (by
        rintro _ ⟨y, rfl⟩
        exact mem_flowDomain_zero hZ1 (ι y))
      (continuous_const.prodMk continuous_id) Prod.snd continuous_snd (fun _ ↦ rfl)
      (by simpa only [Function.comp_def, flowOf_zero] using hιe)
  -- A pseudometrizable space is normal and paracompact, so `U` contains a tube of positive
  -- continuous width.
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric S
  obtain ⟨ε, hε, hεU⟩ := hUo.exists_continuous_pos_forall_abs_lt fun y ↦ hsU ⟨y, rfl⟩
  have hsub : {p : ℝ × S | |p.1| < ε p.2} ⊆ U := fun p hp ↦ hεU p.2 p.1 hp
  refine ⟨ε, hε, hsub.trans hUD, fun p hp q hq hpq ↦ ?_, fun p ↦ hloc ⟨p, hUD (hsub p.2)⟩⟩
  exact congrArg Subtype.val
    (hemb.injective (a₁ := ⟨p, hsub hp⟩) (a₂ := ⟨q, hsub hq⟩) hpq)

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
