/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The local Reeb flow out of a transverse slice

Let `α` be a one-form on a manifold `M` and `Z` a smooth vector field with `α(Z) = 1` and
`ι_Z dα = 0`; for a contact form, `Z` is the Reeb vector field `R_α`. Let `ι : S → M` be a smooth
map, typically the inclusion of a hypersurface. No completeness of `Z` is assumed. The **local
Reeb flow map** is `Φ(s, t) = φₜ(ι s)`, where `φ` is the maximal flow of `Z` (`TauCeti.flowOf`). It
is defined on the open set `D = {(s, t) | φₜ(ι s) is defined}` of `S × ℝ`, which contains `S × {0}`.
On this domain:

* `Φ` pulls `α` back to the form `dt + ι^* α` of `S × ℝ`
  (`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`), which is the contactization form
  `TauCeti.SmoothForm.contactization` of `-ι^* α`, and `dα` back to its exterior derivative, the
  pullback of `d(ι^* α)` along the projection to `S`
  (`TauCeti.mpullback_flowOf_comp_mextDeriv_apply_eq_mextDeriv_contactization`). Indeed the flow
  of `Z` preserves `α`, by Cartan's formula `L_Z α = ι_Z dα + d(α(Z)) = 0`
  (`TauCeti.mpullback_flowOf_apply_of_interior_mextDeriv_eq_zero`), and `Φ` carries `∂_t` to `Z`.
* At a point `(s, t)` of `D` where `d(ι^* α)` is nondegenerate on `T_s S`, the differential of
  `Φ` is injective (`TauCeti.injective_mfderiv_flowOf_comp_of_nondegenerate`). When `S` has one
  dimension less than `M`, `Φ` is then a local diffeomorphism at `(s, t)`
  (`TauCeti.isLocalDiffeomorphAt_flowOf_comp_of_nondegenerate`). Near such a point, `α` therefore
  takes the normal form `dt + β` in coordinates `(s, t)`, with `β = ι^* α` a one-form on `S` whose
  exterior derivative is nondegenerate.
* For a contact form, the nondegeneracy of `d(ι^* α)` at `s` is transversality: if `ι` has
  injective differential at `s` and the Reeb vector at `ι s` is not tangent to the image, then
  `d(ι^* α)` is nondegenerate on `T_s S`
  (`TauCeti.SmoothForm.IsContactForm.nondegenerate_bilinFormAt_mextDerivₗ_mpullback`). So the local
  Reeb flow map out of a hypersurface transverse to `R_α` is a local diffeomorphism at every point
  of `D` (`TauCeti.SmoothForm.IsContactForm.isLocalDiffeomorphAt_flowOf_reebVectorField_comp`).

This Reeb normal form `α = dt + β` reduces Darboux's theorem for a contact form to Darboux's
theorem for the symplectic form `dβ` on the slice: once `dβ` is standard, `β` differs from a
standard primitive by an exact form on a ball, which is absorbed into `t`.

## Main results

* `TauCeti.mpullback_flowOf_comp_apply_eq_contactization`: `Φ^* α = dt + ι^* α` on `D`.
* `TauCeti.mpullback_flowOf_comp_mextDeriv_apply_eq_mextDeriv_contactization`:
  `Φ^* dα = d(dt + ι^* α)`.
* `TauCeti.injective_mfderiv_flowOf_comp_of_nondegenerate`,
  `TauCeti.isLocalDiffeomorphAt_flowOf_comp_of_nondegenerate`: `Φ` is an immersion, and for a
  hypersurface a local diffeomorphism, wherever `d(ι^* α)` is nondegenerate.
* `TauCeti.SmoothForm.IsContactForm.nondegenerate_bilinFormAt_mextDerivₗ_mpullback`: on a
  hypersurface transverse to the Reeb vector field, `d(ι^* α)` is nondegenerate.
* `TauCeti.SmoothForm.IsContactForm.isLocalDiffeomorphAt_flowOf_reebVectorField_comp`: the local
  Reeb flow map out of a transverse hypersurface is a local diffeomorphism.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 (the Reeb vector field) and Section 2.5 (Darboux's theorem).
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

/-- The domain `{(s, t) | φₜ(ι s) is defined}` of the local Reeb flow map is open. -/
private theorem isOpen_setOf_mem_flowDomain_comp_fst :
    IsOpen {p : S × ℝ | (p.2, ι p.1) ∈ flowDomain Z} :=
  (isOpen_flowDomain (hZ.of_le (by simp))).preimage
    (continuous_snd.prodMk (hι.continuous.comp continuous_fst))

/-- The local flow map `(s, t) ↦ φₜ(ι s)` is smooth near every point of its domain. -/
private theorem contMDiffAt_flowOf_comp_fst {p : S × ℝ} (hp : (p.2, ι p.1) ∈ flowDomain Z) :
    ContMDiffAt (J.prod 𝓘(ℝ)) I ∞ (fun q : S × ℝ ↦ flowOf Z q.2 (ι q.1)) p :=
  contMDiffAt_flowOf_comp le_top hZ contMDiffAt_snd (hι.contMDiffAt.comp p contMDiffAt_fst) hp

/-- The differential of the local flow map `(s, t) ↦ φₜ(ι s)` sends a tangent vector `(w, r)` to
`dφₜ(dι w) + r Z`. This is `TauCeti.mfderiv_flowOf_comp_apply` with the factors of the product
exchanged, so that the real coordinate comes last as in the contactization. -/
private theorem mfderiv_flowOf_comp_fst_apply {p : S × ℝ} (hp : (p.2, ι p.1) ∈ flowDomain Z)
    (v : TangentSpace (J.prod 𝓘(ℝ)) p) :
    mfderiv (J.prod 𝓘(ℝ)) I (fun q : S × ℝ ↦ flowOf Z q.2 (ι q.1)) p v =
      mfderiv I I (flowOf Z p.2) (ι p.1) (mfderiv J I ι p.1 v.1) +
        v.2 • Z (flowOf Z p.2 (ι p.1)) := by
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := hZ.of_le (by simp)
  have hflow : MDifferentiableAt I I (flowOf Z p.2) (ι p.1) :=
    (contMDiffAt_flowOf_comp le_rfl hZ1 contMDiffAt_const contMDiffAt_id hp).mdifferentiableAt
      one_ne_zero
  have hcomp : mfderiv J I (flowOf Z p.2 ∘ ι) p.1 =
      (mfderiv I I (flowOf Z p.2) (ι p.1)).comp (mfderiv J I ι p.1) :=
    mfderiv_comp p.1 hflow ((hι p.1).mdifferentiableAt (by simp))
  refine (mfderiv_prod_eq_add_apply
    ((contMDiffAt_flowOf_comp_fst hZ hι hp).mdifferentiableAt (by simp))).trans ?_
  -- The trajectory through `ι s` has velocity `Z` at time `t`.
  rw [mfderiv_flowOf_trajectory_apply hZ1 hp]
  exact congrArg₂ (· + ·) (DFunLike.congr_fun hcomp v.1) rfl

variable [IsManifold J ∞ S] {α : SmoothForm I M ℝ 1}

/-- **The local Reeb flow map pulls the form back to the contactization form.** Let the smooth
vector field `Z` satisfy `α(Z) = 1` and `ι_Z dα = 0`, as the Reeb vector field of a contact form
does, and let `ι : S → M` be smooth. At every point of its domain, the local flow map
`(s, t) ↦ φₜ(ι s)` pulls `α` back to `dt + ι^* α`, the contactization form of `-ι^* α`. -/
theorem mpullback_flowOf_comp_apply_eq_contactization (hαZ : ∀ x, α.1 x ![Z x] = 1)
    (hZα : (mextDeriv α.1).interior Z = 0) {p : S × ℝ} (hp : (p.2, ι p.1) ∈ flowDomain Z) :
    mpullback (J.prod 𝓘(ℝ)) I (fun q : S × ℝ ↦ flowOf Z q.2 (ι q.1)) α.1 p =
      (-SmoothForm.mpullback ι hι α).contactization.1 p := by
  -- The local flow preserves the form: `(φₜ^* α)_x = α_x`.
  have hinv := mpullback_flowOf_apply_of_interior_mextDeriv_eq_zero (hZ.of_le (by simp)) hαZ hZα hp
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  have hs := congrArg (fun β ↦ β ![mfderiv J I ι p.1 w.1]) hinv
  simp only [mpullback_apply, Matrix.cons_val_fin_one, ← Matrix.vec_single_eq_const] at hs
  -- Differentiate the flow map, then use that `α` is linear and takes the value `1` on `Z`.
  rw [mpullback_apply, SmoothForm.contactization_apply]
  simp only [Matrix.cons_val_fin_one, ← Matrix.vec_single_eq_const,
    mfderiv_flowOf_comp_fst_apply hZ hι hp, ContinuousAlternatingMap.vecCons_add,
    ContinuousAlternatingMap.vecCons_smul, hαZ, hs, Manifold.tangentSpaceProdEquiv_apply,
    NormedSpace.fromTangentSpace_apply, Submodule.coe_neg, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, SmoothForm.mpullback_apply, smul_eq_mul, mul_one]
  ring

/-- **The local Reeb flow map pulls `dα` back to the derivative of the contactization form.** Let
the smooth vector field `Z` satisfy `α(Z) = 1` and `ι_Z dα = 0`, and let `ι : S → M` be smooth. At
every point of its domain, the local flow map `(s, t) ↦ φₜ(ι s)` pulls `dα` back to the exterior
derivative of `dt + ι^* α`, which is `d(ι^* α)` on the components in `S`
(`TauCeti.SmoothForm.mextDeriv_contactization_apply`). -/
theorem mpullback_flowOf_comp_mextDeriv_apply_eq_mextDeriv_contactization
    (hαZ : ∀ x, α.1 x ![Z x] = 1) (hZα : (mextDeriv α.1).interior Z = 0) {p : S × ℝ}
    (hp : (p.2, ι p.1) ∈ flowDomain Z) :
    mpullback (J.prod 𝓘(ℝ)) I (fun q : S × ℝ ↦ flowOf Z q.2 (ι q.1)) (mextDeriv α.1) p =
      mextDeriv (-SmoothForm.mpullback ι hι α).contactization.1 p := by
  rw [mpullback_mextDeriv_at ((contMDiffAt_flowOf_comp_fst hZ hι hp).of_le (by simp))
    ((α.contMDiff _).of_le (by simp))]
  -- The two one-forms agree on the open domain of the flow map, a neighbourhood of `p`.
  refine mextDeriv_congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_setOf_mem_flowDomain_comp_fst hZ hι).mem_nhds hp] with q hq
  exact mpullback_flowOf_comp_apply_eq_contactization hZ hι hαZ hZα hq

/-- **The local Reeb flow map is an immersion over a symplectic slice.** Let the smooth vector
field `Z` satisfy `α(Z) = 1` and `ι_Z dα = 0`, and let `ι : S → M` be smooth. At a point `(s, t)` of
its domain at which `d(ι^* α)` is nondegenerate on `T_s S`, the local flow map
`(s, t) ↦ φₜ(ι s)` has injective differential. -/
theorem injective_mfderiv_flowOf_comp_of_nondegenerate (hαZ : ∀ x, α.1 x ![Z x] = 1)
    (hZα : (mextDeriv α.1).interior Z = 0) {p : S × ℝ}
    (hβ : ((mextDerivₗ J 1 (SmoothForm.mpullback ι hι α)).bilinFormAt p.1).Nondegenerate)
    (hp : (p.2, ι p.1) ∈ flowDomain Z) :
    Function.Injective (mfderiv (J.prod 𝓘(ℝ)) I (fun q : S × ℝ ↦ flowOf Z q.2 (ι q.1)) p) := by
  set β := SmoothForm.mpullback ι hι α
  set e := Manifold.tangentSpaceProdEquiv (I := J) (J := 𝓘(ℝ)) p
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  -- A vector killed by `dΦ` is killed by `Φ^* α = dt + β` and is `Φ^* dα`-orthogonal to everything.
  have hα0 : (-β).contactization.1 p ![v] = 0 := by
    rw [← mpullback_flowOf_comp_apply_eq_contactization hZ hι hαZ hZα hp, mpullback_apply]
    simpa [hv] using (α.1 _).map_coord_zero 0 rfl
  have hd0 (u : TangentSpace (J.prod 𝓘(ℝ)) p) :
      mextDeriv (-β).contactization.1 p ![v, u] = 0 := by
    rw [← mpullback_flowOf_comp_mextDeriv_apply_eq_mextDeriv_contactization hZ hι hαZ hZα hp,
      mpullback_apply_pair, hv]
    exact (mextDeriv α.1 _).map_coord_zero 0 rfl
  -- The `S`-component is in the kernel of `dβ`, tested against the vectors `(w, 0)`.
  have h₁ : (e v).1 = 0 := hβ.1 _ fun w ↦ by
    have := hd0 (e.symm (w, 0))
    rw [SmoothForm.mextDeriv_contactization_apply, map_neg, neg_neg,
      ContinuousLinearEquiv.apply_symm_apply] at this
    rwa [SmoothForm.bilinFormAt_apply]
  -- Its real component is then `dt` of `v`, which vanishes.
  have h₂ : (e v).2 = 0 := by
    rw [SmoothForm.contactization_apply, h₁, ((-β).1 p.1).map_coord_zero 0 rfl, sub_zero] at hα0
    exact (NormedSpace.fromTangentSpace p.2).map_eq_zero_iff.1 hα0
  exact e.injective (by rw [map_zero]; exact Prod.ext h₁ h₂)

/-- **The local Reeb flow map is a local diffeomorphism over a symplectic slice.** Let the smooth
vector field `Z` satisfy `α(Z) = 1` and `ι_Z dα = 0`, and let `ι : S → M` be smooth from a
boundaryless manifold of one dimension less. At a point `(s, t)` of its domain at which `d(ι^* α)`
is nondegenerate on `T_s S`, the local flow map `(s, t) ↦ φₜ(ι s)` is a local diffeomorphism. -/
theorem isLocalDiffeomorphAt_flowOf_comp_of_nondegenerate [FiniteDimensional ℝ E']
    [J.Boundaryless] (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hαZ : ∀ x, α.1 x ![Z x] = 1)
    (hZα : (mextDeriv α.1).interior Z = 0) {p : S × ℝ}
    (hβ : ((mextDerivₗ J 1 (SmoothForm.mpullback ι hι α)).bilinFormAt p.1).Nondegenerate)
    (hp : (p.2, ι p.1) ∈ flowDomain Z) :
    IsLocalDiffeomorphAt (J.prod 𝓘(ℝ)) I ∞ (fun q : S × ℝ ↦ flowOf Z q.2 (ι q.1)) p := by
  have hdim' : finrank ℝ (TangentSpace (J.prod 𝓘(ℝ)) p) = finrank ℝ (TangentSpace I
      (flowOf Z p.2 (ι p.1))) := by
    -- The tangent spaces are the model spaces `E' × ℝ` and `E`.
    change finrank ℝ (E' × ℝ) = finrank ℝ E
    rw [← hdim, Module.finrank_prod, Module.finrank_self]
  have hinj := injective_mfderiv_flowOf_comp_of_nondegenerate hZ hι hαZ hZα hβ hp
  exact isLocalDiffeomorphAt_of_mfderiv_eq
    (fun q hq ↦ (contMDiffAt_flowOf_comp_fst hZ hι hq).contMDiffWithinAt)
    (isOpen_setOf_mem_flowDomain_comp_fst hZ hι) hp BoundarylessManifold.isInteriorPoint (by simp)
    (e := (LinearMap.linearEquivOfInjective _ hinj hdim').toContinuousLinearEquiv)
    (ContinuousLinearMap.ext fun w ↦ LinearMap.linearEquivOfInjective_apply hinj hdim' w)

/-! ### Hypersurfaces transverse to the Reeb vector field -/

namespace SmoothForm

omit hZ

omit [I.Boundaryless] [T2Space M] in
/-- **A hypersurface transverse to the Reeb vector field is a symplectic slice.** Let `α` be a
contact form and let `ι : S → M` be smooth from a manifold of one dimension less, with injective
differential at `s` whose image does not contain the Reeb vector `R_α(ι s)`. Then `d(ι^* α)` is
nondegenerate on `T_s S`. -/
theorem IsContactForm.nondegenerate_bilinFormAt_mextDerivₗ_mpullback (hα : α.IsContactForm)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) {s : S} (hιs : Function.Injective (mfderiv J I ι s))
    (hR : α.reebVectorField (ι s) ∉ (mfderiv J I ι s).range) :
    ((mextDerivₗ J 1 (mpullback ι hι α)).bilinFormAt s).Nondegenerate := by
  set L : TangentSpace J s →ₗ[ℝ] TangentSpace I (ι s) := (mfderiv J I ι s).toLinearMap
  set R := α.reebVectorField (ι s)
  set B := (mextDerivₗ I 1 α).bilinFormAt (ι s)
  have : FiniteDimensional ℝ (TangentSpace J s) := Module.Finite.of_injective L hιs
  -- The tangent space at `ι s` is the image of `dι` plus the Reeb line.
  have hLR : LinearMap.range L ⊔ ℝ ∙ R = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Submodule.finrank_sup_span_singleton hR, LinearMap.finrank_range_of_inj hιs]
    exact hdim
  -- `d(ι^* α)` is `dα` on the images under `dι`.
  have hpull (u w : TangentSpace J s) :
      (mextDerivₗ J 1 (mpullback ι hι α)).bilinFormAt s u w = B (L u) (L w) := by
    rw [bilinFormAt_apply, mextDerivₗ_mpullback, eval₂_mpullback, ← bilinFormAt_apply]
    -- `L` is the differential of `ι` viewed as a linear map.
    rfl
  rw [LinearMap.BilinForm.Nondegenerate,
    (isAlt_bilinFormAt _ s).isRefl.nondegenerate_iff_separatingLeft]
  intro w hw
  -- The vector `dι w` is `dα`-orthogonal to the image of `dι` and to the Reeb line, hence to all
  -- tangent vectors.
  have hker (y : TangentSpace I (ι s)) : B (L w) y = 0 := by
    have hy : y ∈ LinearMap.range L ⊔ ℝ ∙ R := hLR ▸ Submodule.mem_top
    obtain ⟨a, ⟨w', rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    have hRB : B (L w) R = 0 := by
      rw [← mextDeriv_eq_bilinFormAt]
      exact hα.mextDeriv_reebVectorField_right _ _
    rw [map_add, map_smul, hRB, smul_zero, add_zero, ← hpull]
    exact hw w'
  -- A vector in the kernel of `dα` is a multiple of the Reeb vector, which is not in the image of
  -- `dι`; so `dι w = 0`.
  have hu : L w = 0 := by
    by_cases ha : α.1 (ι s) ![L w] = 0
    · refine (isContactForm_iff.1 hα (ι s)).2 _ ha fun y _ ↦ ?_
      rw [mextDeriv_eq_bilinFormAt]
      exact hker y
    · refine absurd ⟨(α.1 (ι s) ![L w])⁻¹ • w, ?_⟩ hR
      rw [map_smul]
      refine hα.eq_reebVectorField_iff.2 ⟨?_, fun y ↦ ?_⟩
      · rw [ContinuousAlternatingMap.vecCons_smul, smul_eq_mul, inv_mul_cancel₀ ha]
      · rw [mextDeriv_eq_bilinFormAt, map_smul, LinearMap.smul_apply, hker y, smul_zero]
  exact hιs (by rw [map_zero]; exact hu)

/-- **The local Reeb flow out of a transverse hypersurface is a local diffeomorphism.** Let `α`
be a contact form and let `ι : S → M` be smooth from a boundaryless manifold of one dimension less.
At a point `(s, t)` of its domain such that `ι` has injective differential at `s` and the Reeb
vector `R_α(ι s)` is not tangent to the image, the local Reeb flow map `(s, t) ↦ φₜ(ι s)` is a
local diffeomorphism. It pulls `α` back to `dt + ι^* α`
(`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`). -/
theorem IsContactForm.isLocalDiffeomorphAt_flowOf_reebVectorField_comp [FiniteDimensional ℝ E']
    [J.Boundaryless] (hα : α.IsContactForm) (hdim : finrank ℝ E' + 1 = finrank ℝ E) {p : S × ℝ}
    (hιs : Function.Injective (mfderiv J I ι p.1))
    (hR : α.reebVectorField (ι p.1) ∉ (mfderiv J I ι p.1).range)
    (hp : (p.2, ι p.1) ∈ flowDomain α.reebVectorField) :
    IsLocalDiffeomorphAt (J.prod 𝓘(ℝ)) I ∞
      (fun q : S × ℝ ↦ flowOf α.reebVectorField q.2 (ι q.1)) p := by
  -- The second Reeb equation as an identity of one-forms: `ι_(R_α) dα = 0`.
  have hRα : (mextDeriv α.1).interior α.reebVectorField = 0 := by
    funext x
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
    simpa using hα.mextDeriv_reebVectorField_left x w
  exact isLocalDiffeomorphAt_flowOf_comp_of_nondegenerate hα.contMDiff_reebVectorField hι hdim
    hα.apply_reebVectorField hRα (hα.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι hdim hιs hR)
    hp

end SmoothForm

end TauCeti
