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
  The statement for `dα` needs only `ι_Z dα = 0`: the flow preserves the closed form `dα`, and `Z`
  lies in its kernel.
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

## Acknowledgements

The flow-map arguments adapt those for the local Liouville flow out of a hypersurface in
`TauCeti/Geometry/Symplectic/Liouville/Collar.lean`
(`TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`,
`TauCeti.mpullback_flowOf_comp_mextDeriv_apply`, `TauCeti.injective_mfderiv_flowOf_comp`,
`TauCeti.isLocalDiffeomorphAt_flowOf_comp`), with the time coordinate placed last as in the
contactization.

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

/-- The differential of the local flow map `(s, t) ↦ φₜ(ι s)` sends a tangent vector `(w, r)` to
`r Z + dφₜ(dι w)`. This is `TauCeti.mfderiv_flowOf_comp_prodMk_apply` in the coordinates of
`S × ℝ`. -/
private theorem mfderiv_flowOf_comp_fst_apply {p : S × ℝ} (hp : (p.2, ι p.1) ∈ flowDomain Z)
    (v : TangentSpace (J.prod 𝓘(ℝ)) p) :
    mfderiv (J.prod 𝓘(ℝ)) I (fun q : S × ℝ ↦ flowOf Z q.2 (ι q.1)) p v =
      v.2 • Z (flowOf Z p.2 (ι p.1)) +
        mfderiv I I (flowOf Z p.2) (ι p.1) (mfderiv J I ι p.1 v.1) := by
  rw [mfderiv_flowOf_comp_prodMk_apply (τ := Prod.snd) (f := fun q : S × ℝ ↦ ι q.1)
    (hZ.of_le (by simp)) mdifferentiableAt_snd
    (((hι p.1).mdifferentiableAt (by simp)).comp p mdifferentiableAt_fst) hp,
    show (fun q : S × ℝ ↦ ι q.1) = ι ∘ Prod.fst from rfl,
    mfderiv_comp_apply (g := ι) (f := (Prod.fst : S × ℝ → S)) (x := p)
      ((hι p.1).mdifferentiableAt (by simp)) mdifferentiableAt_fst, mfderiv_fst]
  simp only [mvfderiv, mfderiv_snd]
  -- The remaining projections of `v` agree definitionally.
  rfl

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
the smooth vector field `Z` satisfy `ι_Z dα = 0`, and let `ι : S → M` be smooth. At every point of
its domain, the local flow map `(s, t) ↦ φₜ(ι s)` pulls `dα` back to the exterior derivative of
`dt + ι^* α`, which is `d(ι^* α)` on the components in `S`
(`TauCeti.SmoothForm.mextDeriv_contactization_apply`). No normalization of `α(Z)` is needed: the
flow preserves `dα`, and `Z` lies in its kernel. -/
theorem mpullback_flowOf_comp_mextDeriv_apply_eq_mextDeriv_contactization
    (hZα : (mextDeriv α.1).interior Z = 0) {p : S × ℝ} (hp : (p.2, ι p.1) ∈ flowDomain Z) :
    mpullback (J.prod 𝓘(ℝ)) I (fun q : S × ℝ ↦ flowOf Z q.2 (ι q.1)) (mextDeriv α.1) p =
      mextDeriv (-SmoothForm.mpullback ι hι α).contactization.1 p := by
  -- `Z` lies in the kernel of `dα`, on either side.
  have hZl (x : M) (w : TangentSpace I x) : (mextDerivₗ I 1 α).bilinFormAt x (Z x) w = 0 := by
    have h := congrArg (fun β : RoughForm I M ℝ 1 ↦ β x ![w]) hZα
    simp only [RoughForm.interior_apply, Pi.zero_apply, ContinuousAlternatingMap.coe_zero] at h
    rwa [← SmoothForm.mextDeriv_eq_bilinFormAt]
  have hZr (x : M) (w : TangentSpace I x) : (mextDerivₗ I 1 α).bilinFormAt x w (Z x) = 0 := by
    rw [← (SmoothForm.isAlt_bilinFormAt _ x).neg_eq, hZl, neg_zero]
  -- The local flow preserves the closed form `dα`, whose contraction `ι_Z dα` vanishes.
  have hinv := mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero (hZ.of_le (by simp))
    (SmoothForm.isClosed_mextDerivₗ α) (by rw [mextDerivₗ_apply, hZα, mextDeriv_zero]) hp
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b, v = ![a, b] :=
    ⟨v 0, v 1, funext fun i ↦ by fin_cases i <;> rfl⟩
  set X := mfderiv J I ι p.1 a.1
  set Y := mfderiv J I ι p.1 b.1
  have hs : (mextDerivₗ I 1 α).bilinFormAt (flowOf Z p.2 (ι p.1))
      (mfderiv I I (flowOf Z p.2) (ι p.1) X) (mfderiv I I (flowOf Z p.2) (ι p.1) Y) =
      (mextDerivₗ I 1 α).bilinFormAt (ι p.1) X Y := by
    rw [mextDerivₗ_apply] at hinv
    rw [← SmoothForm.mextDeriv_eq_bilinFormAt, ← SmoothForm.mextDeriv_eq_bilinFormAt]
    exact (mpullback_apply_pair _ _ _ _ _).symm.trans (congrArg (· ![X, Y]) hinv)
  -- `d(ι^* α)` is `dα` on the images under `dι`.
  have hpull (u w : TangentSpace J p.1) :
      (mextDerivₗ J 1 (SmoothForm.mpullback ι hι α)).eval₂ p.1 u w =
        (mextDerivₗ I 1 α).bilinFormAt (ι p.1) (mfderiv J I ι p.1 u) (mfderiv J I ι p.1 w) := by
    rw [SmoothForm.mextDerivₗ_mpullback, SmoothForm.eval₂_mpullback,
      ← SmoothForm.bilinFormAt_apply]
  -- Differentiate the flow map; the components along `Z` drop out.
  rw [mpullback_apply_pair, SmoothForm.mextDeriv_contactization_apply, map_neg, neg_neg,
    SmoothForm.mextDeriv_eq_bilinFormAt, mfderiv_flowOf_comp_fst_apply hZ hι hp,
    mfderiv_flowOf_comp_fst_apply hZ hι hp]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hZl, hZr, smul_zero,
    add_zero, zero_add, Manifold.tangentSpaceProdEquiv_apply]
  exact hs.trans (hpull _ _).symm

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
    rw [← mpullback_flowOf_comp_mextDeriv_apply_eq_mextDeriv_contactization hZ hι hZα hp,
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
  exact isLocalDiffeomorphAt_of_injective_mfderiv
    (fun q hq ↦ (contMDiffAt_flowOf_comp le_top hZ contMDiffAt_snd
      (hι.contMDiffAt.comp q contMDiffAt_fst) hq).contMDiffWithinAt)
    (isOpen_setOf_mem_flowDomain (hZ.of_le (by simp)) continuous_snd
      (hι.continuous.comp continuous_fst)) hp BoundarylessManifold.isInteriorPoint (by simp)
    (injective_mfderiv_flowOf_comp_of_nondegenerate hZ hι hαZ hZα hβ hp)
    (by rw [← hdim, Module.finrank_prod, Module.finrank_self])

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
  set B := (mextDerivₗ I 1 α).bilinFormAt (ι s)
  have : FiniteDimensional ℝ (TangentSpace J s) := Module.Finite.of_injective L hιs
  -- The image of `dι` is a complement of the kernel of `dα`, which is the Reeb line.
  have hc := isContactForm_def.1 hα (ι s)
  have hRv := hα.eq_reebVectorField_iff.2 ⟨by simpa using hc.apply_reebVector, fun y ↦ by
    rw [mextDeriv_eq_bilinFormAt]
    exact hc.apply_reebVector_left (isAlt_bilinFormAt _ _) y⟩
  have hcompl : IsCompl (LinearMap.range L) (LinearMap.ker B) := by
    rw [hc.ker_eq_span_reebVector (isAlt_bilinFormAt _ _), hRv]
    refine ⟨Submodule.disjoint_span_singleton.2 fun h ↦ absurd h hR, codisjoint_iff.2 ?_⟩
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Submodule.finrank_sup_span_singleton hR, LinearMap.finrank_range_of_inj hιs]
    exact hdim
  -- So `dα` is nondegenerate on the image of `dι`, and `d(ι^* α)` is its pullback along `dι`.
  have hnd := (isAlt_bilinFormAt _ _).isRefl.nondegenerate_restrict_of_isCompl_ker hcompl
  rw [LinearMap.BilinForm.Nondegenerate,
    (isAlt_bilinFormAt _ s).isRefl.nondegenerate_iff_separatingLeft]
  intro w hw
  have hLw : (⟨L w, w, rfl⟩ : LinearMap.range L) = 0 := hnd.1 _ fun ⟨_, u, hu⟩ ↦ by
    subst hu
    rw [LinearMap.BilinForm.restrict_apply, ← hw u, bilinFormAt_apply, mextDerivₗ_mpullback,
      eval₂_mpullback, ← bilinFormAt_apply]
    -- `L` is the differential of `ι` viewed as a linear map.
    rfl
  exact hιs (by rw [map_zero]; exact congrArg Subtype.val hLw)

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
  exact isLocalDiffeomorphAt_flowOf_comp_of_nondegenerate hα.contMDiff_reebVectorField hι hdim
    hα.apply_reebVectorField hα.interior_mextDeriv_reebVectorField
    (hα.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι hdim hιs hR) hp

end SmoothForm

end TauCeti
