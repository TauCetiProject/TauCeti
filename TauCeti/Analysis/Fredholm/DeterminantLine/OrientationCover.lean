/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Bundle
public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Transport
public import TauCeti.Topology.VectorBundle.Orientation.ZeroSectionCompl
import TauCeti.LinearAlgebra.Orientation.Basis

/-!
# Orientation transport of Fredholm determinant lines through the orientation double cover

The determinant lines `det (ker T) ⊗ (det (F ⧸ range T))^*` of the Fredholm operators
`T : E →L[ℝ] F` form a real line bundle `TauCeti.FredholmDetLine ℝ E F` over the space of Fredholm
operators, whose local trivializations are kernel charts. Orientations of its fibres are
transported along paths of Fredholm operators in two ways:

* by lifting the path to the orientation double cover of the bundle
  (`TauCeti.VectorBundleOrientationCover.orientationTransport`), which is defined for any real
  vector bundle;
* by following a family of elements of the determinant lines which is *coherent*, read in kernel
  charts as positive multiples of each other nearby (`TauCeti.detLineOrientationTransport`), which
  needs neither the bundle nor its cover.

This file proves that the two agree
(`TauCeti.FredholmDetLine.orientationTransport_eq_iff_detLineOrientationTransport_eq`), so the
transport along coherent families, through which the orientation results on determinant lines
are proved, is the monodromy of the orientation double cover of the determinant line bundle.

The comparison rests on two facts. First, **coherent families lift to the cover.** If `v` is
coherent on `s` along a family `S` of Fredholm operators continuous on `s`, the orientations of the
fibres given by `v x` (`TauCeti.FredholmDetLine.orientationOfNeZero`, the orientation of the
one-vector basis `(v x)`) form a continuous map from `s` to the orientation double cover
(`TauCeti.IsDetLineCoherentOn.continuous_mk_orientationOfNeZero`). The preferred trivialization of
the bundle at each operator is a kernel chart
(`TauCeti.FredholmDetLine.exists_trivializationAt_eq_trivialization`), in which the readings of
`v x` lie on one ray nearby, so the orientation of `(v x)` read in it is locally constant. Second,
coherent families exist along every such family `S` with any nonzero initial value
(`TauCeti.exists_isDetLineCoherentOn_Icc`), so both transports can be computed along one of them.

A companion fact runs in the converse direction: **continuous sections are coherent.** A family
`v` which is a continuous section of the determinant line bundle over `s`, nonzero at every point of
`s`, is coherent on `s` (`TauCeti.isDetLineCoherentOn_of_continuousOn`), since the orientations it
gives form a continuous map to the orientation double cover
(`TauCeti.zeroSectionComplOrientation`) and so stay in one sheet of a kernel chart nearby. In
particular orientation transport carries the orientation of `v a` to that of `v b`
(`TauCeti.detLineOrientationTransport_rayOfNeZero_of_continuousOn`). Such a section also
determines a linear isomorphism between the end fibres, which orientation transport does not; this
compares the two.

## Main definitions

* `TauCeti.FredholmDetLine.orientationOfNeZero`: the orientation of a fibre of the determinant line
  bundle given by a nonzero element of the determinant line.

## Main results

* `TauCeti.IsDetLineCoherentOn.continuous_mk_orientationOfNeZero`: a coherent family is a
  continuous map to the orientation double cover.
* `TauCeti.isDetLineCoherentOn_of_continuousOn`: a nowhere-vanishing continuous section of the
  determinant line bundle is coherent.
* `TauCeti.detLineOrientationTransport_rayOfNeZero_of_continuousOn`: orientation transport follows
  nowhere-vanishing continuous sections.
* `TauCeti.IsDetLineCoherentOn.orientationTransport_orientationOfNeZero`: transport through the
  orientation double cover follows coherent families.
* `TauCeti.FredholmDetLine.orientationTransport_eq_iff_detLineOrientationTransport_eq`: the
  transport of orientations through the orientation double cover agrees with the transport along
  coherent families.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Bundle Filter Set Topology Module ContinuousLinearMap unitInterval

namespace TauCeti

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [TopologicalSpace X]

namespace FredholmDetLine

variable {n m : ℕ} {D₂ : (Fin n → ℝ) →L[ℝ] F} {q : E × (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)}

/-- The orientation of the fibre of the determinant line bundle over a Fredholm operator `T` given
by a nonzero element `u` of the determinant line of `T`: the orientation of the one-vector basis
`(u)`. -/
noncomputable def orientationOfNeZero {T : {T : E →L[ℝ] F // T.IsFredholm}}
    (u : (T.val : E →ₗ[ℝ] F).detLine) (hu : u ≠ 0) :
    Orientation ℝ (FredholmDetLine ℝ E F T) (Fin 1) :=
  (FiniteDimensional.basisSingleton (Fin 1) finrank_eq_one ((linearEquiv T).symm u)
    ((LinearEquiv.map_ne_zero_iff _).2 hu)).orientation

omit [CompleteSpace E] [CompleteSpace F] in
theorem orientationOfNeZero_def {T : {T : E →L[ℝ] F // T.IsFredholm}}
    (u : (T.val : E →ₗ[ℝ] F).detLine) (hu : u ≠ 0) :
    orientationOfNeZero u hu =
      (FiniteDimensional.basisSingleton (Fin 1) finrank_eq_one ((linearEquiv T).symm u)
        ((LinearEquiv.map_ne_zero_iff _).2 hu)).orientation :=
  (rfl)

/-- The orientation given by a nonzero element `u` of a determinant line is the point of the
orientation double cover given by `u` as a nonzero vector of the determinant line bundle. -/
theorem zeroSectionComplOrientation_eq_mk_orientationOfNeZero
    {T : {T : E →L[ℝ] F // T.IsFredholm}} (u : (T.val : E →ₗ[ℝ] F).detLine) (hu : u ≠ 0) :
    zeroSectionComplOrientation (finrank_self ℝ)
        ⟨⟨T, (linearEquiv T).symm u⟩,
          mem_zeroSectionCompl.2 ((LinearEquiv.map_ne_zero_iff _).2 hu)⟩ =
      ⟨T, orientationOfNeZero u hu⟩ := by
  rw [zeroSectionComplOrientation_apply]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The opposite element of a determinant line gives the opposite orientation. -/
@[simp]
theorem orientationOfNeZero_neg {T : {T : E →L[ℝ] F // T.IsFredholm}}
    {u : (T.val : E →ₗ[ℝ] F).detLine} (hu : -u ≠ 0) :
    orientationOfNeZero (-u) hu = -orientationOfNeZero u (neg_ne_zero (a := u).1 hu) := by
  have h : (linearEquiv T).symm (-u) = -(linearEquiv T).symm u := (linearEquiv T).symm.map_neg u
  simp only [orientationOfNeZero_def, h, orientation_basisSingleton_neg]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A positive multiple of an element of a determinant line gives the same orientation. -/
@[simp]
theorem orientationOfNeZero_smul_of_pos {T : {T : E →L[ℝ] F // T.IsFredholm}}
    {u : (T.val : E →ₗ[ℝ] F).detLine} {c : ℝ} (hc : 0 < c) (hu : c • u ≠ 0) :
    orientationOfNeZero (c • u) hu = orientationOfNeZero u (right_ne_zero_of_smul hu) := by
  have h : (linearEquiv T).symm (c • u) = c • (linearEquiv T).symm u := map_smul _ _ _
  simp only [orientationOfNeZero_def, h, orientation_basisSingleton_smul_of_pos _ hc]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Two nonzero elements of a determinant line give the same orientation of the fibre exactly when
they lie on the same ray. -/
theorem orientationOfNeZero_eq_iff {T : {T : E →L[ℝ] F // T.IsFredholm}}
    {u w : (T.val : E →ₗ[ℝ] F).detLine} (hu : u ≠ 0) (hw : w ≠ 0) :
    orientationOfNeZero u hu = orientationOfNeZero w hw ↔ SameRay ℝ u w := by
  rw [orientationOfNeZero_def, orientationOfNeZero_def, Basis.orientation_eq_iff_sameRay,
    FiniteDimensional.basisSingleton_apply, FiniteDimensional.basisSingleton_apply]
  exact SameRay.sameRay_map_iff _

/-- In a kernel chart, the orientations of the fibres of the determinant line bundle given by two
nonzero elements `u` and `u₀` of determinant lines are read as the same orientation of `ℝ` exactly
when the readings of `u` and `u₀` in the kernel chart `ContinuousLinearMap.detLineChartEquiv` lie on
the same ray. -/
private theorem mapOrientation_orientationOfNeZero_eq_iff {T T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (h : ((T.val.coprod D₂).prod q).IsInvertible) (h₀ : ((T₀.val.coprod D₂).prod q).IsInvertible)
    (hT : T ∈ (trivialization D₂ q).baseSet) (hT₀ : T₀ ∈ (trivialization D₂ q).baseSet)
    {u : (T.val : E →ₗ[ℝ] F).detLine} (hu : u ≠ 0) {u₀ : (T₀.val : E →ₗ[ℝ] F).detLine}
    (hu₀ : u₀ ≠ 0) :
    (trivialization D₂ q).mapOrientation (Fin 1) hT (orientationOfNeZero u hu) =
      (trivialization D₂ q).mapOrientation (Fin 1) hT₀ (orientationOfNeZero u₀ hu₀) ↔
      SameRay ℝ (detLineChartEquiv T.val D₂ q h u) (detLineChartEquiv T₀.val D₂ q h₀ u₀) := by
  have hc : (trivialization D₂ q ⟨T, (linearEquiv T).symm u⟩).2 ≠ 0 :=
    ((trivialization D₂ q).snd_apply_ne_zero_iff ℝ hT).2 ((LinearEquiv.map_ne_zero_iff _).2 hu)
  have hc₀ : (trivialization D₂ q ⟨T₀, (linearEquiv T₀).symm u₀⟩).2 ≠ 0 :=
    ((trivialization D₂ q).snd_apply_ne_zero_iff ℝ hT₀).2 ((LinearEquiv.map_ne_zero_iff _).2 hu₀)
  rw [orientationOfNeZero_def, orientationOfNeZero_def,
    Trivialization.mapOrientation_orientation_basisSingleton _ hT finrank_eq_one
      (finrank_self ℝ) _ hc,
    Trivialization.mapOrientation_orientation_basisSingleton _ hT₀ finrank_eq_one
      (finrank_self ℝ) _ hc₀,
    Basis.orientation_eq_iff_sameRay, FiniteDimensional.basisSingleton_apply,
    FiniteDimensional.basisSingleton_apply, trivialization_apply_mk D₂ q h,
    trivialization_apply_mk D₂ q h₀]
  exact sameRay_chartCoord_linearEquiv_symm_iff h h₀ u u₀

end FredholmDetLine

open FredholmDetLine

variable {S : X → {T : E →L[ℝ] F // T.IsFredholm}} {s : Set X}
  {v : ∀ x, ((S x).val : E →ₗ[ℝ] F).detLine}

/-- **Coherent families lift to the orientation double cover.** Let `S` be a family of Fredholm
operators continuous on `s`, and `v` a family of elements of their determinant lines which is
coherent on `s`. Then the orientations of the fibres given by `v x`, for `x ∈ s`, form a continuous
map from `s` to the orientation double cover of the determinant line bundle. -/
theorem IsDetLineCoherentOn.continuous_mk_orientationOfNeZero (hS : ContinuousOn S s)
    (hv : IsDetLineCoherentOn (fun x ↦ (S x).val) v s) :
    Continuous fun x : s ↦ (⟨S x, orientationOfNeZero (v x) (hv.ne_zero x.property)⟩ :
        VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1)) := by
  refine VectorBundleOrientationCover.continuous_of_isOpen_preimage_sheet hS.domRestrict
    fun T₀ o ↦ ?_
  -- The preferred trivialization at `T₀` is a kernel chart.
  obtain ⟨n, m, D₂, q, he⟩ := exists_trivializationAt_eq_trivialization T₀
  have hsheet : ∀ (e : Trivialization ℝ (π ℝ (FredholmDetLine ℝ E F))) [e.IsLinear ℝ],
      e = trivialization D₂ q → VectorBundleOrientationCover.sheet e o =
        VectorBundleOrientationCover.sheet (trivialization D₂ q) o := by
    -- The linearity instance is a proposition, so the two sheets agree on the nose.
    rintro _ _ rfl
    rfl
  rw [hsheet _ he]
  refine isOpen_iff_mem_nhds.2 fun x₀ hx₀ ↦ ?_
  obtain ⟨h₀, hx₀⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 hx₀
  have hi₀ : (((S x₀).val.coprod D₂).prod q).IsInvertible := by
    simpa using h₀
  -- Near `x₀`, the readings of `v x` in the kernel chart lie on the ray of the reading of `v x₀`.
  have hev := (isDetLineCoherentOn_iff.1 hv x₀ x₀.property).eventually_sameRay
    (continuous_subtypeVal.continuousAt.comp_continuousWithinAt (hS x₀ x₀.property)) hi₀
  rw [← map_nhds_subtypeVal, eventually_map] at hev
  filter_upwards [hev, hS.domRestrict.continuousAt.preimage_mem_nhds
    ((trivialization D₂ q).open_baseSet.mem_nhds h₀)] with x ⟨h, hx⟩ hxe
  refine VectorBundleOrientationCover.mem_sheet_iff.2 ⟨hxe, ?_⟩
  rw [← hx₀]
  exact (mapOrientation_orientationOfNeZero_eq_iff h hi₀ hxe h₀ (hv.ne_zero x.property)
    (hv.ne_zero x₀.property)).2 hx

/-- **Continuous sections are coherent.** Let `S` be a family of Fredholm operators. A family `v` of
elements of their determinant lines which is continuous on `s` as a map to the determinant line
bundle and nonzero at every point of `s` is coherent on `s`. -/
theorem isDetLineCoherentOn_of_continuousOn
    (hv : ContinuousOn (fun x ↦ (⟨S x, (linearEquiv (S x)).symm (v x)⟩ :
      TotalSpace ℝ (FredholmDetLine ℝ E F))) s)
    (hv0 : ∀ x ∈ s, v x ≠ 0) : IsDetLineCoherentOn (fun x ↦ (S x).val) v s := by
  -- The family of operators is continuous, as the projection of the section.
  have hS : ContinuousOn S s := (FiberBundle.continuous_proj ℝ _).comp_continuousOn hv
  refine isDetLineCoherentOn_iff.2 fun x₀ hx₀ ↦ ?_
  obtain ⟨n, m, D₂, q, he⟩ := exists_trivializationAt_eq_trivialization (S x₀)
  have h₀ : S x₀ ∈ (trivialization D₂ q).baseSet :=
    he ▸ mem_baseSet_trivializationAt ℝ (FredholmDetLine ℝ E F) (S x₀)
  have hi₀ : (((S x₀).val.coprod D₂).prod q).IsInvertible := by
    simpa using h₀
  -- The orientations given by `v x` form a continuous map from `s` to the orientation double
  -- cover, so near `x₀` they stay in the sheet of the kernel chart through the orientation given by
  -- `v x₀`.
  have hc : Continuous fun x : s ↦ (⟨S x, orientationOfNeZero (v x) (hv0 x x.property)⟩ :
      VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1)) :=
    ((zeroSectionComplOrientation (finrank_self ℝ)).continuous.comp
      (hv.domRestrict.subtype_mk fun x ↦ mem_zeroSectionCompl.2
        ((LinearEquiv.map_ne_zero_iff _).2 (hv0 x x.property)))).congr fun x ↦
        zeroSectionComplOrientation_eq_mk_orientationOfNeZero _ _
  have hev := (hc.continuousAt (x := ⟨x₀, hx₀⟩)).preimage_mem_nhds
    ((VectorBundleOrientationCover.isOpen_sheet (by simp) (trivialization D₂ q)
      ((trivialization D₂ q).mapOrientation (Fin 1) h₀
        (orientationOfNeZero (v x₀) (hv0 x₀ hx₀)))).mem_nhds
      (VectorBundleOrientationCover.mem_sheet_iff.2 ⟨h₀, rfl⟩))
  refine isDetLineCoherentWithinAt_of_eventually_sameRay
    (continuous_subtypeVal.continuousAt.comp_continuousWithinAt (hS x₀ hx₀)) (S x₀).property
    (hv0 x₀ hx₀) hi₀ ?_
  rw [← map_nhds_subtypeVal (⟨x₀, hx₀⟩ : s), eventually_map]
  filter_upwards [hev] with x hx
  obtain ⟨hxe, hxo⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 hx
  have hix : (((S x).val.coprod D₂).prod q).IsInvertible := by
    simpa using hxe
  exact ⟨hix, (mapOrientation_orientationOfNeZero_eq_iff hix hi₀ hxe h₀ (hv0 x x.property)
    (hv0 x₀ hx₀)).1 hxo⟩

/-- **Transport along a continuous section.** If `v` is a continuous section of the determinant
line bundle along a family `S` of Fredholm operators, continuous on `[[a, b]]` and nonzero at every
point of `[[a, b]]`, orientation transport carries the orientation of `v a` to that of `v b`. Such a
section also determines a linear isomorphism between the end fibres, sending `v a` to `v b`; so
this isomorphism carries orientations as orientation transport does, whatever section is chosen. -/
theorem detLineOrientationTransport_rayOfNeZero_of_continuousOn
    {S : ℝ → {T : E →L[ℝ] F // T.IsFredholm}} {v : ∀ t, ((S t).val : E →ₗ[ℝ] F).detLine}
    {a b : ℝ} (hv : ContinuousOn (fun t ↦ (⟨S t, (linearEquiv (S t)).symm (v t)⟩ :
      TotalSpace ℝ (FredholmDetLine ℝ E F))) (uIcc a b))
    (hv0 : ∀ t ∈ uIcc a b, v t ≠ 0) :
    detLineOrientationTransport a b (continuous_subtypeVal.comp_continuousOn
        ((FiberBundle.continuous_proj ℝ (FredholmDetLine ℝ E F)).comp_continuousOn hv))
        (fun t _ ↦ (S t).property) (rayOfNeZero ℝ (v a) (hv0 a left_mem_uIcc)) =
      rayOfNeZero ℝ (v b) (hv0 b right_mem_uIcc) :=
  detLineOrientationTransport_rayOfNeZero _ _ (isDetLineCoherentOn_of_continuousOn hv hv0)

/-- **Coherent families follow the lift to the orientation double cover.** Let `S` be a family of
Fredholm operators continuous on `[[a, b]]`, `γ` the path `τ ↦ S ((1 - τ) a + τ b)` from `S a`
to `S b` in the space of Fredholm operators, and `v` a family of elements of the determinant lines
coherent on `[[a, b]]`. Transport along `γ` through the orientation double cover of the
determinant line bundle carries the orientation given by `v a` to the orientation given by `v b`. -/
theorem IsDetLineCoherentOn.orientationTransport_orientationOfNeZero
    {S : ℝ → {T : E →L[ℝ] F // T.IsFredholm}} {a b : ℝ} (hS : ContinuousOn S (uIcc a b))
    (γ : Path (S a) (S b)) (hγ : ∀ τ : I, γ τ = S (AffineMap.lineMap a b (τ : ℝ)))
    {v : ∀ t, ((S t).val : E →ₗ[ℝ] F).detLine}
    (hv : IsDetLineCoherentOn (fun t ↦ (S t).val) v (uIcc a b)) :
    VectorBundleOrientationCover.orientationTransport (F := ℝ) (FredholmDetLine ℝ E F)
        (by simp) γ (orientationOfNeZero (v a) (hv.ne_zero left_mem_uIcc)) =
      orientationOfNeZero (v b) (hv.ne_zero right_mem_uIcc) := by
  have hmem (τ : I) : AffineMap.lineMap a b (τ : ℝ) ∈ uIcc a b := by
    rw [← segment_eq_uIcc]
    exact lineMap_mem_segment ℝ a b τ.property
  -- The orientations given by `v t` along the segment form a lift of `γ` to the orientation cover.
  let Γ : C(I, VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1)) :=
    ⟨fun τ ↦ ⟨S (AffineMap.lineMap a b (τ : ℝ)), orientationOfNeZero (v _) (hv.ne_zero (hmem τ))⟩,
      (hv.continuous_mk_orientationOfNeZero hS).comp
        (f := fun τ : I ↦ (⟨AffineMap.lineMap a b (τ : ℝ), hmem τ⟩ : uIcc a b))
        (by fun_prop)⟩
  have hΓ : VectorBundleOrientationCover.proj ∘ Γ = γ := funext fun τ ↦ (hγ τ).symm
  -- The ends of the lift, read as orientations of the fibres over `S a` and `S b`.
  have hend (t : ℝ) (ht : t ∈ uIcc a b) (t' : ℝ) (htt' : t = t') (h : S t = S t') :
      VectorBundleOrientationCover.fiberEquiv ℝ (FredholmDetLine ℝ E F) (Fin 1) (S t')
        ⟨⟨S t, orientationOfNeZero (v t) (hv.ne_zero ht)⟩, h⟩ =
      orientationOfNeZero (v t') (hv.ne_zero (htt' ▸ ht)) := by
    subst htt'
    exact VectorBundleOrientationCover.fiberEquiv_mk _
  have h₀ : (Γ 0).proj = S a := by simp [Γ]
  have h₁ : (Γ 1).proj = S b := by simp [Γ]
  have hlift : VectorBundleOrientationCover.orientationTransport (F := ℝ) (FredholmDetLine ℝ E F)
      (by simp) γ (VectorBundleOrientationCover.fiberEquiv ℝ (FredholmDetLine ℝ E F) (Fin 1) (S a)
        ⟨⟨S (AffineMap.lineMap a b ((0 : I) : ℝ)), orientationOfNeZero (v _) (hv.ne_zero (hmem 0))⟩,
          h₀⟩) =
      VectorBundleOrientationCover.fiberEquiv ℝ (FredholmDetLine ℝ E F) (Fin 1) (S b)
        ⟨⟨S (AffineMap.lineMap a b ((1 : I) : ℝ)), orientationOfNeZero (v _) (hv.ne_zero (hmem 1))⟩,
          h₁⟩ :=
    VectorBundleOrientationCover.orientationTransport_eq_of_lift (by simp) γ Γ hΓ h₀ h₁
  rwa [hend _ (hmem 0) a (by simp) h₀, hend _ (hmem 1) b (by simp) h₁] at hlift

namespace FredholmDetLine

/-- **The two transports of orientations agree.** Let `S` be a family of Fredholm operators
continuous on `[[a, b]]`, and `γ` the path `τ ↦ S ((1 - τ) a + τ b)` from `S a` to `S b` in the
space of Fredholm operators. For nonzero elements `u` and `w` of the determinant lines at the two
ends, the lift of `γ` to the orientation double cover of the determinant line bundle carries the
orientation given by `u` to that given by `w` exactly when orientation transport along coherent
families (`TauCeti.detLineOrientationTransport`) carries the orientation of `u` to that of `w`. -/
theorem orientationTransport_eq_iff_detLineOrientationTransport_eq
    {S : ℝ → {T : E →L[ℝ] F // T.IsFredholm}} {a b : ℝ} (hS : ContinuousOn S (uIcc a b))
    (γ : Path (S a) (S b)) (hγ : ∀ τ : I, γ τ = S (AffineMap.lineMap a b (τ : ℝ)))
    {u : ((S a).val : E →ₗ[ℝ] F).detLine} (hu : u ≠ 0) {w : ((S b).val : E →ₗ[ℝ] F).detLine}
    (hw : w ≠ 0) :
    VectorBundleOrientationCover.orientationTransport (F := ℝ) (FredholmDetLine ℝ E F)
        (by simp) γ (orientationOfNeZero u hu) = orientationOfNeZero w hw ↔
      detLineOrientationTransport a b (continuous_subtypeVal.comp_continuousOn hS)
        (fun t _ ↦ (S t).property) (rayOfNeZero ℝ u hu) = rayOfNeZero ℝ w hw := by
  have hF : ∀ t ∈ uIcc a b, ((S t).val).IsFredholm := fun t _ ↦ (S t).property
  have hT : ContinuousOn (fun t ↦ (S t).val) (uIcc a b) :=
    continuous_subtypeVal.comp_continuousOn hS
  -- Both transports follow a coherent family `v` on `[[a, b]]` starting at `u`.
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc hu
  rw [detLineOrientationTransport_rayOfNeZero hT hF hv, ray_eq_iff,
    hv.orientationTransport_orientationOfNeZero hS γ hγ, orientationOfNeZero_eq_iff,
    SameRay.sameRay_comm]

end FredholmDetLine

end TauCeti
