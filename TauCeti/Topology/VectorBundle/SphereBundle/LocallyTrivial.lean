/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import TauCeti.Topology.Homotopy.HurewiczFibration.LocallyTrivial
public import TauCeti.Topology.Homotopy.SerreFibration.Connected
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Sphere bundles are locally trivial

Let `E → B` be a real vector bundle with model fibre `F` whose fibres carry norms, such that the
fibre norm is a continuous function on the total space; for instance a continuous Riemannian
vector bundle (`TauCeti.continuous_norm_bundle`). A linear bundle chart `e` of `E`, followed by
normalization `x ↦ ‖x‖⁻¹ • x` (`NormedSpace.normalize`) of the fibre coordinate, carries the unit
sphere bundle `S(E)` (`TauCeti.sphereBundle`) over its base set onto the product with the unit
sphere `S(F)` of the model fibre, with inverse the inverse of `e` followed by normalization in the
fibres of `E`. So it restricts to a chart of the projection `S(E) → B` (`TauCeti.sphereBundleProj`)
with fibre `S(F)` (`Bundle.Trivialization.sphereBundle`).

So the sphere bundle is locally trivial with fibre the unit sphere of the model fibre
(`TauCeti.exists_trivialization_sphereBundleProj`). Consequently:

* the projection `S(E) → B` is a Serre fibration
  (`TauCeti.TopCat.mem_serreFibrations_sphereBundleProj`), and a Hurewicz fibration over a normal
  paracompact base (`TauCeti.isHurewiczFibration_sphereBundleProj`);
* when `F` has dimension `n + 1`, so that the fibres are `n`-spheres, the projection is
  `n`-connected (`TauCeti.isNConnected_sphereBundleProj`): it induces isomorphisms on `πₖ` for
  `k < n` and a surjection on `πₙ`;
* in particular, for `n ≥ 2`, the sphere bundle is simply connected exactly when the base is
  (`TauCeti.simplyConnectedSpace_sphereBundle_iff`).

These are the facts about a bundle `Sⁿ → Q → B` with structure group `O(n + 1)`, realized as the
unit sphere bundle of a Euclidean vector bundle, that are used to compare the homotopy of `Q` with
that of its base and fibres.

## Main declarations

* `Bundle.Trivialization.sphereBundle`: the chart of `S(E) → B` induced by a linear chart of `E`.
* `TauCeti.exists_trivialization_sphereBundleProj`: the sphere bundle of a real vector bundle with
  continuous fibre norm is locally trivial.
* `TauCeti.TopCat.mem_serreFibrations_sphereBundleProj`,
  `TauCeti.isHurewiczFibration_sphereBundleProj`: it is a Serre fibration, and a Hurewicz
  fibration over a normal paracompact base.
* `TauCeti.isNConnected_sphereBundleProj`, `TauCeti.simplyConnectedSpace_sphereBundle_iff`: its
  connectivity.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§12.1–12.2
  (sphere bundles and the orthogonal group).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §12 (the sphere bundle of a Euclidean vector bundle).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23.
-/

public section

noncomputable section

open Bundle Metric Module Set Topology
open scoped Topology.Homotopy

universe v w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]

section Nonempty

variable [NormedSpace ℝ F] [∀ b, NormedSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- A point of the sphere bundle gives a unit vector in the model fibre. -/
private theorem nonempty_sphere_of_sphereBundle (v : sphereBundle F E) :
    Nonempty (sphere (0 : F) 1) := by
  let b := (v : TotalSpace F E).proj
  let L := (trivializationAt F E b).continuousLinearEquivAt ℝ b (mem_baseSet_trivializationAt F E b)
  have hv : (v : TotalSpace F E).2 ≠ 0 :=
    norm_ne_zero_iff.1 (by rw [(mem_sphereBundle.1 v.2)]; exact one_ne_zero)
  have : Nontrivial F := ⟨⟨L (v : TotalSpace F E).2, 0, L.map_ne_zero_iff.2 hv⟩⟩
  exact (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype

/-- A unit vector in the model fibre gives a point of the sphere bundle over every point. -/
private theorem nonempty_sphereBundle (b : B) (w : sphere (0 : F) 1) :
    Nonempty (sphereBundle F E) := by
  let L := (trivializationAt F E b).continuousLinearEquivAt ℝ b (mem_baseSet_trivializationAt F E b)
  have hw : L.symm w ≠ 0 :=
    L.symm.map_ne_zero_iff.2 (ne_zero_of_mem_unit_sphere w)
  exact ⟨⟨⟨b, ‖L.symm w‖⁻¹ • L.symm w⟩, by
    rw [mem_sphereBundle, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]⟩⟩

end Nonempty

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, NormedSpace ℝ (E b)] (e : Trivialization F (π F E)) [e.IsLinear ℝ]

/-- A linear chart sends unit vectors over its base set to nonzero vectors. -/
private theorem apply_snd_ne_zero_of_mem_sphereBundle {v : TauCeti.sphereBundle F E}
    (hv : (v : TotalSpace F E).proj ∈ e.baseSet) : (e v).2 ≠ 0 :=
  (e.linearEquivAt ℝ _ hv).map_ne_zero_iff.2
    (norm_ne_zero_iff.1 (by rw [mem_sphereBundle.1 v.2]; exact one_ne_zero))

variable [FiberBundle F E] [VectorBundle ℝ F E]

open scoped Classical in
/-- The fibre coordinate of the chart of the sphere bundle: `e` followed by normalization over its
base set, and an arbitrary unit vector elsewhere. -/
private def sphereBundleCoord (v : TauCeti.sphereBundle F E) : sphere (0 : F) 1 :=
  if hv : (v : TotalSpace F E).proj ∈ e.baseSet then
    ⟨NormedSpace.normalize (e v).2, mem_sphere_zero_iff_norm.2
      (NormedSpace.norm_normalize_eq_one_iff.2 (e.apply_snd_ne_zero_of_mem_sphereBundle hv))⟩
  else Classical.choice (nonempty_sphere_of_sphereBundle v)

private theorem coe_sphereBundleCoord {v : TauCeti.sphereBundle F E}
    (hv : (v : TotalSpace F E).proj ∈ e.baseSet) :
    (e.sphereBundleCoord v : F) = NormedSpace.normalize (e v).2 := by
  simp only [sphereBundleCoord, hv, ↓reduceDIte]

open scoped Classical in
/-- The inverse of the chart of the sphere bundle: the inverse of `e` followed by normalization
over its base set, and an arbitrary unit vector elsewhere. -/
private def sphereBundleInv (p : B × sphere (0 : F) 1) : TauCeti.sphereBundle F E :=
  if hp : p.1 ∈ e.baseSet then
    ⟨⟨p.1, NormedSpace.normalize (e.symm p.1 p.2)⟩,
      mem_sphereBundle.2 (NormedSpace.norm_normalize_eq_one_iff.2
        ((e.symm_apply_ne_zero_iff ℝ hp).2 (ne_zero_of_mem_unit_sphere p.2)))⟩
  else Classical.choice (nonempty_sphereBundle p.1 p.2)

private theorem coe_sphereBundleInv {p : B × sphere (0 : F) 1} (hp : p.1 ∈ e.baseSet) :
    (e.sphereBundleInv p : TotalSpace F E) = ⟨p.1, NormedSpace.normalize (e.symm p.1 p.2)⟩ := by
  simp only [sphereBundleInv, hp, ↓reduceDIte]

/-- **The chart of the sphere bundle induced by a linear chart.** For a real vector bundle whose
fibre norm is continuous on the total space, a linear bundle chart `e` of `E`, followed by
normalization of the fibre coordinate, restricts to a chart of the projection `S(E) → B` from the
unit sphere bundle, with fibre the unit sphere of the model fibre and the same base set. -/
def sphereBundle (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    Trivialization (sphere (0 : F) 1) (sphereBundleProj F E) where
  toFun v := (sphereBundleProj F E v, e.sphereBundleCoord v)
  invFun := e.sphereBundleInv
  source := sphereBundleProj F E ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hv := ⟨hv, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, sphereBundleProj_apply, e.coe_sphereBundleInv hp.1]
    exact hp.1
  left_inv' v hv := by
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := by simpa using hv
    have hpos : 0 < ‖(e v).2‖⁻¹ :=
      inv_pos.2 (norm_pos_iff.2 (e.apply_snd_ne_zero_of_mem_sphereBundle hv'))
    apply Subtype.ext
    -- The inverse of `e` is linear on the fibre, so it undoes `e` up to a positive factor.
    rw [sphereBundleProj_apply, e.coe_sphereBundleInv hv', e.coe_sphereBundleCoord hv',
      NormedSpace.normalize.eq_1 (e v).2, e.symm_apply_smul hv',
      NormedSpace.normalize_smul_of_pos hpos, e.symm_proj_apply _ hv',
      NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphereBundle.1 v.2)]
  right_inv' p hp := by
    have hp' : p.1 ∈ e.baseSet := hp.1
    have hpos : 0 < ‖e.symm p.1 p.2‖⁻¹ := inv_pos.2
      (norm_pos_iff.2 ((e.symm_apply_ne_zero_iff ℝ hp').2 (ne_zero_of_mem_unit_sphere p.2)))
    have hsymm := e.coe_sphereBundleInv hp'
    have hz : (e.sphereBundleInv p : TotalSpace F E).proj = p.1 := by rw [hsymm]
    refine Prod.ext ((sphereBundleProj_apply F E _).trans hz) (Subtype.ext ?_)
    -- The chart `e` is linear on the fibre, so it undoes its inverse up to a positive factor.
    rw [e.coe_sphereBundleCoord (by rwa [hz]), hsymm,
      NormedSpace.normalize.eq_1 (e.symm p.1 p.2), e.snd_apply_mk_smul hp', e.apply_mk_symm hp',
      NormedSpace.normalize_smul_of_pos hpos,
      NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p.2)]
  open_source := e.open_baseSet.preimage (sphereBundleProj F E).continuous
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    -- Read the second coordinate in the model fibre, where the map is `e` followed by
    -- normalization.
    rw [(IsInducing.id.prodMap IsInducing.subtypeVal).continuousOn_iff]
    have he : ContinuousOn (fun v : TauCeti.sphereBundle F E ↦ e v)
        (sphereBundleProj F E ⁻¹' e.baseSet) :=
      e.continuousOn.comp continuous_subtype_val.continuousOn fun v hv ↦
        e.mem_source.2 (by simpa using hv)
    refine (he.fst.prodMk (((continuous_norm.comp_continuousOn he.snd).inv₀ fun v hv ↦
      norm_ne_zero_iff.2 (e.apply_snd_ne_zero_of_mem_sphereBundle (by simpa using hv))).smul
        he.snd)).congr
      fun v hv ↦ ?_
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := by simpa using hv
    exact Prod.ext ((sphereBundleProj_apply F E v).trans (e.coe_fst (e.mem_source.2 hv')).symm)
      (e.coe_sphereBundleCoord hv')
  continuousOn_invFun := by
    -- Read the value in the total space of `E`, where the map is the inverse of `e` applied to a
    -- rescaled unit vector; the rescaling factor is continuous because the fibre norm is.
    rw [IsInducing.subtypeVal.continuousOn_iff]
    have hs : ContinuousOn (fun p : B × sphere (0 : F) 1 ↦
        e.toOpenPartialHomeomorph.symm (p.1, (p.2 : F))) (e.baseSet ×ˢ univ) :=
      e.toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuous_id.prodMap continuous_subtype_val).continuousOn
        fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ e.mk_mem_target.2 hp.1
    have hn : ContinuousOn (fun p : B × sphere (0 : F) 1 ↦
        ‖(e.toOpenPartialHomeomorph.symm (p.1, (p.2 : F))).2‖⁻¹) (e.baseSet ×ˢ univ) :=
      (hnorm.comp_continuousOn hs).inv₀ fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ by
        rw [Function.comp_apply, ← e.mk_symm hp.1]
        exact norm_ne_zero_iff.2
          ((e.symm_apply_ne_zero_iff ℝ hp.1).2 (ne_zero_of_mem_unit_sphere p.2))
    refine (e.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_fst.continuousOn.prodMk
        (hn.smul (continuous_subtype_val.comp continuous_snd).continuousOn))
      fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ e.mk_mem_target.2 hp.1).congr
      fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ ?_
    simp only [Function.comp_apply, Pi.smul_apply']
    -- Over the base set the inverse of `e` is `e.symm p.1` in the fibre, which is linear; unfold
    -- `normalize` to its defining scalar multiple.
    rw [e.coe_sphereBundleInv hp.1, ← e.mk_symm hp.1, ← e.mk_symm hp.1, e.symm_apply_smul hp.1,
      NormedSpace.normalize.eq_1]
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)

@[simp]
theorem sphereBundle_baseSet : (e.sphereBundle hnorm).baseSet = e.baseSet :=
  (rfl)

/-- Over its base set, the chart of the sphere bundle reads a unit vector in the chart `e` and
normalizes it. -/
@[simp]
theorem coe_sphereBundle_apply_snd {v : TauCeti.sphereBundle F E}
    (hv : (v : TotalSpace F E).proj ∈ e.baseSet) :
    ((e.sphereBundle hnorm v).2 : F) = NormedSpace.normalize (e v).2 :=
  e.coe_sphereBundleCoord hv

/-- Over its base set, the inverse chart of the sphere bundle is the inverse of `e` followed by
normalization. -/
@[simp]
theorem coe_sphereBundle_symm_apply {b : B} (hb : b ∈ e.baseSet) (w : sphere (0 : F) 1) :
    ((e.sphereBundle hnorm).toOpenPartialHomeomorph.symm (b, w) : TotalSpace F E) =
      ⟨b, NormedSpace.normalize (e.symm b w)⟩ :=
  e.coe_sphereBundleInv (p := (b, w)) hb

end Bundle.Trivialization

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, NormedSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

variable (F E) in
/-- **The sphere bundle of a real vector bundle is locally trivial.** For a real vector bundle
whose fibre norm is continuous on the total space, every point of the base lies in the base set of
a chart of `S(E) → B` with fibre the unit sphere of the model fibre `F`. No finite-dimensionality,
and no separation or paracompactness assumption on the base, is needed. -/
theorem exists_trivialization_sphereBundleProj (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    (b : B) : ∃ e : Trivialization (sphere (0 : F) 1) (sphereBundleProj F E), b ∈ e.baseSet :=
  ⟨(trivializationAt F E b).sphereBundle hnorm, mem_baseSet_trivializationAt F E b⟩

variable (F E) in
/-- **The sphere bundle of a real vector bundle is a Serre fibration.** -/
theorem TopCat.mem_serreFibrations_sphereBundleProj
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    TopCat.serreFibrations (_root_.TopCat.ofHom (sphereBundleProj F E) :
      _root_.TopCat.of (sphereBundle F E) ⟶ _root_.TopCat.of B) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (exists_trivialization_sphereBundleProj F E hnorm)

variable (F E) in
/-- **The sphere bundle of a real vector bundle over a normal paracompact base is a Hurewicz
fibration.** This includes every paracompact Hausdorff base. -/
theorem isHurewiczFibration_sphereBundleProj [NormalSpace B] [ParacompactSpace B]
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    IsHurewiczFibration.{v} (sphereBundleProj F E) :=
  isHurewiczFibration_of_exists_trivialization (exists_trivialization_sphereBundleProj F E hnorm)

variable (E) in
/-- **The `n`-sphere bundle of a real vector bundle is an `n`-connected map.** If the fibre norm is
continuous on the total space and the model fibre `F` has dimension `n + 1`, the projection
`S(E) → B`, whose fibres are `n`-spheres, induces bijections on `πₖ` for `k < n`, path components
included, and a surjection on `πₙ`. -/
theorem isNConnected_sphereBundleProj (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) {n : ℕ}
    (hF : finrank ℝ F = n + 1) : (sphereBundleProj F E).IsNConnected n := by
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  refine (TopCat.isNConnected_iff_of_mem_serreFibrations
    (TopCat.mem_serreFibrations_sphereBundleProj F E hnorm) n).2 fun b ↦ ?_
  -- Every fibre is homeomorphic to the unit sphere of `F`, which is `(n - 1)`-connected.
  obtain ⟨e, hb⟩ := exists_trivialization_sphereBundleProj F E hnorm b
  let h : sphereBundleProj F E ⁻¹' {b} ≃ₜ sphere (0 : F) 1 := e.preimageSingletonHomeomorph hb
  refine ⟨⟨h.symm ⟨_, (NormedSpace.sphere_nonempty.2 zero_le_one).some_mem⟩⟩,
    fun x k hk ↦ ?_⟩
  have := subsingleton_homotopyGroup_sphere_of_lt hF (N := Fin k) (by simpa using hk) (h x)
  exact (HomotopyGroup.homeomorphEquiv h x).subsingleton

variable (E) in
/-- **An `n`-sphere bundle with `n ≥ 2` is simply connected exactly when its base is.** If the fibre
norm of a real vector bundle is continuous on the total space and its model fibre `F` has dimension
`n + 1` with `n ≥ 2`, its unit sphere bundle is simply connected exactly when the base is. -/
theorem simplyConnectedSpace_sphereBundle_iff (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {n : ℕ} (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n) :
    SimplyConnectedSpace (sphereBundle F E) ↔ SimplyConnectedSpace B :=
  (isNConnected_sphereBundleProj E hnorm hF).simplyConnectedSpace_iff hn

end TauCeti
