/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Topology.Homotopy.HurewiczFibration.LocallyTrivial
public import TauCeti.Topology.Homotopy.SerreFibration.Connected
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
import TauCeti.Topology.VectorBundle.OrthonormalTrivialization

/-!
# Sphere bundles are locally trivial

Let `E → B` be a real vector bundle with model fibre `F` whose fibres carry norms. A bundle chart
`e` of `E` whose fibre maps preserve norms carries the unit sphere bundle `S(E)`
(`TauCeti.sphereBundle`) over its base set onto the product with the unit sphere `S(F)` of the
model fibre. So it restricts to a chart of the projection `S(E) → B` with fibre `S(F)`
(`Bundle.Trivialization.sphereBundle`).

A continuous Riemannian vector bundle of finite rank has such norm-preserving charts around every
point, obtained from any linear chart by Gram–Schmidt
(`OrthonormalBasis.exists_orthonormal_trivialization`). So its sphere bundle is locally trivial
with fibre the unit sphere of the model fibre
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

* `Bundle.Trivialization.sphereBundle`: the chart of `S(E) → B` induced by a norm-preserving
  chart of `E`.
* `TauCeti.sphereBundleProj`: the projection `S(E) → B`.
* `TauCeti.exists_trivialization_sphereBundleProj`: the sphere bundle of a continuous Riemannian
  bundle of finite rank is locally trivial.
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

section Proj

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

/-- The projection `S(E) → B` of the unit sphere bundle of a bundle with normed fibres. -/
def sphereBundleProj : C(sphereBundle F E, B) :=
  ⟨fun v ↦ (v : TotalSpace F E).proj, (FiberBundle.continuous_proj F E).comp continuous_subtype_val⟩

@[simp]
theorem sphereBundleProj_apply (v : sphereBundle F E) :
    sphereBundleProj F E v = (v : TotalSpace F E).proj :=
  (rfl)

end Proj

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

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  (e : Trivialization F (π F E)) (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖)

include he in
/-- A norm-preserving chart sends unit vectors over its base set to unit vectors. -/
private theorem norm_apply_snd_of_mem_sphereBundle {v : TauCeti.sphereBundle F E}
    (hv : (v : TotalSpace F E).proj ∈ e.baseSet) : ‖(e v).2‖ = 1 :=
  (he _ hv (v : TotalSpace F E).2).trans (mem_sphereBundle.1 v.2)

include he in
/-- The inverse of a norm-preserving chart sends unit vectors over its base set to unit
vectors. -/
private theorem norm_symm_snd {b : B} (hb : b ∈ e.baseSet) (w : sphere (0 : F) 1) :
    ‖(e.toOpenPartialHomeomorph.symm (b, (w : F))).2‖ = 1 := by
  set z := e.toOpenPartialHomeomorph.symm (b, (w : F))
  have hz : z.proj = b := e.symm_coe_proj hb
  have hez : e z = (b, (w : F)) := e.apply_symm_apply (e.mk_mem_target.2 hb)
  rw [← he _ (hz ▸ hb) z.2, ← norm_eq_of_mem_sphere w]
  exact congrArg (‖·.2‖) hez

variable [NormedSpace ℝ F] [∀ b, NormedSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

open scoped Classical in
/-- The fibre coordinate of the chart of the sphere bundle: `e` over its base set, and an arbitrary
unit vector elsewhere. -/
private def sphereBundleCoord (v : TauCeti.sphereBundle F E) : sphere (0 : F) 1 :=
  if hv : (v : TotalSpace F E).proj ∈ e.baseSet then
    ⟨(e v).2, mem_sphere_zero_iff_norm.2 (e.norm_apply_snd_of_mem_sphereBundle he hv)⟩
  else Classical.choice (nonempty_sphere_of_sphereBundle v)

private theorem coe_sphereBundleCoord {v : TauCeti.sphereBundle F E}
    (hv : (v : TotalSpace F E).proj ∈ e.baseSet) :
    (e.sphereBundleCoord he v : F) = (e v).2 := by
  simp only [sphereBundleCoord, hv, ↓reduceDIte]

open scoped Classical in
/-- The inverse of the chart of the sphere bundle: the inverse of `e` over its base set, and an
arbitrary unit vector elsewhere. -/
private def sphereBundleInv (p : B × sphere (0 : F) 1) : TauCeti.sphereBundle F E :=
  if hp : p.1 ∈ e.baseSet then
    ⟨e.toOpenPartialHomeomorph.symm (p.1, p.2), mem_sphereBundle.2 (e.norm_symm_snd he hp p.2)⟩
  else Classical.choice (nonempty_sphereBundle p.1 p.2)

private theorem coe_sphereBundleInv {p : B × sphere (0 : F) 1} (hp : p.1 ∈ e.baseSet) :
    (e.sphereBundleInv he p : TotalSpace F E) = e.toOpenPartialHomeomorph.symm (p.1, p.2) := by
  simp only [sphereBundleInv, hp, ↓reduceDIte]

/-- **The chart of the sphere bundle induced by a norm-preserving chart.** A bundle chart `e` of
`E` whose fibre maps preserve norms restricts to a chart of the projection `S(E) → B` from the unit
sphere bundle, with fibre the unit sphere of the model fibre and the same base set. -/
def sphereBundle : Trivialization (sphere (0 : F) 1) (sphereBundleProj F E) where
  toFun v := (sphereBundleProj F E v, e.sphereBundleCoord he v)
  invFun := e.sphereBundleInv he
  source := sphereBundleProj F E ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hv := ⟨hv, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, sphereBundleProj_apply, e.coe_sphereBundleInv he hp.1, e.symm_coe_proj hp.1]
    exact hp.1
  left_inv' v hv := by
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := hv
    apply Subtype.ext
    rw [e.coe_sphereBundleInv he hv', e.coe_sphereBundleCoord he hv', sphereBundleProj_apply,
      ← e.coe_fst (e.mem_source.2 hv')]
    exact e.symm_apply_apply (e.mem_source.2 hv')
  right_inv' p hp := by
    have hp' : p.1 ∈ e.baseSet := hp.1
    have hsymm := e.coe_sphereBundleInv he hp'
    have hz : (e.sphereBundleInv he p : TotalSpace F E).proj = p.1 := by
      rw [hsymm, e.symm_coe_proj hp']
    refine Prod.ext hz (Subtype.ext ?_)
    rw [e.coe_sphereBundleCoord he (by rwa [hz]), hsymm,
      e.apply_symm_apply (e.mk_mem_target.2 hp')]
  open_source := e.open_baseSet.preimage (sphereBundleProj F E).continuous
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    -- Read the second coordinate in the model fibre, where the map is `e`.
    rw [(IsInducing.id.prodMap IsInducing.subtypeVal).continuousOn_iff]
    refine (e.continuousOn.comp continuous_subtype_val.continuousOn fun v hv ↦
      e.mem_source.2 hv).congr fun v hv ↦ ?_
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := hv
    exact Prod.ext (e.coe_fst (e.mem_source.2 hv')).symm (e.coe_sphereBundleCoord he hv')
  continuousOn_invFun := by
    -- Read the value in the total space of `E`, where the map is the inverse of `e`.
    rw [IsInducing.subtypeVal.continuousOn_iff]
    refine (e.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_id.prodMap continuous_subtype_val).continuousOn
        fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ e.mk_mem_target.2 hp.1).congr
      fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ e.coe_sphereBundleInv he hp.1
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem sphereBundle_baseSet : (e.sphereBundle he).baseSet = e.baseSet :=
  (rfl)

/-- Over its base set, the chart of the sphere bundle reads a unit vector in the chart `e`. -/
@[simp]
theorem coe_sphereBundle_apply_snd {v : TauCeti.sphereBundle F E}
    (hv : (v : TotalSpace F E).proj ∈ e.baseSet) :
    ((e.sphereBundle he v).2 : F) = (e v).2 :=
  e.coe_sphereBundleCoord he hv

/-- Over its base set, the inverse chart of the sphere bundle is the inverse of `e`. -/
@[simp]
theorem coe_sphereBundle_symm_apply {b : B} (hb : b ∈ e.baseSet) (w : sphere (0 : F) 1) :
    ((e.sphereBundle he).toOpenPartialHomeomorph.symm (b, w) : TotalSpace F E) =
      e.toOpenPartialHomeomorph.symm (b, w) :=
  e.coe_sphereBundleInv he (p := (b, w)) hb

end Bundle.Trivialization

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

section FiniteDimensional

variable [FiniteDimensional ℝ F]

variable (F E) in
/-- **The sphere bundle of a Riemannian vector bundle is locally trivial.** For a continuous
Riemannian vector bundle with finite-dimensional model fibre `F`, every point of the base lies in
the base set of a chart of `S(E) → B` with fibre the unit sphere of `F`. No separation or
paracompactness assumption on the base is needed. -/
theorem exists_trivialization_sphereBundleProj (b : B) :
    ∃ e : Trivialization (sphere (0 : F) 1) (sphereBundleProj F E), b ∈ e.baseSet := by
  obtain ⟨e, -, hb, he⟩ := (stdOrthonormalBasis ℝ F).exists_orthonormal_trivialization (E := E) b
  exact ⟨e.sphereBundle he, hb⟩

variable (F E) in
/-- **The sphere bundle of a Riemannian vector bundle is a Serre fibration.** -/
theorem TopCat.mem_serreFibrations_sphereBundleProj :
    TopCat.serreFibrations (_root_.TopCat.ofHom (sphereBundleProj F E) :
      _root_.TopCat.of (sphereBundle F E) ⟶ _root_.TopCat.of B) :=
  TopCat.mem_serreFibrations_of_exists_trivialization (exists_trivialization_sphereBundleProj F E)

variable (F E) in
/-- **The sphere bundle of a Riemannian vector bundle over a normal paracompact base is a Hurewicz
fibration.** This includes every paracompact Hausdorff base. -/
theorem isHurewiczFibration_sphereBundleProj [NormalSpace B] [ParacompactSpace B] :
    IsHurewiczFibration.{v} (sphereBundleProj F E) :=
  isHurewiczFibration_of_exists_trivialization (exists_trivialization_sphereBundleProj F E)

end FiniteDimensional

variable (E) in
/-- **The `n`-sphere bundle of a Riemannian vector bundle is an `n`-connected map.** If the model
fibre `F` has dimension `n + 1`, the projection `S(E) → B`, whose fibres are `n`-spheres, induces
bijections on `πₖ` for `k < n`, path components included, and a surjection on `πₙ`. -/
theorem isNConnected_sphereBundleProj {n : ℕ} (hF : finrank ℝ F = n + 1) :
    (sphereBundleProj F E).IsNConnected n := by
  have := Module.finite_of_finrank_eq_succ hF
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  refine (TopCat.isNConnected_iff_of_mem_serreFibrations
    (TopCat.mem_serreFibrations_sphereBundleProj F E) n).2 fun b ↦ ?_
  -- Every fibre is homeomorphic to the unit sphere of `F`, which is `(n - 1)`-connected.
  obtain ⟨e, hb⟩ := exists_trivialization_sphereBundleProj F E b
  let h : sphereBundleProj F E ⁻¹' {b} ≃ₜ sphere (0 : F) 1 := e.preimageSingletonHomeomorph hb
  refine ⟨⟨h.symm ⟨_, (NormedSpace.sphere_nonempty.2 zero_le_one).some_mem⟩⟩,
    fun x k hk ↦ ?_⟩
  have := subsingleton_homotopyGroup_sphere_of_lt hF (N := Fin k) (by simpa using hk) (h x)
  exact (HomotopyGroup.homeomorphEquiv h x).subsingleton

variable (E) in
/-- **An `n`-sphere bundle with `n ≥ 2` is simply connected exactly when its base is.** If the
model fibre `F` of a Riemannian vector bundle has dimension `n + 1` with `n ≥ 2`, its unit sphere
bundle is simply connected exactly when the base is. -/
theorem simplyConnectedSpace_sphereBundle_iff {n : ℕ} (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n) :
    SimplyConnectedSpace (sphereBundle F E) ↔ SimplyConnectedSpace B :=
  (isNConnected_sphereBundleProj E hF).simplyConnectedSpace_iff hn

end TauCeti
