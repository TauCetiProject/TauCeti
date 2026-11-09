/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.IntegralAffine
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally integral affine maps and their structure groupoid

Integral affine maps agreeing on a nonempty open set have the same global
extension, including their integral lattice maps. Consequently a map locally
equal to integral affine equivalences on a connected open set extends uniquely
to one global integral affine equivalence. The associated Mathlib pregroupoid
and structure groupoid describe integral affine chart changes.

Adapted from `yuma-mizuno-lean/Mei`, commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/Geometry/Manifold/IntegralAffine/Basic.lean` (Apache 2.0).
-/

public section

open Set

namespace TauCeti.Toric

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

/-- On a set, a map is locally integral affine if near each point it agrees with
one global integral affine equivalence, after restriction to that set. -/
def IsLocallyIntegralAffineOn (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (f : V → W) (s : Set V) : Prop :=
  ∀ x ∈ s, ∃ e : IntegralAffineEquiv h h', ∃ u : Set V,
    IsOpen u ∧ x ∈ u ∧ EqOn f e (s ∩ u)

/-- The public local-witness characterization of integral affine maps on sets. -/
theorem isLocallyIntegralAffineOn_iff {f : V → W} {s : Set V} :
    IsLocallyIntegralAffineOn h h' f s ↔
      ∀ x ∈ s, ∃ e : IntegralAffineEquiv h h', ∃ u : Set V,
        IsOpen u ∧ x ∈ u ∧ EqOn f e (s ∩ u) := Iff.rfl

namespace IsLocallyIntegralAffineOn

/-- Restricting the domain preserves local integral affine witnesses. -/
theorem mono {f : V → W} {s t : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hts : t ⊆ s) :
    IsLocallyIntegralAffineOn h h' f t := by
  rw [isLocallyIntegralAffineOn_iff] at hf ⊢
  intro x hx
  obtain ⟨e, u, hu, hxu, he⟩ := hf x (hts hx)
  exact ⟨e, u, hu, hxu, fun y hy => he ⟨hts hy.1, hy.2⟩⟩

/-- A global integral affine equivalence is a local witness on every set. -/
theorem of_eqOn {f : V → W} {s : Set V} (e : IntegralAffineEquiv h h')
    (he : EqOn f e s) : IsLocallyIntegralAffineOn h h' f s := by
  rw [isLocallyIntegralAffineOn_iff]
  exact fun _ _ => ⟨e, univ, isOpen_univ, trivial, fun y hy => he hy.1⟩

/-- On a nonempty connected open domain, local integral affine witnesses glue to
one unique global integral affine equivalence. No connectedness of the image is assumed. -/
theorem existsUnique_extension {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hs : IsOpen s) (hc : IsConnected s) :
    ∃! e : IntegralAffineEquiv h h', EqOn f e s := by
  classical
  have hw := isLocallyIntegralAffineOn_iff.mp hf
  choose E U hU hxU hEq using fun x : s => hw x.val x.property
  have hE : IsLocallyConstant E := by
    apply (IsLocallyConstant.iff_exists_open E).mpr
    intro x
    refine ⟨Subtype.val ⁻¹' U x, (hU x).preimage continuous_subtype_val, hxU x, ?_⟩
    intro y hy
    apply IntegralAffineEquiv.eq_of_eqOn_open (hs.inter ((hU x).inter (hU y)))
      ⟨y.val, y.property, hy, hxU y⟩
    intro z hz
    exact (hEq y ⟨hz.1, hz.2.2⟩).symm.trans (hEq x ⟨hz.1, hz.2.1⟩)
  let b : LocallyConstant s (IntegralAffineEquiv h h') := ⟨E, hE⟩
  let : PreconnectedSpace s := Subtype.preconnectedSpace hc.isPreconnected
  obtain ⟨x, hx⟩ := hc.nonempty
  let e := E ⟨x, hx⟩
  have he : EqOn f e s := by
    intro y hy
    have hEy := b.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨x, hx⟩
    exact (hEq ⟨y, hy⟩ ⟨hy, hxU ⟨y, hy⟩⟩).trans
      (congrArg (fun a : IntegralAffineEquiv h h' => a y) hEy)
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact IntegralAffineEquiv.eq_of_eqOn_open hs hc.nonempty
    (fun y hy => (he' hy).symm.trans (he hy))

/-- Local integral affine maps compose on the actual common domain. -/
theorem comp {N'' U : Type*} [AddCommGroup N''] [NormedAddCommGroup U]
    [NormedSpace ℝ U] {i'' : N'' →+ U} {h'' : IsIntegralLattice i''}
    {f : V → W} {g : W → U} {s : Set V} {t : Set W}
    (hf : IsLocallyIntegralAffineOn h h' f s)
    (hg : IsLocallyIntegralAffineOn h' h'' g t) :
    IsLocallyIntegralAffineOn h h'' (g ∘ f) (s ∩ f ⁻¹' t) := by
  rw [isLocallyIntegralAffineOn_iff] at hf hg ⊢
  intro x hx
  obtain ⟨e, u, hu, hxu, he⟩ := hf x hx.1
  obtain ⟨e', v, hv, hxv, he'⟩ := hg (f x) hx.2
  refine ⟨e.trans e', u ∩ e ⁻¹' v, hu.inter (hv.preimage e.continuous),
    ⟨hxu, ?_⟩, ?_⟩
  · simpa only [Set.mem_preimage, ← he ⟨hx.1, hxu⟩] using hxv
  · intro y hy
    have hfy := he ⟨hy.1.1, hy.2.1⟩
    have hgy := he' ⟨hy.1.2, hfy.symm ▸ hy.2.2⟩
    simpa only [Function.comp_apply, IntegralAffineEquiv.trans_toAffineEquiv,
      AffineEquiv.trans_apply] using hgy.trans (congrArg e' hfy)

/-- Agreement on the domain preserves local integral affine witnesses. -/
theorem congr {f g : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hfg : EqOn f g s) :
    IsLocallyIntegralAffineOn h h' g s := by
  rw [isLocallyIntegralAffineOn_iff] at hf ⊢
  intro x hx
  obtain ⟨e, u, hu, hxu, he⟩ := hf x hx
  exact ⟨e, u, hu, hxu, fun y hy => (hfg hy.1).symm.trans (he hy)⟩

/-- Integral affine locality glues over arbitrary open neighborhoods of the domain points. -/
theorem locality {f : V → W} {s : Set V}
    (hf : ∀ x ∈ s, ∃ v : Set V, IsOpen v ∧ x ∈ v ∧
      IsLocallyIntegralAffineOn h h' f (s ∩ v)) :
    IsLocallyIntegralAffineOn h h' f s := by
  rw [isLocallyIntegralAffineOn_iff]
  intro x hx
  obtain ⟨v, hv, hxv, hf'⟩ := hf x hx
  obtain ⟨e, u, hu, hxu, he⟩ := isLocallyIntegralAffineOn_iff.mp hf' x ⟨hx, hxv⟩
  exact ⟨e, v ∩ u, hv.inter hu, ⟨hxv, hxu⟩,
    fun y hy => he ⟨⟨hy.1, hy.2.1⟩, hy.2.2⟩⟩

/-- Every connected component of an open domain has its own unique global extension. -/
theorem existsUnique_extension_connectedComponentIn {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hs : IsOpen s) {x : V} (hx : x ∈ s) :
    ∃! e : IntegralAffineEquiv h h', EqOn f e (connectedComponentIn s x) :=
  (hf.mono (connectedComponentIn_subset s x)).existsUnique_extension
    hs.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr hx)

/-- For an open partial homeomorphism, local integral affine witnesses on the
source supply the inverse witnesses on the target. -/
theorem symm {e : OpenPartialHomeomorph V W}
    (he : IsLocallyIntegralAffineOn h h' e e.source) :
    IsLocallyIntegralAffineOn h' h e.symm e.target := by
  rw [isLocallyIntegralAffineOn_iff] at he ⊢
  intro y hy
  obtain ⟨a, u, hu, hxu, ha⟩ := he (e.symm y) (e.map_target hy)
  refine ⟨a.symm, e.target ∩ e.symm ⁻¹' u,
    e.continuousOn_invFun.isOpen_inter_preimage e.open_target hu, ⟨hy, hxu⟩, ?_⟩
  intro z hz
  have haz : a (e.symm z) = z :=
    (ha ⟨e.map_target hz.1, hz.2.2⟩).symm.trans (e.right_inv hz.1)
  simpa only [IntegralAffineEquiv.symm_toAffineEquiv] using
    a.toAffineEquiv.eq_symm_apply.mpr haz

end IsLocallyIntegralAffineOn

/-- The pregroupoid of maps locally given by integral affine equivalences. -/
def integralAffinePregroupoid (h : IsIntegralLattice i) : Pregroupoid V where
  property := IsLocallyIntegralAffineOn h h
  comp hf hg _ _ _ := hf.comp hg
  id_mem := by
    apply IsLocallyIntegralAffineOn.of_eqOn (IntegralAffineEquiv.refl h)
    intro x _
    rw [IntegralAffineEquiv.refl_toAffineEquiv]
    rfl
  locality _ hf := .locality hf
  congr _ hgf hf := hf.congr (fun x hx => (hgf x hx).symm)

/-- The pregroupoid property is precisely the public local-witness predicate. -/
@[simp] theorem integralAffinePregroupoid_property_iff {f : V → V} {s : Set V} :
    (integralAffinePregroupoid h).property f s ↔ IsLocallyIntegralAffineOn h h f s := by
  rw [integralAffinePregroupoid]

/-- The structure groupoid for integral affine atlases, built on Mathlib's carrier. -/
def integralAffineGroupoid (h : IsIntegralLattice i) : StructureGroupoid V :=
  (integralAffinePregroupoid h).groupoid

/-- Membership requires local integral affine witnesses for both directions. -/
theorem mem_integralAffineGroupoid_iff {e : OpenPartialHomeomorph V V} :
    e ∈ integralAffineGroupoid h ↔
      IsLocallyIntegralAffineOn h h e e.source ∧
        IsLocallyIntegralAffineOn h h e.symm e.target := by
  rw [integralAffineGroupoid, mem_groupoid_of_pregroupoid]
  simp only [integralAffinePregroupoid_property_iff]

/-- Groupoid membership is exactly local integral affine behavior on the source;
the inverse condition follows from the partial homeomorphism laws. -/
@[simp] theorem mem_integralAffineGroupoid_iff_forward {e : OpenPartialHomeomorph V V} :
    e ∈ integralAffineGroupoid h ↔ IsLocallyIntegralAffineOn h h e e.source := by
  rw [mem_integralAffineGroupoid_iff]
  exact ⟨And.left, fun he => ⟨he, he.symm⟩⟩

/-- Restricting an integral affine chart change to an open set keeps it integral affine. -/
instance : ClosedUnderRestriction (integralAffineGroupoid h) where
  closedUnderRestriction {e} he s hs := by
    rw [mem_integralAffineGroupoid_iff_forward] at he ⊢
    rw [e.restr_source' s hs]
    exact he.mono inter_subset_left

/-- A global integral affine equivalence, as a partial homeomorphism on the whole
space, is an integral affine chart change. -/
theorem IntegralAffineEquiv.mem_integralAffineGroupoid (e : IntegralAffineEquiv h h) :
    e.toContinuousAffineEquiv.toHomeomorph.toOpenPartialHomeomorph ∈
      integralAffineGroupoid h :=
  mem_integralAffineGroupoid_iff_forward.mpr <|
    .of_eqOn e fun x _ => e.toContinuousAffineEquiv_apply x

/-- A connected nonempty chart-change domain has a unique global integral affine extension. -/
theorem existsUnique_extension_of_mem_integralAffineGroupoid
    {e : OpenPartialHomeomorph V V} (he : e ∈ integralAffineGroupoid h)
    (hc : IsConnected e.source) :
    ∃! a : IntegralAffineEquiv h h, EqOn e a e.source :=
  (mem_integralAffineGroupoid_iff.mp he).1.existsUnique_extension e.open_source hc

/-- Each connected component of the source of a chart change has a unique global integral
affine extension. -/
theorem existsUnique_extension_connectedComponentIn_of_mem_integralAffineGroupoid
    {e : OpenPartialHomeomorph V V} (he : e ∈ integralAffineGroupoid h) {x : V}
    (hx : x ∈ e.source) :
    ∃! a : IntegralAffineEquiv h h, EqOn e a (connectedComponentIn e.source x) :=
  (mem_integralAffineGroupoid_iff.mp he).1.existsUnique_extension_connectedComponentIn
    e.open_source hx

end TauCeti.Toric
