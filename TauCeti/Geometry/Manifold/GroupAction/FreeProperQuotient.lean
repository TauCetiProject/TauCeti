/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Free
public import TauCeti.Geometry.Manifold.GroupAction.Orbit
public import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Manifold.Submersion.Split
public import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# The quotient manifold theorem for free proper actions

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on a
finite-dimensional boundaryless manifold `M`. This file proves that the orbit space `M ⧸ G`, with
its quotient topology, carries charts modelled on `ℝ^(dim M - dim G)` making it a smooth manifold
for which the orbit projection `M → M ⧸ G` is a submersion
(`TauCeti.exists_freeProperQuotient_isSubmersion`).

The charts are built from slices. A *slice tube* is a smooth map `σ : S → M` and an open set
`U ⊆ S` such that the slice map `Φ (g, s) = g • σ s` is injective on `G × U` and a local
diffeomorphism at each of its points. Then:

* `Φ` identifies `G × U` with the open invariant set `Φ (G × U)`, and the map
  `ψ s = ⟦σ s⟧ : U → M ⧸ G` is injective (`MulAction.injOn_smul_univ_prod_iff`) and open, since
  `ψ '' O` is the image of the open set `Φ (G × O)` under the open orbit projection. So `ψ` is an
  open partial homeomorphism `TauCeti.sliceOrbitPartialHomeomorph` with source `U`.
* For two slice tubes the change of orbit charts `ψ₂⁻¹ ∘ ψ₁` is, near each point of its domain,
  `s ↦ pr₂ (Φ₂⁻¹ (σ₁ s))`, so it is smooth
  (`TauCeti.contMDiffOn_sliceOrbitPartialHomeomorph_symm_comp`).
* On `Φ (G × U)` the orbit projection is `z ↦ ψ (pr₂ (Φ⁻¹ z))`, and `⟦·⟧ ∘ Φ = ψ ∘ pr₂`.

Slice tubes exist through every point of a free proper action
(`TauCeti.exists_sliceTube_of_stabilizer_eq_bot`). A free point is locally free, so the chart
slice `v ↦ φ⁻¹ (φ x + L v)` along a linear parametrization `L` of a complement of the orbit tangent
space `𝔤 · x` makes `Φ` a local diffeomorphism at `(1, 0)`
(`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`). This persists along `G × U` for `U` near
`0` (`IsLocalDiffeomorphAt.eventually_forall_smul_slice`), and properness makes `Φ` injective on
`G × U` after shrinking `U` (`ProperSMul.exists_mem_nhds_injOn_smul_slice`). The complement has
dimension `dim M - dim G`, so every slice is parametrized by the same model space.

Neither Hausdorffness nor second countability of `M` or `G` is used, and `M` may be empty. The
charted space `TauCeti.freeProperChartedSpace` is a definition rather than an instance, since
discrete groups acting properly discontinuously already carry the pushed-forward charts of
`MulAction.instChartedSpaceQuotient`, with a different model space.

## Main definitions

* `TauCeti.sliceOrbitPartialHomeomorph`: the orbit chart `s ↦ ⟦σ s⟧` of a slice tube.
* `TauCeti.freeProperChartedSpace`: the charts on the orbit space of a free proper action given by
  inverses of orbit charts of chosen slice tubes.

## Main results

* `IsLocalDiffeomorphAt.exists_sliceTube`: a transverse slice through a free point of a proper
  action can be shrunk to a slice tube.
* `TauCeti.contMDiffOn_sliceOrbitPartialHomeomorph_symm_comp`: orbit charts of slice tubes are
  smoothly compatible.
* `TauCeti.isManifold_freeProperChartedSpace`: the orbit space of a free proper action is a smooth
  manifold.
* `TauCeti.isSubmersion_quotientMk_freeProperChartedSpace`: the orbit projection is a submersion.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: the quotient manifold theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.10 (the
  quotient manifold theorem) and its proof.
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21 and its proof.
-/

public section

noncomputable section

open Function Set Filter Manifold Topology MulAction
open scoped ContDiff Manifold

namespace TauCeti

section SliceTube

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {S : Type*} [TopologicalSpace S] [ChartedSpace K S]
  {σ : S → M} {U : Set S}

/-- **Slice tubes from transverse slices.** If the slice map `(g, s) ↦ g • σ s` of a proper action
is a local diffeomorphism at `(1, s₀)` and `σ s₀` has trivial stabilizer, then for some open
neighbourhood `U` of `s₀` the slice map is injective on the tube `G × U` and a local
diffeomorphism at each point of it. -/
theorem _root_.IsLocalDiffeomorphAt.exists_sliceTube [LieGroup I ∞ G] [ContMDiffSMul I I' ∞ G M]
    [ProperSMul G M] {s₀ : S}
    (h : IsLocalDiffeomorphAt (I.prod J) I' ∞ (fun p : G × S ↦ p.1 • σ p.2) (1, s₀))
    (hfree : stabilizer G (σ s₀) = ⊥) :
    ∃ U : Set S, IsOpen U ∧ s₀ ∈ U ∧ InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (I.prod J) I' ∞ (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  have hσ : ContinuousAt σ s₀ := by
    have hcont := h.contMDiffAt.continuousAt.comp
      (f := fun s : S ↦ ((1 : G), s)) (continuous_const.prodMk continuous_id).continuousAt
    simpa only [comp_def, one_smul] using hcont
  obtain ⟨N, hN, hinjN⟩ := h.exists_mem_nhds_injOn
  obtain ⟨U₁, hU₁, hinj₁⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice hσ hfree hN hinjN
  obtain ⟨U, hsub, hU, hs₀⟩ := mem_nhds_iff.mp (inter_mem hU₁ h.eventually_forall_smul_slice)
  refine ⟨U, hU, hs₀, hinj₁.mono (prod_mono subset_rfl fun s hs ↦ (hsub hs).1), ?_⟩
  rintro ⟨⟨g, s⟩, -, hs⟩
  exact (hsub hs).2 g

omit [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace S] in
/-- On a tube where the slice map is injective, the orbit through `σ s` determines `s`. -/
theorem injOn_quotientMk_slice (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    InjOn (fun s ↦ Quotient.mk (orbitRel G M) (σ s)) U :=
  (MulAction.injOn_smul_univ_prod_iff.mp hinj).2

omit [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace S] in
/-- The orbit of a point of the image of a slice tube is the orbit of the slice point read off
from the inverse of the slice map. -/
theorem quotientMk_slice_snd_invFunOn [Nonempty S] {z : M}
    (hz : z ∈ (fun p : G × S ↦ p.1 • σ p.2) '' (univ ×ˢ U)) :
    Quotient.mk (orbitRel G M) (σ (invFunOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) z).2) =
      Quotient.mk (orbitRel G M) z := by
  set q := invFunOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) z
  have hq : q.1 • σ q.2 = z := invFunOn_eq (f := fun p : G × S ↦ p.1 • σ p.2) hz
  rw [← hq]
  exact (Quotient.sound (orbitRel_apply.mpr (mem_orbit _ q.1))).symm

/-- On the image of a slice tube, the slice coordinate `pr₂ (Φ⁻¹ z)` of a point `z` is smooth. -/
theorem contMDiffOn_snd_invFunOn_slice [Nonempty S] (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    (hΦ : IsLocalDiffeomorphOn (I.prod J) I' ∞ (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    ContMDiffOn I' J ∞ (fun z ↦ (invFunOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) z).2)
      ((fun p : G × S ↦ p.1 • σ p.2) '' (univ ×ˢ U)) :=
  contMDiff_snd.comp_contMDiffOn (hΦ.contMDiffOn_invFunOn (isOpen_univ.prod hU) hinj)

/-- The image of a slice tube is open. -/
theorem isOpen_image_slice (hU : IsOpen U)
    (hΦ : IsLocalDiffeomorphOn (I.prod J) I' ∞ (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    IsOpen ((fun p : G × S ↦ p.1 • σ p.2) '' (univ ×ˢ U)) :=
  hΦ.isLocalHomeomorphOn.isOpen_image (isOpen_univ.prod hU)

/-- For a slice tube, the image of an open subset `O` of `U` under `s ↦ ⟦σ s⟧` is open: it is the
image under the open orbit projection of the open set `Φ (G × O)`. -/
theorem isOpen_image_quotientMk_slice [ContinuousConstSMul G M]
    (hΦ : IsLocalDiffeomorphOn (I.prod J) I' ∞ (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    {O : Set S} (hO : IsOpen O) (hOU : O ⊆ U) :
    IsOpen ((fun s ↦ Quotient.mk (orbitRel G M) (σ s)) '' O) := by
  have himage : (fun s ↦ Quotient.mk (orbitRel G M) (σ s)) '' O =
      Quotient.mk (orbitRel G M) '' ((fun p : G × S ↦ p.1 • σ p.2) '' (univ ×ˢ O)) := by
    ext q
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨σ s, ⟨(1, s), ⟨mem_univ _, hs⟩, one_smul G (σ s)⟩, rfl⟩
    · rintro ⟨_, ⟨⟨g, s⟩, ⟨-, hs⟩, rfl⟩, rfl⟩
      exact ⟨s, hs, (Quotient.sound (orbitRel_apply.mpr (mem_orbit _ g))).symm⟩
  rw [himage]
  refine isOpenMap_quotient_mk'_mul _ ?_
  exact isOpen_image_slice hO fun p ↦ hΦ ⟨p, ⟨p.2.1, hOU p.2.2⟩⟩

variable [ContMDiffSMul I I' ∞ G M] [Nonempty S]

variable (σ) in
/-- **The orbit chart of a slice tube.** For a slice tube `(σ, U)`, the map `s ↦ ⟦σ s⟧` is an open
partial homeomorphism from the slice manifold to the orbit space, with source `U`. -/
def sliceOrbitPartialHomeomorph (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    (hΦ : IsLocalDiffeomorphOn (I.prod J) I' ∞ (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    OpenPartialHomeomorph S (orbitRel.Quotient G M) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((injOn_quotientMk_slice hinj).toPartialEquiv _ U)
    (by
      refine continuous_quotient_mk'.comp_continuousOn ?_
      refine hΦ.contMDiffOn.continuousOn.comp (f := fun s : S ↦ ((1 : G), s))
        (continuous_const.prodMk continuous_id).continuousOn (fun s hs ↦ ⟨mem_univ _, hs⟩)
        |>.congr fun s _ ↦ (one_smul G (σ s)).symm)
    (by
      have : ContinuousConstSMul G M :=
        (ContMDiffSMul.continuousSMul (I := I) (I' := I') ∞).continuousConstSMul
      intro O hO
      rw [domRestrict_eq, image_comp]
      exact isOpen_image_quotientMk_slice hΦ (hU.isOpenMap_subtype_val O hO)
        (Subtype.coe_image_subset U O))
    hU

variable {hU : IsOpen U} {hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)}
  {hΦ : IsLocalDiffeomorphOn (I.prod J) I' ∞ (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)}

/-- The orbit chart of a slice tube sends `s` to the orbit of `σ s`. -/
@[simp]
theorem sliceOrbitPartialHomeomorph_apply (s : S) :
    sliceOrbitPartialHomeomorph σ hU hinj hΦ s = Quotient.mk (orbitRel G M) (σ s) := (rfl)

/-- The orbit chart of a slice tube is defined on the slice parameters `U` of the tube. -/
@[simp]
theorem sliceOrbitPartialHomeomorph_source :
    (sliceOrbitPartialHomeomorph σ hU hinj hΦ).source = U :=
  (rfl)

/-- The orbit chart of a slice tube takes values in the orbits through the slice. -/
@[simp]
theorem sliceOrbitPartialHomeomorph_target :
    (sliceOrbitPartialHomeomorph σ hU hinj hΦ).target =
      (fun s ↦ Quotient.mk (orbitRel G M) (σ s)) '' U :=
  (rfl)

/-- On the image of a slice tube, the inverse orbit chart of the orbit of `z` is the slice
coordinate `pr₂ (Φ⁻¹ z)`. -/
theorem sliceOrbitPartialHomeomorph_symm_quotientMk {z : M}
    (hz : z ∈ (fun p : G × S ↦ p.1 • σ p.2) '' (univ ×ˢ U)) :
    (sliceOrbitPartialHomeomorph σ hU hinj hΦ).symm (Quotient.mk (orbitRel G M) z) =
      (invFunOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) z).2 := by
  have hmem : (invFunOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) z).2 ∈ U :=
    (invFunOn_mem (f := fun p : G × S ↦ p.1 • σ p.2) hz).2
  rw [← quotientMk_slice_snd_invFunOn hz, ← sliceOrbitPartialHomeomorph_apply (hU := hU)
    (hinj := hinj) (hΦ := hΦ)]
  exact (sliceOrbitPartialHomeomorph σ hU hinj hΦ).left_inv hmem

variable {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace K S₂] [Nonempty S₂]
  {σ₂ : S₂ → M} {U₂ : Set S₂} {hU₂ : IsOpen U₂}
  {hinj₂ : InjOn (fun p : G × S₂ ↦ p.1 • σ₂ p.2) (univ ×ˢ U₂)}
  {hΦ₂ : IsLocalDiffeomorphOn (I.prod J) I' ∞ (fun p : G × S₂ ↦ p.1 • σ₂ p.2) (univ ×ˢ U₂)}

/-- **Orbit charts of slice tubes are smoothly compatible.** For two slice tubes, the change of
orbit charts `ψ₂⁻¹ ∘ ψ₁` is smooth on its domain: near each point it is
`s ↦ pr₂ (Φ₂⁻¹ (σ₁ s))`. -/
theorem contMDiffOn_sliceOrbitPartialHomeomorph_symm_comp :
    ContMDiffOn J J ∞
      ((sliceOrbitPartialHomeomorph σ₂ hU₂ hinj₂ hΦ₂).symm ∘
        sliceOrbitPartialHomeomorph σ hU hinj hΦ)
      ((sliceOrbitPartialHomeomorph σ hU hinj hΦ).trans
        (sliceOrbitPartialHomeomorph σ₂ hU₂ hinj₂ hΦ₂).symm).source := by
  set Φ₂ := fun p : G × S₂ ↦ p.1 • σ₂ p.2
  rintro s ⟨hs, hs₂⟩
  simp only [mem_preimage, OpenPartialHomeomorph.symm_source, sliceOrbitPartialHomeomorph_target]
    at hs₂
  -- The orbit of `σ s` meets the second slice, so `σ s` lies in the image of the second tube.
  obtain ⟨w, hw, hws⟩ := hs₂
  obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.exact hws.symm)
  have hσs : σ s ∈ Φ₂ '' (univ ×ˢ U₂) := ⟨(g, w), ⟨mem_univ _, hw⟩, hg⟩
  -- The first slice is smooth at `s`.
  have hσ : ContMDiffAt J I' ∞ σ s := by
    have hcomp := (hΦ ⟨(1, s), ⟨mem_univ _, hs⟩⟩).contMDiffAt.comp s
      (contMDiffAt_const.prodMk contMDiffAt_id)
    simpa only [comp_def, one_smul] using hcomp
  have hopen := (isOpen_image_slice hU₂ hΦ₂).mem_nhds hσs
  have hsmooth : ContMDiffAt J J ∞ (fun s' ↦ (invFunOn Φ₂ (univ ×ˢ U₂) (σ s')).2) s :=
    ((contMDiffOn_snd_invFunOn_slice hU₂ hinj₂ hΦ₂).contMDiffAt hopen).comp s hσ
  refine (hsmooth.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hσ.continuousAt.preimage_mem_nhds hopen] with s' hs'
  exact sliceOrbitPartialHomeomorph_symm_quotientMk hs'

end SliceTube

section Quotient

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ProperSMul G M]

/-- **Slice tubes through free points.** Through every point `x` with trivial stabilizer of a
smooth proper action there is a slice tube parametrized by `ℝ^(dim M - dim G)`: a map `σ` with
`σ 0 = x` and an open neighbourhood `U` of `0` such that `(g, v) ↦ g • σ v` is injective on
`G × U` and a local diffeomorphism at each point of it. -/
theorem exists_sliceTube_of_stabilizer_eq_bot {x : M} (hx : stabilizer G x = ⊥) :
    ∃ σ : (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) → M,
      ∃ U : Set (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ),
      σ 0 = x ∧ IsOpen U ∧ 0 ∈ U ∧ InjOn (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
        IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ))
          I' ∞ (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : CompleteSpace E' := FiniteDimensional.complete ℝ E'
  set F := Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  -- A free point is locally free.
  have hloc : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
    have : Subsingleton (stabilizer G x) := by
      rw [hx]
      infer_instance
    exact (Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := I) (I' := I')).1
      inferInstance
  -- Parametrize a complement `W` of the orbit tangent space by `F`.
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ E',
      IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) W :=
    Submodule.exists_isCompl _
  have hdim : Module.finrank ℝ F = Module.finrank ℝ W := by
    have h₁ := Submodule.finrank_add_eq_of_isCompl hW
    rw [InfinitesimalAction.finrank_orbitTangent_of_isotropy_eq_bot _ _ hloc] at h₁
    -- The Lie algebra of `G` is the model space `E`.
    have h₂ : Module.finrank ℝ (GroupLieAlgebra I G) = Module.finrank ℝ E := rfl
    have h₃ : Module.finrank ℝ (TangentSpace I' x) = Module.finrank ℝ E' := rfl
    rw [Module.finrank_fin_fun, ← h₃, ← h₁, h₂, Nat.add_sub_cancel_left]
    rfl
  let e : F ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq hdim
  -- The chart slice `v ↦ φ⁻¹ (φ x + L v)`, where `L` parametrizes `W` by `F`.
  set φ := extChartAt I' x
  let L : F →L[ℝ] E' := W.subtypeL.comp (e : F →L[ℝ] W)
  let σ : F → M := fun v ↦ φ.symm (φ x + L v)
  have hrange : LinearMap.range (L : F →ₗ[ℝ] E') = W :=
    (LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 e.surjective)).trans
      W.range_subtype
  have h₁ : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, F)) I' ∞ (fun p : G × F ↦ p.1 • σ p.2) (1, 0) :=
    isLocalDiffeomorphAt_smul_extChartAt_symm (G := G) hloc
      (W.injective_subtype.comp e.injective) (hrange ▸ hW)
  have hσ₀ : σ 0 = x := by simp [σ, φ]
  obtain ⟨U, hU, h0, hinj, hΦ⟩ := h₁.exists_sliceTube (by rwa [hσ₀])
  exact ⟨σ, U, hσ₀, hU, h0, hinj, hΦ⟩

variable (I I') in
/-- The orbit chart at `x` of a free proper action: the inverse of the orbit chart of a chosen slice
tube through `x`, parametrized by `ℝ^(dim M - dim G)`. -/
def freeProperSliceChart (hfree : ∀ x : M, stabilizer G x = ⊥) (x : M) :
    OpenPartialHomeomorph (orbitRel.Quotient G M)
      (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) :=
  have h := exists_sliceTube_of_stabilizer_eq_bot (I := I) (I' := I') (hfree x)
  (sliceOrbitPartialHomeomorph h.choose h.choose_spec.choose_spec.2.1
    h.choose_spec.choose_spec.2.2.2.1 h.choose_spec.choose_spec.2.2.2.2).symm

/-- Every orbit chart of a free proper action is the inverse of the orbit chart of a slice tube
whose slice passes through the base point. -/
theorem exists_freeProperSliceChart_eq (hfree : ∀ x : M, stabilizer G x = ⊥) (x : M) :
    ∃ (σ : (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) → M)
      (U : Set (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ)) (hU : IsOpen U)
      (hinj : InjOn (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U))
      (hΦ : IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ))
        I' ∞ (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U)),
      σ 0 = x ∧ 0 ∈ U ∧
        freeProperSliceChart I I' hfree x = (sliceOrbitPartialHomeomorph σ hU hinj hΦ).symm := by
  have h := exists_sliceTube_of_stabilizer_eq_bot (I := I) (I' := I') (hfree x)
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2.1,
    h.choose_spec.choose_spec.2.2.2.1, h.choose_spec.choose_spec.2.2.2.2,
    h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2.2.1, rfl⟩

variable (I I') in
/-- **The charts of the orbit space of a free proper action.** The chart at an orbit `q` is the
orbit chart `TauCeti.freeProperSliceChart` at the representative `q.out`; the atlas consists of
the orbit charts at all points. This is not an instance: see the module docstring. -/
@[instance_reducible]
def freeProperChartedSpace (hfree : ∀ x : M, stabilizer G x = ⊥) :
    ChartedSpace (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) (orbitRel.Quotient G M) where
  atlas := range (freeProperSliceChart I I' hfree)
  chartAt q := freeProperSliceChart I I' hfree q.out
  mem_chart_source q := by
    obtain ⟨σ, U, hU, hinj, hΦ, hσ₀, h0, heq⟩ :=
      exists_freeProperSliceChart_eq (I := I) (I' := I') hfree q.out
    rw [heq, OpenPartialHomeomorph.symm_source, sliceOrbitPartialHomeomorph_target]
    exact ⟨0, h0, by simp only [hσ₀, Quotient.out_eq]⟩
  chart_mem_atlas q := mem_range_self _

/-- **The orbit space of a free proper action is a smooth manifold**, for the charts of
`TauCeti.freeProperChartedSpace`. -/
theorem isManifold_freeProperChartedSpace (hfree : ∀ x : M, stabilizer G x = ⊥) :
    letI := freeProperChartedSpace I I' hfree
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) ∞
      (orbitRel.Quotient G M) := by
  let := freeProperChartedSpace I I' hfree
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  obtain ⟨σ, U, hU, hinj, hΦ, -, -, hx⟩ :=
    exists_freeProperSliceChart_eq (I := I) (I' := I') hfree x
  obtain ⟨σ₂, U₂, hU₂, hinj₂, hΦ₂, -, -, hy⟩ :=
    exists_freeProperSliceChart_eq (I := I) (I' := I') hfree y
  rw [hx, hy, OpenPartialHomeomorph.symm_symm]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, CompTriple.comp_eq,
    preimage_id_eq, id_eq, range_id, inter_univ]
  exact contMDiffOn_iff_contDiffOn.mp contMDiffOn_sliceOrbitPartialHomeomorph_symm_comp

/-- **The orbit projection of a free proper action is a submersion**, for the manifold structure of
`TauCeti.freeProperChartedSpace`. -/
theorem isSubmersion_quotientMk_freeProperChartedSpace (hfree : ∀ x : M, stabilizer G x = ⊥) :
    letI := freeProperChartedSpace I I' hfree
    IsSubmersion I' 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) ∞
      (Quotient.mk (orbitRel G M)) := by
  let := freeProperChartedSpace I I' hfree
  have := isManifold_freeProperChartedSpace (I := I) (I' := I') hfree
  set F := Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ
  -- Near `y`, read the projection through the slice tube of the chart at the orbit of `y`.
  have key : ∀ y : M, ContMDiffAt I' 𝓘(ℝ, F) ∞ (Quotient.mk (orbitRel G M)) y ∧
      Surjective (mfderiv I' 𝓘(ℝ, F) (Quotient.mk (orbitRel G M)) y) := by
    intro y
    obtain ⟨σ, U, hU, hinj, hΦ, hσ₀, h0, heq⟩ :=
      exists_freeProperSliceChart_eq (I := I) (I' := I') hfree (Quotient.mk (orbitRel G M) y).out
    set ψ := sliceOrbitPartialHomeomorph σ hU hinj hΦ
    set Φ := fun p : G × F ↦ p.1 • σ p.2
    have hψ : ψ.symm ∈ atlas F (orbitRel.Quotient G M) := ⟨_, heq⟩
    -- The orbit chart `ψ` is a local diffeomorphism on `U`, as the inverse of a chart.
    have hψd : ∀ s ∈ U, IsLocalDiffeomorphAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ ψ s := fun s hs ↦ by
      simpa only [OpenPartialHomeomorph.symm_symm] using
        ψ.symm.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas hψ) (by simpa [ψ] using hs)
    -- `y` lies in the image of the tube.
    have hy : y ∈ Φ '' (univ ×ˢ U) := by
      obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.exact (Quotient.out_eq
        (Quotient.mk (orbitRel G M) y)).symm)
      exact ⟨(g, 0), ⟨mem_univ _, h0⟩, by simp [Φ, hσ₀, hg]⟩
    set p := invFunOn Φ (univ ×ˢ U) y
    have hp : p ∈ univ ×ˢ U := invFunOn_mem (f := Φ) hy
    have hΦp : Φ p = y := invFunOn_eq (f := Φ) hy
    have hopen := (isOpen_image_slice hU hΦ).mem_nhds hy
    refine ⟨?_, ?_⟩
    · -- On the image of the tube, the projection is `ψ ∘ pr₂ ∘ Φ⁻¹`.
      have hsmooth : ContMDiffAt I' 𝓘(ℝ, F) ∞ (fun z ↦ ψ (invFunOn Φ (univ ×ˢ U) z).2) y :=
        (hψd _ hp.2).contMDiffAt.comp y
          ((contMDiffOn_snd_invFunOn_slice hU hinj hΦ).contMDiffAt hopen)
      refine hsmooth.congr_of_eventuallyEq ?_
      filter_upwards [hopen] with z hz
      exact (quotientMk_slice_snd_invFunOn hz).symm
    · -- The projection composed with `Φ` is `ψ ∘ pr₂`, whose differential is onto.
      have hcomp : Quotient.mk (orbitRel G M) ∘ Φ = ψ ∘ Prod.snd := funext fun q ↦
        Quotient.sound (orbitRel_apply.mpr (mem_orbit (σ q.2) q.1))
      have hrange := (hΦ ⟨p, hp⟩).range_mfderiv_comp (K := 𝓘(ℝ, F))
        (g := Quotient.mk (orbitRel G M))
        (by simp)
      rw [hcomp, hΦp] at hrange
      have hψp := hψd _ hp.2
      rw [mfderiv_comp p (hψp.mdifferentiableAt (by simp)) mdifferentiableAt_snd, mfderiv_snd]
        at hrange
      refine LinearMap.range_eq_top.mp ?_
      rw [← hrange]
      refine LinearMap.range_eq_top.mpr fun v ↦ ?_
      obtain ⟨u, hu⟩ := (hψp.isInvertible_mfderiv (by simp)).surjective v
      exact ⟨(0, u), hu⟩
  exact (ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv (fun y ↦ (key y).1)
    (by simp) fun y ↦ (key y).2).isSubmersion

variable (I) in
include I in
/-- **The quotient manifold theorem for free proper actions.** Let a finite-dimensional real Lie
group `G` act smoothly, freely and properly on a finite-dimensional boundaryless manifold `M`.
Then the orbit space, with its quotient topology, admits charts modelled on `ℝ^(dim M - dim G)`
making it a smooth manifold for which the orbit projection is a submersion. -/
theorem exists_freeProperQuotient_isSubmersion (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    ∃ _ : ChartedSpace (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ)
        (orbitRel.Quotient G M),
      IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) ∞
          (orbitRel.Quotient G M) ∧
        IsSubmersion I' 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) ∞
          (Quotient.mk (orbitRel G M)) := by
  have hstab : ∀ x : M, stabilizer G x = ⊥ := fun x ↦
    (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ hfree g x hg
  exact ⟨freeProperChartedSpace I I' hstab, isManifold_freeProperChartedSpace hstab,
    isSubmersion_quotientMk_freeProperChartedSpace hstab⟩

end Quotient

end TauCeti
