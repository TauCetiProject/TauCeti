/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Basic
public import TauCeti.Topology.FiberBundle.Associated.Section

/-!
# Smooth sections and equivariant functions

The section/function dictionary for associated bundles preserves smoothness at every regularity
`n` (including `∞` and `ω`):
`s(b) = [p,u(p)]` identifies `C^n` sections with `C^n` functions satisfying
`u(p • g) = g⁻¹ • u(p)`. Smoothness uses the existing charts through the fibre on both total
spaces, without changing their topology or introducing vector-bundle structures.

The proof reads `u` in a principal chart as the inverse principal coordinate acting on the
section coordinate. In the other direction it descends the smooth map `p ↦ [p,u(p)]` along
the principal projection. This is the dictionary needed to express associated tensor fields
as equivariant functions before differentiating them.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  Springer, 1993, §10.12 (sections of associated bundles).
-/

public section

open Bundle MulOpposite Set TauCeti
open scoped Manifold Topology ContDiff

namespace TauCeti.AssociatedBundle

variable {n : ℕ∞ω} {𝕜 B G F : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F] [MulAction G F]
  [ContinuousSMul G F] [LieGroup IG n G] [ContMDiffSMul IG IF n G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- A `C^n` section has a `C^n` inverse-equivariant representing function. -/
theorem contMDiff_sectionFunction (s : ∀ b, AssociatedBundle G P F b)
    (hs : ContMDiff IB (IB.prod IF) n fun b ↦
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) ⟨b, s b⟩) :
    ContMDiff (IB.prod IG) IF n fun p : ManifoldTotalSpace G P ↦
      sectionFunction s ((ManifoldTotalSpace.homeomorph G P).symm p) := by
  intro p
  have hπ := ManifoldTotalSpace.contMDiff_proj n G P IB IG
  have hp := ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IG p
  have hs' := (ManifoldTotalSpace.contMDiffAt_iff.1
    ((hs.comp hπ) p)).2
  have hb := mem_baseSet_trivializationAt G P
    ((ManifoldTotalSpace.homeomorph G P).symm p).proj
  refine (hp.inv.smul hs').congr_of_eventuallyEq ?_
  filter_upwards [(hπ p).continuousAt
    ((trivializationAt G P ((ManifoldTotalSpace.homeomorph G P).symm p).proj).open_baseSet.mem_nhds
      hb)] with q hq
  exact sectionFunction_eq_inv_smul s hq _

/-- Smoothness of a section is equivalent to smoothness of its inverse-equivariant function,
for the charts through the fibre. -/
theorem contMDiff_sectionFunction_iff (s : ∀ b, AssociatedBundle G P F b) :
    (ContMDiff (IB.prod IG) IF n fun p : ManifoldTotalSpace G P ↦
      sectionFunction s ((ManifoldTotalSpace.homeomorph G P).symm p)) ↔
    ContMDiff IB (IB.prod IF) n (fun b ↦
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) ⟨b, s b⟩) := by
  refine ⟨fun hu ↦ ?_, contMDiff_sectionFunction s⟩
  apply (ManifoldTotalSpace.contMDiff_comp_proj_iff (F := G) (E := P) (IF := IG)).1
  have hp : ContMDiff (IB.prod IG) (IB.prod IG) n fun p : ManifoldTotalSpace G P ↦
      ManifoldTotalSpace.homeomorph G P
        ⟨((ManifoldTotalSpace.homeomorph G P).symm p).proj,
          ((ManifoldTotalSpace.homeomorph G P).symm p).2⟩ :=
    contMDiff_id.congr fun p ↦ by simp only [TotalSpace.eta, Homeomorph.apply_symm_apply, id_eq]
  exact (hp.totalSpaceMk_associatedBundleMk hu).congr fun p ↦ by
    rw [mk_sectionFunction]

/-- The associated-bundle correspondence restricted to `C^n` sections and `C^n`
inverse-equivariant functions. The functions are evaluated on the manifold total-space copy. -/
noncomputable def contMDiffSectionEquiv :
    {s : ∀ b, AssociatedBundle G P F b //
      ContMDiff IB (IB.prod IF) n fun b ↦
        ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) ⟨b, s b⟩} ≃
    {u : ManifoldTotalSpace G P → F //
      ContMDiff (IB.prod IG) IF n u ∧ ∀ (b : B) (p : P b) (g : G),
        u (ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) =
          g⁻¹ • u (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩)} where
  toFun s := ⟨fun p ↦ sectionFunction s.1 ((ManifoldTotalSpace.homeomorph G P).symm p),
    contMDiff_sectionFunction s.1 s.2, by
      intro b p g
      simp only [Homeomorph.symm_apply_apply, sectionFunction_smul]⟩
  invFun u := ⟨sectionEquiv.symm ⟨fun p ↦ u.1 (ManifoldTotalSpace.homeomorph G P p), u.2.2⟩, by
    apply (contMDiff_sectionFunction_iff (IB := IB) (IG := IG) (IF := IF) (n := n) _).1
    simpa only [sectionFunction_sectionEquiv_symm, Homeomorph.apply_symm_apply]
      using u.2.1⟩
  left_inv s := by
    apply Subtype.ext
    apply sectionFunction_injective
    funext p
    simp only [sectionFunction_sectionEquiv_symm, Homeomorph.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    funext p
    simp only [sectionFunction_sectionEquiv_symm, Homeomorph.apply_symm_apply]

/-- The smooth correspondence is the same representing function on the manifold copy. -/
@[simp]
theorem contMDiffSectionEquiv_apply
    (s : {s : ∀ b, AssociatedBundle G P F b //
      ContMDiff IB (IB.prod IF) n fun b ↦
        ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) ⟨b, s b⟩})
    (p : ManifoldTotalSpace G P) :
    (contMDiffSectionEquiv (IG := IG) s).1 p =
      sectionFunction s.1 ((ManifoldTotalSpace.homeomorph G P).symm p) :=
  (rfl)

/-- The smooth inverse correspondence has the same underlying section as the raw one. -/
@[simp]
theorem contMDiffSectionEquiv_symm_val
    (u : {u : ManifoldTotalSpace G P → F // ContMDiff (IB.prod IG) IF n u ∧
      ∀ (b : B) (p : P b) (g : G),
        u (ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) =
          g⁻¹ • u (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩)}) :
    (contMDiffSectionEquiv.symm u).1 =
      sectionEquiv.symm ⟨fun p ↦ u.1 (ManifoldTotalSpace.homeomorph G P p), u.2.2⟩ :=
  (rfl)

/-- Evaluate the smooth inverse correspondence using any principal frame. -/
theorem contMDiffSectionEquiv_symm_apply
    (u : {u : ManifoldTotalSpace G P → F // ContMDiff (IB.prod IG) IF n u ∧
      ∀ (b : B) (p : P b) (g : G),
        u (ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) =
          g⁻¹ • u (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩)})
    {b : B} (p : P b) :
    (contMDiffSectionEquiv.symm u).1 b =
      mk G p (u.1 (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩)) :=
  sectionEquiv_symm_apply ⟨_, u.2.2⟩ p

end TauCeti.AssociatedBundle
