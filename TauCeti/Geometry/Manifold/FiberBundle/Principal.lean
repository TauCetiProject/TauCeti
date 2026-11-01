/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.Principal

/-!
# Smooth principal bundles

Let `P` be a principal `G`-bundle (`TauCeti.PrincipalBundle G P`) over a manifold `B` modelled on
`IB`, whose structure group `G` is a manifold modelled on `IG`. Its total space is charted through
the fibre by the type copy `TauCeti.ManifoldTotalSpace G P`, which is a `C^n` manifold modelled on
`IB.prod IG` as soon as `P` is a `C^n` fibre bundle (`TauCeti.ContMDiffFiberBundle n G P IB IG`).

Since the coordinate changes of a principal bundle are left multiplications,
`e.coordChange e' b g = e.coordChange e' b 1 * g`, smoothness of the bundle only has to be checked
on its `G`-valued transition functions `b ↦ e.coordChange e' b 1`: when multiplication of `G` is
`C^n`, the bundle is a `C^n` fibre bundle exactly when these functions are `C^n` on the overlaps
of the base sets (`TauCeti.PrincipalBundle.contMDiffFiberBundle_iff`).

For the charts through the fibre, the right action and the division map are smooth. The action
is `C^n` when multiplication of `G` is (`ContMDiff.totalSpaceMk_smul`), and the division map
`TauCeti.PrincipalBundle.division G p q`, the unique `g` with `p • g = q`, is `C^n` on pairs of
points over a common base point when `G` is a `C^n` Lie group (`ContMDiff.division`). As for
continuity in `TauCeti.Topology.FiberBundle.Principal`, both are stated for families of points
`⟨f x, p x⟩` of the total space over a varying base point `f x`, so that no cast between fibres is
needed; none of them uses smoothness of the coordinate changes. Consequently the equivariant
trivialization `TauCeti.PrincipalBundle.trivializationOfSection` determined by a `C^n` local
section is `C^n` with `C^n` inverse (`TauCeti.PrincipalBundle.contMDiffOn_trivializationOfSection`
and `TauCeti.PrincipalBundle.contMDiffOn_trivializationOfSection_symm`).

## Main results

* `TauCeti.PrincipalBundle.contMDiffFiberBundle_iff`: a principal bundle is a `C^n` fibre bundle
  if and only if its transition functions `b ↦ e.coordChange e' b 1` are `C^n`.
* `ContMDiff.totalSpaceMk_smul`: the right action of a principal bundle is `C^n`.
* `ContMDiff.division`: the division map of a principal bundle is `C^n`.
* `TauCeti.PrincipalBundle.contMDiffOn_trivializationOfSection` and
  `TauCeti.PrincipalBundle.contMDiffOn_trivializationOfSection_symm`: a `C^n` local section
  determines a `C^n` equivariant trivialization with `C^n` inverse.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.1–§10.3 (principal fibre bundles, their transition functions and the division map).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5.
-/

public section

open Bundle Filter MulOpposite Set TauCeti TauCeti.PrincipalBundle
open scoped Manifold Topology ContDiff

variable {n : ℕ∞ω} {𝕜 B G M : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-! ### Smoothness from the transition functions -/

variable (n G P IB IG) in
/-- **Smooth principal bundles from their transition functions.** When multiplication of `G` is
`C^n`, a principal `G`-bundle is a `C^n` fibre bundle if and only if, for any two trivializations
`e` and `e'` of its atlas, the transition function `b ↦ e.coordChange e' b 1`, which is the fibre
coordinate `(e' (e⁻¹ (b, 1))).2`, is `C^n` on the overlap of their base sets. -/
theorem TauCeti.PrincipalBundle.contMDiffFiberBundle_iff [ContMDiffMul IG n G] :
    ContMDiffFiberBundle n G P IB IG ↔
      ∀ (e e' : Trivialization G (π G P)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
        ContMDiffOn IB IG n (fun b ↦ e.coordChange e' b 1) (e.baseSet ∩ e'.baseSet) := by
  refine ⟨fun h e e' _ _ ↦ ?_, fun h ↦ ⟨fun e e' _ _ ↦ ?_⟩⟩
  · exact (h.contMDiffOn_coordChange e e').comp (contMDiffOn_id.prodMk contMDiffOn_const)
      fun _ hb ↦ ⟨hb, mem_univ _⟩
  · -- The coordinate change is left multiplication by the transition function.
    refine (((h e e').comp (s := (e.baseSet ∩ e'.baseSet) ×ˢ univ) contMDiffOn_fst
      fun _ hp ↦ hp.1).mul contMDiffOn_snd).congr ?_
    rintro ⟨b, g⟩ ⟨hb, -⟩
    exact e.coordChange_eq_mul e' hb.1 hb.2 g

/-! ### Smoothness of the action and of the division map -/

variable {f : M → B} {p q : ∀ x, P (f x)} {g : M → G} {s : Set M} {x₀ : M}

/-- **The right action of a principal bundle is `C^n`**, for the charts through the fibre: for a
`C^n` family of points `⟨f x, p x⟩` of the total space and a `C^n` family `g x` of group elements,
the family `⟨f x, p x • g x⟩` is `C^n`. -/
theorem ContMDiffWithinAt.totalSpaceMk_smul [ContMDiffMul IG n G]
    (hp : ContMDiffWithinAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) s x₀)
    (hg : ContMDiffWithinAt IM IG n g s x₀) :
    ContMDiffWithinAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, op (g x) • p x⟩) s x₀ := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff] at hp ⊢
  obtain ⟨hf, hp⟩ := hp
  refine ⟨hf, ?_⟩
  let e := trivializationAt G P (f x₀)
  have hx₀ : f x₀ ∈ e.baseSet := mem_baseSet_trivializationAt G P (f x₀)
  -- Over the base set of `e`, the fibre coordinate of `p x • g x` is that of `p x` times `g x`.
  refine (hp.mul hg).congr_of_eventuallyEq ?_ (e.snd_apply_smul hx₀ _ _)
  filter_upwards [hf.continuousWithinAt (e.open_baseSet.mem_nhds hx₀)] with x hx
  exact e.snd_apply_smul hx _ _

/-- The right action of a principal bundle is `C^n` at a point, for the charts through the fibre:
`x ↦ ⟨f x, p x • g x⟩` is `C^n` at `x₀` when `x ↦ ⟨f x, p x⟩` and `g` are. -/
theorem ContMDiffAt.totalSpaceMk_smul [ContMDiffMul IG n G]
    (hp : ContMDiffAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) x₀)
    (hg : ContMDiffAt IM IG n g x₀) :
    ContMDiffAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, op (g x) • p x⟩) x₀ :=
  ContMDiffWithinAt.totalSpaceMk_smul hp hg

/-- The right action of a principal bundle is `C^n` on a set, for the charts through the fibre:
`x ↦ ⟨f x, p x • g x⟩` is `C^n` on `s` when `x ↦ ⟨f x, p x⟩` and `g` are. -/
theorem ContMDiffOn.totalSpaceMk_smul [ContMDiffMul IG n G]
    (hp : ContMDiffOn IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) s)
    (hg : ContMDiffOn IM IG n g s) :
    ContMDiffOn IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, op (g x) • p x⟩) s :=
  fun x hx ↦ (hp x hx).totalSpaceMk_smul (hg x hx)

/-- The right action of a principal bundle is `C^n`, for the charts through the fibre:
`x ↦ ⟨f x, p x • g x⟩` is `C^n` when `x ↦ ⟨f x, p x⟩` and `g` are. -/
theorem ContMDiff.totalSpaceMk_smul [ContMDiffMul IG n G]
    (hp : ContMDiff IM (IB.prod IG) n fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩)
    (hg : ContMDiff IM IG n g) :
    ContMDiff IM (IB.prod IG) n fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, op (g x) • p x⟩ :=
  fun x ↦ (hp x).totalSpaceMk_smul (hg x)

/-- **The division map of a principal bundle is `C^n`**, for the charts through the fibre: for two
`C^n` families of points `⟨f x, p x⟩` and `⟨f x, q x⟩` of the total space over a common base
point, the family `division G (p x) (q x)` of elements of the Lie group `G` is `C^n`. -/
theorem ContMDiffWithinAt.division [LieGroup IG n G]
    (hp : ContMDiffWithinAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) s x₀)
    (hq : ContMDiffWithinAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, q x⟩) s x₀) :
    ContMDiffWithinAt IM IG n (fun x ↦ division G (p x) (q x)) s x₀ := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff] at hp hq
  let e := trivializationAt G P (f x₀)
  have hx₀ : f x₀ ∈ e.baseSet := mem_baseSet_trivializationAt G P (f x₀)
  -- Over the base set of `e`, the division map is read in the fibre coordinates of `e`.
  refine (hp.2.inv.mul hq.2).congr_of_eventuallyEq ?_ (division_eq_of_mem_baseSet hx₀ _ _)
  filter_upwards [hp.1.continuousWithinAt (e.open_baseSet.mem_nhds hx₀)] with x hx
  exact division_eq_of_mem_baseSet hx _ _

/-- The division map of a principal bundle is `C^n` at a point, for the charts through the fibre:
`x ↦ division G (p x) (q x)` is `C^n` at `x₀` when `x ↦ ⟨f x, p x⟩` and `x ↦ ⟨f x, q x⟩` are. -/
theorem ContMDiffAt.division [LieGroup IG n G]
    (hp : ContMDiffAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) x₀)
    (hq : ContMDiffAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, q x⟩) x₀) :
    ContMDiffAt IM IG n (fun x ↦ division G (p x) (q x)) x₀ :=
  ContMDiffWithinAt.division hp hq

/-- The division map of a principal bundle is `C^n` on a set, for the charts through the fibre:
`x ↦ division G (p x) (q x)` is `C^n` on `s` when `x ↦ ⟨f x, p x⟩` and `x ↦ ⟨f x, q x⟩` are. -/
theorem ContMDiffOn.division [LieGroup IG n G]
    (hp : ContMDiffOn IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) s)
    (hq : ContMDiffOn IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, q x⟩) s) :
    ContMDiffOn IM IG n (fun x ↦ division G (p x) (q x)) s :=
  fun x hx ↦ (hp x hx).division (hq x hx)

/-- The division map of a principal bundle is `C^n`, for the charts through the fibre:
`x ↦ division G (p x) (q x)` is `C^n` when `x ↦ ⟨f x, p x⟩` and `x ↦ ⟨f x, q x⟩` are. -/
theorem ContMDiff.division [LieGroup IG n G]
    (hp : ContMDiff IM (IB.prod IG) n fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩)
    (hq : ContMDiff IM (IB.prod IG) n fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, q x⟩) :
    ContMDiff IM IG n fun x ↦ division G (p x) (q x) :=
  fun x ↦ (hp x).division (hq x)

/-! ### Trivializations from smooth local sections -/

namespace TauCeti.PrincipalBundle

variable [IsTopologicalGroup G] {σ : ∀ b, P b} {U : Set B} {hU : IsOpen U}
  {hσ : ContinuousOn (fun b ↦ TotalSpace.mk' G b (σ b)) U}

/-- The equivariant trivialization determined by a section `σ` that is `C^n` on an open set `U` is
`C^n` on its source, as a map from the total space, charted through the fibre, to `B × G`. -/
theorem contMDiffOn_trivializationOfSection [LieGroup IG n G]
    (hσ' : ContMDiffOn IB (IB.prod IG) n (fun b ↦ ManifoldTotalSpace.homeomorph G P ⟨b, σ b⟩) U) :
    ContMDiffOn (IB.prod IG) (IB.prod IG) n
      (fun x ↦ trivializationOfSection σ hU hσ ((ManifoldTotalSpace.homeomorph G P).symm x))
      ((ManifoldTotalSpace.homeomorph G P).symm ⁻¹' (π G P ⁻¹' U)) := by
  have hproj := (ManifoldTotalSpace.contMDiff_proj n G P IB IG).contMDiffOn (s :=
    (ManifoldTotalSpace.homeomorph G P).symm ⁻¹' (π G P ⁻¹' U))
  -- The fibre coordinate is the division map of `σ` at the base point and the point itself.
  have hdiv : ContMDiffOn (IB.prod IG) IG n
      (fun x ↦ division G (σ ((ManifoldTotalSpace.homeomorph G P).symm x).proj)
        ((ManifoldTotalSpace.homeomorph G P).symm x).2)
      ((ManifoldTotalSpace.homeomorph G P).symm ⁻¹' (π G P ⁻¹' U)) :=
    ContMDiffOn.division (hσ'.comp hproj fun _ hx ↦ hx)
      (contMDiffOn_id.congr fun x _ ↦ by rw [TotalSpace.eta, Homeomorph.apply_symm_apply, id_eq])
  simpa only [trivializationOfSection_apply] using hproj.prodMk hdiv

/-- The inverse of the equivariant trivialization determined by a section `σ` that is `C^n` on an
open set `U` is `C^n` on its target `U ×ˢ univ`, as a map from `B × G` to the total space, charted
through the fibre. -/
theorem contMDiffOn_trivializationOfSection_symm [ContMDiffMul IG n G]
    (hσ' : ContMDiffOn IB (IB.prod IG) n (fun b ↦ ManifoldTotalSpace.homeomorph G P ⟨b, σ b⟩) U) :
    ContMDiffOn (IB.prod IG) (IB.prod IG) n
      (fun y ↦ ManifoldTotalSpace.homeomorph G P
        ((trivializationOfSection σ hU hσ).toOpenPartialHomeomorph.symm y)) (U ×ˢ univ) := by
  simp only [trivializationOfSection_symm_apply]
  exact ContMDiffOn.totalSpaceMk_smul (f := Prod.fst) (p := fun y ↦ σ y.1)
    (hσ'.comp contMDiffOn_fst fun _ hy ↦ hy.1) contMDiffOn_snd

end TauCeti.PrincipalBundle
