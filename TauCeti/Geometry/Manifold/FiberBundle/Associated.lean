/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.GroupCocycle
public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Topology.FiberBundle.Associated

/-!
# Smooth associated bundles

Let `P` be a `C^n` principal `G`-bundle over a manifold `B` modelled on `IB`, with structure group
`G` modelled on `IG`, and let `G` act `C^n`-smoothly on the left on a manifold `F` modelled on
`IF`. The associated bundle `TauCeti.AssociatedBundle G P F = P ×_G F` is glued from the transition
functions `b ↦ e.coordChange e' b 1` of `P` acting on `F`. These transition functions are `C^n`
(`TauCeti.PrincipalBundle.contMDiffFiberBundle_iff`), so the associated bundle is a `C^n` fibre
bundle (`TauCeti.AssociatedBundle.contMDiffFiberBundle`). Its total space, charted through the
fibre by `TauCeti.ManifoldTotalSpace`, is then a `C^n` manifold modelled on `IB.prod IF`, and its
projection is a `C^n` submersion (`TauCeti.ManifoldTotalSpace.isSubmersion_proj`). The base may
have boundary: no hypothesis on the model `IB` is made.

In these charts the class `[p, v]` depends `C^n`-smoothly on the pair: in the chart at a base
point it reads `(e p).2 • v`, which is `C^n` in `p` and `v`
(`ContMDiffWithinAt.totalSpaceMk_associatedBundleMk`). In particular the quotient map
`(p, v) ↦ [p, v]` from `P × F` onto `P ×_G F` is `C^n`
(`TauCeti.AssociatedBundle.contMDiff_totalSpaceMk_mk`).

## Main results

* `TauCeti.AssociatedBundle.contMDiffFiberBundle`: the associated bundle of a `C^n` principal
  bundle and a `C^n` action is a `C^n` fibre bundle.
* `ContMDiffWithinAt.totalSpaceMk_associatedBundleMk`,
  `ContMDiffAt.totalSpaceMk_associatedBundleMk`, `ContMDiffOn.totalSpaceMk_associatedBundleMk`
  and `ContMDiff.totalSpaceMk_associatedBundleMk`: the class of a `C^n` family of pairs is a `C^n`
  family.
* `TauCeti.AssociatedBundle.contMDiff_totalSpaceMk_mk`: the quotient map `(p, v) ↦ [p, v]` is
  `C^n`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.7 (associated bundles of smooth principal bundles and smooth actions).
-/

public section

open Bundle MulOpposite Set TauCeti TauCeti.AssociatedBundle
open scoped Manifold Topology ContDiff

variable {n : ℕ∞ω} {𝕜 B G F M : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F] [MulAction G F]
  [ContinuousSMul G F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-! ### The smooth structure -/

variable (IG) in
/-- **Smooth associated bundles.** The bundle associated with a `C^n` principal bundle and a `C^n`
action of its structure group is a `C^n` fibre bundle: its transition functions are those of the
principal bundle, acting on the fibre. The model `IG` of the structure group does not appear in
the conclusion, so this is not an instance. -/
theorem TauCeti.AssociatedBundle.contMDiffFiberBundle [ContMDiffMul IG n G]
    [ContMDiffSMul IG IF n G F] [ContMDiffFiberBundle n G P IB IG] :
    ContMDiffFiberBundle n F (AssociatedBundle G P F) IB IF := by
  unfold AssociatedBundle
  rw [associatedBundleCore_def]
  exact contMDiffFiberBundle_fiberBundleCoreOfGroupCocycle n IB IF F _ _ _ _ _ _ _ fun _ _ ↦
    (PrincipalBundle.contMDiffFiberBundle_iff (n := n) (G := G) (P := P) (IB := IB)
      (IG := IG)).1 inferInstance _ _

/-! ### Smoothness of classes -/

variable {f : M → B} {p : ∀ x, P (f x)} {v : M → F} {s : Set M} {x₀ : M}

/-- **Classes depend smoothly on the pair**, for the charts through the fibre: for a `C^n` family
of points `⟨f x, p x⟩` of the total space of `P` and a `C^n` family `v x` of points of `F`, the
classes `[p x, v x]` form a `C^n` family in the total space of the associated bundle. -/
theorem ContMDiffWithinAt.totalSpaceMk_associatedBundleMk [ContMDiffSMul IG IF n G F]
    (hp : ContMDiffWithinAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) s x₀)
    (hv : ContMDiffWithinAt IM IF n v s x₀) :
    ContMDiffWithinAt IM (IB.prod IF) n
      (fun x ↦ ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨f x, AssociatedBundle.mk G (p x) (v x)⟩) s x₀ := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff] at hp ⊢
  obtain ⟨hf, hp⟩ := hp
  refine ⟨hf, ?_⟩
  have hx₀ := mem_baseSet_trivializationAt G P (f x₀)
  -- Over the base set of the chart `e` at `f x₀`, the coordinate of `[p x, v x]` is
  -- `(e (p x)).2 • v x`.
  refine (hp.smul hv).congr_of_eventuallyEq ?_ (trivializationAt_mk_snd hx₀ _ _)
  filter_upwards [hf.continuousWithinAt
    ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds hx₀)] with x hx
  exact trivializationAt_mk_snd hx _ _

/-- The class of a family of pairs `C^n` at a point is `C^n` at that point, for the charts through
the fibre. -/
theorem ContMDiffAt.totalSpaceMk_associatedBundleMk [ContMDiffSMul IG IF n G F]
    (hp : ContMDiffAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) x₀)
    (hv : ContMDiffAt IM IF n v x₀) :
    ContMDiffAt IM (IB.prod IF) n
      (fun x ↦ ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨f x, AssociatedBundle.mk G (p x) (v x)⟩) x₀ :=
  ContMDiffWithinAt.totalSpaceMk_associatedBundleMk hp hv

/-- The class of a family of pairs `C^n` on a set is `C^n` on that set, for the charts through the
fibre. -/
theorem ContMDiffOn.totalSpaceMk_associatedBundleMk [ContMDiffSMul IG IF n G F]
    (hp : ContMDiffOn IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) s)
    (hv : ContMDiffOn IM IF n v s) :
    ContMDiffOn IM (IB.prod IF) n
      (fun x ↦ ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨f x, AssociatedBundle.mk G (p x) (v x)⟩) s :=
  fun x hx ↦ (hp x hx).totalSpaceMk_associatedBundleMk (hv x hx)

/-- The class of a `C^n` family of pairs is a `C^n` family, for the charts through the fibre. -/
theorem ContMDiff.totalSpaceMk_associatedBundleMk [ContMDiffSMul IG IF n G F]
    (hp : ContMDiff IM (IB.prod IG) n fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩)
    (hv : ContMDiff IM IF n v) :
    ContMDiff IM (IB.prod IF) n fun x ↦ ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
      ⟨f x, AssociatedBundle.mk G (p x) (v x)⟩ :=
  fun x ↦ (hp x).totalSpaceMk_associatedBundleMk (hv x)

namespace TauCeti.AssociatedBundle

variable (n G P F IB IG IF) in
/-- **The quotient map onto the associated bundle is smooth.** For the charts through the fibre,
the map `(p, v) ↦ [p, v]` from pairs of points of the total space of `P` and of `F` onto the total
space of the associated bundle is `C^n`. -/
theorem contMDiff_totalSpaceMk_mk [ContMDiffSMul IG IF n G F] :
    ContMDiff ((IB.prod IG).prod IF) (IB.prod IF) n fun x : ManifoldTotalSpace G P × F ↦
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
          mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).2 x.2⟩ :=
  ContMDiff.totalSpaceMk_associatedBundleMk
    (contMDiff_fst.congr fun x ↦ by rw [TotalSpace.eta, Homeomorph.apply_symm_apply])
    contMDiff_snd

end TauCeti.AssociatedBundle
