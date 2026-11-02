/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
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

The vertical tangent space at a point `p` of the total space, the kernel of the derivative of the
projection, is the image of the derivative at the identity of the orbit map `g ↦ p • g`
(`TauCeti.PrincipalBundle.ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk_smul_one`), and this
derivative is injective (`TauCeti.PrincipalBundle.mfderiv_totalSpaceMk_smul_injective`). So the
vertical tangent vectors at `p` correspond bijectively to the tangent vectors of `G` at the
identity, and the vertical tangent space has the same `Module.finrank` as the model space of `G`,
which is its dimension when that model space is finite-dimensional
(`TauCeti.PrincipalBundle.finrank_ker_mfderiv_proj`). These statements need `C^n` multiplication on
`G` and a `C^n` fibre bundle for some `n ≠ 0`.

## Main results

* `TauCeti.PrincipalBundle.contMDiffFiberBundle_iff`: a principal bundle is a `C^n` fibre bundle
  if and only if its transition functions `b ↦ e.coordChange e' b 1` are `C^n`.
* `ContMDiff.totalSpaceMk_smul`: the right action of a principal bundle is `C^n`.
* `ContMDiff.division`: the division map of a principal bundle is `C^n`.
* `TauCeti.PrincipalBundle.contMDiffOn_trivializationOfSection` and
  `TauCeti.PrincipalBundle.contMDiffOn_trivializationOfSection_symm`: a `C^n` local section
  determines a `C^n` equivariant trivialization with `C^n` inverse.
* `TauCeti.PrincipalBundle.ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk_smul`: the kernel of the
  derivative of the projection at `p • g₀` is the image of the derivative at `g₀` of the orbit map
  of `p`.
* `TauCeti.PrincipalBundle.mfderiv_totalSpaceMk_smul_injective`: the orbit maps have injective
  derivative.
* `TauCeti.PrincipalBundle.finrank_ker_mfderiv_proj`: the vertical tangent space has the same
  `Module.finrank` as the model space of `G`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.1–§10.3 (principal fibre bundles, their transition functions and the division map).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5, and Chapter II, §1 (the vertical subspace is the image of the Lie algebra under
  the derivative of the orbit map).
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

/-! ### The vertical tangent space -/

namespace TauCeti.PrincipalBundle

variable [ContMDiffFiberBundle n G P IB IG] [ContMDiffMul IG n G] {b : B}

/-- Tangent-level properties of the orbit map `g ↦ p • g` through a point `p` of the fibre over
`b`, at `g₀`. Its derivative is killed by the derivative of the projection, and it has a
continuous linear left inverse that is also a right inverse on the kernel of the derivative of the
projection at `p • g₀`. -/
private theorem mfderiv_smul_aux (hn : n ≠ 0) (p : P b) (g₀ : G) :
    (∀ ξ, mfderiv (IB.prod IG) IB
        (fun x : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm x).proj)
        (ManifoldTotalSpace.homeomorph G P ⟨b, op g₀ • p⟩)
        (mfderiv IG (IB.prod IG)
          (fun g : G ↦ ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) g₀ ξ) = 0) ∧
    ∃ L : TangentSpace (IB.prod IG) (ManifoldTotalSpace.homeomorph G P ⟨b, op g₀ • p⟩) →L[𝕜]
        TangentSpace IG g₀,
      (∀ ξ, L (mfderiv IG (IB.prod IG)
        (fun g : G ↦ ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) g₀ ξ) = ξ) ∧
      ∀ w, mfderiv (IB.prod IG) IB
          (fun x : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm x).proj)
          (ManifoldTotalSpace.homeomorph G P ⟨b, op g₀ • p⟩) w = 0 →
        mfderiv IG (IB.prod IG)
          (fun g : G ↦ ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) g₀ (L w) = w := by
  -- Read everything through the trivialization `e` at `b`. With `h = (e p).2`, the map
  -- `ψ x = h⁻¹ * (e x).2` inverts the orbit map `O`, and `O ∘ ψ` is `x ↦ e⁻¹ (b, (e x).2)`, which
  -- differs from `x = e⁻¹ (π x, (e x).2)` only in the base coordinate. The derivative of `ψ` is
  -- the required left inverse.
  let Φ := ManifoldTotalSpace.homeomorph G P
  let e := trivializationAt G P b
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt G P b
  let x₀ := Φ ⟨b, op g₀ • p⟩
  let O : G → ManifoldTotalSpace G P := fun g ↦ Φ ⟨b, op g • p⟩
  let proj : ManifoldTotalSpace G P → B := fun x ↦ (Φ.symm x).proj
  let s : ManifoldTotalSpace G P → G := fun x ↦ (e (Φ.symm x)).2
  let F : B × G → ManifoldTotalSpace G P := fun y ↦ Φ (e.toOpenPartialHomeomorph.symm y)
  let ψ : ManifoldTotalSpace G P → G := fun x ↦ (e ⟨b, p⟩).2⁻¹ * s x
  -- The identities relating the orbit map, the projection, the trivialization and `ψ`.
  have hprojO : proj ∘ O = fun _ ↦ b := funext fun g ↦ by
    simp only [Function.comp_apply, proj, O, Φ, Homeomorph.symm_apply_apply]
  have hFO (g : G) : F (b, (e ⟨b, p⟩).2 * g) = O g := by
    simp only [F, O, ← e.apply_smul hb p g,
      e.symm_apply_apply (x := ⟨b, op g • p⟩) (e.mem_source.2 hb)]
  have hψO' (g : G) : ψ (O g) = g := by
    simp only [ψ, s, O, Φ, Homeomorph.symm_apply_apply, e.snd_apply_smul hb p g,
      inv_mul_cancel_left]
  have hψO : ψ ∘ O = id := funext hψO'
  have hOψ : O ∘ ψ = F ∘ fun x ↦ (b, s x) := funext fun x ↦ by
    rw [Function.comp_apply, Function.comp_apply, ← hFO, mul_inv_cancel_left]
  have hproj₀ : proj x₀ = b := congrFun hprojO g₀
  have hFid : F ∘ (fun x ↦ (proj x, s x)) =ᶠ[𝓝 x₀] id := by
    have hx₀ : x₀ ∈ Φ.symm ⁻¹' e.source := by
      simpa only [mem_preimage, x₀, Φ, Homeomorph.symm_apply_apply] using e.mem_source.2 hb
    filter_upwards [(e.open_source.preimage Φ.symm.continuous).mem_nhds hx₀] with x hx
    simp only [Function.comp_apply, F, proj, s, id, e.symm_apply_mk_proj hx,
      Homeomorph.apply_symm_apply]
  -- The differentiability of the maps involved.
  have hproj : MDifferentiableAt (IB.prod IG) IB proj x₀ :=
    (ManifoldTotalSpace.contMDiff_proj n G P IB IG x₀).mdifferentiableAt hn
  have hsC : ContMDiffAt (IB.prod IG) IG n s x₀ := by
    have := ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IG x₀
    simpa only [x₀, Φ, Homeomorph.symm_apply_apply] using this
  have hsD : MDifferentiableAt (IB.prod IG) IG s x₀ := hsC.mdifferentiableAt hn
  have hψ : MDifferentiableAt (IB.prod IG) IG ψ x₀ :=
    (contMDiffAt_const.mul hsC).mdifferentiableAt hn
  have hO : MDifferentiableAt IG (IB.prod IG) O g₀ :=
    (ContMDiff.totalSpaceMk_smul (f := fun _ : G ↦ b) (p := fun _ ↦ p) contMDiff_const
      contMDiff_id g₀).mdifferentiableAt hn
  have hF : MDifferentiableAt (IB.prod IG) (IB.prod IG) F (b, s x₀) :=
    (((ManifoldTotalSpace.contMDiffOn_trivialization_symm e).contMDiffAt
      (e.open_target.mem_nhds (e.mem_target.2 hb))).mdifferentiableAt hn)
  refine ⟨fun ξ ↦ ?_, mfderiv (IB.prod IG) IG ψ x₀, fun ξ ↦ ?_, fun w hw ↦ ?_⟩
  · have := mfderiv_comp_apply_of_eq g₀ hproj hO rfl ξ
    rw [hprojO, mfderiv_const] at this
    exact this.symm
  · have := mfderiv_comp_apply_of_eq g₀ hψ hO rfl ξ
    rw [hψO, mfderiv_id] at this
    exact this.symm
  · -- Differentiate `O ∘ ψ = F ∘ (b, s)` and `F ∘ (π, s) = id` at `x₀`.
    have h₁ := mfderiv_comp_apply_of_eq x₀ hO hψ (hψO' g₀) w
    rw [hOψ, mfderiv_comp_apply_of_eq (f := fun x ↦ (b, s x)) x₀ hF
      (mdifferentiableAt_const.prodMk hsD) rfl, mfderiv_prodMk mdifferentiableAt_const hsD,
      mfderiv_const] at h₁
    have h₂ := mfderiv_comp_apply_of_eq (f := fun x ↦ (proj x, s x)) x₀ hF
      (hproj.prodMk hsD) (by rw [hproj₀]) w
    rw [hFid.mfderiv_eq, mfderiv_id, ContinuousLinearMap.comp_id, mfderiv_prodMk hproj hsD] at h₂
    -- `tangentSpaceCast` identifies the tangent spaces at the equal points `x₀` and
    -- `F (proj x₀, s x₀)`, and is the identity on vectors.
    change w = _ at h₂
    -- The two expressions differ only in the base component, which vanishes for vertical `w`.
    have h₃ : (ContinuousLinearMap.prod 0 (mfderiv (IB.prod IG) IG s x₀)) w =
        ((mfderiv (IB.prod IG) IB proj x₀).prod (mfderiv (IB.prod IG) IG s x₀)) w :=
      Prod.ext hw.symm rfl
    exact h₁.symm.trans
      ((congrArg (mfderiv (IB.prod IG) (IB.prod IG) F (b, s x₀)) h₃).trans h₂.symm)

variable (IB IG) in
/-- **The orbit maps of a principal bundle have injective derivative.** For a point `p` of the
fibre over `b`, the derivative at every `g₀` of the orbit map `g ↦ p • g` is injective. -/
theorem mfderiv_totalSpaceMk_smul_injective (hn : n ≠ 0) (p : P b) (g₀ : G) :
    Function.Injective (mfderiv IG (IB.prod IG)
      (fun g : G ↦ ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) g₀) := by
  obtain ⟨-, L, hL, -⟩ := mfderiv_smul_aux (IB := IB) (IG := IG) hn p g₀
  exact Function.LeftInverse.injective hL

variable (IB IG) in
/-- **The vertical tangent space of a principal bundle.** At the point `p • g₀` of the fibre over
`b`, the kernel of the derivative of the projection is the image of the derivative at `g₀` of the
orbit map `g ↦ p • g`. For `g₀ = 1` this describes the vertical vectors at `p` as the
derivatives at the identity of `g ↦ p • g`
(`TauCeti.PrincipalBundle.ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk_smul_one`). -/
theorem ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk_smul (hn : n ≠ 0) (p : P b) (g₀ : G) :
    (mfderiv (IB.prod IG) IB
      (fun x : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm x).proj)
      (ManifoldTotalSpace.homeomorph G P ⟨b, op g₀ • p⟩)).ker =
    (mfderiv IG (IB.prod IG)
      (fun g : G ↦ ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) g₀).range := by
  obtain ⟨h, L, -, hL⟩ := mfderiv_smul_aux (IB := IB) (IG := IG) hn p g₀
  refine le_antisymm (fun w hw ↦ ⟨L w, hL w hw⟩) ?_
  rintro _ ⟨ξ, rfl⟩
  exact h ξ

variable (G IB IG) in
/-- **The vertical tangent space of a principal bundle at a point.** At a point `p` of the fibre
over `b`, the kernel of the derivative of the projection is the image of the derivative at the
identity of the orbit map `g ↦ p • g`. -/
theorem ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk_smul_one (hn : n ≠ 0) (p : P b) :
    (mfderiv (IB.prod IG) IB
      (fun x : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm x).proj)
      (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩)).ker =
    (mfderiv IG (IB.prod IG)
      (fun g : G ↦ ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) 1).range := by
  have := ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk_smul IB IG hn p (1 : G)
  rwa [op_one, one_smul] at this

variable (IB IG) in
/-- **The vertical tangent space has the dimension of the structure group.** At every point of the
total space, the kernel of the derivative of the projection has the same `Module.finrank` as the
model space `EG` of `G`. When `EG` is finite-dimensional this is the dimension of `G`; otherwise
both sides are `0`. -/
theorem finrank_ker_mfderiv_proj (hn : n ≠ 0) (x : ManifoldTotalSpace G P) :
    Module.finrank 𝕜 (mfderiv (IB.prod IG) IB
      (fun x : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm x).proj) x).ker =
      Module.finrank 𝕜 EG := by
  obtain ⟨⟨b, p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
  rw [ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk_smul_one G IB IG hn p]
  -- Elaborated before unifying with the goal, whose tangent-space instances are indexed by the
  -- equal point `p` rather than `p • 1`.
  exact (LinearMap.finrank_range_of_inj (R := 𝕜)
    (mfderiv_totalSpaceMk_smul_injective IB IG hn p (1 : G)) :)

end TauCeti.PrincipalBundle
