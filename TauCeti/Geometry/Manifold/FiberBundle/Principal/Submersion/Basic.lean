/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Topology.FiberBundle.Principal.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.RegularValue

/-!
# Smooth principal bundles from free orbit-exact submersions

Every `C^n` principal `G`-bundle (`1 ≤ n`) has a surjective `C^n` submersion projection whose fibres
are the `G`-orbits of a free right action (`ManifoldTotalSpace.isSubmersion_proj`,
`PrincipalBundle.smul_eq_self_iff`, `PrincipalBundle.isPretransitive`), with injective orbit
differentials spanning the vertical tangent spaces `ker (dp_x)`.

This file establishes the converse in Banach and finite-dimensional `C^n` generality, packaging the
fibres of an unbundled `C^n` submersion `p : P → B` via `TauCeti.ProjectionFiber G p` (the automatic
real Lie-group version, Kolář–Michor–Slovák Lemma 10.3, follows in
`TauCeti.Geometry.Manifold.FiberBundle.Principal.Submersion.LieGroup`):

1. **Banach `C^n` criterion (`1 ≤ n`, over any `RCLike` field `𝕜`):** let `p : P → B` be a
   surjective `C^n` submersion from a boundaryless Banach manifold `P` onto `B`, equipped with a
   free `C^n` right action of a group manifold `G` (`[ContMDiffMul IG n G]`) whose orbits are the
   fibres of `p`. If at every `x : P` the orbit differential `d(g ↦ op g • x)_1` is injective and
   its range contains `ker (dp_x)`, then for every `C^n` local section `s : B → P` on an open set
   `U ⊆ B` the action sweep `(b, g) ↦ op g • s b` is an injective `C^n` local diffeomorphism from
   `U ×ˢ univ` onto `p ⁻¹' U`. Its inverse supplies `C^n` equivariant local trivializations, making
   `ProjectionFiber G p` a `C^n` principal `G`-bundle whose charted total space
   `ManifoldTotalSpace G (ProjectionFiber G p)` is canonically `C^n` diffeomorphic to `P` over `B`
   and `G`-equivariantly.
2. **Finite-dimensional `C^n` criterion (`1 ≤ n`, over `𝕜`):** when the model spaces are
   finite-dimensional over `𝕜`, injectivity of `d(g ↦ op g • x)_1` together with the dimension
   identity `P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG` implies the vertical-range condition by
   rank-nullity.

## Main definitions and results

* `TauCeti.PrincipalBundle.isLocalDiffeomorphOn_op_smul_section`: for a `C^n` local section `s` of
  `p` over an open set `U`, `(b, g) ↦ op g • s b` is a `C^n` local diffeomorphism on `U ×ˢ univ`.
* `TauCeti.PrincipalBundle.contMDiffOn_sectionCoord`: the coordinate `sectionCoord horbit hs` is
  `C^n` on `p ⁻¹' U`.
* `TauCeti.PrincipalBundle.fiberBundleOfSubmersion`,
  `TauCeti.PrincipalBundle.principalBundleOfSubmersion`,
  `TauCeti.PrincipalBundle.contMDiffFiberBundleOfSubmersion`: Banach `C^n` principal bundle
  structures on `ProjectionFiber G p`.
* `TauCeti.PrincipalBundle.diffeomorphManifoldTotalSpaceOfSubmersion`: the `C^n` `G`-equivariant
  diffeomorphism `ManifoldTotalSpace G (ProjectionFiber G p) ≃ₘ^n⟮IB.prod IG, IP⟯ P` over `B`.
* `ContMDiffWithinAt.actionDivision`, `ContMDiffAt.actionDivision`, `ContMDiffOn.actionDivision`,
  `ContMDiff.actionDivision`: `C^n` regularity of `actionDivision` along pairs of maps in a common
  fibre when `G` is a `C^n` Lie group.
* `TauCeti.PrincipalBundle.range_mfderiv_op_smul_one_eq_ker_of_finrank_eq`,
  `TauCeti.PrincipalBundle.fiberBundleOfSubmersionOfFinrankEq`,
  `TauCeti.PrincipalBundle.principalBundleOfSubmersionOfFinrankEq`,
  `TauCeti.PrincipalBundle.contMDiffFiberBundleOfSubmersionOfFinrankEq`,
  `TauCeti.PrincipalBundle.diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq`:
  finite-dimensional `C^n` principal bundle criterion from
  `finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.3, Lemma 10.3.
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapters 4, 5, and 21.
-/

public section

noncomputable section

open Bundle Filter Function Manifold Module MulOpposite Set Topology
open scoped ContDiff Manifold

namespace TauCeti.PrincipalBundle

section Banach

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ∞ω}
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP] [CompleteSpace EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP} [IP.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP n P]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [CompleteSpace EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [ContMDiffMul IG n G] [MulAction Gᵐᵒᵖ P]

/-- Right multiplication on the second factor `(b, h) ↦ (b, h * g)` as a `C^n` diffeomorphism of
`B × G`, requiring only `[ContMDiffMul IG n G]` since `g` and `g⁻¹` are fixed elements. -/
private def prodMulRightDiffeomorph (g : G) :
    (B × G) ≃ₘ^n⟮IB.prod IG, IB.prod IG⟯ (B × G) where
  toFun q := (q.1, q.2 * g)
  invFun q := (q.1, q.2 * g⁻¹)
  left_inv q := Prod.ext rfl (mul_inv_cancel_right q.2 g)
  right_inv q := Prod.ext rfl (inv_mul_cancel_right q.2 g)
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.mul contMDiff_const)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.mul contMDiff_const)

/-- Right action by a fixed element `g : G` on `P` as a `C^n` diffeomorphism, requiring only joint
`C^n` regularity of `(x, h) ↦ op h • x`. -/
private def opSmulDiffeomorph (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    (g : G) : P ≃ₘ^n⟮IP, IP⟯ P where
  toFun x := op g • x
  invFun x := op g⁻¹ • x
  left_inv x := by simp only [← mul_smul, ← op_mul, mul_inv_cancel, op_one, one_smul]
  right_inv x := by simp only [← mul_smul, ← op_mul, inv_mul_cancel, op_one, one_smul]
  contMDiff_toFun := hsmul.comp (contMDiff_id.prodMk contMDiff_const)
  contMDiff_invFun := hsmul.comp (contMDiff_id.prodMk contMDiff_const)

omit [CompleteSpace EP] [IP.Boundaryless] [CompleteSpace EB] [CompleteSpace EG] in
/-- At `(b, 1)` for `b ∈ U`, the differential of the action sweep `(b', g') ↦ op g' • s b'` is
bijective whenever `d(g ↦ op g • s b)_1` is injective and its range contains `ker (dp_{s b})`. -/
private theorem bijective_mfderiv_op_smul_section_one (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hp : ContMDiff IP IB n p)
    (horbit_inv : ∀ (g : G) (x : P), p (op g • x) = p x)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) {b : B} (hb : b ∈ U)
    (hinj : Injective (mfderiv IG IP (fun g : G ↦ op g • s b) 1))
    (hker : (mfderiv IP IB p (s b)).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • s b) 1).range) :
    Bijective (mfderiv (IB.prod IG) IP (fun q : B × G ↦ op q.2 • s q.1) (b, 1)) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  let Ψ : B × G → P := fun q ↦ op q.2 • s q.1
  have hΨ_open : IsOpen (U ×ˢ (univ : Set G)) := hU.prod isOpen_univ
  have hΨ_smooth : ContMDiffOn (IB.prod IG) IP n Ψ (U ×ˢ univ) :=
    hsmul.comp_contMDiffOn
      ((hs_smooth.comp (s := U ×ˢ (univ : Set G)) contMDiffOn_fst fun _ hq ↦ hq.1).prodMk
        contMDiffOn_snd)
  have hΨ_diff : MDifferentiableAt (IB.prod IG) IP Ψ (b, 1) :=
    (hΨ_smooth.contMDiffAt (hΨ_open.mem_nhds ⟨hb, mem_univ _⟩)).mdifferentiableAt hn0
  have hs_diff : MDifferentiableAt IB IP s b :=
    (hs_smooth.contMDiffAt (hU.mem_nhds hb)).mdifferentiableAt hn0
  have hp_diff : MDifferentiableAt IP IB p (s b) := (hp (s b)).mdifferentiableAt hn0
  let dΨ : EB × EG →L[𝕜] EP := mfderiv (IB.prod IG) IP Ψ (b, 1)
  let ds : EB →L[𝕜] EP := mfderiv IB IP s b
  let dorb : EG →L[𝕜] EP := mfderiv IG IP (fun g : G ↦ op g • s b) 1
  let dp : EP →L[𝕜] EB := mfderiv IP IB p (s b)
  -- Decompose `dΨ_{(b, 1)} (u, w) = ds_b u + d(g ↦ op g • s b)_1 w` in the model space `EP`.
  have hdecomp (u : EB) (w : EG) : dΨ (u, w) = ds u + dorb w := by
    have h1 : (id : EP → EP) (mfderiv IB IP (fun b' : B ↦ Ψ (b', 1)) b u) = ds u :=
      congrArg (fun f : B → P ↦ (id : EP → EP) (mfderiv IB IP f b u))
        (funext fun b' ↦ by simp only [Ψ, op_one, one_smul])
    exact (mfderiv_prod_eq_add_apply (v := ((u, w) : EB × EG)) hΨ_diff).trans
      (congrArg₂ (HAdd.hAdd (α := EP) (β := EP)) h1 rfl)
  -- `dp_{s b} ∘ ds_b = id` on `EB` since `p ∘ s = id` on `U`, and `dp_{s b}` kills the orbit.
  have hps_ev : p ∘ s =ᶠ[𝓝 b] id := eventually_of_mem (hU.mem_nhds hb) fun b' hb' ↦ hs b' hb'
  have hps (u : EB) : dp (ds u) = u := by
    have hcomp : dp (ds u) = mfderiv IB IB (p ∘ s) b u :=
      (mfderiv_comp_apply b hp_diff hs_diff u).symm
    rw [hps_ev.mfderiv_eq, mfderiv_id] at hcomp
    exact hcomp
  have horb_ker : dorb.range ≤ dp.ker := by
    have h := range_mfderiv_le_ker_mfderiv_of_eventually_eq (K := IG) (I := IP) (J := IB)
      (f := p) (g := fun g : G ↦ op g • s b) (p := (1 : G)) (y := p (s b))
      (Eventually.of_forall fun g : G ↦ horbit_inv g (s b))
    rwa [op_one, one_smul] at h
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨u, w⟩ (huw : dΨ (u, w) = 0)
    have huw' : ds u + dorb w = 0 := (hdecomp u w).symm.trans huw
    have hu0 : u = 0 := by
      have h0 := congrArg dp huw'
      have hw0 : dp (dorb w) = 0 := horb_ker ⟨w, rfl⟩
      rw [map_add, map_zero, hps u, hw0, add_zero] at h0
      exact h0
    subst hu0
    rw [map_zero, zero_add] at huw'
    exact Prod.ext rfl (hinj (huw'.trans (map_zero dorb).symm))
  · intro (v : EP)
    -- Split `v` into its horizontal lift `ds_b (dp_{s b} v)` plus a vertical remainder in `ker dp`.
    let u : EB := dp v
    have hvert : v - ds u ∈ dp.ker := by
      change dp (v - ds u) = 0
      rw [map_sub, hps u, sub_self]
    obtain ⟨w, hw⟩ : ∃ w : EG, dorb w = v - ds u := hker hvert
    exact ⟨(u, w), (hdecomp u w).trans (by rw [hw, add_sub_cancel])⟩

/-- **Action sweep of a local section is a `C^n` local diffeomorphism.** Over an open set `U ⊆ B`
supporting a `C^n` section `s` of a `C^n` submersion `p : P → B` (`1 ≤ n`), the map
`(b, g) ↦ op g • s b` is a `C^n` local diffeomorphism on `U ×ˢ univ`. -/
theorem isLocalDiffeomorphOn_op_smul_section (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (horbit_inv : ∀ (g : G) (x : P), p (op g • x) = p x)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) :
    IsLocalDiffeomorphOn (IB.prod IG) IP n (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have : IsManifold IP 1 P := .of_le hn
  have : IsManifold IB 1 B := .of_le hn
  have : IsManifold IG 1 G := .of_le hn
  let Ψ : B × G → P := fun q ↦ op q.2 • s q.1
  have hΨ_open : IsOpen (U ×ˢ (univ : Set G)) := hU.prod isOpen_univ
  have hΨ_smooth : ContMDiffOn (IB.prod IG) IP n Ψ (U ×ˢ univ) :=
    hsmul.comp_contMDiffOn
      ((hs_smooth.comp (s := U ×ˢ (univ : Set G)) contMDiffOn_fst fun _ hq ↦ hq.1).prodMk
        contMDiffOn_snd)
  -- First establish `IsLocalDiffeomorphAt` along the identity slice `(b, 1)` via Banach IFT.
  have h_one : ∀ b ∈ U, IsLocalDiffeomorphAt (IB.prod IG) IP n Ψ (b, 1) := fun b hb ↦ by
    let dΨ : EB × EG →L[𝕜] EP := mfderiv (IB.prod IG) IP Ψ (b, 1)
    have hbij : Bijective dΨ := bijective_mfderiv_op_smul_section_one hn hsmul hsub.contMDiff
      horbit_inv hU hs_smooth hs hb (hinj (s b)) (hker (s b))
    let e : (EB × EG) ≃L[𝕜] EP := ContinuousLinearEquiv.ofBijective dΨ
      (LinearMap.ker_eq_bot_of_injective hbij.1)
      (LinearMap.range_eq_top_of_surjective _ hbij.2)
    have hbI : IB.IsInteriorPoint b := by
      rw [← hs b hb]
      exact ((hsub.contMDiff (s b)).mdifferentiableAt hn0).isInteriorPoint_of_surjective_mfderiv
        (hsub.surjective_mfderiv hn0 (s b)) BoundarylessManifold.isInteriorPoint
    have h1I : IG.IsInteriorPoint (1 : G) := ContMDiffMul.isInteriorPoint (n := n) hn0 1
    have hb1I : (IB.prod IG).IsInteriorPoint (b, (1 : G)) := by
      rw [ModelWithCorners.isInteriorPoint_iff, extChartAt_prod, PartialEquiv.prod_coe,
        PartialEquiv.prod_target, interior_prod_eq]
      exact ⟨IB.isInteriorPoint_iff.1 hbI, IG.isInteriorPoint_iff.1 h1I⟩
    exact isLocalDiffeomorphAt_of_mfderiv_eq hΨ_smooth hΨ_open ⟨hb, mem_univ _⟩ hb1I hn
      (e := e) (ContinuousLinearMap.ext fun _ ↦ rfl)
  -- Transport from `(b, 1)` to `(b, g)` using right equivariance of `Ψ`.
  rintro ⟨⟨b, g⟩, hb, -⟩
  let φR : (B × G) ≃ₘ^n⟮IB.prod IG, IB.prod IG⟯ (B × G) := prodMulRightDiffeomorph g⁻¹
  have heq : (fun q : B × G ↦ op q.2 • s q.1) = (opSmulDiffeomorph hsmul g) ∘ (Ψ ∘ φR) := by
    funext ⟨b', h⟩
    change op h • s b' = op g • (op (h * g⁻¹) • s b')
    rw [← mul_smul, ← op_mul, inv_mul_cancel_right]
  have h1 : IsLocalDiffeomorphAt (IB.prod IG) (IB.prod IG) n φR (b, g) :=
    φR.isLocalDiffeomorph (b, g)
  have h2 : IsLocalDiffeomorphAt (IB.prod IG) IP n Ψ (φR (b, g)) := by
    have hbg : φR (b, g) = (b, 1) := Prod.ext rfl (mul_inv_cancel g)
    rw [hbg]
    exact h_one b hb
  have h3 : IsLocalDiffeomorphAt IP IP n (opSmulDiffeomorph (n := n) hsmul g)
      ((Ψ ∘ φR) (b, g)) :=
    (opSmulDiffeomorph (n := n) hsmul g).isLocalDiffeomorph _
  rw [heq]
  exact (h1.comp IP P h2).comp IP P h3

/-- **Smoothness of the section coordinate `sectionCoord`.** Under the Banach vertical-tangent
hypotheses, for any `C^n` local section `s` of `p` over an open set `U ⊆ B`, the group coordinate
`sectionCoord horbit hs : P → G` is `C^n` on `p ⁻¹' U`. -/
theorem contMDiffOn_sectionCoord (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) :
    ContMDiffOn IP IG n (sectionCoord horbit hs) (p ⁻¹' U) := by
  let Ψ : B × G → P := fun q ↦ op q.2 • s q.1
  have hloc : IsLocalDiffeomorphOn (IB.prod IG) IP n Ψ (U ×ˢ univ) :=
    isLocalDiffeomorphOn_op_smul_section hn hsmul hsub (map_op_smul_of_orbit_iff horbit) hinj hker
      hU hs_smooth hs
  have hinj_Ψ : InjOn Ψ (U ×ˢ univ) := by
    rintro ⟨b₁, g₁⟩ ⟨hb₁, -⟩ ⟨b₂, g₂⟩ ⟨hb₂, -⟩ hEq
    have hb : b₁ = b₂ := by
      have hpEq := congrArg p hEq
      simpa only [Ψ, map_op_smul_of_orbit_iff horbit, hs b₁ hb₁, hs b₂ hb₂] using hpEq
    subst hb
    exact Prod.ext rfl ((op_smul_eq_op_smul_iff_of_free hfree).1 hEq)
  have himg : Ψ '' (U ×ˢ univ) = p ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨⟨b, g⟩, ⟨hb, -⟩, rfl⟩
      simp only [Ψ, mem_preimage, map_op_smul_of_orbit_iff horbit, hs b hb, hb]
    · intro hx
      exact ⟨(p x, sectionCoord horbit hs x), ⟨hx, mem_univ _⟩, op_sectionCoord_smul horbit hs hx⟩
  intro x hx
  -- At any `x ∈ p ⁻¹' U`, `B × G` is inhabited by `(p x, 1)`, so `invFunOn` is `C^n` on `p ⁻¹' U`.
  have : Nonempty (B × G) := ⟨(p x, 1)⟩
  have hinv : ContMDiffOn IP (IB.prod IG) n (invFunOn Ψ (U ×ˢ univ)) (p ⁻¹' U) := by
    rw [← himg]
    exact hloc.contMDiffOn_invFunOn (hU.prod isOpen_univ) hinj_Ψ
  have hcongr : EqOn (sectionCoord horbit hs) (fun y : P ↦ (invFunOn Ψ (U ×ˢ univ) y).2)
      (p ⁻¹' U) := fun y hy ↦ by
    have hmem : (p y, sectionCoord horbit hs y) ∈ U ×ˢ (univ : Set G) := ⟨hy, mem_univ _⟩
    have hΨy : Ψ (p y, sectionCoord horbit hs y) = y := op_sectionCoord_smul horbit hs hy
    have hleft := hinj_Ψ.leftInvOn_invFunOn hmem
    rw [hΨy] at hleft
    exact (congrArg Prod.snd hleft).symm
  exact ((contMDiff_snd.comp_contMDiffOn hinv).congr hcongr) x hx

/-- The unbundled `Bundle.Trivialization G p` attached to a `C^n` local section `s : B → P` over an
open set `U ⊆ B`. -/
def actionTrivializationOfContMDiffSection (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) : Trivialization G p :=
  actionTrivializationOfSection hsub.contMDiff.continuous horbit hfree hU hs
    (contMDiffOn_sectionCoord hn hsmul hsub hfree horbit hinj hker hU hs_smooth hs).continuousOn
    (hsmul.continuous.comp_continuousOn
      ((hs_smooth.continuousOn.comp (s := U ×ˢ (univ : Set G)) continuousOn_fst fun _ hq ↦
        hq.1).prodMk continuousOn_snd))

/-- Forward map of `actionTrivializationOfContMDiffSection`. -/
@[simp]
theorem actionTrivializationOfContMDiffSection_apply (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) (x : P) :
    actionTrivializationOfContMDiffSection hn hsmul hsub hfree horbit hinj hker hU hs_smooth hs x =
      (p x, sectionCoord horbit hs x) := by
  simp [actionTrivializationOfContMDiffSection]

/-- Partial-homeomorphism inverse of `actionTrivializationOfContMDiffSection`. -/
@[simp]
theorem actionTrivializationOfContMDiffSection_symm_apply (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) (q : B × G) :
    (actionTrivializationOfContMDiffSection hn hsmul hsub hfree horbit hinj hker hU hs_smooth
      hs).toOpenPartialHomeomorph.symm q = op q.2 • s q.1 := by
  simp [actionTrivializationOfContMDiffSection]

/-- Base set of `actionTrivializationOfContMDiffSection`. -/
@[simp]
theorem baseSet_actionTrivializationOfContMDiffSection (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) :
    (actionTrivializationOfContMDiffSection hn hsmul hsub hfree horbit hinj hker hU hs_smooth
      hs).baseSet = U := by
  simp [actionTrivializationOfContMDiffSection]

/-- The atlas of all `actionTrivializationOfContMDiffSection`s arising from `C^n` local sections of
`p`. -/
private def submersionTrivializationAtlas (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range) :
    Set (Trivialization G p) :=
  {t | ∃ (U : Set B) (hU : IsOpen U) (s : B → P) (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b),
    t = actionTrivializationOfContMDiffSection hn hsmul hsub hfree horbit hinj hker hU hs_smooth hs}

private theorem exists_mem_submersionTrivializationAtlas (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    (b : B) :
    ∃ t ∈ submersionTrivializationAtlas hn hsmul hsub hfree horbit hinj hker, b ∈ t.baseSet := by
  obtain ⟨x, rfl⟩ := hsurj b
  obtain ⟨U, hU, hxU, s, -, hs_smooth, hs⟩ := (hsub.isSubmersionAt x).exists_contMDiffOn_section
  exact ⟨actionTrivializationOfContMDiffSection hn hsmul hsub hfree horbit hinj hker hU hs_smooth
    hs, ⟨U, hU, s, hs_smooth, hs, rfl⟩, by simpa using hxU⟩

/-- **`FiberBundle` structure on the fibres of a free orbit-exact `C^n` submersion** (Banach
version). Install locally via `letI := fiberBundleOfSubmersion ...`. -/
@[instance_reducible]
def fiberBundleOfSubmersion (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range) :
    FiberBundle G (ProjectionFiber G p) :=
  ProjectionFiber.fiberBundle
    (submersionTrivializationAtlas hn hsmul hsub hfree horbit hinj hker)
    (exists_mem_submersionTrivializationAtlas hn hsmul hsub hsurj hfree horbit hinj hker)

private theorem mem_trivializationAtlas_fiberBundleOfSubmersion (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    (e : Trivialization G (π G (ProjectionFiber G p))) :
    (letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker;
      e ∈ trivializationAtlas G (ProjectionFiber G p)) →
      e ∈ Bundle.Trivialization.projectionFiber ''
        submersionTrivializationAtlas hn hsmul hsub hfree horbit hinj hker := by
  simp

/-- **`PrincipalBundle` structure on the fibres of a free orbit-exact `C^n` submersion** (Banach
version). -/
theorem principalBundleOfSubmersion (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range) :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
    PrincipalBundle G (ProjectionFiber G p) :=
  ProjectionFiber.principalBundle
    (submersionTrivializationAtlas hn hsmul hsub hfree horbit hinj hker)
    (exists_mem_submersionTrivializationAtlas hn hsmul hsub hsurj hfree horbit hinj hker)
    (map_smul_of_orbit_iff horbit)
    fun _ ⟨_, _, _, _, hs, ht⟩ x hx g ↦ by
      subst ht
      simpa using sectionCoord_op_smul horbit hfree hs (by simpa using hx) g

/-- **`ContMDiffFiberBundle` structure on the fibres of a free orbit-exact `C^n` submersion**
(Banach version). Transition functions `b ↦ sectionCoord horbit hs₂ (s₁ b)` are `C^n` on base
overlaps, requiring only `[ContMDiffMul IG n G]`. -/
theorem contMDiffFiberBundleOfSubmersion (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range) :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    ContMDiffFiberBundle n G (ProjectionFiber G p) IB IG := by
  have hatlas := mem_trivializationAtlas_fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit
    hinj hker
  let := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  let := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
  have := principalBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  rw [PrincipalBundle.contMDiffFiberBundle_iff]
  intro e₁ e₂ he₁ he₂
  rcases hatlas e₁ he₁.out with ⟨_, ⟨U₁, hU₁, s₁, hs₁_smooth, hs₁, rfl⟩, rfl⟩
  rcases hatlas e₂ he₂.out with ⟨_, ⟨U₂, hU₂, s₂, hs₂_smooth, hs₂, rfl⟩, rfl⟩
  have hcoord₂ := contMDiffOn_sectionCoord hn hsmul hsub hfree horbit hinj hker hU₂ hs₂_smooth hs₂
  refine (hcoord₂.comp (hs₁_smooth.mono (by simp)) fun b hb ↦ ?_).congr fun b _ ↦ ?_
  · simp only [Trivialization.projectionFiber_baseSet,
      baseSet_actionTrivializationOfContMDiffSection, mem_inter_iff] at hb
    change p (s₁ b) ∈ U₂
    rw [hs₁ b hb.1]
    exact hb.2
  · rw [Trivialization.projectionFiber_coordChange]
    simp [Trivialization.coordChange]

/-- **The charted total space `ManifoldTotalSpace G (ProjectionFiber G p)` is `C^n` diffeomorphic
to `P`.** Together with `principalBundleOfSubmersion` and `contMDiffFiberBundleOfSubmersion`, this
exhibits `p : P → B` as a `C^n` principal `G`-bundle. -/
def diffeomorphManifoldTotalSpaceOfSubmersion (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range) :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    ManifoldTotalSpace G (ProjectionFiber G p) ≃ₘ^n⟮IB.prod IG, IP⟯ P :=
  letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  have := contMDiffFiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  { toEquiv := (ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm.toEquiv.trans
      (ProjectionFiber.totalSpaceEquiv G p)
    contMDiff_toFun := fun q₀ ↦ by
      set z₀ := (ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q₀
      have hmem := mem_trivializationAtlas_fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit
        hinj hker _ (trivialization_mem_atlas G (ProjectionFiber G p) z₀.proj)
      rcases hmem with ⟨_, ⟨U, hU, s, hs_smooth, hs, rfl⟩, ht_eq⟩
      have hz₀U : z₀.proj ∈ U := by
        have hb := mem_baseSet_trivializationAt G (ProjectionFiber G p) z₀.proj
        simpa [← ht_eq] using hb
      have hproj := ManifoldTotalSpace.contMDiff_proj n G (ProjectionFiber G p) IB IG q₀
      have hs_comp : ContMDiffAt (IB.prod IG) IP n
          (fun q ↦ s ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).proj) q₀ :=
        (hs_smooth.contMDiffAt (hU.mem_nhds hz₀U)).comp q₀ hproj
      have hsnd : ContMDiffAt (IB.prod IG) IG n
          (fun q ↦ (trivializationAt G (ProjectionFiber G p) z₀.proj
            ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q)).2) q₀ :=
        ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IG q₀
      refine (hsmul.contMDiffAt.comp q₀ (hs_comp.prodMk hsnd)).congr_of_eventuallyEq ?_
      filter_upwards [hproj.continuousAt (hU.mem_nhds hz₀U)] with q hqU
      set z := (ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q
      have hzp : p z.2.val = z.proj := z.2.map_val
      have hxU : p z.2.val ∈ U := by rwa [hzp]
      simp only [Equiv.trans_apply, Homeomorph.coe_toEquiv, ProjectionFiber.totalSpaceEquiv_apply,
        comp_apply, ← ht_eq, Trivialization.projectionFiber_apply,
        actionTrivializationOfContMDiffSection_apply]
      have hsec := (op_sectionCoord_smul horbit hs hxU).symm
      rwa [hzp] at hsec
    contMDiff_invFun := fun x₀ ↦ by
      refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨?_, ?_⟩
      · exact (hsub.contMDiff x₀).congr_of_eventuallyEq
          (Eventually.of_forall fun x ↦ ProjectionFiber.proj_totalSpaceEquiv_symm G p x)
      · rw [ProjectionFiber.proj_totalSpaceEquiv_symm]
        have hmem := mem_trivializationAtlas_fiberBundleOfSubmersion hn hsmul hsub hsurj hfree
          horbit hinj hker _ (trivialization_mem_atlas G (ProjectionFiber G p) (p x₀))
        rcases hmem with ⟨_, ⟨U, hU, s, hs_smooth, hs, rfl⟩, ht_eq⟩
        have hx₀U : p x₀ ∈ U := by
          have hb := mem_baseSet_trivializationAt G (ProjectionFiber G p) (p x₀)
          simpa [← ht_eq] using hb
        have hcoord := contMDiffOn_sectionCoord hn hsmul hsub hfree horbit hinj hker hU hs_smooth hs
        have hopen : IsOpen (p ⁻¹' U) := hU.preimage hsub.contMDiff.continuous
        refine (hcoord.contMDiffAt (hopen.mem_nhds hx₀U)).congr_of_eventuallyEq ?_
        exact Eventually.of_forall fun x ↦ by
          simp only [← ht_eq, Trivialization.projectionFiber_apply, Equiv.apply_symm_apply,
            actionTrivializationOfContMDiffSection_apply] }

/-- Forward map of `diffeomorphManifoldTotalSpaceOfSubmersion`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersion_apply (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker q =
      ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).2.val :=
  ProjectionFiber.totalSpaceEquiv_apply G p _

/-- Inverse map of `diffeomorphManifoldTotalSpaceOfSubmersion`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersion_symm_apply (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    (x : P) :
    (letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker;
      (diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker).symm
        x) =
      ManifoldTotalSpace.homeomorph G (ProjectionFiber G p) ⟨p x, ⟨x, rfl⟩⟩ :=
  congrArg (ManifoldTotalSpace.homeomorph G (ProjectionFiber G p))
    (ProjectionFiber.totalSpaceEquiv_symm_apply G p x)

/-- `diffeomorphManifoldTotalSpaceOfSubmersion` commutes with the projections onto `B`. -/
theorem proj_diffeomorphManifoldTotalSpaceOfSubmersion (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    p (diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker q) =
      ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).proj := by
  rw [diffeomorphManifoldTotalSpaceOfSubmersion_apply]
  exact ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).2.map_val

/-- `diffeomorphManifoldTotalSpaceOfSubmersion` is `G`-equivariant for the right `G`-actions. -/
theorem diffeomorphManifoldTotalSpaceOfSubmersion_op_smul (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    (g : G) (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    (letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit);
      diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
        (op g • q)) =
      op g • diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
        q := by
  let := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
  rw [diffeomorphManifoldTotalSpaceOfSubmersion_apply,
    diffeomorphManifoldTotalSpaceOfSubmersion_apply, ManifoldTotalSpace.homeomorph_symm_smul]
  exact ProjectionFiber.val_smul G (map_smul_of_orbit_iff horbit) (op g) _

end Banach

section ActionDivisionSmooth

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ∞ω}
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP] [CompleteSpace EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP} [IP.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP n P]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [CompleteSpace EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [LieGroup IG n G] [MulAction Gᵐᵒᵖ P]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- **Smoothness of `actionDivision` along families in a common fibre** (`ContMDiffWithinAt` form).
When `G` is a `C^n` Lie group (`1 ≤ n`), for any two `C^n` maps `f₁, f₂ : M → P` with
`p (f₁ x) = p (f₂ x)`, the transition map `x ↦ actionDivision horbit (hf x)` is `C^n`. -/
theorem _root_.ContMDiffWithinAt.actionDivision (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {f₁ f₂ : M → P} (hf : ∀ x : M, p (f₁ x) = p (f₂ x)) {s : Set M} {x₀ : M}
    (hf₁ : ContMDiffWithinAt IM IP n f₁ s x₀) (hf₂ : ContMDiffWithinAt IM IP n f₂ s x₀) :
    ContMDiffWithinAt IM IG n (fun x ↦ actionDivision horbit (hf x)) s x₀ := by
  let := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  let := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
  have := principalBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  have := contMDiffFiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  let Φ := diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  let q₁ : ∀ x : M, ProjectionFiber G p (p (f₁ x)) := fun x ↦ ⟨f₁ x, rfl⟩
  let q₂ : ∀ x : M, ProjectionFiber G p (p (f₁ x)) := fun x ↦ ⟨f₂ x, (hf x).symm⟩
  have hq₁_eq : (fun x ↦ ManifoldTotalSpace.homeomorph G (ProjectionFiber G p) ⟨p (f₁ x), q₁ x⟩) =
      fun x ↦ Φ.symm (f₁ x) := funext fun x ↦
    (diffeomorphManifoldTotalSpaceOfSubmersion_symm_apply hn hsmul hsub hsurj hfree horbit hinj
      hker (f₁ x)).symm
  have hq₁ : ContMDiffWithinAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G (ProjectionFiber G p) ⟨p (f₁ x), q₁ x⟩) s x₀ := by
    rw [hq₁_eq]
    exact Φ.symm.contMDiff.contMDiffAt.comp_contMDiffWithinAt x₀ hf₁
  have hq₂_eq : (fun x ↦ ManifoldTotalSpace.homeomorph G (ProjectionFiber G p) ⟨p (f₁ x), q₂ x⟩) =
      fun x ↦ Φ.symm (f₂ x) := funext fun x ↦ by
    have hz : (⟨p (f₁ x), q₂ x⟩ : TotalSpace G (ProjectionFiber G p)) = ⟨p (f₂ x), ⟨f₂ x, rfl⟩⟩ :=
      (ProjectionFiber.totalSpaceEquiv G p).injective (by simp [q₂])
    rw [hz]
    exact (diffeomorphManifoldTotalSpaceOfSubmersion_symm_apply hn hsmul hsub hsurj hfree horbit
      hinj hker (f₂ x)).symm
  have hq₂ : ContMDiffWithinAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G (ProjectionFiber G p) ⟨p (f₁ x), q₂ x⟩) s x₀ := by
    rw [hq₂_eq]
    exact Φ.symm.contMDiff.contMDiffAt.comp_contMDiffWithinAt x₀ hf₂
  exact (hq₁.division hq₂).congr_of_eventuallyEq
    (Eventually.of_forall fun x ↦ (division_projectionFiber_eq_actionDivision horbit
      (q₁ x) (q₂ x)).symm)
    (division_projectionFiber_eq_actionDivision horbit (q₁ x₀) (q₂ x₀)).symm

/-- `ContMDiffAt` form of `ContMDiffWithinAt.actionDivision`. -/
theorem _root_.ContMDiffAt.actionDivision (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {f₁ f₂ : M → P} (hf : ∀ x : M, p (f₁ x) = p (f₂ x)) {x₀ : M}
    (hf₁ : ContMDiffAt IM IP n f₁ x₀) (hf₂ : ContMDiffAt IM IP n f₂ x₀) :
    ContMDiffAt IM IG n (fun x ↦ actionDivision horbit (hf x)) x₀ :=
  ContMDiffWithinAt.actionDivision hn hsmul hsub hsurj hfree horbit hinj hker hf hf₁ hf₂

/-- `ContMDiffOn` form of `ContMDiffWithinAt.actionDivision`. -/
theorem _root_.ContMDiffOn.actionDivision (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {f₁ f₂ : M → P} (hf : ∀ x : M, p (f₁ x) = p (f₂ x)) {s : Set M}
    (hf₁ : ContMDiffOn IM IP n f₁ s) (hf₂ : ContMDiffOn IM IP n f₂ s) :
    ContMDiffOn IM IG n (fun x ↦ actionDivision horbit (hf x)) s :=
  fun x hx ↦ ContMDiffWithinAt.actionDivision hn hsmul hsub hsurj hfree horbit hinj hker hf
    (hf₁ x hx) (hf₂ x hx)

/-- `ContMDiff` form of `ContMDiffWithinAt.actionDivision`. -/
theorem _root_.ContMDiff.actionDivision (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
    {f₁ f₂ : M → P} (hf : ∀ x : M, p (f₁ x) = p (f₂ x))
    (hf₁ : ContMDiff IM IP n f₁) (hf₂ : ContMDiff IM IP n f₂) :
    ContMDiff IM IG n fun x ↦ actionDivision horbit (hf x) :=
  fun x ↦ ContMDiffAt.actionDivision hn hsmul hsub hsurj hfree horbit hinj hker hf (hf₁ x) (hf₂ x)

end ActionDivisionSmooth

section FiniteDimensional

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ∞ω}
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP] [FiniteDimensional 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP} [IP.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP n P]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [FiniteDimensional 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [FiniteDimensional 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [ContMDiffMul IG n G] [MulAction Gᵐᵒᵖ P]

omit [IP.Boundaryless] [FiniteDimensional 𝕜 EB] [FiniteDimensional 𝕜 EG] in
/-- In finite dimensions over `𝕜`, injectivity of `d(g ↦ op g • x)_1` together with
`finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG` implies that the orbit differential spans
`ker (dp_x)`. -/
theorem range_mfderiv_op_smul_one_eq_ker_of_finrank_eq (hn : 1 ≤ n)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (horbit_inv : ∀ (g : G) (x : P), p (op g • x) = p x)
    (x : P) (hinj : Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) :
    (mfderiv IG IP (fun g : G ↦ op g • x) 1).range = (mfderiv IP IB p x).ker := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have hreg : IsRegularPoint IP IB p (op (1 : G) • x) := by
    rw [op_one, one_smul, isRegularPoint_iff]
    exact hsub.surjective_mfderiv hn0 x
  let dpAt (w : P) : EP →L[𝕜] EB := mfderiv IP IB p w
  let dorb : EG →L[𝕜] EP := mfderiv IG IP (fun g : G ↦ op g • x) 1
  have h : dorb.toLinearMap.range = (dpAt (op (1 : G) • x)).toLinearMap.ker :=
    IsRegularPoint.range_mfderiv_eq_ker_mfderiv (I := IP) (J := IB) (K := IG)
      (f := p) (g := fun g : G ↦ op g • x) (p := (1 : G)) (y := p x)
      (Eventually.of_forall fun g : G ↦ horbit_inv g x) hreg hinj (by omega)
  exact h.trans (congrArg (fun w ↦ (dpAt w).toLinearMap.ker) (by rw [op_one, one_smul]))

/-- Finite-dimensional `C^n` `FiberBundle` constructor on `ProjectionFiber G p` from orbit
injectivity and `P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG`. -/
@[instance_reducible]
def fiberBundleOfSubmersionOfFinrankEq (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) :
    FiberBundle G (ProjectionFiber G p) :=
  have := FiniteDimensional.completeSpace 𝕜 EP
  have := FiniteDimensional.completeSpace 𝕜 EB
  have := FiniteDimensional.completeSpace 𝕜 EG
  fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj fun x ↦
    (range_mfderiv_op_smul_one_eq_ker_of_finrank_eq hn hsub (map_op_smul_of_orbit_iff horbit) x
      (hinj x) (hdim x)).ge

/-- Finite-dimensional `C^n` `PrincipalBundle` constructor on `ProjectionFiber G p`. -/
theorem principalBundleOfSubmersionOfFinrankEq (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) :
    letI := fiberBundleOfSubmersionOfFinrankEq hn hsmul hsub hsurj hfree horbit hinj hdim
    letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
    PrincipalBundle G (ProjectionFiber G p) :=
  have := FiniteDimensional.completeSpace 𝕜 EP
  have := FiniteDimensional.completeSpace 𝕜 EB
  have := FiniteDimensional.completeSpace 𝕜 EG
  principalBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj fun x ↦
    (range_mfderiv_op_smul_one_eq_ker_of_finrank_eq hn hsub (map_op_smul_of_orbit_iff horbit) x
      (hinj x) (hdim x)).ge

/-- Finite-dimensional `C^n` `ContMDiffFiberBundle` constructor on `ProjectionFiber G p`. -/
theorem contMDiffFiberBundleOfSubmersionOfFinrankEq (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) :
    letI := fiberBundleOfSubmersionOfFinrankEq hn hsmul hsub hsurj hfree horbit hinj hdim
    ContMDiffFiberBundle n G (ProjectionFiber G p) IB IG :=
  have := FiniteDimensional.completeSpace 𝕜 EP
  have := FiniteDimensional.completeSpace 𝕜 EB
  have := FiniteDimensional.completeSpace 𝕜 EG
  contMDiffFiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj fun x ↦
    (range_mfderiv_op_smul_one_eq_ker_of_finrank_eq hn hsub (map_op_smul_of_orbit_iff horbit) x
      (hinj x) (hdim x)).ge

/-- Finite-dimensional `C^n` diffeomorphism
`ManifoldTotalSpace G (ProjectionFiber G p) ≃ₘ^n⟮IB.prod IG, IP⟯ P`. -/
def diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) :
    letI := fiberBundleOfSubmersionOfFinrankEq hn hsmul hsub hsurj hfree horbit hinj hdim
    ManifoldTotalSpace G (ProjectionFiber G p) ≃ₘ^n⟮IB.prod IG, IP⟯ P :=
  have := FiniteDimensional.completeSpace 𝕜 EP
  have := FiniteDimensional.completeSpace 𝕜 EB
  have := FiniteDimensional.completeSpace 𝕜 EG
  diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj fun x ↦
    (range_mfderiv_op_smul_one_eq_ker_of_finrank_eq hn hsub (map_op_smul_of_orbit_iff horbit) x
      (hinj x) (hdim x)).ge

/-- Forward map of `diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq_apply (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG)
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq hn hsmul hsub hsurj hfree horbit hinj
      hdim q = ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).2.val :=
  ProjectionFiber.totalSpaceEquiv_apply G p _

/-- Inverse map of `diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq_symm_apply (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) (x : P) :
    (letI := fiberBundleOfSubmersionOfFinrankEq hn hsmul hsub hsurj hfree horbit hinj hdim;
      (diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq hn hsmul hsub hsurj hfree horbit hinj
        hdim).symm x) =
      ManifoldTotalSpace.homeomorph G (ProjectionFiber G p) ⟨p x, ⟨x, rfl⟩⟩ :=
  congrArg (ManifoldTotalSpace.homeomorph G (ProjectionFiber G p))
    (ProjectionFiber.totalSpaceEquiv_symm_apply G p x)

/-- `diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq` commutes with the projections onto
`B`. -/
theorem proj_diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG)
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    p (diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq hn hsmul hsub hsurj hfree horbit hinj
        hdim q) = ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).proj := by
  rw [diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq_apply]
  exact ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).2.map_val

/-- `diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq` is `G`-equivariant for the right
`G`-actions. -/
theorem diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq_op_smul (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG)
    (g : G) (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    (letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit);
      diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq hn hsmul hsub hsurj hfree horbit hinj
        hdim (op g • q)) =
      op g • diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq hn hsmul hsub hsurj hfree horbit
        hinj hdim q := by
  have := FiniteDimensional.completeSpace 𝕜 EP
  have := FiniteDimensional.completeSpace 𝕜 EB
  have := FiniteDimensional.completeSpace 𝕜 EG
  exact diffeomorphManifoldTotalSpaceOfSubmersion_op_smul hn hsmul hsub hsurj hfree horbit hinj
    (fun x ↦ (range_mfderiv_op_smul_one_eq_ker_of_finrank_eq hn hsub
      (map_op_smul_of_orbit_iff horbit) x (hinj x) (hdim x)).ge) g q

end FiniteDimensional

end TauCeti.PrincipalBundle
