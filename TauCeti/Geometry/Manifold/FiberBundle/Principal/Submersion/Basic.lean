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
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Topology.FiberBundle.Principal.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.Basic

/-!
# Smooth principal bundles from free orbit-exact submersions

This file constructs `C^n` principal `G`-bundle structures on `TauCeti.ProjectionFiber G p` for an
unbundled surjective `C^n` submersion `p : P → B` (`1 ≤ n`) with a free `C^n` right action of a
group manifold `G` whose orbits are the fibres of `p` (the automatic real Lie-group version,
Kolář–Michor–Slovák Lemma 10.3, follows in
`TauCeti.Geometry.Manifold.FiberBundle.Principal.Submersion.LieGroup`):

1. **Banach `C^n` criterion (`1 ≤ n`, over `RCLike 𝕜`):** for boundaryless Banach `P` and
   `[ContMDiffMul IG n G]`, if at every `x : P` the orbit differential `d(g ↦ op g • x)_1` is
   injective and spans `ker (dp_x)`, then the action sweep `(b, g) ↦ op g • s b` of any `C^n` local
   section `s` over open `U ⊆ B` is a `C^n` local diffeomorphism on `U ×ˢ univ`; when the action
   is also free along `s` and orbit-exact it is injective with image `p ⁻¹' U`, which gives
   `contMDiffOn_sectionCoord`, `C^n` principal bundle structures on `ProjectionFiber G p`, and a
   `G`-equivariant `C^n` diffeomorphism `ManifoldTotalSpace G (ProjectionFiber G p) ≃ₘ^n P`
   over `B`.
2. **Finite-dimensional `C^n` criterion (`1 ≤ n`, over `𝕜`):** injectivity of `d(g ↦ op g • x)_1`
   and `P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG` imply the vertical-range condition by
   rank-nullity (`ker_le_range_of_finrank_eq`), and `contMDiffOn_sectionCoord_of_finrank_eq` gives
   local `C^n` smoothness of `sectionCoord`.

## Main definitions and results

* `TauCeti.PrincipalBundle.range_mfderiv_op_smul_one_le_ker`,
  `range_mfderiv_op_smul_one_eq_ker_of_finrank_eq`,
  `isRegularValue_of_isRegularPoint_of_orbit_eq_fiber`: vertical tangent and regularity lemmas.
* `TauCeti.PrincipalBundle.isLocalDiffeomorphOn_op_smul_section`, `contMDiffOn_sectionCoord`,
  `actionTrivializationOfContMDiffSection`: action sweep local diffeomorphism and `C^n` section
  coordinates.
* `TauCeti.PrincipalBundle.fiberBundleOfSubmersion`,
  `mem_trivializationAtlas_fiberBundleOfSubmersion_iff`, `principalBundleOfSubmersion`,
  `contMDiffFiberBundleOfSubmersion`, `diffeomorphManifoldTotalSpaceOfSubmersion`: Banach `C^n`
  principal bundle structures, atlas characterization, and total-space diffeomorphism.
* `TauCeti.PrincipalBundle.contMDiffWithinAt_actionDivision_of_section`,
  `contMDiffWithinAt_actionDivision`, `contMDiffAt_actionDivision`, `contMDiffOn_actionDivision`,
  `contMDiff_actionDivision`: `C^n` regularity of `actionDivision` for a `C^n` Lie group `G`.
* `TauCeti.PrincipalBundle.contMDiffOn_sectionCoord_of_finrank_eq`,
  `ker_le_range_of_finrank_eq`: finite-dimensional `C^n` section smoothness and vertical-range
  reduction.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.3, Lemma 10.3.
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Ch. 4, 5, 21.
-/

public section

noncomputable section

open Bundle Filter Function Manifold Module MulOpposite Set Topology
open scoped ContDiff Manifold

namespace TauCeti.PrincipalBundle

section ManifoldBase

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G]

section VerticalTangent

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  [Monoid G] [MulAction Gᵐᵒᵖ P]

/-- For a map `p : P → B` that is constant on the right `G`-orbit of `x : P`, the image of the
orbit differential `d(g ↦ op g • x)_1` lies in `ker (dp_x)`. -/
theorem range_mfderiv_op_smul_one_le_ker {p : P → B} {x : P}
    (horbit_inv : ∀ g : G, p (op g • x) = p x) :
    (mfderiv IG IP (fun g : G ↦ op g • x) 1).range ≤ (mfderiv IP IB p x).ker := by
  have hx : op (1 : G) • x = x := by rw [op_one, one_smul]
  have h := range_mfderiv_le_ker_mfderiv_of_eventually_eq (K := IG) (I := IP) (J := IB)
    (f := p) (g := fun g : G ↦ op g • x) (p := (1 : G)) (y := p x)
    (Eventually.of_forall horbit_inv)
  exact h.trans_eq (congrArg (fun L : EP →L[𝕜] EB ↦ L.ker)
    (mfderiv_congr_point (I := IP) (I' := IB) (f := p) hx))

/-- At a regular point `x` of a map `p : P → B` constant on the right `G`-orbit of `x` in finite
dimensions over `𝕜`, injectivity of `d(g ↦ op g • x)_1` and
`finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG` imply the orbit differential spans `ker (dp_x)`. -/
theorem range_mfderiv_op_smul_one_eq_ker_of_finrank_eq [FiniteDimensional 𝕜 EP]
    {p : P → B} {x : P} (hreg : IsRegularPoint IP IB p x)
    (horbit_inv : ∀ g : G, p (op g • x) = p x)
    (hinj : Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) :
    (mfderiv IG IP (fun g : G ↦ op g • x) 1).range = (mfderiv IP IB p x).ker := by
  have hx : op (1 : G) • x = x := by rw [op_one, one_smul]
  have h := IsRegularPoint.range_mfderiv_eq_ker_mfderiv (I := IP) (J := IB) (K := IG)
    (f := p) (g := fun g : G ↦ op g • x) (p := (1 : G)) (y := p x)
    (Eventually.of_forall horbit_inv) (hx.symm ▸ hreg) hinj (by omega)
  exact h.trans (congrArg (fun L : EP →L[𝕜] EB ↦ L.ker)
    (mfderiv_congr_point (I := IP) (I' := IB) (f := p) hx))

omit [TopologicalSpace G] in
/-- If `p : P → B` is invariant under a differentiable right `G`-action transitive on `p ⁻¹' {p x}`
and `p` is differentiable along that fibre, regularity at `x` implies `p x` is a regular value. -/
theorem isRegularValue_of_isRegularPoint_of_orbit_eq_fiber {p : P → B} {x : P}
    (hp : ∀ y : P, p y = p x → MDifferentiableAt IP IB p y)
    (hsmul : ∀ g : G, MDifferentiableAt IP IP (fun z : P ↦ op g • z) x)
    (horbit_inv : ∀ (g : G) (z : P), p (op g • z) = p z)
    (horbit : ∀ y : P, p x = p y → ∃ g : G, op g • x = y)
    (hreg : IsRegularPoint IP IB p x) : IsRegularValue IP IB p (p x) := by
  rw [isRegularValue_iff]; intro y hy
  obtain ⟨g, rfl⟩ := horbit y hy.symm
  have hcomp : (mfderiv IP IB p x : EP →L[𝕜] EB) =
      (mfderiv IP IB p (op g • x) : EP →L[𝕜] EB).comp
        (mfderiv IP IP (fun z : P ↦ op g • z) x : EP →L[𝕜] EP) :=
    (mfderiv_congr (funext fun z ↦ (horbit_inv g z).symm)).trans
      (mfderiv_comp (I := IP) (I' := IP) (I'' := IB) x (hp _ hy) (hsmul g))
  rw [isRegularPoint_iff] at hreg ⊢
  have hsurj : Surjective ((mfderiv IP IB p (op g • x) : EP →L[𝕜] EB).comp
      (mfderiv IP IP (fun z : P ↦ op g • z) x : EP →L[𝕜] EP)) := hcomp ▸ hreg
  rw [ContinuousLinearMap.coe_comp] at hsurj; exact hsurj.of_comp

end VerticalTangent

/-- If `p : P → B` is continuous and admits a local section `σ` over an open neighbourhood `U` of
`p (f₁ x₀)` whose `sectionCoord` is `C^n` on `p ⁻¹' U`, then `x ↦ actionDivision horbit (hf x)` is
`C^n` within `s` at `x₀` for any `f₁, f₂ : M → P` that are `C^n` within `s` at `x₀` and satisfy
`p (f₁ x) = p (f₂ x)`. -/
theorem contMDiffWithinAt_actionDivision_of_section {n : ℕ∞ω} {B : Type*} [TopologicalSpace B]
    [Group G] [LieGroup IG n G] [MulAction Gᵐᵒᵖ P]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {p : P → B} (hp : Continuous p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {U : Set B} (hU : IsOpen U) {σ : B → P} (hσ : ∀ b ∈ U, p (σ b) = b)
    (hcoord : ContMDiffOn IP IG n (sectionCoord horbit hσ) (p ⁻¹' U))
    {f₁ f₂ : M → P} (hf : ∀ x : M, p (f₁ x) = p (f₂ x)) {s : Set M} {x₀ : M}
    (hx₀U : p (f₁ x₀) ∈ U) (hf₁ : ContMDiffWithinAt IM IP n f₁ s x₀)
    (hf₂ : ContMDiffWithinAt IM IP n f₂ s x₀) :
    ContMDiffWithinAt IM IG n (fun x ↦ actionDivision horbit (hf x)) s x₀ := by
  have hopen : IsOpen (p ⁻¹' U) := hU.preimage hp
  have h1 := (hcoord.contMDiffAt (hopen.mem_nhds hx₀U)).comp_contMDiffWithinAt x₀ hf₁
  have h2 := (hcoord.contMDiffAt
    (hopen.mem_nhds (by rwa [mem_preimage, ← hf x₀]))).comp_contMDiffWithinAt x₀ hf₂
  refine (h1.inv.mul h2).congr_of_eventuallyEq ?_
    (actionDivision_eq_inv_sectionCoord_mul_sectionCoord horbit hfree hσ hx₀U (hf x₀))
  filter_upwards [hf₁.continuousWithinAt.preimage_mem_nhdsWithin (hopen.mem_nhds hx₀U)] with x hx
  exact actionDivision_eq_inv_sectionCoord_mul_sectionCoord horbit hfree hσ hx (hf x)

end ManifoldBase

section Banach

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ∞ω}
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP] [CompleteSpace EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP n P]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [CompleteSpace EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G] [MulAction Gᵐᵒᵖ P]

section LocalSection

variable [BoundarylessManifold IP P] [ContMDiffMul IG n G]

omit [CompleteSpace EP] [IsManifold IP n P] [BoundarylessManifold IP P]
  [CompleteSpace EB] [IsManifold IB n B] [CompleteSpace EG] [ContMDiffMul IG n G] in
private theorem contMDiffOn_op_smul_section
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {U : Set B} {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U) :
    ContMDiffOn (IB.prod IG) IP n (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ) :=
  hsmul.comp_contMDiffOn ((hs_smooth.comp (s := U ×ˢ univ) contMDiffOn_fst fun _ hq ↦ hq.1).prodMk
    contMDiffOn_snd)

variable (hn : 1 ≤ n) (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
  {p : P → B} (hp : ContMDiff IP IB n p)

include hn hsmul hp

omit [CompleteSpace EP] [IsManifold IP n P] [BoundarylessManifold IP P] [CompleteSpace EB]
  [IsManifold IB n B] [CompleteSpace EG] [ContMDiffMul IG n G] in
private theorem bijective_mfderiv_op_smul_section_one {U : Set B} (hU : IsOpen U) {s : B → P}
    (hs_smooth : ContMDiffOn IB IP n s U) (hs : ∀ b ∈ U, p (s b) = b) {b : B} (hb : b ∈ U)
    (horbit_inv : ∀ g : G, p (op g • s b) = p (s b))
    (hinj : Injective (mfderiv IG IP (fun g : G ↦ op g • s b) 1))
    (hker : (mfderiv IP IB p (s b)).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • s b) 1).range) :
    Bijective (mfderiv (IB.prod IG) IP (fun q : B × G ↦ op q.2 • s q.1) (b, 1)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  let Ψ : B × G → P := fun q ↦ op q.2 • s q.1
  have hΨ_diff : MDifferentiableAt (IB.prod IG) IP Ψ (b, 1) :=
    ((contMDiffOn_op_smul_section hsmul hs_smooth).contMDiffAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hb, mem_univ _⟩)).mdifferentiableAt hn0
  let dΨ : EB × EG →L[𝕜] EP := mfderiv (IB.prod IG) IP Ψ (b, 1)
  let ds : EB →L[𝕜] EP := mfderiv IB IP s b
  let dorb : EG →L[𝕜] EP := mfderiv IG IP (fun g : G ↦ op g • s b) 1
  let dp : EP →L[𝕜] EB := mfderiv IP IB p (s b)
  have hdecomp (u : EB) (w : EG) : dΨ (u, w) = ds u + dorb w := by
    have h1 : (mfderiv IB IP (fun b' : B ↦ Ψ (b', (1 : G))) b : EB →L[𝕜] EP) = ds :=
      mfderiv_congr (funext fun b' ↦ by simp only [Ψ, op_one, one_smul])
    exact (mfderiv_prod_eq_add_apply (I := IB) (I' := IG) (I'' := IP) (v := (u, w)) hΨ_diff).trans
      (by dsimp only; exact congrArg (· + dorb w) (DFunLike.congr_fun h1 u))
  have hps (u : EB) : dp (ds u) = u :=
    mfderiv_apply_mfderiv_of_eventuallyEq_id ((hp (s b)).mdifferentiableAt hn0)
      ((hs_smooth.contMDiffAt (hU.mem_nhds hb)).mdifferentiableAt hn0)
      (eventually_of_mem (hU.mem_nhds hb) hs) u
  have horb_ker : dorb.range ≤ dp.ker := range_mfderiv_op_smul_one_le_ker horbit_inv
  refine ⟨(injective_iff_map_eq_zero dΨ).2 fun ⟨u, w⟩ huw ↦ ?_, fun (v : EP) ↦ ?_⟩
  · have huw' : ds u + dorb w = 0 := (hdecomp u w).symm.trans huw
    have hw0 : dp (dorb w) = 0 := horb_ker ⟨w, rfl⟩
    have hu0 : u = 0 := by simpa [hps u, hw0] using congrArg dp huw'
    subst hu0; rw [map_zero, zero_add] at huw'
    exact Prod.ext rfl (hinj (huw'.trans (map_zero dorb).symm))
  · have hvert : v - ds (dp v) ∈ dp.ker := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hps (dp v), sub_self]
    obtain ⟨w, hw⟩ : ∃ w : EG, dorb w = v - ds (dp v) := hker hvert
    exact ⟨(dp v, w), (hdecomp (dp v) w).trans (by rw [hw, add_sub_cancel])⟩

/-- **Action sweep of a local section is a `C^n` local diffeomorphism.** Over an open set `U ⊆ B`
supporting a `C^n` local section `s` of `p : P → B` (`1 ≤ n`) whose orbits are preserved by `p`, if
`d(g ↦ op g • s b)_1` is injective and spans `ker (dp_{s b})` for all `b ∈ U`, then
`(b, g) ↦ op g • s b` is a `C^n` local diffeomorphism on `U ×ˢ univ`. -/
theorem isLocalDiffeomorphOn_op_smul_section {U : Set B} (hU : IsOpen U) {s : B → P}
    (hs_smooth : ContMDiffOn IB IP n s U) (hs : ∀ b ∈ U, p (s b) = b)
    (horbit_inv : ∀ b ∈ U, ∀ g : G, p (op g • s b) = p (s b))
    (hinj : ∀ b ∈ U, Injective (mfderiv IG IP (fun g : G ↦ op g • s b) 1))
    (hker : ∀ b ∈ U,
      (mfderiv IP IB p (s b)).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • s b) 1).range) :
    IsLocalDiffeomorphOn (IB.prod IG) IP n (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have : IsManifold IP 1 P := .of_le hn; have : IsManifold IB 1 B := .of_le hn
  have : IsManifold IG 1 G := .of_le hn
  set Ψ : B × G → P := fun q ↦ op q.2 • s q.1
  have h_one : ∀ b ∈ U, IsLocalDiffeomorphAt (IB.prod IG) IP n Ψ (b, 1) := fun b hb ↦ by
    let dΨ : EB × EG →L[𝕜] EP := mfderiv (IB.prod IG) IP Ψ (b, 1)
    have hbij : Bijective dΨ := bijective_mfderiv_op_smul_section_one hn hsmul hp hU hs_smooth hs
      hb (horbit_inv b hb) (hinj b hb) (hker b hb)
    let e : (EB × EG) ≃L[𝕜] EP := ContinuousLinearEquiv.ofBijective dΨ
      (LinearMap.ker_eq_bot_of_injective hbij.1) (LinearMap.range_eq_top_of_surjective _ hbij.2)
    have hbI : IB.IsInteriorPoint b := hs b hb ▸
      ((hp (s b)).mdifferentiableAt hn0).isInteriorPoint_of_surjective_mfderiv
        (surjective_mfderiv_of_eventuallyEq_id ((hp (s b)).mdifferentiableAt hn0)
          ((hs_smooth.contMDiffAt (hU.mem_nhds hb)).mdifferentiableAt hn0)
          (eventually_of_mem (hU.mem_nhds hb) hs))
        BoundarylessManifold.isInteriorPoint
    have hb1I : (IB.prod IG).IsInteriorPoint (b, (1 : G)) :=
      (IB.interior_prod (J := IG) (M := B) (N := G)).ge
        ⟨hbI, ContMDiffMul.isInteriorPoint (n := n) hn0 1⟩
    exact isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_op_smul_section hsmul hs_smooth)
      (hU.prod isOpen_univ) ⟨hb, mem_univ _⟩ hb1I hn (e := e)
      (ContinuousLinearEquiv.coe_ofBijective dΨ _ _)
  have : ContMDiffConstSMul IP n Gᵐᵒᵖ P := hsmul.contMDiffConstSMul_op
  rintro ⟨⟨b, g⟩, hb, -⟩
  let φR : (B × G) ≃ₘ^n⟮IB.prod IG, IB.prod IG⟯ (B × G) :=
    (Diffeomorph.refl IB B n).prodCongr (Diffeomorph.constSmul IG n (op g⁻¹))
  let φL : P ≃ₘ^n⟮IP, IP⟯ P := Diffeomorph.constSmul IP n (op g)
  have heq : Ψ = φL ∘ (Ψ ∘ φR) := funext fun ⟨b', h⟩ ↦ by
    simp only [comp_apply, Ψ, φR, φL, Diffeomorph.coe_prodCongr, Prod.map_apply,
      Diffeomorph.coe_refl, id_eq, Diffeomorph.constSmul_apply, op_smul_eq_mul, ← mul_smul,
      ← op_mul, inv_mul_cancel_right]
  have hbg' : φR (b, g) = (b, 1) := by simp [φR, Diffeomorph.constSmul_apply]
  rw [heq]
  exact ((φR.isLocalDiffeomorph (b, g)).comp IP P (hbg'.symm ▸ h_one b hb)).comp IP P
    (φL.isLocalDiffeomorph _)

/-- **Smoothness of `sectionCoord`.** Under the Banach vertical-tangent hypotheses along a `C^n`
local section `s` of `p : P → B` (`1 ≤ n`) over open `U ⊆ B` for a jointly `C^n` orbit-exact right
`G`-action free along `s`, `sectionCoord horbit hs : P → G` is `C^n` on `p ⁻¹' U`. -/
theorem contMDiffOn_sectionCoord
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1)
    (hinj : ∀ b ∈ U, Injective (mfderiv IG IP (fun g : G ↦ op g • s b) 1))
    (hker : ∀ b ∈ U,
      (mfderiv IP IB p (s b)).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • s b) 1).range) :
    ContMDiffOn IP IG n (sectionCoord horbit hs) (p ⁻¹' U) := by
  let Ψ : B × G → P := fun q ↦ op q.2 • s q.1
  have hloc : IsLocalDiffeomorphOn (IB.prod IG) IP n Ψ (U ×ˢ univ) :=
    isLocalDiffeomorphOn_op_smul_section hn hsmul hp hU hs_smooth hs
      (fun b _ g ↦ map_op_smul_of_orbit_iff horbit g (s b)) hinj hker
  have hinj_Ψ : InjOn Ψ (U ×ˢ univ) := by
    rintro ⟨b₁, g₁⟩ ⟨hb₁, -⟩ ⟨b₂, g₂⟩ ⟨hb₂, -⟩ hEq
    have hb : b₁ = b₂ := by
      simpa only [Ψ, map_op_smul_of_orbit_iff horbit, hs b₁ hb₁, hs b₂ hb₂] using congrArg p hEq
    subst hb
    exact Prod.ext rfl ((op_smul_eq_op_smul_iff_of_op_smul_eq_self_imp (hfree b₁ hb₁)).1 hEq)
  have himg : Ψ '' (U ×ˢ univ) = p ⁻¹' U := subset_antisymm
    (by rintro _ ⟨⟨b, g⟩, ⟨hb, -⟩, rfl⟩; simp [Ψ, map_op_smul_of_orbit_iff horbit, hs b hb, hb])
    fun x hx ↦ ⟨(p x, sectionCoord horbit hs x), ⟨hx, mem_univ _⟩,
      op_sectionCoord_smul horbit hs hx⟩
  intro x hx
  have : Nonempty (B × G) := ⟨(p x, 1)⟩
  have hinv : ContMDiffOn IP (IB.prod IG) n (invFunOn Ψ (U ×ˢ univ)) (p ⁻¹' U) :=
    himg ▸ hloc.contMDiffOn_invFunOn (hU.prod isOpen_univ) hinj_Ψ
  have hcongr : EqOn (sectionCoord horbit hs) (fun y : P ↦ (invFunOn Ψ (U ×ˢ univ) y).2)
      (p ⁻¹' U) := fun y hy ↦ by
    have hleft := hinj_Ψ.leftInvOn_invFunOn (x := (p y, sectionCoord horbit hs y)) ⟨hy, mem_univ _⟩
    dsimp only [Ψ] at hleft; rw [op_sectionCoord_smul horbit hs hy] at hleft
    exact (congrArg Prod.snd hleft).symm
  exact ((contMDiff_snd.comp_contMDiffOn hinv).congr hcongr) x hx

section ActionTriv

variable (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
  (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y) {U : Set B} (hU : IsOpen U)
  {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U) (hs : ∀ b ∈ U, p (s b) = b)
  (hinj : ∀ b ∈ U, Injective (mfderiv IG IP (fun g : G ↦ op g • s b) 1))
  (hker : ∀ b ∈ U,
    (mfderiv IP IB p (s b)).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • s b) 1).range)

/-- The unbundled `Bundle.Trivialization G p` attached to a `C^n` local section `s : B → P` over an
open set `U ⊆ B`. -/
def actionTrivializationOfContMDiffSection : Trivialization G p :=
  actionTrivializationOfSection hp.continuous horbit hfree hU hs
    (contMDiffOn_sectionCoord hn hsmul hp horbit hU hs_smooth hs (fun b _ ↦ hfree (s b)) hinj
      hker).continuousOn
    (contMDiffOn_op_smul_section hsmul hs_smooth).continuousOn

/-- Forward map of `actionTrivializationOfContMDiffSection`. -/
@[simp]
theorem actionTrivializationOfContMDiffSection_apply (x : P) :
    actionTrivializationOfContMDiffSection hn hsmul hp hfree horbit hU hs_smooth hs hinj hker x =
      (p x, sectionCoord horbit hs x) := by simp [actionTrivializationOfContMDiffSection]

/-- Partial-homeomorphism inverse of `actionTrivializationOfContMDiffSection`. -/
@[simp]
theorem actionTrivializationOfContMDiffSection_symm_apply (q : B × G) :
    (actionTrivializationOfContMDiffSection hn hsmul hp hfree horbit hU hs_smooth hs hinj
      hker).toOpenPartialHomeomorph.symm q = op q.2 • s q.1 := by
  simp [actionTrivializationOfContMDiffSection]

/-- Base set of `actionTrivializationOfContMDiffSection`. -/
@[simp]
theorem baseSet_actionTrivializationOfContMDiffSection :
    (actionTrivializationOfContMDiffSection hn hsmul hp hfree horbit hU hs_smooth hs hinj
      hker).baseSet = U := by simp [actionTrivializationOfContMDiffSection]

end ActionTriv

end LocalSection

section Submersion

variable [IP.Boundaryless] [ContMDiffMul IG n G]
  (hn : 1 ≤ n) (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
  {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
  (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
  (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
  (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
  (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)

private def submersionTrivializationAtlas : Set (Trivialization G p) :=
  {t | ∃ (U : Set B) (hU : IsOpen U) (s : B → P) (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b),
    t = actionTrivializationOfContMDiffSection hn hsmul hsub.contMDiff hfree horbit hU hs_smooth
      hs (fun b _ ↦ hinj (s b)) (fun b _ ↦ hker (s b))}

include hsurj in
private theorem exists_mem_submersionTrivializationAtlas (b : B) :
    ∃ t ∈ submersionTrivializationAtlas hn hsmul hsub hfree horbit hinj hker, b ∈ t.baseSet := by
  obtain ⟨x, rfl⟩ := hsurj b
  obtain ⟨U, hU, hxU, s, -, hs_smooth, hs⟩ := (hsub.isSubmersionAt x).exists_contMDiffOn_section
  exact ⟨_, ⟨U, hU, s, hs_smooth, hs, rfl⟩, by simpa using hxU⟩

/-- **`FiberBundle` structure on the fibres of a free orbit-exact `C^n` submersion** (Banach
version). Install locally via `letI := fiberBundleOfSubmersion ...`. -/
@[instance_reducible]
def fiberBundleOfSubmersion : FiberBundle G (ProjectionFiber G p) :=
  ProjectionFiber.fiberBundle
    (submersionTrivializationAtlas hn hsmul hsub hfree horbit hinj hker)
    (exists_mem_submersionTrivializationAtlas hn hsmul hsub hsurj hfree horbit hinj hker)

/-- A trivialization belongs to the atlas of `fiberBundleOfSubmersion` iff it is the
`ProjectionFiber` transport of `actionTrivializationOfContMDiffSection` for some `C^n` local
section `s` of `p` over an open set `U ⊆ B`. -/
theorem mem_trivializationAtlas_fiberBundleOfSubmersion_iff
    (e : Trivialization G (π G (ProjectionFiber G p))) :
    (letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker;
      e ∈ trivializationAtlas G (ProjectionFiber G p)) ↔
      ∃ (U : Set B) (hU : IsOpen U) (s : B → P) (hs_smooth : ContMDiffOn IB IP n s U)
        (hs : ∀ b ∈ U, p (s b) = b),
        e = (actionTrivializationOfContMDiffSection hn hsmul hsub.contMDiff hfree horbit hU
          hs_smooth hs (fun b _ ↦ hinj (s b)) (fun b _ ↦ hker (s b))).projectionFiber := by
  simp only [ProjectionFiber.trivializationAtlas_fiberBundle, mem_image,
    submersionTrivializationAtlas, mem_ofPred_eq]
  exact ⟨fun ⟨_, ⟨U, hU, s, hs_s, hs, rfl⟩, ht⟩ ↦ ⟨U, hU, s, hs_s, hs, ht.symm⟩,
    fun ⟨U, hU, s, hs_s, hs, ht⟩ ↦ ⟨_, ⟨U, hU, s, hs_s, hs, rfl⟩, ht.symm⟩⟩

/-- The `ProjectionFiber` transport of `actionTrivializationOfContMDiffSection` for any `C^n` local
section `s` of `p` over open `U ⊆ B` belongs to the atlas of `fiberBundleOfSubmersion`. -/
theorem projectionFiber_actionTrivializationOfContMDiffSection_mem_trivializationAtlas
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    (actionTrivializationOfContMDiffSection hn hsmul hsub.contMDiff hfree horbit hU hs_smooth hs
      (fun b _ ↦ hinj (s b)) (fun b _ ↦ hker (s b))).projectionFiber ∈
      trivializationAtlas G (ProjectionFiber G p) :=
  (mem_trivializationAtlas_fiberBundleOfSubmersion_iff hn hsmul hsub hsurj hfree horbit hinj hker
    _).2 ⟨U, hU, s, hs_smooth, hs, rfl⟩

/-- **`PrincipalBundle` structure on the fibres of a free orbit-exact `C^n` submersion** (Banach
version). -/
theorem principalBundleOfSubmersion :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
    PrincipalBundle G (ProjectionFiber G p) :=
  ProjectionFiber.principalBundle
    (submersionTrivializationAtlas hn hsmul hsub hfree horbit hinj hker)
    (exists_mem_submersionTrivializationAtlas hn hsmul hsub hsurj hfree horbit hinj hker)
    (map_smul_of_orbit_iff horbit)
    fun _ ⟨_, _, _, _, hs, ht⟩ x hx g ↦ by
      subst ht; simpa using sectionCoord_op_smul horbit hfree hs (by simpa using hx) g

/-- **`ContMDiffFiberBundle` structure on the fibres of a free orbit-exact `C^n` submersion**
(Banach version, requiring only `[ContMDiffMul IG n G]`). -/
theorem contMDiffFiberBundleOfSubmersion :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    ContMDiffFiberBundle n G (ProjectionFiber G p) IB IG := by
  have hatlas := mem_trivializationAtlas_fiberBundleOfSubmersion_iff hn hsmul hsub hsurj hfree
    horbit hinj hker
  let := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  let := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
  have := principalBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  rw [PrincipalBundle.contMDiffFiberBundle_iff]
  intro e₁ e₂ he₁ he₂
  rcases (hatlas e₁).1 he₁.out with ⟨U₁, hU₁, s₁, hs₁_smooth, hs₁, rfl⟩
  rcases (hatlas e₂).1 he₂.out with ⟨U₂, hU₂, s₂, hs₂_smooth, hs₂, rfl⟩
  have hcoord₂ := contMDiffOn_sectionCoord hn hsmul hsub.contMDiff horbit hU₂ hs₂_smooth hs₂
    (fun b _ ↦ hfree (s₂ b)) (fun b _ ↦ hinj (s₂ b)) (fun b _ ↦ hker (s₂ b))
  refine (hcoord₂.comp (hs₁_smooth.mono (by simp)) fun b hb ↦ ?_).congr fun b _ ↦ ?_
  · simp at hb; simpa [hs₁ b hb.1] using hb.2
  · rw [Trivialization.projectionFiber_coordChange]; simp [Trivialization.coordChange]

private theorem exists_section_trivializationAt (b : B) :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    ∃ (U : Set B) (hU : IsOpen U) (s : B → P) (hs_smooth : ContMDiffOn IB IP n s U)
      (hs : ∀ b' ∈ U, p (s b') = b'), b ∈ U ∧
      trivializationAt G (ProjectionFiber G p) b =
        (actionTrivializationOfContMDiffSection hn hsmul hsub.contMDiff hfree horbit hU hs_smooth
          hs (fun b' _ ↦ hinj (s b')) (fun b' _ ↦ hker (s b'))).projectionFiber := by
  let := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  rcases (mem_trivializationAtlas_fiberBundleOfSubmersion_iff hn hsmul hsub hsurj hfree horbit
    hinj hker _).1 (trivialization_mem_atlas G (ProjectionFiber G p) b) with
    ⟨U, hU, s, hs_smooth, hs, ht_eq⟩
  exact ⟨U, hU, s, hs_smooth, hs,
    by simpa [ht_eq] using mem_baseSet_trivializationAt G (ProjectionFiber G p) b, ht_eq⟩

private theorem contMDiff_diffeomorphManifoldTotalSpace_toFun :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    ContMDiff (IB.prod IG) IP n fun q : ManifoldTotalSpace G (ProjectionFiber G p) ↦
      ProjectionFiber.totalSpaceEquiv G p
        ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q) := by
  let := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  have := contMDiffFiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  intro q₀
  set z₀ := (ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q₀
  rcases exists_section_trivializationAt hn hsmul hsub hsurj hfree horbit hinj hker z₀.proj with
    ⟨U, hU, s, hs_smooth, hs, hz₀U, ht_eq⟩
  have hproj := ManifoldTotalSpace.contMDiff_proj n G (ProjectionFiber G p) IB IG q₀
  refine (hsmul.contMDiffAt.comp q₀ (((hs_smooth.contMDiffAt (hU.mem_nhds hz₀U)).comp q₀
    hproj).prodMk (ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IG
    q₀))).congr_of_eventuallyEq ?_
  filter_upwards [hproj.continuousAt (hU.mem_nhds hz₀U)] with q hqU
  set z := (ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q
  have hzp : p z.2.val = z.proj := z.2.map_val
  have hxU : p z.2.val ∈ U := by rwa [hzp]
  dsimp only [z₀] at ht_eq
  simp only [ProjectionFiber.totalSpaceEquiv_apply, comp_apply, ht_eq,
    Trivialization.projectionFiber_apply, actionTrivializationOfContMDiffSection_apply]
  have hsec := (op_sectionCoord_smul horbit hs hxU).symm
  rwa [hzp] at hsec

private theorem contMDiff_diffeomorphManifoldTotalSpace_invFun :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    ContMDiff IP (IB.prod IG) n fun x : P ↦
      ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)
        ((ProjectionFiber.totalSpaceEquiv G p).symm x) := by
  let := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  have := contMDiffFiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  intro x₀
  refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨(hsub.contMDiff x₀).congr_of_eventuallyEq
    (Eventually.of_forall fun x ↦ ProjectionFiber.proj_totalSpaceEquiv_symm G p x), ?_⟩
  rw [ProjectionFiber.proj_totalSpaceEquiv_symm]
  rcases exists_section_trivializationAt hn hsmul hsub hsurj hfree horbit hinj hker (p x₀) with
    ⟨U, hU, s, hs_smooth, hs, hx₀U, ht_eq⟩
  have hcoord := contMDiffOn_sectionCoord hn hsmul hsub.contMDiff horbit hU hs_smooth hs
    (fun b _ ↦ hfree (s b)) (fun b _ ↦ hinj (s b)) (fun b _ ↦ hker (s b))
  exact (hcoord.contMDiffAt ((hU.preimage hsub.contMDiff.continuous).mem_nhds
    hx₀U)).congr_of_eventuallyEq (Eventually.of_forall fun x ↦ by simp [ht_eq])

/-- **The charted total space `ManifoldTotalSpace G (ProjectionFiber G p)` is `C^n` diffeomorphic
to `P`.** -/
def diffeomorphManifoldTotalSpaceOfSubmersion :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    ManifoldTotalSpace G (ProjectionFiber G p) ≃ₘ^n⟮IB.prod IG, IP⟯ P :=
  letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  have := contMDiffFiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
  { toEquiv := (ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm.toEquiv.trans
      (ProjectionFiber.totalSpaceEquiv G p)
    contMDiff_toFun :=
      contMDiff_diffeomorphManifoldTotalSpace_toFun hn hsmul hsub hsurj hfree horbit hinj hker
    contMDiff_invFun :=
      contMDiff_diffeomorphManifoldTotalSpace_invFun hn hsmul hsub hsurj hfree horbit hinj hker }

/-- Forward map of `diffeomorphManifoldTotalSpaceOfSubmersion`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersion_apply
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker q =
      ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).2.val := by
  dsimp [diffeomorphManifoldTotalSpaceOfSubmersion]
  exact ProjectionFiber.totalSpaceEquiv_apply G p _

/-- Inverse map of `diffeomorphManifoldTotalSpaceOfSubmersion`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersion_symm_apply (x : P) :
    (letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker;
      (diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker).symm
        x) =
      ManifoldTotalSpace.homeomorph G (ProjectionFiber G p) ⟨p x, ⟨x, rfl⟩⟩ := by
  dsimp [diffeomorphManifoldTotalSpaceOfSubmersion]
  exact congrArg (ManifoldTotalSpace.homeomorph G (ProjectionFiber G p))
    (ProjectionFiber.totalSpaceEquiv_symm_apply G p x)

/-- `diffeomorphManifoldTotalSpaceOfSubmersion` commutes with the projections onto `B`. -/
theorem proj_diffeomorphManifoldTotalSpaceOfSubmersion
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    p (diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker q) =
      ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).proj :=
  ProjectionFiber.map_totalSpaceEquiv G p _

/-- `diffeomorphManifoldTotalSpaceOfSubmersion` is `G`-equivariant for the right `G`-actions. -/
theorem diffeomorphManifoldTotalSpaceOfSubmersion_op_smul
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

end Submersion

section ActionDivisionSmooth

variable [IP.Boundaryless] [LieGroup IG n G]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  (hn : 1 ≤ n) (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
  {p : P → B} (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
  (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
  (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
  (hker : ∀ x : P, (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range)
  {f₁ f₂ : M → P} (hf : ∀ x : M, p (f₁ x) = p (f₂ x))

include hn hsmul hfree hinj hker

/-- **Smoothness of `actionDivision` along families in a common fibre** (`ContMDiffWithinAt` form).
For a `C^n` map `p : P → B` (`1 ≤ n`) that is a submersion at `f₁ x₀` with a jointly `C^n` free
right action of a `C^n` Lie group `G` whose orbits are the fibres of `p` and whose orbit
differentials at `1` are injective and span `ker (dp_x)`, if `f₁, f₂ : M → P` are `C^n` within `s`
at `x₀` with `p (f₁ x) = p (f₂ x)`, then `x ↦ actionDivision horbit (hf x)` is `C^n` within `s`
at `x₀`. -/
theorem contMDiffWithinAt_actionDivision (hp : ContMDiff IP IB n p) {s : Set M} {x₀ : M}
    (hsub : IsSubmersionAt IP IB n p (f₁ x₀))
    (hf₁ : ContMDiffWithinAt IM IP n f₁ s x₀) (hf₂ : ContMDiffWithinAt IM IP n f₂ s x₀) :
    ContMDiffWithinAt IM IG n (fun x ↦ actionDivision horbit (hf x)) s x₀ := by
  obtain ⟨U, hU, hx₀U, σ, -, hσ_smooth, hσ⟩ := hsub.exists_contMDiffOn_section
  exact contMDiffWithinAt_actionDivision_of_section hp.continuous hfree horbit hU hσ
    (contMDiffOn_sectionCoord hn hsmul hp horbit hU hσ_smooth hσ (fun b _ ↦ hfree (σ b))
      (fun b _ ↦ hinj (σ b)) (fun b _ ↦ hker (σ b)))
    hf hx₀U hf₁ hf₂

/-- `ContMDiffAt` form of `contMDiffWithinAt_actionDivision`. -/
theorem contMDiffAt_actionDivision (hp : ContMDiff IP IB n p) {x₀ : M}
    (hsub : IsSubmersionAt IP IB n p (f₁ x₀))
    (hf₁ : ContMDiffAt IM IP n f₁ x₀) (hf₂ : ContMDiffAt IM IP n f₂ x₀) :
    ContMDiffAt IM IG n (fun x ↦ actionDivision horbit (hf x)) x₀ :=
  contMDiffWithinAt_actionDivision hn hsmul hfree horbit hinj hker hf hp hsub hf₁ hf₂

/-- `ContMDiffOn` form of `contMDiffWithinAt_actionDivision`. -/
theorem contMDiffOn_actionDivision (hsub : IsSubmersion IP IB n p) {s : Set M}
    (hf₁ : ContMDiffOn IM IP n f₁ s) (hf₂ : ContMDiffOn IM IP n f₂ s) :
    ContMDiffOn IM IG n (fun x ↦ actionDivision horbit (hf x)) s :=
  fun x hx ↦ contMDiffWithinAt_actionDivision hn hsmul hfree horbit hinj hker hf hsub.contMDiff
    (hsub.isSubmersionAt (f₁ x)) (hf₁ x hx) (hf₂ x hx)

/-- `ContMDiff` form of `contMDiffWithinAt_actionDivision`. -/
theorem contMDiff_actionDivision (hsub : IsSubmersion IP IB n p)
    (hf₁ : ContMDiff IM IP n f₁) (hf₂ : ContMDiff IM IP n f₂) :
    ContMDiff IM IG n fun x ↦ actionDivision horbit (hf x) :=
  fun x ↦ contMDiffAt_actionDivision hn hsmul hfree horbit hinj hker hf hsub.contMDiff
    (hsub.isSubmersionAt (f₁ x)) (hf₁ x) (hf₂ x)

end ActionDivisionSmooth

end Banach

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

omit [IP.Boundaryless] in
/-- Finite-dimensional smoothness of `sectionCoord`: if `s : B → P` is a `C^n` local section of
`p : P → B` (`1 ≤ n`) on open `U ⊆ B` along which the orbit-exact `C^n` right `G`-action is free,
`d(g ↦ op g • s b)_1` is injective, and `finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG`, then
`sectionCoord horbit hs` is `C^n` on `p ⁻¹' U`. -/
theorem contMDiffOn_sectionCoord_of_finrank_eq [BoundarylessManifold IP P] (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hp : ContMDiff IP IB n p)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1)
    (hinj : ∀ b ∈ U, Injective (mfderiv IG IP (fun g : G ↦ op g • s b) 1))
    (hdim : ∀ b ∈ U, finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) :
    ContMDiffOn IP IG n (sectionCoord horbit hs) (p ⁻¹' U) := by
  have := FiniteDimensional.completeSpace 𝕜 EP; have := FiniteDimensional.completeSpace 𝕜 EB
  have := FiniteDimensional.completeSpace 𝕜 EG
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  exact contMDiffOn_sectionCoord hn hsmul hp horbit hU hs_smooth hs hfree hinj fun b hb ↦
    (range_mfderiv_op_smul_one_eq_ker_of_finrank_eq
      (isRegularPoint_iff.2
        (surjective_mfderiv_of_eventuallyEq_id ((hp (s b)).mdifferentiableAt hn0)
          ((hs_smooth.contMDiffAt (hU.mem_nhds hb)).mdifferentiableAt hn0)
          (eventually_of_mem (hU.mem_nhds hb) hs)))
      (fun g ↦ map_op_smul_of_orbit_iff horbit g (s b)) (hinj b hb) (hdim b hb)).ge

omit [IP.Boundaryless] [IsManifold IP n P] [FiniteDimensional 𝕜 EB] [IsManifold IB n B]
  [FiniteDimensional 𝕜 EG] [ContMDiffMul IG n G] in
/-- In finite dimensions over `𝕜`, if `p : P → B` is a `C^n` submersion (`1 ≤ n`), the right
`G`-orbits equal the fibres of `p`, `d(g ↦ op g • x)_1` is injective, and
`finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG`, then `ker (dp_x) ≤ range (d(g ↦ op g • x)_1)`. -/
theorem ker_le_range_of_finrank_eq (hn : 1 ≤ n)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (hinj : ∀ x : P, Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1))
    (hdim : P → finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) (x : P) :
    (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range :=
  have hn0 : n ≠ 0 := fun h ↦ by rw [h] at hn; simp at hn
  (range_mfderiv_op_smul_one_eq_ker_of_finrank_eq
    (isRegularPoint_iff.2 (hsub.surjective_mfderiv hn0 x))
    (fun g ↦ map_op_smul_of_orbit_iff horbit g x) (hinj x) (hdim x)).ge

end FiniteDimensional

end TauCeti.PrincipalBundle
