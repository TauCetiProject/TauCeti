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
public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Topology.FiberBundle.Principal.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Diffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.RegularValue.Section

/-!
# Smooth principal bundles from free orbit-exact submersions

This file constructs `C^n` principal `G`-bundle structures on `TauCeti.MapFiber p` for an
unbundled surjective `C^n` submersion `p : P → B` (`1 ≤ n`) with a free `C^n` right action of a
group manifold `G` whose orbits are the fibres of `p` (the automatic real Lie-group version,
Kolář–Michor–Slovák Lemma 10.3, follows in
`TauCeti.Geometry.Manifold.FiberBundle.Principal.Submersion.LieGroup`):

1. **Banach `C^n` criterion (`1 ≤ n`, over `[RCLike 𝕜]`):** for Banach model spaces and
   `[ContMDiffMul IG n G]`, if `P` is a boundaryless manifold (`[BoundarylessManifold IP P]`,
   `[IsManifold IP n P]`) and at every `x : P` the orbit differential `d(g ↦ op g • x)_1` is
   injective and spans `ker (dp_x)`, then the action sweep `(b, g) ↦ op g • s b` of any `C^n` local
   section `s` over open `U ⊆ B` is a `C^n` local diffeomorphism on `U ×ˢ univ`; when the action
   is also free along `s` and orbit-exact it is injective with image `p ⁻¹' U`, giving
   `contMDiffOn_sectionCoord`. Under the stronger model hypothesis `[IP.Boundaryless]`, these
   charts yield `C^n` principal bundle structures on `MapFiber p`, a `G`-equivariant `C^n`
   diffeomorphism `ManifoldTotalSpace G (MapFiber p) ≃ₘ^n P` over `B`, and (when
   `[LieGroup IG n G]`) `C^n` regularity of `actionDivisionOrOne`
   (`contMDiffWithinAt_actionDivisionOrOne`).
2. **Finite-dimensional `C^n` criterion (`1 ≤ n`, over `[RCLike 𝕜]`):** injectivity of
   `d(g ↦ op g • x)_1` and `finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG` imply the
   vertical-range condition by rank-nullity (`range_mfderiv_op_smul_one_eq_ker_of_finrank_eq`),
   and `contMDiffOn_sectionCoord_of_finrank_eq` gives local `C^n` smoothness of `sectionCoord`.

## Main definitions and results

* `TauCeti.PrincipalBundle.range_mfderiv_op_smul_one_le_ker`,
  `range_mfderiv_op_smul_one_eq_ker_of_finrank_eq`,
  `isRegularValue_of_isRegularPoint_of_orbit_eq_fiber`: vertical tangent and regularity lemmas.
* `ContMDiff.contMDiffOn_op_smul_section`,
  `TauCeti.PrincipalBundle.isLocalDiffeomorphOn_op_smul_section`, `contMDiffOn_sectionCoord`,
  `ContMDiff.contMDiffOn_actionTrivializationOfSection`,
  `ContMDiff.contMDiffOn_symm_actionTrivializationOfSection`: action sweep local diffeomorphism,
  `C^n` section coordinates, and smoothness of `Continuous.actionTrivializationOfSection`.
* `TauCeti.PrincipalBundle.fiberBundleOfSubmersion`,
  `mem_trivializationAtlas_fiberBundleOfSubmersion_iff`,
  `toMapFiber_actionTrivializationOfSection_mem_trivializationAtlas`,
  `principalBundleOfSubmersion`, `contMDiffFiberBundleOfSubmersion`,
  `diffeomorphManifoldTotalSpaceOfSubmersion`: Banach `C^n` principal bundle structures, atlas
  characterization, and total-space diffeomorphism.
* `Continuous.contMDiffWithinAt_actionDivisionOrOne_of_section`,
  `TauCeti.PrincipalBundle.contMDiffWithinAt_actionDivisionOrOne`,
  `contMDiffAt_actionDivisionOrOne`, `contMDiffOn_actionDivisionOrOne`,
  `contMDiff_actionDivisionOrOne`: `C^n` regularity of
  `actionDivisionOrOne` for a `C^n` Lie group `G`.
* `TauCeti.PrincipalBundle.contMDiffOn_sectionCoord_of_finrank_eq`: finite-dimensional `C^n`
  section smoothness.

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
  have hcomp : (fun z : P ↦ p (op g • z)) = p := funext (horbit_inv g)
  have hreg' : IsRegularPoint IP IB (p ∘ fun z : P ↦ op g • z) x := by
    rwa [Function.comp_def, hcomp]
  exact hreg'.of_comp (hp _ hy) (hsmul g)

end VerticalTangent

open TauCeti.PrincipalBundle in
/-- For a continuous map `p : P → B` and an orbit-exact right action of a `C^n` Lie group `G` on
`P` that is free along a local section `σ` over an open neighbourhood `U` of `p (f₁ x₀)`, if
`sectionCoord` is `C^n` on `p ⁻¹' U`, then `x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)` is `C^n`
within `s` at `x₀` for any `f₁, f₂ : M → P` that are `C^n` within `s` at `x₀` and satisfy
`p (f₁ x₀) = p (f₂ x₀)` and `∀ᶠ x in 𝓝[s] x₀, p (f₁ x) = p (f₂ x)`. -/
theorem _root_.Continuous.contMDiffWithinAt_actionDivisionOrOne_of_section {n : ℕ∞ω} {B : Type*}
    [TopologicalSpace B] [Group G] [LieGroup IG n G] [MulAction Gᵐᵒᵖ P]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {p : P → B} (hp : Continuous p)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {U : Set B} (hU : IsOpen U) {σ : B → P}
    (hfree : ∀ b ∈ U, ∀ g : G, op g • σ b = σ b → g = 1)
    (hσ : ∀ b ∈ U, p (σ b) = b)
    (hcoord : ContMDiffOn IP IG n (sectionCoord horbit hσ) (p ⁻¹' U))
    {f₁ f₂ : M → P} {s : Set M} {x₀ : M}
    (hf₀ : p (f₁ x₀) = p (f₂ x₀)) (hf : ∀ᶠ x in 𝓝[s] x₀, p (f₁ x) = p (f₂ x))
    (hx₀U : p (f₁ x₀) ∈ U) (hf₁ : ContMDiffWithinAt IM IP n f₁ s x₀)
    (hf₂ : ContMDiffWithinAt IM IP n f₂ s x₀) :
    ContMDiffWithinAt IM IG n (fun x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)) s x₀ := by
  have hopen : IsOpen (p ⁻¹' U) := hU.preimage hp
  have h1 := (hcoord.contMDiffAt (hopen.mem_nhds hx₀U)).comp_contMDiffWithinAt x₀ hf₁
  have h2 := (hcoord.contMDiffAt
    (hopen.mem_nhds (by rwa [mem_preimage, ← hf₀]))).comp_contMDiffWithinAt x₀ hf₂
  refine (h1.inv.mul h2).congr_of_eventuallyEq ?_
    (actionDivisionOrOne_eq_inv_sectionCoord_mul_sectionCoord horbit hfree hσ hx₀U hf₀)
  filter_upwards [hf₁.continuousWithinAt.preimage_mem_nhdsWithin (hopen.mem_nhds hx₀U), hf]
    with x hx hfx
  exact actionDivisionOrOne_eq_inv_sectionCoord_mul_sectionCoord horbit hfree hσ hx hfx

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
/-- Action sweep `(b, g) ↦ op g • s b` of a `C^n` local section `s` over `U ⊆ B` under a jointly
`C^n` right `G`-action is `C^n` on `U ×ˢ univ`. -/
theorem _root_.ContMDiff.contMDiffOn_op_smul_section
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {U : Set B} {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U) :
    ContMDiffOn (IB.prod IG) IP n (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ) :=
  hsmul.comp_contMDiffOn ((hs_smooth.comp (s := U ×ˢ univ) contMDiffOn_fst fun _ hq ↦ hq.1).prodMk
    contMDiffOn_snd)

omit [CompleteSpace EP] [IsManifold IP n P] [BoundarylessManifold IP P]
  [CompleteSpace EB] [IsManifold IB n B] [CompleteSpace EG] [ContMDiffMul IG n G] in
/-- Forward `C^n` smoothness of `Continuous.actionTrivializationOfSection` on its source when `p`
is `C^n` and `sectionCoord` is `C^n` on `p ⁻¹' U`. -/
theorem _root_.ContMDiff.contMDiffOn_actionTrivializationOfSection
    {p : P → B} (hp : ContMDiff IP IB n p)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {U : Set B} (hU : IsOpen U) {s : B → P}
    (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1)
    (hs : ∀ b ∈ U, p (s b) = b)
    (hcoord : ContMDiffOn IP IG n (sectionCoord horbit hs) (p ⁻¹' U))
    (hsmul_s : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) :
    ContMDiffOn IP (IB.prod IG) n
      (hp.continuous.actionTrivializationOfSection horbit hU hfree hs hcoord.continuousOn hsmul_s)
      (hp.continuous.actionTrivializationOfSection horbit hU hfree hs hcoord.continuousOn
        hsmul_s).source := by
  rw [Continuous.actionTrivializationOfSection_source]
  exact (hp.contMDiffOn.prodMk hcoord).congr fun x _ ↦
    hp.continuous.actionTrivializationOfSection_apply horbit hU hfree hs hcoord.continuousOn
      hsmul_s x

omit [CompleteSpace EP] [IsManifold IP n P] [BoundarylessManifold IP P]
  [CompleteSpace EB] [IsManifold IB n B] [CompleteSpace EG] [ContMDiffMul IG n G] in
/-- Inverse `C^n` smoothness of `Continuous.actionTrivializationOfSection` on its target when `s`
is `C^n` on `U`, `p` is continuous, and the right `G`-action is jointly `C^n`. -/
theorem _root_.ContMDiff.contMDiffOn_symm_actionTrivializationOfSection
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hp : Continuous p)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1)
    (hs : ∀ b ∈ U, p (s b) = b)
    (hcoord : ContinuousOn (sectionCoord horbit hs) (p ⁻¹' U)) :
    ContMDiffOn (IB.prod IG) IP n
      (hp.actionTrivializationOfSection horbit hU hfree hs hcoord
        (hsmul.contMDiffOn_op_smul_section hs_smooth).continuousOn).toOpenPartialHomeomorph.symm
      (hp.actionTrivializationOfSection horbit hU hfree hs hcoord
        (hsmul.contMDiffOn_op_smul_section hs_smooth).continuousOn).target := by
  rw [Continuous.actionTrivializationOfSection_target]
  exact (hsmul.contMDiffOn_op_smul_section hs_smooth).congr fun q hq ↦
    hp.actionTrivializationOfSection_symm_apply horbit hU hfree hs hcoord
      (hsmul.contMDiffOn_op_smul_section hs_smooth).continuousOn hq.1

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
  have hn0 : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hn
  let Ψ : B × G → P := fun q ↦ op q.2 • s q.1
  have hΨ_diff : MDifferentiableAt (IB.prod IG) IP Ψ (b, 1) :=
    ((hsmul.contMDiffOn_op_smul_section hs_smooth).contMDiffAt
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
  have hps : Function.RightInverse ds dp := fun u ↦
    ((hp (s b)).mdifferentiableAt hn0).mfderiv_apply_mfderiv_of_eventuallyEq_id
      ((hs_smooth.contMDiffAt (hU.mem_nhds hb)).mdifferentiableAt hn0)
      (eventually_of_mem (hU.mem_nhds hb) hs) u
  have horb_ker : dorb.range ≤ dp.ker := range_mfderiv_op_smul_one_le_ker horbit_inv
  let e_ker : EG ≃ dp.ker :=
    Equiv.ofBijective (fun w ↦ ⟨dorb w, horb_ker ⟨w, rfl⟩⟩)
      ⟨fun _ _ h ↦ hinj (congrArg Subtype.val h), fun ⟨_, hv⟩ ↦
        let ⟨w, hw⟩ := hker hv; ⟨w, Subtype.ext hw⟩⟩
  let e : (EB × EG) ≃ EP := (Equiv.prodCongr (Equiv.refl EB) e_ker).trans
    (ContinuousLinearEquiv.equivOfRightInverse dp ds hps).symm.toEquiv
  have he : (dΨ : EB × EG → EP) = e := funext fun ⟨u, w⟩ ↦ by
    rw [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
      LinearEquiv.coe_toEquiv, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.equivOfRightInverse_symm_apply]
    exact hdecomp u w
  exact he ▸ e.bijective

/-- **Action sweep of a local section is a `C^n` local diffeomorphism.** Over an open set `U ⊆ B`
supporting a `C^n` local section `s` of a `C^n` map `p : P → B` (`1 ≤ n`, Banach model spaces,
`[BoundarylessManifold IP P]`, `[ContMDiffMul IG n G]`, jointly `C^n` right `G`-action) whose
orbits are preserved by `p`, if `d(g ↦ op g • s b)_1` is injective and spans `ker (dp_{s b})` for
all `b ∈ U`, then `(b, g) ↦ op g • s b` is a `C^n` local diffeomorphism on `U ×ˢ univ`. -/
theorem isLocalDiffeomorphOn_op_smul_section {U : Set B} (hU : IsOpen U) {s : B → P}
    (hs_smooth : ContMDiffOn IB IP n s U) (hs : ∀ b ∈ U, p (s b) = b)
    (horbit_inv : ∀ b ∈ U, ∀ g : G, p (op g • s b) = p (s b))
    (hinj : ∀ b ∈ U, Injective (mfderiv IG IP (fun g : G ↦ op g • s b) 1))
    (hker : ∀ b ∈ U,
      (mfderiv IP IB p (s b)).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • s b) 1).range) :
    IsLocalDiffeomorphOn (IB.prod IG) IP n (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ) := by
  have hn0 : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hn
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
        (isRegularPoint_iff.1
          (isRegularPoint_of_contMDiffOn_section hn0 hU hs_smooth hs hb (hp (s b))))
        BoundarylessManifold.isInteriorPoint
    have hb1I : (IB.prod IG).IsInteriorPoint (b, (1 : G)) :=
      (IB.interior_prod (J := IG) (M := B) (N := G)).ge
        ⟨hbI, ContMDiffMul.isInteriorPoint (n := n) hn0 1⟩
    exact isLocalDiffeomorphAt_of_mfderiv_eq (hsmul.contMDiffOn_op_smul_section hs_smooth)
      (hU.prod isOpen_univ) ⟨hb, mem_univ _⟩ hb1I hn (e := e)
      (ContinuousLinearEquiv.coe_ofBijective dΨ _ _)
  have : ContMDiffConstSMul IP n Gᵐᵒᵖ P := hsmul.contMDiffConstSMul_op
  rintro ⟨⟨b, g⟩, hb, -⟩
  let φR : (B × G) ≃ₘ^n⟮IB.prod IG, IB.prod IG⟯ (B × G) :=
    (Diffeomorph.refl IB B n).prodCongr (Diffeomorph.constSmul IG n (op g))
  let φL : P ≃ₘ^n⟮IP, IP⟯ P := Diffeomorph.constSmul IP n (op g)
  have heq : Ψ ∘ φR = φL ∘ Ψ := funext fun ⟨b', h⟩ ↦ by
    simp only [comp_apply, Ψ, φR, φL, Diffeomorph.coe_prodCongr, Prod.map_apply,
      Diffeomorph.coe_refl, id_eq, Diffeomorph.constSmul_apply, op_smul_eq_mul, ← mul_smul,
      ← op_mul]
  simpa [φR, Diffeomorph.constSmul_apply] using
    (h_one b hb).of_comp_diffeomorph_eq φR φL le_rfl heq

/-- **Smoothness of `sectionCoord`.** For a `C^n` map `p : P → B` (`1 ≤ n`, Banach model spaces,
`[BoundarylessManifold IP P]`, `[ContMDiffMul IG n G]`), a jointly `C^n` orbit-exact right
`G`-action free along a `C^n` local section `s` over open `U ⊆ B`, and the vertical-tangent
criterion (`hinj` and `hker` along `s`), `sectionCoord horbit hs : P → G` is `C^n` on
`p ⁻¹' U`. -/
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
      (fun b _ g ↦ apply_op_smul_eq_of_orbit_eq_fiber horbit g (s b)) hinj hker
  have hinj_Ψ : InjOn Ψ (U ×ˢ univ) := by
    rintro ⟨b₁, g₁⟩ ⟨hb₁, -⟩ ⟨b₂, g₂⟩ ⟨hb₂, -⟩ hEq
    have hb : b₁ = b₂ := by
      simpa only [Ψ, apply_op_smul_eq_of_orbit_eq_fiber horbit, hs b₁ hb₁, hs b₂ hb₂] using
        congrArg p hEq
    subst hb
    exact Prod.ext rfl ((op_smul_left_inj_of_op_smul_eq_self_imp (hfree b₁ hb₁)).1 hEq)
  have himg : Ψ '' (U ×ˢ univ) = p ⁻¹' U := subset_antisymm
    (by rintro _ ⟨⟨b, g⟩, ⟨hb, -⟩, rfl⟩
        simp [Ψ, apply_op_smul_eq_of_orbit_eq_fiber horbit, hs b hb, hb])
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
    t = hsub.contMDiff.continuous.actionTrivializationOfSection horbit hU (fun b _ ↦ hfree (s b))
      hs (contMDiffOn_sectionCoord hn hsmul hsub.contMDiff horbit hU hs_smooth hs
        (fun b _ ↦ hfree (s b)) (fun b _ ↦ hinj (s b)) (fun b _ ↦ hker (s b))).continuousOn
      (hsmul.contMDiffOn_op_smul_section hs_smooth).continuousOn}

include hsurj in
private theorem exists_mem_submersionTrivializationAtlas (b : B) :
    ∃ t ∈ submersionTrivializationAtlas hn hsmul hsub hfree horbit hinj hker, b ∈ t.baseSet := by
  obtain ⟨x, rfl⟩ := hsurj b
  obtain ⟨U, hU, hxU, s, -, hs_smooth, hs⟩ := (hsub.isSubmersionAt x).exists_contMDiffOn_section
  exact ⟨_, ⟨U, hU, s, hs_smooth, hs, rfl⟩, by simpa using hxU⟩

private def submersionAtlas : MapFiber.Atlas G p :=
  MapFiber.Atlas.ofSet
    (submersionTrivializationAtlas hn hsmul hsub hfree horbit hinj hker)
    (exists_mem_submersionTrivializationAtlas hn hsmul hsub hsurj hfree horbit hinj hker)

private theorem mem_charts_submersionAtlas_iff (t : Trivialization G p) :
    t ∈ (submersionAtlas hn hsmul hsub hsurj hfree horbit hinj hker).charts ↔
      ∃ (U : Set B) (hU : IsOpen U) (s : B → P) (hs_smooth : ContMDiffOn IB IP n s U)
        (hs : ∀ b ∈ U, p (s b) = b),
        t = hsub.contMDiff.continuous.actionTrivializationOfSection horbit hU
          (fun b _ ↦ hfree (s b)) hs
          (contMDiffOn_sectionCoord hn hsmul hsub.contMDiff horbit hU hs_smooth hs
            (fun b _ ↦ hfree (s b)) (fun b _ ↦ hinj (s b)) (fun b _ ↦ hker (s b))).continuousOn
          (hsmul.contMDiffOn_op_smul_section hs_smooth).continuousOn := by
  simp [submersionAtlas, submersionTrivializationAtlas]

private theorem isContMDiff_submersionAtlas :
    (submersionAtlas hn hsmul hsub hsurj hfree horbit hinj hker).IsContMDiff n IB IG IP := by
  refine ⟨fun {t} ht ↦ ?_, fun {t} ht ↦ ?_⟩ <;>
    obtain ⟨U, hU, s, hs_smooth, hs, rfl⟩ :=
      (mem_charts_submersionAtlas_iff hn hsmul hsub hsurj hfree horbit hinj hker t).1 ht
  · exact hsub.contMDiff.contMDiffOn_actionTrivializationOfSection horbit hU
      (fun b _ ↦ hfree (s b)) hs
      (contMDiffOn_sectionCoord hn hsmul hsub.contMDiff horbit hU hs_smooth hs
        (fun b _ ↦ hfree (s b)) (fun b _ ↦ hinj (s b)) (fun b _ ↦ hker (s b)))
      (hsmul.contMDiffOn_op_smul_section hs_smooth).continuousOn
  · exact hsmul.contMDiffOn_symm_actionTrivializationOfSection hsub.contMDiff.continuous horbit hU
      hs_smooth (fun b _ ↦ hfree (s b)) hs
      (contMDiffOn_sectionCoord hn hsmul hsub.contMDiff horbit hU hs_smooth hs
        (fun b _ ↦ hfree (s b)) (fun b _ ↦ hinj (s b)) (fun b _ ↦ hker (s b))).continuousOn

/-- **`FiberBundle` structure on the fibres of a surjective free orbit-exact `C^n` submersion**
(Banach version, `1 ≤ n`), for `p : P → B` with `Surjective p` (`hsurj`), `P` modelled on a
boundaryless model with corners (`[IP.Boundaryless]`), `[ContMDiffMul IG n G]`, and a jointly
`C^n` free orbit-exact right `G`-action (`hsmul`, `hfree`, `horbit`) satisfying the
vertical-tangent criterion: at every `x : P`, the orbit differential `d(g ↦ op g • x)_1` is
injective (`hinj`) and spans `ker (dp_x)` (`hker`). Install locally via
`letI := fiberBundleOfSubmersion ...`. -/
@[instance_reducible]
def fiberBundleOfSubmersion : FiberBundle G (MapFiber p) :=
  (submersionAtlas hn hsmul hsub hsurj hfree horbit hinj hker).fiberBundle

/-- A trivialization belongs to the atlas of `fiberBundleOfSubmersion` iff it is the
`MapFiber` transport of `Continuous.actionTrivializationOfSection` for some `C^n` local
section `s` of `p` over an open set `U ⊆ B`. -/
theorem mem_trivializationAtlas_fiberBundleOfSubmersion_iff
    (e : Trivialization G (π G (MapFiber p))) :
    (letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker;
      e ∈ trivializationAtlas G (MapFiber p)) ↔
      ∃ (U : Set B) (hU : IsOpen U) (s : B → P) (hs_smooth : ContMDiffOn IB IP n s U)
        (hs : ∀ b ∈ U, p (s b) = b),
        e = (hsub.contMDiff.continuous.actionTrivializationOfSection horbit hU
          (fun b _ ↦ hfree (s b)) hs
          (contMDiffOn_sectionCoord hn hsmul hsub.contMDiff horbit hU hs_smooth hs
            (fun b _ ↦ hfree (s b)) (fun b _ ↦ hinj (s b)) (fun b _ ↦ hker (s b))).continuousOn
          (hsmul.contMDiffOn_op_smul_section hs_smooth).continuousOn).toMapFiber := by
  rw [fiberBundleOfSubmersion, MapFiber.Atlas.trivializationAtlas_fiberBundle, mem_image]
  simp only [mem_charts_submersionAtlas_iff]
  exact ⟨fun ⟨_, ⟨U, hU, s, hs_s, hs, rfl⟩, ht⟩ ↦ ⟨U, hU, s, hs_s, hs, ht.symm⟩,
    fun ⟨U, hU, s, hs_s, hs, ht⟩ ↦ ⟨_, ⟨U, hU, s, hs_s, hs, rfl⟩, ht.symm⟩⟩

/-- The `MapFiber` transport of `Continuous.actionTrivializationOfSection` for any `C^n` local
section `s` of `p` over open `U ⊆ B` belongs to the atlas of `fiberBundleOfSubmersion`. -/
theorem toMapFiber_actionTrivializationOfSection_mem_trivializationAtlas
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b)
    (hcoord : ContinuousOn (sectionCoord horbit hs) (p ⁻¹' U))
    (hsmul_s : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    (hsub.contMDiff.continuous.actionTrivializationOfSection horbit hU (fun b _ ↦ hfree (s b)) hs
      hcoord hsmul_s).toMapFiber ∈ trivializationAtlas G (MapFiber p) :=
  (mem_trivializationAtlas_fiberBundleOfSubmersion_iff hn hsmul hsub hsurj hfree horbit hinj hker
    _).2 ⟨U, hU, s, hs_smooth, hs, rfl⟩

/-- **`PrincipalBundle` structure on the fibres of a surjective free orbit-exact `C^n` submersion**
(Banach version, under the full hypotheses of `fiberBundleOfSubmersion`: `1 ≤ n`,
`[IP.Boundaryless]`, `[ContMDiffMul IG n G]`, surjective `C^n` submersion `p`, free orbit-exact
jointly `C^n` right `G`-action, and the vertical-tangent criterion `hinj` and `hker`). -/
theorem principalBundleOfSubmersion :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
    PrincipalBundle G (MapFiber p) :=
  (submersionAtlas hn hsmul hsub hsurj hfree horbit hinj hker).principalBundle
    (apply_smul_eq_of_orbit_eq_fiber horbit)
    fun t ht x hx g ↦ by
      obtain ⟨U, hU, s, hs_smooth, hs, rfl⟩ :=
        (mem_charts_submersionAtlas_iff hn hsmul hsub hsurj hfree horbit hinj hker t).1 ht
      rw [Continuous.baseSet_actionTrivializationOfSection] at hx
      simpa only [Continuous.actionTrivializationOfSection_apply] using
        sectionCoord_op_smul horbit (fun b _ ↦ hfree (s b)) hs hx g

/-- **`ContMDiffFiberBundle` structure on the fibres of a surjective free orbit-exact `C^n`
submersion** (Banach version, under the full hypotheses of `fiberBundleOfSubmersion`: `1 ≤ n`,
`[IP.Boundaryless]`, `[ContMDiffMul IG n G]`, surjective `C^n` submersion `p`, free orbit-exact
jointly `C^n` right `G`-action, and the vertical-tangent criterion `hinj` and `hker`). -/
theorem contMDiffFiberBundleOfSubmersion :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    ContMDiffFiberBundle n G (MapFiber p) IB IG :=
  (submersionAtlas hn hsmul hsub hsurj hfree horbit hinj hker).contMDiffFiberBundle
    (isContMDiff_submersionAtlas hn hsmul hsub hsurj hfree horbit hinj hker)

/-- **The charted total space `ManifoldTotalSpace G (MapFiber p)` is `C^n` diffeomorphic to `P`**
(Banach version, under the full hypotheses of `fiberBundleOfSubmersion`: `1 ≤ n`,
`[IP.Boundaryless]`, `[ContMDiffMul IG n G]`, surjective `C^n` submersion `p`, free orbit-exact
jointly `C^n` right `G`-action, and the vertical-tangent criterion `hinj` and `hker`). -/
def diffeomorphManifoldTotalSpaceOfSubmersion :
    letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
    ManifoldTotalSpace G (MapFiber p) ≃ₘ^n⟮IB.prod IG, IP⟯ P :=
  (submersionAtlas hn hsmul hsub hsurj hfree horbit hinj hker).totalSpaceDiffeomorph
    (isContMDiff_submersionAtlas hn hsmul hsub hsurj hfree horbit hinj hker)

/-- Forward map of `diffeomorphManifoldTotalSpaceOfSubmersion`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersion_apply
    (q : ManifoldTotalSpace G (MapFiber p)) :
    diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker q =
      ((ManifoldTotalSpace.homeomorph G (MapFiber p)).symm q).snd.val := by
  dsimp [diffeomorphManifoldTotalSpaceOfSubmersion]
  rw [MapFiber.Atlas.totalSpaceDiffeomorph_apply, MapFiber.totalSpaceHomeomorph_apply]

/-- Inverse map of `diffeomorphManifoldTotalSpaceOfSubmersion`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersion_symm_apply (x : P) :
    (letI := fiberBundleOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker;
      (diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker).symm
        x) =
      ManifoldTotalSpace.homeomorph G (MapFiber p) ⟨p x, ⟨x, rfl⟩⟩ := by
  dsimp [diffeomorphManifoldTotalSpaceOfSubmersion]
  rw [MapFiber.Atlas.totalSpaceDiffeomorph_symm_apply, MapFiber.totalSpaceHomeomorph_symm_apply]

/-- `diffeomorphManifoldTotalSpaceOfSubmersion` commutes with the projections onto `B`. -/
theorem proj_diffeomorphManifoldTotalSpaceOfSubmersion
    (q : ManifoldTotalSpace G (MapFiber p)) :
    p (diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker q) =
      ((ManifoldTotalSpace.homeomorph G (MapFiber p)).symm q).proj :=
  MapFiber.Atlas.proj_totalSpaceDiffeomorph _ q

/-- `diffeomorphManifoldTotalSpaceOfSubmersion` is `G`-equivariant for the right `G`-actions. -/
theorem diffeomorphManifoldTotalSpaceOfSubmersion_op_smul
    (g : G) (q : ManifoldTotalSpace G (MapFiber p)) :
    (letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit);
      diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
        (op g • q)) =
      op g • diffeomorphManifoldTotalSpaceOfSubmersion hn hsmul hsub hsurj hfree horbit hinj hker
        q :=
  MapFiber.Atlas.totalSpaceDiffeomorph_smul _ (apply_smul_eq_of_orbit_eq_fiber horbit) (op g) q

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
  {f₁ f₂ : M → P}

include hn hsmul hfree hinj hker

/-- **Smoothness of `actionDivisionOrOne` along families in a common fibre** (`ContMDiffWithinAt`
form). For a `C^n` map `p : P → B` (`1 ≤ n`) with `P` modelled on a boundaryless model with
corners (`[IP.Boundaryless]`) that is a submersion at `f₁ x₀`, equipped with a jointly `C^n` free
right action of a `C^n` Lie group `G` whose orbits are the fibres of `p` and whose orbit
differentials at `1` are injective and span `ker (dp_x)`, if `f₁, f₂ : M → P` are `C^n` within `s`
at `x₀` with `p (f₁ x₀) = p (f₂ x₀)` and `∀ᶠ x in 𝓝[s] x₀, p (f₁ x) = p (f₂ x)`, then
`x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)` is `C^n` within `s` at `x₀`. -/
theorem contMDiffWithinAt_actionDivisionOrOne (hp : ContMDiff IP IB n p) {s : Set M} {x₀ : M}
    (hf₀ : p (f₁ x₀) = p (f₂ x₀)) (hf : ∀ᶠ x in 𝓝[s] x₀, p (f₁ x) = p (f₂ x))
    (hsub : IsSubmersionAt IP IB n p (f₁ x₀))
    (hf₁ : ContMDiffWithinAt IM IP n f₁ s x₀) (hf₂ : ContMDiffWithinAt IM IP n f₂ s x₀) :
    ContMDiffWithinAt IM IG n (fun x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)) s x₀ := by
  obtain ⟨U, hU, hx₀U, σ, -, hσ_smooth, hσ⟩ := hsub.exists_contMDiffOn_section
  exact hp.continuous.contMDiffWithinAt_actionDivisionOrOne_of_section horbit hU
    (fun b _ ↦ hfree (σ b)) hσ
    (contMDiffOn_sectionCoord hn hsmul hp horbit hU hσ_smooth hσ (fun b _ ↦ hfree (σ b))
      (fun b _ ↦ hinj (σ b)) (fun b _ ↦ hker (σ b)))
    hf₀ hf hx₀U hf₁ hf₂

/-- `ContMDiffAt` form of `contMDiffWithinAt_actionDivisionOrOne`. -/
theorem contMDiffAt_actionDivisionOrOne (hp : ContMDiff IP IB n p) {x₀ : M}
    (hf : ∀ᶠ x in 𝓝 x₀, p (f₁ x) = p (f₂ x))
    (hsub : IsSubmersionAt IP IB n p (f₁ x₀))
    (hf₁ : ContMDiffAt IM IP n f₁ x₀) (hf₂ : ContMDiffAt IM IP n f₂ x₀) :
    ContMDiffAt IM IG n (fun x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)) x₀ :=
  contMDiffWithinAt_actionDivisionOrOne hn hsmul hfree horbit hinj hker hp hf.self_of_nhds
    (nhdsWithin_univ x₀ ▸ hf) hsub hf₁ hf₂

/-- `ContMDiffOn` form of `contMDiffWithinAt_actionDivisionOrOne`. -/
theorem contMDiffOn_actionDivisionOrOne (hp : ContMDiff IP IB n p) {s : Set M}
    (hf : EqOn (p ∘ f₁) (p ∘ f₂) s)
    (hsub : ∀ x ∈ s, IsSubmersionAt IP IB n p (f₁ x))
    (hf₁ : ContMDiffOn IM IP n f₁ s) (hf₂ : ContMDiffOn IM IP n f₂ s) :
    ContMDiffOn IM IG n (fun x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)) s :=
  fun x hx ↦ contMDiffWithinAt_actionDivisionOrOne hn hsmul hfree horbit hinj hker hp
    (hf hx) (eventually_mem_nhdsWithin.mono fun _ hy ↦ hf hy)
    (hsub x hx) (hf₁ x hx) (hf₂ x hx)

/-- `ContMDiff` form of `contMDiffWithinAt_actionDivisionOrOne`. -/
theorem contMDiff_actionDivisionOrOne (hp : ContMDiff IP IB n p)
    (hf : ∀ x : M, p (f₁ x) = p (f₂ x))
    (hsub : ∀ x : M, IsSubmersionAt IP IB n p (f₁ x))
    (hf₁ : ContMDiff IM IP n f₁) (hf₂ : ContMDiff IM IP n f₂) :
    ContMDiff IM IG n fun x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x) :=
  fun x ↦ contMDiffAt_actionDivisionOrOne hn hsmul hfree horbit hinj hker hp
    (Eventually.of_forall hf) (hsub x) (hf₁ x) (hf₂ x)

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
/-- Finite-dimensional smoothness of `sectionCoord`: for a `C^n` map `p : P → B` (`1 ≤ n`,
finite-dimensional model spaces over `[RCLike 𝕜]`, `[BoundarylessManifold IP P]`,
`[ContMDiffMul IG n G]`) and a jointly `C^n` orbit-exact right `G`-action that is free along a
`C^n` local section `s : B → P` over open `U ⊆ B`, if `d(g ↦ op g • s b)_1` is injective for all
`b ∈ U` and `finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG`, then `sectionCoord horbit hs` is `C^n`
on `p ⁻¹' U`. -/
theorem contMDiffOn_sectionCoord_of_finrank_eq [BoundarylessManifold IP P] (hn : 1 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hp : ContMDiff IP IB n p)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1)
    (hinj : ∀ b ∈ U, Injective (mfderiv IG IP (fun g : G ↦ op g • s b) 1))
    (hdim : finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG) :
    ContMDiffOn IP IG n (sectionCoord horbit hs) (p ⁻¹' U) := by
  have := FiniteDimensional.completeSpace 𝕜 EP; have := FiniteDimensional.completeSpace 𝕜 EB
  have := FiniteDimensional.completeSpace 𝕜 EG
  exact contMDiffOn_sectionCoord hn hsmul hp horbit hU hs_smooth hs hfree hinj fun b hb ↦
    (range_mfderiv_op_smul_one_eq_ker_of_finrank_eq
      (isRegularPoint_of_contMDiffOn_section (ENat.one_le_iff_ne_zero_withTop.mp hn)
        hU hs_smooth hs hb (hp (s b)))
      (fun g ↦ apply_op_smul_eq_of_orbit_eq_fiber horbit g (s b)) (hinj b hb) hdim).ge

end FiniteDimensional

end TauCeti.PrincipalBundle
