/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Submersion.Basic
import TauCeti.Geometry.Lie.FundamentalVectorField.Right
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.RegularValue.Section
import TauCeti.Geometry.Manifold.Sard.Basic

/-!
# Smooth principal bundles from Lie-group submersions (Kolář–Michor–Slovák, Lemma 10.3)

This file proves **Kolář–Michor–Slovák, Lemma 10.3** and related local regularity results for
finite-dimensional real `C^n` manifolds (`3 ≤ n`) with source `P` modelled on a boundaryless model
with corners (`[IP.Boundaryless]`) and a Lindelöf `C^n` Lie group `G` acting on the right with
orbits equal to the fibres of `p`:

* **Bundle criterion (surjective submersion):** when `p : P → B` is a surjective `C^n` submersion
  and the action is free, both infinitesimal hypotheses of
  `TauCeti.Geometry.Manifold.FiberBundle.Principal.Submersion.Basic` hold automatically — orbit
  injectivity via exponential orbits
  (`ContMDiff.injective_mfderiv_op_smul_one_of_op_smul_eq_self_imp`, no `T2Space P` needed), and
  `finrank ℝ EP = finrank ℝ EB + finrank ℝ EG` on regular fibres via Sard's theorem
  (`ContMDiff.finrank_sub_le_finrank_of_isRegularValue_of_surjOn_fiber`), yielding
  `range_mfderiv_op_smul_one_eq_ker_of_lieGroup` and principal bundle structures on `MapFiber p`.
* **Local results (without surjectivity of `p`):** along a `C^n` local section `s` over open
  `U ⊆ B` on which the action is free, `sectionCoord` is `C^n` on `p ⁻¹' U`
  (`contMDiffOn_sectionCoord_of_lieGroup`), giving smooth equivariant section charts; similarly
  `actionDivisionOrOne` is `C^n` along locally fibre-matched families where `p` is a submersion at
  the first point (`contMDiffWithinAt_actionDivisionOrOne_of_lieGroup`).

The Lindelöf hypothesis on `G` is essential (e.g. `ℝ → PUnit` under translation by discrete `ℝ`).

## Main definitions and results

* `TauCeti.PrincipalBundle.finrank_eq_add_finrank_of_isRegularValue_of_orbit_eq_fiber`,
  `finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber`,
  `injective_mfderiv_op_smul_one_of_lieGroup`,
  `range_mfderiv_op_smul_one_eq_ker_of_lieGroup`: automatic dimension identity, orbit-differential
  injectivity, and vertical-kernel identification.
* `TauCeti.PrincipalBundle.contMDiffOn_sectionCoord_of_lieGroup`: `C^n` section coordinates.
* `TauCeti.PrincipalBundle.fiberBundleOfSubmersionLieGroup`,
  `mem_trivializationAtlas_fiberBundleOfSubmersionLieGroup_iff`,
  `toMapFiber_actionTrivializationOfSection_mem_trivializationAtlas_of_lieGroup`,
  `principalBundleOfSubmersionLieGroup`, `contMDiffFiberBundleOfSubmersionLieGroup`,
  `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup`: Kolář–Michor–Slovák, Lemma 10.3.
* `TauCeti.PrincipalBundle.contMDiffWithinAt_actionDivisionOrOne_of_lieGroup`,
  `contMDiffAt_actionDivisionOrOne_of_lieGroup`,
  `contMDiffOn_actionDivisionOrOne_of_lieGroup`,
  `contMDiff_actionDivisionOrOne_of_lieGroup`: `C^n` regularity of `actionDivisionOrOne` along
  locally fibre-matched families where `p` is a submersion at the first point, without
  surjectivity.

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

private theorem one_le_of_three_le {n : ℕ∞ω} (hn : 3 ≤ n) : 1 ≤ n :=
  (by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [IP.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [LindelofSpace G]

section Finrank

variable [IsManifold IP 1 P] [IsManifold IB 1 B]

/-- **Automatic dimension identity on a regular fibre.** For a `C¹` map `p : P → B` on
finite-dimensional real `C¹` manifolds (`[IP.Boundaryless]`) and a `C¹` right action of a
Lindelöf `C^n` Lie group `G` (`3 ≤ n`), if `p x` is a regular value, `x` has trivial stabilizer,
and its orbit equals `p ⁻¹' {p x}`, then `finrank ℝ EP = finrank ℝ EB + finrank ℝ EG`. -/
theorem finrank_eq_add_finrank_of_isRegularValue_of_orbit_eq_fiber {n : ℕ∞ω} [Group G]
    [LieGroup IG n G] (hn : 3 ≤ n) [MulAction Gᵐᵒᵖ P]
    (hsmul : ContMDiff (IP.prod IG) IP 1 fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hp : ContMDiff IP IB 1 p) {x : P} (hreg : IsRegularValue IP IB p (p x))
    (hfree : ∀ g : G, op g • x = x → g = 1)
    (horbit : ∀ y : P, p x = p y ↔ ∃ g : G, op g • x = y) :
    finrank ℝ EP = finrank ℝ EB + finrank ℝ EG := by
  have : IsManifold IG 1 G := .of_le (one_le_of_three_le hn)
  have hinj : Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1) :=
    hsmul.injective_mfderiv_op_smul_one_of_op_smul_eq_self_imp one_ne_zero hn hfree
  have hle := range_mfderiv_op_smul_one_le_ker (IP := IP) (IG := IG) (IB := IB) (p := p) (x := x)
    fun g : G ↦ ((horbit (op g • x)).2 ⟨g, rfl⟩).symm
  have hEG_le : finrank ℝ EG ≤ finrank ℝ (mfderiv IP IB p x).ker := by
    have : FiniteDimensional ℝ (TangentSpace IP x) := inferInstanceAs (FiniteDimensional ℝ EP)
    refine le_trans ?_ (Submodule.finrank_mono (t := (mfderiv IP IB p x).ker) hle)
    exact ((LinearMap.finrank_range_of_inj hinj).trans (finrank_tangentSpace (1 : G))).ge
  have hker_dim := (hreg.isRegularPoint rfl).finrank_ker_mfderiv_add_finrank
  have hle_EG := hp.finrank_sub_le_finrank_of_isRegularValue_of_surjOn_fiber ⟨x, rfl⟩ hreg
    (hsmul.comp (contMDiff_const.prodMk contMDiff_id))
    (fun g ↦ ((horbit (op g • x)).2 ⟨g, rfl⟩).symm)
    fun y hy ↦ (horbit y).1 hy.symm
  omega

end Finrank

section LieGroupReal

variable {n : ℕ∞ω} [IsManifold IP n P] [IsManifold IB n B]
  [Group G] [LieGroup IG n G] [MulAction Gᵐᵒᵖ P]

/-- **Automatic dimension identity for a Lindelöf Lie group acting transitively and freely on the
fibres of a `C^n` submersion (`3 ≤ n`).** -/
theorem finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y) (x : P) :
    finrank ℝ EP = finrank ℝ EB + finrank ℝ EG := by
  have hn1 : (1 : ℕ∞ω) ≤ n := one_le_of_three_le hn
  have : IsManifold IP 1 P := .of_le hn1; have : IsManifold IB 1 B := .of_le hn1
  exact finrank_eq_add_finrank_of_isRegularValue_of_orbit_eq_fiber hn (hsmul.of_le hn1)
    (hsub.contMDiff.of_le hn1)
    (isRegularValue_iff.2 fun y _ ↦ isRegularPoint_iff.2
      (hsub.surjective_mfderiv (ENat.one_le_iff_ne_zero_withTop.mp hn1) y))
    (hfree x) (horbit x)

/-- **Smoothness of `sectionCoord` under a free `C^n` Lindelöf Lie-group action (`3 ≤ n`).** For
finite-dimensional real `C^n` manifolds with `P` modelled on a boundaryless model with corners
(`[IP.Boundaryless]`), a `C^n` map `p : P → B`, and a Lindelöf `C^n` Lie group `G` with a jointly
`C^n` orbit-exact right action free along a `C^n` local section `s` over open `U ⊆ B`,
`sectionCoord horbit hs` is `C^n` on `p ⁻¹' U`. -/
theorem contMDiffOn_sectionCoord_of_lieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hp : ContMDiff IP IB n p)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1) :
    ContMDiffOn IP IG n (sectionCoord horbit hs) (p ⁻¹' U) := by
  have hn1 : (1 : ℕ∞ω) ≤ n := one_le_of_three_le hn
  have hn0 : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hn1
  have : IsManifold IP 1 P := .of_le hn1; have : IsManifold IB 1 B := .of_le hn1
  rcases U.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · simp only [preimage_empty, contMDiffOn_empty]
  · have hreg_b : IsRegularPoint IP IB p (s b₀) :=
      isRegularPoint_of_contMDiffOn_section hn0 hU hs_smooth hs hb₀ (hp (s b₀))
    have hreg_val : IsRegularValue IP IB p (p (s b₀)) :=
      isRegularValue_of_isRegularPoint_of_orbit_eq_fiber (fun y _ ↦ (hp y).mdifferentiableAt hn0)
        (fun _ ↦ (hsmul.comp (contMDiff_id.prodMk contMDiff_const) (s b₀)).mdifferentiableAt hn0)
        (apply_op_smul_eq_of_orbit_eq_fiber horbit) (fun y hy ↦ (horbit (s b₀) y).1 hy) hreg_b
    have hdim : finrank ℝ EP = finrank ℝ EB + finrank ℝ EG :=
      finrank_eq_add_finrank_of_isRegularValue_of_orbit_eq_fiber hn (hsmul.of_le hn1)
        (hp.of_le hn1) hreg_val (hfree b₀ hb₀) (horbit (s b₀))
    exact contMDiffOn_sectionCoord_of_finrank_eq hn1 hsmul hp horbit hU hs_smooth hs hfree
      (fun b hb ↦ hsmul.injective_mfderiv_op_smul_one_of_op_smul_eq_self_imp hn0 hn (hfree b hb))
      hdim

section VerticalKernel

omit [FiniteDimensional ℝ EP] [IP.Boundaryless] [LindelofSpace G] in
/-- For a free jointly `C^n` right action (`3 ≤ n`) of a `C^n` Lie group `G` on a `C^n` manifold
`P`, the orbit differential `d(g ↦ op g • x)_1` is injective at every `x : P`. -/
theorem injective_mfderiv_op_smul_one_of_lieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1) (x : P) :
    Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1) :=
  have hn1 := one_le_of_three_le hn
  have : IsManifold IP 1 P := .of_le hn1
  ContMDiff.injective_mfderiv_op_smul_one_of_op_smul_eq_self_imp (hsmul.of_le hn1) one_ne_zero hn
    (hfree x)

/-- Under the Lie-group submersion hypotheses (`3 ≤ n`, finite-dimensional real `C^n` manifolds
with `[IP.Boundaryless]`, `C^n` submersion `p : P → B`, and free orbit-exact `C^n` right action of
a Lindelöf `C^n` Lie group `G`), the range of the orbit differential `d(g ↦ op g • x)_1` equals
`ker (dp_x)`. -/
theorem range_mfderiv_op_smul_one_eq_ker_of_lieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y) (x : P) :
    (mfderiv IG IP (fun g : G ↦ op g • x) 1).range = (mfderiv IP IB p x).ker :=
  range_mfderiv_op_smul_one_eq_ker_of_finrank_eq
    (isRegularPoint_iff.2
      (hsub.surjective_mfderiv (ENat.one_le_iff_ne_zero_withTop.mp (one_le_of_three_le hn)) x))
    (fun g ↦ apply_op_smul_eq_of_orbit_eq_fiber horbit g x)
    (injective_mfderiv_op_smul_one_of_lieGroup hn hsmul hfree x)
    (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit x)

end VerticalKernel

section LieGroupSubmersion

variable (hn : 3 ≤ n) (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
  {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
  (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
  (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`FiberBundle` structure).** A surjective `C^n` submersion
(`3 ≤ n`) between finite-dimensional real `C^n` manifolds with source `P` modelled on a
boundaryless model with corners (`[IP.Boundaryless]`), equipped with a free orbit-exact `C^n` right
action of a Lindelöf finite-dimensional real `C^n` Lie group `G`, equips `MapFiber p` with a
`FiberBundle` structure. -/
@[instance_reducible]
def fiberBundleOfSubmersionLieGroup : FiberBundle G (MapFiber p) :=
  fiberBundleOfSubmersion (one_le_of_three_le hn) hsmul hsub hsurj hfree horbit
    (injective_mfderiv_op_smul_one_of_lieGroup hn hsmul hfree)
    (fun x ↦ (range_mfderiv_op_smul_one_eq_ker_of_lieGroup hn hsmul hsub hfree horbit x).ge)

/-- A trivialization belongs to the atlas of `fiberBundleOfSubmersionLieGroup` iff it is the
`MapFiber` transport of `sectionTrivialization` for some `C^n` local section `s` of `p` over an
open set `U ⊆ B`. -/
theorem mem_trivializationAtlas_fiberBundleOfSubmersionLieGroup_iff
    (e : Trivialization G (π G (MapFiber p))) :
    (letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit;
      e ∈ trivializationAtlas G (MapFiber p)) ↔
      ∃ (U : Set B) (hU : IsOpen U) (s : B → P) (hs_smooth : ContMDiffOn IB IP n s U)
        (hs : ∀ b ∈ U, p (s b) = b),
        e = (sectionTrivialization ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub.contMDiff
          horbit hU hs_smooth hs (fun b _ ↦ hfree (s b))
          (fun b _ ↦ injective_mfderiv_op_smul_one_of_lieGroup hn hsmul hfree (s b))
          (fun b _ ↦ (range_mfderiv_op_smul_one_eq_ker_of_lieGroup hn hsmul hsub hfree horbit
            (s b)).ge)).toMapFiber := by
  rw [fiberBundleOfSubmersionLieGroup,
    mem_trivializationAtlas_fiberBundleOfSubmersion_iff (one_le_of_three_le hn) hsmul hsub hsurj
      hfree horbit (injective_mfderiv_op_smul_one_of_lieGroup hn hsmul hfree)
      (fun x ↦ (range_mfderiv_op_smul_one_eq_ker_of_lieGroup hn hsmul hsub hfree horbit x).ge)]

/-- The `MapFiber` transport of `Continuous.actionTrivializationOfSection` for any `C^n` local
section `s` of `p` over open `U ⊆ B` belongs to the atlas of `fiberBundleOfSubmersionLieGroup`. -/
theorem toMapFiber_actionTrivializationOfSection_mem_trivializationAtlas_of_lieGroup
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b)
    (hcoord : ContinuousOn (sectionCoord horbit hs) (p ⁻¹' U))
    (hsmul_s : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    (hsub.contMDiff.continuous.actionTrivializationOfSection horbit hU (fun b _ ↦ hfree (s b)) hs
      hcoord hsmul_s).toMapFiber ∈ trivializationAtlas G (MapFiber p) :=
  toMapFiber_actionTrivializationOfSection_mem_trivializationAtlas (one_le_of_three_le hn) hsmul
    hsub hsurj hfree horbit (injective_mfderiv_op_smul_one_of_lieGroup hn hsmul hfree)
    (fun x ↦ (range_mfderiv_op_smul_one_eq_ker_of_lieGroup hn hsmul hsub hfree horbit x).ge)
    hU hs_smooth hs hcoord hsmul_s

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`PrincipalBundle` structure).** Under the same hypotheses as
`fiberBundleOfSubmersionLieGroup` (surjective `C^n` submersion `p : P → B`, `3 ≤ n`, finite
dimensions, `[IP.Boundaryless]`, and free orbit-exact `C^n` right action of a Lindelöf Lie group
`G`), `MapFiber p` carries a `PrincipalBundle G (MapFiber p)` structure. -/
theorem principalBundleOfSubmersionLieGroup :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
    PrincipalBundle G (MapFiber p) :=
  principalBundleOfSubmersion (one_le_of_three_le hn) hsmul hsub hsurj hfree horbit
    (injective_mfderiv_op_smul_one_of_lieGroup hn hsmul hfree)
    (fun x ↦ (range_mfderiv_op_smul_one_eq_ker_of_lieGroup hn hsmul hsub hfree horbit x).ge)

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`ContMDiffFiberBundle` structure).** Under the same
hypotheses as `fiberBundleOfSubmersionLieGroup` (surjective `C^n` submersion `p : P → B`, `3 ≤ n`,
finite dimensions, `[IP.Boundaryless]`, and free orbit-exact `C^n` right action of a Lindelöf Lie
group `G`), `MapFiber p` is a `C^n` smooth fibre bundle (`ContMDiffFiberBundle n G (MapFiber p) IB
IG`). -/
theorem contMDiffFiberBundleOfSubmersionLieGroup :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    ContMDiffFiberBundle n G (MapFiber p) IB IG :=
  contMDiffFiberBundleOfSubmersion (one_le_of_three_le hn) hsmul hsub hsurj hfree horbit
    (injective_mfderiv_op_smul_one_of_lieGroup hn hsmul hfree)
    (fun x ↦ (range_mfderiv_op_smul_one_eq_ker_of_lieGroup hn hsmul hsub hfree horbit x).ge)

/-- **Kolář–Michor–Slovák, Lemma 10.3 (total-space `C^n` diffeomorphism).** Under the same
hypotheses as `fiberBundleOfSubmersionLieGroup` (surjective `C^n` submersion `p : P → B`, `3 ≤ n`,
finite dimensions, `[IP.Boundaryless]`, and free orbit-exact `C^n` right action of a Lindelöf Lie
group `G`), the charted total space `ManifoldTotalSpace G (MapFiber p)` is `G`-equivariantly
`C^n` diffeomorphic to `P` over `B`. -/
def diffeomorphManifoldTotalSpaceOfSubmersionLieGroup :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    ManifoldTotalSpace G (MapFiber p) ≃ₘ^n⟮IB.prod IG, IP⟯ P :=
  diffeomorphManifoldTotalSpaceOfSubmersion (one_le_of_three_le hn) hsmul hsub hsurj hfree horbit
    (injective_mfderiv_op_smul_one_of_lieGroup hn hsmul hfree)
    (fun x ↦ (range_mfderiv_op_smul_one_eq_ker_of_lieGroup hn hsmul hsub hfree horbit x).ge)

/-- Forward map of `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_apply
    (q : ManifoldTotalSpace G (MapFiber p)) :
    diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit q =
      ((ManifoldTotalSpace.homeomorph G (MapFiber p)).symm q).snd.val :=
  diffeomorphManifoldTotalSpaceOfSubmersion_apply _ _ _ _ _ _ _ _ q

/-- Inverse map of `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_symm_apply (x : P) :
    (letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit;
      (diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit).symm
        x) =
      ManifoldTotalSpace.homeomorph G (MapFiber p) ⟨p x, ⟨x, rfl⟩⟩ :=
  diffeomorphManifoldTotalSpaceOfSubmersion_symm_apply _ _ _ _ _ _ _ _ x

/-- `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup` commutes with projections onto `B`. -/
theorem proj_diffeomorphManifoldTotalSpaceOfSubmersionLieGroup
    (q : ManifoldTotalSpace G (MapFiber p)) :
    p (diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit q) =
      ((ManifoldTotalSpace.homeomorph G (MapFiber p)).symm q).proj :=
  proj_diffeomorphManifoldTotalSpaceOfSubmersion _ _ _ _ _ _ _ _ q

/-- `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup` is `G`-equivariant for right `G`-actions. -/
theorem diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_op_smul
    (g : G) (q : ManifoldTotalSpace G (MapFiber p)) :
    (letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit);
      diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
        (op g • q)) =
      op g • diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
        q :=
  diffeomorphManifoldTotalSpaceOfSubmersion_op_smul _ _ _ _ _ _ _ _ g q

end LieGroupSubmersion

section ActionDivisionLieGroup

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  (hn : 3 ≤ n) (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
  {p : P → B} (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
  (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
  {f₁ f₂ : M → P}

include hn hsmul hfree

/-- **`C^n` division map along families in a common fibre** (`ContMDiffWithinAt` form, cf.
Kolář–Michor–Slovák §10.2), deduced from smooth section coordinates
(`contMDiffOn_sectionCoord_of_lieGroup`). For finite-dimensional real `C^n` manifolds (`3 ≤ n`)
with `P` modelled on a boundaryless model with corners (`[IP.Boundaryless]`), a `C^n` map
`p : P → B` that is a submersion at `f₁ x₀`, and a free orbit-exact jointly `C^n` right action of
a Lindelöf `C^n` Lie group `G`, if `f₁, f₂ : M → P` are `C^n` within `s` at `x₀` with
`p (f₁ x₀) = p (f₂ x₀)` and `∀ᶠ x in 𝓝[s] x₀, p (f₁ x) = p (f₂ x)`, then
`x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)` is `C^n` within `s` at `x₀`. -/
theorem contMDiffWithinAt_actionDivisionOrOne_of_lieGroup (hp : ContMDiff IP IB n p) {s : Set M}
    {x₀ : M} (hf₀ : p (f₁ x₀) = p (f₂ x₀)) (hf : ∀ᶠ x in 𝓝[s] x₀, p (f₁ x) = p (f₂ x))
    (hsub : IsSubmersionAt IP IB n p (f₁ x₀))
    (hf₁ : ContMDiffWithinAt IM IP n f₁ s x₀) (hf₂ : ContMDiffWithinAt IM IP n f₂ s x₀) :
    ContMDiffWithinAt IM IG n (fun x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)) s x₀ := by
  obtain ⟨U, hU, hx₀U, σ, -, hσ_smooth, hσ⟩ := hsub.exists_contMDiffOn_section
  exact hp.continuous.contMDiffWithinAt_actionDivisionOrOne_of_section horbit hU
    (fun b _ ↦ hfree (σ b)) hσ
    (contMDiffOn_sectionCoord_of_lieGroup hn hsmul hp horbit hU hσ_smooth hσ
      (fun b _ ↦ hfree (σ b)))
    hf₀ hf hx₀U hf₁ hf₂

/-- `ContMDiffAt` form of `contMDiffWithinAt_actionDivisionOrOne_of_lieGroup`. -/
theorem contMDiffAt_actionDivisionOrOne_of_lieGroup (hp : ContMDiff IP IB n p) {x₀ : M}
    (hf : ∀ᶠ x in 𝓝 x₀, p (f₁ x) = p (f₂ x))
    (hsub : IsSubmersionAt IP IB n p (f₁ x₀))
    (hf₁ : ContMDiffAt IM IP n f₁ x₀) (hf₂ : ContMDiffAt IM IP n f₂ x₀) :
    ContMDiffAt IM IG n (fun x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)) x₀ :=
  contMDiffWithinAt_actionDivisionOrOne_of_lieGroup hn hsmul hfree horbit hp hf.self_of_nhds
    (nhdsWithin_univ x₀ ▸ hf) hsub hf₁ hf₂

/-- `ContMDiffOn` form of `contMDiffWithinAt_actionDivisionOrOne_of_lieGroup`. -/
theorem contMDiffOn_actionDivisionOrOne_of_lieGroup (hp : ContMDiff IP IB n p) {s : Set M}
    (hf : EqOn (p ∘ f₁) (p ∘ f₂) s)
    (hsub : ∀ x ∈ s, IsSubmersionAt IP IB n p (f₁ x))
    (hf₁ : ContMDiffOn IM IP n f₁ s) (hf₂ : ContMDiffOn IM IP n f₂ s) :
    ContMDiffOn IM IG n (fun x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x)) s :=
  fun x hx ↦ contMDiffWithinAt_actionDivisionOrOne_of_lieGroup hn hsmul hfree horbit hp (hf hx)
    (eventually_mem_nhdsWithin.mono fun _ hy ↦ hf hy) (hsub x hx) (hf₁ x hx) (hf₂ x hx)

/-- `ContMDiff` form of `contMDiffWithinAt_actionDivisionOrOne_of_lieGroup`. -/
theorem contMDiff_actionDivisionOrOne_of_lieGroup (hp : ContMDiff IP IB n p)
    (hf : ∀ x : M, p (f₁ x) = p (f₂ x))
    (hsub : ∀ x : M, IsSubmersionAt IP IB n p (f₁ x))
    (hf₁ : ContMDiff IM IP n f₁) (hf₂ : ContMDiff IM IP n f₂) :
    ContMDiff IM IG n fun x ↦ actionDivisionOrOne horbit (f₁ x) (f₂ x) :=
  fun x ↦ contMDiffAt_actionDivisionOrOne_of_lieGroup hn hsmul hfree horbit hp
    (Eventually.of_forall hf) (hsub x) (hf₁ x) (hf₂ x)

end ActionDivisionLieGroup

end LieGroupReal

end TauCeti.PrincipalBundle
