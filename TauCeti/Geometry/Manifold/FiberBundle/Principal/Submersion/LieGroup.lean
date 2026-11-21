/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Submersion.Basic
import TauCeti.Geometry.Lie.FundamentalVectorField.Right
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
import TauCeti.Geometry.Manifold.Sard.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Smooth principal bundles from Lie-group submersions (Kolář–Michor–Slovák, Lemma 10.3)

`TauCeti.Geometry.Manifold.FiberBundle.Principal.Submersion.Basic` equips `ProjectionFiber G p`
with `C^n` principal bundle structures assuming injective orbit differentials spanning
`ker (dp_x)`, and reduces that spanning condition in finite dimensions to
`finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG` (`ker_le_range_of_finrank_eq`). This file proves
**Kolář–Michor–Slovák, Lemma 10.3**: for finite-dimensional real `C^n` manifolds (`3 ≤ n`),
boundaryless `P`, and a Lindelöf `C^n` Lie
group `G` acting freely on the right with orbits equal to the fibres of `p`, both infinitesimal
hypotheses hold automatically — orbit injectivity via exponential orbits
(`ContMDiff.injective_mfderiv_op_smul_one_of_op_smul_eq_self_imp`, no `T2Space P` needed), and
`finrank ℝ EP = finrank ℝ EB + finrank ℝ EG` on any regular fibre via `regularFiberChartedSpace`
and Sard's theorem (`MDifferentiable.isNullSet_range_of_finrank_lt_finrank`). The Lindelöf
hypothesis on `G` is essential (e.g. `ℝ → PUnit` under translation by discrete `ℝ`).

## Main definitions and results

* `TauCeti.PrincipalBundle.finrank_eq_add_finrank_of_isRegularValue_of_orbit_eq_fiber`,
  `finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber`: automatic dimension identity.
* `TauCeti.PrincipalBundle.contMDiffOn_sectionCoord_of_lieGroup`: `C^n` section coordinates.
* `TauCeti.PrincipalBundle.fiberBundleOfSubmersionLieGroup`,
  `mem_trivializationAtlas_fiberBundleOfSubmersionLieGroup_iff`,
  `projectionFiber_actionTrivializationOfSection_mem_trivializationAtlas_of_lieGroup`,
  `principalBundleOfSubmersionLieGroup`, `contMDiffFiberBundleOfSubmersionLieGroup`,
  `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup`: Kolář–Michor–Slovák, Lemma 10.3.
* `TauCeti.PrincipalBundle.contMDiffWithinAt_actionDivision_of_lieGroup`,
  `contMDiffAt_actionDivision_of_lieGroup`, `contMDiffOn_actionDivision_of_lieGroup`,
  `contMDiff_actionDivision_of_lieGroup`: `C^n` regularity of `actionDivision` without surjectivity.

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

private theorem finrank_sub_le_finrank_of_isRegularValue_of_orbit_eq_fiber
    [IsManifold IG 1 G] [SMul Gᵐᵒᵖ P] {p : P → B} (hp : ContMDiff IP IB 1 p)
    {x : P} (hreg : IsRegularValue IP IB p (p x))
    (horbit_smooth : ContMDiff IG IP 1 fun g : G ↦ op g • x)
    (horbit : ∀ y : P, p x = p y ↔ ∃ g : G, op g • x = y) :
    finrank ℝ EP - finrank ℝ EB ≤ finrank ℝ EG := by
  have hc : IB.IsInteriorPoint (p x) :=
    ((hp x).mdifferentiableAt one_ne_zero).isInteriorPoint_of_surjective_mfderiv
      (isRegularPoint_iff.1 (hreg.isRegularPoint rfl)) BoundarylessManifold.isInteriorPoint
  let := regularFiberChartedSpace (le_refl 1) hp hc hreg
  have := isManifold_regularFiber (le_refl 1) hp hc hreg
  let θ : G → {y : P // p y = p x} := fun g ↦ ⟨op g • x, ((horbit _).2 ⟨g, rfl⟩).symm⟩
  have hθ_smooth : ContMDiff IG 𝓘(ℝ, Fin (finrank ℝ EP - finrank ℝ EB) → ℝ) 1 θ :=
    (isSmoothEmbedding_coe_regularFiber (le_refl 1) hp hc hreg).contMDiff_iff_comp.2 horbit_smooth
  have hθ_surj : range θ = univ := eq_univ_iff_forall.2 fun ⟨y, hy⟩ ↦ by
    obtain ⟨g, rfl⟩ := (horbit y).1 hy.symm; exact ⟨g, rfl⟩
  by_contra hlt
  have hlt' : finrank ℝ EG < finrank ℝ (Fin (finrank ℝ EP - finrank ℝ EB) → ℝ) := by
    simpa [Module.finrank_fin_fun] using not_le.1 hlt
  have hnull := (hθ_smooth.mdifferentiable one_ne_zero).isNullSet_range_of_finrank_lt_finrank hlt'
  have hdense : Dense (∅ : Set {y : P // p y = p x}) := by simpa [hθ_surj] using hnull.dense_compl
  have : Nonempty {y : P // p y = p x} := ⟨⟨x, rfl⟩⟩
  exact Set.not_nonempty_empty hdense.nonempty

/-- **Automatic dimension identity on a regular fibre.** For a `C¹` map `p : P → B` on
finite-dimensional real `C¹` manifolds (boundaryless `P`) and a `C¹` right action of a Lindelöf
`C^n` Lie group `G` (`3 ≤ n`), if `p x` is a regular value, `x` has trivial stabilizer, and its
orbit equals `p ⁻¹' {p x}`, then `finrank ℝ EP = finrank ℝ EB + finrank ℝ EG`. -/
theorem finrank_eq_add_finrank_of_isRegularValue_of_orbit_eq_fiber {n : ℕ∞ω} [Group G]
    [LieGroup IG n G] (hn : 3 ≤ n) [MulAction Gᵐᵒᵖ P]
    (hsmul : ContMDiff (IP.prod IG) IP 1 fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hp : ContMDiff IP IB 1 p) {x : P} (hreg : IsRegularValue IP IB p (p x))
    (hfree : ∀ g : G, op g • x = x → g = 1)
    (horbit : ∀ y : P, p x = p y ↔ ∃ g : G, op g • x = y) :
    finrank ℝ EP = finrank ℝ EB + finrank ℝ EG := by
  have : IsManifold IG 1 G := .of_le ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn)
  have hinj : Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1) :=
    hsmul.injective_mfderiv_op_smul_one_of_op_smul_eq_self_imp one_ne_zero hn hfree
  have hle := range_mfderiv_op_smul_one_le_ker (IP := IP) (IG := IG) (IB := IB) (p := p) (x := x)
    fun g : G ↦ ((horbit (op g • x)).2 ⟨g, rfl⟩).symm
  have hEG_le : finrank ℝ EG ≤ finrank ℝ (mfderiv IP IB p x).ker := by
    have : FiniteDimensional ℝ (TangentSpace IP x) := inferInstanceAs (FiniteDimensional ℝ EP)
    refine le_trans ?_ (Submodule.finrank_mono (t := (mfderiv IP IB p x).ker) hle)
    exact ((LinearMap.finrank_range_of_inj hinj).trans (finrank_tangentSpace (1 : G))).ge
  have hker_dim := (hreg.isRegularPoint rfl).finrank_ker_mfderiv_add_finrank
  have hle_EG := finrank_sub_le_finrank_of_isRegularValue_of_orbit_eq_fiber hp hreg
    (hsmul.comp (contMDiff_const.prodMk contMDiff_id)) horbit
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
  have hn1 : (1 : ℕ∞ω) ≤ n := (by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn
  have : IsManifold IP 1 P := .of_le hn1; have : IsManifold IB 1 B := .of_le hn1
  exact finrank_eq_add_finrank_of_isRegularValue_of_orbit_eq_fiber hn (hsmul.of_le hn1)
    (hsub.contMDiff.of_le hn1)
    (isRegularValue_iff.2 fun y _ ↦ isRegularPoint_iff.2
      (hsub.surjective_mfderiv (by rintro rfl; simp at hn) y))
    (hfree x) (horbit x)

/-- **Smoothness of `sectionCoord` under a free `C^n` Lindelöf Lie-group action (`3 ≤ n`).** If `s`
is a `C^n` local section of `p : P → B` on open `U ⊆ B` along which the orbit-exact `C^n` right
`G`-action is free, then `sectionCoord horbit hs` is `C^n` on `p ⁻¹' U`. -/
theorem contMDiffOn_sectionCoord_of_lieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hp : ContMDiff IP IB n p)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1) :
    ContMDiffOn IP IG n (sectionCoord horbit hs) (p ⁻¹' U) := by
  have hn1 : (1 : ℕ∞ω) ≤ n := (by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have : IsManifold IP 1 P := .of_le hn1; have : IsManifold IB 1 B := .of_le hn1
  refine contMDiffOn_sectionCoord_of_finrank_eq hn1 hsmul hp horbit hU hs_smooth hs hfree
    (fun b hb ↦ hsmul.injective_mfderiv_op_smul_one_of_op_smul_eq_self_imp hn0 hn (hfree b hb))
    fun b hb ↦ ?_
  have hreg_b : IsRegularPoint IP IB p (s b) :=
    isRegularPoint_iff.2 (surjective_mfderiv_of_eventuallyEq_id ((hp (s b)).mdifferentiableAt hn0)
      ((hs_smooth.contMDiffAt (hU.mem_nhds hb)).mdifferentiableAt hn0)
      (eventually_of_mem (hU.mem_nhds hb) hs))
  have hreg_val : IsRegularValue IP IB p (p (s b)) :=
    isRegularValue_of_isRegularPoint_of_orbit_eq_fiber (fun y _ ↦ (hp y).mdifferentiableAt hn0)
      (fun _ ↦ (hsmul.comp (contMDiff_id.prodMk contMDiff_const) (s b)).mdifferentiableAt hn0)
      (map_op_smul_of_orbit_iff horbit) (fun y hy ↦ (horbit (s b) y).1 hy) hreg_b
  exact finrank_eq_add_finrank_of_isRegularValue_of_orbit_eq_fiber hn (hsmul.of_le hn1)
    (hp.of_le hn1) hreg_val (hfree b hb) (horbit (s b))

section LieGroupSubmersion

variable (hn : 3 ≤ n) (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
  {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
  (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
  (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)

omit [FiniteDimensional ℝ EP] [IP.Boundaryless] [LindelofSpace G] in
include hn hsmul hfree in
private theorem injective_mfderiv_op_smul_one (x : P) :
    Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1) :=
  have hn1 := (by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn
  have : IsManifold IP 1 P := .of_le hn1
  (hsmul.of_le hn1).injective_mfderiv_op_smul_one_of_op_smul_eq_self_imp one_ne_zero hn (hfree x)

include hn hsmul hsub hfree horbit in
private theorem ker_le_range_of_lieGroup (x : P) :
    (mfderiv IP IB p x).ker ≤ (mfderiv IG IP (fun g : G ↦ op g • x) 1).range :=
  ker_le_range_of_finrank_eq ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsub horbit
    (injective_mfderiv_op_smul_one hn hsmul hfree)
    (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit) x

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`FiberBundle` structure).** A surjective `C^n` submersion
(`3 ≤ n`) with a free orbit-exact `C^n` right action of a Lindelöf finite-dimensional real `C^n`
Lie group `G` equips `ProjectionFiber G p` with a `FiberBundle` structure. -/
@[instance_reducible]
def fiberBundleOfSubmersionLieGroup : FiberBundle G (ProjectionFiber G p) :=
  fiberBundleOfSubmersion ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub hsurj hfree horbit
    (injective_mfderiv_op_smul_one hn hsmul hfree)
    (ker_le_range_of_lieGroup hn hsmul hsub hfree horbit)

/-- A trivialization belongs to the atlas of `fiberBundleOfSubmersionLieGroup` iff it is the
`ProjectionFiber` transport of `actionTrivializationOfSection` for some `C^n` local section `s` of
`p` over an open set `U ⊆ B`. -/
theorem mem_trivializationAtlas_fiberBundleOfSubmersionLieGroup_iff
    (e : Trivialization G (π G (ProjectionFiber G p))) :
    (letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit;
      e ∈ trivializationAtlas G (ProjectionFiber G p)) ↔
      ∃ (U : Set B) (hU : IsOpen U) (s : B → P) (_ : ContMDiffOn IB IP n s U)
        (hs : ∀ b ∈ U, p (s b) = b)
        (hcoord : ContinuousOn (sectionCoord horbit hs) (p ⁻¹' U))
        (hsmul_s : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)),
        e = (actionTrivializationOfSection hsub.contMDiff.continuous horbit hfree hU hs hcoord
          hsmul_s).projectionFiber := by
  have hn1 := (by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn
  rw [fiberBundleOfSubmersionLieGroup,
    mem_trivializationAtlas_fiberBundleOfSubmersion_iff hn1 hsmul hsub hsurj hfree horbit
      (injective_mfderiv_op_smul_one hn hsmul hfree)
      (ker_le_range_of_lieGroup hn hsmul hsub hfree horbit)]
  have htriv (U : Set B) (hU : IsOpen U) (s : B → P) (hs_s : ContMDiffOn IB IP n s U)
      (hs : ∀ b ∈ U, p (s b) = b)
      (hcoord : ContinuousOn (sectionCoord horbit hs) (p ⁻¹' U))
      (hsmul_s : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) :
      actionTrivializationOfContMDiffSection hn1 hsmul hsub.contMDiff hfree horbit hU hs_s hs
        (fun b _ ↦ injective_mfderiv_op_smul_one hn hsmul hfree (s b))
        (fun b _ ↦ ker_le_range_of_lieGroup hn hsmul hsub hfree horbit (s b)) =
        actionTrivializationOfSection hsub.contMDiff.continuous horbit hfree hU hs hcoord
          hsmul_s :=
    Trivialization.ext' _ _ (OpenPartialHomeomorph.ext _ _ (fun _ ↦ by simp) (fun _ ↦ by simp) (by
      ext x
      simp only [Trivialization.mem_source, baseSet_actionTrivializationOfContMDiffSection,
        baseSet_actionTrivializationOfSection])) (by simp)
  exact ⟨fun ⟨U, hU, s, hs_s, hs, ht⟩ ↦ by
      have hcoord := (contMDiffOn_sectionCoord_of_lieGroup hn hsmul hsub.contMDiff horbit hU hs_s
        hs fun b _ ↦ hfree (s b)).continuousOn
      have hsmul_s := (hsmul.comp_contMDiffOn ((hs_s.comp (s := U ×ˢ univ) contMDiffOn_fst
        fun _ hq ↦ hq.1).prodMk contMDiffOn_snd)).continuousOn
      exact ⟨U, hU, s, hs_s, hs, hcoord, hsmul_s,
        ht.trans (congrArg Trivialization.projectionFiber
          (htriv U hU s hs_s hs hcoord hsmul_s))⟩,
    fun ⟨U, hU, s, hs_s, hs, hcoord, hsmul_s, ht⟩ ↦
      ⟨U, hU, s, hs_s, hs,
        ht.trans (congrArg Trivialization.projectionFiber
          (htriv U hU s hs_s hs hcoord hsmul_s).symm)⟩⟩

/-- The `ProjectionFiber` transport of `actionTrivializationOfSection` for any `C^n` local section
`s` of `p` over open `U ⊆ B` belongs to the atlas of `fiberBundleOfSubmersionLieGroup`. -/
theorem projectionFiber_actionTrivializationOfSection_mem_trivializationAtlas_of_lieGroup
    {U : Set B} (hU : IsOpen U) {s : B → P} (hs_smooth : ContMDiffOn IB IP n s U)
    (hs : ∀ b ∈ U, p (s b) = b) (hcoord : ContinuousOn (sectionCoord horbit hs) (p ⁻¹' U))
    (hsmul_s : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    (actionTrivializationOfSection hsub.contMDiff.continuous horbit hfree hU hs hcoord
      hsmul_s).projectionFiber ∈ trivializationAtlas G (ProjectionFiber G p) :=
  (mem_trivializationAtlas_fiberBundleOfSubmersionLieGroup_iff hn hsmul hsub hsurj hfree horbit
    _).2 ⟨U, hU, s, hs_smooth, hs, hcoord, hsmul_s, rfl⟩

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`PrincipalBundle` structure).** -/
theorem principalBundleOfSubmersionLieGroup :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
    PrincipalBundle G (ProjectionFiber G p) :=
  principalBundleOfSubmersion ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub hsurj hfree
    horbit (injective_mfderiv_op_smul_one hn hsmul hfree)
    (ker_le_range_of_lieGroup hn hsmul hsub hfree horbit)

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`ContMDiffFiberBundle` structure).** -/
theorem contMDiffFiberBundleOfSubmersionLieGroup :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    ContMDiffFiberBundle n G (ProjectionFiber G p) IB IG :=
  contMDiffFiberBundleOfSubmersion ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub hsurj hfree
    horbit (injective_mfderiv_op_smul_one hn hsmul hfree)
    (ker_le_range_of_lieGroup hn hsmul hsub hfree horbit)

/-- **Kolář–Michor–Slovák, Lemma 10.3 (total-space `C^n` diffeomorphism).** -/
def diffeomorphManifoldTotalSpaceOfSubmersionLieGroup :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    ManifoldTotalSpace G (ProjectionFiber G p) ≃ₘ^n⟮IB.prod IG, IP⟯ P :=
  diffeomorphManifoldTotalSpaceOfSubmersion ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub
    hsurj hfree horbit (injective_mfderiv_op_smul_one hn hsmul hfree)
    (ker_le_range_of_lieGroup hn hsmul hsub hfree horbit)

/-- Forward map of `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_apply
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit q =
      ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).2.val :=
  diffeomorphManifoldTotalSpaceOfSubmersion_apply _ _ _ _ _ _ _ _ q

/-- Inverse map of `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_symm_apply (x : P) :
    (letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit;
      (diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit).symm
        x) =
      ManifoldTotalSpace.homeomorph G (ProjectionFiber G p) ⟨p x, ⟨x, rfl⟩⟩ :=
  diffeomorphManifoldTotalSpaceOfSubmersion_symm_apply _ _ _ _ _ _ _ _ x

/-- `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup` commutes with projections onto `B`. -/
theorem proj_diffeomorphManifoldTotalSpaceOfSubmersionLieGroup
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    p (diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit q) =
      ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).proj :=
  proj_diffeomorphManifoldTotalSpaceOfSubmersion _ _ _ _ _ _ _ _ q

/-- `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup` is `G`-equivariant for right `G`-actions. -/
theorem diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_op_smul
    (g : G) (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    (letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit);
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
  {f₁ f₂ : M → P} (hf : ∀ x : M, p (f₁ x) = p (f₂ x))

include hn hsmul hfree

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`C^n` division map, `ContMDiffWithinAt` form).** For a `C^n`
map `p : P → B` (`3 ≤ n`) submersion at `f₁ x₀` with a free orbit-exact `C^n` right action of a
Lindelöf Lie group `G`, if `f₁, f₂ : M → P` are `C^n` within `s` at `x₀` with `p (f₁ x) = p (f₂ x)`,
then `x ↦ actionDivision horbit (hf x)` is `C^n` within `s` at `x₀`. -/
theorem contMDiffWithinAt_actionDivision_of_lieGroup (hp : ContMDiff IP IB n p) {s : Set M}
    {x₀ : M} (hsub : IsSubmersionAt IP IB n p (f₁ x₀))
    (hf₁ : ContMDiffWithinAt IM IP n f₁ s x₀) (hf₂ : ContMDiffWithinAt IM IP n f₂ s x₀) :
    ContMDiffWithinAt IM IG n (fun x ↦ actionDivision horbit (hf x)) s x₀ := by
  obtain ⟨U, hU, hx₀U, σ, -, hσ_smooth, hσ⟩ := hsub.exists_contMDiffOn_section
  exact contMDiffWithinAt_actionDivision_of_section hp.continuous hfree horbit hU hσ
    (contMDiffOn_sectionCoord_of_lieGroup hn hsmul hp horbit hU hσ_smooth hσ
      (fun b _ ↦ hfree (σ b)))
    hf hx₀U hf₁ hf₂

/-- `ContMDiffAt` form of `contMDiffWithinAt_actionDivision_of_lieGroup`. -/
theorem contMDiffAt_actionDivision_of_lieGroup (hp : ContMDiff IP IB n p) {x₀ : M}
    (hsub : IsSubmersionAt IP IB n p (f₁ x₀))
    (hf₁ : ContMDiffAt IM IP n f₁ x₀) (hf₂ : ContMDiffAt IM IP n f₂ x₀) :
    ContMDiffAt IM IG n (fun x ↦ actionDivision horbit (hf x)) x₀ :=
  contMDiffWithinAt_actionDivision_of_lieGroup hn hsmul hfree horbit hf hp hsub hf₁ hf₂

/-- `ContMDiffOn` form of `contMDiffWithinAt_actionDivision_of_lieGroup`. -/
theorem contMDiffOn_actionDivision_of_lieGroup (hsub : IsSubmersion IP IB n p) {s : Set M}
    (hf₁ : ContMDiffOn IM IP n f₁ s) (hf₂ : ContMDiffOn IM IP n f₂ s) :
    ContMDiffOn IM IG n (fun x ↦ actionDivision horbit (hf x)) s :=
  fun x hx ↦ contMDiffWithinAt_actionDivision_of_lieGroup hn hsmul hfree horbit hf hsub.contMDiff
    (hsub.isSubmersionAt (f₁ x)) (hf₁ x hx) (hf₂ x hx)

/-- `ContMDiff` form of `contMDiffWithinAt_actionDivision_of_lieGroup`. -/
theorem contMDiff_actionDivision_of_lieGroup (hsub : IsSubmersion IP IB n p)
    (hf₁ : ContMDiff IM IP n f₁) (hf₂ : ContMDiff IM IP n f₂) :
    ContMDiff IM IG n fun x ↦ actionDivision horbit (hf x) :=
  fun x ↦ contMDiffAt_actionDivision_of_lieGroup hn hsmul hfree horbit hf hsub.contMDiff
    (hsub.isSubmersionAt (f₁ x)) (hf₁ x) (hf₂ x)

end ActionDivisionLieGroup

end LieGroupReal

end TauCeti.PrincipalBundle
