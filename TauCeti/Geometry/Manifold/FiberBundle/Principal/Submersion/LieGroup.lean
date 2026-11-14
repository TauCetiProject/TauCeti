/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Submersion.Basic
import TauCeti.Geometry.Lie.FundamentalVectorField.Right
import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
import TauCeti.Geometry.Manifold.Sard.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Smooth principal bundles from Lie-group submersions (Kolář–Michor–Slovák, Lemma 10.3)

`TauCeti.Geometry.Manifold.FiberBundle.Principal.Submersion.Basic` constructs `C^n` principal
`G`-bundle structures on `TauCeti.ProjectionFiber G p` for any surjective `C^n` submersion
`p : P → B` with a free `C^n` right `G`-action whose orbits are the fibres of `p`, provided the
orbit differentials `d(g ↦ op g • x)_1` are injective and span the vertical tangent spaces (or, in
finite dimensions, `finrank 𝕜 EP = finrank 𝕜 EB + finrank 𝕜 EG`).

This file proves **Kolář–Michor–Slovák, Lemma 10.3**: when `P`, `B`, and `G` are finite-dimensional
real `C^n` manifolds (`3 ≤ n`, including `n = ∞` and `n = ω`), `P` is boundaryless, and `G` is a
Lindelöf `C^n` Lie group acting freely on the right with orbits equal to the fibres of a surjective
`C^n` submersion `p : P → B`, *both* infinitesimal hypotheses hold automatically:

* injectivity of `d(g ↦ op g • x)_1` follows from freeness via exponential orbits
  (`TauCeti.injective_mfderiv_op_smul_one_of_forall_op_smul_eq`), with no separation assumption on
  `P`;
* the dimension identity `finrank ℝ EP = finrank ℝ EB + finrank ℝ EG` follows by equipping each
  fibre `{y : P // p y = p x}` with its regular-fibre `C¹` submanifold structure
  (`regularFiberChartedSpace`) of dimension `finrank ℝ EP - finrank ℝ EB` and ruling out
  `finrank ℝ EG < finrank ℝ EP - finrank ℝ EB` by Sard's theorem in smaller source dimension
  (`MDifferentiable.isNullSet_range_of_finrank_lt_finrank`). The Lindelöf hypothesis on `G` is
  essential: the projection `ℝ → PUnit` under translation by `ℝ` with the discrete topology
  satisfies every other hypothesis while failing local triviality.

## Main definitions and results

* `TauCeti.PrincipalBundle.finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber`: automatic
  dimension equality `finrank ℝ EP = finrank ℝ EB + finrank ℝ EG` for a Lindelöf real Lie group.
* `TauCeti.PrincipalBundle.fiberBundleOfSubmersionLieGroup`,
  `TauCeti.PrincipalBundle.principalBundleOfSubmersionLieGroup`,
  `TauCeti.PrincipalBundle.contMDiffFiberBundleOfSubmersionLieGroup`,
  `TauCeti.PrincipalBundle.diffeomorphManifoldTotalSpaceOfSubmersionLieGroup`: Kolář–Michor–Slovák,
  Lemma 10.3.
* `TauCeti.PrincipalBundle.contMDiff_actionDivision_of_lieGroup`: `C^n` regularity of
  `actionDivision` along pairs of `C^n` maps in a common fibre under the hypotheses of Lemma 10.3.

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

section LieGroupReal

variable {n : ℕ∞ω}
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [IP.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP n P]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [LieGroup IG n G] [LindelofSpace G] [MulAction Gᵐᵒᵖ P]

omit [FiniteDimensional ℝ EP] [IP.Boundaryless] [LindelofSpace G] in
/-- For `3 ≤ n`, a free `C^n` right action of a finite-dimensional real Lie group `G` has injective
orbit differential at `1` at every point `x : P`, with no separation assumption on `P`. -/
private theorem injective_mfderiv_orbit_of_lieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1) (x : P) :
    Injective (mfderiv IG IP (fun g : G ↦ op g • x) 1) := by
  have hn1 : 1 ≤ n := (by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn1 (by simp)
  have : IsManifold IP 1 P := .of_le hn1
  have : LieGroup IG 1 G := LieGroup.of_le hn1
  have : LieGroup IG (minSmoothness ℝ 3) G := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact LieGroup.of_le hn
  let _ : T2Space G := IG.t2Space_of_lieGroup n
  have : BoundarylessManifold IG G := ContMDiffMul.boundarylessManifold
  exact injective_mfderiv_op_smul_one_of_forall_op_smul_eq
    ((hsmul.comp (contMDiff_const.prodMk contMDiff_id) 1).mdifferentiableAt hn0)
    (fun g ↦ ((hsmul.comp (contMDiff_id.prodMk contMDiff_const) x).mdifferentiableAt hn0))
    (hfree x)

/-- **Automatic dimension identity for a Lindelöf Lie group acting transitively and freely on the
fibres of a submersion.** Injectivity of the orbit differential gives
`finrank ℝ EB + finrank ℝ EG ≤ finrank ℝ EP`, while Sard's theorem applied to the surjective `C¹`
orbit map `G → {y : P // p y = p x}` into the regular-fibre submanifold rules out strict
inequality. -/
theorem finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y) (x : P) :
    finrank ℝ EP = finrank ℝ EB + finrank ℝ EG := by
  have hn1 : 1 ≤ n := (by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn1 (by simp)
  have : IsManifold IP 1 P := .of_le hn1
  have : IsManifold IB 1 B := .of_le hn1
  have : IsManifold IG 1 G := .of_le hn1
  -- Upper bound on `finrank ℝ EG` from injectivity of the orbit differential into `ker (dp_x)`.
  have hinj := injective_mfderiv_orbit_of_lieGroup hn hsmul hfree x
  let dpAt (w : P) : EP →L[ℝ] EB := mfderiv IP IB p w
  let dorb : EG →L[ℝ] EP := mfderiv IG IP (fun g : G ↦ op g • x) 1
  have hle_ker : dorb.toLinearMap.range ≤ (dpAt x).toLinearMap.ker := by
    have h : dorb.toLinearMap.range ≤ (dpAt (op (1 : G) • x)).toLinearMap.ker :=
      range_mfderiv_le_ker_mfderiv_of_eventually_eq (K := IG) (I := IP) (J := IB)
        (f := p) (g := fun g : G ↦ op g • x) (p := (1 : G)) (y := p x)
        (Eventually.of_forall fun g : G ↦ map_op_smul_of_orbit_iff horbit g x)
    exact h.trans (congrArg (fun w ↦ (dpAt w).toLinearMap.ker) (by rw [op_one, one_smul])).le
  have hreg_x : IsRegularPoint IP IB p x := isRegularPoint_iff.2 (hsub.surjective_mfderiv hn0 x)
  have hker_dim := hreg_x.finrank_ker_mfderiv_add_finrank
  have hEG_le : finrank ℝ EG ≤ finrank ℝ ((mfderiv IP IB p x).ker) := by
    have hinj' : Injective dorb := hinj
    have h := Submodule.finrank_mono hle_ker
    rw [LinearMap.finrank_range_of_inj hinj'] at h
    exact h
  -- Lower bound via Sard's theorem on the regular-fibre `C¹` submanifold `{y : P // p y = p x}`.
  have hp1 : ContMDiff IP IB 1 p := hsub.contMDiff.of_le hn1
  have hc : IB.IsInteriorPoint (p x) :=
    (hp1 x |>.mdifferentiableAt one_ne_zero).isInteriorPoint_of_surjective_mfderiv
      (hsub.surjective_mfderiv hn0 x) BoundarylessManifold.isInteriorPoint
  have hreg : IsRegularValue IP IB p (p x) := by
    rw [isRegularValue_iff]
    intro y _
    exact isRegularPoint_iff.2 (hsub.surjective_mfderiv hn0 y)
  let := regularFiberChartedSpace (le_refl 1) hp1 hc hreg
  have := isManifold_regularFiber (le_refl 1) hp1 hc hreg
  have hemb := isSmoothEmbedding_coe_regularFiber (le_refl 1) hp1 hc hreg
  let θ : G → {y : P // p y = p x} := fun g ↦ ⟨op g • x, map_op_smul_of_orbit_iff horbit g x⟩
  have hθ_smooth : ContMDiff IG 𝓘(ℝ, Fin (finrank ℝ EP - finrank ℝ EB) → ℝ) 1 θ :=
    hemb.contMDiff_iff_comp.2 ((hsmul.of_le hn1).comp (contMDiff_const.prodMk contMDiff_id))
  have hθ_surj : range θ = univ := eq_univ_iff_forall.2 fun ⟨y, hy⟩ ↦ by
    obtain ⟨g, rfl⟩ := (horbit x y).1 hy.symm
    exact ⟨g, rfl⟩
  have hnot_lt : ¬ finrank ℝ EG < finrank ℝ EP - finrank ℝ EB := by
    intro hlt
    have hlt' : finrank ℝ EG < finrank ℝ (Fin (finrank ℝ EP - finrank ℝ EB) → ℝ) := by
      simpa [Module.finrank_fin_fun] using hlt
    have hnull := (hθ_smooth.mdifferentiable one_ne_zero).isNullSet_range_of_finrank_lt_finrank hlt'
    rw [hθ_surj] at hnull
    have hdense := hnull.dense_compl
    rw [compl_univ] at hdense
    have : Nonempty {y : P // p y = p x} := ⟨⟨x, rfl⟩⟩
    exact Set.not_nonempty_empty hdense.nonempty
  omega

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`FiberBundle` structure).** A surjective `C^n` submersion
(`3 ≤ n`) from a boundaryless finite-dimensional real manifold `P` onto `B`, equipped with a free
`C^n` right action of a Lindelöf finite-dimensional `C^n` Lie group `G` whose orbits are the fibres
of `p`, endows `ProjectionFiber G p` with a `FiberBundle` structure. -/
@[instance_reducible]
def fiberBundleOfSubmersionLieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y) :
    FiberBundle G (ProjectionFiber G p) :=
  fiberBundleOfSubmersionOfFinrankEq ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub hsurj
    hfree horbit (injective_mfderiv_orbit_of_lieGroup hn hsmul hfree)
    (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit)

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`PrincipalBundle` structure).** -/
theorem principalBundleOfSubmersionLieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y) :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
    PrincipalBundle G (ProjectionFiber G p) :=
  principalBundleOfSubmersionOfFinrankEq ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub hsurj
    hfree horbit (injective_mfderiv_orbit_of_lieGroup hn hsmul hfree)
    (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit)

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`ContMDiffFiberBundle` structure).** -/
theorem contMDiffFiberBundleOfSubmersionLieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y) :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    ContMDiffFiberBundle n G (ProjectionFiber G p) IB IG :=
  contMDiffFiberBundleOfSubmersionOfFinrankEq ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub
    hsurj hfree horbit (injective_mfderiv_orbit_of_lieGroup hn hsmul hfree)
    (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit)

/-- **Kolář–Michor–Slovák, Lemma 10.3 (total-space `C^n` diffeomorphism).** For a surjective `C^n`
submersion (`3 ≤ n`) with a free `C^n` right action of a Lindelöf finite-dimensional real Lie group
`G` whose orbits are the fibres, `ManifoldTotalSpace G (ProjectionFiber G p)` is canonically `C^n`
diffeomorphic to `P`. -/
def diffeomorphManifoldTotalSpaceOfSubmersionLieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y) :
    letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
    ManifoldTotalSpace G (ProjectionFiber G p) ≃ₘ^n⟮IB.prod IG, IP⟯ P :=
  diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn)
    hsmul hsub hsurj hfree horbit (injective_mfderiv_orbit_of_lieGroup hn hsmul hfree)
    (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit)

/-- Forward map of `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_apply (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit q =
      ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).2.val :=
  diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq_apply
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub hsurj hfree horbit
    (injective_mfderiv_orbit_of_lieGroup hn hsmul hfree)
    (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit) q

/-- Inverse map of `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup`. -/
@[simp]
theorem diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_symm_apply (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y) (x : P) :
    (letI := fiberBundleOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit;
      (diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit).symm
        x) =
      ManifoldTotalSpace.homeomorph G (ProjectionFiber G p) ⟨p x, ⟨x, rfl⟩⟩ :=
  diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq_symm_apply
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub hsurj hfree horbit
    (injective_mfderiv_orbit_of_lieGroup hn hsmul hfree)
    (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit) x

/-- `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup` commutes with the projections onto `B`. -/
theorem proj_diffeomorphManifoldTotalSpaceOfSubmersionLieGroup (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    p (diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit q) =
      ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).proj := by
  rw [diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_apply]
  exact ((ManifoldTotalSpace.homeomorph G (ProjectionFiber G p)).symm q).2.map_val

/-- `diffeomorphManifoldTotalSpaceOfSubmersionLieGroup` is `G`-equivariant for the right
`G`-actions. -/
theorem diffeomorphManifoldTotalSpaceOfSubmersionLieGroup_op_smul (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    (g : G) (q : ManifoldTotalSpace G (ProjectionFiber G p)) :
    (letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit);
      diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
        (op g • q)) =
      op g • diffeomorphManifoldTotalSpaceOfSubmersionLieGroup hn hsmul hsub hsurj hfree horbit
        q :=
  diffeomorphManifoldTotalSpaceOfSubmersionOfFinrankEq_op_smul
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub hsurj hfree horbit
    (injective_mfderiv_orbit_of_lieGroup hn hsmul hfree)
    (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit) g q

/-- **Kolář–Michor–Slovák, Lemma 10.3 (`C^n` division map).** Under the hypotheses of Lemma 10.3,
for any `C^n` maps `f₁, f₂ : M → P` from a `C^n` manifold `M` satisfying `p (f₁ x) = p (f₂ x)`, the
transition map `x ↦ actionDivision horbit (hf x)` is `C^n`. -/
theorem contMDiff_actionDivision_of_lieGroup {EM : Type*} [NormedAddCommGroup EM]
    [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] (hn : 3 ≤ n)
    (hsmul : ContMDiff (IP.prod IG) IP n fun q : P × G ↦ op q.2 • q.1)
    {p : P → B} (hsub : IsSubmersion IP IB n p) (hsurj : Surjective p)
    (hfree : ∀ (x : P) (g : G), op g • x = x → g = 1)
    (horbit : ∀ x y : P, p x = p y ↔ ∃ g : G, op g • x = y)
    {f₁ f₂ : M → P} (hf : ∀ x : M, p (f₁ x) = p (f₂ x))
    (hf₁ : ContMDiff IM IP n f₁) (hf₂ : ContMDiff IM IP n f₂) :
    ContMDiff IM IG n fun x ↦ actionDivision horbit (hf x) :=
  ContMDiff.actionDivision ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsmul hsub hsurj hfree horbit
    (injective_mfderiv_orbit_of_lieGroup hn hsmul hfree)
    (fun x ↦ (range_mfderiv_op_smul_one_eq_ker_of_finrank_eq
      ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans hn) hsub (map_op_smul_of_orbit_iff horbit) x
      (injective_mfderiv_orbit_of_lieGroup hn hsmul hfree x)
      (finrank_eq_add_finrank_of_isSubmersion_of_orbit_eq_fiber hn hsmul hsub hfree horbit x)).ge)
    hf hf₁ hf₂

end LieGroupReal

end TauCeti.PrincipalBundle
