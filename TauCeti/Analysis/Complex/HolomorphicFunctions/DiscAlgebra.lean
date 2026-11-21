/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.Algebra
import TauCeti.Analysis.Analytic.ContinuousMap
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.MeasureTheory.Integral.Circle.ContinuousMap

/-!
# The disc algebra

For a centre `c : ℂ` and radius `R : ℝ`, `TauCeti.discAlgebra c R` is the disc algebra
`A(closedBall c R)`: the complex subalgebra of `C(closedBall c R, ℂ)` consisting of continuous
functions on the closed disc `closedBall c R` that are holomorphic on the open disc `ball c R`.
Holomorphy can be tested on any ambient representative agreeing with the function on
`closedBall c R`, and in particular on the extension by zero (`TauCeti.DiscAlgebra.extend`).

With the supremum norm inherited from `C(closedBall c R, ℂ)`, `discAlgebra c R` is closed
(`TauCeti.isClosed_discAlgebra`) and hence a commutative unital Banach algebra.

## Main declarations

* `TauCeti.discAlgebra`: the disc algebra as a `Subalgebra ℂ C(closedBall c R, ℂ)`.
* `TauCeti.isClosed_discAlgebra` and `CompleteSpace (discAlgebra c R)`: closedness and
  completeness in the supremum norm.
* `TauCeti.DiscAlgebra.of`, `TauCeti.DiscAlgebra.extend`: construction from an ambient function
  and canonical extension by zero outside `closedBall c R`.
* `TauCeti.DiscAlgebra.coord`: the coordinate element `z ↦ z`.
* `TauCeti.DiscAlgebra.dslope`: division by `z - a` after subtracting the value at an interior
  point `a ∈ ball c R`, satisfying `(coord c R - a) * dslope ha f + f(a) = f`.
* `TauCeti.DiscAlgebra.mkD`, `TauCeti.DiscAlgebra.analyticAt_mkD_of_analyticAt`: a jointly analytic
  family `F : E × ℂ → ℂ` near `{a} × closedBall c R` (with `E` finite-dimensional over `ℂ`)
  induces an analytic map `E → discAlgebra c R` at `a`.
* `TauCeti.DiscAlgebra.analyticAt_extend_of_analyticAt`: conversely, for any complex normed space
  `E`, an analytic map `W : E → discAlgebra c R` at `a` evaluates to a jointly analytic function
  `(x, z) ↦ extend (W x) z` at every `(a, z₀)` with `z₀ ∈ ball c R`.

## References

* K. Hoffman, *Banach Spaces of Analytic Functions*, Prentice-Hall, 1962, Chapter 6.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, London Mathematical Society Monographs
  **24**, Oxford University Press, 2000, §4.3.
-/

public section

namespace TauCeti

open Complex Filter Metric Set Topology

/-- The disc algebra `A(closedBall c R)` of continuous functions on `closedBall c R` that are
holomorphic on `ball c R`, as a complex subalgebra of `C(closedBall c R, ℂ)` with the supremum
norm. -/
def discAlgebra (c : ℂ) (R : ℝ) : Subalgebra ℂ C(closedBall c R, ℂ) where
  carrier := {f | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ ∀ z : closedBall c R, g z = f z}
  zero_mem' := ⟨0, differentiableOn_const _, fun _ => rfl⟩
  one_mem' := ⟨1, differentiableOn_const _, fun _ => rfl⟩
  add_mem' := by
    rintro f h ⟨g, hg, hgf⟩ ⟨k, hk, hkh⟩
    exact ⟨g + k, hg.add hk, fun z => by simp [hgf, hkh]⟩
  mul_mem' := by
    rintro f h ⟨g, hg, hgf⟩ ⟨k, hk, hkh⟩
    exact ⟨g * k, hg.mul hk, fun z => by simp [hgf, hkh]⟩
  algebraMap_mem' a := ⟨fun _ => a, differentiableOn_const _, fun _ => rfl⟩

/-- Membership in `discAlgebra c R` means having an ambient representative holomorphic on
`ball c R`. -/
theorem mem_discAlgebra_iff {c : ℂ} {R : ℝ} {f : C(closedBall c R, ℂ)} :
    f ∈ discAlgebra c R ↔
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ ∀ z : closedBall c R, g z = f z := Iff.rfl

/-- Holomorphy on `ball c R` can be tested on any ambient function agreeing with `f` on
`closedBall c R`. -/
theorem mem_discAlgebra_iff_of_eqOn {c : ℂ} {R : ℝ} {f : C(closedBall c R, ℂ)} {g : ℂ → ℂ}
    (hgf : ∀ z : closedBall c R, g z = f z) :
    f ∈ discAlgebra c R ↔ DifferentiableOn ℂ g (ball c R) := by
  constructor
  · rintro ⟨k, hk, hkf⟩
    exact hk.congr fun z hz =>
      (hgf ⟨z, ball_subset_closedBall hz⟩).trans (hkf ⟨z, ball_subset_closedBall hz⟩).symm
  · exact fun hg => ⟨g, hg, hgf⟩

/-- Equivalently, the extension by zero outside `closedBall c R` is holomorphic on `ball c R`. -/
theorem mem_discAlgebra_iff_extend {c : ℂ} {R : ℝ} {f : C(closedBall c R, ℂ)} :
    f ∈ discAlgebra c R ↔
      DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ => 0)) (ball c R) :=
  mem_discAlgebra_iff_of_eqOn fun z => Subtype.val_injective.extend_apply f (fun _ => 0) z

/-- The disc algebra is a closed subalgebra of `C(closedBall c R, ℂ)`: a uniform limit of functions
holomorphic on `ball c R` is holomorphic on `ball c R`. -/
theorem isClosed_discAlgebra (c : ℂ) (R : ℝ) :
    IsClosed (discAlgebra c R : Set C(closedBall c R, ℂ)) := by
  refine IsSeqClosed.isClosed fun u u₀ hu hut => ?_
  refine mem_discAlgebra_iff_extend.mpr ?_
  have hunif : TendstoUniformlyOn
      (fun n => Function.extend Subtype.val (u n) (fun _ => 0))
      (Function.extend Subtype.val u₀ (fun _ => 0)) atTop (ball c R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.1 hut ε hε] with n hn z hz
    have hzc : z ∈ closedBall c R := ball_subset_closedBall hz
    rw [Subtype.val_injective.extend_apply (u n) (fun _ => 0) ⟨z, hzc⟩,
      Subtype.val_injective.extend_apply u₀ (fun _ => 0) ⟨z, hzc⟩]
    exact (ContinuousMap.dist_apply_le_dist (f := u₀) (g := u n) ⟨z, hzc⟩).trans_lt
      (by rwa [dist_comm])
  exact hunif.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun n => mem_discAlgebra_iff_extend.mp (hu n)) isOpen_ball

/-- The disc algebra is a Banach algebra with the supremum norm. -/
instance (c : ℂ) (R : ℝ) : CompleteSpace (discAlgebra c R) :=
  (isClosed_discAlgebra c R).completeSpace_coe

namespace DiscAlgebra

variable {c : ℂ} {R : ℝ}

/-- Construct an element of `discAlgebra c R` from an ambient function continuous on
`closedBall c R` and holomorphic on `ball c R`. -/
def of (c : ℂ) (R : ℝ) (g : ℂ → ℂ) (hc : ContinuousOn g (closedBall c R))
    (hd : DifferentiableOn ℂ g (ball c R)) : discAlgebra c R :=
  ⟨⟨fun z => g z, hc.domRestrict⟩, g, hd, fun _ => rfl⟩

/-- Evaluating `of c R g hc hd` at `z : closedBall c R` returns `g z`. -/
@[simp]
theorem of_apply (g : ℂ → ℂ) (hc : ContinuousOn g (closedBall c R))
    (hd : DifferentiableOn ℂ g (ball c R)) (z : closedBall c R) :
    (of c R g hc hd : C(closedBall c R, ℂ)) z = g z := (rfl)

/-- The canonical ambient representative obtained by extending by zero outside `closedBall c R`. -/
noncomputable def extend (f : discAlgebra c R) : ℂ → ℂ :=
  Function.extend Subtype.val (f : C(closedBall c R, ℂ)) (fun _ => 0)

/-- On `closedBall c R`, the zero extension agrees with `f`. -/
@[simp]
theorem extend_apply (f : discAlgebra c R) (z : closedBall c R) :
    extend f z = (f : C(closedBall c R, ℂ)) z :=
  Subtype.val_injective.extend_apply _ _ _

/-- The zero extension vanishes outside `closedBall c R`. -/
@[simp]
theorem extend_apply_of_notMem (f : discAlgebra c R) {z : ℂ} (hz : z ∉ closedBall c R) :
    extend f z = 0 := by
  rw [extend, Function.extend_apply']
  rintro ⟨w, rfl⟩
  exact hz w.property

/-- The zero extension is continuous on `closedBall c R`. -/
theorem continuousOn_extend (f : discAlgebra c R) :
    ContinuousOn (extend f) (closedBall c R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (f : C(closedBall c R, ℂ)).continuous.congr fun z => (extend_apply f z).symm

/-- The zero extension is holomorphic on `ball c R`. -/
theorem differentiableOn_extend (f : discAlgebra c R) :
    DifferentiableOn ℂ (extend f) (ball c R) :=
  mem_discAlgebra_iff_extend.mp f.property

/-- The zero extension is analytic on every subset of `ball c R`. -/
theorem analyticOnNhd_extend {s : Set ℂ} (hs : s ⊆ ball c R) (f : discAlgebra c R) :
    AnalyticOnNhd ℂ (extend f) s :=
  ((differentiableOn_extend f).analyticOnNhd isOpen_ball).mono hs

/-- The zero extension is bounded everywhere by the supremum norm. -/
theorem norm_extend_apply_le (f : discAlgebra c R) (z : ℂ) : ‖extend f z‖ ≤ ‖f‖ := by
  rw [AddSubgroupClass.coe_norm]
  by_cases hz : z ∈ closedBall c R
  · rw [extend_apply f ⟨z, hz⟩]
    exact ContinuousMap.norm_coe_le_norm (f : C(closedBall c R, ℂ)) ⟨z, hz⟩
  · rw [extend_apply_of_notMem f hz, norm_zero]
    exact norm_nonneg _

/-- Recovering an element of the disc algebra from its zero extension does not change it. -/
@[simp]
theorem of_extend (f : discAlgebra c R) :
    of c R (extend f) (continuousOn_extend f) (differentiableOn_extend f) = f := by
  apply Subtype.ext
  ext z
  simp

/-- The coordinate element `z ↦ z` in `discAlgebra c R`. -/
def coord (c : ℂ) (R : ℝ) : discAlgebra c R :=
  of c R id continuousOn_id differentiableOn_id

/-- Evaluating the coordinate element `coord c R` at `z` returns `z`. -/
@[simp]
theorem coord_apply (c : ℂ) (R : ℝ) (z : closedBall c R) :
    (coord c R : C(closedBall c R, ℂ)) z = z := (rfl)

/-- The divided-difference operator `z ↦ (f z - f a) / (z - a)` (with value `f'(a)` at `a`)
at an interior point `a ∈ ball c R`, acting on `discAlgebra c R`. -/
noncomputable def dslope {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R) :
    discAlgebra c R :=
  of c R (_root_.dslope (extend f) a)
    ((continuousOn_dslope (closedBall_mem_nhds_of_mem ha)).2
      ⟨continuousOn_extend f,
        (differentiableOn_extend f).differentiableAt (isOpen_ball.mem_nhds ha)⟩)
    ((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds ha)).2 (differentiableOn_extend f))

/-- Evaluating `dslope ha f` at `z : closedBall c R` returns `_root_.dslope (extend f) a z`. -/
@[simp]
theorem dslope_apply {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R) (z : closedBall c R) :
    (dslope ha f : C(closedBall c R, ℂ)) z = _root_.dslope (extend f) a z := (rfl)

/-- Dividing off the value at an interior point `a ∈ ball c R` recovers `f`:
`(coord c R - a) * dslope ha f + f(a) = f`. -/
theorem coord_sub_algebraMap_mul_dslope_add {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R) :
    (coord c R - algebraMap ℂ (discAlgebra c R) a) * dslope ha f +
      algebraMap ℂ (discAlgebra c R) (extend f a) = f := by
  apply Subtype.ext
  ext z
  have h := sub_smul_dslope (extend f) a z.val
  rw [smul_eq_mul, extend_apply f z] at h
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_sub,
    Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_one,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one,
    coord_apply, dslope_apply]
  linear_combination h

/-- Construct an element of `discAlgebra c R` from an ambient function `g : ℂ → ℂ`, returning a
default element `d` if `g` is not continuous on `closedBall c R` and holomorphic on `ball c R`. -/
noncomputable def mkD (c : ℂ) (R : ℝ) (g : ℂ → ℂ) (d : discAlgebra c R) : discAlgebra c R :=
  open Classical in
  if h : ContinuousOn g (closedBall c R) ∧ DifferentiableOn ℂ g (ball c R) then
    of c R g h.1 h.2
  else d

/-- When `g` is continuous on `closedBall c R` and holomorphic on `ball c R`, `mkD c R g d` agrees
with `of c R g`. -/
theorem mkD_of_continuousOn_differentiableOn {g : ℂ → ℂ} {d : discAlgebra c R}
    (hc : ContinuousOn g (closedBall c R)) (hd : DifferentiableOn ℂ g (ball c R)) :
    mkD c R g d = of c R g hc hd := by
  dsimp only [mkD]
  exact dite_eq_left ⟨hc, hd⟩

/-- When `g` fails to be continuous on `closedBall c R` and holomorphic on `ball c R`,
`mkD c R g d` returns the default value `d`. -/
theorem mkD_of_not {g : ℂ → ℂ} {d : discAlgebra c R}
    (h : ¬(ContinuousOn g (closedBall c R) ∧ DifferentiableOn ℂ g (ball c R))) :
    mkD c R g d = d := by
  dsimp only [mkD]
  exact dite_eq_right h

/-- Evaluation of `mkD c R g d` when `g` is continuous on `closedBall c R` and holomorphic on
`ball c R`. -/
theorem mkD_apply_of_continuousOn_differentiableOn {g : ℂ → ℂ} {d : discAlgebra c R}
    (hc : ContinuousOn g (closedBall c R)) (hd : DifferentiableOn ℂ g (ball c R))
    (z : closedBall c R) :
    (mkD c R g d : C(closedBall c R, ℂ)) z = g z := by
  rw [mkD_of_continuousOn_differentiableOn hc hd, of_apply]

/-- Evaluation of `mkD c R g d` when `g` is analytic on `closedBall c R`. -/
theorem mkD_apply_of_analyticOnNhd {g : ℂ → ℂ} {d : discAlgebra c R}
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (z : closedBall c R) :
    (mkD c R g d : C(closedBall c R, ℂ)) z = g z :=
  mkD_apply_of_continuousOn_differentiableOn hg.continuousOn
    (hg.mono ball_subset_closedBall).differentiableOn z

/-- Applying `mkD` to the zero extension of `f : discAlgebra c R` returns `f`. -/
@[simp]
theorem mkD_extend (f d : discAlgebra c R) : mkD c R (extend f) d = f := by
  rw [mkD_of_continuousOn_differentiableOn (continuousOn_extend f) (differentiableOn_extend f),
    of_extend]

/-- A map into `discAlgebra c R` is complex differentiable at `a` if and only if its coercion to
`C(closedBall c R, ℂ)` is complex differentiable at `a`. -/
theorem differentiableAt_iff_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → discAlgebra c R} {a : E} :
    DifferentiableAt ℂ f a ↔ DifferentiableAt ℂ (fun x => (f x : C(closedBall c R, ℂ))) a := by
  refine ⟨fun hf => ((discAlgebra c R).valA.toContinuousLinearMap.differentiableAt).comp a hf,
    fun hg => ?_⟩
  let S : Submodule ℂ C(closedBall c R, ℂ) := (discAlgebra c R).toSubmodule
  have hfg := hg.hasFDerivAt
  have hmem : ∀ v, fderiv ℂ (fun x => (f x : C(closedBall c R, ℂ))) a v ∈ S :=
    hfg.apply_mem_of_eventually_sub_mem (isClosed_discAlgebra c R)
      (Eventually.of_forall fun y => (discAlgebra c R).sub_mem (f y).property (f a).property)
  let L : E →L[ℂ] S := (fderiv ℂ (fun x => (f x : C(closedBall c R, ℂ))) a).codRestrict S hmem
  exact (HasFDerivAt.of_comp_of_isEmbedding (f := S.subtypeL) (f' := S.subtypeL) (g := f) (g' := L)
    (Topology.IsEmbedding.subtypeVal.continuousAt_iff.2 hg.continuousAt)
    S.subtypeL.hasFDerivAt Topology.IsEmbedding.subtypeVal hfg EventuallyEq.rfl).differentiableAt

/-- A jointly analytic family `F : E × ℂ → ℂ` on `{a} × closedBall c R`, with `E`
finite-dimensional over `ℂ`, induces an analytic map `x ↦ mkD c R (fun z => F (x, z)) d` into
`discAlgebra c R` at `a`. -/
theorem analyticAt_mkD_of_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {F : E × ℂ → ℂ} {a : E} {d : discAlgebra c R}
    (hF : ∀ z ∈ closedBall c R, AnalyticAt ℂ F (a, z)) :
    AnalyticAt ℂ (fun x => mkD c R (fun z => F (x, z)) d) a := by
  let g : E → C(closedBall c R, ℂ) := fun x => ContinuousMap.mkD (fun z => F (x, z.val)) 0
  have hg : AnalyticAt ℂ g a :=
    TauCeti.analyticAt_mkD_of_analyticAt (K := closedBall c R) continuous_subtypeVal
      fun z => hF z.val z.property
  have hnear : ∀ᶠ x in 𝓝 a, ∀ z ∈ closedBall c R, AnalyticAt ℂ F (x, z) :=
    (isCompact_closedBall c R).eventually_forall_of_forall_eventually fun z hz =>
      (hF z hz).eventually_analyticAt
  obtain ⟨U, hU, hopen, haU⟩ := _root_.eventually_nhds_iff.1 (hnear.and hg.eventually_analyticAt)
  have hcoe (x : E) (hx : x ∈ U) :
      (mkD c R (fun z => F (x, z)) d : C(closedBall c R, ℂ)) = g x := by
    have han : AnalyticOnNhd ℂ (fun z => F (x, z)) (closedBall c R) :=
      fun z hz => ((hU x hx).1 z hz).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    ext z
    dsimp only [g]
    rw [mkD_apply_of_analyticOnNhd han,
      ContinuousMap.mkD_apply_of_continuous (f := fun z : closedBall c R => F (x, z.val))
        (han.continuousOn.comp_continuous continuous_subtypeVal fun w => w.property)]
  refine DifferentiableOn.analyticAt_of_finiteDimensional (s := U) (fun x hx => ?_)
    (hopen.mem_nhds haU)
  refine (differentiableAt_iff_coe.2 ?_).differentiableWithinAt
  exact (hU x hx).2.differentiableAt.congr_of_eventuallyEq
    (Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => hcoe y hy)

/-- For any complex normed space `E`, an analytic map `W : E → discAlgebra c R` at `a` evaluates to
a jointly analytic function `(x, z) ↦ extend (W x) z` at every `(a, z₀)` with `z₀ ∈ ball c R`. -/
theorem analyticAt_extend_of_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : E → discAlgebra c R} {a : E} {z₀ : ℂ}
    (hz₀ : z₀ ∈ ball c R) (hW : AnalyticAt ℂ W a) :
    AnalyticAt ℂ (fun q : E × ℂ => extend (W q.1) q.2) (a, z₀) := by
  have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.1 hz₀)
  have hsphere_sub : sphere c |R| ⊆ closedBall c R := by
    rw [abs_of_pos hR]
    exact sphere_subset_closedBall
  let res : discAlgebra c R →L[ℂ] C(sphere c |R|, ℂ) :=
    (ContinuousMap.compCLM ℂ ℂ (ContinuousMap.inclusion hsphere_sub)).comp
      (discAlgebra c R).valA.toContinuousLinearMap
  -- The Cauchy kernel `z ↦ (ζ ↦ ζ - z)⁻¹` as a `C(sphere c |R|, ℂ)`-valued analytic map near `z₀`.
  let ζId : C(sphere c |R|, ℂ) := ContinuousMap.subtypeVal (sphere c |R|)
  let κ : ℂ → C(sphere c |R|, ℂ) := fun z => ζId - z • (1 : C(sphere c |R|, ℂ))
  have hne {z : ℂ} (hz : z ∈ ball c R) (ζ : sphere c |R|) : ζ.val - z ≠ 0 := by
    intro h
    have hdz : dist ζ.val c = dist z c := by rw [sub_eq_zero.1 h]
    rw [mem_sphere.1 ζ.property, abs_of_pos hR] at hdz
    exact (mem_ball.1 hz).ne hdz.symm
  let κUnit (z : ℂ) (hz : z ∈ ball c R) : C(sphere c |R|, ℂ)ˣ :=
    { val := κ z
      inv := ⟨fun ζ => (ζ.val - z)⁻¹,
        (continuous_subtypeVal.sub continuous_const).inv₀ (hne hz)⟩
      val_inv := ContinuousMap.ext fun ζ => by simp [κ, ζId, mul_inv_cancel₀ (hne hz ζ)]
      inv_val := ContinuousMap.ext fun ζ => by simp [κ, ζId, inv_mul_cancel₀ (hne hz ζ)] }
  have hκ : AnalyticAt ℂ κ z₀ :=
    analyticAt_const.sub (analyticAt_id.smul analyticAt_const)
  have hinv_at : AnalyticAt ℂ Ring.inverse (κ z₀) := analyticAt_inverse (𝕜 := ℂ) (κUnit z₀ hz₀)
  have hinv : AnalyticAt ℂ (fun z => Ring.inverse (κ z)) z₀ := hinv_at.comp hκ
  -- Represent `extend (W x) z` on `E × ball c R` via Cauchy's integral formula.
  let Φ : E × ℂ → ℂ := fun q =>
    (2 * Real.pi * I : ℂ)⁻¹ * circleIntegralCLM c R (Ring.inverse (κ q.2) * res (W q.1))
  have hprod : AnalyticAt ℂ (fun q : E × ℂ => Ring.inverse (κ q.2) * res (W q.1)) (a, z₀) :=
    (hinv.comp_of_eq analyticAt_snd rfl).fun_mul
      (((res.analyticAt _).comp hW).comp_of_eq analyticAt_fst rfl)
  have hci : AnalyticAt ℂ
      (fun q : E × ℂ => circleIntegralCLM c R (Ring.inverse (κ q.2) * res (W q.1))) (a, z₀) :=
    ((circleIntegralCLM (E := ℂ) c R).analyticAt _).comp hprod
  have hΦ : AnalyticAt ℂ Φ (a, z₀) := analyticAt_const.fun_mul hci
  refine hΦ.congr ?_
  filter_upwards [prod_mem_nhds univ_mem (isOpen_ball.mem_nhds hz₀)] with q hq
  have hinv_eq : Ring.inverse (κ q.2) = ↑(κUnit q.2 hq.2)⁻¹ :=
    Ring.inverse_unit (κUnit q.2 hq.2)
  have hint : circleIntegralCLM c R (Ring.inverse (κ q.2) * res (W q.1)) =
      ∮ ζ in C(c, R), (ζ - q.2)⁻¹ • extend (W q.1) ζ := by
    refine circleIntegralCLM_eq_circleIntegral c R _ _ fun ζ => ?_
    simp [hinv_eq, κUnit, res, ← extend_apply (W q.1) (ContinuousMap.inclusion hsphere_sub ζ)]
  have hdiff : DiffContOnCl ℂ (extend (W q.1)) (ball c R) :=
    ⟨differentiableOn_extend (W q.1),
      (continuousOn_extend (W q.1)).mono closure_ball_subset_closedBall⟩
  dsimp only [Φ]
  rw [hint, ← smul_eq_mul, hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hq.2]

end DiscAlgebra

end TauCeti
