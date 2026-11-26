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
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Analytic.ContinuousMap
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Logic.Function.Extend
import TauCeti.MeasureTheory.Integral.Circle.ContinuousMap
import TauCeti.Topology.ContinuousOn.Extension

/-!
# The disc algebra

For a centre `c : ℂ` and radius `R : ℝ`, `TauCeti.discAlgebra c R` is the disc algebra
`A(closedBall c R)`: the complex subalgebra of `C(closedBall c R, ℂ)` consisting of continuous
functions on the closed disc `closedBall c R` that are holomorphic on the open disc `ball c R`.
It is defined by pulling back `TauCeti.holomorphicFunctions ⟨ball c R, isOpen_ball⟩` along
restriction to `ball c R`. Holomorphy can be tested on any ambient representative agreeing with
the function on `closedBall c R`, and in particular on the extension by zero
(`TauCeti.DiscAlgebra.extend`).

With the supremum norm inherited from `C(closedBall c R, ℂ)`, `discAlgebra c R` is closed
(`TauCeti.isClosed_discAlgebra`) and hence a commutative unital Banach algebra.

## Main declarations

* `TauCeti.discAlgebra`: the disc algebra as a `Subalgebra ℂ C(closedBall c R, ℂ)`.
* `TauCeti.isClosed_discAlgebra` and `CompleteSpace (discAlgebra c R)`: closedness and
  completeness in the supremum norm.
* `TauCeti.DiscAlgebra.toHolomorphicFunctions`: continuous `ℂ`-algebra homomorphism restricting a
  disc-algebra element to `holomorphicFunctions ⟨ball c R, isOpen_ball⟩`.
* `TauCeti.DiscAlgebra.of`, `TauCeti.DiscAlgebra.extend`: construction from an ambient function
  and canonical extension by zero outside `closedBall c R`.
* `TauCeti.DiscAlgebra.coord`: the coordinate element `z ↦ z`.
* `TauCeti.DiscAlgebra.dslope`: division by `z - a` after subtracting the value at an interior
  point `a ∈ ball c R`, as a bounded `ℂ`-linear endomorphism (`ContinuousLinearMap`) satisfying
  `(coord c R - a) * dslope ha f + f(a) = f`.
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
noncomputable def discAlgebra (c : ℂ) (R : ℝ) : Subalgebra ℂ C(closedBall c R, ℂ) :=
  (holomorphicFunctions ⟨ball c R, isOpen_ball⟩).comap
    (ContinuousMap.compRightAlgHom ℂ ℂ (ContinuousMap.inclusion ball_subset_closedBall))

/-- A continuous function on `closedBall c R` belongs to `discAlgebra c R` if and only if its
restriction to `ball c R` belongs to `holomorphicFunctions ⟨ball c R, isOpen_ball⟩`. -/
theorem mem_discAlgebra_iff_comp_inclusion {c : ℂ} {R : ℝ} {f : C(closedBall c R, ℂ)} :
    f ∈ discAlgebra c R ↔
      f.comp (ContinuousMap.inclusion ball_subset_closedBall) ∈
        holomorphicFunctions ⟨ball c R, isOpen_ball⟩ := by
  rw [discAlgebra, Subalgebra.mem_comap, ContinuousMap.compRightAlgHom_apply]

/-- Holomorphy on `ball c R` can be tested on any ambient function agreeing with `f` on
`closedBall c R`. -/
theorem mem_discAlgebra_iff_of_eqOn {c : ℂ} {R : ℝ} {f : C(closedBall c R, ℂ)} {g : ℂ → ℂ}
    (hgf : ∀ z : closedBall c R, g z = f z) :
    f ∈ discAlgebra c R ↔ DifferentiableOn ℂ g (ball c R) := by
  rw [mem_discAlgebra_iff_comp_inclusion]
  exact mem_holomorphicFunctions_iff_of_eqOn fun z =>
    hgf ⟨z.val, ball_subset_closedBall z.property⟩

/-- Equivalently, the extension by zero outside `closedBall c R` is holomorphic on `ball c R`. -/
theorem mem_discAlgebra_iff_extend {c : ℂ} {R : ℝ} {f : C(closedBall c R, ℂ)} :
    f ∈ discAlgebra c R ↔
      DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ => 0)) (ball c R) :=
  mem_discAlgebra_iff_of_eqOn fun z => Subtype.val_injective.extend_apply f (fun _ => 0) z

/-- Membership in `discAlgebra c R` means having an ambient representative holomorphic on
`ball c R`. -/
theorem mem_discAlgebra_iff {c : ℂ} {R : ℝ} {f : C(closedBall c R, ℂ)} :
    f ∈ discAlgebra c R ↔
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ ∀ z : closedBall c R, g z = f z :=
  ⟨fun h => ⟨_, mem_discAlgebra_iff_extend.mp h,
      fun z => Subtype.val_injective.extend_apply f (fun _ => 0) z⟩,
    fun ⟨_, hg, hgf⟩ => (mem_discAlgebra_iff_of_eqOn hgf).mpr hg⟩

/-- The disc algebra is a closed subalgebra of `C(closedBall c R, ℂ)`: it is the preimage of the
closed subalgebra of holomorphic functions on `ball c R` under continuous restriction. -/
theorem isClosed_discAlgebra (c : ℂ) (R : ℝ) :
    IsClosed (discAlgebra c R : Set C(closedBall c R, ℂ)) :=
  (isClosed_holomorphicFunctions ⟨ball c R, isOpen_ball⟩).preimage
    (ContinuousMap.compRightAlgHom_continuous ℂ ℂ
      (ContinuousMap.inclusion ball_subset_closedBall))

/-- The disc algebra is a Banach algebra with the supremum norm. -/
instance (c : ℂ) (R : ℝ) : CompleteSpace (discAlgebra c R) :=
  (isClosed_discAlgebra c R).completeSpace_coe

namespace DiscAlgebra

variable {c : ℂ} {R : ℝ}

/-- Construct an element of `discAlgebra c R` from an ambient function continuous on
`closedBall c R` and holomorphic on `ball c R`. -/
def of (c : ℂ) (R : ℝ) (g : ℂ → ℂ) (hc : ContinuousOn g (closedBall c R))
    (hd : DifferentiableOn ℂ g (ball c R)) : discAlgebra c R :=
  ⟨⟨fun z => g z, hc.domRestrict⟩,
    (mem_discAlgebra_iff_of_eqOn (f := ⟨fun z => g z, hc.domRestrict⟩) fun _ => rfl).2 hd⟩

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

/-- Two elements of `discAlgebra c R` are equal if their zero extensions agree on
`closedBall c R`. -/
@[ext]
theorem ext {f g : discAlgebra c R} (h : ∀ z ∈ closedBall c R, extend f z = extend g z) :
    f = g := by
  apply Subtype.ext
  ext z
  rw [← extend_apply f z, ← extend_apply g z]
  exact h z.val z.property

/-- Restriction of a disc-algebra element to the open disc `ball c R`, as a continuous
`ℂ`-algebra homomorphism into `holomorphicFunctions ⟨ball c R, isOpen_ball⟩`. -/
noncomputable def toHolomorphicFunctions (c : ℂ) (R : ℝ) :
    discAlgebra c R →A[ℂ] holomorphicFunctions ⟨ball c R, isOpen_ball⟩ :=
  (({ toAlgHom :=
        ContinuousMap.compRightAlgHom ℂ ℂ (ContinuousMap.inclusion ball_subset_closedBall),
      cont :=
        ContinuousMap.compRightAlgHom_continuous ℂ ℂ
          (ContinuousMap.inclusion ball_subset_closedBall) } :
      C(closedBall c R, ℂ) →A[ℂ] C(ball c R, ℂ)).comp
    (discAlgebra c R).valA).codRestrict (holomorphicFunctions ⟨ball c R, isOpen_ball⟩)
    fun f => mem_discAlgebra_iff_comp_inclusion.mp f.property

/-- Evaluating the restriction of `f : discAlgebra c R` to `ball c R` at `z` returns `f z`. -/
@[simp]
theorem toHolomorphicFunctions_apply (f : discAlgebra c R) (z : ball c R) :
    (toHolomorphicFunctions c R f).val z =
      (f : C(closedBall c R, ℂ)) ⟨z.val, ball_subset_closedBall z.property⟩ :=
  (rfl)

/-- Extending the restriction of `f : discAlgebra c R` to `ball c R` agrees with `extend f` on
`ball c R`. -/
@[simp]
theorem extend_toHolomorphicFunctions (f : discAlgebra c R) {z : ℂ} (hz : z ∈ ball c R) :
    HolomorphicFunctions.extend (toHolomorphicFunctions c R f) z = extend f z := by
  rw [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩, toHolomorphicFunctions_apply,
    extend_apply f ⟨z, ball_subset_closedBall hz⟩]

/-- On `closedBall c R`, the zero extension of `of c R g hc hd` agrees with `g`. -/
@[simp]
theorem extend_of (g : ℂ → ℂ) (hc : ContinuousOn g (closedBall c R))
    (hd : DifferentiableOn ℂ g (ball c R)) {z : ℂ} (hz : z ∈ closedBall c R) :
    extend (of c R g hc hd) z = g z :=
  extend_apply (of c R g hc hd) ⟨z, hz⟩

/-- The zero extension vanishes outside `closedBall c R`. -/
@[simp]
theorem extend_apply_of_notMem (f : discAlgebra c R) {z : ℂ} (hz : z ∉ closedBall c R) :
    extend f z = 0 :=
  Function.extend_subtypeVal_eq _ _ fun hz' => (hz hz').elim

/-- Zero extension sends `0` to `0`. -/
@[simp]
theorem extend_zero : extend (0 : discAlgebra c R) = 0 := by
  simp [extend, ← Pi.zero_def]

/-- Zero extension commutes with addition. -/
@[simp]
theorem extend_add (f g : discAlgebra c R) : extend (f + g) = extend f + extend g := by
  simpa [extend, ← Pi.zero_def] using
    Function.extend_add Subtype.val (f : C(closedBall c R, ℂ)) g 0 0

/-- Zero extension commutes with negation. -/
@[simp]
theorem extend_neg (f : discAlgebra c R) : extend (-f) = -extend f := by
  simpa [extend, ← Pi.zero_def] using
    Function.extend_neg Subtype.val (f : C(closedBall c R, ℂ)) 0

/-- Zero extension commutes with subtraction. -/
@[simp]
theorem extend_sub (f g : discAlgebra c R) : extend (f - g) = extend f - extend g := by
  simpa [extend, ← Pi.zero_def] using
    Function.extend_sub Subtype.val (f : C(closedBall c R, ℂ)) g 0 0

/-- Zero extension commutes with complex scalar multiplication. -/
@[simp]
theorem extend_smul (a : ℂ) (f : discAlgebra c R) : extend (a • f) = a • extend f := by
  simpa [extend, ← Pi.zero_def] using
    Function.extend_smul a Subtype.val (f : C(closedBall c R, ℂ)) 0

/-- Zero extension commutes with multiplication. -/
@[simp]
theorem extend_mul (f g : discAlgebra c R) : extend (f * g) = extend f * extend g := by
  simpa [extend, ← Pi.zero_def] using
    Function.extend_mul Subtype.val (f : C(closedBall c R, ℂ)) g 0 0

/-- On `closedBall c R`, the zero extension commutes with powers. -/
@[simp]
theorem extend_pow (f : discAlgebra c R) (n : ℕ) {z : ℂ} (hz : z ∈ closedBall c R) :
    extend (f ^ n) z = extend f z ^ n := by
  rw [extend_apply _ ⟨z, hz⟩, extend_apply f ⟨z, hz⟩, Subalgebra.coe_pow, ContinuousMap.pow_apply]

/-- On `closedBall c R`, the zero extension of `1` is `1`. -/
@[simp]
theorem extend_one {z : ℂ} (hz : z ∈ closedBall c R) :
    extend (1 : discAlgebra c R) z = 1 := by
  rw [extend_apply _ ⟨z, hz⟩, Subalgebra.coe_one, ContinuousMap.one_apply]

/-- On `closedBall c R`, the zero extension of `algebraMap ℂ (discAlgebra c R) a` is `a`. -/
@[simp]
theorem extend_algebraMap (a : ℂ) {z : ℂ} (hz : z ∈ closedBall c R) :
    extend (algebraMap ℂ (discAlgebra c R) a) z = a := by
  rw [Algebra.algebraMap_eq_smul_one, extend_smul, Pi.smul_apply, extend_one hz, smul_eq_mul,
    mul_one]

/-- The zero extension is continuous on `closedBall c R`. -/
theorem continuousOn_extend (f : discAlgebra c R) :
    ContinuousOn (extend f) (closedBall c R) :=
  (f : C(closedBall c R, ℂ)).continuous.continuousOn_extend_subtypeVal _

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

/-- On `closedBall c R`, the zero extension of `coord c R` is the identity. -/
@[simp]
theorem extend_coord {z : ℂ} (hz : z ∈ closedBall c R) :
    extend (coord c R) z = z :=
  extend_of id continuousOn_id differentiableOn_id hz

/-- Divided-difference element `_root_.dslope (extend f) a` in `discAlgebra c R`. -/
private noncomputable def dslopeFun {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R) :
    discAlgebra c R :=
  of c R (_root_.dslope (extend f) a)
    ((continuousOn_dslope (closedBall_mem_nhds_of_mem ha)).2
      ⟨continuousOn_extend f,
        (differentiableOn_extend f).differentiableAt (isOpen_ball.mem_nhds ha)⟩)
    ((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds ha)).2 (differentiableOn_extend f))

private theorem dslopeFun_apply {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R)
    (z : closedBall c R) :
    (dslopeFun ha f : C(closedBall c R, ℂ)) z = _root_.dslope (extend f) a z := (rfl)

private theorem coord_sub_algebraMap_mul_dslopeFun_add {a : ℂ} (ha : a ∈ ball c R)
    (f : discAlgebra c R) :
    (coord c R - algebraMap ℂ (discAlgebra c R) a) * dslopeFun ha f +
      algebraMap ℂ (discAlgebra c R) (extend f a) = f := by
  apply Subtype.ext
  ext z
  have h := sub_smul_dslope (extend f) a z.val
  rw [smul_eq_mul, extend_apply f z] at h
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_sub,
    Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_one,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one,
    coord_apply, dslopeFun_apply]
  linear_combination h

private theorem eq_dslopeFun_and_eq_of_coord_sub_algebraMap_mul_add {a : ℂ} (ha : a ∈ ball c R)
    {f q : discAlgebra c R} {c₀ : ℂ}
    (h : (coord c R - algebraMap ℂ (discAlgebra c R) a) * q +
      algebraMap ℂ (discAlgebra c R) c₀ = f) :
    q = dslopeFun ha f ∧ c₀ = extend f a := by
  have heval (z : closedBall c R) :
      (z.val - a) * (q : C(closedBall c R, ℂ)) z + c₀ = (f : C(closedBall c R, ℂ)) z := by
    have hz := congrArg (fun g : discAlgebra c R => (g : C(closedBall c R, ℂ)) z) h
    simpa [Algebra.algebraMap_eq_smul_one, mul_one] using hz
  have hc₀ : c₀ = extend f a := by
    have h0 := heval ⟨a, ball_subset_closedBall ha⟩
    simpa [extend_apply f ⟨a, ball_subset_closedBall ha⟩] using h0
  have hne : ∀ z : closedBall c R, z.val ≠ a →
      (q : C(closedBall c R, ℂ)) z = (dslopeFun ha f : C(closedBall c R, ℂ)) z := by
    intro z hza
    rw [dslopeFun_apply, dslope_of_ne _ hza, slope_def_module, smul_eq_mul, extend_apply f z]
    have hz := heval z
    rw [hc₀] at hz
    rw [eq_inv_mul_iff_mul_eq₀ (sub_ne_zero.2 hza)]
    linear_combination hz
  have hev : extend q =ᶠ[𝓝[≠] a] extend (dslopeFun ha f) := by
    filter_upwards [inter_mem_nhdsWithin _ (closedBall_mem_nhds_of_mem ha)] with w ⟨hw_ne, hw_cb⟩
    rw [extend_apply q ⟨w, hw_cb⟩, extend_apply (dslopeFun ha f) ⟨w, hw_cb⟩]
    exact hne ⟨w, hw_cb⟩ hw_ne
  have hqc : ContinuousAt (extend q) a :=
    (continuousOn_extend q).continuousAt (closedBall_mem_nhds_of_mem ha)
  have hfc : ContinuousAt (extend (dslopeFun ha f)) a :=
    (continuousOn_extend (dslopeFun ha f)).continuousAt (closedBall_mem_nhds_of_mem ha)
  have ha_eq : extend q a = extend (dslopeFun ha f) a :=
    (((hqc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hfc).1 hev)).self_of_nhds
  refine ⟨?_, hc₀⟩
  apply Subtype.ext
  ext z
  by_cases hza : z.val = a
  · have hz_eq : z = ⟨a, ball_subset_closedBall ha⟩ := Subtype.ext hza
    subst hz_eq
    rw [← extend_apply q ⟨a, ball_subset_closedBall ha⟩,
      ← extend_apply (dslopeFun ha f) ⟨a, ball_subset_closedBall ha⟩, ha_eq]
  · exact hne z hza

/-- Underlying linear map for `DiscAlgebra.dslope`. -/
private noncomputable def dslopeLinear {a : ℂ} (ha : a ∈ ball c R) :
    discAlgebra c R →ₗ[ℂ] discAlgebra c R where
  toFun := dslopeFun ha
  map_add' f g := by
    refine (eq_dslopeFun_and_eq_of_coord_sub_algebraMap_mul_add ha
      (f := f + g) (c₀ := extend (f + g) a) ?_).1.symm
    rw [extend_add, Pi.add_apply, map_add]
    linear_combination coord_sub_algebraMap_mul_dslopeFun_add ha f +
      coord_sub_algebraMap_mul_dslopeFun_add ha g
  map_smul' k f := by
    refine (eq_dslopeFun_and_eq_of_coord_sub_algebraMap_mul_add ha
      (f := k • f) (c₀ := extend (k • f) a) ?_).1.symm
    rw [extend_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    simp only [RingHom.id_apply, Algebra.smul_def]
    linear_combination
      algebraMap ℂ (discAlgebra c R) k * coord_sub_algebraMap_mul_dslopeFun_add ha f

private theorem dslopeLinear_apply {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R)
    (z : closedBall c R) :
    (dslopeLinear ha f : C(closedBall c R, ℂ)) z = _root_.dslope (extend f) a z := (rfl)

/-- The divided-difference operator `f ↦ (z ↦ (f z - f a) / (z - a))` (with value `f'(a)` at
`a`) at an interior point `a ∈ ball c R`, as a bounded `ℂ`-linear endomorphism of
`discAlgebra c R`. -/
noncomputable def dslope {a : ℂ} (ha : a ∈ ball c R) :
    discAlgebra c R →L[ℂ] discAlgebra c R :=
  ContinuousLinearMap.ofIsClosedGraph (g := dslopeLinear ha) <| by
    have hgraph : ((dslopeLinear ha).graph : Set (discAlgebra c R × discAlgebra c R)) =
        {p : discAlgebra c R × discAlgebra c R |
          (coord c R - algebraMap ℂ (discAlgebra c R) a) * p.2 +
            algebraMap ℂ (discAlgebra c R)
              ((p.1 : C(closedBall c R, ℂ)) ⟨a, ball_subset_closedBall ha⟩) = p.1} := by
      ext ⟨f, q⟩
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_ofPred_eq,
        ← extend_apply f ⟨a, ball_subset_closedBall ha⟩]
      exact ⟨fun h => h ▸ coord_sub_algebraMap_mul_dslopeFun_add ha f,
        fun h => (eq_dslopeFun_and_eq_of_coord_sub_algebraMap_mul_add ha h).1⟩
    rw [hgraph]
    refine isClosed_eq ?_ continuous_fst
    exact (continuous_const.mul continuous_snd).add
      ((algebraMapCLM ℂ (discAlgebra c R)).continuous.comp
        ((continuous_eval_const (⟨a, ball_subset_closedBall ha⟩ : closedBall c R)).comp
          (continuous_subtypeVal.comp continuous_fst)))

private theorem dslope_eq_dslopeLinear {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R) :
    dslope ha f = dslopeLinear ha f :=
  congrFun (ContinuousLinearMap.coeFn_ofIsClosedGraph _) f

/-- Evaluating `dslope ha f` at `z : closedBall c R` returns `_root_.dslope (extend f) a z`. -/
@[simp]
theorem dslope_apply {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R) (z : closedBall c R) :
    (dslope ha f : C(closedBall c R, ℂ)) z = _root_.dslope (extend f) a z := by
  rw [dslope_eq_dslopeLinear, dslopeLinear_apply]

/-- On `closedBall c R`, the zero extension of `dslope ha f` agrees with
`_root_.dslope (extend f) a`. -/
@[simp]
theorem extend_dslope {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R) {z : ℂ}
    (hz : z ∈ closedBall c R) :
    extend (dslope ha f) z = _root_.dslope (extend f) a z := by
  rw [extend_apply _ ⟨z, hz⟩, dslope_apply]

/-- Dividing off the value at an interior point `a ∈ ball c R` recovers `f`:
`(coord c R - a) * dslope ha f + f(a) = f`. -/
@[simp]
theorem coord_sub_algebraMap_mul_dslope_add {a : ℂ} (ha : a ∈ ball c R) (f : discAlgebra c R) :
    (coord c R - algebraMap ℂ (discAlgebra c R) a) * dslope ha f +
      algebraMap ℂ (discAlgebra c R) (extend f a) = f := by
  rw [dslope_eq_dslopeLinear]
  exact coord_sub_algebraMap_mul_dslopeFun_add ha f

/-- Division with remainder by `coord c R - a` in `discAlgebra c R`:
`(coord c R - a) * q + c₀ = f` holds if and only if `q = dslope ha f` and `c₀ = extend f a`. -/
theorem coord_sub_algebraMap_mul_add_eq_iff {a : ℂ} (ha : a ∈ ball c R)
    {f q : discAlgebra c R} {c₀ : ℂ} :
    (coord c R - algebraMap ℂ (discAlgebra c R) a) * q +
        algebraMap ℂ (discAlgebra c R) c₀ = f ↔
      q = dslope ha f ∧ c₀ = extend f a := by
  rw [dslope_eq_dslopeLinear]
  exact ⟨eq_dslopeFun_and_eq_of_coord_sub_algebraMap_mul_add ha, by
    rintro ⟨rfl, rfl⟩
    exact coord_sub_algebraMap_mul_dslopeFun_add ha f⟩

/-- Construct an element of `discAlgebra c R` from an ambient function `g : ℂ → ℂ`, returning a
default element `d` if `g` is not continuous on `closedBall c R` and holomorphic on `ball c R`. -/
noncomputable def mkD (c : ℂ) (R : ℝ) (g : ℂ → ℂ) (d : discAlgebra c R) : discAlgebra c R :=
  open Classical in
  if h : ContinuousOn g (closedBall c R) ∧ DifferentiableOn ℂ g (ball c R) then
    of c R g h.1 h.2
  else d

/-- When `g` is continuous on `closedBall c R` and holomorphic on `ball c R`, `mkD c R g d` agrees
with `of c R g`. -/
@[simp]
theorem mkD_of_continuousOn_differentiableOn {g : ℂ → ℂ} {d : discAlgebra c R}
    (hc : ContinuousOn g (closedBall c R)) (hd : DifferentiableOn ℂ g (ball c R)) :
    mkD c R g d = of c R g hc hd := by
  dsimp only [mkD]
  exact dite_eq_left ⟨hc, hd⟩

/-- When `g` fails to be continuous on `closedBall c R` and holomorphic on `ball c R`,
`mkD c R g d` returns the default value `d`. -/
@[simp]
theorem mkD_of_not_continuousOn_and_differentiableOn {g : ℂ → ℂ} {d : discAlgebra c R}
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
      fun z hz => ((hU x hx).1 z hz).curry_right
    ext z
    dsimp only [g]
    rw [mkD_apply_of_analyticOnNhd han,
      ContinuousMap.mkD_apply_of_continuous (f := fun z : closedBall c R => F (x, z.val))
        (han.continuousOn.comp_continuous continuous_subtypeVal fun w => w.property)]
  refine DifferentiableOn.analyticAt_of_finiteDimensional (s := U) (fun x hx => ?_)
    (hopen.mem_nhds haU)
  refine ((isClosed_discAlgebra c R).differentiableAt_submodule_iff
    (S := (discAlgebra c R).toSubmodule).2 ?_).differentiableWithinAt
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
  -- The Cauchy kernel `z ↦ (ζ ↦ (ζ - z)⁻¹)` as a `C(sphere c |R|, ℂ)`-valued analytic map near
  -- `z₀`.
  let ker : ℂ → C(sphere c |R|, ℂ) :=
    fun z => ContinuousMap.mkD (fun ζ : sphere c |R| => (ζ.val - z)⁻¹) 0
  have hne {z : ℂ} (hz : z ∈ ball c R) (ζ : sphere c |R|) : ζ.val - z ≠ 0 := by
    refine sub_ne_zero.2 fun h => (mem_ball.1 hz).ne ?_
    rw [← h, mem_sphere.1 ζ.property, abs_of_pos hR]
  have hker : AnalyticAt ℂ ker z₀ :=
    TauCeti.analyticAt_mkD_of_analyticAt continuous_subtypeVal fun ζ =>
      (analyticAt_snd.sub analyticAt_fst).inv (hne hz₀ ζ)
  -- Represent `extend (W x) z` on `E × ball c R` via Cauchy's integral formula.
  let Φ : E × ℂ → ℂ := fun q =>
    (2 * Real.pi * I : ℂ)⁻¹ * circleIntegralCLM c R (ker q.2 * res (W q.1))
  have hprod : AnalyticAt ℂ (fun q : E × ℂ => ker q.2 * res (W q.1)) (a, z₀) :=
    (hker.comp_of_eq analyticAt_snd rfl).fun_mul
      (((res.analyticAt _).comp hW).comp_of_eq analyticAt_fst rfl)
  have hci : AnalyticAt ℂ
      (fun q : E × ℂ => circleIntegralCLM c R (ker q.2 * res (W q.1))) (a, z₀) :=
    ((circleIntegralCLM (E := ℂ) c R).analyticAt _).comp hprod
  have hΦ : AnalyticAt ℂ Φ (a, z₀) := analyticAt_const.fun_mul hci
  refine hΦ.congr ?_
  filter_upwards [prod_mem_nhds univ_mem (isOpen_ball.mem_nhds hz₀)] with q hq
  have hcont : Continuous fun ζ : sphere c |R| => (ζ.val - q.2)⁻¹ :=
    continuous_iff_continuousAt.2 fun ζ =>
      ((continuous_subtypeVal.sub continuous_const).continuousAt).inv₀ (hne hq.2 ζ)
  have hint : circleIntegralCLM c R (ker q.2 * res (W q.1)) =
      ∮ ζ in C(c, R), (ζ - q.2)⁻¹ • extend (W q.1) ζ := by
    refine circleIntegralCLM_eq_circleIntegral c R _ _ fun ζ => ?_
    simp [ker, ContinuousMap.mkD_apply_of_continuous hcont, res,
      ← extend_apply (W q.1) (ContinuousMap.inclusion hsphere_sub ζ)]
  have hdiff : DiffContOnCl ℂ (extend (W q.1)) (ball c R) :=
    ⟨differentiableOn_extend (W q.1),
      (continuousOn_extend (W q.1)).mono closure_ball_subset_closedBall⟩
  dsimp only [Φ]
  rw [hint, ← smul_eq_mul, hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hq.2]

end DiscAlgebra

end TauCeti
