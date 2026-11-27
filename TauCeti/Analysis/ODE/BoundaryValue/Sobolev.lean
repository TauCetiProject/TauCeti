/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.BoundaryValue
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.ODE.Regularity
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Sobolev realization of a linear boundary value problem on `[0, 1]`

Let `X` be a real Banach space, `F₀` and `F₁` two finite-dimensional subspaces of `X`, and
`S : ℝ → (X →L[ℝ] X)` a continuous path of operators. This file realizes the boundary value
problem

`w' - S w = f`, `w 0 ∈ F₀`, `w 1 ∈ F₁`

as a bounded operator from a Sobolev space of paths to `L²(0, 1)`, and proves that this operator
is an isomorphism exactly when the homogeneous problem has only the zero solution, that is, when
`Ψ(1) F₀ ∩ F₁ = 0` for the propagator `Ψ = TauCeti.dysonSeriesLeft S` of `w' = S w`, provided the
dimensions of `F₀` and `F₁` add up to that of a finite-dimensional `X`.

For a Hamiltonian chord from a Lagrangian `L₀` to a Lagrangian `L₁`, with `S_t` the linearized
Hamiltonian vector field along the chord and `F₀`, `F₁` the tangent spaces of the Lagrangians at
its ends, the condition `Ψ(1) F₀ ∩ F₁ = 0` is the nondegeneracy of the chord, and
`J (w' - S w)` is the asymptotic operator `TauCeti.Floer.asymptoticOperator` of the stationary
Floer strip over the chord. The linearized Floer operator on a strip between two Lagrangians is
`∂ₛ + A(s)` for a path of such operators acting on paths in `t ∈ [0, 1]`, and its Fredholm theory
over a common domain (`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`) asks for
invertible limits `A(±∞)` on that domain. This file constructs the domain of paths with boundary
values in `F₀` and `F₁`, and shows that at a nondegenerate chord the operator `w' - S w` is
invertible on it. The realization of `J` as a bounded operator on `L²`, the compactness of the
embedding of this domain into `L²`, and the symmetry of `J (w' - S w)` for Lagrangian `F₀` and
`F₁`, which that Fredholm theory also asks for, are not treated here.

* **The space.** `TauCeti.PathSobolev.H1 F₀ F₁` is the closure, in `L²((0, 1], X × X)`, of the
  jets `t ↦ (w t, w' t)` of the `C¹` paths `w` with `w 0 ∈ F₀` and `w 1 ∈ F₁`
  (`TauCeti.PathSobolev.boundaryPath`). It is the completion of these paths in a norm equivalent to
  the `W^{1,2}` norm, and its elements are `L²` pairs `(w, w')`, with projections
  `TauCeti.PathSobolev.valueL` and `TauCeti.PathSobolev.derivL`. The second component is the weak
  derivative of the first on `(0, 1)` (`TauCeti.PathSobolev.hasWeakLineDerivOn_derivL`), so an
  element is determined by its value (`TauCeti.PathSobolev.valueL_injective`), and `H1` is a space
  of paths. The construction follows that of
  `TauCeti.StripSobolev.H1` (`TauCeti.Analysis.Sobolev.Strip.Basic`), here for paths on `[0, 1]`
  instead of functions on the strip.
* **The operator.** For an essentially bounded coefficient `A`, given as a class in
  `L^∞((0, 1], X →L[ℝ] X)`, `TauCeti.PathSobolev.boundaryValueOperator A` sends `(w, w')` to
  `w' - A w`.
* **The estimate.** When `A` is a continuous path `S` and `Ψ(1) F₀ ∩ F₁ = 0`, the `L²` estimate
  `TauCeti.exists_forall_integral_norm_sq_le_mul_integral_norm_sq_of_disjoint` for classical
  solutions passes to the completion, so the operator is bounded below
  (`TauCeti.PathSobolev.exists_forall_norm_le_mul_norm_boundaryValueOperator`): it is injective
  with closed range.
* **Surjectivity.** When moreover `dim F₀ + dim F₁ = dim X`, the classical problem is solvable
  for every continuous right side by variation of constants
  (`TauCeti.exists_hasDerivAt_and_mem_of_disjoint`), and continuous functions are dense in `L²`.
  So the range is dense and closed, and the operator is invertible
  (`TauCeti.PathSobolev.isInvertible_boundaryValueOperator`). Conversely a nonzero classical
  solution of the homogeneous problem is a nonzero element of the kernel
  (`TauCeti.PathSobolev.disjoint_map_dysonSeriesLeft_of_injective`).

## Main definitions

* `TauCeti.PathSobolev.boundaryPath F₀ F₁`: the `C¹` paths with boundary values in `F₀` and `F₁`.
* `TauCeti.PathSobolev.H1 F₀ F₁`: their completion in the `W^{1,2}` norm on `(0, 1)`, as the
  closure of their `L²` jets.
* `TauCeti.PathSobolev.valueL`, `TauCeti.PathSobolev.derivL`: the two components.
* `TauCeti.PathSobolev.boundaryValueOperator`: the operator `(w, w') ↦ w' - A w`.

## Main results

* `TauCeti.PathSobolev.hasWeakLineDerivOn_derivL`: `w'` is the weak derivative of `w` on `(0, 1)`.
* `TauCeti.PathSobolev.valueL_injective`: an element of `H1` is determined by its value.
* `TauCeti.PathSobolev.exists_forall_norm_le_mul_norm_boundaryValueOperator`: the operator is
  bounded below when `Ψ(1) F₀ ∩ F₁ = 0`.
* `TauCeti.PathSobolev.disjoint_map_dysonSeriesLeft_of_injective`: if it is injective, then
  `Ψ(1) F₀ ∩ F₁ = 0`.
* `TauCeti.PathSobolev.isInvertible_boundaryValueOperator_iff`: it is invertible exactly when
  `Ψ(1) F₀ ∩ F₁ = 0`, if `dim F₀ + dim F₁ = dim X`.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547 (the linearized operator on strips with Lagrangian boundary conditions).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33 (the operators `J (d/dt) + S(t)` with Lagrangian boundary conditions).
-/

public section

noncomputable section

open Function MeasureTheory Set Filter Topology
open scoped ENNReal Distributions

namespace TauCeti

namespace PathSobolev

local notation "μ₁" => (volume.restrict (Ioc (0 : ℝ) 1))

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Classical paths with boundary values in two subspaces -/

/-- The `C¹` paths `w : ℝ → X` with boundary values `w 0 ∈ F₀` and `w 1 ∈ F₁`. Only their
restrictions to `[0, 1]` enter `TauCeti.PathSobolev.H1`. -/
def boundaryPath (F₀ F₁ : Submodule ℝ X) : Submodule ℝ (ℝ → X) where
  carrier := {w | ContDiff ℝ 1 w ∧ w 0 ∈ F₀ ∧ w 1 ∈ F₁}
  zero_mem' := ⟨contDiff_const, F₀.zero_mem, F₁.zero_mem⟩
  add_mem' := fun ⟨hw, hw₀, hw₁⟩ ⟨hv, hv₀, hv₁⟩ ↦
    ⟨hw.add hv, F₀.add_mem hw₀ hv₀, F₁.add_mem hw₁ hv₁⟩
  smul_mem' := fun c _ ⟨hw, hw₀, hw₁⟩ ↦
    ⟨contDiff_const.smul hw, F₀.smul_mem c hw₀, F₁.smul_mem c hw₁⟩

variable {F₀ F₁ : Submodule ℝ X} {w : ℝ → X}

/-- Membership in the paths with boundary values in `F₀` and `F₁`. -/
@[simp]
theorem mem_boundaryPath_iff : w ∈ boundaryPath F₀ F₁ ↔ ContDiff ℝ 1 w ∧ w 0 ∈ F₀ ∧ w 1 ∈ F₁ :=
  Iff.rfl

/-- A path with boundary values in `F₀` and `F₁` is `C¹`. -/
theorem contDiff_coe (w : boundaryPath F₀ F₁) : ContDiff ℝ 1 (w : ℝ → X) :=
  (mem_boundaryPath_iff.1 w.property).left

/-- The initial value of a path of `boundaryPath F₀ F₁` lies in `F₀`. -/
theorem coe_zero_mem (w : boundaryPath F₀ F₁) : (w : ℝ → X) 0 ∈ F₀ :=
  (mem_boundaryPath_iff.1 w.property).right.left

/-- The final value of a path of `boundaryPath F₀ F₁` lies in `F₁`. -/
theorem coe_one_mem (w : boundaryPath F₀ F₁) : (w : ℝ → X) 1 ∈ F₁ :=
  (mem_boundaryPath_iff.1 w.property).right.right

/-- The jet `t ↦ (w t, w' t)` of a path. -/
def pathJet (w : ℝ → X) (t : ℝ) : X × X :=
  (w t, deriv w t)

@[simp]
theorem pathJet_apply (w : ℝ → X) (t : ℝ) : pathJet w t = (w t, deriv w t) :=
  (rfl)

/-- A path with boundary values in `F₀` and `F₁` is square integrable on `(0, 1]`. -/
theorem memLp_coe (w : boundaryPath F₀ F₁) : MemLp (w : ℝ → X) 2 μ₁ :=
  (contDiff_coe w).continuous.memLp_restrict_Ioc 2

/-- The derivative of a path with boundary values in `F₀` and `F₁` is square integrable on
`(0, 1]`. -/
theorem memLp_deriv (w : boundaryPath F₀ F₁) : MemLp (deriv (w : ℝ → X)) 2 μ₁ :=
  ((contDiff_coe w).continuous_deriv le_rfl).memLp_restrict_Ioc 2

/-- The residual `t ↦ w' t - S t (w t)` of a path with boundary values in `F₀` and `F₁` is
continuous, for a continuous path of operators `S`. -/
theorem continuous_deriv_sub {S : ℝ → X →L[ℝ] X} (hS : Continuous S) (w : boundaryPath F₀ F₁) :
    Continuous fun t ↦ deriv (w : ℝ → X) t - S t ((w : ℝ → X) t) :=
  ((contDiff_coe w).continuous_deriv le_rfl).sub (hS.clm_apply (contDiff_coe w).continuous)

/-- The jet of a path with boundary values in `F₀` and `F₁` is square integrable on `(0, 1]`. -/
theorem memLp_pathJet (w : boundaryPath F₀ F₁) : MemLp (pathJet (w : ℝ → X)) 2 μ₁ :=
  ((contDiff_coe w).continuous.prodMk
    ((contDiff_coe w).continuous_deriv le_rfl)).memLp_restrict_Ioc 2

variable (F₀ F₁) in
/-- The `L²` jets `(w, w')` of the paths with boundary values in `F₀` and `F₁`. -/
def jetLp : boundaryPath F₀ F₁ →ₗ[ℝ] Lp (X × X) 2 μ₁ where
  toFun w := (memLp_pathJet w).toLp _
  map_add' w v := by
    simp only [Submodule.coe_add, ← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun t ↦ ?_)
    simp [deriv_add ((contDiff_coe w).differentiable one_ne_zero t)
      ((contDiff_coe v).differentiable one_ne_zero t)]
  map_smul' c w := by
    simp only [SetLike.val_smul, RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun t ↦ ?_)
    have h : deriv (c • (w : ℝ → X)) t = c • deriv (w : ℝ → X) t :=
      deriv_const_smul (f := (w : ℝ → X)) c ((contDiff_coe w).differentiable one_ne_zero t)
    simp [h]

/-- The `L²` jet of a path is the class of `t ↦ (w t, w' t)`. -/
theorem jetLp_apply (w : boundaryPath F₀ F₁) :
    jetLp F₀ F₁ w = (memLp_pathJet w).toLp (pathJet (w : ℝ → X)) :=
  (rfl)

/-! ### The Sobolev space -/

variable (F₀ F₁) in
/-- The Sobolev space `W^{1,2}_F((0, 1), X)` of paths with boundary values in `F₀` and `F₁`: the
closure in `L²((0, 1], X × X)` of the jets `(w, w')` of the `C¹` paths with `w 0 ∈ F₀` and
`w 1 ∈ F₁`, that is, their completion in a norm equivalent to the `W^{1,2}` norm. -/
abbrev H1 : Submodule ℝ (Lp (X × X) 2 μ₁) :=
  (LinearMap.range (jetLp F₀ F₁)).topologicalClosure

variable (F₀ F₁) in
/-- The jet of a path with boundary values in `F₀` and `F₁`, as an element of `H1`. -/
def jetH1 : boundaryPath F₀ F₁ →ₗ[ℝ] H1 F₀ F₁ :=
  (jetLp F₀ F₁).codRestrict (H1 F₀ F₁) fun w ↦
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ w)

/-- The jet in `H1` of a path is its `L²` jet. -/
@[simp]
theorem coe_jetH1 (w : boundaryPath F₀ F₁) :
    (jetH1 F₀ F₁ w : Lp (X × X) 2 μ₁) = jetLp F₀ F₁ w :=
  (rfl)

/-- The jets of classical paths are dense in `H1`. -/
theorem denseRange_jetH1 : DenseRange (jetH1 F₀ F₁) := by
  have h : ((H1 F₀ F₁ : Submodule ℝ (Lp (X × X) 2 μ₁)) : Set (Lp (X × X) 2 μ₁)) =
      closure (Set.range (jetLp F₀ F₁)) := by
    rw [Submodule.topologicalClosure_coe, LinearMap.coe_range]
  rw [DenseRange, Subtype.dense_iff, ← range_comp]
  exact h.subset

/-- A closed property of the elements of `H1` which holds for the jets of classical paths holds
everywhere. -/
theorem H1_induction {P : H1 F₀ F₁ → Prop} (hP : IsClosed {x | P x})
    (h : ∀ w : boundaryPath F₀ F₁, P (jetH1 F₀ F₁ w)) (x : H1 F₀ F₁) : P x :=
  denseRange_jetH1.induction_on x hP h

/-- `H1` is complete, as a closed subspace of the complete space `L²((0, 1], X × X)`. -/
instance [CompleteSpace X] : CompleteSpace (H1 F₀ F₁) :=
  Submodule.topologicalClosure.completeSpace _

variable (F₀ F₁) in
/-- The value `(w, w') ↦ w` of an element of `H1`, in `L²((0, 1], X)`. -/
def valueL : H1 F₀ F₁ →L[ℝ] Lp X 2 μ₁ :=
  ((ContinuousLinearMap.fst ℝ X X).compLpL 2 μ₁).comp (H1 F₀ F₁).subtypeL

variable (F₀ F₁) in
/-- The derivative `(w, w') ↦ w'` of an element of `H1`, in `L²((0, 1], X)`. -/
def derivL : H1 F₀ F₁ →L[ℝ] Lp X 2 μ₁ :=
  ((ContinuousLinearMap.snd ℝ X X).compLpL 2 μ₁).comp (H1 F₀ F₁).subtypeL

/-- The value of an element of `H1` is represented by the first component of its jet. -/
theorem coeFn_valueL (x : H1 F₀ F₁) :
    valueL F₀ F₁ x =ᵐ[μ₁] fun t ↦ ((x : Lp (X × X) 2 μ₁) t).fst :=
  ContinuousLinearMap.coeFn_compLpL _ _

/-- The derivative of an element of `H1` is represented by the second component of its jet. -/
theorem coeFn_derivL (x : H1 F₀ F₁) :
    derivL F₀ F₁ x =ᵐ[μ₁] fun t ↦ ((x : Lp (X × X) 2 μ₁) t).snd :=
  ContinuousLinearMap.coeFn_compLpL _ _

/-- The value of the jet of a classical path is the path. -/
@[simp]
theorem valueL_jetH1 (w : boundaryPath F₀ F₁) :
    valueL F₀ F₁ (jetH1 F₀ F₁ w) = (memLp_coe w).toLp w := by
  refine Lp.ext ((coeFn_valueL _).trans ?_)
  filter_upwards [MemLp.coeFn_toLp (memLp_pathJet w), MemLp.coeFn_toLp (memLp_coe w)]
    with t h₁ h₂
  rw [coe_jetH1, jetLp_apply, h₁, h₂, pathJet_apply]

/-- The derivative of the jet of a classical path is the derivative of the path. -/
@[simp]
theorem derivL_jetH1 (w : boundaryPath F₀ F₁) :
    derivL F₀ F₁ (jetH1 F₀ F₁ w) = (memLp_deriv w).toLp (deriv (w : ℝ → X)) := by
  refine Lp.ext ((coeFn_derivL _).trans ?_)
  filter_upwards [MemLp.coeFn_toLp (memLp_pathJet w), MemLp.coeFn_toLp (memLp_deriv w)]
    with t h₁ h₂
  rw [coe_jetH1, jetLp_apply, h₁, h₂, pathJet_apply]

/-- The norm of an element of `H1` is at most the sum of the `L²` norms of its value and its
derivative. -/
theorem norm_le_norm_valueL_add_norm_derivL (x : H1 F₀ F₁) :
    ‖x‖ ≤ ‖valueL F₀ F₁ x‖ + ‖derivL F₀ F₁ x‖ := by
  have hx : (x : Lp (X × X) 2 μ₁) =
      (ContinuousLinearMap.inl ℝ X X).compLpL 2 μ₁ (valueL F₀ F₁ x) +
        (ContinuousLinearMap.inr ℝ X X).compLpL 2 μ₁ (derivL F₀ F₁ x) := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add ((ContinuousLinearMap.inl ℝ X X).compLpL 2 μ₁ (valueL F₀ F₁ x))
      ((ContinuousLinearMap.inr ℝ X X).compLpL 2 μ₁ (derivL F₀ F₁ x)),
      ContinuousLinearMap.coeFn_compLpL (μ := μ₁) (p := 2) (ContinuousLinearMap.inl ℝ X X)
        (valueL F₀ F₁ x),
      ContinuousLinearMap.coeFn_compLpL (μ := μ₁) (p := 2) (ContinuousLinearMap.inr ℝ X X)
        (derivL F₀ F₁ x), coeFn_valueL x, coeFn_derivL x] with t h h₁ h₂ h₃ h₄
    rw [h, Pi.add_apply, h₁, h₂, h₃, h₄]
    simp
  rw [← Submodule.norm_coe, hx]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_of_le_one_left (norm_nonneg _) ((ContinuousLinearMap.norm_compLpL_le _).trans ?_)
    exact ContinuousLinearMap.norm_inl_le_one ℝ X X
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_of_le_one_left (norm_nonneg _) ((ContinuousLinearMap.norm_compLpL_le _).trans ?_)
    exact ContinuousLinearMap.norm_inr_le_one ℝ X X

/-! ### Elements of `H1` are determined by their values -/

section WeakDeriv

variable [CompleteSpace X]

/-- Integration by parts on `(0, 1)` for a `C¹` path against a test function supported in
`(0, 1)`: the integral of `φ' w + φ w'` over `(0, 1]` vanishes. -/
private theorem integral_lineDeriv_smul_add_integral_smul_deriv_eq_zero {w : ℝ → X}
    (hw : ContDiff ℝ 1 w) (φ : 𝓓(⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩, ℝ)) :
    ∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • w t ∂μ₁ + ∫ t, (φ : ℝ → ℝ) t • deriv w t ∂μ₁ = 0 := by
  have h := hasWeakLineDerivOn_of_hasLineDerivAt (μ := volume)
    (Ω := ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩) (v := (1 : ℝ))
    (hw.continuous.locallyIntegrable.locallyIntegrableOn _)
    ((hw.continuous_deriv le_rfl).locallyIntegrable.locallyIntegrableOn _)
    fun t _ ↦ by
      simpa using ((hw.differentiable one_ne_zero t).hasDerivAt.hasFDerivAt.hasLineDerivAt 1)
  have hsub {g : ℝ → X} (hg : ∀ t ∉ Ioo (0 : ℝ) 1, g t = 0) : ∫ t, g t ∂μ₁ = ∫ t, g t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦
      hg t fun h ↦ ht (Ioo_subset_Ioc_self h)
  rw [hsub fun t ht ↦ by
      rw [lineDeriv_of_notMem_tsupport (fun h ↦ ht (φ.tsupport_subset h)) 1, zero_smul],
    hsub fun t ht ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ ht (φ.tsupport_subset h)), zero_smul],
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, neg_add_cancel]

/-- **The derivative of an element of `H1` is the weak derivative of its value** on `(0, 1)`. -/
theorem hasWeakLineDerivOn_derivL (x : H1 F₀ F₁) :
    HasWeakLineDerivOn μ₁ ⟨Ioo 0 1, isOpen_Ioo⟩ (valueL F₀ F₁ x) (derivL F₀ F₁ x) 1 := by
  have hloc (f : Lp X 2 μ₁) : LocallyIntegrableOn f (Ioo 0 1) μ₁ :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn _
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hloc _, hloc _, fun φ ↦ ?_⟩
  refine eq_neg_of_add_eq_zero_left ?_
  -- Both integrals are continuous linear functionals of `x`, which vanish on classical jets.
  have hφ : MemLp (φ : ℝ → ℝ) 2 μ₁ := φ.continuous.memLp_restrict_Ioc 2
  have hφ' : MemLp (fun t ↦ lineDeriv ℝ (φ : ℝ → ℝ) t 1) 2 μ₁ := by
    simpa only [lineDeriv_one] using (φ.contDiff.continuous_deriv (by simp)).memLp_restrict_Ioc 2
  set B : ℝ →L[ℝ] X →L[ℝ] X := ContinuousLinearMap.lsmul ℝ ℝ
  have hpair {ψ : ℝ → ℝ} (hψ : MemLp ψ 2 μ₁) (f : Lp X 2 μ₁) :
      B.lpPairing μ₁ 2 2 (hψ.toLp ψ) f = ∫ t, ψ t • f t ∂μ₁ := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp] with t ht
    simp [B, ht]
  have key : ∀ y : H1 F₀ F₁, B.lpPairing μ₁ 2 2 (hφ'.toLp _) (valueL F₀ F₁ y) +
      B.lpPairing μ₁ 2 2 (hφ.toLp _) (derivL F₀ F₁ y) = 0 := by
    refine H1_induction (isClosed_eq (((B.lpPairing μ₁ 2 2 _).continuous.comp
      (valueL F₀ F₁).continuous).add ((B.lpPairing μ₁ 2 2 _).continuous.comp
      (derivL F₀ F₁).continuous)) continuous_const) fun w ↦ ?_
    rw [hpair, hpair, valueL_jetH1, derivL_jetH1]
    refine Eq.trans (congrArg₂ (· + ·) (integral_congr_ae ?_) (integral_congr_ae ?_))
      (integral_lineDeriv_smul_add_integral_smul_deriv_eq_zero (contDiff_coe w) φ)
    · filter_upwards [(memLp_coe w).coeFn_toLp] with t ht
      rw [ht]
    · filter_upwards [(memLp_deriv w).coeFn_toLp] with t ht
      rw [ht]
  simpa only [hpair] using key x

/-- **An element of `H1` is determined by its value.** The value map `(w, w') ↦ w` is injective on
`H1`: if the value of an element vanishes, so does its derivative, as its weak derivative. Thus
`H1` is a space of paths. -/
theorem valueL_injective : Injective (valueL F₀ F₁) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have hv : valueL F₀ F₁ x =ᵐ[μ₁] 0 := by
    rw [hx]
    exact Lp.coeFn_zero ..
  -- The derivative vanishes almost everywhere, as the weak derivative of `0`.
  have hd : derivL F₀ F₁ x =ᵐ[μ₁] 0 := by
    have h := ((hasWeakLineDerivOn_derivL x).congr_ae (ae_restrict_of_ae hv)).ae_eq
      hasWeakLineDerivOn_zero
    rwa [TopologicalSpace.Opens.coe_mk, Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.2 Ioo_subset_Ioc_self, Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h
  refine Subtype.ext ((Lp.eq_zero_iff_ae_eq_zero).2 ?_)
  filter_upwards [coeFn_valueL x, coeFn_derivL x, hv, hd] with t h₁ h₂ h₃ h₄
  exact Prod.ext (h₁.symm.trans h₃) (h₂.symm.trans h₄)

end WeakDeriv

/-! ### The boundary value operator -/

variable (F₀ F₁) in
/-- The operator `(w, w') ↦ w' - A w` of the boundary value problem `w' - A w = f`, `w 0 ∈ F₀`,
`w 1 ∈ F₁`, from `H1 F₀ F₁` to `L²((0, 1], X)`, for an essentially bounded coefficient `A`. -/
def boundaryValueOperator (A : Lp (X →L[ℝ] X) ∞ μ₁) : H1 F₀ F₁ →L[ℝ] Lp X 2 μ₁ :=
  derivL F₀ F₁ - (Lp.operatorMultiplication 2 A).comp (valueL F₀ F₁)

/-- The boundary value operator sends `(w, w')` to `w' - A w`. -/
theorem boundaryValueOperator_apply (A : Lp (X →L[ℝ] X) ∞ μ₁) (x : H1 F₀ F₁) :
    boundaryValueOperator F₀ F₁ A x =
      derivL F₀ F₁ x - Lp.operatorMultiplication 2 A (valueL F₀ F₁ x) :=
  (rfl)

/-- On the jet of a classical path `w`, the boundary value operator of a coefficient represented by
`S` is the class of `w' - S w`. -/
theorem boundaryValueOperator_jetH1 {A : Lp (X →L[ℝ] X) ∞ μ₁} {S : ℝ → X →L[ℝ] X}
    (hA : A =ᵐ[μ₁] S) (hS : Continuous S) (w : boundaryPath F₀ F₁) :
    boundaryValueOperator F₀ F₁ A (jetH1 F₀ F₁ w) =
      ((continuous_deriv_sub hS w).memLp_restrict_Ioc 2).toLp
        fun t ↦ deriv (w : ℝ → X) t - S t ((w : ℝ → X) t) := by
  rw [boundaryValueOperator_apply, valueL_jetH1, derivL_jetH1]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub ((memLp_deriv w).toLp (deriv (w : ℝ → X)))
      (Lp.operatorMultiplication 2 A ((memLp_coe w).toLp w)),
    Lp.operatorMultiplication_ae A ((memLp_coe w).toLp w), MemLp.coeFn_toLp (memLp_deriv w),
    MemLp.coeFn_toLp (memLp_coe w),
    MemLp.coeFn_toLp (f := fun t ↦ deriv (w : ℝ → X) t - S t ((w : ℝ → X) t))
      ((continuous_deriv_sub hS w).memLp_restrict_Ioc 2), hA]
    with t h h₁ h₂ h₃ h₄ h₅
  rw [h, Pi.sub_apply, h₁, h₂, h₃, h₄, h₅]

/-- A classical solution of `w' = S w + f` with `w 0 ∈ F₀` and `w 1 ∈ F₁`, for continuous `S`
and `f`, is a path with boundary values in `F₀` and `F₁`. -/
theorem mem_boundaryPath_of_hasDerivAt {S : ℝ → X →L[ℝ] X} {f : ℝ → X} (hS : Continuous S)
    (hf : Continuous f) (hw : ∀ t, HasDerivAt w (S t (w t) + f t) t) (hw₀ : w 0 ∈ F₀)
    (hw₁ : w 1 ∈ F₁) : w ∈ boundaryPath F₀ F₁ :=
  ⟨contDiff_one_of_hasDerivAt (X := fun t v ↦ S t v + f t)
    (((hS.comp continuous_fst).clm_apply continuous_snd).add (hf.comp continuous_fst)) hw, hw₀, hw₁⟩

/-- On the jet of a classical solution `w` of `w' = S w + f`, the boundary value operator of a
coefficient represented by `S` is the class of `f`. -/
theorem boundaryValueOperator_jetH1_of_hasDerivAt {A : Lp (X →L[ℝ] X) ∞ μ₁} {S : ℝ → X →L[ℝ] X}
    (hA : A =ᵐ[μ₁] S) (hS : Continuous S) {f : ℝ → X} (hf : Continuous f)
    {w : boundaryPath F₀ F₁} (hw : ∀ t, HasDerivAt (w : ℝ → X) (S t ((w : ℝ → X) t) + f t) t) :
    boundaryValueOperator F₀ F₁ A (jetH1 F₀ F₁ w) = (hf.memLp_restrict_Ioc 2).toLp f := by
  rw [boundaryValueOperator_jetH1 hA hS]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun t ↦ by simp [(hw t).deriv])

section CompleteSpace

variable [CompleteSpace X]

/-- **Injectivity forces nondegenerate boundary conditions.** If the boundary value operator of a
coefficient represented by a continuous path `S` is injective, then `Ψ(1) F₀ ∩ F₁ = 0` for the
propagator `Ψ = dysonSeriesLeft S`: a nonzero classical solution of `w' = S w`, `w 0 ∈ F₀`,
`w 1 ∈ F₁` would give a nonzero element of the kernel. -/
theorem disjoint_map_dysonSeriesLeft_of_injective {A : Lp (X →L[ℝ] X) ∞ μ₁}
    {S : ℝ → X →L[ℝ] X} (hA : A =ᵐ[μ₁] S) (hS : Continuous S)
    (hinj : Injective (boundaryValueOperator F₀ F₁ A)) :
    Disjoint (F₀.map (↑(dysonSeriesLeft S 1) : X →ₗ[ℝ] X)) F₁ := by
  refine (disjoint_map_dysonSeriesLeft_iff hS).2 fun w hw hw₀ hw₁ ↦ ?_
  -- The jet of a classical solution of the homogeneous problem lies in the kernel.
  have hw' (t : ℝ) : HasDerivAt w (S t (w t) + (0 : ℝ → X) t) t := by simpa using hw t
  have hmem := mem_boundaryPath_of_hasDerivAt hS continuous_zero hw' hw₀ hw₁
  have hx0 : jetH1 F₀ F₁ ⟨w, hmem⟩ = 0 := hinj <| by
    rw [boundaryValueOperator_jetH1_of_hasDerivAt (w := ⟨w, hmem⟩) hA hS continuous_zero hw',
      map_zero, MemLp.toLp_zero]
  -- Its value vanishes in `L²`, so `w` vanishes almost everywhere on `(0, 1]`, hence at a point.
  have hv := valueL_jetH1 (F₀ := F₀) (F₁ := F₁) ⟨w, hmem⟩
  rw [hx0, map_zero] at hv
  have hae : w =ᵐ[μ₁] 0 :=
    (MemLp.coeFn_toLp _).symm.trans (by rw [← hv]; exact Lp.coeFn_zero ..)
  have := ae_neBot.2 (by simp [Measure.restrict_eq_zero] : (μ₁ : Measure ℝ) ≠ 0)
  obtain ⟨t, ht⟩ := hae.exists
  -- A solution of `w' = S w` vanishing at one point vanishes everywhere.
  exact hS.eq_of_hasDerivAt_clm_apply hw (fun s ↦ by simp) ht

variable [FiniteDimensional ℝ F₀] [FiniteDimensional ℝ F₁]

/-- **The `L²` estimate on `H1`.** Let `S` be a continuous path representing `A`, with propagator
`Ψ = dysonSeriesLeft S`. If `Ψ(1) F₀ ∩ F₁ = 0`, the value of every element of `H1` is bounded in
`L²` by its image under the boundary value operator. -/
theorem exists_forall_norm_valueL_le_mul_norm_boundaryValueOperator
    {A : Lp (X →L[ℝ] X) ∞ μ₁} {S : ℝ → X →L[ℝ] X} (hA : A =ᵐ[μ₁] S) (hS : Continuous S)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft S 1) : X →ₗ[ℝ] X)) F₁) :
    ∃ C, 0 ≤ C ∧ ∀ x : H1 F₀ F₁, ‖valueL F₀ F₁ x‖ ≤ C * ‖boundaryValueOperator F₀ F₁ A x‖ := by
  obtain ⟨C, hC, hle⟩ :=
    exists_forall_integral_norm_sq_le_mul_integral_norm_sq_of_disjoint hS zero_le_one hP
  refine ⟨√C, Real.sqrt_nonneg C, H1_induction ?_ fun w ↦ ?_⟩
  · exact isClosed_le (continuous_norm.comp (valueL F₀ F₁).continuous)
      (continuous_const.mul (continuous_norm.comp (boundaryValueOperator F₀ F₁ A).continuous))
  -- For a classical path, this is the `L²` estimate for `w' = S w + f` with `f = w' - S w`.
  have hf := continuous_deriv_sub hS w
  have hw (t : ℝ) : HasDerivAt (w : ℝ → X)
      (S t ((w : ℝ → X) t) + (deriv (w : ℝ → X) t - S t ((w : ℝ → X) t))) t := by
    rw [add_sub_cancel]
    exact ((contDiff_coe w).differentiable one_ne_zero t).hasDerivAt
  have h := hle hf hw (coe_zero_mem w) (coe_one_mem w)
  rw [boundaryValueOperator_jetH1 hA hS, valueL_jetH1]
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt hC, MemLp.norm_toLp_sq, MemLp.norm_toLp_sq,
    ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  exact h

/-- **The boundary value operator is bounded below** when `Ψ(1) F₀ ∩ F₁ = 0`, for the propagator
`Ψ = dysonSeriesLeft S` of a continuous path `S` representing the coefficient. -/
theorem exists_forall_norm_le_mul_norm_boundaryValueOperator
    {A : Lp (X →L[ℝ] X) ∞ μ₁} {S : ℝ → X →L[ℝ] X} (hA : A =ᵐ[μ₁] S) (hS : Continuous S)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft S 1) : X →ₗ[ℝ] X)) F₁) :
    ∃ C, 0 ≤ C ∧ ∀ x : H1 F₀ F₁, ‖x‖ ≤ C * ‖boundaryValueOperator F₀ F₁ A x‖ := by
  obtain ⟨C, hC, hle⟩ := exists_forall_norm_valueL_le_mul_norm_boundaryValueOperator hA hS hP
  refine ⟨1 + (‖A‖ + 1) * C, by positivity, fun x ↦ ?_⟩
  -- The derivative is the image plus `A` times the value.
  have hd : derivL F₀ F₁ x =
      boundaryValueOperator F₀ F₁ A x + Lp.operatorMultiplication 2 A (valueL F₀ F₁ x) := by
    rw [boundaryValueOperator_apply, sub_add_cancel]
  have hv := hle x
  have hm := Lp.norm_operatorMultiplication_apply_le (p := 2) A (valueL F₀ F₁ x)
  have hdx : ‖derivL F₀ F₁ x‖ ≤
      ‖boundaryValueOperator F₀ F₁ A x‖ + ‖A‖ * ‖valueL F₀ F₁ x‖ := by
    rw [hd]
    exact (norm_add_le _ _).trans (add_le_add_right hm _)
  calc ‖x‖ ≤ ‖valueL F₀ F₁ x‖ + ‖derivL F₀ F₁ x‖ := norm_le_norm_valueL_add_norm_derivL x
    _ ≤ C * ‖boundaryValueOperator F₀ F₁ A x‖ + (‖boundaryValueOperator F₀ F₁ A x‖ +
        ‖A‖ * (C * ‖boundaryValueOperator F₀ F₁ A x‖)) := by
      gcongr
      exact hdx.trans (by gcongr)
    _ = (1 + (‖A‖ + 1) * C) * ‖boundaryValueOperator F₀ F₁ A x‖ := by ring

end CompleteSpace

variable [FiniteDimensional ℝ X]

/-- The image of the boundary value operator contains the class of every continuous function when
`Ψ(1) F₀ ∩ F₁ = 0` and `dim F₀ + dim F₁ = dim X`: it is the image of the jet of the classical
solution. -/
theorem toLp_mem_range_boundaryValueOperator {A : Lp (X →L[ℝ] X) ∞ μ₁} {S : ℝ → X →L[ℝ] X}
    (hA : A =ᵐ[μ₁] S) (hS : Continuous S)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft S 1) : X →ₗ[ℝ] X)) F₁)
    (hdim : Module.finrank ℝ F₀ + Module.finrank ℝ F₁ = Module.finrank ℝ X) {f : ℝ → X}
    (hf : Continuous f) :
    (hf.memLp_restrict_Ioc 2).toLp f ∈ Set.range (boundaryValueOperator F₀ F₁ A) := by
  obtain ⟨w, hw, hw₀, hw₁⟩ := exists_hasDerivAt_and_mem_of_disjoint hS hP hdim hf
  exact ⟨jetH1 F₀ F₁ ⟨w, mem_boundaryPath_of_hasDerivAt hS hf hw hw₀ hw₁⟩,
    boundaryValueOperator_jetH1_of_hasDerivAt (w := ⟨w, _⟩) hA hS hf hw⟩

/-- **Invertibility at nondegenerate boundary conditions.** Let `S` be a continuous path
representing the coefficient `A`, with propagator `Ψ = dysonSeriesLeft S`. If `Ψ(1) F₀ ∩ F₁ = 0`
and `dim F₀ + dim F₁ = dim X`, the boundary value operator `(w, w') ↦ w' - A w` from `H1 F₀ F₁`
to `L²((0, 1], X)` is invertible. -/
theorem isInvertible_boundaryValueOperator {A : Lp (X →L[ℝ] X) ∞ μ₁} {S : ℝ → X →L[ℝ] X}
    (hA : A =ᵐ[μ₁] S) (hS : Continuous S)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft S 1) : X →ₗ[ℝ] X)) F₁)
    (hdim : Module.finrank ℝ F₀ + Module.finrank ℝ F₁ = Module.finrank ℝ X) :
    (boundaryValueOperator F₀ F₁ A).IsInvertible := by
  obtain ⟨C, -, hle⟩ := exists_forall_norm_le_mul_norm_boundaryValueOperator hA hS hP
  have hinj : Injective (boundaryValueOperator F₀ F₁ A) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ norm_le_zero_iff.1 ?_
    simpa [hx] using hle x
  -- The range is closed, since the operator is bounded below.
  have hclosed : IsClosed (range (boundaryValueOperator F₀ F₁ A)) :=
    ((boundaryValueOperator F₀ F₁ A).antilipschitz_of_bound (K := C.toNNReal)
      fun x ↦ (hle x).trans (by gcongr; exact Real.le_coe_toNNReal C)).isClosed_range
      (boundaryValueOperator F₀ F₁ A).uniformContinuous
  -- The range contains the classes of the smooth compactly supported functions, which are dense.
  have hdense : Dense (range (boundaryValueOperator F₀ F₁ A)) := by
    refine (Lp.dense_hasCompactSupport_contDiff (μ := μ₁) (F := X) (E := ℝ) (p := 2)
      ENNReal.ofNat_ne_top).mono ?_
    rintro _ ⟨g, hg, -, hgc⟩
    obtain ⟨y, hy⟩ := toLp_mem_range_boundaryValueOperator hA hS hP hdim hgc.continuous
    exact ⟨y, hy.trans (Lp.ext ((MemLp.coeFn_toLp _).trans hg.symm))⟩
  refine ContinuousLinearMap.isInvertible_iff_bijective.2 ⟨hinj, ?_⟩
  rw [← range_eq_univ, ← hclosed.closure_eq, hdense.closure_eq]

/-- **Invertibility exactly at nondegenerate boundary conditions.** Let `S` be a continuous path
representing the coefficient `A`, with propagator `Ψ = dysonSeriesLeft S`, and suppose that
`dim F₀ + dim F₁ = dim X`, as for two Lagrangian subspaces of a symplectic space. Then the
boundary value operator `(w, w') ↦ w' - A w` from `H1 F₀ F₁` to `L²((0, 1], X)` is invertible if
and only if `Ψ(1) F₀ ∩ F₁ = 0`, that is, if and only if the classical problem `w' = S w`,
`w 0 ∈ F₀`, `w 1 ∈ F₁` has only the zero solution. -/
theorem isInvertible_boundaryValueOperator_iff {A : Lp (X →L[ℝ] X) ∞ μ₁} {S : ℝ → X →L[ℝ] X}
    (hA : A =ᵐ[μ₁] S) (hS : Continuous S)
    (hdim : Module.finrank ℝ F₀ + Module.finrank ℝ F₁ = Module.finrank ℝ X) :
    (boundaryValueOperator F₀ F₁ A).IsInvertible ↔
      Disjoint (F₀.map (↑(dysonSeriesLeft S 1) : X →ₗ[ℝ] X)) F₁ :=
  ⟨fun h ↦ disjoint_map_dysonSeriesLeft_of_injective hA hS h.injective,
    fun hP ↦ isInvertible_boundaryValueOperator hA hS hP hdim⟩

end PathSobolev

end TauCeti
