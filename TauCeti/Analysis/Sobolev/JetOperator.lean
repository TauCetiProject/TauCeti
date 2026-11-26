/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# First-order operators on `L²` jets

The jet of a section `ξ : ℝ × ℝ → V` of a trivial bundle over a domain of the plane is a map
`ℝ × ℝ → V × V × V` collecting a zeroth-order term and the two first partial derivatives of `ξ`.
A first-order operator with coefficient field `M : ℝ × ℝ → L(V × V × V, W)` acts on jets
pointwise, `f ↦ (z ↦ M z (f z))`. For a measure `μ` on the plane and `M` essentially bounded for
`μ`, this is a bounded operator `L²(μ, V × V × V) → L²(μ, W)` (`TauCeti.jetOperator`), the
operator-valued multiplication operator `MeasureTheory.Lp.operatorMultiplication 2`; otherwise it
is `0`, so a coefficient field with a nonzero operator is essentially bounded
(`TauCeti.memLp_of_jetOperator_ne_zero`). It is additive
in `M` (`TauCeti.jetOperator_add`), and multiplying `M` by an essentially bounded scalar function
multiplies its values pointwise (`TauCeti.coeFn_jetOperator_smul`). It depends
Lipschitz-continuously on `M` in `L^∞` (`TauCeti.norm_jetOperator_sub_le`), hence continuously
along families of coefficient fields continuous in `L^∞` (`TauCeti.continuousOn_jetOperator`).

The operators `∂s + A ∂t + C` with `A, C : V →L[ℝ] V`, such as the linearized Floer operators,
have the coefficient field `(a, b, c) ↦ b + A c + C a` on jets (`TauCeti.firstOrderJetCoeff`),
whose norm is at most `1 + ‖A‖ + ‖C‖` (`TauCeti.norm_firstOrderJetCoeff_le`) and at least `‖A‖`
and `‖C‖` (`TauCeti.norm_le_norm_firstOrderJetCoeff_left`,
`TauCeti.norm_le_norm_firstOrderJetCoeff_right`), which changes by at most
`‖A - A'‖ + ‖C - C'‖` when `A` and `C` are replaced by `A'` and `C'`
(`TauCeti.norm_firstOrderJetCoeff_sub_le`; for `A = A'`,
`TauCeti.norm_firstOrderJetCoeff_sub_firstOrderJetCoeff_le`), and which depends continuously on
`A` and `C` (`TauCeti.continuousAt_firstOrderJetCoeff`).

The Sobolev spaces on the cylinder (with the strip measure) and on conformally weighted domains
of the plane (with Lebesgue measure restricted to the domain) both realize first-order operators
through this one construction.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces and first-order elliptic operators.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

open scoped Classical in
/-- The first-order operator `f ↦ (z ↦ M z (f z))` on `L²(μ)` jets, for a coefficient field `M`
essentially bounded for `μ`. On the jet of a section `ξ` it is the first-order operator with
coefficients `M`. If `M` is not essentially bounded for `μ`, it is `0` by convention. -/
def jetOperator (μ : Measure (ℝ × ℝ)) (M : ℝ × ℝ → V × V × V →L[ℝ] W) :
    Lp (V × V × V) 2 μ →L[ℝ] Lp W 2 μ :=
  if hM : MemLp M ∞ μ then
    Lp.operatorMultiplication 2 (hM.toLp M)
  else 0

/-- The first-order operator of a coefficient field that is not essentially bounded is `0`. -/
theorem jetOperator_of_not_memLp {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : ¬ MemLp M ∞ μ) : jetOperator μ M = 0 := by
  simp [jetOperator, hM]

/-- A coefficient field whose first-order operator is nonzero is essentially bounded. -/
theorem memLp_of_jetOperator_ne_zero {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (h : jetOperator μ M ≠ 0) : MemLp M ∞ μ :=
  not_not.1 (mt jetOperator_of_not_memLp h)

/-- The first-order operator of an essentially bounded coefficient field is the operator-valued
multiplication operator `MeasureTheory.Lp.operatorMultiplication 2` by that field. -/
theorem jetOperator_of_memLp {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) : jetOperator μ M = Lp.operatorMultiplication 2 (hM.toLp M) := by
  simp [jetOperator, hM]

/-- The first-order operator of an essentially bounded coefficient field acts pointwise on
`L²` jets. -/
theorem coeFn_jetOperator {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) (f : Lp (V × V × V) 2 μ) :
    jetOperator μ M f =ᵐ[μ] fun z ↦ M z (f z) := by
  rw [jetOperator_of_memLp hM]
  filter_upwards [Lp.operatorMultiplication_ae (hM.toLp M) f, hM.coeFn_toLp] with z h₁ h₂
  rw [h₁, h₂]

/-- The first-order operator is additive in its coefficient field. -/
theorem jetOperator_add {μ : Measure (ℝ × ℝ)} {M N : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) (hN : MemLp N ∞ μ) :
    jetOperator μ (M + N) = jetOperator μ M + jetOperator μ N := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [coeFn_jetOperator (hM.add hN) f, coeFn_jetOperator hM f,
    coeFn_jetOperator hN f, Lp.coeFn_add (jetOperator μ M f) (jetOperator μ N f)]
    with z h h₁ h₂ h₃
  rw [add_apply, h₃, Pi.add_apply, h, h₁, h₂, Pi.add_apply, add_apply]

/-- Multiplying the coefficient field by an essentially bounded scalar function `b` multiplies the
values of the first-order operator by `b`. -/
theorem coeFn_jetOperator_smul {μ : Measure (ℝ × ℝ)} {b : ℝ × ℝ → ℝ}
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hb : MemLp b ∞ μ) (hM : MemLp M ∞ μ)
    (f : Lp (V × V × V) 2 μ) :
    jetOperator μ (fun z ↦ b z • M z) f =ᵐ[μ] fun z ↦ b z • jetOperator μ M f z := by
  filter_upwards [coeFn_jetOperator (M := fun z ↦ b z • M z) (hb.smul hM) f,
    coeFn_jetOperator hM f] with z h₁ h₂
  rw [h₁, h₂, smul_apply]

/-- An almost everywhere bound `‖M z‖ ≤ C` on the coefficient field bounds the first-order
operator by `C`. -/
theorem norm_jetOperator_apply_le {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) {C : ℝ} (hC : ∀ᵐ z ∂μ, ‖M z‖ ≤ C) (f : Lp (V × V × V) 2 μ) :
    ‖jetOperator μ M f‖ ≤ C * ‖f‖ :=
  Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [coeFn_jetOperator hM f, hC] with z h₁ h₂
    rw [h₁]
    exact ((M z).le_opNorm _).trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)))

/-- The first-order operator depends Lipschitz-continuously on its coefficient field: its operator
norm on `L²` jets is at most the essential supremum of the difference of the coefficients. -/
theorem norm_jetOperator_sub_le {μ : Measure (ℝ × ℝ)} {M M' : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) (hM' : MemLp M' ∞ μ) :
    ‖jetOperator μ M - jetOperator μ M'‖ ≤ (eLpNorm (M - M') ∞ μ).toReal := by
  rw [jetOperator_of_memLp hM, jetOperator_of_memLp hM', ← map_sub, ← MemLp.toLp_sub,
    ← Lp.norm_toLp _ (hM.sub hM')]
  exact Lp.norm_operatorMultiplication_le _

/-- Coefficient fields depending continuously on a parameter in `L^∞` give first-order operators
on `L²` jets depending continuously on the parameter in the operator norm. -/
theorem continuousOn_jetOperator {μ : Measure (ℝ × ℝ)} {X : Type*} [TopologicalSpace X]
    {s : Set X} {M : X → ℝ × ℝ → V × V × V →L[ℝ] W} (hM : ∀ x ∈ s, MemLp (M x) ∞ μ)
    (hcont : ∀ x ∈ s, Tendsto (fun y ↦ eLpNorm (M y - M x) ∞ μ) (𝓝[s] x) (𝓝 0)) :
    ContinuousOn (fun x ↦ jetOperator μ (M x)) s := by
  intro x hx
  have hlim : Tendsto (fun y ↦ (eLpNorm (M y - M x) ∞ μ).toReal) (𝓝[s] x) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont x hx)
  -- `‖D_y - D_x‖ ≤ ‖M y - M x‖_{L^∞}` for `y ∈ s`.
  have hle : ∀ᶠ y in 𝓝[s] x, ‖jetOperator μ (M y) - jetOperator μ (M x)‖ ≤
      (eLpNorm (M y - M x) ∞ μ).toReal := by
    filter_upwards [self_mem_nhdsWithin] with y hy using norm_jetOperator_sub_le (hM y hy) (hM x hx)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hle hlim)

/-- The coefficient field `(a, b, c) ↦ b + A c + C a` on jets `(a, b, c)` of the operator
`∂s + A ∂t + C`, where `b` and `c` are the slots of the partial derivatives `∂s` and `∂t`. -/
def firstOrderJetCoeff (A C : V →L[ℝ] V) : V × V × V →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V)) +
    A.comp ((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))) +
      C.comp (ContinuousLinearMap.fst ℝ V (V × V))

/-- The coefficient field of `∂s + A ∂t + C`, evaluated on a jet. -/
@[simp]
theorem firstOrderJetCoeff_apply (A C : V →L[ℝ] V) (v : V × V × V) :
    firstOrderJetCoeff A C v = v.2.1 + A v.2.2 + C v.1 :=
  (rfl)

/-- The norm of the coefficient field of `∂s + A ∂t + C` on jets is at most `1 + ‖A‖ + ‖C‖`. -/
theorem norm_firstOrderJetCoeff_le (A C : V →L[ℝ] V) :
    ‖firstOrderJetCoeff A C‖ ≤ 1 + ‖A‖ + ‖C‖ := by
  open ContinuousLinearMap in
  refine norm_add₃_le.trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact (opNorm_comp_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (norm_fst_le ℝ V V)).trans (norm_snd_le ℝ V (V × V)))
  · refine (opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
    exact (opNorm_comp_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (norm_snd_le ℝ V V)).trans (norm_snd_le ℝ V (V × V)))
  · exact (opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
      (norm_fst_le ℝ V (V × V)))

/-- The coefficient fields of two operators `∂s + A ∂t + C` and `∂s + A' ∂t + C'` differ by at
most `‖A - A'‖ + ‖C - C'‖`. -/
theorem norm_firstOrderJetCoeff_sub_le (A A' C C' : V →L[ℝ] V) :
    ‖firstOrderJetCoeff A C - firstOrderJetCoeff A' C'‖ ≤ ‖A - A'‖ + ‖C - C'‖ := by
  open ContinuousLinearMap in
  have h : firstOrderJetCoeff A C - firstOrderJetCoeff A' C' =
      (A - A').comp ((snd ℝ V V).comp (snd ℝ V (V × V))) + (C - C').comp (fst ℝ V (V × V)) :=
    ContinuousLinearMap.ext fun v ↦ by simp only [sub_apply, firstOrderJetCoeff_apply, add_apply,
      comp_apply, coe_snd', coe_fst']; abel
  rw [h]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
    exact (opNorm_comp_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (norm_snd_le ℝ V V)).trans (norm_snd_le ℝ V (V × V)))
  · exact (opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (norm_fst_le ℝ V (V × V)))

/-- The coefficient fields of two operators `∂s + A ∂t + C` and `∂s + A ∂t + C'` with the same
principal part differ by at most `‖C - C'‖`. -/
theorem norm_firstOrderJetCoeff_sub_firstOrderJetCoeff_le (A C C' : V →L[ℝ] V) :
    ‖firstOrderJetCoeff A C - firstOrderJetCoeff A C'‖ ≤ ‖C - C'‖ := by
  simpa using norm_firstOrderJetCoeff_sub_le A A C C'

/-- The leading coefficient `A` of `∂s + A ∂t + C` is a component of its coefficient field on
jets: `A v` is the value of the field on `(0, 0, v)`. -/
theorem norm_le_norm_firstOrderJetCoeff_left (A C : V →L[ℝ] V) :
    ‖A‖ ≤ ‖firstOrderJetCoeff A C‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ by
    simpa [Prod.norm_def] using (firstOrderJetCoeff A C).le_opNorm (0, 0, v)

/-- The zeroth-order coefficient `C` of `∂s + A ∂t + C` is a component of its coefficient field on
jets: `C v` is the value of the field on `(v, 0, 0)`. -/
theorem norm_le_norm_firstOrderJetCoeff_right (A C : V →L[ℝ] V) :
    ‖C‖ ≤ ‖firstOrderJetCoeff A C‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ by
    simpa [Prod.norm_def] using (firstOrderJetCoeff A C).le_opNorm (v, 0, 0)

/-- The coefficient field of `∂s + A ∂t + C` on jets depends continuously on `A` and `C`. -/
theorem continuousAt_firstOrderJetCoeff {X : Type*} [TopologicalSpace X] {A C : X → V →L[ℝ] V}
    {x : X} (hA : ContinuousAt A x) (hC : ContinuousAt C x) :
    ContinuousAt (fun x ↦ firstOrderJetCoeff (A x) (C x)) x :=
  (continuousAt_const.add (hA.clm_comp continuousAt_const)).add (hC.clm_comp continuousAt_const)

end TauCeti
