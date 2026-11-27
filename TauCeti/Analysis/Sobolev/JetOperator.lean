/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Normed.Operator.Surjective
import TauCeti.MeasureTheory.Function.Holder

/-!
# First-order operators on `Lᵖ` jets

The jet of a section `ξ : ℝ × ℝ → V` of a trivial bundle over a domain of the plane is a map
`ℝ × ℝ → V × V × V` collecting a zeroth-order term and the two first partial derivatives of `ξ`.
A first-order operator with coefficient field `M : ℝ × ℝ → L(V × V × V, W)` acts on jets
pointwise, `f ↦ (z ↦ M z (f z))`. For a measure `μ` on the plane, an exponent `1 ≤ p ≤ ∞` and
`M` essentially bounded for `μ`, this is a bounded operator `Lᵖ(μ, V × V × V) → Lᵖ(μ, W)`
(`TauCeti.jetOperator p`), the operator-valued multiplication operator
`MeasureTheory.Lp.operatorMultiplication p`; otherwise it is `0`, so a coefficient field with a
nonzero operator is essentially bounded (`TauCeti.memLp_of_jetOperator_ne_zero`). It is additive
in `M` (`TauCeti.jetOperator_add`), and multiplying `M` by an essentially bounded scalar function
multiplies its values pointwise (`TauCeti.coeFn_jetOperator_smul`). The constant identity field
gives the identity (`TauCeti.jetOperator_id`), the operators of two coefficient fields compose to
that of the pointwise composite (`TauCeti.jetOperator_comp_jetOperator`), and applying an
essentially bounded field of maps after a first-order operator is the first-order operator of the
composite field (`TauCeti.jetOperator_comp_eq_operatorMultiplication_comp`). It depends
Lipschitz-continuously on `M` in `L^∞` (`TauCeti.norm_jetOperator_sub_le`): a measurable change
of `M` bounded by `B` almost everywhere moves the operator by at most `B`, even when `M` is not
essentially bounded (`TauCeti.norm_jetOperator_sub_le_of_ae_norm_sub_le`). Hence it depends
continuously along families of coefficient fields continuous in `L^∞`
(`TauCeti.continuousOn_jetOperator`), and a bounded right inverse of the operator of `M` on a space
of jets survives every change of `M` that is small in `L^∞` compared with its norm
(`TauCeti.exists_rightInverse_jetOperator_comp_subtypeL_of_norm_sub_le`).

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
through this one construction. The Hilbert space theory of these operators (adjoints, Fredholm
estimates) uses `p = 2`. For `2 < p < ∞` the elements of the Sobolev space
`TauCeti.CylinderSobolev.W1p V p` of the cylinder are continuous sections
(`TauCeti.CylinderSobolev.continuousValue`), so nonlinear terms such as `J(u + ξ)` can be evaluated
on them.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces and first-order elliptic operators.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
open scoped Classical in
/-- The first-order operator `f ↦ (z ↦ M z (f z))` on `Lᵖ(μ)` jets, for a coefficient field `M`
essentially bounded for `μ`. On the jet of a section `ξ` it is the first-order operator with
coefficients `M`. If `M` is not essentially bounded for `μ`, it is `0` by convention. -/
def jetOperator (μ : Measure (ℝ × ℝ)) (M : ℝ × ℝ → V × V × V →L[ℝ] W) :
    Lp (V × V × V) p μ →L[ℝ] Lp W p μ :=
  if hM : MemLp M ∞ μ then
    Lp.operatorMultiplication p (hM.toLp M)
  else 0

/-- The first-order operator of a coefficient field that is not essentially bounded is `0`. -/
theorem jetOperator_of_not_memLp {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : ¬ MemLp M ∞ μ) : jetOperator p μ M = 0 := by
  simp [jetOperator, hM]

/-- A coefficient field whose first-order operator is nonzero is essentially bounded. -/
theorem memLp_of_jetOperator_ne_zero {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (h : jetOperator p μ M ≠ 0) : MemLp M ∞ μ :=
  not_not.1 (mt jetOperator_of_not_memLp h)

/-- The first-order operator of an essentially bounded coefficient field is the operator-valued
multiplication operator `MeasureTheory.Lp.operatorMultiplication p` by that field. -/
theorem jetOperator_of_memLp {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) : jetOperator p μ M = Lp.operatorMultiplication p (hM.toLp M) := by
  simp [jetOperator, hM]

/-- The first-order operator of an essentially bounded coefficient field acts pointwise on
`Lᵖ` jets. -/
theorem coeFn_jetOperator {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) (f : Lp (V × V × V) p μ) :
    jetOperator p μ M f =ᵐ[μ] fun z ↦ M z (f z) := by
  rw [jetOperator_of_memLp hM]
  filter_upwards [Lp.operatorMultiplication_ae (hM.toLp M) f, hM.coeFn_toLp] with z h₁ h₂
  rw [h₁, h₂]

/-- The first-order operator is additive in its coefficient field. -/
theorem jetOperator_add {μ : Measure (ℝ × ℝ)} {M N : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) (hN : MemLp N ∞ μ) :
    jetOperator p μ (M + N) = jetOperator p μ M + jetOperator p μ N := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [coeFn_jetOperator (hM.add hN) f, coeFn_jetOperator hM f,
    coeFn_jetOperator hN f, Lp.coeFn_add (jetOperator p μ M f) (jetOperator p μ N f)]
    with z h h₁ h₂ h₃
  rw [add_apply, h₃, Pi.add_apply, h, h₁, h₂, Pi.add_apply, add_apply]

/-- The first-order operator of the constant identity coefficient field is the identity of `Lᵖ`
jets. -/
@[simp]
theorem jetOperator_id {μ : Measure (ℝ × ℝ)} :
    jetOperator p μ (fun _ ↦ ContinuousLinearMap.id ℝ (V × V × V)) =
      ContinuousLinearMap.id ℝ (Lp (V × V × V) p μ) := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [coeFn_jetOperator (memLp_top_const (ContinuousLinearMap.id ℝ (V × V × V))) f]
    with z h
  rw [h, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

/-- The first-order operators of two essentially bounded coefficient fields compose to the
first-order operator of their pointwise composite. -/
theorem jetOperator_comp_jetOperator {μ : Measure (ℝ × ℝ)}
    {N : ℝ × ℝ → W × W × W →L[ℝ] U} {M : ℝ × ℝ → V × V × V →L[ℝ] W × W × W}
    (hN : MemLp N ∞ μ) (hM : MemLp M ∞ μ) :
    (jetOperator p μ N).comp (jetOperator p μ M) = jetOperator p μ fun z ↦ (N z).comp (M z) := by
  have hNM : MemLp (fun z ↦ (N z).comp (M z)) ∞ μ := hN.clm_comp ∞ hM
  ext1 f
  refine Lp.ext ?_
  filter_upwards [coeFn_jetOperator hN (jetOperator p μ M f), coeFn_jetOperator hM f,
    coeFn_jetOperator hNM f] with z h₁ h₂ h₃
  rw [ContinuousLinearMap.comp_apply, h₁, h₂, h₃, ContinuousLinearMap.comp_apply]

/-- Applying an essentially bounded field `G` of maps after a first-order operator is the
first-order operator of the composite coefficient field. -/
theorem jetOperator_comp_eq_operatorMultiplication_comp {μ : Measure (ℝ × ℝ)}
    {G : ℝ × ℝ → W →L[ℝ] U} {N : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hG : MemLp G ∞ μ) (hN : MemLp N ∞ μ) :
    jetOperator p μ (fun z ↦ (G z).comp (N z)) =
      (Lp.operatorMultiplication p (hG.toLp G)).comp (jetOperator p μ N) := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [coeFn_jetOperator (hG.clm_comp ∞ hN) f,
    Lp.operatorMultiplication_ae (hG.toLp G) (jetOperator p μ N f),
    hG.coeFn_toLp, coeFn_jetOperator hN f] with z h₁ h₂ h₃ h₄
  rw [h₁, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h₂, h₃, h₄]

/-- Multiplying the coefficient field by an essentially bounded scalar function `b` multiplies the
values of the first-order operator by `b`. -/
theorem coeFn_jetOperator_smul {μ : Measure (ℝ × ℝ)} {b : ℝ × ℝ → ℝ}
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hb : MemLp b ∞ μ) (hM : MemLp M ∞ μ)
    (f : Lp (V × V × V) p μ) :
    jetOperator p μ (fun z ↦ b z • M z) f =ᵐ[μ] fun z ↦ b z • jetOperator p μ M f z := by
  filter_upwards [coeFn_jetOperator (M := fun z ↦ b z • M z) (hb.smul hM) f,
    coeFn_jetOperator hM f] with z h₁ h₂
  rw [h₁, h₂, smul_apply]

/-- An almost everywhere bound `‖M z‖ ≤ C` on the coefficient field bounds the first-order
operator by `C`. -/
theorem norm_jetOperator_apply_le {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) {C : ℝ} (hC : ∀ᵐ z ∂μ, ‖M z‖ ≤ C) (f : Lp (V × V × V) p μ) :
    ‖jetOperator p μ M f‖ ≤ C * ‖f‖ :=
  Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [coeFn_jetOperator hM f, hC] with z h₁ h₂
    rw [h₁]
    exact ((M z).le_opNorm _).trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)))

/-- The first-order operator depends Lipschitz-continuously on its coefficient field: its operator
norm on `Lᵖ` jets is at most the essential supremum of the difference of the coefficients. -/
theorem norm_jetOperator_sub_le {μ : Measure (ℝ × ℝ)} {M M' : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) (hM' : MemLp M' ∞ μ) :
    ‖jetOperator p μ M - jetOperator p μ M'‖ ≤ (eLpNorm (M - M') ∞ μ).toReal := by
  rw [jetOperator_of_memLp hM, jetOperator_of_memLp hM', ← map_sub, ← MemLp.toLp_sub,
    ← Lp.norm_toLp _ (hM.sub hM')]
  exact Lp.norm_operatorMultiplication_le _

/-- If two coefficient fields differ by a measurable field bounded by `B` almost everywhere, their
first-order operators differ by at most `B` in operator norm. Neither field needs to be essentially
bounded: if one is not, neither is the other, and both operators vanish. -/
theorem norm_jetOperator_sub_le_of_ae_norm_sub_le {μ : Measure (ℝ × ℝ)}
    {M M' : ℝ × ℝ → V × V × V →L[ℝ] W} (hD : AEStronglyMeasurable (M - M') μ) {B : ℝ}
    (hB₀ : 0 ≤ B) (hB : ∀ᵐ z ∂μ, ‖M z - M' z‖ ≤ B) :
    ‖jetOperator p μ M - jetOperator p μ M'‖ ≤ B := by
  have hDm : MemLp (M - M') ∞ μ := memLp_top_of_bound hD B hB
  by_cases hM' : MemLp M' ∞ μ
  · have hM : MemLp M ∞ μ := by simpa only [add_sub_cancel] using hM'.add hDm
    refine (norm_jetOperator_sub_le hM hM').trans (ENNReal.toReal_le_of_le_ofReal hB₀ ?_)
    rw [eLpNorm_exponent_top hD]
    exact eLpNormEssSup_le_of_ae_bound hB
  · -- Otherwise neither coefficient field is essentially bounded, and both operators vanish.
    have hM : ¬ MemLp M ∞ μ := fun h ↦ hM' (by simpa only [sub_sub_cancel] using h.sub hDm)
    rw [jetOperator_of_not_memLp hM, jetOperator_of_not_memLp hM', sub_zero, norm_zero]
    exact hB₀

/-- **Right inverses survive small changes of the coefficient field.** Let `S` be a subspace of the
`Lᵖ` jets, such as a Sobolev space, and suppose that the first-order operator of an essentially
bounded coefficient field `G`, restricted to `S`, has a bounded linear right inverse `Q₀`. If the
coefficient field `M` is almost everywhere within `δ` of `G`, with `δ ‖Q₀‖ ≤ 1 / 2`, then the
first-order operator of `M`, restricted to `S`, has a bounded linear right inverse of norm at most
`2 ‖Q₀‖`. -/
theorem exists_rightInverse_jetOperator_comp_subtypeL_of_norm_sub_le [CompleteSpace W]
    {μ : Measure (ℝ × ℝ)} {M G : ℝ × ℝ → V × V × V →L[ℝ] W} (hG : MemLp G ∞ μ)
    (hM : AEStronglyMeasurable M μ) {δ : ℝ} (hMG : ∀ᵐ z ∂μ, ‖M z - G z‖ ≤ δ)
    {S : Submodule ℝ (Lp (V × V × V) p μ)} {Q₀ : Lp W p μ →L[ℝ] S}
    (hQ₀ : ((jetOperator p μ G).comp S.subtypeL).comp Q₀ = ContinuousLinearMap.id ℝ _)
    (hδ : δ * ‖Q₀‖ ≤ 1 / 2) :
    ∃ Q : Lp W p μ →L[ℝ] S, ((jetOperator p μ M).comp S.subtypeL).comp Q =
      ContinuousLinearMap.id ℝ _ ∧ ‖Q‖ ≤ 2 * ‖Q₀‖ := by
  open ContinuousLinearMap in
  -- The operator of `M` is that of `G` plus that of the field `M - G`, bounded by `max δ 0`.
  have hbound : ∀ᵐ z ∂μ, ‖(M - G) z‖ ≤ max δ 0 := hMG.mono fun z hz ↦ le_max_of_le_left hz
  have hD : MemLp (M - G) ∞ μ := memLp_top_of_bound (hM.sub hG.aestronglyMeasurable) _ hbound
  have hsplit : (jetOperator p μ M).comp S.subtypeL =
      (jetOperator p μ G).comp S.subtypeL + (jetOperator p μ (M - G)).comp S.subtypeL := by
    rw [← add_comp, ← jetOperator_add hG hD, add_sub_cancel]
  refine exists_rightInverse_of_norm_comp_sub_id_le_half _ Q₀ ?_
  rw [hsplit, add_comp, hQ₀, add_sub_cancel_left]
  refine opNorm_le_bound _ (by norm_num) fun η ↦ ?_
  have hδ' : max δ 0 * ‖Q₀‖ ≤ 1 / 2 := by
    rcases le_total δ 0 with h | h
    · rw [max_eq_right h, zero_mul]
      norm_num
    · rwa [max_eq_left h]
  calc ‖jetOperator p μ (M - G) (S.subtypeL (Q₀ η))‖
      ≤ max δ 0 * ‖S.subtypeL (Q₀ η)‖ := norm_jetOperator_apply_le hD hbound _
    _ = max δ 0 * ‖Q₀ η‖ := by rw [Submodule.subtypeL_apply, Submodule.norm_coe]
    _ ≤ max δ 0 * (‖Q₀‖ * ‖η‖) := by gcongr; exact Q₀.le_opNorm η
    _ ≤ 1 / 2 * ‖η‖ := by rw [← mul_assoc]; gcongr

/-- Coefficient fields depending continuously on a parameter in `L^∞` give first-order operators
on `Lᵖ` jets depending continuously on the parameter in the operator norm. -/
theorem continuousOn_jetOperator {μ : Measure (ℝ × ℝ)} {X : Type*} [TopologicalSpace X]
    {s : Set X} {M : X → ℝ × ℝ → V × V × V →L[ℝ] W} (hM : ∀ x ∈ s, MemLp (M x) ∞ μ)
    (hcont : ∀ x ∈ s, Tendsto (fun y ↦ eLpNorm (M y - M x) ∞ μ) (𝓝[s] x) (𝓝 0)) :
    ContinuousOn (fun x ↦ jetOperator p μ (M x)) s := by
  intro x hx
  have hlim : Tendsto (fun y ↦ (eLpNorm (M y - M x) ∞ μ).toReal) (𝓝[s] x) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont x hx)
  -- `‖D_y - D_x‖ ≤ ‖M y - M x‖_{L^∞}` for `y ∈ s`.
  have hle : ∀ᶠ y in 𝓝[s] x, ‖jetOperator p μ (M y) - jetOperator p μ (M x)‖ ≤
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
