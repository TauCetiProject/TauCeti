/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Energy
public import TauCeti.Analysis.OperatorIdeal.Family.Basic
public import Mathlib.Analysis.MeanInequalities

/-!
# The Hilbert--Schmidt operator ideal

The **Hilbert--Schmidt norm** of a bounded operator between Hilbert spaces is the square
root of its Hilbert--Schmidt energy,

```
‖T‖_HS = (∑' i, ‖T (b i)‖ₑ ^ 2) ^ (1/2),
```

which by `ContinuousLinearMap.hilbertSchmidtEnergy_indep` does not depend on the Hilbert
basis `b`.  Like the energy it takes values in `ℝ≥0∞` and is therefore defined for every
bounded operator, being `∞` exactly off the ideal.

The point of the file is the final construction: these operators form a
`TauCeti.SymmetricOperatorIdealFamily`, the second concrete instance of that structure
after the Ky Fan families.  Two instances built from genuinely different mathematics is
what makes the structure worth having, and the Hilbert--Schmidt one is the instance the
literature reaches for first.

## Main definitions and results

* `ContinuousLinearMap.hilbertSchmidtENorm`: the Hilbert--Schmidt norm, valued in `ℝ≥0∞`;
* `ContinuousLinearMap.hilbertSchmidtENorm_add_le`: the triangle inequality, which is
  Minkowski's inequality at `p = 2`;
* `ContinuousLinearMap.enorm_le_hilbertSchmidtENorm`: it dominates the operator norm;
* `ContinuousLinearMap.hilbertSchmidtENorm_comp_le`: the two-sided ideal bound;
* `ContinuousLinearMap.hilbertSchmidtENorm_adjoint`: it is adjoint-invariant;
* `TauCeti.hilbertSchmidtIdealFamily`: the resulting symmetric operator ideal family.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: none.  `vendor/Spectra` models Hilbert--Schmidt operators as a Hilbert
  tensor product and does not build an operator ideal from them.
-/

open scoped ENNReal NNReal InnerProductSpace

public section

namespace ENNReal

variable {ι : Type*}

/-- **Minkowski's inequality in `ℓᵖ` for `tsum`, over `ℝ≥0∞`.**  Mathlib's
`ENNReal.Lp_add_le` is stated for a `Finset`, and its `tsum` counterpart exists only over
`ℝ≥0` (`NNReal.Lp_add_le_tsum`), where it carries summability hypotheses on both summands.
This is the `ℝ≥0∞` version, which needs no summability hypothesis at all — that is exactly
why the operator-ideal gauges are `ℝ≥0∞`-valued, since it lets their laws hold
unconditionally at non-members.

The proof is the standard supremum argument: the finite inequality bounds every partial sum
of the left side by the `p`-th power of the right side, and `∑'` is the supremum of its
partial sums. -/
theorem tsum_rpow_add_le {p : ℝ} (hp : 1 ≤ p) (f g : ι → ℝ≥0∞) :
    (∑' i, (f i + g i) ^ p) ^ p⁻¹ ≤
      (∑' i, f i ^ p) ^ p⁻¹ + (∑' i, g i ^ p) ^ p⁻¹ := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set A := (∑' i, f i ^ p) ^ p⁻¹ with hA
  set B := (∑' i, g i ^ p) ^ p⁻¹ with hB
  have hpow : ∀ x : ℝ≥0∞, (x ^ p⁻¹) ^ p = x := fun x => by
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  have key : ∀ s : Finset ι, ∑ i ∈ s, (f i + g i) ^ p ≤ (A + B) ^ p := by
    intro s
    have hfin := ENNReal.Lp_add_le (s := s) (f := f) (g := g) (p := p) hp
    rw [one_div] at hfin
    have hfA : (∑ i ∈ s, f i ^ p) ^ p⁻¹ ≤ A :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by positivity)
    have hgB : (∑ i ∈ s, g i ^ p) ^ p⁻¹ ≤ B :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by positivity)
    calc ∑ i ∈ s, (f i + g i) ^ p
        = ((∑ i ∈ s, (f i + g i) ^ p) ^ p⁻¹) ^ p := (hpow _).symm
      _ ≤ (A + B) ^ p :=
          ENNReal.rpow_le_rpow (hfin.trans (add_le_add hfA hgB)) hp0.le
  have hsum : ∑' i, (f i + g i) ^ p ≤ (A + B) ^ p :=
    ENNReal.tsum_eq_iSup_sum.trans_le (iSup_le key)
  calc (∑' i, (f i + g i) ^ p) ^ p⁻¹
      ≤ ((A + B) ^ p) ^ p⁻¹ := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = A + B := by rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]

/-- **Minkowski's inequality at `p = 2` for `tsum`**, the instance the Hilbert--Schmidt
energy uses.  Stated separately because its consumers carry the `^ 2` in `ℕ`-power form. -/
theorem tsum_sq_add_rpow_le (f g : ι → ℝ≥0∞) :
    (∑' i, (f i + g i) ^ 2) ^ (2 : ℝ)⁻¹ ≤
      (∑' i, f i ^ 2) ^ (2 : ℝ)⁻¹ + (∑' i, g i ^ 2) ^ (2 : ℝ)⁻¹ := by
  simpa only [← ENNReal.rpow_two] using tsum_rpow_add_le (p := 2) one_le_two f g

end ENNReal

namespace TauCeti

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The index set of `TauCeti.chosenHilbertBasis`: a choice of Hilbert basis of `E`, used to
give the Hilbert--Schmidt norm a definition that mentions no basis.  Nothing depends on
*which* basis this is — every statement about it is proved from
`ContinuousLinearMap.hilbertSchmidtEnergy_indep`. -/
noncomputable def chosenHilbertBasisSet (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : Set E :=
  Classical.choose (exists_hilbertBasis 𝕜 E)

/-- A choice of Hilbert basis of `E`, indexed by `TauCeti.chosenHilbertBasisSet`. -/
noncomputable def chosenHilbertBasis (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    HilbertBasis (chosenHilbertBasisSet 𝕜 E) 𝕜 E :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis 𝕜 E))

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {ι : Type*}

/-- The **Hilbert--Schmidt norm** of `T`, valued in `ℝ≥0∞` and therefore defined for every
bounded operator: it is `∞` exactly when `T` is not Hilbert--Schmidt. -/
noncomputable def hilbertSchmidtENorm (T : E →L[𝕜] F) : ℝ≥0∞ :=
  (T.hilbertSchmidtEnergy (TauCeti.chosenHilbertBasis 𝕜 E)) ^ (2 : ℝ)⁻¹

/-- The Hilbert--Schmidt norm computed in *any* Hilbert basis. -/
theorem hilbertSchmidtENorm_eq (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtENorm = (T.hilbertSchmidtEnergy b) ^ (2 : ℝ)⁻¹ := by
  rw [hilbertSchmidtENorm, T.hilbertSchmidtEnergy_indep _ b]

/-- Squaring the Hilbert--Schmidt norm returns the energy. -/
theorem hilbertSchmidtENorm_rpow_two (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtENorm ^ (2 : ℝ) = T.hilbertSchmidtEnergy b := by
  rw [T.hilbertSchmidtENorm_eq b, ← ENNReal.rpow_mul]
  norm_num

/-- Squaring the Hilbert--Schmidt norm returns the energy, natural-power form. -/
theorem hilbertSchmidtENorm_sq (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtENorm ^ 2 = T.hilbertSchmidtEnergy b := by
  rw [← ENNReal.rpow_two, T.hilbertSchmidtENorm_rpow_two b]

omit [CompleteSpace F] in
/-- The zero operator has zero Hilbert--Schmidt norm. -/
@[simp] theorem hilbertSchmidtENorm_zero : (0 : E →L[𝕜] F).hilbertSchmidtENorm = 0 := by
  rw [hilbertSchmidtENorm, hilbertSchmidtEnergy_zero]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

omit [CompleteSpace F] in
/-- The Hilbert--Schmidt norm is unchanged by negation. -/
@[simp] theorem hilbertSchmidtENorm_neg (T : E →L[𝕜] F) :
    (-T).hilbertSchmidtENorm = T.hilbertSchmidtENorm := by
  rw [hilbertSchmidtENorm, hilbertSchmidtENorm, hilbertSchmidtEnergy_neg]

omit [CompleteSpace F] in
/-- The Hilbert--Schmidt norm is absolutely homogeneous, in `ℝ≥0∞`. -/
theorem hilbertSchmidtENorm_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).hilbertSchmidtENorm = ‖c‖ₑ * T.hilbertSchmidtENorm := by
  rw [hilbertSchmidtENorm, hilbertSchmidtENorm, hilbertSchmidtEnergy_smul,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast ‖c‖ₑ 2,
    ← ENNReal.rpow_mul]
  norm_num

/-- **The triangle inequality**, which is Minkowski's inequality at `p = 2`. -/
theorem hilbertSchmidtENorm_add_le (S T : E →L[𝕜] F) :
    (S + T).hilbertSchmidtENorm ≤ S.hilbertSchmidtENorm + T.hilbertSchmidtENorm := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [(S + T).hilbertSchmidtENorm_eq b, S.hilbertSchmidtENorm_eq b, T.hilbertSchmidtENorm_eq b]
  refine le_trans (ENNReal.rpow_le_rpow ?_ (by norm_num)) <|
    ENNReal.tsum_sq_add_rpow_le (fun i => ‖S (b i)‖ₑ) (fun i => ‖T (b i)‖ₑ)
  refine ENNReal.tsum_le_tsum fun i => ?_
  gcongr
  exact enorm_add_le _ _

/-- **The Hilbert--Schmidt norm dominates the operator norm.** -/
theorem enorm_le_hilbertSchmidtENorm (T : E →L[𝕜] F) : ‖T‖ₑ ≤ T.hilbertSchmidtENorm := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  refine opENorm_le_bound _ fun x => ?_
  have hbase : ‖T x‖ₑ ^ (2 : ℝ) ≤ (T.hilbertSchmidtENorm * ‖x‖ₑ) ^ (2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), T.hilbertSchmidtENorm_rpow_two b,
      ENNReal.rpow_two, ENNReal.rpow_two]
    exact T.enorm_apply_sq_le_hilbertSchmidtEnergy_mul b x
  have h2 := ENNReal.rpow_le_rpow hbase (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one, ENNReal.rpow_one] at h2

/-- **Adjoint invariance.** -/
theorem hilbertSchmidtENorm_adjoint (T : E →L[𝕜] F) :
    T.adjoint.hilbertSchmidtENorm = T.hilbertSchmidtENorm := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨v, c, -⟩ := exists_hilbertBasis 𝕜 F
  rw [T.adjoint.hilbertSchmidtENorm_eq c, T.hilbertSchmidtENorm_eq b,
    ← T.hilbertSchmidtEnergy_adjoint b c]

/-- Postcomposition contracts the Hilbert--Schmidt norm. -/
theorem hilbertSchmidtENorm_comp_left_le (A : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (A ∘L T).hilbertSchmidtENorm ≤ ‖A‖ₑ * T.hilbertSchmidtENorm := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hsplit : ‖A‖ₑ * (T.hilbertSchmidtEnergy b) ^ (2 : ℝ)⁻¹
      = (‖A‖ₑ ^ 2 * T.hilbertSchmidtEnergy b) ^ (2 : ℝ)⁻¹ := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
  rw [(A ∘L T).hilbertSchmidtENorm_eq b, T.hilbertSchmidtENorm_eq b, hsplit]
  exact ENNReal.rpow_le_rpow (hilbertSchmidtEnergy_comp_left_le A T b) (by norm_num)

/-- Precomposition contracts the Hilbert--Schmidt norm. -/
theorem hilbertSchmidtENorm_comp_right_le (T : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (T ∘L B).hilbertSchmidtENorm ≤ T.hilbertSchmidtENorm * ‖B‖ₑ := by
  have h := ContinuousLinearMap.hilbertSchmidtENorm_comp_left_le B.adjoint T.adjoint
  rw [← ContinuousLinearMap.adjoint_comp, hilbertSchmidtENorm_adjoint,
    hilbertSchmidtENorm_adjoint, B.enorm_adjoint] at h
  rwa [mul_comm]

/-- `T` is a **Hilbert--Schmidt operator** when its Hilbert--Schmidt norm is finite.

The predicate is stated through the `ℝ≥0∞`-valued norm rather than through a summability
hypothesis so that it carries no choice of basis; `isHilbertSchmidt_iff_summable` recovers
the concrete form. -/
def IsHilbertSchmidt (T : E →L[𝕜] F) : Prop := T.hilbertSchmidtENorm ≠ ∞

/-- An operator is Hilbert--Schmidt exactly when its energy is finite; this is the bridge between
the predicate and the summability condition that is actually checked. -/
theorem isHilbertSchmidt_iff_energy_ne_top (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.IsHilbertSchmidt ↔ T.hilbertSchmidtEnergy b ≠ ∞ := by
  rw [IsHilbertSchmidt, T.hilbertSchmidtENorm_eq b, Ne, Ne,
    ENNReal.rpow_eq_top_iff_of_pos (by norm_num)]

/-- Concretely, `T` is Hilbert--Schmidt exactly when the squared column norms are
summable in any — equivalently, some — Hilbert basis. -/
theorem isHilbertSchmidt_iff_summable (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.IsHilbertSchmidt ↔ Summable fun i => ‖T (b i)‖ ^ 2 := by
  rw [T.isHilbertSchmidt_iff_energy_ne_top b, hilbertSchmidtEnergy]
  have hcoe : ∀ i, ‖T (b i)‖ₑ ^ 2 = ((‖T (b i)‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := fun i => by
    simp [enorm_eq_nnnorm]
  simp only [hcoe]
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp

/-- **The two-sided ideal bound.** -/
theorem hilbertSchmidtENorm_comp_le (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) :
    (L ∘L T ∘L R).hilbertSchmidtENorm ≤ ‖L‖ₑ * T.hilbertSchmidtENorm * ‖R‖ₑ := by
  refine ((L ∘L T).hilbertSchmidtENorm_comp_right_le R).trans ?_
  gcongr
  exact L.hilbertSchmidtENorm_comp_left_le T

/-! ### Closure properties of the class

The Hilbert--Schmidt operators form a self-adjoint two-sided ideal, and each of the
closure facts below is the corresponding `hilbertSchmidtENorm` estimate read as a
finiteness statement.  Nothing here needs a basis, a choice, or spectral theory: the
`ℝ≥0∞`-valued norm already carries all of it.
-/

omit [CompleteSpace F] in
/-- The zero operator is Hilbert--Schmidt. -/
@[simp] theorem isHilbertSchmidt_zero : (0 : E →L[𝕜] F).IsHilbertSchmidt := by
  simp [IsHilbertSchmidt]

omit [CompleteSpace F] in
/-- Negation does not change the class. -/
@[simp] theorem isHilbertSchmidt_neg_iff (T : E →L[𝕜] F) :
    (-T).IsHilbertSchmidt ↔ T.IsHilbertSchmidt := by
  rw [IsHilbertSchmidt, IsHilbertSchmidt, hilbertSchmidtENorm_neg]

omit [CompleteSpace F] in
/-- A scalar multiple of a Hilbert--Schmidt operator is Hilbert--Schmidt. -/
theorem IsHilbertSchmidt.smul {T : E →L[𝕜] F} (hT : T.IsHilbertSchmidt) (c : 𝕜) :
    (c • T).IsHilbertSchmidt := by
  rw [IsHilbertSchmidt, hilbertSchmidtENorm_smul]
  exact ENNReal.mul_ne_top (by simp) hT

omit [CompleteSpace F] in
/-- Scaling by a nonzero scalar does not change the class. -/
theorem isHilbertSchmidt_smul_iff {c : 𝕜} (hc : c ≠ 0) (T : E →L[𝕜] F) :
    (c • T).IsHilbertSchmidt ↔ T.IsHilbertSchmidt := by
  refine ⟨fun h => ?_, fun h => h.smul c⟩
  have := h.smul c⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- **The class is closed under addition**, by the triangle inequality. -/
theorem IsHilbertSchmidt.add {S T : E →L[𝕜] F}
    (hS : S.IsHilbertSchmidt) (hT : T.IsHilbertSchmidt) : (S + T).IsHilbertSchmidt :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hS, hT⟩) (hilbertSchmidtENorm_add_le S T)

/-- **The class is closed under subtraction.** -/
theorem IsHilbertSchmidt.sub {S T : E →L[𝕜] F}
    (hS : S.IsHilbertSchmidt) (hT : T.IsHilbertSchmidt) : (S - T).IsHilbertSchmidt := by
  rw [sub_eq_add_neg]
  exact hS.add ((isHilbertSchmidt_neg_iff T).2 hT)

/-- **The class is self-adjoint.** -/
@[simp] theorem isHilbertSchmidt_adjoint_iff (T : E →L[𝕜] F) :
    T.adjoint.IsHilbertSchmidt ↔ T.IsHilbertSchmidt := by
  rw [IsHilbertSchmidt, IsHilbertSchmidt, hilbertSchmidtENorm_adjoint]

/-- Postcomposition with a bounded operator stays in the class. -/
theorem IsHilbertSchmidt.comp_left {T : E →L[𝕜] F} (hT : T.IsHilbertSchmidt)
    (A : F →L[𝕜] G) : (A ∘L T).IsHilbertSchmidt :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hT)
    (hilbertSchmidtENorm_comp_left_le A T)

/-- Precomposition with a bounded operator stays in the class. -/
theorem IsHilbertSchmidt.comp_right {T : F →L[𝕜] G} (hT : T.IsHilbertSchmidt)
    (B : E →L[𝕜] F) : (T ∘L B).IsHilbertSchmidt :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hT (by simp))
    (hilbertSchmidtENorm_comp_right_le T B)

/-- **The two-sided ideal property**, as a statement about the class. -/
theorem IsHilbertSchmidt.comp {T : E →L[𝕜] F} (hT : T.IsHilbertSchmidt)
    (L : F →L[𝕜] G) (R : H →L[𝕜] E) : (L ∘L T ∘L R).IsHilbertSchmidt :=
  (hT.comp_left L).comp_right R

/-- **Every operator out of a finite-dimensional space is Hilbert--Schmidt**: the column
sum has finitely many terms.  This is the entry point a finite-dimensional argument needs,
and it is why the finite-dimensional theory never has to mention the class at all. -/
theorem isHilbertSchmidt_of_finiteDimensional [FiniteDimensional 𝕜 E] (T : E →L[𝕜] F) :
    T.IsHilbertSchmidt :=
  (T.isHilbertSchmidt_iff_summable
    (stdOrthonormalBasis 𝕜 E).toHilbertBasis).2 (summable_of_hasFiniteSupport (Set.toFinite _))

/-- **Fatou for the Hilbert--Schmidt gauge.**  The gauge is lower semicontinuous along
operator-norm convergence: if `T i → T` pointwise on a basis, the limit's energy is at most
the `liminf` of the energies.

This is the step that replaces the Ky Fan shortcut.  `kyFanIdealFamily` gets completeness
from `‖A‖ ≤ kyFanGauge k A ≤ k ‖A‖`, so a gauge-Cauchy sequence is norm-Cauchy *and* the
norm limit is automatically a gauge limit.  The Hilbert--Schmidt gauge is not equivalent to
the operator norm, so the second half fails and the limit has to be controlled term by term
instead -- which is Fatou's lemma in the shape a `tsum` of `ℝ≥0∞` already provides.

The proof is by finite sections rather than through `MeasureTheory.lintegral_liminf_le`
against the counting measure.  The two are the same argument, but the measure route obliges
the *basis index type* to carry `MeasurableSpace`, `MeasurableSingletonClass` and
`DiscreteMeasurableSpace`, and the filter to be countably generated, none of which the
statement is about; `∑'` over `ℝ≥0∞` is already a supremum of finite partial sums, so the
same Fatou step is `Filter.liminf_le_liminf` on each section. -/
theorem hilbertSchmidtENorm_le_liminf {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    {u : Filter ℕ} [u.NeBot]
    {T : ℕ → E →L[𝕜] F} {L : E →L[𝕜] F}
    (hptwise : ∀ i, Filter.Tendsto (fun n => ‖T n (b i)‖ₑ ^ 2) u
      (nhds (‖L (b i)‖ₑ ^ 2))) :
    L.hilbertSchmidtENorm ^ (2 : ℝ) ≤
      Filter.liminf (fun n => (T n).hilbertSchmidtENorm ^ (2 : ℝ)) u := by
  classical
  have hT : ∀ n, (T n).hilbertSchmidtENorm ^ (2 : ℝ) = ∑' i, ‖T n (b i)‖ₑ ^ 2 :=
    fun n => (T n).hilbertSchmidtENorm_rpow_two b
  rw [L.hilbertSchmidtENorm_rpow_two b, L.hilbertSchmidtEnergy_eq_iSup_sum b]
  refine iSup_le fun s => ?_
  have hfin : Filter.Tendsto (fun n => ∑ i ∈ s, ‖T n (b i)‖ₑ ^ 2) u
      (nhds (∑ i ∈ s, ‖L (b i)‖ₑ ^ 2)) :=
    tendsto_finsetSum _ fun i _ => hptwise i
  calc ∑ i ∈ s, ‖L (b i)‖ₑ ^ 2
      = Filter.liminf (fun n => ∑ i ∈ s, ‖T n (b i)‖ₑ ^ 2) u := hfin.liminf_eq.symm
    _ ≤ Filter.liminf (fun n => (T n).hilbertSchmidtENorm ^ (2 : ℝ)) u :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => by
          rw [hT n]; exact ENNReal.sum_le_tsum s)


/-! ### The real-valued norm

The gauge of an operator ideal is `ℝ≥0∞`-valued, because a gauge has to be defined on
operators outside the ideal.  An estimate *inside* the ideal is an inequality between real
numbers, and stating it in `ℝ≥0∞` forces every consumer to carry finiteness through
arithmetic that does not need it.  So the ideal keeps the extended norm and this is its
real-valued reading, defined on all operators and equal to zero off the ideal.

The two are interchangeable exactly where it matters: `ofReal_hilbertSchmidtNorm` turns a
real statement into the extended one for a Hilbert--Schmidt operator, and
`hilbertSchmidtNorm_eq_toReal` is the definition. -/

/-- The real-valued Hilbert--Schmidt norm.  Zero off the ideal. -/
@[expose]
noncomputable def hilbertSchmidtNorm (T : E →L[𝕜] F) : ℝ := T.hilbertSchmidtENorm.toReal

omit [CompleteSpace F] in
/-- The real norm is the extended one read in `ℝ`; this is the definition. -/
theorem hilbertSchmidtNorm_eq_toReal (T : E →L[𝕜] F) :
    T.hilbertSchmidtNorm = T.hilbertSchmidtENorm.toReal := by
  rw [hilbertSchmidtNorm]

omit [CompleteSpace F] in
/-- On the ideal, the real norm determines the extended one. -/
theorem ofReal_hilbertSchmidtNorm {T : E →L[𝕜] F} (hT : T.IsHilbertSchmidt) :
    ENNReal.ofReal T.hilbertSchmidtNorm = T.hilbertSchmidtENorm :=
  ENNReal.ofReal_toReal hT

omit [CompleteSpace F] in
/-- The real Hilbert--Schmidt norm is nonnegative, on and off the ideal. -/
@[simp] theorem hilbertSchmidtNorm_nonneg (T : E →L[𝕜] F) : 0 ≤ T.hilbertSchmidtNorm :=
  ENNReal.toReal_nonneg

omit [CompleteSpace F] in
/-- The zero operator has zero real Hilbert--Schmidt norm. -/
@[simp] theorem hilbertSchmidtNorm_zero : (0 : E →L[𝕜] F).hilbertSchmidtNorm = 0 := by
  simp [hilbertSchmidtNorm]

omit [CompleteSpace F] in
/-- The real Hilbert--Schmidt norm is unchanged by negation. -/
@[simp] theorem hilbertSchmidtNorm_neg (T : E →L[𝕜] F) :
    (-T).hilbertSchmidtNorm = T.hilbertSchmidtNorm := by
  simp [hilbertSchmidtNorm]

omit [CompleteSpace F] in
/-- **Absolute homogeneity**, in `ℝ`.  No finiteness is needed: both sides are `0`
off the ideal, and `‖c‖ * 0 = 0`. -/
theorem hilbertSchmidtNorm_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).hilbertSchmidtNorm = ‖c‖ * T.hilbertSchmidtNorm := by
  rw [hilbertSchmidtNorm, hilbertSchmidtENorm_smul, ENNReal.toReal_mul,
    hilbertSchmidtNorm, enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm]

/-- **Adjoint invariance**, in `ℝ`. -/
theorem hilbertSchmidtNorm_adjoint (T : E →L[𝕜] F) :
    T.adjoint.hilbertSchmidtNorm = T.hilbertSchmidtNorm := by
  rw [hilbertSchmidtNorm, hilbertSchmidtNorm, hilbertSchmidtENorm_adjoint]

/-- **The triangle inequality**, in `ℝ`, for two Hilbert--Schmidt operators.  Finiteness
is needed: `ENNReal.toReal` sends `∞` to `0`, so the inequality is false without it. -/
theorem hilbertSchmidtNorm_add_le {S T : E →L[𝕜] F}
    (hS : S.IsHilbertSchmidt) (hT : T.IsHilbertSchmidt) :
    (S + T).hilbertSchmidtNorm ≤ S.hilbertSchmidtNorm + T.hilbertSchmidtNorm := by
  rw [hilbertSchmidtNorm, hilbertSchmidtNorm, hilbertSchmidtNorm,
    ← ENNReal.toReal_add hS hT]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hS, hT⟩) (hilbertSchmidtENorm_add_le S T)

/-- **The two-sided ideal bound**, in `ℝ`. -/
theorem hilbertSchmidtNorm_comp_le (L : F →L[𝕜] G) {T : E →L[𝕜] F}
    (hT : T.IsHilbertSchmidt) (R : H →L[𝕜] E) :
    (L ∘L T ∘L R).hilbertSchmidtNorm ≤ ‖L‖ * T.hilbertSchmidtNorm * ‖R‖ := by
  have hfin : ‖L‖ₑ * T.hilbertSchmidtENorm * ‖R‖ₑ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hT) (by simp)
  have h := ENNReal.toReal_mono hfin (hilbertSchmidtENorm_comp_le L T R)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, enorm_eq_nnnorm, enorm_eq_nnnorm,
    ENNReal.coe_toReal, ENNReal.coe_toReal, coe_nnnorm, coe_nnnorm] at h

/-- **Contractions do not enlarge the Hilbert--Schmidt norm.**  This is the
two-sided ideal bound with both factors of norm at most one. -/
theorem hilbertSchmidtNorm_comp_isometries_le (L : F →L[𝕜] G) {T : E →L[𝕜] F}
    (hT : T.IsHilbertSchmidt) (R : H →L[𝕜] E) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    (L ∘L T ∘L R).hilbertSchmidtNorm ≤ T.hilbertSchmidtNorm := by
  calc (L ∘L T ∘L R).hilbertSchmidtNorm
      ≤ ‖L‖ * T.hilbertSchmidtNorm * ‖R‖ := hilbertSchmidtNorm_comp_le L hT R
    _ ≤ 1 * T.hilbertSchmidtNorm * 1 := by
        gcongr <;> simp [hilbertSchmidtNorm_nonneg T]
    _ = T.hilbertSchmidtNorm := by ring

/-- **The Hilbert--Schmidt norm dominates the operator norm**, in `ℝ`. -/
theorem norm_le_hilbertSchmidtNorm {T : E →L[𝕜] F} (hT : T.IsHilbertSchmidt) :
    ‖T‖ ≤ T.hilbertSchmidtNorm := by
  have h := ENNReal.toReal_mono hT (enorm_le_hilbertSchmidtENorm T)
  rwa [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm] at h


end ContinuousLinearMap

namespace TauCeti

universe u v

/-- **The Hilbert--Schmidt operator ideal.**

This is the second instance of `TauCeti.SymmetricOperatorIdealFamily`, after the Ky Fan
families of `DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean`.  The two are
built from unrelated mathematics — approximation numbers there, orthonormal expansions here
— which is the evidence that the structure captures the right notion. -/
@[expose]
noncomputable def hilbertSchmidtIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge A := A.hilbertSchmidtENorm
  gauge_add_le A B := A.hilbertSchmidtENorm_add_le B
  gauge_smul c A := A.hilbertSchmidtENorm_smul c
  enorm_le_gauge A := A.enorm_le_hilbertSchmidtENorm
  gauge_comp_le L A R := ContinuousLinearMap.hilbertSchmidtENorm_comp_le L A R
  gauge_adjoint A := A.hilbertSchmidtENorm_adjoint

/-- **The Hilbert--Schmidt ideal is complete.**

The `kyFanIdealFamily` route is unavailable here -- that one gets completeness from
`‖A‖ ≤ kyFanGauge k A ≤ k ‖A‖`, so its gauge limit *is* its operator-norm limit -- and the
Hilbert--Schmidt gauge is not equivalent to the operator norm.  What replaces it is
`ContinuousLinearMap.hilbertSchmidtENorm_le_liminf`: take the operator-norm limit, which
exists because the gauge dominates the operator norm, then bound its energy, and the energy
of each difference, by the `liminf` along the sequence. -/
instance isComplete_hilbertSchmidtIdealFamily {𝕜 : Type u} [RCLike 𝕜] :
    (hilbertSchmidtIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    -- the gauge dominates the operator norm, so the sequence is Cauchy there too
    have hop : CauchySeq fun n => (a n).val :=
      TauCeti.OperatorIdealFamily.Elem.cauchySeq_val ha
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hop
    obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 E
    classical
    -- pointwise, on each basis vector, the differences converge to the difference of limits
    have hpt : ∀ (n : ℕ) (i : s),
        Filter.Tendsto (fun m => ‖((a m).val - (a n).val) (b i)‖ₑ ^ 2) Filter.atTop
          (nhds (‖(L - (a n).val) (b i)‖ₑ ^ 2)) := by
      intro n i
      have h1 : Filter.Tendsto (fun m => ((a m).val - (a n).val) (b i)) Filter.atTop
          (nhds ((L - (a n).val) (b i))) := by
        simpa using
          ((ContinuousLinearMap.apply 𝕜 F (b i)).continuous.tendsto L).comp hL |>.sub
            tendsto_const_nhds
      exact (ENNReal.continuous_pow 2).tendsto _ |>.comp ((continuous_enorm.tendsto _).comp h1)
    -- Fatou: the limit's energy is controlled by the tail of the Cauchy estimate
    have hfatou : ∀ n : ℕ,
        (L - (a n).val).hilbertSchmidtENorm ^ (2 : ℝ) ≤
          Filter.liminf (fun m => ((a m).val - (a n).val).hilbertSchmidtENorm ^ (2 : ℝ))
            Filter.atTop :=
      fun n => ContinuousLinearMap.hilbertSchmidtENorm_le_liminf b (hpt n)
    -- the Cauchy estimate, transported from the ideal norm to the gauge
    have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        (L - (a n).val).hilbertSchmidtENorm ≤ ENNReal.ofReal ε := by
      intro ε hε
      rw [Metric.cauchySeq_iff] at ha
      obtain ⟨N, hN⟩ := ha ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hev : ∀ᶠ m in Filter.atTop,
          ((a m).val - (a n).val).hilbertSchmidtENorm ^ (2 : ℝ)
            ≤ ENNReal.ofReal ε ^ (2 : ℝ) := by
        filter_upwards [Filter.eventually_ge_atTop N] with m hm
        have hd : ‖a m - a n‖ < ε := by simpa [dist_eq_norm] using hN m hm n hn
        have hgauge : ((a m).val - (a n).val).hilbertSchmidtENorm ≤ ENNReal.ofReal ε := by
          have heq : (hilbertSchmidtIdealFamily.{u, v} 𝕜).gauge (a m - a n).val
              = ((a m).val - (a n).val).hilbertSchmidtENorm := rfl
          rw [← heq, ← TauCeti.OperatorIdealFamily.Elem.enorm_eq_gauge, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hd.le
        exact ENNReal.rpow_le_rpow hgauge (by norm_num)
      have hle : Filter.liminf
          (fun m => ((a m).val - (a n).val).hilbertSchmidtENorm ^ (2 : ℝ))
          Filter.atTop ≤ ENNReal.ofReal ε ^ (2 : ℝ) := by
        calc Filter.liminf
              (fun m => ((a m).val - (a n).val).hilbertSchmidtENorm ^ (2 : ℝ)) Filter.atTop
            ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal ε ^ (2 : ℝ)) Filter.atTop :=
              Filter.liminf_le_liminf hev
          _ = ENNReal.ofReal ε ^ (2 : ℝ) := Filter.liminf_const _
      have h2 := (hfatou n).trans hle
      have hpow : (0 : ℝ) < 2 := by norm_num
      exact (ENNReal.rpow_le_rpow_iff hpow).mp h2
    -- the limit lies in the ideal: it differs from a member by something of finite gauge
    obtain ⟨N₁, hN₁⟩ := hcauchy 1 one_pos
    have hmemL : L ∈ (hilbertSchmidtIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.carrier := by
      have hsplit : L = (L - (a N₁).val) + (a N₁).val := by abel
      rw [TauCeti.OperatorIdealFamily.mem_carrier_iff, hsplit]
      refine ne_top_of_le_ne_top ?_
        ((hilbertSchmidtIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.gauge_add_le _ _)
      refine ENNReal.add_ne_top.mpr ⟨?_, (a N₁).gauge_val_ne_top⟩
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hN₁ N₁ le_rfl)
    refine ⟨TauCeti.OperatorIdealFamily.Elem.mk hmemL, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hgauge : ((a n).val - L).hilbertSchmidtENorm ≤ ENNReal.ofReal (ε / 2) := by
      have hneg : ((a n).val - L) = -(L - (a n).val) := by abel
      rw [hneg, ContinuousLinearMap.hilbertSchmidtENorm_neg]
      exact hN n hn
    have hle : ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ ≤ ε / 2 := by
      have hne : ((a n).val - L).hilbertSchmidtENorm ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgauge
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgauge
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    calc dist (a n) (TauCeti.OperatorIdealFamily.Elem.mk hmemL)
        = ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ := dist_eq_norm _ _
      _ ≤ ε / 2 := hle
      _ < ε := by linarith

/-- Membership in the Hilbert--Schmidt ideal is exactly `IsHilbertSchmidt`. -/
theorem mem_hilbertSchmidtIdealFamily_carrier_iff {𝕜 : Type u} [RCLike 𝕜] {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (A : E →L[𝕜] F) :
    A ∈ (hilbertSchmidtIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.carrier ↔
      A.IsHilbertSchmidt := (Iff.rfl)
/-- The gauge of the Hilbert--Schmidt family is the Hilbert--Schmidt norm. -/
@[simp] theorem hilbertSchmidtIdealFamily_gauge {𝕜 : Type u} [RCLike 𝕜] {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (A : E →L[𝕜] F) :
    (hilbertSchmidtIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.gauge A =
      A.hilbertSchmidtENorm := (rfl)

end TauCeti
