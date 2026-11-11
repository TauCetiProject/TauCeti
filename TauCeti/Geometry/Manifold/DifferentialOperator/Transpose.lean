/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The formal transpose of a differential operator

Let `E` be a finite-dimensional real normed space with a measure `μ`. A linear operator `D'` on
the algebra `C^∞(E)` of smooth real functions is a *formal transpose* of `D` with respect to `μ`
(`LinearMap.IsFormalTranspose`) when

`∫ (D f) g dμ = ∫ f (D' g) dμ`

for all smooth `f` and `g` one of which has compact support. This is the operator through which
`D` acts on distributions, `⟨D T, φ⟩ = ⟨T, D' φ⟩`, and it depends on the density `μ`: with respect
to a weighted measure it differs from the transpose for the unweighted one.

When `μ` is an additive Haar measure, every differential operator `D` of order at most `m`, in
Grothendieck's sense of iterated commutators with multiplication operators
(`TauCeti.differentialOperators`), has a formal transpose of order at most `m`, the same for every
Haar measure. In coordinates, with `D f = ∑_{|α| ≤ m} c_α ∂^α f`, it is the operator

`Dᵗ g = ∑_{|α| ≤ m} (-1) ^ |α| ∂^α (c_α g)`

(`LinearMap.isFormalTranspose_coordinateOperator`): integration by parts moves each directional
derivative `∂_v` to the other factor as `-∂_v` (`LinearMap.isFormalTranspose_lineDerivation`).
Since continuous functions are determined by their integrals against compactly supported smooth
functions, the formal transpose is unique whenever `μ` is locally finite and positive on open sets
(`LinearMap.IsFormalTranspose.unique`). On differential operators, `LinearMap.formalTranspose` is
therefore linear, involutive and reverses compositions.

## Main definitions

* `LinearMap.IsFormalTranspose D D' μ`: `D'` is a formal transpose of `D` with respect to `μ`.
* `LinearMap.formalTranspose D μ`: the formal transpose of `D`, if it has one, and `0` otherwise.

## Main results

* `LinearMap.IsFormalTranspose.unique`: uniqueness of formal transposes.
* `LinearMap.isFormalTranspose_lineDerivation`: the formal transpose of `∂_v` is `-∂_v`.
* `LinearMap.isFormalTranspose_multiIndexDeriv`,
  `LinearMap.isFormalTranspose_coordinateOperator`, `LinearMap.formalTranspose_multiIndexDeriv`,
  `LinearMap.formalTranspose_coordinateOperator`: the formal transposes of `∂^α` and of a
  coordinate expression.
* `LinearMap.isFormalTranspose_formalTranspose`,
  `LinearMap.formalTranspose_mem_differentialOperators`: a differential operator of order at most
  `m` has a formal transpose with respect to an additive Haar measure, again of order at most `m`;
  by `LinearMap.formalTranspose_eq_of_isAddHaarMeasure` it does not depend on the Haar measure.
* `LinearMap.formalTranspose_formalTranspose`, `LinearMap.formalTranspose_comp`,
  `LinearMap.formalTranspose_add`, `LinearMap.formalTranspose_smul`,
  `LinearMap.formalTranspose_sum`: the formal transpose is a linear involution of the
  differential operators that reverses compositions.
* `LinearMap.formalTranspose_mulLeft_comp_lineDerivation`: the formal transpose of `c ∂_v` is
  `-c ∂_v - (∂_v c)`, not just `-c ∂_v`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §§3.1 and 6.1 (formal transposes of differential operators).
-/

public section

noncomputable section

open MeasureTheory Finset Function TauCeti
open scoped ContDiff Manifold

namespace ContMDiffMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- The product of two smooth functions, one of which has compact support, is integrable. -/
theorem integrable_mul_of_hasCompactSupport {f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) : Integrable (fun x ↦ f x * g x) μ :=
  (f.contMDiff.continuous.mul g.contMDiff.continuous).integrable_of_hasCompactSupport
    (hfg.elim (·.mul_right) (·.mul_left))

end ContMDiffMap

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- A linear operator `D'` on `C^∞(E)` is a *formal transpose* of `D` with respect to the measure
`μ` if `∫ (D f) g dμ = ∫ f (D' g) dμ` for all smooth functions `f` and `g` one of which has compact
support. -/
def IsFormalTranspose (D D' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (μ : Measure E) :
    Prop :=
  ∀ f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport f ∨ HasCompactSupport g →
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ

open Classical in
/-- The formal transpose of a linear operator `D` on `C^∞(E)` with respect to the measure `μ`: an
operator `D'` with `∫ (D f) g dμ = ∫ f (D' g) dμ` whenever `f` or `g` has compact support
(`LinearMap.IsFormalTranspose`), if there is one, and `0` otherwise. For an additive Haar measure
every differential operator has a formal transpose, and it is unique
(`LinearMap.isFormalTranspose_formalTranspose`, `LinearMap.IsFormalTranspose.formalTranspose_eq`).
-/
def formalTranspose (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (μ : Measure E) :
    C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯ :=
  if h : ∃ D', D.IsFormalTranspose D' μ then h.choose else 0

variable {D D' D₁ D₂ D₁' D₂' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {μ : Measure E}

omit [MeasurableSpace E] in
/-- An operator on `C^∞(E)` that does not enlarge supports preserves compact support. -/
theorem _root_.HasCompactSupport.apply_of_tsupport_subset
    (hD : ∀ f, tsupport (D f) ⊆ tsupport f) {f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hf : HasCompactSupport f) :
    HasCompactSupport (D f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (hD f)

/-! ### The algebra of formal transposes -/

/-- Formal transposition is symmetric: if `D'` is a formal transpose of `D`, then `D` is one of
`D'`. -/
theorem IsFormalTranspose.symm (h : D.IsFormalTranspose D' μ) : D'.IsFormalTranspose D μ := by
  intro f g hfg
  calc ∫ x, D' f x * g x ∂μ = ∫ x, D g x * f x ∂μ := by
        simp_rw [mul_comm _ (g _)]; exact (h g f hfg.symm).symm
    _ = ∫ x, f x * D g x ∂μ := by simp_rw [mul_comm (D g _)]

theorem isFormalTranspose_comm : D.IsFormalTranspose D' μ ↔ D'.IsFormalTranspose D μ :=
  ⟨.symm, .symm⟩

/-- The zero operator is its own formal transpose, for every measure. -/
protected theorem IsFormalTranspose.zero :
    (0 : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose 0 μ :=
  fun _ _ _ ↦ by simp

/-- The identity is its own formal transpose, for every measure. -/
protected theorem IsFormalTranspose.one :
    (1 : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose 1 μ :=
  fun _ _ _ ↦ rfl

/-- Formal transposes are compatible with scalar multiplication. -/
theorem IsFormalTranspose.smul (h : D.IsFormalTranspose D' μ) (c : ℝ) :
    (c • D).IsFormalTranspose (c • D') μ := by
  intro f g hfg
  simp only [LinearMap.smul_apply, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc, mul_left_comm (f _) c]
  rw [integral_const_mul, integral_const_mul, h f g hfg]

/-- Formal transposes are compatible with negation. -/
theorem IsFormalTranspose.neg (h : D.IsFormalTranspose D' μ) :
    (-D).IsFormalTranspose (-D') μ := by
  intro f g hfg
  simp only [LinearMap.neg_apply, ContMDiffMap.coe_neg, Pi.neg_apply, neg_mul, mul_neg,
    integral_neg, h f g hfg]

/-- The formal transpose of a composition is the composition of the formal transposes in the
reverse order, provided the inner operator and the transpose of the outer one do not enlarge
supports. -/
theorem IsFormalTranspose.comp (h₁ : D₁.IsFormalTranspose D₁' μ)
    (h₂ : D₂.IsFormalTranspose D₂' μ) (hD₂ : ∀ f, tsupport (D₂ f) ⊆ tsupport f)
    (hD₁' : ∀ g, tsupport (D₁' g) ⊆ tsupport g) :
    (D₁ ∘ₗ D₂).IsFormalTranspose (D₂' ∘ₗ D₁') μ := by
  intro f g hfg
  calc ∫ x, (D₁ ∘ₗ D₂) f x * g x ∂μ = ∫ x, D₂ f x * D₁' g x ∂μ :=
        h₁ _ _ (hfg.imp (·.apply_of_tsupport_subset hD₂) _root_.id)
    _ = ∫ x, f x * (D₂' ∘ₗ D₁') g x ∂μ :=
        h₂ _ _ (hfg.imp _root_.id (·.apply_of_tsupport_subset hD₁'))

section Integrable

variable [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]

private theorem integrable_apply_mul (hD : ∀ f, tsupport (D f) ⊆ tsupport f)
    {f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    Integrable (fun x ↦ D f x * g x) μ :=
  ContMDiffMap.integrable_mul_of_hasCompactSupport
    (hfg.imp (·.apply_of_tsupport_subset hD) _root_.id)

private theorem integrable_mul_apply (hD : ∀ f, tsupport (D f) ⊆ tsupport f)
    {f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    Integrable (fun x ↦ f x * D g x) μ :=
  ContMDiffMap.integrable_mul_of_hasCompactSupport
    (hfg.imp _root_.id (·.apply_of_tsupport_subset hD))

/-- Formal transposes of operators that do not enlarge supports add. -/
theorem IsFormalTranspose.add (h₁ : D₁.IsFormalTranspose D₁' μ)
    (h₂ : D₂.IsFormalTranspose D₂' μ) (hD₁ : ∀ f, tsupport (D₁ f) ⊆ tsupport f)
    (hD₂ : ∀ f, tsupport (D₂ f) ⊆ tsupport f) (hD₁' : ∀ g, tsupport (D₁' g) ⊆ tsupport g)
    (hD₂' : ∀ g, tsupport (D₂' g) ⊆ tsupport g) :
    (D₁ + D₂).IsFormalTranspose (D₁' + D₂') μ := by
  intro f g hfg
  simp only [LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply, add_mul, mul_add]
  rw [integral_add (integrable_apply_mul hD₁ hfg) (integrable_apply_mul hD₂ hfg),
    integral_add (integrable_mul_apply hD₁' hfg) (integrable_mul_apply hD₂' hfg), h₁ f g hfg,
    h₂ f g hfg]

/-- Formal transposes of operators that do not enlarge supports subtract. -/
theorem IsFormalTranspose.sub (h₁ : D₁.IsFormalTranspose D₁' μ)
    (h₂ : D₂.IsFormalTranspose D₂' μ) (hD₁ : ∀ f, tsupport (D₁ f) ⊆ tsupport f)
    (hD₂ : ∀ f, tsupport (D₂ f) ⊆ tsupport f) (hD₁' : ∀ g, tsupport (D₁' g) ⊆ tsupport g)
    (hD₂' : ∀ g, tsupport (D₂' g) ⊆ tsupport g) :
    (D₁ - D₂).IsFormalTranspose (D₁' - D₂') μ := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h₁.add h₂.neg hD₁ (fun f ↦ by simpa using hD₂ f) hD₁' (fun g ↦ by simpa using hD₂' g)

/-- Formal transposes of operators that do not enlarge supports add. -/
theorem IsFormalTranspose.sum {ι : Type*} (s : Finset ι)
    {D D' : ι → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h : ∀ i ∈ s, (D i).IsFormalTranspose (D' i) μ)
    (hD : ∀ i ∈ s, ∀ f, tsupport (D i f) ⊆ tsupport f)
    (hD' : ∀ i ∈ s, ∀ g, tsupport (D' i g) ⊆ tsupport g) :
    (∑ i ∈ s, D i).IsFormalTranspose (∑ i ∈ s, D' i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun f g _ ↦ by simp
  | insert i s hi ih =>
    simp only [Finset.forall_mem_insert] at h hD hD'
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact h.1.add (ih h.2 hD.2 hD'.2) hD.1 (tsupport_sum_apply_subset s hD.2) hD'.1
      (tsupport_sum_apply_subset s hD'.2)

end Integrable

/-! ### Uniqueness -/

section Unique

variable [FiniteDimensional ℝ E] [BorelSpace E] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- **Uniqueness of formal transposes.** With respect to a locally finite measure that is positive
on open sets, a linear operator on `C^∞(E)` has at most one formal transpose. -/
theorem IsFormalTranspose.unique (h₁ : D.IsFormalTranspose D₁ μ) (h₂ : D.IsFormalTranspose D₂ μ) :
    D₁ = D₂ := by
  ext g x
  have key : ∀ᵐ x ∂μ, D₁ g x = D₂ g x := by
    refine ae_eq_of_integral_contDiff_smul_eq (D₁ g).contMDiff.continuous.locallyIntegrable
      (D₂ g).contMDiff.continuous.locallyIntegrable fun φ hφ hφc ↦ ?_
    let f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ := ⟨φ, hφ.contMDiff⟩
    have hf : HasCompactSupport f := hφc
    simpa [f, smul_eq_mul] using (h₁ f g (.inl hf)).symm.trans (h₂ f g (.inl hf))
  exact congrFun ((Continuous.ae_eq_iff_eq μ (D₁ g).contMDiff.continuous
    (D₂ g).contMDiff.continuous).1 key) x

/-- A formal transpose of `D` is `LinearMap.formalTranspose D μ`. -/
theorem IsFormalTranspose.formalTranspose_eq (h : D.IsFormalTranspose D' μ) :
    D.formalTranspose μ = D' := by
  have hex : ∃ D', D.IsFormalTranspose D' μ := ⟨D', h⟩
  simp only [formalTranspose, hex, ↓reduceDIte]
  exact hex.choose_spec.unique h

/-- The formal transpose of the zero operator is zero. -/
@[simp]
theorem formalTranspose_zero :
    (0 : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).formalTranspose μ = 0 :=
  IsFormalTranspose.zero.formalTranspose_eq

/-- The identity is its own formal transpose. -/
@[simp]
theorem formalTranspose_one : (1 : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯).formalTranspose μ = 1 :=
  IsFormalTranspose.one.formalTranspose_eq

/-- Formal transposition commutes with negation. -/
@[simp]
theorem formalTranspose_neg : (-D).formalTranspose μ = -D.formalTranspose μ := by
  by_cases h : ∃ D', D.IsFormalTranspose D' μ
  · obtain ⟨D', h⟩ := h
    rw [h.formalTranspose_eq, h.neg.formalTranspose_eq]
  · have h' : ¬∃ D', (-D).IsFormalTranspose D' μ := fun ⟨D', hD'⟩ ↦
      h ⟨-D', by simpa using hD'.neg⟩
    simp [formalTranspose, h, h']

/-- Formal transposition commutes with scalar multiplication. -/
@[simp]
theorem formalTranspose_smul (c : ℝ) : (c • D).formalTranspose μ = c • D.formalTranspose μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases h : ∃ D', D.IsFormalTranspose D' μ
  · obtain ⟨D', h⟩ := h
    rw [h.formalTranspose_eq, (h.smul c).formalTranspose_eq]
  · have h' : ¬∃ D', (c • D).IsFormalTranspose D' μ := fun ⟨D', hD'⟩ ↦
      h ⟨c⁻¹ • D', by simpa [smul_smul, hc] using hD'.smul c⁻¹⟩
    simp [formalTranspose, h, h']

end Unique

/-- If `D` has a formal transpose, then `LinearMap.formalTranspose D μ` is one. -/
theorem IsFormalTranspose.isFormalTranspose_formalTranspose (h : D.IsFormalTranspose D' μ) :
    D.IsFormalTranspose (D.formalTranspose μ) μ := by
  have hex : ∃ D', D.IsFormalTranspose D' μ := ⟨D', h⟩
  simp only [formalTranspose, hex, ↓reduceDIte]
  exact hex.choose_spec

/-! ### Directional derivatives and multiplication operators -/

/-- **Integration by parts.** With respect to an additive Haar measure, the formal transpose of
the directional derivative `∂_v` is `-∂_v`. -/
theorem isFormalTranspose_lineDerivation [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] (v : E) :
    (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose
      (-(lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)) μ := by
  intro f g hfg
  have hd (h : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : Differentiable ℝ h :=
    h.contMDiff.contDiff.differentiable (by simp)
  have hs := tsupport_lineDerivation_apply_subset (𝕜 := ℝ) v
  have hint := ContMDiffMap.integrable_mul_of_hasCompactSupport (μ := μ)
    (f := lineDerivation ℝ v f) (g := g) (hfg.imp (·.apply_of_tsupport_subset hs) _root_.id)
  have hint' := ContMDiffMap.integrable_mul_of_hasCompactSupport (μ := μ)
    (f := f) (g := lineDerivation ℝ v g) (hfg.imp _root_.id (·.apply_of_tsupport_subset hs))
  simp only [LinearMap.neg_apply, Derivation.coeFn_coe, ContMDiffMap.coe_neg, Pi.neg_apply,
    lineDerivation_apply_apply, mul_neg, integral_neg] at hint hint' ⊢
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint hint'
    (ContMDiffMap.integrable_mul_of_hasCompactSupport hfg) (fun x _ ↦ hd f x)
    (fun x _ ↦ hd g x), neg_neg]

/-- Multiplication by a smooth function is its own formal transpose, for every measure. -/
theorem isFormalTranspose_mulLeft (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    (mulLeft ℝ c).IsFormalTranspose (mulLeft ℝ c) μ := by
  intro f g _
  simp only [mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply]
  congr 1 with x
  ring

/-- Multiplication by a smooth function is its own formal transpose. -/
@[simp]
theorem formalTranspose_mulLeft [FiniteDimensional ℝ E] [BorelSpace E] [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    (mulLeft ℝ c).formalTranspose μ = mulLeft ℝ c :=
  (isFormalTranspose_mulLeft c).formalTranspose_eq

/-! ### Coordinate expressions -/

section Coordinates

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι]
  (v : ι → E)

/-- The formal transpose of the monomial `∂^α` in directional derivatives is `(-1) ^ |α| ∂^α`,
with respect to an additive Haar measure. -/
theorem isFormalTranspose_multiIndexDeriv (α : ι → ℕ) :
    (multiIndexDeriv (fun i ↦ lineDerivation ℝ (v i))
        (fun i j ↦ commute_lineDerivation (v i) (v j)) α).IsFormalTranspose
      ((-1 : ℝ) ^ (∑ i, α i) • multiIndexDeriv (fun i ↦ lineDerivation ℝ (v i))
        (fun i j ↦ commute_lineDerivation (v i) (v j)) α) μ := by
  classical
  induction α using multiIndex_induction_add_single with
  | zero => simpa using IsFormalTranspose.one (μ := μ)
  | add_single α i ih =>
    have h := ih.comp (isFormalTranspose_lineDerivation (μ := μ) (v i))
      (tsupport_lineDerivation_apply_subset (v i))
      (tsupport_smul_apply_subset (tsupport_multiIndexDeriv_apply_subset v α) _)
    have hsign : (-1 : ℝ) ^ ∑ j, (α + Pi.single i 1 : ι → ℕ) j = -(-1) ^ ∑ j, α j := by
      simp [Finset.sum_add_distrib, pow_succ]
    rw [LinearMap.neg_comp, LinearMap.comp_smul, ← Module.End.mul_eq_comp,
      ← Module.End.mul_eq_comp, ← multiIndexDeriv_add_single,
      ← multiIndexDeriv_add_single' (fun i ↦ lineDerivation ℝ (v i))] at h
    convert h using 1
    rw [hsign]
    exact neg_smul (M := Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) _ _

/-- The formal transpose of the monomial `∂^α` in directional derivatives is `(-1) ^ |α| ∂^α`,
with respect to an additive Haar measure. -/
@[simp]
theorem formalTranspose_multiIndexDeriv (α : ι → ℕ) :
    (multiIndexDeriv (fun i ↦ lineDerivation ℝ (v i))
        (fun i j ↦ commute_lineDerivation (v i) (v j)) α).formalTranspose μ =
      (-1 : ℝ) ^ (∑ i, α i) • multiIndexDeriv (fun i ↦ lineDerivation ℝ (v i))
        (fun i j ↦ commute_lineDerivation (v i) (v j)) α :=
  (isFormalTranspose_multiIndexDeriv v α).formalTranspose_eq

/-- The formal transpose of the coordinate expression `f ↦ ∑_{|α| ≤ m} c_α ∂^α f` in directional
derivatives is `g ↦ ∑_{|α| ≤ m} (-1) ^ |α| ∂^α (c_α g)`, with respect to an additive Haar
measure. -/
theorem isFormalTranspose_coordinateOperator [DecidableEq ι] (m : ℕ)
    (c : (ι → ℕ) → C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    (coordinateOperator (fun i ↦ lineDerivation ℝ (v i))
        (fun i j ↦ commute_lineDerivation (v i) (v j)) m c).IsFormalTranspose
      (∑ k ∈ Finset.range (m + 1), ∑ α ∈ piAntidiag univ k,
        (-1 : ℝ) ^ k • (multiIndexDeriv (fun i ↦ lineDerivation ℝ (v i))
          (fun i j ↦ commute_lineDerivation (v i) (v j)) α ∘ₗ mulLeft ℝ (c α))) μ := by
  rw [coordinateOperator_eq_sum_mulLeft]
  have hmul (a : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
      tsupport (mulLeft ℝ a f) ⊆ tsupport f :=
    tsupport_mulLeft_apply_subset a f
  have hterm (α : ι → ℕ) : ∀ f, tsupport ((mulLeft ℝ (c α) ∘ₗ
      multiIndexDeriv (fun i ↦ lineDerivation ℝ (v i))
        (fun i j ↦ commute_lineDerivation (v i) (v j)) α) f) ⊆ tsupport f :=
    fun f ↦ (hmul _ _).trans (tsupport_multiIndexDeriv_apply_subset v α f)
  have hterm' (k : ℕ) (α : ι → ℕ) : ∀ g, tsupport (((-1 : ℝ) ^ k •
      (multiIndexDeriv (fun i ↦ lineDerivation ℝ (v i))
        (fun i j ↦ commute_lineDerivation (v i) (v j)) α ∘ₗ mulLeft ℝ (c α))) g) ⊆
      tsupport g :=
    tsupport_smul_apply_subset (fun g ↦ (tsupport_multiIndexDeriv_apply_subset v α
      (mulLeft ℝ (c α) g)).trans (hmul _ g)) _
  refine IsFormalTranspose.sum _ (fun k _ ↦ IsFormalTranspose.sum _ (fun α hα ↦ ?_)
    (fun α _ ↦ hterm α) (fun α _ ↦ hterm' k α))
    (fun k _ ↦ tsupport_sum_apply_subset _ fun α _ ↦ hterm α)
    (fun k _ ↦ tsupport_sum_apply_subset _ fun α _ ↦ hterm' k α)
  rw [mem_piAntidiag] at hα
  have h := (isFormalTranspose_mulLeft (μ := μ) (c α)).comp
    (isFormalTranspose_multiIndexDeriv (μ := μ) v α)
    (tsupport_multiIndexDeriv_apply_subset v α) (hmul _)
  rwa [hα.1, LinearMap.smul_comp] at h

/-- The formal transpose of the coordinate expression `f ↦ ∑_{|α| ≤ m} c_α ∂^α f` in directional
derivatives is `g ↦ ∑_{|α| ≤ m} (-1) ^ |α| ∂^α (c_α g)`, with respect to an additive Haar
measure. -/
theorem formalTranspose_coordinateOperator [DecidableEq ι] (m : ℕ)
    (c : (ι → ℕ) → C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    (coordinateOperator (fun i ↦ lineDerivation ℝ (v i))
        (fun i j ↦ commute_lineDerivation (v i) (v j)) m c).formalTranspose μ =
      ∑ k ∈ Finset.range (m + 1), ∑ α ∈ piAntidiag univ k,
        (-1 : ℝ) ^ k • (multiIndexDeriv (fun i ↦ lineDerivation ℝ (v i))
          (fun i j ↦ commute_lineDerivation (v i) (v j)) α ∘ₗ mulLeft ℝ (c α)) :=
  (isFormalTranspose_coordinateOperator v m c).formalTranspose_eq

end Coordinates

/-! ### The formal transpose of a differential operator -/

section DifferentialOperator

variable [FiniteDimensional ℝ E] [BorelSpace E] {m k : ℕ}

/-- **Existence of formal transposes.** A differential operator of order at most `m` on `C^∞(E)`
has a formal transpose of order at most `m`, the same for every additive Haar measure. -/
theorem exists_isFormalTranspose_of_mem_differentialOperators
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    ∃ D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m,
      ∀ (μ : Measure E) [μ.IsAddHaarMeasure], D.IsFormalTranspose D' μ := by
  set b := Module.finBasis ℝ E
  set c := coordinateCoeff b.smoothCoord D
  refine ⟨_, sum_neg_one_pow_smul_multiIndexDeriv_comp_mulLeft_mem_differentialOperators
    (fun i ↦ lineDerivation ℝ (b i)) (fun i j ↦ commute_lineDerivation (b i) (b j)) m c,
    fun μ _ ↦ ?_⟩
  have h := isFormalTranspose_coordinateOperator (μ := μ) b m c
  rwa [← b.eq_coordinateOperator_coordinateCoeff hD] at h

variable (μ : Measure E) [μ.IsAddHaarMeasure]
  (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
    C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m)
include hD

/-- With respect to an additive Haar measure, `LinearMap.formalTranspose D μ` is a formal
transpose of a differential operator `D`. -/
theorem isFormalTranspose_formalTranspose : D.IsFormalTranspose (D.formalTranspose μ) μ := by
  obtain ⟨D', -, h⟩ := exists_isFormalTranspose_of_mem_differentialOperators hD
  exact (h μ).isFormalTranspose_formalTranspose

/-- The formal transpose of a differential operator of order at most `m` is a differential
operator of order at most `m`. -/
theorem formalTranspose_mem_differentialOperators :
    D.formalTranspose μ ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m := by
  obtain ⟨D', hD', h⟩ := exists_isFormalTranspose_of_mem_differentialOperators hD
  exact (h μ).formalTranspose_eq ▸ hD'

/-- The formal transpose of a differential operator does not enlarge supports. -/
theorem tsupport_formalTranspose_apply_subset (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    tsupport (D.formalTranspose μ g) ⊆ tsupport g :=
  tsupport_apply_subset_of_mem_differentialOperators
    (formalTranspose_mem_differentialOperators μ hD) g

/-- The formal transpose of a differential operator is the same for every additive Haar
measure. -/
theorem formalTranspose_eq_of_isAddHaarMeasure (ν : Measure E) [ν.IsAddHaarMeasure] :
    D.formalTranspose μ = D.formalTranspose ν := by
  obtain ⟨D', -, h⟩ := exists_isFormalTranspose_of_mem_differentialOperators hD
  rw [(h μ).formalTranspose_eq, (h ν).formalTranspose_eq]

/-- The formal transpose is an involution on differential operators. -/
theorem formalTranspose_formalTranspose : (D.formalTranspose μ).formalTranspose μ = D :=
  (isFormalTranspose_formalTranspose μ hD).symm.formalTranspose_eq

/-- The formal transpose of a sum of differential operators is the sum of their formal
transposes. -/
theorem formalTranspose_add
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (D + D').formalTranspose μ = D.formalTranspose μ + D'.formalTranspose μ :=
  ((isFormalTranspose_formalTranspose μ hD).add (isFormalTranspose_formalTranspose μ hD')
    (tsupport_apply_subset_of_mem_differentialOperators hD)
    (tsupport_apply_subset_of_mem_differentialOperators hD')
    (tsupport_formalTranspose_apply_subset μ hD)
    (tsupport_formalTranspose_apply_subset μ hD')).formalTranspose_eq

/-- The formal transpose of a difference of differential operators is the difference of their
formal transposes. -/
theorem formalTranspose_sub
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (D - D').formalTranspose μ = D.formalTranspose μ - D'.formalTranspose μ :=
  ((isFormalTranspose_formalTranspose μ hD).sub (isFormalTranspose_formalTranspose μ hD')
    (tsupport_apply_subset_of_mem_differentialOperators hD)
    (tsupport_apply_subset_of_mem_differentialOperators hD')
    (tsupport_formalTranspose_apply_subset μ hD)
    (tsupport_formalTranspose_apply_subset μ hD')).formalTranspose_eq

/-- The formal transpose of a composition of differential operators is the composition of their
formal transposes in the reverse order. -/
theorem formalTranspose_comp
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (D ∘ₗ D').formalTranspose μ = D'.formalTranspose μ ∘ₗ D.formalTranspose μ :=
  ((isFormalTranspose_formalTranspose μ hD).comp (isFormalTranspose_formalTranspose μ hD')
    (tsupport_apply_subset_of_mem_differentialOperators hD')
    (tsupport_formalTranspose_apply_subset μ hD)).formalTranspose_eq

end DifferentialOperator

/-- The formal transpose of a finite sum of differential operators is the sum of their formal
transposes. -/
theorem formalTranspose_sum [FiniteDimensional ℝ E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {ι : Type*} (s : Finset ι)
    {D : ι → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {m : ι → ℕ}
    (hD : ∀ i ∈ s, D i ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ (m i)) :
    (∑ i ∈ s, D i).formalTranspose μ = ∑ i ∈ s, (D i).formalTranspose μ :=
  (IsFormalTranspose.sum s (fun i hi ↦ isFormalTranspose_formalTranspose μ (hD i hi))
    (fun i hi ↦ tsupport_apply_subset_of_mem_differentialOperators (hD i hi))
    (fun i hi ↦ tsupport_formalTranspose_apply_subset μ (hD i hi))).formalTranspose_eq

section Examples

variable [FiniteDimensional ℝ E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The formal transpose of the directional derivative `∂_v` is `-∂_v`. -/
@[simp]
theorem formalTranspose_lineDerivation (v : E) :
    (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).formalTranspose μ =
      -(lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :=
  (isFormalTranspose_lineDerivation v).formalTranspose_eq

/-- The formal transpose of the first-order operator `c ∂_v` is `-c ∂_v - (∂_v c)`: integration
by parts also differentiates the coefficient. -/
theorem formalTranspose_mulLeft_comp_lineDerivation (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (v : E) :
    (mulLeft ℝ c ∘ₗ
        (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)).formalTranspose μ =
      -(mulLeft ℝ c ∘ₗ (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)) -
        mulLeft ℝ (lineDerivation ℝ v c) := by
  refine IsFormalTranspose.formalTranspose_eq ?_
  convert (isFormalTranspose_mulLeft c).comp (isFormalTranspose_lineDerivation (μ := μ) v)
    (tsupport_lineDerivation_apply_subset v) (fun g ↦ ?_) using 1
  · ext g x
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  · exact tsupport_mulLeft_apply_subset c g

end Examples

end LinearMap
