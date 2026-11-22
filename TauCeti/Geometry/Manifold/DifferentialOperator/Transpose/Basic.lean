/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
public import TauCeti.Geometry.Manifold.ContMDiffMap.Integrable
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Algebra.BigOperators.Pi
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# The formal transpose of a differential operator

Let `μ` be a measure on a manifold `M`. A linear operator `D'` on the algebra `C^∞(M)` of smooth
real functions is a *formal transpose* of `D` with respect to `μ` (`LinearMap.IsFormalTranspose`)
when

`∫ (D f) g dμ = ∫ f (D' g) dμ`

for all smooth `f` and `g` one of which has compact support. This is the operator through which
`D` acts on distributions, `⟨D T, φ⟩ = ⟨T, D' φ⟩`, and it depends on the density `μ`: with respect
to a weighted measure it differs from the transpose for the unweighted one. For real functions the
transpose is also the formal adjoint for the `L²(μ)` inner product.

Since continuous functions are determined by their integrals against compactly supported smooth
functions, the formal transpose is unique whenever `μ` is locally finite and positive on open sets
of a Hausdorff σ-compact manifold (`LinearMap.IsFormalTranspose.unique`), and
`LinearMap.formalTranspose` picks it.

Differential operators are taken in Grothendieck's sense (`TauCeti.differentialOperators`):
operators all of whose `(m + 1)`-fold commutators with multiplication operators vanish. They are
local and do not enlarge supports, which makes formal transposes of differential operators reverse
compositions. Multiplication operators are their own transposes, so
the transpose of a commutator `[D, a]` is `-[D', a]`; hence the `m`-fold commutators of a transpose
`D'` are `(-1) ^ m` times those of `D`, and a formal transpose of a differential operator of order
at most `m` that is a differential operator has order at most `m`, and on a boundaryless manifold
its principal symbol is `ξ ↦ (-1) ^ m σ(ξ)`.

On a finite-dimensional real vector space `E` with an additive Haar measure, every differential
operator `D` of order at most `m` has a formal transpose of order at most `m`, the same for every
Haar measure. In coordinates, with `D f = ∑_{|α| ≤ m} c_α ∂^α f`, it is the operator

`Dᵗ g = ∑_{|α| ≤ m} (-1) ^ |α| ∂^α (c_α g)`

(`LinearMap.isFormalTranspose_coordinateOperator`): integration by parts moves each directional
derivative `∂_v` to the other factor as `-∂_v` (`LinearMap.isFormalTranspose_lineDerivation`).
On differential operators, `LinearMap.formalTranspose` is therefore linear, involutive and reverses
compositions.

## Main definitions

* `LinearMap.IsFormalTranspose D D' μ`: `D'` is a formal transpose of `D` with respect to `μ`.
* `LinearMap.formalTranspose D μ`: the formal transpose of `D`, if it has one, and `0` otherwise.

## Main results

* `LinearMap.IsFormalTranspose.unique`: uniqueness of formal transposes.
* `LinearMap.isFormalTranspose_self_of_mem_differentialOperators_zero`: operators of order zero,
  that is multiplication operators, are their own transposes.
* `LinearMap.IsFormalTranspose.smulCommutator`: the transpose of `[D, a]` is `-[D', a]`.
* `LinearMap.IsFormalTranspose.withDensity`: if `D'` is a transpose of `D` with respect to `μ`,
  `ρ ≥ 0` is smooth and `ρ D'' g = D' (ρ g)` for all `g`, then `D''` is a transpose of `D` with
  respect to the weighted measure `ρ μ` (for `ρ > 0`, `D'' g = ρ⁻¹ D' (ρ g)`).
* `LinearMap.IsFormalTranspose.mem_differentialOperators`: a formal transpose of a differential
  operator of order at most `m` that is a differential operator has order at most `m`.
* `LinearMap.IsFormalTranspose.smoothPrincipalSymbol_eq`: on a boundaryless manifold, its principal
  symbol is `(-1) ^ m` times that of the operator.
* `LinearMap.IsFormalTranspose.mem_differentialOperators_of_neg_one_pow_smul`,
  `LinearMap.IsFormalTranspose.mem_differentialOperators_two_mul_of_self`: if `(-1) ^ m D` is a
  formal transpose of an operator `D` of order at most `m + 1`, then `D` has order at most `m`; in
  particular a formally self-adjoint operator of order at most `2 k + 1` has order at most `2 k`.
* `LinearMap.isFormalTranspose_lineDerivation`: the formal transpose of `∂_v` is `-∂_v`.
* `LinearMap.isFormalTranspose_multiIndexDeriv`,
  `LinearMap.isFormalTranspose_coordinateOperator`, `LinearMap.formalTranspose_multiIndexDeriv`,
  `LinearMap.formalTranspose_coordinateOperator`: the formal transposes of `∂^α` and of a
  coordinate expression.
* `LinearMap.isFormalTranspose_formalTranspose`,
  `LinearMap.formalTranspose_mem_differentialOperators`: a differential operator of order at most
  `m` has a formal transpose with respect to an additive Haar measure, again of order at most `m`;
  by `LinearMap.formalTranspose_eq_of_isAddHaarMeasure` it does not depend on the Haar measure.
* `LinearMap.formalTranspose_eq_iff`,
  `LinearMap.integral_apply_mul_eq_integral_mul_formalTranspose_apply`: on differential operators,
  `LinearMap.formalTranspose` is characterized by integration by parts.
* `LinearMap.formalTranspose_formalTranspose`, `LinearMap.formalTranspose_comp`,
  `LinearMap.formalTranspose_pow`, `LinearMap.formalTranspose_add`,
  `LinearMap.formalTranspose_smul`, `LinearMap.formalTranspose_sum`: the formal transpose is a
  linear involution of the differential operators that reverses compositions.
* `LinearMap.formalTranspose_mulLeft_comp_lineDerivation`: the formal transpose of `c ∂_v` is
  `-c ∂_v - (∂_v c)`, not just `-c ∂_v`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §§3.1 and 6.1 (formal transposes of differential operators).
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

noncomputable section

open MeasureTheory Finset Function TauCeti
open scoped ContDiff Manifold

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Manifold

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]

/-- A linear operator `D'` on `C^∞(M)` is a *formal transpose* of `D` with respect to the measure
`μ` if `∫ (D f) g dμ = ∫ f (D' g) dμ` for all smooth functions `f` and `g` one of which has compact
support. -/
def IsFormalTranspose (D D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) (μ : Measure M) :
    Prop :=
  ∀ f g : C^∞⟮I, M; ℝ⟯, HasCompactSupport f ∨ HasCompactSupport g →
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ

open Classical in
/-- The formal transpose of a linear operator `D` on `C^∞(M)` with respect to the measure `μ`: an
operator `D'` with `∫ (D f) g dμ = ∫ f (D' g) dμ` whenever `f` or `g` has compact support
(`LinearMap.IsFormalTranspose`), if there is one, and `0` otherwise. For an additive Haar measure on
a vector space every differential operator has a formal transpose, and it is unique
(`LinearMap.isFormalTranspose_formalTranspose`, `LinearMap.IsFormalTranspose.formalTranspose_eq`).
-/
def formalTranspose (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) (μ : Measure M) :
    C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  if h : ∃ D', D.IsFormalTranspose D' μ then h.choose else 0

variable {D D' D₁ D₂ D₁' D₂' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯} {μ : Measure M}

/-- Unfolding `LinearMap.IsFormalTranspose`: `D'` is a formal transpose of `D` if and only if
`∫ (D f) g dμ = ∫ f (D' g) dμ` whenever `f` or `g` has compact support. -/
theorem isFormalTranspose_iff : D.IsFormalTranspose D' μ ↔
    ∀ f g : C^∞⟮I, M; ℝ⟯, HasCompactSupport f ∨ HasCompactSupport g →
      ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ :=
  Iff.rfl

/-- Integration by parts against a formal transpose: if `D'` is a formal transpose of `D`, then
`∫ (D f) g dμ = ∫ f (D' g) dμ` whenever `f` or `g` has compact support. -/
theorem IsFormalTranspose.integral_mul_eq (h : D.IsFormalTranspose D' μ)
    {f g : C^∞⟮I, M; ℝ⟯} (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ :=
  h f g hfg

/-- An operator without a formal transpose has formal transpose `0` by convention. -/
theorem formalTranspose_eq_zero_of_not_exists (h : ¬∃ D', D.IsFormalTranspose D' μ) :
    D.formalTranspose μ = 0 := by
  simp [formalTranspose, h]

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
    (0 : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose 0 μ :=
  fun _ _ _ ↦ by simp

/-- The identity is its own formal transpose, for every measure. -/
protected theorem IsFormalTranspose.one :
    (1 : Module.End ℝ C^∞⟮I, M; ℝ⟯).IsFormalTranspose 1 μ :=
  fun _ _ _ ↦ rfl

/-- The identity is its own formal transpose, for every measure. -/
protected theorem IsFormalTranspose.id :
    (LinearMap.id : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose LinearMap.id μ :=
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
        h₁ _ _ (hfg.imp (·.mono' ((subset_tsupport _).trans (hD₂ f))) _root_.id)
    _ = ∫ x, f x * (D₂' ∘ₗ D₁') g x ∂μ :=
        h₂ _ _ (hfg.imp _root_.id (·.mono' ((subset_tsupport _).trans (hD₁' g))))

/-- The formal transpose of a power is the power of the formal transpose, provided both do not
enlarge supports. -/
theorem IsFormalTranspose.pow (h : D.IsFormalTranspose D' μ)
    (hD : ∀ f, tsupport (D f) ⊆ tsupport f) (hD' : ∀ g, tsupport (D' g) ⊆ tsupport g) (n : ℕ) :
    (D ^ n).IsFormalTranspose (D' ^ n) μ := by
  have hpow (n : ℕ) (g : C^∞⟮I, M; ℝ⟯) : tsupport ((D' ^ n) g) ⊆ tsupport g := by
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp]
      exact (ih _).trans (hD' g)
  induction n with
  | zero => exact IsFormalTranspose.one
  | succ n ih =>
    rw [pow_succ, pow_succ']
    exact ih.comp h hD (hpow n)

section Integrable

variable [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]

/-- Formal transposes of operators that do not enlarge supports add. -/
theorem IsFormalTranspose.add (h₁ : D₁.IsFormalTranspose D₁' μ)
    (h₂ : D₂.IsFormalTranspose D₂' μ) (hD₁ : ∀ f, tsupport (D₁ f) ⊆ tsupport f)
    (hD₂ : ∀ f, tsupport (D₂ f) ⊆ tsupport f) (hD₁' : ∀ g, tsupport (D₁' g) ⊆ tsupport g)
    (hD₂' : ∀ g, tsupport (D₂' g) ⊆ tsupport g) :
    (D₁ + D₂).IsFormalTranspose (D₁' + D₂') μ := by
  intro f g hfg
  simp only [LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply, add_mul, mul_add]
  rw [integral_add (ContMDiffMap.integrable_apply_mul_of_tsupport_subset hD₁ hfg)
      (ContMDiffMap.integrable_apply_mul_of_tsupport_subset hD₂ hfg),
    integral_add (ContMDiffMap.integrable_mul_apply_of_tsupport_subset hD₁' hfg)
      (ContMDiffMap.integrable_mul_apply_of_tsupport_subset hD₂' hfg), h₁ f g hfg, h₂ f g hfg]

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
    {D D' : ι → C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
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

/-- Multiplication by a smooth function is its own formal transpose, for every measure. -/
theorem isFormalTranspose_mulLeft (c : C^∞⟮I, M; ℝ⟯) :
    (mulLeft ℝ c).IsFormalTranspose (mulLeft ℝ c) μ := by
  intro f g _
  simp only [mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply]
  congr 1 with x
  ring

/-- An operator of order zero on `C^∞(M)`, that is a multiplication operator, is its own formal
transpose. -/
theorem isFormalTranspose_self_of_mem_differentialOperators_zero
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 0) :
    D.IsFormalTranspose D μ := by
  have hD1 : D = mulLeft ℝ (D 1) := LinearMap.ext fun f ↦ by
    simpa [mul_comm] using mem_differentialOperators_zero_iff.1 hD f 1
  rw [hD1]
  exact isFormalTranspose_mulLeft _

/-! ### Change of density -/

/-- **Change of density.** Let `D'` be a formal transpose of `D` with respect to `μ`, and let
`ρ ≥ 0` be smooth. An operator `D''` with `ρ D'' g = D' (ρ g)` for every `g` is a formal transpose
of `D` with respect to the weighted measure `ρ μ`. For `ρ > 0` this says `D'' g = ρ⁻¹ D' (ρ g)`. -/
theorem IsFormalTranspose.withDensity [OpensMeasurableSpace M] (h : D.IsFormalTranspose D' μ)
    {D'' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯} {ρ : C^∞⟮I, M; ℝ⟯} (hρ : ∀ x, 0 ≤ ρ x)
    (hD'' : ∀ g, ρ * D'' g = D' (ρ * g)) :
    D.IsFormalTranspose D'' (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x)) := by
  intro f g hfg
  have hρm : Measurable fun x ↦ ENNReal.ofReal (ρ x) :=
    ENNReal.measurable_ofReal.comp ρ.contMDiff.continuous.measurable
  have hρt : ∀ᵐ x ∂μ, ENNReal.ofReal (ρ x) < ⊤ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  simp only [integral_withDensity_eq_integral_toReal_smul hρm hρt, ENNReal.toReal_ofReal (hρ _),
    smul_eq_mul]
  have hρg : HasCompactSupport f ∨ HasCompactSupport (ρ * g) :=
    hfg.imp _root_.id fun hg ↦ by simpa only [ContMDiffMap.coe_mul] using hg.mul_left
  calc ∫ x, ρ x * (D f x * g x) ∂μ = ∫ x, D f x * (ρ * g) x ∂μ := by
        congr 1 with x
        simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
        ring
    _ = ∫ x, f x * D' (ρ * g) x ∂μ := h f _ hρg
    _ = ∫ x, ρ x * (f x * D'' g x) ∂μ := by
        congr 1 with x
        rw [← hD'']
        simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
        ring

/-! ### Uniqueness -/

section Unique

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [BorelSpace M]
  [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- **Uniqueness of formal transposes.** With respect to a locally finite measure that is positive
on open sets of a Hausdorff σ-compact manifold, a linear operator on `C^∞(M)` has at most one formal
transpose. -/
theorem IsFormalTranspose.unique (h₁ : D.IsFormalTranspose D₁ μ) (h₂ : D.IsFormalTranspose D₂ μ) :
    D₁ = D₂ := by
  ext g x
  -- A continuous function whose integrals against all compactly supported smooth functions vanish
  -- is zero.
  have hcont : Continuous fun y ↦ D₁ g y - D₂ g y :=
    (D₁ g).contMDiff.continuous.sub (D₂ g).contMDiff.continuous
  have hae : ∀ᵐ y ∂μ, D₁ g y - D₂ g y = 0 := by
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hcont.locallyIntegrable
      fun φ hφ hφc ↦ ?_
    have hφg := (h₁ ⟨φ, hφ⟩ g (.inl hφc)).symm.trans (h₂ ⟨φ, hφ⟩ g (.inl hφc))
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub, sub_eq_zero]
    · exact hφg
    all_goals exact (hφ.continuous.mul (ContMDiffMap.contMDiff _).continuous)
      |>.integrable_of_hasCompactSupport hφc.mul_right
  exact sub_eq_zero.1 (congr_fun ((hcont.ae_eq_iff_eq μ continuous_const).1 hae) x)

/-- A formal transpose of `D` is `LinearMap.formalTranspose D μ`. -/
theorem IsFormalTranspose.formalTranspose_eq (h : D.IsFormalTranspose D' μ) :
    D.formalTranspose μ = D' := by
  have hex : ∃ D', D.IsFormalTranspose D' μ := ⟨D', h⟩
  simp only [formalTranspose, hex, ↓reduceDIte]
  exact hex.choose_spec.unique h

/-- If `D` has a formal transpose `D'`, then `LinearMap.formalTranspose D μ` is characterized as
the formal transpose of `D`. -/
theorem IsFormalTranspose.formalTranspose_eq_iff (h : D.IsFormalTranspose D' μ) :
    D.formalTranspose μ = D₁ ↔ D.IsFormalTranspose D₁ μ := by
  rw [h.formalTranspose_eq]
  exact ⟨fun h' ↦ h' ▸ h, h.unique⟩

/-- If `D` has a formal transpose, then transposing twice gives back `D`. -/
theorem IsFormalTranspose.formalTranspose_formalTranspose (h : D.IsFormalTranspose D' μ) :
    (D.formalTranspose μ).formalTranspose μ = D := by
  rw [h.formalTranspose_eq, h.symm.formalTranspose_eq]

/-- The formal transpose of the zero operator is zero. -/
@[simp]
theorem formalTranspose_zero :
    (0 : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).formalTranspose μ = 0 :=
  IsFormalTranspose.zero.formalTranspose_eq

/-- The identity is its own formal transpose. -/
@[simp]
theorem formalTranspose_one : (1 : Module.End ℝ C^∞⟮I, M; ℝ⟯).formalTranspose μ = 1 :=
  IsFormalTranspose.one.formalTranspose_eq

/-- The identity is its own formal transpose. -/
@[simp]
theorem formalTranspose_id :
    (LinearMap.id : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).formalTranspose μ =
      LinearMap.id :=
  IsFormalTranspose.id.formalTranspose_eq

/-- Formal transposition commutes with negation. -/
@[simp]
theorem formalTranspose_neg : (-D).formalTranspose μ = -D.formalTranspose μ := by
  by_cases h : ∃ D', D.IsFormalTranspose D' μ
  · obtain ⟨D', h⟩ := h
    rw [h.formalTranspose_eq, h.neg.formalTranspose_eq]
  · have h' : ¬∃ D', (-D).IsFormalTranspose D' μ := fun ⟨D', hD'⟩ ↦
      h ⟨-D', by simpa using hD'.neg⟩
    rw [formalTranspose_eq_zero_of_not_exists h, formalTranspose_eq_zero_of_not_exists h',
      neg_zero]

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
    rw [formalTranspose_eq_zero_of_not_exists h, formalTranspose_eq_zero_of_not_exists h',
      smul_zero]

end Unique

/-- If `D` has a formal transpose, then `LinearMap.formalTranspose D μ` is one. -/
theorem IsFormalTranspose.isFormalTranspose_formalTranspose (h : D.IsFormalTranspose D' μ) :
    D.IsFormalTranspose (D.formalTranspose μ) μ := by
  have hex : ∃ D', D.IsFormalTranspose D' μ := ⟨D', h⟩
  simp only [formalTranspose, hex, ↓reduceDIte]
  exact hex.choose_spec

/-- Multiplication by a smooth function is its own formal transpose. -/
@[simp]
theorem formalTranspose_mulLeft [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [BorelSpace M] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (c : C^∞⟮I, M; ℝ⟯) :
    (mulLeft ℝ c).formalTranspose μ = mulLeft ℝ c :=
  (isFormalTranspose_mulLeft c).formalTranspose_eq

/-! ### Differential operators -/

section DifferentialOperator

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]

/-- **The transpose of a commutator.** If `D'` is a formal transpose of `D`, both differential
operators, then `-[D', a]` is a formal transpose of the commutator `[D, a]` with multiplication by
`a`: multiplication operators are their own transposes and transposition reverses compositions. -/
theorem IsFormalTranspose.smulCommutator {k k' : ℕ} (h : D.IsFormalTranspose D' μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k')
    (a : C^∞⟮I, M; ℝ⟯) :
    (TauCeti.smulCommutator ℝ a D).IsFormalTranspose (-TauCeti.smulCommutator ℝ a D') μ := by
  have ha := mulLeft_mem_differentialOperators_zero (R := ℝ) a
  have h' := (h.comp (isFormalTranspose_mulLeft a) (tsupport_differentialOperators_apply_subset ha)
      (tsupport_differentialOperators_apply_subset hD')).sub
    ((isFormalTranspose_mulLeft a).comp h (tsupport_differentialOperators_apply_subset hD)
      (tsupport_differentialOperators_apply_subset ha))
    (tsupport_differentialOperators_apply_subset (comp_mem_differentialOperators hD ha))
    (tsupport_differentialOperators_apply_subset (comp_mem_differentialOperators ha hD))
    (tsupport_differentialOperators_apply_subset (comp_mem_differentialOperators ha hD'))
    (tsupport_differentialOperators_apply_subset (comp_mem_differentialOperators hD' ha))
  convert h' using 1 <;> ext f x <;> simp [sub_eq_neg_add]

/-- The transpose of an iterated commutator: `(-1) ^ j [⋯[D', a], …, a]` is a formal transpose of
`[⋯[D, a], …, a]`, with `j` commutators. -/
theorem IsFormalTranspose.smulCommutator_pow {k k' : ℕ} (h : D.IsFormalTranspose D' μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k')
    (a : C^∞⟮I, M; ℝ⟯) (j : ℕ) :
    ((TauCeti.smulCommutator ℝ a ^ j) D).IsFormalTranspose
      ((-1 : ℝ) ^ j • (TauCeti.smulCommutator ℝ a ^ j) D') μ := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have h' := ih.smulCommutator
      (smulCommutator_pow_mem_differentialOperators (differentialOperators_mono
        (Nat.le_add_right k j) hD) a)
      (Submodule.smul_mem _ _ (smulCommutator_pow_mem_differentialOperators
        (differentialOperators_mono (Nat.le_add_right k' j) hD') a)) a
    rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
    convert h' using 1
    ext f x
    simp [pow_succ]

variable [SigmaCompactSpace M] [BorelSpace M] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- **The order of a formal transpose.** A formal transpose of a differential operator of order at
most `m` that is a differential operator has order at most `m`. -/
theorem IsFormalTranspose.mem_differentialOperators {m k : ℕ} (h : D.IsFormalTranspose D' μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k) :
    D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m := by
  induction m generalizing D D' with
  | zero =>
    rwa [h.unique (isFormalTranspose_self_of_mem_differentialOperators_zero hD)]
  | succ m ih =>
    refine mem_differentialOperators_succ_iff.2 fun a ↦ ?_
    simpa using neg_mem <| ih (h.smulCommutator (differentialOperators_le_succ _ hD) hD' a)
      (smulCommutator_mem_differentialOperators hD a)
      (neg_mem (smulCommutator_mem_differentialOperators (differentialOperators_le_succ _ hD') a))

omit [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ] in
/-- **The parity of a formally symmetric operator.** If `(-1) ^ m D` is a formal transpose of a
differential operator `D` of order at most `m + 1`, then `D` has order at most `m`: the
`(m + 1)`-fold commutators of `D` have order zero, so they are their own transposes, while
transposition multiplies them by `(-1) ^ (m + 1) (-1) ^ m = -1`. For even `m` this says that a
formally self-adjoint operator of odd order `m + 1` has order at most `m`, and for odd `m` that a
formally skew-adjoint operator of even order `m + 1` has order at most `m`. -/
theorem IsFormalTranspose.mem_differentialOperators_of_neg_one_pow_smul {m : ℕ}
    (h : D.IsFormalTranspose ((-1 : ℝ) ^ m • D) μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (m + 1)) :
    D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m := by
  induction m generalizing D with
  | zero =>
    refine mem_differentialOperators_zero_iff_smulCommutator.2 fun a ↦ ?_
    have h' := (h.smulCommutator hD (Submodule.smul_mem _ _ hD) a).unique
      (isFormalTranspose_self_of_mem_differentialOperators_zero
        (smulCommutator_mem_differentialOperators hD a))
    rw [pow_zero, one_smul] at h'
    have h2 : (2 : ℝ) • TauCeti.smulCommutator ℝ a D = 0 := by
      rw [two_smul]
      nth_rw 1 [← h']
      exact neg_add_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  | succ m ih =>
    refine mem_differentialOperators_succ_iff.2 fun a ↦ ih ?_
      (smulCommutator_mem_differentialOperators hD a)
    convert h.smulCommutator hD (Submodule.smul_mem _ _ hD) a using 1
    rw [map_smul, pow_succ, mul_neg_one]
    module

omit [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ] in
/-- **Formally self-adjoint operators have even order.** A formally self-adjoint differential
operator of order at most `2 k + 1` has order at most `2 k`. -/
theorem IsFormalTranspose.mem_differentialOperators_two_mul_of_self {k : ℕ}
    (h : D.IsFormalTranspose D μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (2 * k + 1)) :
    D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (2 * k) :=
  IsFormalTranspose.mem_differentialOperators_of_neg_one_pow_smul (by simpa using h) hD

/-- **The principal symbol of a formal transpose.** On a boundaryless manifold, if `D'` is a formal
transpose of `D`, both differential operators of order at most `m`, then
`σ(D')(ξ) = (-1) ^ m σ(D)(ξ)`. -/
theorem IsFormalTranspose.smoothPrincipalSymbol_eq [BoundarylessManifold I M] {m : ℕ}
    {D D' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m}
    (h : (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose D' μ) {x : M}
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I BoundarylessManifold.isInteriorPoint D' ξ =
      (-1) ^ m * smoothPrincipalSymbol I BoundarylessManifold.isInteriorPoint D ξ := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) ξ
  -- The `m`-fold commutators of `D` and `D'` with `f` have order zero, so they are their own
  -- transposes, and by uniqueness `(-1) ^ m [⋯[D', f], …, f] = [⋯[D, f], …, f]`.
  have hm : ∀ P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m,
      (TauCeti.smulCommutator ℝ f ^ m) (P : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) ∈
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 0 := fun P ↦
    smulCommutator_pow_mem_differentialOperators (by simp) f
  have heq := (h.smulCommutator_pow D.property D'.property f m).unique
    (isFormalTranspose_self_of_mem_differentialOperators_zero (hm D))
  have heq' : (TauCeti.smulCommutator ℝ f ^ m) (D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) =
      (-1 : ℝ) ^ m • (TauCeti.smulCommutator ℝ f ^ m) (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) := by
    rw [← heq, smul_smul, ← mul_pow]
    simp
  rw [smoothPrincipalSymbol_mvfderiv, smoothPrincipalSymbol_mvfderiv, heq']
  simp only [LinearMap.smul_apply, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

end DifferentialOperator

end Manifold

section Euclidean

variable [MeasurableSpace E] {D D' D₁ D₂ D₁' D₂' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
  {μ : Measure E}

/-! ### Directional derivatives -/

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
  have hint := ContMDiffMap.integrable_apply_mul_of_tsupport_subset (μ := μ) hs hfg
  have hint' := ContMDiffMap.integrable_mul_apply_of_tsupport_subset (μ := μ) hs hfg
  simp only [LinearMap.neg_apply, Derivation.coeFn_coe, ContMDiffMap.coe_neg, Pi.neg_apply,
    lineDerivation_apply_apply, mul_neg, integral_neg] at hint hint' ⊢
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint hint'
    (ContMDiffMap.integrable_mul_of_hasCompactSupport hfg) (fun x _ ↦ hd f x)
    (fun x _ ↦ hd g x), neg_neg]

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
  refine ⟨_, sum_smul_multiIndexDeriv_comp_mulLeft_mem_differentialOperators
    (fun i ↦ lineDerivation ℝ (b i)) (fun i j ↦ commute_lineDerivation (b i) (b j)) m
    (fun k ↦ (-1) ^ k) c,
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

/-- On differential operators, `LinearMap.formalTranspose D μ` is characterized as the formal
transpose of `D` with respect to an additive Haar measure. -/
theorem formalTranspose_eq_iff : D.formalTranspose μ = D' ↔ D.IsFormalTranspose D' μ :=
  (isFormalTranspose_formalTranspose μ hD).formalTranspose_eq_iff

/-- **Integration by parts** for a differential operator `D`: `∫ (D f) g dμ = ∫ f (Dᵗ g) dμ`
whenever `f` or `g` has compact support. -/
theorem integral_apply_mul_eq_integral_mul_formalTranspose_apply {f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D.formalTranspose μ g x ∂μ :=
  (isFormalTranspose_formalTranspose μ hD).integral_mul_eq hfg

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
  tsupport_differentialOperators_apply_subset
    (formalTranspose_mem_differentialOperators μ hD) g

/-- The formal transpose of a differential operator is the same for every additive Haar
measure. -/
theorem formalTranspose_eq_of_isAddHaarMeasure (ν : Measure E) [ν.IsAddHaarMeasure] :
    D.formalTranspose μ = D.formalTranspose ν := by
  obtain ⟨D', -, h⟩ := exists_isFormalTranspose_of_mem_differentialOperators hD
  rw [(h μ).formalTranspose_eq, (h ν).formalTranspose_eq]

/-- The formal transpose is an involution on differential operators. -/
theorem formalTranspose_formalTranspose : (D.formalTranspose μ).formalTranspose μ = D :=
  (isFormalTranspose_formalTranspose μ hD).formalTranspose_formalTranspose

/-- The formal transpose of a sum of differential operators is the sum of their formal
transposes. -/
theorem formalTranspose_add
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (D + D').formalTranspose μ = D.formalTranspose μ + D'.formalTranspose μ :=
  ((isFormalTranspose_formalTranspose μ hD).add (isFormalTranspose_formalTranspose μ hD')
    (tsupport_differentialOperators_apply_subset hD)
    (tsupport_differentialOperators_apply_subset hD')
    (tsupport_formalTranspose_apply_subset μ hD)
    (tsupport_formalTranspose_apply_subset μ hD')).formalTranspose_eq

/-- The formal transpose of a difference of differential operators is the difference of their
formal transposes. -/
theorem formalTranspose_sub
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (D - D').formalTranspose μ = D.formalTranspose μ - D'.formalTranspose μ :=
  ((isFormalTranspose_formalTranspose μ hD).sub (isFormalTranspose_formalTranspose μ hD')
    (tsupport_differentialOperators_apply_subset hD)
    (tsupport_differentialOperators_apply_subset hD')
    (tsupport_formalTranspose_apply_subset μ hD)
    (tsupport_formalTranspose_apply_subset μ hD')).formalTranspose_eq

/-- The formal transpose of a composition of differential operators is the composition of their
formal transposes in the reverse order. -/
theorem formalTranspose_comp
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (D ∘ₗ D').formalTranspose μ = D'.formalTranspose μ ∘ₗ D.formalTranspose μ :=
  ((isFormalTranspose_formalTranspose μ hD).comp (isFormalTranspose_formalTranspose μ hD')
    (tsupport_differentialOperators_apply_subset hD')
    (tsupport_formalTranspose_apply_subset μ hD)).formalTranspose_eq

/-- The formal transpose of a product of differential operators is the product of their formal
transposes in the reverse order. -/
theorem formalTranspose_mul
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (D * D').formalTranspose μ = D'.formalTranspose μ * D.formalTranspose μ :=
  formalTranspose_comp μ hD hD'

/-- The formal transpose of a power of a differential operator is the power of its formal
transpose. -/
theorem formalTranspose_pow (n : ℕ) : (D ^ n).formalTranspose μ = D.formalTranspose μ ^ n :=
  ((isFormalTranspose_formalTranspose μ hD).pow
    (tsupport_differentialOperators_apply_subset hD)
    (tsupport_formalTranspose_apply_subset μ hD) n).formalTranspose_eq

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
    (fun i hi ↦ tsupport_differentialOperators_apply_subset (hD i hi))
    (fun i hi ↦ tsupport_formalTranspose_apply_subset μ (hD i hi))).formalTranspose_eq

section Examples

variable [FiniteDimensional ℝ E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The formal transpose of the directional derivative `∂_v` is `-∂_v`. -/
@[simp]
theorem formalTranspose_lineDerivation (v : E) :
    (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).formalTranspose μ =
      -(lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :=
  (isFormalTranspose_lineDerivation v).formalTranspose_eq

/-- The formal transpose of the power `∂_v ^ k` of a directional derivative is
`(-1) ^ k ∂_v ^ k`. -/
@[simp]
theorem formalTranspose_lineDerivation_pow (v : E) (k : ℕ) :
    ((lineDerivation ℝ v : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ^ k).formalTranspose μ =
      (-1 : ℝ) ^ k • (lineDerivation ℝ v : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ^ k := by
  rw [← smul_pow, neg_one_smul]
  exact ((isFormalTranspose_lineDerivation v).pow (tsupport_lineDerivation_apply_subset v)
    (fun g ↦ by simpa using tsupport_lineDerivation_apply_subset v g) k).formalTranspose_eq

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

end Euclidean

end LinearMap
