/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
-- Private: used only inside proofs.
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.SmoothCutoff
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Smooth compactly supported fields are dense in vector-valued `W^{1,p}(ℝⁿ)`

For a real Banach space `F` and `1 ≤ p < ∞`, every element of the first-order weak-derivative
graph over `Lᵖ(ℝⁿ, F)` is a limit of the graph elements of smooth compactly supported fields
`ℝⁿ → F` (`TauCeti.WeakDerivStep.dense_setOf_exists_contDiff_hasCompactSupport`). A priori
estimates proved for smooth compactly supported fields therefore extend to the whole Sobolev space
by continuity. No finite dimensionality of `F` is assumed, so this applies to paths in an
infinite-dimensional Hilbert space, the setting of the linearized operators `d/ds + A(s)` on a
strip.

The proof mollifies, then cuts off. Convolving a field `u` with weak derivative `Du` against a
normalized smooth bump gives a smooth field whose classical derivative is the mollification of
`Du` (`TauCeti.HasWeakFDerivOn.hasFDerivAt_convolution_right`), and the mollifications converge to
`u` and `Du` in `Lᵖ` (`TauCeti.tendsto_eLpNorm_normed_convolution_sub`). A smooth field with
derivative in `Lᵖ` is in turn the limit of its products with the expanding cutoffs `χ (x / n)`
(`TauCeti.exists_contDiff_hasCompactSupport_approximation`), and a smooth compactly supported field
has its classical derivative as weak derivative.

The file also provides the coordinate fields used to pass between scalar and vector-valued Sobolev
spaces: a scalar Sobolev function `u` and a vector `b : F` give the field `x ↦ u x • b`
(`TauCeti.WeakDerivStep.smulRightW1pL`), with weak derivative `v ↦ ∂ᵥ u • b`, and for a basis `bᵢ`
of a finite-dimensional `F`, with coordinate functionals `ℓᵢ`, a field `u` is the sum of the fields
`ℓᵢ ∘ u • bᵢ` built from its scalar projections `TauCeti.WeakDerivStep.toW1pL`.

## Main declarations

* `TauCeti.WeakDerivStep.dense_setOf_exists_contDiff_hasCompactSupport`: the fields with a smooth
  compactly supported representative are dense.
* `TauCeti.WeakDerivStep.smulRightW1pL`: the bounded linear map `u ↦ (x ↦ u x • b)` from scalar
  Sobolev functions to `F`-valued ones.
* `TauCeti.WeakDerivStep.prev_smulRightW1pL_ofTestFunctionₗ_ae_eq`: for a test function `ψ`, this
  field is represented by `x ↦ ψ x • b`.
* `TauCeti.WeakDerivStep.sum_smulRightW1pL_toW1pL`: a field is the sum of its coordinate fields.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.1; H. Brezis, *Functional Analysis, Sobolev
Spaces and Partial Differential Equations*, Theorem 9.2 (mollification and cutoff, in the scalar
case).
-/

public section

noncomputable section

open Filter MeasureTheory TopologicalSpace Set
open scoped Convolution ENNReal Distributions Topology

namespace TauCeti.WeakDerivStep

section Gradient

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative `v ↦ ⟪g, v⟫ • b` of the field `x ↦ u x • b` at a point where the scalar
function `u` has gradient `g`. -/
def smulRightGradientL (b : F) : E →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E ℝ F (ContinuousLinearMap.toSpanSingleton ℝ b)).comp
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap

/-- Evaluation formula for `smulRightGradientL`. -/
@[simp]
theorem smulRightGradientL_apply (b : F) (g v : E) :
    smulRightGradientL b g v = inner ℝ g v • b := by
  simp [smulRightGradientL]

end Gradient

section CoordinateFields

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

section CompleteSpace

variable [CompleteSpace F]

/-- The field `x ↦ u x • b` of a scalar Sobolev function has weak derivative
`v ↦ ⟪∇u x, v⟫ • b`. -/
theorem hasWeakFDerivOn_smulRight (b : F) (u : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega
      ((ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega) (W1p.value u))
      ((smulRightGradientL b).compLpL p (mu.restrict Omega) (W1p.gradient u)) := by
  refine ((W1p.hasWeakFDerivOn u).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ b)).congr_ae
    ((ContinuousLinearMap.toSpanSingleton ℝ b).coeFn_compLpL (W1p.value u)).symm
    |>.congr_ae_deriv ?_
  filter_upwards [(smulRightGradientL b).coeFn_compLpL (W1p.gradient u)] with x hx
  rw [hx]
  ext v
  simp [real_inner_comm]

/-- The bounded linear map sending a scalar Sobolev function `u` to the `F`-valued Sobolev field
`x ↦ u x • b`. -/
def smulRightW1pL (b : F) :
    W1p mu Omega p →L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      ((((ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega)).comp
          W1p.valueL).prod
        (((smulRightGradientL b).compLpL p (mu.restrict Omega)).comp W1p.gradientL)))
    _ fun u ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr (by
      simpa using hasWeakFDerivOn_smulRight b u)

/-- The value of `smulRightW1pL b u` is the class of `x ↦ u x • b`. -/
@[simp]
theorem prev_smulRightW1pL (b : F) (u : W1p mu Omega p) :
    prev _ (smulRightW1pL b u) =
      (ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega) (W1p.value u) := by
  simp [prev_coe, smulRightW1pL]

/-- The weak derivative of `smulRightW1pL b u` is the class of `x ↦ (v ↦ ⟪∇u x, v⟫ • b)`. -/
@[simp]
theorem weakFDeriv_smulRightW1pL (b : F) (u : W1p mu Omega p) :
    weakFDeriv _ (smulRightW1pL b u) =
      (smulRightGradientL b).compLpL p (mu.restrict Omega) (W1p.gradient u) := by
  simp [weakFDeriv_coe, smulRightW1pL]

/-- The field `smulRightW1pL b φ` of a test function `φ` is represented by `x ↦ φ x • b`. -/
theorem prev_smulRightW1pL_ofTestFunctionₗ_ae_eq (b : F) (φ : 𝓓(Omega, ℝ)) :
    ⇑(prev _ (smulRightW1pL b (W1p.ofTestFunctionₗ mu Omega p φ)))
      =ᵐ[mu.restrict Omega] fun x ↦ φ x • b := by
  rw [prev_smulRightW1pL, W1p.value_ofTestFunctionₗ]
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ b).coeFn_compLpL
    (testFunctionLp (mu := mu) p φ), testFunctionLp_apply_ae (mu := mu) p φ] with x hx hφ
  rw [hx, ContinuousLinearMap.toSpanSingleton_apply, hφ]

end CompleteSpace

/-- **Coordinate reconstruction.** For a basis `b` of `F`, an `F`-valued Sobolev field is the sum
of the fields `ℓᵢ ∘ u • bᵢ` built from its scalar coordinate projections. -/
theorem sum_smulRightW1pL_toW1pL [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ∑ i, smulRightW1pL (b i) (toW1pL _ (b.coord i).toContinuousLinearMap u) = u := by
  apply ext
  rw [← prevL_apply, map_sum]
  simp only [prevL_apply, prev_smulRightW1pL, value_toW1pL, ContinuousLinearMap.id_apply]
  exact (eq_sum_basis_compLpL b (prev _ u)).symm

end CoordinateFields

section Density

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

/-- A `C¹` field `g` such that `g` and its derivative lie in `Lᵖ` is represented by an element of
the weak-derivative graph over `Lᵖ(ℝⁿ, F)`, whose weak derivative is the classical derivative of
`g`. -/
private theorem exists_prev_ae_eq_and_weakFDeriv_ae_eq_of_contDiff {g : E → F}
    (hg : ContDiff ℝ 1 g) (hgp : MemLp g p (mu.restrict (⊤ : Opens E)))
    (hdg : MemLp (fderiv ℝ g) p (mu.restrict (⊤ : Opens E))) :
    ∃ w : WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))),
      ⇑(prev _ w) =ᵐ[mu.restrict (⊤ : Opens E)] g ∧
        ⇑(weakFDeriv _ w) =ᵐ[mu.restrict (⊤ : Opens E)] fderiv ℝ g := by
  have hweak : HasWeakFDerivOn mu ⊤
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E))) (hgp.toLp g))
      (hdg.toLp (fderiv ℝ g)) :=
    ((hasWeakFDerivOn_of_differentiableOn
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hdg.locallyIntegrable Fact.out))
      fun x _ ↦ hg.differentiable one_ne_zero x).congr_ae
        hgp.coeFn_toLp.symm).congr_ae_deriv hdg.coeFn_toLp.symm
  refine ⟨mk _ _ _ hweak, ?_, ?_⟩
  · rw [prev_mk]; exact hgp.coeFn_toLp
  · rw [weakFDeriv_mk]; exact hdg.coeFn_toLp

omit [FiniteDimensional ℝ E] in
/-- Elements of the weak-derivative graph converge when representatives of their fields and of
their weak derivatives converge in `Lᵖ`. -/
private theorem tendsto_of_tendsto_eLpNorm {ι : Type*} {l : Filter ι}
    {w : ι → WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E))))}
    {u : WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E))))}
    {g : ι → E → F} {G : ι → E → E →L[ℝ] F} {g₀ : E → F} {D₀ : E → E →L[ℝ] F}
    (hw : ∀ i, ⇑(prev _ (w i)) =ᵐ[mu.restrict (⊤ : Opens E)] g i)
    (hdw : ∀ i, ⇑(weakFDeriv _ (w i)) =ᵐ[mu.restrict (⊤ : Opens E)] G i)
    (hu : ⇑(prev _ u) =ᵐ[mu.restrict (⊤ : Opens E)] g₀)
    (hD : ⇑(weakFDeriv _ u) =ᵐ[mu.restrict (⊤ : Opens E)] D₀)
    (hconv : Tendsto (fun i ↦ eLpNorm (g i - g₀) p (mu.restrict (⊤ : Opens E))) l (𝓝 0))
    (hdconv : Tendsto (fun i ↦ eLpNorm (G i - D₀) p (mu.restrict (⊤ : Opens E))) l (𝓝 0)) :
    Tendsto w l (𝓝 u) := by
  refine tendsto_iff_prev_weakFDeriv.2 ⟨?_, ?_⟩ <;> rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  · exact hconv.congr fun i ↦ eLpNorm_congr_ae ((hw i).sub hu).symm
  · exact hdconv.congr fun i ↦ eLpNorm_congr_ae ((hdw i).sub hD).symm

/-- **Cutting off a smooth field.** An element of the weak-derivative graph over `Lᵖ(ℝⁿ, F)`
represented by a smooth field `g` whose derivative lies in `Lᵖ` is a limit of elements represented
by smooth compactly supported fields: the expanding cutoffs `χ (x / (n + 1)) • g x`. -/
private theorem mem_closure_setOf_exists_contDiff_hasCompactSupport (hp : p ≠ ∞)
    {v : WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E))))}
    {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hvg : ⇑(prev _ v) =ᵐ[mu.restrict (⊤ : Opens E)] g)
    (hdg : MemLp (fderiv ℝ g) p (mu.restrict (⊤ : Opens E))) :
    v ∈ closure {u : WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))) |
      ∃ φ : E → F, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        ⇑(prev _ u) =ᵐ[mu.restrict (⊤ : Opens E)] φ} := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hgp : MemLp g p (mu.restrict (⊤ : Opens E)) := (Lp.memLp (prev _ v)).ae_eq hvg
  have hmem : ∀ i ≤ 1, MemLp (iteratedFDeriv ℝ i g) p (mu.restrict (⊤ : Opens E)) := by
    intro i hi
    interval_cases i
    · exact hgp.congr_norm ((hg.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
        (.of_forall fun x ↦ by simp)
    · exact hdg.congr_norm ((hg.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
        (.of_forall fun x ↦ by simp)
  obtain ⟨h, hh, -, hconv⟩ := exists_contDiff_hasCompactSupport_approximation hp hg 1
    (by simp) hmem
  have hh1 (n : ℕ) : ContDiff ℝ 1 (h n) := (hh n).1.of_le (by exact_mod_cast le_top)
  have hhp (n : ℕ) : MemLp (h n) p (mu.restrict (⊤ : Opens E)) :=
    (hh1 n).continuous.memLp_of_hasCompactSupport (hh n).2
  have hdhp (n : ℕ) : MemLp (fderiv ℝ (h n)) p (mu.restrict (⊤ : Opens E)) :=
    ((hh1 n).continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport ((hh n).2.fderiv ℝ)
  -- The weak derivative of `v` is the classical derivative of its smooth representative.
  have hdv : ⇑(weakFDeriv _ v) =ᵐ[mu.restrict (⊤ : Opens E)] fderiv ℝ g :=
    ((hasWeakFDerivOn_base_prev _ v).congr_ae hvg).ae_eq_fderiv
      ((hg1.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      fun x _ ↦ hg1.differentiable one_ne_zero x
  choose w hw hdw using fun n ↦
    exists_prev_ae_eq_and_weakFDeriv_ae_eq_of_contDiff (hh1 n) (hhp n) (hdhp n)
  refine mem_closure_of_tendsto (tendsto_of_tendsto_eLpNorm (l := atTop) hw hdw hvg hdv ?_ ?_)
    (.of_forall fun n ↦ ⟨h n, (hh n).1, (hh n).2, hw n⟩)
  · refine (hconv 0 zero_le_one).congr fun n ↦ eLpNorm_congr_norm_ae
      (((hh n).1.continuous_iteratedFDeriv (by simp)).sub
        (hg.continuous_iteratedFDeriv (by simp))).aestronglyMeasurable
      ((hh1 n).continuous.sub hg1.continuous).aestronglyMeasurable (.of_forall fun x ↦ ?_)
    rw [Pi.sub_apply, ← iteratedFDeriv_sub_apply ((hh1 n).contDiffAt.of_le zero_le_one)
      (hg1.contDiffAt.of_le zero_le_one), norm_iteratedFDeriv_zero, Pi.sub_apply]
  · refine (hconv 1 le_rfl).congr fun n ↦ eLpNorm_congr_norm_ae
      (((hh n).1.continuous_iteratedFDeriv (by simp)).sub
        (hg.continuous_iteratedFDeriv (by simp))).aestronglyMeasurable
      (((hh1 n).continuous_fderiv one_ne_zero).sub
        (hg1.continuous_fderiv one_ne_zero)).aestronglyMeasurable (.of_forall fun x ↦ ?_)
    rw [Pi.sub_apply, ← iteratedFDeriv_sub_apply (hh1 n).contDiffAt hg1.contDiffAt,
      norm_iteratedFDeriv_one, Pi.sub_apply, fderiv_sub ((hh1 n).differentiable one_ne_zero x)
      (hg1.differentiable one_ne_zero x)]

open ContinuousLinearMap in
/-- **Mollifying a field.** Every element of the weak-derivative graph over `Lᵖ(ℝⁿ, F)` is a limit
of elements represented by smooth fields whose derivatives lie in `Lᵖ`: its convolutions with
normalized smooth bumps of shrinking radii. -/
private theorem exists_tendsto_of_contDiff (hp : p ≠ ∞)
    (u : WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E))))) :
    ∃ v : ℕ → WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))),
      Tendsto v atTop (𝓝 u) ∧ ∀ k, ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧
        ⇑(prev _ (v k)) =ᵐ[mu.restrict (⊤ : Opens E)] g ∧
        MemLp (fderiv ℝ g) p (mu.restrict (⊤ : Opens E)) := by
  have hν : mu.restrict ((⊤ : Opens E) : Set E) = mu := by simp
  set f : E → F := ⇑(prev _ u)
  set D : E → E →L[ℝ] F := ⇑(weakFDeriv _ u)
  have hf : MemLp f p mu := by rw [← hν]; exact Lp.memLp _
  have hD : MemLp D p mu := by rw [← hν]; exact Lp.memLp _
  let phi : ℕ → ContDiffBump (0 : E) := fun k ↦
    ⟨1 / ((k : ℝ) + 1) / 2, 1 / ((k : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hphi : Tendsto (fun k ↦ (phi k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- The mollified field `g k` is smooth, and its classical derivative is the mollified weak
  -- derivative.
  let g : ℕ → E → F := fun k ↦ (phi k).normed mu ⋆[lsmul ℝ ℝ, mu] f
  have hg (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (g k) :=
    (phi k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (phi k).contDiff_normed (hf.locallyIntegrable Fact.out)
  have hg1 (k : ℕ) : ContDiff ℝ 1 (g k) := (hg k).of_le (by exact_mod_cast le_top)
  have hfd (k : ℕ) : fderiv ℝ (g k) = (phi k).normed mu ⋆[lsmul ℝ ℝ, mu] D := funext fun x ↦ by
    have h := (hasWeakFDerivOn_base_prev _ u).hasFDerivAt_convolution_right
      (hf.locallyIntegrable Fact.out) (hD.locallyIntegrable Fact.out) ((phi k).normed mu)
      (phi k).contDiff_normed (phi k).hasCompactSupport_normed x (fun _ _ ↦ trivial)
    rw [convolution_flip, convolution_flip] at h
    exact h.fderiv
  have hgp (k : ℕ) : MemLp (g k) p (mu.restrict (⊤ : Opens E)) := by
    rw [hν]; exact (Lp.memLp _).ae_eq (normedBumpLp_ae_eq_convolution hp (phi k) hf)
  have hdgp (k : ℕ) : MemLp (fderiv ℝ (g k)) p (mu.restrict (⊤ : Opens E)) := by
    rw [hν, hfd]; exact (Lp.memLp _).ae_eq (normedBumpLp_ae_eq_convolution hp (phi k) hD)
  choose v hv hdv using fun k ↦
    exists_prev_ae_eq_and_weakFDeriv_ae_eq_of_contDiff (hg1 k) (hgp k) (hdgp k)
  refine ⟨v, tendsto_of_tendsto_eLpNorm (g₀ := f) (D₀ := D) hv hdv .rfl .rfl ?_ ?_,
    fun k ↦ ⟨g k, hg k, hv k, hdgp k⟩⟩
  · rw [hν]; exact tendsto_eLpNorm_normed_convolution_sub hp hphi hf
  · rw [hν]; simpa only [hfd] using tendsto_eLpNorm_normed_convolution_sub hp hphi hD

/-- **Density of smooth compactly supported fields.** For a real Banach space `F` and
`1 ≤ p < ∞`, the elements of the weak-derivative graph over `Lᵖ(ℝⁿ, F)` represented by a smooth
compactly supported field are dense. -/
theorem dense_setOf_exists_contDiff_hasCompactSupport (hp : p ≠ ∞) :
    Dense {u : WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))) |
      ∃ φ : E → F, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        ⇑(prev _ u) =ᵐ[mu.restrict (⊤ : Opens E)] φ} := fun u ↦ by
  obtain ⟨v, hv, hsmooth⟩ := exists_tendsto_of_contDiff hp u
  refine closure_closure.subset (mem_closure_of_tendsto hv (Eventually.of_forall fun k ↦ ?_))
  obtain ⟨g, hg, hvg, hdg⟩ := hsmooth k
  exact mem_closure_setOf_exists_contDiff_hasCompactSupport hp hg hvg hdg

end Density

end TauCeti.WeakDerivStep
