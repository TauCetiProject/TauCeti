/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HalfSpace
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Const
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.DifferentiatedEquation
import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.Analysis.Sobolev.W1p.Symmetry
import TauCeti.Analysis.Sobolev.W1p.TangentialDerivative
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv

/-!
# All-order local regularity at a flat Dirichlet boundary

Let `Ω ∩ U = H ∩ U` for an open half-space `H`, allowing the empty and whole-space
degeneracies. A scalar weak solution on `Ω ∩ U` of
`-div(a ∇u) = f`, with smooth coefficients and forcing on `U`, is in every Sobolev
order on `Ω ∩ V` whenever `closure V` is compact and contained in `U`. The homogeneous
boundary condition is imposed by requiring every cutoff supported in `U` times the
solution to lie in `H¹₀(Ω)` when the half-space has a nonzero normal.

For each Sobolev order, an intermediate open set supplies the derivatives used in the
localized forcing. The cutoff one on `closure V` then gives the same solution there
as the global half-space problem, where tangential differentiation and the conormal
flux recover all derivatives.

Reference: L. C. Evans, *Partial Differential Equations*, §6.3.2, Theorem 5.
-/

public section

section Multipliers

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal

namespace TauCeti.Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {U K : Set E}

/-- Multiplication by a smooth coefficient preserves (W^{k,p}(Ω)) if the coefficient
is smooth on an open neighbourhood of `closure Ω` and constant off a compact set there. -/
private theorem exists_value_ae_eq_mul_of_eqOn_compl_isCompact (k : ℕ)
    {ψ : E → ℝ} {c : ℝ} (hU : IsOpen U) (hΩU : closure (Omega : Set E) ⊆ U)
    (hK : IsCompact K) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hψc : EqOn ψ (fun _ ↦ c) (U \ K)) (u : Wkp mu Omega p k) :
    ∃ w : Wkp mu Omega p k, (value k w : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x ↦ ψ x * value k u x := by
  obtain ⟨χ, hχ, -, hχ1, hχc, hχU⟩ :=
    (hK.inter_right isClosed_closure).exists_contDiff_cutoff hU
      (fun _ hx ↦ hΩU hx.2)
  let ψ₀ : E → ℝ := fun x ↦ χ x * (ψ x - c)
  have hψ₀ : ContDiff ℝ ∞ ψ₀ :=
    (hψ.sub contDiffOn_const).contDiff_smul_of_tsupport_subset hU hχ.contDiffOn hχU
  have hψ₀c : HasCompactSupport ψ₀ :=
    hχc.mul_right
  obtain ⟨v, hv⟩ := exists_value_ae_eq_mul_of_hasCompactSupport k hψ₀ hψ₀c u
  refine ⟨v + c • u, ?_⟩
  filter_upwards [value_add_ae k v (c • u), value_smul_ae k c u, hv,
    ae_restrict_mem Omega.isOpen.measurableSet] with x h₁ h₂ h₃ hx
  have h : ψ₀ x = ψ x - c := by
    change χ x * (ψ x - c) = ψ x - c
    by_cases hxK : x ∈ K
    · rw [show χ x = 1 from interior_subset (hχ1 ⟨hxK, subset_closure hx⟩), one_mul]
    · rw [show ψ x = c from hψc ⟨hΩU (subset_closure hx), hxK⟩, sub_self, mul_zero]
  rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, h₃, h, smul_eq_mul]
  ring

end TauCeti.Wkp

end Multipliers

section DifferentiatedEquation

open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal InnerProductSpace NNReal Topology

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {K : Set (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ} {lam Lam : ℝ}

local notation "E" => EuclideanSpace ℝ ι
local notation "𝔟" => EuclideanSpace.basisFun ι ℝ

private theorem exists_lipschitzWith_and_norm_bound_of_eqOn_const (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j)) :
    ∃ L : ℝ≥0, ∃ M : ℝ, LipschitzWith L (fun x ↦ matrixBilinearForm (a x)) ∧
      ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M := by
  let d (i j : ι) (x : E) := a x i j - A i j
  have hc (i j : ι) : HasCompactSupport (d i j) := by
    refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
    intro x hx
    by_contra h
    exact hx (by simp [d, hconst h])
  have hd (i j : ι) : ContDiff ℝ ∞ (d i j) := (hsm i j).sub contDiff_const
  choose L hL using fun i j ↦ (hd i j).lipschitzWith_of_hasCompactSupport (hc i j) (by simp)
  choose M hM using fun i j ↦ (hc i j).exists_bound_of_continuous (hd i j).continuous
  have heq (i j : ι) : (fun x ↦ a x i j) = fun x ↦ d i j x + A i j :=
    funext fun x ↦ (sub_add_cancel (a x i j) (A i j)).symm
  have hlip (i j : ι) : LipschitzWith (L i j) (fun x ↦ a x i j) := by
    rw [heq]
    simpa using (hL i j).add (LipschitzWith.const (A i j))
  refine ⟨∑ i, ∑ j, L i j, ∑ i, ∑ j, (M i j + |A i j|),
    lipschitzWith_matrixBilinearForm_of_forall hlip, fun x ↦ ?_⟩
  refine (norm_matrixBilinearForm_le_sum_abs (a x)).trans
    (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_)
  rw [congrFun (heq i j) x]
  exact (abs_add_le _ _).trans (add_le_add (hM i j x) le_rfl)

/-- The differentiated principal equation has `H^k` forcing even on an unbounded domain
if the smooth coefficient field is constant off a compact set. -/
private theorem exists_hasWeakLineDerivOn_and_energyFormH1_eq_of_eqOn_const (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) (F : Wkp mu Omega 2 (k + 1)) {u : W1p mu Omega 2}
    (U : Wkp mu Omega 2 (k + 2)) (hU : Wkp.value (k + 2) U = W1p.value u)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value (k + 1) F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (e : E) :
    ∃ (d : Wkp mu Omega 2 (k + 1)) (G : Wkp mu Omega 2 k),
      HasWeakLineDerivOn mu Omega (W1p.value u) (Wkp.value (k + 1) d) e ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (Wkp.firstOrder k d) (v : W1p mu Omega 2) =
        ∫ x in Omega, Wkp.value k G x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  obtain ⟨_, _, hL, hM⟩ := exists_lipschitzWith_and_norm_bound_of_eqOn_const hK hconst hsm
  have hcoeff := memLp_energyIntegrand_of_continuous (mu := mu) hM hL.continuous Omega
  choose D hD using fun j ↦ Wkp.exists_hasWeakLineDerivOn_value (k + 1) U (𝔟 j)
  choose DD hDD using fun i j ↦ Wkp.exists_hasWeakLineDerivOn_value k (D j) (𝔟 i)
  obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) U e
  obtain ⟨Fe, hFe⟩ := Wkp.exists_hasWeakLineDerivOn_value k F e
  rw [hU] at hD hd
  have hD₁ (j : ι) : HasWeakLineDerivOn mu Omega (W1p.value u)
      (W1p.value (Wkp.firstOrder k (D j))) (𝔟 j) := by
    simpa only [Wkp.value_firstOrder] using hD j
  let C₁ (i j : ι) (x : E) := fderiv ℝ (fun y ↦ a y i j) x e
  let C₂ (i j : ι) (x : E) := fderiv ℝ (C₁ i j) x (𝔟 i)
  have hs₁ (i j : ι) : ContDiff ℝ ∞ (C₁ i j) :=
    ((hsm i j).fderiv_right (by simp)).clm_apply contDiff_const
  have hs₂ (i j : ι) : ContDiff ℝ ∞ (C₂ i j) :=
    ((hs₁ i j).fderiv_right (by simp)).clm_apply contDiff_const
  have hc (i j : ι) : EqOn (fun x ↦ a x i j) (fun _ ↦ A i j) Kᶜ :=
    fun _ hx ↦ congrArg (fun B ↦ B i j) (hconst hx)
  have hc₁ (i j : ι) : EqOn (C₁ i j) (fun _ ↦ 0) Kᶜ := fun x hx ↦ by
    simp [C₁, fderiv_eq_zero_of_eqOn_const ℝ hK.isClosed.isOpen_compl (hc i j) hx]
  have hc₂ (i j : ι) : EqOn (C₂ i j) (fun _ ↦ 0) Kᶜ := fun x hx ↦ by
    simp [C₂, fderiv_eq_zero_of_eqOn_const ℝ hK.isClosed.isOpen_compl (hc₁ i j) hx]
  choose M₁ hM₁ using fun i j ↦ Wkp.exists_value_ae_eq_mul_of_eqOn_compl_isCompact k
    isOpen_univ (subset_univ _) hK (hs₂ i j).contDiffOn
    (fun x hx ↦ hc₂ i j hx.2) (Wkp.lowerOrder k (D j))
  choose M₂ hM₂ using fun i j ↦ Wkp.exists_value_ae_eq_mul_of_eqOn_compl_isCompact k
    isOpen_univ (subset_univ _) hK (hs₁ i j).contDiffOn (fun x hx ↦ hc₁ i j hx.2) (DD i j)
  refine ⟨d, Fe + ∑ i, ∑ j, (M₁ i j + M₂ i j), hd, ?_⟩
  have hut := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff _ u).1 hu
  refine (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff _ _).2 fun φ ↦ ?_
  rw [energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn
    (fun i j ↦ (hsm i j).contDiffOn.of_le (by simp)) hut
    ((Wkp.value_firstOrder k d).symm ▸ hd) hD₁ hFe φ]
  have hv₁ (i j : ι) : ∀ᵐ x ∂mu.restrict Omega, Wkp.value k (M₁ i j) x =
      C₂ i j x * ⟪W1p.gradient u x, 𝔟 j⟫_ℝ := by
    filter_upwards [hM₁ i j, (hD j).ae_eq ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (𝔟 j))]
      with x h₁ h₂
    rw [h₁, ← Wkp.value_succ, h₂, innerSL_apply_apply]
  have hv₂ (i j : ι) : ∀ᵐ x ∂mu.restrict Omega, Wkp.value k (M₂ i j) x =
      C₁ i j x * ⟪W1p.gradient (Wkp.firstOrder k (D j)) x, 𝔟 i⟫_ℝ := by
    have h := (W1p.hasWeakFDerivOn (Wkp.firstOrder k (D j))).hasWeakLineDerivOn (𝔟 i)
    rw [Wkp.value_firstOrder] at h
    filter_upwards [hM₂ i j, (hDD i j).ae_eq h] with x h₁ h₂
    rw [h₁, h₂, innerSL_apply_apply]
  refine integral_congr_ae ?_
  filter_upwards [Wkp.ae_value_add_sum_eq Fe Finset.univ Finset.univ M₁ M₂
    ((ae_all_iff.2 fun i ↦ ae_all_iff.2 (hv₁ i)).mono fun x h i _ j _ ↦ h i j)
    ((ae_all_iff.2 fun i ↦ ae_all_iff.2 (hv₂ i)).mono fun x h i _ j _ ↦ h i j)] with x hx
  rw [hx]

end TauCeti.PDE

end DifferentiatedEquation

section NormalRecovery

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {K : Set (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ} {lam Lam : ℝ}

local notation "E" => EuclideanSpace ℝ ι
local notation "b" => EuclideanSpace.basisFun ι ℝ

private noncomputable def flux (u : W1p mu Omega 2) (a : E → Matrix ι ι ℝ) (p x : E) : ℝ :=
  matrixBilinearForm (a x) p (W1p.gradient u x)

private theorem flux_eq_sum (u : W1p mu Omega 2) (p x : E) :
    flux u a p x = ∑ j, matrixBilinearForm (a x) p (b j) *
      ⟪W1p.gradient u x, b j⟫_ℝ := by
  unfold flux
  simpa only [real_inner_comm (W1p.gradient u x)] using
    ((b).sum_apply_mul_inner (matrixBilinearForm (a x) p) (W1p.gradient u x)).symm

private theorem flux_eq_normal_add_tangential (u : W1p mu Omega 2) {e : E} (he : ‖e‖ = 1)
    (x : E) :
    flux u a e x =
      matrixBilinearForm (a x) e e * ⟪W1p.gradient u x, e⟫_ℝ +
        ∑ i, matrixBilinearForm (a x) e (b i) *
          ⟪W1p.gradient u x, (ℝ ∙ e)ᗮ.starProjection (b i)⟫_ℝ := by
  have h := (b).sum_apply_mul_inner_sub_sum_apply_mul_inner_starProjection
    (matrixBilinearForm (a x) e) e (W1p.gradient u x)
  simp only [RCLike.ofReal_real_eq_id, id_eq, he, one_pow, inv_one, one_smul,
    real_inner_comm (W1p.gradient u x)] at h
  rw [flux_eq_sum]
  exact sub_eq_iff_eq_add.mp h

private theorem hasWeakLineDerivOn_normal_flux
    {u : W1p0 mu Omega 2} {f : Lp ℝ 2 (mu.restrict Omega)}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) {e : E} (he : ‖e‖ = 1)
    (hq : LocallyIntegrableOn (flux (u : W1p mu Omega 2) a e) Omega mu)
    {G : ι → E → ℝ} (hG : ∀ i, HasWeakLineDerivOn mu Omega
      (flux (u : W1p mu Omega 2) a (b i)) (G i) ((ℝ ∙ e)ᗮ.starProjection (b i))) :
    HasWeakLineDerivOn mu Omega (flux (u : W1p mu Omega 2) a e)
      (fun x ↦ -(f x + ∑ i, G i x)) e := by
  set w := (u : W1p mu Omega 2)
  set P := (ℝ ∙ e)ᗮ.starProjection
  have hf := Lp.locallyIntegrableOn f (by norm_num)
  have hGloc := locallyIntegrableOn_finsetSum Finset.univ
    fun i _ ↦ (hG i).locallyIntegrableOn_deriv
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hq, (hf.add hGloc).neg, ?_⟩
  intro φ
  have hφ : Differentiable ℝ (φ : E → ℝ) := φ.contDiff.differentiable (by simp)
  have hI : ∀ i, Integrable (fun x ↦ lineDeriv ℝ (φ : E → ℝ) x (P (b i)) •
      flux w a (b i) x) mu := fun i ↦
    integrable_lineDeriv_smul_of_locallyIntegrableOn (hG i).locallyIntegrableOn φ _
  have hIq := integrable_lineDeriv_smul_of_locallyIntegrableOn hq φ e
  have hsplit : (∫ x in Omega, matrixBilinearForm (a x)
        (W1p.gradient (W1p.ofTestFunctionₗ mu Omega 2 φ) x) (W1p.gradient w x) ∂mu) =
      ∫ x in Omega, (lineDeriv ℝ (φ : E → ℝ) x e • flux w a e x +
        ∑ i, lineDeriv ℝ (φ : E → ℝ) x (P (b i)) • flux w a (b i) x) ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx, ← ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      (b).bilin_eq_inner_mul_sum_add_sum_sum_inner_starProjection b _ e]
    simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, RCLike.ofReal_real_eq_id,
      id_eq, he, one_pow, inv_one, one_smul, real_inner_comm (gradient (φ : E → ℝ) x),
      inner_gradient_left, (hφ x).lineDeriv_eq_fderiv,
      smul_eq_mul, flux_eq_sum, Finset.mul_sum, P, real_inner_comm (W1p.gradient w x)]
  have heq := hu.energyFormH1_ofTestFunctionₗ φ
  rw [energyFormH1_zero_zero_eq_setIntegral, hsplit,
    integral_add hIq.integrableOn
      (integrable_finsetSum _ fun i _ ↦ (hI i).integrableOn),
    integral_finsetSum _ fun i _ ↦ (hI i).integrableOn,
    setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ e] at heq
  simp_rw [setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ,
    fun i ↦ (hG i).integral_lineDeriv_smul_eq_neg_integral_smul φ] at heq
  have hIG i := φ.integrable_smul (hG i).locallyIntegrableOn_deriv
  have hR := TestFunction.neg_integral_smul_neg_add_eq
    (G := fun i (_ : Unit) ↦ G i) φ hf (fun i _ ↦ hIG i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_nsmul] at hR
  rw [hR]
  simp only [Finset.sum_neg_distrib] at heq
  linarith [heq]

private theorem exists_value_ae_eq_sum (k : ℕ) {g : ι → E → ℝ}
    (hg : ∀ i, ∃ G : Wkp mu Omega 2 k, Wkp.value k G =ᵐ[mu.restrict Omega] g i) :
    ∃ G : Wkp mu Omega 2 k, Wkp.value k G =ᵐ[mu.restrict Omega] fun x ↦ ∑ i, g i x := by
  choose G hG using hg
  refine ⟨∑ i, G i, ?_⟩
  filter_upwards [Wkp.value_finsetSum_ae k Finset.univ G, ae_all_iff.2 hG] with x hx hGx
  simp only [hx, hGx]

private theorem exists_value_ae_eq_gradient_inner (k : ℕ) {u : W1p mu Omega 2}
    (U : Wkp mu Omega 2 (k + 1)) (hU : Wkp.value (k + 1) U = W1p.value u) (p : E) :
    ∃ D : Wkp mu Omega 2 k, Wkp.value k D =ᵐ[mu.restrict Omega]
      fun x ↦ ⟪W1p.gradient u x, p⟫_ℝ := by
  obtain ⟨D, hD⟩ := Wkp.exists_hasWeakLineDerivOn_value k U p
  rw [hU] at hD
  exact ⟨D, hD.ae_eq (W1p.hasWeakLineDerivOn_inner_gradient u p)⟩

private theorem exists_value_ae_eq_mul_coefficient (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) (p q : E) (w : Wkp mu Omega 2 k) :
    ∃ W : Wkp mu Omega 2 k, Wkp.value k W =ᵐ[mu.restrict Omega]
      fun x ↦ matrixBilinearForm (a x) p q * Wkp.value k w x :=
  Wkp.exists_value_ae_eq_mul_of_eqOn_compl_isCompact k isOpen_univ (subset_univ _) hK
    (contDiff_matrixBilinearForm_apply hsm contDiff_const contDiff_const).contDiffOn
    (fun _ hx ↦ congrArg (fun B ↦ matrixBilinearForm B p q) (hconst hx.2)) w

private theorem exists_value_ae_eq_flux (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) {u : W1p mu Omega 2} (U : Wkp mu Omega 2 (k + 1))
    (hU : Wkp.value (k + 1) U = W1p.value u) (p : E) :
    ∃ Q : Wkp mu Omega 2 k, Wkp.value k Q =ᵐ[mu.restrict Omega] flux u a p := by
  obtain ⟨Q, hQ⟩ := exists_value_ae_eq_sum k fun j ↦ by
    obtain ⟨D, hD⟩ := exists_value_ae_eq_gradient_inner k U hU (b j)
    obtain ⟨M, hM⟩ := exists_value_ae_eq_mul_coefficient hK hconst hsm k p (b j) D
    exact ⟨M, hM.trans (hD.mono fun x hx ↦ congrArg (matrixBilinearForm (a x) p (b j) * ·) hx)⟩
  exact ⟨Q, hQ.mono fun x hx ↦ hx.trans (flux_eq_sum u p x).symm⟩

private theorem exists_hasWeakLineDerivOn_flux (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) {u : W1p mu Omega 2} (U : Wkp mu Omega 2 (k + 1))
    (hU : Wkp.value (k + 1) U = W1p.value u) (p τ : E)
    (T : Wkp mu Omega 2 (k + 1))
    (hT : HasWeakLineDerivOn mu Omega (W1p.value u) (Wkp.value (k + 1) T) τ) :
    ∃ Q : Wkp mu Omega 2 k, HasWeakLineDerivOn mu Omega (flux u a p) (Wkp.value k Q) τ := by
  let C (j : ι) (x : E) := matrixBilinearForm (a x) p (b j)
  have hC (j : ι) : ContDiff ℝ ∞ (C j) :=
    contDiff_matrixBilinearForm_apply hsm contDiff_const contDiff_const
  have hG (j : ι) : ∃ G : Wkp mu Omega 2 k, HasWeakLineDerivOn mu Omega
      (fun x ↦ C j x * ⟪W1p.gradient u x, b j⟫_ℝ) (Wkp.value k G) τ := by
    obtain ⟨D, hD⟩ := exists_value_ae_eq_gradient_inner k U hU (b j)
    obtain ⟨Tj, hTj⟩ := Wkp.exists_hasWeakLineDerivOn_value k T (b j)
    have hDτ := hT.comm hTj (W1p.hasWeakLineDerivOn_inner_gradient u (b j))
    have hC' : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ (C j) x τ) :=
      ((hC j).fderiv_right (by simp)).clm_apply contDiff_const
    have hc : EqOn (C j) (fun _ ↦ matrixBilinearForm A p (b j)) Kᶜ :=
      fun _ hx ↦ congrArg (fun B ↦ matrixBilinearForm B p (b j)) (hconst hx)
    have hc' : EqOn (fun x ↦ fderiv ℝ (C j) x τ) (fun _ ↦ 0) Kᶜ := fun x hx ↦ by
      simp [fderiv_eq_zero_of_eqOn_const ℝ hK.isClosed.isOpen_compl hc hx]
    obtain ⟨M, hM⟩ := exists_value_ae_eq_mul_coefficient hK hconst hsm k p (b j) Tj
    obtain ⟨N, hN⟩ := Wkp.exists_value_ae_eq_mul_of_eqOn_compl_isCompact k
      isOpen_univ (subset_univ _) hK hC'.contDiffOn (fun _ hx ↦ hc' hx.2) D
    refine ⟨M + N, ?_⟩
    apply ((hDτ.contDiffOn_smul_of_ne_zero (hC j).contDiffOn (by simp)).congr_ae
      (Eventually.of_forall fun x ↦ smul_eq_mul _ _)).congr_ae_deriv
    filter_upwards [Wkp.value_add_ae k M N, hM, hN, hD] with x h₁ h₂ h₃ h₄
    simp only [smul_eq_mul, h₁, Pi.add_apply, h₂, h₃, h₄, C]
  choose G hG using hG
  refine ⟨∑ i, G i, ?_⟩
  refine ((HasWeakLineDerivOn.sum Finset.univ fun i _ ↦ hG i).congr_ae
    (Eventually.of_forall fun x ↦ ?_)).congr_ae_deriv ?_
  · exact (flux_eq_sum u p x).symm
  · filter_upwards [Wkp.value_finsetSum_ae k Finset.univ G] with x hx
    exact hx.symm

private theorem exists_hasWeakLineDerivOn_of_normal_and_tangential (k : ℕ)
    {e : E} (he : ‖e‖ = 1) {q : E → ℝ} {N : Wkp mu Omega 2 k}
    (hN : HasWeakLineDerivOn mu Omega q (Wkp.value k N) e)
    (hT : ∀ τ : E, ⟪τ, e⟫_ℝ = 0 → ∃ T : Wkp mu Omega 2 k,
      HasWeakLineDerivOn mu Omega q (Wkp.value k T) τ) (v : E) :
    ∃ D : Wkp mu Omega 2 k, HasWeakLineDerivOn mu Omega q (Wkp.value k D) v := by
  let P := (ℝ ∙ e)ᗮ.starProjection
  obtain ⟨T, hT⟩ := hT (P v) (Submodule.mem_orthogonal_singleton_iff_inner_left.1
    (Submodule.starProjection_apply_mem _ _))
  have hsplit : P v + ⟪e, v⟫_ℝ • e = v := by
    simpa only [Submodule.starProjection_singleton, he, one_pow, RCLike.ofReal_real_eq_id,
      id_eq, div_one, add_comm, P] using
      (ℝ ∙ e).starProjection_add_starProjection_orthogonal v
  have hd := hT.add_direction (hN.smul_direction ⟪e, v⟫_ℝ)
  rw [hsplit] at hd
  refine ⟨T + ⟪e, v⟫_ℝ • N, hd.congr_ae_deriv ?_⟩
  filter_upwards [Wkp.value_add_ae k T (⟪e, v⟫_ℝ • N), Wkp.value_smul_ae k ⟪e, v⟫_ℝ N]
    with x h₁ h₂
  simp only [h₁, h₂, Pi.add_apply]

private theorem exists_value_ae_eq_normal_flux (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) (F : Wkp mu Omega 2 (k + 1)) {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value (k + 1) F) u)
    (U : Wkp mu Omega 2 (k + 2)) (hU : Wkp.value (k + 2) U = W1p.value (u : W1p mu Omega 2))
    {e : E} (he : ‖e‖ = 1)
    (hT : ∀ τ : E, ⟪τ, e⟫_ℝ = 0 → ∃ T : Wkp mu Omega 2 (k + 2),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (Wkp.value (k + 2) T) τ) :
    ∃ Q : Wkp mu Omega 2 (k + 2), Wkp.value (k + 2) Q =ᵐ[mu.restrict Omega]
      flux (u : W1p mu Omega 2) a e := by
  let P := (ℝ ∙ e)ᗮ.starProjection
  have hP (i : ι) : ⟪P (b i), e⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Submodule.starProjection_apply_mem _ _)
  have hTang (p τ : E) (hτ : ⟪τ, e⟫_ℝ = 0) :
      ∃ Q : Wkp mu Omega 2 (k + 1),
        HasWeakLineDerivOn mu Omega (flux (u : W1p mu Omega 2) a p) (Wkp.value (k + 1) Q) τ := by
    obtain ⟨T, ht⟩ := hT τ hτ
    exact exists_hasWeakLineDerivOn_flux hK hconst hsm (k + 1) U hU p τ T ht
  obtain ⟨q, hq⟩ := exists_value_ae_eq_flux hK hconst hsm (k + 1) U hU e
  have hqLp := (Lp.memLp (Wkp.value (k + 1) q)).ae_eq hq
  have hqLoc := locallyIntegrableOn_of_locallyIntegrable_restrict (hqLp.locallyIntegrable (by simp))
  choose G hG using fun i ↦ hTang (b i) (P (b i)) (hP i)
  have hn := hasWeakLineDerivOn_normal_flux hu he hqLoc hG
  have hN : HasWeakLineDerivOn mu Omega (flux (u : W1p mu Omega 2) a e)
      (Wkp.value (k + 1) (-(F + ∑ i, G i))) e := by
    apply hn.congr_ae_deriv
    filter_upwards [Wkp.value_neg_ae (k + 1) (F + ∑ i, G i),
      Wkp.value_add_ae (k + 1) F (∑ i, G i),
      Wkp.value_finsetSum_ae (k + 1) Finset.univ G] with x h₁ h₂ h₃
    simp only [h₁, h₂, Pi.neg_apply, Pi.add_apply, h₃]
  choose d hd using exists_hasWeakLineDerivOn_of_normal_and_tangential (k + 1) he hN (hTang e)
  exact Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn (k + 1) hqLp d hd

/-- For a weak elliptic solution already in `H^{k+2}`, if every tangential first derivative
belongs to `H^{k+2}` and the forcing belongs to `H^{k+1}`, then so does the normal first
derivative. The equation determines the normal derivative of the conormal flux. -/
private theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_normal_of_tangential [DecidableEq ι]
    (ha : UniformlyEllipticOn (Omega : Set E) a lam Lam) (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) (F : Wkp mu Omega 2 (k + 1)) {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value (k + 1) F) u)
    (U : Wkp mu Omega 2 (k + 2)) (hU : Wkp.value (k + 2) U = W1p.value (u : W1p mu Omega 2))
    {e : E} (he : ‖e‖ = 1)
    (hT : ∀ τ : E, ⟪τ, e⟫_ℝ = 0 → ∃ T : Wkp mu Omega 2 (k + 2),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (Wkp.value (k + 2) T) τ) :
    ∃ N : Wkp mu Omega 2 (k + 2),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (Wkp.value (k + 2) N) e := by
  let P := (ℝ ∙ e)ᗮ.starProjection
  have hP (i : ι) : ⟪P (b i), e⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Submodule.starProjection_apply_mem _ _)
  obtain ⟨Q, hQ⟩ := exists_value_ae_eq_normal_flux hK hconst hsm k F hu U hU he hT
  obtain ⟨T, hTeq⟩ := exists_value_ae_eq_sum (k + 2) fun i ↦ by
    obtain ⟨Ti, hi⟩ := hT (P (b i)) (hP i)
    obtain ⟨M, hM⟩ := exists_value_ae_eq_mul_coefficient hK hconst hsm (k + 2) e (b i) Ti
    refine ⟨M, hM.trans ((hi.ae_eq (W1p.hasWeakLineDerivOn_inner_gradient (u : W1p mu Omega 2)
      (P (b i)))).mono fun x hx ↦ ?_)⟩
    exact congrArg (matrixBilinearForm (a x) e (b i) * ·) hx
  let ann (x : E) := matrixBilinearForm (a x) e e
  have hann : ContDiff ℝ ∞ ann :=
    contDiff_matrixBilinearForm_apply hsm contDiff_const contDiff_const
  have hAnn (x : E) (hx : x ∈ closure (Omega : Set E)) : lam ≤ ann x :=
    closure_minimal (fun z hz ↦ by
      change lam ≤ ann z
      simpa only [ann, matrixBilinearForm_self, he, one_pow, mul_one] using ha.lower_bound hz e)
      (isClosed_le continuous_const hann.continuous) hx
  let S : Set E := {x | 0 < ann x}
  have hS : IsOpen S := isOpen_lt continuous_const hann.continuous
  have hΩS : closure (Omega : Set E) ⊆ S := fun x hx ↦ ha.pos.trans_le (hAnn x hx)
  obtain ⟨N, hNval⟩ := Wkp.exists_value_ae_eq_mul_of_eqOn_compl_isCompact (k + 2)
    hS hΩS hK (hann.contDiffOn.inv fun x hx ↦ ne_of_gt hx)
    (c := (matrixBilinearForm A e e)⁻¹)
    (fun x hx ↦ by change (matrixBilinearForm (a x) e e)⁻¹ = _; rw [hconst hx.2]) (Q - T)
  refine ⟨N, (W1p.hasWeakLineDerivOn_inner_gradient (u : W1p mu Omega 2) e).congr_ae_deriv ?_⟩
  filter_upwards [hNval, Wkp.value_sub (k + 2) Q T ▸ Lp.coeFn_sub (Wkp.value (k + 2) Q)
      (Wkp.value (k + 2) T), hQ, hTeq, ae_restrict_mem Omega.isOpen.measurableSet]
    with x h₁ h₂ h₃ h₄ hx
  rw [h₁, h₂, Pi.sub_apply, h₃, h₄, flux_eq_normal_add_tangential _ he]
  change _ = (ann x)⁻¹ * (ann x * _ + _ - _)
  rw [add_sub_cancel_right, inv_mul_cancel_left₀ (ne_of_gt (hΩS (subset_closure hx)))]

/-- Global `H^{k+2}` regularity of a homogeneous Dirichlet solution on a half-space, with
`H^k` forcing and smooth uniformly elliptic coefficients constant off a compact set. -/
private theorem UniformlyEllipticOn.exists_value_succ_succ_eq_of_isWeakSolutionDirichlet_halfSpace
    [DecidableEq ι]
    {ν : E} {c : ℝ} (hν : ν ≠ 0) (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set E) a lam Lam) (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ)
    (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j)) (k : ℕ)
    {F : Wkp mu Omega 2 k} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value k F) u) :
    ∃ W : Wkp mu Omega 2 (k + 2), Wkp.value (k + 2) W = W1p.value (u : W1p mu Omega 2) := by
  induction k generalizing u with
  | zero =>
    obtain ⟨_, _, hL, -⟩ := exists_lipschitzWith_and_norm_bound_of_eqOn_const hK hconst hsm
    obtain ⟨U, hU⟩ := ha.exists_lowerOrder_eq_of_halfSpace hν hΩ hL.lipschitzOnWith hu
    exact ⟨U, by
      rw [Wkp.value_succ, hU]
      exact Wkp.value_one (u : W1p mu Omega 2)⟩
  | succ k ih =>
    have hv : IsWeakSolutionDirichlet a 0 0 (Wkp.value k (Wkp.lowerOrder k F)) u := by
      rw [← Wkp.value_succ]
      exact hu
    obtain ⟨U, hU⟩ := ih hv
    let e : E := ‖ν‖⁻¹ • ν
    have he : ‖e‖ = 1 := norm_smul_inv_norm hν
    have hT (τ : E) (hτ : ⟪τ, e⟫_ℝ = 0) :
        ∃ T : Wkp mu Omega 2 (k + 2),
          HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (Wkp.value (k + 2) T) τ := by
      obtain ⟨d, G, hd, hdG⟩ :=
        exists_hasWeakLineDerivOn_and_energyFormH1_eq_of_eqOn_const hK hconst hsm k F
          U hU ((isWeakSolutionDirichlet_iff _ _).1 hu) τ
      have hτν : ⟪τ, ν⟫_ℝ = 0 := by
        change ⟪τ, ‖ν‖⁻¹ • ν⟫_ℝ = 0 at hτ
        rw [real_inner_smul_right] at hτ
        exact (mul_eq_zero.1 hτ).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 hν))
      have hd₁ : HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2))
          (W1p.value (Wkp.firstOrder k d)) τ := by simpa only [Wkp.value_firstOrder] using hd
      have hD (j : ι) : ∃ D : W1p mu Omega 2, HasWeakLineDerivOn mu Omega
          (W1p.value (u : W1p mu Omega 2)) (W1p.value D) (b j) := by
        obtain ⟨D, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) U (b j)
        exact ⟨Wkp.firstOrder k D, by simpa only [hU, Wkp.value_firstOrder] using hd⟩
      choose D hD using hD
      have hmem := W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn (by simp)
        (TauCeti.convex_of_halfSpace hΩ) (TauCeti.mapsTo_add_smul_of_halfSpace hΩ hτν)
        b u.property hD hd₁
      let d₀ : W1p0 mu Omega 2 := ⟨Wkp.firstOrder k d, hmem⟩
      have hd₀ : IsWeakSolutionDirichlet a 0 0 (Wkp.value k G) d₀ :=
        (isWeakSolutionDirichlet_iff _ _).2 hdG
      obtain ⟨T, hT⟩ := ih hd₀
      exact ⟨T, hT.symm ▸ hd₁⟩
    obtain ⟨N, hN⟩ := ha.exists_hasWeakLineDerivOn_normal_of_tangential hK hconst hsm k F
      hu U hU he hT
    exact (Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn (k + 2) _).2
      (exists_hasWeakLineDerivOn_of_normal_and_tangential (k + 2) he hN hT)

end TauCeti.PDE

end NormalRecovery

section Localization

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {lam Lam : ℝ}

local notation "E" => EuclideanSpace ℝ ι
local notation "𝔟" => EuclideanSpace.basisFun ι ℝ

/-- The localized forcing belongs to `H^k` when the original forcing belongs to `H^k`
and the solution belongs to `H^{k+1}`. -/
private theorem exists_value_ae_eq_localizedForcing_of_order
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j)) {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (k : ℕ)
    (F : Wkp mu Omega 2 k) (U : Wkp mu Omega 2 (k + 1)) :
    ∃ G : Wkp mu Omega 2 k, Wkp.value k G =ᵐ[mu.restrict Omega]
      localizedForcing a ψ (Wkp.value k F) (Wkp.firstOrder k U) := by
  set u := Wkp.firstOrder k U
  let c (i : ι) (x : E) :=
    -(matrixBilinearForm (a x) (𝔟 i) (∇ ψ x) + matrixBilinearForm (a x) (∇ ψ x) (𝔟 i))
  have hgψ : ContDiff ℝ ∞ (∇ ψ) := hψ.gradient_right (m := ∞) (by simp)
  have hc (i : ι) : ContDiff ℝ ∞ (c i) :=
    ((contDiff_matrixBilinearForm_apply ha contDiff_const hgψ).add
      (contDiff_matrixBilinearForm_apply ha hgψ contDiff_const)).neg
  have hcc (i : ι) : HasCompactSupport (c i) := hψc.mono' fun x hx ↦ by
    by_contra hxψ
    exact hx (by simp [c, gradient_of_notMem_tsupport hxψ])
  have hc₀c : HasCompactSupport (fun x ↦ -divMatrixGradient a ψ x) := hψc.mono' fun x hx ↦ by
    by_contra hxψ
    exact hx (by simp [divMatrixGradient_eq_zero_of_notMem_tsupport hxψ])
  choose D hD using fun i ↦ Wkp.exists_hasWeakLineDerivOn_value k U (𝔟 i)
  have hDval (i : ι) : Wkp.value k (D i) =ᵐ[mu.restrict Omega]
      fun x ↦ ⟪W1p.gradient u x, 𝔟 i⟫_ℝ := by
    have h := (W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (𝔟 i)
    simpa only [innerSL_apply_apply] using (hD i).ae_eq (Wkp.value_firstOrder k U ▸ h)
  obtain ⟨T, hT⟩ := Wkp.exists_value_ae_eq_mul_of_hasCompactSupport k hψ hψc F
  choose S hS using fun i ↦
    Wkp.exists_value_ae_eq_mul_of_hasCompactSupport k (hc i) (hcc i) (D i)
  obtain ⟨Z, hZ⟩ := Wkp.exists_value_ae_eq_mul_of_hasCompactSupport k
    (contDiff_divMatrixGradient (k := ∞) (fun i j ↦ (ha i j).of_le (by simp))
      (hψ.of_le (by simp))).neg hc₀c (Wkp.lowerOrder k U)
  refine ⟨T + ∑ i, S i + Z, ?_⟩
  filter_upwards [Wkp.value_add_ae k (T + ∑ i, S i) Z, Wkp.value_add_ae k T (∑ i, S i),
    Wkp.value_finsetSum_ae k Finset.univ S, hT, hZ, ae_all_iff.2 hS, ae_all_iff.2 hDval]
    with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hB₁ : ∑ i, ⟪W1p.gradient u x, 𝔟 i⟫_ℝ * matrixBilinearForm (a x) (𝔟 i) (∇ ψ x) =
      matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x) := sum_inner_mul_matrixBilinearForm _ _
  have hB₂ : ∑ i, ⟪W1p.gradient u x, 𝔟 i⟫_ℝ * matrixBilinearForm (a x) (∇ ψ x) (𝔟 i) =
      matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x) := by
    simpa only [matrixBilinearForm_transpose_apply] using
      sum_inner_mul_matrixBilinearForm (A := (a x).transpose) (W1p.gradient u x) (∇ ψ x)
  have hval : Wkp.value k (Wkp.lowerOrder k U) = W1p.value u :=
    (Wkp.value_succ k U).symm.trans (Wkp.value_firstOrder k U).symm
  simp only [Pi.add_apply] at h₁ h₂
  rw [h₁, h₂, h₃, h₄, h₅, hval, localizedForcing_def]
  simp only [h₆, h₇, c, ← hB₁, ← hB₂, neg_add, neg_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp only [mul_comm _ ⟪W1p.gradient u x, _⟫_ℝ]
  ring

/-- Extend an elliptic field near a compact set by a smooth field which is constant off
a compact set. Ellipticity is inherited on any set whose intersection with the region
of agreement lies in the original elliptic region. -/
private theorem UniformlyEllipticOn.exists_contDiff_eqOn_inter_const_off_compact [DecidableEq ι]
    {S H C : Set E} {U : Opens E} (ha : UniformlyEllipticOn S a lam Lam)
    (hsm : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hHU : H ∩ U ⊆ S) (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ a' : E → Matrix ι ι ℝ, ∃ K : Set E, ∃ L : ℝ≥0, ∃ M : ℝ,
      IsCompact K ∧ EqOn a' (fun _ ↦ lam • (1 : Matrix ι ι ℝ)) Kᶜ ∧
      UniformlyEllipticOn H a' lam Lam ∧ (∀ i j, ContDiff ℝ ∞ (fun x ↦ a' x i j)) ∧
      LipschitzWith L (fun x ↦ matrixBilinearForm (a' x)) ∧
      (∀ x, ‖matrixBilinearForm (a' x)‖ ≤ M) ∧ EqOn a' a C := by
  classical
  obtain ⟨χ, hχ, hr, hχ1, hχc, hχs⟩ := hC.exists_contDiff_cutoff U.isOpen hCU
  let B : Matrix ι ι ℝ := lam • 1
  let D (x : E) := χ x • (a x - B)
  let a' (x : E) := D x + B
  let K := tsupport χ
  have hD₀ (x : E) (hx : x ∉ K) : D x = 0 := by
    simp [D, image_eq_zero_of_notMem_tsupport hx]
  have hD (i j : ι) : ContDiff ℝ ∞ (fun x ↦ D x i j) := by
    exact ((hsm i j).sub contDiffOn_const).contDiff_smul_of_tsupport_subset U.isOpen
      hχ.contDiffOn hχs
  have hconst : EqOn a' (fun _ ↦ B) Kᶜ := fun x hx ↦ by simp [a', hD₀ x hx]
  have hsm' (i j : ι) : ContDiff ℝ ∞ (fun x ↦ a' x i j) :=
    (hD i j).add contDiff_const
  obtain ⟨L, M, hL, hM⟩ :=
    exists_lipschitzWith_and_norm_bound_of_eqOn_const hχc.isCompact hconst hsm'
  have hblend (x : E) : χ x • a x + (1 - χ x) • B = a' x := by
    simp only [a', D, smul_sub, sub_smul, one_smul]
    abel
  have hH : UniformlyEllipticOn H a' lam Lam := by
    have hB := uniformlyEllipticOn_const_smul_one (n := ι) (univ : Set E) ha.pos le_rfl ha.le
    have ht := ha.smul_add_one_sub_smul hB (χ := fun x ↦ if x ∈ H then χ x else 0)
      (fun x ↦ by split_ifs <;> simp [hr (mem_range_self x)])
      (fun x hx ↦ by
        split_ifs with hxH
        · exact image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hHU ⟨hxH, hχs ht⟩))
        · rfl)
    exact (ht.mono_set (subset_univ H)).congr fun x hx ↦ by
      simp only [hx, ite_true, ← hblend, B]
  refine ⟨a', K, L, M, hχc.isCompact, hconst, hH, hsm', hL, hM, fun x hx ↦ ?_⟩
  have hxχ : χ x = 1 := interior_subset (hχ1 hx)
  change a' x = a x
  rw [← hblend, hxχ, one_smul, sub_self, zero_smul, add_zero]

/-- A Dirichlet localization on the half-space preserves the Sobolev order of the forcing. -/
private theorem exists_isWeakSolutionDirichlet_extendByZero_of_order {H : Opens E} {M : ℝ} {L : ℝ≥0}
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hL : LipschitzWith L (fun x ↦ matrixBilinearForm (a x)))
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j)) (hΩH : Omega ≤ H)
    (k : ℕ) (F : Wkp mu Omega 2 k) (U : Wkp mu Omega 2 (k + 1))
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (Wkp.firstOrder k U) (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value k F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set E)) {N : ℝ} (hN : 0 ≤ N)
    (hψN : ∀ x ∈ Omega, |ψ x| ≤ N) (hgradN : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ N)
    (hmem : W1p.contDiffSMul ψ hψ hN hψN hgradN (Wkp.firstOrder k U) ∈
      w1p0Submodule mu Omega 2) :
    ∃ w : W1p0 mu H 2, ∃ G : Wkp mu H 2 k, IsWeakSolutionDirichlet a 0 0 (Wkp.value k G) w ∧
      W1p.value (w : W1p mu H 2) =ᵐ[mu.restrict H]
        (Omega : Set E).indicator (fun x ↦ ψ x * W1p.value (Wkp.firstOrder k U) x) := by
  obtain ⟨w, g, hw, hg, hwv, -⟩ :=
    exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem
      hM hL hΩH hu hψ hψc hts hN hψN hgradN hmem
  obtain ⟨q, hq⟩ := exists_value_ae_eq_localizedForcing_of_order ha hψ hψc k F U
  have hq₀ : ∀ᵐ x ∂mu.restrict Omega, x ∉ tsupport ψ → Wkp.value k q x = 0 := by
    filter_upwards [hq] with x hx h
    rw [hx, localizedForcing_def, image_eq_zero_of_notMem_tsupport h, gradient_of_notMem_tsupport h,
      divMatrixGradient_eq_zero_of_notMem_tsupport h]
    simp
  obtain ⟨G, hG⟩ := Wkp.exists_value_ae_eq_indicator_of_isClosed (V := H)
    (isClosed_tsupport ψ) (fun x hx ↦ hts ⟨hx.2, hx.1⟩) k q hq₀
  have hval : Wkp.value k G = g := by
    refine Lp.ext ?_
    filter_upwards [hG, hg, ae_restrict_of_ae ((ae_restrict_iff' Omega.isOpen.measurableSet).1 hq)]
      with x h₁ h₂ h₃
    rw [h₁, h₂]
    by_cases hx : x ∈ (Omega : Set E)
    · rw [indicator_of_mem hx, indicator_of_mem hx, h₃ hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  exact ⟨w, G, hval ▸ hw, hwv⟩

end TauCeti.PDE

end Localization

section LocalRegularity

open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff Gradient InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega H U V : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c₀ : ℝ} {ν : EuclideanSpace ℝ ι}
  {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}

local notation "E" => EuclideanSpace ℝ ι

private theorem exists_value_eq_value_restrictL_of_halfSpace_of_order
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (k : ℕ) {W : Opens E} (hW : IsCompact (closure (W : Set E)))
    (hWU : closure (W : Set E) ⊆ U) (hV : IsCompact (closure (V : Set E)))
    (hVW : closure (V : Set E) ⊆ W) (Z : Wkp mu (Omega ⊓ W) 2 (k + 1))
    (hZ : Wkp.value (k + 1) Z = W1p.value (W1p.restrictL inf_le_left u)) :
    ∃ Q : Wkp mu (Omega ⊓ V) 2 (k + 2),
      Wkp.value (k + 2) Q = W1p.value (W1p.restrictL inf_le_left u) := by
  have hHU : (H : Set E) ∩ U ⊆ (Omega : Set E) ∩ U := hΩU.ge
  obtain ⟨a', K, L, M, hK, hconst, ha', hsm', hL, hM, hagree⟩ :=
    ha.exists_contDiff_eqOn_inter_const_off_compact hsmooth hHU hW hWU
  let D := Omega ⊓ W
  have hD : D ≤ Omega := inf_le_left
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hΩH (x : E) (hx : x ∈ U) : x ∈ Omega ↔ x ∈ H := by
    change x ∈ (Omega : Set E) ↔ x ∈ (H : Set E)
    have hx' : x ∈ (U : Set E) := hx
    simpa only [mem_inter_iff, hx', and_true] using Set.ext_iff.1 hΩU x
  have hDU : D ≤ Omega ⊓ U := fun _ hx ↦ ⟨hx.1, hWsub hx.2⟩
  have hDH : D ≤ H := fun x hx ↦ (hΩH x (hWsub hx.2)).1 hx.1
  have hz₁ : Wkp.firstOrder k Z = W1p.restrictL hD u :=
    W1p.ext_value ((Wkp.value_firstOrder k Z).trans hZ)
  obtain ⟨F, hF⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := mu) (Omega := D)
    (p := 2) k U.isOpen (hf.of_le (by simp)) hW
    (fun x hx ↦ subset_closure hx.2) hWU
  have huD (v : W1p0 mu D 2) :
      energyFormH1 a' 0 0 (Wkp.firstOrder k Z) (v : W1p mu D 2) =
        ∫ x in D, Wkp.value k F x * W1p.value (v : W1p mu D 2) x ∂mu := by
    rw [hz₁, ← W1p.restrictL_restrictL inf_le_left hDU,
      energyFormH1_restrictL_eq_setIntegral_of_eqOn hDU
      (fun x hx ↦ hagree (subset_closure hx.2)) hu]
    exact integral_congr_ae (hF.mono fun x hx ↦ congrArg (· * W1p.value (v : W1p mu D 2) x) hx.symm)
  obtain ⟨ψ, N, hψ, -, hψ1, hψc, hψs, hN, hψN, hgradN⟩ :=
    hV.exists_contDiff_cutoff_with_bounds W.isOpen hVW
  obtain ⟨d, hd⟩ := W1p.exists_w1p0_value_ae_eq_mul_restrictL hWsub hu0 hψ hψc hψs
  have hψu : W1p.contDiffSMul ψ hψ hN (fun x _ ↦ hψN x) (fun x _ ↦ hgradN x)
      (Wkp.firstOrder k Z) = (d : W1p mu D 2) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hψ hN (fun x _ ↦ hψN x) (fun x _ ↦ hgradN x)
      (Wkp.firstOrder k Z), hd] with x h₁ h₂
    rw [h₁, h₂, hz₁, smul_eq_mul]
  have hts : tsupport ψ ∩ H ⊆ (D : Set E) := fun x hx ↦
    ⟨(hΩH x (hWsub (hψs hx.1))).2 hx.2, hψs hx.1⟩
  obtain ⟨w, G, hw, hwv⟩ := exists_isWeakSolutionDirichlet_extendByZero_of_order
    hM hL hsm' hDH k F Z huD hψ hψc hts hN _ _ (hψu ▸ d.property)
  obtain ⟨Q, hQ⟩ := ha'.exists_value_succ_succ_eq_of_isWeakSolutionDirichlet_halfSpace
    hν hH hK hconst hsm' k hw
  have hVD : Omega ⊓ V ≤ D := fun _ hx ↦ ⟨hx.1, hVW (subset_closure hx.2)⟩
  have hVH : Omega ⊓ V ≤ H := hVD.trans hDH
  refine ⟨Wkp.restrictL hVH (k + 2) Q, Lp.ext ?_⟩
  filter_upwards [Wkp.value_restrictL_ae hVH (k + 2) Q,
    ae_restrict_of_ae_restrict_of_subset hVH hwv,
    ae_restrict_of_ae_restrict_of_subset hVD (W1p.value_restrictL_ae hD u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
    ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x h₁ h₂ h₃ h₄ hx
  have hψx : ψ x = 1 := interior_subset (hψ1 (subset_closure hx.2))
  rw [h₁, hQ, h₂, indicator_of_mem (hVD hx), hψx, one_mul, hz₁, h₃, h₄]

private theorem exists_value_eq_value_restrictL_allOrders_of_ne_zero
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  have high (k : ℕ) {V : Opens E} (hV : IsCompact (closure (V : Set E)))
      (hVU : closure (V : Set E) ⊆ U) :
      ∃ Q : Wkp mu (Omega ⊓ V) 2 (k + 2),
        Wkp.value (k + 2) Q = W1p.value (W1p.restrictL inf_le_left u) := by
    induction k generalizing V with
    | zero =>
      obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
        exists_open_between_and_isCompact_closure hV U.isOpen hVU
      let W : Opens E := ⟨W₀, hWo⟩
      exact exists_value_eq_value_restrictL_of_halfSpace_of_order hν hH hΩU ha hsmooth hf hu hu0
        0 (W := W) hW hWU hV hVW (W1p.restrictL inf_le_left u)
        (Wkp.value_one (W1p.restrictL (inf_le_left : Omega ⊓ W ≤ Omega) u))
    | succ k ih =>
      obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
        exists_open_between_and_isCompact_closure hV U.isOpen hVU
      let W : Opens E := ⟨W₀, hWo⟩
      obtain ⟨Z, hZ⟩ := ih (V := W) hW hWU
      exact exists_value_eq_value_restrictL_of_halfSpace_of_order hν hH hΩU ha hsmooth hf hu hu0
        (k + 1) hW hWU hV hVW Z hZ
  intro k
  obtain ⟨Q, hQ⟩ := high k hV hVU
  exact ⟨Wkp.toOrderL (show k ≤ k + 2 by omega) Q,
    (Wkp.value_toOrderL _ Q).trans hQ⟩

private theorem exists_value_eq_value_restrictL_allOrders_of_interior
    (hUΩ : U ≤ Omega) (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  let W : Opens E := ⟨W₀, hWo⟩
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hWΩU : W ≤ Omega ⊓ U := fun _ hx ↦ ⟨hUΩ (hWsub hx), hWsub hx⟩
  have hWΩ : W ≤ Omega := hWΩU.trans inf_le_left
  have haW : UniformlyEllipticOn (W : Set E) a lam Lam := ha.mono_set hWΩU
  have hY : closure ((Omega ⊓ V : Opens E) : Set E) ⊆ closure (V : Set E) :=
    closure_mono inter_subset_right
  intro k
  obtain ⟨F, hF⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := mu) (Omega := W)
    (p := 2) k U.isOpen (hf.of_le (by simp)) hW subset_closure hWU
  have huW (v : W1p0 mu W 2) :
      energyFormH1 a 0 0 (W1p.restrictL hWΩ u) (v : W1p mu W 2) =
        ∫ x in W, Wkp.value k F x * W1p.value (v : W1p mu W 2) x ∂mu := by
    rw [← W1p.restrictL_restrictL inf_le_left hWΩU,
      energyFormH1_restrictL_eq_setIntegral hWΩU hu]
    exact integral_congr_ae (hF.mono fun x hx ↦
      congrArg (· * W1p.value (v : W1p mu W 2) x) hx.symm)
  obtain ⟨Q, hQ⟩ := haW.exists_value_eq_value_restrictL_of_contDiffOn k
    (fun i j ↦ ((hsmooth i j).mono hWsub).of_le (by simp))
    (b := 0) (c := 0) contDiffOn_const contDiffOn_const huW
    (V := Omega ⊓ V) (hV.of_isClosed_subset isClosed_closure hY) (hY.trans hVW)
  refine ⟨Wkp.toOrderL (show k ≤ k + 2 by omega) Q, ?_⟩
  rw [Wkp.value_toOrderL, hQ, W1p.restrictL_restrictL]

private theorem exists_value_eq_value_restrictL_allOrders_of_uniformlyElliptic
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ν ≠ 0 → ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  by_cases hν : ν = 0
  · have hH₀ (x : E) : x ∈ H ↔ c₀ < 0 := by simpa [hν] using hH x
    have hΩH (x : E) (hx : x ∈ (U : Set E)) : x ∈ Omega ↔ x ∈ H := by
      change x ∈ (Omega : Set E) ↔ x ∈ (H : Set E)
      simpa only [mem_inter_iff, hx, and_true] using Set.ext_iff.1 hΩU x
    by_cases hc : c₀ < 0
    · exact exists_value_eq_value_restrictL_allOrders_of_interior
        (fun x hx ↦ (hΩH x hx).2 ((hH₀ x).2 hc)) ha hsmooth hf hu hV hVU
    · intro k
      refine ⟨0, Lp.ext ?_⟩
      filter_upwards [ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x hx
      exact (hc ((hH₀ x).1 ((hΩH x (hVU (subset_closure hx.2))).1 hx.1))).elim
  · exact exists_value_eq_value_restrictL_allOrders_of_ne_zero
      hν hH hΩU ha hsmooth hf hu (hu0 hν) hV hVU


private theorem exists_uniformlyEllipticOn_inter_of_isCompact_closure {W : Opens E}
    (hW : IsCompact (closure (W : Set E))) (hWU : closure (W : Set E) ⊆ U)
    (hlam : 0 < lam) (ha : ∀ x ∈ (Omega : Set E) ∩ U, ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ (a x).toQuadraticForm' v)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U) :
    ∃ Lam, UniformlyEllipticOn ((Omega : Set E) ∩ W) a lam Lam := by
  choose C hC using fun i j ↦ hW.exists_bound_of_continuousOn
    ((hsmooth i j).continuousOn.mono hWU)
  let M := ∑ i, ∑ j, C i j
  refine ⟨max lam M, UniformlyEllipticOn.of_bounds hlam (le_max_left _ _) ?_ ?_⟩
  · intro x hx v
    exact ha x ⟨hx.1, hWU (subset_closure hx.2)⟩ v
  · intro x hx v w
    have hB : ‖matrixBilinearForm (a x)‖ ≤ M :=
      (norm_matrixBilinearForm_le_sum_abs _).trans (Finset.sum_le_sum fun i _ ↦
        Finset.sum_le_sum fun j _ ↦ by
          simpa only [Real.norm_eq_abs] using hC i j x (subset_closure hx.2))
    simpa only [matrixBilinearForm_apply, Real.norm_eq_abs] using
      (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le
        (hB.trans (le_max_right lam M)) (le_refl ‖v‖) (le_refl ‖w‖)

omit [DecidableEq ι] in
/-- A scalar weak solution with smooth coefficients and forcing has every finite Sobolev
order locally up to a flat homogeneous Dirichlet boundary.

The weak equation and the uniform positive lower bound for the coefficient field are required
only on the chart patch. Smoothness bounds the coefficients on a smaller compact neighbourhood.
A zero normal gives an interior or empty patch, for which there is no trace condition. -/
theorem exists_value_eq_value_restrictL_allOrders_of_halfSpace
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (hlam : 0 < lam) (ha : ∀ x ∈ (Omega : Set E) ∩ U, ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ matrixBilinearForm (a x) v v)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ν ≠ 0 → ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  classical
  obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  let W : Opens E := ⟨W₀, hWo⟩
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hWΩU : Omega ⊓ W ≤ Omega ⊓ U := fun _ hx ↦ ⟨hx.1, hWsub hx.2⟩
  have hΩW : (Omega : Set E) ∩ W = (H : Set E) ∩ W := by
    ext x
    constructor
    · intro hx
      exact ⟨((Set.ext_iff.1 hΩU x).1 ⟨hx.1, hWsub hx.2⟩).1, hx.2⟩
    · intro hx
      exact ⟨((Set.ext_iff.1 hΩU x).2 ⟨hx.1, hWsub hx.2⟩).1, hx.2⟩
  obtain ⟨_, haW⟩ :=
    exists_uniformlyEllipticOn_inter_of_isCompact_closure (W := W) hW hWU hlam
      (fun x hx v ↦ by simpa only [matrixBilinearForm_self] using ha x hx v) hsmooth
  have huW (v : W1p0 mu (Omega ⊓ W) 2) :
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ W) 2) =
        ∫ x in Omega ⊓ W, f x * W1p.value (v : W1p mu (Omega ⊓ W) 2) x ∂mu := by
    rw [← W1p.restrictL_restrictL inf_le_left hWΩU]
    exact energyFormH1_restrictL_eq_setIntegral hWΩU hu v
  exact exists_value_eq_value_restrictL_allOrders_of_uniformlyElliptic hH hΩW haW
    (fun i j ↦ (hsmooth i j).mono hWsub) (hf.mono hWsub) huW
    (fun hν ψ hψ hψc hψs ↦ hu0 hν ψ hψ hψc (hψs.trans hWsub)) hV hVW

end TauCeti.PDE

end LocalRegularity
