/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
import TauCeti.Analysis.Calculus.IteratedGradient.Integral
import TauCeti.Analysis.Calculus.Taylor.Pairing.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Polynomiality of Taylor-monomial and contracted-field pairings

On `EuclideanSpace ℝ ι`, powerset combinations `x ↦ ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_ℝ) * c u`
of degree `t.card ≤ m` lie in `TauCeti.polynomialsDegLE ι m`
(`TauCeti.sum_powerset_prod_inner_mul_mem_polynomialsDegLE`), so zero-order shifted inner-product
pairings, iterated-derivative Taylor-monomial pairings, and shifted full-contraction pairings all
belong to `polynomialsDegLE ι m`.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory IteratedGradient
open scoped ContDiff InnerProductSpace

variable {ι : Type*} [Fintype ι]

/-- Any powerset combination `x ↦ ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_ℝ) * c u` with `t.card ≤ m`
belongs to `TauCeti.polynomialsDegLE ι m`. -/
theorem sum_powerset_prod_inner_mul_mem_polynomialsDegLE {α : Type*} {m : ℕ}
    (t : Finset α) (htm : t.card ≤ m) (a : α → EuclideanSpace ℝ ι) (c : Finset α → ℝ) :
    (fun x => ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_ℝ) * c u) ∈ polynomialsDegLE ι m := by
  have hconv : (fun x => ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_ℝ) * c u) =
      ∑ u ∈ t.powerset, c u • fun x => ∏ l ∈ u, ⟪a l, x⟫_ℝ := by
    ext x; simp [Finset.sum_apply, mul_comm]
  rw [hconv]
  exact Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _
    (prod_inner_mem_polynomialsDegLE u a
      ((Finset.card_le_card (Finset.mem_powerset.1 hu)).trans htm))

variable [MeasurableSpace (EuclideanSpace ℝ ι)]

/-- Zero-order shifted inner-product pairings of degree `t.card ≤ m` with integrable moments lie in
`TauCeti.polynomialsDegLE ι m`. -/
theorem setIntegral_prod_inner_sub_right_mul_mem_polynomialsDegLE {α : Type*}
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)} {m : ℕ} (t : Finset α)
    (htm : t.card ≤ m) (a : α → EuclideanSpace ℝ ι) {w : EuclideanSpace ℝ ι → ℝ}
    (hw : ∀ v ⊆ t, IntegrableOn (fun y => (∏ l ∈ v, ⟪a l, y⟫_ℝ) * w y) s μ) :
    (fun x => ∫ y in s, (∏ l ∈ t, ⟪a l, x - y⟫_ℝ) * w y ∂μ) ∈ polynomialsDegLE ι m := by
  classical
  rw [funext (setIntegral_prod_inner_sub_right_mul_eq_sum t a hw)]
  exact sum_powerset_prod_inner_mul_mem_polynomialsDegLE t htm a _

variable [OpensMeasurableSpace (EuclideanSpace ℝ ι)]

/-- Taylor-monomial pairings (`iteratedFDerivAlong` form) of degree `t.card ≤ m` belong to
`TauCeti.polynomialsDegLE ι m`. -/
theorem setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE {α : Type*}
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)} {m : ℕ} (t : Finset α)
    (htm : t.card ≤ m) (a : α → EuclideanSpace ℝ ι) {n : ℕ∞ω} {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (vs : List (EuclideanSpace ℝ ι)) (hvs : vs.length ≤ n)
    {v : EuclideanSpace ℝ ι → ℝ} (hv : LocallyIntegrableOn v s μ) :
    (fun x => ∫ y in s, iteratedFDerivAlong ℝ vs
      (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ) ∈ polynomialsDegLE ι m := by
  classical
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum t a hφ hφc hφs vs hvs hv)]
  exact sum_powerset_prod_inner_mul_mem_polynomialsDegLE t htm a _

/-- `iteratedFDeriv` form of
`TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE`. -/
theorem setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)} {j m : ℕ} (hjm : j ≤ m)
    (a : Fin j → EuclideanSpace ℝ ι) {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ j φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s) {v : EuclideanSpace ℝ ι → ℝ}
    (hv : LocallyIntegrableOn v s μ) :
    (fun x => ∫ y in s, iteratedFDeriv ℝ j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z)
      y a * v y ∂μ) ∈ polynomialsDegLE ι m := by
  simp_rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ v]
  exact setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE Finset.univ
    (by simpa using hjm) a hφ hφc hφs (List.ofFn a) (by simp) hv

/-- Integrating `fullContractL k (x - y) (G y) * φ y` against locally integrable `G` on `s` and
compactly supported `φ` continuous on `tsupport φ` lies in `polynomialsDegLE ι m` (`k + 1 ≤ m`). -/
theorem setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)} {k m : ℕ} (hkm : k + 1 ≤ m)
    {G : EuclideanSpace ℝ ι → IteratedGradient (EuclideanSpace ℝ ι) k}
    (hG : LocallyIntegrableOn G s μ) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContinuousOn φ (tsupport φ)) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s) :
    (fun x => ∫ y in s, fullContractL k (x - y) (G y) * φ y ∂μ) ∈ polynomialsDegLE ι m := by
  let b := EuclideanSpace.basisFun ι ℝ
  have hexp : (fun x => ∫ y in s, fullContractL k (x - y) (G y) * φ y ∂μ) =
      ∑ I : Fin (k + 1) → ι, fun x => ∫ y in s, (∏ l : Fin (k + 1), ⟪b (I l), x - y⟫_ℝ) *
        (φ y * evalTupleL k (b ∘ I) (G y)) ∂μ := by
    ext x; simpa only [Finset.sum_apply, mul_assoc] using
      setIntegral_fullContractL_sub_mul_eq_sum b k hG hφ hφc hφs x
  rw [hexp]
  refine Submodule.sum_mem _ fun I _ =>
    setIntegral_prod_inner_sub_right_mul_mem_polynomialsDegLE Finset.univ (by simpa using hkm)
      (b ∘ I) fun v _ => ?_
  have heq : (fun y => φ y • ((∏ l ∈ v, ⟪b (I l), y⟫_ℝ) • evalTupleL k (b ∘ I)) (G y)) =
      fun y => (∏ l ∈ v, ⟪(b ∘ I) l, y⟫_ℝ) * (φ y * evalTupleL k (b ∘ I) (G y)) :=
    funext fun _ => by simp only [smul_apply, smul_eq_mul, Function.comp_apply]; ring
  exact heq ▸ (hG.integrable_smul_clm_apply_of_hasCompactSupport hφ hφc hφs
    ((continuous_finsetProd v fun l _ => (innerSL ℝ (b (I l))).continuous).continuousOn.smul
      continuousOn_const)).integrableOn

end TauCeti
