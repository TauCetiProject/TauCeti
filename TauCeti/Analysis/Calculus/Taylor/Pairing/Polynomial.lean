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

On `EuclideanSpace ℝ ι`, every Taylor-monomial integral pairing of degree at most `m` against a
locally integrable function on an arbitrary set `s` expands via powersets into a linear combination
of finite products of inner products
(`TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum`), and therefore lies in the
bounded-degree polynomial subspace `TauCeti.polynomialsDegLE ι m`.

The same holds for zero-order shifted inner-product pairings against arbitrary weights with
integrable monomial moments (`TauCeti.setIntegral_prod_inner_sub_right_mul_mem_polynomialsDegLE`),
and for shifted full-contraction integrals
`x ↦ ∫ y in s, fullContractL k (x - y) (G y) * φ y ∂μ` whenever `k + 1 ≤ m`, using the
orthonormal-basis expansion `TauCeti.setIntegral_fullContractL_sub_mul_eq_sum` with `φ` only
continuous on `tsupport φ` (no differentiability or global continuity required on `φ`).

## Main declarations

* `TauCeti.setIntegral_prod_inner_sub_right_mul_mem_polynomialsDegLE`: a zero-order shifted
  inner-product pairing of degree `t.card ≤ m` against an arbitrary weight with integrable monomial
  moments belongs to `polynomialsDegLE ι m`.
* `TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE`: a single
  Taylor-monomial pairing (`iteratedFDerivAlong` form) of degree `t.card ≤ m` belongs to
  `polynomialsDegLE ι m`.
* `TauCeti.setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE`: `iteratedFDeriv`
  form for a `Fin j`-indexed tuple with `j ≤ m`.
* `TauCeti.sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE`: finite
  tuple-sum corollary.
* `TauCeti.setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE`: shifted full-contraction
  pairing of a locally integrable `IteratedGradient` field against a compactly supported weight
  continuous on its `tsupport` belongs to `polynomialsDegLE ι m` when `k + 1 ≤ m`.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory
open scoped ContDiff InnerProductSpace

section Polynomiality

variable {ι : Type*} [Fintype ι] [MeasurableSpace (EuclideanSpace ℝ ι)]

/-- Every zero-order shifted inner-product integral pairing of degree `t.card ≤ m` against an
arbitrary weight `w` with integrable monomial moments on `s` defines a polynomial function in
`TauCeti.polynomialsDegLE ι m`. -/
theorem setIntegral_prod_inner_sub_right_mul_mem_polynomialsDegLE {α : Type*}
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)} {m : ℕ} (t : Finset α)
    (htm : t.card ≤ m) (a : α → EuclideanSpace ℝ ι) {w : EuclideanSpace ℝ ι → ℝ}
    (hw : ∀ v ⊆ t, IntegrableOn (fun y => (∏ l ∈ v, ⟪a l, y⟫_ℝ) * w y) s μ) :
    (fun x => ∫ y in s, (∏ l ∈ t, ⟪a l, x - y⟫_ℝ) * w y ∂μ) ∈ polynomialsDegLE ι m := by
  classical
  have hconv : (fun x => ∫ y in s, (∏ l ∈ t, ⟪a l, x - y⟫_ℝ) * w y ∂μ) =
      ∑ u ∈ t.powerset,
        (∫ y in s, (∏ l ∈ t \ u, -⟪a l, y⟫_ℝ) * w y ∂μ) • fun x => ∏ l ∈ u, ⟪a l, x⟫_ℝ := by
    ext x
    rw [setIntegral_prod_inner_sub_right_mul_eq_sum t a hw x, Finset.sum_apply]
    exact Finset.sum_congr rfl fun u _ => by simp [smul_eq_mul, mul_comm]
  rw [hconv]
  exact Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _
    (prod_inner_mem_polynomialsDegLE u a
      ((Finset.card_le_card (Finset.mem_powerset.1 hu)).trans htm))

variable [OpensMeasurableSpace (EuclideanSpace ℝ ι)]

/-- Every single Taylor-monomial pairing (`iteratedFDerivAlong` form) of degree `t.card ≤ m`
against a locally integrable function on an arbitrary subset `s` of `EuclideanSpace ℝ ι` defines a
polynomial function in `TauCeti.polynomialsDegLE ι m`. -/
theorem setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE {α : Type*}
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)} {m : ℕ} (t : Finset α)
    (htm : t.card ≤ m) (a : α → EuclideanSpace ℝ ι) {n : ℕ∞ω} {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (vs : List (EuclideanSpace ℝ ι)) (hvs : vs.length ≤ n)
    {v : EuclideanSpace ℝ ι → ℝ} (hv : LocallyIntegrableOn v s μ) :
    (fun x => ∫ y in s, iteratedFDerivAlong ℝ vs
      (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ) ∈
      polynomialsDegLE ι m := by
  classical
  have hconv : (fun x => ∫ y in s, iteratedFDerivAlong ℝ vs
        (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ) =
      ∑ u ∈ t.powerset,
        (∫ y in s, iteratedFDerivAlong ℝ vs
          (fun z => (∏ l ∈ t \ u, -⟪a l, z⟫_ℝ) * φ z) y * v y ∂μ) •
          fun x => ∏ l ∈ u, ⟪a l, x⟫_ℝ := by
    ext x
    rw [setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum t a hφ hφc hφs vs hvs hv x,
      Finset.sum_apply]
    exact Finset.sum_congr rfl fun u _ => by simp [smul_eq_mul, mul_comm]
  rw [hconv]
  exact Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _
    (prod_inner_mem_polynomialsDegLE u a
      ((Finset.card_le_card (Finset.mem_powerset.1 hu)).trans htm))

/-- `iteratedFDeriv` form of
`TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE`. -/
theorem setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)} {j m : ℕ}
    (hjm : j ≤ m) (a : Fin j → EuclideanSpace ℝ ι) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ j φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    {v : EuclideanSpace ℝ ι → ℝ} (hv : LocallyIntegrableOn v s μ) :
    (fun x => ∫ y in s, iteratedFDeriv ℝ j
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y a * v y ∂μ) ∈
      polynomialsDegLE ι m := by
  simp_rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ v]
  exact setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE Finset.univ
    (by simpa using hjm) a hφ hφc hφs (List.ofFn a) (by simp) hv

/-- Finite tuple-sum corollary of
`TauCeti.setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE`. -/
theorem sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE
    {κ : Type*} [Fintype κ] (b : κ → EuclideanSpace ℝ ι)
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)} {j m : ℕ}
    (hjm : j ≤ m) {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ j φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    {v : EuclideanSpace ℝ ι → ℝ} (hv : LocallyIntegrableOn v s μ) :
    (fun x => ∑ I : Fin j → κ,
      ∫ y in s, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ) ∈
      polynomialsDegLE ι m := by
  have hsum_fn : (fun x => ∑ I : Fin j → κ,
        ∫ y in s, iteratedFDeriv ℝ j
          (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ) =
      ∑ I : Fin j → κ, fun x => ∫ y in s, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ := by
    ext x; simp
  rw [hsum_fn]
  exact Submodule.sum_mem (polynomialsDegLE ι m) fun I _ =>
    setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE hjm (b ∘ I) hφ
      hφc hφs hv

/-- Integrating `fullContractL k (x - y) (G y) * φ y` against any locally integrable field `G` on
an arbitrary set `s` and compactly supported weight `φ` continuous on `tsupport φ` gives a
polynomial of total degree at most `m` whenever `k + 1 ≤ m`. No differentiability or global
continuity of `φ` is needed. -/
theorem setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)}
    {k m : ℕ} (hkm : k + 1 ≤ m)
    {G : EuclideanSpace ℝ ι → IteratedGradient (EuclideanSpace ℝ ι) k}
    (hG : LocallyIntegrableOn G s μ) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContinuousOn φ (tsupport φ)) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s) :
    (fun x => ∫ y in s, IteratedGradient.fullContractL k (x - y) (G y) * φ y ∂μ) ∈
      polynomialsDegLE ι m := by
  let b := EuclideanSpace.basisFun ι ℝ
  have hexp : (fun x => ∫ y in s, IteratedGradient.fullContractL k (x - y) (G y) * φ y ∂μ) =
      ∑ I : Fin (k + 1) → ι, fun x => ∫ y in s, (∏ l : Fin (k + 1), ⟪b (I l), x - y⟫_ℝ) *
        (φ y * IteratedGradient.evalTupleL k (b ∘ I) (G y)) ∂μ := by
    ext x
    simpa only [Finset.sum_apply, mul_assoc] using
      setIntegral_fullContractL_sub_mul_eq_sum b k hG hφ hφc hφs x
  rw [hexp]
  refine Submodule.sum_mem (polynomialsDegLE ι m) fun I _ =>
    setIntegral_prod_inner_sub_right_mul_mem_polynomialsDegLE Finset.univ (by simpa using hkm)
      (b ∘ I) fun v _ => ?_
  have hA : ContinuousOn
      (fun y => (∏ l ∈ v, ⟪b (I l), y⟫_ℝ) • IteratedGradient.evalTupleL k (b ∘ I)) (tsupport φ) :=
    (continuous_finsetProd v fun l _ => (innerSL ℝ (b (I l))).continuous).continuousOn.smul
      continuousOn_const
  have heq : (fun y => φ y • ((∏ l ∈ v, ⟪b (I l), y⟫_ℝ) •
        IteratedGradient.evalTupleL k (b ∘ I)) (G y)) =
      fun y => (∏ l ∈ v, ⟪(b ∘ I) l, y⟫_ℝ) *
        (φ y * IteratedGradient.evalTupleL k (b ∘ I) (G y)) :=
    funext fun y => by simp only [smul_apply, smul_eq_mul, Function.comp_apply]; ring
  exact heq ▸ (hG.integrable_smul_clm_apply_of_hasCompactSupport hφ hφc hφs hA).integrableOn

end Polynomiality

end TauCeti
