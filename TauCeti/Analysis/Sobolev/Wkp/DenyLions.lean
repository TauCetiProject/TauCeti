/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Polynomial
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Normed.Module.Quotient

/-!
# The Deny–Lions lemma from compactness

Let `Ω` be an open set such that forgetting the highest weak derivative is a compact operator
`W^{m+1,p}(Ω) → W^{m,p}(Ω)`, as the Rellich–Kondrachov theorem provides on bounded Lipschitz
domains. Write `N` for the kernel of the highest weak derivative `D^{m+1}` on `W^{m+1,p}(Ω)`.
This file proves the **Deny–Lions lemma**: on the quotient `W^{m+1,p}(Ω) ⧸ N` the quotient norm is
equivalent to the top seminorm `‖D^{m+1} u‖_{Lᵖ}`, which descends to the quotient. Concretely:

* `N` is finite-dimensional;
* there is a continuous projection `P` of `W^{m+1,p}(Ω)` onto `N` with
  `‖u - P u‖ ≤ C * ‖D^{m+1} u‖` for every `u`;
* `‖D^{m+1} u‖ ≤ ‖[u]‖ ≤ C * ‖D^{m+1} u‖`, where `[u]` is the class of `u` in the quotient. The
  lower bound holds for the quotient by any subspace of `N`.

These statements about `N` need no connectedness.

On a preconnected open subset `Ω` of `EuclideanSpace ℝ ι`, the kernel `N` is the subspace
`TauCeti.Wkp.polynomialClasses (m + 1) m` of classes of polynomials of total degree at most `m`
(`TauCeti.Wkp.ker_iteratedGradientL`). This gives the classical form of the lemma: on the quotient
`W^{m+1,p}(Ω) ⧸ polynomialClasses (m + 1) m`, the quotient norm `inf_q ‖u - q‖` and the descended
top seminorm `TauCeti.Wkp.quotientSeminorm m` are equivalent norms. On a nonempty bounded `Ω`, the
projection form becomes a continuous linear map `π` from `W^{m+1,p}(Ω)` to the polynomial functions
of degree at most `m` that recovers each polynomial from its Sobolev class and satisfies
`‖u - π u‖_{m+1,p} ≤ C * |u|_{m+1,p}`. Preconnectedness cannot be dropped: on two disjoint balls,
the function equal to `0` on one and `1` on the other has vanishing gradient but is not almost
everywhere equal to a constant.

The argument is Peetre's compact-error estimate in its quotient form,
`ContinuousLinearMap.exists_norm_quotientMk_ker_le_of_compact_estimate`, and in its projection form,
`ContinuousLinearMap.exists_projection_norm_sub_le_of_compact_estimate`, applied to the estimate
`‖u‖_{m+1,p} ≤ ‖u‖_{m,p} + ‖D^{m+1} u‖_{Lᵖ}` of the graph norm. The first-order case with the
constants as kernel is `TauCeti.W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator`.
The corresponding statements on bounded Lipschitz domains are in
`TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.DenyLions`.

## Main declarations

* `TauCeti.Wkp.finiteDimensional_ker_iteratedGradientL_of_isCompactOperator`: the kernel of the
  highest weak derivative is finite-dimensional.
* `TauCeti.Wkp.exists_projection_norm_sub_le_of_isCompactOperator`: a continuous projection onto
  that kernel whose error is controlled by the highest weak derivative.
* `TauCeti.Wkp.exists_norm_quotientMk_ker_le_of_isCompactOperator`,
  `TauCeti.Wkp.norm_iteratedGradient_le_norm_quotientMk_of_le_ker`: the two halves of the
  equivalence between the quotient norm and the top seminorm.
* `TauCeti.Wkp.exists_norm_le_quotientSeminorm_of_isCompactOperator`: on a preconnected domain,
  the quotient norm modulo polynomial classes is bounded by the descended top seminorm.
* `TauCeti.Wkp.exists_polynomialProjection_norm_sub_le_of_isCompactOperator`: on a nonempty bounded
  preconnected domain, a continuous linear projection onto the polynomials of degree at most `m`
  whose error is bounded by the top seminorm.

## References

* J. Deny, J.-L. Lions, *Les espaces du type de Beppo Levi*, Ann. Inst. Fourier 5 (1954),
  305–370, Chapitre III, §2, Théorème 2.1.
* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, SIAM (2002), Theorem 3.1.1.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-- The graph-norm estimate in the compact-error form used by Peetre's lemma: the
`W^{m+1,p}` norm is at most the norm of the highest weak derivative plus the `W^{m,p}` norm. -/
private theorem norm_le_one_mul_norm_iteratedGradientL_add_norm_lowerOrderL (m : ℕ)
    (u : Wkp mu Omega p (m + 1)) :
    ‖u‖ ≤ 1 * ‖iteratedGradientL m u‖ + ‖lowerOrderL m u‖ := by
  rw [one_mul, add_comm ‖_‖, iteratedGradientL_apply, lowerOrderL_apply]
  exact norm_le_norm_lowerOrder_add_norm_iteratedGradient m u

/-- If forgetting the highest weak derivative is a compact operator
`W^{m+1,p}(Ω) → W^{m,p}(Ω)`, then the kernel of the highest weak derivative on `W^{m+1,p}(Ω)` is
finite-dimensional. -/
theorem finiteDimensional_ker_iteratedGradientL_of_isCompactOperator (m : ℕ)
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) m)) :
    FiniteDimensional ℝ (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker :=
  (iteratedGradientL m).finiteDimensional_ker_of_compact_estimate hK
    (norm_le_one_mul_norm_iteratedGradientL_add_norm_lowerOrderL m)

/-- **The Deny–Lions lemma, projection form.** If forgetting the highest weak derivative is a
compact operator `W^{m+1,p}(Ω) → W^{m,p}(Ω)`, there are a continuous linear projection `P` of
`W^{m+1,p}(Ω)` onto the kernel of the highest weak derivative `D^{m+1}` and a constant `C` with
`‖u - P u‖ ≤ C * ‖D^{m+1} u‖` for every `u ∈ W^{m+1,p}(Ω)`. -/
theorem exists_projection_norm_sub_le_of_isCompactOperator (m : ℕ)
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) m)) :
    ∃ (P : Wkp mu Omega p (m + 1) →L[ℝ] Wkp mu Omega p (m + 1)) (C : ℝ), 0 ≤ C ∧
      (∀ u, iteratedGradient m (P u) = 0) ∧ (∀ u, iteratedGradient m u = 0 → P u = u) ∧
      ∀ u, ‖u - P u‖ ≤ C * ‖iteratedGradient m u‖ := by
  obtain ⟨P, C, hC, hP, hrange, hbound⟩ :=
    (iteratedGradientL m).exists_projection_norm_sub_le_of_compact_estimate hK
      (norm_le_one_mul_norm_iteratedGradientL_add_norm_lowerOrderL m)
  refine ⟨P, C, hC, fun u ↦ ?_, fun u hu ↦ ?_, fun u ↦ ?_⟩
  · have h : P u ∈ (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker :=
      hrange ▸ LinearMap.mem_range_self _ u
    simpa [← iteratedGradientL_apply] using h
  · have hu' : u ∈ (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker := by
      simpa [← iteratedGradientL_apply] using hu
    obtain ⟨v, rfl⟩ := hrange ▸ hu'
    simpa using congr($hP v)
  · simpa [← iteratedGradientL_apply] using hbound u

/-- **The Deny–Lions lemma.** If forgetting the highest weak derivative is a compact operator
`W^{m+1,p}(Ω) → W^{m,p}(Ω)`, the quotient norm of `u ∈ W^{m+1,p}(Ω)` modulo the kernel of the
highest weak derivative `D^{m+1}` is bounded by a constant multiple of `‖D^{m+1} u‖`. With
`TauCeti.Wkp.norm_iteratedGradient_le_norm_quotientMk_of_le_ker`, the quotient norm and the
descended top seminorm are equivalent. -/
theorem exists_norm_quotientMk_ker_le_of_isCompactOperator (m : ℕ)
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Wkp mu Omega p (m + 1),
      ‖(Submodule.Quotient.mk u : Wkp mu Omega p (m + 1) ⧸
        (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker)‖ ≤
        C * ‖iteratedGradient m u‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    (iteratedGradientL m).exists_norm_quotientMk_ker_le_of_compact_estimate hK
      (norm_le_one_mul_norm_iteratedGradientL_add_norm_lowerOrderL m)
  refine ⟨C, hC, fun u ↦ ?_⟩
  simpa [← iteratedGradientL_apply] using hbound u

/-- The highest weak derivative descends without increasing norms to the quotient by any subspace
`S` of its kernel: `‖D^{m+1} u‖` is at most the quotient norm of `u` modulo `S`. For `S` the kernel
of `D^{m+1}`, this is the easy half of the Deny–Lions equivalence, and needs no compactness. -/
theorem norm_iteratedGradient_le_norm_quotientMk_of_le_ker {m : ℕ}
    {S : Submodule ℝ (Wkp mu Omega p (m + 1))}
    (hS : S ≤ (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker)
    (u : Wkp mu Omega p (m + 1)) :
    ‖iteratedGradient m u‖ ≤ ‖(Submodule.Quotient.mk u : Wkp mu Omega p (m + 1) ⧸ S)‖ := by
  have hnorm : ‖iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
      simpa [← iteratedGradientL_apply] using norm_iteratedGradient_le m v
  simpa [← iteratedGradientL_apply] using
    (S.norm_apply_le_norm_mul_norm_quotientMk _ hS u).trans
      (mul_le_of_le_one_left (norm_nonneg _) hnorm)

/-! ### The Deny–Lions lemma modulo polynomials -/

section Polynomial

variable {ι : Type*} [Fintype ι] {ν : Measure (EuclideanSpace ℝ ι)} [ν.IsAddHaarMeasure]
  {Ω : Opens (EuclideanSpace ℝ ι)}

/-- **The Deny–Lions lemma modulo polynomials.** Let `Ω ⊆ EuclideanSpace ℝ ι` be a preconnected
open set on which forgetting the highest weak derivative is a compact operator
`W^{m+1,p}(Ω) → W^{m,p}(Ω)`. On the quotient of `W^{m+1,p}(Ω)` by the polynomial classes of degree
at most `m`, the quotient norm `inf_q ‖u - q‖` is bounded by a constant multiple of the descended
top seminorm `|u|_{m+1,p}`. With `TauCeti.Wkp.quotientSeminorm_le_norm`, the two are equivalent
norms on the quotient. -/
theorem exists_norm_le_quotientSeminorm_of_isCompactOperator
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ ι))) (m : ℕ)
    (hK : IsCompactOperator (lowerOrderL (mu := ν) (Omega := Ω) (p := p) m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Wkp ν Ω p (m + 1) ⧸ polynomialClasses (m + 1) m,
      ‖x‖ ≤ C * quotientSeminorm m x := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_quotientMk_ker_le_of_isCompactOperator m hK
  rw [ker_iteratedGradientL hc] at hbound
  refine ⟨C, hC, fun x ↦ ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H u => rw [quotientSeminorm_mk, seminorm_succ_self_apply]; exact hbound u

/-- **The Deny–Lions lemma, polynomial projection form.** Let `Ω ⊆ EuclideanSpace ℝ ι` be a
nonempty, bounded, preconnected open set on which forgetting the highest weak derivative is a
compact operator `W^{m+1,p}(Ω) → W^{m,p}(Ω)`. There are a continuous linear map `π` from
`W^{m+1,p}(Ω)` to the polynomial functions of total degree at most `m`, which recovers every such
polynomial from its Sobolev class, and a constant `C` such that the Sobolev class of `π u`
approximates `u` with `‖u - π u‖_{m+1,p} ≤ C * |u|_{m+1,p}`. -/
theorem exists_polynomialProjection_norm_sub_le_of_isCompactOperator
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ ι)))
    (hne : (Ω : Set (EuclideanSpace ℝ ι)).Nonempty) (m : ℕ)
    (hK : IsCompactOperator (lowerOrderL (mu := ν) (Omega := Ω) (p := p) m)) :
    ∃ (π : Wkp ν Ω p (m + 1) →L[ℝ] polynomialsDegLE ι m) (C : ℝ), 0 ≤ C ∧
      (∀ q, π (polynomialL hb (m + 1) m q) = q) ∧
      ∀ u, ‖u - polynomialL hb (m + 1) m (π u)‖ ≤ C * seminorm (m + 1) (m + 1) le_rfl u := by
  obtain ⟨P, C, hC, hP, hfix, hbound⟩ := exists_projection_norm_sub_le_of_isCompactOperator m hK
  have hinj := polynomialL_injective (mu := ν) (p := p) hb hne (m + 1) m
  -- `P` lands in the kernel of the top derivative, which is the range of `polynomialL`.
  have hrange : ∀ u, P u ∈ (polynomialL (mu := ν) (p := p) hb (m + 1) m).range := fun u ↦ by
    rw [range_polynomialL, ← ker_iteratedGradientL hc, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, iteratedGradientL_apply]
    exact hP u
  -- Invert `polynomialL` on its finite-dimensional range.
  let ψ := (LinearEquiv.ofInjective _ hinj).toContinuousLinearEquiv
  have hψ (u) : polynomialL hb (m + 1) m (ψ.symm (P.codRestrict _ hrange u)) = P u :=
    congr($(ψ.apply_symm_apply (P.codRestrict _ hrange u)).val)
  refine ⟨ψ.symm.toContinuousLinearMap.comp (P.codRestrict _ hrange), C, hC, fun q ↦ ?_,
    fun u ↦ ?_⟩
  · refine hinj ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hψ]
    exact hfix _ (iteratedGradient_eq_zero_of_mem_polynomialClasses le_rfl
      (polynomialL_mem_polynomialClasses hb q))
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hψ,
      seminorm_succ_self_apply]
    exact hbound u

end Polynomial

end Wkp

end TauCeti
