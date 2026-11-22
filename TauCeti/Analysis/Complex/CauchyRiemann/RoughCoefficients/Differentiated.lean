/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Basic
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Sobolev.Local.Multiplication
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry

/-!
# The differentiated Cauchy–Riemann system with Sobolev coefficients

Write `z = s + i t` on `ℂ` and consider the operator `ξ ↦ ∂_s ξ + J ∂_t ξ + S ξ` for coefficient
fields `J, S : ℂ → (V →L[ℝ] V)` on a finite-dimensional real normed space `V`, where, for a weak
derivative `Dξ` of `ξ`, `∂_s ξ = Dξ(·) 1` and `∂_t ξ = Dξ(·) I`. Interior regularity for this
operator is proved by induction on the order (McDuff–Salamon, Proposition B.4.9, Steps 2 and 3):
the pair `Ξ = (∂_s ξ, ∂_t ξ)` solves a system of the same shape,

`∂_s Ξ + J₂ ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)`,

with `J₂ = diag(J, J)` and `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]`. The classical computation for
`C²` maps is `TauCeti.crOperator_differentiated_system`.

This file proves both the strong and weak Sobolev forms of the differentiated system:

* **Strong form** (`TauCeti.ae_differentiated_cauchyRiemann`): for `p > 2`, `1 < q ≤ p`,
  `J, S ∈ W^{1,p}_loc`, `ξ ∈ W^{2,q}_loc` and `η` with weak derivative `Dη` satisfying
  `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on an open `Ω`, the pair `Ξ` is in `W^{1,q}_loc`
  and every weak derivative of `Ξ` satisfies the differentiated system almost everywhere on `Ω`.
  The products `J ∂_t ξ` and `S ξ` are differentiated by the weak Leibniz rule for mixed exponents,
  and the mixed second weak derivatives of `ξ` commute.
* **Weak form** (`TauCeti.isWeakCRSolution_differentiated`): on a finite-dimensional real inner
  product space, for `1 < p ≤ ∞` and `1 < q ≤ ∞` with `p⁻¹ + q⁻¹ ≤ 1`, when `J, S ∈ W^{1,p}_loc`,
  `ξ ∈ W^{1,q}_loc`, and `η` has weak derivative `Dη` with `∂_s ξ + J ∂_t ξ + S ξ = η` almost
  everywhere on `Ω`, the pair `Ξ = (∂_s ξ, ∂_t ξ)` valued in `WithLp 2 (V × V)` is a weak solution
  (`TauCeti.IsWeakCRSolution`) of the differentiated system. Neither second weak derivatives of `ξ`
  nor second weak derivatives of `J` are assumed: the `∂_s` row uses a distributional commutator
  identity established by interior mollification of `ξ`.

The coefficients and right side of the new system inherit the regularity the induction needs: `J₂`
has the regularity of `J`, `S₂` is in `W^{k,p}_loc` as soon as `S ∈ W^{k,p}_loc` and
`J ∈ W^{k+1,p}_loc`, and the right side lies in `L^q_loc` for `k = 0` and in `W^{k,q}_loc` for
`S ∈ W^{k+1,p}_loc`, `ξ ∈ W^{max 1 k, q}_loc`, and `η ∈ W^{k+1,q}_loc`.

## Main declarations

* `TauCeti.MemWkpLoc.memWkpLoc_partials_of_hasWeakFDerivOn`: `Ξ = (∂_s ξ, ∂_t ξ) ∈ W^{k,q}_loc`
  for `ξ ∈ W^{k+1,q}_loc`.
* `TauCeti.ae_differentiated_cauchyRiemann`: the differentiated system, almost everywhere.
* `TauCeti.isWeakCRSolution_differentiated`: the weak differentiated system on `WithLp 2 (V × V)`
  when `ξ ∈ W^{1,q}_loc(Ω)`, `1 < p, q ≤ ∞`, and `p⁻¹ + q⁻¹ ≤ 1`.
* `TauCeti.MemWkpLoc.differentiatedCRCoefficient`: the regularity of `S₂`.
* `TauCeti.memLpLoc_differentiatedCR_rightSide` and
  `TauCeti.memWkpLoc_differentiatedCR_rightSide`: the right side is in `L^q_loc` and in
  `W^{k,q}_loc`.
* `TauCeti.ae_differentiated_cauchyRiemann_const`: for a constant coefficient `J` and `S = 0`,
  the system is the original operator applied to each component of `Ξ`.

The coefficient `S₂` is `TauCeti.differentiatedCRCoefficient`, and
`TauCeti.differentiatedCRCoefficient_ne_prodMap` shows `S₂ ≠ diag(S, S)` as soon as `∂_s J ≠ 0`.
The regularity of `J₂` is `TauCeti.MemWkpLoc.prodMap`, and `J₂² = -1` whenever `J² = -1` is
`TauCeti.prodMap_mul_self_eq_neg_one`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.4.9.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

section StrongDifferentiated

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {Ω : Opens ℂ} {k : ℕ}

/-- **The partial derivatives of a `W^{k+1,q}_loc` map.** For a weak derivative `Dξ` of
`ξ ∈ W^{k+1,q}_loc`, the pair `Ξ = (∂_s ξ, ∂_t ξ) = (Dξ(·) 1, Dξ(·) I)` is in `W^{k,q}_loc`. -/
theorem MemWkpLoc.memWkpLoc_partials_of_hasWeakFDerivOn {q : ℝ≥0∞} {ξ : ℂ → V}
    {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : MemWkpLoc q Ω (k + 1) ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) :
    MemWkpLoc q Ω k (fun z => (Dξ z 1, Dξ z I)) := by
  have := hξ.completeSpace
  have h := hξ.memWkpLoc_of_hasWeakFDerivOn hDξ
  exact (h.clm_comp (ContinuousLinearMap.apply ℝ V 1)).prodMk
    (h.clm_comp (ContinuousLinearMap.apply ℝ V I))

/-- **The differentiated system.** Let `p > 2` and `1 < q ≤ p`. Let `J, S ∈ W^{1,p}_loc(Ω)` have
weak derivatives `DJ`, `DS`, let `ξ ∈ W^{2,q}_loc(Ω)` have weak derivative `Dξ`, and let `η` have
weak derivative `Dη`. If `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω`, then every weak
derivative `DΞ` of `Ξ = (∂_s ξ, ∂_t ξ)` satisfies, almost everywhere on `Ω`,
`∂_s Ξ + J₂ ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)`,
with `J₂ = diag(J, J)` and `S₂ = TauCeti.differentiatedCRCoefficient S DJ`.
Such a `DΞ` exists by `TauCeti.MemWkpLoc.memWkpLoc_partials_of_hasWeakFDerivOn`. -/
theorem ae_differentiated_cauchyRiemann [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} {DΞ : ℂ → ℂ →L[ℝ] V × V}
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 2 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (hDΞ : HasWeakFDerivOn volume Ω (fun z => (Dξ z 1, Dξ z I)) DΞ) :
    ∀ᵐ z ∂volume.restrict Ω, DΞ z 1 + (J z).prodMap (J z) (DΞ z I) +
        differentiatedCRCoefficient (S z) (DJ z) (Dξ z 1, Dξ z I) =
      (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z)) := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le.trans hqp⟩
  have hDξ1 : MemWkpLoc q Ω 1 Dξ := hξ.memWkpLoc_of_hasWeakFDerivOn hDξ
  obtain ⟨D2, hD2, hD2q⟩ := hDξ1.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hD2q
  -- The partial derivatives `z ↦ Dξ z v` have weak derivatives `w ↦ D2 z w v`.
  have hpart (v : ℂ) : HasWeakFDerivOn volume Ω (fun z => Dξ z v)
      (fun z => (ContinuousLinearMap.apply ℝ V v).comp (D2 z)) :=
    hD2.clm_comp (ContinuousLinearMap.apply ℝ V v)
  have hpartLp (v : ℂ) : MemLpLoc q Ω (fun z => Dξ z v) :=
    hDξ1.memLpLoc.clm_comp (ContinuousLinearMap.apply ℝ V v)
  have hpartDLp (v : ℂ) :
      MemLpLoc q Ω (fun z => (ContinuousLinearMap.apply ℝ V v).comp (D2 z)) :=
    hD2q.clm_comp (ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] V) V (ContinuousLinearMap.apply ℝ V v))
  -- The mixed second weak derivatives of `ξ` commute.
  have hsymm : (fun z => D2 z I 1) =ᵐ[volume.restrict Ω] fun z => D2 z 1 I :=
    ((hDξ.hasWeakLineDerivOn 1).comm ((hpart 1).hasWeakLineDerivOn I)
      (hDξ.hasWeakLineDerivOn I)).ae_eq ((hpart I).hasWeakLineDerivOn 1)
  -- The weak Leibniz rule for `J ∂_t ξ` and `S ξ`.
  have hJξ := hDJ.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
    ((hJ.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top)
    (hJ.memLpLoc_of_hasWeakFDerivOn hDJ) (hpart I) (hpartLp I) (hpartDLp I)
  have hSξ := hDS.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
    ((hS.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top)
    (hS.memLpLoc_of_hasWeakFDerivOn hDS) hDξ hξ.memLpLoc hDξ1.memLpLoc
  -- Differentiating the equation.
  have hsum := (((hpart 1).add hJξ).add hSξ).congr_ae (heq.mono fun z hz => by simpa using hz)
  have hη := hsum.ae_eq hDη
  have hΞ := hDΞ.ae_eq ((hpart 1).prodMk (hpart I))
  filter_upwards [hη, hΞ, hsymm] with z h1 h2 h3
  -- The `∂_s` and `∂_t` components of the differentiated equation.
  have e1 : D2 z 1 1 + (DJ z 1 (Dξ z I) + J z (D2 z 1 I)) + (DS z 1 (ξ z) + S z (Dξ z 1)) =
      Dη z 1 := by
    simpa using congr($h1 1)
  have eI : D2 z I 1 + (DJ z I (Dξ z I) + J z (D2 z I I)) + (DS z I (ξ z) + S z (Dξ z I)) =
      Dη z I := by
    simpa using congr($h1 I)
  rw [h2]
  ext
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
      Prod.mk_add_mk, differentiatedCRCoefficient_apply, h3]
    rw [← e1]
    abel
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
      Prod.mk_add_mk, differentiatedCRCoefficient_apply, ← h3]
    rw [← eI]
    abel

/-- **Regularity of `S₂`.** If `S ∈ W^{k,p}_loc(Ω)` and `J ∈ W^{k+1,p}_loc(Ω)` with weak
derivative `DJ`, then `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]` is in `W^{k,p}_loc(Ω)`. For
`S ∈ W^{m,p}_loc` and `J ∈ W^{ℓ,p}_loc` this gives `S₂ ∈ W^{min(m, ℓ - 1),p}_loc` after lowering the
orders with `TauCeti.MemWkpLoc.of_le`. -/
theorem MemWkpLoc.differentiatedCRCoefficient [CompleteSpace V] {p : ℝ≥0∞} {J S : ℂ → V →L[ℝ] V}
    {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} (hS : MemWkpLoc p Ω k S) (hJ : MemWkpLoc p Ω (k + 1) J)
    (hDJ : HasWeakFDerivOn volume Ω J DJ) :
    MemWkpLoc p Ω k (fun z => TauCeti.differentiatedCRCoefficient (S z) (DJ z)) := by
  simpa using (hS.prodMk (hJ.memWkpLoc_of_hasWeakFDerivOn hDJ)).clm_comp
    differentiatedCRCoefficientL

/-- **The right side of the differentiated system is locally `L^q`.** For `p > 2`, `1 ≤ q ≤ p`,
`S ∈ W^{1,p}_loc(Ω)` with weak derivative `DS` and `ξ, η ∈ W^{1,q}_loc(Ω)` with `η` having weak
derivative `Dη`, the map `(∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` is in `L^q_loc(Ω)`. -/
theorem memLpLoc_differentiatedCR_rightSide [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hq : 1 ≤ q) (hqp : q ≤ p)
    {S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V}
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS) (hξ : MemWkpLoc q Ω 1 ξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη) :
    MemLpLoc q Ω (fun z => (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  have hDSp := hS.memLpLoc_of_hasWeakFDerivOn hDS
  have hDηq := hη.memLpLoc_of_hasWeakFDerivOn hDη
  have hcomp (v : ℂ) : MemLpLoc q Ω (fun z => Dη z v - DS z v (ξ z)) :=
    (hDηq.clm_comp (ContinuousLinearMap.apply ℝ V v)).sub
      (MemLpLoc.bilin_of_memWkpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hqp
        (hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)) hξ)
  exact memWkpLoc_zero_iff.1
    ((memWkpLoc_zero_iff.2 (hcomp 1)).prodMk (memWkpLoc_zero_iff.2 (hcomp I)))

/-- **Higher-order regularity of the differentiated right side.** For `p > 2`, `1 < q ≤ p`,
`S ∈ W^{k+1,p}_loc(Ω)` with weak derivative `DS`, `ξ ∈ W^{max 1 k, q}_loc(Ω)`, and
`η ∈ W^{k+1,q}_loc(Ω)` with weak derivative `Dη`, the map
`(∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` lies in `W^{k,q}_loc(Ω)`. -/
theorem memWkpLoc_differentiatedCR_rightSide [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V}
    (hS : MemWkpLoc p Ω (k + 1) S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω (max 1 k) ξ) (hη : MemWkpLoc q Ω (k + 1) η)
    (hDη : HasWeakFDerivOn volume Ω η Dη) :
    MemWkpLoc q Ω k (fun z => (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  cases k with
  | zero =>
    exact memWkpLoc_zero_iff.2 (memLpLoc_differentiatedCR_rightSide hp hq.le hqp hS hDS hξ hη hDη)
  | succ n =>
    have hξ' : MemWkpLoc q Ω (n + 1) ξ := by simpa [Nat.succ_eq_add_one] using hξ
    have hDSn : MemWkpLoc p Ω (n + 1) DS := hS.memWkpLoc_of_hasWeakFDerivOn hDS
    have hDηn : MemWkpLoc q Ω (n + 1) Dη := hη.memWkpLoc_of_hasWeakFDerivOn hDη
    have hcomp (v : ℂ) : MemWkpLoc q Ω (n + 1) (fun z => Dη z v - DS z v (ξ z)) :=
      (hDηn.clm_comp (ContinuousLinearMap.apply ℝ V v)).sub
        ((hDSn.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)).clm_apply_succ
          hp hq hqp hξ')
    exact (hcomp 1).prodMk (hcomp I)

/-- **Check: the constant case.** For a constant structure `J = A` and `S = 0`, the differentiated
system is the original operator `∂_s + A ∂_t` applied to each component of `Ξ = (∂_s ξ, ∂_t ξ)`:
every weak derivative `DΞ` of `Ξ` satisfies `∂_s Ξ + diag(A, A) ∂_t Ξ = (∂_s η, ∂_t η)` almost
everywhere on `Ω`. -/
theorem ae_differentiated_cauchyRiemann_const {q : ℝ≥0∞}
    (A : V →L[ℝ] V) {ξ η : ℂ → V} {Dξ Dη : ℂ → ℂ →L[ℝ] V} {DΞ : ℂ → ℂ →L[ℝ] V × V}
    (hξ : MemWkpLoc q Ω 2 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + A (Dξ z I) = η z)
    (hDΞ : HasWeakFDerivOn volume Ω (fun z => (Dξ z 1, Dξ z I)) DΞ) :
    ∀ᵐ z ∂volume.restrict Ω, DΞ z 1 + A.prodMap A (DΞ z I) = (Dη z 1, Dη z I) := by
  have := hξ.completeSpace
  obtain ⟨D2, hD2, -⟩ := (hξ.memWkpLoc_of_hasWeakFDerivOn hDξ).exists_weakFDeriv_of_isOpen
  -- The partial derivatives `z ↦ Dξ z v` have weak derivatives `w ↦ D2 z w v`.
  have hpart (v : ℂ) : HasWeakFDerivOn volume Ω (fun z => Dξ z v)
      (fun z => (ContinuousLinearMap.apply ℝ V v).comp (D2 z)) :=
    hD2.clm_comp (ContinuousLinearMap.apply ℝ V v)
  -- The mixed second weak derivatives of `ξ` commute.
  have hsymm : (fun z => D2 z I 1) =ᵐ[volume.restrict Ω] fun z => D2 z 1 I :=
    ((hDξ.hasWeakLineDerivOn 1).comm ((hpart 1).hasWeakLineDerivOn I)
      (hDξ.hasWeakLineDerivOn I)).ae_eq ((hpart I).hasWeakLineDerivOn 1)
  -- Differentiating the equation through the constant operator `A`.
  have hη := (((hpart 1).add ((hpart I).clm_comp A)).congr_ae heq).ae_eq hDη
  have hΞ := hDΞ.ae_eq ((hpart 1).prodMk (hpart I))
  filter_upwards [hη, hΞ, hsymm] with z h1 h2 h3
  have e1 : D2 z 1 1 + A (D2 z 1 I) = Dη z 1 := by simpa using congr($h1 1)
  have eI : D2 z I 1 + A (D2 z I I) = Dη z I := by simpa using congr($h1 I)
  rw [h2]
  ext
  · simpa [h3] using e1
  · simpa [← h3] using eI

end StrongDifferentiated

/-! ### The weak differentiated Cauchy–Riemann system -/

section WeakDifferentiated

open Filter Metric Set
open scoped ContDiff Convolution Distributions InnerProductSpace LineDeriv Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Ω : Opens ℂ}

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (ℂ →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (ℂ →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (V × V →L[ℝ] V × V) := inferInstance
private local instance : NormedSpace ℝ (V × V →L[ℝ] V × V) := inferInstance
private local instance :
    NormedAddCommGroup (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance
private local instance :
    NormedSpace ℝ (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance

/-- Commutator identity for a smooth field `ψ` and a `W^{1,p}_loc` coefficient `J`: symmetry of the
second Fréchet derivative of `ψ` cancels the second-derivative terms in the weak Leibniz rules for
`∂_t(J ∂_s ψ)` and `∂_s(J ∂_t ψ)`. -/
private theorem integral_commutator_of_contDiff [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (φ : 𝓓(Ω, V)) {ψ : ℂ → V}
    (hψ : ContDiff ℝ ∞ ψ) :
    -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (fderiv ℝ ψ z 1)⟫_ℝ) -
        (∫ z, ⟪(φ : ℂ → V) z, DJ z I (fderiv ℝ ψ z 1)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (fderiv ℝ ψ z I)⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, J z (fderiv ℝ ψ z I)⟫_ℝ) := by
  let u : ℂ → ℂ → V := fun v z => fderiv ℝ ψ z v
  have hu_s (v : ℂ) : ContDiff ℝ ∞ (u v) :=
    (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hu_q (v : ℂ) : MemLpLoc q Ω (u v) := (hu_s v).continuous.continuousOn.memLpLoc
  have hdu_q (v w : ℂ) : MemLpLoc q Ω (fun z => fderiv ℝ (u v) z w) :=
    (((hu_s v).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      contDiff_const).continuous.continuousOn.memLpLoc
  have hDJw (w : ℂ) : MemLpLoc p Ω (fun z => DJ z w) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hJu (v w : ℂ) : HasWeakLineDerivOn volume Ω (fun z => J z (u v z))
      (fun z => DJ z w (u v z) + J z (fderiv ℝ (u v) z w)) w := by
    simpa using (hc.hasWeakFDerivOn.hasWeakLineDerivOn w).bilin_of_memLpLoc
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hp hq hq hpq hpq hpq
      (((hu_s v).contDiffOn.of_le (by simp)).hasWeakFDerivOn_fderiv.hasWeakLineDerivOn w)
      hc.memLpLoc_coeff (hDJw w) (hu_q v) (hdu_q v w)
  have hloc := Ω.isOpen.isLocallyClosed
  have hibp (v w : ℂ) : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z w, J z (u v z)⟫_ℝ =
      -((∫ z, ⟪(φ : ℂ → V) z, DJ z w (u v z)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, J z (fderiv ℝ (u v) z w)⟫_ℝ) := by
    have h := (hJu v w).integral_inner_lineDeriv_eq_neg φ
    simp only [TestFunction.lineDeriv_eq_fderiv, inner_add_right] at h
    exact h.trans (congrArg Neg.neg (integral_add
      (φ.integrable_inner ((hDJw w).locallyIntegrableOn_clm_apply (hu_q v) hpq hloc))
      (φ.integrable_inner (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply (hdu_q v w) hpq hloc))))
  have hsymm (z : ℂ) : fderiv ℝ (u 1) z I = fderiv ℝ (u I) z 1 := by
    have hd : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
      (hψ.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero z
    simpa [u, fderiv_clm_apply hd (differentiableAt_const _)] using
      ((hψ.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)).eq I 1
  have h1 := hibp 1 I
  simp_rw [hsymm] at h1
  linarith [hibp I 1]

/-- On the support of a test function `Θ`, when every `ρ.rOut`-ball around `tsupport Θ` lies in
`W ⊆ Ω`, the Fréchet derivative of `ρ.normed ⋆ 1_W u` agrees with `ρ.normed ⋆ 1_W Du`, so their
inner-product pairings against `z ↦ B z ·` are equal. -/
theorem HasWeakFDerivOn.integral_inner_mollified_fderiv_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) {W : Opens ℂ} (hWΩ : closure (W : Set ℂ) ⊆ Ω)
    {u : ℂ → F} {Du : ℂ → ℂ →L[ℝ] F} (hDu : HasWeakFDerivOn volume Ω u Du)
    (huW : MemLp u p (volume.restrict W)) (hDuW : MemLp Du p (volume.restrict W))
    (ρ : ContDiffBump (0 : ℂ)) (Θ : 𝓓(Ω, V))
    (hball : ∀ z ∈ tsupport (Θ : ℂ → V), closedBall z ρ.rOut ⊆ W)
    (B : ℂ → (ℂ →L[ℝ] F) → V) :
    (∫ z, ⟪(Θ : ℂ → V) z, B z (fderiv ℝ
        (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator u)
        z)⟫_ℝ) =
      ∫ z, ⟪(Θ : ℂ → V) z, B z
        ((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator Du)
          z)⟫_ℝ := by
  refine integral_congr_ae (.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport (Θ : ℂ → V)
  · have hd := (hDu.mono (subset_closure.trans hWΩ)).fderiv_indicator_convolution_normed
      huW hDuW hp1 hp1 ρ z (hball z hz)
    simp only [convolution_flip] at hd
    dsimp only
    rw [hd]
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-- Distributional commutator identity for `J ∈ W^{1,p}_loc(Ω)` and `ξ ∈ W^{1,q}_loc(Ω)` when
`p⁻¹ + q⁻¹ ≤ 1`, proved by interior mollification of `ξ` on a precompact open neighbourhood of
`tsupport φ`. -/
private theorem integral_commutator_of_hasWeakFDerivOn [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hξq : MemLpLoc q Ω ξ) (hDξq : MemLpLoc q Ω Dξ) (φ : 𝓓(Ω, V)) :
    -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ) -
        (∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, J z (Dξ z I)⟫_ℝ) := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  obtain ⟨W, hφW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨ρ, hρ0, hball⟩ :=
    ContDiffBump.exists_seq_tendsto_rOut_closedBall_subset W.isOpen φ.hasCompactSupport hφW
  have hξW : MemLp ξ q (volume.restrict W) := hξq.memLp_restrict_of_isCompact_closure hWc hWΩ
  have hDξW : MemLp Dξ q (volume.restrict W) := hDξq.memLp_restrict_of_isCompact_closure hWc hWΩ
  have hJW : MemLp J p (volume.restrict W) :=
    hc.memLpLoc_coeff.memLp_restrict_of_isCompact_closure hWc hWΩ
  have hDJW (w : ℂ) : MemLp (fun z => DJ z w) p (volume.restrict W) :=
    (hc.memLpLoc_deriv.memLp_restrict_of_isCompact_closure hWc hWΩ).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hξext : MemLp ((W : Set ℂ).indicator ξ) q volume :=
    (memLp_indicator_iff_restrict W.isOpen.measurableSet.nullMeasurableSet).2 hξW
  let Dψ (n : ℕ) : ℂ → ℂ →L[ℝ] V :=
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator Dξ
  have hid (n : ℕ) : -(∫ z, ⟪(∂_{I} φ : 𝓓(Ω, V)) z, J z (Dψ n z 1)⟫_ℝ) -
      (∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dψ n z 1)⟫_ℝ) +
      (∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (Dψ n z I)⟫_ℝ) =
      -(∫ z, ⟪(∂_{(1 : ℂ)} φ : 𝓓(Ω, V)) z, J z (Dψ n z I)⟫_ℝ) := by
    have hψ_smooth : ContDiff ℝ ∞ _ :=
      ((ρ n).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) ((ρ n).contDiff_normed (μ := volume))
        (hξext.locallyIntegrable hq1)
    have hc_n := integral_commutator_of_contDiff hp hq hpq hc φ hψ_smooth
    simp_rw [← TestFunction.lineDerivOp_apply_eq_fderiv] at hc_n
    have hrew := hDξ.integral_inner_mollified_fderiv_eq (V := V) hq1 hWΩ hξW hDξW (ρ n)
    rwa [hrew (∂_{I} φ) (fun z hz => hball n z (φ.tsupport_lineDerivOp_subset I hz))
        (fun z M => J z (M 1)),
      hrew φ (hball n) (fun z M => DJ z I (M 1)),
      hrew φ (hball n) (fun z M => DJ z 1 (M I)),
      hrew (∂_{(1 : ℂ)} φ) (fun z hz => hball n z (φ.tsupport_lineDerivOp_subset 1 hz))
        (fun z M => J z (M I))] at hc_n
  let B (v : ℂ) : (ℂ →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) →L[ℝ] V :=
    (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).flip.comp (ContinuousLinearMap.apply ℝ V v)
  have hconv (Θ : 𝓓(Ω, V)) (hΘW : tsupport (Θ : ℂ → V) ⊆ W) {A : ℂ → V →L[ℝ] V}
      (hAW : MemLp A p (volume.restrict W)) (v : ℂ) :
      Tendsto (fun n => ∫ z, ⟪(Θ : ℂ → V) z, A z (Dψ n z v)⟫_ℝ)
        atTop (𝓝 (∫ z, ⟪(Θ : ℂ → V) z, A z (Dξ z v)⟫_ℝ)) := by
    simpa [B, Dψ] using Θ.tendsto_integral_inner_bilin_normed_convolution (B v)
      (add_comm p⁻¹ q⁻¹ ▸ hpq) W.isOpen.measurableSet.nullMeasurableSet hΘW hDξW hAW hρ0
  have ht1 := hconv (∂_{I} φ) ((φ.tsupport_lineDerivOp_subset I).trans hφW) hJW 1
  have ht4 := hconv (∂_{(1 : ℂ)} φ) ((φ.tsupport_lineDerivOp_subset 1).trans hφW) hJW I
  simpa only [TestFunction.lineDerivOp_apply_eq_fderiv] using tendsto_nhds_unique
    ((ht1.neg.sub (hconv φ hφW (hDJW I) 1)).add (hconv φ hφW (hDJW 1) I))
    (ht4.neg.congr fun n => (hid n).symm)

/-- Local integrability of each coordinate `Dη · v - DS · v (ξ ·)` of the differentiated right-hand
side without assuming `L^q_loc` integrability on `Dη`. -/
private theorem locallyIntegrableOn_differentiatedCR_coord {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V}
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemLpLoc q Ω ξ) (hDη : HasWeakFDerivOn volume Ω η Dη) (v : ℂ) :
    LocallyIntegrableOn (fun z => Dη z v - DS z v (ξ z)) Ω volume := by
  have hDSp : MemLpLoc p Ω DS := memWkpLoc_zero_iff.1 (hS.memWkpLoc_of_hasWeakFDerivOn hDS)
  exact (hDη.hasWeakLineDerivOn v).locallyIntegrableOn_deriv.sub
    ((hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)).locallyIntegrableOn_clm_apply
      hξ hpq Ω.isOpen.isLocallyClosed)

/-- Common weak directional differentiation of `∂_s ξ + J ∂_t ξ + S ξ = η` along `v ∈ ℂ` against a
test function `θ ∈ 𝓓(Ω, V)`. -/
private theorem integral_lineDeriv_crEquation [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} (hJ : MemLpLoc p Ω J)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (v : ℂ) (θ : 𝓓(Ω, V)) :
    -(∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, Dξ z 1⟫_ℝ) -
        (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, J z (Dξ z I)⟫_ℝ) +
        ∫ z, ⟪(θ : ℂ → V) z, S z (Dξ z v)⟫_ℝ =
      ∫ z, ⟪(θ : ℂ → V) z, Dη z v - DS z v (ξ z)⟫_ℝ := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hDξq : MemLpLoc q Ω Dξ := memWkpLoc_zero_iff.1 (hξ.memWkpLoc_of_hasWeakFDerivOn hDξ)
  have hDSv : MemLpLoc p Ω (fun z => DS z v) :=
    (memWkpLoc_zero_iff.1 (hS.memWkpLoc_of_hasWeakFDerivOn hDS)).clm_comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
  have hDξv (w : ℂ) : MemLpLoc q Ω (fun z => Dξ z w) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V w)
  have hSξ : HasWeakLineDerivOn volume Ω (fun z => S z (ξ z))
      (fun z => DS z v (ξ z) + S z (Dξ z v)) v := by
    simpa using (hDS.hasWeakLineDerivOn v).bilin_of_memLpLoc
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hp hq hq hpq hpq hpq
      (hDξ.hasWeakLineDerivOn v) hS.memLpLoc hDSv hξ.memLpLoc (hDξv v)
  have iD1 := θ.integrable_inner_fderiv ((hDξv 1).locallyIntegrableOn hq1 hloc) v
  have iJD := θ.integrable_inner_fderiv (hJ.locallyIntegrableOn_clm_apply (hDξv I) hpq hloc) v
  have iSξ := θ.integrable_inner_fderiv
    (hS.memLpLoc.locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc) v
  have iDSξ := θ.integrable_inner (hDSv.locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc)
  have iSD := θ.integrable_inner
    (hS.memLpLoc.locallyIntegrableOn_clm_apply (hDξv v) hpq hloc)
  have iDη := θ.integrable_inner (hDη.hasWeakLineDerivOn v).locallyIntegrableOn_deriv
  have hpde : (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, Dξ z 1⟫_ℝ) +
      (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, S z (ξ z)⟫_ℝ) =
      ∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, η z⟫_ℝ := by
    rw [← integral_add iD1 iJD]
    refine (integral_add (iD1.add iJD) iSξ).symm.trans
      (integral_congr_ae ((ae_imp_of_ae_restrict heq).mono fun z hz => ?_))
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · simp only [Pi.add_apply, ← inner_add_right, hz hzΩ]
    · simp [fderiv_of_notMem_tsupport ℝ fun h => hzΩ (θ.tsupport_subset h)]
  have hS_ibp := hSξ.integral_inner_lineDeriv_eq_neg θ
  have hη_ibp := (hDη.hasWeakLineDerivOn v).integral_inner_lineDeriv_eq_neg θ
  simp only [TestFunction.lineDeriv_eq_fderiv, inner_add_right, integral_add iDSξ iSD]
    at hS_ibp hη_ibp
  simp_rw [inner_sub_right, integral_sub iDη iDSξ]
  linarith

/-- Pointwise decomposition of the formal adjoint pairing on `WithLp 2 (V × V)` into the two
coordinate test functions `φ₁ = fst ∘ Φ` and `φ₂ = snd ∘ Φ`. -/
private theorem inner_crFormalAdjoint_withLp_eq [CompleteSpace V]
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) (z : ℂ) (u₁ u₂ : V) :
    let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
    let φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.fstL 2 ℝ V V) Φ
    let φ₂ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.sndL 2 ℝ V V) Φ
    ⟪crFormalAdjoint (fun w => (J w).withLpProdMap 2 (J w))
        (fun w => (ContinuousLinearMap.withLpDiagL 2 ℝ V V).comp (DJ w))
        (fun w => e.arrowCongr e (differentiatedCRCoefficient (S w) (DJ w))) Φ z,
        WithLp.toLp 2 (u₁, u₂)⟫_ℝ =
      (⟪crFormalAdjoint J DJ S φ₁ z, u₁⟫_ℝ + ⟪(φ₁ : ℂ → V) z, DJ z 1 u₂⟫_ℝ) +
        (⟪crFormalAdjoint J DJ S φ₂ z, u₂⟫_ℝ + ⟪(φ₂ : ℂ → V) z, DJ z I u₂⟫_ℝ) := by
  intro e φ₁ φ₂
  have hf (L : WithLp 2 (V × V) →L[ℝ] V) (v : ℂ) :
      L (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z v) =
        fderiv ℝ (TestFunction.postcompCLM L Φ : ℂ → V) z v := by
    rw [← TestFunction.lineDerivOp_apply_eq_fderiv, ← TestFunction.lineDerivOp_apply_eq_fderiv]
    simp
  have hf1 (v : ℂ) : (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z v).fst = fderiv ℝ (φ₁ : ℂ → V) z v := by
    simpa only [WithLp.fstL_apply] using hf (WithLp.fstL 2 ℝ V V) v
  have hf2 (v : ℂ) : (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z v).snd = fderiv ℝ (φ₂ : ℂ → V) z v := by
    simpa only [WithLp.sndL_apply] using hf (WithLp.sndL 2 ℝ V V) v
  rw [inner_crFormalAdjoint, inner_crFormalAdjoint, inner_crFormalAdjoint]
  simp [e, hf1, hf2, φ₁, φ₂, inner_add_right]
  ring

/-- Evaluates `∫ ⟪crFormalAdjoint J₂ DJ₂ S₂ Φ, Ξ⟫` on `WithLp 2 (V × V)` by splitting into the
two coordinate rows and combining `integral_commutator_of_hasWeakFDerivOn` (row 1) and
`HasWeakLineDerivOn.integral_inner_lineDeriv_comm` (row 2) with `integral_lineDeriv_crEquation`. -/
private theorem integral_inner_crFormalAdjoint_differentiated_aux [FiniteDimensional ℝ V]
    {p q : ℝ≥0∞} (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) :
    let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
    ∫ z, ⟪crFormalAdjoint (fun w => (J w).withLpProdMap 2 (J w))
        (fun w => (ContinuousLinearMap.withLpDiagL 2 ℝ V V).comp (DJ w))
        (fun w => e.arrowCongr e (differentiatedCRCoefficient (S w) (DJ w))) Φ z,
        WithLp.toLp 2 (Dξ z 1, Dξ z I)⟫_ℝ =
      ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z,
        WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))⟫_ℝ := by
  intro e
  let φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.fstL 2 ℝ V V) Φ
  let φ₂ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.sndL 2 ℝ V V) Φ
  have hDξq : MemLpLoc q Ω Dξ := memWkpLoc_zero_iff.1 (hξ.memWkpLoc_of_hasWeakFDerivOn hDξ)
  have hDξv (v : ℂ) : MemLpLoc q Ω (fun z => Dξ z v) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V v)
  have iA (v : ℂ) (φ : 𝓓(Ω, V)) := hc.integrable_inner_crFormalAdjoint hpq (hDξv v) φ
  have iB (v : ℂ) (φ : 𝓓(Ω, V)) : Integrable (fun z => ⟪(φ : ℂ → V) z, DJ z v (Dξ z I)⟫_ℝ) :=
    φ.integrable_inner ((hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
      ).locallyIntegrableOn_clm_apply (hDξv I) hpq Ω.isOpen.isLocallyClosed)
  have hrow1 : (∫ z, ⟪crFormalAdjoint J DJ S φ₁ z, Dξ z 1⟫_ℝ) +
      (∫ z, ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) =
      ∫ z, ⟪(φ₁ : ℂ → V) z, Dη z 1 - DS z 1 (ξ z)⟫_ℝ := by
    rw [hc.integral_inner_crFormalAdjoint_eq_terms hpq (hDξv 1) φ₁]
    linarith [integral_commutator_of_hasWeakFDerivOn hp hq hpq hc hDξ hξ.memLpLoc hDξq φ₁,
      integral_lineDeriv_crEquation hp hq hpq hc.memLpLoc_coeff hS hDS hξ hDξ hDη heq 1 φ₁]
  have hrow2 : (∫ z, ⟪crFormalAdjoint J DJ S φ₂ z, Dξ z I⟫_ℝ) +
      (∫ z, ⟪(φ₂ : ℂ → V) z, DJ z I (Dξ z I)⟫_ℝ) =
      ∫ z, ⟪(φ₂ : ℂ → V) z, Dη z I - DS z I (ξ z)⟫_ℝ := by
    have hmixed := (hDξ.hasWeakLineDerivOn 1).integral_inner_lineDeriv_comm
      (hDξ.hasWeakLineDerivOn I) φ₂
    simp only [TestFunction.lineDeriv_eq_fderiv] at hmixed
    rw [hc.integral_inner_crFormalAdjoint_eq_terms hpq (hDξv I) φ₂, ← hmixed]
    linarith [integral_lineDeriv_crEquation hp hq hpq hc.memLpLoc_coeff hS hDS hξ hDξ hDη heq I φ₂]
  have hloc := locallyIntegrableOn_differentiatedCR_coord hpq hS hDS hξ.memLpLoc hDη
  rw [integral_congr_ae (.of_forall fun z => inner_crFormalAdjoint_withLp_eq Φ z (Dξ z 1) (Dξ z I)),
    integral_add, integral_add (iA 1 φ₁) (iB 1 φ₁), integral_add (iA I φ₂) (iB I φ₂),
    hrow1, hrow2, ← integral_add (φ₁.integrable_inner (hloc 1)) (φ₂.integrable_inner (hloc I))]
  · exact integral_congr_ae (.of_forall fun z => by simp [φ₁, φ₂])
  · exact (iA 1 φ₁).add (iB 1 φ₁)
  · exact (iA I φ₂).add (iB I φ₂)

/-- **The weak differentiated Cauchy–Riemann system.** Let `1 < p, q ≤ ∞` satisfy `p⁻¹ + q⁻¹ ≤ 1`.
If `J, S ∈ W^{1,p}_loc(Ω)` with weak derivatives `DJ, DS`, `ξ ∈ W^{1,q}_loc(Ω)` with weak
derivative `Dξ`, and `η` has weak derivative `Dη` on `Ω` such that `∂_s ξ + J ∂_t ξ + S ξ = η`
almost everywhere on `Ω`, then `Ξ = (∂_s ξ, ∂_t ξ)` valued in the Hilbert product
`WithLp 2 (V × V)` is a weak solution (`TauCeti.IsWeakCRSolution`) of
`∂_s Ξ + diag(J, J) ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` with
`S₂ = TauCeti.differentiatedCRCoefficient S DJ`. -/
theorem isWeakCRSolution_differentiated [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : 1 < p) (hq : 1 < q) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V} {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    IsWeakCRSolution q Ω
      (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => (ContinuousLinearMap.withLpDiagL 2 ℝ V V).comp (DJ z))
      (fun z => (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
        (differentiatedCRCoefficient (S z) (DJ z)))
      (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I))
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  let diagL := ContinuousLinearMap.withLpDiagL 2 ℝ V V
  have hDJ₂ : HasWeakFDerivOn volume Ω (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => diagL.comp (DJ z)) := by simpa [diagL] using hDJ.clm_comp diagL
  have hJ₂ : MemWkpLoc p Ω 1 (fun z => (J z).withLpProdMap 2 (J z)) := by
    simpa [diagL] using hJ.clm_comp diagL
  have hc₂ : IsSobolevCRCoefficients p Ω (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => diagL.comp (DJ z))
      (fun z => e.arrowCongr e (differentiatedCRCoefficient (S z) (DJ z))) :=
    ⟨hDJ₂, hJ₂.memLpLoc, memWkpLoc_zero_iff.1 (hJ₂.memWkpLoc_of_hasWeakFDerivOn hDJ₂),
      (memWkpLoc_zero_iff.1 ((memWkpLoc_zero_iff.2 hS.memLpLoc).differentiatedCRCoefficient
        hJ hDJ)).clm_comp (e.arrowCongr e).toContinuousLinearMap⟩
  have hΞq : MemLpLoc q Ω (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) := by
    simpa only [e, WithLp.prodContinuousLinearEquiv_symm_apply] using
      e.comp_memLpLoc_iff.2 (memWkpLoc_zero_iff.1 (hξ.memWkpLoc_partials_of_hasWeakFDerivOn hDξ))
  have hloc := locallyIntegrableOn_differentiatedCR_coord hpq hS hDS hξ.memLpLoc hDη
  have hHloc : LocallyIntegrableOn
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) Ω volume := by
    rw [TauCeti.toLp_prodMk_eq_add (𝕜 := ℝ)]
    exact ((e.toContinuousLinearMap.comp (.inl ℝ V V)).locallyIntegrableOn_comp (hloc 1)).add
      ((e.toContinuousLinearMap.comp (.inr ℝ V V)).locallyIntegrableOn_comp (hloc I))
  obtain ⟨p₀, q₀, hp₀, hq₀, hp₀p, hq₀q, hp₀q₀⟩ :
      ∃ p₀ q₀ : ℝ≥0∞, p₀ ≠ ⊤ ∧ q₀ ≠ ⊤ ∧ p₀ ≤ p ∧ q₀ ≤ q ∧ p₀⁻¹ + q₀⁻¹ ≤ 1 := by
    rcases eq_or_ne p ⊤ with rfl | hpt <;> rcases eq_or_ne q ⊤ with rfl | hqt
    · exact ⟨2, 2, ENNReal.ofNat_ne_top, ENNReal.ofNat_ne_top, le_top, le_top,
        ENNReal.inv_two_add_inv_two.le⟩
    · refine ⟨(1 - q⁻¹)⁻¹, q,
        ENNReal.inv_ne_top.2 (tsub_pos_of_lt (ENNReal.inv_lt_one.2 hq)).ne', hqt, le_top,
        le_rfl, ?_⟩
      rw [inv_inv, tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hq.le)]
    · refine ⟨p, (1 - p⁻¹)⁻¹, hpt,
        ENNReal.inv_ne_top.2 (tsub_pos_of_lt (ENNReal.inv_lt_one.2 hp)).ne', le_rfl, le_top, ?_⟩
      rw [inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_one.2 hp.le)]
    · exact ⟨p, q, hpt, hqt, le_rfl, le_rfl, hpq⟩
  have hJ₀ := hJ.mono_exponent hp₀p
  have hS₀ := hS.mono_exponent hp₀p
  have hξ₀ := hξ.mono_exponent hq₀q
  have hc₀ : IsSobolevCRCoefficients p₀ Ω J DJ S :=
    ⟨hDJ, hJ₀.memLpLoc, memWkpLoc_zero_iff.1 (hJ₀.memWkpLoc_of_hasWeakFDerivOn hDJ), hS₀.memLpLoc⟩
  exact isWeakCRSolution_iff.2 ⟨hΞq, hHloc, fun Φ =>
    ⟨hc₂.integrable_inner_crFormalAdjoint hpq hΞq Φ,
      integral_inner_crFormalAdjoint_differentiated_aux hp₀ hq₀ hp₀q₀ hc₀ hS₀ hDS hξ₀ hDξ hDη heq
        Φ⟩⟩

end WeakDifferentiated

end TauCeti
