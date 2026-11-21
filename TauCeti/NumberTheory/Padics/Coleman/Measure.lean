/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.LinearTopology
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Coleman.Norm
public import TauCeti.NumberTheory.Padics.Measure.PhiPsi
public import TauCeti.NumberTheory.Padics.Measure.RootTranslation

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Vandermonde
import TauCeti.NumberTheory.Padics.Coleman.Limit
import TauCeti.NumberTheory.Padics.Measure.Topology.Amice
import TauCeti.RingTheory.Huber.Padic.Basic
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.PiTopology

/-!
# Coleman operators, `ψ` on `ℤ_p⟦X⟧`, and root-of-unity evaluations

This file bridges Coleman's `coord`, `trace`, and `norm` (`Coleman.Basic`, `Coleman.Norm`) to:
1. **Amice-transformed `ℤ_p`-measures on `ℤ_[p]⟦X⟧`**: identifying `coord p ℤ_[p] 0` with
   `TauCeti.psiSeries p`, yielding `ψ(Φ(F)) = F`, `τ(F) = p * ψ(F)`, and fixed-point/kernel
   equivalences.
2. **Cyclotomic root-of-unity translates**: for `(p)`-adically complete `O`, `ρ : O →+* S` into a
   complete linearly topologized domain `S`, and primitive `p`-th root `ζ ∈ S` with `ζ - 1`
   topologically nilpotent, expressing the sum and product of `(map ρ F)(ζ ^ i * (1 + X) - 1)` as
   `map ρ (Φ(τ(F)))` and `map ρ (Φ(N(F)))` (with uniqueness for injective `ρ`), specialized to
   `rootTranslation` on `ℤ_[p]⟦X⟧ → 𝓞_ℂ_[p]⟦X⟧`.

## Main results

* `TauCeti.Coleman.coord_zero_eq_psiSeries`, `TauCeti.Coleman.psiSeries_frobeniusHom`,
  `TauCeti.Coleman.trace_eq_p_mul_psiSeries`,
  `TauCeti.Coleman.trace_eq_p_mul_self_iff_psiSeries_eq_self`,
  `TauCeti.Coleman.trace_eq_zero_iff_psiSeries_eq_zero`: bridge between `coord`/`trace` and `ψ`.
* `TauCeti.Coleman.eval₂_frobeniusHom`, `TauCeti.IwasawaAveraging.rootTranslation_frobeniusHom`:
  `p`-th root translates fix power series in the image of `Φ`.
* `IsPrimitiveRoot.sum_eval₂_map_eq_map_frobeniusHom_trace`,
  `IsPrimitiveRoot.prod_eval₂_map_eq_map_frobeniusHom_norm`,
  `IsPrimitiveRoot.map_frobeniusHom_eq_prod_eval₂_map_iff`, and their `rootTranslation`
  specializations `IsPrimitiveRoot.sum_rootTranslation_eq_map_frobeniusHom_trace`,
  `IsPrimitiveRoot.prod_rootTranslation`,
  `IsPrimitiveRoot.map_frobeniusHom_eq_prod_rootTranslation_iff`.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §§II, IV (Thm. 4,
  Cor. 5(i), Thm. 11, Cor. 12(ii)).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §§2.2, 3.3.
* R. Sharifi, *Iwasawa Theory*, §5.4 (Lemma 5.4.14).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), §§3.5,
  10.2–10.3 (Lemmas 10.8–10.11).
* C. Birkbeck et al., `CBirkbeck/padic-L-functions` (`Coleman/NormOperator.lean`, commit
  `45307015169791f1316f23a459c8e92ed5961c54`), adapted for the Vandermonde intertwining proof and
  generalized here to arbitrary `(p)`-adically complete coefficient rings `O`.
-/

public noncomputable section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti.Coleman

variable {p : ℕ} [Fact p.Prime]

/-- On `ℤ_[p]⟦X⟧`, the zeroth Coleman coordinate equals `TauCeti.psiSeries p`. -/
theorem coord_zero_eq_psiSeries (F : ℤ_[p]⟦X⟧) :
    coord p ℤ_[p] ⟨0, (Fact.out : p.Prime).pos⟩ F = TauCeti.psiSeries p F := by
  have hAdic : IsAdic (Ideal.span {(p : ℤ_[p])}) :=
    PadicInt.maximalIdeal_eq_span_p (p := p) ▸ TauCeti.Huber.PadicInt.isAdic_maximalIdeal
  refine congrFun ((PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).equalizer
    (continuous_coord hAdic _) TauCeti.continuous_psiSeries ?_) F
  funext P
  let Q : Polynomial ℤ_[p] := P.comp (Polynomial.X - 1)
  have hP : (P : ℤ_[p]⟦X⟧) = ∑ n ∈ Q.support, Q.coeff n • ((1 + X : ℤ_[p]⟦X⟧) ^ n) := by
    conv_lhs => rw [show P = Q.comp (1 + Polynomial.X) by
      rw [Polynomial.comp_assoc]; simp [Polynomial.sub_comp], Q.as_sum_support_C_mul_X_pow]
    rw [Polynomial.sum_comp, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    exact Finset.sum_congr rfl fun n _ ↦ by
      simp [Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.smul_eq_C_mul]
  simp only [Function.comp_apply, hP, map_sum, map_smul]
  refine Finset.sum_congr rfl fun n _ ↦ congrArg _ ?_
  simp only [coord_one_add_X_pow, TauCeti.psiSeries_one_add_X_pow,
    show (0 = n % p ↔ p ∣ n) by rw [eq_comm, Nat.dvd_iff_mod_eq_zero]]

/-- On `ℤ_[p]⟦X⟧`, `ψ` is a left inverse to Frobenius substitution `Φ`. -/
@[simp]
theorem psiSeries_frobeniusHom (F : ℤ_[p]⟦X⟧) :
    TauCeti.psiSeries p (frobeniusHom p ℤ_[p] F) = F := by
  simp only [← coord_zero_eq_psiSeries, coord_frobeniusHom, ↓reduceIte]

/-- **Coleman's trace is `p` times measure `ψ` on `ℤ_[p]⟦X⟧`.** -/
theorem trace_eq_p_mul_psiSeries (F : ℤ_[p]⟦X⟧) :
    trace p ℤ_[p] F = (p : ℤ_[p]⟦X⟧) * TauCeti.psiSeries p F := by
  rw [trace_eq_p_mul_coord_zero, coord_zero_eq_psiSeries]

/-- On `ℤ_[p]⟦X⟧`, `τ(F) = p * F` if and only if `ψ(F) = F`. -/
theorem trace_eq_p_mul_self_iff_psiSeries_eq_self (F : ℤ_[p]⟦X⟧) :
    trace p ℤ_[p] F = (p : ℤ_[p]⟦X⟧) * F ↔ TauCeti.psiSeries p F = F := by
  rw [trace_eq_p_mul_psiSeries,
    mul_right_inj' (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]

/-- On `ℤ_[p]⟦X⟧`, Coleman's trace vanishes if and only if `ψ` vanishes. -/
theorem trace_eq_zero_iff_psiSeries_eq_zero (F : ℤ_[p]⟦X⟧) :
    trace p ℤ_[p] F = 0 ↔ TauCeti.psiSeries p F = 0 := by
  rw [trace_eq_p_mul_psiSeries, mul_eq_zero,
    or_iff_right (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]

private theorem hasEval_C_pow_mul_one_add_X_sub_one
    {S : Type*} [CommRing S] [TopologicalSpace S] [IsLinearTopology S S]
    {ζ : S} (hζ_nil : IsTopologicallyNilpotent (ζ - 1)) (i : ℕ) :
    HasEval (C (ζ ^ i) * (1 + X) - 1 : S⟦X⟧) := by
  apply MvPowerSeries.LinearTopology.isTopologicallyNilpotent_of_constantCoeff
  simpa only [← PowerSeries.constantCoeff_eq, map_sub, map_mul, constantCoeff_C,
    map_add, map_one, constantCoeff_X, add_zero, mul_one, ← geom_sum_mul ζ i] using
    PowerSeries.HasEval.mul_left (∑ j ∈ Finset.range i, ζ ^ j) hζ_nil

/-- Topological evaluation at `ζ ^ i * (1 + X) - 1` fixes the image of `Φ` when `ζ ^ p = 1` and
`ζ - 1` is topologically nilpotent. -/
theorem eval₂_frobeniusHom
    {p : ℕ} {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζp : ζ ^ p = 1) (hζ_nil : IsTopologicallyNilpotent (ζ - 1)) (i : ℕ) (g : S⟦X⟧) :
    eval₂ C (C (ζ ^ i) * (1 + X) - 1) (frobeniusHom p S g) = frobeniusHom p S g := by
  have hEval := hasEval_C_pow_mul_one_add_X_sub_one hζ_nil i
  let e : S⟦X⟧ →+* S⟦X⟧ := eval₂Hom PowerSeries.WithPiTopology.continuous_C hEval
  have hcont : Continuous e :=
    (coe_eval₂Hom PowerSeries.WithPiTopology.continuous_C hEval).symm ▸
      continuous_eval₂ PowerSeries.WithPiTopology.continuous_C hEval
  rw [← coe_eval₂Hom PowerSeries.WithPiTopology.continuous_C hEval]
  refine congrFun ((PowerSeries.WithPiTopology.denseRange_toPowerSeries S).equalizer
    (hcont.comp (continuous_frobeniusHom (p := p))) (continuous_frobeniusHom (p := p)) ?_) g
  funext P; simp only [Function.comp_apply]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.coe_add, map_add, hP, hQ]
  | monomial n a =>
    have hX : e (frobeniusHom p S X) = frobeniusHom p S X := by
      rw [frobeniusHom_X, map_sub, map_one, map_pow, map_add, map_one, coe_eval₂Hom, eval₂_X,
        add_sub_cancel, mul_pow, ← map_pow, ← pow_mul, mul_comm i p, pow_mul, hζp, one_pow,
        map_one, one_mul]
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      map_mul, map_pow, frobeniusHom_C, show e (C a) = C a by rw [coe_eval₂Hom, eval₂_C], hX]

end TauCeti.Coleman

namespace TauCeti.IwasawaAveraging

open PadicComplex (integralCoefficientMap continuous_integralCoefficientMap)

private theorem rootTranslation_eq_eval₂_map (p : ℕ) [Fact p.Prime] (ζ : 𝓞_ℂ_[p])
    (hζ : ζ ^ p = 1) (i : ℕ) (F : ℤ_[p]⟦X⟧) :
    rootTranslation p ζ hζ i F =
      eval₂ C (C (ζ ^ i) * (1 + X) - 1) (PowerSeries.map (integralCoefficientMap p) F) := by
  have hEval := hasEval_rootTranslation p ζ hζ i
  have huniq := eval₂_unique (φ := C.comp (integralCoefficientMap p))
    (PowerSeries.WithPiTopology.continuous_C.comp (continuous_integralCoefficientMap p)) hEval
    ((continuous_eval₂ PowerSeries.WithPiTopology.continuous_C hEval).comp
      (PowerSeries.WithPiTopology.continuous_map (continuous_integralCoefficientMap p)))
    (fun P ↦ by simp only [Function.comp_apply, ← Polynomial.polynomial_map_coe, eval₂_coe,
      Polynomial.eval₂_map])
  exact (rootTranslation_apply ..).trans (congrFun huniq F).symm

/-- Every `p`-th root translation fixes series in the image of `Φ`, up to `ℤ_[p] → 𝓞_ℂ_[p]`. -/
@[simp]
theorem rootTranslation_frobeniusHom (p : ℕ) [Fact p.Prime] (ζ : 𝓞_ℂ_[p]) (hζ : ζ ^ p = 1)
    (i : ℕ) (g : ℤ_[p]⟦X⟧) :
    rootTranslation p ζ hζ i (Coleman.frobeniusHom p ℤ_[p] g) =
      PowerSeries.map (integralCoefficientMap p) (Coleman.frobeniusHom p ℤ_[p] g) := by
  rw [rootTranslation_eq_eval₂_map, Coleman.map_frobeniusHom,
    Coleman.eval₂_frobeniusHom hζ (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ) i,
    ← Coleman.map_frobeniusHom]

end TauCeti.IwasawaAveraging

namespace IsPrimitiveRoot

open TauCeti TauCeti.IwasawaAveraging
open PadicComplex (integralCoefficientMap)

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
private theorem eval₂_root_map_frobeniusHom_mul_pow
    {O S : Type*} [CommRing O] [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζp : ζ ^ p = 1) (hζ_nil : IsTopologicallyNilpotent (ζ - 1))
    (ρ : O →+* S) (i n : ℕ) (a : O⟦X⟧) :
    eval₂ C (C (ζ ^ i) * (1 + X) - 1)
        (PowerSeries.map ρ (Coleman.frobeniusHom p O a * (1 + X) ^ n)) =
      PowerSeries.map ρ (Coleman.frobeniusHom p O a) * (C (ζ ^ i) * (1 + X)) ^ n := by
  have hEval := Coleman.hasEval_C_pow_mul_one_add_X_sub_one hζ_nil i
  let e : S⟦X⟧ →+* S⟦X⟧ := eval₂Hom PowerSeries.WithPiTopology.continuous_C hEval
  rw [← coe_eval₂Hom PowerSeries.WithPiTopology.continuous_C hEval]
  change e _ = _
  rw [map_mul, map_mul, map_pow, map_add, map_one, map_X, map_pow, map_add, map_one]
  simp only [e, coe_eval₂Hom, eval₂_X, add_sub_cancel, Coleman.map_frobeniusHom,
    Coleman.eval₂_frobeniusHom hζp hζ_nil i]

/-- **Root-of-unity sum equals Frobenius of Coleman's trace** (Sharifi, Lemma 5.4.14; RJW,
Lemma 10.8): `∑ i : Fin p, (map ρ F)(ζ ^ i * (1 + X) - 1) = map ρ (Φ(τ(F)))`. -/
theorem sum_eval₂_map_eq_map_frobeniusHom_trace
    {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    {S : Type*} [CommRing S] [IsDomain S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hζ_nil : IsTopologicallyNilpotent (ζ - 1))
    (ρ : O →+* S) (F : O⟦X⟧) :
    ∑ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
      PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.trace p O F)) := by
  have hterm (i : Fin p) :
      eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
        ∑ j : Fin p, PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.coord p O j F)) *
          (1 + X) ^ (j : ℕ) * C ((ζ ^ (j : ℕ)) ^ (i : ℕ)) := by
    have hEval := Coleman.hasEval_C_pow_mul_one_add_X_sub_one hζ_nil (i : ℕ)
    conv_lhs => rw [← Coleman.sum_frobeniusHom_coord (p := p) F]
    rw [← coe_eval₂Hom PowerSeries.WithPiTopology.continuous_C hEval, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [coe_eval₂Hom, eval₂_root_map_frobeniusHom_mul_pow hζ.pow_eq_one hζ_nil, mul_pow,
      ← map_pow, ← pow_mul, mul_comm (i : ℕ) (j : ℕ), pow_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm, Finset.sum_eq_single ⟨0, (Fact.out : p.Prime).pos⟩ ?_ (by simp)]
  · simp [Coleman.trace_eq_p_mul_coord_zero, mul_comm]
  · intro j _ hj
    rw [← Finset.mul_sum, ← map_sum]
    have hsum : ∑ i : Fin p, (ζ ^ (j : ℕ)) ^ (i : ℕ) = 0 :=
      mul_right_cancel₀ (sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt
          (fun h ↦ hj (Fin.ext h)) j.isLt)) <| by
        rw [Fin.sum_univ_eq_sum_range, geom_sum_mul, ← pow_mul, mul_comm, pow_mul,
          hζ.pow_eq_one, one_pow, sub_self, zero_mul]
    rw [hsum, map_zero, mul_zero]

/-- **Root-of-unity product equals Frobenius of Coleman's norm** (Sharifi, Lemma 5.4.14; RJW,
Lemmas 10.8–10.11): `∏ i : Fin p, (map ρ F)(ζ ^ i * (1 + X) - 1) = map ρ (Φ(N(F)))`. -/
theorem prod_eval₂_map_eq_map_frobeniusHom_norm
    {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    {S : Type*} [CommRing S] [IsDomain S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hζ_nil : IsTopologicallyNilpotent (ζ - 1))
    (ρ : O →+* S) (F : O⟦X⟧) :
    ∏ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
      PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.norm p O F)) := by
  let ψ : O⟦X⟧ →+* S⟦X⟧ := (PowerSeries.map ρ).comp (Coleman.frobeniusHom p O).toRingHom
  let V : Matrix (Fin p) (Fin p) S⟦X⟧ := Matrix.vandermonde fun i ↦ C (ζ ^ (i : ℕ)) * (1 + X)
  have hmat : Matrix.diagonal
      (fun i : Fin p ↦ eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F)) * V =
        V * (Coleman.leftMulMatrix p O F).map ψ := by
    refine Matrix.ext fun i j ↦ ?_
    have hEval := Coleman.hasEval_C_pow_mul_one_add_X_sub_one hζ_nil (i : ℕ)
    have hcol := congrArg ((eval₂Hom PowerSeries.WithPiTopology.continuous_C hEval).comp
      (PowerSeries.map ρ)) (Coleman.mul_one_add_X_pow_eq_sum_leftMulMatrix (p := p) F j)
    have h1X (k : Fin p) : eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1)
        (PowerSeries.map ρ ((1 + X) ^ (k : ℕ))) = (C (ζ ^ (i : ℕ)) * (1 + X)) ^ (k : ℕ) := by
      simpa only [map_one, one_mul] using
        eval₂_root_map_frobeniusHom_mul_pow (p := p) hζ.pow_eq_one hζ_nil ρ (i : ℕ) (k : ℕ) 1
    simp only [RingHom.comp_apply, map_mul, map_sum, coe_eval₂Hom, h1X] at hcol
    rw [Matrix.diagonal_mul, Matrix.mul_apply]; dsimp only [V]
    rw [Matrix.vandermonde_apply, hcol]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.vandermonde_apply, Coleman.map_frobeniusHom,
      Coleman.eval₂_frobeniusHom hζ.pow_eq_one hζ_nil, ← Coleman.map_frobeniusHom, mul_comm]; rfl
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hV : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr fun i j hij ↦
    Fin.ext (hζ.injOn_pow (by simp) (by simp)
      (C_injective (mul_right_cancel₀ (fun h ↦ by simpa using congrArg constantCoeff h) hij)))
  have hprod : ∏ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
      ((Coleman.leftMulMatrix p O F).map ψ).det := mul_right_cancel₀ hV (by rw [hdet, mul_comm])
  rw [hprod, show ((Coleman.leftMulMatrix p O F).map ψ).det = ψ (Coleman.leftMulMatrix p O F).det
    from (RingHom.map_det ψ _).symm, ← Coleman.norm_eq_det_leftMulMatrix]; rfl

/-- **Uniqueness of Coleman's norm via root-of-unity products** (Sharifi, Lemma 5.4.14; RJW,
Lemmas 10.8–10.11): for injective `ρ`, `map ρ (Φ(G)) = ∏ i, (map ρ F)(ζ ^ i * (1 + X) - 1)` iff
`G = N(F)`. -/
theorem map_frobeniusHom_eq_prod_eval₂_map_iff
    {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    {S : Type*} [CommRing S] [IsDomain S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hζ_nil : IsTopologicallyNilpotent (ζ - 1))
    {ρ : O →+* S} (hρ : Function.Injective ρ) (F G : O⟦X⟧) :
    PowerSeries.map ρ (Coleman.frobeniusHom p O G) =
        ∏ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) ↔
      G = Coleman.norm p O F := by
  rw [hζ.prod_eval₂_map_eq_map_frobeniusHom_norm hζ_nil ρ F,
    (PowerSeries.map_injective ρ hρ).eq_iff, (Coleman.frobeniusHom_injective (p := p)).eq_iff]

section PadicInt

variable {ζ : 𝓞_ℂ_[p]}

/-- **Root-translation sum equals `Φ(τ(F))`** on `ℤ_[p]⟦X⟧ → 𝓞_ℂ_[p]⟦X⟧` (Sharifi, Lemma 5.4.14). -/
theorem sum_rootTranslation_eq_map_frobeniusHom_trace (hζ : IsPrimitiveRoot ζ p) (F : ℤ_[p]⟦X⟧) :
    ∑ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F =
      PowerSeries.map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] (Coleman.trace p ℤ_[p] F)) := by
  simp_rw [rootTranslation_eq_eval₂_map]
  exact hζ.sum_eval₂_map_eq_map_frobeniusHom_trace
    (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ.pow_eq_one) (integralCoefficientMap p) F

/-- **Root-translation product equals `Φ(N(F))`** on `ℤ_[p]⟦X⟧` (RJW, Lemmas 10.8–10.11). -/
theorem prod_rootTranslation (hζ : IsPrimitiveRoot ζ p) (F : ℤ_[p]⟦X⟧) :
    ∏ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F =
      PowerSeries.map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] (Coleman.norm p ℤ_[p] F)) := by
  simp_rw [rootTranslation_eq_eval₂_map]
  exact hζ.prod_eval₂_map_eq_map_frobeniusHom_norm
    (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ.pow_eq_one) (integralCoefficientMap p) F

/-- **Uniqueness of Coleman's norm on `ℤ_[p]⟦X⟧`** (Sharifi, Lemma 5.4.14; RJW, Lemmas 10.8–11). -/
theorem map_frobeniusHom_eq_prod_rootTranslation_iff (hζ : IsPrimitiveRoot ζ p) (F G : ℤ_[p]⟦X⟧) :
    PowerSeries.map (integralCoefficientMap p) (Coleman.frobeniusHom p ℤ_[p] G) =
        ∏ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F ↔
      G = Coleman.norm p ℤ_[p] F := by
  simp_rw [rootTranslation_eq_eval₂_map]
  exact hζ.map_frobeniusHom_eq_prod_eval₂_map_iff
    (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ.pow_eq_one)
    (PadicComplex.integralCoefficientMap_injective p) F G

end PadicInt

end IsPrimitiveRoot
