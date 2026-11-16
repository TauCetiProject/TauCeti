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

This file bridges the abstract Coleman operators (`coord`, `trace`, `norm`) of
`TauCeti.NumberTheory.Padics.Coleman.Basic` and `TauCeti.NumberTheory.Padics.Coleman.Norm` to two
concrete settings needed for Coleman interpolation and `p`-adic `L`-functions:

1. **Amice-transformed `ℤ_p`-measures on `ℤ_[p]⟦X⟧`.** Using the global `(p)`-adic completeness
   instance `PadicInt.isAdicComplete_span_p` from `TauCeti.NumberTheory.Padics.Basic`, we identify
   Coleman's zeroth coordinate with `TauCeti.psiSeries p`, deduce `τ(F) = p * ψ(F)` and
   `ψ(Φ(F)) = F`, and relate fixed points and kernels of `τ` and `ψ`.
2. **Cyclotomic root-of-unity translates.** For a general `(p)`-adically complete ring `O`, a ring
   homomorphism `ρ : O →+* S` into a complete, linearly topologized domain `S`, and a primitive
   `p`-th root of unity `ζ ∈ S` with `ζ - 1` topologically nilpotent, we prove that the sum and
   product of the `p` translates `(map ρ F)(ζ ^ i * (1 + X) - 1)` equal `map ρ (Φ(τ(F)))` and
   `map ρ (Φ(N(F)))`, together with the uniqueness characterization of `N(F)` when `ρ` is
   injective. Specializing to `ℤ_[p] → 𝓞_ℂ_[p]` recovers the corresponding identities for
   `TauCeti.IwasawaAveraging.rootTranslation`.

## Main results

* `TauCeti.Coleman.coord_zero_eq_psiSeries`: the zeroth Coleman coordinate on `ℤ_[p]⟦X⟧` equals
  `TauCeti.psiSeries p`.
* `TauCeti.Coleman.psiSeries_frobeniusHom`: `ψ(Φ(F)) = F` on `ℤ_[p]⟦X⟧`.
* `TauCeti.Coleman.trace_eq_p_mul_psiSeries`: `τ(F) = p * ψ(F)` on `ℤ_[p]⟦X⟧`, so `τ(F) = p * F`
  iff `ψ(F) = F` and `τ(F) = 0` iff `ψ(F) = 0`.
* `TauCeti.Coleman.eval₂_frobeniusHom` and `TauCeti.IwasawaAveraging.rootTranslation_frobeniusHom`:
  `p`-th root translates fix power series in the image of `Φ`.
* `IsPrimitiveRoot.sum_eval₂_map_eq_map_frobeniusHom_trace`,
  `IsPrimitiveRoot.prod_eval₂_map_eq_map_frobeniusHom_norm`, and
  `IsPrimitiveRoot.map_frobeniusHom_eq_prod_eval₂_map_iff`: general root-of-unity sum, product,
  and norm-uniqueness formulas over `(p)`-adically complete `O`.
* `IsPrimitiveRoot.sum_rootTranslation_eq_map_frobeniusHom_trace`,
  `IsPrimitiveRoot.prod_rootTranslation`, and
  `IsPrimitiveRoot.map_frobeniusHom_eq_prod_rootTranslation_iff`: specializations to
  `rootTranslation` on `ℤ_[p]⟦X⟧ → 𝓞_ℂ_[p]⟦X⟧`.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §§II, IV (Theorem 4,
  Corollary 5(i), Theorem 11, Corollary 12(ii)).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §§2.2, 3.3
  (Lemma 2.2.5).
* R. Sharifi, *Iwasawa Theory*, §5.4 (Lemma 5.4.14).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), §§3.5,
  10.2–10.3 (Lemmas 10.8–10.11).
* C. Birkbeck et al., `CBirkbeck/padic-L-functions` (`Coleman/NormOperator.lean`, commit
  `45307015169791f1316f23a459c8e92ed5961c54`), adapted for the Vandermonde intertwining proof of
  the root-of-unity product formula and generalized here to arbitrary `(p)`-adically complete
  coefficient rings `O`.
-/

public noncomputable section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti.Coleman

variable {p : ℕ} [Fact p.Prime]

/-- **Identification of the zeroth Coleman coordinate with measure `ψ`.** On `ℤ_[p]⟦X⟧`, the zeroth
coordinate in the Coleman basis equals `TauCeti.psiSeries p`. -/
theorem coord_zero_eq_psiSeries (F : ℤ_[p]⟦X⟧) :
    coord p ℤ_[p] ⟨0, (Fact.out : p.Prime).pos⟩ F = TauCeti.psiSeries p F := by
  have hAdic : IsAdic (Ideal.span {(p : ℤ_[p])}) :=
    PadicInt.maximalIdeal_eq_span_p (p := p) ▸ TauCeti.Huber.PadicInt.isAdic_maximalIdeal
  refine congrFun ((PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).equalizer
    (continuous_coord hAdic _) TauCeti.continuous_psiSeries ?_) F
  funext P
  let Q : Polynomial ℤ_[p] := P.comp (Polynomial.X - 1)
  have hcomp : Q.comp (1 + Polynomial.X) = P := by
    rw [Polynomial.comp_assoc]
    simp [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp]
  have hP : (P : ℤ_[p]⟦X⟧) = ∑ n ∈ Q.support, Q.coeff n • ((1 + X : ℤ_[p]⟦X⟧) ^ n) := by
    conv_lhs => rw [← hcomp, Q.as_sum_support_C_mul_X_pow]
    rw [Polynomial.sum_comp, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.smul_eq_C_mul]
  simp only [Function.comp_apply, hP, map_sum, map_smul]
  refine Finset.sum_congr rfl fun n _ ↦ congrArg _ ?_
  rw [coord_one_add_X_pow, TauCeti.psiSeries_one_add_X_pow]
  have hiff : (0 : ℕ) = n % p ↔ p ∣ n := by rw [eq_comm, Nat.dvd_iff_mod_eq_zero]
  simp [hiff]

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
  have hi : IsTopologicallyNilpotent (ζ ^ i - 1) := by
    rw [← geom_sum_mul ζ i]
    exact PowerSeries.HasEval.mul_left _ hζ_nil
  apply MvPowerSeries.LinearTopology.isTopologicallyNilpotent_of_constantCoeff
  simpa only [← PowerSeries.constantCoeff_eq, map_sub, map_mul, constantCoeff_C,
    map_add, map_one, constantCoeff_X, add_zero, mul_one] using hi

/-- Topological evaluation at `ζ ^ i * (1 + X) - 1` fixes every series in the image of Frobenius
substitution `Φ` whenever `ζ ^ p = 1` and `ζ - 1` is topologically nilpotent. -/
theorem eval₂_frobeniusHom
    {p : ℕ} {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζp : ζ ^ p = 1) (hζ_nil : IsTopologicallyNilpotent (ζ - 1)) (i : ℕ) (g : S⟦X⟧) :
    eval₂ C (C (ζ ^ i) * (1 + X) - 1) (frobeniusHom p S g) = frobeniusHom p S g := by
  have hEval := hasEval_C_pow_mul_one_add_X_sub_one hζ_nil i
  let e : S⟦X⟧ →+* S⟦X⟧ := eval₂Hom PowerSeries.WithPiTopology.continuous_C hEval
  have hcont : Continuous e := by
    rw [coe_eval₂Hom]
    exact continuous_eval₂ PowerSeries.WithPiTopology.continuous_C hEval
  have heq : e (frobeniusHom p S g) = frobeniusHom p S g := by
    refine congrFun ((PowerSeries.WithPiTopology.denseRange_toPowerSeries S).equalizer
      (hcont.comp continuous_frobeniusHom) continuous_frobeniusHom ?_) g
    funext P
    simp only [Function.comp_apply]
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => simp only [Polynomial.coe_add, map_add, hP, hQ]
    | monomial n a =>
      have hX : e (frobeniusHom p S X) = frobeniusHom p S X := by
        have hζi : (ζ ^ i) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
        have heX : e X = C (ζ ^ i) * (1 + X) - 1 := by
          rw [coe_eval₂Hom, eval₂_X]
        rw [frobeniusHom_X, map_sub, map_one, map_pow, map_add, map_one, heX,
          add_sub_cancel, mul_pow, ← map_pow, hζi, map_one, one_mul]
      have hC : e (C a) = C a := by rw [coe_eval₂Hom, eval₂_C]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
        map_mul, map_pow, frobeniusHom_C, hC, hX]
  simpa only [e, coe_eval₂Hom] using heq

end TauCeti.Coleman

namespace TauCeti.IwasawaAveraging

open PadicComplex (integralCoefficientMap continuous_integralCoefficientMap)

private theorem rootTranslation_eq_eval₂_map (p : ℕ) [Fact p.Prime] (ζ : 𝓞_ℂ_[p])
    (hζ : ζ ^ p = 1) (i : ℕ) (F : ℤ_[p]⟦X⟧) :
    rootTranslation p ζ hζ i F =
      eval₂ C (C (ζ ^ i) * (1 + X) - 1) (PowerSeries.map (integralCoefficientMap p) F) := by
  have hEval := hasEval_rootTranslation p ζ hζ i
  have huniq := eval₂_unique (φ := C.comp (integralCoefficientMap p))
    (PowerSeries.WithPiTopology.continuous_C.comp (continuous_integralCoefficientMap p))
    hEval
    ((continuous_eval₂ PowerSeries.WithPiTopology.continuous_C hEval).comp
      (PowerSeries.WithPiTopology.continuous_map (continuous_integralCoefficientMap p)))
    (fun P ↦ by
      simp only [Function.comp_apply, ← Polynomial.polynomial_map_coe, eval₂_coe,
        Polynomial.eval₂_map])
  rw [rootTranslation_apply]
  exact (congrFun huniq F).symm

/-- Every `p`-th root translation fixes series in the image of Frobenius substitution `Φ`,
up to the integral coefficient inclusion `ℤ_[p] → 𝓞_ℂ_[p]`. -/
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

/-- **Root-of-unity sum equals Frobenius of Coleman's trace** (Sharifi, *Iwasawa Theory*,
Lemma 5.4.14; Rodrigues Jacinto–Williams, Lemma 10.8). For a `(p)`-adically complete ring `O`,
a ring homomorphism `ρ : O →+* S` into a complete, linearly topologized domain `S`, and a
primitive `p`-th root of unity `ζ ∈ S` with `ζ - 1` topologically nilpotent,
`∑ i : Fin p, (map ρ F)(ζ ^ i * (1 + X) - 1) = map ρ (Φ(τ(F)))`. -/
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
        ∑ j : Fin p,
          PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.coord p O j F)) *
            (C ((ζ ^ (j : ℕ)) ^ (i : ℕ)) * (1 + X) ^ (j : ℕ)) := by
    let e : S⟦X⟧ →+* S⟦X⟧ := eval₂Hom PowerSeries.WithPiTopology.continuous_C
      (Coleman.hasEval_C_pow_mul_one_add_X_sub_one hζ_nil (i : ℕ))
    have he_eq : eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
        e (PowerSeries.map ρ F) := by
      rw [coe_eval₂Hom]
    conv_lhs => rw [he_eq, ← Coleman.sum_frobeniusHom_coord (p := p) F, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_mul, map_pow, map_add, map_one, map_X, map_pow, map_add, map_one]
    have heΦ : e (PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.coord p O j F))) =
        PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.coord p O j F)) := by
      rw [coe_eval₂Hom, Coleman.map_frobeniusHom,
        Coleman.eval₂_frobeniusHom hζ.pow_eq_one hζ_nil (i : ℕ), ← Coleman.map_frobeniusHom]
    have heX : e X = C (ζ ^ (i : ℕ)) * (1 + X) - 1 := by
      rw [coe_eval₂Hom, eval₂_X]
    rw [heΦ, heX, add_sub_cancel, mul_pow, ← map_pow, ← pow_mul, mul_comm (i : ℕ) (j : ℕ),
      pow_mul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hinner (j : Fin p) :
      ∑ i : Fin p,
          PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.coord p O j F)) *
            (C ((ζ ^ (j : ℕ)) ^ (i : ℕ)) * (1 + X) ^ (j : ℕ)) =
        if j = ⟨0, (Fact.out : p.Prime).pos⟩ then
          PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.trace p O F))
        else 0 := by
    have hfactor :
        ∑ i : Fin p,
            PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.coord p O j F)) *
              (C ((ζ ^ (j : ℕ)) ^ (i : ℕ)) * (1 + X) ^ (j : ℕ)) =
          PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.coord p O j F)) *
            (1 + X) ^ (j : ℕ) * C (∑ i : Fin p, (ζ ^ (j : ℕ)) ^ (i : ℕ)) := by
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hfactor]
    split_ifs with hj
    · subst hj
      simp only [pow_zero, one_pow, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, map_natCast]
      rw [Coleman.trace_eq_p_mul_coord_zero, map_mul, map_natCast, map_mul, map_natCast, mul_comm]
    · have hj0 : (j : ℕ) ≠ 0 := fun h ↦ hj (Fin.ext h)
      have hne : ζ ^ (j : ℕ) - 1 ≠ 0 :=
        sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt hj0 j.isLt)
      have hsum : ∑ i : Fin p, (ζ ^ (j : ℕ)) ^ (i : ℕ) = 0 := by
        apply mul_right_cancel₀ hne
        rw [Fin.sum_univ_eq_sum_range, geom_sum_mul, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one,
          one_pow, sub_self, zero_mul]
      rw [hsum, map_zero, mul_zero]
  simp_rw [hinner]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]

/-- **Root-of-unity product equals Frobenius of Coleman's norm** (Sharifi, *Iwasawa Theory*,
Lemma 5.4.14; Rodrigues Jacinto–Williams, Lemmas 10.8–10.11). For a `(p)`-adically complete ring
`O`, a ring homomorphism `ρ : O →+* S` into a complete, linearly topologized domain `S`, and a
primitive `p`-th root of unity `ζ ∈ S` with `ζ - 1` topologically nilpotent,
`∏ i : Fin p, (map ρ F)(ζ ^ i * (1 + X) - 1) = map ρ (Φ(N(F)))`. -/
theorem prod_eval₂_map_eq_map_frobeniusHom_norm
    {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    {S : Type*} [CommRing S] [IsDomain S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hζ_nil : IsTopologicallyNilpotent (ζ - 1))
    (ρ : O →+* S) (F : O⟦X⟧) :
    ∏ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
      PowerSeries.map ρ (Coleman.frobeniusHom p O (Coleman.norm p O F)) := by
  let ψ : O⟦X⟧ →+* S⟦X⟧ := (PowerSeries.map ρ).comp (Coleman.frobeniusHom p O).toRingHom
  let v : Fin p → S⟦X⟧ := fun i ↦ C (ζ ^ (i : ℕ)) * (1 + X)
  let V : Matrix (Fin p) (Fin p) S⟦X⟧ := Matrix.vandermonde v
  let M : Matrix (Fin p) (Fin p) S⟦X⟧ := (Coleman.leftMulMatrix p O F).map ψ
  have hmat : Matrix.diagonal
      (fun i : Fin p ↦ eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F)) * V =
        V * M := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    let e : S⟦X⟧ →+* S⟦X⟧ := eval₂Hom PowerSeries.WithPiTopology.continuous_C
      (Coleman.hasEval_C_pow_mul_one_add_X_sub_one hζ_nil (i : ℕ))
    have he_eq (g : O⟦X⟧) :
        eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ g) =
          e (PowerSeries.map ρ g) := by
      rw [coe_eval₂Hom]
    have heΦ (a : O⟦X⟧) : e (PowerSeries.map ρ (Coleman.frobeniusHom p O a)) = ψ a := by
      rw [coe_eval₂Hom, Coleman.map_frobeniusHom,
        Coleman.eval₂_frobeniusHom hζ.pow_eq_one hζ_nil (i : ℕ), ← Coleman.map_frobeniusHom]
      simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have he1X (n : ℕ) : e (PowerSeries.map ρ ((1 + X) ^ n)) = v i ^ n := by
      have heX : e X = C (ζ ^ (i : ℕ)) * (1 + X) - 1 := by
        rw [coe_eval₂Hom, eval₂_X]
      rw [map_pow, map_add, map_one, map_X, map_pow, map_add, map_one, heX, add_sub_cancel]
    have hcol := congrArg (e.comp (PowerSeries.map ρ))
      (Coleman.mul_one_add_X_pow_eq_sum_leftMulMatrix (p := p) F j)
    simp only [RingHom.comp_apply, map_mul, map_sum, he1X, heΦ] at hcol
    rw [he_eq]
    simpa only [V, M, Matrix.vandermonde_apply, Matrix.map_apply, mul_comm (v i ^ _)] using hcol
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hV : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    have h1X : (1 + X : S⟦X⟧) ≠ 0 := fun h ↦ by
      have h0 := congrArg constantCoeff h; simp at h0
    exact Fin.ext (hζ.injOn_pow (by simp) (by simp) (C_injective (mul_right_cancel₀ h1X hij)))
  have hprod :
      (∏ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F)) = M.det :=
    mul_right_cancel₀ hV (by rw [hdet, mul_comm])
  have hMdet : M.det = ψ (Matrix.det (Coleman.leftMulMatrix p O F)) :=
    (RingHom.map_det ψ (Coleman.leftMulMatrix p O F)).symm
  rw [hprod, hMdet, ← Coleman.norm_eq_det_leftMulMatrix]
  simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- **Uniqueness characterization of Coleman's norm via root-of-unity products** (Sharifi,
*Iwasawa Theory*, Lemma 5.4.14; Rodrigues Jacinto–Williams, Lemmas 10.8–10.11). When `ρ` is
injective, `G = N(F)` if and only if `map ρ (Φ(G))` equals the product of the `p` root-of-unity
translates `(map ρ F)(ζ ^ i * (1 + X) - 1)`. -/
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

/-- **Root-translation sum equals Frobenius of Coleman's trace** (Sharifi, *Iwasawa Theory*,
Lemma 5.4.14; Rodrigues Jacinto–Williams, Lemma 10.8). For a primitive `p`-th root of unity
`ζ ∈ 𝓞_ℂ_[p]`, `∑ i : Fin p, F(ζ ^ i * (1 + X) - 1) = Φ(τ(F))` after coefficient inclusion
`ℤ_[p] → 𝓞_ℂ_[p]`. -/
theorem sum_rootTranslation_eq_map_frobeniusHom_trace (hζ : IsPrimitiveRoot ζ p) (F : ℤ_[p]⟦X⟧) :
    ∑ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F =
      PowerSeries.map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] (Coleman.trace p ℤ_[p] F)) := by
  simp_rw [rootTranslation_eq_eval₂_map]
  exact hζ.sum_eval₂_map_eq_map_frobeniusHom_trace
    (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ.pow_eq_one)
    (integralCoefficientMap p) F

/-- **Root-translation product equals Frobenius of Coleman's norm** (Sharifi, *Iwasawa Theory*,
Lemma 5.4.14; Rodrigues Jacinto–Williams, Lemmas 10.8–10.11). For a primitive `p`-th root of unity
`ζ ∈ 𝓞_ℂ_[p]`, `∏ i : Fin p, F(ζ ^ i * (1 + X) - 1) = Φ(N(F))` after coefficient inclusion
`ℤ_[p] → 𝓞_ℂ_[p]`. -/
theorem prod_rootTranslation (hζ : IsPrimitiveRoot ζ p) (F : ℤ_[p]⟦X⟧) :
    ∏ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F =
      PowerSeries.map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] (Coleman.norm p ℤ_[p] F)) := by
  simp_rw [rootTranslation_eq_eval₂_map]
  exact hζ.prod_eval₂_map_eq_map_frobeniusHom_norm
    (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ.pow_eq_one)
    (integralCoefficientMap p) F

/-- **Uniqueness characterization of Coleman's norm on `ℤ_[p]⟦X⟧`** (Sharifi, *Iwasawa Theory*,
Lemma 5.4.14; Rodrigues Jacinto–Williams, Lemmas 10.8–10.11). For a primitive `p`-th root of unity
`ζ ∈ 𝓞_ℂ_[p]`, `G = N(F)` if and only if `Φ(G)` equals `∏ i : Fin p, F(ζ ^ i * (1 + X) - 1)`
after coefficient inclusion `ℤ_[p] → 𝓞_ℂ_[p]`. -/
theorem map_frobeniusHom_eq_prod_rootTranslation_iff (hζ : IsPrimitiveRoot ζ p)
    (F G : ℤ_[p]⟦X⟧) :
    PowerSeries.map (integralCoefficientMap p) (Coleman.frobeniusHom p ℤ_[p] G) =
        ∏ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F ↔
      G = Coleman.norm p ℤ_[p] F := by
  simp_rw [rootTranslation_eq_eval₂_map]
  exact hζ.map_frobeniusHom_eq_prod_eval₂_map_iff
    (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ.pow_eq_one)
    (PadicComplex.integralCoefficientMap_injective p) F G

end PadicInt

end IsPrimitiveRoot
