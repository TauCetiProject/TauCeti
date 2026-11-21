/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.LinearTopology
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.NumberTheory.Padics.Coleman.Norm

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import TauCeti.NumberTheory.Padics.Coleman.Topology
import TauCeti.RingTheory.PowerSeries.Evaluation
import TauCeti.RingTheory.PowerSeries.PiTopology

/-!
# Root-of-unity evaluation of Coleman's trace and norm

For a prime `p`, a `(p)`-adically complete commutative ring `O`, a ring homomorphism `ρ : O →+* S`
into a complete Hausdorff linearly topologized domain `S`, and a primitive `p`-th root of unity
`ζ ∈ S` with `ζ - 1` topologically nilpotent, this file proves:
1. Topological evaluation at `ζ ^ i * (1 + X) - 1` fixes the image of `frobeniusHom` (proved for
   any `p : ℕ` without primality).
2. The sum of `(map ρ F)(ζ ^ i * (1 + X) - 1)` over `i : Fin p` equals `map ρ (Φ(τ(F)))`
   (`IsPrimitiveRoot.sum_eval₂_map_eq_map_frobeniusHom_trace`).
3. The product of `(map ρ F)(ζ ^ i * (1 + X) - 1)` over `i : Fin p` equals `map ρ (Φ(N(F)))`
   (`IsPrimitiveRoot.prod_eval₂_map_eq_map_frobeniusHom_norm`), giving the norm characterization
   `map ρ (Φ(G)) = ∏ i, (map ρ F)(ζ ^ i * (1 + X) - 1) ↔ G = N(F)` whenever `ρ` is injective
   (`IsPrimitiveRoot.map_frobeniusHom_eq_prod_eval₂_map_iff`).

## Main results

* `TauCeti.Coleman.eval₂_frobeniusHom`: `eval₂ C (C (ζ ^ i) * (1 + X) - 1)` fixes `Φ(g)` over a
  complete Hausdorff linearly topologized ring `S`.
* `IsPrimitiveRoot.sum_eval₂_map_eq_map_frobeniusHom_trace`: trace identity at primitive `p`-th
  roots of unity.
* `IsPrimitiveRoot.prod_eval₂_map_eq_map_frobeniusHom_norm`: norm product formula at primitive
  `p`-th roots of unity.
* `IsPrimitiveRoot.map_frobeniusHom_eq_prod_eval₂_map_iff`: uniqueness characterization of
  Coleman's norm via root-of-unity products for injective `ρ`.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §IV (Thm. 11,
  Cor. 12(ii)).
* R. Sharifi, *Iwasawa Theory*, §5.4 (Lemma 5.4.14).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Ch. 10
  (Lemmas 10.8–10.11).
* C. Birkbeck et al., `CBirkbeck/padic-L-functions` (`Coleman/NormOperator.lean`, commit
  `45307015169791f1316f23a459c8e92ed5961c54`), adapted for the Vandermonde intertwining proof and
  generalized here to arbitrary `(p)`-adically complete coefficient rings `O`.
-/

public noncomputable section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti.Coleman

section RootEvalHelpers

private def rootEvalHom
    {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ_nil : IsTopologicallyNilpotent (ζ - 1)) (i : ℕ) : S⟦X⟧ →+* S⟦X⟧ :=
  eval₂Hom PowerSeries.WithPiTopology.continuous_C
    (PowerSeries.hasEval_C_pow_mul_one_add_X_sub_one hζ_nil i)

private theorem rootEvalHom_apply
    {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ_nil : IsTopologicallyNilpotent (ζ - 1)) (i : ℕ) (f : S⟦X⟧) :
    rootEvalHom hζ_nil i f = eval₂ C (C (ζ ^ i) * (1 + X) - 1) f :=
  congrFun (coe_eval₂Hom PowerSeries.WithPiTopology.continuous_C
    (PowerSeries.hasEval_C_pow_mul_one_add_X_sub_one hζ_nil i)) f

private theorem rootEvalHom_C
    {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ_nil : IsTopologicallyNilpotent (ζ - 1)) (i : ℕ) (a : S) :
    rootEvalHom hζ_nil i (C a) = C a := by
  rw [rootEvalHom_apply, eval₂_C]

private theorem rootEvalHom_one_add_X
    {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ_nil : IsTopologicallyNilpotent (ζ - 1)) (i : ℕ) :
    rootEvalHom hζ_nil i (1 + X) = C (ζ ^ i) * (1 + X) := by
  rw [map_add, map_one, rootEvalHom_apply, eval₂_X, add_sub_cancel]

end RootEvalHelpers

/-- For a complete Hausdorff linearly topologized commutative ring `S`, `ζ ∈ S` with `ζ ^ p = 1`,
and `ζ - 1` topologically nilpotent, topological evaluation at `ζ ^ i * (1 + X) - 1` fixes the
image of `frobeniusHom p S`. -/
theorem eval₂_frobeniusHom
    {p : ℕ} {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζp : ζ ^ p = 1) (hζ_nil : IsTopologicallyNilpotent (ζ - 1)) (i : ℕ) (g : S⟦X⟧) :
    eval₂ C (C (ζ ^ i) * (1 + X) - 1) (frobeniusHom p S g) = frobeniusHom p S g := by
  rw [← rootEvalHom_apply hζ_nil i]
  have hcont : Continuous (rootEvalHom hζ_nil i) := by
    simp_rw [funext (rootEvalHom_apply hζ_nil i)]
    exact continuous_eval₂ PowerSeries.WithPiTopology.continuous_C
      (PowerSeries.hasEval_C_pow_mul_one_add_X_sub_one hζ_nil i)
  refine congrFun ((PowerSeries.WithPiTopology.denseRange_toPowerSeries S).equalizer
    (hcont.comp (continuous_frobeniusHom (p := p))) (continuous_frobeniusHom (p := p)) ?_) g
  funext P; simp only [Function.comp_apply]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.coe_add, map_add, hP, hQ]
  | monomial n a =>
    have hX : rootEvalHom hζ_nil i (frobeniusHom p S X) = frobeniusHom p S X := by
      rw [frobeniusHom_X, map_sub, map_one, map_pow, rootEvalHom_one_add_X, mul_pow,
        ← map_pow, ← pow_mul, mul_comm i p, pow_mul, hζp, one_pow, map_one, one_mul]
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      map_mul, map_pow, frobeniusHom_C, rootEvalHom_C, hX]

end TauCeti.Coleman

namespace IsPrimitiveRoot

open TauCeti TauCeti.Coleman

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
private theorem eval₂_root_map_frobeniusHom_mul_pow
    {O S : Type*} [CommRing O] [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζp : ζ ^ p = 1) (hζ_nil : IsTopologicallyNilpotent (ζ - 1))
    (ρ : O →+* S) (i n : ℕ) (a : O⟦X⟧) :
    eval₂ C (C (ζ ^ i) * (1 + X) - 1)
        (PowerSeries.map ρ (frobeniusHom p O a * (1 + X) ^ n)) =
      PowerSeries.map ρ (frobeniusHom p O a) * (C (ζ ^ i) * (1 + X)) ^ n := by
  rw [← rootEvalHom_apply hζ_nil i, map_mul, map_mul, map_pow, map_add, map_one, map_X,
    map_pow, rootEvalHom_one_add_X, rootEvalHom_apply, map_frobeniusHom,
    eval₂_frobeniusHom hζp hζ_nil i]

/-- **Root-of-unity sum equals Frobenius of Coleman's trace** (Sharifi, Lemma 5.4.14; RJW,
Lemma 10.8): for prime `p`, `(p)`-adically complete `O`, a homomorphism `ρ : O →+* S` into a
complete Hausdorff linearly topologized domain `S`, and primitive `p`-th root `ζ ∈ S` with
`ζ - 1` topologically nilpotent,
`∑ i : Fin p, (map ρ F)(ζ ^ i * (1 + X) - 1) = map ρ (Φ(τ(F)))`. -/
theorem sum_eval₂_map_eq_map_frobeniusHom_trace
    {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    {S : Type*} [CommRing S] [IsDomain S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hζ_nil : IsTopologicallyNilpotent (ζ - 1))
    (ρ : O →+* S) (F : O⟦X⟧) :
    ∑ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
      PowerSeries.map ρ (frobeniusHom p O (trace p O F)) := by
  have hterm (i : Fin p) :
      eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
        ∑ j : Fin p, PowerSeries.map ρ (frobeniusHom p O (coord p O j F)) *
          (1 + X) ^ (j : ℕ) * C ((ζ ^ (j : ℕ)) ^ (i : ℕ)) := by
    conv_lhs => rw [← sum_frobeniusHom_coord (p := p) F]
    rw [← rootEvalHom_apply hζ_nil (i : ℕ), map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [rootEvalHom_apply, eval₂_root_map_frobeniusHom_mul_pow hζ.pow_eq_one hζ_nil, mul_pow,
      ← map_pow, ← pow_mul, mul_comm (i : ℕ) (j : ℕ), pow_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm, Finset.sum_eq_single ⟨0, (Fact.out : p.Prime).pos⟩ ?_ (by simp)]
  · simp [trace_eq_p_mul_coord_zero, mul_comm]
  · intro j _ hj
    rw [← Finset.mul_sum, ← map_sum]
    have hsum : ∑ i : Fin p, (ζ ^ (j : ℕ)) ^ (i : ℕ) = 0 :=
      mul_right_cancel₀ (sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt
          (fun h ↦ hj (Fin.ext h)) j.isLt)) <| by
        rw [Fin.sum_univ_eq_sum_range, geom_sum_mul, ← pow_mul, mul_comm, pow_mul,
          hζ.pow_eq_one, one_pow, sub_self, zero_mul]
    rw [hsum, map_zero, mul_zero]

/-- **Root-of-unity product equals Frobenius of Coleman's norm** (Sharifi, Lemma 5.4.14; RJW,
Lemmas 10.8–10.11): for prime `p`, `(p)`-adically complete `O`, a homomorphism `ρ : O →+* S` into a
complete Hausdorff linearly topologized domain `S`, and primitive `p`-th root `ζ ∈ S` with
`ζ - 1` topologically nilpotent,
`∏ i : Fin p, (map ρ F)(ζ ^ i * (1 + X) - 1) = map ρ (Φ(N(F)))`. -/
theorem prod_eval₂_map_eq_map_frobeniusHom_norm
    {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    {S : Type*} [CommRing S] [IsDomain S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hζ_nil : IsTopologicallyNilpotent (ζ - 1))
    (ρ : O →+* S) (F : O⟦X⟧) :
    ∏ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
      PowerSeries.map ρ (frobeniusHom p O (norm p O F)) := by
  let ψ : O⟦X⟧ →+* S⟦X⟧ := (PowerSeries.map ρ).comp (frobeniusHom p O).toRingHom
  let V : Matrix (Fin p) (Fin p) S⟦X⟧ := Matrix.vandermonde fun i ↦ C (ζ ^ (i : ℕ)) * (1 + X)
  have hmat : Matrix.diagonal
      (fun i : Fin p ↦ eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F)) * V =
        V * ψ.mapMatrix (leftMulMatrix p O F) := by
    refine Matrix.ext fun i j ↦ ?_
    have hcol := congrArg (fun g ↦ rootEvalHom hζ_nil (i : ℕ) (PowerSeries.map ρ g))
      (mul_one_add_X_pow_eq_sum_leftMulMatrix (p := p) F j)
    have h1X (k : Fin p) : rootEvalHom hζ_nil (i : ℕ) (PowerSeries.map ρ ((1 + X) ^ (k : ℕ))) =
        (C (ζ ^ (i : ℕ)) * (1 + X)) ^ (k : ℕ) := by
      rw [map_pow, map_pow, map_add, map_one, map_X, rootEvalHom_one_add_X]
    simp only [map_mul, map_sum, h1X] at hcol
    rw [Matrix.diagonal_mul, Matrix.mul_apply]; dsimp only [V]
    rw [Matrix.vandermonde_apply, ← rootEvalHom_apply hζ_nil (i : ℕ), hcol]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.vandermonde_apply, rootEvalHom_apply, map_frobeniusHom,
      eval₂_frobeniusHom hζ.pow_eq_one hζ_nil, ← map_frobeniusHom, mul_comm]
    simp [ψ]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hV : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr fun i j hij ↦
    Fin.ext (hζ.injOn_pow (by simp) (by simp)
      (C_injective (mul_right_cancel₀ (fun h ↦ by simpa using congrArg constantCoeff h) hij)))
  have hprod : ∏ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) =
      (ψ.mapMatrix (leftMulMatrix p O F)).det := mul_right_cancel₀ hV (by rw [hdet, mul_comm])
  rw [hprod, ← RingHom.map_det ψ, ← norm_eq_det_leftMulMatrix]
  simp [ψ]

/-- **Uniqueness of Coleman's norm via root-of-unity products** (Sharifi, Lemma 5.4.14; RJW,
Lemmas 10.8–10.11): for prime `p`, `(p)`-adically complete `O`, an injective homomorphism
`ρ : O →+* S` into a complete Hausdorff linearly topologized domain `S`, and primitive `p`-th root
`ζ ∈ S` with `ζ - 1` topologically nilpotent,
`map ρ (Φ(G)) = ∏ i, (map ρ F)(ζ ^ i * (1 + X) - 1)` iff `G = N(F)`. -/
theorem map_frobeniusHom_eq_prod_eval₂_map_iff
    {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    {S : Type*} [CommRing S] [IsDomain S] [UniformSpace S] [IsUniformAddGroup S] [T2Space S]
    [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hζ_nil : IsTopologicallyNilpotent (ζ - 1))
    {ρ : O →+* S} (hρ : Function.Injective ρ) (F G : O⟦X⟧) :
    PowerSeries.map ρ (frobeniusHom p O G) =
        ∏ i : Fin p, eval₂ C (C (ζ ^ (i : ℕ)) * (1 + X) - 1) (PowerSeries.map ρ F) ↔
      G = norm p O F := by
  rw [hζ.prod_eval₂_map_eq_map_frobeniusHom_norm hζ_nil ρ F,
    (PowerSeries.map_injective ρ hρ).eq_iff, (frobeniusHom_injective (p := p)).eq_iff]

end IsPrimitiveRoot
