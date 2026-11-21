/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.KnotTheory.Hecke.Trace
public import TauCeti.KnotTheory.Jimbo.ReducedTrace
import Mathlib.Tactic.LinearCombination

/-!
# The weighted Jimbo traces are realizations of the Ocneanu trace

Let `q : Rˣ` and let `[N] = ∑ a, q ^ (N - 1 - 2 * a)` be the quantum dimension of the Jimbo
representation with `N` colours, the sum of Turaev's enhancement weights
`TauCeti.KnotTheory.jimboWeight`. Assume that `[N]` is invertible, with inverse `c`. This file
compares the weighted Jimbo trace `tr (ρ(x) * μ^{⊗n})` with the Ocneanu trace of the infinite
type-A Hecke algebra, where `ρ` is the Jimbo representation `TauCeti.TypeAHeckeAlgebra.jimbo`
and `μ^{⊗n}` is the enhancement `TauCeti.KnotTheory.jimboEnhancement`.

On the Hecke algebra on `n` strands, the weighted trace divided by `[N] ^ n` is the Ocneanu trace
with parameter `z = q ^ N / [N]`, along the embedding into the infinite algebra
(`TauCeti.TypeAHeckeAlgebra.trace_jimbo_mul_jimboEnhancement_eq_ocneanuTrace`). The proof
checks the four conditions of the uniqueness theorem
`TauCeti.TypeAHeckeAlgebra.eq_ocneanuTrace_toInfinite`: the enhancement commutes with the action
of every element (`TauCeti.TypeAHeckeAlgebra.commute_jimboEnhancement_jimbo`), so the weighted
trace is tracial; an uncrossed last strand multiplies it by `[N]`; and multiplying by the last
generator multiplies it by `q ^ N`. The last two are the braid-level identities
`TauCeti.KnotTheory.jimboWeightedTrace_strandIncl` and
`TauCeti.KnotTheory.jimboWeightedTrace_stabilize`, extended linearly from the images of braids,
which span the Hecke algebra.

For a braid `b` on `n` strands this reads `jimboWeightedTrace q b = [N] ^ n * tr_z(γ_n(b))`
(`TauCeti.KnotTheory.jimboWeightedTrace_eq_ocneanuTrace`). The two stabilization constants of
`tr_z` are `z = q ^ N / [N]` and `z - (q - q⁻¹) = q ^ (-N) / [N]`, so the normalization of
`TauCeti.MarkovBraid.heckeTrace` with unlink factor `C = [N]` and writhe factor `l = q ^ (-N)`
applies. With these choices the writhe-normalized Jimbo trace `TauCeti.MarkovBraid.jimboTrace`,
whose unknot value is `[N]`, is `[N]` times the normalized Hecke trace, whose unknot value is `1`
(`TauCeti.MarkovBraid.jimboTrace_eq_mul_heckeTrace`). On Markov classes, the writhe-normalized
Jimbo trace with `N` colours is therefore `[N]` times the braid-closure invariant
`TauCeti.heckeBraidInvariant` of the Ocneanu trace with parameter `q ^ N / [N]`
(`TauCeti.MarkovBraid.jimboTrace_eq_mul_heckeBraidInvariant`). Over a field, the reduced Jimbo
trace `TauCeti.MarkovBraid.jimboReducedTrace`, normalized to unknot value `1`, is the normalized
Hecke trace itself (`TauCeti.MarkovBraid.jimboReducedTrace_eq_heckeTrace`).

## Main results

* `TauCeti.TypeAHeckeAlgebra.trace_jimbo_mul_jimboEnhancement_eq_ocneanuTrace`: the normalized
  weighted Jimbo trace on the Hecke algebra on `n` strands is the Ocneanu trace.
* `TauCeti.KnotTheory.jimboWeightedTrace_eq_ocneanuTrace`: the same statement for braids.
* `TauCeti.KnotTheory.jimboWeight_sum_mul_inv_mul_eq_one` and
  `TauCeti.KnotTheory.jimboWeight_sum_mul_inv_inv_mul_sub_eq_one`: the normalization conditions
  for `C = [N]`, `l = q ^ (-N)` and `z = q ^ N / [N]`.
* `TauCeti.MarkovBraid.jimboTrace_eq_mul_heckeTrace` and
  `TauCeti.MarkovBraid.jimboTrace_eq_mul_heckeBraidInvariant`: the writhe-normalized Jimbo trace
  is the quantum dimension times the normalized Hecke trace of the Ocneanu trace.
* `TauCeti.MarkovBraid.jimboReducedTrace_eq_heckeTrace`: over a field, the Jimbo trace normalized
  to unknot value `1` is the normalized Hecke trace of the Ocneanu trace.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6 (the Ocneanu trace and its braid invariant).
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553 (weighted traces of enhanced Yang-Baxter operators).
-/

public section

namespace TauCeti

open KnotTheory

variable {R : Type*} [CommRing R] {q : Rˣ} {N n : ℕ}

namespace TypeAHeckeAlgebra

/-- The weighted Jimbo trace on the Hecke algebra on `n` strands, as a linear map. -/
private noncomputable def weightedTrace (N : ℕ) (q : Rˣ) (n : ℕ) :
    TypeAHeckeAlgebra R q n →ₗ[R] R :=
  LinearMap.trace R ((Fin n → Fin N) →₀ R) ∘ₗ LinearMap.mulRight R (jimboEnhancement q) ∘ₗ
    (jimbo (Fin N) q).toLinearMap

private theorem weightedTrace_apply (x : TypeAHeckeAlgebra R q n) :
    weightedTrace N q n x = LinearMap.trace R _ (jimbo (Fin N) q x * jimboEnhancement q) :=
  (rfl)

/-- On the image of a braid, the weighted trace is the weighted braid trace. -/
private theorem weightedTrace_braidHom (b : BraidGroup n) :
    weightedTrace N q n (braidHom R q n b) = jimboWeightedTrace (N := N) q b := by
  rw [weightedTrace_apply, jimbo_braidHom, jimboWeightedTrace_def]

private theorem weightedTrace_one :
    weightedTrace N q n 1 = (∑ a : Fin N, jimboWeight q a) ^ n := by
  simpa using weightedTrace_braidHom (N := N) (q := q) (1 : BraidGroup n)

private theorem weightedTrace_mul_comm (x y : TypeAHeckeAlgebra R q n) :
    weightedTrace N q n (x * y) = weightedTrace N q n (y * x) := by
  rw [weightedTrace_apply, weightedTrace_apply, map_mul (jimbo (Fin N) q) x y,
    map_mul (jimbo (Fin N) q) y x, mul_assoc,
    ← (commute_jimboEnhancement_jimbo y).eq, ← mul_assoc, LinearMap.trace_mul_comm, mul_assoc]

/-- An uncrossed last strand multiplies the weighted trace by the quantum dimension. -/
private theorem weightedTrace_strandIncl (x : TypeAHeckeAlgebra R q n) :
    weightedTrace N q (n + 1) (strandIncl R q n x) =
      weightedTrace N q n x * ∑ a : Fin N, jimboWeight q a := by
  have h : (weightedTrace N q (n + 1)).comp (strandIncl R q n).toLinearMap =
      (∑ a : Fin N, jimboWeight q a) • weightedTrace N q n := by
    refine LinearMap.ext_on_range (span_range_braidHom (R := R) (q := q) (n := n)) fun b ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply, smul_eq_mul]
    cases n with
    | zero =>
      rw [BraidGroup.eq_one_of_le_one zero_le_one b]
      simp [weightedTrace_one]
    | succ n =>
      rw [← braidHom_strandIncl, weightedTrace_braidHom, weightedTrace_braidHom,
        jimboWeightedTrace_strandIncl, mul_comm]
  simpa [mul_comm] using LinearMap.congr_fun h x

/-- Multiplying by the generator crossing the new last strand multiplies the weighted trace by
`q ^ N`. -/
private theorem weightedTrace_strandIncl_mul_T_last (x : TypeAHeckeAlgebra R q (n + 1)) :
    weightedTrace N q (n + 2) (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      ↑(q ^ N) * weightedTrace N q (n + 1) x := by
  have h : (weightedTrace N q (n + 2)).comp
        ((LinearMap.mulRight R (T q (Fin.last n))).comp (strandIncl R q (n + 1)).toLinearMap) =
      (↑(q ^ N) : R) • weightedTrace N q (n + 1) := by
    refine LinearMap.ext_on_range (span_range_braidHom (R := R) (q := q) (n := n + 1))
      fun b ↦ ?_
    have hb : strandIncl R q (n + 1) (braidHom R q (n + 1) b : TypeAHeckeAlgebra R q (n + 1)) *
        T q (Fin.last n) =
          (braidHom R q (n + 2) (BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)) :
            TypeAHeckeAlgebra R q (n + 2)) := by
      rw [map_mul, Units.val_mul, braidHom_strandIncl, braidHom_sigma, val_unitT]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hb, weightedTrace_braidHom, weightedTrace_braidHom, jimboWeightedTrace_stabilize]
  exact LinearMap.congr_fun h x

/-- **The weighted Jimbo trace is the Ocneanu trace.** If `c` is an inverse of the quantum
dimension `[N] = ∑ a, q ^ (N - 1 - 2 * a)`, then on the Hecke algebra on `n` strands the weighted
Jimbo trace `tr (ρ(x) * μ^{⊗n})`, multiplied by `c ^ n`, is the Ocneanu trace with parameter
`z = c * q ^ N`, along the embedding into the infinite type-A Hecke algebra. -/
theorem trace_jimbo_mul_jimboEnhancement_eq_ocneanuTrace {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (x : TypeAHeckeAlgebra R q n) :
    c ^ n * LinearMap.trace R _ (jimbo (Fin N) q x * jimboEnhancement q) =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  have key := eq_ocneanuTrace_toInfinite (q := q) (z := c * ↑(q ^ N))
    (fun m ↦ c ^ m • weightedTrace N q m)
    (by
      simp [weightedTrace_one])
    (fun m y ↦ by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, weightedTrace_strandIncl, smul_eq_mul,
        smul_eq_mul, pow_succ]
      linear_combination c ^ m * weightedTrace N q m y * hc)
    (fun m y y' ↦ by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, weightedTrace_mul_comm])
    (fun m y ↦ by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, weightedTrace_strandIncl_mul_T_last,
        smul_eq_mul, smul_eq_mul, pow_succ]
      ring)
    n x
  rwa [LinearMap.smul_apply, smul_eq_mul, weightedTrace_apply] at key

end TypeAHeckeAlgebra

namespace KnotTheory

/-- **The weighted Jimbo trace of a braid is the Ocneanu trace.** If `c` is an inverse of the
quantum dimension `[N] = ∑ a, q ^ (N - 1 - 2 * a)`, then the weighted trace of a braid `b` on
`n` strands in the Jimbo representation with `N` colours, multiplied by `c ^ n`, is the Ocneanu
trace with parameter `z = c * q ^ N` of the image of `b` in the infinite type-A Hecke
algebra. -/
theorem jimboWeightedTrace_eq_ocneanuTrace {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (b : BraidGroup n) :
    c ^ n * jimboWeightedTrace (N := N) q b =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N))
        (InfiniteTypeAHeckeAlgebra.braidHom R q n b) := by
  rw [← TypeAHeckeAlgebra.toInfinite_braidHom,
    ← TypeAHeckeAlgebra.trace_jimbo_mul_jimboEnhancement_eq_ocneanuTrace hc,
    TypeAHeckeAlgebra.jimbo_braidHom, jimboWeightedTrace_def]

/-- The positive normalization condition `C * l * z = 1` of the Hecke braid trace holds for the
unlink factor `C = [N]`, the writhe factor `l = q ^ (-N)` and the parameter `z = c * q ^ N` of the
Ocneanu trace realized by the weighted Jimbo trace. -/
theorem jimboWeight_sum_mul_inv_mul_eq_one {c : R} (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * (((q ^ N)⁻¹ : Rˣ) : R) * (c * ↑(q ^ N)) = 1 := by
  have hq : (((q ^ N)⁻¹ : Rˣ) : R) * ↑(q ^ N) = 1 := Units.inv_mul _
  linear_combination (((q ^ N)⁻¹ : Rˣ) : R) * ↑(q ^ N) * hc + hq

/-- The negative normalization condition `C * l⁻¹ * (z - (q - q⁻¹)) = 1` of the Hecke braid trace
holds for the unlink factor `C = [N]`, the writhe factor `l = q ^ (-N)` and the parameter
`z = c * q ^ N` of the Ocneanu trace realized by the weighted Jimbo trace. -/
theorem jimboWeight_sum_mul_inv_inv_mul_sub_eq_one {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * ((((q ^ N)⁻¹)⁻¹ : Rˣ) : R) *
      (c * ↑(q ^ N) - ((q : R) - ↑q⁻¹)) = 1 := by
  have hq : (↑(q ^ N) : R) * ↑(q⁻¹ ^ N) = 1 := by
    rw [← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
  rw [inv_inv]
  linear_combination (↑(q ^ N) : R) ^ 2 * hc - (↑(q ^ N) : R) * jimboWeight_sum (N := N) q + hq

end KnotTheory

namespace MarkovBraid

/-- **The Jimbo invariants are specializations of the Hecke braid invariant.** If `c` is an
inverse of the quantum dimension `[N] = ∑ a, q ^ (N - 1 - 2 * a)`, the writhe-normalized Jimbo
trace with `N` colours is `[N]` times the normalized Hecke trace of the Ocneanu trace with
parameter `z = c * q ^ N`, normalized by the unlink factor `C = [N]` and the writhe factor
`l = q ^ (-N)`. -/
theorem jimboTrace_eq_mul_heckeTrace {c : R} (hc : c * ∑ a : Fin N, jimboWeight q a = 1)
    (β : MarkovBraid) :
    jimboTrace (N := N) β q = (∑ a : Fin N, jimboWeight q a) *
      β.heckeTrace (InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ := by
  rw [jimboTrace_def, heckeTrace_def, ← jimboWeightedTrace_eq_ocneanuTrace hc, inv_zpow']
  have h : (c * ∑ a : Fin N, jimboWeight q a) ^ (β.predStrands + 1) = 1 := by rw [hc, one_pow]
  linear_combination
    -(↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid))) *
      jimboWeightedTrace (N := N) q β.braid) * h


/-- **The Jimbo invariants are specializations of the Hecke braid invariant**, on Markov classes:
if `c` is an inverse of the quantum dimension `[N]`, the writhe-normalized Jimbo trace with `N`
colours of a braid is `[N]` times the braid-closure invariant of the Ocneanu trace with parameter
`z = c * q ^ N`, normalized by `C = [N]` and `l = q ^ (-N)`, of its Markov class. -/
theorem jimboTrace_eq_mul_heckeBraidInvariant {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    jimboTrace (N := N) β q = (∑ a : Fin N, jimboWeight q a) *
      heckeBraidInvariant (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ (jimboWeight_sum_mul_inv_mul_eq_one hc)
        (jimboWeight_sum_mul_inv_inv_mul_sub_eq_one hc) (Quot.mk MarkovEquiv β) := by
  rw [heckeBraidInvariant_mk, jimboTrace_eq_mul_heckeTrace hc]

/-- **The reduced Jimbo trace is the normalized Hecke trace.** Over a field in which the quantum
dimension `[N]` is nonzero, the Jimbo trace with `N` colours normalized to unknot value `1` is the
normalized Hecke trace of the Ocneanu trace with parameter `z = q ^ N / [N]`, with unlink factor
`C = [N]` and writhe factor `l = q ^ (-N)`. -/
theorem jimboReducedTrace_eq_heckeTrace {K : Type*} [Field K] {q : Kˣ}
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) (β : MarkovBraid) :
    jimboReducedTrace (N := N) β q =
      β.heckeTrace
        (InfiniteTypeAHeckeAlgebra.ocneanuTrace K q ((∑ a : Fin N, jimboWeight q a)⁻¹ * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ := by
  rw [jimboReducedTrace_def, jimboTrace_eq_mul_heckeTrace (inv_mul_cancel₀ hδ),
    mul_div_cancel_left₀ _ hδ]

end MarkovBraid

end TauCeti
