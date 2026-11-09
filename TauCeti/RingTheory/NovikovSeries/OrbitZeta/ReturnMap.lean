/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.DetSign
public import TauCeti.RingTheory.NovikovSeries.OrbitZeta.Basic

/-!
# Orbit zeta functions of linearized return maps

Let `f i` be an endomorphism of a finite-dimensional real vector space `V i`, the linearized return
map of the `i`-th primitive orbit, and give the `k`-fold iterate the Lefschetz sign
`sgn det (1 - f i ^ k)`. If `1 - f i ^ k` is invertible for every `k ≥ 1`, these signs form a
geometric sequence with ratio `(-1) ^ i₋(f i)` (`LinearMap.sign_det_one_sub_pow_succ`), where
`i₊(f)`, `i₋(f)` and `i₀(f)` count the real eigenvalues of `f` in `(1, ∞)`, `(-∞, -1)` and
`(-1, 1)`, with algebraic multiplicity. The product formula
`TauCeti.NovikovSeries.orbitZeta_eq_eulerProduct` then reads

`ζ = ∏ᵢ (1 - (-1) ^ i₋(f i) e^(γ i)) ^ (-(-1) ^ (i₊(f i) + i₋(f i)))`,

and the exponent is `(-1) ^ (dim V i + i₀(f i) + 1)`.

## Main results

* `TauCeti.NovikovSeries.orbitZeta_sign_det_one_sub_pow_eq_eulerProduct`: the product formula
  when the signs are the Lefschetz signs of linearized return maps.
* `TauCeti.NovikovSeries.orbitZeta_sign_det_one_sub_pow_eq_eulerProduct_finrank`: the same
  formula with the exponent `(-1) ^ (dim V i + i₀(f i) + 1)`.
* `TauCeti.NovikovSeries.orbitZeta_sign_det_one_sub_pow_eq_mapRingHom_eulerProduct`: integrality
  of the orbit zeta function of linearized return maps.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

open Filter

namespace TauCeti.NovikovSeries

variable {ι H : Type*} [AddCommMonoid H] {N : H →+ ℝ} {γ : ι → H} {K : Type*} [CommRing K]
  [Algebra ℚ K] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, FiniteDimensional ℝ (V i)]

/-- **The product formula for linearized return maps.** Let `f i` be an endomorphism of a
finite-dimensional real vector space such that `1 - f i ^ k` is invertible for every `k ≥ 1`, and
let the `k`-fold iterate of the `i`-th orbit have the Lefschetz sign `sgn det (1 - f i ^ k)`. Then
the orbit zeta function is the Euler product
`∏ᵢ (1 - (-1) ^ i₋(f i) e^(γ i)) ^ (-(-1) ^ (i₊(f i) + i₋(f i)))`, where `i₊(f)` and `i₋(f)` count
the real roots of the characteristic polynomial of `f` in `(1, ∞)` and in `(-∞, -1)`, with
multiplicity. -/
theorem orbitZeta_sign_det_one_sub_pow_eq_eulerProduct (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (f : ∀ i, Module.End ℝ (V i))
    (hf : ∀ i (k : ℕ), (1 - f i ^ (k + 1)).det ≠ 0) :
    orbitZeta K N γ (fun i k => SignType.sign (1 - f i ^ k).det) =
      eulerProduct γ hpos (fun i => (-1) ^ ((f i).charpoly.roots.filter (· < -1)).card)
        (fun i => -(-1) ^ (((f i).charpoly.roots.filter (1 < ·)).card +
          ((f i).charpoly.roots.filter (· < -1)).card)) := by
  rw [orbitZeta_eq_eulerProduct hpos hfin _ (fun i => (-1) ^ ((f i).charpoly.roots.filter
    (· < -1)).card) fun i k => by
      rw [(f i).sign_det_one_sub_pow_succ k (hf i k), pow_one]
      simp]
  congr 1 <;> funext i
  · simp
  · rw [(f i).sign_det_one_sub_pow 1 (hf i 0)]
    simp [pow_mul, pow_add]

/-- **The product formula for linearized return maps, with dimension exponents.** Under the
hypotheses of `TauCeti.NovikovSeries.orbitZeta_sign_det_one_sub_pow_eq_eulerProduct`, the exponent
of the factor of the `i`-th orbit is `(-1) ^ (dim V i + i₀(f i) + 1)`, where `i₀(f)` counts the real
roots of the characteristic polynomial of `f` in `(-1, 1)`, with multiplicity. For the return maps
of a flow on a manifold `X`, acting on normal spaces of dimension `dim X - 1`, this exponent is
`(-1) ^ (dim X + i₀(f i))`. -/
theorem orbitZeta_sign_det_one_sub_pow_eq_eulerProduct_finrank (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (f : ∀ i, Module.End ℝ (V i))
    (hf : ∀ i (k : ℕ), (1 - f i ^ (k + 1)).det ≠ 0) :
    orbitZeta K N γ (fun i k => SignType.sign (1 - f i ^ k).det) =
      eulerProduct γ hpos (fun i => (-1) ^ ((f i).charpoly.roots.filter (· < -1)).card)
        (fun i => (-1) ^ (Module.finrank ℝ (V i) +
          ((f i).charpoly.roots.filter (|·| < 1)).card + 1)) := by
  rw [orbitZeta_sign_det_one_sub_pow_eq_eulerProduct hpos hfin f hf]
  congr 1
  funext i
  have h := congrArg (fun s : SignType => (s : ℤ))
    ((f i).neg_one_pow_card_filter_one_lt_add_card_filter_lt_neg_one (hf i 1))
  simp only [SignType.coe_pow, SignType.coe_neg_one] at h
  rw [h, pow_succ, mul_neg_one]

/-- **Integrality of the orbit zeta function for linearized return maps.** Under the hypotheses of
`TauCeti.NovikovSeries.orbitZeta_sign_det_one_sub_pow_eq_eulerProduct`, the orbit zeta function is
the image of the Euler product `∏ᵢ (1 - (-1) ^ i₋(f i) e^(γ i)) ^ (-(-1) ^ (i₊(f i) + i₋(f i)))`
with integer coefficients. -/
theorem orbitZeta_sign_det_one_sub_pow_eq_mapRingHom_eulerProduct (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (f : ∀ i, Module.End ℝ (V i))
    (hf : ∀ i (k : ℕ), (1 - f i ^ (k + 1)).det ≠ 0) :
    orbitZeta K N γ (fun i k => SignType.sign (1 - f i ^ k).det) =
      mapRingHom (Int.castRingHom K) (AddMonoidHom.id H) ⟨1, one_pos, by simp⟩
        (eulerProduct γ hpos (fun i => (-1) ^ ((f i).charpoly.roots.filter (· < -1)).card)
          (fun i => -(-1) ^ (((f i).charpoly.roots.filter (1 < ·)).card +
            ((f i).charpoly.roots.filter (· < -1)).card))) := by
  rw [orbitZeta_sign_det_one_sub_pow_eq_eulerProduct hpos hfin f hf,
    mapRingHom_eulerProduct _ _ _ hpos hfin]
  simp

end TauCeti.NovikovSeries
