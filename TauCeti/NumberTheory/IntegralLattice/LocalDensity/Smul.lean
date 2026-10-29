/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.LocalDensity.Basic
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.Smul

/-!
# The local density of a rescaled lattice

Rescaling the Gram matrix `A` of a `ℤ_p`-lattice of rank `n` by a nonzero `c ∈ ℤ_p` of valuation
`k` multiplies its local density by `p^{k n (n + 1) / 2}`:

```text
α_p(c • A) = p^{k n (n + 1) / 2} · α_p(A).
```

At the level of counts, `Xᵀ (c • A) X ≡ c • A (mod p^{r+k})` says exactly that
`Xᵀ A X ≡ A (mod pʳ)`, a condition on `X` modulo `pʳ` only, so each of the
`#{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X ≡ A}` solutions has `p^{k n²}` lifts to `ℤ/p^{r+k}`. Normalizing by
`p^{r n (n - 1) / 2}` turns `p^{k n²}` into `p^{k n (n + 1) / 2}`, since
`n² - n (n - 1) / 2 = n (n + 1) / 2`.

Together with the values at a prime `p ∤ 2 det A`, this evaluates the local density at an odd
prime of every lattice with a single Jordan constituent `p^k L₀`, `L₀` unimodular:

```text
n = 2m + 1:  α_p(c • A) = p^{k n (n + 1) / 2} · 2 ∏_{i=1}^{m} (1 - p^{-2i}),
n = 2m + 2:  α_p(c • A) = p^{k n (n + 1) / 2} · 2 (1 - ε p^{-(m+1)}) ∏_{i=1}^{m} (1 - p^{-2i}),
```

with `ε = ((-1)^{m+1} det A | p)` the type of the unimodular constituent. A lattice with several
Jordan constituents of different scales is not covered here.

## Main results

* `Matrix.localDensityCount_smul`: the count for `c • A` at level `r + v_p(c)` is
  `p ^ (v_p(c) * n ^ 2)` times the count for `A` at level `r`.
* `Matrix.localDensityCount_smul_div_pow`: the same for the normalized counts, with factor
  `p ^ (v_p(c) * (n + 1).choose 2)`.
* `Matrix.tendsto_localDensityCount_smul_div`: if the normalized counts of `A` converge to `α`,
  those of `c • A` converge to `p ^ (v_p(c) * (n + 1).choose 2) * α`.
* `Matrix.tendsto_localDensityCount_smul_div_of_card_eq_two_mul_add_one`,
  `Matrix.tendsto_localDensityCount_smul_div_of_card_eq_two_mul_add_two`: the local density at an
  odd prime of `c • A` for `A` with unit determinant, in odd and in even rank.

## References

* C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36
  (1935).
* J. H. Conway, N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*, Proc. Roy.
  Soc. London Ser. A 419 (1988), where the `p`-mass of a Jordan decomposition carries the
  corresponding scaling factors.
-/

public section

open Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]

/-- **The local density count of a rescaled Gram matrix.** For `c ≠ 0` of valuation `k`, the
number of `X ∈ Mₙ(ℤ/p^{r+k})` with `Xᵀ (c • A) X = c • A` is `p ^ (k * n ^ 2)` times the number
of `X ∈ Mₙ(ℤ/pʳ)` with `Xᵀ A X = A`. -/
theorem localDensityCount_smul {c : ℤ_[p]} (hc : c ≠ 0) (A : Matrix n n ℤ_[p]) (r : ℕ) :
    (c • A).localDensityCount (r + c.valuation) =
      p ^ (c.valuation * Fintype.card n ^ 2) * A.localDensityCount r := by
  have hpr : p ^ c.valuation * p ^ r = p ^ (r + c.valuation) := by rw [← pow_add, add_comm]
  have hpk : p ^ c.valuation ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hpr0 : p ^ r ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  set f := ZMod.castHom (Dvd.intro_left _ hpr) (ZMod (p ^ r))
  have hcomp : f.comp (PadicInt.toZModPow (r + c.valuation)) = PadicInt.toZModPow r :=
    PadicInt.zmod_cast_comp_toZModPow r _ (Nat.le_add_right r _)
  -- `c` is a unit times `p ^ k`, so its image modulo `p^{r+k}` has annihilator `ker f`
  have hcz (z : ZMod (p ^ (r + c.valuation))) :
      PadicInt.toZModPow (r + c.valuation) c * z = 0 ↔ f z = 0 := by
    have hc' : PadicInt.toZModPow (r + c.valuation) c = PadicInt.toZModPow (r + c.valuation)
        (PadicInt.unitCoeff hc) * ((p ^ c.valuation : ℕ) : ZMod (p ^ (r + c.valuation))) := by
      rw [← map_natCast (PadicInt.toZModPow _), ← map_mul, Nat.cast_pow,
        ← PadicInt.unitCoeff_spec hc]
    rw [hc', mul_assoc, ((PadicInt.unitCoeff hc).isUnit.map _).mul_right_eq_zero]
    exact ZMod.natCast_mul_eq_zero_iff _ hpr hpk z
  rw [localDensityCount_def, localDensityCount_def, Matrix.map_smul' _ _ _ (map_mul _),
    natCard_isometryMatrices_smul f (ZMod.ringHom_surjective f) hcz,
    ZMod.natCard_ker_castHom _ hpr hpr0, Matrix.map_map, ← RingHom.coe_comp, hcomp, ← pow_mul]

/-- **The normalized local density count of a rescaled Gram matrix.** For `c ≠ 0` of valuation
`k`, the normalized count `#{X : Xᵀ (c • A) X = c • A} / p ^ (r' * n.choose 2)` at level
`r' = r + k` is `p ^ (k * (n + 1).choose 2)` times the normalized count of `A` at level `r`. -/
theorem localDensityCount_smul_div_pow {c : ℤ_[p]} (hc : c ≠ 0) (A : Matrix n n ℤ_[p]) (r : ℕ) :
    ((c • A).localDensityCount (r + c.valuation) : ℚ) /
        (p : ℚ) ^ ((r + c.valuation) * (Fintype.card n).choose 2) =
      (p : ℚ) ^ (c.valuation * (Fintype.card n + 1).choose 2) *
        ((A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2)) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  -- `n ^ 2 = n.choose 2 + (n + 1).choose 2`
  have hsq : Fintype.card n ^ 2 = (Fintype.card n).choose 2 + (Fintype.card n + 1).choose 2 := by
    rw [Nat.choose_two_right (_ + 1), Nat.add_sub_cancel, mul_comm, sq,
      Nat.choose_two_add_mul_succ_div_two]
  rw [localDensityCount_smul hc, Nat.cast_mul, Nat.cast_pow, hsq,
    div_eq_iff (pow_ne_zero _ hp0)]
  field_simp
  ring

/-- **The local density of a rescaled Gram matrix.** If the normalized counts of `A` converge to
`α`, then for `c ≠ 0` of valuation `k` the normalized counts of `c • A` converge to
`p ^ (k * (n + 1).choose 2) * α`: rescaling by `c` multiplies the local density by
`p^{k n (n + 1) / 2}`. -/
theorem tendsto_localDensityCount_smul_div {c : ℤ_[p]} (hc : c ≠ 0) {A : Matrix n n ℤ_[p]}
    {α : ℚ} (h : Tendsto (fun r => (A.localDensityCount r : ℚ) /
      (p : ℚ) ^ (r * (Fintype.card n).choose 2)) atTop (𝓝 α)) :
    Tendsto (fun r => ((c • A).localDensityCount r : ℚ) /
        (p : ℚ) ^ (r * (Fintype.card n).choose 2)) atTop
      (𝓝 ((p : ℚ) ^ (c.valuation * (Fintype.card n + 1).choose 2) * α)) := by
  rw [← tendsto_add_atTop_iff_nat c.valuation]
  simpa only [localDensityCount_smul_div_pow hc] using h.const_mul _

/-- **The local density at an odd prime of a lattice with one Jordan constituent, in odd rank.**
If `p` is odd, `A` is a symmetric `(2m + 1) × (2m + 1)` matrix over `ℤ_p` with unit determinant,
and `c ≠ 0` has valuation `k`, the normalized counts of `c • A` converge to
`p ^ (k * (n + 1).choose 2) · 2 ∏_{i=1}^{m} (1 - p^{-2i})`. -/
theorem tendsto_localDensityCount_smul_div_of_card_eq_two_mul_add_one (hp : p ≠ 2)
    {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A) (hdet : IsUnit A.det) {m : ℕ}
    (hn : Fintype.card n = 2 * m + 1) {c : ℤ_[p]} (hc : c ≠ 0) :
    Tendsto (fun r => ((c • A).localDensityCount r : ℚ) /
        (p : ℚ) ^ (r * (Fintype.card n).choose 2)) atTop
      (𝓝 ((p : ℚ) ^ (c.valuation * (Fintype.card n + 1).choose 2) *
        (2 * ∏ i ∈ Finset.range m, (1 - ((p : ℚ) ^ (2 * (i + 1)))⁻¹)))) :=
  tendsto_localDensityCount_smul_div hc
    (tendsto_localDensityCount_div_of_card_eq_two_mul_add_one hp hA hdet hn)

/-- **The local density at an odd prime of a lattice with one Jordan constituent, in even
rank.** If `p` is odd, `A` is a symmetric `(2m + 2) × (2m + 2)` matrix over `ℤ_p` with unit
determinant, and `c ≠ 0` has valuation `k`, the normalized counts of `c • A` converge to
`p ^ (k * (n + 1).choose 2) · 2 (1 - ε p^{-(m+1)}) ∏_{i=1}^{m} (1 - p^{-2i})`, where
`ε = ((-1)^{m+1} det A | p)` is the type of the unimodular constituent `A`. -/
theorem tendsto_localDensityCount_smul_div_of_card_eq_two_mul_add_two (hp : p ≠ 2)
    {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A) (hdet : IsUnit A.det) {m : ℕ}
    (hn : Fintype.card n = 2 * m + 2) {c : ℤ_[p]} (hc : c ≠ 0) :
    Tendsto (fun r => ((c • A).localDensityCount r : ℚ) /
        (p : ℚ) ^ (r * (Fintype.card n).choose 2)) atTop
      (𝓝 ((p : ℚ) ^ (c.valuation * (Fintype.card n + 1).choose 2) *
        (2 * (1 - quadraticChar (ZMod p) ((-1) ^ (m + 1) * (A.map PadicInt.toZMod).det) *
          ((p : ℚ) ^ (m + 1))⁻¹) * ∏ i ∈ Finset.range m, (1 - ((p : ℚ) ^ (2 * (i + 1)))⁻¹)))) :=
  tendsto_localDensityCount_smul_div hc
    (tendsto_localDensityCount_div_of_card_eq_two_mul_add_two hp hA hdet hn)

end Matrix
