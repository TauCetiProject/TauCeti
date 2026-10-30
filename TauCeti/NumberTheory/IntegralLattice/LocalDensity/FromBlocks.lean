/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import TauCeti.NumberTheory.IntegralLattice.LocalDensity.Basic
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.FromBlocks
import TauCeti.NumberTheory.IntegralLattice.LocalDensity.Smul
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Splitting off the unimodular Jordan constituent of a local density

Let `p` be an odd prime and let `L = L₀ ⊥ L'` be an orthogonal splitting of a `ℤ_p`-lattice in which
`L₀` is unimodular and the Gram matrix of `L'` is divisible by `p`, as in the Jordan splitting
`L = ⊥ⱼ pʲ Lⱼ` with `L' = ⊥_{j ≥ 1} pʲ Lⱼ`. Then the local density is multiplicative:

```text
α_p(L₀ ⊥ L') = α_p(L₀) · α_p(L').
```

At the level of counts, `#{X mod pʳ : Xᵀ (A ⊕ B) X = A ⊕ B}` is
`p^{r n₀ n'} · #{X mod pʳ : Xᵀ A X = A} · #{X mod pʳ : Xᵀ B X = B}` at every level `r`, for
`n₀` and `n'` the ranks of `L₀` and `L'`. This is
`Matrix.natCard_isometryMatrices_fromBlocks_of_isNilpotent` over `ℤ/pʳ`, where the multiples of `p`
form a nilpotent ideal. The factor `p^{r n₀ n'}` is the
cross term of `n (n - 1) / 2 = n₀ (n₀ - 1) / 2 + n' (n' - 1) / 2 + n₀ n'`, so it disappears after
normalization.

Writing `L' = p L''` and combining with the scaling of local densities gives the recursion

```text
α_p(L₀ ⊥ p^k L'') = α_p(L₀) · p^{k n'' (n'' + 1) / 2} · α_p(L''),
```

for `k ≥ 1` and `n''` the rank of `L''`. Together with the values of `α_p` on unimodular
lattices it evaluates the local density at an odd prime from a Jordan splitting.

## Main results

* `Matrix.localDensityCount_fromBlocks`: the count for `fromBlocks A 0 0 B` with `A` unimodular
  and `B` divisible by `p` is `p ^ (r * (n₀ * n'))` times the product of the counts.
* `Matrix.localDensityCount_fromBlocks_div_pow`: the normalized counts multiply.
* `Matrix.tendsto_localDensityCount_fromBlocks_div`, `Matrix.localDensity_fromBlocks`: the local
  density of `fromBlocks A 0 0 B` is `α_p(A) · α_p(B)`.
* `Matrix.localDensity_fromBlocks_smul`: the recursion for `fromBlocks A 0 0 (c • B)` with `p ∣ c`.

## References

* Y. Kitaoka, *Arithmetic of Quadratic Forms*, Cambridge Tracts in Mathematics 106 (1993),
  Chapter 5, for the reduction of local densities along a Jordan splitting.
* J. H. Conway, N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*, Proc. Roy.
  Soc. London Ser. A 419 (1988), where the `p`-mass at odd `p` is assembled from the Jordan
  constituents.
-/

public section

open Filter Topology

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {p : ℕ}
  [Fact p.Prime]

/-- **The local density count of an orthogonal sum with a unimodular summand.** For `p` odd, `A`
symmetric with unit determinant and `B` symmetric with entries divisible by `p`, the number of
`X ∈ M(ℤ/pʳ)` with `Xᵀ (A ⊕ B) X = A ⊕ B` is `p ^ (r * (n₀ * n'))` times the product of the counts
for `A` and for `B`, where `n₀` and `n'` are the sizes of `A` and `B`. -/
theorem localDensityCount_fromBlocks (hp : p ≠ 2) {A : Matrix ι ι ℤ_[p]} {B : Matrix κ κ ℤ_[p]}
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (hB : Bᵀ = B) (hBp : ∀ i j, (p : ℤ_[p]) ∣ B i j)
    (r : ℕ) :
    (fromBlocks A 0 0 B).localDensityCount r =
      p ^ (r * (Fintype.card ι * Fintype.card κ)) * A.localDensityCount r *
        B.localDensityCount r := by
  set f := PadicInt.toZModPow (p := p) r
  -- the multiples of `p` form a nilpotent ideal of `ℤ/pʳ`, containing the entries of `B mod pʳ`
  set I : Ideal (ZMod (p ^ r)) := Ideal.span {(p : ZMod (p ^ r))}
  have hI : IsNilpotent I := ⟨r, by
    rw [Ideal.span_singleton_pow, ← Nat.cast_pow, ZMod.natCast_self, Set.singleton_zero,
      Ideal.span_zero, Submodule.zero_eq_bot]⟩
  have hBI (i j : κ) : B.map f i j ∈ I := by
    obtain ⟨c, hc⟩ := hBp i j
    rw [map_apply, hc, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h2 : IsUnit (2 : ZMod (p ^ r)) := by
    simpa only [map_ofNat] using (PadicInt.isUnit_two hp).map f
  have hdet' : IsUnit (A.map f).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  rw [localDensityCount_def, localDensityCount_def, localDensityCount_def, fromBlocks_map,
    Matrix.map_zero _ (map_zero f), Matrix.map_zero _ (map_zero f),
    natCard_isometryMatrices_fromBlocks_of_isNilpotent h2 hI (by rw [← transpose_map, hA]) hdet'
      (by rw [← transpose_map, hB]) hBI, Nat.card_zmod, ← pow_mul]

/-- **The normalized local density count of an orthogonal sum with a unimodular summand.** For
`p` odd, `A` symmetric with unit determinant and `B` symmetric with entries divisible by `p`, the
normalized count `#{X : Xᵀ (A ⊕ B) X = A ⊕ B} / p ^ (r * n.choose 2)` is the product of the
normalized counts for `A` and for `B`. -/
theorem localDensityCount_fromBlocks_div_pow (hp : p ≠ 2) {A : Matrix ι ι ℤ_[p]}
    {B : Matrix κ κ ℤ_[p]} (hA : Aᵀ = A) (hdet : IsUnit A.det) (hB : Bᵀ = B)
    (hBp : ∀ i j, (p : ℤ_[p]) ∣ B i j) (r : ℕ) :
    ((fromBlocks A 0 0 B).localDensityCount r : ℚ) /
        (p : ℚ) ^ (r * (Fintype.card (ι ⊕ κ)).choose 2) =
      (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card ι).choose 2) *
        ((B.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card κ).choose 2)) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [localDensityCount_fromBlocks hp hA hdet hB hBp, Fintype.card_sum, Nat.add_choose_two]
  push_cast
  field_simp
  ring

/-- **The local density of an orthogonal sum with a unimodular summand.** For `p` odd, `A`
symmetric with unit determinant and `B` symmetric with entries divisible by `p`, if the
normalized counts of `B` converge to `β`, then those of `fromBlocks A 0 0 B` converge to
`α_p(A) · β`. -/
theorem tendsto_localDensityCount_fromBlocks_div (hp : p ≠ 2) {A : Matrix ι ι ℤ_[p]}
    {B : Matrix κ κ ℤ_[p]} (hA : Aᵀ = A) (hdet : IsUnit A.det) (hB : Bᵀ = B)
    (hBp : ∀ i j, (p : ℤ_[p]) ∣ B i j) {β : ℚ}
    (h : Tendsto (fun r => (B.localDensityCount r : ℚ) /
      (p : ℚ) ^ (r * (Fintype.card κ).choose 2)) atTop (𝓝 β)) :
    Tendsto (fun r => ((fromBlocks A 0 0 B).localDensityCount r : ℚ) /
      (p : ℚ) ^ (r * (Fintype.card (ι ⊕ κ)).choose 2)) atTop (𝓝 (A.localDensity * β)) := by
  simpa only [localDensityCount_fromBlocks_div_pow hp hA hdet hB hBp] using
    (tendsto_localDensityCount_div_of_det_ne_zero hA hdet.ne_zero).mul h

/-- **The local density is multiplicative across a unimodular Jordan constituent.** For `p` odd,
`A` symmetric with unit determinant and `B` symmetric and nondegenerate with entries divisible by
`p`, `α_p(A ⊕ B) = α_p(A) · α_p(B)`. -/
theorem localDensity_fromBlocks (hp : p ≠ 2) {A : Matrix ι ι ℤ_[p]} {B : Matrix κ κ ℤ_[p]}
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (hB : Bᵀ = B) (hBdet : B.det ≠ 0)
    (hBp : ∀ i j, (p : ℤ_[p]) ∣ B i j) :
    (fromBlocks A 0 0 B).localDensity = A.localDensity * B.localDensity :=
  tendsto_nhds_unique
    (tendsto_localDensityCount_div_of_det_ne_zero
      (by rw [fromBlocks_transpose, hA, hB, transpose_zero, transpose_zero])
      (by rw [det_fromBlocks_zero₂₁]; exact mul_ne_zero hdet.ne_zero hBdet))
    (tendsto_localDensityCount_fromBlocks_div hp hA hdet hB hBp
      (tendsto_localDensityCount_div_of_det_ne_zero hB hBdet))

/-- **The recursion along a Jordan splitting at an odd prime.** For `p` odd, `A` symmetric with
unit determinant, `B` symmetric and nondegenerate of size `n''`, and `c ≠ 0` divisible by `p` of
valuation `k`, `α_p(A ⊕ c B) = p ^ (k * (n'' + 1).choose 2) · α_p(A) · α_p(B)`. -/
theorem localDensity_fromBlocks_smul (hp : p ≠ 2) {A : Matrix ι ι ℤ_[p]} {B : Matrix κ κ ℤ_[p]}
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (hB : Bᵀ = B) (hBdet : B.det ≠ 0) {c : ℤ_[p]}
    (hc : c ≠ 0) (hcp : (p : ℤ_[p]) ∣ c) :
    (fromBlocks A 0 0 (c • B)).localDensity =
      (p : ℚ) ^ (c.valuation * (Fintype.card κ + 1).choose 2) * A.localDensity *
        B.localDensity := by
  have hcB : (c • B)ᵀ = c • B := by rw [transpose_smul, hB]
  have hcBdet : (c • B).det ≠ 0 := by
    rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) hBdet
  have hsmul : (c • B).localDensity =
      (p : ℚ) ^ (c.valuation * (Fintype.card κ + 1).choose 2) * B.localDensity :=
    tendsto_nhds_unique (tendsto_localDensityCount_div_of_det_ne_zero hcB hcBdet)
      (tendsto_localDensityCount_smul_div hc
        (tendsto_localDensityCount_div_of_det_ne_zero hB hBdet))
  rw [localDensity_fromBlocks hp hA hdet hcB hcBdet fun i j => by
      rw [smul_apply, smul_eq_mul]
      exact dvd_mul_of_dvd_left hcp _,
    hsmul]
  ring

end Matrix
