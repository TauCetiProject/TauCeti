/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.NumberTheory.IntegralLattice.LocalDensity.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.LocalDensity.FromBlocks

/-!
# The local density at an odd prime from a diagonal Jordan form

At an odd prime `p` every nondegenerate `ℤ_p`-lattice has an orthogonal basis in which its Gram
matrix is diagonal with entries `uᵢ pᵏⁱ`, `uᵢ` a unit of `ℤ_p`
(`TauCeti.IntegralLattice.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow`). Grouping the
basis vectors by their exponent gives the Jordan splitting `L = ⊥ⱼ pʲ Lⱼ`, where `Lⱼ` is the
unimodular lattice with diagonal Gram matrix `(uᵢ)_{kᵢ = j}`, of rank `nⱼ = #{i | kᵢ = j}`. This
file evaluates the local density `α_p(L)` from these Jordan data:

```text
α_p(diag(uᵢ pᵏⁱ)) = p^{∑_{j ≥ 1} (Nⱼ + 1) Nⱼ / 2} · ∏ⱼ α_p(Lⱼ),      Nⱼ = #{i | j ≤ kᵢ}.
```

Since `Nⱼ = ∑_{j' ≥ j} n_{j'}`, the exponent equals `∑ⱼ j nⱼ (nⱼ + 1) / 2 + ∑_{j < j'} j nⱼ n_{j'}`.
Each `α_p(Lⱼ)` is the density of a unimodular lattice, given in closed form by its rank and the
quadratic character of its signed determinant
(`Matrix.tendsto_localDensityCount_div_of_card_eq_two_mul_add_one`,
`Matrix.tendsto_localDensityCount_div_of_card_eq_two_mul_add_two`), so together these compute the
local density at an odd prime of every nondegenerate lattice.

The proof peels off the unimodular constituent `L₀` and divides the rest by `p`, using the
recursion `α_p(L₀ ⊥ p L') = p^{(n' + 1) n' / 2} · α_p(L₀) · α_p(L')`
(`Matrix.localDensity_fromBlocks_smul`), and inducts on the largest exponent.

## Main results

* `Matrix.localDensity_diagonal_unit_mul_pow`: the local density at an odd prime of a diagonal
  Gram matrix with entries `uᵢ pᵏⁱ`, in terms of the densities of its unimodular Jordan
  constituents.
* `LinearMap.BilinForm.localDensity_toMatrix_of_iIsOrtho`: the same value for the Gram matrix, in
  any basis, of a bilinear form over `ℤ_p` with an orthogonal basis of diagonal entries `uᵢ pᵏⁱ`,
  as produced at an odd prime by
  `TauCeti.IntegralLattice.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow`.

## References

* Y. Kitaoka, *Arithmetic of Quadratic Forms*, Cambridge Tracts in Mathematics 106 (1993),
  Chapter 5, for the reduction of local densities along a Jordan splitting.
* J. H. Conway, N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*, Proc. Roy.
  Soc. London Ser. A 419 (1988), where the `p`-mass at odd `p` is assembled from the Jordan
  constituents.
-/

public section

open Finset

namespace Matrix

variable {p : ℕ} [Fact p.Prime]

/-- Splitting a diagonal Jordan form `diag(uᵢ pᵏⁱ)` into its unimodular constituent
`{i | kᵢ = 0}` and `p` times the diagonal Jordan form `diag(uᵢ pᵏⁱ⁻¹)` on `{i | kᵢ ≠ 0}`. -/
private theorem diagonal_unit_mul_pow_eq_reindex_fromBlocks {κ : Type*} [DecidableEq κ]
    (u : κ → ℤ_[p]ˣ) (k : κ → ℕ) :
    (diagonal fun i => (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) =
      reindex (Equiv.sumCompl fun i => k i = 0) (Equiv.sumCompl fun i => k i = 0)
        (fromBlocks (diagonal fun i : {i // k i = 0} => (u i : ℤ_[p])) 0 0
          ((p : ℤ_[p]) • diagonal fun i : {i // ¬k i = 0} =>
            (u i : ℤ_[p]) * (p : ℤ_[p]) ^ (k i - 1))) := by
  rw [← diagonal_smul, fromBlocks_diagonal, reindex_apply, submatrix_diagonal_equiv]
  congr 1
  funext i
  by_cases hi : k i = 0
  · rw [Function.comp_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun i => k i = 0) hi,
      Sum.elim_inl, hi, pow_zero, mul_one]
  · rw [Function.comp_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun i => k i = 0) hi,
      Sum.elim_inr, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← pow_succ',
      Nat.sub_add_cancel (Nat.pos_of_ne_zero hi)]

/-- **The local density of a diagonal Jordan form, with a bound on the exponents.** This is
`Matrix.localDensity_diagonal_unit_mul_pow` with the product taken over all scales `j ≤ K`,
including scales with no diagonal entry, for any `K` bounding the exponents. -/
private theorem localDensity_diagonal_unit_mul_pow_of_le (hp : p ≠ 2) (K : ℕ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (u : ι → ℤ_[p]ˣ) (k : ι → ℕ) (hk : ∀ i, k i ≤ K) :
    (diagonal fun i => (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i).localDensity =
      (p : ℚ) ^ (∑ j ∈ range K, (#{i | j < k i} + 1).choose 2) *
        ∏ j ∈ range (K + 1), (diagonal fun i : {i // k i = j} => (u i : ℤ_[p])).localDensity := by
  induction K generalizing ι with
  | zero =>
    have hk0 (i : ι) : k i = 0 := Nat.le_zero.mp (hk i)
    rw [range_zero, sum_empty, pow_zero, one_mul, prod_range_one]
    exact (localDensity_diagonal_congr (Equiv.subtypeUnivEquiv hk0) fun i => by
      simp [hk0 i.1]).symm
  | succ K ih =>
    -- split off the unimodular constituent `{i | k i = 0}` and write the rest as `p • B`
    set S := {i // ¬k i = 0}
    have hAdet : IsUnit (diagonal fun i : {i // k i = 0} => (u i : ℤ_[p])).det := by
      rw [det_diagonal, ← Units.coe_prod]
      exact Units.isUnit _
    have hBdet : (diagonal fun i : S => (u i : ℤ_[p]) * (p : ℤ_[p]) ^ (k i - 1)).det ≠ 0 := by
      rw [det_diagonal]
      exact prod_ne_zero_iff.mpr fun i _ =>
        mul_ne_zero (u i).ne_zero (pow_ne_zero _ (NeZero.ne _))
    rw [diagonal_unit_mul_pow_eq_reindex_fromBlocks, localDensity_reindex,
      localDensity_fromBlocks_smul hp (diagonal_transpose _) hAdet (diagonal_transpose _) hBdet
        (NeZero.ne _) dvd_rfl,
      ih (fun i : S => u i) (fun i => k i - 1) fun i => by have := hk i; omega,
      PadicInt.valuation_p, one_mul, sum_range_succ', prod_range_succ' _ (K + 1), pow_add]
    -- match the rank of the `p`-divisible part, the ranks above each scale, and the constituents
    have hcard : Fintype.card S = #{i | 0 < k i} := by
      simp only [S, Fintype.card_subtype, Nat.pos_iff_ne_zero]
    have hrank (j : ℕ) : #{i : S | j < k i - 1} = #{i | j + 1 < k i} := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr <|
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun i => ¬k i = 0) fun i => j < k i - 1).trans <|
          Equiv.subtypeEquivRight fun i => by omega
    have hblock (j : ℕ) :
        (diagonal fun i : {i : S // k i - 1 = j} => (u i : ℤ_[p])).localDensity =
          (diagonal fun i : {i // k i = j + 1} => (u i : ℤ_[p])).localDensity :=
      localDensity_diagonal_congr
        ((Equiv.subtypeSubtypeEquivSubtypeInter (fun i => ¬k i = 0) fun i => k i - 1 = j).trans <|
          Equiv.subtypeEquivRight fun i => by omega) fun _ => rfl
    simp only [hcard, hrank, hblock]
    ring

/-- **The local density at an odd prime from a diagonal Jordan form.** For `p` odd, units
`uᵢ` of `ℤ_p` and exponents `kᵢ`, the local density of the diagonal Gram matrix with entries
`uᵢ pᵏⁱ` is
`p ^ ∑_{j < max k} binom(#{i | j < kᵢ} + 1, 2)` times the product, over the exponents `j` that
occur, of the densities of the unimodular Jordan constituents with diagonal entries
`(uᵢ)_{kᵢ = j}`. -/
theorem localDensity_diagonal_unit_mul_pow (hp : p ≠ 2) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℤ_[p]ˣ) (k : ι → ℕ) :
    (diagonal fun i => (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i).localDensity =
      (p : ℚ) ^ (∑ j ∈ range (univ.sup k), (#{i | j < k i} + 1).choose 2) *
        ∏ j ∈ univ.image k, (diagonal fun i : {i // k i = j} => (u i : ℤ_[p])).localDensity := by
  rw [localDensity_diagonal_unit_mul_pow_of_le hp _ u k fun i => le_sup (mem_univ i)]
  congr 1
  refine (prod_subset (fun j hj => ?_) fun j _ hj => ?_).symm
  · obtain ⟨i, -, rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup (mem_univ i)))
  · have : IsEmpty {i // k i = j} :=
      ⟨fun i => hj (mem_image.mpr ⟨i.1, mem_univ _, i.2⟩)⟩
    exact localDensity_of_isEmpty _

end Matrix

namespace LinearMap.BilinForm

open Matrix Module

variable {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]

/-- **The local density at an odd prime of a form with a diagonal Jordan basis.** Let `B` be a
bilinear form over `ℤ_p`, `p` odd, with an orthogonal basis `b₀` whose diagonal entries are
`B (b₀ i) (b₀ i) = uᵢ pᵏⁱ`. Then the Gram matrix of `B` in every basis `b`, with any index type,
has local density `p ^ ∑_{j < max k} binom(#{i | j < kᵢ} + 1, 2)` times the product of the densities
of the unimodular Jordan constituents with diagonal entries `(uᵢ)_{kᵢ = j}`. -/
theorem localDensity_toMatrix_of_iIsOrtho (hp : p ≠ 2) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : LinearMap.BilinForm ℤ_[p] M} {b₀ : Basis ι ℤ_[p] M} (hb₀ : B.iIsOrtho b₀) {u : ι → ℤ_[p]ˣ}
    {k : ι → ℕ} (hu : ∀ i, B (b₀ i) (b₀ i) = u i * (p : ℤ_[p]) ^ k i) {κ : Type*} [Fintype κ]
    [DecidableEq κ] (b : Basis κ ℤ_[p] M) :
    (toMatrix b B).localDensity =
      (p : ℚ) ^ (∑ j ∈ Finset.range (univ.sup k), (#{i | j < k i} + 1).choose 2) *
        ∏ j ∈ univ.image k, (diagonal fun i : {i // k i = j} => (u i : ℤ_[p])).localDensity := by
  have hdiag : toMatrix b₀ B = diagonal fun i => (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i := by
    simpa only [hu] using hb₀.toMatrix_eq_diagonal
  set e := b₀.indexEquiv b
  have hb : toMatrix (b.reindex e.symm) B = reindex e.symm e.symm (toMatrix b B) := by
    ext i j
    simp only [toMatrix_apply, Basis.reindex_apply, Equiv.symm_symm, reindex_apply,
      submatrix_apply]
  have := b₀.invertibleToMatrix (b.reindex e.symm)
  rw [← localDensity_reindex e.symm, ← hb, ← toMatrix_mul_basis_toMatrix b₀ _ B, hdiag,
    localDensity_transpose_mul_mul (isUnit_det_of_invertible _)]
  exact localDensity_diagonal_unit_mul_pow hp u k

end LinearMap.BilinForm
