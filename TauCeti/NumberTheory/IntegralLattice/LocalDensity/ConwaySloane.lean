/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.NumberTheory.IntegralLattice.LocalDensity.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.IntegralLattice.LocalDensity.Diagonal

/-!
# The Conway–Sloane `p`-mass at an odd prime

Conway and Sloane write the mass of a genus of positive definite lattices of rank `n` as

```text
m(f) = 2 π^{-n (n + 1) / 4} ∏_{j=1}^{n} Γ(j / 2) ∏_p 2 m_p(f),
```

where the `p`-mass `m_p(f)` is read off a Jordan decomposition `f = ⊕_q q f_q` of the Gram
matrix over `ℤ_p`, with `q` running over the powers of `p` and each `f_q` unimodular of
dimension `n(q)`. At an odd prime `p` it is

```text
m_p(f) = ∏_q std(f_q) · ∏_{q < q'} (q' / q)^{n(q) n(q') / 2},
```

a product of the *diagonal factors* `std(f_q)` and of the *cross terms*. The diagonal factor of a
unimodular constituent of dimension `n` and determinant `d` is the standard `p`-mass

```text
n = 2m + 1:  std = 1 / (2 ∏_{i=1}^{m} (1 - p^{-2i})),
n = 2m + 2:  std = 1 / (2 (1 - ε p^{-(m+1)}) ∏_{i=1}^{m} (1 - p^{-2i})),  ε = ((-1)^{m+1} d | p),
```

and `std = 1` for `n = 0`. The sign `ε` is the Legendre symbol of the *signed* determinant; the
Conway–Sloane `p`-adic symbol records the Legendre symbol `(d | p)` of the determinant itself, and
the two differ by `(-1 | p)^{m+1}`. The cross terms are half-integral powers of `p`, so `m_p(f)` is
a real number that need not be rational.

This file defines the standard `p`-mass (`TauCeti.conwaySloaneStdMass`) and the `p`-mass of a
diagonal Jordan form `diag(uᵢ pᵏⁱ)` (`TauCeti.conwaySloanePMass`), and proves the dictionary to the
local density `α_p` of `Matrix.localDensity`, the limit of
`p^{-r n (n - 1) / 2} · #{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X ≡ A (mod pʳ)}`:

```text
m_p(f) · α_p(f) = p^{v_p(det f) (n + 1) / 2}.
```

At a prime not dividing `2 det f` the valuation is `0` and this says `m_p(f) = α_p(f)⁻¹`, the
inverse of the closed values of `α_p` recorded by the standard `p`-mass, so the factor `2 m_p(f)`
of the mass formula is the normalized density `(α_p(f) / 2)⁻¹`. In general the power of
`p` is the `p`-part of the factor `det(f)^{(n + 1) / 2}` of Siegel's form of the mass formula.
Since `α_p` only depends on the isometry class of the lattice, so does `m_p`: two orthogonal bases
of one form give the same `p`-mass.

## Main definitions

* `TauCeti.conwaySloaneStdMass p n d`: the standard `p`-mass of a unimodular `ℤ_p`-lattice of rank
  `n` whose determinant reduces to `d` modulo `p`.
* `TauCeti.conwaySloanePMass p u k`: the Conway–Sloane `p`-mass of the diagonal Jordan form
  `diag(uᵢ pᵏⁱ)`.

## Main results

* `TauCeti.conwaySloaneStdMass_mul_localDensity`: the standard `p`-mass of a unimodular Gram
  matrix is the inverse of its local density.
* `TauCeti.conwaySloanePMass_mul_localDensity_diagonal`: `m_p · α_p = p^{(n + 1) ∑ kᵢ / 2}` for
  `diag(uᵢ pᵏⁱ)`.
* `TauCeti.conwaySloanePMass_mul_localDensity_toMatrix`: the same identity for the Gram matrix,
  in any basis, of a bilinear form over `ℤ_p` with an orthogonal basis of diagonal entries
  `uᵢ pᵏⁱ`, with `∑ kᵢ` replaced by the valuation of the determinant.
* `TauCeti.conwaySloanePMass_eq_of_iIsOrtho`: the `p`-mass does not depend on the orthogonal basis.

## References

* J. H. Conway, N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*, Proc. Roy.
  Soc. London Ser. A 419 (1988), 259–285: the `p`-mass, its diagonal factors and cross terms, and
  the standard mass, with §12 for the comparison with Siegel's local densities.
-/

public section

open Finset Matrix

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- **The Conway–Sloane standard `p`-mass** of a unimodular `ℤ_p`-lattice of rank `n` whose Gram
determinant reduces to `d` modulo `p`: it is `1` in rank `0`, and otherwise
`1 / (2 ∏_{i=1}^{m} (1 - p^{-2i}))` in rank `2m + 1` and
`1 / (2 (1 - ε p^{-(m+1)}) ∏_{i=1}^{m} (1 - p^{-2i}))` in rank `2m + 2`, where
`ε = ((-1)^{m+1} d | p)`. For `p` odd it is the inverse of the local density
(`TauCeti.conwaySloaneStdMass_mul_localDensity`). -/
noncomputable def conwaySloaneStdMass (n : ℕ) (d : ZMod p) : ℚ :=
  match n with
  | 0 => 1
  | n + 1 =>
    if Even n then
      (2 * ∏ i ∈ range (n / 2), (1 - ((p : ℚ) ^ (2 * (i + 1)))⁻¹))⁻¹
    else
      (2 * (1 - quadraticChar (ZMod p) ((-1) ^ (n / 2 + 1) * d) * ((p : ℚ) ^ (n / 2 + 1))⁻¹) *
        ∏ i ∈ range (n / 2), (1 - ((p : ℚ) ^ (2 * (i + 1)))⁻¹))⁻¹

variable {p}

/-- The standard `p`-mass in rank `0` is `1`. -/
@[simp]
theorem conwaySloaneStdMass_zero (d : ZMod p) : conwaySloaneStdMass p 0 d = 1 := by
  simp [conwaySloaneStdMass]

/-- The standard `p`-mass in odd rank `2m + 1` is `1 / (2 ∏_{i=1}^{m} (1 - p^{-2i}))`; it does
not depend on the determinant. -/
theorem conwaySloaneStdMass_two_mul_add_one (m : ℕ) (d : ZMod p) :
    conwaySloaneStdMass p (2 * m + 1) d =
      (2 * ∏ i ∈ range m, (1 - ((p : ℚ) ^ (2 * (i + 1)))⁻¹))⁻¹ := by
  simp [conwaySloaneStdMass]

/-- The standard `p`-mass in even rank `2m + 2` is
`1 / (2 (1 - ε p^{-(m+1)}) ∏_{i=1}^{m} (1 - p^{-2i}))`, with `ε = ((-1)^{m+1} d | p)`. -/
theorem conwaySloaneStdMass_two_mul_add_two (m : ℕ) (d : ZMod p) :
    conwaySloaneStdMass p (2 * m + 2) d =
      (2 * (1 - quadraticChar (ZMod p) ((-1) ^ (m + 1) * d) * ((p : ℚ) ^ (m + 1))⁻¹) *
        ∏ i ∈ range m, (1 - ((p : ℚ) ^ (2 * (i + 1)))⁻¹))⁻¹ := by
  have h : (2 * m + 1) / 2 = m := by omega
  simp [conwaySloaneStdMass, h]

/-- **The standard `p`-mass is the inverse of the local density** of a unimodular lattice: for `p`
odd and `A` a symmetric matrix over `ℤ_p` with unit determinant, `std_p(A) · α_p(A) = 1`, where
`std_p(A)` is computed from the rank of `A` and the reduction of `det A` modulo `p`. -/
theorem conwaySloaneStdMass_mul_localDensity (hp : p ≠ 2) {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A) (hdet : IsUnit A.det) :
    conwaySloaneStdMass p (Fintype.card n) (A.map PadicInt.toZMod).det * A.localDensity = 1 := by
  have hα := (localDensity_pos hA hdet.ne_zero).ne'
  have hlim := tendsto_localDensityCount_div_of_det_ne_zero hA hdet.ne_zero
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (Fintype.card n)
  · cases m with
    | zero =>
      have : IsEmpty n := Fintype.card_eq_zero_iff.mp hm
      simp
    | succ m =>
      have hm' : Fintype.card n = 2 * m + 2 := by omega
      rw [hm', conwaySloaneStdMass_two_mul_add_two,
        tendsto_nhds_unique (tendsto_localDensityCount_div_of_card_eq_two_mul_add_two hp hA hdet
          hm') hlim]
      exact inv_mul_cancel₀ hα
  · rw [hm, conwaySloaneStdMass_two_mul_add_one,
      tendsto_nhds_unique (tendsto_localDensityCount_div_of_card_eq_two_mul_add_one hp hA hdet hm)
        hlim]
    exact inv_mul_cancel₀ hα

variable (p) in
/-- **The Conway–Sloane `p`-mass** of the diagonal Jordan form `diag(uᵢ pᵏⁱ)`, for units `uᵢ` of
`ℤ_p`: the product over the scales `j` that occur of the standard `p`-masses of the unimodular
constituents, of rank `#{i | kᵢ = j}` and determinant `∏_{kᵢ = j} uᵢ`, times the cross terms
`∏_{j < j'} (p^{j'} / p^j)^{nⱼ n_{j'} / 2} = √p ^ ∑_{i, i'} (k_{i'} - kᵢ)⁺`.

This is Conway and Sloane's formula for `m_p` at an odd prime `p`, where it satisfies
`m_p · α_p = p^{(n + 1) v_p(det) / 2}` (`TauCeti.conwaySloanePMass_mul_localDensity_toMatrix`).
Their `2`-mass has different diagonal factors and an extra type factor, and is not this
expression at `p = 2`. -/
noncomputable def conwaySloanePMass {ι : Type*} [Fintype ι] (u : ι → ℤ_[p]ˣ) (k : ι → ℕ) : ℝ :=
  (∏ j ∈ univ.image k,
      (conwaySloaneStdMass p #{i | k i = j} (∏ i with k i = j, PadicInt.toZMod (u i : ℤ_[p])) :
        ℝ)) *
    √(p : ℝ) ^ ∑ i, ∑ i', (k i' - k i)

/-- The defining formula of the Conway–Sloane `p`-mass: diagonal factors times cross terms. -/
theorem conwaySloanePMass_def {ι : Type*} [Fintype ι] (u : ι → ℤ_[p]ˣ) (k : ι → ℕ) :
    conwaySloanePMass p u k =
      (∏ j ∈ univ.image k,
          (conwaySloaneStdMass p #{i | k i = j} (∏ i with k i = j, PadicInt.toZMod (u i : ℤ_[p])) :
            ℝ)) *
        √(p : ℝ) ^ ∑ i, ∑ i', (k i' - k i) := by
  rw [conwaySloanePMass]

/-- The exponent identity behind the Conway–Sloane dictionary: twice the exponent
`∑_{j < max k} binom(Nⱼ + 1, 2)`, `Nⱼ = #{i | j < kᵢ}`, of the local density of a diagonal Jordan
form, plus the exponent `∑_{i, i'} (k_{i'} - kᵢ)⁺` of the cross terms, is `(n + 1) ∑ kᵢ`. -/
private theorem two_mul_sum_choose_add_sum_sum_tsub {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    2 * ∑ j ∈ range (univ.sup k), (#{i | j < k i} + 1).choose 2 + ∑ i, ∑ i', (k i' - k i) =
      (Fintype.card ι + 1) * ∑ i, k i := by
  set K := univ.sup k
  have hK (i : ι) : k i ≤ K := le_sup (mem_univ i)
  have hcount (m : ℕ) (hm : m ≤ K) : #{j ∈ range K | j < m} = m := by
    rw [show {j ∈ range K | j < m} = range m by ext j; simp; omega, card_range]
  -- `∑ⱼ Nⱼ = ∑ᵢ kᵢ` and `∑ⱼ Nⱼ² = ∑_{i, i'} min kᵢ k_{i'}`, by counting the `j` below `kᵢ`
  have h1 : ∑ j ∈ range K, #{i | j < k i} = ∑ i, k i := by
    simp_rw [card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← card_filter, hcount _ (hK i)]
  have h2 : ∑ j ∈ range K, #{i | j < k i} * #{i | j < k i} = ∑ i, ∑ i', min (k i) (k i') := by
    simp_rw [card_filter, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun i' _ => ?_
    rw [← hcount _ (min_le_of_left_le (hK i)), card_filter]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> omega
  have hchoose (N : ℕ) : 2 * (N + 1).choose 2 = N * N + N := by
    have h := Nat.add_one_mul_choose_eq N 1
    rw [Nat.choose_one_right] at h
    linarith
  calc 2 * ∑ j ∈ range K, (#{i | j < k i} + 1).choose 2 + ∑ i, ∑ i', (k i' - k i)
      = ∑ i, ∑ i', (min (k i) (k i') + (k i' - k i)) + ∑ i, k i := by
        simp_rw [mul_sum, hchoose, sum_add_distrib, h1, h2]
        ring
    _ = (Fintype.card ι + 1) * ∑ i, k i := by
        rw [sum_comm]
        simp_rw [show ∀ i i', min (k i) (k i') + (k i' - k i) = k i' from fun i i' => by omega]
        simp [sum_const, card_univ, add_mul, mul_sum, sum_add_distrib]

/-- **The Conway–Sloane dictionary at an odd prime, for a diagonal Jordan form.** For `p` odd,
units `uᵢ` of `ℤ_p` and exponents `kᵢ`, the `p`-mass and the local density of the diagonal Gram
matrix with entries `uᵢ pᵏⁱ` satisfy `m_p · α_p = p^{(n + 1) ∑ kᵢ / 2}`, where `n` is the rank and
`∑ kᵢ` is the valuation of the determinant. -/
theorem conwaySloanePMass_mul_localDensity_diagonal (hp : p ≠ 2) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (u : ι → ℤ_[p]ˣ) (k : ι → ℕ) :
    conwaySloanePMass p u k *
        ((diagonal fun i => (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i).localDensity : ℝ) =
      √(p : ℝ) ^ ((Fintype.card ι + 1) * ∑ i, k i) := by
  -- the diagonal factors cancel the densities of the unimodular constituents
  have hblocks : ∏ j ∈ univ.image k,
      ((conwaySloaneStdMass p #{i | k i = j} (∏ i with k i = j, PadicInt.toZMod (u i : ℤ_[p])) :
        ℝ) * ((diagonal fun i : {i // k i = j} => (u i : ℤ_[p])).localDensity : ℝ)) = 1 := by
    refine prod_eq_one fun j _ => ?_
    have hdet : IsUnit (diagonal fun i : {i // k i = j} => (u i : ℤ_[p])).det := by
      rw [det_diagonal, ← Units.coe_prod]
      exact Units.isUnit _
    have h := conwaySloaneStdMass_mul_localDensity hp (diagonal_transpose _) hdet
    rw [diagonal_map (map_zero _), det_diagonal, Fintype.card_subtype] at h
    rw [prod_subtype (univ.filter fun i => k i = j) (p := fun i => k i = j) (by simp),
      ← Rat.cast_mul, h, Rat.cast_one]
  rw [prod_mul_distrib] at hblocks
  have hsq : √(p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  rw [localDensity_diagonal_unit_mul_pow hp, conwaySloanePMass,
    ← two_mul_sum_choose_add_sum_sum_tsub k, pow_add, pow_mul, hsq]
  push_cast
  linear_combination ((p : ℝ) ^ (∑ j ∈ range (univ.sup k), (#{i | j < k i} + 1).choose 2 : ℕ) *
    √(p : ℝ) ^ (∑ i, ∑ i', (k i' - k i) : ℕ)) * hblocks

section BilinForm

open LinearMap (BilinForm)
open LinearMap.BilinForm Module

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]

/-- The Gram matrix, in any basis `b`, of a bilinear form with an orthogonal basis `b₀` of
diagonal entries `uᵢ pᵏⁱ` is congruent to `diag(uᵢ pᵏⁱ)`, so the valuation of its determinant is
`∑ kᵢ`. -/
private theorem valuation_det_toMatrix_of_iIsOrtho {ι : Type*} [Fintype ι]
    {B : BilinForm ℤ_[p] M} {b₀ : Basis ι ℤ_[p] M} (hb₀ : B.iIsOrtho b₀)
    {u : ι → ℤ_[p]ˣ} {k : ι → ℕ} (hu : ∀ i, B (b₀ i) (b₀ i) = u i * (p : ℤ_[p]) ^ k i)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ ℤ_[p] M) :
    (toMatrix b B).det.valuation = ∑ i, k i := by
  classical
  have hdiag : toMatrix b₀ B = diagonal fun i => (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i := by
    simpa only [hu] using hb₀.toMatrix_eq_diagonal
  set e := b₀.indexEquiv b
  have hb : toMatrix (b.reindex e.symm) B = reindex e.symm e.symm (toMatrix b B) := by
    ext i j
    simp only [toMatrix_apply, Basis.reindex_apply, Equiv.symm_symm, reindex_apply,
      submatrix_apply]
  have := b₀.invertibleToMatrix (b.reindex e.symm)
  set P := b₀.toMatrix (b.reindex e.symm)
  have hP : IsUnit P.det := isUnit_det_of_invertible _
  have hcongr : reindex e.symm e.symm (toMatrix b B) =
      Pᵀ * (diagonal fun i => (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) * P := by
    rw [← hb, ← toMatrix_mul_basis_toMatrix b₀ _ B, hdiag]
  have hu' : IsUnit (∏ i, (u i : ℤ_[p])) := by
    rw [← Units.coe_prod]
    exact Units.isUnit _
  have hp0 : (p : ℤ_[p]) ^ ∑ i, k i ≠ 0 := pow_ne_zero _ (NeZero.ne _)
  have hD : (∏ i, (u i : ℤ_[p])) * (p : ℤ_[p]) ^ ∑ i, k i ≠ 0 := mul_ne_zero hu'.ne_zero hp0
  rw [← det_reindex_self e.symm, hcongr, det_mul, det_mul, det_transpose, det_diagonal,
    prod_mul_distrib, prod_pow_eq_pow_sum,
    PadicInt.valuation_mul (mul_ne_zero hP.ne_zero hD) hP.ne_zero,
    PadicInt.valuation_mul hP.ne_zero hD, PadicInt.valuation_mul hu'.ne_zero hp0,
    PadicInt.valuation_eq_zero_of_isUnit hP, PadicInt.valuation_eq_zero_of_isUnit hu',
    PadicInt.valuation_pow, PadicInt.valuation_p]
  simp

/-- **The Conway–Sloane dictionary at an odd prime.** Let `B` be a bilinear form over `ℤ_p`, `p`
odd, with an orthogonal basis `b₀` whose diagonal entries are `B (b₀ i) (b₀ i) = uᵢ pᵏⁱ`. Then the
Gram matrix `A` of `B` in every basis `b`, with any index type, satisfies
`m_p · α_p(A) = p^{(n + 1) v_p(det A) / 2}`, where `m_p` is the Conway–Sloane `p`-mass of the
Jordan data `(uᵢ, kᵢ)` and `n` is the rank. -/
theorem conwaySloanePMass_mul_localDensity_toMatrix (hp : p ≠ 2) {ι : Type*} [Fintype ι]
    {B : BilinForm ℤ_[p] M} {b₀ : Basis ι ℤ_[p] M} (hb₀ : B.iIsOrtho b₀)
    {u : ι → ℤ_[p]ˣ} {k : ι → ℕ} (hu : ∀ i, B (b₀ i) (b₀ i) = u i * (p : ℤ_[p]) ^ k i)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ ℤ_[p] M) :
    conwaySloanePMass p u k * ((toMatrix b B).localDensity : ℝ) =
      √(p : ℝ) ^ ((Fintype.card κ + 1) * (toMatrix b B).det.valuation) := by
  classical
  rw [valuation_det_toMatrix_of_iIsOrtho hb₀ hu b, localDensity_toMatrix_of_iIsOrtho hp hb₀ hu b,
    ← localDensity_diagonal_unit_mul_pow hp u k, ← Fintype.card_congr (b₀.indexEquiv b)]
  exact conwaySloanePMass_mul_localDensity_diagonal hp u k

/-- **The Conway–Sloane `p`-mass is an invariant of the form**: at an odd prime, two orthogonal
bases of one bilinear form over `ℤ_p`, with diagonal entries `uᵢ pᵏⁱ` and `u'ᵢ p^{k'ᵢ}`, give the
same `p`-mass, although the Jordan data `(uᵢ, kᵢ)` and `(u'ᵢ, k'ᵢ)` themselves need not agree. -/
theorem conwaySloanePMass_eq_of_iIsOrtho (hp : p ≠ 2) {ι : Type*} [Fintype ι]
    {B : BilinForm ℤ_[p] M} {b₀ : Basis ι ℤ_[p] M} (hb₀ : B.iIsOrtho b₀) {u : ι → ℤ_[p]ˣ}
    {k : ι → ℕ} (hu : ∀ i, B (b₀ i) (b₀ i) = u i * (p : ℤ_[p]) ^ k i) {κ : Type*} [Fintype κ]
    {b₁ : Basis κ ℤ_[p] M} (hb₁ : B.iIsOrtho b₁) {u' : κ → ℤ_[p]ˣ}
    {k' : κ → ℕ} (hu' : ∀ i, B (b₁ i) (b₁ i) = u' i * (p : ℤ_[p]) ^ k' i) :
    conwaySloanePMass p u k = conwaySloanePMass p u' k' := by
  classical
  have h₀ := conwaySloanePMass_mul_localDensity_toMatrix hp hb₀ hu b₀
  have h₁ := conwaySloanePMass_mul_localDensity_toMatrix hp hb₁ hu' b₀
  have hα : ((toMatrix b₀ B).localDensity : ℝ) ≠ 0 := by
    refine fun h => ?_
    rw [h, mul_zero] at h₀
    exact pow_ne_zero _ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Fact.out : p.Prime).pos))
      h₀.symm
  exact mul_right_cancel₀ hα (h₀.trans h₁.symm)

end BilinForm

end TauCeti
