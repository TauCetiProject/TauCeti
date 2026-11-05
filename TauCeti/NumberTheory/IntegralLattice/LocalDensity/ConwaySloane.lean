/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.NumberTheory.IntegralLattice.LocalDensity.Basic
import TauCeti.Algebra.BigOperators.Finset.LayerCake
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

* `TauCeti.conwaySloanePMass_def`, `TauCeti.conwaySloanePMass_zero`: the defining formula of the
  `p`-mass, and its value on a unimodular diagonal form.
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

/-- The defining formula of the Conway–Sloane `p`-mass, the product of the standard `p`-masses of
the unimodular constituents and of the cross terms. The body of `TauCeti.conwaySloanePMass` is not
exposed to importing modules, so this is how they evaluate it. -/
theorem conwaySloanePMass_def {ι : Type*} [Fintype ι] (u : ι → ℤ_[p]ˣ) (k : ι → ℕ) :
    conwaySloanePMass p u k =
      (∏ j ∈ univ.image k,
          (conwaySloaneStdMass p #{i | k i = j} (∏ i with k i = j, PadicInt.toZMod (u i : ℤ_[p])) :
            ℝ)) *
        √(p : ℝ) ^ ∑ i, ∑ i', (k i' - k i) := by
  rw [conwaySloanePMass]

/-- The `p`-mass of a unimodular diagonal form `diag(uᵢ)` is the standard `p`-mass of its rank
and of the reduction of `∏ uᵢ` modulo `p`: it has a single constituent and no cross terms. -/
@[simp]
theorem conwaySloanePMass_zero {ι : Type*} [Fintype ι] (u : ι → ℤ_[p]ˣ) :
    conwaySloanePMass p u 0 =
      (conwaySloaneStdMass p (Fintype.card ι) (∏ i, PadicInt.toZMod (u i : ℤ_[p])) : ℝ) := by
  rw [conwaySloanePMass_def]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · have himage : univ.image (0 : ι → ℕ) = {0} := image_const univ_nonempty 0
    simp [himage]

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
  rw [localDensity_diagonal_unit_mul_pow hp, conwaySloanePMass_def, ← card_univ,
    ← two_mul_sum_range_choose_add_sum_sum_tsub univ k, pow_add, pow_mul, hsq]
  push_cast
  linear_combination ((p : ℝ) ^ (∑ j ∈ range (univ.sup k), (#{i | j < k i} + 1).choose 2 : ℕ) *
    √(p : ℝ) ^ (∑ i, ∑ i', (k i' - k i) : ℕ)) * hblocks

section BilinForm

open LinearMap (BilinForm)
open LinearMap.BilinForm Module

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]

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
