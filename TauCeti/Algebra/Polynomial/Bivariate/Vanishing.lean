/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.Algebra.Polynomial.Bivariate.Basic
import TauCeti.Algebra.Polynomial.Bivariate.SchwartzZippel
import TauCeti.Algebra.Polynomial.Bivariate.Specialization
import TauCeti.Algebra.Polynomial.HasseDeriv
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.Polynomial.IrreducibleBasis.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.Multiplicity

/-!
# Bivariate polynomial vanishing estimates

Throughout this file, a bivariate polynomial `P : K[X][X]` is evaluated at a point `(x, y) : K × K`
via `P.evalEval y x = (P.map (evalRingHom y)).eval x`. Accordingly, the first coordinate `x` enters
the outer polynomial variable (bounded by `P.natDegree`, denoted `dX` below) and the second
coordinate `y` enters the inner coefficient polynomials (bounded by
`∀ i, (P.coeff i).natDegree ≤ dY`).
Note that this reverses the `R[X][Y]` variable naming convention used in
`TauCeti.Algebra.Polynomial.Bivariate.Basic` and
`TauCeti.Algebra.Polynomial.Bivariate.Specialization`.

For a squarefree `F : K[X][X]` over a GCD domain of characteristic zero, the resultant
`F.resultant F.derivative` is nonzero by `Squarefree.resultant_derivative_ne_zero`, so
`Polynomial.sum_rootMultiplicity_map_le` bounds the sum of
`(F.map (evalRingHom p.2)).rootMultiplicity p.1` over a finite set `Ω` with distinct second
coordinates by the zero count of `F` in `Ω` plus `(2 * F.natDegree - 1) * dY`
(`Polynomial.sum_rootMultiplicity_le_of_squarefree`). By Mathlib's convention
`(0 : K[X]).rootMultiplicity a = 0`, an identically zero fiber `F.map (evalRingHom p.2) = 0`
contributes `0` to the sum, not an unbounded vanishing order (in contrast to divisibility by every
power `(X - C p.1) ^ k`).

Factoring an arbitrary nonzero polynomial `P : K[X][X]` over a characteristic-zero GCD domain into
a coefficient-ring factor in `K[X]` and a multiset of irreducible factors of positive outer natural
degree (`Polynomial.exists_eq_C_mul_prod_irreducible`), and applying
`Polynomial.sum_rootMultiplicity_le_of_squarefree` to each irreducible (hence squarefree) factor,
yields a general bivariate vanishing estimate on any finite point set having both distinct second
coordinates and the Schwartz–Zippel zero bound `M * (F.natDegree + (Bivariate.swap F).natDegree)`
for every irreducible `F : K[X][X]` of positive outer natural degree
(`Polynomial.mul_card_le_of_forall_X_sub_C_pow_dvd`).

Specializing to the image of a Cartesian grid `S × S` under `Matrix.toLinProd M` for a
`2 × 2` matrix `M` with nonzero determinant over `K`
(`Polynomial.card_filter_evalEval_eq_zero_linearGrid_le_of_natDegree_le`) whose second linear form
separates grid points yields a vanishing criterion on sheared grids
(`Polynomial.eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd`), and in characteristic zero fiber
divisibility by `(X - C x) ^ k` is equivalent to vanishing of the first `k` outer iterated
derivatives
(`Polynomial.X_sub_C_pow_dvd_map_evalRingHom_iff_forall_evalEval_iterate_derivative_eq_zero`).

## Main results

* `Polynomial.sum_rootMultiplicity_le_of_squarefree`: sum of fiberwise root multiplicities of a
  squarefree bivariate polynomial over a set with distinct second coordinates in characteristic
  zero.
* `Polynomial.mul_card_le_of_forall_X_sub_C_pow_dvd`: abstract bivariate multiplicity bound
  requiring distinct second coordinates and the Schwartz–Zippel zero bound
  `M * (F.natDegree + (Bivariate.swap F).natDegree)` for every irreducible `F : K[X][X]` of
  positive outer natural degree.
* `Polynomial.X_sub_C_pow_dvd_map_evalRingHom_iff_forall_evalEval_iterate_derivative_eq_zero`:
  characterization of fiberwise divisibility `(X - C x) ^ k ∣ P.map (evalRingHom y)` in
  characteristic zero via vanishing of the first `k` outer iterated derivatives at `(x, y)`.
* `Polynomial.eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd`: vanishing criterion on a sheared
  grid `(S ×ˢ S).image (Matrix.toLinProd M)` for a `2 × 2` matrix `M` with nonzero
  determinant.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026, Appendix A.
* T. Tao, *A sketch of the proof of non-existence of Siegel zeroes*, blog post, 2026.
-/

public section

open Finset

namespace Polynomial

section SquarefreeBound

/-- **Sum of fiberwise root multiplicities of a squarefree bivariate polynomial.**
Over a GCD domain of characteristic zero, if `F : K[X][X]` is squarefree and every coefficient
`F.coeff i` has natural degree at most `dY`, then the sum of
`(F.map (evalRingHom p.2)).rootMultiplicity p.1` over a finite set `Ω` of points with distinct
second coordinates is bounded by the number of zeros of `F` in `Ω` (`F.evalEval p.2 p.1 = 0`) plus
`(2 * F.natDegree - 1) * dY`. -/
theorem sum_rootMultiplicity_le_of_squarefree {K : Type*} [CommRing K] [IsDomain K]
    [IsGCDMonoid K] [CharZero K] [DecidableEq K]
    {F : K[X][X]} (hF : Squarefree F)
    {dY : ℕ} (hdY : ∀ i, (F.coeff i).natDegree ≤ dY)
    {Ω : Finset (K × K)} (hinj : Set.InjOn Prod.snd (Ω : Set (K × K))) :
    ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      (Ω.filter fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card +
        (2 * F.natDegree - 1) * dY := by
  let := Classical.arbitrary (NormalizedGCDMonoid K)
  simpa [IsRoot, map_evalRingHom_eval] using
    sum_rootMultiplicity_map_le hinj hF.resultant_derivative_ne_zero hdY

end SquarefreeBound

section VanishingHelpers

private theorem sum_rootMultiplicity_le_of_squarefree_of_zero_bound {K : Type*} [CommRing K]
    [IsDomain K] [IsGCDMonoid K] [CharZero K] [DecidableEq K]
    {F : K[X][X]} (hF : Squarefree F) {Ω : Finset (K × K)}
    (hinj : Set.InjOn Prod.snd (Ω : Set (K × K))) {M : ℕ}
    (hzero : (Ω.filter fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card ≤
      M * (F.natDegree + (Bivariate.swap F).natDegree)) :
    ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      M * (F.natDegree + (Bivariate.swap F).natDegree) +
        2 * F.natDegree * (Bivariate.swap F).natDegree := by
  have hcoeffF : ∀ i, (F.coeff i).natDegree ≤ (Bivariate.swap F).natDegree :=
    (natDegree_swap_le_iff F _).mp le_rfl
  calc ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1
      ≤ (Ω.filter fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card +
          (2 * F.natDegree - 1) * (Bivariate.swap F).natDegree :=
        sum_rootMultiplicity_le_of_squarefree hF hcoeffF hinj
    _ ≤ M * (F.natDegree + (Bivariate.swap F).natDegree) +
          2 * F.natDegree * (Bivariate.swap F).natDegree := by
        have h2 : (2 * F.natDegree - 1) * (Bivariate.swap F).natDegree ≤
            2 * F.natDegree * (Bivariate.swap F).natDegree :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        omega

private theorem mul_card_le_of_sum_rootMultiplicity_le {K : Type*} [CommRing K]
    {s : Multiset K[X][X]} {Ω₁ : Finset (K × K)} {M k : ℕ}
    (hpt : ∀ p ∈ Ω₁, k ≤ (s.map fun F ↦ (F.map (evalRingHom p.2)).rootMultiplicity p.1).sum)
    (hF_bound : ∀ F ∈ s, ∑ p ∈ Ω₁, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      M * (F.natDegree + (Bivariate.swap F).natDegree) +
        2 * F.natDegree * (Bivariate.swap F).natDegree) :
    k * Ω₁.card ≤
      M * ((s.map natDegree).sum + (s.map fun F ↦ (Bivariate.swap F).natDegree).sum) +
        2 * (s.map natDegree).sum * (s.map fun F ↦ (Bivariate.swap F).natDegree).sum := by
  set sX := (s.map natDegree).sum
  set sY := (s.map fun F ↦ (Bivariate.swap F).natDegree).sum
  have hlin : (s.map fun F ↦ M * (F.natDegree + (Bivariate.swap F).natDegree) +
        2 * F.natDegree * (Bivariate.swap F).natDegree).sum =
      M * (sX + sY) + 2 * (s.map fun F ↦ F.natDegree * (Bivariate.swap F).natDegree).sum := by
    simp only [sX, sY, mul_add, mul_assoc, Multiset.sum_map_add, Multiset.sum_map_mul_left]
  calc k * Ω₁.card = ∑ _p ∈ Ω₁, k := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ Ω₁, (s.map fun F ↦ (F.map (evalRingHom p.2)).rootMultiplicity p.1).sum :=
        Finset.sum_le_sum hpt
    _ = (s.map fun F ↦ ∑ p ∈ Ω₁, (F.map (evalRingHom p.2)).rootMultiplicity p.1).sum :=
        (Multiset.sum_map_sum (m := s) (s := Ω₁)
          (f := fun F p ↦ (F.map (evalRingHom p.2)).rootMultiplicity p.1)).symm
    _ ≤ (s.map fun F ↦ M * (F.natDegree + (Bivariate.swap F).natDegree) +
          2 * F.natDegree * (Bivariate.swap F).natDegree).sum :=
        Multiset.sum_map_le_sum_map _ _ hF_bound
    _ = M * (sX + sY) +
          2 * (s.map fun F ↦ F.natDegree * (Bivariate.swap F).natDegree).sum := hlin
    _ ≤ M * (sX + sY) + 2 * (sX * sY) := by
        refine Nat.add_le_add_left (Nat.mul_le_mul_left 2 ?_) _
        exact (Multiset.sum_map_le_sum_map _ _ fun F hF ↦ Nat.mul_le_mul_left _
          (Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hF))).trans_eq
          Multiset.sum_map_mul_right
    _ = M * (sX + sY) + 2 * sX * sY := by ring

private theorem mul_card_add_le_of_split {card₀ card₁ degC sX sY dX dY M k : ℕ}
    (hΩ₀ : card₀ ≤ degC) (hΩ₁ : k * card₁ ≤ M * (sX + sY) + 2 * sX * sY)
    (hsX : sX ≤ dX) (hY : degC + sY ≤ dY) :
    k * (card₀ + card₁) ≤ M * dX + max k M * dY + 2 * dX * dY := by
  have hsY : sY ≤ dY := le_trans (Nat.le_add_left _ _) hY
  calc k * (card₀ + card₁) = k * card₀ + k * card₁ := by rw [mul_add]
    _ ≤ k * degC + (M * (sX + sY) + 2 * sX * sY) :=
        add_le_add (Nat.mul_le_mul_left k hΩ₀) hΩ₁
    _ ≤ max k M * degC + (M * sX + max k M * sY + 2 * sX * sY) := by
        have h1 : k * degC ≤ max k M * degC := Nat.mul_le_mul_right _ (le_max_left k M)
        have h2 : M * sY ≤ max k M * sY := Nat.mul_le_mul_right _ (le_max_right k M)
        rw [mul_add]
        omega
    _ = M * sX + max k M * (degC + sY) + 2 * sX * sY := by ring
    _ ≤ M * dX + max k M * dY + 2 * dX * dY := by
        have h1 : M * sX ≤ M * dX := Nat.mul_le_mul_left M hsX
        have h2 : max k M * (degC + sY) ≤ max k M * dY := Nat.mul_le_mul_left _ hY
        have h3 : 2 * sX * sY ≤ 2 * dX * dY :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hsX) hsY
        omega

end VanishingHelpers

section VanishingEstimates

/-- **Abstract bivariate multiplicity bound.** Let `P : K[X][X]` be nonzero over a GCD domain of
characteristic zero, where point evaluation at `(x, y)` is
`P.evalEval y x = (P.map (evalRingHom y)).eval x`, `dX` bounds the first-coordinate (outer)
natural degree `P.natDegree`, and `dY` bounds the second-coordinate (inner) coefficient natural
degrees `(P.coeff i).natDegree`. If `Ω` is a finite set of points satisfying both distinct second
coordinates and the Schwartz–Zippel zero bound
`(Ω.filter fun p ↦ F.evalEval p.2 p.1 = 0).card ≤ M * (F.natDegree + (Bivariate.swap F).natDegree)`
for every irreducible `F : K[X][X]` of positive outer natural degree, and `P.map (evalRingHom p.2)`
vanishes to order at least `k` at `p.1` for every `p ∈ Ω`, then
`k * Ω.card ≤ M * dX + max k M * dY + 2 * dX * dY`. -/
theorem mul_card_le_of_forall_X_sub_C_pow_dvd {K : Type*} [CommRing K] [IsDomain K]
    [IsGCDMonoid K] [CharZero K] [DecidableEq K]
    {P : K[X][X]} (hP : P ≠ 0) {dX dY : ℕ}
    (hdX : P.natDegree ≤ dX) (hdY : ∀ i, (P.coeff i).natDegree ≤ dY)
    {Ω : Finset (K × K)} (hinj : Set.InjOn Prod.snd (Ω : Set (K × K)))
    {M k : ℕ}
    (hsz : ∀ F : K[X][X], Irreducible F → 0 < F.natDegree →
      (Ω.filter fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card ≤
        M * (F.natDegree + (Bivariate.swap F).natDegree))
    (hvan : ∀ p ∈ Ω, (X - C p.1) ^ k ∣ P.map (evalRingHom p.2)) :
    k * Ω.card ≤ M * dX + max k M * dY + 2 * dX * dY := by
  -- Factor `P = C c * s.prod` into its `Y`-content `c` and primitive irreducible factors `s`.
  obtain ⟨c, s, hs, hPeq⟩ := exists_eq_C_mul_prod_irreducible P
  have hc0 : c ≠ 0 := fun h0 ↦ hP (by rw [hPeq, h0, map_zero, zero_mul])
  have hs_ne : ∀ F ∈ s, F ≠ 0 := fun F hF ↦ (hs F hF).1.ne_zero
  have hdegX_sum : (s.map natDegree).sum = P.natDegree := by
    rw [hPeq, natDegree_C_mul hc0, natDegree_multiset_prod s fun h ↦ hs_ne 0 h rfl]
  have hdegY_sum : c.natDegree + (s.map fun F ↦ (Bivariate.swap F).natDegree).sum =
      (Bivariate.swap P).natDegree :=
    (natDegree_swap_eq_of_eq_C_mul_multiset_prod hPeq hc0 hs_ne).symm
  -- Split `Ω` into `Ω₀` (where `c` vanishes, giving zero fibers) and `Ω₁` (where `c` is nonzero).
  let Ω₀ : Finset (K × K) := Ω.filter fun p ↦ c.eval p.2 = 0
  let Ω₁ : Finset (K × K) := Ω.filter fun p ↦ ¬ c.eval p.2 = 0
  have hcard_split : Ω.card = Ω₀.card + Ω₁.card :=
    (Finset.card_filter_add_card_filter_not (s := Ω) (p := fun p : K × K ↦ c.eval p.2 = 0)).symm
  have hΩ₀_le : Ω₀.card ≤ c.natDegree := card_filter_eval_comp_eq_zero_le hc0 hinj
  -- On `Ω₁`, every specialized factor and hence `P.map (evalRingHom p.2)` is nonzero, so
  -- fiber multiplicity at `p.1` splits as the sum over `F ∈ s`.
  have hpt : ∀ p ∈ Ω₁, k ≤ (s.map fun F ↦ (F.map (evalRingHom p.2)).rootMultiplicity p.1).sum := by
    intro p hp
    have hpΩ : p ∈ Ω := (Finset.mem_filter.mp hp).1
    have hcp : c.eval p.2 ≠ 0 := (Finset.mem_filter.mp hp).2
    have hFmap_ne : ∀ F ∈ s, F.map (evalRingHom p.2) ≠ 0 := fun F hF ↦
      ((hs F hF).1.isPrimitive (hs F hF).2.ne').map_evalRingHom_ne_zero p.2
    have hPmap_ne : P.map (evalRingHom p.2) ≠ 0 :=
      (map_ne_zero_iff_of_eq_C_mul_multiset_prod hPeq).mpr ⟨hcp, hFmap_ne⟩
    rw [← rootMultiplicity_map_eq_sum hPeq hPmap_ne]
    exact (le_rootMultiplicity_iff hPmap_ne).mpr (hvan p hpΩ)
  -- Bound each irreducible factor `F ∈ s` on `Ω₁` via the resultant multiplicity estimate.
  have hF_bound : ∀ F ∈ s,
      ∑ p ∈ Ω₁, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
        M * (F.natDegree + (Bivariate.swap F).natDegree) +
          2 * F.natDegree * (Bivariate.swap F).natDegree := fun F hF ↦
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ Ω)).trans
      (sum_rootMultiplicity_le_of_squarefree_of_zero_bound (hs F hF).1.squarefree hinj
        (hsz F (hs F hF).1 (hs F hF).2))
  -- Aggregate over `F ∈ s` and combine the `Ω₀` and `Ω₁` bounds.
  set sX := (s.map natDegree).sum
  set sY := (s.map fun F ↦ (Bivariate.swap F).natDegree).sum
  have hΩ₁_bound : k * Ω₁.card ≤ M * (sX + sY) + 2 * sX * sY :=
    mul_card_le_of_sum_rootMultiplicity_le hpt hF_bound
  rw [hcard_split]
  exact mul_card_add_le_of_split hΩ₀_le hΩ₁_bound (hdegX_sum.le.trans hdX)
    (hdegY_sum.le.trans ((natDegree_swap_le_iff P dY).mpr hdY))

/-- Over a commutative ring of characteristic zero without zero divisors, `(X - C x) ^ k`
divides the fiber `P.map (evalRingHom y)` if and only if the first `k` outer iterated
derivatives of `P` vanish at `(x, y)` (including when the fiber vanishes identically). -/
theorem X_sub_C_pow_dvd_map_evalRingHom_iff_forall_evalEval_iterate_derivative_eq_zero
    {K : Type*} [CommRing K] [NoZeroDivisors K] [CharZero K]
    {P : K[X][X]} {x y : K} {k : ℕ} :
    (X - C x) ^ k ∣ P.map (evalRingHom y) ↔
      ∀ i < k, (derivative^[i] P).evalEval y x = 0 := by
  rw [X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero]
  refine forall₂_congr fun i _ ↦ ?_
  have hi : (Nat.factorial i : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  rw [← mul_eq_zero_iff_left hi, ← eval_iterate_derivative_eq_factorial_mul,
    iterate_derivative_map, map_evalRingHom_eval]

/-- **Bivariate vanishing criterion on a sheared grid.** Let `P : K[X][X]` over a GCD domain of
characteristic zero be evaluated at `(x, y)` via `P.evalEval y x = (P.map (evalRingHom y)).eval x`,
with first-coordinate (outer) natural degree `P.natDegree ≤ dX` and second-coordinate (inner)
coefficient natural degrees `(P.coeff i).natDegree ≤ dY`. Let `M` be a `2 × 2` matrix over `K` with
nonzero determinant such that `Prod.snd ∘ Matrix.toLinProd M` is injective on `S × S`. If
`P.map (evalRingHom (Matrix.toLinProd M q).2)` vanishes to order at least `k` at
`(Matrix.toLinProd M q).1` for all `q ∈ S ×ˢ S`, and
`S.card * dX + max k S.card * dY + 2 * dX * dY < k * S.card ^ 2`, then `P = 0`. -/
theorem eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd {K : Type*} [CommRing K] [IsDomain K]
    [IsGCDMonoid K] [CharZero K]
    {P : K[X][X]} {dX dY k : ℕ}
    (hdX : P.natDegree ≤ dX) (hdY : ∀ i, (P.coeff i).natDegree ≤ dY)
    {S : Finset K} {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det ≠ 0)
    (hinj : Set.InjOn (Prod.snd ∘ Matrix.toLinProd M) (S ×ˢ S : Finset (K × K)))
    (hvan : ∀ q ∈ S ×ˢ S,
      (X - C (Matrix.toLinProd M q).1) ^ k ∣
        P.map (evalRingHom (Matrix.toLinProd M q).2))
    (hlt : S.card * dX + max k S.card * dY + 2 * dX * dY < k * S.card ^ 2) :
    P = 0 := by
  classical
  by_contra hP
  let Ω : Finset (K × K) := (S ×ˢ S).image (Matrix.toLinProd M)
  have hΩ_card : Ω.card = S.card ^ 2 := by
    rw [Finset.card_image_of_injOn hinj.of_comp, Finset.card_product, sq]
  have hΩ_inj : Set.InjOn Prod.snd (Ω : Set (K × K)) := by
    simpa [Ω] using hinj.image_of_comp
  have hvanΩ : ∀ p ∈ Ω, (X - C p.1) ^ k ∣ P.map (evalRingHom p.2) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hvan q hq
  have hbound := mul_card_le_of_forall_X_sub_C_pow_dvd hP hdX hdY hΩ_inj
    (fun F hF _ ↦ card_filter_evalEval_eq_zero_linearGrid_le_of_natDegree_le hdet hF.ne_zero le_rfl
      ((natDegree_swap_le_iff F _).mp le_rfl))
    hvanΩ
  rw [hΩ_card] at hbound
  omega

end VanishingEstimates

end Polynomial
