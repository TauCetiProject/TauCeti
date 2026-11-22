/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import TauCeti.Algebra.Polynomial.Bivariate.SchwartzZippel
import TauCeti.Algebra.Polynomial.Bivariate.Basic
import TauCeti.Algebra.Polynomial.Bivariate.Factorization
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.Multiplicity

/-!
# Bivariate polynomial vanishing estimates

Throughout this file, a bivariate polynomial `P : K[X][X]` is evaluated at a point `(x, y) : K × K`
via `P.evalEval y x = (P.map (evalRingHom y)).eval x`. Accordingly, the first coordinate `x` enters
the outer polynomial variable (bounded by `P.natDegree`, denoted `dX` below) and the second
coordinate `y` enters the inner coefficient polynomials (bounded by
`∀ i, (P.coeff i).natDegree ≤ dY`).
Note that this reverses the `R[X][Y]` variable naming convention used for algebraic factorization in
`TauCeti.Algebra.Polynomial.Bivariate.Factorization`.

Whenever the fixed-degree resultant `F.resultant F.derivative F.natDegree (F.natDegree - 1)` is
nonzero over an integral domain `K` (in particular, when `F` is irreducible over a GCD domain of
characteristic zero), summing `(F.map (evalRingHom p.2)).rootMultiplicity p.1` over a finite set
`Ω` with distinct second coordinates is bounded by the zero count of `F` in `Ω` plus
`(2 * F.natDegree - 1) * dY` (`Polynomial.sum_rootMultiplicity_le_of_resultant_deriv_ne_zero` and
`Polynomial.sum_rootMultiplicity_le_of_irreducible`). By Mathlib's convention
`(0 : K[X]).rootMultiplicity a = 0`, an identically zero fiber `F.map (evalRingHom p.2) = 0`
contributes `0` to the sum, not an unbounded vanishing order (in contrast to divisibility by every
power `(X - C p.1) ^ k`).

Factoring an arbitrary nonzero polynomial `P : K[X][X]` over a characteristic-zero unique
factorization domain into a coefficient-ring factor in `K[X]` and a multiset of irreducible factors
of positive outer natural degree (`Polynomial.exists_C_mul_multiset_prod_irreducible`), and
applying `Polynomial.sum_rootMultiplicity_le_of_irreducible` to each irreducible factor, yields a
general bivariate vanishing estimate on any finite point set having both distinct second
coordinates and a Schwartz–Zippel zero bound on irreducible positive-degree factors
(`Polynomial.mul_card_le_of_forall_X_sub_C_pow_dvd`).

Specializing to the image of a Cartesian grid `S × S` under `Polynomial.linearGridMap M` for a
`2 × 2` matrix `M` with nonzero determinant over `K`
(`Polynomial.card_filter_eval_eq_zero_linearGrid_le`) whose second linear form separates grid
points yields a vanishing criterion on sheared grids
(`Polynomial.eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd`).

## Main results

* `Polynomial.sum_rootMultiplicity_le_of_resultant_deriv_ne_zero`: sum of fiberwise root
  multiplicities over a set with distinct second coordinates whenever the fixed-degree resultant
  with the derivative is nonzero.
* `Polynomial.sum_rootMultiplicity_le_of_irreducible`: sum of fiberwise root multiplicities of an
  irreducible bivariate polynomial over a set with distinct second coordinates in characteristic
  zero.
* `Polynomial.mul_card_le_of_forall_X_sub_C_pow_dvd`: abstract bivariate multiplicity bound
  requiring distinct second coordinates and a Schwartz–Zippel zero bound on irreducible factors.
* `Polynomial.eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd`: vanishing criterion on a sheared
  grid `(S ×ˢ S).image (linearGridMap M)` for a `2 × 2` matrix `M` with nonzero determinant.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026, Appendix A.
* T. Tao, *A sketch of the proof of non-existence of Siegel zeroes*, blog post, 2026.
-/

public section

open Finset

namespace Polynomial

section IrreducibleBound

/-- **Sum of fiberwise root multiplicities when the fixed-degree resultant is nonzero.**
Over an integral domain `K`, if `F : K[X][X]` has nonzero fixed-degree resultant
`F.resultant F.derivative F.natDegree (F.natDegree - 1) ≠ 0` and every coefficient `F.coeff i` has
natural degree at most `dY`, then the sum of `(F.map (evalRingHom p.2)).rootMultiplicity p.1` over
a finite set `Ω` of points with distinct second coordinates is bounded by the number of zeros of `F`
in `Ω` (`F.evalEval p.2 p.1 = 0`) plus `(2 * F.natDegree - 1) * dY`.

By Mathlib's convention `(0 : K[X]).rootMultiplicity a = 0`, any point `p ∈ Ω` whose fiber
`F.map (evalRingHom p.2)` vanishes identically contributes `0` to the sum rather than an unbounded
vanishing order (in contrast to divisibility by every power `(X - C p.1) ^ k`). -/
theorem sum_rootMultiplicity_le_of_resultant_deriv_ne_zero {K : Type*} [CommRing K] [IsDomain K]
    [DecidableEq K] {F : K[X][X]}
    (hres : F.resultant F.derivative F.natDegree (F.natDegree - 1) ≠ 0)
    {dY : ℕ} (hdY : ∀ i, (F.coeff i).natDegree ≤ dY)
    {Ω : Finset (K × K)} (hinj : Set.InjOn Prod.snd (Ω : Set (K × K))) :
    ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      (Ω.filter fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card +
        (2 * F.natDegree - 1) * dY := by
  set res := F.resultant F.derivative F.natDegree (F.natDegree - 1)
  have hres_deg : res.natDegree ≤ (2 * F.natDegree - 1) * dY := by
    have hder_deg : ∀ i ≤ F.natDegree - 1, (F.derivative.coeff i).natDegree ≤ dY := by
      intro i _
      rw [coeff_derivative]
      exact (natDegree_mul_le).trans (by simpa [natDegree_natCast] using hdY (i + 1))
    calc res.natDegree ≤ F.natDegree * dY + (F.natDegree - 1) * dY :=
          natDegree_resultant_le (fun i _ ↦ hdY i) hder_deg
      _ = (2 * F.natDegree - 1) * dY := by
          rw [← add_mul]
          congr 1
          omega
  let Z : Finset (K × K) := Ω.filter fun p ↦ F.evalEval p.2 p.1 = 0
  have hsum_eq : ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 =
      ∑ p ∈ Z, (F.map (evalRingHom p.2)).rootMultiplicity p.1 := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ Ω) fun p hp hpZ ↦ ?_
    have hne : (F.map (evalRingHom p.2)).eval p.1 ≠ 0 := by
      rw [map_evalRingHom_eval]
      simpa [Z, hp] using hpZ
    exact rootMultiplicity_eq_zero hne
  have hsum_Z : ∑ p ∈ Z, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      Z.card + ∑ p ∈ Z, res.rootMultiplicity p.2 := by
    calc ∑ p ∈ Z, (F.map (evalRingHom p.2)).rootMultiplicity p.1
        ≤ ∑ p ∈ Z, (1 + res.rootMultiplicity p.2) :=
          Finset.sum_le_sum fun _ _ ↦
            rootMultiplicity_le_one_add_rootMultiplicity_resultant_deriv hres
      _ = Z.card + ∑ p ∈ Z, res.rootMultiplicity p.2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hinjZ : Set.InjOn Prod.snd (Z : Set (K × K)) :=
    hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ Ω))
  have hsum_res : ∑ p ∈ Z, res.rootMultiplicity p.2 ≤ res.natDegree := by
    rw [← Finset.sum_image (f := fun b ↦ res.rootMultiplicity b) (g := Prod.snd) hinjZ]
    exact sum_rootMultiplicity_le_natDegree res (Z.image Prod.snd)
  exact hsum_eq.le.trans (hsum_Z.trans (Nat.add_le_add_left (hsum_res.trans hres_deg) Z.card))

/-- **Sum of fiberwise root multiplicities of an irreducible bivariate polynomial.**
Over a GCD domain of characteristic zero, if `F : K[X][X]` is irreducible and every coefficient
`F.coeff i` has natural degree at most `dY`, then the sum of
`(F.map (evalRingHom p.2)).rootMultiplicity p.1` over a finite set `Ω` of points with distinct
second coordinates is bounded by the number of zeros of `F` in `Ω` (`F.evalEval p.2 p.1 = 0`) plus
`(2 * F.natDegree - 1) * dY`.

When `0 < F.natDegree`, every inner-variable specialization `F.map (evalRingHom p.2)` is nonzero by
`Polynomial.IsPrimitive.map_evalRingHom_ne_zero`. -/
theorem sum_rootMultiplicity_le_of_irreducible {K : Type*} [CommRing K] [IsDomain K]
    [IsGCDMonoid K] [CharZero K] [DecidableEq K]
    {F : K[X][X]} (hF : Irreducible F)
    {dY : ℕ} (hdY : ∀ i, (F.coeff i).natDegree ≤ dY)
    {Ω : Finset (K × K)} (hinj : Set.InjOn Prod.snd (Ω : Set (K × K))) :
    ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      (Ω.filter fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card +
        (2 * F.natDegree - 1) * dY :=
  sum_rootMultiplicity_le_of_resultant_deriv_ne_zero
    (resultant_deriv_ne_zero_of_squarefree hF.squarefree) hdY hinj

end IrreducibleBound

section VanishingHelpers

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

end VanishingHelpers

section VanishingEstimates

/-- **Abstract bivariate multiplicity bound.** Let `P : K[X][X]` be nonzero over a unique
factorization domain of characteristic zero, where point evaluation at `(x, y)` is
`P.evalEval y x = (P.map (evalRingHom y)).eval x`, `dX` bounds the first-coordinate (outer)
natural degree `P.natDegree`, and `dY` bounds the second-coordinate (inner) coefficient natural
degrees `(P.coeff i).natDegree`. If `Ω` is a finite set of points satisfying both distinct second
coordinates and a Schwartz–Zippel zero bound with parameter `M` on irreducible factors of positive
outer natural degree, and `P.map (evalRingHom p.2)` vanishes to order at least `k` at `p.1` for
every `p ∈ Ω`, then `k * Ω.card ≤ M * dX + max k M * dY + 2 * dX * dY`. -/
theorem mul_card_le_of_forall_X_sub_C_pow_dvd {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [CharZero K] [DecidableEq K]
    {P : K[X][X]} (hP : P ≠ 0) {dX dY : ℕ}
    (hdX : P.natDegree ≤ dX) (hdY : ∀ i, (P.coeff i).natDegree ≤ dY)
    {Ω : Finset (K × K)} (hinj : Set.InjOn Prod.snd (Ω : Set (K × K)))
    {M k : ℕ}
    (hsz : ∀ F : K[X][X], Irreducible F → 0 < F.natDegree →
      (Ω.filter fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card ≤
        M * (F.natDegree + (Bivariate.swap F).natDegree))
    (hvan : ∀ p ∈ Ω, (X - C p.1) ^ k ∣ P.map (evalRingHom p.2)) :
    k * Ω.card ≤ M * dX + max k M * dY + 2 * dX * dY := by
  obtain ⟨c, s, hc0, hs, hPeq⟩ := exists_C_mul_multiset_prod_irreducible P hP
  have hs_ne : ∀ F ∈ s, F ≠ 0 := fun F hF ↦ (hs F hF).1.ne_zero
  have hdegX_sum : (s.map natDegree).sum = P.natDegree :=
    (natDegree_eq_sum_of_eq_C_mul_multiset_prod hPeq hc0 hs_ne).symm
  have hdegY_sum : c.natDegree + (s.map fun F ↦ (Bivariate.swap F).natDegree).sum =
      (Bivariate.swap P).natDegree :=
    (natDegree_swap_eq_of_eq_C_mul_multiset_prod hPeq hc0 hs_ne).symm
  let Ω₀ : Finset (K × K) := Ω.filter fun p ↦ c.eval p.2 = 0
  let Ω₁ : Finset (K × K) := Ω.filter fun p ↦ ¬ c.eval p.2 = 0
  have hcard_split : Ω.card = Ω₀.card + Ω₁.card :=
    (Finset.card_filter_add_card_filter_not (s := Ω) (p := fun p : K × K ↦ c.eval p.2 = 0)).symm
  have hΩ₀_le : Ω₀.card ≤ c.natDegree := card_filter_eval_comp_eq_zero_le hc0 hinj
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
  have hF_bound : ∀ F ∈ s,
      ∑ p ∈ Ω₁, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
        M * (F.natDegree + (Bivariate.swap F).natDegree) +
          2 * F.natDegree * (Bivariate.swap F).natDegree := by
    intro F hF
    have hcoeffF : ∀ i, (F.coeff i).natDegree ≤ (Bivariate.swap F).natDegree :=
      (natDegree_swap_le_iff F _).mp le_rfl
    calc ∑ p ∈ Ω₁, (F.map (evalRingHom p.2)).rootMultiplicity p.1
        ≤ ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ Ω)
      _ ≤ (Ω.filter fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card +
            (2 * F.natDegree - 1) * (Bivariate.swap F).natDegree :=
          sum_rootMultiplicity_le_of_irreducible (hs F hF).1 hcoeffF hinj
      _ ≤ M * (F.natDegree + (Bivariate.swap F).natDegree) +
            2 * F.natDegree * (Bivariate.swap F).natDegree := by
          have h1 := hsz F (hs F hF).1 (hs F hF).2
          have h2 : (2 * F.natDegree - 1) * (Bivariate.swap F).natDegree ≤
              2 * F.natDegree * (Bivariate.swap F).natDegree :=
            Nat.mul_le_mul_right _ (Nat.sub_le _ _)
          omega
  set sX := (s.map natDegree).sum
  set sY := (s.map fun F ↦ (Bivariate.swap F).natDegree).sum
  have hΩ₁_bound : k * Ω₁.card ≤ M * (sX + sY) + 2 * sX * sY :=
    mul_card_le_of_sum_rootMultiplicity_le hpt hF_bound
  have hsX_le : sX ≤ dX := hdegX_sum.le.trans hdX
  have hc_sY_le : c.natDegree + sY ≤ dY :=
    hdegY_sum.le.trans ((natDegree_swap_le_iff P dY).mpr hdY)
  have hsY_le : sY ≤ dY := le_trans (Nat.le_add_left _ _) hc_sY_le
  calc k * Ω.card = k * Ω₀.card + k * Ω₁.card := by rw [hcard_split, mul_add]
    _ ≤ k * c.natDegree + (M * (sX + sY) + 2 * sX * sY) :=
        add_le_add (Nat.mul_le_mul_left k hΩ₀_le) hΩ₁_bound
    _ ≤ max k M * c.natDegree + (M * sX + max k M * sY + 2 * sX * sY) := by
        have h1 : k * c.natDegree ≤ max k M * c.natDegree :=
          Nat.mul_le_mul_right _ (le_max_left k M)
        have h2 : M * sY ≤ max k M * sY := Nat.mul_le_mul_right _ (le_max_right k M)
        rw [mul_add]
        omega
    _ = M * sX + max k M * (c.natDegree + sY) + 2 * sX * sY := by ring
    _ ≤ M * dX + max k M * dY + 2 * dX * dY := by
        have h1 : M * sX ≤ M * dX := Nat.mul_le_mul_left M hsX_le
        have h2 : max k M * (c.natDegree + sY) ≤ max k M * dY :=
          Nat.mul_le_mul_left _ hc_sY_le
        have h3 : 2 * sX * sY ≤ 2 * dX * dY :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hsX_le) hsY_le
        omega

/-- **Bivariate vanishing criterion on a sheared grid.** Let `P : K[X][X]` over a unique
factorization domain of characteristic zero be evaluated at `(x, y)` via
`P.evalEval y x = (P.map (evalRingHom y)).eval x`, with first-coordinate (outer) natural degree
`P.natDegree ≤ dX` and second-coordinate (inner) coefficient natural degrees
`(P.coeff i).natDegree ≤ dY`. Let `M` be a `2 × 2` matrix over `K` with nonzero determinant such
that `Prod.snd ∘ linearGridMap M` is injective on `S × S`. If
`P.map (evalRingHom (linearGridMap M q).2)` vanishes to order at least `k` at
`(linearGridMap M q).1` for all `q ∈ S ×ˢ S`, and
`S.card * dX + max k S.card * dY + 2 * dX * dY < k * S.card ^ 2`, then `P = 0`. -/
theorem eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [CharZero K]
    {P : K[X][X]} {dX dY k : ℕ}
    (hdX : P.natDegree ≤ dX) (hdY : ∀ i, (P.coeff i).natDegree ≤ dY)
    {S : Finset K} {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det ≠ 0)
    (hinj : Set.InjOn (Prod.snd ∘ linearGridMap M) (S ×ˢ S : Finset (K × K)))
    (hvan : ∀ q ∈ S ×ˢ S,
      (X - C (linearGridMap M q).1) ^ k ∣ P.map (evalRingHom (linearGridMap M q).2))
    (hlt : S.card * dX + max k S.card * dY + 2 * dX * dY < k * S.card ^ 2) :
    P = 0 := by
  classical
  by_contra hP
  let Ω : Finset (K × K) := (S ×ˢ S).image (linearGridMap M)
  have hΩ_card : Ω.card = S.card ^ 2 := by
    rw [Finset.card_image_of_injOn hinj.of_comp, Finset.card_product, sq]
  have hΩ_inj : Set.InjOn Prod.snd (Ω : Set (K × K)) := by
    simpa [Ω] using hinj.image_of_comp
  have hvanΩ : ∀ p ∈ Ω, (X - C p.1) ^ k ∣ P.map (evalRingHom p.2) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hvan q hq
  have hbound := mul_card_le_of_forall_X_sub_C_pow_dvd hP hdX hdY hΩ_inj
    (fun F hF _ ↦ card_filter_eval_eq_zero_linearGrid_le hdet hF.ne_zero le_rfl
      ((natDegree_swap_le_iff F _).mp le_rfl))
    hvanΩ
  rw [hΩ_card] at hbound
  omega

end VanishingEstimates

end Polynomial
