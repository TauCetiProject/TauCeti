/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import TauCeti.Algebra.Polynomial.Bivariate.Basic
import TauCeti.Algebra.Polynomial.Bivariate.Factorization
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.RingTheory.MvPolynomial.LinearSubst
import TauCeti.RingTheory.Polynomial.Resultant.Multiplicity

/-!
# Bivariate polynomial vanishing estimates

Factoring an arbitrary nonzero polynomial `P : K[X][X]` over a characteristic-zero unique
factorization domain into a coefficient-ring factor in `K[X]` and irreducible factors of positive
outer natural degree (`Polynomial.exists_C_mul_list_prod_irreducible`), and applying the resultant
multiplicity bound (`Polynomial.sum_rootMultiplicity_le_of_irreducible`) to each irreducible
factor, yields a general bivariate vanishing estimate on any finite point set having both distinct
second coordinates and a Schwartz–Zippel zero bound
(`Polynomial.mul_card_le_of_forall_X_sub_C_pow_dvd`).

Pulling a bivariate polynomial back along an invertible `2 × 2` linear map into
`MvPolynomial (Fin 2) K` (`MvPolynomial.linearSubst` composed with
`Polynomial.Bivariate.equivMvPolynomial`) transports `MvPolynomial.schwartz_zippel_totalDegree` to
the image of a Cartesian grid `S × S` (`Polynomial.card_filter_eval_eq_zero_linearGrid_le`).
Specializing to a sheared grid whose second coordinate separates grid points yields a vanishing
criterion (`Polynomial.eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd`).

## Main results

* `Polynomial.mul_card_le_of_forall_X_sub_C_pow_dvd`: abstract bivariate multiplicity bound
  requiring both distinct second coordinates and a Schwartz–Zippel zero bound.
* `Polynomial.card_filter_eval_eq_zero_linearGrid_le`: Schwartz–Zippel zero bound on the image of
  a Cartesian grid `S × S` under an invertible `2 × 2` linear map.
* `Polynomial.eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd`: vanishing criterion on a sheared
  grid `M (S × S)`.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026, Appendix A.
* T. Tao, *A sketch of the proof of non-existence of Siegel zeroes*, blog post, 2026.
-/

public section

open Finset

namespace Polynomial

section FactorizationHelpers

private theorem natDegree_eq_sum_of_C_mul_list_prod {R : Type*} [CommRing R] [IsDomain R]
    {P : R[X][X]} {c : R[X]} {l : List R[X][X]} (hc0 : c ≠ 0) (hl_ne : ∀ F ∈ l, F ≠ 0)
    (hPeq : P = C c * l.prod) :
    (l.map natDegree).sum = P.natDegree := by
  rw [hPeq, natDegree_C_mul hc0]
  simpa using (natDegree_multiset_prod (l : Multiset R[X][X])
    (by simpa using fun h0 ↦ hl_ne 0 h0 rfl)).symm

private theorem natDegree_swap_eq_add_sum_of_C_mul_list_prod {R : Type*} [CommRing R]
    [IsDomain R] {P : R[X][X]} {c : R[X]} {l : List R[X][X]} (hc0 : c ≠ 0)
    (hl_ne : ∀ F ∈ l, F ≠ 0) (hPeq : P = C c * l.prod) :
    c.natDegree + (l.map fun F ↦ (Bivariate.swap F).natDegree).sum =
      (Bivariate.swap P).natDegree := by
  have hprod_ne : l.prod ≠ 0 := List.prod_ne_zero fun h0 ↦ hl_ne 0 h0 rfl
  have hswap_prod : (Bivariate.swap l.prod).natDegree =
      (l.map fun F ↦ (Bivariate.swap F).natDegree).sum := by
    rw [map_list_prod]
    simpa [List.map_map, Function.comp_def] using
      natDegree_multiset_prod (↑(l.map Bivariate.swap) : Multiset R[X][X])
        (by simpa using fun h0 ↦ hl_ne 0 h0 rfl)
  rw [hPeq, natDegree_swap_mul (C_ne_zero.mpr hc0) hprod_ne, natDegree_swap_C, hswap_prod]

private theorem le_sum_rootMultiplicity_of_C_mul_list_prod_dvd {K : Type*} [CommRing K]
    [IsDomain K] {P : K[X][X]} {c : K[X]} {l : List K[X][X]}
    (hl : ∀ F ∈ l, Irreducible F ∧ 0 < F.natDegree) (hPeq : P = C c * l.prod)
    {a b : K} {k : ℕ} (hcp : c.eval b ≠ 0)
    (hdvd : (X - C a) ^ k ∣ P.map (evalRingHom b)) :
    k ≤ (l.map fun F ↦ (F.map (evalRingHom b)).rootMultiplicity a).sum := by
  have hFmap_ne : ∀ F ∈ l, F.map (evalRingHom b) ≠ 0 := fun F hF ↦
    map_evalRingHom_ne_zero_of_irreducible (hl F hF).1 (hl F hF).2 b
  have hmap_list_ne : ∀ p ∈ l.map (mapRingHom (evalRingHom b)), p ≠ 0 := by
    intro p hp
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hp
    simpa [coe_mapRingHom] using hFmap_ne F hF
  have hmap_prod_ne : (l.map (mapRingHom (evalRingHom b))).prod ≠ 0 :=
    List.prod_ne_zero fun h0 ↦ hmap_list_ne 0 h0 rfl
  have hPmap_eq :
      P.map (evalRingHom b) = C (c.eval b) * (l.map (mapRingHom (evalRingHom b))).prod := by
    rw [hPeq, Polynomial.map_mul, map_C, ← coe_mapRingHom, map_list_prod]
    rfl
  have hPmap_ne : P.map (evalRingHom b) ≠ 0 := by
    rw [hPmap_eq]
    exact mul_ne_zero (C_ne_zero.mpr hcp) hmap_prod_ne
  have hle_rm : k ≤ (P.map (evalRingHom b)).rootMultiplicity a :=
    (le_rootMultiplicity_iff hPmap_ne).mpr hdvd
  rw [hPmap_eq, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hcp) hmap_prod_ne),
    rootMultiplicity_eq_zero (by simpa using hcp), zero_add,
    rootMultiplicity_list_prod a _ hmap_list_ne] at hle_rm
  simpa [List.map_map, Function.comp_def, coe_mapRingHom] using hle_rm

end FactorizationHelpers

section VanishingEstimates

/-- **Abstract bivariate multiplicity bound.** Let `P : K[X][X]` be nonzero over a unique
factorization domain of characteristic zero, with outer natural degree at most `dX` and inner
coefficient natural degrees at most `dY`. If `Ω` is a finite set of points satisfying both
distinct second coordinates and a Schwartz–Zippel bound with parameter `M`, and `P(X, p.2)`
vanishes to order at least `k` at `p.1` for every `p ∈ Ω`, then
`k * Ω.card ≤ M * dX + max k M * dY + 2 * dX * dY`. -/
theorem mul_card_le_of_forall_X_sub_C_pow_dvd {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [CharZero K] [DecidableEq K]
    {P : K[X][X]} (hP : P ≠ 0) {dX dY : ℕ}
    (hdX : P.natDegree ≤ dX) (hdY : ∀ i, (P.coeff i).natDegree ≤ dY)
    {Ω : Finset (K × K)} (hinj : Set.InjOn Prod.snd (Ω : Set (K × K)))
    {M k : ℕ}
    (hsz : ∀ F : K[X][X], F ≠ 0 → ∀ a b : ℕ, F.natDegree ≤ a →
      (∀ i, (F.coeff i).natDegree ≤ b) →
      (Ω.filter fun p : K × K ↦ (F.map (evalRingHom p.2)).eval p.1 = 0).card ≤ M * (a + b))
    (hvan : ∀ p ∈ Ω, (X - C p.1) ^ k ∣ P.map (evalRingHom p.2)) :
    k * Ω.card ≤ M * dX + max k M * dY + 2 * dX * dY := by
  obtain ⟨c, l, hc0, hl, hPeq⟩ := exists_C_mul_list_prod_irreducible P hP
  have hl_ne : ∀ F ∈ l, F ≠ 0 := fun F hF ↦ (hl F hF).1.ne_zero
  have hdegX_sum := natDegree_eq_sum_of_C_mul_list_prod hc0 hl_ne hPeq
  have hdegY_sum := natDegree_swap_eq_add_sum_of_C_mul_list_prod hc0 hl_ne hPeq
  let Ω₀ : Finset (K × K) := Ω.filter fun p ↦ c.eval p.2 = 0
  let Ω₁ : Finset (K × K) := Ω.filter fun p ↦ ¬ c.eval p.2 = 0
  have hcard_split : Ω.card = Ω₀.card + Ω₁.card :=
    (Finset.card_filter_add_card_filter_not (s := Ω) (p := fun p : K × K ↦ c.eval p.2 = 0)).symm
  have hΩ₀_le : Ω₀.card ≤ c.natDegree := by
    have hinj₀ : Set.InjOn Prod.snd (Ω₀ : Set (K × K)) :=
      hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ Ω))
    rw [← Finset.card_image_of_injOn hinj₀]
    calc (Ω₀.image Prod.snd).card
        ≤ c.roots.toFinset.card := Finset.card_le_card fun b hb ↦ by
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
          exact Multiset.mem_toFinset.mpr ((mem_roots hc0).mpr (Finset.mem_filter.mp hp).2)
      _ ≤ c.roots.card := Multiset.toFinset_card_le _
      _ ≤ c.natDegree := card_roots' c
  have hpt : ∀ p ∈ Ω₁, k ≤ (l.map fun F ↦ (F.map (evalRingHom p.2)).rootMultiplicity p.1).sum :=
    fun p hp ↦ le_sum_rootMultiplicity_of_C_mul_list_prod_dvd hl hPeq
      (Finset.mem_filter.mp hp).2 (hvan p (Finset.mem_filter.mp hp).1)
  have hF_bound : ∀ F ∈ l,
      ∑ p ∈ Ω₁, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
        M * (F.natDegree + (Bivariate.swap F).natDegree) +
          2 * F.natDegree * (Bivariate.swap F).natDegree := by
    intro F hF
    have hcoeffF : ∀ i, (F.coeff i).natDegree ≤ (Bivariate.swap F).natDegree :=
      (natDegree_swap_le_iff F _).mp le_rfl
    calc ∑ p ∈ Ω₁, (F.map (evalRingHom p.2)).rootMultiplicity p.1
        ≤ ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ Ω)
      _ ≤ (Ω.filter fun p : K × K ↦ (F.map (evalRingHom p.2)).eval p.1 = 0).card +
            (2 * F.natDegree - 1) * (Bivariate.swap F).natDegree :=
          sum_rootMultiplicity_le_of_irreducible (hl F hF).1 hcoeffF hinj
      _ ≤ M * (F.natDegree + (Bivariate.swap F).natDegree) +
            2 * F.natDegree * (Bivariate.swap F).natDegree := by
          have h1 := hsz F (hl_ne F hF) F.natDegree (Bivariate.swap F).natDegree le_rfl hcoeffF
          have h2 : (2 * F.natDegree - 1) * (Bivariate.swap F).natDegree ≤
              2 * F.natDegree * (Bivariate.swap F).natDegree :=
            Nat.mul_le_mul_right _ (Nat.sub_le _ _)
          omega
  have hlin_sum : ∀ m : List K[X][X],
      (m.map fun F ↦ M * (F.natDegree + (Bivariate.swap F).natDegree) +
        2 * F.natDegree * (Bivariate.swap F).natDegree).sum =
      M * ((m.map natDegree).sum + (m.map fun F ↦ (Bivariate.swap F).natDegree).sum) +
        2 * (m.map fun F ↦ F.natDegree * (Bivariate.swap F).natDegree).sum := by
    intro m
    induction m with
    | nil => simp
    | cons F m ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  set sX := (l.map natDegree).sum
  set sY := (l.map fun F ↦ (Bivariate.swap F).natDegree).sum
  have hΩ₁_bound : k * Ω₁.card ≤ M * (sX + sY) + 2 * sX * sY := by
    calc k * Ω₁.card = ∑ _p ∈ Ω₁, k := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ Ω₁, (l.map fun F ↦ (F.map (evalRingHom p.2)).rootMultiplicity p.1).sum :=
          Finset.sum_le_sum hpt
      _ = (l.map fun F ↦ ∑ p ∈ Ω₁, (F.map (evalRingHom p.2)).rootMultiplicity p.1).sum := by
          simpa using (Multiset.sum_map_sum (m := (l : Multiset K[X][X])) (s := Ω₁)
            (f := fun F p ↦ (F.map (evalRingHom p.2)).rootMultiplicity p.1)).symm
      _ ≤ (l.map fun F ↦ M * (F.natDegree + (Bivariate.swap F).natDegree) +
            2 * F.natDegree * (Bivariate.swap F).natDegree).sum :=
          List.sum_le_sum hF_bound
      _ = M * (sX + sY) +
            2 * (l.map fun F ↦ F.natDegree * (Bivariate.swap F).natDegree).sum :=
          hlin_sum l
      _ ≤ M * (sX + sY) + 2 * (sX * sY) := by
          refine Nat.add_le_add_left (Nat.mul_le_mul_left 2 ?_) _
          exact (List.sum_le_sum fun F hF ↦ Nat.mul_le_mul_left _
            (List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _
              (List.mem_map_of_mem hF))).trans_eq
            (List.sum_map_mul_right l natDegree sY)
      _ = M * (sX + sY) + 2 * sX * sY := by ring
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

/-- Schwartz–Zippel zero bound pulled back along an invertible `2 × 2` linear map on `S × S`. -/
theorem card_filter_eval_eq_zero_linearGrid_le {K : Type*} [CommRing K] [IsDomain K]
    [DecidableEq K] {S : Finset K} (hS : 0 < S.card) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det ≠ 0) {F : K[X][X]} (hF : F ≠ 0) {a b : ℕ}
    (ha : F.natDegree ≤ a) (hb : ∀ i, (F.coeff i).natDegree ≤ b) :
    (((S ×ˢ S).image fun q : K × K ↦
        (M 0 0 * q.1 + M 0 1 * q.2, M 1 0 * q.1 + M 1 1 * q.2)).filter
      fun p : K × K ↦ (F.map (evalRingHom p.2)).eval p.1 = 0).card ≤ S.card * (a + b) := by
  let M' : Matrix (Fin 2) (Fin 2) K := M.submatrix (Equiv.swap 0 1) id
  let P' : MvPolynomial (Fin 2) K := MvPolynomial.linearSubst M' (Bivariate.equivMvPolynomial K F)
  have hdet' : M'.det ≠ 0 := by
    dsimp only [M']
    rw [Matrix.det_permute (Equiv.swap 0 1) M, Equiv.Perm.sign_swap (by decide)]
    simp [hdet]
  have hP'_ne : P' ≠ 0 := fun h0 ↦
    hF ((Bivariate.equivMvPolynomial K).injective
      (MvPolynomial.linearSubst_injective hdet' (by simpa [P'] using h0)))
  have heval : ∀ v : Fin 2 → K, MvPolynomial.eval v P' =
      (F.map (evalRingHom (M 1 0 * v 0 + M 1 1 * v 1))).eval (M 0 0 * v 0 + M 0 1 * v 1) := by
    intro v
    dsimp only [P']
    rw [MvPolynomial.eval_linearSubst, Bivariate.eval_equivMvPolynomial]
    simp [M', Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hcard_le :
      (((S ×ˢ S).image fun q : K × K ↦
          (M 0 0 * q.1 + M 0 1 * q.2, M 1 0 * q.1 + M 1 1 * q.2)).filter
        fun p : K × K ↦ (F.map (evalRingHom p.2)).eval p.1 = 0).card ≤
      ((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
        MvPolynomial.eval v P' = 0).card := by
    refine Finset.card_le_card_of_surjOn
      (fun v : Fin 2 → K ↦ (M 0 0 * v 0 + M 0 1 * v 1, M 1 0 * v 0 + M 1 1 * v 1)) ?_
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hp.1
    rw [Finset.mem_product] at hqS
    refine ⟨![q.1, q.2], Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr (Fin.forall_fin_two.mpr hqS), ?_⟩), rfl⟩
    rw [heval]
    exact hp.2
  have hsz_nnrat := MvPolynomial.schwartz_zippel_totalDegree hP'_ne S
  have hS_ne : (S.card : NNRat) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  have hnnrat_le :
      (((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
          MvPolynomial.eval v P' = 0).card : NNRat) ≤
        (S.card : NNRat) * (P'.totalDegree : NNRat) := by
    have h := mul_le_mul_of_nonneg_right hsz_nnrat (pow_nonneg (Nat.cast_nonneg S.card) 2)
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hS_ne)] at h
    have hrhs : (P'.totalDegree : NNRat) / (S.card : NNRat) * (S.card : NNRat) ^ 2 =
        (S.card : NNRat) * (P'.totalDegree : NNRat) := by
      rw [sq, ← mul_assoc, div_mul_cancel₀ _ hS_ne, mul_comm]
    rwa [hrhs] at h
  have hnat_le :
      ((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
        MvPolynomial.eval v P' = 0).card ≤ S.card * P'.totalDegree := by
    exact_mod_cast hnnrat_le
  have hdeg_le : P'.totalDegree ≤ a + b :=
    (MvPolynomial.totalDegree_linearSubst_le M' _).trans
      (Bivariate.totalDegree_equivMvPolynomial_le F ha hb)
  exact hcard_le.trans (hnat_le.trans (Nat.mul_le_mul_left S.card hdeg_le))

/-- **Bivariate vanishing criterion on a sheared grid.** Let `P : K[X][X]` over a unique
factorization domain of characteristic zero have outer natural degree at most `dX` and inner
coefficient natural degrees at most `dY`. Let `M` be a `2 × 2` matrix over `K` with nonzero
determinant whose second linear form is injective on `S × S`. If `P(X, M₁₀ x + M₁₁ y)` vanishes to
order at least `k` at `M₀₀ x + M₀₁ y` for all `x, y ∈ S`, and
`S.card * dX + max k S.card * dY + 2 * dX * dY < k * S.card ^ 2`, then `P = 0`. -/
theorem eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [CharZero K]
    {P : K[X][X]} {dX dY k : ℕ}
    (hdX : P.natDegree ≤ dX) (hdY : ∀ i, (P.coeff i).natDegree ≤ dY)
    {S : Finset K} {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det ≠ 0)
    (hinj : ∀ x₁ ∈ S, ∀ y₁ ∈ S, ∀ x₂ ∈ S, ∀ y₂ ∈ S,
      M 1 0 * x₁ + M 1 1 * y₁ = M 1 0 * x₂ + M 1 1 * y₂ → x₁ = x₂ ∧ y₁ = y₂)
    (hvan : ∀ x ∈ S, ∀ y ∈ S,
      (X - C (M 0 0 * x + M 0 1 * y)) ^ k ∣
        P.map (evalRingHom (M 1 0 * x + M 1 1 * y)))
    (hlt : S.card * dX + max k S.card * dY + 2 * dX * dY < k * S.card ^ 2) :
    P = 0 := by
  classical
  by_contra hP
  have hS_pos : 0 < S.card := by
    by_contra h0
    simp only [Nat.eq_zero_of_not_pos h0, zero_pow two_ne_zero, mul_zero, not_lt_zero] at hlt
  let g : K × K → K × K := fun q ↦ (M 0 0 * q.1 + M 0 1 * q.2, M 1 0 * q.1 + M 1 1 * q.2)
  have hsnd_inj : Set.InjOn (Prod.snd ∘ g) (S ×ˢ S : Finset (K × K)) := by
    intro q₁ hq₁ q₂ hq₂ h
    rw [Finset.mem_coe, Finset.mem_product] at hq₁ hq₂
    exact Prod.ext_iff.mpr (hinj q₁.1 hq₁.1 q₁.2 hq₁.2 q₂.1 hq₂.1 q₂.2 hq₂.2 h)
  have hg_inj : Set.InjOn g (S ×ˢ S : Finset (K × K)) := hsnd_inj.of_comp
  let Ω : Finset (K × K) := (S ×ˢ S).image g
  have hΩ_card : Ω.card = S.card ^ 2 := by
    rw [Finset.card_image_of_injOn hg_inj, Finset.card_product, sq]
  have hΩ_inj : Set.InjOn Prod.snd (Ω : Set (K × K)) := by
    simpa [Ω] using hsnd_inj.image_of_comp
  have hvanΩ : ∀ p ∈ Ω, (X - C p.1) ^ k ∣ P.map (evalRingHom p.2) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_product] at hq
    exact hvan q.1 hq.1 q.2 hq.2
  have hbound := mul_card_le_of_forall_X_sub_C_pow_dvd hP hdX hdY hΩ_inj
    (fun F hF _ _ ha hb ↦ card_filter_eval_eq_zero_linearGrid_le hS_pos hdet hF ha hb) hvanΩ
  rw [hΩ_card] at hbound
  omega

end VanishingEstimates

end Polynomial
