/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Algebra.Polynomial.Bivariate
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Resultant multiplicity bounds and bivariate vanishing estimates

For a bivariate polynomial `f ∈ R[Y][X]`, a root `a` of multiplicity `k` in the fiber
`f(X, b)` makes the first `k - 1` rows of the shifted Sylvester matrix of `f` and `∂_X f`
divisible by `Y - b`, so `(Y - b) ^ (k - 1)` divides the `X`-resultant
`Res_X(f, ∂_X f)` (`Polynomial.X_sub_C_pow_dvd_resultant_deriv`). Combined with the
coefficient-degree bound `Polynomial.natDegree_resultant_le` on Sylvester determinants,
this controls the sum of fiberwise root multiplicities of an irreducible bivariate polynomial
over a finite set of points with distinct second coordinates
(`Polynomial.sum_rootMultiplicity_le_of_irreducible`).

Factoring an arbitrary nonzero polynomial `P ∈ K[Y][X]` over a field of characteristic zero
into its `Y`-content and irreducible factors of positive `X`-degree yields a general
bivariate vanishing estimate on any point set satisfying a Schwartz–Zippel zero bound
(`Polynomial.mul_card_le_of_forall_X_sub_C_pow_dvd`), and in particular on the image of a
Cartesian grid `S × S` under an invertible linear map whose second coordinate separates
grid points (`Polynomial.eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd`).

## Main results

* `Polynomial.X_sub_C_pow_dvd_resultant_deriv`: `(X - C b) ^ (k - 1)` divides the resultant
  of `f` and `f.derivative` whenever `(X - C a) ^ k` divides the specialization of `f` at `b`.
* `Polynomial.rootMultiplicity_le_one_add_rootMultiplicity_resultant_deriv`: the fiberwise
  root multiplicity at `(a, b)` is at most `1` plus the root multiplicity of the resultant at `b`.
* `Polynomial.resultant_deriv_ne_zero_of_squarefree`: a squarefree polynomial of positive
  degree over a GCD domain of characteristic zero has nonzero resultant with its derivative.
* `Polynomial.sum_rootMultiplicity_le_of_irreducible`: sum of fiberwise root multiplicities of
  an irreducible bivariate polynomial over a set with distinct second coordinates.
* `Polynomial.mul_card_le_of_forall_X_sub_C_pow_dvd`: abstract bivariate multiplicity bound
  from a Schwartz–Zippel hypothesis.
* `Polynomial.eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd`: vanishing criterion on a sheared
  grid `M (S × S)`.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026, Appendix A.
* T. Tao, *A sketch of the proof of non-existence of Siegel zeroes*, blog post, 2026.
-/

public section

open Finset

namespace Polynomial

section MultiplicityDivisibility

variable {R : Type*} [CommRing R]

/-- Base case of the resultant multiplicity divisibility at `(a, b) = (0, 0)`: if `X` divides the
first `k` coefficients of `f : R[X][X]`, then `X` divides every entry in the first `k - 1` rows
of `sylvester f f.derivative`, so `X ^ (k - 1)` divides each summand of the determinant and hence
divides the resultant. -/
private theorem X_pow_dvd_resultant_deriv_of_forall_dvd (f : R[X][X]) {k : ℕ}
    (hk : k - 1 ≤ f.natDegree + (f.natDegree - 1)) (hcoeff : ∀ i < k, X ∣ f.coeff i) :
    X ^ (k - 1) ∣ f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
  set m := f.natDegree
  set n := f.natDegree - 1
  have hrow : ∀ (i j : Fin (m + n)), (i : ℕ) < k - 1 → X ∣ sylvester f f.derivative m n i j := by
    intro i j hi
    by_cases hj : (j : ℕ) < m
    · rw [sylvester_apply_of_lt f f.derivative i j hj]
      split_ifs with h
      · rw [coeff_derivative]
        exact dvd_mul_of_dvd_left (hcoeff ((i : ℕ) - j + 1) (by omega)) _
      · exact dvd_zero _
    · rw [sylvester_apply_of_le f f.derivative i j (Nat.le_of_not_lt hj)]
      split_ifs with h
      · exact hcoeff ((i : ℕ) + m - j) (by omega)
      · exact dvd_zero _
  rw [resultant, Matrix.det_apply]
  refine Finset.dvd_sum fun σ _ ↦ ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine dvd_mul_of_dvd_right ?_ _
  let T : Finset (Fin (m + n)) := Finset.univ.filter fun j ↦ (σ j : ℕ) < k - 1
  have hcard : T.card = k - 1 := by
    have hbij : T.card = (Finset.univ.filter fun i : Fin (m + n) ↦ (i : ℕ) < k - 1).card := by
      refine Finset.card_bij (fun j _ ↦ σ j) ?_ ?_ ?_
      · intro j hj; simpa [T] using hj
      · intro j₁ _ j₂ _ h; exact σ.injective h
      · intro i hi
        refine ⟨σ.symm i, ?_, by simp⟩
        simpa [T] using hi
    rw [hbij]
    have hcard_lt : (Finset.univ.filter fun i : Fin (m + n) ↦ (i : ℕ) < k - 1).card =
        (Finset.range (k - 1)).card := by
      refine Finset.card_bij (fun i _ ↦ (i : ℕ)) ?_ ?_ ?_
      · intro i hi; simpa using hi
      · intro i₁ _ i₂ _ h; exact Fin.ext h
      · intro t ht
        have ht' : t < k - 1 := Finset.mem_range.mp ht
        exact ⟨⟨t, lt_of_lt_of_le ht' hk⟩, by simp [ht'], rfl⟩
    rw [hcard_lt, Finset.card_range]
  have hdvd_T : X ^ (k - 1) ∣ ∏ j ∈ T, sylvester f f.derivative m n (σ j) j := by
    calc X ^ (k - 1) = ∏ _j ∈ T, X := by rw [Finset.prod_const, hcard]
      _ ∣ ∏ j ∈ T, sylvester f f.derivative m n (σ j) j :=
        Finset.prod_dvd_prod_of_dvd _ _ fun j hj ↦ hrow (σ j) j (Finset.mem_filter.mp hj).2
  exact hdvd_T.trans
    (Finset.prod_dvd_prod_of_subset T Finset.univ
      (fun j ↦ sylvester f f.derivative m n (σ j) j) (Finset.subset_univ T))

/-- Translating the outer variable by `a` preserves the resultant of `f` and `f.derivative` at
the formal degree bounds `f.natDegree` and `f.natDegree - 1`, over any commutative ring. -/
private theorem resultant_taylor_deriv (f : R[X][X]) (a : R) :
    (taylor (C a) f).resultant (taylor (C a) f).derivative f.natDegree (f.natDegree - 1) =
      f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
  have hder : (taylor (C a) f).derivative = taylor (C a) f.derivative := by
    simp [taylor_apply, derivative_comp]
  rw [hder]
  calc
    (taylor (C a) f).resultant (taylor (C a) f.derivative) f.natDegree (f.natDegree - 1)
      = f.leadingCoeff ^ (f.natDegree - 1 - f.derivative.natDegree) *
          (taylor (C a) f).resultant (taylor (C a) f.derivative) := by
        conv_lhs => rw [← Nat.add_sub_of_le (natDegree_derivative_le f)]
        rw [resultant_add_right_deg _ _ _ _ _ (by simp), coeff_taylor_natDegree]
        simp only [natDegree_taylor]
    _ = f.leadingCoeff ^ (f.natDegree - 1 - f.derivative.natDegree) *
          f.resultant f.derivative := by rw [resultant_taylor]
    _ = f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
        conv_rhs => rw [← Nat.add_sub_of_le (natDegree_derivative_le f)]
        rw [resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]

/-- **Resultant multiplicity divisibility.** If `(X - C a) ^ k` divides the specialization of a
bivariate polynomial `f : R[X][X]` at `b` (with `k - 1 ≤ f.natDegree + (f.natDegree - 1)`),
then `(X - C b) ^ (k - 1)` divides `Res_X(f, f.derivative)`. -/
theorem X_sub_C_pow_dvd_resultant_deriv (f : R[X][X]) {a b : R} {k : ℕ}
    (hk : k - 1 ≤ f.natDegree + (f.natDegree - 1))
    (hdvd : (X - C a) ^ k ∣ f.map (evalRingHom b)) :
    (X - C b) ^ (k - 1) ∣ f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
  let φ : R[X] →+* R[X] := eval₂RingHom C (X + C b)
  let ψ : R[X] →+* R[X] := eval₂RingHom C (X - C b)
  have hψφ_comp : ψ.comp φ = RingHom.id R[X] := by
    apply Polynomial.ringHom_ext <;> simp [φ, ψ]
  have hψφ : ∀ g : R[X], ψ (φ g) = g := RingHom.congr_fun hψφ_comp
  have hφ_inj : Function.Injective φ := Function.LeftInverse.injective hψφ
  let f₁ : R[X][X] := f.map φ
  have hf₁_deg : f₁.natDegree = f.natDegree := natDegree_map_eq_of_injective hφ_inj f
  let f₂ : R[X][X] := taylor (C a) f₁
  have hf₂_deg : f₂.natDegree = f.natDegree := by
    rw [natDegree_taylor, hf₁_deg]
  have heval0 : (evalRingHom (0 : R)).comp φ = evalRingHom b := by
    ext <;> simp [φ]
  have hf₁_eval0 : f₁.map (evalRingHom 0) = f.map (evalRingHom b) := by
    rw [Polynomial.map_map, heval0]
  have hf₂_eval0 : f₂.map (evalRingHom 0) = (f.map (evalRingHom b)).comp (X + C a) := by
    rw [← hf₁_eval0]
    simp only [f₂, taylor_apply, map_comp, Polynomial.map_add, map_X, map_C, coe_evalRingHom,
      eval_C]
  have hX_pow_dvd : X ^ k ∣ f₂.map (evalRingHom 0) := by
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨q.comp (X + C a), ?_⟩
    rw [hf₂_eval0, hq, mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right]
  have hcoeff : ∀ i < k, X ∣ f₂.coeff i := by
    intro i hi
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    have h0 : (f₂.map (evalRingHom 0)).coeff i = 0 := by
      obtain ⟨q, hq⟩ := hX_pow_dvd
      rw [hq, coeff_X_pow_mul']
      simp [not_le.mpr hi]
    rwa [coeff_map, coe_evalRingHom] at h0
  have hdvd_res₂ : X ^ (k - 1) ∣ f₂.resultant f₂.derivative f₂.natDegree (f₂.natDegree - 1) :=
    X_pow_dvd_resultant_deriv_of_forall_dvd f₂ (by rwa [hf₂_deg]) hcoeff
  have hres_eq : f₂.resultant f₂.derivative f₂.natDegree (f₂.natDegree - 1) =
      φ (f.resultant f.derivative f.natDegree (f.natDegree - 1)) := by
    rw [hf₂_deg, ← hf₁_deg, resultant_taylor_deriv f₁ a, hf₁_deg]
    dsimp only [f₁]
    rw [derivative_map, resultant_map_map]
  rw [hres_eq] at hdvd_res₂
  have hdvd_ψ : ψ (X ^ (k - 1)) ∣ ψ (φ (f.resultant f.derivative f.natDegree (f.natDegree - 1))) :=
    _root_.map_dvd ψ hdvd_res₂
  rw [hψφ, map_pow] at hdvd_ψ
  simpa [ψ] using hdvd_ψ

/-- Over an integral domain `R`, if the `X`-resultant of `f : R[X][X]` and `f.derivative` is
nonzero and the fiber `f(X, b)` is nonzero, then the root multiplicity of `f(X, b)` at `a` is
at most `1` plus the root multiplicity of `Res_X(f, f.derivative)` at `b`. -/
theorem rootMultiplicity_le_one_add_rootMultiplicity_resultant_deriv [IsDomain R]
    {f : R[X][X]} {a b : R}
    (hres : f.resultant f.derivative f.natDegree (f.natDegree - 1) ≠ 0)
    (hfb : f.map (evalRingHom b) ≠ 0) :
    (f.map (evalRingHom b)).rootMultiplicity a ≤
      1 + (f.resultant f.derivative f.natDegree (f.natDegree - 1)).rootMultiplicity b := by
  set k := (f.map (evalRingHom b)).rootMultiplicity a
  have hk_eq : ((X - C a) ^ k).natDegree = k := by
    rw [(monic_X_sub_C a).natDegree_pow k, natDegree_X_sub_C, mul_one]
  have hk_le_deg : k ≤ f.natDegree := by
    rw [← hk_eq]
    exact (natDegree_le_of_dvd (pow_rootMultiplicity_dvd _ a) hfb).trans natDegree_map_le
  have hk : k - 1 ≤ f.natDegree + (f.natDegree - 1) := by omega
  have hdvd := X_sub_C_pow_dvd_resultant_deriv f hk (pow_rootMultiplicity_dvd _ a)
  have hle : k - 1 ≤ (f.resultant f.derivative f.natDegree (f.natDegree - 1)).rootMultiplicity b :=
    (le_rootMultiplicity_iff hres).mpr hdvd
  omega

/-- Over a GCD domain of characteristic zero, a squarefree polynomial of positive degree has
nonzero resultant with its derivative. -/
theorem resultant_deriv_ne_zero_of_squarefree {D : Type*} [CommRing D] [IsDomain D]
    [IsGCDMonoid D] [CharZero D] {f : D[X]} (hf : Squarefree f) (hdeg : 0 < f.natDegree) :
    f.resultant f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
  rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp hdeg)]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp))
    (leadingCoeff_ne_zero.mpr hf.ne_zero)) hf.discr_ne_zero

end MultiplicityDivisibility

section BivariateVanishing

/-- **Sum of fiberwise root multiplicities of an irreducible bivariate polynomial.**
Over a GCD domain of characteristic zero, the sum of `(F(X, p.2)).rootMultiplicity p.1` over a
finite set `Ω` of points with distinct second coordinates is bounded by the number of zeros of `F`
in `Ω` plus `(2 * F.natDegree - 1) * dY`. -/
theorem sum_rootMultiplicity_le_of_irreducible {K : Type*} [CommRing K] [IsDomain K]
    [IsGCDMonoid K] [CharZero K] [DecidableEq K]
    {F : K[X][X]} (hF : Irreducible F) (hdeg : 0 < F.natDegree)
    {dY : ℕ} (hdY : ∀ i, (F.coeff i).natDegree ≤ dY)
    {Ω : Finset (K × K)} (hinj : Set.InjOn Prod.snd (Ω : Set (K × K))) :
    ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      (Ω.filter fun p : K × K ↦ (F.map (evalRingHom p.2)).eval p.1 = 0).card +
        (2 * F.natDegree - 1) * dY := by
  set res := F.resultant F.derivative F.natDegree (F.natDegree - 1)
  have hres_ne : res ≠ 0 := resultant_deriv_ne_zero_of_squarefree hF.squarefree hdeg
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
  let Z : Finset (K × K) := Ω.filter fun p ↦ (F.map (evalRingHom p.2)).eval p.1 = 0
  have hsum_eq : ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 =
      ∑ p ∈ Z, (F.map (evalRingHom p.2)).rootMultiplicity p.1 := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ Ω) fun p hp hpZ ↦ ?_
    have hne : (F.map (evalRingHom p.2)).eval p.1 ≠ 0 := by
      simpa [Z, hp] using hpZ
    exact rootMultiplicity_eq_zero hne
  have hsum_Z : ∑ p ∈ Z, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      Z.card + ∑ p ∈ Z, res.rootMultiplicity p.2 := by
    calc ∑ p ∈ Z, (F.map (evalRingHom p.2)).rootMultiplicity p.1
        ≤ ∑ p ∈ Z, (1 + res.rootMultiplicity p.2) := by
          refine Finset.sum_le_sum fun p _ ↦ ?_
          exact rootMultiplicity_le_one_add_rootMultiplicity_resultant_deriv hres_ne
            (map_evalRingHom_ne_zero_of_irreducible hF hdeg p.2)
      _ = Z.card + ∑ p ∈ Z, res.rootMultiplicity p.2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hsum_res : ∑ p ∈ Z, res.rootMultiplicity p.2 ≤ res.natDegree :=
    sum_rootMultiplicity_snd_le_natDegree res (Finset.filter_subset _ Ω) hinj
  exact hsum_eq.le.trans (hsum_Z.trans (Nat.add_le_add_left (hsum_res.trans hres_deg) Z.card))

/-- **Abstract bivariate multiplicity bound.** Let `P : K[X][X]` be nonzero over a field of
characteristic zero, with `X`-degree at most `dX` and `Y`-degree at most `dY`. If `Ω` is a
finite set of points with distinct second coordinates satisfying a Schwartz–Zippel bound with
parameter `M`, and `P(X, p.2)` vanishes to order at least `k` at `p.1` for every `p ∈ Ω`, then
`k * Ω.card ≤ M * dX + max k M * dY + 2 * dX * dY`. -/
theorem mul_card_le_of_forall_X_sub_C_pow_dvd {K : Type*} [Field K] [CharZero K] [DecidableEq K]
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
  have hprod_ne : l.prod ≠ 0 := List.prod_ne_zero (fun h0 ↦ hl_ne 0 h0 rfl)
  have hdegX_sum : (l.map natDegree).sum = P.natDegree := by
    rw [hPeq, natDegree_C_mul hc0]
    simpa using (natDegree_multiset_prod (l : Multiset K[X][X])
      (by simpa using fun h0 ↦ hl_ne 0 h0 rfl)).symm
  have hdegY_sum : c.natDegree + (l.map fun F ↦ (Bivariate.swap F).natDegree).sum =
      (Bivariate.swap P).natDegree := by
    have hswap_prod : (Bivariate.swap l.prod).natDegree =
        (l.map fun F ↦ (Bivariate.swap F).natDegree).sum := by
      rw [map_list_prod]
      simpa [List.map_map, Function.comp_def] using
        natDegree_multiset_prod (↑(l.map Bivariate.swap) : Multiset K[X][X])
          (by simpa using fun h0 ↦ hl_ne 0 h0 rfl)
    rw [hPeq, natDegree_swap_mul (C_ne_zero.mpr hc0) hprod_ne, natDegree_swap_C, hswap_prod]
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
  have hpt : ∀ p ∈ Ω₁, k ≤ (l.map fun F ↦ (F.map (evalRingHom p.2)).rootMultiplicity p.1).sum := by
    intro p hp
    have hcp : c.eval p.2 ≠ 0 := (Finset.mem_filter.mp hp).2
    have hFmap_ne : ∀ F ∈ l, F.map (evalRingHom p.2) ≠ 0 := fun F hF ↦
      map_evalRingHom_ne_zero_of_irreducible (hl F hF).1 (hl F hF).2 p.2
    have hmap_prod_ne : l.prod.map (evalRingHom p.2) ≠ 0 :=
      map_list_prod_ne_zero (evalRingHom p.2) l hFmap_ne
    have hPmap_ne : P.map (evalRingHom p.2) ≠ 0 := by
      rw [hPeq, Polynomial.map_mul, map_C]
      exact mul_ne_zero (C_ne_zero.mpr (by simpa using hcp)) hmap_prod_ne
    have hle_rm : k ≤ (P.map (evalRingHom p.2)).rootMultiplicity p.1 :=
      (le_rootMultiplicity_iff hPmap_ne).mpr (hvan p (Finset.mem_filter.mp hp).1)
    rw [hPeq, Polynomial.map_mul, map_C,
      rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (by simpa using hcp)) hmap_prod_ne)]
      at hle_rm
    rw [coe_evalRingHom, rootMultiplicity_eq_zero (by simpa using hcp), zero_add,
      rootMultiplicity_map_list_prod (evalRingHom p.2) p.1 l hFmap_ne] at hle_rm
    exact hle_rm
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
          sum_rootMultiplicity_le_of_irreducible (hl F hF).1 (hl F hF).2 hcoeffF hinj
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

/-- Pull a bivariate polynomial `F : K[X][X]` back along a `2 × 2` matrix `M` into
`MvPolynomial (Fin 2) K`. -/
private noncomputable def linearPullback {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) :
    K[X][X] →+* MvPolynomial (Fin 2) K :=
  eval₂RingHom
    (eval₂RingHom MvPolynomial.C
      (MvPolynomial.C (M 1 0) * MvPolynomial.X 0 + MvPolynomial.C (M 1 1) * MvPolynomial.X 1))
    (MvPolynomial.C (M 0 0) * MvPolynomial.X 0 + MvPolynomial.C (M 0 1) * MvPolynomial.X 1)

private theorem linearPullback_X {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) :
    linearPullback M X =
      MvPolynomial.C (M 0 0) * MvPolynomial.X 0 + MvPolynomial.C (M 0 1) * MvPolynomial.X 1 := by
  simp [linearPullback]

private theorem linearPullback_C_X {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) :
    linearPullback M (C X) =
      MvPolynomial.C (M 1 0) * MvPolynomial.X 0 + MvPolynomial.C (M 1 1) * MvPolynomial.X 1 := by
  simp [linearPullback]

private theorem linearPullback_C_C {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K)
    (c : K) : linearPullback M (C (C c)) = MvPolynomial.C c := by
  simp [linearPullback]

private theorem eval_linearPullback {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K)
    (F : K[X][X]) (v : Fin 2 → K) :
    MvPolynomial.eval v (linearPullback M F) =
      (F.map (evalRingHom (M 1 0 * v 0 + M 1 1 * v 1))).eval (M 0 0 * v 0 + M 0 1 * v 1) := by
  have hhom : (MvPolynomial.eval v).comp (linearPullback M) =
      (evalRingHom (M 0 0 * v 0 + M 0 1 * v 1)).comp
        (mapRingHom (evalRingHom (M 1 0 * v 0 + M 1 1 * v 1))) := by
    apply Polynomial.ringHom_ext
    · intro p
      have hC : ((MvPolynomial.eval v).comp (linearPullback M)).comp C =
          evalRingHom (M 1 0 * v 0 + M 1 1 * v 1) := by
        apply Polynomial.ringHom_ext <;> simp [linearPullback]
      simpa using RingHom.congr_fun hC p
    · simp [linearPullback]
  exact RingHom.congr_fun hhom F

private theorem totalDegree_linearPullback_le {K : Type*} [CommRing K]
    (M : Matrix (Fin 2) (Fin 2) K) (F : K[X][X]) {a b : ℕ}
    (ha : F.natDegree ≤ a) (hb : ∀ i, (F.coeff i).natDegree ≤ b) :
    (linearPullback M F).totalDegree ≤ a + b := by
  rcases subsingleton_or_nontrivial K with hsub | _
  · rw [Subsingleton.elim (linearPullback M F) 0, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  have hlin : ∀ c₀ c₁ : K,
      (MvPolynomial.C c₀ * MvPolynomial.X 0 + MvPolynomial.C c₁ * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
    intro c₀ c₁
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])
  rw [F.as_sum_support_C_mul_X_pow, map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun r hr ↦ ?_)
  have hr_le : r ≤ a := (le_natDegree_of_mem_supp r hr).trans ha
  rw [map_mul, map_pow]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hX_pow : (linearPullback M X ^ r).totalDegree ≤ r := by
    refine (MvPolynomial.totalDegree_pow _ r).trans ?_
    simpa [linearPullback_X] using Nat.mul_le_mul_left r (hlin (M 0 0) (M 0 1))
  have hC_deg : (linearPullback M (C (F.coeff r))).totalDegree ≤ b := by
    rw [(F.coeff r).as_sum_support_C_mul_X_pow, map_sum, map_sum]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs ↦ ?_)
    have hs_le : s ≤ b := (le_natDegree_of_mem_supp s hs).trans (hb r)
    rw [map_mul, map_pow, map_mul, map_pow, linearPullback_C_C, linearPullback_C_X]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_pow _ s).trans ?_
    exact (Nat.mul_le_mul_left s (hlin (M 1 0) (M 1 1))).trans (by omega)
  omega

private theorem linearPullback_injective {K : Type*} [Field K] {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det ≠ 0) : Function.Injective (linearPullback M) := by
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet)
  let N := M⁻¹
  let invHom : MvPolynomial (Fin 2) K →+* K[X][X] :=
    MvPolynomial.eval₂Hom (C.comp C) fun i ↦
      C (C (N i 0)) * X + C (C (N i 1)) * C X
  have hmul_entry : ∀ i j : Fin 2,
      M i 0 * N 0 j + M i 1 * N 1 j = (1 : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    have h := congr_fun (congr_fun hmul i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_two, N] using h
  have hinv_lin : ∀ i : Fin 2,
      invHom (MvPolynomial.C (M i 0) * MvPolynomial.X 0 +
        MvPolynomial.C (M i 1) * MvPolynomial.X 1) = if i = 0 then X else C X := by
    intro i
    simp only [invHom, map_add, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      RingHom.comp_apply]
    have h0 := hmul_entry i 0
    have h1 := hmul_entry i 1
    have hre :
        C (C (M i 0)) * (C (C (N 0 0)) * X + C (C (N 0 1)) * C X) +
        C (C (M i 1)) * (C (C (N 1 0)) * X + C (C (N 1 1)) * C X) =
        C (C (M i 0 * N 0 0 + M i 1 * N 1 0)) * X +
        C (C (M i 0 * N 0 1 + M i 1 * N 1 1)) * C X := by
      simp only [map_add, map_mul]
      ring
    rw [hre, h0, h1]
    fin_cases i <;> simp [Matrix.one_apply]
  have hleft_comp : invHom.comp (linearPullback M) = RingHom.id K[X][X] := by
    apply Polynomial.ringHom_ext
    · intro p
      have hC : (invHom.comp (linearPullback M)).comp C = C := by
        apply Polynomial.ringHom_ext
        · intro c; simp [invHom, linearPullback]
        · simpa [linearPullback_C_X] using hinv_lin 1
      exact RingHom.congr_fun hC p
    · simpa [linearPullback_X] using hinv_lin 0
  exact Function.LeftInverse.injective (g := invHom) fun F ↦ RingHom.congr_fun hleft_comp F

/-- Schwartz–Zippel zero bound pulled back along an invertible `2 × 2` linear map on `S × S`. -/
private theorem card_filter_eval_eq_zero_linearGrid_le {K : Type*} [Field K] [DecidableEq K]
    {S : Finset K} (hS : 0 < S.card) {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det ≠ 0)
    (hg_inj : Set.InjOn (fun q : K × K ↦ (M 0 0 * q.1 + M 0 1 * q.2, M 1 0 * q.1 + M 1 1 * q.2))
      (S ×ˢ S : Finset (K × K)))
    {F : K[X][X]} (hF : F ≠ 0) {a b : ℕ}
    (ha : F.natDegree ≤ a) (hb : ∀ i, (F.coeff i).natDegree ≤ b) :
    (((S ×ˢ S).image fun q : K × K ↦ (M 0 0 * q.1 + M 0 1 * q.2, M 1 0 * q.1 + M 1 1 * q.2)).filter
      fun p : K × K ↦ (F.map (evalRingHom p.2)).eval p.1 = 0).card ≤ S.card * (a + b) := by
  let g : K × K → K × K := fun q ↦ (M 0 0 * q.1 + M 0 1 * q.2, M 1 0 * q.1 + M 1 1 * q.2)
  have hpull_ne : linearPullback M F ≠ 0 := fun h0 ↦
    hF (linearPullback_injective hdet (by rwa [map_zero]))
  have hcard_eq :
      ((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
          MvPolynomial.eval v (linearPullback M F) = 0).card =
        (((S ×ˢ S).image g).filter fun p : K × K ↦
          (F.map (evalRingHom p.2)).eval p.1 = 0).card := by
    refine Finset.card_bij (fun v _ ↦ g (v 0, v 1)) ?_ ?_ ?_
    · intro v hv
      have hvS := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hv).1
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(v 0, v 1), Finset.mem_product.mpr ⟨hvS 0, hvS 1⟩, rfl⟩, ?_⟩
      rw [← eval_linearPullback M F v]
      exact (Finset.mem_filter.mp hv).2
    · intro v₁ hv₁ v₂ hv₂ h
      have hv₁S := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hv₁).1
      have hv₂S := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hv₂).1
      have hq : (v₁ 0, v₁ 1) = (v₂ 0, v₂ 1) :=
        hg_inj (Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hv₁S 0, hv₁S 1⟩))
          (Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hv₂S 0, hv₂S 1⟩)) h
      ext i
      fin_cases i
      · exact congrArg Prod.fst hq
      · exact congrArg Prod.snd hq
    · intro p hp
      obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp).1
      rw [Finset.mem_product] at hqS
      refine ⟨![q.1, q.2], Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ ?_, ?_⟩, rfl⟩
      · fin_cases i
        · exact hqS.1
        · exact hqS.2
      · rw [eval_linearPullback]
        exact (Finset.mem_filter.mp hp).2
  rw [← hcard_eq]
  have hsz_nnrat := MvPolynomial.schwartz_zippel_totalDegree hpull_ne S
  have hS_ne : (S.card : NNRat) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  have hnnrat_le :
      (((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
          MvPolynomial.eval v (linearPullback M F) = 0).card : NNRat) ≤
        (S.card : NNRat) * ((linearPullback M F).totalDegree : NNRat) := by
    have h := mul_le_mul_of_nonneg_right hsz_nnrat (pow_nonneg (Nat.cast_nonneg S.card) 2)
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hS_ne)] at h
    have hrhs : ((linearPullback M F).totalDegree : NNRat) / (S.card : NNRat) *
        (S.card : NNRat) ^ 2 = (S.card : NNRat) * ((linearPullback M F).totalDegree : NNRat) := by
      rw [sq, ← mul_assoc, div_mul_cancel₀ _ hS_ne, mul_comm]
    rwa [hrhs] at h
  have hnat_le :
      ((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
        MvPolynomial.eval v (linearPullback M F) = 0).card ≤
        S.card * (linearPullback M F).totalDegree := by
    exact_mod_cast hnnrat_le
  exact hnat_le.trans (Nat.mul_le_mul_left S.card (totalDegree_linearPullback_le M F ha hb))

/-- **Bivariate vanishing criterion on a sheared grid.** Let `P : K[X][X]` over a field of
characteristic zero have `X`-degree at most `dX` and `Y`-degree at most `dY`. Let `M` be an
invertible `2 × 2` matrix over `K` whose second linear form is injective on `S × S`. If
`P(X, M₁₀ x + M₁₁ y)` vanishes to order at least `k` at `M₀₀ x + M₀₁ y` for all `x, y ∈ S`,
and `S.card * dX + max k S.card * dY + 2 * dX * dY < k * S.card ^ 2`, then `P = 0`. -/
theorem eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd {K : Type*} [Field K] [CharZero K]
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
  have hg_inj : Set.InjOn g (S ×ˢ S : Finset (K × K)) := by
    intro q₁ hq₁ q₂ hq₂ h
    rw [Finset.mem_coe, Finset.mem_product] at hq₁ hq₂
    have h2 : M 1 0 * q₁.1 + M 1 1 * q₁.2 = M 1 0 * q₂.1 + M 1 1 * q₂.2 := congrArg Prod.snd h
    exact Prod.ext_iff.mpr (hinj q₁.1 hq₁.1 q₁.2 hq₁.2 q₂.1 hq₂.1 q₂.2 hq₂.2 h2)
  let Ω : Finset (K × K) := (S ×ˢ S).image g
  have hΩ_card : Ω.card = S.card ^ 2 := by
    rw [Finset.card_image_of_injOn hg_inj, Finset.card_product, sq]
  have hΩ_inj : Set.InjOn Prod.snd (Ω : Set (K × K)) := by
    intro p₁ hp₁ p₂ hp₂ h
    obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp₁)
    obtain ⟨q₂, hq₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp₂)
    rw [Finset.mem_product] at hq₁ hq₂
    have hq : q₁ = q₂ := Prod.ext_iff.mpr (hinj q₁.1 hq₁.1 q₁.2 hq₁.2 q₂.1 hq₂.1 q₂.2 hq₂.2 h)
    rw [hq]
  have hvanΩ : ∀ p ∈ Ω, (X - C p.1) ^ k ∣ P.map (evalRingHom p.2) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_product] at hq
    exact hvan q.1 hq.1 q.2 hq.2
  have hbound := mul_card_le_of_forall_X_sub_C_pow_dvd hP hdX hdY hΩ_inj
    (fun F hF _ _ ha hb ↦ card_filter_eval_eq_zero_linearGrid_le hS_pos hdet hg_inj hF ha hb) hvanΩ
  rw [hΩ_card] at hbound
  omega

end BivariateVanishing

end Polynomial
