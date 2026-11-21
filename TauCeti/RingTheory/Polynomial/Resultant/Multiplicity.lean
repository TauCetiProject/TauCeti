/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultant degree bounds and bivariate multiplicity estimates

Translating the indeterminate by a constant leaves the resultant unchanged at any valid degree
bounds (`Polynomial.resultant_comp_X_add_C`): translation induces a unitriangular automorphism on
each degree-bounded polynomial space `R[X]_k` that intertwines the Sylvester maps.

Over a univariate polynomial ring `R[X]`, expanding the determinant of the Sylvester matrix bounds
the parameter degree of `resultant f g m n` by `n * a + m * b` when the coefficients of `f` have
degree at most `a` and those of `g` have degree at most `b` (`Polynomial.natDegree_resultant_le`).
In particular, the resultant `Res_z(f, ∂_z f)` at bounds `m` and `m - 1` has parameter degree at
most `(2 * m - 1) * a` (`Polynomial.natDegree_resultant_derivative_le`).

Combining translation invariance with row divisibility in the Sylvester matrix gives a parameter
divisibility bound for multiple roots: if the specialization `f(·, y)` has a root `x` of
multiplicity `m`, then `(X - C y) ^ (m - 1)` divides `Res_z(f, ∂_z f)` in `R[X]`
(`Polynomial.pow_rootMultiplicity_sub_one_dvd_resultant_derivative`). After translating `x` to `0`,
all entries in the first `m - 1` rows of the Sylvester matrix are divisible by `X - C y`.

Over a field `K` of characteristic zero, iterating this bound over primitive irreducible factors
produces a bivariate multiplicity estimate (`Polynomial.sum_rootMultiplicity_le` and
`Polynomial.mul_card_le_of_forall_iterate_derivative_eval_eq_zero`): on a finite point set with
distinct second coordinates satisfying a linear zero-count bound `≤ N * (deg_z g + deg_{z'} g)`,
a nonzero polynomial `F : K[X][X]` vanishing to order `N` in `z` at every point satisfies
`N * |ι| ≤ N * deg_z F + N * deg_{z'} F + 2 * deg_z F * deg_{z'} F`.

## Main results

* `Polynomial.resultant_comp_X_add_C`: invariance of the resultant under `X ↦ X + C c`.
* `Polynomial.natDegree_resultant_le`, `Polynomial.natDegree_resultant_derivative_le`:
  parameter-degree bounds for resultants over `R[X]`.
* `Polynomial.pow_rootMultiplicity_sub_one_dvd_resultant_derivative`,
  `Polynomial.rootMultiplicity_sub_one_le_rootMultiplicity_resultant_derivative`:
  `(X - C y) ^ (m - 1) ∣ Res_z(f, ∂_z f)` when `x` is a root of `f(·, y)` of multiplicity `m`.
* `Polynomial.sum_rootMultiplicity_le`: sum-of-multiplicities bound for bivariate polynomials.
* `Polynomial.mul_card_le_of_forall_iterate_derivative_eval_eq_zero`: bivariate multiplicity
  estimate on a point set with distinct second coordinates and a linear zero-count bound.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026, §6 and Appendix A (resultant
  degree and multiplicity bounds for bivariate polynomials).
* OpenAI, *Uniform exclusion of Landau–Siegel zeros*, October 2026.
-/

public section

open scoped Polynomial

namespace Polynomial

/-! ### Translation invariance of the resultant -/

section Translate

variable {R : Type*} [CommRing R]

/-- **Translation invariance of the resultant.** Translating both polynomials by `X ↦ X + C c`
preserves their resultant at any valid degree bounds `f.natDegree ≤ m` and `g.natDegree ≤ n`. -/
theorem resultant_comp_X_add_C (f g : R[X]) (c : R) {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (f.comp (X + C c)).resultant (g.comp (X + C c)) m n = f.resultant g m n := by
  have hf' : (f.comp (X + C c)).natDegree ≤ m := by
    rw [← taylor_apply]; exact (natDegree_taylor f c).le.trans hf
  have hg' : (g.comp (X + C c)).natDegree ≤ n := by
    rw [← taylor_apply]; exact (natDegree_taylor g c).le.trans hg
  let bm := degreeLT.basis R m
  let bn := degreeLT.basis R n
  let b₁ := (bm.prod bn).reindex finSumFinEquiv
  let bmn := degreeLT.basis R (m + n)
  let Tm := (taylorLinearEquiv c m).toLinearMap
  let Tn := (taylorLinearEquiv c n).toLinearMap
  let Tmn := (taylorLinearEquiv c (m + n)).toLinearMap
  have hcomm :
      sylvesterMap (f.comp (X + C c)) (g.comp (X + C c)) hf' hg' ∘ₗ Tm.prodMap Tn =
        Tmn ∘ₗ sylvesterMap f g hf hg :=
    LinearMap.ext fun ⟨p, q⟩ ↦ Subtype.ext <| by
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, Tm, Tn, Tmn,
        LinearEquiv.coe_coe, taylorLinearEquiv_apply_coe, sylvesterMap_apply_coe, ← taylor_apply]
      change taylor c f * (taylorEquiv c : R[X] →ₗ[R] R[X]) ↑q +
          taylor c g * (taylorEquiv c : R[X] →ₗ[R] R[X]) ↑p =
        (taylorEquiv c : R[X] →ₗ[R] R[X]) (f * ↑q + g * ↑p)
      simp [coe_taylorEquiv, taylor_apply, add_comp, mul_comp]
  have hmat := congrArg (LinearMap.toMatrix b₁ bmn) hcomm
  rw [LinearMap.toMatrix_comp b₁ b₁ bmn, LinearMap.toMatrix_comp b₁ bmn bmn,
    toMatrix_sylvesterMap', toMatrix_sylvesterMap'] at hmat
  have hdet := congrArg Matrix.det hmat
  have hre : LinearMap.toMatrix b₁ b₁ (Tm.prodMap Tn) =
      (LinearMap.toMatrix (bm.prod bn) (bm.prod bn) (Tm.prodMap Tn)).reindex
        finSumFinEquiv finSumFinEquiv := by
    ext i j
    simp [b₁, LinearMap.toMatrix_apply, Matrix.reindex_apply]
  have hprod_det : (LinearMap.toMatrix b₁ b₁ (Tm.prodMap Tn)).det = 1 := by
    rw [hre, Matrix.det_reindex_self, LinearMap.toMatrix_prodMap, Matrix.det_fromBlocks_zero₂₁,
      LinearMap.det_toMatrix, LinearMap.det_toMatrix, det_taylorLinearEquiv_toLinearMap,
      det_taylorLinearEquiv_toLinearMap, mul_one]
  rw [Matrix.det_mul, Matrix.det_mul, hprod_det, mul_one, ← resultant, ← resultant,
    LinearMap.det_toMatrix, det_taylorLinearEquiv_toLinearMap, one_mul] at hdet
  exact hdet

end Translate

/-! ### Parameter-degree bounds for resultants -/

section DegreeBound

variable {R : Type*} [CommRing R]

/-- **Parameter-degree bound for the resultant.** For bivariate polynomials `f, g : R[X][X]`
whose coefficients in degrees `≤ m` and `≤ n` have parameter degree at most `a` and `b`,
respectively, the resultant `f.resultant g m n` has degree at most `n * a + m * b`. -/
theorem natDegree_resultant_le {f g : R[X][X]} {m n a b : ℕ}
    (hf : ∀ i ≤ m, (f.coeff i).natDegree ≤ a)
    (hg : ∀ i ≤ n, (g.coeff i).natDegree ≤ b) :
    (f.resultant g m n).natDegree ≤ n * a + m * b := by
  rw [resultant, Matrix.det_apply]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ ↦ ?_)
  refine (natDegree_smul_le _ _).trans ?_
  rw [Fin.prod_univ_add]
  refine natDegree_mul_le.trans ?_
  have h1 : (∏ j : Fin m, f.sylvester g m n (σ (j.castAdd n)) (j.castAdd n)).natDegree ≤
      m * b := by
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ j : Fin m, (f.sylvester g m n (σ (j.castAdd n)) (j.castAdd n)).natDegree
        ≤ ∑ _j : Fin m, b := Finset.sum_le_sum fun j _ ↦ ?_
      _ = m * b := by simp
    rw [sylvester_apply_of_lt _ _ _ _ j.isLt]
    split_ifs with h
    · exact hg _ (by omega)
    · simp
  have h2 : (∏ j : Fin n, f.sylvester g m n (σ (j.natAdd m)) (j.natAdd m)).natDegree ≤
      n * a := by
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ j : Fin n, (f.sylvester g m n (σ (j.natAdd m)) (j.natAdd m)).natDegree
        ≤ ∑ _j : Fin n, a := Finset.sum_le_sum fun j _ ↦ ?_
      _ = n * a := by simp
    rw [sylvester_apply_of_le _ _ _ _ (by simp)]
    split_ifs with h
    · exact hf _ (by simp at h ⊢; omega)
    · simp
  omega

/-- Parameter-degree bound for the discriminant resultant `Res_z(f, ∂_z f)` at bounds `m` and
`m - 1`: when every coefficient of `f` up to degree `m` has parameter degree at most `a`, the
resultant has degree at most `(2 * m - 1) * a`. -/
theorem natDegree_resultant_derivative_le {f : R[X][X]} {m a : ℕ}
    (hf : ∀ i ≤ m, (f.coeff i).natDegree ≤ a) :
    (f.resultant f.derivative m (m - 1)).natDegree ≤ (2 * m - 1) * a := by
  obtain _ | m := m
  · simp
  have hg : ∀ i ≤ m, (f.derivative.coeff i).natDegree ≤ a := fun i hi ↦ by
    rw [coeff_derivative, mul_comm, show ((i : R[X]) + 1) * f.coeff (i + 1) =
      (i + 1 : ℕ) • f.coeff (i + 1) by simp [nsmul_eq_mul]]
    exact (natDegree_smul_le _ _).trans (hf (i + 1) (by omega))
  have hmul : 2 * (m + 1) - 1 = m + (m + 1) := by omega
  simpa [hmul, add_mul] using natDegree_resultant_le hf hg

end DegreeBound

/-! ### Root multiplicity and divisibility of the resultant -/

section Divisibility

private theorem pow_dvd_det_of_forall_lt_dvd {S : Type*} [CommRing S] {k r : ℕ}
    {M : Matrix (Fin k) (Fin k) S} {c : S} (hr : r ≤ k)
    (hM : ∀ i : Fin k, (i : ℕ) < r → ∀ j, c ∣ M i j) : c ^ r ∣ M.det := by
  have hdvd := Matrix.prod_dvd_det_of_dvd_row M (fun i ↦ if (i : ℕ) < r then c else 1)
    fun i j ↦ by split_ifs with hi <;> [exact hM i hi j; exact one_dvd _]
  rwa [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const,
    Fin.card_filter_val_lt, min_eq_right hr] at hdvd

/-- **Resultant divisibility from a multiple root.** If `f : R[X][X]` over a commutative ring `R`
satisfies `f.natDegree ≤ d`, and `x` is a root of the specialization `f(·, y)` of multiplicity `m`,
then `(X - C y) ^ (m - 1)` divides `Res_z(f, ∂_z f)` at degree bounds `d` and `d - 1`. -/
theorem pow_rootMultiplicity_sub_one_dvd_resultant_derivative
    {R : Type*} [CommRing R] {f : R[X][X]} {d : ℕ}
    (hf : f.natDegree ≤ d) (x y : R) :
    (X - C y) ^ ((f.map (evalRingHom y)).rootMultiplicity x - 1) ∣
      f.resultant f.derivative d (d - 1) := by
  classical
  set fy := f.map (evalRingHom y)
  set m := fy.rootMultiplicity x
  rcases le_or_gt m 1 with hm | hm
  · simp [Nat.sub_eq_zero_of_le hm]
  have hmd : m ≤ d := by
    have hle : m ≤ (fy.comp (X + C x)).natDegree := by
      have hm_eq : m = (fy.comp (X + C x)).natTrailingDegree :=
        rootMultiplicity_eq_natTrailingDegree
      exact hm_eq ▸ natTrailingDegree_le_natDegree _
    rw [← taylor_apply, natDegree_taylor] at hle
    exact (hle.trans natDegree_map_le).trans hf
  -- Translate `x` to `0`, preserving the resultant while making low coefficients vanish at `y`.
  set h := f.comp (X + C (C x))
  have hhderiv : h.derivative = f.derivative.comp (X + C (C x)) := by
    simp only [h, ← taylor_apply, taylor_derivative]
  have hres : h.resultant h.derivative d (d - 1) = f.resultant f.derivative d (d - 1) := by
    rw [hhderiv]
    exact resultant_comp_X_add_C f f.derivative (C x) hf
      ((natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1))
  have hmap : h.map (evalRingHom y) = fy.comp (X + C x) := by
    simp [h, fy, Polynomial.map_comp]
  have hcoeff {k : ℕ} (hk : k < m) : X - C y ∣ h.coeff k := by
    rw [dvd_iff_isRoot, IsRoot, ← coe_evalRingHom, ← coeff_map, hmap]
    exact coeff_eq_zero_of_lt_natTrailingDegree <| by
      rwa [← rootMultiplicity_eq_natTrailingDegree]
  rw [← hres, resultant]
  refine pow_dvd_det_of_forall_lt_dvd (by omega) fun i hi j ↦ ?_
  by_cases hj : (j : ℕ) < d
  · rw [sylvester_apply_of_lt _ _ _ _ hj]
    split_ifs with hmem
    · rw [coeff_derivative]
      exact dvd_mul_of_dvd_left (hcoeff (by omega)) _
    · exact dvd_zero _
  · rw [sylvester_apply_of_le _ _ _ _ (not_lt.mp hj)]
    split_ifs with hmem
    · exact hcoeff (by omega)
    · exact dvd_zero _

/-- When `Res_z(f, ∂_z f)` does not vanish, the root multiplicity `m` of `x` in `f(·, y)` satisfies
`m - 1 ≤ ord_y Res_z(f, ∂_z f)`. -/
theorem rootMultiplicity_sub_one_le_rootMultiplicity_resultant_derivative
    {R : Type*} [CommRing R] {f : R[X][X]} {d : ℕ}
    (hf : f.natDegree ≤ d) (hres : f.resultant f.derivative d (d - 1) ≠ 0) (x y : R) :
    (f.map (evalRingHom y)).rootMultiplicity x - 1 ≤
      (f.resultant f.derivative d (d - 1)).rootMultiplicity y :=
  (le_rootMultiplicity_iff hres).mpr
    (pow_rootMultiplicity_sub_one_dvd_resultant_derivative hf x y)

end Divisibility

/-! ### Bivariate multiplicity estimate -/

section BivariateMultiplicity

variable {K : Type*} [Field K]

private theorem coeff_coeff_swap (F : K[X][X]) (m n : ℕ) :
    ((Bivariate.swap F).coeff m).coeff n = (F.coeff n).coeff m := by
  induction F using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
    induction a using Polynomial.induction_on' with
    | add p q hp hq => simp [map_add, hp, hq]
    | monomial l r =>
      rw [Bivariate.swap_monomial_monomial, coeff_monomial_apply, coeff_monomial_apply]
      split_ifs with hm hn
      · subst hm hn; simp
      · simp [Ne.symm hn]
      · simp [Ne.symm hm]
      · simp

private theorem swap_natDegree_eq_sup (F : K[X][X]) :
    (Bivariate.swap F).natDegree = F.support.sup fun k ↦ (F.coeff k).natDegree := by
  refine le_antisymm ?_ (Finset.sup_le fun k _ ↦ natDegree_le_iff_coeff_eq_zero.mpr fun m hm ↦ ?_)
  · by_cases hF : F = 0
    · simp [hF]
    have hsw : Bivariate.swap F ≠ 0 := (map_ne_zero_iff _ (EquivLike.injective _)).mpr hF
    have hlc : (Bivariate.swap F).coeff (Bivariate.swap F).natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr hsw
    obtain ⟨n, hn⟩ := support_nonempty.mpr hlc
    rw [mem_support_iff, coeff_coeff_swap] at hn
    have hk : n ∈ F.support := mem_support_iff.mpr fun h0 ↦ hn (by simp [h0])
    exact (le_natDegree_of_ne_zero hn).trans (Finset.le_sup (f := fun k ↦ (F.coeff k).natDegree) hk)
  · rw [← coeff_coeff_swap, coeff_eq_zero_of_natDegree_lt hm, coeff_zero]

private theorem coeff_natDegree_le_swap_natDegree (F : K[X][X]) (k : ℕ) :
    (F.coeff k).natDegree ≤ (Bivariate.swap F).natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun m hm ↦ by
    rw [← coeff_coeff_swap, coeff_eq_zero_of_natDegree_lt hm, coeff_zero]

/-- A primitive polynomial over `K[X]` does not vanish identically under any specialization
`evalRingHom y`. -/
private theorem map_evalRingHom_ne_zero_of_isPrimitive {F : K[X][X]} (hF : F.IsPrimitive) (y : K) :
    F.map (evalRingHom y) ≠ 0 := by
  intro h0
  have hdvd : C (X - C y) ∣ F := by
    refine (C_dvd_iff_dvd_coeff (X - C y) F).mpr fun k ↦ ?_
    rw [dvd_iff_isRoot, IsRoot, ← coe_evalRingHom, ← coeff_map, h0, coeff_zero]
  have hdeg : (X - C y).natDegree = 0 := natDegree_eq_zero_of_isUnit (hF (X - C y) hdvd)
  simp at hdeg

/-- The sum of root multiplicities of a nonzero polynomial over an injective family of points is at
most its degree. -/
private theorem sum_rootMultiplicity_comp_le_natDegree {ι : Type*} [Fintype ι] {f : ι → K}
    (hf : Function.Injective f) {p : K[X]} :
    ∑ i : ι, p.rootMultiplicity (f i) ≤ p.natDegree := by
  classical
  rw [← Finset.sum_image (f := p.rootMultiplicity) fun _ _ _ _ h ↦ hf h]
  exact p.sum_rootMultiplicity_le_natDegree _

/-- Over a field of characteristic zero, the discriminant resultant `Res_z(F, ∂_z F)` of an
irreducible polynomial `F : K[X][X]` of positive `z`-degree is nonzero. -/
private theorem resultant_derivative_ne_zero_of_irreducible [CharZero K] {F : K[X][X]}
    (hF : Irreducible F) (hpos : 0 < F.natDegree) :
    F.resultant F.derivative F.natDegree (F.natDegree - 1) ≠ 0 := by
  have hprim : F.IsPrimitive := hF.isPrimitive hpos.ne'
  set L := FractionRing K[X]
  let φ : K[X] →+* L := algebraMap K[X] L
  have hφ : Function.Injective φ := IsFractionRing.injective K[X] L
  have hF_irr : Irreducible (F.map φ) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hF
  have hF_deg : (F.map φ).natDegree = F.natDegree := natDegree_map_eq_of_injective hφ F
  have hFd_deg : (F.derivative.map φ).natDegree = F.natDegree - 1 := by
    rw [natDegree_map_eq_of_injective hφ, natDegree_derivative]
  have hcop : IsCoprime (F.map φ) (F.derivative.map φ) := by
    rw [← derivative_map]
    exact (separable_def _).mp hF_irr.separable
  have hresL : (F.map φ).resultant (F.derivative.map φ) ≠ 0 :=
    Polynomial.resultant_ne_zero _ _ hcop
  intro h0
  apply hresL
  rw [hF_deg, hFd_deg, resultant_map_map, h0, map_zero]

/-- Base case of `sum_rootMultiplicity_le_of_isPrimitive` for an irreducible factor. -/
private theorem sum_rootMultiplicity_le_of_irreducible [CharZero K] [DecidableEq K]
    {ι : Type*} [Fintype ι] {P : ι → K × K} (hP_snd : Function.Injective fun i ↦ (P i).2) {N : ℕ}
    (hSZ : ∀ g : K[X][X], g ≠ 0 →
      (Finset.univ.filter fun i ↦ (g.map (evalRingHom (P i).2)).eval (P i).1 = 0).card ≤
        N * (g.natDegree + (Bivariate.swap g).natDegree))
    {F : K[X][X]} (hF : Irreducible F) (hpos : 0 < F.natDegree) :
    ∑ i : ι, (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
      N * F.natDegree + N * (Bivariate.swap F).natDegree +
        2 * F.natDegree * (Bivariate.swap F).natDegree := by
  set R := F.resultant F.derivative F.natDegree (F.natDegree - 1) with hRdef
  have hR0 : R ≠ 0 := resultant_derivative_ne_zero_of_irreducible hF hpos
  have hRdeg : R.natDegree ≤ 2 * F.natDegree * (Bivariate.swap F).natDegree :=
    (natDegree_resultant_derivative_le fun i _ ↦ coeff_natDegree_le_swap_natDegree F i).trans
      (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  have hpt (i : ι) :
      (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
        (if (F.map (evalRingHom (P i).2)).eval (P i).1 = 0 then 1 else 0) +
          R.rootMultiplicity (P i).2 := by
    set m := (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1
    rcases eq_or_ne m 0 with hm | hm
    · simp [hm]
    · have hroot : (F.map (evalRingHom (P i).2)).eval (P i).1 = 0 :=
        (rootMultiplicity_pos'.mp (Nat.pos_of_ne_zero hm)).2
      have hmul : m - 1 ≤ R.rootMultiplicity (P i).2 := by
        rw [hRdef]
        exact rootMultiplicity_sub_one_le_rootMultiplicity_resultant_derivative
          le_rfl hR0 (P i).1 (P i).2
      rw [ite_eq_left hroot]
      omega
  calc ∑ i : ι, (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1
      ≤ ∑ i : ι, ((if (F.map (evalRingHom (P i).2)).eval (P i).1 = 0 then 1 else 0) +
          R.rootMultiplicity (P i).2) := Finset.sum_le_sum fun i _ ↦ hpt i
    _ = (Finset.univ.filter fun i ↦ (F.map (evalRingHom (P i).2)).eval (P i).1 = 0).card +
          ∑ i : ι, R.rootMultiplicity (P i).2 := by
        rw [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
    _ ≤ N * (F.natDegree + (Bivariate.swap F).natDegree) + R.natDegree :=
        Nat.add_le_add (hSZ F hF.ne_zero) (sum_rootMultiplicity_comp_le_natDegree hP_snd)
    _ ≤ N * F.natDegree + N * (Bivariate.swap F).natDegree +
          2 * F.natDegree * (Bivariate.swap F).natDegree := by
        rw [Nat.mul_add]
        exact Nat.add_le_add_left hRdeg _

/-- A reducible primitive polynomial of positive `z`-degree factors into two primitive polynomials
of strictly smaller positive `z`-degrees. -/
private theorem exists_mul_of_not_irreducible_of_isPrimitive {F : K[X][X]}
    (hF : F.IsPrimitive) (hpos : 0 < F.natDegree) (hirr : ¬ Irreducible F) :
    ∃ A B, F = A * B ∧ A.IsPrimitive ∧ B.IsPrimitive ∧ 0 < A.natDegree ∧ 0 < B.natDegree := by
  have hnu : ¬ IsUnit F := fun hu ↦ hpos.ne' (natDegree_eq_zero_of_isUnit hu)
  rw [irreducible_iff, not_and_or] at hirr
  have hred := hirr.resolve_left (not_not.mpr hnu)
  push Not at hred
  obtain ⟨A, B, hFAB, hAu, hBu⟩ := hred
  have hAp : A.IsPrimitive := isPrimitive_of_dvd hF ⟨B, hFAB⟩
  have hBp : B.IsPrimitive := isPrimitive_of_dvd hF ⟨A, by rw [hFAB, mul_comm]⟩
  have hdeg_pos {Q : K[X][X]} (hQp : Q.IsPrimitive) (hQu : ¬ IsUnit Q) : 0 < Q.natDegree := by
    by_contra h0
    rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (not_lt.mp h0))] at hQp hQu
    exact hQu (isUnit_C.mpr (hQp (Q.coeff 0) dvd_rfl))
  exact ⟨A, B, hFAB, hAp, hBp, hdeg_pos hAp hAu, hdeg_pos hBp hBu⟩

/-- Sum-of-multiplicities bound for primitive bivariate polynomials. -/
private theorem sum_rootMultiplicity_le_of_isPrimitive [CharZero K] [DecidableEq K]
    {ι : Type*} [Fintype ι] {P : ι → K × K}
    (hP_snd : Function.Injective fun i ↦ (P i).2) {N : ℕ}
    (hSZ : ∀ g : K[X][X], g ≠ 0 →
      (Finset.univ.filter fun i ↦ (g.map (evalRingHom (P i).2)).eval (P i).1 = 0).card ≤
        N * (g.natDegree + (Bivariate.swap g).natDegree))
    {F : K[X][X]} (hF : F.IsPrimitive) :
    ∑ i : ι, (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
      N * F.natDegree + N * (Bivariate.swap F).natDegree +
        2 * F.natDegree * (Bivariate.swap F).natDegree := by
  induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
  | ind d ih =>
    rcases eq_or_ne d 0 with rfl | hd0
    · have hconst (i : ι) : (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 = 0 := by
        have hdeg : (F.map (evalRingHom (P i).2)).natDegree = 0 :=
          Nat.eq_zero_of_le_zero (natDegree_map_le.trans hd.le)
        rw [← count_roots]
        exact Nat.eq_zero_of_le_zero
          (((Multiset.count_le_card _ _).trans (card_roots' _)).trans hdeg.le)
      simp [hconst]
    · by_cases hirr : Irreducible F
      · rw [← hd]
        exact sum_rootMultiplicity_le_of_irreducible hP_snd hSZ hirr (hd ▸ Nat.pos_of_ne_zero hd0)
      · obtain ⟨A, B, hFAB, hAp, hBp, hApos, hBpos⟩ :=
          exists_mul_of_not_irreducible_of_isPrimitive hF (hd ▸ Nat.pos_of_ne_zero hd0) hirr
        have hdeg : d = A.natDegree + B.natDegree := by
          rw [← hd, hFAB, natDegree_mul hAp.ne_zero hBp.ne_zero]
        have hpdeg : (Bivariate.swap F).natDegree =
            (Bivariate.swap A).natDegree + (Bivariate.swap B).natDegree := by
          rw [hFAB, map_mul,
            natDegree_mul ((map_ne_zero_iff _ (EquivLike.injective _)).mpr hAp.ne_zero)
              ((map_ne_zero_iff _ (EquivLike.injective _)).mpr hBp.ne_zero)]
        have hihA := ih A.natDegree (by omega) hAp rfl
        have hihB := ih B.natDegree (by omega) hBp rfl
        have hsplit : ∑ i : ι, (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 =
            (∑ i : ι, (A.map (evalRingHom (P i).2)).rootMultiplicity (P i).1) +
              ∑ i : ι, (B.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hFAB, Polynomial.map_mul, rootMultiplicity_mul
            (mul_ne_zero (map_evalRingHom_ne_zero_of_isPrimitive hAp _)
              (map_evalRingHom_ne_zero_of_isPrimitive hBp _))]
        rw [hsplit, hdeg, hpdeg]
        nlinarith

/-- **Sum-of-multiplicities bound for bivariate polynomials.** Over a field `K` of characteristic
zero, let `P : ι → K × K` have injective second coordinate and satisfy the linear zero-count bound
`#{i | g(P i) = 0} ≤ N * (deg_z g + deg_{z'} g)` for every nonzero `g : K[X][X]`. Then every
polynomial `F : K[X][X]` satisfies
`∑ i, mult_{z = (P i).1} F(z, (P i).2) ≤
  N * deg_z F + N * deg_{z'} F + 2 * deg_z F * deg_{z'} F`. -/
theorem sum_rootMultiplicity_le [CharZero K] [DecidableEq K]
    {ι : Type*} [Fintype ι] {P : ι → K × K}
    (hP_snd : Function.Injective fun i ↦ (P i).2) {N : ℕ}
    (hSZ : ∀ g : K[X][X], g ≠ 0 →
      (Finset.univ.filter fun i ↦ (g.map (evalRingHom (P i).2)).eval (P i).1 = 0).card ≤
        N * (g.natDegree + g.support.sup fun k ↦ (g.coeff k).natDegree))
    (F : K[X][X]) :
    ∑ i : ι, (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
      N * F.natDegree + N * (F.support.sup fun k ↦ (F.coeff k).natDegree) +
        2 * F.natDegree * (F.support.sup fun k ↦ (F.coeff k).natDegree) := by
  simp_rw [← swap_natDegree_eq_sup] at hSZ ⊢
  rcases eq_or_ne F 0 with rfl | hF
  · simp
  set c := F.content
  set G := F.primPart
  have hc0 : c ≠ 0 := content_eq_zero_iff.not.mpr hF
  have hpdeg : (Bivariate.swap F).natDegree = c.natDegree + (Bivariate.swap G).natDegree := by
    conv_lhs => rw [F.eq_C_content_mul_primPart]
    rw [map_mul, natDegree_mul ((map_ne_zero_iff _ (EquivLike.injective _)).mpr (C_ne_zero.mpr hc0))
        ((map_ne_zero_iff _ (EquivLike.injective _)).mpr F.isPrimitive_primPart.ne_zero),
      Bivariate.swap_C, natDegree_map_eq_of_injective C_injective]
  have hsum_le : ∑ i : ι, (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
      ∑ i : ι, (G.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 := by
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hmap : F.map (evalRingHom (P i).2) =
        C (c.eval (P i).2) * G.map (evalRingHom (P i).2) := by
      conv_lhs => rw [F.eq_C_content_mul_primPart]
      rw [Polynomial.map_mul, map_C, coe_evalRingHom]
    rw [hmap]
    by_cases hcy : c.eval (P i).2 = 0
    · simp [hcy]
    · rw [rootMultiplicity_C_mul hcy]
  have hG := sum_rootMultiplicity_le_of_isPrimitive hP_snd hSZ F.isPrimitive_primPart
  rw [hpdeg, ← F.natDegree_primPart]
  nlinarith

/-- If `F = C c * G` with `G` primitive and `∂_z^j F(x, y) = 0` for all `j < N` at a point where
`c(y) ≠ 0`, then `G(·, y)` vanishes at `x` to order at least `N`. -/
private theorem le_rootMultiplicity_primPart [CharZero K] [DecidableEq K] {F : K[X][X]} {N : ℕ}
    (hN : N ≠ 0) {x y : K} (hcy : F.content.eval y ≠ 0)
    (hvan : ∀ j < N, ((derivative^[j] F).map (evalRingHom y)).eval x = 0) :
    N ≤ (F.primPart.map (evalRingHom y)).rootMultiplicity x := by
  have hFmap : F.map (evalRingHom y) = C (F.content.eval y) * F.primPart.map (evalRingHom y) := by
    conv_lhs => rw [F.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, map_C, coe_evalRingHom]
  have hFne : F.map (evalRingHom y) ≠ 0 := by
    rw [hFmap]
    exact mul_ne_zero (C_ne_zero.mpr hcy)
      (map_evalRingHom_ne_zero_of_isPrimitive F.isPrimitive_primPart y)
  have hlt : N - 1 < (F.map (evalRingHom y)).rootMultiplicity x := by
    rw [lt_rootMultiplicity_iff_isRoot_iterate_derivative hFne]
    intro j hj
    rw [IsRoot, iterate_derivative_map]
    exact hvan j (by omega)
  rw [hFmap, rootMultiplicity_C_mul hcy] at hlt
  omega

/-- **Bivariate grid multiplicity estimate.** Over a field `K` of characteristic zero, let
`P : ι → K × K` have injective second coordinate and satisfy the linear zero-count bound
`#{i | g(P i) = 0} ≤ N * (deg_z g + deg_{z'} g)` for every nonzero `g : K[X][X]`. If a nonzero
polynomial `F : K[X][X]` satisfies `∂_z^j F(P i) = 0` for every `i : ι` and every `j < N`, then
`N * card ι ≤ N * deg_z F + N * deg_{z'} F + 2 * deg_z F * deg_{z'} F`. -/
theorem mul_card_le_of_forall_iterate_derivative_eval_eq_zero [CharZero K] [DecidableEq K]
    {ι : Type*} [Fintype ι] {P : ι → K × K} (hP_snd : Function.Injective fun i ↦ (P i).2) {N : ℕ}
    (hSZ : ∀ g : K[X][X], g ≠ 0 →
      (Finset.univ.filter fun i ↦ (g.map (evalRingHom (P i).2)).eval (P i).1 = 0).card ≤
        N * (g.natDegree + g.support.sup fun k ↦ (g.coeff k).natDegree))
    {F : K[X][X]} (hF : F ≠ 0)
    (hvan : ∀ i : ι, ∀ j < N,
      ((derivative^[j] F).map (evalRingHom (P i).2)).eval (P i).1 = 0) :
    N * Fintype.card ι ≤
      N * F.natDegree + N * (F.support.sup fun k ↦ (F.coeff k).natDegree) +
        2 * F.natDegree * (F.support.sup fun k ↦ (F.coeff k).natDegree) := by
  simp_rw [← swap_natDegree_eq_sup] at hSZ ⊢
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  set c := F.content
  set G := F.primPart
  have hc0 : c ≠ 0 := content_eq_zero_iff.not.mpr hF
  have hpdeg : (Bivariate.swap F).natDegree = c.natDegree + (Bivariate.swap G).natDegree := by
    conv_lhs => rw [F.eq_C_content_mul_primPart]
    rw [map_mul, natDegree_mul ((map_ne_zero_iff _ (EquivLike.injective _)).mpr (C_ne_zero.mpr hc0))
        ((map_ne_zero_iff _ (EquivLike.injective _)).mpr F.isPrimitive_primPart.ne_zero),
      Bivariate.swap_C, natDegree_map_eq_of_injective C_injective]
  let sGood := Finset.univ.filter fun i : ι ↦ c.eval (P i).2 ≠ 0
  let sBad := Finset.univ.filter fun i : ι ↦ c.eval (P i).2 = 0
  have hcard : Fintype.card ι = sGood.card + sBad.card := by
    simpa [sGood, sBad, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun i : ι ↦ c.eval (P i).2 ≠ 0)).symm
  have hBad : sBad.card ≤ c.natDegree := by
    calc sBad.card = ∑ _i ∈ sBad, 1 := by simp
      _ ≤ ∑ i ∈ sBad, c.rootMultiplicity (P i).2 := Finset.sum_le_sum fun i hi ↦
          (rootMultiplicity_pos hc0).mpr (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i : ι, c.rootMultiplicity (P i).2 :=
          Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _
      _ ≤ c.natDegree := sum_rootMultiplicity_comp_le_natDegree hP_snd
  have hGood : N * sGood.card ≤
      ∑ i : ι, (G.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 := by
    calc N * sGood.card = ∑ _i ∈ sGood, N := by simp [mul_comm]
      _ ≤ ∑ i ∈ sGood, (G.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 :=
          Finset.sum_le_sum fun i hi ↦
            le_rootMultiplicity_primPart hN0 (Finset.mem_filter.mp hi).2 (hvan i)
      _ ≤ ∑ i : ι, (G.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 :=
          Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _
  have hGsum := sum_rootMultiplicity_le_of_isPrimitive hP_snd hSZ F.isPrimitive_primPart
  rw [hcard, Nat.mul_add, hpdeg, ← F.natDegree_primPart]
  nlinarith

end BivariateMultiplicity

end Polynomial
