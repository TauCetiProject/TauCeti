/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
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

private theorem natDegree_comp_X_add_C_le (p : R[X]) (c : R) :
    (p.comp (X + C c)).natDegree ≤ p.natDegree := by
  nontriviality R
  exact natDegree_comp_le.trans (by rw [natDegree_X_add_C, mul_one])

private theorem comp_X_add_C_mem_degreeLT {p : R[X]} {k : ℕ} (c : R) (hp : p ∈ degreeLT R k) :
    p.comp (X + C c) ∈ degreeLT R k := by
  rw [mem_degreeLT] at hp ⊢
  rcases eq_or_ne p 0 with rfl | hp0
  · simp at hp ⊢
  have h0 : p.comp (X + C c) ≠ 0 := comp_X_add_C_ne_zero_iff.mpr hp0
  rw [degree_eq_natDegree hp0] at hp
  rw [degree_eq_natDegree h0]
  exact (Nat.cast_le.mpr (natDegree_comp_X_add_C_le p c)).trans_lt hp

/-- Translation `p ↦ p.comp (X + C c)` as an `R`-linear equivalence on `degreeLT R k`. -/
private noncomputable def translateDegreeLT (c : R) (k : ℕ) :
    degreeLT R k ≃ₗ[R] degreeLT R k where
  toFun p := ⟨p.1.comp (X + C c), comp_X_add_C_mem_degreeLT c p.2⟩
  map_add' p q := by ext1; simp [add_comp]
  map_smul' r p := by ext1; simp [smul_eq_C_mul, mul_comp]
  invFun p := ⟨p.1.comp (X + C (-c)), comp_X_add_C_mem_degreeLT (-c) p.2⟩
  left_inv p := by ext1; simp [comp_assoc]
  right_inv p := by ext1; simp [comp_assoc]

/-- The matrix of `translateDegreeLT c k` in the monomial basis of `degreeLT R k` is upper
triangular with `1`s on the diagonal, hence has determinant `1`. -/
private theorem det_toMatrix_translateDegreeLT (c : R) (k : ℕ) :
    (LinearMap.toMatrix (degreeLT.basis R k) (degreeLT.basis R k)
      (translateDegreeLT c k).toLinearMap).det = 1 := by
  set M := LinearMap.toMatrix (degreeLT.basis R k) (degreeLT.basis R k)
    (translateDegreeLT c k).toLinearMap
  have hM (i j : Fin k) : M i j = c ^ ((j : ℕ) - i) * (j : ℕ).choose i := by
    simp only [M, LinearMap.toMatrix_apply, degreeLT.basis_repr, LinearEquiv.coe_coe]
    change (((degreeLT.basis R k j : R[X])).comp (X + C c)).coeff i = _
    rw [degreeLT.basis_val, X_pow_comp, coeff_X_add_C_pow]
  have htri : M.BlockTriangular id := by
    intro i j hij
    have hlt : (j : ℕ) < i := hij
    rw [hM, Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_eq_one fun i _ ↦ ?_
  rw [hM, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]

/-- The block-diagonal translation automorphism on `R[X]_m × R[X]_n` has determinant `1`. -/
private theorem det_toMatrix_prodMap_translateDegreeLT (c : R) (m n : ℕ) :
    (LinearMap.toMatrix
      (((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv)
      (((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv)
      ((translateDegreeLT c m).toLinearMap.prodMap (translateDegreeLT c n).toLinearMap)).det =
        1 := by
  let bm := degreeLT.basis R m
  let bn := degreeLT.basis R n
  let Tm := (translateDegreeLT c m).toLinearMap
  let Tn := (translateDegreeLT c n).toLinearMap
  have hre : LinearMap.toMatrix ((bm.prod bn).reindex finSumFinEquiv)
      ((bm.prod bn).reindex finSumFinEquiv) (Tm.prodMap Tn) =
      (LinearMap.toMatrix (bm.prod bn) (bm.prod bn) (Tm.prodMap Tn)).reindex
        finSumFinEquiv finSumFinEquiv := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.reindex_apply]
  rw [hre, Matrix.det_reindex_self]
  have hblk : LinearMap.toMatrix (bm.prod bn) (bm.prod bn) (Tm.prodMap Tn) =
      Matrix.fromBlocks (LinearMap.toMatrix bm bm Tm) 0 0 (LinearMap.toMatrix bn bn Tn) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.prod_apply]
  rw [hblk, Matrix.det_fromBlocks_zero₂₁, det_toMatrix_translateDegreeLT c m,
    det_toMatrix_translateDegreeLT c n, mul_one]

/-- **Translation invariance of the resultant.** Translating both polynomials by `X ↦ X + C c`
preserves their resultant at any valid degree bounds `f.natDegree ≤ m` and `g.natDegree ≤ n`. -/
theorem resultant_comp_X_add_C (f g : R[X]) (c : R) {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (f.comp (X + C c)).resultant (g.comp (X + C c)) m n = f.resultant g m n := by
  have hf' : (f.comp (X + C c)).natDegree ≤ m := (natDegree_comp_X_add_C_le f c).trans hf
  have hg' : (g.comp (X + C c)).natDegree ≤ n := (natDegree_comp_X_add_C_le g c).trans hg
  let b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv
  let bmn := degreeLT.basis R (m + n)
  let Tm := (translateDegreeLT c m).toLinearMap
  let Tn := (translateDegreeLT c n).toLinearMap
  let Tmn := (translateDegreeLT c (m + n)).toLinearMap
  have hcomm :
      sylvesterMap (f.comp (X + C c)) (g.comp (X + C c)) hf' hg' ∘ₗ Tm.prodMap Tn =
        Tmn ∘ₗ sylvesterMap f g hf hg :=
    LinearMap.ext fun ⟨p, q⟩ ↦ Subtype.ext <| by
      simp [Tm, Tn, Tmn, translateDegreeLT, add_comp, mul_comp]
  have hmat := congrArg (LinearMap.toMatrix b₁ bmn) hcomm
  rw [LinearMap.toMatrix_comp b₁ b₁ bmn, LinearMap.toMatrix_comp b₁ bmn bmn,
    toMatrix_sylvesterMap', toMatrix_sylvesterMap'] at hmat
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, ← resultant, ← resultant,
    det_toMatrix_translateDegreeLT c (m + n),
    det_toMatrix_prodMap_translateDegreeLT c m n, one_mul, mul_one] at hdet
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

/-- If an element `c` divides every entry in the first `r` rows of a `k × k` matrix `M` (with
`r ≤ k`), then `c ^ r` divides `M.det`. -/
private theorem pow_dvd_det_of_forall_lt_dvd {S : Type*} [CommRing S] {k r : ℕ}
    {M : Matrix (Fin k) (Fin k) S} {c : S} (hr : r ≤ k)
    (hM : ∀ i : Fin k, (i : ℕ) < r → ∀ j, c ∣ M i j) : c ^ r ∣ M.det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.dvd_sum fun σ _ ↦ ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine dvd_mul_of_dvd_right ?_ _
  let s : Finset (Fin k) := Finset.univ.filter fun i : Fin k ↦ (i : ℕ) < r
  have hcard : s.card = r := by
    have heq : s = (Finset.range r).attach.map
        ⟨fun x ↦ ⟨x.1, (Finset.mem_range.mp x.2).trans_le hr⟩,
          fun x y h ↦ Subtype.ext (by simpa using congrArg Fin.val h)⟩ := by
      ext i
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_attach, true_and]
      exact ⟨fun hi ↦ ⟨⟨i.1, Finset.mem_range.mpr hi⟩, rfl⟩,
        fun ⟨⟨x, hx⟩, h⟩ ↦ h ▸ Finset.mem_range.mp hx⟩
    rw [heq, Finset.card_map, Finset.card_attach, Finset.card_range]
  have hprod : ∏ i : Fin k, M i (σ i) = (∏ i ∈ s, M i (σ i)) * ∏ i ∈ sᶜ, M i (σ i) := by
    rw [Finset.prod_mul_prod_compl]
  rw [show (∏ i : Fin k, M.transpose (σ i) i) = ∏ i : Fin k, M i (σ i) by rfl, hprod]
  refine dvd_mul_of_dvd_left ?_ _
  rw [← hcard, ← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ hM i (Finset.mem_filter.mp hi).2 (σ i)

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
    exact ((hle.trans (natDegree_comp_X_add_C_le fy x)).trans natDegree_map_le).trans hf
  -- Translate `x` to `0`, preserving the resultant while making low coefficients vanish at `y`.
  set h := f.comp (X + C (C x))
  have hhderiv : h.derivative = f.derivative.comp (X + C (C x)) := by
    simp [h, derivative_comp]
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

/-- The parameter degree of a bivariate polynomial `F : K[X][X]`, defined as the maximum `natDegree`
of its coefficients. -/
private noncomputable def paramNatDegree (F : K[X][X]) : ℕ :=
  F.support.sup fun k ↦ (F.coeff k).natDegree

private theorem coeff_natDegree_le_paramNatDegree (F : K[X][X]) (k : ℕ) :
    (F.coeff k).natDegree ≤ paramNatDegree F := by
  by_cases hk : k ∈ F.support
  · exact Finset.le_sup (f := fun j ↦ (F.coeff j).natDegree) hk
  · rw [notMem_support_iff.mp hk, natDegree_zero]
    exact Nat.zero_le _

private theorem paramNatDegree_C (c : K[X]) : paramNatDegree (C c) = c.natDegree := by
  by_cases hc : c = 0
  · simp [paramNatDegree, hc]
  · simp [paramNatDegree, support_C hc]

private theorem paramNatDegree_mul_le (A B : K[X][X]) :
    paramNatDegree (A * B) ≤ paramNatDegree A + paramNatDegree B := by
  refine Finset.sup_le fun k _ ↦ ?_
  rw [coeff_mul]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun pq _ ↦ ?_)
  exact natDegree_mul_le.trans
    (Nat.add_le_add (coeff_natDegree_le_paramNatDegree A pq.1)
      (coeff_natDegree_le_paramNatDegree B pq.2))

/-- Every nonzero `A : K[X][X]` has a largest `z`-index attaining `paramNatDegree A`. -/
private theorem exists_max_paramNatDegree {A : K[X][X]} (hA : A ≠ 0) :
    ∃ i₀, A.coeff i₀ ≠ 0 ∧ (A.coeff i₀).natDegree = paramNatDegree A ∧
      ∀ p, i₀ < p → (A.coeff p).natDegree < paramNatDegree A ∨ A.coeff p = 0 := by
  classical
  set s := A.support.filter fun i ↦ (A.coeff i).natDegree = paramNatDegree A
  have hs : s.Nonempty := by
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup A.support (support_nonempty.mpr hA)
      (fun k ↦ (A.coeff k).natDegree)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq.symm⟩⟩
  refine ⟨s.max' hs, mem_support_iff.mp (Finset.mem_filter.mp (s.max'_mem hs)).1,
    (Finset.mem_filter.mp (s.max'_mem hs)).2, fun p hp ↦ ?_⟩
  by_cases h0 : A.coeff p = 0
  · exact Or.inr h0
  · left
    refine lt_of_le_of_ne (coeff_natDegree_le_paramNatDegree A p) fun heq ↦
      not_lt_of_ge (s.le_max' p (Finset.mem_filter.mpr ⟨mem_support_iff.mpr h0, heq⟩)) hp

/-- For nonzero `A, B : K[X][X]`, the parameter degree is at least the sum of the parameter degrees
of the factors: the highest `z`-index attaining `paramNatDegree` in each factor contributes an
uncancelled leading term to `A * B`. -/
private theorem add_paramNatDegree_le_mul {A B : K[X][X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    paramNatDegree A + paramNatDegree B ≤ paramNatDegree (A * B) := by
  obtain ⟨i₀, hi₀_ne, hi₀_deg, hvanA⟩ := exists_max_paramNatDegree hA
  obtain ⟨j₀, hj₀_ne, hj₀_deg, hvanB⟩ := exists_max_paramNatDegree hB
  have hcoeff_top : ((A * B).coeff (i₀ + j₀)).coeff (paramNatDegree A + paramNatDegree B) =
      (A.coeff i₀).leadingCoeff * (B.coeff j₀).leadingCoeff := by
    rw [coeff_mul, show (∑ x ∈ Finset.antidiagonal (i₀ + j₀), A.coeff x.1 * B.coeff x.2).coeff
        (paramNatDegree A + paramNatDegree B) =
        ∑ x ∈ Finset.antidiagonal (i₀ + j₀),
          (A.coeff x.1 * B.coeff x.2).coeff (paramNatDegree A + paramNatDegree B) from
        map_sum (lcoeff K (paramNatDegree A + paramNatDegree B)) _ _,
      Finset.sum_eq_single (i₀, j₀)]
    · dsimp only
      rw [← hi₀_deg, ← hj₀_deg, ← natDegree_mul hi₀_ne hj₀_ne, ← leadingCoeff, leadingCoeff_mul]
    · intro pq hpq hne
      have hsum : pq.1 + pq.2 = i₀ + j₀ := Finset.mem_antidiagonal.mp hpq
      rcases lt_or_gt_of_ne (fun h1 ↦ hne (Prod.ext h1 (by omega))) with h1 | h1
      · rcases hvanB pq.2 (by omega) with hdegB | hb0
        · exact coeff_eq_zero_of_natDegree_lt <| natDegree_mul_le.trans_lt
            (Nat.add_lt_add_of_le_of_lt (coeff_natDegree_le_paramNatDegree A pq.1) hdegB)
        · rw [hb0, mul_zero, coeff_zero]
      · rcases hvanA pq.1 h1 with hdegA | ha0
        · exact coeff_eq_zero_of_natDegree_lt <| natDegree_mul_le.trans_lt
            (Nat.add_lt_add_of_lt_of_le hdegA (coeff_natDegree_le_paramNatDegree B pq.2))
        · rw [ha0, zero_mul, coeff_zero]
    · intro h
      exact absurd (Finset.mem_antidiagonal.mpr (rfl : i₀ + j₀ = i₀ + j₀)) h
  have hne : ((A * B).coeff (i₀ + j₀)).coeff (paramNatDegree A + paramNatDegree B) ≠ 0 := by
    rw [hcoeff_top]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hi₀_ne) (leadingCoeff_ne_zero.mpr hj₀_ne)
  exact (le_natDegree_of_ne_zero hne).trans (coeff_natDegree_le_paramNatDegree (A * B) (i₀ + j₀))

private theorem paramNatDegree_mul {A B : K[X][X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    paramNatDegree (A * B) = paramNatDegree A + paramNatDegree B :=
  le_antisymm (paramNatDegree_mul_le A B) (add_paramNatDegree_le_mul hA hB)

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
private theorem sum_rootMultiplicity_le_natDegree {ι : Type*} [Fintype ι] {f : ι → K}
    (hf : Function.Injective f) {p : K[X]} :
    ∑ i : ι, p.rootMultiplicity (f i) ≤ p.natDegree := by
  classical
  calc ∑ i : ι, p.rootMultiplicity (f i)
      = ∑ a ∈ Finset.univ.image f, p.rootMultiplicity a := by
        rw [Finset.sum_image fun _ _ _ _ h ↦ hf h]
    _ = ∑ a ∈ Finset.univ.image f, p.roots.count a := by
        simp [count_roots]
    _ ≤ p.roots.card := by
        rw [← Multiset.toFinset_sum_count_eq p.roots]
        have hsub : (Finset.univ.image f).filter (· ∈ p.roots.toFinset) ⊆ p.roots.toFinset :=
          fun _ hx ↦ (Finset.mem_filter.mp hx).2
        calc ∑ a ∈ Finset.univ.image f, p.roots.count a
            = ∑ a ∈ (Finset.univ.image f).filter (· ∈ p.roots.toFinset), p.roots.count a := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun a _ ↦ ?_
              split_ifs with h
              · rfl
              · exact Multiset.count_eq_zero.mpr (Multiset.mem_toFinset.not.mp h)
          _ ≤ ∑ a ∈ p.roots.toFinset, p.roots.count a :=
              Finset.sum_le_sum_of_subset hsub
    _ ≤ p.natDegree := p.card_roots'

/-- Over a field of characteristic zero, the discriminant resultant `Res_z(F, ∂_z F)` of an
irreducible polynomial `F : K[X][X]` of positive `z`-degree is nonzero. -/
private theorem resultant_derivative_ne_zero_of_irreducible [CharZero K] {F : K[X][X]}
    (hF : Irreducible F) (hpos : 0 < F.natDegree) :
    F.resultant F.derivative F.natDegree (F.natDegree - 1) ≠ 0 := by
  have hprim : F.IsPrimitive := by
    intro r ⟨Q, hQ⟩
    rcases hF.isUnit_or_isUnit hQ with hC | hQu
    · exact isUnit_C.mp hC
    · have hQ0 : Q.natDegree = 0 := natDegree_eq_zero_of_isUnit hQu
      have hF0 : F.natDegree = 0 :=
        Nat.eq_zero_of_le_zero ((hQ ▸ natDegree_mul_le).trans (by simp [hQ0]))
      omega
  set L := FractionRing K[X]
  let φ : K[X] →+* L := algebraMap K[X] L
  have hφ : Function.Injective φ := IsFractionRing.injective K[X] L
  have hF_irr : Irreducible (F.map φ) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hF
  have hF_deg : (F.map φ).natDegree = F.natDegree := natDegree_map_eq_of_injective hφ F
  have hFd_ne : F.derivative ≠ 0 := by
    intro h0
    have := derivative_eq_zero.mp h0
    omega
  have hFd_deg : F.derivative.natDegree = F.natDegree - 1 := natDegree_derivative F
  have hFd_map_deg : (F.derivative.map φ).natDegree = F.natDegree - 1 := by
    rw [natDegree_map_eq_of_injective hφ, hFd_deg]
  have hcop : IsCoprime (F.map φ) (F.derivative.map φ) := by
    refine (hF_irr.isCoprime_or_dvd _).resolve_right fun hdvd ↦ ?_
    have hle := natDegree_le_of_dvd hdvd ((Polynomial.map_ne_zero_iff hφ).mpr hFd_ne)
    rw [hF_deg, hFd_map_deg] at hle
    omega
  have hresL : (F.map φ).resultant (F.derivative.map φ) ≠ 0 := by
    rw [ne_eq, resultant_eq_zero_iff]
    exact fun h ↦ h.2 hcop
  intro h0
  apply hresL
  rw [hF_deg, hFd_map_deg, resultant_map_map, h0, map_zero]

/-- Base case of `sum_rootMultiplicity_le_of_isPrimitive` for an irreducible factor. -/
private theorem sum_rootMultiplicity_le_of_irreducible [CharZero K] [DecidableEq K]
    {ι : Type*} [Fintype ι] {P : ι → K × K} (hP_snd : Function.Injective fun i ↦ (P i).2) {N : ℕ}
    (hSZ : ∀ g : K[X][X], g ≠ 0 →
      (Finset.univ.filter fun i ↦ (g.map (evalRingHom (P i).2)).eval (P i).1 = 0).card ≤
        N * (g.natDegree + paramNatDegree g))
    {F : K[X][X]} (hF : Irreducible F) (hpos : 0 < F.natDegree) :
    ∑ i : ι, (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
      N * F.natDegree + N * paramNatDegree F + 2 * F.natDegree * paramNatDegree F := by
  set R := F.resultant F.derivative F.natDegree (F.natDegree - 1) with hRdef
  have hR0 : R ≠ 0 := resultant_derivative_ne_zero_of_irreducible hF hpos
  have hRdeg : R.natDegree ≤ 2 * F.natDegree * paramNatDegree F :=
    (natDegree_resultant_derivative_le fun i _ ↦ coeff_natDegree_le_paramNatDegree F i).trans
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
    _ ≤ N * (F.natDegree + paramNatDegree F) + R.natDegree :=
        Nat.add_le_add (hSZ F hF.ne_zero) (sum_rootMultiplicity_le_natDegree hP_snd)
    _ ≤ N * F.natDegree + N * paramNatDegree F + 2 * F.natDegree * paramNatDegree F := by
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
        N * (g.natDegree + g.support.sup fun k ↦ (g.coeff k).natDegree))
    {F : K[X][X]} (hF : F.IsPrimitive) :
    ∑ i : ι, (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
      N * F.natDegree + N * (F.support.sup fun k ↦ (F.coeff k).natDegree) +
        2 * F.natDegree * (F.support.sup fun k ↦ (F.coeff k).natDegree) := by
  change ∑ i : ι, (F.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
    N * F.natDegree + N * paramNatDegree F + 2 * F.natDegree * paramNatDegree F
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
        have hpdeg : paramNatDegree F = paramNatDegree A + paramNatDegree B := by
          rw [hFAB, paramNatDegree_mul hAp.ne_zero hBp.ne_zero]
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
  rcases eq_or_ne F 0 with rfl | hF
  · simp
  set c := F.content
  set G := F.primPart
  have hc0 : c ≠ 0 := content_eq_zero_iff.not.mpr hF
  have hpdeg : paramNatDegree F = c.natDegree + paramNatDegree G := by
    conv_lhs => rw [F.eq_C_content_mul_primPart]
    rw [paramNatDegree_mul (C_ne_zero.mpr hc0) F.isPrimitive_primPart.ne_zero, paramNatDegree_C]
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
  have hG : ∑ i : ι, (G.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
      N * G.natDegree + N * paramNatDegree G + 2 * G.natDegree * paramNatDegree G :=
    sum_rootMultiplicity_le_of_isPrimitive hP_snd hSZ F.isPrimitive_primPart
  change _ ≤ N * F.natDegree + N * paramNatDegree F + 2 * F.natDegree * paramNatDegree F
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
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  set c := F.content
  set G := F.primPart
  have hc0 : c ≠ 0 := content_eq_zero_iff.not.mpr hF
  have hpdeg : paramNatDegree F = c.natDegree + paramNatDegree G := by
    conv_lhs => rw [F.eq_C_content_mul_primPart]
    rw [paramNatDegree_mul (C_ne_zero.mpr hc0) F.isPrimitive_primPart.ne_zero, paramNatDegree_C]
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
      _ ≤ c.natDegree := sum_rootMultiplicity_le_natDegree hP_snd
  have hGood : N * sGood.card ≤
      ∑ i : ι, (G.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 := by
    calc N * sGood.card = ∑ _i ∈ sGood, N := by simp [mul_comm]
      _ ≤ ∑ i ∈ sGood, (G.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 :=
          Finset.sum_le_sum fun i hi ↦
            le_rootMultiplicity_primPart hN0 (Finset.mem_filter.mp hi).2 (hvan i)
      _ ≤ ∑ i : ι, (G.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 :=
          Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _
  have hGsum : ∑ i : ι, (G.map (evalRingHom (P i).2)).rootMultiplicity (P i).1 ≤
      N * G.natDegree + N * paramNatDegree G + 2 * G.natDegree * paramNatDegree G :=
    sum_rootMultiplicity_le_of_isPrimitive hP_snd hSZ F.isPrimitive_primPart
  change N * Fintype.card ι ≤
    N * F.natDegree + N * paramNatDegree F + 2 * F.natDegree * paramNatDegree F
  rw [hcard, Nat.mul_add, hpdeg, ← F.natDegree_primPart]
  nlinarith

end BivariateMultiplicity

end Polynomial
