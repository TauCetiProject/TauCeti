/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Data.Matrix.Composition
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.LinearAlgebra.TensorProduct.Submodule

/-!
# Amitsur's theorem on integral characteristic polynomials

Let `ρ : Λ → M_n(L)` be an `R`-algebra homomorphism, with `L` a commutative `R`-algebra and `Λ`
any `R`-algebra. If `Λ` is spanned over `R` by elements whose characteristic polynomials under
`ρ` have their coefficients in the image of `R`, then every element of `Λ` has this property. This
is the integrality consequence of Amitsur's formula for the characteristic polynomial of a sum of
matrices; the proof here avoids the formula and works with `det (1 - t ρ(w))` modulo powers of `t`.

It passes to block matrices (an array `P` over `Λ` gives the block matrix `ρ(P)` with blocks
`ρ (P i j)`) and to arrays with polynomial entries, through the extension
`AlgHom.mvPolynomialBaseChange` of `ρ` to `R[X_σ] ⊗_R Λ → M_n(L[X_σ])`. For a representation
`r : G → M_n(L)` whose characteristic polynomials have coefficients in the image of `R`, this gives
the hypothesis (P) of `LengthBoundsInPadicFamilies` §1.8c: the determinant of every array over
`R[X_σ] ⊗_R R[G]` has its coefficients in the image of `R` (1.8c (4)). In the split case `L = O^X`
and `R = A ⊆ O^X`, so the coefficients, as functions of `x ∈ X`, lie in `A`. In the language of
`IntegralHeckeAndGaloisDeterminants` §0.5, these are the integrality statements that follow from
Amitsur's formula for the determinant of `M_{mn}`; the formula itself (with Lyndon words) is not
needed and not proved here.

## Main results

* `AlgHom.charpoly_coeff_mem_range_of_span`: Amitsur's theorem.
* `AlgHom.charpoly_coeff_comp_mem_range`: the same for block matrices of arrays over `Λ`.
* `AlgHom.coeff_charpoly_coeff_comp_mvPolynomialBaseChange_mem_range` and
  `AlgHom.coeff_det_comp_mvPolynomialBaseChange_mem_range`: the same for arrays with polynomial
  entries.
* `MonoidHom.charpoly_coeff_lift_mem_range` and
  `MonoidHom.coeff_det_comp_mvPolynomialBaseChange_lift_mem_range`: from group elements to the
  monoid algebra, and to arrays over it (1.8c (4)).

## Provenance

`AlgHom.charpoly_coeff_mem_range_of_span` and `AlgHom.charpoly_coeff_comp_mem_range` are adapted
from `New.amitsur_charpoly_mem_of_span` (file `src/Lib/General/LinearAlgebra/Eigenvalues.lean`) and
`New.amitsur_charpoly_comp_coeff_mem_range` (file `src/New/Congruences/FirstOrder/RibetMethod.lean`)
in grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), which
treats variables one at a time through `Λ[X]`; the version with several variables through
`R[X_σ] ⊗_R Λ` and the monoid algebra form are new here.

## References

* S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*, Linear and Multilinear
  Algebra 8 (1980), no. 3, 177–182.
* G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, LMS Lecture Note Ser. 414 (2014), (1.5).
-/

@[expose] public section

open Polynomial Matrix

namespace AlgHom

variable {R L n Λ : Type*} [CommRing R] [CommRing L] [Algebra R L] [Fintype n] [DecidableEq n]
  [Ring Λ] [Algebra R Λ] (ρ : Λ →ₐ[R] Matrix n n L)

open Submodule in
/-- The induction step of Amitsur's theorem. Let `S` be an `R`-subalgebra of a commutative
`R`-algebra `C`, `f : S ⊗_R Λ → M_n(C)` an `S`-algebra homomorphism and `t ∈ S` with `t ^ e = 0`.
If `Λ` is spanned over `R` by elements `s` with `det (1 - c • f (1 ⊗ s)) ∈ S` for all `c ∈ S`, then
`det (1 - t • f β) ∈ S` implies `det (1 - t • f (β + t ^ j • γ)) ∈ S` for every `γ` and `j ≤ e`: by
descending induction on `j`, multiplying by `1 - t ^ (j + 1) c • f (1 ⊗ s)` adds `t ^ j c ⊗ s` to
`β` up to an error divisible by `t ^ (j + 1)`. -/
private theorem det_one_sub_smul_add_pow_smul_mem {C : Type*} [CommRing C] [Algebra R C]
    (S : Subalgebra R C) (f : TensorProduct R S Λ →ₐ[S] Matrix n n C) (T : Set Λ)
    (hT : span R T = ⊤) (det_mem : ∀ s ∈ T, ∀ c : S, det (1 - c • f (1 ⊗ₜ s)) ∈ S) (t : S)
    {e : ℕ} (t_pow : t ^ e = 0) {j : ℕ} (hj : j ≤ e) (γ β : TensorProduct R S Λ) :
    det (1 - t • f β) ∈ S → det (1 - t • f (β + t ^ j • γ)) ∈ S := by
  -- The tensors `1 ⊗ₜ s`, `s ∈ T`, span `S ⊗ Λ` over `S`.
  have mem_span (γ : TensorProduct R S Λ) : γ ∈ span S (TensorProduct.mk R S Λ 1 '' T) := by
    simp [← baseChange_span, hT]
  induction hj using Nat.decreasingInduction generalizing γ β with
  | self => simp [t_pow]
  | of_succ j _ ih =>
    induction mem_span γ using closure_induction generalizing β with
    | zero => simp
    | add γ γ' _ _ ih_γ ih_γ' =>
      intro hβ
      simpa [smul_add, ← add_assoc] using ih_γ' _ (ih_γ β hβ)
    | smul_mem c x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      intro hβ
      -- Multiplying by `1 - t ^ (j + 1) • c • s` adds `t ^ j • c • s` to `β`, up to the error
      -- `t ^ (j + 1) • δ`, which the induction hypothesis removes.
      let δ : TensorProduct R S Λ := c • β * 1 ⊗ₜ s
      let β' : TensorProduct R S Λ := β + t ^ j • c • (1 : S) ⊗ₜ[R] s - t ^ (j + 1) • δ
      have factor : 1 - t • f β' = (1 - t • f β) * (1 - (t ^ (j + 1) * c) • f (1 ⊗ₜ s)) := by
        simp only [β', δ, map_sub, map_add, map_smul, map_mul, sub_mul, mul_sub, mul_one, one_mul,
          smul_mul_assoc, mul_smul_comm]
        module
      have h_mem : det (1 - t • f β') ∈ S := by
        rw [factor, det_mul]
        exact mul_mem hβ (det_mem s hs _)
      simpa [β'] using ih δ β' h_mem

open Submodule AdjoinRoot Finset Fintype Algebra Function in
/-- **Amitsur's theorem** (Amitsur 1980; Chenevier 2014, (1.5)). Let `ρ : Λ → M_n(L)` be an
`R`-algebra homomorphism, with `L` a commutative `R`-algebra. If `Λ` is spanned over `R` by elements
whose characteristic polynomials under `ρ` have coefficients in the image of `R`, so does every
element. The proof works with `det (1 - t ρ(w))` modulo `t ^ e` over the image `S` of `R[t]` in
`L[t]/(t ^ e)` and builds `w` up from the spanning set one term at a time
(`det_one_sub_smul_add_pow_smul_mem`). -/
theorem charpoly_coeff_mem_range_of_span
    (hρ : span R {s : Λ | ∀ k : ℕ, (ρ s).charpoly.coeff k ∈ (algebraMap R L).range} = ⊤) (w : Λ)
    (k : ℕ) : (ρ w).charpoly.coeff k ∈ (algebraMap R L).range := by
  let e : ℕ := revAt (ρ w).charpoly.natDegree k + 1
  let S : Subalgebra R (AdjoinRoot (X ^ e : L[X])) := (aeval (root (X ^ e : L[X]))).range
  let t : S := ⟨aeval (root (X ^ e : L[X])) (X : R[X]), X, rfl⟩
  let f : TensorProduct R S Λ →ₐ[S] Matrix n n (AdjoinRoot (X ^ e : L[X])) :=
    ((ofAlgHom R (X ^ e : L[X])).mapMatrix.comp ρ).liftEquiv R S _ _
  have det_eq (s : Λ) (c : S) :
      det (1 - c • f (1 ⊗ₜ s)) = (ρ s).charpoly.reverse.aeval (c : AdjoinRoot (X ^ e : L[X])) := by
    simp [f, reverse_charpoly, charpolyRev, AlgHom.map_det, S.smul_def, map_sub, Matrix.map_smul',
      comp_def]
  let T : Set Λ := {s | ∀ k : ℕ, (ρ s).charpoly.coeff k ∈ (algebraMap R L).range}
  have det_mem (s : Λ) (hs : s ∈ T) (c : S) : det (1 - c • f (1 ⊗ₜ s)) ∈ S := by
    obtain ⟨y, hy⟩ : ∃ y : R[X], y.map (algebraMap R L) = (ρ s).charpoly :=
      (lifts_iff_coeff_lifts _).2 hs
    simp [det_eq, reverse, ← hy, reflect_map]
  have t_pow : t ^ e = 0 := Subtype.ext (by simp [t, ← mk_X, ← map_pow])
  -- The case `j = 0`, `β = 0`: `det (1 - t • ρ w)` is the value at `t` of some `q : R[X]`.
  obtain ⟨q, hq⟩ : det (1 - t • f (0 + t ^ 0 • (1 : S) ⊗ₜ[R] w)) ∈ S :=
    det_one_sub_smul_add_pow_smul_mem S f T hρ det_mem t t_pow e.zero_le (1 ⊗ₜ w) 0 (by simp)
  -- `q` agrees with the reversed characteristic polynomial in all degrees below `e`.
  have h_agree : ∀ d < e,
      algebraMap R L (q.coeff d) = (ρ w).charpoly.coeff (revAt (ρ w).charpoly.natDegree d) := by
    simpa [aeval_eq_of_algebra, det_eq, t, X_pow_dvd_iff, sub_eq_zero, coeff_reverse] using hq
  exact ⟨q.coeff (e - 1), by simpa [e] using h_agree (e - 1) (Nat.lt_succ_self _)⟩

/-- **Amitsur's theorem for block matrices.** If every `ρ w` has its characteristic polynomial
over the image of `R`, so does every block matrix `ρ(P) = (ρ (P i j))_{i j}` of a square array `P`
over `Λ`. The arrays with one nonzero row span `M_N(Λ)`, and for such an array `ρ(P)` is a product
`col * row` with `row * col = ρ (P q q)`, so its characteristic polynomial is that of `ρ (P q q)`
up to a power of `X`. -/
theorem charpoly_coeff_comp_mem_range
    (hρ : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range)
    {N : Type*} [Fintype N] [DecidableEq N] (P : Matrix N N Λ) (k : ℕ) :
    (Matrix.comp N N n n L (P.map ρ)).charpoly.coeff k ∈ (algebraMap R L).range := by
  let φ : Matrix N N Λ →ₐ[R] Matrix (N × n) (N × n) L :=
    (compAlgEquiv N n L R).toAlgHom.comp ρ.mapMatrix
  suffices h_row : ∀ (Q : Matrix N N Λ) (q : N) (m : ℕ),
      (φ (∑ j, single q j (Q q j))).charpoly.coeff m ∈ (algebraMap R L).range by
    refine charpoly_coeff_mem_range_of_span φ (top_unique fun Q _ ↦ ?_) P k
    rw [matrix_eq_sum_single Q]
    exact Submodule.sum_mem _ fun q _ ↦ Submodule.subset_span (h_row Q q)
  intro Q q m
  have hφ (M : Matrix N N Λ) (i j : N) (a b : n) : φ M (i, a) (j, b) = ρ (M i j) a b := rfl
  let col : Matrix (N × n) n L := of fun x b ↦ if x = (q, b) then 1 else 0
  let row : Matrix n (N × n) L := (φ Q).submatrix (fun x ↦ (q, x)) id
  have h_factor : φ (∑ j, single q j (Q q j)) = col * row := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [hφ]
    obtain rfl | hi := eq_or_ne q i
    · simp [col, row, hφ, Matrix.sum_apply, Matrix.single, Matrix.mul_apply]
    · simp [col, hi, hi.symm, Matrix.sum_apply, Matrix.mul_apply]
  have h_swap : row * col = ρ (Q q q) := by
    ext a b
    simp [col, row, hφ, Matrix.mul_apply]
  have h_charpoly : X ^ Fintype.card n * (col * row).charpoly =
      X ^ Fintype.card (N × n) * (ρ (Q q q)).charpoly := by
    rw [charpoly_mul_comm', h_swap]
  rw [h_factor, ← coeff_X_pow_mul _ (Fintype.card n), h_charpoly, coeff_X_pow_mul']
  split_ifs
  exacts [hρ _ _, zero_mem _]

section Variables

open MvPolynomial TensorProduct

variable (σ : Type*)

/-- The extension of `ρ : Λ → M_n(L)` to arrays with polynomial entries: the `R`-algebra
homomorphism `R[X_σ] ⊗_R Λ → M_n(L[X_σ])`, `f ⊗ w ↦ f • ρ(w)`. -/
noncomputable def mvPolynomialBaseChange :
    MvPolynomial σ R ⊗[R] Λ →ₐ[R] Matrix n n (MvPolynomial σ L) :=
  Algebra.TensorProduct.lift
    (((Algebra.ofId (MvPolynomial σ L) (Matrix n n (MvPolynomial σ L))).restrictScalars R).comp
      (mapAlgHom (Algebra.ofId R L)))
    ((IsScalarTower.toAlgHom R L (MvPolynomial σ L)).mapMatrix.comp ρ)
    fun f _ ↦ by exact Algebra.commute_algebraMap_left (map (algebraMap R L) f) _

/-- The extension of `ρ` on pure tensors: `f ⊗ w ↦ f • ρ(w)`. -/
theorem mvPolynomialBaseChange_tmul (f : MvPolynomial σ R) (w : Λ) :
    ρ.mvPolynomialBaseChange σ (f ⊗ₜ w) =
      algebraMap _ _ (map (algebraMap R L) f) * (ρ w).map MvPolynomial.C := by
  rw [mvPolynomialBaseChange, Algebra.TensorProduct.lift_tmul]
  rfl

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- The extension of `ρ` is `R[X_σ]`-linear, which puts it in the scope of Amitsur's theorem over
the base ring `R[X_σ]`. -/
private theorem charpoly_coeff_mvPolynomialBaseChange_mem_range_map
    (hρ : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range)
    {N : Type*} [Fintype N] [DecidableEq N] (P : Matrix N N (MvPolynomial σ R ⊗[R] Λ)) (k : ℕ) :
    (Matrix.comp N N n n _ (P.map (ρ.mvPolynomialBaseChange σ))).charpoly.coeff k ∈
      (map (σ := σ) (algebraMap R L)).range := by
  let ρX : MvPolynomial σ R ⊗[R] Λ →ₐ[MvPolynomial σ R] Matrix n n (MvPolynomial σ L) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      ((IsScalarTower.toAlgHom R L (MvPolynomial σ L)).mapMatrix.comp ρ)
      fun f _ ↦ Algebra.commute_algebraMap_left f _
  have hρX : ⇑ρX = ρ.mvPolynomialBaseChange σ := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul f w => simp [ρX, mvPolynomialBaseChange_tmul]; rfl
    | add x y hx hy => simp [map_add, hx, hy]
  have hrange : (algebraMap (MvPolynomial σ R) (MvPolynomial σ L)).range =
      (map (σ := σ) (algebraMap R L)).range := rfl
  rw [← hρX, ← hrange]
  refine charpoly_coeff_comp_mem_range ρX (fun w ↦ charpoly_coeff_mem_range_of_span _
    (top_unique fun γ _ ↦ ?_) w) P k
  have hγ : γ ∈ Submodule.span (MvPolynomial σ R)
      (TensorProduct.mk R (MvPolynomial σ R) Λ 1 '' Set.univ) := by
    rw [← Submodule.baseChange_span, Submodule.span_univ, Submodule.baseChange_top]
    exact Submodule.mem_top
  refine Submodule.span_mono ?_ hγ
  rintro _ ⟨s, -, rfl⟩ j
  obtain ⟨c, hc⟩ := hρ s j
  refine ⟨MvPolynomial.C c, ?_⟩
  have h1 : ρX (1 ⊗ₜ s) = (ρ s).map MvPolynomial.C := by
    rw [congrFun hρX, mvPolynomialBaseChange_tmul, map_one, map_one, one_mul]
  rw [TensorProduct.mk_apply, h1, charpoly_map, Polynomial.coeff_map, ← hc]
  exact MvPolynomial.map_C _ _

/-- **Amitsur's theorem with variables.** If every `ρ w` has its characteristic polynomial over
the image of `R`, then for every square array `P` over `R[X_σ] ⊗_R Λ` the characteristic
polynomial of the block matrix `ρ(P)` over `L[X_σ]` has all coefficients of all its
coefficients in the image of `R`. -/
theorem coeff_charpoly_coeff_comp_mvPolynomialBaseChange_mem_range
    (hρ : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range)
    {N : Type*} [Fintype N] [DecidableEq N] (P : Matrix N N (MvPolynomial σ R ⊗[R] Λ)) (k : ℕ)
    (s : σ →₀ ℕ) :
    ((Matrix.comp N N n n _ (P.map (ρ.mvPolynomialBaseChange σ))).charpoly.coeff k).coeff s ∈
      (algebraMap R L).range := by
  obtain ⟨y, hy⟩ := charpoly_coeff_mvPolynomialBaseChange_mem_range_map ρ σ hρ P k
  exact ⟨y.coeff s, by rw [← hy, MvPolynomial.coeff_map]⟩

/-- **Determinants of arrays with variables** (`LengthBoundsInPadicFamilies` §1.8c (4)). If every
`ρ w` has its characteristic polynomial over the image of `R`, then for every square array `P`
over `R[X_σ] ⊗_R Λ` the determinant of the block matrix `ρ(P)`, a polynomial over `L`, has all
its coefficients in the image of `R`. -/
theorem coeff_det_comp_mvPolynomialBaseChange_mem_range
    (hρ : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range)
    {N : Type*} [Fintype N] [DecidableEq N] (P : Matrix N N (MvPolynomial σ R ⊗[R] Λ))
    (s : σ →₀ ℕ) :
    (Matrix.comp N N n n _ (P.map (ρ.mvPolynomialBaseChange σ))).det.coeff s ∈
      (algebraMap R L).range := by
  obtain ⟨y, hy⟩ := charpoly_coeff_mvPolynomialBaseChange_mem_range_map ρ σ hρ P 0
  rw [det_eq_sign_charpoly_coeff, ← hy]
  refine ⟨((-1) ^ Fintype.card (N × n) * y).coeff s, ?_⟩
  rw [← MvPolynomial.coeff_map, map_mul, map_pow, map_neg, map_one]

end Variables

end AlgHom

section MonoidAlgebra

open TensorProduct

variable {R L n : Type*} [CommRing R] [CommRing L] [Algebra R L] [Fintype n] [DecidableEq n]
  {G : Type*} [Monoid G] (r : G →* Matrix n n L)

/-- **Amitsur's theorem for a representation.** If the characteristic polynomials of the `r g`,
`g ∈ G`, have their coefficients in the image of `R`, so do those of all elements of the image of
the monoid algebra `R[G]`, which is spanned by the `g`. -/
theorem MonoidHom.charpoly_coeff_lift_mem_range
    (hr : ∀ (g : G) (k : ℕ), (r g).charpoly.coeff k ∈ (algebraMap R L).range)
    (w : MonoidAlgebra R G) (k : ℕ) :
    (MonoidAlgebra.lift R (Matrix n n L) G r w).charpoly.coeff k ∈ (algebraMap R L).range := by
  refine AlgHom.charpoly_coeff_mem_range_of_span _ (top_unique fun x _ ↦ ?_) w k
  clear w
  induction x using MonoidAlgebra.induction_on with
  | of g => exact Submodule.subset_span fun k ↦ by rw [MonoidAlgebra.lift_of]; exact hr g k
  | add x y hx hy => exact add_mem (hx Submodule.mem_top) (hy Submodule.mem_top)
  | smul c x hx => exact Submodule.smul_mem _ c (hx Submodule.mem_top)

/-- **The hypothesis (P) from characteristic polynomials of group elements**
(`LengthBoundsInPadicFamilies` §1.8c (4)). If the characteristic polynomials of the `r g` have
their coefficients in the image of `R`, then for every square array `P` over `R[X_σ] ⊗_R R[G]` the
determinant of the block matrix `r(P)` over `L[X_σ]` has all its coefficients in the image of
`R`. For `L = O^X` and `R = A ⊆ O^X` a split algebra, this says that `x ↦ det P(x)` has
coefficients in `A`. -/
theorem MonoidHom.coeff_det_comp_mvPolynomialBaseChange_lift_mem_range
    (hr : ∀ (g : G) (k : ℕ), (r g).charpoly.coeff k ∈ (algebraMap R L).range) (σ : Type*)
    {N : Type*} [Fintype N] [DecidableEq N]
    (P : Matrix N N (MvPolynomial σ R ⊗[R] MonoidAlgebra R G)) (s : σ →₀ ℕ) :
    (Matrix.comp N N n n _
      (P.map ((MonoidAlgebra.lift R (Matrix n n L) G r).mvPolynomialBaseChange σ))).det.coeff s ∈
        (algebraMap R L).range :=
  AlgHom.coeff_det_comp_mvPolynomialBaseChange_mem_range _ σ (r.charpoly_coeff_lift_mem_range hr)
    P s

end MonoidAlgebra
