/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Decomposition
public import TauCeti.Algebra.HopfAlgebra.CompactType.SchurOrthogonality

/-!
# The modular automorphism and Kac characterization of compact-type Hopf star algebras

Every algebraic Haar state `h : AlgebraicHaar A` on a complex Hopf star algebra `A` admits a
unique algebra automorphism `θ : A ≃ₐ[ℂ] A` — the *modular automorphism* (or Woronowicz
character automorphism) — satisfying `h (a * b) = h (b * θ a)` for all `a, b : A`
(Neshveyev–Tuset, Theorem 1.7.3; Timmermann, Proposition 3.2.15).

On the coefficient matrix `u` of any finite-dimensional simple unitary comodule `(M, b)` with
unique positive definite Schur matrix `Ft` (`Ft.trace = Ft⁻¹.trace`), the modular automorphism acts
by two-sided multiplication by `F := Ftᵀ`:

`u.map h.modularAutomorphism = F * u * F`,

whereas the squared antipode acts by conjugation `u.map (S ∘ S) = F * u * F⁻¹`
(`AlgebraicHaar.map_antipode_antipode_coefficientMatrix`). Comparing the two formulas yields the
algebraic Kac characterization (Neshveyev–Tuset, Proposition 1.7.7): `h` is tracial if and only if
the antipode is involutive (`S ∘ S = id`).

## Main declarations

* `TauCeti.AlgebraicHaar.modularAutomorphism`: the unique modular algebra automorphism `θ`
  satisfying `h (a * b) = h (b * θ a)`.
* `TauCeti.AlgebraicHaar.apply_mul_eq_mul_modularAutomorphism`: the modular KMS-type identity
  `h (a * b) = h (b * h.modularAutomorphism a)`.
* `TauCeti.AlgebraicHaar.existsUnique_modularAutomorphism`: existence and uniqueness of the
  modular automorphism.
* `TauCeti.AlgebraicHaar.modularAutomorphism_eq_refl_iff`: `h.modularAutomorphism = AlgEquiv.refl`
  if and only if `h` is tracial.
* `TauCeti.AlgebraicHaar.modularAutomorphism_coefficientMatrix`: explicit action
  `u.map h.modularAutomorphism = Ftᵀ * u * Ftᵀ` on any finite simple unitary comodule.
* `TauCeti.AlgebraicHaar.apply_mul_comm_iff_antipode_involutive`: `h` is tracial if and only if
  `S (S a) = a` for all `a : A`.

## References

* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Theorem 1.7.3 and Proposition 1.7.7.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
-/

public section

open Module Matrix
open scoped ComplexOrder DirectSum

namespace TauCeti.AlgebraicHaar

universe u w

variable {A : Type u} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]

omit [StarRing A] [StarModule ℂ A] [StarCoalgebra ℂ A] in
/-- Entrywise expansion of `X.map (algebraMap ℂ A) * u * Y.map (algebraMap ℂ A)`. -/
private theorem scalar_mul_matrix_mul_scalar_apply {ι : Type*} [Fintype ι]
    (X Y : Matrix ι ι ℂ) (u : Matrix ι ι A) (i j : ι) :
    (X.map (algebraMap ℂ A) * u * Y.map (algebraMap ℂ A)) i j =
      ∑ p, ∑ q, (X i p * Y q j) • u p q := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  rw [mul_comm (Y q j)]

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
/-- Core weighted Schur identity behind the modular automorphism on a single simple unitary
block: pairing `star (u k l)` against `(Ftᵀ * u * Ftᵀ) i j` reproduces `h (u i j * star (u k l))`.
-/
private theorem apply_star_mul_modular_entry (h : AlgebraicHaar A)
    {M : Type w} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ M) {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef) (htr : Ft.trace = Ft⁻¹.trace)
    (h1' : ∀ i j k l,
      h (star (Comodule.coefficientMatrix (C := A) b i j) *
          Comodule.coefficientMatrix (C := A) b k l) =
        if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0)
    (h2' : ∀ i j k l,
      h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0)
    (i j k l : ι) :
    h (star (Comodule.coefficientMatrix (C := A) b k l) *
        (Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
          Ftᵀ.map (algebraMap ℂ A)) i j) =
      h (Comodule.coefficientMatrix (C := A) b i j *
        star (Comodule.coefficientMatrix (C := A) b k l)) := by
  set u := Comodule.coefficientMatrix (C := A) b
  set F := Ftᵀ
  have hFFinv : F * F⁻¹ = 1 := by
    rw [← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul,
      nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hFt.isUnit), Matrix.transpose_one]
  rw [scalar_mul_matrix_mul_scalar_apply, Finset.mul_sum, map_sum]
  simp_rw [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, h1']
  have hinner (p : ι) :
      ∑ q, F i p * F q j * (if l = q then Ft⁻¹ k p / Ft⁻¹.trace else 0) =
        F i p * F⁻¹ p k * (Ft j l / Ft.trace) := by
    rw [Finset.sum_eq_single l _ (by simp)]
    · simp only [↓reduceIte, ← htr]
      have hFinv : F⁻¹ p k = Ft⁻¹ k p := by
        rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply]
      have hFlj : F l j = Ft j l := rfl
      rw [hFinv, hFlj]
      ring
    · intro q _ hql
      simp [Ne.symm hql]
  simp_rw [hinner, ← Finset.sum_mul]
  have hmul_ik : ∑ p, F i p * F⁻¹ p k = (1 : Matrix ι ι ℂ) i k := by
    simpa [Matrix.mul_apply] using congrFun (congrFun hFFinv i) k
  rw [hmul_ik, h2']
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

omit [StarRing A] [StarModule ℂ A] [StarCoalgebra ℂ A] in
/-- Construct the linear automorphism `u ↦ Ftᵀ * u * Ftᵀ` on a single simple coefficient block
`P = matrixCoefficientSubmodule M`. -/
private theorem exists_block_modular_equiv
    {P : Submodule ℂ A} {M : Type w} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [IsSimpleOrder (Subcomodule ℂ A M)] {n : ℕ} (b : Basis (Fin n) ℂ M)
    (hP : P = Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M))
    {Ft : Matrix (Fin n) (Fin n) ℂ} (hFt : Ft.PosDef) :
    ∃ e : P ≃ₗ[ℂ] P, ∀ i j : Fin n,
      (e ⟨Comodule.coefficientMatrix (C := A) b i j, by
        rw [hP, Comodule.coefficientMatrix_apply]
        exact Comodule.matrixCoefficient_mem_submodule _ _⟩ : A) =
        (Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
          Ftᵀ.map (algebraMap ℂ A)) i j := by
  have : Module.Finite ℂ M := Module.Finite.of_basis b
  let B0 := Comodule.matrixCoefficientBasis (C := A) b
  let eEq : P ≃ₗ[ℂ] Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) :=
    LinearEquiv.ofEq _ _ hP
  let B : Basis (Fin n × Fin n) ℂ P := B0.map eEq.symm
  have hB_val (p : Fin n × Fin n) :
      (B p : A) = Comodule.coefficientMatrix (C := A) b p.1 p.2 := by
    simp [B, B0, eEq]
  set F := Ftᵀ
  have hFFinv : F * F⁻¹ = 1 := by
    rw [← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul,
      nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hFt.isUnit),
      Matrix.transpose_one]
  have hFinvF : F⁻¹ * F = 1 := by
    rw [← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul,
      mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hFt.isUnit),
      Matrix.transpose_one]
  let fwd : P →ₗ[ℂ] P :=
    B.constr ℂ fun p ↦ ∑ q : Fin n × Fin n, (F p.1 q.1 * F q.2 p.2) • B q
  let inv : P →ₗ[ℂ] P :=
    B.constr ℂ fun p ↦ ∑ q : Fin n × Fin n, (F⁻¹ p.1 q.1 * F⁻¹ q.2 p.2) • B q
  have hcomp_aux (X Y : Matrix (Fin n) (Fin n) ℂ) (hXY : X * Y = 1) (hYX : Y * X = 1) :
      (B.constr ℂ fun p ↦ ∑ q, (Y p.1 q.1 * Y q.2 p.2) • B q).comp
        (B.constr ℂ fun p ↦ ∑ q, (X p.1 q.1 * X q.2 p.2) • B q) = LinearMap.id := by
    refine B.ext fun ⟨i, j⟩ ↦ ?_
    simp only [LinearMap.comp_apply, Basis.constr_basis, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have hterm (r : Fin n × Fin n) :
        ∑ q : Fin n × Fin n, (X i q.1 * X q.2 j * (Y q.1 r.1 * Y r.2 q.2)) • B r =
          (if r = (i, j) then (1 : ℂ) else 0) • B r := by
      rw [← Finset.sum_smul]
      congr 1
      rw [Fintype.sum_prod_type]
      calc ∑ q₁, ∑ q₂, X i q₁ * X q₂ j * (Y q₁ r.1 * Y r.2 q₂)
          = (∑ q₁, X i q₁ * Y q₁ r.1) * (∑ q₂, Y r.2 q₂ * X q₂ j) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun q₁ _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q₂ _ ↦ by ring
        _ = (1 : Matrix _ _ ℂ) i r.1 * (1 : Matrix _ _ ℂ) r.2 j := by
            have h1' : ∑ q₁, X i q₁ * Y q₁ r.1 = (1 : Matrix _ _ ℂ) i r.1 := by
              simpa [Matrix.mul_apply] using congrFun (congrFun hXY i) r.1
            have h2' : ∑ q₂, Y r.2 q₂ * X q₂ j = (1 : Matrix _ _ ℂ) r.2 j := by
              simpa [Matrix.mul_apply] using congrFun (congrFun hYX r.2) j
            rw [h1', h2']
        _ = if r = (i, j) then 1 else 0 := by
            rcases r with ⟨r₁, r₂⟩
            by_cases hr₁ : i = r₁
            · subst hr₁
              by_cases hr₂ : r₂ = j
              · subst hr₂
                simp
              · simp [hr₂]
            · simp [Matrix.one_apply, hr₁, Ne.symm hr₁]
    simp_rw [hterm]
    simp
  let e : P ≃ₗ[ℂ] P := LinearEquiv.ofLinearMap fwd inv
    (hcomp_aux F⁻¹ F hFinvF hFFinv) (hcomp_aux F F⁻¹ hFFinv hFinvF)
  refine ⟨e, fun i j ↦ ?_⟩
  have hmem : (⟨Comodule.coefficientMatrix (C := A) b i j, by
      rw [hP, Comodule.coefficientMatrix_apply]
      exact Comodule.matrixCoefficient_mem_submodule _ _⟩ : P) = B (i, j) := by
    ext
    exact (hB_val (i, j)).symm
  rw [hmem, scalar_mul_matrix_mul_scalar_apply]
  simp only [e, LinearEquiv.coe_ofLinearMap, fwd, Basis.constr_basis, Submodule.coe_sum,
    SetLike.val_smul, hB_val]
  rw [Fintype.sum_prod_type]

/-- Existence of a modular algebra automorphism `θ : A ≃ₐ[ℂ] A` satisfying
`h (a * b) = h (b * θ a)`. -/
private theorem exists_modularAutomorphism (h : AlgebraicHaar A) :
    ∃ θ : A ≃ₐ[ℂ] A, ∀ a b : A, h (a * b) = h (b * θ a) := by
  classical
  set S := Comodule.simpleCoefficientSubmodules ℂ A
  have hS_top : sSup S = ⊤ :=
    (AlgebraicHaar.isLinearlyReductive.{u, 0} h).sSup_simpleCoefficientSubmodules_eq_top
  have hInt : DirectSum.IsInternal (fun P : S ↦ (P.1 : Submodule ℂ A)) :=
    (AlgebraicHaar.isLinearlyReductive.{u, 0} h).isInternal_simpleCoefficientSubmodules
  let iso : (⨁ P : S, P.1) ≃ₗ[ℂ] A :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap fun P : S ↦ (P.1 : Submodule ℂ A)) hInt
  have hiso (z : ⨁ P : S, P.1) :
      iso z = DirectSum.coeLinearMap (fun P : S ↦ (P.1 : Submodule ℂ A)) z := rfl
  -- For each simple coefficient block `P : S`, pick a simple unitary witness and its Schur matrix.
  have hblock (P : S) :
      ∃ (M : ComoduleCat.{0, u, u} ℂ A) (_ : IsSimpleOrder (Subcomodule ℂ A M))
        (n : ℕ) (b : Basis (Fin n) ℂ M) (Ft : Matrix (Fin n) (Fin n) ℂ),
        P.1 = Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ∧
        Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix (Fin n) (Fin n) A) ∧
        Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
        (∀ i j k l,
          h (star (Comodule.coefficientMatrix (C := A) b i j) *
              Comodule.coefficientMatrix (C := A) b k l) =
            if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
        (∀ i j k l,
          h (Comodule.coefficientMatrix (C := A) b i j *
              star (Comodule.coefficientMatrix (C := A) b k l)) =
            if i = k then Ft j l / Ft.trace else 0) := by
    obtain ⟨M, hM, hPM⟩ := Comodule.mem_simpleCoefficientSubmodules.mp P.2
    have : IsSimpleOrder (Subcomodule ℂ A M) := hM
    have : Module.Finite ℂ M := Subcomodule.finite_of_isSimpleOrder (R := ℂ) (C := A)
    obtain ⟨b, hb⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
      h.right_invariant h.functional_ne_zero h.positive (Module.finBasis ℂ M)
    obtain ⟨Ft, ⟨hFt, htr, h1', h2'⟩, _⟩ := h.schur_orthogonality b hb
    exact ⟨M, hM, finrank ℂ M, b, Ft, hPM, hb, hFt, htr, h1', h2'⟩
  choose M_P hM_P n_P b_P Ft_P hP_eq hb_P hFt_P htr_P hSchur1_P hSchur2_P using hblock
  choose e_P he_P using fun P : S ↦
    have : IsSimpleOrder (Subcomodule ℂ A (M_P P)) := hM_P P
    exists_block_modular_equiv (b_P P) (hP_eq P) (hFt_P P)
  -- Assemble the blockwise automorphisms on the internal direct sum `A ≃ₗ[ℂ] ⨁ P, P.1`.
  let fwdDS : (⨁ P : S, P.1) →ₗ[ℂ] (⨁ P : S, P.1) :=
    DirectSum.lmap fun P ↦ (e_P P).toLinearMap
  let invDS : (⨁ P : S, P.1) →ₗ[ℂ] (⨁ P : S, P.1) :=
    DirectSum.lmap fun P ↦ (e_P P).symm.toLinearMap
  have hDS_right : fwdDS.comp invDS = LinearMap.id := by
    simp [fwdDS, invDS, ← DirectSum.lmap_comp]
  have hDS_left : invDS.comp fwdDS = LinearMap.id := by
    simp [fwdDS, invDS, ← DirectSum.lmap_comp]
  let eDS : (⨁ P : S, P.1) ≃ₗ[ℂ] (⨁ P : S, P.1) :=
    LinearEquiv.ofLinearMap fwdDS invDS hDS_right hDS_left
  let θ_lin : A ≃ₗ[ℂ] A := iso.symm.trans (eDS.trans iso)
  have hθ_block (P : S) (x : P.1) : θ_lin (x : A) = (e_P P x : A) := by
    have hsymm : iso.symm (x : A) = DirectSum.of (fun Q : S ↦ (Q.1 : Type u)) P x := by
      apply iso.injective
      rw [iso.apply_symm_apply, hiso, DirectSum.coeLinearMap_of]
    simp only [θ_lin, LinearEquiv.trans_apply, eDS, LinearEquiv.coe_ofLinearMap, hsymm, fwdDS,
      DirectSum.lmap_of, hiso, DirectSum.coeLinearMap_of, LinearEquiv.coe_coe]
  have hθ_coeff (P : S) (i j : Fin (n_P P)) :
      θ_lin (Comodule.coefficientMatrix (C := A) (b_P P) i j) =
        ((Ft_P P)ᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) (b_P P) *
          (Ft_P P)ᵀ.map (algebraMap ℂ A)) i j := by
    have hmem : Comodule.coefficientMatrix (C := A) (b_P P) i j ∈ P.1 := by
      rw [hP_eq P, Comodule.coefficientMatrix_apply]
      exact Comodule.matrixCoefficient_mem_submodule _ _
    simpa using (hθ_block P ⟨_, hmem⟩).trans (he_P P i j)
  -- Verify the modular identity on block generators `u_P i j` and `star (u_Q k l)`.
  have hmod_gen (P Q : S) (i j : Fin (n_P P)) (k l : Fin (n_P Q)) :
      h (Comodule.coefficientMatrix (C := A) (b_P P) i j *
          star (Comodule.coefficientMatrix (C := A) (b_P Q) k l)) =
        h (star (Comodule.coefficientMatrix (C := A) (b_P Q) k l) *
          θ_lin (Comodule.coefficientMatrix (C := A) (b_P P) i j)) := by
    rw [hθ_coeff P i j]
    by_cases hPQ : P = Q
    · subst hPQ
      exact (apply_star_mul_modular_entry h (b_P P) (hFt_P P) (htr_P P)
        (hSchur1_P P) (hSchur2_P P) i j k l).symm
    · have : IsSimpleOrder (Subcomodule ℂ A (M_P P)) := hM_P P
      have : IsSimpleOrder (Subcomodule ℂ A (M_P Q)) := hM_P Q
      have hHomPQ : ∀ g : Comodule.Hom ℂ A (M_P P) (M_P Q), g = 0 := by
        by_contra! H
        obtain ⟨g, hg⟩ := H
        apply hPQ
        ext1
        rw [hP_eq P, hP_eq Q, Comodule.matrixCoefficientSubmodule_eq_of_ne_zero hg]
      have hHomQP : ∀ g : Comodule.Hom ℂ A (M_P Q) (M_P P), g = 0 := by
        by_contra! H
        obtain ⟨g, hg⟩ := H
        apply hPQ
        ext1
        rw [hP_eq P, hP_eq Q, Comodule.matrixCoefficientSubmodule_eq_of_ne_zero hg]
      have hL : h (Comodule.coefficientMatrix (C := A) (b_P P) i j *
          star (Comodule.coefficientMatrix (C := A) (b_P Q) k l)) = 0 :=
        h.left_invariant.apply_coefficientMatrix_mul_star_eq_zero (b_P P) (b_P Q) (hb_P Q)
          hHomQP i j k l
      have hR : h (star (Comodule.coefficientMatrix (C := A) (b_P Q) k l) *
          ((Ft_P P)ᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) (b_P P) *
            (Ft_P P)ᵀ.map (algebraMap ℂ A)) i j) = 0 := by
        rw [scalar_mul_matrix_mul_scalar_apply, Finset.mul_sum, map_sum]
        refine Finset.sum_eq_zero fun p _ ↦ ?_
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_eq_zero fun q _ ↦ ?_
        have hzero : h (star (Comodule.coefficientMatrix (C := A) (b_P Q) k l) *
            Comodule.coefficientMatrix (C := A) (b_P P) p q) = 0 :=
          h.right_invariant.apply_star_coefficientMatrix_mul_eq_zero (b_P Q) (b_P P) (hb_P Q)
            hHomPQ k l p q
        rw [mul_smul_comm, map_smul, hzero, smul_zero]
      rw [hL, hR]
  -- Extend from block generators to all `a, b : A`.
  have hmod_gen_all (P : S) (i j : Fin (n_P P)) (b : A) :
      h (Comodule.coefficientMatrix (C := A) (b_P P) i j * b) =
        h (b * θ_lin (Comodule.coefficientMatrix (C := A) (b_P P) i j)) := by
    let a := Comodule.coefficientMatrix (C := A) (b_P P) i j
    let K : Submodule ℂ A :=
      { carrier := {y : A | h (a * star y) = h (star y * θ_lin a)}
        zero_mem' := by simp
        add_mem' := fun {y₁ y₂} hy₁ hy₂ ↦ by
          simp only [Set.mem_ofPred_eq, star_add, mul_add, add_mul, map_add] at hy₁ hy₂ ⊢
          rw [hy₁, hy₂]
        smul_mem' := fun c {y} hy ↦ by
          simp only [Set.mem_ofPred_eq, star_smul, mul_smul_comm, smul_mul_assoc, map_smul] at hy ⊢
          rw [hy] }
    have hK : K = ⊤ := by
      rw [eq_top_iff, ← hS_top]
      refine sSup_le fun Q hQ ↦ ?_
      have hQeq : Q = _ := hP_eq ⟨Q, hQ⟩
      rw [hQeq, ← Comodule.span_range_coefficientMatrix_eq (b_P ⟨Q, hQ⟩), Submodule.span_le]
      rintro _ ⟨⟨k, l⟩, rfl⟩
      exact hmod_gen P ⟨Q, hQ⟩ i j k l
    have hmem : star b ∈ K := by rw [hK]; trivial
    simpa [K, a] using hmem
  have hmod (a b : A) : h (a * b) = h (b * θ_lin a) := by
    let L : Submodule ℂ A :=
      { carrier := {x : A | h (x * b) = h (b * θ_lin x)}
        zero_mem' := by simp
        add_mem' := fun {x₁ x₂} hx₁ hx₂ ↦ by
          simp only [Set.mem_ofPred_eq, add_mul, map_add, mul_add] at hx₁ hx₂ ⊢
          rw [hx₁, hx₂]
        smul_mem' := fun c {x} hx ↦ by
          simp only [Set.mem_ofPred_eq, smul_mul_assoc, map_smul, mul_smul_comm] at hx ⊢
          rw [hx] }
    have hL : L = ⊤ := by
      rw [eq_top_iff, ← hS_top]
      refine sSup_le fun P hP ↦ ?_
      have hPeq : P = _ := hP_eq ⟨P, hP⟩
      rw [hPeq, ← Comodule.span_range_coefficientMatrix_eq (b_P ⟨P, hP⟩), Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact hmod_gen_all ⟨P, hP⟩ i j b
    have hmem : a ∈ L := by rw [hL]; trivial
    exact hmem
  -- Upgrade `θ_lin` to an algebra automorphism via right algebraic faithfulness of `h`.
  have hmap_one : θ_lin 1 = 1 := by
    refine sub_eq_zero.mp (h.eq_zero_of_forall_mul_eq_zero_right fun c ↦ ?_)
    rw [mul_sub, map_sub, mul_one, ← hmod 1 c, one_mul, sub_self]
  have hmap_mul (a b : A) : θ_lin (a * b) = θ_lin a * θ_lin b := by
    refine sub_eq_zero.mp (h.eq_zero_of_forall_mul_eq_zero_right fun c ↦ ?_)
    rw [mul_sub, map_sub, ← hmod (a * b) c, mul_assoc, hmod a (b * c), mul_assoc,
      hmod b (c * θ_lin a), mul_assoc, sub_self]
  exact ⟨AlgEquiv.ofLinearEquiv θ_lin hmap_one hmap_mul, hmod⟩

/-- The unique modular algebra automorphism `θ : A ≃ₐ[ℂ] A` of an algebraic Haar state,
characterized by `h (a * b) = h (b * θ a)` (`apply_mul_eq_mul_modularAutomorphism`). -/
noncomputable def modularAutomorphism (h : AlgebraicHaar A) : A ≃ₐ[ℂ] A :=
  (exists_modularAutomorphism h).choose

/-- The modular KMS-type identity `h (a * b) = h (b * h.modularAutomorphism a)`
(Neshveyev–Tuset, Theorem 1.7.3). -/
theorem apply_mul_eq_mul_modularAutomorphism (h : AlgebraicHaar A) (a b : A) :
    h (a * b) = h (b * h.modularAutomorphism a) :=
  (exists_modularAutomorphism h).choose_spec a b

/-- **Existence and uniqueness of the modular automorphism (Neshveyev–Tuset, Theorem 1.7.3).**
There is a unique algebra automorphism `θ : A ≃ₐ[ℂ] A` satisfying `h (a * b) = h (b * θ a)`
for all `a, b : A`. -/
theorem existsUnique_modularAutomorphism (h : AlgebraicHaar A) :
    ∃! θ : A ≃ₐ[ℂ] A, ∀ a b : A, h (a * b) = h (b * θ a) := by
  refine ⟨h.modularAutomorphism, h.apply_mul_eq_mul_modularAutomorphism, fun θ hθ ↦ ?_⟩
  ext a
  refine sub_eq_zero.mp (h.eq_zero_of_forall_mul_eq_zero_right fun b ↦ ?_)
  rw [mul_sub, map_sub, ← hθ a b, ← h.apply_mul_eq_mul_modularAutomorphism a b, sub_self]

/-- The modular automorphism is trivial if and only if the algebraic Haar state is tracial. -/
theorem modularAutomorphism_eq_refl_iff (h : AlgebraicHaar A) :
    h.modularAutomorphism = AlgEquiv.refl ↔ ∀ a b : A, h (a * b) = h (b * a) := by
  constructor
  · intro hrefl a b
    rw [h.apply_mul_eq_mul_modularAutomorphism a b, hrefl, AlgEquiv.coe_refl, id_eq]
  · intro htr
    exact (h.existsUnique_modularAutomorphism).unique
      h.apply_mul_eq_mul_modularAutomorphism (fun a b ↦ by simpa using htr a b)

/-- The modular automorphism acts on the coefficient matrix of any finite-dimensional simple
unitary comodule by two-sided multiplication by the transpose of its Schur matrix:
`u.map h.modularAutomorphism = Ftᵀ * u * Ftᵀ`. -/
theorem modularAutomorphism_coefficientMatrix (h : AlgebraicHaar A)
    {M : Type w} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [IsSimpleOrder (Subcomodule ℂ A M)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef) (htr : Ft.trace = Ft⁻¹.trace)
    (h2' : ∀ i j k l,
      h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0) :
    (Comodule.coefficientMatrix (C := A) b).map h.modularAutomorphism =
      Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
        Ftᵀ.map (algebraMap ℂ A) := by
  obtain ⟨Ft₀, ⟨hFt₀, htr₀, h1₀, h2₀⟩, _⟩ := h.schur_orthogonality b hu
  have hFt_eq : Ft = Ft₀ := h.eq_of_schur_orthogonality b hFt htr h2' hFt₀ htr₀ h2₀
  subst hFt_eq
  set u := Comodule.coefficientMatrix (C := A) b
  set W := Ft.transpose.map (algebraMap ℂ A) * u * Ft.transpose.map (algebraMap ℂ A)
  have hS_top : sSup (Comodule.simpleCoefficientSubmodules ℂ A) = ⊤ :=
    (AlgebraicHaar.isLinearlyReductive.{u, 0} h).sSup_simpleCoefficientSubmodules_eq_top
  ext i j
  rw [Matrix.map_apply]
  refine sub_eq_zero.mp (h.eq_zero_of_forall_mul_eq_zero_right fun x ↦ ?_)
  rw [mul_sub, map_sub, sub_eq_zero]
  -- Suffices to check `h (u i j * star y) = h (star y * W i j)` for every `y : A`.
  let K : Submodule ℂ A :=
    { carrier := {y : A | h (u i j * star y) = h (star y * W i j)}
      zero_mem' := by simp
      add_mem' := fun {y₁ y₂} hy₁ hy₂ ↦ by
        simp only [Set.mem_ofPred_eq, star_add, mul_add, add_mul, map_add] at hy₁ hy₂ ⊢
        rw [hy₁, hy₂]
      smul_mem' := fun c {y} hy ↦ by
        simp only [Set.mem_ofPred_eq, star_smul, mul_smul_comm, smul_mul_assoc, map_smul] at hy ⊢
        rw [hy] }
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← hS_top]
    refine sSup_le fun P hP ↦ ?_
    by_cases hPM : P = Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M)
    · rw [hPM, ← Comodule.span_range_coefficientMatrix_eq b, Submodule.span_le]
      rintro _ ⟨⟨k, l⟩, rfl⟩
      exact (apply_star_mul_modular_entry h b hFt htr h1₀ h2' i j k l).symm
    · obtain ⟨N, hN, hPN⟩ := Comodule.mem_simpleCoefficientSubmodules.mp hP
      have : IsSimpleOrder (Subcomodule ℂ A N) := hN
      have : Module.Finite ℂ N := Subcomodule.finite_of_isSimpleOrder (R := ℂ) (C := A) (M := N)
      obtain ⟨c, hc⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
        h.right_invariant h.functional_ne_zero h.positive (Module.finBasis ℂ N)
      have hHomMN : ∀ g : Comodule.Hom ℂ A M N, g = 0 := by
        by_contra! H
        obtain ⟨g, hg⟩ := H
        exact hPM (hPN.trans (Comodule.matrixCoefficientSubmodule_eq_of_ne_zero hg).symm)
      have hHomNM : ∀ g : Comodule.Hom ℂ A N M, g = 0 := by
        by_contra! H
        obtain ⟨g, hg⟩ := H
        exact hPM (hPN.trans (Comodule.matrixCoefficientSubmodule_eq_of_ne_zero hg))
      rw [hPN, ← Comodule.span_range_coefficientMatrix_eq c, Submodule.span_le]
      rintro _ ⟨⟨k, l⟩, rfl⟩
      have hL : h (u i j * star (Comodule.coefficientMatrix (C := A) c k l)) = 0 :=
        h.left_invariant.apply_coefficientMatrix_mul_star_eq_zero b c hc hHomNM i j k l
      have hR : h (star (Comodule.coefficientMatrix (C := A) c k l) * W i j) = 0 := by
        have hW : W i j = ∑ p, ∑ q, (Ftᵀ i p * Ftᵀ q j) • u p q :=
          scalar_mul_matrix_mul_scalar_apply Ftᵀ Ftᵀ u i j
        rw [hW, Finset.mul_sum, map_sum]
        refine Finset.sum_eq_zero fun p _ ↦ ?_
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_eq_zero fun q _ ↦ ?_
        have hzero : h (star (Comodule.coefficientMatrix (C := A) c k l) * u p q) = 0 :=
          h.right_invariant.apply_star_coefficientMatrix_mul_eq_zero c b hc hHomMN k l p q
        rw [mul_smul_comm, map_smul, hzero, smul_zero]
      exact hL.trans hR.symm
  have hmem : star x ∈ K := by rw [hK]; trivial
  have heq : h (u i j * x) = h (x * W i j) := by simpa [K] using hmem
  rw [← h.apply_mul_eq_mul_modularAutomorphism (u i j) x, heq]

/-- A positive definite matrix `Ft` whose transpose equals `c • 1` with `c * c = 1` equals `1`. -/
private theorem eq_one_of_posDef_of_scalar_smul_one {ι : Type*} [DecidableEq ι]
    [Nonempty ι] {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef) {c : ℂ} (hF : Ftᵀ = c • 1)
    (hc_sq : c * c = 1) : Ft = 1 := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hpos : (0 : ℂ) < c := by
    have hdiag : (0 : ℂ) < Ft i₀ i₀ := by
      have hq := hFt.2 (x := Finsupp.single i₀ (1 : ℂ)) (Finsupp.single_ne_zero.mpr one_ne_zero)
      simpa [Finsupp.sum_single_index] using hq
    have hci : c = Ft i₀ i₀ := by
      have h := congrFun (congrFun hF i₀) i₀
      simpa using h.symm
    rwa [hci]
  obtain ⟨hre, him⟩ := Complex.lt_def.mp hpos
  simp only [Complex.zero_re] at hre
  have hce : c = (c.re : ℂ) := Complex.ext rfl him.symm
  have hc1 : c = 1 := by
    rw [hce] at hc_sq ⊢
    norm_cast at hc_sq ⊢
    nlinarith
  have hFtT : Ftᵀ = 1 := by rw [hF, hc1, one_smul]
  simpa using congrArg Matrix.transpose hFtT

/-- **Kac characterization (Neshveyev–Tuset, Proposition 1.7.7).**
The algebraic Haar state on a complex Hopf star algebra is tracial if and only if the antipode is
involutive (`S² = id`). -/
theorem apply_mul_comm_iff_antipode_involutive (h : AlgebraicHaar A) :
    (∀ a b : A, h (a * b) = h (b * a)) ↔
      ∀ a : A, HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ a) = a := by
  have hS_top : sSup (Comodule.simpleCoefficientSubmodules ℂ A) = ⊤ :=
    (AlgebraicHaar.isLinearlyReductive.{u, 0} h).sSup_simpleCoefficientSubmodules_eq_top
  constructor
  · -- Tracial Haar state ⇒ `θ = id` ⇒ `Ft = 1` on every simple block ⇒ `S² = id`.
    intro htr
    have hθ : h.modularAutomorphism = AlgEquiv.refl := h.modularAutomorphism_eq_refl_iff.mpr htr
    let f : A →ₗ[ℂ] A :=
      (HopfAlgebra.antipode ℂ (A := A)).comp (HopfAlgebra.antipode ℂ (A := A)) - LinearMap.id
    have hker : LinearMap.ker f = ⊤ := by
      rw [eq_top_iff, ← hS_top]
      refine sSup_le fun P hP ↦ ?_
      obtain ⟨M, hM, hPM⟩ := Comodule.mem_simpleCoefficientSubmodules.mp hP
      have : IsSimpleOrder (Subcomodule ℂ A M) := hM
      have : Module.Finite ℂ M := Subcomodule.finite_of_isSimpleOrder (R := ℂ) (C := A) (M := M)
      obtain ⟨b, hb⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
        h.right_invariant h.functional_ne_zero h.positive (Module.finBasis ℂ M)
      obtain ⟨Ft, ⟨hFt, htrFt, _, h2'⟩, _⟩ := h.schur_orthogonality b hb
      have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
      have : Nonempty (Fin (finrank ℂ M)) := b.index_nonempty
      have hmod_u := h.modularAutomorphism_coefficientMatrix b hb hFt htrFt h2'
      rw [hθ] at hmod_u
      have hfix : Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
          Ftᵀ.map (algebraMap ℂ A) = Comodule.coefficientMatrix (C := A) b := by
        simpa [Matrix.map_id] using hmod_u.symm
      obtain ⟨c, hc0, hF1, hF2⟩ :=
        (Comodule.mul_coefficientMatrix_mul_eq_self_iff b Ftᵀ Ftᵀ).mp hfix
      have hcsq : c * c = 1 := by
        obtain ⟨i₀⟩ := ‹Nonempty (Fin (finrank ℂ M))›
        have hcc : c = c⁻¹ := by
          have h' := congrFun (congrFun (hF1.symm.trans hF2) i₀) i₀
          simpa using h'
        calc c * c = c * c⁻¹ := by rw [← hcc]
          _ = 1 := mul_inv_cancel₀ hc0
      have hFt1 : Ft = 1 := eq_one_of_posDef_of_scalar_smul_one hFt hF1 hcsq
      have hS2_u := h.map_antipode_antipode_coefficientMatrix b hb hFt htrFt h2'
      have hinv1 : (1 : Matrix (Fin (finrank ℂ M)) (Fin (finrank ℂ M)) ℂ)⁻¹ = 1 :=
        Matrix.inv_eq_right_inv (Matrix.one_mul 1)
      have hmap1 : (1 : Matrix (Fin (finrank ℂ M)) (Fin (finrank ℂ M)) ℂ).map (algebraMap ℂ A) =
          1 := Matrix.map_one (algebraMap ℂ A) (map_zero (algebraMap ℂ A))
            (_root_.map_one (algebraMap ℂ A))
      rw [hFt1, Matrix.transpose_one, hinv1, hmap1, Matrix.one_mul, Matrix.mul_one] at hS2_u
      rw [hPM, ← Comodule.span_range_coefficientMatrix_eq b, Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have hij := congrFun (congrFun hS2_u i) j
      simp only [SetLike.mem_coe, LinearMap.mem_ker, f, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.id_apply, sub_eq_zero]
      simpa using hij
    intro a
    have ha : a ∈ LinearMap.ker f := by rw [hker]; trivial
    exact sub_eq_zero.mp ha
  · -- `S² = id` ⇒ `Ft = 1` on every simple block ⇒ `θ = id` ⇒ `h` is tracial.
    intro hS2
    rw [← h.modularAutomorphism_eq_refl_iff]
    let f : A →ₗ[ℂ] A := h.modularAutomorphism.toLinearMap - LinearMap.id
    have hker : LinearMap.ker f = ⊤ := by
      rw [eq_top_iff, ← hS_top]
      refine sSup_le fun P hP ↦ ?_
      obtain ⟨M, hM, hPM⟩ := Comodule.mem_simpleCoefficientSubmodules.mp hP
      have : IsSimpleOrder (Subcomodule ℂ A M) := hM
      have : Module.Finite ℂ M := Subcomodule.finite_of_isSimpleOrder (R := ℂ) (C := A) (M := M)
      obtain ⟨b, hb⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
        h.right_invariant h.functional_ne_zero h.positive (Module.finBasis ℂ M)
      obtain ⟨Ft, ⟨hFt, htrFt, _, h2'⟩, _⟩ := h.schur_orthogonality b hb
      have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
      have : Nonempty (Fin (finrank ℂ M)) := b.index_nonempty
      have hS2_u := h.map_antipode_antipode_coefficientMatrix b hb hFt htrFt h2'
      have hfix : Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
          Ftᵀ⁻¹.map (algebraMap ℂ A) = Comodule.coefficientMatrix (C := A) b := by
        rw [← hS2_u]
        ext i j
        exact hS2 _
      obtain ⟨c, hc0, hF1, hF2⟩ :=
        (Comodule.mul_coefficientMatrix_mul_eq_self_iff b Ftᵀ Ftᵀ⁻¹).mp hfix
      have hcsq : c * c = 1 := by
        have htrF : Ftᵀ.trace = Ftᵀ⁻¹.trace := by
          rw [Matrix.trace_transpose, ← Matrix.transpose_nonsing_inv, Matrix.trace_transpose, htrFt]
        rw [hF2, hF1, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
          smul_eq_mul, smul_eq_mul] at htrF
        have hcard : (Fintype.card (Fin (finrank ℂ M)) : ℂ) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        have hcc : c = c⁻¹ := mul_right_cancel₀ hcard htrF
        calc c * c = c * c⁻¹ := by rw [← hcc]
          _ = 1 := mul_inv_cancel₀ hc0
      have hFt1 : Ft = 1 := eq_one_of_posDef_of_scalar_smul_one hFt hF1 hcsq
      have hmod_u := h.modularAutomorphism_coefficientMatrix b hb hFt htrFt h2'
      have hmap1 : (1 : Matrix (Fin (finrank ℂ M)) (Fin (finrank ℂ M)) ℂ).map (algebraMap ℂ A) =
          1 := Matrix.map_one (algebraMap ℂ A) (map_zero (algebraMap ℂ A))
            (_root_.map_one (algebraMap ℂ A))
      rw [hFt1, Matrix.transpose_one, hmap1, Matrix.one_mul, Matrix.mul_one] at hmod_u
      rw [hPM, ← Comodule.span_range_coefficientMatrix_eq b, Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have hij := congrFun (congrFun hmod_u i) j
      simp only [SetLike.mem_coe, LinearMap.mem_ker, f, LinearMap.sub_apply,
        AlgEquiv.toLinearMap_apply, LinearMap.id_apply, sub_eq_zero]
      simpa using hij
    ext a
    have ha : a ∈ LinearMap.ker f := by rw [hker]; trivial
    exact sub_eq_zero.mp ha

end TauCeti.AlgebraicHaar
