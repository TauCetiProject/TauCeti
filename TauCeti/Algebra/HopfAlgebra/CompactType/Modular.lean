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

Every algebraic Haar state `h : AlgebraicHaar A` admits a unique algebra automorphism
`θ : A ≃ₐ[ℂ] A` satisfying `h (a * b) = h (b * θ a)` (Neshveyev–Tuset, Theorem 1.7.3). On a finite
simple unitary comodule with Schur matrix `Ft`, `u.map θ = Ftᵀ * u * Ftᵀ`, whereas
`u.map (S ∘ S) = Ftᵀ * u * (Ftᵀ)⁻¹`. Comparing the two yields the Kac characterization: `h` is
tracial if and only if `S ∘ S = id` (Neshveyev–Tuset, Proposition 1.7.7).

## Main declarations

* `TauCeti.AlgebraicHaar.modularAutomorphism`,
  `TauCeti.AlgebraicHaar.apply_mul_eq_mul_modularAutomorphism`,
  `TauCeti.AlgebraicHaar.existsUnique_modularAutomorphism`
* `TauCeti.AlgebraicHaar.modularAutomorphism_eq_refl_iff`,
  `TauCeti.AlgebraicHaar.modularAutomorphism_coefficientMatrix`,
  `TauCeti.AlgebraicHaar.apply_mul_comm_iff_antipode_involutive`

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
private theorem scalar_mul_matrix_mul_scalar_apply {ι : Type*} [Fintype ι]
    (X Y : Matrix ι ι ℂ) (u : Matrix ι ι A) (i j : ι) :
    (X.map (algebraMap ℂ A) * u * Y.map (algebraMap ℂ A)) i j =
      ∑ p, ∑ q, (X i p * Y q j) • u p q := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [mul_comm (Y _ _)]

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
/-- Core weighted Schur identity on a single simple unitary block: pairing `star (u k l)` against
`(Ftᵀ * u * Ftᵀ) i j` reproduces `h (u i j * star (u k l))`. -/
private theorem apply_star_mul_modular_entry (h : AlgebraicHaar A)
    {M : Type w} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ M)
    {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef) (htr : Ft.trace = Ft⁻¹.trace)
    (h1' : ∀ i j k l, h (star (Comodule.coefficientMatrix (C := A) b i j) *
          Comodule.coefficientMatrix (C := A) b k l) =
        if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0)
    (h2' : ∀ i j k l, h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0)
    (i j k l : ι) :
    h (star (Comodule.coefficientMatrix (C := A) b k l) *
        (Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
          Ftᵀ.map (algebraMap ℂ A)) i j) =
      h (Comodule.coefficientMatrix (C := A) b i j *
        star (Comodule.coefficientMatrix (C := A) b k l)) := by
  set F := Ftᵀ
  have hFFinv : F * F⁻¹ = 1 := by
    rw [← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul,
      nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hFt.isUnit), Matrix.transpose_one]
  rw [scalar_mul_matrix_mul_scalar_apply, Finset.mul_sum, map_sum]
  simp_rw [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, h1']
  have hinner (p : ι) :
      ∑ q, F i p * F q j * (if l = q then Ft⁻¹ k p / Ft⁻¹.trace else 0) =
        F i p * F⁻¹ p k * (Ft j l / Ft.trace) := by
    rw [Finset.sum_eq_single l (fun q _ hql ↦ by simp [Ne.symm hql]) (by simp)]
    simp only [↓reduceIte, ← htr, show F⁻¹ p k = Ft⁻¹ k p by
      rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply]]
    change F i p * Ft j l * (Ft⁻¹ k p / Ft.trace) = _; ring
  simp_rw [hinner, ← Finset.sum_mul]
  rw [show ∑ p, F i p * F⁻¹ p k = (1 : Matrix ι ι ℂ) i k by
    simpa [Matrix.mul_apply] using congrFun (congrFun hFFinv i) k, h2']
  by_cases hik : i = k <;> simp [Matrix.one_apply, hik]

/-- The modular pairing identity `h (u i j * x) = h (x * (Ftᵀ * u * Ftᵀ) i j)` holds for every
`x : A` and every entry `u i j` of a finite simple unitary comodule with Schur matrix `Ft`. -/
private theorem apply_mul_eq_mul_modular_block (h : AlgebraicHaar A)
    {M : Type w} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [IsSimpleOrder (Subcomodule ℂ A M)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ M) {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef) (htr : Ft.trace = Ft⁻¹.trace)
    (h1' : ∀ i j k l, h (star (Comodule.coefficientMatrix (C := A) b i j) *
          Comodule.coefficientMatrix (C := A) b k l) =
        if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0)
    (h2' : ∀ i j k l, h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0)
    (i j : ι) (x : A) :
    h (Comodule.coefficientMatrix (C := A) b i j * x) =
      h (x * (Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
        Ftᵀ.map (algebraMap ℂ A)) i j) := by
  set u := Comodule.coefficientMatrix (C := A) b
  set W := Ftᵀ.map (algebraMap ℂ A) * u * Ftᵀ.map (algebraMap ℂ A)
  let K : Submodule ℂ A :=
    { carrier := {y : A | h (u i j * star y) = h (star y * W i j)}
      zero_mem' := by simp
      add_mem' := fun hy₁ hy₂ ↦ by
        simpa [star_add, mul_add, add_mul, map_add] using congrArg₂ (· + ·) hy₁ hy₂
      smul_mem' := fun c _ hy ↦ by
        simpa [star_smul, mul_smul_comm, smul_mul_assoc, map_smul] using congrArg (star c • ·) hy }
  have hK : K = ⊤ := by
    rw [eq_top_iff,
      ← (AlgebraicHaar.isLinearlyReductive.{u, 0} h).sSup_simpleCoefficientSubmodules_eq_top]
    refine sSup_le fun P hP ↦ ?_
    by_cases hPM : P = Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M)
    · rw [hPM, ← Comodule.span_range_coefficientMatrix_eq b, Submodule.span_le]
      rintro _ ⟨⟨k, l⟩, rfl⟩
      exact (apply_star_mul_modular_entry h b hFt htr h1' h2' i j k l).symm
    · obtain ⟨N, hN, hPN⟩ := Comodule.mem_simpleCoefficientSubmodules.mp hP
      have : IsSimpleOrder (Subcomodule ℂ A N) := hN
      have : Module.Finite ℂ N := Subcomodule.finite_of_isSimpleOrder (R := ℂ) (C := A)
      obtain ⟨c, hc⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
        h.right_invariant h.functional_ne_zero h.positive (Module.finBasis ℂ N)
      have hHomMN : ∀ g : Comodule.Hom ℂ A M N, g = 0 := fun g ↦ by_contra fun hg ↦
        hPM (hPN.trans (Comodule.matrixCoefficientSubmodule_eq_of_ne_zero hg).symm)
      have hHomNM : ∀ g : Comodule.Hom ℂ A N M, g = 0 := fun g ↦ by_contra fun hg ↦
        hPM (hPN.trans (Comodule.matrixCoefficientSubmodule_eq_of_ne_zero hg))
      rw [hPN, ← Comodule.span_range_coefficientMatrix_eq c, Submodule.span_le]
      rintro _ ⟨⟨k, l⟩, rfl⟩
      have hL := h.left_invariant.apply_coefficientMatrix_mul_star_eq_zero b c hc hHomNM i j k l
      have hR : h (star (Comodule.coefficientMatrix (C := A) c k l) * W i j) = 0 := by
        rw [show W i j = ∑ p, ∑ q, (Ftᵀ i p * Ftᵀ q j) • u p q from
          scalar_mul_matrix_mul_scalar_apply Ftᵀ Ftᵀ u i j]
        simp only [u, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
          ← AlgebraicHaar.functional_apply,
          h.right_invariant.apply_star_coefficientMatrix_mul_eq_zero c b hc hHomMN k l,
          smul_zero, Finset.sum_const_zero]
      exact hL.trans hR.symm
  simpa [K] using (hK ▸ Submodule.mem_top : star x ∈ K)

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
  let B : Basis (Fin n × Fin n) ℂ P :=
    (Comodule.matrixCoefficientBasis (C := A) b).map (LinearEquiv.ofEq _ _ hP).symm
  let eMat : P ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun x := Matrix.of fun p q ↦ B.repr x (p, q)
      invFun X := ∑ p, ∑ q, X p q • B (p, q)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp
      left_inv x := (Fintype.sum_prod_type _).symm.trans (B.sum_repr x)
      right_inv X := by ext p q; simp [map_sum, Finsupp.single_apply, ite_and] }
  have hmul : Ft * Ft⁻¹ = 1 := mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hFt.isUnit)
  have hmul' : Ft⁻¹ * Ft = 1 := nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hFt.isUnit)
  let mulLR : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun X := Ft * X * Ft
      invFun X := Ft⁻¹ * X * Ft⁻¹
      map_add' _ _ := by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' _ _ := by simp
      left_inv X := by
        simp [Matrix.mul_assoc, ← Matrix.mul_assoc Ft⁻¹ Ft, hmul', Matrix.mul_assoc X, hmul]
      right_inv X := by
        simp [Matrix.mul_assoc, ← Matrix.mul_assoc Ft Ft⁻¹, hmul, Matrix.mul_assoc X, hmul'] }
  refine ⟨eMat.trans (mulLR.trans eMat.symm), fun i j ↦ ?_⟩
  have hmem : (⟨Comodule.coefficientMatrix (C := A) b i j, by
      rw [hP, Comodule.coefficientMatrix_apply]
      exact Comodule.matrixCoefficient_mem_submodule _ _⟩ : P) = B (i, j) := by ext; simp [B]
  have heMatB : eMat (B (i, j)) = Matrix.single i j (1 : ℂ) := by
    ext p q; change B.repr (B (i, j)) (p, q) = _; simp [Matrix.single, Finsupp.single_apply]
  rw [hmem, LinearEquiv.trans_apply, LinearEquiv.trans_apply, heMatB,
    scalar_mul_matrix_mul_scalar_apply]
  change (∑ p, ∑ q, (Ft * Matrix.single i j (1 : ℂ) * Ft) p q • B (p, q) : P).1 = _
  simp only [Submodule.coe_sum, SetLike.val_smul]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  have hsingle : (Ft * Matrix.single i j (1 : ℂ) * Ft) p q = Ft p i * Ft j q := by
    simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_eq_single j (fun r _ hr ↦ by simp [Ne.symm hr]) (by simp),
      Finset.sum_eq_single i (fun r _ hr ↦ by simp [Ne.symm hr]) (by simp)]; simp
  simp [hsingle, B]

/-- Existence of a modular algebra automorphism `θ : A ≃ₐ[ℂ] A` satisfying
`h (a * b) = h (b * θ a)`. -/
private theorem exists_modularAutomorphism (h : AlgebraicHaar A) :
    ∃ θ : A ≃ₐ[ℂ] A, ∀ a b : A, h (a * b) = h (b * θ a) := by
  classical
  set S := Comodule.simpleCoefficientSubmodules ℂ A
  have hS_top : sSup S = ⊤ :=
    (AlgebraicHaar.isLinearlyReductive.{u, 0} h).sSup_simpleCoefficientSubmodules_eq_top
  let iso : (⨁ P : S, P.1) ≃ₗ[ℂ] A := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap fun P : S ↦ (P.1 : Submodule ℂ A))
    (AlgebraicHaar.isLinearlyReductive.{u, 0} h).isInternal_simpleCoefficientSubmodules
  have hiso (z : ⨁ P : S, P.1) :
      iso z = DirectSum.coeLinearMap (fun P : S ↦ (P.1 : Submodule ℂ A)) z := rfl
  choose M_P hM_P hP_eq using fun P : S ↦ Comodule.mem_simpleCoefficientSubmodules.mp P.2
  have hb_ex (P : S) : ∃ b : Basis (Fin (finrank ℂ (M_P P))) ℂ (M_P P),
      Comodule.coefficientMatrix (C := A) b ∈
        unitary (Matrix (Fin (finrank ℂ (M_P P))) (Fin (finrank ℂ (M_P P))) A) := by
    have : IsSimpleOrder (Subcomodule ℂ A (M_P P)) := hM_P P
    have : Module.Finite ℂ (M_P P) := Subcomodule.finite_of_isSimpleOrder (R := ℂ) (C := A)
    exact Comodule.exists_basis_coefficientMatrix_mem_unitary
      h.right_invariant h.functional_ne_zero h.positive (Module.finBasis ℂ (M_P P))
  choose b_P hb_P using hb_ex
  choose Ft_P hFt_spec _ using fun P : S ↦
    have : IsSimpleOrder (Subcomodule ℂ A (M_P P)) := hM_P P
    h.schur_orthogonality (b_P P) (hb_P P)
  choose e_P he_P using fun P : S ↦
    have : IsSimpleOrder (Subcomodule ℂ A (M_P P)) := hM_P P
    exists_block_modular_equiv (b_P P) (hP_eq P) (hFt_spec P).1
  let eDS : (⨁ P : S, P.1) ≃ₗ[ℂ] (⨁ P : S, P.1) := LinearEquiv.ofLinearMap
    (DirectSum.lmap fun P ↦ (e_P P).toLinearMap) (DirectSum.lmap fun P ↦ (e_P P).symm.toLinearMap)
    (by simp [← DirectSum.lmap_comp]) (by simp [← DirectSum.lmap_comp])
  let θ_lin : A ≃ₗ[ℂ] A := iso.symm.trans (eDS.trans iso)
  have hθ_coeff (P : S) (i j : Fin (finrank ℂ (M_P P))) :
      θ_lin (Comodule.coefficientMatrix (C := A) (b_P P) i j) =
        ((Ft_P P)ᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) (b_P P) *
          (Ft_P P)ᵀ.map (algebraMap ℂ A)) i j := by
    have hmem : Comodule.coefficientMatrix (C := A) (b_P P) i j ∈ P.1 := by
      rw [hP_eq P, Comodule.coefficientMatrix_apply]
      exact Comodule.matrixCoefficient_mem_submodule _ _
    have hsymm : iso.symm (Comodule.coefficientMatrix (C := A) (b_P P) i j) =
        DirectSum.of (fun Q : S ↦ (Q.1 : Type u)) P ⟨_, hmem⟩ :=
      iso.injective (by rw [iso.apply_symm_apply, hiso, DirectSum.coeLinearMap_of])
    simpa [θ_lin, eDS, hsymm, hiso] using he_P P i j
  have hmod (a b : A) : h (a * b) = h (b * θ_lin a) := by
    let L := LinearMap.ker (h.functional.comp (LinearMap.mulRight ℂ b) -
      h.functional.comp ((LinearMap.mulLeft ℂ b).comp θ_lin.toLinearMap))
    have hL : L = ⊤ := by
      rw [eq_top_iff, ← hS_top]
      refine sSup_le fun P hP ↦ ?_
      have hPeq : P = _ := hP_eq ⟨P, hP⟩
      rw [hPeq, ← Comodule.span_range_coefficientMatrix_eq (b_P ⟨P, hP⟩), Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have : IsSimpleOrder (Subcomodule ℂ A (M_P ⟨P, hP⟩)) := hM_P ⟨P, hP⟩
      have hspec := hFt_spec ⟨P, hP⟩
      simpa [L, sub_eq_zero, hθ_coeff ⟨P, hP⟩ i j] using apply_mul_eq_mul_modular_block h
        (b_P ⟨P, hP⟩) hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2 i j b
    exact sub_eq_zero.mp (hL ▸ Submodule.mem_top : a ∈ L)
  have hmap_one : θ_lin 1 = 1 := sub_eq_zero.mp <| h.eq_zero_of_forall_mul_eq_zero_right fun c ↦ by
    rw [mul_sub, map_sub, mul_one, ← hmod 1 c, one_mul, sub_self]
  have hmap_mul (a b : A) : θ_lin (a * b) = θ_lin a * θ_lin b :=
    sub_eq_zero.mp <| h.eq_zero_of_forall_mul_eq_zero_right fun c ↦ by
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
    ∃! θ : A ≃ₐ[ℂ] A, ∀ a b : A, h (a * b) = h (b * θ a) :=
  ⟨h.modularAutomorphism, h.apply_mul_eq_mul_modularAutomorphism, fun θ hθ ↦
    AlgEquiv.ext fun a ↦ sub_eq_zero.mp <| h.eq_zero_of_forall_mul_eq_zero_right fun b ↦ by
      rw [mul_sub, map_sub, ← hθ a b, ← h.apply_mul_eq_mul_modularAutomorphism a b, sub_self]⟩

/-- The modular automorphism is trivial if and only if the algebraic Haar state is tracial. -/
theorem modularAutomorphism_eq_refl_iff (h : AlgebraicHaar A) :
    h.modularAutomorphism = AlgEquiv.refl ↔ ∀ a b : A, h (a * b) = h (b * a) :=
  ⟨fun hrefl a b ↦ by rw [h.apply_mul_eq_mul_modularAutomorphism a b, hrefl]; rfl,
   fun htr ↦ (h.existsUnique_modularAutomorphism).unique
      h.apply_mul_eq_mul_modularAutomorphism (fun a b ↦ by simpa using htr a b)⟩

/-- The modular automorphism acts on the coefficient matrix of any finite-dimensional simple
unitary comodule by two-sided multiplication by the transpose of its Schur matrix:
`u.map h.modularAutomorphism = Ftᵀ * u * Ftᵀ`. -/
theorem modularAutomorphism_coefficientMatrix (h : AlgebraicHaar A)
    {M : Type w} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [IsSimpleOrder (Subcomodule ℂ A M)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef) (htr : Ft.trace = Ft⁻¹.trace)
    (h2' : ∀ i j k l, h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0) :
    (Comodule.coefficientMatrix (C := A) b).map h.modularAutomorphism =
      Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
        Ftᵀ.map (algebraMap ℂ A) := by
  obtain ⟨Ft₀, ⟨hFt₀, htr₀, h1₀, h2₀⟩, _⟩ := h.schur_orthogonality b hu
  have hFt_eq : Ft = Ft₀ := h.eq_of_schur_orthogonality b hFt htr h2' hFt₀ htr₀ h2₀
  subst hFt_eq
  ext i j
  refine sub_eq_zero.mp (h.eq_zero_of_forall_mul_eq_zero_right fun x ↦ ?_)
  rw [mul_sub, map_sub, Matrix.map_apply, ← h.apply_mul_eq_mul_modularAutomorphism,
    apply_mul_eq_mul_modular_block h b hFt htr h1₀ h2' i j x, sub_self]

/-- A positive definite matrix `Ft` whose transpose equals `c • 1` with `c * c = 1` equals `1`. -/
private theorem eq_one_of_posDef_of_scalar_smul_one {ι : Type*} [DecidableEq ι]
    [Nonempty ι] {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef) {c : ℂ} (hF : Ftᵀ = c • 1)
    (hc_sq : c * c = 1) : Ft = 1 := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hdiag : (0 : ℂ) < Ft i₀ i₀ := by
    simpa [Finsupp.sum_single_index] using
      hFt.2 (x := Finsupp.single i₀ (1 : ℂ)) (Finsupp.single_ne_zero.mpr one_ne_zero)
  have hci : c = Ft i₀ i₀ := by simpa using (congrFun (congrFun hF i₀) i₀).symm
  obtain ⟨hre, him⟩ := Complex.lt_def.mp (hci ▸ hdiag)
  simp only [Complex.zero_re] at hre
  have hc1 : c = 1 := by
    rw [show c = (c.re : ℂ) from Complex.ext rfl him.symm] at hc_sq ⊢
    norm_cast at hc_sq ⊢; nlinarith
  simpa using congrArg Matrix.transpose (show Ftᵀ = 1 by rw [hF, hc1, one_smul])

/-- Two `ℂ`-linear maps `A →ₗ[ℂ] A` agree once they agree on the coefficient matrix of every
finite simple unitary comodule. -/
private theorem linearMap_eq_of_simple_unitary (h : AlgebraicHaar A) {f g : A →ₗ[ℂ] A}
    (H : ∀ (M : ComoduleCat.{0, u, u} ℂ A) [IsSimpleOrder (Subcomodule ℂ A M)]
      (b : Basis (Fin (finrank ℂ M)) ℂ M),
      Comodule.coefficientMatrix (C := A) b ∈
        unitary (Matrix (Fin (finrank ℂ M)) (Fin (finrank ℂ M)) A) →
      (Comodule.coefficientMatrix (C := A) b).map f =
        (Comodule.coefficientMatrix (C := A) b).map g) : f = g := by
  have hker : LinearMap.ker (f - g) = ⊤ := by
    rw [eq_top_iff,
      ← (AlgebraicHaar.isLinearlyReductive.{u, 0} h).sSup_simpleCoefficientSubmodules_eq_top]
    refine sSup_le fun P hP ↦ ?_
    obtain ⟨M, hM, hPM⟩ := Comodule.mem_simpleCoefficientSubmodules.mp hP
    have : IsSimpleOrder (Subcomodule ℂ A M) := hM
    have : Module.Finite ℂ M := Subcomodule.finite_of_isSimpleOrder (R := ℂ) (C := A)
    obtain ⟨b, hb⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
      h.right_invariant h.functional_ne_zero h.positive (Module.finBasis ℂ M)
    rw [hPM, ← Comodule.span_range_coefficientMatrix_eq b, Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact sub_eq_zero.mpr (congrFun (congrFun (H M b hb) i) j)
  exact LinearMap.ext fun a ↦ sub_eq_zero.mp (hker ▸ Submodule.mem_top : a ∈ LinearMap.ker (f - g))

/-- **Kac characterization (Neshveyev–Tuset, Proposition 1.7.7).**
The algebraic Haar state on a complex Hopf star algebra is tracial if and only if the antipode is
involutive (`S² = id`). -/
theorem apply_mul_comm_iff_antipode_involutive (h : AlgebraicHaar A) :
    (∀ a b : A, h (a * b) = h (b * a)) ↔
      ∀ a : A, HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ a) = a := by
  have hblock_iff (M : ComoduleCat.{0, u, u} ℂ A) [IsSimpleOrder (Subcomodule ℂ A M)]
      (b : Basis (Fin (finrank ℂ M)) ℂ M)
      (hb : Comodule.coefficientMatrix (C := A) b ∈
        unitary (Matrix (Fin (finrank ℂ M)) (Fin (finrank ℂ M)) A)) :
      (Comodule.coefficientMatrix (C := A) b).map h.modularAutomorphism =
          Comodule.coefficientMatrix (C := A) b ↔
        (Comodule.coefficientMatrix (C := A) b).map
            (HopfAlgebra.antipode ℂ ∘ HopfAlgebra.antipode ℂ) =
          Comodule.coefficientMatrix (C := A) b := by
    obtain ⟨Ft, ⟨hFt, htrFt, _, h2'⟩, _⟩ := h.schur_orthogonality b hb
    have : Module.Finite ℂ M := Module.Finite.of_basis b
    have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
    have : Nonempty (Fin (finrank ℂ M)) := b.index_nonempty
    have hmod_u := h.modularAutomorphism_coefficientMatrix b hb hFt htrFt h2'
    have hS2_u := h.map_antipode_antipode_coefficientMatrix b hb hFt htrFt h2'
    have hmap1 : (1 : Matrix (Fin (finrank ℂ M)) (Fin (finrank ℂ M)) ℂ).map (algebraMap ℂ A) = 1 :=
      Matrix.map_one (algebraMap ℂ A) (map_zero _) (_root_.map_one _)
    constructor <;> intro hfix
    · obtain ⟨c, hc0, hF1, hF2⟩ :=
        (Comodule.mul_coefficientMatrix_mul_eq_self_iff b Ftᵀ Ftᵀ).mp (hmod_u.symm.trans hfix)
      obtain ⟨i₀⟩ := ‹Nonempty (Fin (finrank ℂ M))›
      have hcc : c = c⁻¹ := by simpa using congrFun (congrFun (hF1.symm.trans hF2) i₀) i₀
      have hFt1 : Ft = 1 :=
        eq_one_of_posDef_of_scalar_smul_one hFt hF1 (by rw [← mul_inv_cancel₀ hc0, ← hcc])
      rw [hS2_u, hFt1, Matrix.transpose_one,
        Matrix.inv_eq_right_inv (Matrix.one_mul 1), hmap1, Matrix.one_mul, Matrix.mul_one]
    · obtain ⟨c, hc0, hF1, hF2⟩ :=
        (Comodule.mul_coefficientMatrix_mul_eq_self_iff b Ftᵀ Ftᵀ⁻¹).mp (hS2_u.symm.trans hfix)
      have htrF : Ftᵀ.trace = Ftᵀ⁻¹.trace := by
        rw [Matrix.trace_transpose, ← Matrix.transpose_nonsing_inv, Matrix.trace_transpose, htrFt]
      rw [hF2, hF1, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
        smul_eq_mul, smul_eq_mul] at htrF
      have hcc : c = c⁻¹ := mul_right_cancel₀ (by exact_mod_cast Fintype.card_ne_zero) htrF
      have hFt1 : Ft = 1 :=
        eq_one_of_posDef_of_scalar_smul_one hFt hF1 (by rw [← mul_inv_cancel₀ hc0, ← hcc])
      rw [hmod_u, hFt1, Matrix.transpose_one, hmap1, Matrix.one_mul, Matrix.mul_one]
  rw [← h.modularAutomorphism_eq_refl_iff]
  exact ⟨fun hθ a ↦ LinearMap.congr_fun (linearMap_eq_of_simple_unitary h
      (f := (HopfAlgebra.antipode ℂ (A := A)).comp (HopfAlgebra.antipode ℂ (A := A)))
      (g := LinearMap.id) fun M _ b hb ↦ by
        simpa [Matrix.map_id] using (hblock_iff M b hb).mp (by simp [hθ, Matrix.map_id])) a,
    fun hS2 ↦ AlgEquiv.ext fun a ↦ LinearMap.congr_fun (linearMap_eq_of_simple_unitary h
      (f := h.modularAutomorphism.toLinearMap) (g := LinearMap.id) fun M _ b hb ↦ by
        simpa [Matrix.map_id] using (hblock_iff M b hb).mpr (by ext i j; exact hS2 _)) a⟩

end TauCeti.AlgebraicHaar
