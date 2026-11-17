/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Module.ULift
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Decomposition
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Transport
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Trivial
public import TauCeti.Algebra.HopfAlgebra.CompactType.SchurOrthogonality

/-!
# Characterization of compact-type complex Hopf star algebras

A complex Hopf star algebra `A` is of *compact type* (a *CQG algebra*) when it admits an
`AlgebraicHaar A` state. By Timmermann (Theorem 3.2.12) and Dijkhuizen–Koornwinder, this holds iff
`A` is linearly spanned by the matrix coefficients of its finite-dimensional unitary comodules.

## Main declarations

* `TauCeti.unitaryCoefficientSet`: entries of unitary coefficient matrices of finite comodules.
* `TauCeti.mem_unitaryCoefficientSet_iff`: membership characterization of `unitaryCoefficientSet A`.
* `TauCeti.mem_unitaryCoefficientSet_of_coefficientMatrix_mem_unitary`: entries of any finite
  unitary coefficient matrix lie in `unitaryCoefficientSet A`.
* `TauCeti.nonempty_algebraicHaar_iff_span_unitaryCoefficientSet_eq_top`: compact-type iff.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Theorem 3.2.12.
* M. S. Dijkhuizen and T. H. Koornwinder, *CQG algebras: a direct algebraic approach to compact
  quantum groups*, Lett. Math. Phys. 32 (1994), 315–330.
-/

public section

open Module Matrix
open scoped ComplexOrder DirectSum

namespace TauCeti

universe u w

section UnitaryCoefficientSet

variable (A : Type u) [Semiring A] [StarRing A] [Algebra ℂ A] [Coalgebra ℂ A]

/-- The set of matrix entries of finite-dimensional unitary comodules of `A`.

Every finite-dimensional comodule (in any universe) having a basis with unitary coefficient matrix
contributes all entries of that matrix to `unitaryCoefficientSet A`
(`mem_unitaryCoefficientSet_of_coefficientMatrix_mem_unitary`). -/
def unitaryCoefficientSet : Set A :=
  {a | ∃ (n : ℕ) (_ : Comodule ℂ A (Fin n → ℂ)),
    Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n)) ∈
      unitary (Matrix (Fin n) (Fin n) A) ∧
    ∃ i j : Fin n, Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n)) i j = a}

/-- Membership in `unitaryCoefficientSet A` means occurring as an entry of a unitary coefficient
matrix on some `Fin n → ℂ`. -/
theorem mem_unitaryCoefficientSet_iff {a : A} :
    a ∈ unitaryCoefficientSet A ↔
      ∃ (n : ℕ) (_ : Comodule ℂ A (Fin n → ℂ)),
        Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n)) ∈
          unitary (Matrix (Fin n) (Fin n) A) ∧
        ∃ i j : Fin n, Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n)) i j = a :=
  (Iff.rfl)

variable {A}

/-- Every entry of the coefficient matrix of a finite unitary basis (on a comodule in any
universe) belongs to `unitaryCoefficientSet A`. -/
theorem mem_unitaryCoefficientSet_of_coefficientMatrix_mem_unitary
    {M : Type w} [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j : ι) :
    Comodule.coefficientMatrix (C := A) b i j ∈ unitaryCoefficientSet A := by
  let eFin := Fintype.equivFin ι
  let bFin := b.reindex eFin
  let e := bFin.equivFun
  let : Comodule ℂ A (Fin (Fintype.card ι) → ℂ) := Comodule.Transport (R := ℂ) (C := A) e
  have hbmap : bFin.map e = Pi.basisFun ℂ (Fin (Fintype.card ι)) := by
    ext k x; simp [e, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have hmat : Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin (Fintype.card ι))) =
      (Comodule.coefficientMatrix (C := A) b).submatrix eFin.symm eFin.symm := by
    rw [← hbmap, Comodule.coefficientMatrix_map bFin e (Comodule.transportToHom e)
      (Comodule.transportToHom_apply e), Comodule.coefficientMatrix_reindex b eFin]
  have hunit : Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin (Fintype.card ι))) ∈
      unitary (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) A) := by
    rw [hmat, Unitary.mem_iff]
    constructor <;>
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv _ _ _ eFin.symm, ← Matrix.star_eq_conjTranspose]
      simp [(Unitary.mem_iff.mp hu).1, (Unitary.mem_iff.mp hu).2, Matrix.submatrix_one_equiv]
  exact ⟨Fintype.card ι, inferInstance, hunit, eFin i, eFin j, by simp [hmat]⟩

/-- The matrix-coefficient submodule of a finite unitary comodule is contained in the span of
`unitaryCoefficientSet A`. -/
theorem matrixCoefficientSubmodule_le_span_unitaryCoefficientSet
    {M : Type w} [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ≤
      Submodule.span ℂ (unitaryCoefficientSet A) := by
  rw [← Comodule.span_range_coefficientMatrix_eq b, Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact Submodule.subset_span (mem_unitaryCoefficientSet_of_coefficientMatrix_mem_unitary b hu i j)

/-- The unit `1` lies in `unitaryCoefficientSet A` for any complex star bialgebra `A`. -/
theorem one_mem_unitaryCoefficientSet {B : Type u} [Semiring B] [StarRing B] [Bialgebra ℂ B] :
    (1 : B) ∈ unitaryCoefficientSet B := by
  let : Comodule ℂ B (Fin 1 → ℂ) := Comodule.trivial (R := ℂ) (C := B) (M := Fin 1 → ℂ)
  have hmat : Comodule.coefficientMatrix (C := B) (Pi.basisFun ℂ (Fin 1)) = 1 := by
    ext i j; rw [Fin.eq_zero i, Fin.eq_zero j]
    simp [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_groupLike, Basis.coord_apply]
  exact ⟨1, inferInstance, hmat ▸ one_mem _, 0, 0, by simp [hmat]⟩

end UnitaryCoefficientSet

section CompactTypeIff

variable {A : Type u} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]

attribute [local instance] Comodule.dual Comodule.convolutionModule

/-- Internal witness predicate: `P` is the coefficient space of a simple comodule in `Type u`
carrying a finite basis with unitary coefficient matrix. -/
private def HasUnitarySimpleWitness (P : Submodule ℂ A) : Prop :=
  ∃ (M : ComoduleCat.{0, u, u} ℂ A) (_ : IsSimpleOrder (Subcomodule ℂ A M))
    (n : ℕ) (b : Basis (Fin n) ℂ M),
    Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix (Fin n) (Fin n) A) ∧
    P = Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M)

omit [StarRing A] [StarModule ℂ A] in
private theorem isSimpleOrder_transport {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [Comodule ℂ A M] [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N)
    [IsSimpleOrder (Subcomodule ℂ A M)] :
    letI : Comodule ℂ A N := Comodule.Transport (R := ℂ) (C := A) e
    IsSimpleOrder (Subcomodule ℂ A N) := by
  let : Comodule ℂ A N := Comodule.Transport (R := ℂ) (C := A) e
  have : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) M :=
    Comodule.isSimpleModule_convolution_iff.mpr inferInstance
  let f := (Comodule.transportToHom (R := ℂ) (C := A) e).toConvolutionLinearMap
  have hbij : Function.Bijective f := (funext fun x ↦ by simp [f] : (f : M → N) = e) ▸ e.bijective
  exact Comodule.isSimpleModule_convolution_iff.mp
    (IsSimpleModule.congr (LinearEquiv.ofBijective f hbij).symm)

/-- Every finite comodule with a unitary basis has its matrix-coefficient submodule contained in
the supremum of simple unitary coefficient spaces. -/
private theorem matrixCoefficientSubmodule_le_sSup_hasUnitarySimpleWitness
    {n : ℕ} [Comodule ℂ A (Fin n → ℂ)]
    (hu : Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n)) ∈
      unitary (Matrix (Fin n) (Fin n) A)) :
    Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := Fin n → ℂ) ≤
      sSup {P : Submodule ℂ A | HasUnitarySimpleWitness (A := A) P} := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let : Comodule ℂ A (EuclideanSpace ℂ (Fin n)) := Comodule.Transport (R := ℂ) (C := A) e
  rw [← Comodule.matrixCoefficientSubmodule_transport (R := ℂ) (C := A) e]
  let bE := EuclideanSpace.basisFun (Fin n) ℂ
  have hU : Comodule.IsUnitary ℂ A (EuclideanSpace ℂ (Fin n)) := by
    have hbE : bE.toBasis = (Pi.basisFun ℂ (Fin n)).map e := by
      ext i; simp [bE, e, EuclideanSpace.basisFun_apply, Pi.basisFun_apply, PiLp.toLp_single]
    rw [bE.isUnitary_comodule_iff, hbE, Comodule.coefficientMatrix_map (Pi.basisFun ℂ (Fin n)) e
      (Comodule.transportToHom e) (Comodule.transportToHom_apply e)]
    exact hu
  have hAtoms : sSup {S : Subcomodule ℂ A (EuclideanSpace ℂ (Fin n)) | IsAtom S} = ⊤ :=
    Comodule.isCompletelyReducible_iff_sSup_atoms_eq_top.mp hU.isCompletelyReducible
  set U := sSup {P : Submodule ℂ A | HasUnitarySimpleWitness (A := A) P}
  refine Comodule.matrixCoefficientSubmodule_le fun φ m ↦ ?_
  have hle : (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n))) ≤
      Submodule.comap (Comodule.matrixCoefficientHom (C := A) φ).toLinearMap U := by
    rw [← Subcomodule.top_toSubmodule (R := ℂ) (C := A), ← hAtoms, Subcomodule.sSup_toSubmodule]
    refine iSup_le fun S x hx ↦ ?_
    have : IsSimpleOrder (Subcomodule ℂ A S.1) :=
      Comodule.isSimpleModule_convolution_iff.mp (S.1.isSimpleModule_convolution_iff_isAtom.mpr S.2)
    let eL : S.1 ≃ₗ[ℂ] ULift.{u} S.1 := (ULift.moduleEquiv (R := ℂ) (M := S.1)).symm
    let : Comodule ℂ A (ULift.{u} S.1) := Comodule.Transport (R := ℂ) (C := A) eL
    let bS := (stdOrthonormalBasis ℂ S.1).toBasis
    have hS_mem : Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := S.1) ∈
        {P : Submodule ℂ A | HasUnitarySimpleWitness (A := A) P} :=
      ⟨ComoduleCat.of ℂ A (ULift.{u} S.1), isSimpleOrder_transport eL, finrank ℂ S.1, bS.map eL,
        (Comodule.coefficientMatrix_map (C := A) bS eL (Comodule.transportToHom eL)
          (Comodule.transportToHom_apply eL)).symm ▸
          (S.1.isUnitary hU).coefficientMatrix_mem_unitary (stdOrthonormalBasis ℂ S.1),
        (Comodule.matrixCoefficientSubmodule_transport (R := ℂ) (C := A) eL).symm⟩
    rw [Submodule.mem_comap, show (Comodule.matrixCoefficientHom (C := A) φ).toLinearMap x =
        Comodule.matrixCoefficient (C := A) (φ.comp S.1.subtype.toLinearMap) ⟨x, hx⟩ by
      simpa using Comodule.matrixCoefficient_map S.1.subtype φ ⟨x, hx⟩]
    exact le_sSup hS_mem (Comodule.matrixCoefficient_mem_submodule _ _)
  simpa [Submodule.mem_comap] using hle (x := m) trivial

private theorem sSup_hasUnitarySimpleWitness_eq_top
    (hspan : Submodule.span ℂ (unitaryCoefficientSet A) = ⊤) :
    sSup {Q : Submodule ℂ A | HasUnitarySimpleWitness (A := A) Q} = ⊤ := by
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro a ⟨n, hcom, hu, i, j, rfl⟩
  let : Comodule ℂ A (Fin n → ℂ) := hcom
  exact matrixCoefficientSubmodule_le_sSup_hasUnitarySimpleWitness (A := A) hu
    (by rw [Comodule.coefficientMatrix_apply]; exact Comodule.matrixCoefficient_mem_submodule _ _)

/-- From `span (unitaryCoefficientSet A) = ⊤`, every simple coefficient block admits a simple
unitary witness. -/
private theorem hasUnitarySimpleWitness_of_mem_simpleCoefficientSubmodules
    (hspan : Submodule.span ℂ (unitaryCoefficientSet A) = ⊤)
    {P : Submodule ℂ A} (hP : P ∈ Comodule.simpleCoefficientSubmodules ℂ A) :
    HasUnitarySimpleWitness (A := A) P := by
  by_contra hnot
  have hdisj : Disjoint P (sSup (Comodule.simpleCoefficientSubmodules ℂ A \ {P})) :=
    Comodule.sSupIndep_simpleCoefficientSubmodules hP
  have htop : sSup (Comodule.simpleCoefficientSubmodules ℂ A \ {P}) = ⊤ := eq_top_iff.mpr <|
    (sSup_hasUnitarySimpleWitness_eq_top hspan).symm.le.trans <|
      sSup_le_sSup fun Q hQ ↦ ⟨let ⟨M, hM, _, _, _, h⟩ := hQ
        Comodule.mem_simpleCoefficientSubmodules.mpr ⟨M, hM, h⟩, fun hQP ↦ hnot (hQP ▸ hQ)⟩
  rw [htop, disjoint_top] at hdisj
  exact Comodule.bot_notMem_simpleCoefficientSubmodules (hdisj ▸ hP)

/-- If every simple coefficient block admits a unitary witness, then every finite-dimensional
simple comodule (in any universe) admits a finite basis with unitary coefficient matrix. -/
private theorem exists_basis_mem_unitary_of_simple
    (hspan : Submodule.span ℂ (unitaryCoefficientSet A) = ⊤)
    {M : Type w} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [Module.Finite ℂ M] [IsSimpleOrder (Subcomodule ℂ A M)] :
    ∃ (n : ℕ) (b : Basis (Fin n) ℂ M),
      Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix (Fin n) (Fin n) A) := by
  let e : M ≃ₗ[ℂ] ULift.{u} (Fin (finrank ℂ M) → ℂ) :=
    (Module.finBasis ℂ M).equivFun.trans (ULift.moduleEquiv (R := ℂ)).symm
  let : Comodule ℂ A (ULift.{u} (Fin (finrank ℂ M) → ℂ)) := Comodule.Transport (R := ℂ) (C := A) e
  have : IsSimpleOrder (Subcomodule ℂ A (ULift.{u} (Fin (finrank ℂ M) → ℂ))) :=
    isSimpleOrder_transport e
  have hPmem : Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ∈
      Comodule.simpleCoefficientSubmodules ℂ A :=
    Comodule.matrixCoefficientSubmodule_transport (R := ℂ) (C := A) e ▸
      Comodule.matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules
  obtain ⟨N, hNsimp, n, c, hc_unit, hPN⟩ :=
    hasUnitarySimpleWitness_of_mem_simpleCoefficientSubmodules hspan hPmem
  have : IsSimpleOrder (Subcomodule ℂ A N) := hNsimp
  obtain ⟨f, hf⟩ := (Comodule.matrixCoefficientSubmodule_eq_iff (R := ℂ) (C := A)
    (M := N) (N := M)).mp hPN.symm
  have : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) N :=
    Comodule.isSimpleModule_convolution_iff.mpr hNsimp
  have : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) M :=
    Comodule.isSimpleModule_convolution_iff.mpr inferInstance
  have hf_ne : f.toConvolutionLinearMap ≠ 0 :=
    fun h0 ↦ hf <| by ext x; simpa using LinearMap.congr_fun h0 x
  let iso : N ≃ₗ[ℂ] M := LinearEquiv.ofBijective f.toLinearMap <|
    (funext fun x ↦ by simp : (f.toLinearMap : N → M) = f.toConvolutionLinearMap) ▸
      LinearMap.bijective_of_ne_zero hf_ne
  exact ⟨n, c.map iso, (Comodule.coefficientMatrix_map c iso f fun _ ↦ rfl).symm ▸ hc_unit⟩

omit [StarRing A] [StarModule ℂ A] in
/-- The trivial line `ℂ · 1` is a simple coefficient submodule of `A`. -/
private theorem span_one_mem_simpleCoefficientSubmodules :
    Submodule.span ℂ ({(1 : A)} : Set A) ∈ Comodule.simpleCoefficientSubmodules ℂ A := by
  let : Comodule ℂ A ℂ := Comodule.trivial (R := ℂ) (C := A) (M := ℂ)
  let e : ℂ ≃ₗ[ℂ] ULift.{u} ℂ := (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm
  let : Comodule ℂ A (ULift.{u} ℂ) := Comodule.Transport (R := ℂ) (C := A) e
  have : IsSimpleOrder (Subcomodule ℂ A (ULift.{u} ℂ)) :=
    Subcomodule.isSimpleOrder_of_transitive (ULift.up (1 : ℂ))
      (fun h ↦ one_ne_zero (congrArg ULift.down h)) (fun (c : ℂ) x ↦ c • x)
      (fun {v w} _ hw ↦ ⟨v.down * w.down⁻¹, ULift.ext (by
        simp [mul_assoc, inv_mul_cancel₀ (fun h ↦ hw (ULift.ext h))])⟩)
      (fun W c _ hx ↦ W.toSubmodule.smul_mem c hx)
  rw [← Comodule.trivial_rankOne_matrixCoefficientSubmodule_eq_span_singleton_one,
    ← Comodule.matrixCoefficientSubmodule_transport (R := ℂ) (C := A) e]
  exact Comodule.matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules

/-- Positivity of a normalized two-sided invariant functional on a simple unitary block, deduced
directly from positivity-free weighted Schur orthogonality. -/
private theorem nonneg_on_simpleBlock_of_schur [StarCoalgebra ℂ A]
    (hspan : Submodule.span ℂ (unitaryCoefficientSet A) = ⊤)
    {h : A →ₗ[ℂ] ℂ} (hl : h.IsLeftInvariantIntegral) (hr : h.IsRightInvariantIntegral)
    (h1 : h 1 = 1) {M : Type w} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [IsSimpleOrder (Subcomodule ℂ A M)] {n : ℕ} (b : Basis (Fin n) ℂ M)
    (hb : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix (Fin n) (Fin n) A))
    {x : A} (hx : x ∈ Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M)) :
    0 ≤ h (star x * x) := by
  have : Module.Finite ℂ M := Module.Finite.of_basis b
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty (Fin n) := b.index_nonempty
  have : IsSimpleOrder (Subcomodule ℂ A (Module.Dual ℂ M)) :=
    (Subcomodule.isSimpleOrder_dual_iff (k := ℂ) (H := A) (M := M)
      (TauCeti.HopfAlgebra.antipode_bijective (R := ℂ) (A := A)).injective).mpr inferInstance
  obtain ⟨_, d, hd⟩ := exists_basis_mem_unitary_of_simple hspan (M := Module.Dual ℂ M)
  obtain ⟨Ft, ⟨hFt, _, hSchur1, _⟩, _⟩ :=
    LinearMap.existsUnique_posDef_schur_orthogonality hl hr h1 b hb d hd
  let B := Comodule.matrixCoefficientBasis (C := A) b
  let c (i j : Fin n) : ℂ := B.repr ⟨x, hx⟩ (i, j)
  have hx_eq : x = ∑ i, ∑ j, c i j • Comodule.coefficientMatrix (C := A) b i j := by
    simpa only [Fintype.sum_prod_type, Submodule.coe_sum, SetLike.val_smul, B,
      Comodule.coe_matrixCoefficientBasis] using (congrArg Subtype.val (B.sum_repr ⟨x, hx⟩)).symm
  have hquad : h (star x * x) =
      (Ft⁻¹.trace)⁻¹ * ∑ j, star (fun i ↦ c i j) ⬝ᵥ (Ft⁻¹ *ᵥ fun k ↦ c k j) := by
    rw [hx_eq]
    simp_rw [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      map_sum, map_smul, smul_eq_mul, hSchur1]
    simp_rw [show ∀ i j k,
        ∑ l, star (c i j) * (c k l * if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) =
          (Ft⁻¹.trace)⁻¹ * (star (c i j) * (Ft⁻¹ i k * c k j)) from fun i j k ↦ by
      rw [Finset.sum_eq_single j (fun l _ hlj ↦ by simp [Ne.symm hlj]) (by simp)]
      simp only [↓reduceIte]; ring]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ by
      simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  obtain ⟨hre, him⟩ := Complex.lt_def.mp hFt.inv.trace_pos
  rw [hquad]
  refine mul_nonneg ?_
    (Finset.sum_nonneg fun j _ ↦ hFt.inv.posSemidef.dotProduct_mulVec_nonneg (fun i ↦ c i j))
  rw [show Ft⁻¹.trace = (Ft⁻¹.trace.re : ℂ) from Complex.ext rfl him.symm, ← Complex.ofReal_inv]
  exact Complex.le_def.mpr ⟨inv_nonneg.mpr hre.le, rfl⟩

/-- **Characterization of compact-type complex Hopf star algebras (Timmermann, Theorem 3.2.12).**
A complex Hopf star algebra admits an algebraic Haar state if and only if it is linearly spanned
by the matrix coefficients of its finite-dimensional unitary comodules. -/
theorem nonempty_algebraicHaar_iff_span_unitaryCoefficientSet_eq_top [StarCoalgebra ℂ A] :
    Nonempty (AlgebraicHaar A) ↔ Submodule.span ℂ (unitaryCoefficientSet A) = ⊤ := by
  constructor
  · rintro ⟨h⟩
    rw [eq_top_iff,
      ← (AlgebraicHaar.isLinearlyReductive.{u, 0} h).iSup_matrixCoefficientSubmodule_eq_top]
    refine iSup_le fun S ↦ iSup_le fun hS ↦ ?_
    have : Module.Finite ℂ S := S.finite_of_isAtom hS
    obtain ⟨c, hc⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
      h.right_invariant h.functional_ne_zero h.positive (Module.finBasis ℂ S)
    exact matrixCoefficientSubmodule_le_span_unitaryCoefficientSet c hc
  · intro hspan
    classical
    set S := Comodule.simpleCoefficientSubmodules ℂ A
    set P₁ : Submodule ℂ A := Submodule.span ℂ ({(1 : A)} : Set A)
    have hP₁ : P₁ ∈ S := span_one_mem_simpleCoefficientSubmodules (A := A)
    have hStop : sSup S = ⊤ := eq_top_iff.mpr <|
      (sSup_hasUnitarySimpleWitness_eq_top hspan).symm.le.trans <|
        sSup_le_sSup fun _ ⟨M, hM, _, _, _, hQ⟩ ↦
          Comodule.mem_simpleCoefficientSubmodules.mpr ⟨M, hM, hQ⟩
    let iso : (⨁ P : S, P.1) ≃ₗ[ℂ] A := LinearEquiv.ofBijective
      (DirectSum.coeLinearMap fun P : S ↦ (P.1 : Submodule ℂ A))
      (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
        ((sSupIndep_iff _).mp Comodule.sSupIndep_simpleCoefficientSubmodules)
        (by rw [← sSup_eq_iSup', hStop]))
    have hiso (z : ⨁ P : S, P.1) :
        iso z = DirectSum.coeLinearMap (fun P : S ↦ (P.1 : Submodule ℂ A)) z := rfl
    let h : A →ₗ[ℂ] ℂ :=
      (DirectSum.toModule ℂ S ℂ fun P ↦
        if P.1 = P₁ then (Coalgebra.counit (R := ℂ)).comp P.1.subtype else 0).comp
        iso.symm.toLinearMap
    have h_apply_mem (P : S) {x : A} (hx : x ∈ P.1) :
        h x = if P.1 = P₁ then Coalgebra.counit (R := ℂ) x else 0 := by
      have hsymm : iso.symm x = DirectSum.lof ℂ S (fun Q : S ↦ (Q.1 : Type u)) P ⟨x, hx⟩ :=
        iso.injective (by rw [iso.apply_symm_apply, hiso, DirectSum.lof_eq_of,
          DirectSum.coeLinearMap_of])
      simp only [h, LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, DirectSum.toModule_lof]
      split_ifs <;> rfl
    have h1 : h 1 = 1 := by
      simp [h_apply_mem ⟨P₁, hP₁⟩ (Submodule.subset_span (Set.mem_singleton (1 : A)))]
    choose M_P hM_P n_P b_P hb_P hP_eq using fun P : S ↦
      hasUnitarySimpleWitness_of_mem_simpleCoefficientSubmodules hspan P.2
    have hvanish (T : A →ₗ[ℂ] A) (hT1 : T 1 = 0)
        (hT : ∀ P : S, P.1 ≠ P₁ → ∀ i j : Fin (n_P P),
          T (Comodule.coefficientMatrix (C := A) (b_P P) i j) = 0) (a : A) : T a = 0 := by
      have hker : LinearMap.ker T = ⊤ := by
        rw [eq_top_iff, ← hStop]
        refine sSup_le fun P hP ↦ ?_
        by_cases hPP₁ : P = P₁
        · rw [hPP₁, Submodule.span_le]; rintro _ rfl; exact hT1
        · have hPeq : P = _ := hP_eq ⟨P, hP⟩
          rw [hPeq, ← Comodule.span_range_coefficientMatrix_eq (b_P ⟨P, hP⟩), Submodule.span_le]
          rintro _ ⟨⟨i, j⟩, rfl⟩; exact hT ⟨P, hP⟩ hPP₁ i j
      exact (hker ▸ Submodule.mem_top : a ∈ LinearMap.ker T)
    have hzero (P : S) (hPP₁ : P.1 ≠ P₁) (p q : Fin (n_P P)) :
        h (Comodule.coefficientMatrix (C := A) (b_P P) p q) = 0 := by
      have hmem : Comodule.coefficientMatrix (C := A) (b_P P) p q ∈ P.1 := by
        rw [hP_eq P, Comodule.coefficientMatrix_apply]
        exact Comodule.matrixCoefficient_mem_submodule _ _
      simp [h_apply_mem P hmem, hPP₁]
    have hl : h.IsLeftInvariantIntegral := LinearMap.isLeftInvariantIntegral_iff.mpr fun a ↦
      sub_eq_zero.mp <| hvanish
        ((TensorProduct.rid ℂ A ∘ₗ h.lTensor A ∘ₗ Coalgebra.comul (R := ℂ)) - h.smulRight (1 : A))
        (by simp [h1, Algebra.TensorProduct.one_def]) (fun P hPP₁ i j ↦ by
          simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smulRight_apply,
            Comodule.comul_coefficientMatrix_eq_sum (b_P P), map_sum, LinearMap.lTensor_tmul,
            hzero P hPP₁ i j, zero_smul, sub_zero]
          exact Finset.sum_eq_zero fun k _ ↦ by simp [hzero P hPP₁ k j]) a
    have hr : h.IsRightInvariantIntegral := LinearMap.isRightInvariantIntegral_iff.mpr fun a ↦
      sub_eq_zero.mp <| hvanish
        ((TensorProduct.lid ℂ A ∘ₗ h.rTensor A ∘ₗ Coalgebra.comul (R := ℂ)) - h.smulRight (1 : A))
        (by simp [h1, Algebra.TensorProduct.one_def]) (fun P hPP₁ i j ↦ by
          simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smulRight_apply,
            Comodule.comul_coefficientMatrix_eq_sum (b_P P), map_sum, LinearMap.rTensor_tmul,
            hzero P hPP₁ i j, zero_smul, sub_zero]
          exact Finset.sum_eq_zero fun k _ ↦ by simp [hzero P hPP₁ i k]) a
    have hblock_ortho (P Q : S) (hPQ : P ≠ Q) {x y : A} (hx : x ∈ P.1) (hy : y ∈ Q.1) :
        h (star x * y) = 0 := by
      have : IsSimpleOrder (Subcomodule ℂ A (M_P P)) := hM_P P
      have : IsSimpleOrder (Subcomodule ℂ A (M_P Q)) := hM_P Q
      have hHom : ∀ g : Comodule.Hom ℂ A (M_P Q) (M_P P), g = 0 := fun g ↦ by_contra fun hg ↦
        hPQ <| Subtype.ext <| by
          rw [hP_eq P, hP_eq Q, Comodule.matrixCoefficientSubmodule_eq_of_ne_zero hg]
      rw [hP_eq P, ← Comodule.span_range_coefficientMatrix_eq (b_P P)] at hx
      rw [hP_eq Q, ← Comodule.span_range_coefficientMatrix_eq (b_P Q)] at hy
      refine Submodule.span_induction (p := fun u _ ↦ h (star u * y) = 0) ?_ (by simp)
        (fun _ _ _ _ hu hv ↦ by simp [add_mul, hu, hv]) (fun _ _ _ hu ↦ by simp [hu]) hx
      rintro _ ⟨⟨i, j⟩, rfl⟩
      refine Submodule.span_induction (p := fun v _ ↦
        h (star (Comodule.coefficientMatrix (C := A) (b_P P) i j) * v) = 0) ?_ (by simp)
        (fun _ _ _ _ hu hv ↦ by simp [mul_add, hu, hv]) (fun _ _ _ hv ↦ by simp [hv]) hy
      rintro _ ⟨⟨k, l⟩, rfl⟩
      exact hr.apply_star_coefficientMatrix_mul_eq_zero (b_P P) (b_P Q) (hb_P P) hHom i j k l
    have hpos (a : A) : 0 ≤ h (star a * a) := by
      let z := iso.symm a
      have ha : a = ∑ P ∈ z.support, (z P : A) := by
        simpa [hiso, DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum] using
          (iso.apply_symm_apply a).symm
      rw [ha, star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum, map_sum]
      refine Finset.sum_nonneg fun P hP ↦ ?_
      rw [Finset.sum_eq_single P (fun Q _ hQP ↦ hblock_ortho P Q (Ne.symm hQP) (z P).2 (z Q).2)
        (fun hnot ↦ absurd hP hnot)]
      have : IsSimpleOrder (Subcomodule ℂ A (M_P P)) := hM_P P
      exact nonneg_on_simpleBlock_of_schur hspan hl hr h1 (b_P P) (hb_P P) (hP_eq P ▸ (z P).2)
    exact ⟨⟨h, h1, hl, hr, hpos⟩⟩

end CompactTypeIff

end TauCeti
