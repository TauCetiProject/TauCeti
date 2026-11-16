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

A complex Hopf star algebra `A` is of *compact type* (or a *CQG algebra*) when it admits an
algebraic Haar state `TauCeti.AlgebraicHaar A`. The central algebraic theorem of the theory
(Timmermann, Theorem 3.2.12; Dijkhuizen–Koornwinder) characterizes compact type purely in terms
of unitary corepresentations:

> `A` admits an algebraic Haar state if and only if `A` is linearly spanned by the matrix
> coefficients of its finite-dimensional unitary comodules.

The forward implication combines linear reductivity (`AlgebraicHaar.isLinearlyReductive`),
cosemisimplicity (`Coalgebra.IsLinearlyReductive.iSup_matrixCoefficientSubmodule_eq_top`), and
algebraic unitarization (`Comodule.exists_basis_coefficientMatrix_mem_unitary`).

For the converse, every finite-dimensional unitary comodule decomposes as a sum of simple unitary
subcomodules. Hence the simple unitary coefficient spaces span `A`; independence of distinct
simple coefficient spaces (`Comodule.sSupIndep_simpleCoefficientSubmodules`) then forces *every*
simple comodule — including the dual comodule of each simple comodule — to admit a unitary basis.
Defining `h : A →ₗ[ℂ] ℂ` on the internal direct sum of simple coefficient blocks to be the counit
on `ℂ · 1` and `0` on all other simple blocks gives a normalized two-sided invariant functional,
whose positivity `0 ≤ h (star a * a)` follows directly from the positivity-free weighted Schur
orthogonality theorem (`LinearMap.existsUnique_posDef_schur_orthogonality`).

## Main declarations

* `TauCeti.unitaryCoefficientSet`: the set of entries of unitary coefficient matrices of
  finite-dimensional comodules of `A`.
* `TauCeti.mem_unitaryCoefficientSet_iff`: membership characterization of
  `unitaryCoefficientSet A`.
* `TauCeti.mem_unitaryCoefficientSet_of_coefficientMatrix_mem_unitary`: entries of any finite
  unitary coefficient matrix (in any carrier universe) lie in `unitaryCoefficientSet A`.
* `TauCeti.nonempty_algebraicHaar_iff_span_unitaryCoefficientSet_eq_top`: a complex Hopf star
  algebra admits an algebraic Haar state if and only if `unitaryCoefficientSet A` spans `A`.

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
  let eFin : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let bFin : Basis (Fin (Fintype.card ι)) ℂ M := b.reindex eFin
  let e : M ≃ₗ[ℂ] (Fin (Fintype.card ι) → ℂ) := bFin.equivFun
  let : Comodule ℂ A (Fin (Fintype.card ι) → ℂ) := Comodule.Transport (R := ℂ) (C := A) e
  have hbmap : bFin.map e = Pi.basisFun ℂ (Fin (Fintype.card ι)) := by
    ext k x
    simp [e, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have hmat : Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin (Fintype.card ι))) =
      (Comodule.coefficientMatrix (C := A) b).submatrix eFin.symm eFin.symm := by
    rw [← hbmap,
      Comodule.coefficientMatrix_map bFin e (Comodule.transportToHom e)
        (Comodule.transportToHom_apply e),
      Comodule.coefficientMatrix_reindex b eFin]
  have hunit : Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin (Fintype.card ι))) ∈
      unitary (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) A) := by
    rw [hmat, Unitary.mem_iff]
    have h1 : (Comodule.coefficientMatrix (C := A) b)ᴴ *
        Comodule.coefficientMatrix (C := A) b = 1 := (Unitary.mem_iff.mp hu).1
    have h2 : Comodule.coefficientMatrix (C := A) b *
        (Comodule.coefficientMatrix (C := A) b)ᴴ = 1 := (Unitary.mem_iff.mp hu).2
    constructor
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv _ _ _ eFin.symm, h1, Matrix.submatrix_one_equiv]
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv _ _ _ eFin.symm, h2, Matrix.submatrix_one_equiv]
  refine ⟨Fintype.card ι, inferInstance, hunit, eFin i, eFin j, ?_⟩
  simp [hmat]

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
    ext i j
    rw [Fin.eq_zero i, Fin.eq_zero j]
    simp [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_groupLike, Basis.coord_apply]
  refine ⟨1, inferInstance, ?_, 0, 0, by simp [hmat]⟩
  rw [hmat]
  exact one_mem _

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

/-- Every finite comodule with a unitary basis has its matrix-coefficient submodule contained in
the supremum of simple unitary coefficient spaces. -/
private theorem matrixCoefficientSubmodule_le_sSup_hasUnitarySimpleWitness
    {n : ℕ} [Comodule ℂ A (Fin n → ℂ)]
    (hu : Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n)) ∈
      unitary (Matrix (Fin n) (Fin n) A)) :
    Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := Fin n → ℂ) ≤
      sSup {P : Submodule ℂ A | HasUnitarySimpleWitness (A := A) P} := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let : Comodule ℂ A (EuclideanSpace ℂ (Fin n)) := Comodule.Transport (R := ℂ) (C := A) e
  rw [← Comodule.matrixCoefficientSubmodule_transport (R := ℂ) (C := A) e]
  let bE := EuclideanSpace.basisFun (Fin n) ℂ
  have hbE : bE.toBasis = (Pi.basisFun ℂ (Fin n)).map e := by
    ext i
    simp [bE, e, EuclideanSpace.basisFun_apply, Pi.basisFun_apply, PiLp.toLp_single]
  have hU : Comodule.IsUnitary ℂ A (EuclideanSpace ℂ (Fin n)) := by
    rw [bE.isUnitary_comodule_iff, hbE,
      Comodule.coefficientMatrix_map (Pi.basisFun ℂ (Fin n)) e
        (Comodule.transportToHom e) (Comodule.transportToHom_apply e)]
    exact hu
  have hAtoms : sSup {S : Subcomodule ℂ A (EuclideanSpace ℂ (Fin n)) | IsAtom S} = ⊤ :=
    Comodule.isCompletelyReducible_iff_sSup_atoms_eq_top.mp hU.isCompletelyReducible
  -- Each simple subcomodule `S` is unitary and lifts to `Type u` with the same coefficient space.
  have hS_mem (S : Subcomodule ℂ A (EuclideanSpace ℂ (Fin n))) (hS : IsAtom S) :
      Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := S) ∈
        {P : Submodule ℂ A | HasUnitarySimpleWitness (A := A) P} := by
    have hSU : Comodule.IsUnitary ℂ A S := S.isUnitary hU
    have hSsimp_conv : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) S :=
      S.isSimpleModule_convolution_iff_isAtom.mpr hS
    let eL : S ≃ₗ[ℂ] ULift.{u} S := (ULift.moduleEquiv (R := ℂ) (M := S)).symm
    let : Comodule ℂ A (ULift.{u} S) := Comodule.Transport (R := ℂ) (C := A) eL
    have hLsimp : IsSimpleOrder (Subcomodule ℂ A (ULift.{u} S)) := by
      let f := (Comodule.transportToHom (R := ℂ) (C := A) eL).toConvolutionLinearMap
      have hfun : (f : S → ULift.{u} S) = eL := by
        funext x
        simp [f]
      have hbij : Function.Bijective f := hfun ▸ eL.bijective
      exact Comodule.isSimpleModule_convolution_iff.mp
        (IsSimpleModule.congr (LinearEquiv.ofBijective f hbij).symm)
    let bS : Basis (Fin (finrank ℂ S)) ℂ S := (stdOrthonormalBasis ℂ S).toBasis
    have hbS_unit : Comodule.coefficientMatrix (C := A) bS ∈
        unitary (Matrix (Fin (finrank ℂ S)) (Fin (finrank ℂ S)) A) :=
      hSU.coefficientMatrix_mem_unitary (stdOrthonormalBasis ℂ S)
    have hmat_eq : Comodule.coefficientMatrix (C := A) (bS.map eL) =
        Comodule.coefficientMatrix (C := A) bS :=
      Comodule.coefficientMatrix_map bS eL (Comodule.transportToHom eL)
        (Comodule.transportToHom_apply eL)
    refine ⟨ComoduleCat.of ℂ A (ULift.{u} S), hLsimp, finrank ℂ S, bS.map eL,
      by rwa [hmat_eq], ?_⟩
    exact (Comodule.matrixCoefficientSubmodule_transport (R := ℂ) (C := A) eL).symm
  -- Every vector in `EuclideanSpace ℂ (Fin n)` lies in the span of the simple subcomodules.
  refine Comodule.matrixCoefficientSubmodule_le fun φ m ↦ ?_
  have hle : (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n))) ≤
      Submodule.comap (Comodule.matrixCoefficientHom (C := A) φ).toLinearMap
        (sSup {P : Submodule ℂ A | HasUnitarySimpleWitness (A := A) P}) := by
    rw [← Subcomodule.top_toSubmodule (R := ℂ) (C := A), ← hAtoms, Subcomodule.sSup_toSubmodule]
    refine iSup_le fun S x hx ↦ ?_
    rw [Submodule.mem_comap]
    have hval : (Comodule.matrixCoefficientHom (C := A) φ).toLinearMap x =
        Comodule.matrixCoefficient (C := A) φ x := by simp
    rw [hval]
    have hxS : Comodule.matrixCoefficient (C := A) φ x =
        Comodule.matrixCoefficient (C := A) (φ.comp S.1.subtype.toLinearMap) ⟨x, hx⟩ := by
      simpa using (Comodule.matrixCoefficient_map S.1.subtype φ ⟨x, hx⟩)
    rw [hxS]
    exact le_sSup (hS_mem S.1 S.2) (Comodule.matrixCoefficient_mem_submodule _ _)
  simpa [Submodule.mem_comap] using hle (x := m) trivial

/-- From `span (unitaryCoefficientSet A) = ⊤`, every simple coefficient block admits a simple
unitary witness. -/
private theorem hasUnitarySimpleWitness_of_mem_simpleCoefficientSubmodules
    (hspan : Submodule.span ℂ (unitaryCoefficientSet A) = ⊤)
    {P : Submodule ℂ A} (hP : P ∈ Comodule.simpleCoefficientSubmodules ℂ A) :
    HasUnitarySimpleWitness (A := A) P := by
  set U : Set (Submodule ℂ A) := {Q | HasUnitarySimpleWitness (A := A) Q}
  have hU_sub : U ⊆ Comodule.simpleCoefficientSubmodules ℂ A := by
    rintro Q ⟨M, hM, _, _, _, rfl⟩
    exact Comodule.mem_simpleCoefficientSubmodules.mpr ⟨M, hM, rfl⟩
  have hU_top : sSup U = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro a ⟨n, hcom, hu, i, j, rfl⟩
    let : Comodule ℂ A (Fin n → ℂ) := hcom
    have hle := matrixCoefficientSubmodule_le_sSup_hasUnitarySimpleWitness (A := A) hu
    exact hle (by
      rw [Comodule.coefficientMatrix_apply]
      exact Comodule.matrixCoefficient_mem_submodule _ _)
  by_contra hnot
  have hsub : U ⊆ Comodule.simpleCoefficientSubmodules ℂ A \ {P} := fun Q hQ ↦
    ⟨hU_sub hQ, fun hQP ↦ hnot (hQP ▸ hQ)⟩
  have hdisj : Disjoint P (sSup (Comodule.simpleCoefficientSubmodules ℂ A \ {P})) :=
    Comodule.sSupIndep_simpleCoefficientSubmodules hP
  have htop : sSup (Comodule.simpleCoefficientSubmodules ℂ A \ {P}) = ⊤ :=
    eq_top_iff.mpr (hU_top ▸ sSup_le_sSup hsub)
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
  -- Transport `M` into `Type u` so its coefficient space lies in `simpleCoefficientSubmodules`.
  let e : M ≃ₗ[ℂ] ULift.{u} (Fin (finrank ℂ M) → ℂ) :=
    (Module.finBasis ℂ M).equivFun.trans (ULift.moduleEquiv (R := ℂ)).symm
  let : Comodule ℂ A (ULift.{u} (Fin (finrank ℂ M) → ℂ)) :=
    Comodule.Transport (R := ℂ) (C := A) e
  have hMsimp : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) M :=
    Comodule.isSimpleModule_convolution_iff.mpr inferInstance
  have hLsimp : IsSimpleOrder (Subcomodule ℂ A (ULift.{u} (Fin (finrank ℂ M) → ℂ))) := by
    let f := (Comodule.transportToHom (R := ℂ) (C := A) e).toConvolutionLinearMap
    have hfun : (f : M → ULift.{u} (Fin (finrank ℂ M) → ℂ)) = e := by
      funext m
      simp [f]
    have hbij : Function.Bijective f := hfun ▸ e.bijective
    exact Comodule.isSimpleModule_convolution_iff.mp
      (IsSimpleModule.congr (LinearEquiv.ofBijective f hbij).symm)
  have hPmem : Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ∈
      Comodule.simpleCoefficientSubmodules ℂ A := by
    rw [← Comodule.matrixCoefficientSubmodule_transport (R := ℂ) (C := A) e]
    exact Comodule.matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules
  obtain ⟨N, hNsimp, n, c, hc_unit, hPN⟩ :=
    hasUnitarySimpleWitness_of_mem_simpleCoefficientSubmodules hspan hPmem
  have : IsSimpleOrder (Subcomodule ℂ A N) := hNsimp
  obtain ⟨f, hf⟩ := (Comodule.matrixCoefficientSubmodule_eq_iff (R := ℂ) (C := A)
    (M := N) (N := M)).mp hPN.symm
  have hNconv : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) N :=
    Comodule.isSimpleModule_convolution_iff.mpr hNsimp
  have hf_ne : f.toConvolutionLinearMap ≠ 0 := fun h0 ↦ hf <| by
    ext x
    simpa using LinearMap.congr_fun h0 x
  have hbij : Function.Bijective f.toLinearMap := by
    have h1 := LinearMap.bijective_of_ne_zero hf_ne
    have hfun : (f.toLinearMap : N → M) = f.toConvolutionLinearMap := by
      funext x
      simp
    rwa [hfun]
  let iso : N ≃ₗ[ℂ] M := LinearEquiv.ofBijective f.toLinearMap hbij
  refine ⟨n, c.map iso, ?_⟩
  rw [Comodule.coefficientMatrix_map c iso f (fun _ ↦ rfl)]
  exact hc_unit

omit [StarRing A] [StarModule ℂ A] in
/-- The trivial line `ℂ · 1` is a simple coefficient submodule of `A`. -/
private theorem span_one_mem_simpleCoefficientSubmodules :
    Submodule.span ℂ ({(1 : A)} : Set A) ∈ Comodule.simpleCoefficientSubmodules ℂ A := by
  let : Comodule ℂ A ℂ := Comodule.trivial (R := ℂ) (C := A) (M := ℂ)
  let e : ℂ ≃ₗ[ℂ] ULift.{u} ℂ := (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm
  let : Comodule ℂ A (ULift.{u} ℂ) := Comodule.Transport (R := ℂ) (C := A) e
  have hsimp : IsSimpleOrder (Subcomodule ℂ A (ULift.{u} ℂ)) :=
    Subcomodule.isSimpleOrder_of_transitive (ULift.up (1 : ℂ))
      (fun h ↦ one_ne_zero (congrArg ULift.down h))
      (fun (c : ℂ) x ↦ c • x)
      (fun {v w} _ hw ↦ ⟨v.down * w.down⁻¹, ULift.ext (by
        have hw' : w.down ≠ 0 := fun h ↦ hw (ULift.ext h)
        simp [mul_assoc, inv_mul_cancel₀ hw'])⟩)
      (fun W c _ hx ↦ W.toSubmodule.smul_mem c hx)
  have hcoef : Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := ULift.{u} ℂ) =
      Submodule.span ℂ ({(1 : A)} : Set A) := by
    rw [Comodule.matrixCoefficientSubmodule_transport (R := ℂ) (C := A) e]
    exact Comodule.trivial_rankOne_matrixCoefficientSubmodule_eq_span_singleton_one
  rw [← hcoef]
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
  have : IsSimpleOrder (Subcomodule ℂ A (Module.Dual ℂ M)) :=
    (Subcomodule.isSimpleOrder_dual_iff (k := ℂ) (H := A) (M := M)
      (TauCeti.HopfAlgebra.antipode_bijective (R := ℂ) (A := A)).injective).mpr inferInstance
  obtain ⟨m, d, hd⟩ := exists_basis_mem_unitary_of_simple hspan (M := Module.Dual ℂ M)
  obtain ⟨Ft, ⟨hFt, _, hSchur1, _⟩, _⟩ :=
    LinearMap.existsUnique_posDef_schur_orthogonality hl hr h1 b hb d hd
  let B := Comodule.matrixCoefficientBasis (C := A) b
  let c : Fin n → Fin n → ℂ := fun i j ↦ B.repr ⟨x, hx⟩ (i, j)
  have hx_eq : x = ∑ i, ∑ j, c i j • Comodule.coefficientMatrix (C := A) b i j := by
    have hsum := congrArg Subtype.val (B.sum_repr ⟨x, hx⟩)
    simp only [Fintype.sum_prod_type, Submodule.coe_sum, SetLike.val_smul, B,
      Comodule.coe_matrixCoefficientBasis] at hsum
    exact hsum.symm
  have hquad : h (star x * x) =
      (Ft⁻¹.trace)⁻¹ * ∑ j, star (fun i ↦ c i j) ⬝ᵥ (Ft⁻¹ *ᵥ fun k ↦ c k j) := by
    rw [hx_eq]
    simp_rw [star_sum, star_smul, Finset.sum_mul]
    simp_rw [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul,
      hSchur1]
    have hstep : ∀ i j k,
        ∑ l, star (c i j) * (c k l * if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) =
          (Ft⁻¹.trace)⁻¹ * (star (c i j) * (Ft⁻¹ i k * c k j)) := by
      intro i j k
      rw [Finset.sum_eq_single j _ (by simp)]
      · simp only [↓reduceIte]
        ring
      · intro l _ hlj
        simp [Ne.symm hlj]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  rw [hquad]
  have hsum_nonneg : 0 ≤ ∑ j, star (fun i ↦ c i j) ⬝ᵥ (Ft⁻¹ *ᵥ fun k ↦ c k j) :=
    Finset.sum_nonneg fun j _ ↦ hFt.inv.posSemidef.dotProduct_mulVec_nonneg (fun i ↦ c i j)
  have htr_nonneg : 0 ≤ (Ft⁻¹.trace)⁻¹ := by
    have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
    have : Nonempty (Fin n) := b.index_nonempty
    obtain ⟨hre, him⟩ := Complex.lt_def.mp hFt.inv.trace_pos
    have heq : Ft⁻¹.trace = (Ft⁻¹.trace.re : ℂ) := Complex.ext rfl him.symm
    rw [heq, ← Complex.ofReal_inv]
    exact Complex.le_def.mpr ⟨inv_nonneg.mpr hre.le, rfl⟩
  rw [Complex.le_def] at htr_nonneg hsum_nonneg ⊢
  refine ⟨?_, by simp [Complex.mul_im, ← htr_nonneg.2, ← hsum_nonneg.2]⟩
  rw [Complex.mul_re, ← htr_nonneg.2, ← hsum_nonneg.2]
  simpa using mul_nonneg htr_nonneg.1 hsum_nonneg.1

/-- **Characterization of compact-type complex Hopf star algebras (Timmermann, Theorem 3.2.12).**
A complex Hopf star algebra admits an algebraic Haar state if and only if it is linearly spanned
by the matrix coefficients of its finite-dimensional unitary comodules. -/
theorem nonempty_algebraicHaar_iff_span_unitaryCoefficientSet_eq_top [StarCoalgebra ℂ A] :
    Nonempty (AlgebraicHaar A) ↔ Submodule.span ℂ (unitaryCoefficientSet A) = ⊤ := by
  constructor
  · -- Forward direction: linear reductivity + cosemisimplicity + algebraic unitarization.
    rintro ⟨h⟩
    rw [eq_top_iff,
      ← (AlgebraicHaar.isLinearlyReductive.{u, 0} h).iSup_matrixCoefficientSubmodule_eq_top]
    refine iSup_le fun S ↦ iSup_le fun hS ↦ ?_
    have : Module.Finite ℂ S := S.finite_of_isAtom hS
    obtain ⟨c, hc⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
      h.right_invariant h.functional_ne_zero h.positive (Module.finBasis ℂ S)
    exact matrixCoefficientSubmodule_le_span_unitaryCoefficientSet c hc
  · -- Backward direction: construct `h` on the internal direct sum of simple blocks and verify
    -- positivity using positivity-free weighted Schur orthogonality.
    intro hspan
    classical
    set S := Comodule.simpleCoefficientSubmodules ℂ A
    set P₁ : Submodule ℂ A := Submodule.span ℂ ({(1 : A)} : Set A)
    have hP₁ : P₁ ∈ S := span_one_mem_simpleCoefficientSubmodules (A := A)
    have hStop : sSup S = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro a ⟨n, hcom, hu, i, j, rfl⟩
      let : Comodule ℂ A (Fin n → ℂ) := hcom
      have hle := (matrixCoefficientSubmodule_le_sSup_hasUnitarySimpleWitness (A := A) hu).trans
        (sSup_le_sSup fun Q ⟨M, hM, _, _, _, hQ⟩ ↦
          Comodule.mem_simpleCoefficientSubmodules.mpr ⟨M, hM, hQ⟩)
      exact hle (by
        rw [Comodule.coefficientMatrix_apply]
        exact Comodule.matrixCoefficient_mem_submodule _ _)
    have hInt : DirectSum.IsInternal (fun P : S ↦ (P.1 : Submodule ℂ A)) := by
      apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      · exact (sSupIndep_iff _).mp Comodule.sSupIndep_simpleCoefficientSubmodules
      · rw [← sSup_eq_iSup', hStop]
    let iso : (⨁ P : S, P.1) ≃ₗ[ℂ] A :=
      LinearEquiv.ofBijective (DirectSum.coeLinearMap fun P : S ↦ (P.1 : Submodule ℂ A)) hInt
    have hiso (z : ⨁ P : S, P.1) :
        iso z = DirectSum.coeLinearMap (fun P : S ↦ (P.1 : Submodule ℂ A)) z := rfl
    let h : A →ₗ[ℂ] ℂ :=
      (DirectSum.toModule ℂ S ℂ fun P ↦
        if P.1 = P₁ then (Coalgebra.counit (R := ℂ)).comp P.1.subtype else 0).comp
        iso.symm.toLinearMap
    have h_apply_mem (P : S) {x : A} (hx : x ∈ P.1) :
        h x = if P.1 = P₁ then Coalgebra.counit (R := ℂ) x else 0 := by
      have hsymm : iso.symm x = DirectSum.lof ℂ S (fun Q : S ↦ (Q.1 : Type u)) P ⟨x, hx⟩ := by
        apply iso.injective
        rw [iso.apply_symm_apply, hiso, DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
      simp only [h, LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, DirectSum.toModule_lof]
      split_ifs <;> rfl
    have h1 : h 1 = 1 := by
      have hmem : (1 : A) ∈ P₁ := Submodule.subset_span (Set.mem_singleton 1)
      simp [h_apply_mem ⟨P₁, hP₁⟩ hmem]
    -- Check left and right invariance on each simple block `P ∈ S`.
    have hinv_block (P : S) :
        P.1 ≤ LinearMap.ker
          ((TensorProduct.rid ℂ A ∘ₗ h.lTensor A ∘ₗ Coalgebra.comul (R := ℂ)) -
            h.smulRight (1 : A)) ∧
        P.1 ≤ LinearMap.ker
          ((TensorProduct.lid ℂ A ∘ₗ h.rTensor A ∘ₗ Coalgebra.comul (R := ℂ)) -
            h.smulRight (1 : A)) := by
      by_cases hPP₁ : P.1 = P₁
      · constructor <;>
        · rw [hPP₁, Submodule.span_le]
          rintro _ rfl
          simp [h1, Algebra.TensorProduct.one_def]
      · obtain ⟨M, _, n, b, _, hPM⟩ :=
          hasUnitarySimpleWitness_of_mem_simpleCoefficientSubmodules hspan P.2
        have hzero {x : A} (hx : x ∈ P.1) : h x = 0 := by
          simp [h_apply_mem P hx, hPP₁]
        have hk_mem (p q : Fin n) :
            Comodule.coefficientMatrix (C := A) b p q ∈ P.1 := by
          rw [hPM, Comodule.coefficientMatrix_apply]
          exact Comodule.matrixCoefficient_mem_submodule _ _
        rw [hPM, ← Comodule.span_range_coefficientMatrix_eq b]
        constructor
        · rw [Submodule.span_le]
          rintro _ ⟨⟨i, j⟩, rfl⟩
          dsimp only
          simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
            LinearMap.smulRight_apply, Comodule.comul_coefficientMatrix_eq_sum b, map_sum,
            LinearMap.lTensor_tmul, hzero (hk_mem i j), zero_smul, sub_zero]
          exact Finset.sum_eq_zero fun k _ ↦ by
            simp [hzero (hk_mem k j)]
        · rw [Submodule.span_le]
          rintro _ ⟨⟨i, j⟩, rfl⟩
          dsimp only
          simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
            LinearMap.smulRight_apply, Comodule.comul_coefficientMatrix_eq_sum b, map_sum,
            LinearMap.rTensor_tmul, hzero (hk_mem i j), zero_smul, sub_zero]
          exact Finset.sum_eq_zero fun k _ ↦ by
            simp [hzero (hk_mem i k)]
    have hl : h.IsLeftInvariantIntegral := by
      rw [LinearMap.isLeftInvariantIntegral_iff]
      intro a
      have hker : LinearMap.ker
          ((TensorProduct.rid ℂ A ∘ₗ h.lTensor A ∘ₗ Coalgebra.comul (R := ℂ)) -
            h.smulRight (1 : A)) = ⊤ := by
        rw [eq_top_iff, ← hStop]
        exact sSup_le fun P hP ↦ (hinv_block ⟨P, hP⟩).1
      have ha : a ∈ LinearMap.ker
          ((TensorProduct.rid ℂ A ∘ₗ h.lTensor A ∘ₗ Coalgebra.comul (R := ℂ)) -
            h.smulRight (1 : A)) := by rw [hker]; trivial
      exact sub_eq_zero.mp ha
    have hr : h.IsRightInvariantIntegral := by
      rw [LinearMap.isRightInvariantIntegral_iff]
      intro a
      have hker : LinearMap.ker
          ((TensorProduct.lid ℂ A ∘ₗ h.rTensor A ∘ₗ Coalgebra.comul (R := ℂ)) -
            h.smulRight (1 : A)) = ⊤ := by
        rw [eq_top_iff, ← hStop]
        exact sSup_le fun P hP ↦ (hinv_block ⟨P, hP⟩).2
      have ha : a ∈ LinearMap.ker
          ((TensorProduct.lid ℂ A ∘ₗ h.rTensor A ∘ₗ Coalgebra.comul (R := ℂ)) -
            h.smulRight (1 : A)) := by rw [hker]; trivial
      exact sub_eq_zero.mp ha
    -- Choose a unitary simple witness `(M_P, b_P)` for every `P : S`, and prove positivity of `h`.
    choose M_P hM_P n_P b_P hb_P hP_eq using fun P : S ↦
      hasUnitarySimpleWitness_of_mem_simpleCoefficientSubmodules hspan P.2
    have hblock_ortho (P Q : S) (hPQ : P ≠ Q) {x y : A} (hx : x ∈ P.1) (hy : y ∈ Q.1) :
        h (star x * y) = 0 := by
      have : IsSimpleOrder (Subcomodule ℂ A (M_P P)) := hM_P P
      have : IsSimpleOrder (Subcomodule ℂ A (M_P Q)) := hM_P Q
      have hHom : ∀ g : Comodule.Hom ℂ A (M_P Q) (M_P P), g = 0 := by
        by_contra! H
        obtain ⟨g, hg⟩ := H
        have heq := Comodule.matrixCoefficientSubmodule_eq_of_ne_zero hg
        apply hPQ
        ext1
        rw [hP_eq P, hP_eq Q, heq]
      have hx' : x ∈ Submodule.span ℂ
          (Set.range fun p : Fin (n_P P) × Fin (n_P P) ↦
            Comodule.coefficientMatrix (C := A) (b_P P) p.1 p.2) := by
        rw [Comodule.span_range_coefficientMatrix_eq, ← hP_eq P]; exact hx
      have hy' : y ∈ Submodule.span ℂ
          (Set.range fun q : Fin (n_P Q) × Fin (n_P Q) ↦
            Comodule.coefficientMatrix (C := A) (b_P Q) q.1 q.2) := by
        rw [Comodule.span_range_coefficientMatrix_eq, ← hP_eq Q]; exact hy
      refine Submodule.span_induction (p := fun u _ ↦ h (star u * y) = 0) ?_ (by simp)
        (fun u v _ _ hu hv ↦ by simp [add_mul, hu, hv])
        (fun c u _ hu ↦ by simp [hu]) hx'
      rintro _ ⟨⟨i, j⟩, rfl⟩
      refine Submodule.span_induction (p := fun v _ ↦
        h (star (Comodule.coefficientMatrix (C := A) (b_P P) i j) * v) = 0) ?_ (by simp)
        (fun u v _ _ hu hv ↦ by simp [mul_add, hu, hv])
        (fun c v _ hv ↦ by simp [hv]) hy'
      rintro _ ⟨⟨k, l⟩, rfl⟩
      exact hr.apply_star_coefficientMatrix_mul_eq_zero (b_P P) (b_P Q) (hb_P P) hHom i j k l
    have hpos (a : A) : 0 ≤ h (star a * a) := by
      let z := iso.symm a
      have ha : a = ∑ P ∈ z.support, (z P : A) := by
        have h1' : iso z = a := iso.apply_symm_apply a
        rw [hiso, DirectSum.coeLinearMap_eq_dfinsuppSum] at h1'
        exact h1'.symm
      rw [ha, star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum, map_sum]
      refine Finset.sum_nonneg fun P hP ↦ ?_
      rw [Finset.sum_eq_single P]
      · have : IsSimpleOrder (Subcomodule ℂ A (M_P P)) := hM_P P
        exact nonneg_on_simpleBlock_of_schur hspan hl hr h1 (b_P P) (hb_P P)
          (hP_eq P ▸ (z P).2)
      · intro Q _ hQP
        exact hblock_ortho P Q (Ne.symm hQP) (z P).2 (z Q).2
      · intro hnot
        exact absurd hP hnot
    exact ⟨⟨h, h1, hl, hr, hpos⟩⟩

end CompactTypeIff

end TauCeti
