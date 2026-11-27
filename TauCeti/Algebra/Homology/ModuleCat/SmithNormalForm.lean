/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.Localization
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.LinearAlgebra.FreeModule.PID
public import TauCeti.LinearAlgebra.FreeModule.SmithSubquotient

/-!
# Homology of complexes of finite free modules over a PID

Let `R` be a principal ideal domain and let `X₁ ⟶ X₂ ⟶ X₃` be a short complex of `R`-modules with
maps `f` and `g`, with `X₂` finite free and `X₃` torsion-free. Choose a Smith normal form of the
boundaries `B = im f` inside `X₂`: a basis `b` of `X₂`, selected vectors `b (e j)` and nonzero
coefficients `a j` such that the `a j • b (e j)` span `B`. Then the homology `ker g ⧸ im f` is

`R ^ (rank X₂ - rank g - |κ|) × Π j, R ⧸ (a j)`

(`CategoryTheory.ShortComplex.moduleCatHomologyEquivOfRangeEqSpan`), and the class of a cycle `z`
has torsion coordinates the classes of the coordinates of `z` along the selected vectors. Indeed,
`g (a j • b (e j)) = 0` and `X₃` is torsion-free, so every selected vector `b (e j)` is a cycle
(`CategoryTheory.ShortComplex.mem_ker_g_of_smul_mem_range_f`); the cycles then split as the free
module on the selected vectors times the cycles off them, and `B` sits in the first factor as the
span of the `a j • b (e j)`. The free rank `rank X₂ - rank g - |κ|` is `rank Z - rank B`, and
`|κ|` is the rank of `f`.

Applied to a homological complex `C` of modules over `R` whose term `Cⁱ` is finite free and whose
next term is torsion-free, this computes

`Hⁱ(C) ≅ R ^ (rank Cⁱ - rank dⁱ - rank dⁱ⁻¹) × Π j, R ⧸ (eⱼ)`,

where the `eⱼ` are the diagonal coefficients of a Smith normal form of the boundaries in `Cⁱ`
(`HomologicalComplex.homologyEquivOfSmithNormalForm`), or equivalently the nonzero entries
of a rectangular diagonal matrix `L * A * Q` with `L`, `Q` of unit determinant, where `A` is the
matrix of `dⁱ⁻¹` (`HomologicalComplex.nonempty_homologyEquiv_of_mul_toMatrix_mul_eq`). Such
a presentation always exists (`HomologicalComplex.exists_homologyEquiv`), by Mathlib's
`Submodule.smithNormalForm`. Over `ℤ` the factors `ℤ ⧸ (eⱼ)` with `|eⱼ| = 1` vanish and the
others are the cyclic groups `ℤ ⧸ (|eⱼ|)` making up the torsion subgroup, so this computes the
integral homology of a bounded complex of finite free abelian groups from integer matrices,
torsion included.

## Main definitions

* `CategoryTheory.ShortComplex.moduleCatHomologyEquivOfRangeEqSpan`: the homology of a short
  complex of modules, from a diagonal presentation of the boundaries.
* `CategoryTheory.ShortComplex.moduleCatHomologyEquivOfSmithNormalForm`: the same from a
  Smith normal form of the boundaries in Mathlib's sense.
* `HomologicalComplex.homologyEquivOfSmithNormalForm`: the homology of a complex in a
  degree whose term is finite free and whose next term is torsion-free.

## Main results

* `HomologicalComplex.nonempty_homologyEquiv_of_mul_toMatrix_mul_eq`: the homology from a
  diagonalization of the matrix of the incoming differential by unimodular transformations.
* `HomologicalComplex.exists_homologyEquiv`: such a homology group is
  `R ^ (rank Cⁱ - rank dⁱ - rank dⁱ⁻¹) × Π j, R ⧸ (eⱼ)` for some nonzero `eⱼ`, as many as the rank
  of `dⁱ⁻¹`.

## References

* J. R. Munkres, *Elements of Algebraic Topology*, Addison-Wesley, 1984, §11.
-/

public section

noncomputable section

open Module Submodule

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R] [IsDomain R] (S : ShortComplex (ModuleCat.{v} R))
  {ι κ : Type*} (b : Basis ι R S.X₂) (e : κ ↪ ι) (a : κ → R)

variable [IsPrincipalIdealRing R] [Finite ι] [Fintype κ] [Module.IsTorsionFree R S.X₃]

omit [IsPrincipalIdealRing R] [Finite ι] [Fintype κ] in
variable {S b e a} in
/-- Every selected basis vector is a cycle when the rescaled vectors `a j • b (e j)`, with
`a j ≠ 0`, span the boundaries. -/
private theorem mem_ker_g_of_range_f_eq_span (ha : ∀ j, a j ≠ 0)
    (hf : LinearMap.range S.f.hom = span R (Set.range fun j ↦ a j • b (e j))) (j : κ) :
    b (e j) ∈ LinearMap.ker S.g.hom :=
  mem_ker_g_of_smul_mem_range_f (.of_ne_zero (ha j)) (hf ▸ subset_span ⟨j, rfl⟩)

variable {S b e} in
/-- The cycles off the selected basis vectors form a free module whose rank is the rank of `X₂`,
minus the rank of `g`, minus the number of selected vectors. -/
private def kerInfSpanEquivFin (hZ : ∀ j, b (e j) ∈ LinearMap.ker S.g.hom) :
    ↥(LinearMap.ker S.g.hom ⊓ span R (b '' (Set.range e)ᶜ)) ≃ₗ[R]
      (Fin (finrank R S.X₂ - finrank R (LinearMap.range S.g.hom) - Fintype.card κ) → R) :=
  haveI : Module.Free R S.X₂ := .of_basis b
  haveI : Module.Finite R S.X₂ := .of_basis b
  haveI := Submodule.free_of_isPrincipalIdealRing
    (LinearMap.ker S.g.hom ⊓ span R (b '' (Set.range e)ᶜ))
  (Module.finBasisOfFinrankEq R _ (by
    have hker := (LinearMap.ker S.g.hom).finrank_quotient_add_finrank
    rw [S.g.hom.quotKerEquivRange.finrank_eq, b.finrank_eq_card_add_finrank_inf e hZ] at hker
    omega)).equivFun

/-- **The homology of a short complex with free middle term over a PID.** If the middle term of a
short complex of modules over a principal ideal domain has a finite basis `b`, the next term is
torsion-free, and the boundaries are spanned by the rescaled selected basis vectors
`a j • b (e j)` with `a j ≠ 0`, then the homology is the product of the free module of rank
`rank X₂ - rank g - |κ|` and of the cyclic modules `R ⧸ (a j)`. -/
def moduleCatHomologyEquivOfRangeEqSpan (ha : ∀ j, a j ≠ 0)
    (hf : LinearMap.range S.f.hom = span R (Set.range fun j ↦ a j • b (e j))) :
    S.homology ≃ₗ[R]
      (Fin (finrank R S.X₂ - finrank R (LinearMap.range S.g.hom) - Fintype.card κ) → R) ×
        ∀ j, R ⧸ Ideal.span ({a j} : Set R) :=
  (S.moduleCatHomologyIso.toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.range_codRestrict, hf]))).trans <|
    (b.quotientSpanSMulEquivOfMem e (mem_ker_g_of_range_f_eq_span ha hf) a).trans <|
      (LinearEquiv.prodComm R _ _).trans <|
        LinearEquiv.prodCongr (kerInfSpanEquivFin (mem_ker_g_of_range_f_eq_span ha hf))
          (LinearEquiv.refl R _)

/-- The torsion coordinates of the class of a cycle `z` are the classes modulo the `a j` of its
coordinates along the selected basis vectors. -/
theorem moduleCatHomologyEquivOfRangeEqSpan_homologyπ_snd (ha : ∀ j, a j ≠ 0)
    (hf : LinearMap.range S.f.hom = span R (Set.range fun j ↦ a j • b (e j)))
    (z : LinearMap.ker S.g.hom) (j : κ) :
    (S.moduleCatHomologyEquivOfRangeEqSpan b e a ha hf
      (S.homologyπ (S.moduleCatCyclesIso.inv z))).2 j =
      Ideal.Quotient.mk _ (b.repr z (e j)) := by
  simp only [moduleCatHomologyEquivOfRangeEqSpan, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, moduleCatCyclesIso_inv_π_assoc,
    Iso.inv_hom_id, Category.comp_id]
  simp

/-- **The homology of a short complex from a Smith normal form of its boundaries.** Over a
principal ideal domain, if the middle term is finite free and the next term torsion-free, a Smith
normal form of the boundaries with diagonal coefficients `a j` exhibits the homology as the
product of the free module of rank `rank X₂ - rank g - rank f` and of the cyclic modules
`R ⧸ (a j)`. -/
def moduleCatHomologyEquivOfSmithNormalForm {n : ℕ}
    (snf : Basis.SmithNormalForm (LinearMap.range S.f.hom) ι n) :
    S.homology ≃ₗ[R]
      (Fin (finrank R S.X₂ - finrank R (LinearMap.range S.g.hom) -
          finrank R (LinearMap.range S.f.hom)) → R) ×
        ∀ j, R ⧸ Ideal.span ({snf.a j} : Set R) :=
  (S.moduleCatHomologyEquivOfRangeEqSpan snf.bM snf.f snf.a snf.a_ne_zero
      snf.eq_span_range_smul).trans
    (LinearEquiv.prodCongr
      (LinearEquiv.funCongrLeft R R (finCongr (by
        rw [finrank_eq_card_basis snf.bN, Fintype.card_fin]))) (LinearEquiv.refl R _))

/-- The torsion coordinates of the class of a cycle `z` are the classes modulo the diagonal
coefficients `a j` of its coordinates along the selected Smith basis vectors. -/
theorem moduleCatHomologyEquivOfSmithNormalForm_homologyπ_snd {n : ℕ}
    (snf : Basis.SmithNormalForm (LinearMap.range S.f.hom) ι n) (z : LinearMap.ker S.g.hom)
    (j : Fin n) :
    (S.moduleCatHomologyEquivOfSmithNormalForm snf
      (S.homologyπ (S.moduleCatCyclesIso.inv z))).2 j =
      Ideal.Quotient.mk _ (snf.bM.repr z (snf.f j)) :=
  S.moduleCatHomologyEquivOfRangeEqSpan_homologyπ_snd snf.bM snf.f snf.a snf.a_ne_zero
    snf.eq_span_range_smul z j

end CategoryTheory.ShortComplex

namespace HomologicalComplex

open CategoryTheory

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {ι : Type*}
  {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (i : ι)
  [Module.IsTorsionFree R (C.X (c.next i))]

/-- The term `(C.sc i).X₃` is `C.X (c.next i)` by definition, so it inherits torsion-freeness. -/
private local instance isTorsionFree_sc_X₃ : Module.IsTorsionFree R (C.sc i).X₃ :=
  ‹Module.IsTorsionFree R (C.X (c.next i))›

/-- **The homology of a complex of free modules over a PID.** If the term `Cⁱ` of a complex of
modules over a principal ideal domain is finite free and the next term is torsion-free, a Smith
normal form of the boundaries `im dⁱ⁻¹` in `Cⁱ`, with diagonal coefficients `eⱼ`, exhibits
`Hⁱ(C)` as `R ^ (rank Cⁱ - rank dⁱ - rank dⁱ⁻¹) × Π j, R ⧸ (eⱼ)`. -/
def homologyEquivOfSmithNormalForm {κ : Type*} [Finite κ] {n : ℕ}
    (snf : Basis.SmithNormalForm (LinearMap.range (C.d (c.prev i) i).hom) κ n) :
    C.homology i ≃ₗ[R]
      (Fin (finrank R (C.X i) - finrank R (LinearMap.range (C.d i (c.next i)).hom) -
          finrank R (LinearMap.range (C.d (c.prev i) i).hom)) → R) ×
        ∀ j, R ⧸ Ideal.span ({snf.a j} : Set R) :=
  (C.sc i).moduleCatHomologyEquivOfSmithNormalForm snf

/-- The torsion coordinates of the homology class of a cycle `z` of `Cⁱ` are the classes modulo
the diagonal coefficients `eⱼ` of its coordinates along the selected Smith basis vectors. -/
theorem homologyEquivOfSmithNormalForm_homologyπ_snd {κ : Type*} [Finite κ] {n : ℕ}
    (snf : Basis.SmithNormalForm (LinearMap.range (C.d (c.prev i) i).hom) κ n)
    (z : LinearMap.ker (C.d i (c.next i)).hom) (j : Fin n) :
    (C.homologyEquivOfSmithNormalForm i snf
      (C.homologyπ i ((C.sc i).moduleCatCyclesIso.inv z))).2 j =
      Ideal.Quotient.mk _ (snf.bM.repr z (snf.f j)) :=
  (C.sc i).moduleCatHomologyEquivOfSmithNormalForm_homologyπ_snd snf z j

/-- **The homology of a complex of free modules from the matrix of its differential.** Let the term
`Cⁱ` of a complex of modules over a principal ideal domain have a finite basis `b₁`, let the next
term be torsion-free, and let `A` be the matrix of `dⁱ⁻¹` in a finite basis `b₀` of `Cⁱ⁻¹` and
`b₁`. If `L * A * Q`, for `L` and `Q` of unit determinant, is the rectangular diagonal matrix with
the nonzero entry `a j` in row `e j` and column `e' j` for each `j`, then
`Hⁱ(C) ≅ R ^ (rank Cⁱ - rank dⁱ - |κ|) × Π j, R ⧸ (a j)`. -/
theorem nonempty_homologyEquiv_of_mul_toMatrix_mul_eq {ι₀ ι₁ κ : Type*} [Fintype ι₀]
    [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁] [Fintype κ] (b₀ : Basis ι₀ R (C.X (c.prev i)))
    (b₁ : Basis ι₁ R (C.X i)) {L : Matrix ι₁ ι₁ R} {Q : Matrix ι₀ ι₀ R} (hL : IsUnit L.det)
    (hQ : IsUnit Q.det) {e : κ ↪ ι₁} {e' : κ ↪ ι₀} {a : κ → R} (ha : ∀ j, a j ≠ 0)
    (h : L * LinearMap.toMatrix b₀ b₁ (C.d (c.prev i) i).hom * Q =
      ∑ j, Matrix.single (e j) (e' j) (a j)) :
    Nonempty (C.homology i ≃ₗ[R]
      (Fin (finrank R (C.X i) - finrank R (LinearMap.range (C.d i (c.next i)).hom) -
          Fintype.card κ) → R) ×
        ∀ j, R ⧸ Ideal.span ({a j} : Set R)) := by
  obtain ⟨b, -, hb⟩ :=
    (C.d (c.prev i) i).hom.exists_basis_range_eq_span_range_smul_of_mul_toMatrix_mul_eq b₀ b₁ hL
      hQ h
  exact ⟨(C.sc i).moduleCatHomologyEquivOfRangeEqSpan b e a ha hb⟩

/-- **Homology of a complex of finite free modules over a PID.** If the term `Cⁱ` of a complex of
modules over a principal ideal domain is finite free and the next term is torsion-free, then
`Hⁱ(C) ≅ R ^ (rank Cⁱ - rank dⁱ - rank dⁱ⁻¹) × Π j, R ⧸ (eⱼ)` for some nonzero `eⱼ`, as many as
the rank of `dⁱ⁻¹`. -/
theorem exists_homologyEquiv [Module.Free R (C.X i)] [Module.Finite R (C.X i)] :
    ∃ (n : ℕ) (e : Fin n → R), n = finrank R (LinearMap.range (C.d (c.prev i) i).hom) ∧
      (∀ j, e j ≠ 0) ∧
      Nonempty (C.homology i ≃ₗ[R]
        (Fin (finrank R (C.X i) - finrank R (LinearMap.range (C.d i (c.next i)).hom) -
            finrank R (LinearMap.range (C.d (c.prev i) i).hom)) → R) ×
          ∀ j, R ⧸ Ideal.span ({e j} : Set R)) := by
  obtain ⟨n, snf⟩ := (LinearMap.range (C.d (c.prev i) i).hom).smithNormalForm
    (Module.Free.chooseBasis R (C.X i))
  refine ⟨n, snf.a, ?_, snf.a_ne_zero, ⟨C.homologyEquivOfSmithNormalForm i snf⟩⟩
  rw [finrank_eq_card_basis snf.bN, Fintype.card_fin]

end HomologicalComplex
