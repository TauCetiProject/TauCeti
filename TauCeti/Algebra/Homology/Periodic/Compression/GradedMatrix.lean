/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.GradedMatrix
public import TauCeti.Algebra.Homology.Periodic.Compression.Homology

/-!
# Compression of complexes of graded matrices

Let `ι` be a finite set of generators with integer degrees `e : ι → ℤ`, and let `D` be a square
matrix raising degrees by one with `D * D = 0`, so that `K = gradedMatrixComplex e D` is a bounded
integer-graded complex of free modules. Reading the degrees modulo `n` gives a second graded
matrix complex, `gradedMatrixComplex (fun i ↦ (e i : ZMod n)) D`, with the same generators and the
same matrix. It is the `n`-periodic compression `Δₙ K` of `K`
(`TauCeti.PeriodicComplex.compressionGradedMatrixComplexIso`): the term of residue `r` of `Δₙ K`
is the sum of the free modules on the generators of the degrees congruent to `r`, which is the free
module on the generators whose degree is congruent to `r`.

Combined with the homology of the compression, this computes the homology of the reduced complex:
in residue `r` it is the direct sum of the homology of `K` in the degrees congruent to `r`
(`TauCeti.PeriodicComplex.homologyGradedMatrixComplexIntCastIso`), and over a field its total
dimension is the total dimension of the homology of `K`
(`TauCeti.PeriodicComplex.sum_finrank_homology_gradedMatrixComplex_intCast`).

This is the computation of the homology of a Morse complex whose grading is read modulo twice the
minimal Chern number, as it appears after the specialization `t ↦ 1` of the Laurent coefficients
of monotone Hamiltonian Floer theory.

## Main results

* `TauCeti.PeriodicComplex.compressionGradedMatrixComplexIso`: `Δₙ (gradedMatrixComplex e D)` is
  isomorphic to `gradedMatrixComplex (fun i ↦ (e i : ZMod n)) D`.
* `TauCeti.PeriodicComplex.homologyGradedMatrixComplexIntCastIso`: the homology of the reduced
  complex in residue `r` is the direct sum of the homology of `gradedMatrixComplex e D` in the
  degrees congruent to `r`.
* `TauCeti.PeriodicComplex.sum_finrank_homology_gradedMatrixComplex_intCast`: over a field the two
  complexes have homology of the same total dimension.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Module

namespace TauCeti

universe u v

namespace PeriodicComplex

section Compression

/-- Reading the degrees modulo `n` keeps a matrix raising the degrees by one raising them by one. -/
theorem intCast_eq_intCast_add_one {R : Type*} [Zero R] {ι : Type*} (n : ℕ) {e : ι → ℤ}
    {D : Matrix ι ι R} (hD : ∀ i k, D i k ≠ 0 → e k = e i + 1) (i k : ι) (h : D i k ≠ 0) :
    (e k : ZMod n) = e i + 1 := by
  rw [hD i k h, Int.cast_add, Int.cast_one]

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] (n : ℕ) (e : ι → ℤ)
  (D : Matrix ι ι R) (hD : ∀ i k, D i k ≠ 0 → e k = e i + 1) (hDD : D * D = 0)

/-- The generators of degree `j` go to the generators of their residue, and to zero in the other
residues. -/
private def toResidue (j : ℤ) (r : ZMod n) :
    (gradedMatrixComplex e D hD hDD).X j ⟶
      (gradedMatrixComplex (fun i ↦ (e i : ZMod n)) D
        (intCast_eq_intCast_add_one n hD) hDD).X r :=
  ModuleCat.ofHom <| (gradedMatrixComplexBasis e D hD hDD j).constr R fun i ↦
    if h : (e i : ZMod n) = r then gradedMatrixComplexBasis _ D _ hDD r ⟨i, h⟩ else 0

private theorem toResidue_basis (j : ℤ) (r : ZMod n) (i : {i // e i = j})
    (h : (e i : ZMod n) = r) :
    (toResidue n e D hD hDD j r).hom (gradedMatrixComplexBasis e D hD hDD j i) =
      gradedMatrixComplexBasis _ D
        (intCast_eq_intCast_add_one n hD) hDD r ⟨i, h⟩ := by
  rw [toResidue, ModuleCat.hom_ofHom, Basis.constr_basis]
  simp [h]

/-- The generators of residue `r` go to the same generators in the summands of their degrees. -/
private def fromResidue (r : ZMod n) :
    (gradedMatrixComplex (fun i ↦ (e i : ZMod n)) D
        (intCast_eq_intCast_add_one n hD) hDD).X r ⟶
      (compression n (gradedMatrixComplex e D hD hDD)).X r :=
  ModuleCat.ofHom <| (gradedMatrixComplexBasis _ D _ hDD r).constr R fun i ↦
    (ιCompression n (gradedMatrixComplex e D hD hDD) (e i) r i.property).hom
      (gradedMatrixComplexBasis e D hD hDD (e i) ⟨i, rfl⟩)

private theorem fromResidue_basis (r : ZMod n) (i : {i // (e i : ZMod n) = r}) :
    (fromResidue n e D hD hDD r).hom (gradedMatrixComplexBasis _ D
        (intCast_eq_intCast_add_one n hD) hDD r i) =
      (ιCompression n (gradedMatrixComplex e D hD hDD) (e i) r i.property).hom
        (gradedMatrixComplexBasis e D hD hDD (e i) ⟨i, rfl⟩) := by
  rw [fromResidue, ModuleCat.hom_ofHom, Basis.constr_basis]

private theorem compressionDesc_toResidue_basis (j : ℤ) (r : ZMod n) (hj : (j : ZMod n) = r)
    (i : {i // e i = j}) :
    (compressionDesc n _ fun j _ ↦ toResidue n e D hD hDD j r).hom
        ((ιCompression n (gradedMatrixComplex e D hD hDD) j r hj).hom
          (gradedMatrixComplexBasis e D hD hDD j i)) =
      gradedMatrixComplexBasis _ D (intCast_eq_intCast_add_one n hD) hDD r
        ⟨i, by rw [i.property, hj]⟩ := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ιCompression_compressionDesc]
  exact toResidue_basis n e D hD hDD j r i _

/-- The term of residue `r` of the compression of `gradedMatrixComplex e D` is the term of residue
`r` of the reduced complex: the generators of a summand go to the same generators. -/
private def compressionXIso (r : ZMod n) :
    (compression n (gradedMatrixComplex e D hD hDD)).X r ≅
      (gradedMatrixComplex (fun i ↦ (e i : ZMod n)) D
        (intCast_eq_intCast_add_one n hD) hDD).X r where
  hom := compressionDesc n _ fun j _ ↦ toResidue n e D hD hDD j r
  inv := fromResidue n e D hD hDD r
  hom_inv_id := by
    refine compression_hom_ext fun j hj ↦ ?_
    rw [ιCompression_compressionDesc_assoc, Category.comp_id]
    refine ModuleCat.hom_ext <| (gradedMatrixComplexBasis e D hD hDD j).ext fun i ↦ ?_
    obtain ⟨i, rfl⟩ := i
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, toResidue_basis n e D hD hDD _ r ⟨i, rfl⟩ hj,
      fromResidue_basis]
  inv_hom_id := ModuleCat.hom_ext <| (gradedMatrixComplexBasis _ D _ hDD r).ext fun i ↦ by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, fromResidue_basis,
      compressionDesc_toResidue_basis, ModuleCat.hom_id, LinearMap.id_apply]

/-- **The compression of the complex of a graded matrix** is the complex of the same matrix with
the degrees read modulo `n`: `Δₙ (gradedMatrixComplex e D) ≅ gradedMatrixComplex (e mod n) D`.
The generators of each summand go to the same generators
(`TauCeti.PeriodicComplex.compressionGradedMatrixComplexIso_hom_f_ιCompression`). -/
def compressionGradedMatrixComplexIso :
    compression n (gradedMatrixComplex e D hD hDD) ≅
      gradedMatrixComplex (fun i ↦ (e i : ZMod n)) D
        (intCast_eq_intCast_add_one n hD) hDD :=
  HomologicalComplex.Hom.isoOfComponents (compressionXIso n e D hD hDD) fun r s hrs ↦ by
    refine compression_hom_ext fun j hj ↦ ModuleCat.hom_ext <|
      (gradedMatrixComplexBasis e D hD hDD j).ext fun i ↦ ?_
    have hj' : ((j + 1 : ℤ) : ZMod n) = s := by rw [Int.cast_add, Int.cast_one, hj]; exact hrs
    obtain ⟨i, rfl⟩ := i
    rw [ιCompression_d_assoc n _ (e i) (e i + 1) rfl r s hj hj']
    simp only [compressionXIso, ιCompression_compressionDesc_assoc, ModuleCat.hom_comp,
      LinearMap.comp_apply, toResidue_basis n e D hD hDD _ r ⟨i, rfl⟩ hj,
      gradedMatrixComplex_d_basis, map_sum, map_smul]
    -- Both sides are sums over the generators of the target: those of degree `e i + 1`, and
    -- those of residue `s`. The second sum has more terms, on which the matrix entry vanishes.
    refine (Fintype.sum_of_injective (fun k : {k // e k = e i + 1} ↦
        (⟨k, by rw [k.property, ← hj']⟩ : {k // (e k : ZMod n) = s}))
      (fun k k' h ↦ Subtype.ext (congrArg Subtype.val h :)) _ _ (fun k hk ↦ ?_)
      fun k ↦ by rw [compressionDesc_toResidue_basis]).symm
    have : D i k = 0 := by
      by_contra h
      exact hk ⟨⟨k, hD i k h⟩, rfl⟩
    rw [this, zero_smul]

/-- The isomorphism `compressionGradedMatrixComplexIso` sends a generator of a summand of the
compression to the same generator of the reduced complex. -/
@[simp]
theorem compressionGradedMatrixComplexIso_hom_f_ιCompression (j : ℤ) (r : ZMod n)
    (hj : (j : ZMod n) = r) (i : {i // e i = j}) :
    ((compressionGradedMatrixComplexIso n e D hD hDD).hom.f r).hom
        ((ιCompression n (gradedMatrixComplex e D hD hDD) j r hj).hom
          (gradedMatrixComplexBasis e D hD hDD j i)) =
      gradedMatrixComplexBasis _ D (intCast_eq_intCast_add_one n hD) hDD
        r ⟨i, by rw [i.property, hj]⟩ := by
  simp only [compressionGradedMatrixComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    compressionXIso]
  exact compressionDesc_toResidue_basis n e D hD hDD j r hj i

/-- The inverse of `compressionGradedMatrixComplexIso` sends a generator of residue `r` to the same
generator in the summand of its degree. -/
@[simp]
theorem compressionGradedMatrixComplexIso_inv_f_basis (r : ZMod n)
    (i : {i // (e i : ZMod n) = r}) :
    ((compressionGradedMatrixComplexIso n e D hD hDD).inv.f r).hom
        (gradedMatrixComplexBasis _ D (intCast_eq_intCast_add_one n hD) hDD r i) =
      (ιCompression n (gradedMatrixComplex e D hD hDD) (e i) r i.property).hom
        (gradedMatrixComplexBasis e D hD hDD (e i) ⟨i, rfl⟩) := by
  simp only [compressionGradedMatrixComplexIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    compressionXIso]
  exact fromResidue_basis n e D hD hDD r i

/-- **The homology of the complex of a graded matrix with degrees read modulo `n`.** If the
degrees of the generators lie in `[a, b]`, the homology of the reduced complex in residue `r` is
the direct sum of the homology of `gradedMatrixComplex e D` in the degrees of `[a, b]` congruent to
`r`. -/
def homologyGradedMatrixComplexIntCastIso (a b : ℤ) (ha : ∀ i, a ≤ e i) (hb : ∀ i, e i ≤ b)
    (r : ZMod n) :
    (gradedMatrixComplex (fun i ↦ (e i : ZMod n)) D
        (intCast_eq_intCast_add_one n hD) hDD).homology r ≅
      ⨁ fun j : ({j ∈ Finset.Icc a b | (j : ZMod n) = r} : Finset ℤ) ↦
        (gradedMatrixComplex e D hD hDD).homology j :=
  have := isStrictlyGE_gradedMatrixComplex (hD := hD) (hDD := hDD) ha
  have := isStrictlyLE_gradedMatrixComplex (hD := hD) (hDD := hDD) hb
  (HomologicalComplex.homologyFunctor _ _ r).mapIso
      (compressionGradedMatrixComplexIso n e D hD hDD).symm ≪≫
    compressionHomologyIso n _ a b r

end Compression

section Finrank

variable {k : Type u} [Field k] {ι : Type v} [Fintype ι] (n : ℕ) [NeZero n] (e : ι → ℤ)
  (D : Matrix ι ι k) (hD : ∀ i k, D i k ≠ 0 → e k = e i + 1) (hDD : D * D = 0)

/-- Over a field, reading the degrees of a graded matrix complex modulo a positive `n` does not
change the total dimension of its homology, if the degrees of the generators lie in `[a, b]`. -/
theorem sum_finrank_homology_gradedMatrixComplex_intCast (a b : ℤ) (ha : ∀ i, a ≤ e i)
    (hb : ∀ i, e i ≤ b) :
    ∑ r : ZMod n, finrank k ((gradedMatrixComplex (fun i ↦ (e i : ZMod n)) D
        (intCast_eq_intCast_add_one n hD) hDD).homology r) =
      ∑ j ∈ Finset.Icc a b, finrank k ((gradedMatrixComplex e D hD hDD).homology j) := by
  have := isStrictlyGE_gradedMatrixComplex (hD := hD) (hDD := hDD) ha
  have := isStrictlyLE_gradedMatrixComplex (hD := hD) (hDD := hDD) hb
  have (j : ℤ) : Module.Finite k ((gradedMatrixComplex e D hD hDD).homology j) :=
    have : IsNoetherian k ((gradedMatrixComplex e D hD hDD).sc j).X₂ :=
      inferInstanceAs (IsNoetherian k ((gradedMatrixComplex e D hD hDD).X j))
    ((gradedMatrixComplex e D hD hDD).sc j).finite_homology
  rw [← sum_finrank_homology_compression n _ a b]
  exact Finset.sum_congr rfl fun r _ ↦ ((HomologicalComplex.homologyFunctor _ _ r).mapIso
    (compressionGradedMatrixComplexIso n e D hD hDD)).toLinearEquiv.finrank_eq.symm

end Finrank

end PeriodicComplex

end TauCeti
