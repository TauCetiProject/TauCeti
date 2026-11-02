/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.Isometry
public import TauCeti.NumberTheory.IntegralLattice.ClassNumber
public import TauCeti.NumberTheory.BinaryQuadraticForm.FiniteClasses

/-!
# Finiteness of the class number of a binary lattice

A nondegenerate integral lattice of rank two has finitely many classes in its genus, whatever its
signature. This is the rank-two case of the finiteness of the class number, and its proof is
special to rank two: it runs through the binary norm form rather than through reduction of
definite forms or strong approximation.

A carrier basis `b` of a rank-two lattice `L` gives the norm form `A x² + 2B x y + C y²`
(`TauCeti.IntegralLattice.binaryNormForm`) of discriminant `-4 det L`, and lattices with bases of
equal norm forms are isometric (`TauCeti.IntegralLattice.exists_isometry_map_basis_iff`). Changing
`b` by `γ : SL(2, ℤ)` changes the norm form to a properly equivalent one, and every properly
equivalent form arises in this way (`TauCeti.IntegralLattice.exists_binaryNormForm_eq_smul`). For
a nonzero discriminant finitely many forms represent every proper class
(`TauCeti.BinaryQuadraticForm.exists_finset_forall_exists_smul_mem`): Lagrange reduced forms for a
nonsquare discriminant, triangular forms for a square one. Hence finitely many norm forms represent
all rank-two lattices of a given nonzero determinant, and all lattices in one genus have the rank
and the determinant of `L`.

The statement covers indefinite binary lattices, isotropic or not, where reduction of definite
forms does not apply, and it agrees with `TauCeti.IntegralLattice.IsPosDef.finite_genusClasses`
for definite ones.

## Main results

* `TauCeti.IntegralLattice.exists_finset_forall_exists_binaryNormForm_mem`: a finite set of binary
  forms contains a norm form of every rank-two lattice of a given nonzero determinant.
* `TauCeti.IntegralLattice.finite_of_pairwise_isEmpty_isometry_of_finrank_eq_two`: a family of
  pairwise non-isometric rank-two lattices of one nonzero determinant is finite.
* `TauCeti.IntegralLattice.finite_genusClasses_of_finrank_eq_two`: the genus of a nondegenerate
  rank-two lattice contains finitely many classes.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 13, for binary forms of arbitrary
  discriminant and the class number of a binary lattice.
* D. A. Cox, *Primes of the Form x² + ny²*, §2.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

/-- **Finitely many norm forms represent all rank-two lattices of a given nonzero determinant.**
For `d ≠ 0` there is a finite set `S` of binary quadratic forms such that every integral lattice
of rank two and determinant `d`, in any rational space, has a norm form in `S`. -/
theorem exists_finset_forall_exists_binaryNormForm_mem {d : ℤ} (hd : d ≠ 0) :
    ∃ S : Finset (BinaryQuadraticForm ℤ), ∀ {V : Type u} [AddCommGroup V] [Module ℚ V]
      (L : IntegralLattice V), finrank ℤ L = 2 → L.determinant = d →
        ∃ b : Basis (Fin 2) ℤ L, L.binaryNormForm b ∈ S := by
  obtain ⟨S, hS⟩ := BinaryQuadraticForm.exists_finset_forall_exists_smul_mem
    (mul_ne_zero (by decide : (-4 : ℤ) ≠ 0) hd)
  refine ⟨S, fun {V} _ _ L h2 hdet ↦ ?_⟩
  let b := Module.finBasisOfFinrankEq ℤ L h2
  obtain ⟨γ, hγ⟩ := hS (L.binaryNormForm b) (by rw [discrim_binaryNormForm, hdet])
  obtain ⟨b', hb'⟩ := L.exists_binaryNormForm_eq_smul b γ
  exact ⟨b', hb' ▸ hγ⟩

/-- **There are finitely many classes of rank-two lattices of a given nonzero determinant.** A
family of pairwise non-isometric integral lattices of rank two and determinant `d ≠ 0` is finite.
No definiteness is assumed. -/
theorem finite_of_pairwise_isEmpty_isometry_of_finrank_eq_two {ι : Type*} {V : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)] (L : ∀ i, IntegralLattice (V i)) {d : ℤ}
    (hd : d ≠ 0) (hrank : ∀ i, finrank ℤ (L i) = 2) (hdet : ∀ i, (L i).determinant = d)
    (hL : Pairwise fun i j ↦ IsEmpty (Isometry (L i) (L j))) : Finite ι := by
  obtain ⟨S, hS⟩ := exists_finset_forall_exists_binaryNormForm_mem.{u} hd
  choose b hb using fun i ↦ hS (L i) (hrank i) (hdet i)
  refine Finite.of_injective (fun i ↦ (⟨(L i).binaryNormForm (b i), hb i⟩ : S)) fun i j hij ↦ ?_
  by_contra hne
  obtain ⟨e, -⟩ := (exists_isometry_map_basis_iff (b i) (b j)).mpr (congrArg Subtype.val hij).symm
  exact (hL hne).false e

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- **The genus of a nondegenerate binary lattice contains finitely many classes.** The lattices
in the genus of `L` have the rank and the determinant of `L`. No definiteness is assumed, so this
covers indefinite binary lattices, isotropic or anisotropic. -/
theorem finite_genusClasses_of_finrank_eq_two {L : IntegralLattice V} [L.IsNondegenerate]
    (h2 : finrank ℤ L = 2) : L.genusClasses.Finite := by
  have hgen (c : L.genusClasses) : L.SameGenus c.1.out := mem_genusClasses_iff.mp c.2
  exact Set.finite_coe_iff.mp <| finite_of_pairwise_isEmpty_isometry_of_finrank_eq_two
    (fun c : L.genusClasses ↦ c.1.out) (L.determinant_ne_zero_iff.mpr L.form_nondegenerate)
    (fun c ↦ (hgen c).finrank_eq.symm.trans h2) (fun c ↦ (hgen c).determinant_eq.symm)
    fun c d hcd ↦ ⟨fun e ↦ hcd (Subtype.ext (IsometryQuotient.eq_of_isometry_out e))⟩

/-- A nondegenerate binary lattice has positive class number. -/
theorem classNumber_pos_of_finrank_eq_two {L : IntegralLattice V} [L.IsNondegenerate]
    (h2 : finrank ℤ L = 2) : 0 < L.classNumber :=
  classNumber_pos_iff.mpr (finite_genusClasses_of_finrank_eq_two h2)

end TauCeti.IntegralLattice
