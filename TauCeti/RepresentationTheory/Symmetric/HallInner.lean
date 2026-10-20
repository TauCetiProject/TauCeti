/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.FrobeniusCharacteristic
public import TauCeti.RepresentationTheory.Symmetric.Specht.Orthogonality
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basis

/-!
# The Hall inner product and the Frobenius characteristic

For `d ≥ n`, the symmetric homogeneous polynomials of degree `n` in `d` variables have the Schur
basis `TauCeti.schurBasis`, indexed by the partitions of `n`.  The **Hall inner product** is the
bilinear form that makes this basis orthonormal, `⟨s_μ, s_ν⟩ = δ_{μν}`.  In this finite-variable
setting it is the degree-`n` shadow of the Hall inner product on the stable ring of symmetric
functions; the stable ring itself is not built here.

The main results are:

* `TauCeti.hallInner_psumPart`: the power-sum products are orthogonal with the classical weights,
  `⟨p_μ, p_ν⟩ = z_μ δ_{μν}`.  Over `ℂ` this follows from the second orthogonality relation for
  the character table of `Sₙ`, using Frobenius's formula
  `TauCeti.psumPart_eq_sum_spechtCharValue_smul_schurPoly`.
* `TauCeti.characterPairing_eq_hallInner`: **the Frobenius characteristic is an isometry** from
  the character pairing on class functions of `Sₙ` to the Hall inner product.  Equivalently, the
  Specht characters form an orthonormal basis just as the Schur polynomials do.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I, Section 4
  (the Hall inner product and the power-sum orthogonality).
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4, §4.1 and
  Appendix A.
-/

public section

namespace TauCeti

open MvPolynomial Finset

variable {n : ℕ}

/-- The Schur basis of the symmetric homogeneous polynomials of degree `n` in `d` variables,
indexed by all partitions of `n`.  The hypothesis `n ≤ d` lets every partition of `n` fit in the
alphabet `Fin d`, through `TauCeti.partitionEquivSchurIndex`. -/
noncomputable def schurBasis (n d : ℕ) (h : n ≤ d) :
    Module.Basis (n.Partition) ℂ (symmetricHomogeneousSubmodule (Fin d) ℂ n) :=
  (schurPolyBasis (Fin d) ℂ n).reindex (partitionEquivSchurIndex n d h).symm

/-- The `μ`-th vector of `TauCeti.schurBasis` is the Schur polynomial `s_μ`. -/
@[simp]
theorem coe_schurBasis (n d : ℕ) (h : n ≤ d) (μ : n.Partition) :
    ((schurBasis n d h μ : symmetricHomogeneousSubmodule (Fin d) ℂ n) :
        MvPolynomial (Fin d) ℂ) = schurPoly (Fin d) ℂ μ := by
  rw [schurBasis, Module.Basis.reindex_apply, coe_schurPolyBasis]
  simp

/-- The power-sum product `p_μ` of a partition `μ` of `n`, regarded as an element of the
symmetric homogeneous submodule of degree `n`. -/
@[expose]
noncomputable def psumPartSubmodule (n d : ℕ) (_h : n ≤ d) (μ : n.Partition) :
    symmetricHomogeneousSubmodule (Fin d) ℂ n :=
  ⟨psumPart (Fin d) ℂ μ, mem_symmetricHomogeneousSubmodule.mpr
    ⟨psumPart_isSymmetric ℂ μ, isHomogeneous_psumPart ℂ μ⟩⟩

@[simp]
theorem coe_psumPartSubmodule (n d : ℕ) (h : n ≤ d) (μ : n.Partition) :
    ((psumPartSubmodule n d h μ : symmetricHomogeneousSubmodule (Fin d) ℂ n) :
        MvPolynomial (Fin d) ℂ) = psumPart (Fin d) ℂ μ :=
  rfl

/-- The Hall inner product on the symmetric homogeneous polynomials of degree `n` in `d`
variables, defined by declaring the Schur polynomials orthonormal. -/
noncomputable def hallInner (n d : ℕ) (h : n ≤ d) :
    LinearMap.BilinForm ℂ (symmetricHomogeneousSubmodule (Fin d) ℂ n) :=
  LinearMap.mk₂ ℂ
    (fun p q => ∑ μ : n.Partition,
      (schurBasis n d h).repr p μ * (schurBasis n d h).repr q μ)
    (by
      intro p q r
      rw [map_add]
      simp only [Finsupp.add_apply, add_mul]
      rw [Finset.sum_add_distrib])
    (by
      intro c p q
      rw [map_smul]
      simp only [Finsupp.smul_apply, smul_eq_mul, mul_assoc]
      rw [Finset.mul_sum])
    (by
      intro p q r
      rw [map_add]
      simp only [Finsupp.add_apply, mul_add]
      rw [Finset.sum_add_distrib])
    (by
      intro c p q
      rw [map_smul]
      simp only [Finsupp.smul_apply, smul_eq_mul, mul_left_comm]
      rw [Finset.mul_sum])

/-- The defining formula for the Hall inner product. -/
theorem hallInner_apply (n d : ℕ) (h : n ≤ d)
    (p q : symmetricHomogeneousSubmodule (Fin d) ℂ n) :
    hallInner n d h p q = ∑ μ : n.Partition,
      (schurBasis n d h).repr p μ * (schurBasis n d h).repr q μ :=
  (rfl)

/-- The Schur polynomials are orthonormal for the Hall inner product. -/
@[simp]
theorem hallInner_schurBasis (n d : ℕ) (h : n ≤ d) (μ ν : n.Partition) :
    hallInner n d h (schurBasis n d h μ) (schurBasis n d h ν) =
      if μ = ν then 1 else 0 := by
  rw [hallInner_apply]
  simp only [Module.Basis.repr_self_apply]
  rw [Finset.sum_eq_single μ]
  · simp [eq_comm]
  · intro ν _ hν
    rw [ite_eq_right (Ne.symm hν), zero_mul]
  · intro hμ
    exact absurd (Finset.mem_univ μ) hμ

/-- The Hall inner product is symmetric. -/
theorem hallInner_symm (n d : ℕ) (h : n ≤ d)
    (p q : symmetricHomogeneousSubmodule (Fin d) ℂ n) :
    hallInner n d h p q = hallInner n d h q p := by
  rw [hallInner_apply, hallInner_apply]
  exact Finset.sum_congr rfl fun μ _ => mul_comm _ _

/-- The characters of the complex Specht modules are orthonormal for the character pairing. -/
theorem characterPairing_spechtCharacterBasis (n : ℕ) (μ ν : n.Partition) :
    ClassFunction.characterPairing (spechtCharacterBasis n μ) (spechtCharacterBasis n ν) =
      if μ = ν then 1 else 0 := by
  have h := spechtCharacterBasis_repr (n := n) (spechtCharacterBasis n ν) μ
  rw [Module.Basis.repr_self_apply, spechtCharacterBasis_apply] at h
  rw [spechtCharacterBasis_apply]
  simpa [eq_comm] using h.symm

/-- The Frobenius characteristic sends the Specht character basis to the Schur basis. -/
theorem frobeniusCharacteristic_spechtCharacterBasis (n d : ℕ) (h : n ≤ d)
    (μ : n.Partition) :
    frobeniusCharacteristic n d h (spechtCharacterBasis n μ) = schurBasis n d h μ := by
  apply Subtype.ext
  rw [spechtCharacterBasis_apply, frobeniusCharacteristic_spechtCharacter, coe_schurBasis]

/-- **The Frobenius characteristic is an isometry** for the character pairing and the Hall inner
product. -/
theorem characterPairing_eq_hallInner (n d : ℕ) (h : n ≤ d)
    (f g : ClassFunction ℂ (Equiv.Perm (Fin n))) :
    ClassFunction.characterPairing f g =
      hallInner n d h (frobeniusCharacteristic n d h f)
        (frobeniusCharacteristic n d h g) := by
  have hforms : ClassFunction.characterPairing =
      (hallInner n d h).compl₁₂ (frobeniusCharacteristic n d h).toLinearMap
        (frobeniusCharacteristic n d h).toLinearMap := by
    refine LinearMap.BilinForm.ext_basis (b := spechtCharacterBasis n) ?_
    intro μ ν
    rw [characterPairing_spechtCharacterBasis]
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap]
    simp only [frobeniusCharacteristic_spechtCharacterBasis, hallInner_schurBasis]
  simpa using congrArg (fun B => B f g) hforms

/-- The Schur coordinates of a power-sum product are the corresponding character values. -/
theorem schurBasis_repr_psumPart (n d : ℕ) (h : n ≤ d) (ρ μ : n.Partition) :
    (schurBasis n d h).repr (psumPartSubmodule n d h ρ) μ =
      (spechtCharValue μ ρ : ℂ) := by
  have hsum : psumPartSubmodule n d h ρ =
      ∑ ν : n.Partition, (spechtCharValue ν ρ : ℂ) • schurBasis n d h ν := by
    apply Subtype.ext
    simpa [psumPartSubmodule, coe_schurBasis, Int.cast_smul_eq_zsmul] using
      (psumPart_eq_sum_spechtCharValue_smul_schurPoly (σ := Fin d) (R := ℂ) (n := n) ρ)
  calc
    (schurBasis n d h).repr (psumPartSubmodule n d h ρ) μ
        = (fun ν : n.Partition => (spechtCharValue ν ρ : ℂ)) μ := by
          rw [hsum, Module.Basis.repr_sum_self]
    _ = (spechtCharValue μ ρ : ℂ) := rfl

/-- **The power-sum orthogonality relation** for the Hall inner product:
`⟨p_μ, p_ν⟩ = z_μ δ_{μν}`.  This is the second orthogonality relation for the character table of
`Sₙ`, read through Frobenius's formula. -/
theorem hallInner_psumPart (n d : ℕ) (h : n ≤ d) (ρ τ : n.Partition) :
    hallInner n d h (psumPartSubmodule n d h ρ) (psumPartSubmodule n d h τ) =
      if ρ = τ then (zPart ρ : ℂ) else 0 := by
  rw [hallInner_apply]
  simp_rw [schurBasis_repr_psumPart]
  have horth := congrArg (Int.cast : ℤ → ℂ)
    (symmetricCharacterTable_column_orthogonality (n := n) ρ τ)
  push_cast at horth
  simpa [symmetricCharacterTable_apply] using horth

end TauCeti
