/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Basis
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basis
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.HsymmPart

/-!
# The Hall inner product

The **Hall inner product** is the symmetric bilinear form on the symmetric polynomials of degree
`n` for which the Schur polynomials are orthonormal.  Macdonald introduces it instead as the form
for which the complete homogeneous products `h_μ` and the monomial symmetric polynomials `m_ν` are
dual bases, `⟨h_μ, m_ν⟩ = δ_{μν}`, and deduces the orthonormality of the Schur functions from the
Cauchy identity.  Here the logic runs the other way: the form is defined by the Schur basis, and
the duality of `h` and `m` is a theorem.  It follows from the two Kostka expansions
`h_ν = ∑_λ K_{λν} s_λ` and `s_λ = ∑_ν K_{λν} m_ν`: pairing with `h_ν` reads off the coefficient
of the sorted monomial `x^ν` (`TauCeti.hallInner_hsymmPart_left`).

The form lives on `TauCeti.symmetricHomogeneousSubmodule σ R n` for a finite alphabet `σ` and a
commutative ring `R`, the module of which the Schur polynomials of the partitions of `n` with at
most `Fintype.card σ` parts are a basis (`TauCeti.schurPolyBasis`).  When `σ` has at least `n`
letters this module is the degree-`n` part of the ring of symmetric functions, and the form is the
classical one; with fewer letters it is the form induced on the quotient in which the Schur
functions of the longer partitions vanish.

The power-sum orthogonality `⟨p_ρ, p_ρ'⟩ = z_ρ δ_{ρρ'}` and the isometry of the Frobenius
characteristic need the character table of the symmetric group, and are proved in
`TauCeti/RepresentationTheory/Symmetric/FrobeniusCharacteristic.lean`.

## Main definitions

* `TauCeti.hallInner`: the Hall inner product on the symmetric polynomials of degree `n`.

## Main results

* `TauCeti.hallInner_schurPoly`: the Schur polynomials are orthonormal.
* `TauCeti.hallInner_apply`: the form is the dot product of Schur coordinates.
* `TauCeti.isSymm_hallInner` and `TauCeti.nondegenerate_hallInner`: it is symmetric and
  nondegenerate.
* `TauCeti.hallInner_hsymmPart_left`: pairing with `h_ν` reads off the coefficient of `x^ν`.
* `TauCeti.hallInner_hsymmPart_msymm`: **the `h_μ` and the `m_ν` are dual bases**.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 4, (4.5)–(4.8).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Section 7.9.
-/

public section

namespace TauCeti

open MvPolynomial Finset

/-! ### Products of complete homogeneous symmetric polynomials -/

section CommSemiring

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommSemiring R] {n : ℕ}

/-- **A product of complete homogeneous symmetric polynomials is symmetric and homogeneous**: `h_ν`
is homogeneous of degree `n` for a partition `ν` of `n`.  It is a combination of Schur
polynomials of degree `n` (`TauCeti.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly`). -/
theorem hsymmPart_mem_symmetricHomogeneousSubmodule (ν : n.Partition) :
    hsymmPart σ R ν ∈ symmetricHomogeneousSubmodule σ R n := by
  rw [hsymmPart_eq_sum_kostkaNumber_smul_schurPoly]
  exact Submodule.sum_mem _ fun μ _ =>
    Submodule.smul_mem _ _ (schurPoly_mem_symmetricHomogeneousSubmodule μ)

end CommSemiring

/-! ### The Hall inner product -/

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R] {n : ℕ}

variable (σ R n) in
/-- **The Hall inner product** on the symmetric polynomials of degree `n` in the alphabet `σ`: the
bilinear form in which the Schur polynomials of the partitions of `n` with at most `Fintype.card σ`
parts are orthonormal (`TauCeti.hallInner_schurPoly`).  It is the dot product of the coordinates
in the Schur basis (`TauCeti.hallInner_apply`), and the complete homogeneous products `h_μ` and
the monomial symmetric polynomials `m_ν` are dual bases for it
(`TauCeti.hallInner_hsymmPart_msymm`). -/
noncomputable def hallInner : LinearMap.BilinForm R (symmetricHomogeneousSubmodule σ R n) :=
  (schurPolyBasis σ R n).toDual

/-- **The Schur basis is orthonormal for the Hall inner product.**  It is not a `simp` lemma:
`TauCeti.hallInner_schurPolyBasis_right` already reduces the left side to a Schur coordinate. -/
theorem hallInner_schurPolyBasis (μ ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    hallInner σ R n (schurPolyBasis σ R n μ) (schurPolyBasis σ R n ν) = if μ = ν then 1 else 0 :=
  Module.Basis.toDual_apply _ μ ν

/-- **Pairing with a Schur polynomial on the right reads off the Schur coordinate.** -/
@[simp]
theorem hallInner_schurPolyBasis_right (p : symmetricHomogeneousSubmodule σ R n)
    (μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    hallInner σ R n p (schurPolyBasis σ R n μ) = (schurPolyBasis σ R n).repr p μ :=
  Module.Basis.toDual_apply_left _ p μ

/-- **Pairing with a Schur polynomial on the left reads off the Schur coordinate.** -/
@[simp]
theorem hallInner_schurPolyBasis_left (μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ})
    (p : symmetricHomogeneousSubmodule σ R n) :
    hallInner σ R n (schurPolyBasis σ R n μ) p = (schurPolyBasis σ R n).repr p μ :=
  Module.Basis.toDual_apply_right _ μ p

/-- **The Hall inner product is the dot product of Schur coordinates.** -/
theorem hallInner_apply (p q : symmetricHomogeneousSubmodule σ R n) :
    hallInner σ R n p q =
      ∑ μ, (schurPolyBasis σ R n).repr p μ * (schurPolyBasis σ R n).repr q μ := by
  conv_lhs => rw [← (schurPolyBasis σ R n).sum_repr q]
  simp only [map_sum, map_smul, hallInner_schurPolyBasis_right, smul_eq_mul, mul_comm]

/-- **The Hall inner product is symmetric.** -/
theorem hallInner_comm (p q : symmetricHomogeneousSubmodule σ R n) :
    hallInner σ R n p q = hallInner σ R n q p := by
  simp only [hallInner_apply, mul_comm]

/-- **The Hall inner product is a symmetric bilinear form.** -/
theorem isSymm_hallInner : (hallInner σ R n).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr hallInner_comm

/-- **The Hall inner product is nondegenerate**: a symmetric polynomial orthogonal to every Schur
polynomial has all its Schur coordinates `0`. -/
theorem nondegenerate_hallInner : (hallInner σ R n).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (hallInner σ R n) := fun p hp =>
    (schurPolyBasis σ R n).ext_elem fun μ => by
      rw [← hallInner_schurPolyBasis_right, hp, map_zero, Finsupp.zero_apply]
  exact ⟨hl, fun q hq => hl q fun p => by rw [hallInner_comm]; exact hq p⟩

/-- **The Schur polynomials are orthonormal for the Hall inner product**, stated for partitions:
`⟨s_λ, s_μ⟩ = δ_{λμ}` whenever `μ` has at most `Fintype.card σ` parts.  No bound on `λ` is needed:
the Schur polynomial of a longer partition is `0`, and that partition differs from `μ`. -/
theorem hallInner_schurPoly (l μ : n.Partition) (hμ : μ.parts.card ≤ Fintype.card σ) :
    hallInner σ R n ⟨schurPoly σ R l, schurPoly_mem_symmetricHomogeneousSubmodule l⟩
        ⟨schurPoly σ R μ, schurPoly_mem_symmetricHomogeneousSubmodule μ⟩ =
      if l = μ then 1 else 0 := by
  have hs : (⟨schurPoly σ R μ, schurPoly_mem_symmetricHomogeneousSubmodule μ⟩ :
      symmetricHomogeneousSubmodule σ R n) = schurPolyBasis σ R n ⟨μ, hμ⟩ :=
    Subtype.ext (coe_schurPolyBasis (σ := σ) (R := R) ⟨μ, hμ⟩).symm
  classical
  rw [hs, hallInner_schurPolyBasis_right]
  refine schurPolyBasis_repr_of_coe_eq_sum (c := fun ν => if ν = l then 1 else 0) ?_ ⟨μ, hμ⟩
    |>.trans (if_congr eq_comm rfl rfl)
  simp

/-! ### The complete homogeneous and monomial bases are dual -/

variable [DecidableEq σ]

/-- **Pairing with `h_ν` reads off the coefficient of `x^ν`**: for a partition `ν` with at most
`Fintype.card σ` parts, the Hall inner product of `h_ν` with a symmetric polynomial of degree `n`
is its coefficient at the sorted monomial `x^ν` recording the parts of `ν`, which is its
coordinate in the monomial basis (`TauCeti.msymmBasis_repr_apply`).  On a Schur polynomial `s_μ`
both sides are the Kostka number `K_{μν}`: the left by the expansion of `h_ν` in Schur polynomials,
the right by the monomial expansion of `s_μ`. -/
theorem hallInner_hsymmPart_left (ν : n.Partition) (hν : ν.parts.card ≤ Fintype.card σ)
    (p : symmetricHomogeneousSubmodule σ R n) :
    hallInner σ R n ⟨hsymmPart σ R ν, hsymmPart_mem_symmetricHomogeneousSubmodule ν⟩ p =
      (p : MvPolynomial σ R).coeff (partWeight σ ν) := by
  rw [← msymmBasis_repr_apply p ⟨ν, hν⟩, ← Module.Basis.coord_apply]
  congr 1
  refine (schurPolyBasis σ R n).ext fun μ => ?_
  rw [hallInner_schurPolyBasis_right, Module.Basis.coord_apply,
    schurPolyBasis_repr_of_coe_eq_sum (hsymmPart_eq_sum_kostkaNumber_smul_schurPoly σ ν),
    ← msymmBasis_repr_schurPoly μ.1 ⟨ν, hν⟩]
  congr 2
  exact Subtype.ext (coe_schurPolyBasis μ).symm

/-- **The complete homogeneous products and the monomial symmetric polynomials are dual bases for
the Hall inner product**: `⟨h_μ, m_ν⟩ = δ_{μν}` for partitions `μ` and `ν` of `n`, `μ` having at
most `Fintype.card σ` parts.  This is Macdonald's definition of the Hall inner product.  No bound on
`ν` is needed: the monomial symmetric polynomial of a longer partition is `0`, and that partition
differs from `μ`. -/
theorem hallInner_hsymmPart_msymm (μ ν : n.Partition) (hμ : μ.parts.card ≤ Fintype.card σ) :
    hallInner σ R n ⟨hsymmPart σ R μ, hsymmPart_mem_symmetricHomogeneousSubmodule μ⟩
        ⟨msymm σ R ν, msymm_mem_symmetricHomogeneousSubmodule ν⟩ =
      if μ = ν then 1 else 0 := by
  rw [hallInner_hsymmPart_left μ hμ]
  exact coeff_msymm_partWeight R ν μ hμ

end TauCeti
