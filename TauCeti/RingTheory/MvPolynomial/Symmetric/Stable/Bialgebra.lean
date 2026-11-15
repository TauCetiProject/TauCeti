/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.Algebra.BigOperators.NatAntidiagonal
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Generators
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Sum

/-!
# The bialgebra of symmetric functions

The ring `Λ_R` of symmetric functions over a commutative ring is the polynomial ring on the
elementary symmetric functions `e₁, e₂, …` (`TauCeti.SymmetricFunction.esymmAlgEquiv`), so an
algebra homomorphism out of `Λ_R` may be prescribed freely on the `e_n`. This file makes `Λ_R` a
cocommutative bialgebra, with the comultiplication `Δ(e_n) = ∑_{i + j = n} e_i ⊗ e_j` and the
counit taking the constant term.

The comultiplication is the restriction of symmetric functions to a disjoint union of two
alphabets: specializing the two tensor factors to the alphabets `Fin d` and `Fin e`, the
coproduct of `x` becomes `x` specialized to `Fin d ⊕ Fin e ≃ Fin (d + e)`. These split
specializations jointly determine an element of `Λ_R ⊗ Λ_R`, so the alphabet-splitting identities
for `h_n` and `p_n` compute their coproducts: `Δ(h_n) = ∑_{i + j = n} h_i ⊗ h_j`, and the power
sums are primitive.

## Main definitions

* `TauCeti.SymmetricFunction.instBialgebra`: the bialgebra structure on `Λ_R`.
* `TauCeti.SymmetricFunction.splitSpecialization R d e`: the specialization of `Λ_R ⊗ Λ_R` to the
  two disjoint alphabets `Fin d` and `Fin e`.

## Main results

* `TauCeti.SymmetricFunction.comul_of_stableEsymm`: `Δ(e_n) = ∑_{i + j = n} e_i ⊗ e_j`.
* `TauCeti.SymmetricFunction.C_counit`, `TauCeti.SymmetricFunction.counit_of_ne_zero`: the counit
  is the specialization to the empty alphabet, and vanishes in positive degree.
* `TauCeti.SymmetricFunction.instIsCocomm`: the comultiplication is cocommutative.
* `TauCeti.SymmetricFunction.splitSpecialization_comul`: the comultiplication splits the alphabet.
* `TauCeti.SymmetricFunction.ext_splitSpecialization`: the split specializations to `Fin d ⊕ Fin d`
  determine an element of `Λ_R ⊗ Λ_R`.
* `TauCeti.SymmetricFunction.comul_of_stableHsymm`: `Δ(h_n) = ∑_{i + j = n} h_i ⊗ h_j`.
* `TauCeti.SymmetricFunction.comul_of_stablePsum`: `Δ(p_n) = p_n ⊗ 1 + 1 ⊗ p_n`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5, Example 25: the comultiplication of `Λ` and the alphabet-splitting description.
* The bialgebra instance is built with `Bialgebra.ofAlgHom`, following the construction of
  `SymmetricAlgebra.instBialgebra` and `SymmetricAlgebra.instIsCocomm` in Mathlib's
  `Mathlib.RingTheory.Bialgebra.SymmetricAlgebra`.
-/

public section

open Finset MvPolynomial TensorProduct

namespace TauCeti

namespace SymmetricFunction

variable (R : Type*) [CommRing R]

/- The comultiplication is the algebra homomorphism prescribed on the free generators by
`e_(r + 1) ↦ ∑_{i + j = r + 1} e_i ⊗ e_j`, and the counit is the specialization to the empty
alphabet, read as a scalar. The two are written out in the statements below, rather than named
by private definitions, because the bialgebra instance must not refer to private declarations. -/

private theorem comul_aux_of_stableEsymm (n : ℕ) :
    ((aeval fun r => ∑ p ∈ antidiagonal (r + 1), DirectSum.of _ p.1 (stableEsymm R p.1) ⊗ₜ[R]
        DirectSum.of _ p.2 (stableEsymm R p.2)).comp (esymmAlgEquiv R).symm.toAlgHom)
      (DirectSum.of _ n (stableEsymm R n)) = ∑ p ∈ antidiagonal n,
        (DirectSum.of _ p.1 (stableEsymm R p.1) : SymmetricFunction R) ⊗ₜ[R]
          (DirectSum.of _ p.2 (stableEsymm R p.2) : SymmetricFunction R) := by
  cases n with
  | zero => simp [Algebra.TensorProduct.one_def]
  | succ r => simp

private theorem C_counit_aux (x : SymmetricFunction R) :
    C (((isEmptyAlgEquiv R (Fin 0)).toAlgHom.comp (specialization R 0)) x) =
      specialization R 0 x := by
  rw [← isEmptyAlgEquiv_symm_apply (R := R) (σ := Fin 0)]
  exact (isEmptyAlgEquiv R (Fin 0)).symm_apply_apply _

private theorem counit_aux_of_ne_zero {n : ℕ} (hn : n ≠ 0) (f : stableSymmetricSubmodule R n) :
    ((isEmptyAlgEquiv R (Fin 0)).toAlgHom.comp (specialization R 0)) (DirectSum.of _ n f) = 0 := by
  refine C_injective (Fin 0) R ?_
  rw [C_counit_aux, specialization_of, C_0,
    eq_C_of_isEmpty (p := (stableSymmetricProj R n 0 f : MvPolynomial (Fin 0) R)),
    (mem_symmetricHomogeneousSubmodule.mp (stableSymmetricProj R n 0 f).2).2.coeff_eq_zero
      (by simpa using hn.symm), C_0]

private theorem counit_aux_of_stableEsymm (n : ℕ) :
    ((isEmptyAlgEquiv R (Fin 0)).toAlgHom.comp (specialization R 0))
      (DirectSum.of _ n (stableEsymm R n)) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn
    rw [stableEsymm_zero, of_stableSymmetricOne, map_one]
  · exact counit_aux_of_ne_zero R hn _

section Laws

variable {R} {Δ : SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R}
  {ε : SymmetricFunction R →ₐ[R] R}

/-- A comultiplication with `Δ(e_n) = ∑_{i + j = n} e_i ⊗ e_j` is coassociative. -/
private theorem coassoc_of_comul_stableEsymm
    (hΔ : ∀ n, Δ (DirectSum.of _ n (stableEsymm R n)) = ∑ p ∈ antidiagonal n,
      (DirectSum.of _ p.1 (stableEsymm R p.1) : SymmetricFunction R) ⊗ₜ[R]
        (DirectSum.of _ p.2 (stableEsymm R p.2) : SymmetricFunction R)) :
    (Algebra.TensorProduct.assoc R R R _ _ _).toAlgHom.comp
        ((Algebra.TensorProduct.map Δ (.id R _)).comp Δ) =
      (Algebra.TensorProduct.map (.id R _) Δ).comp Δ := by
  refine algHom_ext fun n => ?_
  simp only [AlgHom.comp_apply, hΔ, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    sum_tmul, tmul_sum, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.assoc_tmul]
  exact Finset.Nat.sum_antidiagonal_sum_antidiagonal_fst _ fun a b c =>
    (DirectSum.of _ a (stableEsymm R a) : SymmetricFunction R) ⊗ₜ[R]
      ((DirectSum.of _ b (stableEsymm R b) : SymmetricFunction R) ⊗ₜ[R]
        (DirectSum.of _ c (stableEsymm R c) : SymmetricFunction R))

/-- The left counit law for `Δ(e_n) = ∑_{i + j = n} e_i ⊗ e_j` and `ε(e_n) = δ_{n0}`. -/
private theorem rTensor_counit_comp_comul_of_stableEsymm
    (hΔ : ∀ n, Δ (DirectSum.of _ n (stableEsymm R n)) = ∑ p ∈ antidiagonal n,
      (DirectSum.of _ p.1 (stableEsymm R p.1) : SymmetricFunction R) ⊗ₜ[R]
        (DirectSum.of _ p.2 (stableEsymm R p.2) : SymmetricFunction R))
    (hε : ∀ n, ε (DirectSum.of _ n (stableEsymm R n)) = if n = 0 then 1 else 0) :
    (Algebra.TensorProduct.map ε (.id R _)).comp Δ =
      (Algebra.TensorProduct.lid R (SymmetricFunction R)).symm :=
  algHom_ext fun n => by
    simp [hΔ, hε, Finset.Nat.sum_antidiagonal_succ]

/-- The right counit law for `Δ(e_n) = ∑_{i + j = n} e_i ⊗ e_j` and `ε(e_n) = δ_{n0}`. -/
private theorem lTensor_counit_comp_comul_of_stableEsymm
    (hΔ : ∀ n, Δ (DirectSum.of _ n (stableEsymm R n)) = ∑ p ∈ antidiagonal n,
      (DirectSum.of _ p.1 (stableEsymm R p.1) : SymmetricFunction R) ⊗ₜ[R]
        (DirectSum.of _ p.2 (stableEsymm R p.2) : SymmetricFunction R))
    (hε : ∀ n, ε (DirectSum.of _ n (stableEsymm R n)) = if n = 0 then 1 else 0) :
    (Algebra.TensorProduct.map (.id R _) ε).comp Δ =
      (Algebra.TensorProduct.rid R R (SymmetricFunction R)).symm :=
  algHom_ext fun n => by
    simp [hΔ, hε, Finset.Nat.sum_antidiagonal_succ']

end Laws

/-- **The bialgebra of symmetric functions**: the comultiplication sends the elementary symmetric
function `e_n` to `∑_{i + j = n} e_i ⊗ e_j`, and the counit takes the constant term. -/
noncomputable instance instBialgebra : Bialgebra R (SymmetricFunction R) :=
  .ofAlgHom
    ((aeval fun r => ∑ p ∈ antidiagonal (r + 1), DirectSum.of _ p.1 (stableEsymm R p.1) ⊗ₜ[R]
        DirectSum.of _ p.2 (stableEsymm R p.2)).comp (esymmAlgEquiv R).symm.toAlgHom)
    ((isEmptyAlgEquiv R (Fin 0)).toAlgHom.comp (specialization R 0))
    (by exact coassoc_of_comul_stableEsymm (comul_aux_of_stableEsymm R))
    (by
      exact rTensor_counit_comp_comul_of_stableEsymm (comul_aux_of_stableEsymm R)
        (counit_aux_of_stableEsymm R))
    (by
      exact lTensor_counit_comp_comul_of_stableEsymm (comul_aux_of_stableEsymm R)
        (counit_aux_of_stableEsymm R))

/-- **The coproduct of an elementary symmetric function**: `Δ(e_n) = ∑_{i + j = n} e_i ⊗ e_j`. -/
@[simp]
theorem comul_of_stableEsymm (n : ℕ) :
    Coalgebra.comul (R := R) (A := SymmetricFunction R) (DirectSum.of _ n (stableEsymm R n)) =
      ∑ p ∈ antidiagonal n,
        (DirectSum.of _ p.1 (stableEsymm R p.1) : SymmetricFunction R) ⊗ₜ[R]
          (DirectSum.of _ p.2 (stableEsymm R p.2) : SymmetricFunction R) :=
  comul_aux_of_stableEsymm R n

/-- **The counit is the specialization to the empty alphabet**: as a constant polynomial in no
variables, the counit of `x` is `x` specialized to `Fin 0`. -/
theorem C_counit (x : SymmetricFunction R) :
    C (Coalgebra.counit (R := R) x) = specialization R 0 x :=
  C_counit_aux R x

/-- **The counit vanishes in positive degree.** -/
@[simp]
theorem counit_of_ne_zero {n : ℕ} (hn : n ≠ 0) (f : stableSymmetricSubmodule R n) :
    Coalgebra.counit (R := R) (A := SymmetricFunction R) (DirectSum.of _ n f) = 0 :=
  counit_aux_of_ne_zero R hn f

/-- **The comultiplication of the symmetric functions is cocommutative.** -/
instance instIsCocomm : Coalgebra.IsCocomm R (SymmetricFunction R) where
  comm_comp_comul := by
    have h : (Algebra.TensorProduct.comm R (SymmetricFunction R)
        (SymmetricFunction R)).toAlgHom.comp (Bialgebra.comulAlgHom R _) =
        Bialgebra.comulAlgHom R (SymmetricFunction R) :=
      algHom_ext fun n => by
        simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, comul_of_stableEsymm, map_sum]
        exact Finset.Nat.sum_antidiagonal_swap.symm.trans (by simp)
    congrm ($h).toLinearMap

/-- **The specialization of `Λ_R ⊗ Λ_R` to two disjoint alphabets**: the first tensor factor is
specialized to the alphabet `Fin d` and the second to `Fin e`, both read in the polynomials on
`Fin d ⊕ Fin e`. -/
noncomputable def splitSpecialization (d e : ℕ) :
    SymmetricFunction R ⊗[R] SymmetricFunction R →ₐ[R] MvPolynomial (Fin d ⊕ Fin e) R :=
  Algebra.TensorProduct.productMap ((rename Sum.inl).comp (specialization R d))
    ((rename Sum.inr).comp (specialization R e))

/-- The split specialization of a pure tensor `x ⊗ y` is the product of `x` in the first alphabet
and `y` in the second. -/
@[simp]
theorem splitSpecialization_tmul (d e : ℕ) (x y : SymmetricFunction R) :
    splitSpecialization R d e (x ⊗ₜ y) =
      rename Sum.inl (specialization R d x) * rename Sum.inr (specialization R e y) := by
  simp [splitSpecialization]

/-- **The comultiplication splits the alphabet**: specializing the two tensor factors of `Δ(x)` to
the alphabets `Fin d` and `Fin e` gives `x` specialized to the alphabet `Fin d ⊕ Fin e`, identified
with `Fin (d + e)`. -/
theorem splitSpecialization_comul (d e : ℕ) (x : SymmetricFunction R) :
    splitSpecialization R d e (Coalgebra.comul x) =
      rename finSumFinEquiv.symm (specialization R (d + e) x) := by
  have h : (splitSpecialization R d e).comp (Bialgebra.comulAlgHom R _) =
      (rename finSumFinEquiv.symm).comp (specialization R (d + e)) :=
    algHom_ext fun n => by simp [rename_esymm, esymm_sum_type]
  exact DFunLike.congr_fun h x

/-- The polynomials in the elementary symmetric functions of the two tensor factors, as
polynomials in the variables `ℕ ⊕ ℕ`. -/
private noncomputable def esymmTensorEquiv :
    MvPolynomial (ℕ ⊕ ℕ) R ≃ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R :=
  (tensorEquivSum R ℕ ℕ R).symm.trans
    (Algebra.TensorProduct.congr (esymmAlgEquiv R) (esymmAlgEquiv R))

/-- The split specialization to `Fin d ⊕ Fin d`, read on polynomials in the elementary symmetric
functions of the two tensor factors, substitutes the elementary symmetric polynomials of the two
alphabets. -/
private theorem splitSpecialization_comp_esymmTensorEquiv (d : ℕ) :
    (splitSpecialization R d d).comp (esymmTensorEquiv R).toAlgHom =
      aeval (Sum.elim (fun r : ℕ => rename Sum.inl (esymm (Fin d) R (r + 1)))
        (fun r : ℕ => rename Sum.inr (esymm (Fin d) R (r + 1)))) := by
  refine MvPolynomial.algHom_ext fun k => ?_
  cases k with
  | inl r =>
    have hX : (tensorEquivSum R ℕ ℕ R).symm (X (Sum.inl r)) = X r ⊗ₜ 1 := by
      rw [AlgEquiv.symm_apply_eq, tensorEquivSum_X_tmul_one]
    simp [esymmTensorEquiv, hX]
  | inr r =>
    have hX : (tensorEquivSum R ℕ ℕ R).symm (X (Sum.inr r)) = 1 ⊗ₜ X r := by
      rw [AlgEquiv.symm_apply_eq, tensorEquivSum_one_tmul_X]
    simp [esymmTensorEquiv, hX]

/-- **The split specializations determine an element of `Λ_R ⊗ Λ_R`**: two elements agreeing on
the alphabets `Fin d ⊕ Fin d` for every `d` are equal. -/
theorem ext_splitSpecialization {x y : SymmetricFunction R ⊗[R] SymmetricFunction R}
    (h : ∀ d, splitSpecialization R d d x = splitSpecialization R d d y) : x = y := by
  obtain ⟨q, hq⟩ := (esymmTensorEquiv R).surjective (x - y)
  rw [← sub_eq_zero, ← hq]
  -- every variable of `q` lies in `Fin N ⊕ Fin N`, for `N` past all of them
  obtain ⟨N, hN⟩ : ∃ N, ∀ k ∈ q.vars,
      k ∈ Set.range (Sum.map (Fin.val : Fin N → ℕ) (Fin.val : Fin N → ℕ)) :=
    ⟨q.vars.sup (Sum.elim id id) + 1, fun k hk => by
      have hle := Finset.le_sup (f := Sum.elim id id) hk
      cases k with
      | inl r => exact ⟨Sum.inl ⟨r, Nat.lt_succ_of_le hle⟩, rfl⟩
      | inr r => exact ⟨Sum.inr ⟨r, Nat.lt_succ_of_le hle⟩, rfl⟩⟩
  obtain ⟨q', rfl⟩ := exists_rename_eq_of_vars_subset_range q _
    (Sum.map_injective.mpr ⟨Fin.val_injective, Fin.val_injective⟩) hN
  have hN := congr($(splitSpecialization_comp_esymmTensorEquiv R N)
    (rename (Sum.map (Fin.val : Fin N → ℕ) (Fin.val : Fin N → ℕ)) q'))
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hq, map_sub, h N, sub_self, aeval_rename,
    Sum.elim_comp_map] at hN
  rw [(injective_iff_map_eq_zero _).mp
    (algebraicIndependent_iff_injective_aeval.mp
      (algebraicIndependent_esymm_sum_type R (by simp) (by simp))) q'
    hN.symm, map_zero, map_zero]

/-- **The coproduct of a complete homogeneous symmetric function**:
`Δ(h_n) = ∑_{i + j = n} h_i ⊗ h_j`. -/
@[simp]
theorem comul_of_stableHsymm (n : ℕ) :
    Coalgebra.comul (R := R) (A := SymmetricFunction R) (DirectSum.of _ n (stableHsymm R n)) =
      ∑ p ∈ antidiagonal n,
        (DirectSum.of _ p.1 (stableHsymm R p.1) : SymmetricFunction R) ⊗ₜ[R]
          (DirectSum.of _ p.2 (stableHsymm R p.2) : SymmetricFunction R) :=
  ext_splitSpecialization R fun d => by
    simp [splitSpecialization_comul, rename_hsymm, hsymm_sum_type]

/-- **The power sums are primitive**: `Δ(p_n) = p_n ⊗ 1 + 1 ⊗ p_n` for `n ≠ 0`. -/
@[simp]
theorem comul_of_stablePsum {n : ℕ} (hn : n ≠ 0) :
    Coalgebra.comul (R := R) (A := SymmetricFunction R) (DirectSum.of _ n (stablePsum R hn)) =
      DirectSum.of _ n (stablePsum R hn) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] DirectSum.of _ n (stablePsum R hn) :=
  ext_splitSpecialization R fun d => by
    simp [splitSpecialization_comul, rename_psum, psum_sum_type]

end SymmetricFunction

end TauCeti
