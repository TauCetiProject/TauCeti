/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Stability

/-!
# The symmetric functions of a fixed degree

A symmetric function of degree `n` over a commutative ring `R` is a symmetric polynomial of degree
`n` "in infinitely many variables". This file realizes it as a **compatible family**: one symmetric
polynomial `f_d` of degree `n` in each finite alphabet `Fin d`, such that setting the last of
`d + 1` variables to zero turns `f_{d+1}` into `f_d`. These families form the `R`-submodule
`TauCeti.stableSymmetricSubmodule R n` of the product of the degree-`n` pieces
`TauCeti.symmetricHomogeneousSubmodule (Fin d) R n`; the degree-`n` piece of the ring of
symmetric functions `Λ_R` is this module.

The point of the construction is that it loses nothing and adds nothing once the alphabet is large
enough. The Schur polynomials are stable under setting a variable to zero
(`TauCeti.aeval_snoc_zero_diagramSchurPoly`), so each partition `μ` of `n` gives a compatible family
`TauCeti.stableSchur R μ`, the **Schur function** `s_μ`. In `d ≥ n` variables the Schur polynomials
of *all* partitions of `n` are a basis of the symmetric polynomials of degree `n`, so setting a
variable to zero is injective on them as long as `d ≥ n`
(`TauCeti.injOn_aeval_snoc_zero_symmetricHomogeneousSubmodule`). Consequently a compatible family
is determined by its member in any alphabet with at least `n` letters, and every symmetric
polynomial of degree `n` in any alphabet is such a member:

* `TauCeti.stableSymmetricProjEquiv`: for `n ≤ d`, projecting to the alphabet `Fin d` is a linear
  equivalence from the degree-`n` symmetric functions onto the symmetric polynomials of degree `n`
  in `d` variables;
* `TauCeti.stableSchurBasis`: the Schur functions `s_μ`, for **all** partitions `μ` of `n`, are an
  `R`-basis of the degree-`n` symmetric functions. Its coordinates are the Schur coordinates of
  any projection to `d ≥ n` variables (`TauCeti.stableSchurBasis_repr_apply`).

Below degree, projection stays surjective (`TauCeti.stableSymmetricProj_surjective`) but is not
injective: the Schur function `s_((1,1))` vanishes in one variable.

## Main definitions

* `TauCeti.stableSymmetricSubmodule R n`: the compatible families of degree-`n` symmetric
  polynomials, that is, the symmetric functions of degree `n`.
* `TauCeti.stableSymmetricProj R n d`: the projection to the alphabet `Fin d`.
* `TauCeti.stableSchur R μ`: the Schur function of a partition `μ`.
* `TauCeti.stableSymmetricProjEquiv R h`: the projection as a linear equivalence for `n ≤ d`.
* `TauCeti.stableSchurBasis R n`: the Schur basis of the symmetric functions of degree `n`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2: the ring `Λ` as the inverse limit of the rings of symmetric polynomials in finitely
  many variables, and the restriction `Λⁿ → Λⁿ_d` being an isomorphism for `d ≥ n`; Section 3:
  the Schur functions are a basis of `Λⁿ`.
-/

public section

namespace TauCeti

open MvPolynomial

section CommSemiring

variable (R : Type*) [CommSemiring R] (n : ℕ)

/-- **The symmetric functions of degree `n`**: the families `(f_d)_d` of symmetric polynomials of
degree `n`, one in each finite alphabet `Fin d`, that are compatible under setting the last
variable to zero, `f_{d+1}(x₀, …, x_{d-1}, 0) = f_d(x₀, …, x_{d-1})`. -/
noncomputable def stableSymmetricSubmodule :
    Submodule R (∀ d : ℕ, symmetricHomogeneousSubmodule (Fin d) R n) where
  carrier := {f | ∀ d, aeval (Fin.snoc (X : Fin d → MvPolynomial (Fin d) R) 0)
    (f (d + 1) : MvPolynomial (Fin (d + 1)) R) = f d}
  add_mem' {f g} hf hg d := by
    simp only [Pi.add_apply, Submodule.coe_add, map_add, hf d, hg d]
  zero_mem' d := by simp
  smul_mem' c f hf d := by
    simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, hf d]

variable {R n}

/-- A family of symmetric polynomials of degree `n` is a symmetric function exactly when setting
the last variable to zero turns each member into the previous one. -/
theorem mem_stableSymmetricSubmodule {f : ∀ d : ℕ, symmetricHomogeneousSubmodule (Fin d) R n} :
    f ∈ stableSymmetricSubmodule R n ↔ ∀ d, aeval (Fin.snoc (X : Fin d → MvPolynomial (Fin d) R) 0)
      (f (d + 1) : MvPolynomial (Fin (d + 1)) R) = f d :=
  Iff.rfl

variable (R n) in
/-- The projection of the symmetric functions of degree `n` to the symmetric polynomials of degree
`n` in the alphabet `Fin d`: the member of a compatible family in `d` variables. -/
noncomputable def stableSymmetricProj (d : ℕ) :
    stableSymmetricSubmodule R n →ₗ[R] symmetricHomogeneousSubmodule (Fin d) R n :=
  (LinearMap.proj d).comp (stableSymmetricSubmodule R n).subtype

/-- The projection to `d` variables reads off the member of the family in `d` variables. -/
theorem stableSymmetricProj_apply (d : ℕ) (f : stableSymmetricSubmodule R n) :
    stableSymmetricProj R n d f = (f : ∀ d : ℕ, symmetricHomogeneousSubmodule (Fin d) R n) d :=
  (rfl)

/-- Setting the last variable to zero in the projection to `d + 1` variables gives the projection
to `d` variables. -/
@[simp]
theorem aeval_snoc_zero_stableSymmetricProj (d : ℕ) (f : stableSymmetricSubmodule R n) :
    aeval (Fin.snoc (X : Fin d → MvPolynomial (Fin d) R) 0)
        (stableSymmetricProj R n (d + 1) f : MvPolynomial (Fin (d + 1)) R) =
      stableSymmetricProj R n d f :=
  f.2 d

/-- Two symmetric functions are equal when all their projections to finite alphabets are. -/
theorem stableSymmetricSubmodule_ext {f g : stableSymmetricSubmodule R n}
    (h : ∀ d, stableSymmetricProj R n d f = stableSymmetricProj R n d g) : f = g :=
  Subtype.ext (funext h)

/-- If a symmetric function projects to zero in `d` variables, it projects to zero in every
smaller alphabet. -/
theorem stableSymmetricProj_eq_zero_of_le {f : stableSymmetricSubmodule R n} {d e : ℕ}
    (hed : e ≤ d) (hf : stableSymmetricProj R n d f = 0) : stableSymmetricProj R n e f = 0 := by
  induction d, hed using Nat.le_induction with
  | base => exact hf
  | succ d _ ih =>
    refine ih (Subtype.ext ?_)
    rw [← aeval_snoc_zero_stableSymmetricProj, hf, Submodule.coe_zero, map_zero,
      Submodule.coe_zero]

variable (R) in
/-- **The Schur function** `s_μ` of a partition `μ` of `n`: the compatible family of the Schur
polynomials of `μ` in all finite alphabets. -/
noncomputable def stableSchur (μ : n.Partition) : stableSymmetricSubmodule R n :=
  ⟨fun d => ⟨schurPoly (Fin d) R μ, schurPoly_mem_symmetricHomogeneousSubmodule μ⟩,
    fun d => aeval_snoc_zero_schurPoly d μ⟩

/-- The projection of a Schur function to `d` variables is the Schur polynomial in `d` variables.
-/
@[simp]
theorem coe_stableSymmetricProj_stableSchur (d : ℕ) (μ : n.Partition) :
    (stableSymmetricProj R n d (stableSchur R μ) : MvPolynomial (Fin d) R) =
      schurPoly (Fin d) R μ :=
  (rfl)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **A symmetric function of degree `n` is determined by its projection to any alphabet with at
least `n` letters.** -/
theorem stableSymmetricProj_injective {d : ℕ} (hn : n ≤ d) :
    Function.Injective (stableSymmetricProj R n d) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => stableSymmetricSubmodule_ext fun e => ?_
  rw [map_zero]
  rcases le_total e d with hed | hde
  · exact stableSymmetricProj_eq_zero_of_le hed hf
  · induction e, hde using Nat.le_induction with
    | base => exact hf
    | succ e hde ih =>
      refine Subtype.ext (injOn_aeval_snoc_zero_symmetricHomogeneousSubmodule (hn.trans hde)
        (Subtype.prop _) (Submodule.zero_mem _) ?_)
      rw [aeval_snoc_zero_stableSymmetricProj, ih, Submodule.coe_zero, Submodule.coe_zero,
        map_zero]

/-- **Every symmetric polynomial of degree `n` in finitely many variables is the projection of a
symmetric function of degree `n`**, in any alphabet, even one with fewer than `n` letters. Its
Schur basis consists of projections of Schur functions. -/
theorem stableSymmetricProj_surjective (d : ℕ) :
    Function.Surjective (stableSymmetricProj R n d) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (schurPolyBasis (Fin d) R n).span_eq,
    Submodule.span_le]
  rintro _ ⟨μ, rfl⟩
  exact ⟨stableSchur R μ.1, Subtype.ext (by simp)⟩

variable (R) in
/-- **The symmetric functions of degree `n` are the symmetric polynomials of degree `n` in any
alphabet with at least `n` letters**: for `n ≤ d`, projection to `Fin d` is a linear
equivalence. -/
noncomputable def stableSymmetricProjEquiv {d : ℕ} (hn : n ≤ d) :
    stableSymmetricSubmodule R n ≃ₗ[R] symmetricHomogeneousSubmodule (Fin d) R n :=
  .ofBijective (stableSymmetricProj R n d)
    ⟨stableSymmetricProj_injective hn, stableSymmetricProj_surjective d⟩

@[simp]
theorem stableSymmetricProjEquiv_apply {d : ℕ} (hn : n ≤ d) (f : stableSymmetricSubmodule R n) :
    stableSymmetricProjEquiv R hn f = stableSymmetricProj R n d f :=
  (rfl)

variable (R n) in
/-- **The Schur basis of the symmetric functions of degree `n`**: the Schur functions `s_μ`, for
all partitions `μ` of `n`, are an `R`-basis. The basis vectors are read off by
`TauCeti.stableSchurBasis_apply`. -/
noncomputable def stableSchurBasis :
    Module.Basis n.Partition R (stableSymmetricSubmodule R n) :=
  ((schurPolyBasis (Fin n) R n).reindex
      (partitionEquivSchurIndex (Fin n) n (by simp)).symm).map
    (stableSymmetricProjEquiv R le_rfl).symm

/-- **The vectors of the Schur basis are the Schur functions.** -/
@[simp]
theorem stableSchurBasis_apply (μ : n.Partition) : stableSchurBasis R n μ = stableSchur R μ := by
  refine (stableSymmetricProjEquiv R le_rfl).injective (Subtype.ext ?_)
  simp [stableSchurBasis]

/-- **The Schur coordinates of a symmetric function are the Schur coordinates of any of its
projections to an alphabet with at least `n` letters.** -/
theorem stableSchurBasis_repr_apply {d : ℕ} (hn : n ≤ d) (f : stableSymmetricSubmodule R n)
    (μ : n.Partition) :
    (stableSchurBasis R n).repr f μ =
      (schurPolyBasis (Fin d) R n).repr (stableSymmetricProj R n d f)
        (partitionEquivSchurIndex (Fin d) n (by simpa using hn) μ) := by
  have hb : (stableSchurBasis R n).map (stableSymmetricProjEquiv R hn) =
      (schurPolyBasis (Fin d) R n).reindex
        (partitionEquivSchurIndex (Fin d) n (by simpa using hn)).symm := by
    refine Module.Basis.eq_of_apply_eq fun μ => Subtype.ext ?_
    simp
  have := congrArg (fun b : Module.Basis _ _ _ => b.repr (stableSymmetricProjEquiv R hn f) μ) hb
  simp only [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Module.Basis.repr_reindex_apply, Equiv.symm_symm] at this
  exact this

instance : Module.Free R (stableSymmetricSubmodule R n) :=
  .of_basis (stableSchurBasis R n)

instance : Module.Finite R (stableSymmetricSubmodule R n) :=
  .of_basis (stableSchurBasis R n)

/-- **The dimension of the symmetric functions of degree `n` is the number of partitions of `n`.**
-/
theorem finrank_stableSymmetricSubmodule [Nontrivial R] :
    Module.finrank R (stableSymmetricSubmodule R n) = Fintype.card n.Partition :=
  Module.finrank_eq_card_basis (stableSchurBasis R n)

end CommRing

end TauCeti
