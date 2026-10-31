/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Sym.Card
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalSections

/-!
# Zeroth cohomology of the twisting sheaves on projective space

Let `M` be a free `R`-module with a basis `b` indexed by a type `κ` with at least two elements, and
let `A = Sym M ≅ R[Xᵢ | i ∈ κ]`, so that `Proj A` is projective space over `R`. This file computes
the zeroth cohomology of the twisting sheaves `𝒪(n)` on `Proj A` as an `R`-module, over any
commutative ring `R`:

* for `j : ℕ`, `H⁰(Proj A, 𝒪(j)) ≅ A_j`, the forms of degree `j`, which is free with the basis of
  monomials of degree `j` in the coordinates, indexed by the degree-`j` multisets of `κ`;
* for `n < 0`, `H⁰(Proj A, 𝒪(n)) = 0`.

So `H⁰(Proj A, 𝒪(n))` is a free `R`-module for every `n : ℤ`, finitely generated when `κ` is
finite, of rank `(card κ).multichoose j` for `n = j ≥ 0`. On the projective line this is the
rank `max (n + 1) 0`. This is the `H⁰` part of Hartshorne, Theorem III.5.1, and follows from the
computation of global sections (`TauCeti.SymmetricAlgebra.bijective_toTwistingSheaf_top`) through
the identification of zeroth cohomology with global sections.

## Main definitions

* `TauCeti.SymmetricAlgebra.cohomologyZeroTwistingSheafLinearEquiv`:
  `H⁰(Proj A, 𝒪(j)) ≃ₗ[R] A_j`.
* `TauCeti.SymmetricAlgebra.cohomologyZeroTwistingSheafBasis`: the basis of `H⁰(Proj A, 𝒪(j))`
  given by the monomials of degree `j`.

## Main results

* `TauCeti.SymmetricAlgebra.subsingleton_cohomology_zero_twistingSheaf_of_neg`:
  `H⁰(Proj A, 𝒪(n)) = 0` for `n < 0`.
* `TauCeti.SymmetricAlgebra.free_cohomology_zero_twistingSheaf`,
  `TauCeti.SymmetricAlgebra.finite_cohomology_zero_twistingSheaf`: `H⁰(Proj A, 𝒪(n))` is free for
  every `n`, and finitely generated when `κ` is finite.
* `TauCeti.SymmetricAlgebra.finrank_cohomology_zero_twistingSheaf`: its rank is
  `(card κ).multichoose j` in degree `j : ℕ`.
* `TauCeti.AlgebraicGeometry.projectiveLine.finrank_cohomology_zero_twistingSheaf`: on the
  projective line, `H⁰(ℙ¹_R, 𝒪(n))` is free of rank `max (n + 1) 0` for every `n : ℤ`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.1(a).
* [Stacks, Lemma 30.8.1 (01XS)](https://stacks.math.columbia.edu/tag/01XS)
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.SymmetricAlgebra

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M] {κ : Type*}

local notation "𝒜" => homogeneousSubmodule R M

/-- **The zeroth cohomology of `𝒪(j)` on projective space is the module of forms of degree `j`**:
`H⁰(Proj A, 𝒪(j)) ≃ₗ[R] A_j` for `A = Sym M` and `M` free of rank at least two. The inverse sends
a form `r` to the class of the global section `r / 1`. -/
def cohomologyZeroTwistingSheafLinearEquiv (j : ℕ) (b : Module.Basis κ R M) [Nontrivial κ] :
    Cohomology (Proj.twistingSheaf 𝒜 j) 0 ≃ₗ[R] 𝒜 j :=
  (cohomologyZeroBaseLinearEquiv R _ _).trans
    (homogeneousSubmoduleLinearEquivTwistingSheafTop j b).symm

@[simp]
theorem cohomologyZeroTwistingSheafLinearEquiv_symm_apply (j : ℕ) (b : Module.Basis κ R M)
    [Nontrivial κ] (r : 𝒜 j) :
    (cohomologyZeroTwistingSheafLinearEquiv j b).symm r =
      (cohomologyZeroBaseLinearEquiv R _ _).symm
        (Proj.toTwistingSheaf 𝒜 (rfl : (j : ℤ) = j) ⊤ r) := by
  rw [cohomologyZeroTwistingSheafLinearEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, homogeneousSubmoduleLinearEquivTwistingSheafTop_apply]

/-- The basis of `H⁰(Proj A, 𝒪(j))` given by the monomials of degree `j` in the coordinates,
indexed by the degree-`j` multisets of basis indices. -/
def cohomologyZeroTwistingSheafBasis (j : ℕ) (b : Module.Basis κ R M) [Nontrivial κ] :
    Module.Basis (Sym κ j) R (Cohomology (Proj.twistingSheaf 𝒜 j) 0) :=
  (b.symmetricAlgebraHomogeneous j).map (cohomologyZeroTwistingSheafLinearEquiv j b).symm

/-- The monomial basis vector of `H⁰(Proj A, 𝒪(j))` indexed by `s` corresponds to the monomial
`∏_{i ∈ s} Xᵢ`. -/
@[simp]
theorem cohomologyZeroTwistingSheafLinearEquiv_basis (j : ℕ) (b : Module.Basis κ R M)
    [Nontrivial κ] (s : Sym κ j) :
    cohomologyZeroTwistingSheafLinearEquiv j b (cohomologyZeroTwistingSheafBasis j b s) =
      b.symmetricAlgebraHomogeneous j s := by
  rw [cohomologyZeroTwistingSheafBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]

/-- **Twisting sheaves of negative degree have no zeroth cohomology** on projective space:
`H⁰(Proj A, 𝒪(n)) = 0` for `n < 0`, with `A = Sym M` and `M` free of rank at least two. -/
theorem subsingleton_cohomology_zero_twistingSheaf_of_neg {n : ℤ} (hn : n < 0)
    (b : Module.Basis κ R M) [Nontrivial κ] :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 n) 0) :=
  have : Subsingleton Γ(Proj.twistingSheaf 𝒜 n, ⊤) :=
    ⟨fun s t ↦ (twistingSheaf_top_eq_zero_of_neg hn b s).trans
      (twistingSheaf_top_eq_zero_of_neg hn b t).symm⟩
  (cohomologyZeroBaseLinearEquiv R _ _).toEquiv.subsingleton

/-- The zeroth cohomology `H⁰(Proj A, 𝒪(n))` on projective space is a free `R`-module for every
`n : ℤ`. -/
theorem free_cohomology_zero_twistingSheaf (n : ℤ) (b : Module.Basis κ R M) [Nontrivial κ] :
    Module.Free R (Cohomology (Proj.twistingSheaf 𝒜 n) 0) := by
  rcases lt_or_ge n 0 with hn | hn
  · have := subsingleton_cohomology_zero_twistingSheaf_of_neg (R := R) hn b
    exact .of_subsingleton _ _
  · lift n to ℕ using hn
    exact .of_basis (cohomologyZeroTwistingSheafBasis n b)

/-- The zeroth cohomology `H⁰(Proj A, 𝒪(n))` on projective space of finite dimension is a finitely
generated `R`-module for every `n : ℤ`. -/
theorem finite_cohomology_zero_twistingSheaf (n : ℤ) (b : Module.Basis κ R M) [Nontrivial κ]
    [Finite κ] : Module.Finite R (Cohomology (Proj.twistingSheaf 𝒜 n) 0) := by
  rcases lt_or_ge n 0 with hn | hn
  · have := subsingleton_cohomology_zero_twistingSheaf_of_neg (R := R) hn b
    infer_instance
  · lift n to ℕ using hn
    exact .of_basis (cohomologyZeroTwistingSheafBasis n b)

/-- **The rank of `H⁰(Proj A, 𝒪(j))`** on projective space with homogeneous coordinates indexed
by `κ` is the number `(card κ).multichoose j` of monomials of degree `j`. -/
theorem finrank_cohomology_zero_twistingSheaf [Nontrivial R] (j : ℕ) (b : Module.Basis κ R M)
    [Nontrivial κ] [Fintype κ] :
    Module.finrank R (Cohomology (Proj.twistingSheaf 𝒜 j) 0) = (Fintype.card κ).multichoose j := by
  classical
  rw [Module.finrank_eq_card_basis (cohomologyZeroTwistingSheafBasis j b),
    Sym.card_sym_eq_multichoose]

end TauCeti.SymmetricAlgebra

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R : Type u) [CommRing R]

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)

/-- `H⁰(ℙ¹_R, 𝒪(n))` is a free `R`-module for every `n : ℤ`. -/
instance free_cohomology_zero_twistingSheaf (n : ℤ) :
    Module.Free R (Cohomology (Proj.twistingSheaf 𝒜 n) 0) :=
  SymmetricAlgebra.free_cohomology_zero_twistingSheaf n (Pi.basisFun R (Fin 2))

/-- `H⁰(ℙ¹_R, 𝒪(n))` is a finitely generated `R`-module for every `n : ℤ`, over any ring. -/
instance finite_cohomology_zero_twistingSheaf (n : ℤ) :
    Module.Finite R (Cohomology (Proj.twistingSheaf 𝒜 n) 0) :=
  SymmetricAlgebra.finite_cohomology_zero_twistingSheaf n (Pi.basisFun R (Fin 2))

/-- **The zeroth cohomology of `𝒪(n)` on the projective line** has rank `max (n + 1) 0`: the
free `R`-module `H⁰(ℙ¹_R, 𝒪(n))` has rank `n + 1` for `n ≥ 0`, and vanishes for `n < 0`. -/
theorem finrank_cohomology_zero_twistingSheaf [Nontrivial R] (n : ℤ) :
    Module.finrank R (Cohomology (Proj.twistingSheaf 𝒜 n) 0) = (n + 1).toNat := by
  rcases lt_or_ge n 0 with hn | hn
  · have := SymmetricAlgebra.subsingleton_cohomology_zero_twistingSheaf_of_neg (R := R) hn
      (Pi.basisFun R (Fin 2))
    rw [Module.finrank_zero_of_subsingleton]
    omega
  · lift n to ℕ using hn
    rw [SymmetricAlgebra.finrank_cohomology_zero_twistingSheaf n (Pi.basisFun R (Fin 2)),
      Fintype.card_fin, Nat.multichoose_two]
    omega

end TauCeti.AlgebraicGeometry.projectiveLine
