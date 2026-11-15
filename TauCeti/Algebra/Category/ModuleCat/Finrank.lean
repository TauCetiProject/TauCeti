/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finrank of zero objects, coproducts, biproducts and short exact sequences in `ModuleCat`

Vanishing and direct sums of objects of `ModuleCat R` are naturally expressed categorically, as
`CategoryTheory.Limits.IsZero`, coproducts `∐ Z` (`ModuleCat.isZero_sigmaObj`), and biproducts
`M ⊞ N`, while the dimension counts that consume them speak of `Module.finrank`. This file supplies
the translations between the two: the ring itself has finrank one (`ModuleCat.finrank_of_self`), a
zero object has finrank zero, and finrank is additive on biproducts and finite coproducts of finite
free modules (`ModuleCat.finrank_biprod`, `ModuleCat.finrank_sigmaObj`).

For short exact sequences in `ModuleCat R`, finite generation of the outer terms passes to the
middle term over any ring (`CategoryTheory.ShortComplex.ShortExact.moduleCat_finite_X₂`), and over a
ring satisfying the rank-nullity theorem (`HasRankNullity`), such as a division ring or a
commutative domain, finrank is additive on every short exact sequence whose middle term is finitely
generated (`CategoryTheory.ShortComplex.ShortExact.moduleCat_finrank_eq_add`). Unlike Mathlib's
`ModuleCat.free_shortExact_finrank_add`, no freeness is assumed, so this covers sequences of
finitely generated abelian groups with torsion.

The first translation is what bounds the `Module.finrank` support of a bounded complex of vector
spaces by its bounding interval, which is in turn what makes Mathlib's `finsum`-based Euler
characteristic of such a complex an honest finite sum. For an `ℕ`-indexed family vanishing from
some degree on, `ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range` records that finite sum
directly.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R]

section Nontrivial

variable [Nontrivial R]

/-- The ring `R`, as an object of `ModuleCat R`, has finrank one. -/
theorem finrank_of_self (R : Type u) [Ring R] [StrongRankCondition R] :
    Module.finrank R (ModuleCat.of R R) = 1 :=
  Module.finrank_self R

/-- A zero object in `ModuleCat R` has finrank zero. -/
theorem finrank_eq_zero_of_isZero {X : ModuleCat.{v} R} (hX : IsZero X) :
    Module.finrank R X = 0 :=
  have := subsingleton_of_isZero hX
  Module.finrank_zero_of_subsingleton

/-- If an `ℕ`-indexed family in `ModuleCat R` vanishes from degree `N` on, the alternating
`finsum` of its finranks is the honest finite sum over the degrees below `N`. -/
theorem finsum_neg_one_pow_finrank_eq_sum_range {M : ℕ → ModuleCat.{v} R} {N : ℕ}
    (hN : ∀ n ≥ N, IsZero (M n)) :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Module.finrank R (M n) =
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * Module.finrank R (M n) := by
  refine finsum_eq_sum_of_support_subset _ fun n hn ↦ ?_
  contrapose hn
  simp [finrank_eq_zero_of_isZero (hN n (by simpa using hn))]

end Nontrivial

/-- A coproduct of zero objects in `ModuleCat R` is a zero object. -/
theorem isZero_sigmaObj {ι : Type*} (Z : ι → ModuleCat.{v} R) [HasCoproduct Z]
    (h : ∀ i, IsZero (Z i)) : IsZero (∐ Z) :=
  (IsZero.iff_id_eq_zero _).2 <| Sigma.hom_ext _ _ fun i ↦ (h i).eq_of_src _ _

/-- The finrank of a biproduct of finite free modules is the sum of their finranks. -/
@[simp]
theorem finrank_biprod [StrongRankCondition R] (M N : ModuleCat.{v} R)
    [Module.Free R M] [Module.Free R N] [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R ↑(M ⊞ N) = Module.finrank R M + Module.finrank R N :=
  (biprodIsoProd M N).toLinearEquiv.finrank_eq.trans Module.finrank_prod

/-- The finrank of a finite coproduct of finite free modules is the sum of their finranks. -/
@[simp]
theorem finrank_sigmaObj [StrongRankCondition R] {ι : Type*} [Fintype ι]
    (Z : ι → ModuleCat.{v} R) [HasCoproduct Z] [∀ i, Module.Free R (Z i)]
    [∀ i, Module.Finite R (Z i)] :
    Module.finrank R ↥(∐ Z) = ∑ i, Module.finrank R (Z i) := by
  let e := (Fintype.equivFin ι).symm
  have : HasCoproduct (Z ∘ e) := ⟨_, coproductCoconeIsColimit.{u, 0, v} (Z ∘ e)⟩
  let iso := (Sigma.reindex e Z).symm ≪≫ coprodIsoDirectSum.{u, 0, v} (Z ∘ e)
  exact iso.toLinearEquiv.finrank_eq.trans
    ((Module.finrank_directSum R fun k ↦ Z (e k)).trans
      (e.sum_comp fun i ↦ Module.finrank R (Z i)))

end ModuleCat

namespace CategoryTheory.ShortComplex.ShortExact

/-- Over any ring `R`, if `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence in `ModuleCat R` with
`X₁` and `X₃` finitely generated, then `X₂` is finitely generated. -/
theorem moduleCat_finite_X₂ {R : Type u} [Ring R] {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) [Module.Finite R S.X₁] [Module.Finite R S.X₃] :
    Module.Finite R S.X₂ :=
  Module.Finite.of_exact (f := S.f.hom) (g := S.g.hom)
    ((moduleCat_exact_iff_function_exact S).1 hS.exact) hS.moduleCat_surjective_g

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]

/-- Over a ring with the rank-nullity property, finrank is additive on a short exact sequence of
modules whose middle term is finitely generated. -/
theorem moduleCat_finrank_eq_add {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    [Module.Finite R S.X₂] :
    Module.finrank R S.X₂ = Module.finrank R S.X₁ + Module.finrank R S.X₃ := by
  -- Rank-nullity for the kernel of `g`, which is the image of the injective map `f`.
  have h := (LinearMap.ker S.g.hom).finrank_quotient_add_finrank
  rw [(S.g.hom.quotKerEquivOfSurjective hS.moduleCat_surjective_g).finrank_eq,
    ← hS.exact.moduleCat_range_eq_ker,
    (LinearEquiv.ofInjective _ hS.moduleCat_injective_f).finrank_eq.symm] at h
  lia

end CategoryTheory.ShortComplex.ShortExact
