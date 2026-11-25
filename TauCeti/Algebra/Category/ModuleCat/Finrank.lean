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
import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.Algebra.Category.ModuleCat.Biproducts
import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic

/-!
# Finrank of zero objects, coproducts, biproducts and short exact sequences in `ModuleCat`

Vanishing and direct sums of objects of `ModuleCat R` are naturally expressed categorically, as
`CategoryTheory.Limits.IsZero`, coproducts `∐ Z`, and biproducts `M ⊞ N`, while the dimension counts
that consume them speak of `Module.finrank`. This file supplies the translations between the two:
the ring itself has finrank one (`ModuleCat.finrank_of_self`), a zero object has finrank zero, and
finrank is additive on biproducts and finite coproducts of finite free modules
(`ModuleCat.finrank_biprod`, `ModuleCat.finrank_sigmaObj`).

Over a ring satisfying the rank-nullity theorem (`HasRankNullity`), such as a division ring or a
commutative domain, finrank is moreover additive on every short exact sequence whose middle term is
finitely generated (`CategoryTheory.ShortComplex.ShortExact.moduleCat_finrank_eq_add`), hence on
binary biproducts (`ModuleCat.finrank_biprod_of_hasRankNullity`) and finite biproducts
(`ModuleCat.finrank_biproduct`) of finitely generated modules. Unlike Mathlib's
`ModuleCat.free_shortExact_finrank_add`, no freeness is assumed, so this covers biproducts and
sequences of finitely generated abelian groups with torsion.

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

namespace ModuleCat

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]

/-- Over a ring satisfying the strong rank condition and the rank-nullity property
(`HasRankNullity`), such as a division ring or a commutative domain, the finrank of a binary
biproduct of finitely generated modules is the sum of their finranks, without assuming freeness. -/
theorem finrank_biprod_of_hasRankNullity (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R ↑(M ⊞ N) = Module.finrank R M + Module.finrank R N := by
  have : Module.Finite R ↑(M ⊞ N) := Module.Finite.equiv (biprodIsoProd M N).symm.toLinearEquiv
  exact (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact.moduleCat_finrank_eq_add

/-- Over a ring satisfying the strong rank condition and the rank-nullity property
(`HasRankNullity`), such as a division ring or a commutative domain, the finrank of a finite
biproduct of finitely generated modules is the sum of their finranks. Unlike
`ModuleCat.finrank_biprod`, no freeness is assumed, so this covers finitely generated abelian
groups with torsion. -/
theorem finrank_biproduct {ι : Type*} [Fintype ι] (V : ι → ModuleCat.{v} R)
    [∀ i, Module.Finite R (V i)] :
    Module.finrank R (⨁ V : ModuleCat.{v} R) = ∑ i, Module.finrank R (V i) := by
  refine Fintype.induction_empty_option
    (P := fun α [Fintype α] ↦ ∀ (W : α → ModuleCat.{v} R) [∀ i, Module.Finite R (W i)],
      Module.finrank R (⨁ W : ModuleCat.{v} R) = ∑ i, Module.finrank R (W i))
    ?_ ?_ ?_ ι V
  · intro α β _ e ih W _
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have hsum := Equiv.sum_comp e (fun i ↦ Module.finrank R (W i))
    rw [((biproduct.whiskerEquiv e fun _ ↦ Iso.refl _).symm).toLinearEquiv.finrank_eq,
      ih (fun a ↦ W (e a)), hsum]
  · intro W _
    have := subsingleton_of_isZero (TauCeti.isZero_biproduct_of_isEmpty W)
    simp [Module.finrank_zero_of_subsingleton]
  · intro α _ ih W _
    have : Module.Finite R (⨁ fun j ↦ W (some j) : ModuleCat.{v} R) :=
      finite_biproduct (fun j ↦ W (some j))
    rw [(TauCeti.biproductOptionIso W).toLinearEquiv.finrank_eq,
      finrank_biprod_of_hasRankNullity, ih (fun j ↦ W (some j)), Fintype.sum_option]

end ModuleCat
