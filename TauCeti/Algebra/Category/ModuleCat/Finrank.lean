/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.LinearAlgebra.Dimension.Prod

/-!
# Finrank of zero objects, biproducts and short exact sequences in `ModuleCat`

Vanishing and direct sums of objects of `ModuleCat R` are naturally expressed categorically, as
`CategoryTheory.Limits.IsZero` and biproducts `M ⊞ N`, while the dimension counts that consume them
speak of `Module.finrank`. This file supplies the translations between the two: the ring itself
has finrank one (`ModuleCat.finrank_of_self`), a zero object has finrank zero, and finrank is
additive on biproducts of finite free modules
(`ModuleCat.finrank_biprod`, the analogue of `FGModuleCat.finrank_biprod`).

Over a ring satisfying the strong rank condition (`StrongRankCondition`) and the rank--nullity
theorem (`HasRankNullity`), such as a division ring or a commutative domain, finrank is moreover
additive on every short exact sequence whose middle term is finitely generated
(`CategoryTheory.ShortComplex.ShortExact.moduleCat_finrank_eq_add`), hence on binary biproducts
(`ModuleCat.finrank_biprod_of_hasRankNullity`), finite biproducts (`ModuleCat.finrank_biproduct`),
and finite coproducts (`ModuleCat.finrank_sigma`) of finitely generated modules. Unlike Mathlib's
`ModuleCat.free_shortExact_finrank_add` and `Module.finrank_directSum`, no freeness is assumed, so
this covers biproducts, coproducts, and sequences of finitely generated abelian groups with torsion.

The first translation is what bounds the `Module.finrank` support of a bounded complex of vector
spaces by its bounding interval, which is in turn what makes Mathlib's `finsum`-based Euler
characteristic of such a complex an honest finite sum. For an `ℕ`-indexed family vanishing from
some degree on, `ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range` records that finite sum
directly.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe w v u

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

end ModuleCat

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]

/-- Over a ring with the strong rank condition and the rank--nullity property, finrank is additive
on a short exact sequence of modules whose middle term is finitely generated. -/
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
    Module.finrank R ↑(M ⊞ N) = Module.finrank R M + Module.finrank R N :=
  (biprodIsoProd M N).toLinearEquiv.finrank_eq.trans Module.finrank_prod_of_hasRankNullity

/-- Over a ring satisfying the strong rank condition and the rank-nullity property
(`HasRankNullity`), such as a division ring or a commutative domain, the finrank of a finite
biproduct of finitely generated modules is the sum of their finranks. Unlike
`ModuleCat.finrank_biprod`, no freeness is assumed, so this covers finitely generated abelian
groups with torsion. -/
theorem finrank_biproduct {ι : Type*} [Fintype ι] (V : ι → ModuleCat.{v} R)
    [∀ i, Module.Finite R (V i)] :
    Module.finrank R (⨁ V : ModuleCat.{v} R) = ∑ i, Module.finrank R (V i) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have : ∀ j, Module.Finite R (V (e j)) := fun j ↦ inferInstance
  rw [((biproduct.whiskerEquiv e fun _ ↦ Iso.refl _).symm ≪≫
        biproductIsoPi (fun j : Fin (Fintype.card ι) ↦ V (e j))).toLinearEquiv.finrank_eq,
    Module.finrank_pi_fintype_of_hasRankNullity]
  exact Fintype.sum_equiv e _ _ fun _ ↦ rfl

/-- Over a ring with the strong rank condition and rank-nullity, the finrank of a finite coproduct
of finitely generated modules is the sum of their finranks (without assuming freeness). -/
theorem finrank_sigma {ι : Type w} [Fintype ι] (f : ι → ModuleCat.{v} R)
    [HasCoproduct f] [∀ i, Module.Finite R (f i)] :
    Module.finrank R ↑(∐ f) = ∑ i, Module.finrank R (f i) :=
  ((biproduct.isoCoproduct f).symm.toLinearEquiv.finrank_eq).trans (finrank_biproduct f)

end ModuleCat
