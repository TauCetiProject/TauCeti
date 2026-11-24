/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.LocallyFree.IdealClass
import TauCeti.LinearAlgebra.Dimension.Pi
import TauCeti.LinearAlgebra.Dimension.Prod
import TauCeti.RingTheory.FractionalIdeal.LinearEquiv

/-!
# Projective `K₀` of a Dedekind domain

For a Dedekind domain `A`, the rank and the Steinitz class of finite projective modules are
additive invariants, and together they identify the split Grothendieck group of finite
projective `A`-modules:

```text
K₀(A) ≃+ ℤ × Additive (ClassGroup A),   [P] ↦ (rank P, st(P)).
```

The inverse sends `(n, c)` to `n[A] + ([I] - [A])` for any nonzero ideal `I` of class `c`, that
is, to `n[A]` plus the value at `c` of the ideal-class homomorphism
`TauCeti.FiniteProjectiveModules.idealClassHom`. Its image is the kernel of the rank, which is
therefore the locally free class group of `A` over itself
(`TauCeti.LocallyFree.mem_classGroup_iff_rankSteinitz_fst_eq_zero`); the injectivity of the
ideal-class homomorphism and its identification with the locally free class group
(`TauCeti.LocallyFree.ofIdealClassEquiv`) are in
`TauCeti.RingTheory.DedekindDomain.LocallyFree.IdealClass`.

## Main definitions

* `TauCeti.FiniteProjectiveModules.rankSteinitz`: the homomorphism `[P] ↦ (rank P, st(P))`.
* `TauCeti.FiniteProjectiveModules.rankSteinitzEquiv`: the isomorphism
  `K₀(A) ≃+ ℤ × Additive (ClassGroup A)`.

## Main results

* `TauCeti.FiniteProjectiveModules.rankSteinitz_of`, `rankSteinitz_idealClassHom` and
  `rankSteinitzEquiv_symm_apply`: the values on projective classes and on ideal classes, and the
  inverse.
* `TauCeti.FiniteProjectiveModules.mem_range_idealClassHom_iff`: the reduced ideal classes are
  exactly the classes of rank zero.
* `TauCeti.LocallyFree.mem_classGroup_iff_rankSteinitz_fst_eq_zero`: the locally free classes are
  exactly the classes of rank zero.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Chapter II,
  Proposition 2.6 and Corollary 2.6.3, and Chapter I, Proposition 3.4.
-/

public section

namespace TauCeti

universe u

variable (A : Type u) [CommRing A] [IsDedekindDomain A]

namespace FiniteProjectiveModules

/-- Rank and Steinitz class, as an additive invariant of finite projective modules. -/
private noncomputable def rankSteinitzInvariant :
    SplitK0.AdditiveInvariant (finiteProjectiveModules A).FullSubcategory
      (ℤ × Additive (ClassGroup A)) where
  obj P := (Module.finrank A P.obj, Additive.ofMul (Module.steinitzClass A P.obj))
  map_iso X Y e := by
    let e' : X.obj ≃ₗ[A] Y.obj := ((finiteProjectiveModules A).ι.mapIso e).toLinearEquiv
    rw [e'.finrank_eq, Module.steinitzClass_congr e']
  map_biprod X Y := by
    let e := biprodLinearEquiv X Y
    rw [e.finrank_eq, Module.steinitzClass_congr e,
      Module.finrank_prod_of_hasRankNullity (Module.rank_lt_aleph0 A X.obj)
        (Module.rank_lt_aleph0 A Y.obj), Module.steinitzClass_prod]
    simp

/-- The inverse of the rank–Steinitz isomorphism, `(n, c) ↦ n[A] + idealClassHom c`. -/
private noncomputable def rankSteinitzInv :
    ℤ × Additive (ClassGroup A) →+ SplitK0.{u} (finiteProjectiveModules A).FullSubcategory :=
  (zmultiplesHom (SplitK0.{u} (finiteProjectiveModules A).FullSubcategory)
    (SplitK0.of.{u} (finiteProjectiveModulesRegular A))).coprod (idealClassHom A)

/-- The homomorphism from projective `K₀` of a Dedekind domain sending the class of a finite
projective module to its rank and its Steinitz class. -/
noncomputable def rankSteinitz :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory →+ ℤ × Additive (ClassGroup A) :=
  SplitK0.lift (rankSteinitzInvariant A)

/-- The class of a finite projective module goes to its rank and its Steinitz class. -/
@[simp]
theorem rankSteinitz_of (P : (finiteProjectiveModules A).FullSubcategory) :
    rankSteinitz A (SplitK0.of P) =
      ((Module.finrank A P.obj : ℤ), Additive.ofMul (Module.steinitzClass A P.obj)) :=
  SplitK0.lift_of _ _

/-- The class of the regular module goes to rank one and the trivial class. -/
theorem rankSteinitz_of_finiteProjectiveModulesRegular :
    rankSteinitz A (SplitK0.of.{u} (finiteProjectiveModulesRegular A)) = (1, 0) := by
  simp [finiteProjectiveModulesRegular]

/-- A reduced ideal class `[I] - [A]` has rank zero and Steinitz class `[I]`. -/
@[simp]
theorem rankSteinitz_idealClassHom (c : Additive (ClassGroup A)) :
    rankSteinitz A (idealClassHom A c) = (0, c) := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c.toMul
  have : Module.Projective A (I : Ideal A) := .of_equiv
    (FractionalIdeal.coeIdealEquiv (S := nonZeroDivisors A) (P := FractionRing A) (I : Ideal A))
  have hrank : Module.finrank A (I : Ideal A) = 1 :=
    Module.finrank_eq_card_of_linearEquiv_pi (J := fun _ : Unit ↦ (I : Ideal A))
      (fun _ ↦ mem_nonZeroDivisors_iff_ne_zero.mp I.property)
      (LinearEquiv.piUnique A fun _ : Unit ↦ (I : Ideal A)).symm
  rw [← ofMul_toMul c, ← hI]
  simp [classOf_def, hrank]

/-- **Projective `K₀` of a Dedekind domain.** Rank and Steinitz class identify projective `K₀`
with `ℤ × Additive (ClassGroup A)`. -/
noncomputable def rankSteinitzEquiv :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+ ℤ × Additive (ClassGroup A) where
  toFun := rankSteinitz A
  invFun := rankSteinitzInv A
  left_inv := DFunLike.congr_fun (show (rankSteinitzInv A).comp (rankSteinitz A) =
      AddMonoidHom.id _ from SplitK0.hom_ext fun P ↦ by
    simp [rankSteinitzInv, idealClassHom_steinitzClass, classOf_def,
      finiteProjectiveModulesRegular])
  right_inv p := by
    simp only [rankSteinitzInv, AddMonoidHom.coprod_apply, zmultiplesHom_apply, map_add,
      map_zsmul, rankSteinitz_of_finiteProjectiveModulesRegular, rankSteinitz_idealClassHom]
    ext <;> simp
  map_add' := map_add _

@[simp]
theorem rankSteinitzEquiv_apply (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    rankSteinitzEquiv A x = rankSteinitz A x :=
  (rfl)

/-- The inverse of the rank–Steinitz isomorphism sends `(n, c)` to `n[A]` plus the reduced ideal
class `c`. -/
@[simp]
theorem rankSteinitzEquiv_symm_apply (p : ℤ × Additive (ClassGroup A)) :
    (rankSteinitzEquiv A).symm p =
      p.1 • SplitK0.of.{u} (finiteProjectiveModulesRegular A) + idealClassHom A p.2 := by
  simp [rankSteinitzEquiv, rankSteinitzInv, AddEquiv.symm_mk, AddMonoidHom.coprod_apply,
    zmultiplesHom_apply]

/-- The reduced ideal classes are exactly the classes of rank zero in projective `K₀`. -/
theorem mem_range_idealClassHom_iff
    {x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory} :
    x ∈ (idealClassHom A).range ↔ (rankSteinitz A x).1 = 0 := by
  refine ⟨?_, fun hx ↦ ⟨(rankSteinitz A x).2, (rankSteinitzEquiv A).injective ?_⟩⟩
  · rintro ⟨c, rfl⟩
    simp
  · rw [rankSteinitzEquiv_apply, rankSteinitzEquiv_apply, rankSteinitz_idealClassHom]
    exact Prod.ext hx.symm rfl

end FiniteProjectiveModules

namespace LocallyFree

variable {A} {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

open FiniteProjectiveModules

/-- The locally free class group of a Dedekind domain `A` over itself is the kernel of the rank on
projective `K₀`. -/
theorem mem_classGroup_iff_rankSteinitz_fst_eq_zero
    {x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory} :
    x ∈ classGroup A K A ↔ (rankSteinitz A x).1 = 0 := by
  rw [← mem_range_idealClassHom_iff]
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨c, hc⟩ := ofIdealClass_surjective (K := K) ⟨x, hx⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  · rintro ⟨c, rfl⟩
    exact idealClassHom_mem_classGroup c

end LocallyFree

end TauCeti
