/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Module.Projective.FreeComplement
public import TauCeti.Algebra.Module.StableEquivalent
public import TauCeti.CategoryTheory.GrothendieckGroup.Split

/-!
# Equality in the split `K₀` of finitely generated projective modules

For a ring `R`, not necessarily commutative, the projective `K₀` of `R` is the split Grothendieck
group `TauCeti.SplitK0` of the full subcategory of finitely generated projective `R`-modules. This
file identifies equality of classes there with stable equivalence: `[P] = [Q]` if and only if
`P × Rⁿ ≃ₗ[R] Q × Rⁿ` for some `n` (`TauCeti.StableEquivalent`). In particular `[P] = [Rⁿ]` if and
only if `P × Rᵏ ≃ₗ[R] Rⁿ⁺ᵏ` for some `k`, which is the stable freeness measured by classes
`[M] - n[R]`.

Equality in a group completion is witnessed by a common summand (`TauCeti.SplitK0.of_eq_of_iff`).
Here that summand `T` is finitely generated projective, so it has a complement `N` with
`T × N ≃ₗ[R] Rⁿ` (`Module.Projective.exists_prod_linearEquiv_fin`), and adding `N` to both sides
replaces `T` by a finite free module. Equality in `K₀` is stable equivalence rather than
isomorphism, since there are stably free modules which are not free.

## Main results

* `TauCeti.SplitK0.of_eq_of_iff_stableEquivalent`: two finitely generated projective modules have
  the same class in split `K₀` if and only if they are stably equivalent.
* `TauCeti.SplitK0.of_eq_of_iff_exists_prod_linearEquiv_fin`: a finitely generated projective
  module `P` has the class of a module `Q ≃ₗ[R] Rⁿ` if and only if `P × Rᵏ ≃ₗ[R] Rⁿ⁺ᵏ` for some
  `k`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §1,
  Proposition 1.1 and Corollary 1.3, pp. 1–2, and §2, p. 5.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [Ring R]

/-- Two biproducts of finitely generated projective modules are isomorphic exactly when the
products of the underlying modules are linearly isomorphic. -/
private theorem nonempty_biprod_iso_biprod_iff
    {X S Y T : (finiteProjectiveModules R).FullSubcategory} :
    Nonempty (X ⊞ S ≅ Y ⊞ T) ↔ Nonempty ((X.obj × S.obj) ≃ₗ[R] (Y.obj × T.obj)) := by
  -- The inclusion into `ModuleCat R` is additive, so it carries biproducts to products.
  let e (A B : (finiteProjectiveModules R).FullSubcategory) : (A ⊞ B).obj ≃ₗ[R] A.obj × B.obj :=
    letI : PreservesBinaryBiproduct A B (finiteProjectiveModules R).ι :=
      preservesBinaryBiproduct_of_preservesBinaryCoproduct _
    (((finiteProjectiveModules R).ι.mapBiprod A B).trans
      (ModuleCat.biprodIsoProd _ _)).toLinearEquiv
  exact ⟨fun ⟨f⟩ => ⟨(e X S).symm.trans <|
      ((finiteProjectiveModules R).ι.mapIso f).toLinearEquiv.trans (e Y T)⟩,
    fun ⟨f⟩ => ⟨(finiteProjectiveModules R).fullyFaithfulι.preimageIso <|
      ((e X S).trans <| f.trans (e Y T).symm).toModuleIso⟩⟩

namespace SplitK0

/-- **Equality in projective `K₀` is stable equivalence.** Two finitely generated projective
`R`-modules have the same class in split `K₀` if and only if `P × Rⁿ ≃ₗ[R] Q × Rⁿ` for some `n`. -/
theorem of_eq_of_iff_stableEquivalent {P Q : (finiteProjectiveModules R).FullSubcategory} :
    of.{u} P = of.{u} Q ↔ StableEquivalent R P.obj Q.obj := by
  rw [of_eq_of_iff, stableEquivalent_iff]
  constructor
  · rintro ⟨T, h⟩
    obtain ⟨e⟩ := nonempty_biprod_iso_biprod_iff.1 h
    obtain ⟨N, _, _, _, _, n, ⟨c⟩⟩ := Module.Projective.exists_prod_linearEquiv_fin R T.obj
    -- Enlarge the common summand `T` to the finite free module `T × N ≃ₗ[R] Rⁿ`.
    exact ⟨n, ⟨((LinearEquiv.refl R P.obj).prodCongr c.symm).trans <|
      (LinearEquiv.prodAssoc R P.obj T.obj N).symm.trans <|
      (e.prodCongr (LinearEquiv.refl R N)).trans <|
      (LinearEquiv.prodAssoc R Q.obj T.obj N).trans <| (LinearEquiv.refl R Q.obj).prodCongr c⟩⟩
  · rintro ⟨n, h⟩
    exact ⟨⟨ModuleCat.of R (Fin n → R),
      finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩,
      nonempty_biprod_iso_biprod_iff.2 h⟩

/-- **Classes of finite free modules in projective `K₀`.** If `Q ≃ₗ[R] Rⁿ`, then a finitely
generated projective module `P` has the class of `Q` in split `K₀` if and only if
`P × Rᵏ ≃ₗ[R] Rⁿ⁺ᵏ` for some `k`. -/
theorem of_eq_of_iff_exists_prod_linearEquiv_fin
    {P Q : (finiteProjectiveModules R).FullSubcategory} {n : ℕ} (e : Q.obj ≃ₗ[R] (Fin n → R)) :
    of.{u} P = of.{u} Q ↔ ∃ k : ℕ, Nonempty ((P.obj × (Fin k → R)) ≃ₗ[R] (Fin (n + k) → R)) := by
  rw [of_eq_of_iff_stableEquivalent, ← stableEquivalent_fin_fun_iff]
  exact ⟨fun h => h.trans (.of_equiv e), fun h => h.trans (.of_equiv e.symm)⟩

end SplitK0

end TauCeti
