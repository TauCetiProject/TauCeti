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

The file also records additivity on products of modules, `[P × Q] = [P] + [Q]` and
`[Rⁿ] = n[R]`, in the form consumed by classes `[M] - n[R]`.

## Main results

* `TauCeti.SplitK0.of_eq_add_of_linearEquiv_prod`: the class of a module isomorphic to `P × Q` is
  the sum of the classes of `P` and `Q`.
* `TauCeti.SplitK0.of_eq_nsmul_of_linearEquiv_fin`: the class of a module isomorphic to `Rⁿ` is
  `n` times the class of `R`.
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

/-- The underlying module of a biproduct of finitely generated projective modules is the product of
the underlying modules: the inclusion into `ModuleCat R` is additive, so it carries biproducts to
products. -/
private noncomputable def biprodLinearEquiv (X Y : (finiteProjectiveModules R).FullSubcategory) :
    (X ⊞ Y).obj ≃ₗ[R] X.obj × Y.obj :=
  letI : PreservesBinaryBiproduct X Y (finiteProjectiveModules R).ι :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  (((finiteProjectiveModules R).ι.mapBiprod X Y).trans (ModuleCat.biprodIsoProd _ _)).toLinearEquiv

/-- Two biproducts of finitely generated projective modules are isomorphic exactly when the
products of the underlying modules are linearly isomorphic. -/
private theorem nonempty_biprod_iso_biprod_iff
    {X S Y T : (finiteProjectiveModules R).FullSubcategory} :
    Nonempty (X ⊞ S ≅ Y ⊞ T) ↔ Nonempty ((X.obj × S.obj) ≃ₗ[R] (Y.obj × T.obj)) :=
  ⟨fun ⟨f⟩ => ⟨(biprodLinearEquiv X S).symm.trans <|
      ((finiteProjectiveModules R).ι.mapIso f).toLinearEquiv.trans (biprodLinearEquiv Y T)⟩,
    fun ⟨f⟩ => ⟨(finiteProjectiveModules R).fullyFaithfulι.preimageIso <|
      ((biprodLinearEquiv X S).trans <| f.trans (biprodLinearEquiv Y T).symm).toModuleIso⟩⟩

namespace SplitK0

/-- **Additivity on products.** The class of a finitely generated projective module isomorphic to
a product `P × Q` is the sum of the classes of `P` and `Q`. -/
theorem of_eq_add_of_linearEquiv_prod {X P Q : (finiteProjectiveModules R).FullSubcategory}
    (e : X.obj ≃ₗ[R] (P.obj × Q.obj)) : of.{u} X = of.{u} P + of.{u} Q := by
  rw [← of_biprod]
  exact of_congr ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
    (e.trans (biprodLinearEquiv P Q).symm).toModuleIso)

/-- The class of a finitely generated projective module isomorphic to `Rⁿ` is `n` times the class
of `R`. -/
theorem of_eq_nsmul_of_linearEquiv_fin {X R' : (finiteProjectiveModules R).FullSubcategory}
    {n : ℕ} (e : X.obj ≃ₗ[R] (Fin n → R)) (e' : R'.obj ≃ₗ[R] R) : of.{u} X = n • of.{u} R' := by
  induction n generalizing X with
  | zero =>
    have : Subsingleton ((finiteProjectiveModules R).ι.obj X) := e.toEquiv.subsingleton
    rw [zero_smul]
    exact of_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero (finiteProjectiveModules R).ι
      X (ModuleCat.isZero_of_subsingleton _))
  | succ n ih =>
    -- Split `Rⁿ⁺¹ ≃ R × Rⁿ` and use additivity on products.
    let Y : (finiteProjectiveModules R).FullSubcategory :=
      ⟨ModuleCat.of R (Fin n → R), finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩
    rw [of_eq_add_of_linearEquiv_prod (P := R') (Q := Y)
      (e.trans ((Fin.consLinearEquiv R fun _ ↦ R).symm.trans (e'.symm.prodCongr (.refl _ _)))),
      ih (X := Y) (.refl _ _), succ_nsmul']

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
