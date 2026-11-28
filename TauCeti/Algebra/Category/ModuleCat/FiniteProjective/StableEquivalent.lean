/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0.Basic
public import TauCeti.Algebra.Module.StableEquivalent

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

The file defines `TauCeti.FiniteProjectiveModules.classOf R M n = [M] - n[R]`, with
isomorphism invariance, stable-freeness and stable-equivalence criteria, additivity on products,
and vanishing on finite free modules. These classes measure the obstruction to stable freeness.

Additivity on binary and finite products (`TauCeti.SplitK0.of_eq_add_of_linearEquiv_prod`,
`TauCeti.SplitK0.of_eq_sum_of_linearEquiv_pi`) and finite-free class formulas (`[Rⁿ] = n[R]`)
are in `TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0.Basic`.

## Main results

* `TauCeti.FiniteProjectiveModules.classOf_eq_zero_iff`: the class `[M] - n[R]` vanishes
  exactly when `M` is stably free of rank `n`.
* `TauCeti.FiniteProjectiveModules.classOf_eq_classOf_iff`: equality of classes in the same
  rank is stable equivalence.
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
    Nonempty (X ⊞ S ≅ Y ⊞ T) ↔ Nonempty ((X.obj × S.obj) ≃ₗ[R] (Y.obj × T.obj)) :=
  ⟨fun ⟨f⟩ => ⟨(FiniteProjectiveModules.biprodLinearEquiv X S).symm.trans <|
      ((finiteProjectiveModules R).ι.mapIso f).toLinearEquiv.trans
        (FiniteProjectiveModules.biprodLinearEquiv Y T)⟩,
    fun ⟨f⟩ => ⟨(finiteProjectiveModules R).fullyFaithfulι.preimageIso <|
      ((FiniteProjectiveModules.biprodLinearEquiv X S).trans <|
        f.trans (FiniteProjectiveModules.biprodLinearEquiv Y T).symm).toModuleIso⟩⟩

namespace SplitK0

/-- **Equality in projective `K₀` is stable equivalence.** Two finitely generated projective
`R`-modules have the same class in split `K₀` if and only if `P × Rⁿ ≃ₗ[R] Q × Rⁿ` for some `n`. -/
theorem of_eq_of_iff_stableEquivalent {P Q : (finiteProjectiveModules R).FullSubcategory} :
    of.{u} P = of.{u} Q ↔ StableEquivalent R P.obj Q.obj := by
  rw [of_eq_of_iff, stableEquivalent_iff]
  constructor
  · rintro ⟨T, h⟩
    obtain ⟨e⟩ := nonempty_biprod_iso_biprod_iff.1 h
    obtain ⟨N, n, ⟨iso⟩⟩ := FiniteProjectiveModules.exists_biprod_iso_fin T
    let c : (T.obj × N.obj) ≃ₗ[R] (Fin n → R) :=
      (FiniteProjectiveModules.biprodLinearEquiv T N).symm.trans
        (((finiteProjectiveModules R).ι.mapIso iso ≪≫
          eqToIso (FiniteProjectiveModules.finFreeObj_obj R n)).toLinearEquiv)
    -- Enlarge the common summand `T` to the finite free module `T × N ≃ₗ[R] Rⁿ`.
    exact ⟨n, ⟨((LinearEquiv.refl R P.obj).prodCongr c.symm).trans <|
      (LinearEquiv.prodAssoc R P.obj T.obj N.obj).symm.trans <|
      (e.prodCongr (LinearEquiv.refl R N.obj)).trans <|
      (LinearEquiv.prodAssoc R Q.obj T.obj N.obj).trans <| (LinearEquiv.refl R Q.obj).prodCongr c⟩⟩
  · rintro ⟨n, h⟩
    exact ⟨FiniteProjectiveModules.of R (Fin n → R), nonempty_biprod_iso_biprod_iff.2 h⟩

/-- **Classes of finite free modules in projective `K₀`.** If `Q ≃ₗ[R] Rⁿ`, then a finitely
generated projective module `P` has the class of `Q` in split `K₀` if and only if
`P × Rᵏ ≃ₗ[R] Rⁿ⁺ᵏ` for some `k`. -/
theorem of_eq_of_iff_exists_prod_linearEquiv_fin
    {P Q : (finiteProjectiveModules R).FullSubcategory} {n : ℕ} (e : Q.obj ≃ₗ[R] (Fin n → R)) :
    of.{u} P = of.{u} Q ↔ ∃ k : ℕ, Nonempty ((P.obj × (Fin k → R)) ≃ₗ[R] (Fin (n + k) → R)) := by
  rw [of_eq_of_iff_stableEquivalent, ← stableEquivalent_fin_fun_iff]
  exact ⟨fun h => h.trans (.of_equiv e), fun h => h.trans (.of_equiv e.symm)⟩

end SplitK0

namespace FiniteProjectiveModules

section ClassOf

variable (Λ : Type u) [Ring Λ]
  (M : Type u) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] [Module.Projective Λ M]
  {N : Type u} [AddCommGroup N] [Module Λ N] [Module.Finite Λ N] [Module.Projective Λ N]

/-- The class `[M] - n[Λ]` of a finitely generated projective `Λ`-module `M` in the split `K₀` of
finitely generated projective `Λ`-modules. For a locally free `Λ`-lattice of rank `n` over a
Dedekind domain `A` with `¬IsField A`, this is its class in the locally free class group. -/
noncomputable def classOf (n : ℕ) : SplitK0.{u} (finiteProjectiveModules Λ).FullSubcategory :=
  SplitK0.of.{u} (of Λ M) - n • SplitK0.of.{u} (of Λ Λ)

theorem classOf_def (n : ℕ) :
    classOf Λ M n = SplitK0.of.{u} (of Λ M) - n • SplitK0.of.{u} (of Λ Λ) :=
  (rfl)

variable {Λ M}

/-- Isomorphic modules have the same class. -/
theorem classOf_congr (e : M ≃ₗ[Λ] N) (n : ℕ) : classOf Λ M n = classOf Λ N n := by
  rw [classOf, classOf, SplitK0.of_congr.{u} (X := of Λ M) (Y := of Λ N)
    (ObjectProperty.isoMk _ e.toModuleIso)]

/-- **Stably free classes.** The class `[M] - n[Λ]` vanishes if and only if `M` is stably free of
rank `n`: `M × Λᵏ ≃ Λⁿ⁺ᵏ` for some `k`. -/
theorem classOf_eq_zero_iff (n : ℕ) :
    classOf Λ M n = 0 ↔ ∃ k : ℕ, Nonempty ((M × (Fin k → Λ)) ≃ₗ[Λ] (Fin (n + k) → Λ)) := by
  rw [classOf, sub_eq_zero, ← SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := of Λ (Fin n → Λ))
    (.refl _ _) (.refl _ _)]
  exact SplitK0.of_eq_of_iff_exists_prod_linearEquiv_fin (.refl _ _)

/-- Two finitely generated projective modules have the same class in the same rank if and only if
they are stably equivalent. -/
theorem classOf_eq_classOf_iff (n : ℕ) :
    classOf Λ M n = classOf Λ N n ↔ StableEquivalent Λ M N := by
  rw [classOf, classOf, sub_left_inj]
  exact SplitK0.of_eq_of_iff_stableEquivalent

/-- The class of a product is the sum of the classes, the ranks adding. -/
theorem classOf_prod (n m : ℕ) : classOf Λ (M × N) (n + m) = classOf Λ M n + classOf Λ N m := by
  rw [classOf, classOf, classOf, SplitK0.of_eq_add_of_linearEquiv_prod (X := of Λ (M × N))
    (P := of Λ M) (Q := of Λ N) (.refl _ _), add_nsmul]
  abel

variable (Λ) in
/-- The class of the free module `Λⁿ` in rank `n` vanishes. -/
@[simp]
theorem classOf_free (n : ℕ) : classOf Λ (Fin n → Λ) n = 0 := by
  rw [classOf, sub_eq_zero]
  exact SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := of Λ (Fin n → Λ)) (R' := of Λ Λ)
    (.refl _ _) (.refl _ _)

/-- Extension of scalars on split `K₀` sends `[M] - n[Λ]` to `[Λ' ⊗_Λ M] - n[Λ']`, for every
finitely generated projective `Λ`-module `M`. -/
@[simp]
theorem map_extendScalars_classOf {Λ' : Type u} [Ring Λ'] (f : Λ →+* Λ') (n : ℕ) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars (classOf Λ M n) =
      classOf Λ' (BalancedExtension f M) n := by
  rw [classOf_def, classOf_def, map_sub, map_nsmul,
    SplitK0.map_of, SplitK0.map_of,
    SplitK0.of_extendScalars_obj (Q := of Λ' (BalancedExtension f M)) (.refl _ _),
    SplitK0.of_extendScalars_obj (Q := of Λ' Λ') (BalancedExtension.rid f)]

end ClassOf

end FiniteProjectiveModules

end TauCeti
