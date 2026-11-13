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

The file defines `TauCeti.FiniteProjectiveModules.classOf R M n = [M] - n[R]`, with
isomorphism invariance, stable-freeness and stable-equivalence criteria, additivity on products,
and vanishing on finite free modules. These classes measure the obstruction to stable freeness.

The file also records additivity on products of modules, `[P × Q] = [P] + [Q]` and
`[Rⁿ] = n[R]`, in the form consumed by classes `[M] - n[R]`.

## Main results

* `TauCeti.FiniteProjectiveModules.biprodLinearEquiv`: the underlying module of a biproduct
  of finite projective modules is linearly isomorphic to the product.
* `TauCeti.FiniteProjectiveModules.classOf_eq_zero_iff`: the class `[M] - n[R]` vanishes
  exactly when `M` is stably free of rank `n`.
* `TauCeti.FiniteProjectiveModules.classOf_eq_classOf_iff`: equality of classes in the same
  rank is stable equivalence.
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
noncomputable def FiniteProjectiveModules.biprodLinearEquiv
    (X Y : (finiteProjectiveModules R).FullSubcategory) :
    (X ⊞ Y).obj ≃ₗ[R] X.obj × Y.obj :=
  letI : PreservesBinaryBiproduct X Y (finiteProjectiveModules R).ι :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  (((finiteProjectiveModules R).ι.mapBiprod X Y).trans (ModuleCat.biprodIsoProd _ _)).toLinearEquiv

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

/-- **Additivity on products.** The class of a finitely generated projective module isomorphic to
a product `P × Q` is the sum of the classes of `P` and `Q`. -/
theorem of_eq_add_of_linearEquiv_prod {X P Q : (finiteProjectiveModules R).FullSubcategory}
    (e : X.obj ≃ₗ[R] (P.obj × Q.obj)) : of.{u} X = of.{u} P + of.{u} Q := by
  rw [← of_biprod]
  exact of_congr ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
    (e.trans (FiniteProjectiveModules.biprodLinearEquiv P Q).symm).toModuleIso)

/-- **Additivity on finite products.** The class of a finitely generated projective module
isomorphic to a finite product is the sum of the classes of the factors. -/
theorem of_eq_sum_of_linearEquiv_pi {ι : Type*} [Fintype ι]
    {X : (finiteProjectiveModules R).FullSubcategory}
    (P : ι → (finiteProjectiveModules R).FullSubcategory)
    (e : X.obj ≃ₗ[R] (i : ι) → (P i).obj) : of.{u} X = ∑ i, of.{u} (P i) := by
  obtain ⟨n, ⟨f⟩⟩ := Finite.exists_equiv_fin ι
  rw [← Equiv.sum_comp f.symm (fun i ↦ of.{u} (P i))]
  have := hasFiniteBiproducts_of_hasBinaryBiproducts
    (C := (finiteProjectiveModules R).FullSubcategory)
  rw [← of_biproduct.{u} (fun i ↦ P (f.symm i))]
  exact of_congr ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
    ((e.trans (LinearEquiv.piCongrLeft' R (fun i ↦ (P i).obj) f)).toModuleIso ≪≫
      (ModuleCat.biproductIsoPi fun i ↦ (P (f.symm i)).obj).symm ≪≫
      ((finiteProjectiveModules R).ι.mapBiproduct (fun i ↦ P (f.symm i))).symm))

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

namespace FiniteProjectiveModules

section ClassOf

variable (Λ : Type u) [Ring Λ]
  (M : Type u) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] [Module.Projective Λ M]
  {N : Type u} [AddCommGroup N] [Module Λ N] [Module.Finite Λ N] [Module.Projective Λ N]

/-- A finitely generated projective module as an object of the subcategory of finitely generated
projective modules. -/
private abbrev obj (P : Type u) [AddCommGroup P] [Module Λ P] [Module.Finite Λ P]
    [Module.Projective Λ P] : (finiteProjectiveModules Λ).FullSubcategory :=
  ⟨ModuleCat.of Λ P, finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩

/-- The class `[M] - n[Λ]` of a finitely generated projective `Λ`-module `M` in the split `K₀` of
finitely generated projective `Λ`-modules. For a locally free `Λ`-lattice of rank `n` over a
Dedekind domain `A` with `¬IsField A`, this is its class in the locally free class group. -/
noncomputable def classOf (n : ℕ) : SplitK0.{u} (finiteProjectiveModules Λ).FullSubcategory :=
  SplitK0.of ⟨ModuleCat.of Λ M, finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ -
    n • SplitK0.of ⟨ModuleCat.of Λ Λ, finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩

theorem classOf_def (n : ℕ) :
    classOf Λ M n =
      SplitK0.of ⟨ModuleCat.of Λ M, finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ -
        n • SplitK0.of
          ⟨ModuleCat.of Λ Λ, finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ :=
  (rfl)

variable {Λ M}

/-- Isomorphic modules have the same class. -/
theorem classOf_congr (e : M ≃ₗ[Λ] N) (n : ℕ) : classOf Λ M n = classOf Λ N n := by
  rw [classOf, classOf, SplitK0.of_congr.{u} (X := obj Λ M) (Y := obj Λ N)
    (ObjectProperty.isoMk _ e.toModuleIso)]

/-- **Stably free classes.** The class `[M] - n[Λ]` vanishes if and only if `M` is stably free of
rank `n`: `M × Λᵏ ≃ Λⁿ⁺ᵏ` for some `k`. -/
theorem classOf_eq_zero_iff (n : ℕ) :
    classOf Λ M n = 0 ↔ ∃ k : ℕ, Nonempty ((M × (Fin k → Λ)) ≃ₗ[Λ] (Fin (n + k) → Λ)) := by
  rw [classOf, sub_eq_zero, ← SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := obj Λ (Fin n → Λ))
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
  rw [classOf, classOf, classOf, SplitK0.of_eq_add_of_linearEquiv_prod (X := obj Λ (M × N))
    (P := obj Λ M) (Q := obj Λ N) (.refl _ _), add_nsmul]
  abel

/-- A module isomorphic to a finite product has the sum of the reduced classes of its factors,
with the ranks adding. -/
theorem classOf_eq_sum_of_linearEquiv_pi {ι : Type*} [Fintype ι] (P : ι → Type u)
    [∀ i, AddCommGroup (P i)] [∀ i, Module Λ (P i)] [∀ i, Module.Finite Λ (P i)]
    [∀ i, Module.Projective Λ (P i)] (e : M ≃ₗ[Λ] (i : ι) → P i) (n : ι → ℕ) :
    classOf Λ M (∑ i, n i) = ∑ i, classOf Λ (P i) (n i) := by
  simp only [classOf_def, SplitK0.of_eq_sum_of_linearEquiv_pi (X := obj Λ M)
    (fun i ↦ obj Λ (P i)) e, Finset.sum_sub_distrib, Finset.sum_smul]

variable (Λ) in
/-- The class of the free module `Λⁿ` in rank `n` vanishes. -/
@[simp]
theorem classOf_free (n : ℕ) : classOf Λ (Fin n → Λ) n = 0 := by
  rw [classOf, sub_eq_zero]
  exact SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := obj Λ (Fin n → Λ)) (R' := obj Λ Λ)
    (.refl _ _) (.refl _ _)

end ClassOf

end FiniteProjectiveModules

end TauCeti
