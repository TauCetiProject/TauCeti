/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Basic
public import TauCeti.Algebra.Category.FGModuleCat.Equivalence
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
public import TauCeti.Algebra.Category.ModuleCat.Equivalence
public import TauCeti.Algebra.Module.Generator
public import TauCeti.RingTheory.DominantDimension

/-!
# Morita invariance of the dominant dimension

An equivalence `F : ModuleCat A ≌ ModuleCat B` preserves the dominant dimension of objects
(`CategoryTheory.Equivalence.dominantDimension_functor_obj`), but it carries the regular module `A`
to a progenerator `P` of `B`, not to `B` itself. The dominant dimension of a module only goes up
under retracts and finite powers (`CategoryTheory.dominantDimension_le_of_retract`, which uses the
minimal injective coresolutions every module has, and
`TauCeti.ModuleCat.dominantDimension_le_dominantDimension_pi`). Since `B` is a retract of a finite
power of the generator `P`, and `P` is a retract of a finite power of `B`, the two have the same
dominant dimension, so Morita equivalent algebras have the same dominant dimension
(`IsMoritaEquivalent.dominantDimension_eq`). No finiteness of the algebras is needed.

## Main results

* `TauCeti.ModuleCat.dominantDimension_le_dominantDimension_pi`: `dom.dim M ≤ dom.dim Mⁿ`.
* `IsMoritaEquivalent.dominantDimension_eq`: **Morita equivalent algebras have the same dominant
  dimension.**

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §II.2 and §VI.5.
-/

public section

universe u v

open CategoryTheory Limits

namespace TauCeti

variable {Γ : Type u} [Ring Γ]

/-- **Finite powers.** The dominant dimension of a finite power `Mⁿ` of a module is at least that
of `M`; for `n = 0` the power is zero, of dominant dimension `⊤`. -/
theorem ModuleCat.dominantDimension_le_dominantDimension_pi (M : ModuleCat.{v} Γ) (n : ℕ) :
    CategoryTheory.dominantDimension M ≤
      CategoryTheory.dominantDimension (ModuleCat.of Γ (Fin n → M)) := by
  induction n with
  | zero =>
    have hZ : IsZero (ModuleCat.of Γ (Fin 0 → M)) := ModuleCat.isZero_of_subsingleton _
    have := hZ.projective
    have := hZ.injective
    rw [dominantDimension_eq_top (ModuleCat.of Γ (Fin 0 → M))]
    exact le_top
  | succ n ih =>
    let e : ModuleCat.of Γ (Fin (n + 1) → M) ≅ M ⊞ ModuleCat.of Γ (Fin n → M) :=
      (Fin.consLinearEquiv Γ fun _ : Fin (n + 1) ↦ M).symm.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd M (ModuleCat.of Γ (Fin n → M))).symm
    rw [dominantDimension_eq_of_iso e]
    exact (le_min le_rfl ih).trans (min_dominantDimension_le_dominantDimension_biprod _ _)

/-- The regular module is a retract of a finite power of a generator. -/
private theorem exists_retract_pi_of_isGenerator (M : ModuleCat.{u} Γ)
    [Module.IsGenerator Γ M] : ∃ n : ℕ, Nonempty (Retract (ModuleCat.of Γ Γ)
      (ModuleCat.of Γ (Fin n → M))) := by
  obtain ⟨n, φ, m, h⟩ := Module.isGenerator_iff_exists_sum_eq_one.1 ‹Module.IsGenerator Γ M›
  let i : Γ →ₗ[Γ] (Fin n → M) := LinearMap.pi fun j ↦ LinearMap.toSpanSingleton Γ M (m j)
  let r : (Fin n → M) →ₗ[Γ] Γ := ∑ j, φ j ∘ₗ LinearMap.proj j
  refine ⟨n, ⟨⟨ModuleCat.ofHom i, ModuleCat.ofHom r, ?_⟩⟩⟩
  ext
  simp [i, r, h]

/-- A finitely generated projective module is a retract of a finite free module. -/
private theorem exists_retract_pi_of_finite_projective (M : ModuleCat.{u} Γ) [Module.Finite Γ M]
    [Module.Projective Γ M] :
    ∃ k : ℕ, Nonempty (Retract M (ModuleCat.of Γ (Fin k → Γ))) := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' Γ M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact ⟨k, ⟨⟨ModuleCat.ofHom s, ModuleCat.ofHom f, by ext; simp [hs]⟩⟩⟩

end TauCeti

open TauCeti in
/-- **Morita equivalent algebras have the same dominant dimension.** An equivalence of module
categories carries the regular module `A` to a progenerator `P` of `B`; `B` is a retract of a finite
power of `P` and `P` a retract of a finite power of `B`, and the dominant dimension of a module only
goes up under retracts and finite powers. -/
theorem IsMoritaEquivalent.dominantDimension_eq {R : Type*} [CommSemiring R] {A B : Type u}
    [Ring A] [Ring B] [Algebra R A] [Algebra R B] (h : IsMoritaEquivalent R A B) :
    dominantDimension A = dominantDimension B := by
  obtain ⟨e⟩ := h.cond
  let F : ModuleCat.{u} A ≌ ModuleCat.{u} B := e.eqv
  let P : ModuleCat.{u} B := F.functor.obj (ModuleCat.of A A)
  have hdd : dominantDimension A = CategoryTheory.dominantDimension P := by
    rw [dominantDimension_eq_dominantDimension_of]
    exact (F.dominantDimension_functor_obj _).symm
  have : Module.Finite B P := (F.finite_functor_obj_iff _).2 inferInstance
  have : Module.Projective B P := (F.projective_functor_obj_iff _).2 inferInstance
  have : Module.IsGenerator B P := by
    exact (congrArg (fun X : ModuleCat.{u} B ↦ Module.IsGenerator B X)
      (F.finiteModulesEquivalence_functor_obj_obj (FGModuleCat.of A A))).mp
      F.finiteModulesEquivalence.isGenerator_functor_obj_regular
  rw [hdd, dominantDimension_eq_dominantDimension_of]
  refine le_antisymm ?_ ?_
  · obtain ⟨n, ⟨r⟩⟩ := exists_retract_pi_of_isGenerator P
    exact (ModuleCat.dominantDimension_le_dominantDimension_pi P n).trans
      (dominantDimension_le_of_retract r (ModuleCat.exists_isMinimalInjectiveCoresolution _))
  · obtain ⟨k, ⟨r⟩⟩ := exists_retract_pi_of_finite_projective P
    exact (ModuleCat.dominantDimension_le_dominantDimension_pi (ModuleCat.of B B) k).trans
      (dominantDimension_le_of_retract r (ModuleCat.exists_isMinimalInjectiveCoresolution _))
