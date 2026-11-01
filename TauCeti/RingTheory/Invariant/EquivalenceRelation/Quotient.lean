/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import TauCeti.RingTheory.Invariant.EquivalenceRelation.Local

/-!
# The quotient of an affine scheme by a finite free equivalence relation

Let `s = algebraMap A B` and `t : A →+* B` define an equivalence relation `Spec B ⇉ Spec A`
(`RingHom.IsSpecEquivRel`) with `B` finite free over `A` through `s`, and let
`C = {a : s a = t a}` be its ring of invariants. This file proves that `Spec A ⟶ Spec C` is the
quotient of `Spec A` by the relation, as in SGA 3, Exposé V, Théorème 4.1, for relations which are
finite free, rather than only finite locally free, over `Spec A`:

* `A` is a finite, finitely presented, projective and faithfully flat `C`-module
  (`RingHom.IsSpecEquivRel.finite`, `RingHom.IsSpecEquivRel.finitePresentation`,
  `RingHom.IsSpecEquivRel.projective`, `RingHom.IsSpecEquivRel.faithfullyFlat`), so that
  `Spec A ⟶ Spec C` is finite locally free and surjective;
* the map `A ⊗[C] A → B`, `x ⊗ y ↦ s x * t y`, is an isomorphism of `A`-algebras
  (`RingHom.IsSpecEquivRel.bijective_tensorProductMap`), so that the relation is the kernel pair
  `Spec A ×_{Spec C} Spec A` of the quotient map.

No hypothesis is made on `C`. The case of a local ring of invariants is
`TauCeti.RingTheory.Invariant.EquivalenceRelation.Local`, and the general case reduces to it by
localization at the maximal ideals `P` of `C`. Base change along the flat map `C → C_P` gives the
relation `Spec (A' ⊗[A] B) ⇉ Spec A'` with `A' = C_P ⊗[C] A`, which is again finite free, and
whose ring of invariants is `C_P` because invariants commute with flat base change
(`RingHom.IsSpecEquivRel.exists_baseChange_ringEquiv_eqLocus`). By the local case `A'` has a
basis `aᵢ` over `C_P` whose images `t' aᵢ` form a basis of `A' ⊗[A] B` over `A'`. So `A'` is free
over `C_P`, and the base change of `A ⊗[C] A → B` along `C → C_P`, which is
`A' ⊗[C_P] A' → A' ⊗[A] B`, carries the basis `1 ⊗ aᵢ` to the basis `t' aᵢ` and is bijective
(`Algebra.TensorProduct.lift_bijective_of_basis`). Flatness and bijectivity are local at the
maximal ideals of `C`. Since the points of `Spec C` are the orbits of the relation
(`RingHom.IsSpecEquivRel.comap_subtype_eqLocus_surjective`), `A` is faithfully flat over `C`, and
finiteness and finite presentation descend from `A ⊗[C] A ≅ B` along `C → A`.

## Main results

* `RingHom.IsSpecEquivRel.bijective_tensorProductMap`: the map `A ⊗[C] A → B`,
  `x ⊗ y ↦ s x * t y`, is bijective, so that `A ⊗[C] A ≃ₐ[A] B`.
* `RingHom.IsSpecEquivRel.flat` and `RingHom.IsSpecEquivRel.faithfullyFlat`: `A` is faithfully
  flat over `C`.
* `RingHom.IsSpecEquivRel.finite`, `RingHom.IsSpecEquivRel.finitePresentation` and
  `RingHom.IsSpecEquivRel.projective`: `A` is a finite projective `C`-module.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, Théorème 4.1.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Finite flat groupoids, affine case*.
-/

public section

universe u

open TensorProduct

namespace RingHom.IsSpecEquivRel

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {t : A →+* B}

-- the map `A ⊗[C] A → B`, `x ⊗ y ↦ s x * t y`, as a linear map over the ring of invariants `C`
private noncomputable def tensorProductLinearMap :
    A ⊗[(algebraMap A B).eqLocus t] A →ₗ[(algebraMap A B).eqLocus t] B :=
  (tensorProductMap t).toLinearMap.restrictScalars _

private theorem tensorProductLinearMap_tmul (x y : A) :
    tensorProductLinearMap (t := t) (x ⊗ₜ y) = algebraMap A B x * t y :=
  tensorProductMap_tmul x y

variable (h : (algebraMap A B).IsSpecEquivRel t) [Module.Finite A B] [Module.Free A B]
include h

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
-- base change along a flat map `C → C'` to a local ring: `C' ⊗[C] A` is free over `C'`, and the
-- base change of `A ⊗[C] A → B` is bijective
private theorem free_and_bijective_baseChange (C' : Type u) [CommRing C']
    [Algebra ((algebraMap A B).eqLocus t) C'] [Module.Flat ((algebraMap A B).eqLocus t) C']
    [IsLocalRing C'] :
    Module.Free C' (C' ⊗[(algebraMap A B).eqLocus t] A) ∧
      Function.Bijective ((tensorProductLinearMap (t := t)).baseChange C') := by
  let A' := C' ⊗[(algebraMap A B).eqLocus t] A
  let B' := A' ⊗[A] B
  -- the base change `t' : A' → B'` of `t`, whose invariants are a copy `e` of the local ring `C'`
  obtain ⟨t', e, h', ht₁, ht₂, he⟩ := h.exists_baseChange_ringEquiv_eqLocus C'
  have : Nontrivial ((algebraMap A' B').eqLocus t') := e.symm.toEquiv.nontrivial
  have : IsLocalRing ((algebraMap A' B').eqLocus t') := .of_surjective' e.toRingHom e.surjective
  -- a basis `aᵢ` of `A'` over `C'` whose images `t' aᵢ` form a basis of `B'` over `A'`
  obtain ⟨b', a', hb'⟩ := h'.exists_basis_eq_apply
  let bA' : Module.Basis _ C' A' := (h'.basis b' hb').mapCoeffs e.symm fun c x ↦ by
    rw [Algebra.smul_def, Subring.smul_def, smul_eq_mul, ← he, e.apply_symm_apply]
  refine ⟨.of_basis bA', ?_⟩
  -- so `ψ : A' ⊗[C'] A' → B'`, `x ⊗ y ↦ s' x * t' y`, which carries the basis `1 ⊗ aᵢ` of
  -- `A' ⊗[C'] A'` over `A'` to the basis `t' aᵢ` of `B'`, is bijective
  let u : A' →ₐ[C'] B' := AlgHom.mk t' fun c ↦ by
    rw [IsScalarTower.algebraMap_apply C' A' B']
    exact congr($ht₂ c)
  let ψ := Algebra.TensorProduct.lift (Algebra.ofId A' B') u fun _ _ ↦ .all _ _
  have hψ : Function.Bijective ψ :=
    Algebra.TensorProduct.lift_bijective_of_basis u bA' b' fun i ↦ by simp [u, bA', hb']
  -- through `C' ⊗[C] (A ⊗[C] A) ≅ A' ⊗[C'] A'` and `B' ≅ C' ⊗[C] B`, the base change of
  -- `A ⊗[C] A → B` is `ψ`
  let eB := Algebra.IsPushout.cancelBaseChange ((algebraMap A B).eqLocus t) C' A A' B
  let eT := AlgebraTensorModule.distribBaseChange ((algebraMap A B).eqLocus t) C' A A
  have key (c : C') (x y : A) :
      eB.symm (c ⊗ₜ (algebraMap A B x * t y)) = ψ (eT (c ⊗ₜ (x ⊗ₜ y))) := by
    have hy : t' (1 ⊗ₜ y) = algebraMap B B' (t y) := congr($ht₁ y)
    have hx : x • algebraMap C' A' c = c ⊗ₜ x := by
      rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      simp
    simp only [eB, eT, ψ, u, Algebra.IsPushout.cancelBaseChange_symm_tmul,
      AlgebraTensorModule.distribBaseChange_tmul, Algebra.TensorProduct.lift_tmul,
      Algebra.ofId_apply, AlgHom.coe_mk, hy]
    rw [← Algebra.smul_def, ← smul_tmul, hx, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp
  have hcomp (z : C' ⊗[(algebraMap A B).eqLocus t] (A ⊗[(algebraMap A B).eqLocus t] A)) :
      (tensorProductLinearMap (t := t)).baseChange C' z = eB (ψ (eT z)) := by
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul c w =>
      induction w using TensorProduct.inductionOn with
      | add w₁ w₂ h₁ h₂ => simp only [tmul_add, map_add, h₁, h₂]
      | tmul x y =>
        rw [eq_comm, ← LinearEquiv.eq_symm_apply, LinearMap.baseChange_tmul,
          tensorProductLinearMap_tmul, key]
  rw [show ⇑((tensorProductLinearMap (t := t)).baseChange C') = eB ∘ ψ ∘ eT from funext hcomp]
  exact eB.bijective.comp (hψ.comp eT.bijective)

/-- **The quotient map is flat.** If `Spec B ⇉ Spec A` is an equivalence relation with `B` finite
free over `A` through `s`, then `A` is flat over the ring of invariants `C = {a : s a = t a}`. -/
theorem flat : Module.Flat ((algebraMap A B).eqLocus t) A :=
  Module.flat_of_isLocalized_maximal _ A
    (fun P _ ↦ Localization.AtPrime P ⊗[(algebraMap A B).eqLocus t] A)
    (fun P _ ↦ TensorProduct.mk _ (Localization.AtPrime P) A 1) fun P _ ↦
      have := (h.free_and_bijective_baseChange (Localization.AtPrime P)).1
      .trans _ (Localization.AtPrime P) _

/-- **The quotient map is faithfully flat.** If `Spec B ⇉ Spec A` is an equivalence relation with
`B` finite free over `A` through `s`, then `A` is faithfully flat over the ring of invariants
`C = {a : s a = t a}`. -/
theorem faithfullyFlat : Module.FaithfullyFlat ((algebraMap A B).eqLocus t) A :=
  have := h.flat
  .of_comap_surjective h.comap_subtype_eqLocus_surjective

/-- **The relation is the kernel pair of the quotient map.** If `Spec B ⇉ Spec A` is an
equivalence relation with `B` finite free over `A` through `s`, and `C = {a : s a = t a}` is the
ring of invariants, then the map `A ⊗[C] A → B`, `x ⊗ y ↦ s x * t y`, is bijective, so that it is
an isomorphism of `A`-algebras `A ⊗[C] A ≃ₐ[A] B` (`AlgEquiv.ofBijective`). -/
theorem bijective_tensorProductMap : Function.Bijective (tensorProductMap t) := by
  -- bijectivity is local at the maximal ideals `P` of `C`, and the localization of the map at `P`
  -- is its base change along `C → C_P`
  change Function.Bijective (tensorProductLinearMap (t := t))
  refine bijective_of_isLocalized_maximal _
    (fun P _ ↦ TensorProduct.mk _ (Localization.AtPrime P) _ 1) _
    (fun P _ ↦ TensorProduct.mk _ (Localization.AtPrime P) B 1) tensorProductLinearMap
    fun P _ ↦ ?_
  have hmap : IsLocalizedModule.map P.primeCompl
      (TensorProduct.mk _ (Localization.AtPrime P) (A ⊗[(algebraMap A B).eqLocus t] A) 1)
      (TensorProduct.mk _ (Localization.AtPrime P) B 1) tensorProductLinearMap =
        (tensorProductLinearMap.baseChange (Localization.AtPrime P)).restrictScalars _ := by
    refine IsLocalizedModule.linearMap_ext P.primeCompl
      (TensorProduct.mk _ (Localization.AtPrime P) _ 1)
      (TensorProduct.mk _ (Localization.AtPrime P) B 1) (LinearMap.ext fun z ↦ ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, IsLocalizedModule.map_apply]
    simp
  rw [hmap]
  exact (h.free_and_bijective_baseChange (Localization.AtPrime P)).2

/-- **The quotient map is finite.** If `Spec B ⇉ Spec A` is an equivalence relation with `B`
finite free over `A` through `s`, then `A` is a finite module over the ring of invariants
`C = {a : s a = t a}`. -/
theorem finite : Module.Finite ((algebraMap A B).eqLocus t) A := by
  have := h.faithfullyFlat
  let e := AlgEquiv.ofBijective _ h.bijective_tensorProductMap
  have : Module.Finite A (A ⊗[(algebraMap A B).eqLocus t] A) := .equiv e.symm.toLinearEquiv
  exact .of_finite_tensorProduct_of_faithfullyFlat A

/-- **The quotient map is finitely presented.** If `Spec B ⇉ Spec A` is an equivalence relation
with `B` finite free over `A` through `s`, then `A` is a finitely presented module over the ring of
invariants `C = {a : s a = t a}`. -/
theorem finitePresentation : Module.FinitePresentation ((algebraMap A B).eqLocus t) A := by
  have := h.faithfullyFlat
  have := h.finite
  let e := AlgEquiv.ofBijective _ h.bijective_tensorProductMap
  have : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  have : Algebra.FinitePresentation A (A ⊗[(algebraMap A B).eqLocus t] A) := .equiv e.symm
  have : Algebra.FinitePresentation ((algebraMap A B).eqLocus t) A :=
    .of_finitePresentation_tensorProduct_of_faithfullyFlat A
  exact .of_finite_of_finitePresentation _ _

/-- **The quotient map is finite locally free.** If `Spec B ⇉ Spec A` is an equivalence relation
with `B` finite free over `A` through `s`, then `A` is a projective module over the ring of
invariants `C = {a : s a = t a}`; it is also finite (`RingHom.IsSpecEquivRel.finite`). -/
theorem projective : Module.Projective ((algebraMap A B).eqLocus t) A :=
  have := h.flat
  have := h.finitePresentation
  Module.Flat.projective_of_finitePresentation

end RingHom.IsSpecEquivRel
