/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Scalar extension of linear-map spaces

For a finite projective source module, extending the scalars of the space of linear maps is the
same as taking linear maps between the scalar-extended modules: if `P` and `Q` are base changes
of `M` and `N` to `S`, then `P →ₗ[S] Q` is the base change of `M →ₗ[R] N`
(`IsBaseChange.linearMapLeftRight_of_projective`). Mathlib proves this for a finite free source
(`IsBaseChange.linearMapLeftRight`); a finite projective module is a retract of a finite free one,
and the comparison map is natural in the source, so the free case passes to retracts.

This file also identifies Mathlib's `LinearMap.baseChangeHom` as the scalar-extension map, so
`IsBaseChange.equiv` supplies the comparison equivalence and `IsBaseChange.equiv_tmul` evaluates
it on pure tensors.
-/

public section

open TensorProduct

namespace IsBaseChange

variable {R S M N P Q : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P]
  [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]

/-- **Linear maps out of a finite projective module commute with base change.** If `α : M → P`
and `β : N → Q` exhibit `P` and `Q` as the base changes of `M` and `N` to `S`, and `M` is finite
projective, then `P →ₗ[S] Q` is the base change of `M →ₗ[R] N`, through the map sending `g` to the
unique `S`-linear map `P → Q` extending `β ∘ g`. -/
theorem linearMapLeftRight_of_projective [Module.Finite R M] [Module.Projective R M]
    {α : M →ₗ[R] P} (j : IsBaseChange S α) {β : N →ₗ[R] Q} (k : IsBaseChange S β) :
    IsBaseChange S (linearMapLeftRightHom j β) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  set F := Fin n → R
  have jF := TensorProduct.isBaseChange R F S
  -- `M` is a retract of the free module `F`, and `P` of its base change `S ⊗[R] F`.
  let pS : S ⊗[R] F →ₗ[S] P := LinearMap.liftBaseChange S (α ∘ₗ p)
  let iS : P →ₗ[S] S ⊗[R] F := j.lift (TensorProduct.mk R S F 1 ∘ₗ i)
  have hpiS (x : P) : pS (iS x) = x := by
    induction x using j.inductionOn with
    | tmul m => simp [pS, iS, j.lift_eq, ← LinearMap.comp_apply p i, hpi]
    | smul s x h => simp [h]
    | add x y hx hy => simp [hx, hy]
  -- The comparison maps for `M` and for `F`; the second is bijective since `F` is free.
  let ΦM := LinearMap.liftBaseChange S (linearMapLeftRightHom j β)
  let ΦF := LinearMap.liftBaseChange S (linearMapLeftRightHom jF β)
  have hΦF : Function.Bijective ΦF := by
    convert (jF.linearMapLeftRight k).equiv.bijective using 1
    funext x
    induction x with
    | tmul s y => simp [ΦF, IsBaseChange.equiv_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  -- The comparison maps commute with composition with the retraction and the section.
  have hp (x : M →ₗ[R] N) : linearMapLeftRightHom jF β (x ∘ₗ p) =
      linearMapLeftRightHom j β x ∘ₗ pS := by
    apply jF.algHom_ext
    intro v
    rw [linearMapLeftRightHom_comp_apply]
    simp [pS, linearMapLeftRightHom_comp_apply]
  have hi (y : F →ₗ[R] N) : linearMapLeftRightHom j β (y ∘ₗ i) =
      linearMapLeftRightHom jF β y ∘ₗ iS := by
    apply j.algHom_ext
    intro m
    rw [linearMapLeftRightHom_comp_apply]
    simp only [LinearMap.comp_apply, iS, j.lift_eq]
    exact (linearMapLeftRightHom_comp_apply jF β y (i m)).symm
  have ha (z : S ⊗[R] (M →ₗ[R] N)) :
      ΦF ((LinearMap.lcomp R N p).baseChange S z) = ΦM z ∘ₗ pS := by
    induction z with
    | tmul s x => simp [ΦF, ΦM, ← hp, LinearMap.smul_comp, LinearMap.lcomp_apply']
    | add x y hx hy => simp [hx, hy, LinearMap.add_comp]
  have hb (z : S ⊗[R] (F →ₗ[R] N)) :
      ΦM ((LinearMap.lcomp R N i).baseChange S z) = ΦF z ∘ₗ iS := by
    induction z with
    | tmul s y => simp [ΦF, ΦM, ← hi, LinearMap.smul_comp, LinearMap.lcomp_apply']
    | add x y hx hy => simp [hx, hy, LinearMap.add_comp]
  have hc (z : S ⊗[R] (M →ₗ[R] N)) :
      (LinearMap.lcomp R N i).baseChange S ((LinearMap.lcomp R N p).baseChange S z) = z := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have : LinearMap.lcomp R N i ∘ₗ LinearMap.lcomp R N p = LinearMap.id := by
      ext x : 1
      simp [LinearMap.lcomp_apply', LinearMap.comp_assoc, hpi]
    simp [this]
  have hd (g : P →ₗ[S] Q) : (g ∘ₗ pS) ∘ₗ iS = g := by
    ext x
    simp [hpiS]
  -- Hence `ΦM` is a retract of the bijection `ΦF`, so it is bijective.
  refine of_equiv (LinearEquiv.ofBijective ΦM ⟨fun z z' h ↦ ?_, fun g ↦ ?_⟩) fun x ↦
    (LinearMap.liftBaseChange_tmul _ _ _ _).trans (one_smul S _)
  · rw [← hc z, ← hc z', hΦF.1 ((ha z).trans (h ▸ (ha z').symm))]
  · obtain ⟨z, hz⟩ := hΦF.2 (g ∘ₗ pS)
    exact ⟨(LinearMap.lcomp R N i).baseChange S z, by rw [hb, hz, hd]⟩

end IsBaseChange

namespace LinearMap

/-- Linear maps out of a finite projective module commute with scalar extension of both
modules. -/
theorem isBaseChange_baseChangeHom (R A M N : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module.Projective R M] [Module.Finite R M]
    [AddCommMonoid N] [Module R N] :
    IsBaseChange A (baseChangeHom R A M N) := by
  convert! (TensorProduct.isBaseChange R M A).linearMapLeftRight_of_projective
    (TensorProduct.isBaseChange R N A) using 1
  ext f m
  exact (IsBaseChange.linearMapLeftRightHom_comp_apply (TensorProduct.isBaseChange R M A)
    ((TensorProduct.mk R A N) 1) f m).symm

end LinearMap
