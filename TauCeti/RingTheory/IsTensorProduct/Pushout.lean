/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.RingTheory.TensorProduct.Maps

import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Algebra homomorphisms and ideals under pushout

Let `S'` be the pushout of `R → S` along `R → R'`, as expressed by `Algebra.IsPushout R S R' S'`.
Mathlib's `Algebra.pushoutDesc` describes the `R`-algebra homomorphisms out of `S'`. This file
describes the `R'`-algebra homomorphisms out of `S'`: they are determined by their restrictions to
`S`, and every `R`-algebra homomorphism out of `S` extends to one. It also describes the ring
homomorphisms out of `S'`, into a ring carrying no algebra structure: they are determined by their
restrictions to `S` and `R'`, and every pair of ring homomorphisms out of `S` and `R'` which agree
on `R` glues to one. It also records the naturality of `Algebra.IsPushout.cancelBaseChangeAlg` in
the coefficient algebra.

For an ideal of `R'`, its extension to the pushout `S'` is spanned over `S` by its image.
This identifies extension of ideals with extension of the underlying submodule.

## Main definitions

* `Algebra.IsPushout.lift f`: the `R'`-algebra homomorphism `S' →ₐ[R'] A` extending an
  `R`-algebra homomorphism `f : S →ₐ[R] A` along `S → S'`.
* `Algebra.IsPushout.liftRingHom x y h`: the ring homomorphism `S' →+* T` restricting to ring
  homomorphisms `x : S →+* T` and `y : R' →+* T` which agree on `R`.

## Main results

* `Algebra.IsPushout.lift_algebraMap`: `lift f` restricts to `f` on `S`.
* `Algebra.IsPushout.algHom_ext'`: `R'`-algebra homomorphisms out of `S'` agreeing on `S` are
  equal.
* `Algebra.IsPushout.ringHom_ext`: ring homomorphisms out of `S'` agreeing on `S` and on `R'` are
  equal.
* `Ideal.restrictScalars_map_eq_span`: the extension to `S'` of an ideal `J` of `R'` is the
  `S`-span of the image of `J`.
* `Module.Finite.of_isPushout`, `Module.Projective.of_isPushout`,
  `Algebra.FinitePresentation.of_isPushout`: finiteness, projectivity and finite presentation are
  stable under pushout.
* `Algebra.IsPushout.adjoin_image_eq_top`: generators of `S` over `R` map to generators of `S'`
  over `R'`; `Algebra.IsPushout.adjoin_zero_union_one_eq_top` is the case of generation in degrees
  `0` and `1` along a graded ring homomorphism.
* `Algebra.IsPushout.cancelBaseChangeAlg_symm_lTensor`: the isomorphism
  `S ⊗[R] T ≃ₐ[S] S' ⊗[R'] T` is natural in the `R'`-algebra `T`.
-/

public section

open scoped TensorProduct

namespace Algebra.IsPushout

section CommSemiring

variable {R S R' S' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring R'] [CommSemiring S']
  [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R R' S']
  [IsScalarTower R S S'] [h : IsPushout R S R' S']

section Lift

variable {A : Type*} [Semiring A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

variable (R') in
/-- The `R'`-algebra homomorphism out of the pushout `S'` extending an `R`-algebra homomorphism
`f : S →ₐ[R] A` along `S → S'`. -/
noncomputable def lift (f : S →ₐ[R] A) : S' →ₐ[R'] A :=
  { pushoutDesc S' f (IsScalarTower.toAlgHom R R' A) fun x y ↦ (Algebra.commutes y (f x)).symm with
    commutes' := pushoutDesc_right S' f _ _ }

/-- `lift R' f` restricts to `f` on `S`. -/
@[simp]
theorem lift_algebraMap (f : S →ₐ[R] A) (s : S) : lift R' f (algebraMap S S' s) = f s := by
  unfold lift
  exact pushoutDesc_left S' f _ _ s

/-- Two `R'`-algebra homomorphisms out of the pushout `S'` that agree on `S` are equal. -/
@[ext (iff := false)]
theorem algHom_ext' {f g : S' →ₐ[R'] A}
    (h : (f.restrictScalars R).comp (IsScalarTower.toAlgHom R S S') =
      (g.restrictScalars R).comp (IsScalarTower.toAlgHom R S S')) : f = g :=
  AlgHom.restrictScalars_injective R <| IsPushout.algHom_ext (R' := R') S' (by ext; simp) h

end Lift

section LiftRingHom

include h in
/-- Two ring homomorphisms out of the pushout `S'` that agree on `S` and on `R'` are equal. -/
theorem ringHom_ext {T : Type*} [Semiring T] {f g : S' →+* T}
    (hS : f.comp (algebraMap S S') = g.comp (algebraMap S S'))
    (hR' : f.comp (algebraMap R' S') = g.comp (algebraMap R' S')) : f = g := by
  ext x
  induction x using h.out.inductionOn with
  | tmul x => simpa using congr($hR' x)
  | smul s x hx => rw [Algebra.smul_def, map_mul, map_mul, hx, ← f.comp_apply, hS, g.comp_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {T : Type*} [CommSemiring T] (x : S →+* T) (y : R' →+* T)
  (hxy : x.comp (algebraMap R S) = y.comp (algebraMap R R'))

variable (S') in
/-- The ring homomorphism out of the pushout `S' = S ⊗[R] R'` restricting to ring homomorphisms
`x : S →+* T` and `y : R' →+* T` which agree on `R`. No algebra structure on `T` is involved. -/
noncomputable def liftRingHom : S' →+* T :=
  (Algebra.TensorProduct.liftRingHom x y hxy).comp (equiv R S R' S').symm.toRingEquiv.toRingHom

/-- `liftRingHom S' x y hxy` restricts to `x` on `S`. -/
@[simp]
theorem liftRingHom_algebraMap_left (s : S) :
    liftRingHom S' x y hxy (algebraMap S S' s) = x s := by
  simp [liftRingHom]

/-- `liftRingHom S' x y hxy` restricts to `y` on `R'`. -/
@[simp]
theorem liftRingHom_algebraMap_right (r : R') :
    liftRingHom S' x y hxy (algebraMap R' S' r) = y r := by
  simp [liftRingHom, equiv_symm_algebraMap_right]

end LiftRingHom

open Submodule in
include h in
/-- In a pushout `S' = S ⊗[R] R'`, the extension of an ideal `J` of `R'` is spanned over `S` by
the image of `J`. -/
theorem _root_.Ideal.restrictScalars_map_eq_span (J : Ideal R') :
    (Ideal.map (algebraMap R' S') J).restrictScalars S = span S (algebraMap R' S' '' J) := by
  refine le_antisymm (fun y hy ↦ ?_) (span_le.2 fun _ ⟨x, hx, hxy⟩ ↦ hxy ▸ J.mem_map_of_mem _ hx)
  -- the `S`-span of the image of `J` is stable under multiplication by `S'`
  have key (b : S') {y : S'} (hy : y ∈ span S (algebraMap R' S' '' J)) :
      b * y ∈ span S (algebraMap R' S' '' J) := by
    induction b using h.out.inductionOn with
    | tmul b =>
      induction hy using span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        exact subset_span ⟨b * x, J.mul_mem_left b hx, by simp⟩
      | zero => simp
      | add y z _ _ hy hz => simpa [mul_add] using add_mem hy hz
      | smul a y _ hy => simpa [mul_smul_comm] using smul_mem _ a hy
    | smul a b hb => simpa [smul_mul_assoc] using smul_mem _ a hb
    | add b c hb hc => simpa [add_mul] using add_mem hb hc
  induction hy using span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact subset_span ⟨x, hx, rfl⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul b y _ hy => exact key b hy

section Finiteness

variable (R S R' S')

/-- Finiteness as a module is stable under pushout: if `S` is a finite `R`-module, then the pushout
`S'` is a finite `R'`-module. -/
theorem _root_.Module.Finite.of_isPushout [Module.Finite R S] : Module.Finite R' S' := by
  have := IsPushout.symm (inferInstance : IsPushout R S R' S')
  exact Module.Finite.equiv (IsPushout.equiv R R' S S').toLinearEquiv

/-- Projectivity as a module is stable under pushout: if `S` is a projective `R`-module, then the
pushout `S'` is a projective `R'`-module. -/
theorem _root_.Module.Projective.of_isPushout [Module.Projective R S] :
    Module.Projective R' S' := by
  have := IsPushout.symm (inferInstance : IsPushout R S R' S')
  exact Module.Projective.of_equiv (IsPushout.equiv R R' S S').toLinearEquiv

end Finiteness

/-- Generators pass to the pushout: if `s` generates `S` as an `R`-algebra, then its image
generates the pushout `S'` as an `R'`-algebra. -/
theorem adjoin_image_eq_top {s : Set S} (hs : Algebra.adjoin R s = ⊤) :
    Algebra.adjoin R' (algebraMap S S' '' s) = ⊤ := by
  have := h.symm
  -- `S'` is `R' ⊗[R] S`, which is generated by the elements `1 ⊗ x` for `x ∈ s`.
  have he : ⇑(equiv R R' S S') ∘ ((1 : R') ⊗ₜ[R] ·) = algebraMap S S' :=
    funext fun _ ↦ by simp [equiv_tmul]
  rw [← he, Set.image_comp, ← AlgEquiv.coe_toAlgHom, ← AlgHom.map_adjoin,
    Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := R') s hs, Algebra.map_top,
    AlgHom.range_eq_top]
  exact (equiv R R' S S').surjective

/-- Generation in degrees `0` and `1` passes to the pushout along a graded ring homomorphism: if
`S` is generated over `R` by its homogeneous elements of degrees `0` and `1`, and `S → S'`
underlies a graded ring homomorphism, then `S'` is generated over `R'` by its homogeneous elements
of degrees `0` and `1`. -/
theorem adjoin_zero_union_one_eq_top {σ τ : Type*} [SetLike σ S] [SetLike τ S'] {𝒜 : ℕ → σ}
    {ℬ : ℕ → τ} (φ : 𝒜 →+*ᵍ ℬ) (hφ : ∀ x, φ x = algebraMap S S' x)
    (hs : Algebra.adjoin R ((𝒜 0 : Set S) ∪ 𝒜 1) = ⊤) :
    Algebra.adjoin R' ((ℬ 0 : Set S') ∪ ℬ 1) = ⊤ := by
  refine top_unique ((adjoin_image_eq_top hs).ge.trans (Algebra.adjoin_mono ?_))
  rintro _ ⟨y, hy, rfl⟩
  rw [← hφ]
  exact hy.imp φ.map_mem φ.map_mem

end CommSemiring

section CommRing

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
  [Algebra R R'] [Algebra R' S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R R' S']
  [IsScalarTower R S S'] [IsPushout R S R' S']

variable (R S R' S') in
/-- Finite presentation is stable under pushout: if `S` is a finitely presented `R`-algebra, then
the pushout `S'` is a finitely presented `R'`-algebra. -/
theorem _root_.Algebra.FinitePresentation.of_isPushout [FinitePresentation R S] :
    FinitePresentation R' S' := by
  have := IsPushout.symm (inferInstance : IsPushout R S R' S')
  exact FinitePresentation.equiv (IsPushout.equiv R R' S S')

end CommRing

section CancelBaseChange

variable {R S R' S' : Type*} [CommSemiring R] [CommSemiring S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra R S'] [Algebra S S']
  [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsPushout R S R' S']

variable (S') in
/-- The isomorphism `S ⊗[R] T ≃ₐ[S] S' ⊗[R'] T` is natural in the `R'`-algebra `T`. -/
theorem cancelBaseChangeAlg_symm_lTensor {T T' : Type*} [CommRing T] [Algebra R' T]
    [Algebra R T] [IsScalarTower R R' T] [CommRing T'] [Algebra R' T'] [Algebra R T']
    [IsScalarTower R R' T'] (g : T →ₐ[R'] T') (z : S ⊗[R] T) :
    (cancelBaseChangeAlg R S R' S' T').symm
        (Algebra.TensorProduct.lTensor (S := S) S (g.restrictScalars R) z) =
      Algebra.TensorProduct.lTensor (S := S') S' g ((cancelBaseChangeAlg R S R' S' T).symm z) := by
  induction z <;> simp [*]

end CancelBaseChange

end Algebra.IsPushout
