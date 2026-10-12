/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Homomorphisms from a constant monoid

Let `A` be a finite monoid and `R` a commutative ring, and let `coordinateRing R A`
(`TauCeti.ConstantGroup.coordinateRing`) be the coordinate ring of the constant monoid `A_R`,
whose underlying algebra is the functions `A → R`. This file proves, for every `R`-bialgebra `H`,
that restricting along the evaluations at the elements of `A` is a bijection

  `(H →ₐc[R] coordinateRing R A) ≃ (A →* WithConv (H →ₐ[R] R))`

(`TauCeti.ConstantGroup.bialgHomEquiv`). No finiteness, flatness or commutativity hypothesis is
made on `H`, and no connectedness hypothesis is made on `R`; `R` is only required to be a
commutative ring (a commutative semiring for `TauCeti.ConstantGroup.mapDomain_comp_bijective`).

When `H` is commutative, so that `G = Spec H` is an affine monoid scheme over `R`, this is the
universal property of the constant monoid scheme `A_R = ⨆_{a ∈ A} Spec R`: a homomorphism of monoid
schemes `A_R → G` over `Spec R` is the same as a monoid homomorphism `A →* G(R)`. Over a
disconnected base `A_R` is still a disjoint union of copies of the base, so homomorphisms from it
are still indexed by `A`.

The bijection is proved for every bialgebra `C` together with a monoid homomorphism
`p : A →* WithConv (C →ₐ[R] R)` whose values identify `C` with the functions `A → R`
(`TauCeti.ConstantGroup.mapDomain_comp_bijective`). Besides `coordinateRing R A` with its
evaluations, this applies to any base change of it, which is how Katz–Mazur `A`-generators over a
varying base are read off a scheme of homomorphisms from the constant group `A_R` of a finite
group `A`.

## Main results

* `TauCeti.ConstantGroup.mapDomain_comp_bijective`: if the points `p a` identify `C` with the
  functions on `A`, then a bialgebra homomorphism `H →ₐc[R] C` is the same as a monoid
  homomorphism from `A` to the `R`-points `WithConv (H →ₐ[R] R)` of `H`.
* `TauCeti.ConstantGroup.bialgHomEquiv`: bialgebra homomorphisms `H →ₐc[R] coordinateRing R A`
  are the monoid homomorphisms `A →* WithConv (H →ₐ[R] R)`.
* `TauCeti.ConstantGroup.pi_toPoints_bijective` and
  `TauCeti.ConstantGroup.pi_pointsBaseChange_toPoints_bijective`: the evaluations identify
  `coordinateRing R A`, and each of its base changes `T ⊗[R] coordinateRing R A`, with the
  functions on `A`, so `mapDomain_comp_bijective` applies to them.
* `TauCeti.ConstantGroup.pointsOfBialgHomEquiv`: after base change to an `R`-algebra `T`,
  `T`-bialgebra homomorphisms `T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A` are the monoid
  homomorphisms `A →* WithConv (T ⊗[R] H →ₐ[T] T)`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §1.10.
-/

public section

open scoped TensorProduct

namespace TauCeti.ConstantGroup

section Recognition

variable {R : Type*} [CommSemiring R] {H C : Type*} [Semiring H] [Bialgebra R H] [Semiring C]
  [Bialgebra R C] {A : Type*} [Monoid A] [Finite A] {p : A →* WithConv (C →ₐ[R] R)}

/-- **Recognition of constant monoids.** Let `p : A →* WithConv (C →ₐ[R] R)` be a monoid
homomorphism from a finite monoid to the `R`-points of `C` whose values identify `C` with the
functions on `A`, that is, `c ↦ (a ↦ p a c)` is bijective. Then for every bialgebra `H`, a
bialgebra homomorphism `g : H →ₐc[R] C` is determined by, and can be prescribed through, the monoid
homomorphism `a ↦ p a ∘ g` from `A` to the `R`-points of `H`. -/
theorem mapDomain_comp_bijective
    (hp : Function.Bijective (AlgHom.pi fun a ↦ (p a).ofConv)) :
    Function.Bijective fun g : H →ₐc[R] C ↦ (AlgHom.mapDomain g).comp p := by
  refine ⟨fun g g' hgg' ↦ BialgHom.ext fun x ↦ hp.1 <| funext fun a ↦ ?_, fun φ ↦ ?_⟩
  · simpa using DFunLike.congr_fun (congrArg WithConv.ofConv (DFunLike.congr_fun hgg' a)) x
  let e := AlgEquiv.ofBijective _ hp
  let g₀ : H →ₐ[R] C := e.symm.toAlgHom.comp (AlgHom.pi fun a ↦ (φ a).ofConv)
  have he (c : C) (a : A) : e c a = (p a).ofConv c := by simp [e]
  have hg₀ (a : A) (x : H) : (p a).ofConv (g₀ x) = (φ a).ofConv x := by
    rw [← he]
    simp [g₀]
  have hcounit : (Bialgebra.counitAlgHom R C).comp g₀ = Bialgebra.counitAlgHom R H := by
    ext x
    have h₁ := DFunLike.congr_fun (congrArg WithConv.ofConv (map_one p)) (g₀ x)
    have h₂ := DFunLike.congr_fun (congrArg WithConv.ofConv (map_one φ)) x
    simp only [AlgHom.convOne_def, WithConv.ofConv_toConv, AlgHom.comp_apply,
      Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply] at h₁ h₂
    rw [AlgHom.comp_apply, ← h₁, ← h₂, hg₀]
  have hcomul : (Algebra.TensorProduct.map g₀ g₀).comp (Bialgebra.comulAlgHom R H) =
      (Bialgebra.comulAlgHom R C).comp g₀ := by
    ext x
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    refine Algebra.TensorProduct.eq_of_pi_bijective hp hp fun a b ↦ ?_
    have h₁ := DFunLike.congr_fun (congrArg WithConv.ofConv (map_mul p a b)) (g₀ x)
    have h₂ := DFunLike.congr_fun (congrArg WithConv.ofConv (map_mul φ a b)) x
    rw [WithConv.ofConv_toConv, AlgHom.convMul_apply] at h₁ h₂
    have hlift : (Algebra.TensorProduct.lift (p a).ofConv (p b).ofConv (fun _ _ ↦ .all _ _)).comp
        (Algebra.TensorProduct.map g₀ g₀) =
          Algebra.TensorProduct.lift (φ a).ofConv (φ b).ofConv (fun _ _ ↦ .all _ _) := by
      ext <;> simp [hg₀]
    rw [← h₁, hg₀, h₂]
    exact DFunLike.congr_fun hlift _
  refine ⟨BialgHom.ofAlgHom g₀ hcounit hcomul, MonoidHom.ext fun a ↦ ?_⟩
  apply WithConv.ofConv_injective
  ext x
  simp [hg₀]

end Recognition

section Universal

variable (R : Type*) [CommRing R] (H : Type*) [Semiring H] [Bialgebra R H] (A : Type*) [Monoid A]
  [Finite A]

/-- The evaluations at the elements of `A` identify `coordinateRing R A` with the functions on
`A`. -/
theorem pi_toPoints_bijective :
    Function.Bijective (AlgHom.pi fun a ↦ (toPoints R A a).ofConv) := by
  convert (functionAlgEquiv R A).bijective
  ext
  simp

/-- **Universal property of the constant monoid.** Bialgebra homomorphisms
`H →ₐc[R] coordinateRing R A` correspond to monoid homomorphisms from `A` to the `R`-points
`WithConv (H →ₐ[R] R)` of `H`; a homomorphism `g` goes to `a ↦ eval a ∘ g`. When `H` is
commutative, these are the homomorphisms of monoid schemes `A_R → Spec H` from the constant
monoid, and `eval a ∘ g` is the image of the point `a` of `A_R`. -/
noncomputable def bialgHomEquiv :
    (H →ₐc[R] coordinateRing R A) ≃ (A →* WithConv (H →ₐ[R] R)) :=
  Equiv.ofBijective _ (mapDomain_comp_bijective (pi_toPoints_bijective R A))

/-- The base changes to an `R`-algebra `T` of the evaluations at the elements of `A` identify
`T ⊗[R] coordinateRing R A` with the functions `A → T`. Geometrically, the base change of the
constant monoid `A_R` is the constant monoid `A_T`. -/
theorem pi_pointsBaseChange_toPoints_bijective (T : Type*) [CommRing T] [Algebra R T] :
    Function.Bijective
      (AlgHom.pi fun a ↦ ((AlgHom.pointsBaseChange T).comp (toPoints R A) a).ofConv) := by
  classical
  have := Fintype.ofFinite A
  convert ((LinearEquiv.lTensor T (functionLinearEquiv R A)).trans
    (TensorProduct.piScalarRight R R T A)).bijective using 1
  ext x a
  induction x using TensorProduct.inductionOn with
  | tmul t f => simp [AlgHom.pointsBaseChange_apply_tmul, Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable {R H A}

/-- The point attached to `a ∈ A` by `bialgHomEquiv g` is evaluation at `a` composed with `g`. -/
@[simp]
theorem ofConv_bialgHomEquiv_apply (g : H →ₐc[R] coordinateRing R A) (a : A) :
    (bialgHomEquiv R H A g a).ofConv = (eval R A a).comp (g : H →ₐ[R] coordinateRing R A) := by
  simp [bialgHomEquiv]

/-- The bialgebra homomorphism attached to `φ : A →* G(R)` takes `x` to the function
`a ↦ φ a x`: its value at `a`, the pairing with `MonoidAlgebra.single a 1`, is `φ a x`. -/
@[simp]
theorem bialgHomEquiv_symm_apply_ofConv_single (φ : A →* WithConv (H →ₐ[R] R)) (a : A) (x : H) :
    ((bialgHomEquiv R H A).symm φ x).ofConv (MonoidAlgebra.single a 1) = (φ a).ofConv x := by
  have h := congrArg (fun ψ ↦ (ψ a).ofConv x) ((bialgHomEquiv R H A).apply_symm_apply φ)
  simpa only [ofConv_bialgHomEquiv_apply, AlgHom.comp_apply, BialgHom.coe_toAlgHom, eval_apply,
    functionAlgEquiv_apply] using h

end Universal

section BaseChange

variable {R : Type*} [CommRing R] (H : Type*) [Semiring H] [Bialgebra R H] {A : Type*} [Monoid A]
  [Finite A] {T : Type*} [CommRing T] [Algebra R T]

/-- The homomorphism `A →* WithConv (T ⊗[R] H →ₐ[T] T)` attached to a `T`-bialgebra homomorphism
`g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A`: `a ∈ A` goes to the composite of `g` with the base
change of evaluation at `a`. When `H` is commutative, `g` is a homomorphism `A_T → G_T` of monoid
schemes over `T` from the constant monoid, where `G = Spec H`, and `a` goes to the image under `g`
of the point `a` of `A_T`. -/
noncomputable def pointsOfBialgHom (g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A) :
    A →* WithConv (T ⊗[R] H →ₐ[T] T) :=
  (AlgHom.mapDomain (H₁ := T ⊗[R] H) (H₂ := T ⊗[R] coordinateRing R A) (A := T) g).comp
    ((AlgHom.pointsBaseChange T).comp (toPoints R A))

variable {H}

/-- The point `pointsOfBialgHom g a` is the composite of `g` with the base change of evaluation
at `a`. -/
@[simp]
theorem ofConv_pointsOfBialgHom (g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A) (a : A) :
    (pointsOfBialgHom H g a).ofConv = ((eval R A a).sectionBaseChange T).comp (g : _ →ₐ[T] _) := by
  simp [pointsOfBialgHom, AlgHom.ofConv_pointsBaseChange]

variable (H) in
/-- **Homomorphisms from the constant monoid after base change.** `T`-bialgebra homomorphisms
`T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A` correspond through `pointsOfBialgHom` to the monoid
homomorphisms `A →* WithConv (T ⊗[R] H →ₐ[T] T)`. -/
theorem pointsOfBialgHom_bijective :
    Function.Bijective (pointsOfBialgHom (R := R) (A := A) (T := T) H) :=
  mapDomain_comp_bijective (pi_pointsBaseChange_toPoints_bijective R A T)

variable (R H A T) in
/-- `pointsOfBialgHom` as an equivalence: after base change to `T`, bialgebra homomorphisms from
`T ⊗[R] H` to the coordinate ring of the constant monoid correspond to the monoid homomorphisms
`A →* WithConv (T ⊗[R] H →ₐ[T] T)`. -/
noncomputable def pointsOfBialgHomEquiv :
    (T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A) ≃ (A →* WithConv (T ⊗[R] H →ₐ[T] T)) :=
  Equiv.ofBijective _ (pointsOfBialgHom_bijective H)

/-- `pointsOfBialgHomEquiv` is `pointsOfBialgHom`. -/
@[simp]
theorem pointsOfBialgHomEquiv_apply (g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A) :
    pointsOfBialgHomEquiv R H A T g = pointsOfBialgHom H g := by
  simp [pointsOfBialgHomEquiv]

/-- The bialgebra homomorphism attached to `φ : A →* WithConv (T ⊗[R] H →ₐ[T] T)` takes `x` to
an element whose base-changed evaluation at `a` is `φ a x`. -/
@[simp]
theorem sectionBaseChange_eval_pointsOfBialgHomEquiv_symm_apply
    (φ : A →* WithConv (T ⊗[R] H →ₐ[T] T)) (a : A) (x : T ⊗[R] H) :
    (eval R A a).sectionBaseChange T ((pointsOfBialgHomEquiv R H A T).symm φ x) =
      (φ a).ofConv x := by
  have h := congrArg (fun ψ ↦ (ψ a).ofConv x) ((pointsOfBialgHomEquiv R H A T).apply_symm_apply φ)
  simpa only [pointsOfBialgHomEquiv_apply, ofConv_pointsOfBialgHom, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom] using h

end BaseChange

end TauCeti.ConstantGroup
