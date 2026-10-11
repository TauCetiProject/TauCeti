/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Homomorphisms from a constant group

Let `A` be a finite group and `R` a commutative ring. The constant group `A_R` is the disjoint
union `⨆_{a ∈ A} Spec R`, with coordinate ring the functions `A → R`
(`TauCeti.ConstantGroup.coordinateRing`). A morphism of schemes `A_R → G` over `Spec R` is
therefore a family of `|A|` points of `G` with values in `R`, and it is a homomorphism of monoid
schemes exactly when this family is a monoid homomorphism `A →* G(R)`. This file proves this
universal property in coordinates: for an `R`-bialgebra `H`, with `G = Spec H`,
restricting along the points of `A_R` is a bijection

  `(H →ₐc[R] coordinateRing R A) ≃ (A →* G(R))`

(`TauCeti.ConstantGroup.bialgHomEquiv`). No finiteness, flatness or connectedness hypothesis is
made on `H` or on `R`; over a disconnected base `A_R` is still a disjoint union of copies of the
base, so homomorphisms from it are still indexed by `A`.

The universal property is proved for every bialgebra `C` together with a monoid homomorphism
`p : A →* WithConv (C →ₐ[R] R)` whose values identify `C` with the functions `A → R`
(`TauCeti.ConstantGroup.bijective_mapDomain_comp`). Besides `coordinateRing R A` with its
evaluations, this applies to any base change of it, which is how Katz–Mazur `A`-generators over a
varying base are read off a scheme of homomorphisms from the constant group.

## Main results

* `TauCeti.ConstantGroup.bijective_mapDomain_comp`: if the points `p a` identify `C` with the
  functions on `A`, then a bialgebra homomorphism `H →ₐc[R] C` is the same as a monoid
  homomorphism from `A` to the points of `Spec H`.
* `TauCeti.ConstantGroup.bialgHomEquiv`: homomorphisms of monoid schemes `A_R → Spec H` are the
  monoid homomorphisms `A →* WithConv (H →ₐ[R] R)`.
* `TauCeti.ConstantGroup.bijective_pi_toPoints` and
  `TauCeti.ConstantGroup.bijective_pi_pointsBaseChange_toPoints`: the evaluations identify
  `coordinateRing R A`, and each of its base changes `T ⊗[R] coordinateRing R A`, with the
  functions on `A`, so `bijective_mapDomain_comp` applies to them.

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

-- If the points `p a` identify `C` with the functions on `A`, then the points
-- `Algebra.TensorProduct.lift (p a) (p b)` separate the elements of `C ⊗[R] C`: through
-- `C ⊗[R] C ≅ (A → R) ⊗[R] (A → R) ≅ (A → A → R)` they are the coordinates.
private theorem tensor_ext_of_bijective
    (hp : Function.Bijective (AlgHom.pi fun a ↦ (p a).ofConv)) {x y : C ⊗[R] C}
    (h : ∀ a b, Algebra.TensorProduct.lift (p a).ofConv (p b).ofConv (fun _ _ ↦ .all _ _) x =
      Algebra.TensorProduct.lift (p a).ofConv (p b).ofConv (fun _ _ ↦ .all _ _) y) :
    x = y := by
  classical
  have := Fintype.ofFinite A
  let e := (AlgEquiv.ofBijective _ hp).toLinearEquiv
  let F := (TensorProduct.congr e e).trans (TensorProduct.piScalarRight R R (A → R) A)
  have hF (z : C ⊗[R] C) (a b : A) :
      F z b a = Algebra.TensorProduct.lift (p a).ofConv (p b).ofConv (fun _ _ ↦ .all _ _) z := by
    induction z using TensorProduct.inductionOn with
    | tmul c d =>
        simp [F, e, TensorProduct.piScalarRightHom_tmul, mul_comm]
    | add z z' hz hz' =>
        simp only [map_add, Pi.add_apply] at hz hz' ⊢
        rw [hz, hz']
  exact F.injective <| funext fun b ↦ funext fun a ↦ by rw [hF, hF, h]

/-- **Recognition of constant groups.** Let `p : A →* WithConv (C →ₐ[R] R)` be a monoid
homomorphism from a finite monoid to the points of `Spec C` whose values identify `C` with the
functions on `A`, that is, `c ↦ (a ↦ p a c)` is bijective. Then for every bialgebra `H`, a
bialgebra homomorphism `g : H →ₐc[R] C` is determined by, and can be prescribed through, the monoid
homomorphism `a ↦ p a ∘ g` from `A` to the points of `Spec H`. -/
theorem bijective_mapDomain_comp
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
    refine tensor_ext_of_bijective hp fun a b ↦ ?_
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

variable (R : Type*) [CommRing R] (H : Type*) [Semiring H] [Bialgebra R H] (A : Type*) [Group A]
  [Finite A]

/-- The evaluations at the elements of `A` identify `coordinateRing R A` with the functions on
`A`. -/
theorem bijective_pi_toPoints :
    Function.Bijective (AlgHom.pi fun a ↦ (toPoints R A a).ofConv) := by
  convert (functionAlgEquiv R A).bijective
  ext
  simp

/-- **Universal property of the constant group.** Homomorphisms of monoid schemes `A_R → Spec H`
from the constant group, given as bialgebra homomorphisms `H →ₐc[R] coordinateRing R A`,
correspond to monoid homomorphisms from `A` to the points `WithConv (H →ₐ[R] R)` of `Spec H`. A
homomorphism `g` goes to `a ↦ eval a ∘ g`, the image of the point `a` of `A_R`. -/
noncomputable def bialgHomEquiv :
    (H →ₐc[R] coordinateRing R A) ≃ (A →* WithConv (H →ₐ[R] R)) :=
  Equiv.ofBijective _ (bijective_mapDomain_comp (bijective_pi_toPoints R A))

/-- The base changes to an `R`-algebra `T` of the evaluations at the elements of `A` identify
`T ⊗[R] coordinateRing R A` with the functions `A → T`: the base change of the constant group
`A_R` is the constant group `A_T`. -/
theorem bijective_pi_pointsBaseChange_toPoints (T : Type*) [CommRing T] [Algebra R T] :
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
`a ↦ φ a x`. -/
@[simp]
theorem eval_bialgHomEquiv_symm_apply (φ : A →* WithConv (H →ₐ[R] R)) (a : A) (x : H) :
    eval R A a ((bialgHomEquiv R H A).symm φ x) = (φ a).ofConv x := by
  have h := congrArg (fun ψ ↦ (ψ a).ofConv x) ((bialgHomEquiv R H A).apply_symm_apply φ)
  rwa [ofConv_bialgHomEquiv_apply] at h

end Universal

end TauCeti.ConstantGroup
