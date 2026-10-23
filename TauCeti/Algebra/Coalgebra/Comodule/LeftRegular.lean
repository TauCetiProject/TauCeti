/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# The left regular comodule of a Hopf algebra

A Hopf algebra `H` is a right comodule over itself in a second way, besides the regular
comodule `TauCeti.Comodule.instSelf` given by the comultiplication. The *left regular* coaction
is

```text
f ↦ ∑ f₍₂₎ ⊗ S(f₍₁₎),
```

the comultiplication followed by the swap of the tensor factors and the antipode on the
coefficient factor. On points it is left translation by the inverse: a point `g` sends a
function `f` to `x ↦ f(g⁻¹ x)`, whereas the regular comodule is right translation
`x ↦ f(x g)`. Coassociativity is the statement that the antipode reverses comultiplication,
`TauCeti.HopfAlgebra.antipode_comul_antidistrib`.

Since left and right translations commute, this is the coaction for which the functions on a
homogeneous space `G/H`, the functions invariant under right translation by a subgroup, form
a subrepresentation. It is the natural target of the pullback of functions along an orbit map
`g ↦ g • v`.

## Main declarations

* `TauCeti.Comodule.leftRegularCoact`: the left regular coaction `f ↦ ∑ f₍₂₎ ⊗ S(f₍₁₎)`.
* `TauCeti.Comodule.leftRegular`: the left regular comodule structure on `H`.
* `TauCeti.Comodule.leftRegularCoactAlgHom`: for commutative `H`, the coaction as an algebra
  homomorphism.
* `TauCeti.Comodule.endOfPoint_leftRegular_tmul`: an algebra-valued point `g` acts by
  `a ⊗ f ↦ a • ∑ g(S f₍₁₎) ⊗ f₍₂₎`.
* `TauCeti.Comodule.lid_endOfPoint_leftRegular`: a base-valued point acts as left translation
  by its inverse.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.2.7.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v

noncomputable section

section Coaction

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

variable (R H) in
/-- The left regular coaction of a Hopf algebra on itself, `f ↦ ∑ f₍₂₎ ⊗ S(f₍₁₎)`. On points
it is left translation by the inverse point (`lid_endOfPoint_leftRegular`). -/
def leftRegularCoact : H →ₗ[R] H ⊗[R] H :=
  (HopfAlgebra.antipode R).lTensor H ∘ₗ (TensorProduct.comm R H H).toLinearMap ∘ₗ
    Coalgebra.comul

/-- The left regular coaction of `f` is `∑ f₍₂₎ ⊗ S(f₍₁₎)`. -/
theorem leftRegularCoact_apply (f : H) :
    leftRegularCoact R H f =
      (HopfAlgebra.antipode R).lTensor H (TensorProduct.comm R H H (Coalgebra.comul f)) := by
  simp [leftRegularCoact]

/-- The swap-and-antipode map `a ⊗ (b ⊗ c) ↦ c ⊗ (S b ⊗ S a)`, through which both sides of
the coassociativity law of `leftRegularCoact` factor. -/
private def reverseAntipode : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] (H ⊗[R] H) :=
  (TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R) ∘ₗ
      (TensorProduct.comm R H H).toLinearMap).lTensor H ∘ₗ
    (TensorProduct.comm R (H ⊗[R] H) H).toLinearMap ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap

private theorem reverseAntipode_tmul (a b c : H) :
    reverseAntipode (R := R) (a ⊗ₜ (b ⊗ₜ c)) =
      c ⊗ₜ (HopfAlgebra.antipode R b ⊗ₜ HopfAlgebra.antipode R a) := by
  simp [reverseAntipode]

/-- The left regular coaction is coassociative. -/
theorem leftRegularCoact_coassoc :
    TensorProduct.assoc R H H H ∘ₗ (leftRegularCoact R H).rTensor H ∘ₗ leftRegularCoact R H =
      (Coalgebra.comul (R := R) (A := H)).lTensor H ∘ₗ leftRegularCoact R H := by
  -- Both sides are `reverseAntipode` applied to the two bracketings of the iterated
  -- comultiplication, which agree by coassociativity.
  have hleft : TensorProduct.assoc R H H H ∘ₗ (leftRegularCoact R H).rTensor H ∘ₗ
      leftRegularCoact R H = reverseAntipode ∘ₗ (Coalgebra.comul (R := R) (A := H)).lTensor H ∘ₗ
        Coalgebra.comul := by
    rw [leftRegularCoact]
    simp only [← LinearMap.comp_assoc]
    congr 1
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
    induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
    | tmul x y => simp [reverseAntipode_tmul]
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add, hx, hy]
  have hright : (Coalgebra.comul (R := R) (A := H)).lTensor H ∘ₗ leftRegularCoact R H =
      reverseAntipode ∘ₗ (TensorProduct.assoc R H H H).toLinearMap ∘ₗ
        (Coalgebra.comul (R := R) (A := H)).rTensor H ∘ₗ Coalgebra.comul := by
    rw [leftRegularCoact]
    simp only [← LinearMap.comp_assoc]
    congr 1
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
      TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply]
    induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
    | tmul x y => simp [reverseAntipode_tmul]
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add, hx, hy]
  rw [hleft, hright, ← Coalgebra.coassoc]

/-- The counit law of the left regular coaction. -/
theorem lTensor_counit_comp_leftRegularCoact :
    (Coalgebra.counit (R := R) (A := H)).lTensor H ∘ₗ leftRegularCoact R H =
      (TensorProduct.mk R H R).flip 1 := by
  -- Applying `id ⊗ ε` to `∑ f₍₂₎ ⊗ S(f₍₁₎)` swaps the counit law `∑ ε(f₍₁₎) ⊗ f₍₂₎ = 1 ⊗ f`.
  ext f
  calc _ = TensorProduct.comm R R H (Coalgebra.counit.rTensor H (Coalgebra.comul f)) := by
        rw [LinearMap.comp_apply, leftRegularCoact_apply]
        induction Coalgebra.comul (R := R) f using TensorProduct.inductionOn with
        | tmul x y => simp
        | add x y hx hy => simp only [map_add, hx, hy]
    _ = _ := by simp

variable (R H) in
/-- The left regular comodule structure on a Hopf algebra, with coaction
`f ↦ ∑ f₍₂₎ ⊗ S(f₍₁₎)`.

This is deliberately not a global instance: `H` is already a comodule over itself through the
regular comodule `instSelf`. Downstream code should select it explicitly, typically as a local
instance. -/
@[instance_reducible]
def leftRegular : Comodule R H H where
  coact := leftRegularCoact R H
  coassoc := leftRegularCoact_coassoc
  lTensor_counit_comp_coact := lTensor_counit_comp_leftRegularCoact

/-- The coaction of the left regular comodule is `leftRegularCoact`. -/
@[simp]
theorem leftRegular_coact :
    letI := leftRegular R H
    coact (R := R) (C := H) (M := H) = leftRegularCoact R H := (rfl)

end Coaction

section Commutative

variable {R : Type u} {H : Type v} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]

variable (R H) in
/-- For a commutative Hopf algebra the antipode is multiplicative, so the left regular
coaction is an algebra homomorphism. -/
def leftRegularCoactAlgHom : H →ₐ[R] H ⊗[R] H :=
  (Algebra.TensorProduct.map (AlgHom.id R H) (HopfAlgebra.antipodeAlgHom R H)).comp
    ((Algebra.TensorProduct.comm R H H).toAlgHom.comp (Bialgebra.comulAlgHom R H))

/-- The underlying linear map of `leftRegularCoactAlgHom` is the left regular coaction. -/
@[simp]
theorem toLinearMap_leftRegularCoactAlgHom :
    (leftRegularCoactAlgHom R H).toLinearMap = leftRegularCoact R H := by
  apply LinearMap.ext
  intro f
  simp only [leftRegularCoactAlgHom, leftRegularCoact, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply, LinearMap.comp_apply, Bialgebra.comulAlgHom_apply, AlgEquiv.coe_toAlgHom,
    LinearEquiv.coe_coe]
  induction Coalgebra.comul (R := R) f using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The algebra homomorphism `leftRegularCoactAlgHom` applies as the left regular coaction. -/
@[simp]
theorem leftRegularCoactAlgHom_apply (f : H) :
    leftRegularCoactAlgHom R H f = leftRegularCoact R H f := by
  rw [← AlgHom.toLinearMap_apply, toLinearMap_leftRegularCoactAlgHom]

end Commutative

section Points

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- **The point action of the left regular comodule.** An `A`-point `g` sends `a ⊗ f` to
`a • ∑ g(S f₍₁₎) ⊗ f₍₂₎`: it is left translation by the inverse point, `f ↦ f(g⁻¹ ·)`. -/
theorem endOfPoint_leftRegular_tmul (g : H →ₐ[R] A) (a : A) (f : H) :
    letI := leftRegular R H
    endOfPoint H g (a ⊗ₜ f) =
      a • TensorProduct.map (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) LinearMap.id
        (Coalgebra.comul f) := by
  let := leftRegular R H
  rw [endOfPoint_tmul, leftRegular_coact, leftRegularCoact_apply]
  congr 1
  induction Coalgebra.comul (R := R) f using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Points

section BasePoints

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- **Base-valued points act on the left regular comodule by left translation by the
inverse.** Under `R ⊗[R] H ≃ H`, the action of a rational point `g` on `f` is the pullback of
`f` along left translation by `g⁻¹`, that is, the function `x ↦ f(g⁻¹ x)`. -/
theorem lid_endOfPoint_leftRegular (g : WithConv (H →ₐ[R] R)) (f : H) :
    letI := leftRegular R H
    TensorProduct.lid R H (endOfPoint H g.ofConv (1 ⊗ₜ f)) =
      HopfAlgebra.leftTranslationAlgEquiv g⁻¹ f := by
  let := leftRegular R H
  rw [endOfPoint_leftRegular_tmul, one_smul, HopfAlgebra.leftTranslationAlgEquiv_apply]
  induction Coalgebra.comul (R := R) f using TensorProduct.inductionOn with
  | tmul x y => simp [WithConv.algHom_inv_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end BasePoints

end

end TauCeti.Comodule
