/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Topology.Algebra.PointTopology.Basic

/-!
# Values of characters on points

Let `G = Spec H` be an affine group scheme over a commutative ring `k`, given by a Hopf algebra
`H`. A character of `G` defined over `k`, that is a homomorphism `G → 𝔾ₘ` over `k`, is a
group-like element `χ ∈ H` (`Δ χ = χ ⊗ χ`, `ε χ = 1`). Its value at a point
`x : H →ₐ[k] A` with coefficients in a commutative `k`-algebra `A` is `x χ`, a unit of `A` whose
inverse is `x (S χ)`. This file bundles the value as a group homomorphism
`χ.characterValue A : G(A) →* Aˣ` on the convolution group of points.

The value is multiplicative in the character as well as in the point, it is natural in the
coefficient algebra, and it is continuous for Tau Ceti's point topology on `G(A)` and the
topology of `Aˣ` as a unit group (the embedding `u ↦ (u, u⁻¹)` into `A × Aᵐᵒᵖ`). Continuity
needs no assumption on the topology of `A`: both `x χ` and `x (S χ)` are evaluations of `x`.

## Main declarations

* `GroupLike.characterValue`: the value `x ↦ x χ` of a character as a homomorphism to `Aˣ`.
* `GroupLike.val_characterValue`, `GroupLike.val_characterValue_inv`: its value and the value
  of its inverse.
* `GroupLike.characterValue_one`, `GroupLike.characterValue_mul`,
  `GroupLike.characterValue_inv`: the value is multiplicative in the character.
* `GroupLike.characterValue_mapValue`: the value is natural in the coefficient algebra.
* `GroupLike.continuous_characterValue`: the value is continuous.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 12.
* J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4 (2005), §3, p. 16.
-/

public section

open HopfAlgebra WithConv

namespace GroupLike

variable {k H : Type*} [CommSemiring k] [Semiring H] [HopfAlgebra k H]
variable (A : Type*) [CommSemiring A] [Algebra k A]

/-- The value `χ(x) = x χ ∈ Aˣ` of a character `χ` of `G = Spec H` at a point
`x : H →ₐ[k] A`, as a homomorphism from the convolution group of points to the units of `A`.
The inverse of `χ(x)` is `x (S χ)`. -/
def characterValue (χ : GroupLike k H) : WithConv (H →ₐ[k] A) →* Aˣ where
  toFun x := Units.map x.ofConv.toMonoidHom (GroupLike.toUnits k χ)
  map_one' := Units.ext <| by simp [AlgHom.convOne_apply]
  map_mul' x y := Units.ext <| by
    simp [AlgHom.convMul_apply, χ.isGroupLikeElem_val.comul_eq_tmul_self]

variable {A}

/-- The value of a character `χ` at a point `x` is `x χ`. -/
@[simp]
theorem val_characterValue (χ : GroupLike k H) (x : WithConv (H →ₐ[k] A)) :
    (χ.characterValue A x : A) = x.ofConv χ :=
  (rfl)

/-- The inverse of the value of a character `χ` at a point `x` is `x (S χ)`. -/
@[simp]
theorem val_characterValue_inv (χ : GroupLike k H) (x : WithConv (H →ₐ[k] A)) :
    ((χ.characterValue A x)⁻¹ : Aˣ) = x.ofConv (antipode k (χ : H)) :=
  (rfl)

/-- The trivial character has value `1` at every point. -/
@[simp]
theorem characterValue_one (x : WithConv (H →ₐ[k] A)) :
    (1 : GroupLike k H).characterValue A x = 1 :=
  Units.ext <| by simp

/-- The value of a product of characters is the product of the values. -/
@[simp]
theorem characterValue_mul (χ ψ : GroupLike k H) (x : WithConv (H →ₐ[k] A)) :
    (χ * ψ).characterValue A x = χ.characterValue A x * ψ.characterValue A x :=
  Units.ext <| by simp

/-- The value of the inverse character is the inverse of the value. -/
@[simp]
theorem characterValue_inv (χ : GroupLike k H) (x : WithConv (H →ₐ[k] A)) :
    χ⁻¹.characterValue A x = (χ.characterValue A x)⁻¹ :=
  Units.ext <| by simp

/-- The value of a power of a character is the power of the value. -/
@[simp]
theorem characterValue_zpow (χ : GroupLike k H) (n : ℤ) (x : WithConv (H →ₐ[k] A)) :
    (χ ^ n).characterValue A x = χ.characterValue A x ^ n :=
  map_zpow (MonoidHom.mk' (fun ψ : GroupLike k H ↦ ψ.characterValue A x) fun ψ ψ' ↦
    characterValue_mul ψ ψ' x) χ n

/-- **Naturality in the coefficients.** Changing the coefficients of a point along an algebra
map `φ : A →ₐ[k] B` changes the value of a character by `φ`. -/
theorem characterValue_mapValue {B : Type*} [CommSemiring B] [Algebra k B] (χ : GroupLike k H)
    (φ : A →ₐ[k] B) (x : WithConv (H →ₐ[k] A)) :
    χ.characterValue B (AlgHom.mapValue φ x) = Units.map φ.toMonoidHom (χ.characterValue A x) :=
  Units.ext <| by simp

open TauCeti.PointTopology in
/-- The value of a character is continuous for the point topology on the points and the
topology of the unit group `Aˣ`. No assumption on the topology of `A` is needed: the value and
its inverse are the evaluations at `χ` and `S χ`. -/
@[fun_prop]
theorem continuous_characterValue [TopologicalSpace A] (χ : GroupLike k H) :
    Continuous (χ.characterValue A) :=
  Units.continuous_iff.2 ⟨continuous_eval_ofConv (χ : H), continuous_eval_ofConv _⟩

end GroupLike
