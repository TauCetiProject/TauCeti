/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# Evaluation of group-like elements on convolution points of a Hopf algebra

For a Hopf algebra `H` over `k`, a group-like element `χ : GroupLike k H` satisfies `ε(χ) = 1` and
`Δ(χ) = χ ⊗ₜ χ`, with multiplicative inverse given by the antipode `S(χ)`. When `H` is commutative,
group-like elements of `H` are the rational characters `Spec H → 𝔾ₘ` of the affine group scheme
`Spec H`.

Evaluating convolution points `x : WithConv (H →ₐ[k] R)` at `χ` produces a group homomorphism
`TauCeti.characterValue R χ : WithConv (H →ₐ[k] R) →* Rˣ` for every commutative `k`-algebra `R`.
This pairing is multiplicative in `χ`, covariant in the coefficient algebra `R`, and contravariant
in the coordinate Hopf algebra `H`. Over a number field `F`, pairing `characterValue` on adelic
points with the idele norm cuts out the subgroup `G(𝔸_F)^1` of norm-one adelic points.

## Main declarations

* `BialgHom.mapGroupLike`: monoid homomorphism `GroupLike k H₁ →* GroupLike k H₂` induced by a
  bialgebra morphism `H₁ →ₐc[k] H₂`.
* `TauCeti.characterValue`: group homomorphism `WithConv (H →ₐ[k] R) →* Rˣ` evaluating points at a
  group-like element `χ : GroupLike k H`.
* `TauCeti.characterValue_one`, `TauCeti.characterValue_mul`, `TauCeti.characterValue_inv`,
  `TauCeti.characterValue_pow`, `TauCeti.characterValue_zpow`: group-homomorphism laws in `χ`.
* `TauCeti.characterValue_mapValue`, `TauCeti.characterValue_mapDomain`: covariance in `R` and
  contravariance in `H`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Graduate Texts in Mathematics 66,
  Springer (1979), §2.2.
* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §§2–3.
-/

public section

open WithConv

section BialgHom

variable {k H₁ H₂ : Type*} [CommSemiring k] [Semiring H₁] [Bialgebra k H₁]
  [Semiring H₂] [Bialgebra k H₂]

/-- A bialgebra morphism maps group-like elements to group-like elements as a monoid
homomorphism. -/
def BialgHom.mapGroupLike (φ : H₁ →ₐc[k] H₂) : GroupLike k H₁ →* GroupLike k H₂ where
  toFun χ := ⟨φ χ, χ.2.map φ⟩
  map_one' := GroupLike.ext <| by simp
  map_mul' χ₁ χ₂ := GroupLike.ext <| by simp

@[simp]
theorem BialgHom.val_mapGroupLike (φ : H₁ →ₐc[k] H₂) (χ : GroupLike k H₁) :
    (φ.mapGroupLike χ : H₂) = φ χ := by
  simp [mapGroupLike]

end BialgHom

namespace TauCeti

variable {k H : Type*} [CommSemiring k] [Semiring H] [HopfAlgebra k H]

/-- Evaluating convolution points of a Hopf algebra `H` at a group-like element `χ : GroupLike k H`
defines a group homomorphism into `Rˣ`, with inverse given by evaluating at the antipode of `χ`. -/
noncomputable def characterValue (R : Type*) [CommSemiring R] [Algebra k R]
    (χ : GroupLike k H) : WithConv (H →ₐ[k] R) →* Rˣ where
  toFun x := Units.map x.ofConv.toMonoidHom (GroupLike.toUnits k χ)
  map_one' := Units.ext <| by
    simp [AlgHom.convOne_def]
  map_mul' x y := Units.ext <| by
    simp [AlgHom.convMul_apply, χ.2.comul_eq_tmul_self]

@[simp]
theorem coe_characterValue_apply (R : Type*) [CommSemiring R] [Algebra k R]
    (χ : GroupLike k H) (x : WithConv (H →ₐ[k] R)) :
    (characterValue R χ x : R) = x.ofConv χ := by
  simp [characterValue]

@[simp]
theorem coe_inv_characterValue_apply (R : Type*) [CommSemiring R] [Algebra k R]
    (χ : GroupLike k H) (x : WithConv (H →ₐ[k] R)) :
    (↑(characterValue R χ x)⁻¹ : R) = x.ofConv (HopfAlgebra.antipode k (χ : H)) := by
  simp [characterValue]

@[simp]
theorem characterValue_one (R : Type*) [CommSemiring R] [Algebra k R] :
    characterValue R (1 : GroupLike k H) = 1 := by
  ext x
  simp

@[simp]
theorem characterValue_mul (R : Type*) [CommSemiring R] [Algebra k R]
    (χ₁ χ₂ : GroupLike k H) (x : WithConv (H →ₐ[k] R)) :
    characterValue R (χ₁ * χ₂) x = characterValue R χ₁ x * characterValue R χ₂ x := by
  ext
  simp

@[simp]
theorem characterValue_inv (R : Type*) [CommSemiring R] [Algebra k R]
    (χ : GroupLike k H) (x : WithConv (H →ₐ[k] R)) :
    characterValue R χ⁻¹ x = (characterValue R χ x)⁻¹ :=
  Units.ext <| by simp

@[simp]
theorem characterValue_pow (R : Type*) [CommSemiring R] [Algebra k R]
    (χ : GroupLike k H) (n : ℕ) (x : WithConv (H →ₐ[k] R)) :
    characterValue R (χ ^ n) x = characterValue R χ x ^ n :=
  Units.ext <| by simp

@[simp]
theorem characterValue_zpow (R : Type*) [CommSemiring R] [Algebra k R]
    (χ : GroupLike k H) (z : ℤ) (x : WithConv (H →ₐ[k] R)) :
    characterValue R (χ ^ z) x = characterValue R χ x ^ z := by
  cases z <;> simp

/-- Character evaluation commutes with change of coefficient algebra. -/
theorem characterValue_mapValue {R S : Type*} [CommSemiring R] [Algebra k R]
    [CommSemiring S] [Algebra k S] (φ : R →ₐ[k] S) (χ : GroupLike k H)
    (x : WithConv (H →ₐ[k] R)) :
    characterValue S χ (AlgHom.mapValue φ x) =
      Units.map φ.toMonoidHom (characterValue R χ x) := by
  ext
  simp

/-- Character evaluation is contravariant along Hopf bialgebra morphisms. -/
theorem characterValue_mapDomain {H₁ H₂ : Type*} [Semiring H₁] [HopfAlgebra k H₁]
    [Semiring H₂] [HopfAlgebra k H₂] (R : Type*) [CommSemiring R] [Algebra k R]
    (φ : H₁ →ₐc[k] H₂) (χ : GroupLike k H₁) (x : WithConv (H₂ →ₐ[k] R)) :
    characterValue R (φ.mapGroupLike χ) x =
      characterValue R χ (BialgHom.mapDomain φ x) :=
  Units.ext <| by simp

end TauCeti
