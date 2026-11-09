/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Ring.Action.ConjAct
import TauCeti.Algebra.Ring.Commutator

/-!
# First-order automorphisms of derivations

Let `B` be an associative `K`-algebra and `e ∈ K` a square-zero scalar, `e * e = 0`. For a
derivation `D` of `B`, the map `1 + e • D` is an automorphism of the `K`-algebra `B`, with inverse
`1 - e • D`: it is the exponential `exp (e • D)`, truncated because its quadratic term vanishes.
These are the first-order automorphisms through which a derivation acts on modules over a
coefficient ring with a square-zero parameter, for example `K = R[ε]` with `B = R[ε] ⊗[R] A`.

The assignment `D ↦ 1 + e • D` turns sums of derivations into composites, so it is a group
homomorphism from the additive group of derivations. Three further formulas compare it with the
structure of `Der B`:

* inner derivations go to inner automorphisms: `1 + e • ad b` is conjugation by the unit
  `1 + e • b`;
* conjugating `1 + e • D` by an algebra automorphism `σ` gives `1 + e • (σ ∘ D ∘ σ⁻¹)`;
* for two square-zero parameters `e` and `f`, the group commutator of `1 + e • D` and `1 + f • E`
  is `1 + (e * f) • ⁅D, E⁆`. With `K = R[ε, η] / (ε², η²)`, the commutator of the flows
  `1 + ε • D` and `1 + η • E` is the mixed second-order map `1 + (ε * η) • ⁅D, E⁆`.

## Main definitions

* `TauCeti.derivationLieAlgebra.firstOrderAlgEquiv e he D`: the automorphism `1 + e • D`.
* `TauCeti.derivationLieAlgebra.firstOrderHom e he`: the same assignment, as a group
  homomorphism from `Multiplicative (derivationLieAlgebra K B)`.

## Main results

* `TauCeti.derivationLieAlgebra.firstOrderAlgEquiv_add`: `1 + e • (D + E)` is the composite of
  `1 + e • D` and `1 + e • E`.
* `TauCeti.derivationLieAlgebra.firstOrderAlgEquiv_innerDerivation`: `1 + e • ad b` is
  conjugation by any unit with value `1 + e • b`.
* `TauCeti.derivationLieAlgebra.mul_firstOrderAlgEquiv_mul_inv`: conjugation of `1 + e • D` by an
  automorphism `σ` is `1 + e • (σ ∘ D ∘ σ⁻¹)`.
* `TauCeti.derivationLieAlgebra.commutatorElement_firstOrderAlgEquiv`: the commutator formula
  `⁅1 + e • D, 1 + f • E⁆ = 1 + (e * f) • ⁅D, E⁆`.

## Implementation notes

Mathlib's `LieDerivation.exp` exponentiates a nilpotent derivation of a Lie algebra over a
`ℚ`-algebra. Here the algebra is associative and the coefficients are arbitrary: since
`(e • D) ∘ (e • D) = (e * e) • (D ∘ D) = 0`, no denominators occur and the exponential is just
`1 + e • D`.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced
  Mathematics 103, Cambridge University Press, 2007, for first-order deformations of
  categories of modules along derivations.
-/

public section

namespace TauCeti.derivationLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

open scoped commutatorElement

variable {K B : Type*} [CommRing K] [Ring B] [Algebra K B]

/-- **The first-order automorphism** `1 + e • D` of a derivation `D`, for a square-zero scalar
`e`. Its inverse is `1 - e • D`. -/
def firstOrderAlgEquiv (e : K) (he : e * e = 0) (D : derivationLieAlgebra K B) : B ≃ₐ[K] B where
  toFun x := x + e • (D : Module.End K B) x
  invFun x := x - e • (D : Module.End K B) x
  left_inv x := by
    simp [smul_add, smul_smul, he]
  right_inv x := by
    simp [smul_sub, smul_smul, he]
  map_mul' x y := by
    simp only [leibniz, smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, he,
      zero_smul, add_zero]
    abel
  map_add' x y := by
    simp only [map_add, smul_add]
    abel
  commutes' r := by
    simp

variable (e : K) (he : e * e = 0)

@[simp]
theorem firstOrderAlgEquiv_apply (D : derivationLieAlgebra K B) (x : B) :
    firstOrderAlgEquiv e he D x = x + e • (D : Module.End K B) x :=
  (rfl)

@[simp]
theorem firstOrderAlgEquiv_symm_apply (D : derivationLieAlgebra K B) (x : B) :
    (firstOrderAlgEquiv e he D).symm x = x - e • (D : Module.End K B) x :=
  (rfl)

/-- As a linear map, the first-order automorphism of `D` is `1 + e • D`. -/
@[simp]
theorem firstOrderAlgEquiv_toLinearMap (D : derivationLieAlgebra K B) :
    (firstOrderAlgEquiv e he D).toLinearMap = 1 + e • (D : Module.End K B) := by
  ext x
  simp

/-- The first-order automorphism of `D` determines `e • D`, and only `e • D`. -/
theorem firstOrderAlgEquiv_eq_iff {D E : derivationLieAlgebra K B} :
    firstOrderAlgEquiv e he D = firstOrderAlgEquiv e he E ↔ e • D = e • E := by
  rw [← AlgEquiv.toLinearMap_injective.eq_iff, firstOrderAlgEquiv_toLinearMap,
    firstOrderAlgEquiv_toLinearMap, add_right_inj, ← Subtype.coe_inj, SetLike.val_smul,
    SetLike.val_smul]

/-- The first-order automorphism of the zero derivation is the identity. -/
@[simp]
theorem firstOrderAlgEquiv_zero : firstOrderAlgEquiv e he (0 : derivationLieAlgebra K B) = 1 := by
  ext x
  simp

/-- **Sums of derivations go to composites**: `1 + e • (D + E) = (1 + e • D) ∘ (1 + e • E)`. -/
theorem firstOrderAlgEquiv_add (D E : derivationLieAlgebra K B) :
    firstOrderAlgEquiv e he (D + E) = firstOrderAlgEquiv e he D * firstOrderAlgEquiv e he E := by
  ext x
  simp only [firstOrderAlgEquiv_apply, AlgEquiv.mul_apply, AddMemClass.coe_add,
    LinearMap.add_apply, map_add, map_smul, smul_add, smul_smul, he, zero_smul, add_zero]
  abel

/-- The first-order automorphism of `-D` is the inverse of that of `D`. -/
@[simp]
theorem firstOrderAlgEquiv_neg (D : derivationLieAlgebra K B) :
    firstOrderAlgEquiv e he (-D) = (firstOrderAlgEquiv e he D)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← firstOrderAlgEquiv_add, neg_add_cancel, firstOrderAlgEquiv_zero]

/-- **The first-order automorphisms as a group homomorphism**: `D ↦ 1 + e • D`, from the
additive group of derivations to the automorphism group of `B`. -/
def firstOrderHom : Multiplicative (derivationLieAlgebra K B) →* (B ≃ₐ[K] B) where
  toFun D := firstOrderAlgEquiv e he D.toAdd
  map_one' := firstOrderAlgEquiv_zero e he
  map_mul' D E := firstOrderAlgEquiv_add e he D.toAdd E.toAdd

@[simp]
theorem firstOrderHom_apply (D : Multiplicative (derivationLieAlgebra K B)) :
    firstOrderHom e he D = firstOrderAlgEquiv e he D.toAdd :=
  (rfl)

/-- **Inner derivations give inner automorphisms**: `1 + e • ad b` sends `x` to
`(1 + e • b) * x * (1 - e • b)`. -/
theorem firstOrderAlgEquiv_innerDerivation_apply (b x : B) :
    firstOrderAlgEquiv e he (innerDerivation K b) x = (1 + e • b) * x * (1 - e • b) := by
  simp only [firstOrderAlgEquiv_apply, coe_innerDerivation, LieAlgebra.ad_apply, Ring.lie_def,
    add_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, he, zero_smul,
    smul_sub, smul_add]
  abel

/-- **Inner derivations give inner automorphisms**: `1 + e • ad b` is conjugation by any unit
whose value is `1 + e • b`. Such units exist, since `e • b` squares to zero
(`IsNilpotent.isUnit_one_add`), and their inverse is `1 - e • b`. -/
theorem firstOrderAlgEquiv_innerDerivation (b : B) (u : Bˣ) (hu : (u : B) = 1 + e • b) :
    firstOrderAlgEquiv e he (innerDerivation K b) =
      MulSemiringAction.toAlgEquiv K B (ConjAct.toConjAct u) := by
  have hinv : ((u⁻¹ : Bˣ) : B) = 1 - e • b :=
    Units.val_inv_eq_one_sub u (e • b) hu (by rw [smul_mul_smul_comm, he, zero_smul])
  ext x
  rw [firstOrderAlgEquiv_innerDerivation_apply, MulSemiringAction.toAlgEquiv_apply,
    ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, hinv, hu]

/-- **Conjugating a first-order automorphism** by an algebra automorphism `σ` replaces the
derivation `D` by its conjugate `σ ∘ D ∘ σ⁻¹`. -/
theorem mul_firstOrderAlgEquiv_mul_inv (σ : B ≃ₐ[K] B) (D : derivationLieAlgebra K B) :
    σ * firstOrderAlgEquiv e he D * σ⁻¹ =
      firstOrderAlgEquiv e he (derivationLieAlgebraCongr σ.toLinearEquiv
        (fun x y => by simp) D) := by
  ext x
  simp [AlgEquiv.mul_apply, AlgEquiv.aut_inv, derivationLieAlgebraCongr_apply]

/-- **The commutator of two first-order automorphisms**: for square-zero scalars `e` and `f`,
the group commutator of `1 + e • D` and `1 + f • E` is `1 + (e * f) • ⁅D, E⁆`. -/
theorem commutatorElement_firstOrderAlgEquiv {f : K} (hf : f * f = 0)
    (D E : derivationLieAlgebra K B) :
    ⁅firstOrderAlgEquiv e he D, firstOrderAlgEquiv f hf E⁆ =
      firstOrderAlgEquiv (e * f) (by rw [mul_mul_mul_comm, he, zero_mul]) ⁅D, E⁆ := by
  -- Compute in the units of `Module.End K B`, where the commutator of `1 + e • D` and
  -- `1 + f • E` is given by `Units.val_commutatorElement_eq_one_add_lie`.
  let φ := (Units.map (AlgEquiv.toLinearMapHom K B)).comp (toUnits : (B ≃ₐ[K] B) ≃* _).toMonoidHom
  have hφ (σ : B ≃ₐ[K] B) : (φ σ : Module.End K B) = σ.toLinearMap := by
    ext
    simp [φ]
  set d := (D : Module.End K B)
  set d' := (E : Module.End K B)
  have h := Units.val_commutatorElement_eq_one_add_lie (φ (firstOrderAlgEquiv e he D))
    (φ (firstOrderAlgEquiv f hf E)) (e • d) (f • d')
    ((hφ _).trans (firstOrderAlgEquiv_toLinearMap e he D))
    ((hφ _).trans (firstOrderAlgEquiv_toLinearMap f hf E))
    (by rw [smul_mul_smul_comm, he, zero_smul]) (by rw [smul_mul_smul_comm, hf, zero_smul])
    (by rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_right_comm, he, zero_mul, zero_smul])
    (by rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_right_comm, hf, zero_mul, zero_smul])
  rw [← map_commutatorElement, Ring.lie_def, smul_mul_smul_comm, smul_mul_smul_comm,
    mul_comm f e, hφ] at h
  apply AlgEquiv.toLinearMap_injective
  rw [firstOrderAlgEquiv_toLinearMap, LieSubalgebra.coe_bracket, Ring.lie_def, smul_sub]
  exact h

end TauCeti.derivationLieAlgebra
