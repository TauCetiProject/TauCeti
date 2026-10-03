/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.PowerClassGroup
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Basic
public import TauCeti.RingTheory.Norm.Units
public import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RingTheory.Norm.Basic

/-!
# Norms on completed multiplicative modules

For a finite extension `L/K`, the field norm induces a `ℤ_p`-linear map `A(L) → A(K)` on
the inverse limits of the `p`-power class groups. Its value on the canonical class of a unit
is the canonical class of its norm.

The completed norm is invariant under every `K`-automorphism of `L`, including on elements
of `A(L)` that do not come from individual units. It therefore factors through Mathlib's
coinvariants of the representation `padicCompletionUnitsRepresentation p L K`. This is the
norm map whose cokernel enters the reciprocity description of a finite Galois layer.

The construction uses the algebraic inverse-limit carrier; it requires neither a topology
on the fields nor a Galois hypothesis.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., VII §4,
  especially (7.4.4).
-/

public section

noncomputable section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L]

-- The completion uses raw power-hom ranges; identify them with the generic power classes
-- via the public subgroup equality, without requiring `powerSubgroup` to be exposed.
private def padicCompletionUnitsNormHom :
    ↑(padicCompletionUnits p L) →* ↑(padicCompletionUnits p K) := by
  let norm (m : ℕ) :=
    ((QuotientGroup.quotientMulEquivOfEq
      (powerSubgroup_eq_range_powMonoidHom Kˣ (p ^ m))).toMonoidHom).comp
      ((powerClassMap (p ^ m) (Algebra.normUnits K : Lˣ →* Kˣ)).comp
        (QuotientGroup.quotientMulEquivOfEq
          (powerSubgroup_eq_range_powMonoidHom Lˣ (p ^ m)).symm).toMonoidHom)
  refine MonoidHom.codRestrict
    (MonoidHom.pi fun m ↦ (norm m).comp
      ((Pi.evalMonoidHom _ m).comp (padicCompletionUnits p L).subtype)) _ ?_
  intro x
  rw [mem_padicCompletionUnits_iff]
  intro m
  have hx := (mem_padicCompletionUnits_iff p L x.1).mp x.2 m
  have hnorm (y : Lˣ ⧸ (powMonoidHom (p ^ (m + 1)) : Lˣ →* Lˣ).range) :
      padicCompletionTransition p K m (norm (m + 1) y) =
        norm m (padicCompletionTransition p L m y) := by
    induction y using QuotientGroup.induction_on with
    | H y => simp [norm]
  simpa using (hnorm (x.1 (m + 1))).trans (congrArg (norm m) hx)

omit [Fact p.Prime] in
@[simp]
private theorem padicCompletionUnitsNormHom_apply (x : ↑(padicCompletionUnits p L))
    (m : ℕ) :
    (padicCompletionUnitsNormHom p K L x).1 m =
      QuotientGroup.quotientMulEquivOfEq (powerSubgroup_eq_range_powMonoidHom Kˣ (p ^ m))
        (powerClassMap (p ^ m) (Algebra.normUnits K : Lˣ →* Kˣ)
          (QuotientGroup.quotientMulEquivOfEq
            (powerSubgroup_eq_range_powMonoidHom Lˣ (p ^ m)).symm (x.1 m))) := (rfl)

/-- The `ℤ_p`-linear norm `A(L) → A(K)` induced by the field norm at every finite level.
Finiteness excludes the constant-one value of Mathlib's total norm on infinite extensions. -/
def padicCompletionUnitsNorm [_hfin : FiniteDimensional K L] :
    Additive ↑(padicCompletionUnits p L) →ₗ[ℤ_[p]]
      Additive ↑(padicCompletionUnits p K) where
  toFun x := Additive.ofMul (padicCompletionUnitsNormHom p K L x.toMul)
  map_add' x y := by
    apply Additive.toMul.injective
    exact map_mul (padicCompletionUnitsNormHom p K L) x.toMul y.toMul
  map_smul' a x := by
    apply Additive.toMul.injective
    ext m
    simp only [toMul_ofMul, RingHom.id_apply, padicCompletionUnitsNormHom_apply,
      padicCompletionUnits_smul_apply]
    simp only [map_pow]

variable [FiniteDimensional K L]

/-- The completed norm is computed by the norm on each power-class coordinate. -/
@[simp]
theorem padicCompletionUnitsNorm_apply (x : Additive ↑(padicCompletionUnits p L)) (m : ℕ) :
    (padicCompletionUnitsNorm p K L x).toMul.1 m =
      QuotientGroup.quotientMulEquivOfEq (powerSubgroup_eq_range_powMonoidHom Kˣ (p ^ m))
        (powerClassMap (p ^ m) (Algebra.normUnits K : Lˣ →* Kˣ)
          (QuotientGroup.quotientMulEquivOfEq
            (powerSubgroup_eq_range_powMonoidHom Lˣ (p ^ m)).symm (x.toMul.1 m))) := (rfl)

/-- The norm of the canonical class of a unit is the canonical class of its norm. -/
@[simp]
theorem padicCompletionUnitsNorm_of (x : Lˣ) :
    padicCompletionUnitsNorm p K L (Additive.ofMul (padicCompletionUnitsOf p L x)) =
      Additive.ofMul (padicCompletionUnitsOf p K (Algebra.normUnits K x)) := by
  apply Additive.toMul.injective
  ext m
  simp

omit [Fact p.Prime] [FiniteDimensional K L] in
/-- The canonical class of a norm is unchanged on replacing a unit by a Galois conjugate. -/
@[simp]
theorem padicCompletionUnitsOf_norm_algEquiv (σ : L ≃ₐ[K] L) (x : Lˣ) :
    padicCompletionUnitsOf p K (Algebra.normUnits K (Units.map ((σ : L →+* L) : L →* L) x)) =
      padicCompletionUnitsOf p K (Algebra.normUnits K x) := by
  congr 1
  exact Units.ext (by simp [Algebra.norm_eq_of_algEquiv σ])

/-- The completed norm is invariant under the full `K`-automorphism action on `A(L)`. -/
@[simp]
theorem padicCompletionUnitsNorm_aut (σ : L ≃ₐ[K] L)
    (x : ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsNorm p K L (Additive.ofMul (padicCompletionUnitsAut p L K σ x)) =
      padicCompletionUnitsNorm p K L (Additive.ofMul x) := by
  apply Additive.toMul.injective
  ext m
  simp only [padicCompletionUnitsNorm_apply, toMul_ofMul, padicCompletionUnitsAut_apply]
  induction x.1 m using QuotientGroup.induction_on with
  | H y =>
    simp only [padicCompletionPowerClassMap_mk, QuotientGroup.quotientMulEquivOfEq_mk,
      powerClassMap_mk]
    simpa only [padicCompletionUnitsOf_apply, QuotientGroup.mk'_apply,
      RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom] using
      congrArg (fun z : ↑(padicCompletionUnits p K) ↦ z.1 m)
      (padicCompletionUnitsOf_norm_algEquiv p K L σ y)

/-- The group algebra acts through its augmentation after applying the completed norm.
In particular the augmentation ideal annihilates the norm. -/
@[simp]
theorem padicCompletionUnitsNorm_smul
    (r : MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (x : Additive ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsNorm p K L (r • x) =
      MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L) r • padicCompletionUnitsNorm p K L x := by
  induction r using _root_.MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp [add_smul, hr, hs]
  | single σ a =>
    conv_lhs => rw [← ofMul_toMul x, padicCompletionUnits_single_smul]
    simp

/-- The completed norm descends to the coinvariants of the Galois representation on `A(L)`. -/
def padicCompletionUnitsCoinvariantsNorm :
    (padicCompletionUnitsRepresentation p L K).Coinvariants →ₗ[ℤ_[p]]
      Additive ↑(padicCompletionUnits p K) :=
  Representation.Coinvariants.lift _ (padicCompletionUnitsNorm p K L) fun σ ↦ by
    ext x
    simp

/-- The norm on coinvariants recovers the completed norm on a representative. -/
@[simp]
theorem padicCompletionUnitsCoinvariantsNorm_mk (x : Additive ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsCoinvariantsNorm p K L
        (Representation.Coinvariants.mk (padicCompletionUnitsRepresentation p L K) x) =
      padicCompletionUnitsNorm p K L x :=
  Representation.Coinvariants.lift_mk _ _ _ x

end TauCeti
