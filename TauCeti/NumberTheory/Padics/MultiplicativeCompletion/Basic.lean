/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import TauCeti.GroupTheory.QuotientGroup.Map
public import TauCeti.GroupTheory.QuotientGroup.PowMonoidHom
public import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The p-adic completion of a multiplicative group

For a prime `p` and a field `L`, this file constructs the inverse limit

`A(L) = lim_m Lˣ / (Lˣ)^(p^m)`.

The carrier is the subgroup of the product of the power-class groups consisting of compatible
families.  Its `ℤ_p`-module structure is intrinsic: at level `m`, a `p`-adic integer acts
through its residue modulo `p^m`.  Field automorphisms preserve power subgroups, and therefore
act on the whole inverse limit.

For a finite extension `L` of `ℚ_p`, this completed multiplicative module is the one used in
local reciprocity and in the Galois-module theory of local units, where it is finitely generated
over `ℤ_p`. This file imposes no such hypothesis and proves no finiteness statement: it supplies
only the carrier, its `ℤ_p`-module structure, and its Galois action. Finite generation is proved in
`TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Finite`.

## Main declarations

* `padicCompletionUnits`: the inverse-limit carrier `A(L)`.
* `padicCompletionUnitsPadicModule`: its intrinsic `ℤ_p`-module structure.
* `padicCompletionUnitsAut`: the coordinatewise Galois action.
* `padicCompletionUnitsRepresentation`: the `ℤ_p`-linear Galois representation on `A(L)`.
* `padicCompletionUnitsModule`: the integral `ℤ_p[Gal(L/K)]`-module structure on `A(L)`, namely
  Mathlib's `Representation.asModule` structure of `padicCompletionUnitsRepresentation`.
* `MonoidAlgebra.smul_padicCompletionUnitsOf`: a group-algebra element acts on the class of a unit
  through the classes of its conjugates.
* `MonoidAlgebra.smul_padicCompletionUnitsOf_of_forall_eq`: on the class of a unit fixed by every
  automorphism, the group algebra acts through the augmentation.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.4.
-/

public section

noncomputable section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L]

/-- The transition map from `p^(m+1)`-power classes to `p^m`-power classes. -/
def padicCompletionTransition (m : ℕ) :
    (Lˣ ⧸ (powMonoidHom (p ^ (m + 1)) : Lˣ →* Lˣ).range) →*
      (Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :=
  QuotientGroup.mapOfLE (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x ^ p, by rw [powMonoidHom_apply, powMonoidHom_apply, ← pow_mul, ← pow_succ']⟩)

omit [Fact p.Prime] in
/-- The transition map sends the class of a unit to its class at the previous level. -/
@[simp]
theorem padicCompletionTransition_mk (m : ℕ) (x : Lˣ) :
    padicCompletionTransition p L m
        (x : Lˣ ⧸ (powMonoidHom (p ^ (m + 1)) : Lˣ →* Lˣ).range) =
      (x : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :=
  QuotientGroup.mapOfLE_mk _ x

/-- `A(L) = lim_m Lˣ/(Lˣ)^(p^m)`, realized as the subgroup of compatible families in the
product of the power-class groups. -/
def padicCompletionUnits :
    Subgroup (∀ m : ℕ, Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :=
  ⨅ m : ℕ, MonoidHom.eqLocus
    ((padicCompletionTransition p L m).comp (Pi.evalMonoidHom _ (m + 1)))
    (Pi.evalMonoidHom _ m)

omit [Fact p.Prime] in
-- Recorded directly: deriving this structure through the product of the power-class groups is
-- slow enough to defeat instance searches built on top of it, such as the one for the quotient
-- of `Additive A(L)` by a submodule.
/-- `A(L)` is a commutative group, with the pointwise group structure of compatible families of
power classes inherited from the product `∏ₘ Lˣ/(Lˣ)^(p^m)`. -/
instance : CommGroup ↑(padicCompletionUnits p L) := inferInstance

omit [Fact p.Prime] in
/-- A compatible family is characterized by the transition equation at every level. -/
@[simp]
theorem mem_padicCompletionUnits_iff
    (x : ∀ m : ℕ, Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :
    x ∈ padicCompletionUnits p L ↔
      ∀ m, padicCompletionTransition p L m (x (m + 1)) = x m := by
  rw [padicCompletionUnits, Subgroup.mem_iInf]
  rfl

/-- The canonical homomorphism from `Lˣ` to its `p`-adic completion. -/
def padicCompletionUnitsOf : Lˣ →* ↑(padicCompletionUnits p L) :=
  MonoidHom.codRestrict (MonoidHom.pi fun _ ↦ QuotientGroup.mk' _) _ (by
    simp)

omit [Fact p.Prime] in
/-- The `m`-th coordinate of the canonical map is the power-class quotient map. -/
@[simp]
theorem padicCompletionUnitsOf_apply (x : Lˣ) (m : ℕ) :
    (padicCompletionUnitsOf p L x).1 m =
      QuotientGroup.mk' _ x :=
  by simp [padicCompletionUnitsOf]

/-- A `p`-adic integer acts on `A(L)` by truncated exponentiation: at level `m` it acts through
its residue modulo `p^m`. -/
instance padicCompletionUnitsSMul : SMul ℤ_[p] (Additive ↑(padicCompletionUnits p L)) where
  smul a x := Additive.ofMul ⟨fun m ↦ x.toMul.1 m ^ a.appr m, by
      rw [mem_padicCompletionUnits_iff]
      intro m
      have hx := (mem_padicCompletionUnits_iff p L x.toMul.1).mp x.toMul.2 m
      rw [map_pow, hx]
      exact PadicInt.pow_appr_eq_pow_appr a
        (QuotientGroup.pow_eq_one_quotient_range_powMonoidHom _ _) (Nat.le_succ m)⟩

/-- Scalar multiplication in the completion is truncated exponentiation in every coordinate. -/
@[simp]
theorem padicCompletionUnits_smul_apply (a : ℤ_[p])
    (x : Additive ↑(padicCompletionUnits p L)) (m : ℕ) :
    (a • x).toMul.1 m = x.toMul.1 m ^ a.appr m :=
  (rfl)

/-- The intrinsic `ℤ_p`-module structure on the completed multiplicative group. -/
instance padicCompletionUnitsPadicModule :
    Module ℤ_[p] (Additive ↑(padicCompletionUnits p L)) where
  one_smul x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    simpa only [padicCompletionUnits_smul_apply, Nat.cast_one, pow_one] using
      pow_eq_pow_of_modEq (PadicInt.appr_natCast_modEq 1 m)
        (QuotientGroup.pow_eq_one_quotient_range_powMonoidHom _ (x.toMul.1 m))
  mul_smul a b x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    simp only [padicCompletionUnits_smul_apply]
    rw [← pow_mul, mul_comm (b.appr m)]
    exact pow_eq_pow_of_modEq (PadicInt.appr_mul_modEq a b m)
      (QuotientGroup.pow_eq_one_quotient_range_powMonoidHom _ _)
  smul_zero a := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    simp
  smul_add a x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    simp only [padicCompletionUnits_smul_apply, toMul_add, Subgroup.coe_mul, Pi.mul_apply]
    exact mul_pow (x.toMul.1 m) (y.toMul.1 m) (a.appr m)
  add_smul a b x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    simp only [padicCompletionUnits_smul_apply, toMul_add, Subgroup.coe_mul, Pi.mul_apply]
    rw [← pow_add]
    exact pow_eq_pow_of_modEq (PadicInt.appr_add_modEq a b m)
      (QuotientGroup.pow_eq_one_quotient_range_powMonoidHom _ _)
  zero_smul x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    simpa only [padicCompletionUnits_smul_apply, Nat.cast_zero, pow_zero, toMul_zero,
      OneMemClass.coe_one, Pi.one_apply] using
      pow_eq_pow_of_modEq (PadicInt.appr_natCast_modEq 0 m)
        (QuotientGroup.pow_eq_one_quotient_range_powMonoidHom _ (x.toMul.1 m))

/-- The `ℤ_p`-action extends the intrinsic natural-number action on the completion. -/
@[simp]
theorem padicCompletionUnits_natCast_smul (n : ℕ)
    (x : Additive ↑(padicCompletionUnits p L)) :
    (n : ℤ_[p]) • x = n • x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  funext m
  rw [padicCompletionUnits_smul_apply, toMul_nsmul]
  exact pow_eq_pow_of_modEq (PadicInt.appr_natCast_modEq n m)
    (QuotientGroup.pow_eq_one_quotient_range_powMonoidHom _ (x.toMul.1 m))

/-- Adding a `p ^ m`-multiple in `A(L)` does not change the level-`m` coordinate. -/
theorem padicCompletionUnits_add_pow_smul_apply (m : ℕ)
    (y z : Additive ↑(padicCompletionUnits p L)) :
    (y + (p : ℤ_[p]) ^ m • z).toMul.1 m = y.toMul.1 m := by
  simp

section GaloisAction

variable (K : Type*) [Field K] [Algebra K L]

/-- The automorphism of a power-class group induced by a field automorphism. -/
def padicCompletionPowerClassMap (σ : L ≃ₐ[K] L) (m : ℕ) :
    (Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) ≃*
      (Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :=
  QuotientGroup.congrRangePowMonoidHom (Units.mapEquiv σ.toRingEquiv.toMulEquiv) (p ^ m)

omit [Fact p.Prime] in
/-- An automorphism acts on a power class through its action on a representative. -/
@[simp]
theorem padicCompletionPowerClassMap_mk (σ : L ≃ₐ[K] L) (m : ℕ) (x : Lˣ) :
    padicCompletionPowerClassMap p L K σ m
        (x : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) =
      (Units.map σ.toRingEquiv.toMonoidHom x : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :=
  QuotientGroup.congrRangePowMonoidHom_mk _ _ x

omit [Fact p.Prime] in
private theorem padicCompletionPowerClassMap_transition (σ : L ≃ₐ[K] L) (m : ℕ)
    (x : Lˣ ⧸ (powMonoidHom (p ^ (m + 1)) : Lˣ →* Lˣ).range) :
    padicCompletionTransition p L m (padicCompletionPowerClassMap p L K σ (m + 1) x) =
      padicCompletionPowerClassMap p L K σ m (padicCompletionTransition p L m x) := by
  induction x using QuotientGroup.induction_on with
  | H x => simp

omit [Fact p.Prime] in
private theorem padicCompletionPowerClassMap_symm (σ : L ≃ₐ[K] L) (m : ℕ) :
    (padicCompletionPowerClassMap p L K σ m).symm =
      padicCompletionPowerClassMap p L K σ.symm m := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [MulEquiv.symm_apply_eq, padicCompletionPowerClassMap_mk, padicCompletionPowerClassMap_mk]
    exact congrArg _ (Units.ext (by simp))

omit [Fact p.Prime] in
private theorem padicCompletionPowerClassMap_one (m : ℕ) :
    padicCompletionPowerClassMap p L K 1 m = MulEquiv.refl _ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [padicCompletionPowerClassMap_mk]
    exact congrArg _ (Units.ext (by simp))

omit [Fact p.Prime] in
private theorem padicCompletionPowerClassMap_mul (σ τ : L ≃ₐ[K] L) (m : ℕ) :
    padicCompletionPowerClassMap p L K (σ * τ) m =
      (padicCompletionPowerClassMap p L K τ m).trans (padicCompletionPowerClassMap p L K σ m) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    simp only [MulEquiv.trans_apply, padicCompletionPowerClassMap_mk]
    exact congrArg _ (Units.ext (by simp))

/-- A field automorphism acts coordinatewise on the completed multiplicative group. -/
private def padicCompletionUnitsMap (σ : L ≃ₐ[K] L) :
    ↑(padicCompletionUnits p L) →* ↑(padicCompletionUnits p L) :=
  MonoidHom.codRestrict
    ((MonoidHom.pi fun m ↦ (padicCompletionPowerClassMap p L K σ m).toMonoidHom.comp
      ((Pi.evalMonoidHom _ m).comp (padicCompletionUnits p L).subtype))) _ (by
    intro x
    rw [mem_padicCompletionUnits_iff]
    intro m
    have hx := (mem_padicCompletionUnits_iff p L x.1).mp x.2 m
    simp [padicCompletionPowerClassMap_transition, hx])

omit [Fact p.Prime] in
@[simp]
private theorem padicCompletionUnitsMap_apply (σ : L ≃ₐ[K] L)
    (x : ↑(padicCompletionUnits p L)) (m : ℕ) :
    (padicCompletionUnitsMap p L K σ x).1 m =
      padicCompletionPowerClassMap p L K σ m (x.1 m) := by
  simp [padicCompletionUnitsMap]

/-- A field automorphism acts on the completed multiplicative group by a group automorphism. -/
private def padicCompletionUnitsMulEquiv (σ : L ≃ₐ[K] L) :
    ↑(padicCompletionUnits p L) ≃* ↑(padicCompletionUnits p L) :=
  { padicCompletionUnitsMap p L K σ with
    invFun := padicCompletionUnitsMap p L K σ.symm
    left_inv x := by
      apply Subtype.ext
      funext m
      simp [← padicCompletionPowerClassMap_symm]
    right_inv x := by
      apply Subtype.ext
      funext m
      simp [← padicCompletionPowerClassMap_symm] }

omit [Fact p.Prime] in
@[simp]
private theorem padicCompletionUnitsMulEquiv_apply (σ : L ≃ₐ[K] L)
    (x : ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsMulEquiv p L K σ x = padicCompletionUnitsMap p L K σ x :=
  (rfl)

/-- The Galois action on the completed multiplicative group. -/
def padicCompletionUnitsAut :
    (L ≃ₐ[K] L) →* MulAut ↑(padicCompletionUnits p L) where
  toFun σ := padicCompletionUnitsMulEquiv p L K σ
  map_one' := by
    ext x m
    simp [padicCompletionPowerClassMap_one]
  map_mul' σ τ := by
    ext x m
    simp [padicCompletionPowerClassMap_mul]

omit [Fact p.Prime] in
/-- The Galois action on `A(L)` is induced coordinatewise from the action on `Lˣ`. -/
@[simp]
theorem padicCompletionUnitsAut_apply (σ : L ≃ₐ[K] L)
    (x : ↑(padicCompletionUnits p L)) (m : ℕ) :
    (padicCompletionUnitsAut p L K σ x).1 m =
      padicCompletionPowerClassMap p L K σ m (x.1 m) := by
  simp [padicCompletionUnitsAut]

omit [Fact p.Prime] in
/-- The Galois action sends the canonical class of a unit to the class of its conjugate. -/
@[simp]
theorem padicCompletionUnitsAut_of (σ : L ≃ₐ[K] L) (x : Lˣ) :
    padicCompletionUnitsAut p L K σ (padicCompletionUnitsOf p L x) =
      padicCompletionUnitsOf p L (Units.map σ.toRingEquiv.toMonoidHom x) := by
  ext m
  simp

/-- The Galois action regarded as a `ℤ_p`-linear endomorphism. -/
def padicCompletionUnitsLinearMap (σ : L ≃ₐ[K] L) :
    Additive ↑(padicCompletionUnits p L) →ₗ[ℤ_[p]]
      Additive ↑(padicCompletionUnits p L) where
  toFun x := Additive.ofMul (padicCompletionUnitsAut p L K σ x.toMul)
  map_add' x y := by
    apply Additive.toMul.injective
    exact map_mul (padicCompletionUnitsAut p L K σ) x.toMul y.toMul
  map_smul' a x := by
    apply Additive.toMul.injective
    ext m
    simp only [toMul_ofMul, RingHom.id_apply, padicCompletionUnitsAut_apply,
      padicCompletionUnits_smul_apply]
    exact map_pow _ _ _

/-- The `ℤ_p`-linear Galois action is the multiplicative Galois action. -/
@[simp]
theorem padicCompletionUnitsLinearMap_apply (σ : L ≃ₐ[K] L)
    (x : Additive ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsLinearMap p L K σ x =
      Additive.ofMul (padicCompletionUnitsAut p L K σ x.toMul) :=
  (rfl)

/-- The linear representation underlying the integral Galois module `A(L)`. -/
def padicCompletionUnitsRepresentation :
    Representation ℤ_[p] (L ≃ₐ[K] L) (Additive ↑(padicCompletionUnits p L)) where
  toFun σ := padicCompletionUnitsLinearMap p L K σ
  map_one' := LinearMap.ext fun x ↦ by simp
  map_mul' σ τ := LinearMap.ext fun x ↦ by simp

/-- The representation acts on `A(L)` through the `ℤ_p`-linear Galois action. -/
@[simp]
theorem padicCompletionUnitsRepresentation_apply (σ : L ≃ₐ[K] L) :
    padicCompletionUnitsRepresentation p L K σ = padicCompletionUnitsLinearMap p L K σ :=
  (rfl)

/-- The integral `ℤ_p[Gal(L/K)]`-module structure on `A(L)`: the `Representation.asModule`
structure of the Galois representation, placed on `A(L)` itself. -/
instance padicCompletionUnitsModule :
    Module (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (Additive ↑(padicCompletionUnits p L)) :=
  inferInstanceAs (Module _ (padicCompletionUnitsRepresentation p L K).asModule)

/-- A group-algebra monomial acts through the corresponding field automorphism, scaled by its
coefficient. -/
@[simp]
theorem padicCompletionUnits_single_smul (σ : L ≃ₐ[K] L) (a : ℤ_[p])
    (x : ↑(padicCompletionUnits p L)) :
    (MonoidAlgebra.single σ a : MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) • Additive.ofMul x =
      a • Additive.ofMul (padicCompletionUnitsAut p L K σ x) :=
  (padicCompletionUnitsRepresentation p L K).single_smul a σ (Additive.ofMul x)

/-- Restriction of the group-algebra action recovers the intrinsic `ℤ_p`-action on `A(L)`. -/
instance padicCompletionUnits_isScalarTower :
    IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (Additive ↑(padicCompletionUnits p L)) :=
  inferInstanceAs (IsScalarTower ℤ_[p] _ (padicCompletionUnitsRepresentation p L K).asModule)

variable {L K} in
/-- For a finite automorphism group, an element `x = ∑ σ, x_σ σ` of the group algebra acts on the
class of a unit `u` as the combination `∑ σ, x_σ [σ u]` of the classes of its conjugates. -/
theorem _root_.MonoidAlgebra.smul_padicCompletionUnitsOf [Fintype (L ≃ₐ[K] L)]
    (x : MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (u : Lˣ) :
    x • Additive.ofMul (padicCompletionUnitsOf p L u) =
      ∑ σ, x.coeff σ • Additive.ofMul
        (padicCompletionUnitsOf p L (Units.map σ.toRingEquiv.toMonoidHom u)) := by
  conv_lhs => rw [← x.sum_coeff_single]
  rw [Finsupp.sum_fintype _ _ fun σ ↦ by simp, Finset.sum_smul]
  simp [padicCompletionUnits_single_smul]

variable {L K} in
/-- For a finite automorphism group, the group algebra acts on the class of a unit fixed by every
automorphism through the augmentation. -/
theorem _root_.MonoidAlgebra.smul_padicCompletionUnitsOf_of_forall_eq [Finite (L ≃ₐ[K] L)]
    (x : MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) {u : Lˣ}
    (hu : ∀ σ : L ≃ₐ[K] L, Units.map σ.toRingEquiv.toMonoidHom u = u) :
    x • Additive.ofMul (padicCompletionUnitsOf p L u) =
      TauCeti.MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L) x •
        Additive.ofMul (padicCompletionUnitsOf p L u) := by
  have := Fintype.ofFinite (L ≃ₐ[K] L)
  rw [MonoidAlgebra.smul_padicCompletionUnitsOf]
  simp only [hu, ← Finset.sum_smul]
  congr 1
  conv_rhs => rw [← x.sum_coeff_single]
  rw [Finsupp.sum_fintype _ _ fun σ ↦ by simp, map_sum]
  simp

end GaloisAction

end TauCeti
