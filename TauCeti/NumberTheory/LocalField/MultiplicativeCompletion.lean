/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The p-adic completion of a multiplicative group

For a prime `p` and a field `L`, this file constructs the inverse limit

`A(L) = lim_m Lˣ / (Lˣ)^(p^m)`.

The carrier is the subgroup of the product of the power-class groups consisting of compatible
families.  Its `ℤ_p`-module structure is intrinsic: at level `m`, a `p`-adic integer acts
through its residue modulo `p^m`.  Field automorphisms preserve power subgroups, and therefore
act on the whole inverse limit.

The construction is the integral multiplicative lattice used in local reciprocity and in the
Galois-module theory of local units.

## Main declarations

* `padicCompletionUnits`: the inverse-limit carrier `A(L)`.
* `padicCompletionUnitsPadicModule`: its intrinsic `ℤ_p`-module structure.
* `padicCompletionUnitsAut`: the coordinatewise Galois action.
* `padicCompletionUnitsModule`: the resulting `ℤ_p[Gal(L/K)]`-module structure.

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
  QuotientGroup.map _ _ (MonoidHom.id Lˣ) (by
    rintro _ ⟨x, rfl⟩
    refine ⟨x ^ p, ?_⟩
    simp only [powMonoidHom_apply, MonoidHom.id_apply, ← pow_mul]
    rw [← pow_succ'])

/-- `A(L) = lim_m Lˣ/(Lˣ)^(p^m)`, realized as the subgroup of compatible families in the
product of the power-class groups. -/
def padicCompletionUnits :
    Subgroup (∀ m : ℕ, Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :=
  ⨅ m : ℕ, MonoidHom.eqLocus
    ((padicCompletionTransition p L m).comp (Pi.evalMonoidHom _ (m + 1)))
    (Pi.evalMonoidHom _ m)

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
    intro x
    rw [mem_padicCompletionUnits_iff]
    intro m
    rfl)

omit [Fact p.Prime] in
/-- The `m`-th coordinate of the canonical map is the power-class quotient map. -/
@[simp]
theorem padicCompletionUnitsOf_apply (x : Lˣ) (m : ℕ) :
    (padicCompletionUnitsOf p L x).1 m =
      QuotientGroup.mk' _ x :=
  by simp [padicCompletionUnitsOf]

omit [Fact p.Prime] in
/-- Every `p^m`-power class is killed by `p^m`. -/
private theorem pow_powerClass_eq_one (m : ℕ)
    (x : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :
    x ^ p ^ m = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  -- Expose the quotient coercion so that the standard membership criterion applies.
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨x, rfl⟩

/-- The additive form of `A(L)` carries the commutative group structure of the inverse limit. -/
instance padicCompletionUnitsAddCommGroup :
    AddCommGroup (Additive ↑(padicCompletionUnits p L)) :=
  Additive.addCommGroup

/-- The intrinsic `ℤ_p`-module structure on the completed multiplicative group. -/
instance padicCompletionUnitsPadicModule :
    Module ℤ_[p] (Additive ↑(padicCompletionUnits p L)) where
  smul a x := Additive.ofMul ⟨fun m ↦ x.toMul.1 m ^ a.appr m, by
      rw [mem_padicCompletionUnits_iff]
      intro m
      have hx := (mem_padicCompletionUnits_iff p L x.toMul.1).mp x.toMul.2 m
      rw [map_pow, hx]
      exact PadicInt.pow_appr_eq_pow_appr a (pow_powerClass_eq_one p L m _) (Nat.le_succ m)⟩
  one_smul x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    -- Unfold only the scalar field being verified; the coordinate action is truncated power.
    change x.toMul.1 m ^ ((1 : ℤ_[p]).appr m) = x.toMul.1 m
    simpa only [Nat.cast_one, pow_one] using
      pow_eq_pow_of_modEq (PadicInt.appr_natCast_modEq 1 m)
        (pow_powerClass_eq_one p L m _)
  mul_smul a b x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    change x.toMul.1 m ^ (a * b).appr m =
      (x.toMul.1 m ^ b.appr m) ^ a.appr m
    rw [← pow_mul, mul_comm (b.appr m)]
    exact pow_eq_pow_of_modEq (PadicInt.appr_mul_modEq a b m)
      (pow_powerClass_eq_one p L m _)
  smul_zero a := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    change (1 : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) ^ a.appr m = 1
    simp
  smul_add a x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    change (x.toMul.1 m * y.toMul.1 m) ^ a.appr m =
      x.toMul.1 m ^ a.appr m * y.toMul.1 m ^ a.appr m
    exact map_mul
      (powMonoidHom (α := Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) (a.appr m)) _ _
  add_smul a b x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    change x.toMul.1 m ^ (a + b).appr m =
      x.toMul.1 m ^ a.appr m * x.toMul.1 m ^ b.appr m
    rw [← pow_add]
    exact pow_eq_pow_of_modEq (PadicInt.appr_add_modEq a b m)
      (pow_powerClass_eq_one p L m _)
  zero_smul x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext m
    change x.toMul.1 m ^ (0 : ℤ_[p]).appr m = 1
    simpa only [Nat.cast_zero, pow_zero] using
      pow_eq_pow_of_modEq (PadicInt.appr_natCast_modEq 0 m)
        (pow_powerClass_eq_one p L m _)

/-- Scalar multiplication in the completion is truncated exponentiation in every coordinate. -/
@[simp]
theorem padicCompletionUnits_smul_apply (a : ℤ_[p])
    (x : Additive ↑(padicCompletionUnits p L)) (m : ℕ) :
    (a • x).toMul.1 m = x.toMul.1 m ^ a.appr m :=
  (rfl)

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
    (pow_powerClass_eq_one p L m (x.toMul.1 m))

section GaloisAction

variable (K : Type*) [Field K] [Algebra K L]

/-- The map on a power-class group induced by a field automorphism. -/
def padicCompletionPowerClassMap (σ : L ≃ₐ[K] L) (m : ℕ) :
    (Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) →*
      (Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :=
  QuotientGroup.map _ _ (Units.map σ.toRingEquiv.toMonoidHom) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨Units.map σ.toRingEquiv.toMonoidHom x, by simp⟩)

omit [Fact p.Prime] in
/-- An automorphism acts on a power class through its action on a representative. -/
@[simp]
theorem padicCompletionPowerClassMap_mk (σ : L ≃ₐ[K] L) (m : ℕ) (x : Lˣ) :
    padicCompletionPowerClassMap p L K σ m
        (x : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) =
      (Units.map σ.toRingEquiv.toMonoidHom x : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) :=
  QuotientGroup.map_mk _ _ _ _ x

omit [Fact p.Prime] in
private theorem padicCompletionPowerClassMap_transition (σ : L ≃ₐ[K] L) (m : ℕ)
    (x : Lˣ ⧸ (powMonoidHom (p ^ (m + 1)) : Lˣ →* Lˣ).range) :
    padicCompletionTransition p L m (padicCompletionPowerClassMap p L K σ (m + 1) x) =
      padicCompletionPowerClassMap p L K σ m (padicCompletionTransition p L m x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rfl

/-- A field automorphism acts coordinatewise on the completed multiplicative group. -/
private def padicCompletionUnitsMap (σ : L ≃ₐ[K] L) :
    ↑(padicCompletionUnits p L) →* ↑(padicCompletionUnits p L) where
  toFun x := ⟨fun m ↦ padicCompletionPowerClassMap p L K σ m (x.1 m), by
    rw [mem_padicCompletionUnits_iff]
    intro m
    have hx := (mem_padicCompletionUnits_iff p L x.1).mp x.2 m
    rw [padicCompletionPowerClassMap_transition, hx]⟩
  map_one' := by
    apply Subtype.ext
    funext m
    change padicCompletionPowerClassMap p L K σ m 1 = 1
    exact map_one _
  map_mul' x y := by
    apply Subtype.ext
    funext m
    change padicCompletionPowerClassMap p L K σ m (x.1 m * y.1 m) =
      padicCompletionPowerClassMap p L K σ m (x.1 m) *
        padicCompletionPowerClassMap p L K σ m (y.1 m)
    exact map_mul _ _ _

omit [Fact p.Prime] in
@[simp]
private theorem padicCompletionUnitsMap_apply (σ : L ≃ₐ[K] L)
    (x : ↑(padicCompletionUnits p L)) (m : ℕ) :
    (padicCompletionUnitsMap p L K σ x).1 m =
      padicCompletionPowerClassMap p L K σ m (x.1 m) :=
  rfl

omit [Fact p.Prime] in
private theorem padicCompletionUnitsMap_comp (σ τ : L ≃ₐ[K] L)
    (x : ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsMap p L K (σ * τ) x =
      padicCompletionUnitsMap p L K σ (padicCompletionUnitsMap p L K τ x) := by
  apply Subtype.ext
  funext m
  change padicCompletionPowerClassMap p L K (σ * τ) m (x.1 m) =
    padicCompletionPowerClassMap p L K σ m
      (padicCompletionPowerClassMap p L K τ m (x.1 m))
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective _ (x.1 m)
  rw [← hy]
  rfl

/-- The Galois action on the completed multiplicative group. -/
def padicCompletionUnitsAut :
    (L ≃ₐ[K] L) →* MulAut ↑(padicCompletionUnits p L) where
  toFun σ :=
    { padicCompletionUnitsMap p L K σ with
      invFun := padicCompletionUnitsMap p L K σ.symm
      left_inv x := by
        apply Subtype.ext
        funext m
        change padicCompletionPowerClassMap p L K σ.symm m
          (padicCompletionPowerClassMap p L K σ m (x.1 m)) = x.1 m
        obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (x.1 m)
        rw [← hy, padicCompletionPowerClassMap_mk, padicCompletionPowerClassMap_mk]
        congr 1
        ext
        simp
      right_inv x := by
        apply Subtype.ext
        funext m
        change padicCompletionPowerClassMap p L K σ m
          (padicCompletionPowerClassMap p L K σ.symm m (x.1 m)) = x.1 m
        obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (x.1 m)
        rw [← hy, padicCompletionPowerClassMap_mk, padicCompletionPowerClassMap_mk]
        congr 1
        ext
        simp }
  map_one' := by
    apply MulEquiv.ext
    intro x
    change padicCompletionUnitsMap p L K 1 x = x
    apply Subtype.ext
    funext m
    change padicCompletionPowerClassMap p L K 1 m (x.1 m) = x.1 m
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective _ (x.1 m)
    rw [← hy]
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    change padicCompletionUnitsMap p L K (σ * τ) x =
      padicCompletionUnitsMap p L K σ (padicCompletionUnitsMap p L K τ x)
    exact padicCompletionUnitsMap_comp p L K σ τ x

omit [Fact p.Prime] in
/-- The Galois action on `A(L)` is induced coordinatewise from the action on `Lˣ`. -/
@[simp]
theorem padicCompletionUnitsAut_apply (σ : L ≃ₐ[K] L)
    (x : ↑(padicCompletionUnits p L)) (m : ℕ) :
    (padicCompletionUnitsAut p L K σ x).1 m =
      padicCompletionPowerClassMap p L K σ m (x.1 m) := by
  exact padicCompletionUnitsMap_apply p L K σ x m

omit [Fact p.Prime] in
/-- The Galois action sends the canonical class of a unit to the class of its conjugate. -/
@[simp]
theorem padicCompletionUnitsAut_of (σ : L ≃ₐ[K] L) (x : Lˣ) :
    padicCompletionUnitsAut p L K σ (padicCompletionUnitsOf p L x) =
      padicCompletionUnitsOf p L (Units.map σ.toRingEquiv.toMonoidHom x) := by
  apply Subtype.ext
  funext m
  change padicCompletionPowerClassMap p L K σ m (QuotientGroup.mk' _ x) =
    QuotientGroup.mk' _ (Units.map σ.toRingEquiv.toMonoidHom x)
  exact padicCompletionPowerClassMap_mk p L K σ m x

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
    apply Subtype.ext
    funext m
    change padicCompletionPowerClassMap p L K σ m (x.toMul.1 m ^ a.appr m) =
      padicCompletionPowerClassMap p L K σ m (x.toMul.1 m) ^ a.appr m
    exact map_pow _ _ _

/-- The linear representation underlying the integral Galois module `A(L)`. -/
def padicCompletionUnitsRepresentation :
    Representation ℤ_[p] (L ≃ₐ[K] L) (Additive ↑(padicCompletionUnits p L)) where
  toFun σ := padicCompletionUnitsLinearMap p L K σ
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    change padicCompletionUnitsAut p L K 1 x.toMul = x.toMul
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    change padicCompletionUnitsAut p L K (σ * τ) x.toMul =
      padicCompletionUnitsAut p L K σ (padicCompletionUnitsAut p L K τ x.toMul)
    rw [map_mul]
    rfl

/-- The integral `ℤ_p[Gal(L/K)]`-module structure on `A(L)`. -/
instance padicCompletionUnitsModule :
    Module (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (Additive ↑(padicCompletionUnits p L)) :=
  Module.compHom _
    (padicCompletionUnitsRepresentation p L K).asAlgebraHom.toRingHom

/-- A group element in the group algebra acts through the corresponding field automorphism. -/
@[simp]
theorem padicCompletionUnits_single_smul (σ : L ≃ₐ[K] L)
    (x : ↑(padicCompletionUnits p L)) :
    (MonoidAlgebra.single σ (1 : ℤ_[p]) : MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) •
        Additive.ofMul x = Additive.ofMul (padicCompletionUnitsAut p L K σ x) := by
  change (padicCompletionUnitsRepresentation p L K).asAlgebraHom
    (MonoidAlgebra.single σ 1) (Additive.ofMul x) = _
  rw [Representation.asAlgebraHom_single]
  simp only [one_smul]
  rfl

/-- Restriction of the group-algebra action recovers the intrinsic `ℤ_p`-action on `A(L)`. -/
instance padicCompletionUnits_isScalarTower :
    IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (Additive ↑(padicCompletionUnits p L)) :=
  IsScalarTower.of_algebraMap_smul fun a x ↦ by
    change (padicCompletionUnitsRepresentation p L K).asAlgebraHom
      (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) a) x = a • x
    rw [AlgHom.commutes]
    rfl

end GaloisAction

end TauCeti
