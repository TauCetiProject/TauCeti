/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CongruenceSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic

/-!
# Congruence subgroups of the multiplicative group

Under the identification `TauCeti.MultiplicativeGroup.pointsMulEquiv` of the points of `𝔾ₘ` with
units, the congruence subgroup of level `I` is the group of units congruent to `1` modulo `I`.
Over the valuation ring `𝒪[K]` of a nonarchimedean local field `K`, the congruence subgroups of
the levels `𝓂[K] ^ i` are therefore the steps `U(K,i)` of the unit filtration
`TauCeti.unitFiltration`.

## Main declarations

* `TauCeti.MultiplicativeGroup.map_congruenceSubgroup`: the image of the congruence subgroup of
  level `I` is the kernel of reduction of units modulo `I`.
* `TauCeti.MultiplicativeGroup.mem_congruenceSubgroup_iff`: a point `x` lies in the congruence
  subgroup of level `I` exactly when the unit it represents is congruent to `1` modulo `I`.
* `TauCeti.MultiplicativeGroup.map_map_congruenceSubgroup_eq_unitFiltration`: the congruence
  subgroups of `𝔾ₘ` over `𝒪[K]` map onto the unit filtration of `K`.
-/

public section

open scoped LaurentPolynomial

namespace TauCeti

namespace MultiplicativeGroup

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- Under `pointsMulEquiv`, the congruence subgroup of level `I` of `𝔾ₘ` is the kernel of the
reduction map `Aˣ → (A ⧸ I)ˣ`. -/
theorem map_congruenceSubgroup (I : Ideal A) :
    (HopfAlgebra.congruenceSubgroup R R[T;T⁻¹] I).map
        (pointsMulEquiv (R := R) (A := A)).toMonoidHom =
      (Units.map (Ideal.Quotient.mk I : A →* A ⧸ I)).ker := by
  ext u
  rw [Subgroup.mem_map_equiv, HopfAlgebra.mem_congruenceSubgroup_iff_mapValue_eq_one,
    MonoidHom.mem_ker, ← (pointsMulEquiv (R := R) (A := A ⧸ I)).map_eq_one_iff,
    pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply]
  simp only [Units.ext_iff, Units.coe_map, MonoidHom.coe_ofClass, Ideal.Quotient.mkₐ_eq_mk]

/-- A point of `𝔾ₘ` lies in the congruence subgroup of level `I` exactly when the unit it
represents is congruent to `1` modulo `I`. -/
theorem mem_congruenceSubgroup_iff {I : Ideal A} {x : WithConv (R[T;T⁻¹] →ₐ[R] A)} :
    x ∈ HopfAlgebra.congruenceSubgroup R R[T;T⁻¹] I ↔ ((pointsMulEquiv x : Aˣ) : A) - 1 ∈ I := by
  rw [← Subgroup.mem_map_iff_mem (f := (pointsMulEquiv (R := R) (A := A)).toMonoidHom)
    pointsMulEquiv.injective, map_congruenceSubgroup, MonoidHom.mem_ker, Units.ext_iff,
    Units.coe_map, Units.val_one, ← map_one (Ideal.Quotient.mk I), MonoidHom.coe_ofClass,
    Ideal.Quotient.eq, MulEquiv.coe_toMonoidHom]

section LocalField

open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Over the valuation ring `𝒪[K]` of a nonarchimedean local field `K`, the congruence subgroup of
level `𝓂[K] ^ i` of `𝔾ₘ` is the step `U(K,i)` of the unit filtration of `K`, once units of
`𝒪[K]` are viewed in `Kˣ`. -/
theorem map_map_congruenceSubgroup_eq_unitFiltration (i : ℕ) :
    ((HopfAlgebra.congruenceSubgroup 𝒪[K] 𝒪[K][T;T⁻¹] (𝓂[K] ^ i)).map
        (pointsMulEquiv (R := 𝒪[K]) (A := 𝒪[K])).toMonoidHom).map
      (Units.map (Subring.subtype 𝒪[K]).toMonoidHom) = unitFiltration K i := by
  ext x
  simp only [map_congruenceSubgroup, mem_unitFiltration_iff_exists, Subgroup.mem_map,
    MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one, MonoidHom.coe_ofClass,
    RingHom.toMonoidHom_eq_coe, Subring.coe_subtype, ← map_one (Ideal.Quotient.mk (𝓂[K] ^ i)),
    Ideal.Quotient.eq]

end LocalField

end MultiplicativeGroup

end TauCeti
