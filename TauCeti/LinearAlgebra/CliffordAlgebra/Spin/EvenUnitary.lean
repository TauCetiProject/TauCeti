/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map

/-!
# The even unitary carrier of a Clifford algebra

The even Clifford algebra carries the canonical reversal involution. On even elements this is
Mathlib's `star`, so the unitary equation `star x * x = 1` is the reverse-unitary equation used in
the low-dimensional descriptions of Spin groups. This file packages the even unitary elements as
a subgroup of Clifford units, transports that subgroup along quadratic isometries, and compares it
with Mathlib's Lipschitz-defined `spinGroup`.

The carrier is intentionally larger than `spinGroup`: the latter also requires membership in the
Lipschitz closure. The range theorem records that distinction exactly, so subsequent low-rank
arguments can prove when the two carriers coincide rather than building a second Spin definition.

The construction follows the Clifford-group conventions of H. B. Lawson and M.-L. Michelsohn,
*Spin Geometry* (1989), Chapter I §2, and uses Mathlib's `SpinGroup` and Tau Ceti's Clifford
functoriality API.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- Units whose Clifford values are even and unitary for the canonical star involution. -/
def evenUnitaryGroup : Subgroup (CliffordAlgebra Q)ˣ where
  carrier := {x | (x : CliffordAlgebra Q) ∈ even Q ∧
    (x : CliffordAlgebra Q) ∈ unitary (CliffordAlgebra Q)}
  one_mem' := by simp [Unitary.mem_iff]
  mul_mem' := by
    intro x y hx hy
    exact ⟨(even Q).mul_mem hx.1 hy.1,
      (unitary (CliffordAlgebra Q)).mul_mem hx.2 hy.2⟩
  inv_mem' := by
    intro x hx
    have hstar : star (x : CliffordAlgebra Q) ∈ even Q := by
      dsimp only [even] at hx ⊢
      simp only [Submodule.mem_toSubalgebra] at hx ⊢
      rw [star_def, reverse_mem_evenOdd_iff, involute_mem_evenOdd_iff]
      exact hx.1
    have hunit : star (x : CliffordAlgebra Q) ∈ unitary (CliffordAlgebra Q) :=
      Unitary.star_mem hx.2
    have hinv : ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        star (x : CliffordAlgebra Q) := by
      apply Units.inv_eq_of_mul_eq_one_right
      exact Unitary.mul_star_self_of_mem hx.2
    refine ⟨?_, ?_⟩
    · rw [hinv]
      exact hstar
    · rw [hinv]
      exact hunit

namespace evenUnitaryGroup

/-- Membership in `evenUnitaryGroup` is exactly evenness together with the unitary equation. -/
@[simp]
theorem mem_iff {x : (CliffordAlgebra Q)ˣ} :
    x ∈ evenUnitaryGroup Q ↔
      (x : CliffordAlgebra Q) ∈ even Q ∧
        (x : CliffordAlgebra Q) ∈ unitary (CliffordAlgebra Q) := Iff.rfl

theorem mem_even {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ evenUnitaryGroup Q) :
    (x : CliffordAlgebra Q) ∈ even Q :=
  hx.1

theorem mem_unitary {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ evenUnitaryGroup Q) :
    (x : CliffordAlgebra Q) ∈ unitary (CliffordAlgebra Q) :=
  hx.2

end evenUnitaryGroup

end CliffordAlgebra

namespace QuadraticMap.Isometry

universe u u' v' w' z'

variable {R : Type u} [CommRing R]
variable {M₁ : Type v'} {M₂ : Type w'} {M₃ : Type z'}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R M₁] [Module R M₂] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- The Clifford-algebra map of a quadratic isometry restricts to the even unitary carriers. -/
def evenUnitaryGroupMap (f : Q₁ →qᵢ Q₂) :
    CliffordAlgebra.evenUnitaryGroup Q₁ →* CliffordAlgebra.evenUnitaryGroup Q₂ where
  toFun x := by
    refine ⟨Units.map (CliffordAlgebra.map f).toMonoidHom x, ?_⟩
    constructor
    · exact CliffordAlgebra.map_mem_even f x.2.1
    · rw [Unitary.mem_iff]
      have hmap :
          (↑(Units.map (CliffordAlgebra.map f).toMonoidHom (x : (CliffordAlgebra Q₁)ˣ)) :
              CliffordAlgebra Q₂) = CliffordAlgebra.map f
                ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) := by
        simp only [Units.coe_map]
        -- The algebra-map and ring-hom coercions coincide definitionally here.
        rfl
      constructor
      · rw [hmap, ← CliffordAlgebra.map_star, ← map_mul,
          Unitary.star_mul_self_of_mem x.2.2, map_one]
      · rw [hmap, ← CliffordAlgebra.map_star, ← map_mul,
          Unitary.mul_star_self_of_mem x.2.2, map_one]
  map_one' := by simp
  map_mul' x y := by simp

/-- After coercion, the induced map is the `Units.map` of the Clifford-algebra map. -/
@[simp]
theorem coe_evenUnitaryGroupMap_apply (f : Q₁ →qᵢ Q₂)
    (x : CliffordAlgebra.evenUnitaryGroup Q₁) :
    ((f.evenUnitaryGroupMap x : CliffordAlgebra.evenUnitaryGroup Q₂) : (CliffordAlgebra Q₂)ˣ) =
      Units.map (CliffordAlgebra.map f).toMonoidHom (x : (CliffordAlgebra Q₁)ˣ) := by
  rfl

/-- The identity quadratic isometry induces the identity even-unitary-group homomorphism. -/
@[simp]
theorem evenUnitaryGroupMap_id (Q : QuadraticForm R M₁) :
    (QuadraticMap.Isometry.id Q).evenUnitaryGroupMap = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  simp

/-- Even-unitary-group homomorphisms respect composition of quadratic isometries. -/
@[simp]
theorem evenUnitaryGroupMap_comp (f : Q₂ →qᵢ Q₃)
    (g : Q₁ →qᵢ Q₂) :
    (f.evenUnitaryGroupMap).comp (g.evenUnitaryGroupMap) =
      (f.comp g).evenUnitaryGroupMap := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun h : CliffordAlgebra Q₁ →ₐ[R] CliffordAlgebra Q₃ =>
      h ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁))
    (CliffordAlgebra.map_comp_map f g)

end QuadraticMap.Isometry

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- The Spin units are precisely the Lipschitz units that lie in the even unitary carrier. -/
@[simp]
theorem range_spinGroup_toUnits :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range =
      (lipschitzGroup Q) ⊓ evenUnitaryGroup Q := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨spinGroup.units_mem_lipschitzGroup g.2, ?_⟩
    exact ⟨g.2.2, g.2.1.2⟩
  · intro hx
    rcases hx with ⟨hLip, hEvenUnit⟩
    have hEven : (x : CliffordAlgebra Q) ∈ even Q := hEvenUnit.1
    have hUnitary : (x : CliffordAlgebra Q) ∈ unitary (CliffordAlgebra Q) := hEvenUnit.2
    have hPin : (x : CliffordAlgebra Q) ∈ pinGroup Q := by
      rw [pinGroup.mem_iff]
      exact ⟨lipschitzGroup.coe_mem_iff_mem.mpr hLip, hUnitary⟩
    refine ⟨⟨(x : CliffordAlgebra Q), hPin, hEven⟩, ?_⟩
    apply Units.ext
    rfl

end CliffordAlgebra
