/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
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

The theorem `CliffordAlgebra.evenUnitaryGroupEquivUnitaryOfAlgEquiv` transports this carrier along
any algebra equivalence from the even Clifford algebra that carries reversal to the target star.
Its coercion equations expose the forward and inverse maps without unfolding the construction.

The construction follows the Clifford-group conventions of H. B. Lawson and M.-L. Michelsohn,
*Spin Geometry* (1989), Chapter I §2, and uses Mathlib's `SpinGroup` and Tau Ceti's Clifford
functoriality API.

## Main results

* `CliffordAlgebra.evenUnitaryGroup.mem_iff_reverse_mul_self_eq_one` characterizes the carrier
  by the reverse-norm equation.
* `CliffordAlgebra.evenUnitaryGroup.reverse_mul_self` and
  `CliffordAlgebra.evenUnitaryGroup.self_mul_reverse` give its two norm equations.
* `CliffordAlgebra.evenUnitaryGroup.reverse_eq_inv` identifies reversal with the unit inverse.
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

/-- An even Clifford unit lies in `evenUnitaryGroup` exactly when its reverse norm is one. -/
theorem mem_iff_reverse_mul_self_eq_one {x : (CliffordAlgebra Q)ˣ} :
    x ∈ evenUnitaryGroup Q ↔
      (x : CliffordAlgebra Q) ∈ even Q ∧
        reverse (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q) = 1 := by
  rw [mem_iff]
  constructor
  · rintro ⟨heven, hunitary⟩
    refine ⟨heven, ?_⟩
    rw [← star_mul_self_eq_reverse_mul_self_of_mem_even heven]
    exact Unitary.star_mul_self_of_mem hunitary
  · rintro ⟨heven, hreverse⟩
    refine ⟨heven, ?_⟩
    apply x.isUnit.mem_unitary_of_star_mul_self
    rw [star_mul_self_eq_reverse_mul_self_of_mem_even heven]
    exact hreverse

/-- The reverse norm of an even unitary Clifford element is one. -/
theorem reverse_mul_self (x : evenUnitaryGroup Q) :
    reverse ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1 :=
  (mem_iff_reverse_mul_self_eq_one Q).mp x.2 |>.2

/-- The right-handed reverse norm of an even unitary Clifford element is one. -/
theorem self_mul_reverse (x : evenUnitaryGroup Q) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      reverse ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1 := by
  apply self_mul_reverse_of_reverse_mul_self
  exact (reverse_mul_self Q x).trans
    (map_one (algebraMap R (CliffordAlgebra Q))).symm

/-- Reversal of an even unitary Clifford element is its unit inverse after coercion. -/
@[simp]
theorem reverse_eq_inv (x : evenUnitaryGroup Q) :
    reverse ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  exact Units.eq_inv_of_mul_eq_one_right (reverse_mul_self Q x)

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

universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- Forget an even unitary Clifford unit to its value in the even Clifford subalgebra. -/
def evenUnitaryGroupEvenPart : evenUnitaryGroup Q →* even Q where
  toFun x := ⟨((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q), x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Coercing the even part of an even unitary element recovers its Clifford value. -/
@[simp]
theorem coe_evenUnitaryGroupEvenPart (x : evenUnitaryGroup Q) :
    (evenUnitaryGroupEvenPart Q x : CliffordAlgebra Q) =
      ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  simp [evenUnitaryGroupEvenPart]

section Transport

variable {A : Type w} [Ring A] [Algebra R A] [StarRing A]

private noncomputable def evenUnitaryGroupToUnitaryOfAlgEquiv
    (e : even Q ≃ₐ[R] A) (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    evenUnitaryGroup Q →* unitary A :=
  (e.toMonoidHom.comp (evenUnitaryGroupEvenPart Q)).codRestrict (unitary A) fun x => by
    let a := evenUnitaryGroupEvenPart Q x
    let uEven : (even Q)ˣ :=
      { val := a
        inv := evenUnitaryGroupEvenPart Q x⁻¹
        val_inv := by apply Subtype.ext; simp [a]
        inv_val := by apply Subtype.ext; simp [a] }
    have hunit : IsUnit (e a) := by
      exact IsUnit.map e.toMonoidHom (Units.isUnit uEven)
    change e a ∈ unitary A
    rw [IsUnit.mem_unitary_iff_star_mul_self hunit]
    change star (e a) * e a = 1
    have h : reverseEven Q a * a = 1 := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, Subalgebra.coe_one, coe_reverseEven_apply]
      change reverse (((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
          ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1
      exact evenUnitaryGroup.reverse_mul_self Q x
    calc
      star (e a) * e a = e (reverseEven Q a) * e a := by rw [he]
      _ = e (reverseEven Q a * a) := (map_mul e _ _).symm
      _ = e 1 := congrArg e h
      _ = 1 := map_one e

private noncomputable def unitaryToEvenUnitaryGroupOfAlgEquiv
    (e : even Q ≃ₐ[R] A) (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    unitary A →* evenUnitaryGroup Q where
  toFun q := by
    let a : even Q := e.symm (q : A)
    let uEven : (even Q)ˣ := Units.mapEquiv e.toMulEquiv |>.symm (Unitary.toUnits q)
    let u : (CliffordAlgebra Q)ˣ := Units.map (even Q).val.toMonoidHom uEven
    refine ⟨u, ?_⟩
    have hu : (u : CliffordAlgebra Q) = a := rfl
    rw [evenUnitaryGroup.mem_iff]
    refine ⟨hu ▸ a.2, ?_⟩
    rw [IsUnit.mem_unitary_iff_star_mul_self (Units.isUnit u), hu,
      ← reverse_eq_star_of_mem_even a]
    have h : reverseEven Q a * a = 1 := by
      apply e.injective
      have ha : e a = (q : A) := by simp [a]
      rw [map_mul, he, ha, map_one]
      exact Unitary.star_mul_self_of_mem q.2
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_one, coe_reverseEven_apply] using
      congrArg Subtype.val h
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp
  map_mul' q r := by
    apply Subtype.ext
    apply Units.ext
    simp

/-- A reversal-preserving equivalence from the even Clifford algebra transports its even unitary
carrier to the unitary group of the target algebra. -/
noncomputable def evenUnitaryGroupEquivUnitaryOfAlgEquiv
    (e : even Q ≃ₐ[R] A) (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    evenUnitaryGroup Q ≃* unitary A where
  toFun := evenUnitaryGroupToUnitaryOfAlgEquiv Q e he
  invFun := unitaryToEvenUnitaryGroupOfAlgEquiv Q e he
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    simp [evenUnitaryGroupToUnitaryOfAlgEquiv, unitaryToEvenUnitaryGroupOfAlgEquiv,
      evenUnitaryGroupEvenPart]
  right_inv q := by
    apply Subtype.ext
    simp [evenUnitaryGroupToUnitaryOfAlgEquiv, unitaryToEvenUnitaryGroupOfAlgEquiv,
      evenUnitaryGroupEvenPart]
  map_mul' := map_mul (evenUnitaryGroupToUnitaryOfAlgEquiv Q e he)

/-- The forward unitary transport applies the algebra equivalence to the even Clifford value. -/
@[simp]
theorem coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply
    (e : even Q ≃ₐ[R] A) (he : ∀ x, e (reverseEven Q x) = star (e x))
    (x : evenUnitaryGroup Q) :
    (evenUnitaryGroupEquivUnitaryOfAlgEquiv Q e he x : A) =
      e (evenUnitaryGroupEvenPart Q x) := by
  simp [evenUnitaryGroupEquivUnitaryOfAlgEquiv,
    evenUnitaryGroupToUnitaryOfAlgEquiv]

/-- The inverse unitary transport has Clifford value obtained by applying the inverse algebra
equivalence. -/
@[simp]
theorem coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_symm_apply
    (e : even Q ≃ₐ[R] A) (he : ∀ x, e (reverseEven Q x) = star (e x)) (q : unitary A) :
    ((((evenUnitaryGroupEquivUnitaryOfAlgEquiv Q e he).symm q : evenUnitaryGroup Q) :
        (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = (e.symm (q : A) : even Q) := by
  simp [evenUnitaryGroupEquivUnitaryOfAlgEquiv,
    unitaryToEvenUnitaryGroupOfAlgEquiv]

end Transport

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
