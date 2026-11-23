/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Topology.Covering.Quotient
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The finite cover `S¹ × SU(n) → U(n)`

Multiplying a special unitary matrix by a scalar of modulus one gives a continuous homomorphism

`S¹ × SU(n) → U(n)`, `(z, A) ↦ z A`

(`TauCeti.circleProdSpecialUnitary`). It is onto, since every unitary matrix becomes
special unitary after rescaling by a `card n`-th root of the inverse of its determinant
(`Matrix.exists_circle_smul_mem_specialUnitaryGroup`). A pair `(z, A)` lies in its kernel exactly
when `A = z⁻¹ I` (`TauCeti.mem_ker_circleProdSpecialUnitary_iff`), and then
`det A = z⁻ⁿ = 1`, with `n = card n`. So the first projection identifies the kernel with the group
of `n`-th roots of unity of the circle, embedded as `ζ ↦ (ζ, ζ⁻¹ I)`
(`TauCeti.kerCircleProdSpecialUnitaryEquiv`), and the kernel has `n` elements
(`TauCeti.natCard_ker_circleProdSpecialUnitary`).

For a nonempty index type the kernel is a finite, hence discrete, subgroup, and a continuous
surjective homomorphism from the compact group `S¹ × SU(n)` onto the Hausdorff group `U(n)` is a
quotient map. So the homomorphism is the quotient of `S¹ × SU(n)` by its kernel, a covering map
(`TauCeti.isQuotientCoveringMap_circleProdSpecialUnitary`,
`TauCeti.isCoveringMap_circleProdSpecialUnitary`) each of whose fibres has `n` points
(`TauCeti.natCard_preimage_circleProdSpecialUnitary`).

This is the decomposition of a compact connected Lie group as a finite quotient `(T × K) / Γ` of
the product of a torus `T` and a simply connected semisimple compact group `K`, for `G = U(n)`:
here `T = S¹` is the identity component of the centre, `K = SU(n)`, and the cover has degree `n`.
For the empty index type `U(n)` and `SU(n)` are trivial, the kernel is the whole circle
(`rootsOfUnity 0` is everything), and the map is not a covering.

## Main definitions

* `TauCeti.circleProdSpecialUnitary`: the homomorphism `(z, A) ↦ z A`.
* `TauCeti.kerCircleProdSpecialUnitaryEquiv`: its kernel is the group of `n`-th
  roots of unity of the circle.

## Main results

* `TauCeti.circleProdSpecialUnitary_surjective`: the homomorphism is onto.
* `TauCeti.natCard_ker_circleProdSpecialUnitary`: its kernel has `n` elements.
* `TauCeti.isCoveringMap_circleProdSpecialUnitary`: it is a covering map.
* `TauCeti.natCard_preimage_circleProdSpecialUnitary`: every fibre has `n` points.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, Theorem 8.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
-/

public section

open Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`U(n)` from the circle and `SU(n)`**: the homomorphism `S¹ × SU(n) → U(n)`,
`(z, A) ↦ z A`. -/
noncomputable def circleProdSpecialUnitary :
    Circle × specialUnitaryGroup n ℂ →* unitaryGroup n ℂ where
  toFun p := ⟨(p.1 : ℂ) • (p.2 : Matrix n n ℂ),
    Unitary.smul_mem_of_mem p.1.coe_mem_unitary (mem_specialUnitaryGroup_iff.1 p.2.property).1⟩
  map_one' := Subtype.ext <| by simp
  map_mul' p q := Subtype.ext <| by
    simp only [Prod.fst_mul, Prod.snd_mul, Circle.coe_mul, Submonoid.coe_mul]
    exact (smul_mul_smul_comm _ _ _ _).symm

/-- The matrix `z A` given by a point `(z, A)` of `S¹ × SU(n)`. -/
@[simp]
theorem coe_circleProdSpecialUnitary_apply (p : Circle × specialUnitaryGroup n ℂ) :
    (circleProdSpecialUnitary p : Matrix n n ℂ) = (p.1 : ℂ) • (p.2 : Matrix n n ℂ) :=
  (rfl)

/-- The homomorphism `(z, A) ↦ z A` is continuous. -/
theorem continuous_circleProdSpecialUnitary :
    Continuous (circleProdSpecialUnitary : Circle × specialUnitaryGroup n ℂ → unitaryGroup n ℂ) :=
  ((continuous_subtypeVal.comp continuous_fst).smul
    (continuous_subtypeVal.comp continuous_snd)).subtype_mk _

/-- Every unitary matrix is `z A` for a point `z` of the circle and a special unitary matrix
`A`. -/
theorem circleProdSpecialUnitary_surjective :
    Function.Surjective (circleProdSpecialUnitary (n := n)) := by
  intro U
  obtain ⟨c, hc⟩ := exists_circle_smul_mem_specialUnitaryGroup U
  refine ⟨(c⁻¹, ⟨_, hc⟩), Subtype.ext ?_⟩
  rw [coe_circleProdSpecialUnitary_apply]
  exact inv_smul_smul c (U : Matrix n n ℂ)

/-- A pair `(z, A)` maps to the identity exactly when `A` is the scalar matrix `z⁻¹ I`. -/
theorem mem_ker_circleProdSpecialUnitary_iff (p : Circle × specialUnitaryGroup n ℂ) :
    p ∈ (circleProdSpecialUnitary (n := n)).ker ↔
      (p.2 : Matrix n n ℂ) = ((p.1⁻¹ : Circle) : ℂ) • 1 := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, coe_circleProdSpecialUnitary_apply,
    UnitaryGroup.one_val, ← Circle.smul_def, ← Circle.smul_def, eq_inv_smul_iff]

/-- The first coordinate of a point of the kernel is a `card n`-th root of unity: the second
coordinate `z⁻¹ I` has determinant `z⁻ⁿ`, which must be one. -/
theorem pow_card_eq_one_of_mem_ker_circleProdSpecialUnitary {p : Circle × specialUnitaryGroup n ℂ}
    (hp : p ∈ (circleProdSpecialUnitary (n := n)).ker) : p.1 ^ Fintype.card n = 1 := by
  rw [← inv_eq_one, ← inv_pow, ← circle_smul_one_mem_specialUnitaryGroup_iff,
    ← (mem_ker_circleProdSpecialUnitary_iff p).1 hp]
  exact p.2.property

/-- **The kernel of `S¹ × SU(n) → U(n)` is the group of `n`-th roots of unity**, embedded as
`ζ ↦ (ζ, ζ⁻¹ I)`; the isomorphism is the first projection. -/
noncomputable def kerCircleProdSpecialUnitaryEquiv :
    (circleProdSpecialUnitary (n := n)).ker ≃* rootsOfUnity (Fintype.card n) Circle where
  toFun p := ⟨toUnits p.val.1,
    (mem_rootsOfUnity' _ _).2 (pow_card_eq_one_of_mem_ker_circleProdSpecialUnitary p.property)⟩
  invFun ζ := ⟨(((ζ : Circleˣ) : Circle),
      ⟨_, circle_smul_one_mem_specialUnitaryGroup_iff.2 <|
        (inv_pow _ _).trans (inv_eq_one.2 ((mem_rootsOfUnity' _ _).1 ζ.property))⟩),
    (mem_ker_circleProdSpecialUnitary_iff _).2 rfl⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
    exact ((mem_ker_circleProdSpecialUnitary_iff _).1 p.property).symm
  right_inv ζ := Subtype.ext (Units.ext rfl)
  map_mul' _ _ := Subtype.ext (Units.ext rfl)

/-- The root of unity attached to a point of the kernel is its first coordinate. -/
@[simp]
theorem coe_kerCircleProdSpecialUnitaryEquiv_apply (p : (circleProdSpecialUnitary (n := n)).ker) :
    ((kerCircleProdSpecialUnitaryEquiv p : Circleˣ) : Circle) = p.val.1 :=
  (rfl)

/-- The point of the kernel attached to a root of unity `ζ` has first coordinate `ζ`. -/
@[simp]
theorem fst_kerCircleProdSpecialUnitaryEquiv_symm_apply
    (ζ : rootsOfUnity (Fintype.card n) Circle) :
    ((kerCircleProdSpecialUnitaryEquiv (n := n)).symm ζ).val.1 = ((ζ : Circleˣ) : Circle) :=
  (rfl)

/-- The point of the kernel attached to a root of unity `ζ` has second coordinate `ζ⁻¹ I`. -/
@[simp]
theorem coe_snd_kerCircleProdSpecialUnitaryEquiv_symm_apply
    (ζ : rootsOfUnity (Fintype.card n) Circle) :
    (((kerCircleProdSpecialUnitaryEquiv (n := n)).symm ζ).val.2 : Matrix n n ℂ) =
      ((((ζ : Circleˣ) : Circle)⁻¹ : Circle) : ℂ) • 1 :=
  (rfl)

/-- **The cover `S¹ × SU(n) → U(n)` has degree `n`**: its kernel has `card n` elements. -/
theorem natCard_ker_circleProdSpecialUnitary [Nonempty n] :
    Nat.card (circleProdSpecialUnitary (n := n)).ker = Fintype.card n := by
  have : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  rw [Nat.card_congr kerCircleProdSpecialUnitaryEquiv.toEquiv,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity]

/-- The kernel of `S¹ × SU(n) → U(n)` is finite. -/
instance [Nonempty n] : Finite (circleProdSpecialUnitary (n := n)).ker :=
  Nat.finite_of_card_ne_zero <| by
    rw [natCard_ker_circleProdSpecialUnitary]
    exact Fintype.card_ne_zero

/-- **`S¹ × SU(n) → U(n)` is the quotient by its kernel**, a quotient covering map: it is a
continuous surjection from a compact group onto a Hausdorff one, and its kernel is finite. -/
theorem isQuotientCoveringMap_circleProdSpecialUnitary [Nonempty n] :
    IsQuotientCoveringMap (circleProdSpecialUnitary (n := n))
      (circleProdSpecialUnitary (n := n)).ker :=
  (continuous_circleProdSpecialUnitary.isClosedMap.isQuotientMap
      continuous_circleProdSpecialUnitary circleProdSpecialUnitary_surjective)
    |>.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
      (have : Finite ((circleProdSpecialUnitary (n := n)).ker :
          Set (Circle × specialUnitaryGroup n ℂ)) :=
        inferInstanceAs (Finite (circleProdSpecialUnitary (n := n)).ker)
      DiscreteTopology.isDiscrete)

/-- **`S¹ × SU(n) → U(n)` is a covering map.** -/
theorem isCoveringMap_circleProdSpecialUnitary [Nonempty n] :
    IsCoveringMap (circleProdSpecialUnitary (n := n)) :=
  isQuotientCoveringMap_circleProdSpecialUnitary.isCoveringMap

/-- Every fibre of the cover `S¹ × SU(n) → U(n)` has `card n` points. -/
theorem natCard_preimage_circleProdSpecialUnitary [Nonempty n] (U : unitaryGroup n ℂ) :
    Nat.card (circleProdSpecialUnitary ⁻¹' {U}) = Fintype.card n := by
  obtain ⟨p, hp⟩ := circleProdSpecialUnitary_surjective U
  rw [← natCard_ker_circleProdSpecialUnitary, Nat.card_congr
    (isQuotientCoveringMap_circleProdSpecialUnitary.fiberEquivGroup ⟨p, hp⟩)]

end TauCeti
