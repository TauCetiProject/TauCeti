/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.LocalField.UnitSquareClasses

/-!
# Unit-norm square classes of a quadratic extension

For `a : K` over a valued field, the valuation-one elements of `quadraticNormSubgroup a` form a
subgroup `TauCeti.unitQuadraticNormSquareClasses a ≤ TauCeti.unitSquareClasses K` inside
`Kˣ ⧸ (Kˣ)²` (`TauCeti.mem_unitQuadraticNormSquareClasses_iff`,
`TauCeti.unitQuadraticNormSquareClasses_le_unitSquareClasses`), invariant under rescaling `a` by the
square of a unit of `K` (`TauCeti.unitQuadraticNormSquareClasses_mul_sq`,
`TauCeti.unitQuadraticNormSquareClasses_eq_of_isSquare_mul`) and equal to `unitSquareClasses K` when
`2 ≠ 0` and `a : Kˣ` is a square
(`TauCeti.unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_isSquare`). Because every square of
a unit of `𝒪[K]` is already a valuation-one norm from `K[√a]`, the quotient map
`U(K, 0) → unitSquareClasses K` pulls `unitQuadraticNormSquareClasses a` back to
`(quadraticNormSubgroup a).subgroupOf (unitFiltration K 0)`, identifying their indices over a
nonarchimedean local field (`TauCeti.relIndex_unitQuadraticNormSquareClasses`).

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

section ValuedField

variable {K : Type*} [Field K] [ValuativeRel K]

/-- The subgroup of `Kˣ ⧸ (Kˣ)²` consisting of the square classes of norms of valuation one from
`K[√a]`. -/
def unitQuadraticNormSquareClasses (a : K) : Subgroup (Kˣ ⧸ Subgroup.square Kˣ) :=
  (quadraticNormSubgroup a ⊓ (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K)).range).map
    squareClassHom

/-- `unitQuadraticNormSquareClasses a` is the image under `squareClassHom` of the valuation-one
elements of `quadraticNormSubgroup a`. -/
theorem unitQuadraticNormSquareClasses_def (a : K) :
    unitQuadraticNormSquareClasses a =
      (quadraticNormSubgroup a ⊓ (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K)).range).map
        squareClassHom :=
  (rfl)

/-- A square class belongs to `unitQuadraticNormSquareClasses a` if and only if it is represented by
an element of `quadraticNormSubgroup a` of valuation one. -/
theorem mem_unitQuadraticNormSquareClasses_iff (a : K) (q : Kˣ ⧸ Subgroup.square Kˣ) :
    q ∈ unitQuadraticNormSquareClasses a ↔
      ∃ b : Kˣ, b ∈ quadraticNormSubgroup a ∧ valuation K (b : K) = 1 ∧ squareClassHom b = q := by
  simp only [unitQuadraticNormSquareClasses, Subgroup.mem_map, Subgroup.mem_inf,
    MonoidHom.mem_range]
  refine ⟨fun ⟨b, ⟨hb, u, hub⟩, hbq⟩ ↦ ⟨b, hb, ?_, hbq⟩,
    fun ⟨b, hb, hbv, hbq⟩ ↦ ⟨b, ⟨hb, ((Valuation.integer.integers (valuation K)).isUnit_of_one'
      (x := ⟨(b : K), hbv.le⟩) hbv).unit, by ext; simp⟩, hbq⟩⟩
  rw [← congrArg Units.val hub]
  exact (Valuation.integer.integers (valuation K)).valuation_unit u

/-- Every valuation-one norm square class from `K[√a]` is a unit square class of `K`. -/
theorem unitQuadraticNormSquareClasses_le_unitSquareClasses (a : K) :
    unitQuadraticNormSquareClasses a ≤ unitSquareClasses K := by
  rintro _ ⟨_, ⟨_, u, rfl⟩, rfl⟩
  exact (mem_unitSquareClasses_iff K _).mpr ⟨u, (squareClassHom_apply _).symm⟩

/-- Rescaling the radicand by the square of a unit of `K` leaves `unitQuadraticNormSquareClasses`
unchanged. -/
@[simp]
theorem unitQuadraticNormSquareClasses_mul_sq (a : K) (c : Kˣ) :
    unitQuadraticNormSquareClasses (a * (c : K) ^ 2) = unitQuadraticNormSquareClasses a := by
  simp only [unitQuadraticNormSquareClasses_def, quadraticNormSubgroup_mul_sq]

/-- `unitQuadraticNormSquareClasses` depends only on the square class of `a : Kˣ`. -/
theorem unitQuadraticNormSquareClasses_eq_of_isSquare_mul {a b : Kˣ} (h : IsSquare (a * b)) :
    unitQuadraticNormSquareClasses (a : K) = unitQuadraticNormSquareClasses (b : K) := by
  rw [unitQuadraticNormSquareClasses_def, unitQuadraticNormSquareClasses_def,
    quadraticNormSubgroup_eq_of_isSquare_mul h]

/-- When `2 ≠ 0` in `K` and `a : Kˣ` is a square, every unit square class of `K` is represented by a
valuation-one norm from `K[√a]`. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_isSquare (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : IsSquare a) :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  refine le_antisymm (unitQuadraticNormSquareClasses_le_unitSquareClasses _) fun q hq ↦ ?_
  obtain ⟨u, rfl⟩ := (mem_unitSquareClasses_iff K q).mp hq
  let b : Kˣ := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u
  exact (mem_unitQuadraticNormSquareClasses_iff (a : K) _).mpr
    ⟨b, (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).mp
      (hilbertSymbol_eq_one_of_isSquare_left ha b),
      (Valuation.integer.integers (valuation K)).valuation_unit u, squareClassHom_apply b⟩

end ValuedField

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Over a nonarchimedean local field, the index of `unitQuadraticNormSquareClasses a` inside
`unitSquareClasses K` equals the index of the valuation-one quadratic norms inside `U(K, 0)`. -/
theorem relIndex_unitQuadraticNormSquareClasses (a : K) :
    (unitQuadraticNormSquareClasses a).relIndex (unitSquareClasses K) =
      ((quadraticNormSubgroup a).subgroupOf (unitFiltration K 0)).index := by
  let φ : unitFiltration K 0 →* unitSquareClasses K :=
    (squareClassHom.comp (unitFiltration K 0).subtype).codRestrict (unitSquareClasses K) fun u ↦ by
      obtain ⟨w, -, hwu⟩ := mem_unitFiltration_iff_exists.mp u.2
      exact (mem_unitSquareClasses_iff K _).mpr ⟨w, by
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, squareClassHom_apply,
          QuotientGroup.mk'_apply]; congr 1; exact Units.ext hwu⟩
  have hφ_surj : Function.Surjective φ := fun ⟨q, hq⟩ ↦ by
    obtain ⟨w, rfl⟩ := (mem_unitSquareClasses_iff K q).mp hq
    refine ⟨⟨Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) w, (mem_unitFiltration_zero _).mpr
      ((Valuation.integer.integers (valuation K)).valuation_unit w)⟩, ?_⟩
    ext; simp [φ, squareClassHom_apply]
  let H := (unitQuadraticNormSquareClasses a).subgroupOf (unitSquareClasses K)
  have hcomap : H.comap φ = (quadraticNormSubgroup a).subgroupOf (unitFiltration K 0) := by
    ext u
    simp only [H, φ, Subgroup.mem_comap, Subgroup.mem_subgroupOf, MonoidHom.codRestrict_apply,
      MonoidHom.comp_apply, Subgroup.coe_subtype, mem_unitQuadraticNormSquareClasses_iff]
    refine ⟨fun ⟨b, hb, _, hbu⟩ ↦ ?_, fun hu ↦ ⟨u, hu, (mem_unitFiltration_zero _).mp u.2, rfl⟩⟩
    have hsq : b⁻¹ * (u : Kˣ) ∈ Subgroup.square Kˣ := by
      rwa [← QuotientGroup.eq, ← squareClassHom_apply, ← squareClassHom_apply]
    simpa only [mul_inv_cancel_left] using
      (quadraticNormSubgroup a).mul_mem hb (square_le_quadraticNormSubgroup a hsq)
  rw [Subgroup.relIndex, ← hcomap, Subgroup.index_comap_of_surjective H hφ_surj]

end LocalField

end TauCeti
