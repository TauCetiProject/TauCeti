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
`TauCeti.unitQuadraticNormSquareClasses_le_unitSquareClasses`). Because `quadraticNormSubgroup a`
contains all squares of `Kˣ`, this subgroup equals the intersection of
`(quadraticNormSubgroup a).map squareClassHom` with `unitSquareClasses K`
(`TauCeti.unitQuadraticNormSquareClasses_eq_inf`), is invariant under rescaling `a` by a square
(`TauCeti.unitQuadraticNormSquareClasses_mul_sq`,
`TauCeti.unitQuadraticNormSquareClasses_eq_of_isSquare_mul`), vanishes at `0`, and fills
`unitSquareClasses K` whenever `a` is a nonzero square (`2 ≠ 0`).

Over a nonarchimedean local field, `unitQuadraticNormSquareClasses a = unitSquareClasses K` if and
only if every depth-zero unit is a norm
(`TauCeti.unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff`), and the quotient map
`U(K, 0) → unitSquareClasses K` identifies the relative index of `unitQuadraticNormSquareClasses a`
in `unitSquareClasses K` with the index of the valuation-one quadratic norms inside `U(K, 0)`
(`TauCeti.relIndex_unitQuadraticNormSquareClasses`).

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

/-- `unitQuadraticNormSquareClasses a` is the intersection inside `Kˣ ⧸ (Kˣ)²` of the full norm
square-class subgroup `(quadraticNormSubgroup a).map squareClassHom` with `unitSquareClasses K`. -/
theorem unitQuadraticNormSquareClasses_eq_inf (a : K) :
    unitQuadraticNormSquareClasses a =
      (quadraticNormSubgroup a).map squareClassHom ⊓ unitSquareClasses K := by
  refine le_antisymm (le_inf
    (Subgroup.map_mono inf_le_left) (unitQuadraticNormSquareClasses_le_unitSquareClasses a)) ?_
  intro q hq
  obtain ⟨hN, hU⟩ := Subgroup.mem_inf.mp hq
  obtain ⟨u, rfl⟩ := (mem_unitSquareClasses_iff K q).mp hU
  have hu : Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u ∈ quadraticNormSubgroup a :=
    (squareClassHom_mem_map_quadraticNormSubgroup_iff a _).mp
      (by simpa only [QuotientGroup.mk'_apply, squareClassHom_apply] using hN)
  exact ⟨Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u, ⟨hu, u, rfl⟩,
    by rw [squareClassHom_apply, QuotientGroup.mk'_apply]⟩

/-- Rescaling the radicand `a` by a square leaves `unitQuadraticNormSquareClasses` unchanged. -/
@[simp]
theorem unitQuadraticNormSquareClasses_mul_sq (a : K) (c : Kˣ) :
    unitQuadraticNormSquareClasses (a * (c : K) ^ 2) = unitQuadraticNormSquareClasses a := by
  simp only [unitQuadraticNormSquareClasses, quadraticNormSubgroup_mul_sq]

/-- Unit radicands in the same square class determine the same subgroup of unit-norm square
classes. -/
theorem unitQuadraticNormSquareClasses_eq_of_isSquare_mul {a b : Kˣ} (h : IsSquare (a * b)) :
    unitQuadraticNormSquareClasses (a : K) = unitQuadraticNormSquareClasses (b : K) := by
  simp only [unitQuadraticNormSquareClasses, quadraticNormSubgroup_eq_of_isSquare_mul h]

/-- At radicand `0`, the only valuation-one norm square class is the trivial class `1`. -/
@[simp]
theorem unitQuadraticNormSquareClasses_zero :
    unitQuadraticNormSquareClasses (0 : K) = ⊥ := by
  rw [unitQuadraticNormSquareClasses_eq_inf, map_squareClassHom_quadraticNormSubgroup_zero,
    bot_inf_eq]

/-- When `2 ≠ 0` in `K`, every unit square class is a valuation-one norm class from `K[√1]`. -/
theorem unitQuadraticNormSquareClasses_one (h2 : (2 : K) ≠ 0) :
    unitQuadraticNormSquareClasses (1 : K) = unitSquareClasses K := by
  rw [unitQuadraticNormSquareClasses_eq_inf, quadraticNormSubgroup_one h2.isUnit,
    Subgroup.map_top_of_surjective _ squareClassHom_surjective, top_inf_eq]

/-- When `2 ≠ 0` in `K`, every nonzero square radicand has `unitSquareClasses K` as its unit-norm
square-class subgroup. -/
theorem unitQuadraticNormSquareClasses_of_isSquare (h2 : (2 : K) ≠ 0) {a : K}
    (ha : a ≠ 0) (hsq : IsSquare a) :
    unitQuadraticNormSquareClasses a = unitSquareClasses K := by
  rw [unitQuadraticNormSquareClasses_eq_inf,
    map_squareClassHom_quadraticNormSubgroup_of_isSquare h2 ha hsq, top_inf_eq]

/-- Over a valued field, `unitQuadraticNormSquareClasses a` fills `unitSquareClasses K` if and only
if every unit of `𝒪[K]` is a norm from `K[√a]`. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_range_le (a : K) :
    unitQuadraticNormSquareClasses a = unitSquareClasses K ↔
      (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K)).range ≤ quadraticNormSubgroup a := by
  rw [unitQuadraticNormSquareClasses_eq_inf, inf_eq_right]
  constructor
  · rintro h _ ⟨u, rfl⟩
    refine (squareClassHom_mem_map_quadraticNormSubgroup_iff a _).mp ?_
    simpa only [QuotientGroup.mk'_apply, squareClassHom_apply] using
      h ((mem_unitSquareClasses_iff K _).mpr ⟨u, rfl⟩)
  · intro h q hq
    obtain ⟨u, rfl⟩ := (mem_unitSquareClasses_iff K q).mp hq
    simpa only [QuotientGroup.mk'_apply, squareClassHom_apply] using
      (squareClassHom_mem_map_quadraticNormSubgroup_iff a _).mpr (h ⟨u, rfl⟩)

end ValuedField

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Over a nonarchimedean local field, `unitQuadraticNormSquareClasses a` equals
`unitSquareClasses K` if and only if `U(K, 0) ≤ quadraticNormSubgroup a`. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff (a : K) :
    unitQuadraticNormSquareClasses a = unitSquareClasses K ↔
      unitFiltration K 0 ≤ quadraticNormSubgroup a := by
  have hrange : (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K)).range = unitFiltration K 0 := by
    ext x
    rw [MonoidHom.mem_range, mem_unitFiltration_zero]
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ (Valuation.integer.integers (valuation K)).valuation_unit u,
      fun hx ↦ ⟨((Valuation.integer.integers (valuation K)).isUnit_of_one'
        (x := ⟨(x : K), hx.le⟩) hx).unit, by ext; simp⟩⟩
  rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_range_le, hrange]

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
