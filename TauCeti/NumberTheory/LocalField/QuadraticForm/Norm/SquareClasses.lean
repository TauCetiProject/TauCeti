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

For an element `a` of a valued field `K`, the norms of valuation one in `quadraticNormSubgroup a`
determine a subgroup `TauCeti.unitQuadraticNormSquareClasses a` of `TauCeti.unitSquareClasses K`
inside `Kˣ ⧸ (Kˣ)²`. Because every square of a unit of `𝒪[K]` is already a valuation-one norm from
`K[√a]`, the square-class quotient map `U(K, 0) → unitSquareClasses K` pulls
`unitQuadraticNormSquareClasses a` back to
`(quadraticNormSubgroup a).subgroupOf (unitFiltration K 0)`, so the two subgroups have the same
index.

## Main definitions

* `TauCeti.unitQuadraticNormSquareClasses`: the subgroup of `Kˣ ⧸ (Kˣ)²` consisting of the square
  classes of elements of valuation one in `quadraticNormSubgroup a`.

## Main results

* `TauCeti.mem_unitQuadraticNormSquareClasses_iff`: characterization of membership in terms of a
  valuation-one representative in `quadraticNormSubgroup a`.
* `TauCeti.unitQuadraticNormSquareClasses_le_unitSquareClasses`: inclusion in `unitSquareClasses K`.
* `TauCeti.relIndex_unitQuadraticNormSquareClasses`: over a nonarchimedean local field, the relative
  index inside `unitSquareClasses K` equals the index of valuation-one norms in `U(K, 0)`.

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
    fun ⟨b, hb, hbv, hbq⟩ ↦ ⟨b, ⟨hb, ?_⟩, hbq⟩⟩
  · rw [← hub, Units.coe_map, MonoidHom.coe_ofClass, Subring.coe_subtype]
    exact (Valuation.integer.integers (valuation K)).valuation_unit u
  · have hu : IsUnit (⟨(b : K), hbv.le⟩ : 𝒪[K]) :=
      (Valuation.integer.integers (valuation K)).isUnit_of_one' hbv
    refine ⟨hu.unit, ?_⟩
    ext
    simp

/-- Every valuation-one norm square class from `K[√a]` is a unit square class of `K`. -/
theorem unitQuadraticNormSquareClasses_le_unitSquareClasses (a : K) :
    unitQuadraticNormSquareClasses a ≤ unitSquareClasses K := by
  rintro _ ⟨_, ⟨_, u, rfl⟩, rfl⟩
  exact (mem_unitSquareClasses_iff K _).mpr ⟨u, (squareClassHom_apply _).symm⟩

end ValuedField

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Over a nonarchimedean local field, the index of `unitQuadraticNormSquareClasses a` inside
`unitSquareClasses K` equals the index of the valuation-one quadratic norms inside `U(K, 0)`. -/
theorem relIndex_unitQuadraticNormSquareClasses (a : K) :
    (unitQuadraticNormSquareClasses a).relIndex (unitSquareClasses K) =
      ((quadraticNormSubgroup a).subgroupOf (unitFiltration K 0)).index := by
  have hmem_sq : ∀ u : unitFiltration K 0, squareClassHom (u : Kˣ) ∈ unitSquareClasses K := by
    intro u
    obtain ⟨w, -, hwu⟩ := mem_unitFiltration_iff_exists.mp u.2
    refine (mem_unitSquareClasses_iff K _).mpr ⟨w, ?_⟩
    rw [squareClassHom_apply, QuotientGroup.mk'_apply]
    congr 1
    ext
    exact hwu
  let φ : unitFiltration K 0 →* unitSquareClasses K :=
    { toFun := fun u ↦ ⟨squareClassHom (u : Kˣ), hmem_sq u⟩
      map_one' := by ext; simp
      map_mul' := fun x y ↦ by ext; simp }
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨w, rfl⟩ := (mem_unitSquareClasses_iff K q).mp hq
    let uK : Kˣ := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) w
    have hu0 : uK ∈ unitFiltration K 0 := by
      rw [mem_unitFiltration_zero]
      exact (Valuation.integer.integers (valuation K)).valuation_unit w
    refine ⟨⟨uK, hu0⟩, ?_⟩
    ext
    simp [φ, uK, squareClassHom_apply]
  let H := (unitQuadraticNormSquareClasses a).subgroupOf (unitSquareClasses K)
  have hcomap : H.comap φ = (quadraticNormSubgroup a).subgroupOf (unitFiltration K 0) := by
    ext u
    dsimp only [H, φ]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MonoidHom.coe_mk,
      OneHom.coe_mk, mem_unitQuadraticNormSquareClasses_iff]
    constructor
    · rintro ⟨b, hb_mem, -, hbu⟩
      have hsq : b⁻¹ * (u : Kˣ) ∈ Subgroup.square Kˣ := by
        rw [← QuotientGroup.eq, ← squareClassHom_apply, ← squareClassHom_apply]
        exact hbu
      have hmul := (quadraticNormSubgroup a).mul_mem hb_mem
        (square_le_quadraticNormSubgroup a hsq)
      simpa only [mul_inv_cancel_left] using hmul
    · intro hu_mem
      exact ⟨(u : Kˣ), hu_mem, (mem_unitFiltration_zero _).mp u.2, rfl⟩
  rw [Subgroup.relIndex, ← hcomap, Subgroup.index_comap_of_surjective H hφ_surj]

end LocalField

end TauCeti
