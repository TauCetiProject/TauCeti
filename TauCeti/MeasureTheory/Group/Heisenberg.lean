/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Group.Lattice
public import TauCeti.MeasureTheory.Measure.Lebesgue.Shear
public import TauCeti.Topology.Algebra.Group.Heisenberg

/-!
# Haar measure and the integer lattice of the real Heisenberg group

The real Heisenberg group `H(ℝ)` (`TauCeti.HeisenbergGroup ℝ`), the group of real upper
unitriangular `3 × 3` matrices with product
`(x, y, z) * (x', y', z') = (x + x', y + y', z + z' + x y')`, carries Lebesgue measure in its
coordinates `(x, y, z)`. Left and right multiplications are affine maps of `ℝ³` whose linear parts
are shears (`TauCeti.measurePreserving_prod3_add_shear_fst`,
`TauCeti.measurePreserving_prod3_add_shear_snd`), so this measure is a left and right invariant
Haar measure: `H(ℝ)` is unimodular.

The integer Heisenberg group `H(ℤ)`, the image of `TauCeti.HeisenbergGroup.map` for the cast
`ℤ → ℝ`, is a uniform lattice of covolume one. The half-open unit cube `[0, 1)³` is a fundamental
domain for its right action `g ↦ g γ`: for `g = (x, y, z)` the translate `g (a, b, c)` is
`(x + a, y + b, z + c + x b)`, so `a = -⌊x⌋`, `b = -⌊y⌋` and `c = -⌊z + x b⌋` are forced. Weil's
formula for this lattice is the explicit unfolding
`∫_{H(ℝ)} f = ∫_{[0,1)³} ∑_{(a, b, c) ∈ ℤ³} f(x + a, y + b, z + c + x b) dx dy dz`.

This is the basic example of a uniform lattice in a non-abelian nilpotent Lie group.

## Main definitions

* `TauCeti.HeisenbergGroup.instMeasurableSpace`, `instBorelSpace`: the Borel measurable
  structure of the topology on `HeisenbergGroup R`.
* `TauCeti.HeisenbergGroup.instMeasureSpace`: Lebesgue measure on `H(ℝ)` in coordinates.
* `TauCeti.HeisenbergGroup.unitCube`, `closedUnitCube`: the half-open unit cube `[0, 1)³` and the
  closed unit cube `[0, 1]³` in coordinates.

## Main results

* `TauCeti.HeisenbergGroup.measurePreserving_homeomorphProd`: the coordinates identify the
  measure with Lebesgue measure on `ℝ × ℝ × ℝ`.
* `TauCeti.HeisenbergGroup.instIsHaarMeasure`, `instIsMulRightInvariant`: Lebesgue measure is a
  left and right invariant Haar measure.
* `TauCeti.HeisenbergGroup.isFundamentalDomain_unitCube`: the unit cube is a fundamental domain
  for the right action of `H(ℤ)`.
* `TauCeti.HeisenbergGroup.covolume_intLattice`: `H(ℤ)` has covolume one.
* `TauCeti.HeisenbergGroup.isUniformLattice_intLattice`: `H(ℤ)` is a uniform lattice.
* `TauCeti.HeisenbergGroup.lintegral_eq_setLIntegral_unitCube_tsum`: Weil's formula for `H(ℤ)`.
-/

public section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace HeisenbergGroup

section Measurable

variable {R : Type*} [TopologicalSpace R]

/-- The measurable structure on the Heisenberg group over a topological space `R`: the Borel
structure of its topology. -/
instance instMeasurableSpace : MeasurableSpace (HeisenbergGroup R) :=
  borel _

/-- The measurable structure on the Heisenberg group is Borel. -/
instance instBorelSpace : BorelSpace (HeisenbergGroup R) :=
  ⟨rfl⟩

/-- Over a second countable Borel space, the coordinate homeomorphism
`HeisenbergGroup R ≃ R × R × R` is a measurable equivalence. -/
def measurableEquivProd [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] :
    HeisenbergGroup R ≃ᵐ R × R × R :=
  homeomorphProd.toMeasurableEquiv

/-- The coordinate measurable equivalence is the coordinate homeomorphism. -/
theorem coe_measurableEquivProd [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] :
    ⇑(measurableEquivProd : HeisenbergGroup R ≃ᵐ R × R × R) = homeomorphProd :=
  homeomorphProd.toMeasurableEquiv_coe

/-- The coordinate measurable equivalence reads off the three coordinates. -/
@[simp]
theorem measurableEquivProd_apply [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R]
    (a : HeisenbergGroup R) : measurableEquivProd a = (a.x, a.y, a.z) := by
  rw [coe_measurableEquivProd, homeomorphProd_apply]

/-- The inverse coordinate measurable equivalence assembles the three coordinates. -/
@[simp]
theorem measurableEquivProd_symm_apply [MeasurableSpace R] [BorelSpace R]
    [SecondCountableTopology R] (a : R × R × R) :
    measurableEquivProd.symm a = ⟨a.1, a.2.1, a.2.2⟩ := by
  rw [measurableEquivProd, Homeomorph.toMeasurableEquiv_symm_coe, homeomorphProd_symm_apply]

end Measurable

/-- **Lebesgue measure** on the real Heisenberg group: the push-forward of Lebesgue measure on
`ℝ × ℝ × ℝ` along the inverse of the coordinate map. -/
noncomputable instance instMeasureSpace : MeasureSpace (HeisenbergGroup ℝ) :=
  ⟨Measure.map measurableEquivProd.symm volume⟩

/-- The measure on `H(ℝ)` is the image of Lebesgue measure on `ℝ × ℝ × ℝ`. -/
theorem volume_eq : (volume : Measure (HeisenbergGroup ℝ)) =
    Measure.map measurableEquivProd.symm volume :=
  (rfl)

/-- The coordinates `(x, y, z)` identify the measure on `H(ℝ)` with Lebesgue measure. -/
theorem measurePreserving_measurableEquivProd :
    MeasurePreserving (measurableEquivProd : HeisenbergGroup ℝ ≃ᵐ ℝ × ℝ × ℝ) volume volume := by
  refine ⟨measurableEquivProd.measurable, ?_⟩
  rw [volume_eq, Measure.map_map measurableEquivProd.measurable
    measurableEquivProd.symm.measurable, MeasurableEquiv.self_comp_symm, Measure.map_id]

/-- The coordinate homeomorphism identifies the measure on `H(ℝ)` with Lebesgue measure. -/
theorem measurePreserving_homeomorphProd :
    MeasurePreserving (homeomorphProd : HeisenbergGroup ℝ ≃ₜ ℝ × ℝ × ℝ) volume volume :=
  coe_measurableEquivProd (R := ℝ) ▸ measurePreserving_measurableEquivProd

/-- Left multiplication preserves Lebesgue measure on `H(ℝ)`. -/
instance instIsMulLeftInvariant : (volume : Measure (HeisenbergGroup ℝ)).IsMulLeftInvariant := by
  refine ⟨fun g ↦ ?_⟩
  have h := (measurePreserving_measurableEquivProd.symm _).comp
    ((measurePreserving_prod3_add_shear_snd g.x g.y g.z g.x).comp
      measurePreserving_measurableEquivProd)
  refine Eq.trans ?_ h.map_eq
  congr 1
  ext a <;> simp [add_comm]

/-- Right multiplication preserves Lebesgue measure on `H(ℝ)`: the Heisenberg group is
unimodular. -/
instance instIsMulRightInvariant :
    (volume : Measure (HeisenbergGroup ℝ)).IsMulRightInvariant := by
  refine ⟨fun g ↦ ?_⟩
  have h := (measurePreserving_measurableEquivProd.symm _).comp
    ((measurePreserving_prod3_add_shear_fst g.x g.y g.z g.y).comp
      measurePreserving_measurableEquivProd)
  refine Eq.trans ?_ h.map_eq
  congr 1
  ext a <;> simp [mul_comm]

/-- The half-open unit cube `[0, 1)³` in the coordinates of `H(ℝ)`. -/
def unitCube : Set (HeisenbergGroup ℝ) :=
  homeomorphProd ⁻¹' (Ico 0 1 ×ˢ Ico 0 1 ×ˢ Ico 0 1)

/-- Membership in the unit cube, coordinate by coordinate. -/
@[simp]
theorem mem_unitCube {g : HeisenbergGroup ℝ} :
    g ∈ unitCube ↔ g.x ∈ Ico 0 1 ∧ g.y ∈ Ico 0 1 ∧ g.z ∈ Ico 0 1 := by
  simp [unitCube]

/-- The closed unit cube `[0, 1]³` in the coordinates of `H(ℝ)`. -/
def closedUnitCube : Set (HeisenbergGroup ℝ) :=
  homeomorphProd ⁻¹' (Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1)

/-- Membership in the closed unit cube, coordinate by coordinate. -/
@[simp]
theorem mem_closedUnitCube {g : HeisenbergGroup ℝ} :
    g ∈ closedUnitCube ↔ g.x ∈ Icc 0 1 ∧ g.y ∈ Icc 0 1 ∧ g.z ∈ Icc 0 1 := by
  simp only [closedUnitCube, mem_preimage, homeomorphProd_apply, mem_prod]

/-- The closed unit cube is compact. -/
theorem isCompact_closedUnitCube : IsCompact closedUnitCube :=
  homeomorphProd.isCompact_preimage.mpr (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

/-- The half-open unit cube lies in the closed unit cube. -/
theorem unitCube_subset_closedUnitCube : unitCube ⊆ closedUnitCube := fun _ hg ↦
  ⟨Ico_subset_Icc_self hg.1, Ico_subset_Icc_self hg.2.1, Ico_subset_Icc_self hg.2.2⟩

/-- The measure of a coordinate box in `H(ℝ)` is the product of the lengths of its sides. -/
theorem volume_preimage_homeomorphProd_prod (s t u : Set ℝ) :
    volume (homeomorphProd ⁻¹' (s ×ˢ t ×ˢ u) : Set (HeisenbergGroup ℝ)) =
      volume s * volume t * volume u := by
  rw [← coe_measurableEquivProd, measurePreserving_measurableEquivProd.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, mul_assoc]

/-- The unit cube has measure one. -/
theorem volume_unitCube : volume unitCube = 1 := by
  simp [unitCube, volume_preimage_homeomorphProd_prod]

/-- Lebesgue measure is a Haar measure on `H(ℝ)`. -/
instance instIsHaarMeasure : (volume : Measure (HeisenbergGroup ℝ)).IsHaarMeasure := by
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior volume closedUnitCube
    isCompact_closedUnitCube ?_ ?_ ?_
  · rw [closedUnitCube, ← homeomorphProd.preimage_interior, interior_prod_eq, interior_prod_eq]
    simp only [interior_Icc]
    exact ⟨homeomorphProd.symm (1 / 2, 1 / 2, 1 / 2), by norm_num⟩
  all_goals
    rw [closedUnitCube, volume_preimage_homeomorphProd_prod]
    simp

/-- The unit cube is a Borel set. -/
theorem measurableSet_unitCube : MeasurableSet unitCube :=
  homeomorphProd.continuous.measurable
    (measurableSet_Ico.prod (measurableSet_Ico.prod measurableSet_Ico))

/-- The translate of `g` by an integer point `(a, b, c)` lies in the unit cube exactly when `a`,
`b` and `c` cancel the integer parts of `x`, `y` and `z + x b`. -/
theorem mul_intCast_mem_unitCube_iff {g : HeisenbergGroup ℝ} {a b c : ℤ} :
    g * ⟨a, b, c⟩ ∈ unitCube ↔ ⌊g.x⌋ + a = 0 ∧ ⌊g.y⌋ + b = 0 ∧ ⌊g.z + g.x * b⌋ + c = 0 := by
  -- the translate of `g` by `(a, b, c)` is `(x + a, y + b, z + c + x b)`
  simp only [mem_unitCube, mul_x, mul_y, mul_z, ← Int.floor_eq_zero_iff]
  rw [add_right_comm g.z]
  simp only [Int.floor_add_intCast]

/-- Every coset `g H(ℤ)` meets the unit cube. -/
theorem exists_mul_mem_unitCube (g : HeisenbergGroup ℝ) :
    ∃ γ ∈ intLattice, g * γ ∈ unitCube :=
  ⟨⟨((-⌊g.x⌋ : ℤ) : ℝ), ((-⌊g.y⌋ : ℤ) : ℝ), ((-⌊g.z + g.x * ((-⌊g.y⌋ : ℤ) : ℝ)⌋ : ℤ) : ℝ)⟩,
    mem_intLattice.mpr ⟨_, _, _, rfl⟩,
    mul_intCast_mem_unitCube_iff.mpr ⟨add_neg_cancel _, add_neg_cancel _, add_neg_cancel _⟩⟩

/-- The half-open unit cube is a fundamental domain for the right action of `H(ℤ)` on `H(ℝ)`. -/
theorem isFundamentalDomain_unitCube :
    IsFundamentalDomain intLattice.op unitCube (volume : Measure (HeisenbergGroup ℝ)) := by
  refine .mk' measurableSet_unitCube.nullMeasurableSet fun g ↦ ?_
  obtain ⟨γ, hγ, hmem⟩ := exists_mul_mem_unitCube g
  refine ⟨⟨MulOpposite.op γ, Subgroup.mem_op.mpr hγ⟩, hmem, ?_⟩
  -- two translates in the cube have the same integer coordinates
  have key : ∀ δ ∈ intLattice, g * δ ∈ unitCube → δ = γ := by
    intro δ hδ hδmem
    obtain ⟨a', b', c', rfl⟩ := mem_intLattice.mp hδ
    obtain ⟨a, b, c, rfl⟩ := mem_intLattice.mp hγ
    obtain ⟨hx, hy, hz⟩ := mul_intCast_mem_unitCube_iff.mp hδmem
    obtain ⟨hx', hy', hz'⟩ := mul_intCast_mem_unitCube_iff.mp hmem
    obtain rfl : b' = b := by omega
    obtain ⟨rfl, rfl⟩ : a' = a ∧ c' = c := by omega
    rfl
  rintro ⟨δ, hδ⟩ hδmem
  exact Subtype.ext (MulOpposite.unop_injective (key _ (Subgroup.mem_op.mp hδ) hδmem))

/-- The integer Heisenberg group has covolume one in `H(ℝ)`. -/
theorem covolume_intLattice :
    covolume intLattice.op (HeisenbergGroup ℝ) volume = 1 := by
  rw [isFundamentalDomain_unitCube.covolume_eq_volume, volume_unitCube]

/-- The integer Heisenberg group is a uniform lattice in `H(ℝ)`: the closed unit cube is a
compact set whose right `H(ℤ)`-translates cover `H(ℝ)`. -/
theorem isUniformLattice_intLattice :
    intLattice.IsUniformLattice (volume : Measure (HeisenbergGroup ℝ)) := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance, unitCube, isFundamentalDomain_unitCube,
    by simp [volume_unitCube]⟩, closedUnitCube, isCompact_closedUnitCube, ?_⟩
  refine eq_univ_of_forall fun g ↦ ?_
  obtain ⟨γ, hγ, hmem⟩ := exists_mul_mem_unitCube g
  exact ⟨g * γ, unitCube_subset_closedUnitCube hmem, γ⁻¹, Subgroup.inv_mem _ hγ, by group⟩

/-- **Weil's formula** for the integer Heisenberg lattice: for measurable `f ≥ 0`,
`∫_{H(ℝ)} f = ∫_{[0,1)³} ∑_{(a, b, c) ∈ ℤ³} f(x + a, y + b, z + c + x b)`. -/
theorem lintegral_eq_setLIntegral_unitCube_tsum {f : HeisenbergGroup ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g = ∫⁻ g in unitCube, ∑' n : HeisenbergGroup ℤ, f (g * map (Int.castRingHom ℝ) n) := by
  rw [isFundamentalDomain_unitCube.lintegral_eq_tsum'', lintegral_tsum
    (f := fun n g ↦ f (g * map (Int.castRingHom ℝ) n)) fun n ↦
    (hf.comp (measurable_mul_const _)).aemeasurable]
  -- reindex the sum over `H(ℤ)ᵐᵒᵖ` by `HeisenbergGroup ℤ`
  rw [← (intLatticeEquiv.toEquiv.trans intLattice.equivOp).tsum_eq]
  simp [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]

end HeisenbergGroup

end TauCeti
