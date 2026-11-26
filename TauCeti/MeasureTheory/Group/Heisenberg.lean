/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Group.Lattice
public import TauCeti.Topology.Algebra.Group.Heisenberg

/-!
# Haar measure and the integer lattice of the real Heisenberg group

The real Heisenberg group `H(ℝ)` (`TauCeti.HeisenbergGroup ℝ`), the group of real upper
unitriangular `3 × 3` matrices with product
`(x, y, z) * (x', y', z') = (x + x', y + y', z + z' + x y')`, carries Lebesgue measure in its
coordinates `(x, y, z)`. Left and right multiplications are affine maps of `ℝ³` whose linear parts
are shears, so this measure is a left and right invariant Haar measure: `H(ℝ)` is unimodular.

The integer Heisenberg group `H(ℤ)`, the image of `TauCeti.HeisenbergGroup.map` for the cast
`ℤ → ℝ`, is a uniform lattice of covolume one. The half-open unit cube `[0, 1)³` is a fundamental
domain for its right action `g ↦ g γ`: for `g = (x, y, z)` the translate `g (a, b, c)` is
`(x + a, y + b, z + c + x b)`, so `a = -⌊x⌋`, `b = -⌊y⌋` and `c = -⌊z + x b⌋` are forced. Weil's
formula for this lattice is the explicit unfolding
`∫_{H(ℝ)} f = ∫_{[0,1)³} ∑_{(a, b, c) ∈ ℤ³} f(x + a, y + b, z + c + x b) dx dy dz`.

This is the integer Heisenberg example of VonNeumannAlgebras Layer 9.

## Main definitions

* `TauCeti.HeisenbergGroup.instMeasurableSpace`, `instBorelSpace`: the measurable structure,
  pulled back from `R × R × R`.
* `TauCeti.HeisenbergGroup.instMeasureSpace`: Lebesgue measure on `H(ℝ)` in coordinates.
* `TauCeti.HeisenbergGroup.intLattice`: the integer Heisenberg subgroup `H(ℤ) ≤ H(ℝ)`.
* `TauCeti.HeisenbergGroup.unitCube`: the half-open unit cube `[0, 1)³` in coordinates.

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

/-- The Heisenberg group over a countable ring is countable. -/
instance instCountable {R : Type*} [Countable R] : Countable (HeisenbergGroup R) :=
  equivProd.injective.countable

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

/-- The coordinate measurable equivalence reads off the three coordinates. -/
@[simp]
theorem measurableEquivProd_apply [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R]
    (a : HeisenbergGroup R) : measurableEquivProd a = (a.x, a.y, a.z) :=
  homeomorphProd_apply a

/-- The inverse coordinate measurable equivalence assembles the three coordinates. -/
@[simp]
theorem measurableEquivProd_symm_apply [MeasurableSpace R] [BorelSpace R]
    [SecondCountableTopology R] (a : R × R × R) :
    measurableEquivProd.symm a = ⟨a.1, a.2.1, a.2.2⟩ :=
  homeomorphProd_symm_apply a

/-- The coordinate measurable equivalence is the coordinate homeomorphism. -/
theorem coe_measurableEquivProd [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] :
    ⇑(measurableEquivProd : HeisenbergGroup R ≃ᵐ R × R × R) = homeomorphProd :=
  (rfl)

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

/-- In coordinates on `ℝ × ℝ`, the shear `(y, z) ↦ (y + b, z + c + a y)` preserves Lebesgue
measure. -/
private theorem measurePreserving_shear (a b c : ℝ) :
    MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1 + b, q.2 + c + a * q.1)) volume volume := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) b).skew_product
    (μc := (volume : Measure ℝ)) (μd := (volume : Measure ℝ))
    (g := fun (y z : ℝ) ↦ z + (c + a * y)) (by fun_prop)
    (Filter.Eventually.of_forall fun y ↦ (measurePreserving_add_right volume _).map_eq)
  rw [← Measure.volume_eq_prod] at h
  convert h using 2 with q
  simp [add_assoc]

/-- In coordinates, the map `(x, y, z) ↦ (x + a, y + b, z + c + d x)` preserves Lebesgue measure:
it is a translation composed with a shear. -/
theorem measurePreserving_affine (a b c d : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ ↦ (p.1 + a, p.2.1 + b, p.2.2 + c + d * p.1))
      volume volume := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) a).skew_product
    (μc := (volume : Measure (ℝ × ℝ))) (μd := (volume : Measure (ℝ × ℝ)))
    (g := fun (x : ℝ) (q : ℝ × ℝ) ↦ (q.1 + b, q.2 + (c + d * x) + 0 * q.1)) (by fun_prop)
    (Filter.Eventually.of_forall fun x ↦ (measurePreserving_shear 0 b (c + d * x)).map_eq)
  rw [← Measure.volume_eq_prod] at h
  convert h using 2 with p
  simp [add_assoc]

/-- In coordinates, the map `(x, y, z) ↦ (x + a, y + b, z + c + a y)` preserves Lebesgue measure:
it is a translation composed with a shear. -/
theorem measurePreserving_affine' (a b c : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ ↦ (p.1 + a, p.2.1 + b, p.2.2 + c + a * p.2.1))
      volume volume := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) a).skew_product
    (μc := (volume : Measure (ℝ × ℝ))) (μd := (volume : Measure (ℝ × ℝ)))
    (g := fun (_ : ℝ) (q : ℝ × ℝ) ↦ (q.1 + b, q.2 + c + a * q.1)) (by fun_prop)
    (Filter.Eventually.of_forall fun _ ↦ (measurePreserving_shear a b c).map_eq)
  rwa [← Measure.volume_eq_prod] at h

/-- Left multiplication preserves Lebesgue measure on `H(ℝ)`. -/
instance instIsMulLeftInvariant : (volume : Measure (HeisenbergGroup ℝ)).IsMulLeftInvariant := by
  refine ⟨fun g ↦ ?_⟩
  have h := (measurePreserving_measurableEquivProd.symm _).comp
    ((measurePreserving_affine' g.x g.y g.z).comp measurePreserving_measurableEquivProd)
  refine Eq.trans ?_ h.map_eq
  congr 1
  ext a <;> simp [add_comm]

/-- Right multiplication preserves Lebesgue measure on `H(ℝ)`: the Heisenberg group is
unimodular. -/
instance instIsMulRightInvariant :
    (volume : Measure (HeisenbergGroup ℝ)).IsMulRightInvariant := by
  refine ⟨fun g ↦ ?_⟩
  have h := (measurePreserving_measurableEquivProd.symm _).comp
    ((measurePreserving_affine g.x g.y g.z g.y).comp measurePreserving_measurableEquivProd)
  refine Eq.trans ?_ h.map_eq
  congr 1
  ext a <;> simp [mul_comm]

/-- The half-open unit cube `[0, 1)³` in the coordinates of `H(ℝ)`. -/
def unitCube : Set (HeisenbergGroup ℝ) :=
  homeomorphProd ⁻¹' (Ico 0 1 ×ˢ Ico 0 1 ×ˢ Ico 0 1)

/-- Membership in the unit cube, coordinate by coordinate. -/
theorem mem_unitCube {g : HeisenbergGroup ℝ} :
    g ∈ unitCube ↔ g.x ∈ Ico 0 1 ∧ g.y ∈ Ico 0 1 ∧ g.z ∈ Ico 0 1 := by
  simp [unitCube]

/-- The unit cube has measure one. -/
theorem volume_unitCube : volume unitCube = 1 := by
  rw [unitCube, ← coe_measurableEquivProd,
    measurePreserving_measurableEquivProd.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- Lebesgue measure is a Haar measure on `H(ℝ)`. -/
instance instIsHaarMeasure : (volume : Measure (HeisenbergGroup ℝ)).IsHaarMeasure := by
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior volume
    (homeomorphProd ⁻¹' (Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1)) ?_ ?_ ?_ ?_
  · exact homeomorphProd.isCompact_preimage.mpr
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  · rw [← homeomorphProd.preimage_interior, interior_prod_eq, interior_prod_eq]
    simp only [interior_Icc]
    exact ⟨homeomorphProd.symm (1 / 2, 1 / 2, 1 / 2), by norm_num⟩
  all_goals
    rw [← coe_measurableEquivProd, measurePreserving_measurableEquivProd.measure_preimage_equiv,
      Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    simp

/-- The **integer Heisenberg group** `H(ℤ)`, as a subgroup of the real Heisenberg group. -/
def intLattice : Subgroup (HeisenbergGroup ℝ) :=
  (map (Int.castRingHom ℝ)).range

/-- An element of `H(ℝ)` lies in `H(ℤ)` exactly when its three coordinates are integers. -/
theorem mem_intLattice {g : HeisenbergGroup ℝ} :
    g ∈ intLattice ↔ ∃ a b c : ℤ, g = ⟨a, b, c⟩ := by
  simp only [intLattice, MonoidHom.mem_range, map_apply, eq_intCast]
  exact ⟨fun ⟨n, hn⟩ ↦ ⟨n.x, n.y, n.z, hn.symm⟩, fun ⟨a, b, c, h⟩ ↦ ⟨⟨a, b, c⟩, h.symm⟩⟩

/-- The integer Heisenberg group is discrete. -/
instance instDiscreteTopologyIntLattice : DiscreteTopology intLattice := by
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.mpr
    ⟨homeomorphProd ⁻¹' (Ioo (-1) 1 ×ˢ Ioo (-1) 1 ×ˢ Ioo (-1) 1),
      homeomorphProd.isOpen_preimage.mpr (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)), ?_⟩)
  ext ⟨g, hg⟩
  obtain ⟨a, b, c, rfl⟩ := mem_intLattice.mp hg
  simp only [mem_preimage, homeomorphProd_apply, mem_prod, mem_Ioo, mem_singleton_iff]
  rw [Subtype.ext_iff]
  simp only [OneMemClass.coe_one, HeisenbergGroup.ext_iff, one_x, one_y, one_z, Int.cast_eq_zero]
  norm_cast
  omega

/-- An integer `k` with `r + k ∈ [0, 1)` is `-⌊r⌋`. -/
private theorem eq_neg_floor {r : ℝ} {k : ℤ} (h : r + k ∈ Ico (0 : ℝ) 1) : k = -⌊r⌋ := by
  have := Int.floor_eq_zero_iff.mpr h
  rw [Int.floor_add_intCast] at this
  omega

/-- `r - ⌊r⌋` lies in `[0, 1)`. -/
private theorem add_neg_floor_mem (r : ℝ) : r + ((-⌊r⌋ : ℤ) : ℝ) ∈ Ico (0 : ℝ) 1 := by
  rw [Int.cast_neg, ← sub_eq_add_neg, Int.self_sub_floor]
  exact ⟨Int.fract_nonneg r, Int.fract_lt_one r⟩

/-- The unit cube is a Borel set. -/
theorem measurableSet_unitCube : MeasurableSet unitCube :=
  homeomorphProd.continuous.measurable
    (measurableSet_Ico.prod (measurableSet_Ico.prod measurableSet_Ico))

/-- Every coset `g H(ℤ)` meets the unit cube. -/
theorem exists_mul_mem_unitCube (g : HeisenbergGroup ℝ) :
    ∃ γ ∈ intLattice, g * γ ∈ unitCube := by
  -- the translate of `g` by `(a, b, c)` is `(x + a, y + b, z + c + x b)`
  refine ⟨⟨((-⌊g.x⌋ : ℤ) : ℝ), ((-⌊g.y⌋ : ℤ) : ℝ), ((-⌊g.z + g.x * ((-⌊g.y⌋ : ℤ) : ℝ)⌋ : ℤ) : ℝ)⟩,
    mem_intLattice.mpr ⟨_, _, _, rfl⟩, ?_⟩
  simp only [mem_unitCube, mul_x, mul_y, mul_z]
  refine ⟨add_neg_floor_mem _, add_neg_floor_mem _, ?_⟩
  rw [add_right_comm]
  exact add_neg_floor_mem _

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
    simp only [mem_unitCube, mul_x, mul_y, mul_z] at hδmem hmem
    obtain ⟨hx, hy, hz⟩ := hδmem
    obtain ⟨hx', hy', hz'⟩ := hmem
    rw [eq_neg_floor hx, eq_neg_floor hx', eq_neg_floor hy, eq_neg_floor hy'] at *
    rw [add_right_comm] at hz hz'
    rw [eq_neg_floor hz, eq_neg_floor hz']
  rintro ⟨δ, hδ⟩ hδmem
  exact Subtype.ext (MulOpposite.unop_injective (key _ (Subgroup.mem_op.mp hδ) hδmem))

/-- The integer Heisenberg group has covolume one in `H(ℝ)`. -/
theorem covolume_intLattice :
    covolume intLattice.op (HeisenbergGroup ℝ) volume = 1 := by
  have : Countable intLattice := Set.countable_range _ |>.to_subtype
  rw [isFundamentalDomain_unitCube.covolume_eq_volume, volume_unitCube]

/-- The integer Heisenberg group is a uniform lattice in `H(ℝ)`: the closed unit cube is a
compact set whose right `H(ℤ)`-translates cover `H(ℝ)`. -/
theorem isUniformLattice_intLattice :
    intLattice.IsUniformLattice (volume : Measure (HeisenbergGroup ℝ)) := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance, unitCube, isFundamentalDomain_unitCube,
    by simp [volume_unitCube]⟩, homeomorphProd ⁻¹' (Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1),
    homeomorphProd.isCompact_preimage.mpr
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)), ?_⟩
  refine eq_univ_of_forall fun g ↦ ?_
  obtain ⟨γ, hγ, hmem⟩ := exists_mul_mem_unitCube g
  refine ⟨g * γ, ?_, γ⁻¹, Subgroup.inv_mem _ hγ, by group⟩
  rw [mem_unitCube] at hmem
  simp only [mem_preimage, homeomorphProd_apply, mem_prod]
  exact ⟨Ico_subset_Icc_self hmem.1, Ico_subset_Icc_self hmem.2.1, Ico_subset_Icc_self hmem.2.2⟩

/-- **Weil's formula** for the integer Heisenberg lattice: for measurable `f ≥ 0`,
`∫_{H(ℝ)} f = ∫_{[0,1)³} ∑_{(a, b, c) ∈ ℤ³} f(x + a, y + b, z + c + x b)`. -/
theorem lintegral_eq_setLIntegral_unitCube_tsum {f : HeisenbergGroup ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g = ∫⁻ g in unitCube, ∑' n : HeisenbergGroup ℤ, f (g * map (Int.castRingHom ℝ) n) := by
  have : Countable intLattice := Set.countable_range _ |>.to_subtype
  rw [isFundamentalDomain_unitCube.lintegral_eq_tsum'', lintegral_tsum
    (f := fun n g ↦ f (g * map (Int.castRingHom ℝ) n)) fun n ↦
    (hf.comp (measurable_mul_const _)).aemeasurable]
  -- reindex the sum over `H(ℤ)ᵐᵒᵖ` by `HeisenbergGroup ℤ`
  have hinj : Function.Injective (map (Int.castRingHom ℝ)) := fun m n h ↦ by
    simp only [map_apply, eq_intCast, HeisenbergGroup.mk.injEq, Int.cast_inj] at h
    exact HeisenbergGroup.ext h.1 h.2.1 h.2.2
  let e : HeisenbergGroup ℤ → intLattice.op := fun n ↦
    ⟨MulOpposite.op (map (Int.castRingHom ℝ) n), Subgroup.mem_op.mpr ⟨n, rfl⟩⟩
  have he : Function.Bijective e :=
    ⟨fun m n h ↦ hinj (MulOpposite.op_injective (congrArg Subtype.val h)), fun ⟨γ, hγ⟩ ↦ by
      obtain ⟨n, hn⟩ := Subgroup.mem_op.mp hγ
      exact ⟨n, Subtype.ext (MulOpposite.unop_injective hn)⟩⟩
  rw [← (Equiv.ofBijective e he).tsum_eq]
  rfl

end HeisenbergGroup

end TauCeti
