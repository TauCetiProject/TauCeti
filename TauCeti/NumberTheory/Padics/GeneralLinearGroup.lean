/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL n R` and `Matrix.GeneralLinearGroup.map` occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `ℚ_[p]`, `ℤ_[p]` and the inclusion `PadicInt.Coe.ringHom` occur in the statements below.
public import Mathlib.NumberTheory.Padics.PadicIntegers
-- The topology of `GL n ℚ_[p]` as the unit group of the matrix ring occurs in the statements
-- below.
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.Matrix
-- Non-public: the compactness of `ℤ_[p]` is used only in the compactness proof, and the
-- ultrametric determinant bound only in `mem_iff_inv`.
import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.Analysis.Matrix.Ultra

/-!
# The subgroup `GLₙ(ℤ_p)` of `GLₙ(ℚ_p)`

For a prime `p` and a finite index type `n`, this file names the subgroup `GLₙ(ℤ_p)` of
`GLₙ(ℚ_p)`: the image of `GLₙ(ℤ_p)` under the inclusion `ℤ_p ⊂ ℚ_p` (`TauCeti.GLPadicInt`). Its
elements are the matrices with integral entries and unit determinant, equivalently with `g` and
`g⁻¹` both integral. Entrywise integrality alone does not suffice: `diag(p, 1)` is integral but
does not lie in `GL₂(ℤ_p)`. The subgroup `GLₙ(ℤ_p)` is compact and open.

## Main definitions

* `TauCeti.GLPadicInt p n`: the subgroup `GLₙ(ℤ_p)` of `GLₙ(ℚ_p)`.

## Main results

* `TauCeti.GLPadicInt.mem_iff`: `g ∈ GLₙ(ℤ_p)` iff the entries of `g` are integral and its
  determinant is a unit.
* `TauCeti.GLPadicInt.mem_iff_inv`: `g ∈ GLₙ(ℤ_p)` iff `g` and `g⁻¹` have integral entries.
* `TauCeti.GLPadicInt.isOpen`, `TauCeti.GLPadicInt.isCompact`: `GLₙ(ℤ_p)` is open and compact.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010), §III.1.1.
-/

public section

namespace TauCeti

open Matrix

variable (p : ℕ) [hp : Fact p.Prime] (n : Type*) [Fintype n] [DecidableEq n]

/-- The subgroup `GLₙ(ℤ_p)` of `GLₙ(ℚ_p)`: the image of `GLₙ(ℤ_p)` under the inclusion
`ℤ_p ⊂ ℚ_p`. -/
noncomputable def GLPadicInt : Subgroup (GL n ℚ_[p]) :=
  (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p))).range

namespace GLPadicInt

variable {p n}

/-- **Membership in `GLₙ(ℤ_p)`**: an element of `GLₙ(ℚ_p)` lies in `GLₙ(ℤ_p)` exactly when its
entries are integral and its determinant is a `p`-adic unit. -/
theorem mem_iff {g : GL n ℚ_[p]} :
    g ∈ GLPadicInt p n ↔ (∀ i j, ‖(g : Matrix n n ℚ_[p]) i j‖ ≤ 1) ∧
      ‖(g : Matrix n n ℚ_[p]).det‖ = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.map_apply, PadicInt.Coe.ringHom_apply, PadicInt.norm_coe]
      exact PadicInt.norm_le_one _
    · simpa [← RingHom.mapMatrix_apply, ← RingHom.map_det] using
        PadicInt.isUnit_iff.mp (Matrix.GeneralLinearGroup.det h).isUnit
  · rintro ⟨hint, hdet⟩
    -- The entries of `g` lift to a matrix over `ℤ_p`, whose determinant is the unit `det g`.
    set M : Matrix n n ℤ_[p] := fun i j => ⟨_, hint i j⟩
    -- `ℤ_[p]` is a type synonym for a subtype of `ℚ_[p]`, so the value of `⟨x, hx⟩ : ℤ_[p]` is `x`
    -- by `rfl`; Mathlib states no simp lemma for it (compare `PadicInt.mk_coe`).
    have hM : M.map PadicInt.Coe.ringHom = (g : Matrix n n ℚ_[p]) :=
      Matrix.ext fun _ _ => rfl
    have hMdet : IsUnit M.det := by
      simpa [PadicInt.isUnit_iff, ← PadicInt.norm_coe, ← PadicInt.Coe.ringHom_apply,
        RingHom.map_det, hM] using hdet
    refine ⟨Matrix.GeneralLinearGroup.mk'' M hMdet, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    simp [Matrix.GeneralLinearGroup.map_apply, ← hM]

/-- **`GLₙ(ℤ_p)` is the stabiliser of the standard lattice**: an element of `GLₙ(ℚ_p)` lies in
`GLₙ(ℤ_p)` exactly when it and its inverse have integral entries. -/
theorem mem_iff_inv {g : GL n ℚ_[p]} :
    g ∈ GLPadicInt p n ↔ (∀ i j, ‖(g : Matrix n n ℚ_[p]) i j‖ ≤ 1) ∧
      ∀ i j, ‖((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]) i j‖ ≤ 1 := by
  refine ⟨fun hg => ⟨(mem_iff.mp hg).1, (mem_iff.mp (Subgroup.inv_mem _ hg)).1⟩, ?_⟩
  rintro ⟨hg, hg'⟩
  refine mem_iff.mpr ⟨hg, ?_⟩
  -- `det g * det g⁻¹ = 1` with both factors integral forces `‖det g‖ = 1`.
  have h1 : ‖(g : Matrix n n ℚ_[p]).det‖ * ‖((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]).det‖ = 1 := by
    simp [(Matrix.isUnits_det_units g).ne_zero]
  -- By the ultrametric inequality an integral matrix has integral determinant.
  have h2 : ‖(g : Matrix n n ℚ_[p]).det‖ ≤ 1 := by
    simpa using Matrix.norm_det_le_prod_of_norm_le (c := fun _ => 1) hg
  have h3 : ‖((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]).det‖ ≤ 1 := by
    simpa using Matrix.norm_det_le_prod_of_norm_le (c := fun _ => 1) hg'
  nlinarith [norm_nonneg ((g : Matrix n n ℚ_[p]).det),
    norm_nonneg (((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]).det)]

/-- An element of `GLₙ(ℚ_p)` lies in `GLₙ(ℤ_p)` exactly when it is the image of an element of
`GLₙ(ℤ_p)` under the inclusion `ℤ_p ⊂ ℚ_p`. -/
theorem mem_iff_exists_map {g : GL n ℚ_[p]} :
    g ∈ GLPadicInt p n ↔
      ∃ h : GL n ℤ_[p], Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom h = g :=
  MonoidHom.mem_range

/-- The image of an element of `GLₙ(ℤ_p)` under the inclusion `ℤ_p ⊂ ℚ_p` lies in `GLₙ(ℤ_p)`. -/
@[simp]
theorem map_mem (h : GL n ℤ_[p]) :
    Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom h ∈ GLPadicInt p n :=
  MonoidHom.mem_range.mpr ⟨h, rfl⟩

variable (p n)

/-- `GLₙ(ℤ_p)` is open in `GLₙ(ℚ_p)`. -/
theorem isOpen : IsOpen (GLPadicInt p n : Set (GL n ℚ_[p])) := by
  have hball : IsOpen (Metric.closedBall (0 : ℚ_[p]) 1) :=
    IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hset : (GLPadicInt p n : Set (GL n ℚ_[p])) =
      (⋂ (i : n) (j : n), (fun g : GL n ℚ_[p] =>
        (g : Matrix n n ℚ_[p]) i j) ⁻¹' Metric.closedBall 0 1) ∩
      ⋂ (i : n) (j : n), (fun g : GL n ℚ_[p] =>
        ((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]) i j) ⁻¹' Metric.closedBall 0 1 := by
    ext g
    simp [mem_iff_inv]
  rw [hset]
  refine IsOpen.inter
    (isOpen_iInter_of_finite (ι := n) fun i => isOpen_iInter_of_finite (ι := n) fun j =>
      hball.preimage ?_)
    (isOpen_iInter_of_finite (ι := n) fun i => isOpen_iInter_of_finite (ι := n) fun j =>
      hball.preimage ?_)
  · exact Units.continuous_val.matrix_elem i j
  · exact (Units.continuous_val.comp continuous_inv).matrix_elem i j

/-- `GLₙ(ℤ_p)` is compact: it is the continuous image of the compact group `GLₙ(ℤ_p)`. -/
theorem isCompact : IsCompact (GLPadicInt p n : Set (GL n ℚ_[p])) := by
  have hcont : Continuous
      (Matrix.GeneralLinearGroup.map (n := n) (PadicInt.Coe.ringHom (p := p))) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_subtypeVal)
  -- `Matrix` is a type synonym for a function type, so instance search does not find its
  -- compactness, which the compactness instance of the unit group `GL n ℤ_[p]` needs.
  have : CompactSpace (Matrix n n ℤ_[p]) := inferInstanceAs (CompactSpace (n → n → ℤ_[p]))
  exact isCompact_range hcont

end GLPadicInt

end TauCeti
