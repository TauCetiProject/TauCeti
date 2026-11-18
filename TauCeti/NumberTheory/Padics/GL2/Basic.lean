/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2Mirabolic`, `TauCeti.GL2Borel.mk` and `TauCeti.GL2WeylElement` occur in the
-- statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Mirabolic
-- `ℚ_[p]`, `ℤ_[p]` and the inclusion `PadicInt.Coe.ringHom` occur in the statements below.
public import Mathlib.NumberTheory.Padics.PadicIntegers
-- The topology of `GL (Fin 2) ℚ_[p]` as a unit group occurs in the statements below.
public import Mathlib.Topology.Algebra.Group.Units
-- Non-public: the topology on matrices and the compactness of `ℤ_[p]` are used only in the
-- compactness and openness proofs, and the ultrametric inequality and the ultrametric determinant
-- bound only in integrality proofs.
import Mathlib.Topology.Instances.Matrix
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Matrix.Ultra

/-!
# The standard subgroups of `GL₂(ℚ_p)`

For a prime `p` this file names the subgroups and the submonoid of `G = GL₂(ℚ_p)` from which
Colmez's construction of representations of `G` from `(φ, Γ)`-modules starts:

* `K = GL₂(ℤ_p)`, the image of `GL₂(ℤ_p)` under the inclusion `ℤ_p ⊂ ℚ_p`
  (`TauCeti.GL2PadicInt`). Its elements are the matrices with integral entries and unit
  determinant, equivalently with `g` and `g⁻¹` both integral. Entrywise integrality alone does not
  suffice: `diag(p, 1)` is integral but not in `K`. The subgroup `K` is compact and open.
* `P⁺`, the submonoid of the mirabolic subgroup `P = GL2Mirabolic ℚ_[p]` of matrices
  `!![a, b; 0, 1]` with `a, b ∈ ℤ_p` (`TauCeti.GL2MirabolicPlus`). The invertibility of the
  matrix forces `a ≠ 0`.
* `P(ℤ_p) = P ∩ K`, the matrices `!![a, b; 0, 1]` with `a ∈ ℤ_p^×` and `b ∈ ℤ_p`
  (`TauCeti.GL2MirabolicPadicInt`). It is contained in `P⁺`.
* `φ = diag(p, 1)` (`TauCeti.GL2PhiElement`), which lies in `P⁺` while its inverse does not.

Colmez makes an étale `(φ, Γ)`-module into a module over `P⁺`: the unipotent `!![1, 1; 0, 1]`
acts as multiplication by `1 + T`, `φ` acts as the Frobenius and `diag(a, 1)` for `a ∈ ℤ_p^×` acts
as the element of `Γ` with cyclotomic character `a`. The passage from `P⁺` to `P` inverts `φ`: every
element of `P` is `φ⁻ⁿ` times an element of `P⁺`, so `P` is generated as a monoid by `P⁺` and `φ⁻¹`
(`TauCeti.GL2MirabolicPlus.closure_insert_inv_gl2PhiElement_eq_gl2Mirabolic`). Together with
`TauCeti.GL2Mirabolic.closure_insert_gl2WeylElement_union_center_eq_top`, which says that `P`, the
centre and the Weyl element generate `G`, this is the group-theoretic input of the construction.

## Main definitions

* `TauCeti.GL2PadicInt p`: the subgroup `GL₂(ℤ_p)` of `GL₂(ℚ_p)`.
* `TauCeti.GL2MirabolicPlus p`: the submonoid `P⁺` of `GL₂(ℚ_p)`.
* `TauCeti.GL2MirabolicPadicInt p`: the subgroup `P(ℤ_p) = P ∩ GL₂(ℤ_p)`.
* `TauCeti.GL2PhiElement p`: the matrix `diag(p, 1)`.

## Main results

* `TauCeti.GL2PadicInt.mem_iff`: `g ∈ GL₂(ℤ_p)` iff the entries of `g` are integral and its
  determinant is a unit.
* `TauCeti.GL2PadicInt.isOpen`, `TauCeti.GL2PadicInt.isCompact`: `GL₂(ℤ_p)` is open and compact.
* `TauCeti.GL2MirabolicPlus.mk_mem_iff`: `!![a, b; 0, 1] ∈ P⁺` iff `a` and `b` are integral.
* `TauCeti.GL2MirabolicPadicInt.mem_iff`: `P(ℤ_p)` consists of the mirabolic matrices with
  upper-left entry a `p`-adic unit and integral upper-right entry.
* `TauCeti.GL2MirabolicPlus.exists_gl2PhiElement_pow_mul_mem`: every element of `P` lands in
  `P⁺` after multiplication by a power of `φ`.
* `TauCeti.GL2MirabolicPlus.closure_insert_inv_gl2PhiElement_eq_gl2Mirabolic`: `P⁺` and `φ⁻¹`
  generate `P` as a monoid.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010),
  Introduction §4, Remarque 0.4, and §III.1.1–III.1.2.
* V. Paškūnas, *The image of Colmez's Montreal functor*, Publ. Math. IHÉS 118 (2013), §1.
-/

public section

namespace TauCeti

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

/-- The subgroup `GL₂(ℤ_p)` of `GL₂(ℚ_p)`: the image of `GL₂(ℤ_p)` under the inclusion
`ℤ_p ⊂ ℚ_p`. -/
noncomputable def GL2PadicInt : Subgroup (GL (Fin 2) ℚ_[p]) :=
  (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p))).range

/-- The positive mirabolic monoid `P⁺`: the matrices `!![a, b; 0, 1]` with `a` and `b` in `ℤ_p`.
Invertibility forces `a ≠ 0`. -/
noncomputable def GL2MirabolicPlus : Submonoid (GL (Fin 2) ℚ_[p]) where
  carrier := {g | g ∈ GL2Mirabolic ℚ_[p] ∧
    ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0‖ ≤ 1 ∧ ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ 1}
  one_mem' := ⟨Subgroup.one_mem _, by simp, by simp⟩
  mul_mem' := by
    rintro g h ⟨hgP, hg₀, hg₁⟩ ⟨hhP, hh₀, hh₁⟩
    refine ⟨Subgroup.mul_mem _ hgP hhP, ?_, ?_⟩
    · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        (GL2Mirabolic.mem_iff.mp hhP).1, mul_zero, add_zero, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hg₀).trans hh₀
    · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        (GL2Mirabolic.mem_iff.mp hhP).2, mul_one]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hg₁)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hg₀).trans hh₁

/-- The integral mirabolic subgroup `P(ℤ_p) = P ∩ GL₂(ℤ_p)`: the matrices `!![a, b; 0, 1]` with
`a ∈ ℤ_p^×` and `b ∈ ℤ_p`. -/
noncomputable def GL2MirabolicPadicInt : Subgroup (GL (Fin 2) ℚ_[p]) :=
  GL2Mirabolic ℚ_[p] ⊓ GL2PadicInt p

/-- The matrix `φ = diag(p, 1)`, which acts on étale `(φ, Γ)`-modules as the Frobenius. -/
noncomputable def GL2PhiElement : GL (Fin 2) ℚ_[p] :=
  GL2Borel.mk (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.out.ne_zero)) 1 0

variable {p}

/-- The underlying matrix of `φ` is `diag(p, 1)`. -/
@[simp]
theorem coe_gl2PhiElement :
    ((GL2PhiElement p : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      !![(p : ℚ_[p]), 0; 0, 1] := by
  simp [GL2PhiElement]

/-- `φ = diag(p, 1)` in the normal form `TauCeti.GL2Borel.mk` of upper-triangular matrices. -/
theorem gl2PhiElement_eq_mk :
    GL2PhiElement p =
      GL2Borel.mk (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.out.ne_zero)) 1 0 :=
  (rfl)

/-- The inverse of `φ = diag(p, 1)` is `diag(p⁻¹, 1)`. -/
theorem inv_gl2PhiElement :
    (GL2PhiElement p)⁻¹ =
      GL2Borel.mk (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.out.ne_zero))⁻¹ 1 0 := by
  simp [gl2PhiElement_eq_mk]

/-- The powers of `φ = diag(p, 1)` are the matrices `diag(pⁿ, 1)`. -/
theorem gl2PhiElement_pow (n : ℕ) :
    GL2PhiElement p ^ n =
      GL2Borel.mk (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.out.ne_zero) ^ n) 1 0 := by
  -- `φ` is the image of `(p, 1)` under the torus homomorphism, which commutes with powers.
  rw [gl2PhiElement_eq_mk, ← GL2Borel.coe_torusHom (_, 1), ← Subgroup.coe_pow, ← map_pow,
    Prod.pow_mk, one_pow, GL2Borel.coe_torusHom]

namespace GL2PadicInt

/-- **Membership in `GL₂(ℤ_p)`**: an element of `GL₂(ℚ_p)` lies in `GL₂(ℤ_p)` exactly when its
entries are integral and its determinant is a `p`-adic unit. -/
theorem mem_iff {g : GL (Fin 2) ℚ_[p]} :
    g ∈ GL2PadicInt p ↔ (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1) ∧
      ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.map_apply, PadicInt.Coe.ringHom_apply, PadicInt.norm_coe]
      exact PadicInt.norm_le_one _
    · simpa [← RingHom.mapMatrix_apply, ← RingHom.map_det] using
        PadicInt.isUnit_iff.mp (Matrix.GeneralLinearGroup.det h).isUnit
  · rintro ⟨hint, hdet⟩
    -- The entries of `g` lift to a matrix over `ℤ_p`, whose determinant is the unit `det g`.
    set M : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j => ⟨_, hint i j⟩
    -- `ℤ_[p]` is a type synonym for a subtype of `ℚ_[p]`, so the value of `⟨x, hx⟩ : ℤ_[p]` is `x`
    -- by `rfl`; Mathlib states no simp lemma for it (compare `PadicInt.mk_coe`).
    have hM : M.map PadicInt.Coe.ringHom = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :=
      Matrix.ext fun _ _ => rfl
    have hMdet : IsUnit M.det := by
      simpa [PadicInt.isUnit_iff, ← PadicInt.norm_coe, ← PadicInt.Coe.ringHom_apply,
        RingHom.map_det, hM] using hdet
    refine ⟨Matrix.GeneralLinearGroup.mk'' M hMdet, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    simp [Matrix.GeneralLinearGroup.map_apply, ← hM]

/-- **`GL₂(ℤ_p)` is the stabiliser of the standard lattice**: an element of `GL₂(ℚ_p)` lies in
`GL₂(ℤ_p)` exactly when it and its inverse have integral entries. -/
theorem mem_iff_inv {g : GL (Fin 2) ℚ_[p]} :
    g ∈ GL2PadicInt p ↔ (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1) ∧
      ∀ i j, ‖((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := by
  refine ⟨fun hg => ⟨(mem_iff.mp hg).1, (mem_iff.mp (Subgroup.inv_mem _ hg)).1⟩, ?_⟩
  rintro ⟨hg, hg'⟩
  refine mem_iff.mpr ⟨hg, ?_⟩
  -- `det g * det g⁻¹ = 1` with both factors integral forces `‖det g‖ = 1`.
  have h1 : ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ *
      ‖((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ = 1 := by
    simp [(Matrix.isUnits_det_units g).ne_zero]
  -- By the ultrametric inequality an integral matrix has integral determinant.
  have h2 : ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ ≤ 1 := by
    simpa using Matrix.norm_det_le_prod_of_norm_le (c := fun _ => 1) hg
  have h3 : ‖((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ ≤ 1 := by
    simpa using Matrix.norm_det_le_prod_of_norm_le (c := fun _ => 1) hg'
  nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det),
    norm_nonneg (((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).det)]

/-- An element of `GL₂(ℚ_p)` lies in `GL₂(ℤ_p)` exactly when it is the image of an element of
`GL₂(ℤ_p)` under the inclusion `ℤ_p ⊂ ℚ_p`. -/
theorem mem_iff_exists_map {g : GL (Fin 2) ℚ_[p]} :
    g ∈ GL2PadicInt p ↔
      ∃ h : GL (Fin 2) ℤ_[p], Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom h = g :=
  MonoidHom.mem_range

/-- The image of an element of `GL₂(ℤ_p)` under the inclusion `ℤ_p ⊂ ℚ_p` lies in `GL₂(ℤ_p)`. -/
@[simp]
theorem map_mem (h : GL (Fin 2) ℤ_[p]) :
    Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom h ∈ GL2PadicInt p :=
  MonoidHom.mem_range.mpr ⟨h, rfl⟩

variable (p)

/-- `GL₂(ℤ_p)` is open in `GL₂(ℚ_p)`. -/
theorem isOpen : IsOpen (GL2PadicInt p : Set (GL (Fin 2) ℚ_[p])) := by
  have hball : IsOpen (Metric.closedBall (0 : ℚ_[p]) 1) :=
    IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hset : (GL2PadicInt p : Set (GL (Fin 2) ℚ_[p])) =
      (⋂ (i : Fin 2) (j : Fin 2), (fun g : GL (Fin 2) ℚ_[p] =>
        (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j) ⁻¹' Metric.closedBall 0 1) ∩
      ⋂ (i : Fin 2) (j : Fin 2), (fun g : GL (Fin 2) ℚ_[p] =>
        ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j) ⁻¹'
          Metric.closedBall 0 1 := by
    ext g
    simp [mem_iff_inv]
  rw [hset]
  refine IsOpen.inter
    (isOpen_iInter_of_finite (ι := Fin 2) fun i => isOpen_iInter_of_finite (ι := Fin 2) fun j =>
      hball.preimage ?_)
    (isOpen_iInter_of_finite (ι := Fin 2) fun i => isOpen_iInter_of_finite (ι := Fin 2) fun j =>
      hball.preimage ?_)
  · exact Units.continuous_val.matrix_elem i j
  · exact (Units.continuous_val.comp continuous_inv).matrix_elem i j

/-- `GL₂(ℤ_p)` is compact: it is the continuous image of the compact group `GL₂(ℤ_p)`. -/
theorem isCompact : IsCompact (GL2PadicInt p : Set (GL (Fin 2) ℚ_[p])) := by
  have hcont : Continuous
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (PadicInt.Coe.ringHom (p := p))) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map continuous_subtype_val
    · exact Units.continuous_coe_inv.matrix_map continuous_subtype_val
  -- `Matrix` is a type synonym for a function type, so instance search does not find its
  -- compactness, which the compactness instance of the unit group `GL (Fin 2) ℤ_[p]` needs.
  have : CompactSpace (Matrix (Fin 2) (Fin 2) ℤ_[p]) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → ℤ_[p]))
  exact isCompact_range hcont

end GL2PadicInt

/-- The Weyl element lies in `GL₂(ℤ_p)`. -/
theorem gl2WeylElement_mem_gl2PadicInt : GL2WeylElement ℚ_[p] ∈ GL2PadicInt p := by
  refine GL2PadicInt.mem_iff.mpr ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp
  · simp [Matrix.det_fin_two]

/-- The integral matrix `φ = diag(p, 1)` does not lie in `GL₂(ℤ_p)`, its determinant `p` not being
a unit: entrywise integrality alone does not characterise `GL₂(ℤ_p)`. -/
theorem gl2PhiElement_notMem_gl2PadicInt : GL2PhiElement p ∉ GL2PadicInt p := by
  intro h
  exact hp.out.ne_one <| by
    simpa [Matrix.det_fin_two, Padic.norm_p] using (GL2PadicInt.mem_iff.mp h).2

namespace GL2MirabolicPlus

theorem mem_iff {g : GL (Fin 2) ℚ_[p]} :
    g ∈ GL2MirabolicPlus p ↔ g ∈ GL2Mirabolic ℚ_[p] ∧
      ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0‖ ≤ 1 ∧
      ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ 1 :=
  Iff.rfl

/-- `P⁺` is a submonoid of the mirabolic subgroup. -/
theorem le_gl2Mirabolic : GL2MirabolicPlus p ≤ (GL2Mirabolic ℚ_[p]).toSubmonoid :=
  fun _ hg => hg.1

/-- **Membership in `P⁺`**: the mirabolic matrix `!![a, b; 0, 1]` lies in `P⁺` exactly when `a` and
`b` are integral. -/
@[simp]
theorem mk_mem_iff {a : ℚ_[p]ˣ} {b : ℚ_[p]} :
    GL2Borel.mk a 1 b ∈ GL2MirabolicPlus p ↔ ‖(a : ℚ_[p])‖ ≤ 1 ∧ ‖b‖ ≤ 1 := by
  simp [mem_iff, GL2Mirabolic.mk_mem]

/-- The upper unipotent matrix `!![1, b; 0, 1]` lies in `P⁺` exactly when `b` is integral. -/
theorem upperRightHom_mem_iff {b : ℚ_[p]} :
    Matrix.GeneralLinearGroup.upperRightHom b ∈ GL2MirabolicPlus p ↔ ‖b‖ ≤ 1 := by
  simp [mem_iff, GL2Mirabolic.mem_iff, Matrix.GeneralLinearGroup.upperRightHom]

end GL2MirabolicPlus

/-- `φ = diag(p, 1)` lies in `P⁺`. -/
theorem gl2PhiElement_mem_gl2MirabolicPlus : GL2PhiElement p ∈ GL2MirabolicPlus p := by
  rw [gl2PhiElement_eq_mk, GL2MirabolicPlus.mk_mem_iff]
  simpa [Padic.norm_p] using inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr hp.out.one_lt.le)

/-- `φ⁻¹ = diag(p⁻¹, 1)` does not lie in `P⁺`, its upper-left entry not being integral. -/
theorem inv_gl2PhiElement_notMem_gl2MirabolicPlus : (GL2PhiElement p)⁻¹ ∉ GL2MirabolicPlus p := by
  simp [inv_gl2PhiElement, Padic.norm_p, hp.out.one_lt]

namespace GL2MirabolicPadicInt

variable (p) in
/-- `P(ℤ_p)` is the intersection of the mirabolic subgroup with `GL₂(ℤ_p)`. -/
theorem eq_inf : GL2MirabolicPadicInt p = GL2Mirabolic ℚ_[p] ⊓ GL2PadicInt p :=
  (rfl)

/-- `P(ℤ_p) ⊆ P`. -/
theorem le_gl2Mirabolic : GL2MirabolicPadicInt p ≤ GL2Mirabolic ℚ_[p] :=
  inf_le_left

/-- `P(ℤ_p) ⊆ GL₂(ℤ_p)`. -/
theorem le_gl2PadicInt : GL2MirabolicPadicInt p ≤ GL2PadicInt p :=
  inf_le_right

/-- **Membership in `P(ℤ_p)`**: a mirabolic matrix `!![a, b; 0, 1]` lies in `GL₂(ℤ_p)` exactly when
`a` is a `p`-adic unit and `b` is integral. -/
theorem mem_iff {g : GL (Fin 2) ℚ_[p]} :
    g ∈ GL2MirabolicPadicInt p ↔ g ∈ GL2Mirabolic ℚ_[p] ∧
      ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0‖ = 1 ∧
      ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ 1 := by
  rw [eq_inf, Subgroup.mem_inf, and_congr_right_iff]
  intro hg
  obtain ⟨hg₀, hg₁⟩ := GL2Mirabolic.mem_iff.mp hg
  rw [GL2PadicInt.mem_iff, GL2Mirabolic.det_eq hg]
  refine ⟨fun h => ⟨h.2, h.1 0 1⟩, fun h => ⟨fun i j => ?_, h.1⟩⟩
  fin_cases i <;> fin_cases j <;> simp [h.1.le, h.2, hg₀, hg₁]

/-- **Membership in `P(ℤ_p)`**: the mirabolic matrix `!![a, b; 0, 1]` lies in `P(ℤ_p)` exactly
when `a` is a `p`-adic unit and `b` is integral. -/
@[simp]
theorem mk_mem_iff {a : ℚ_[p]ˣ} {b : ℚ_[p]} :
    GL2Borel.mk a 1 b ∈ GL2MirabolicPadicInt p ↔ ‖(a : ℚ_[p])‖ = 1 ∧ ‖b‖ ≤ 1 := by
  simp [mem_iff, GL2Mirabolic.mk_mem]

/-- `P(ℤ_p) ⊆ P⁺`. -/
theorem le_gl2MirabolicPlus : (GL2MirabolicPadicInt p).toSubmonoid ≤ GL2MirabolicPlus p :=
  fun _ hg =>
    have h := mem_iff.mp hg
    ⟨h.1, h.2.1.le, h.2.2⟩

end GL2MirabolicPadicInt

namespace GL2MirabolicPlus

/-- **`P = ⋃ φ⁻ⁿ P⁺`**: every element of the mirabolic subgroup is carried into `P⁺` by
multiplication with a power of `φ = diag(p, 1)`. -/
theorem exists_gl2PhiElement_pow_mul_mem {g : GL (Fin 2) ℚ_[p]} (hg : g ∈ GL2Mirabolic ℚ_[p]) :
    ∃ n : ℕ, GL2PhiElement p ^ n * g ∈ GL2MirabolicPlus p := by
  obtain ⟨a, b, rfl⟩ := GL2Mirabolic.mem_iff_exists_mk.mp hg
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max ‖(a : ℚ_[p])‖ ‖b‖)
    (Nat.one_lt_cast.mpr hp.out.one_lt : (1 : ℝ) < p)
  -- Multiplying by `p ^ n` scales both coordinates by `p⁻ⁿ` in norm.
  have hscale : ∀ x : ℚ_[p], ‖x‖ < (p : ℝ) ^ n → ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1 := by
    intro x hx
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow,
      inv_mul_le_iff₀ (pow_pos (Nat.cast_pos.mpr hp.out.pos) n), mul_one]
    exact hx.le
  refine ⟨n, ?_⟩
  simpa [gl2PhiElement_pow] using
    And.intro (hscale _ ((le_max_left _ _).trans_lt hn)) (hscale _ ((le_max_right _ _).trans_lt hn))

variable (p)

/-- **`P⁺` and `φ⁻¹` generate `P`**: the mirabolic subgroup of `GL₂(ℚ_p)` is generated as a monoid,
hence also as a group, by the positive mirabolic monoid and the inverse of `φ = diag(p, 1)`. -/
theorem closure_insert_inv_gl2PhiElement_eq_gl2Mirabolic :
    Submonoid.closure (insert (GL2PhiElement p)⁻¹ (GL2MirabolicPlus p : Set (GL (Fin 2) ℚ_[p]))) =
      (GL2Mirabolic ℚ_[p]).toSubmonoid := by
  refine le_antisymm (Submonoid.closure_le.mpr ?_) fun g hg => ?_
  · rintro g (rfl | hg)
    · exact Subgroup.inv_mem _ (le_gl2Mirabolic gl2PhiElement_mem_gl2MirabolicPlus)
    · exact le_gl2Mirabolic hg
  · obtain ⟨n, hn⟩ := exists_gl2PhiElement_pow_mul_mem hg
    have hφ : (GL2PhiElement p)⁻¹ ∈ Submonoid.closure
        (insert (GL2PhiElement p)⁻¹ (GL2MirabolicPlus p : Set (GL (Fin 2) ℚ_[p]))) :=
      Submonoid.subset_closure (Set.mem_insert _ _)
    have h := Submonoid.mul_mem _ (Submonoid.pow_mem _ hφ n)
      (Submonoid.subset_closure (Set.mem_insert_of_mem _ hn))
    rwa [inv_pow, inv_mul_cancel_left] at h

end GL2MirabolicPlus

end TauCeti
