/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Stabilizer
public import TauCeti.NumberTheory.IntegralLattice.Binary.Isometry
public import TauCeti.NumberTheory.IntegralLattice.Binary.Order
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Proper automorphisms of binary lattices and norm-one units

Let `L` be an integral lattice of rank two with nonzero form, and fix a carrier basis. Writing a
proper isometry of `L` as its matrix in that basis identifies `SO(L)` with the stabilizer in
`SL(2, ℤ)` of the binary norm form, that is, with its proper automorphs. Through the primitive part
of the norm form, these are the norm-one units of the quadratic order `𝒪(L) = ℤ[(Δ + √Δ)/2]` of
the primitive discriminant `Δ`:
```
SO(L) ≃* {u ∈ 𝒪(L)ˣ : N(u) = 1}.
```
The unit `x + y√Δ` acts by `!![x - b y, -2 c y; 2 a y, x + b y]`, where `(a, b, c)` is the primitive
part of the norm form. The isomorphism depends on the basis only through conjugation, and it holds
for degenerate nonzero forms as well.

The three cases of the unit group give the size of `SO(L)`:

* for `Δ < 0`, every unit has norm one, so `|SO(L)| = #𝒪(L)ˣ`, which is `6`, `4` or `2`;
* for `Δ > 0` not a square, Pell's equation gives infinitely many norm-one units, so `SO(L)` and
  `O(L)` are infinite;
* for a nonzero square `Δ`, the norm-one units are `±1`, so `SO(L) = {±1}`.

The infinite case is the input that the anisotropic indefinite lattices of rank at least three
need, since their automorphisms are built from those of an anisotropic binary sublattice.

## Main results

* `TauCeti.IntegralLattice.specialOrthogonalGroupEquivStabilizer`: `SO(L)` is the group of proper
  automorphs of the norm form in a carrier basis.
* `TauCeti.IntegralLattice.specialOrthogonalGroupEquivNormOneUnits`: `SO(L)` is the group of
  norm-one units of the order of `L`.
* `TauCeti.IntegralLattice.card_specialOrthogonalGroup_of_binaryDiscriminant_neg`: for negative
  discriminant, `|SO(L)| = #𝒪(L)ˣ`.
* `TauCeti.IntegralLattice.infinite_isometry_of_binaryDiscriminant_pos_of_not_isSquare`: for
  positive nonsquare discriminant, `O(L)` is infinite, and already `SO(L)` is, by
  `infinite_specialOrthogonalGroup_of_binaryDiscriminant_pos_of_not_isSquare`.
* `TauCeti.IntegralLattice.card_specialOrthogonalGroup_of_isSquare_binaryDiscriminant`: for a
  nonzero square discriminant, `|SO(L)| = 2`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2 and §7.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 13.
-/

public section

open Module Matrix MulAction
open scoped MatrixGroups

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}
variable (b : Basis (Fin 2) ℤ L)

/-- The matrix of a proper isometry in a carrier basis, as an element of `SL(2, ℤ)`. -/
private noncomputable def toSL : specialOrthogonalGroup L →* SL(2, ℤ) where
  toFun g := ⟨LinearMap.toMatrix b b ((g : Isometry L L).carrierEquiv : L →ₗ[ℤ] L), by
    rw [LinearMap.det_toMatrix, ← Isometry.coe_det, mem_specialOrthogonalGroup_iff.mp g.prop,
      Units.val_one]⟩
  map_one' := Subtype.ext <|
    (congrArg (fun e : L ≃ₗ[ℤ] L ↦ LinearMap.toMatrix b b (e : L →ₗ[ℤ] L))
      (Isometry.carrierEquiv_refl L)).trans (LinearMap.toMatrix_id b)
  map_mul' g h := Subtype.ext <|
    (congrArg (fun e : L ≃ₗ[ℤ] L ↦ LinearMap.toMatrix b b (e : L →ₗ[ℤ] L))
      (Isometry.carrierEquiv_trans (h : Isometry L L) g)).trans
      (LinearMap.toMatrix_comp b b b _ _)

private theorem coe_toSL (g : specialOrthogonalGroup L) :
    ((toSL b g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      LinearMap.toMatrix b b ((g : Isometry L L).carrierEquiv : L →ₗ[ℤ] L) := (rfl)

/-- The matrix of a proper isometry fixes the binary norm form. -/
private theorem toSL_mem_stabilizer (g : specialOrthogonalGroup L) :
    toSL b g ∈ stabilizer SL(2, ℤ) (L.binaryNormForm b) := by
  have h := L.binaryNormForm_eq_inv_smul b (b.map (g : Isometry L L).carrierEquiv) (toSL b g)
    (by rw [coe_toSL, LinearMap.toMatrix_eq_basisToMatrix, Basis.coe_map]; rfl)
  rw [← Isometry.carrierBasisEquiv_apply, binaryNormForm_map_isometry] at h
  exact (Subgroup.inv_mem_iff _).mp (mem_stabilizer_iff.mpr h.symm)

private theorem toSL_injective : Function.Injective (toSL (L := L) b) := by
  intro g h hgh
  apply Subtype.ext
  apply Isometry.carrierEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix b b).injective
  simpa only [coe_toSL] using congrArg (fun γ : SL(2, ℤ) ↦ (γ : Matrix (Fin 2) (Fin 2) ℤ)) hgh

/-- Every proper automorph of the norm form is the matrix of a proper isometry. -/
private theorem exists_toSL_eq {γ : SL(2, ℤ)} (hγ : γ ∈ stabilizer SL(2, ℤ) (L.binaryNormForm b)) :
    ∃ g : specialOrthogonalGroup L, toSL b g = γ := by
  let φ := Matrix.toLinearEquiv b (γ : Matrix (Fin 2) (Fin 2) ℤ)
    (by rw [SpecialLinearGroup.det_coe]; exact isUnit_one)
  have hφ : b.toMatrix (b.map φ) = γ := by
    rw [Basis.coe_map, ← LinearEquiv.coe_toLinearMap, ← LinearMap.toMatrix_eq_basisToMatrix]
    exact LinearMap.toMatrix_toLin b b _
  have hN : L.binaryNormForm (b.map φ) = L.binaryNormForm b := by
    rw [L.binaryNormForm_eq_inv_smul b _ γ hφ]
    exact mem_stabilizer_iff.mp ((Subgroup.inv_mem_iff _).mpr hγ)
  obtain ⟨e, he⟩ := (exists_isometry_map_basis_iff b (b.map φ)).mpr hN
  have hm : LinearMap.toMatrix b b (e.carrierEquiv : L →ₗ[ℤ] L) = γ := by
    rw [LinearMap.toMatrix_eq_basisToMatrix, LinearEquiv.coe_toLinearMap, ← Basis.coe_map,
      ← Isometry.carrierBasisEquiv_apply, he, hφ]
  have hdet : e ∈ specialOrthogonalGroup L := by
    rw [mem_specialOrthogonalGroup_iff]
    apply Units.ext
    rw [Isometry.coe_det, ← LinearMap.det_toMatrix b, hm, SpecialLinearGroup.det_coe, Units.val_one]
  exact ⟨⟨e, hdet⟩, Subtype.ext hm⟩

/-- **Proper isometries are proper automorphs.** In a carrier basis `b` of a rank-two lattice, the
matrix of a proper isometry is an element of `SL(2, ℤ)` fixing the binary norm form, and every such
automorph arises from exactly one proper isometry. -/
noncomputable def specialOrthogonalGroupEquivStabilizer :
    specialOrthogonalGroup L ≃* stabilizer SL(2, ℤ) (L.binaryNormForm b) :=
  MulEquiv.ofBijective ((toSL b).codRestrict _ (toSL_mem_stabilizer b))
    ⟨fun _ _ h ↦ toSL_injective b (congrArg Subtype.val h), fun γ ↦
      (exists_toSL_eq b γ.prop).imp fun _ hg ↦ Subtype.ext hg⟩

/-- The automorph attached to a proper isometry is its matrix in the carrier basis. -/
@[simp]
theorem coe_specialOrthogonalGroupEquivStabilizer_apply (g : specialOrthogonalGroup L) :
    ((specialOrthogonalGroupEquivStabilizer b g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      LinearMap.toMatrix b b ((g : Isometry L L).carrierEquiv : L →ₗ[ℤ] L) := (rfl)

/-- The proper isometry attached to an automorph of the norm form has that automorph as its matrix
in the carrier basis. -/
@[simp]
theorem toMatrix_specialOrthogonalGroupEquivStabilizer_symm_apply
    (γ : stabilizer SL(2, ℤ) (L.binaryNormForm b)) :
    LinearMap.toMatrix b b (((specialOrthogonalGroupEquivStabilizer b).symm γ :
      Isometry L L).carrierEquiv : L →ₗ[ℤ] L) = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [← coe_specialOrthogonalGroupEquivStabilizer_apply, MulEquiv.apply_symm_apply]

variable (hV : Module.finrank ℚ V = 2)

/-- **Proper isometries of a binary lattice are norm-one units.** For a rank-two lattice with
nonzero form and a carrier basis `b`, the proper isometries form a group isomorphic to the norm-one
units of the quadratic order of the primitive discriminant. The inverse is described by
`map_toMatrix_specialOrthogonalGroupEquivNormOneUnits_symm_apply`. -/
noncomputable def specialOrthogonalGroupEquivNormOneUnits (hL : L.form ≠ 0) :
    specialOrthogonalGroup L ≃* QuadraticOrder.normOneUnits (L.binaryDiscriminant hV)
      (L.binaryDiscriminant_emod_four_eq_zero_or_one hV) :=
  (specialOrthogonalGroupEquivStabilizer b).trans <|
    (MulEquiv.subgroupCongr (BinaryQuadraticForm.stabilizer_primPart _).symm).trans <|
      BinaryQuadraticForm.stabilizerEquivNormOneUnits (L.isPrimitive_binaryNormForm_primPart b hL)
        (L.binaryDiscriminant_eq_discrim_primPart b hV).symm

/-- The proper isometry attached to the norm-one unit `x + y√Δ` has matrix
`!![x - b y, -2 c y; 2 a y, x + b y]` in the carrier basis, read over `ℚ`, where `(a, b, c)` is the
primitive part of the norm form. -/
theorem map_toMatrix_specialOrthogonalGroupEquivNormOneUnits_symm_apply (hL : L.form ≠ 0)
    (u : QuadraticOrder.normOneUnits (L.binaryDiscriminant hV)
      (L.binaryDiscriminant_emod_four_eq_zero_or_one hV)) :
    (LinearMap.toMatrix b b
        (((specialOrthogonalGroupEquivNormOneUnits b hV hL).symm u : Isometry L L).carrierEquiv :
          L →ₗ[ℤ] L)).map (Int.cast : ℤ → ℚ) =
      let f := (L.binaryNormForm b).primPart
      let O := QuadraticOrder.toSubalgebra (L.binaryDiscriminant hV)
        (L.binaryDiscriminant_emod_four_eq_zero_or_one hV)
      let x := ((u : Oˣ) : QuadraticAlgebra ℚ (L.binaryDiscriminant hV : ℚ) 0).re
      let y := ((u : Oˣ) : QuadraticAlgebra ℚ (L.binaryDiscriminant hV : ℚ) 0).im
      !![x - f.b * y, -2 * f.c * y; 2 * f.a * y, x + f.b * y] := by
  rw [← BinaryQuadraticForm.map_stabilizerEquivNormOneUnits_symm_apply
    (L.isPrimitive_binaryNormForm_primPart b hL)
    (L.binaryDiscriminant_eq_discrim_primPart b hV).symm u,
    specialOrthogonalGroupEquivNormOneUnits, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
    toMatrix_specialOrthogonalGroupEquivStabilizer_symm_apply, MulEquiv.subgroupCongr_symm_apply]

/-- A rank-two lattice with nonzero primitive discriminant has nonzero form. -/
private theorem form_ne_zero_of_binaryDiscriminant_ne_zero (h : L.binaryDiscriminant hV ≠ 0) :
    L.form ≠ 0 := by
  intro hL
  apply h
  rw [L.binaryDiscriminant_eq_discrim_primPart
    (finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)) hV,
    (binaryNormForm_eq_zero_iff _ _).mpr hL]
  simp [BinaryQuadraticForm.discrim_def, discrim]

/-- **Negative discriminant.** For a rank-two lattice of negative primitive discriminant, the
proper isometries are as many as the units of its quadratic order. The unit count is
`QuadraticOrder.card_units_of_neg`: `6` for `Δ = -3`, `4` for `Δ = -4`, and `2` otherwise. -/
theorem card_specialOrthogonalGroup_of_binaryDiscriminant_neg
    (hneg : L.binaryDiscriminant hV < 0) :
    Nat.card (specialOrthogonalGroup L) = Nat.card (L.binaryOrder hV)ˣ := by
  rw [Nat.card_congr (specialOrthogonalGroupEquivNormOneUnits
    (finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)) hV
    (form_ne_zero_of_binaryDiscriminant_ne_zero hV hneg.ne)).toEquiv,
    QuadraticOrder.normOneUnits_eq_top_of_neg _ _ hneg, Subgroup.card_top, binaryOrder_def]

/-- **Positive nonsquare discriminant.** A rank-two lattice whose primitive discriminant is positive
and not a square has infinitely many proper isometries, by Pell's equation. -/
theorem infinite_specialOrthogonalGroup_of_binaryDiscriminant_pos_of_not_isSquare
    (hpos : 0 < L.binaryDiscriminant hV) (hns : ¬ IsSquare (L.binaryDiscriminant hV)) :
    Infinite (specialOrthogonalGroup L) :=
  (specialOrthogonalGroupEquivNormOneUnits (finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV))
    hV (form_ne_zero_of_binaryDiscriminant_ne_zero hV hpos.ne')).toEquiv.infinite_iff.mpr
    (QuadraticOrder.infinite_normOneUnits_of_pos_of_not_isSquare _ _ hpos hns)

/-- **Positive nonsquare discriminant.** A rank-two lattice whose primitive discriminant is positive
and not a square has infinitely many isometries. -/
theorem infinite_isometry_of_binaryDiscriminant_pos_of_not_isSquare
    (hpos : 0 < L.binaryDiscriminant hV) (hns : ¬ IsSquare (L.binaryDiscriminant hV)) :
    Infinite (Isometry L L) :=
  have := infinite_specialOrthogonalGroup_of_binaryDiscriminant_pos_of_not_isSquare hV hpos hns
  Infinite.of_injective (Subtype.val : specialOrthogonalGroup L → Isometry L L)
    Subtype.val_injective

/-- **Nonzero square discriminant.** A rank-two lattice whose primitive discriminant is a nonzero
square has exactly two proper isometries, the identity and negation. -/
theorem card_specialOrthogonalGroup_of_isSquare_binaryDiscriminant
    (hsq : IsSquare (L.binaryDiscriminant hV)) (h₀ : L.binaryDiscriminant hV ≠ 0) :
    Nat.card (specialOrthogonalGroup L) = 2 := by
  obtain ⟨s, hs⟩ := hsq
  have hs₀ : s ≠ 0 := by rintro rfl; exact h₀ (by simpa using hs)
  have key (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) (hDs : D = s ^ 2) :
      Nat.card (QuadraticOrder.normOneUnits D hD) = 2 := by
    subst hDs
    exact QuadraticOrder.card_normOneUnits_sq s hs₀
  rw [Nat.card_congr (specialOrthogonalGroupEquivNormOneUnits
    (finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)) hV
    (form_ne_zero_of_binaryDiscriminant_ne_zero hV h₀)).toEquiv]
  exact key _ _ (hs.trans (sq s).symm)

end TauCeti.IntegralLattice
