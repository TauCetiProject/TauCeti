/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.Topology.Grassmannian.StiefelFibration.Unitary

/-!
# The Stiefel fibration `SU(m) → SU(r + m) → V_r(ℂ^(r + m))`

Applying a special unitary matrix to the standard frame `(e₀, …, e_{r-1})` gives the map
`SU(r + m) → V_r(ℂ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, to the orthonormal `r`-frames
(`TauCeti.specialUnitaryFrameMap`): it reads off the first `r` columns of `A`. It is the
restriction of the unitary Stiefel map `TauCeti.unitaryFrameMap` to `SU(r + m)`. Its fibres are
the left cosets of the stabilizer of the standard frame
(`TauCeti.specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff`), and the block embedding
`B ↦ diag(1_r, B)` (`Matrix.specialUnitaryGroup.fromBlocksOne`) identifies `SU(m)` with that
stabilizer (`TauCeti.specialUnitaryStabilizerHomeomorph`). For `m ≥ 1` the map is surjective and a
locally trivial bundle with fibre `SU(m)`, and hence a Serre fibration. For `r = 1` and `m = 2` this
is the bundle `SU(2) → SU(3) → S⁵` with projection `A ↦ A e₀` onto the unit vectors of `ℂ³`.

The determinant is what separates `SU(r + m)` from `U(r + m)`, and for `m ≥ 1` it can be corrected
without moving the frame. Multiplying a unitary matrix `A` on the right by the block matrix
`diag(1_r, diag(det A⁻¹, 1, …, 1))`, which fixes the standard frame, gives a special unitary matrix
with the same first `r` columns. Applied to the Gram–Schmidt section of the unitary Stiefel map
(`TauCeti.exists_unitaryFrameMap_localSection`), this correction gives a continuous section of the
special unitary map near the standard frame, equal to `1` there
(`TauCeti.exists_specialUnitaryFrameMap_localSection`). Translating it by `SU(r + m)` gives one near
every frame, and such a section defines a chart with fibre the stabilizer of the standard frame
(`Subgroup.localSectionTrivializationOfCosetFibers`), which is `SU(m)`.

Over `ℝ` the special unitary group is the special orthogonal group, and the real fibration
`SO(m) → SO(r + m) → V_r(ℝ^(r + m))` is `TauCeti.Topology.Grassmannian.StiefelFibration.Basic`.
There a real orthogonal matrix near the identity already has determinant `1`, whereas over `ℂ` the
determinant ranges over the circle and has to be corrected.

## Main definitions

* `TauCeti.specialUnitaryFrameMap`: the map `SU(r + m) → V_r(ℂ^(r + m))`,
  `A ↦ (A e₀, …, A e_{r-1})`.
* `TauCeti.specialUnitaryStabilizer`: the stabilizer of the standard frame in `SU(r + m)`.
* `TauCeti.specialUnitaryStabilizerHomeomorph`: `SU(m)` is homeomorphic to this stabilizer, through
  `B ↦ diag(1_r, B)`.

## Main results

* `TauCeti.specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff`: the fibres are the left cosets of
  the stabilizer of the standard frame.
* `TauCeti.surjective_specialUnitaryFrameMap`: for `m ≥ 1` every orthonormal `r`-frame of
  `ℂ^(r + m)` consists of the first `r` columns of a special unitary matrix.
* `TauCeti.exists_specialUnitaryFrameMap_localSection`: a continuous section of the frame map near
  the standard frame, taking the value `1` there.
* `TauCeti.exists_trivialization_specialUnitaryFrameMap`: a chart with fibre `SU(m)` around each
  frame.
* `TauCeti.specialUnitaryFrameMap_mem_serreFibrations`: `SU(r + m) → V_r(ℂ^(r + m))` is a Serre
  fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (Stiefel manifolds and
  the fibrations `SU(n - k) → SU(n) → V_k(ℂⁿ)`, in particular `SU(n - 1) → SU(n) → S^(2n - 1)`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

open Matrix Set Topology

noncomputable section

namespace TauCeti

open finiteOrthonormalFrame

variable {r m : ℕ}

/-! ### The frame map `SU(r + m) → V_r(ℂ^(r + m))` -/

variable (r m) in
/-- The special unitary Stiefel map `SU(r + m) → V_r(ℂ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`,
sending a special unitary matrix to its first `r` columns. It is the unitary Stiefel map
`TauCeti.unitaryFrameMap` on the special unitary matrices. -/
def specialUnitaryFrameMap (A : specialUnitaryGroup (Fin (r + m)) ℂ) :
    finiteOrthonormalFrame ℂ r (r + m) :=
  unitaryFrameMap r m (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A)

/-- In coordinates, the `i`-th vector of `specialUnitaryFrameMap r m A` is the column `A e_i` of
`A`. -/
@[simp]
theorem coe_specialUnitaryFrameMap (A : specialUnitaryGroup (Fin (r + m)) ℂ) :
    (specialUnitaryFrameMap r m A : Fin r → Fin (r + m) → ℂ) =
      fun i ↦ (A : Matrix (Fin (r + m)) (Fin (r + m)) ℂ) *ᵥ Pi.single (Fin.castAdd m i) 1 :=
  coe_unitaryFrameMap _

variable (r m) in
/-- The frame map `SU(r + m) → V_r(ℂ^(r + m))` is continuous. -/
@[fun_prop]
theorem continuous_specialUnitaryFrameMap : Continuous (specialUnitaryFrameMap r m) :=
  (continuous_unitaryFrameMap ℂ r m).comp (continuous_subtypeVal.subtype_mk _)

/-- The frame map is equivariant: `(A B) • e = A • (B • e)`. -/
theorem specialUnitaryFrameMap_mul (A B : specialUnitaryGroup (Fin (r + m)) ℂ) :
    specialUnitaryFrameMap r m (A * B) =
      unitaryMap (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A)
        (specialUnitaryFrameMap r m B) := by
  rw [specialUnitaryFrameMap, specialUnitaryFrameMap, map_mul, unitaryFrameMap_mul]

/-- The frame map of the identity is the standard frame. -/
@[simp]
theorem specialUnitaryFrameMap_one :
    specialUnitaryFrameMap r m 1 = standard ℂ (Nat.le_add_right r m) := by
  rw [specialUnitaryFrameMap, map_one, unitaryFrameMap_one]

/-! ### The stabilizer of the standard frame -/

variable (r m) in
/-- The **stabilizer of the standard frame** `(e₀, …, e_{r-1})` in `SU(r + m)`: the special unitary
matrices whose image in `U(r + m)` lies in the stabilizer of the standard frame,
`TauCeti.finiteOrthonormalFrame.unitaryStabilizer`. -/
def specialUnitaryStabilizer : Subgroup (specialUnitaryGroup (Fin (r + m)) ℂ) :=
  (unitaryStabilizer ℂ (Nat.le_add_right r m)).comap
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

/-- The fibres of the frame map are the left cosets of the stabilizer of the standard frame. -/
theorem specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff
    {A B : specialUnitaryGroup (Fin (r + m)) ℂ} :
    specialUnitaryFrameMap r m A = specialUnitaryFrameMap r m B ↔
      A⁻¹ * B ∈ specialUnitaryStabilizer r m := by
  rw [specialUnitaryFrameMap, specialUnitaryFrameMap, unitaryFrameMap_eq_unitaryFrameMap_iff,
    specialUnitaryStabilizer, Subgroup.mem_comap, map_mul, map_inv]

/-- A special unitary matrix lies in the stabilizer exactly when it fixes the standard frame. -/
theorem mem_specialUnitaryStabilizer_iff {A : specialUnitaryGroup (Fin (r + m)) ℂ} :
    A ∈ specialUnitaryStabilizer r m ↔
      specialUnitaryFrameMap r m A = standard ℂ (Nat.le_add_right r m) := by
  rw [← specialUnitaryFrameMap_one, eq_comm, specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff,
    inv_one, one_mul]

/-- A special unitary matrix lies in the stabilizer of the standard frame exactly when it is a
block matrix `diag(1_r, B)` with `B ∈ SU(m)`. A unitary block `B` for which `diag(1_r, B)` is
special unitary has determinant `1`, since it has the determinant of `diag(1_r, B)`. -/
theorem mem_specialUnitaryStabilizer_iff_exists {A : specialUnitaryGroup (Fin (r + m)) ℂ} :
    A ∈ specialUnitaryStabilizer r m ↔
      ∃ B : specialUnitaryGroup (Fin m) ℂ, specialUnitaryGroup.fromBlocksOne ℂ r m B = A := by
  rw [specialUnitaryStabilizer, Subgroup.mem_comap, ← range_fromBlocksOne_eq_unitaryStabilizer]
  constructor
  · rintro ⟨B, hB⟩
    have hdet : (B : Matrix (Fin m) (Fin m) ℂ).det = 1 := by
      rw [← UnitaryGroup.det_fromBlocksOne ℂ r B, hB]
      exact (mem_specialUnitaryGroup_iff.1 A.property).2
    exact ⟨⟨B, mem_specialUnitaryGroup_iff.2 ⟨B.property, hdet⟩⟩,
      Subtype.ext ((specialUnitaryGroup.coe_fromBlocksOne ℂ r _).trans (Subtype.ext_iff.1 hB))⟩
  · rintro ⟨B, rfl⟩
    exact ⟨_, Subtype.ext (specialUnitaryGroup.coe_fromBlocksOne ℂ r B).symm⟩

variable (r m) in
/-- The block embedding `B ↦ diag(1_r, B)` is a homeomorphism of `SU(m)` onto the stabilizer of the
standard `r`-frame in `SU(r + m)`. -/
def specialUnitaryStabilizerHomeomorph :
    specialUnitaryGroup (Fin m) ℂ ≃ₜ specialUnitaryStabilizer r m :=
  ((specialUnitaryGroup.continuous_fromBlocksOne m).rangeFactorization.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective _ (specialUnitaryGroup.fromBlocksOne_injective ℂ r))).trans
    (Homeomorph.setCongr <| by
      ext A
      exact mem_specialUnitaryStabilizer_iff_exists.symm)

@[simp]
theorem coe_specialUnitaryStabilizerHomeomorph_apply (B : specialUnitaryGroup (Fin m) ℂ) :
    (specialUnitaryStabilizerHomeomorph r m B : specialUnitaryGroup (Fin (r + m)) ℂ) =
      specialUnitaryGroup.fromBlocksOne ℂ r m B :=
  (rfl)

/-- Embedding the preimage of a stabilizer element in `SU(m)` recovers that element. -/
@[simp]
theorem fromBlocksOne_specialUnitaryStabilizerHomeomorph_symm_apply
    (A : specialUnitaryStabilizer r m) :
    specialUnitaryGroup.fromBlocksOne ℂ r m ((specialUnitaryStabilizerHomeomorph r m).symm A) =
      A := by
  rw [← coe_specialUnitaryStabilizerHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- The identity of `SU(m)` corresponds to the identity of the stabilizer. -/
@[simp]
theorem specialUnitaryStabilizerHomeomorph_one : specialUnitaryStabilizerHomeomorph r m 1 = 1 :=
  Subtype.ext (by simp)

/-! ### Correcting the determinant -/

/-- The diagonal unitary matrix `diag(1_r, diag(det A⁻¹, 1, …, 1))`. It fixes the standard frame,
and multiplying `A` by it on the right gives a special unitary matrix. -/
private def detCorrection [NeZero m] (A : unitaryGroup (Fin (r + m)) ℂ) :
    unitaryGroup (Fin (r + m)) ℂ :=
  UnitaryGroup.fromBlocksOne ℂ r m
    (unitaryTorusHom (Fin m) (Pi.mulSingle 0 (Matrix.UnitaryGroup.detCircle A)⁻¹))

private theorem continuous_detCorrection [NeZero m] :
    Continuous (detCorrection (r := r) (m := m)) :=
  (UnitaryGroup.continuous_fromBlocksOne m).comp <| continuous_unitaryTorusHom.comp <|
    continuous_pi fun k ↦ by
      rcases eq_or_ne k 0 with rfl | hk
      · simpa using Matrix.UnitaryGroup.continuous_detCircle.inv
      · simpa [hk] using continuous_const

private theorem detCorrection_one [NeZero m] :
    detCorrection (r := r) (m := m) 1 = 1 := by
  simp [detCorrection]

/-- The correction has the inverse determinant: `det (detCorrection A) = (det A)⁻¹`. -/
private theorem det_detCorrection [NeZero m] (A : unitaryGroup (Fin (r + m)) ℂ) :
    (detCorrection A : Matrix (Fin (r + m)) (Fin (r + m)) ℂ).det =
      (A : Matrix (Fin (r + m)) (Fin (r + m)) ℂ).det⁻¹ := by
  -- The only diagonal entry different from `1` is the one at `0`.
  rw [detCorrection, UnitaryGroup.det_fromBlocksOne, coe_unitaryTorusHom, det_diagonal,
    Fintype.prod_eq_single 0 fun k hk ↦ by simp [hk]]
  simp

private theorem det_mul_detCorrection [NeZero m] (A : unitaryGroup (Fin (r + m)) ℂ) :
    ((A * detCorrection A : unitaryGroup (Fin (r + m)) ℂ) :
      Matrix (Fin (r + m)) (Fin (r + m)) ℂ).det = 1 := by
  rw [Submonoid.coe_mul, det_mul, det_detCorrection]
  exact mul_inv_cancel₀ (by simpa using (Matrix.UnitaryGroup.detCircle A).coe_ne_zero)

private theorem unitaryFrameMap_mul_detCorrection [NeZero m] (A : unitaryGroup (Fin (r + m)) ℂ) :
    unitaryFrameMap r m (A * detCorrection A) = unitaryFrameMap r m A := by
  have h : unitaryFrameMap r m (detCorrection A) = unitaryFrameMap r m 1 :=
    unitaryFrameMap_eq_unitaryFrameMap_one_iff.2 ⟨_, rfl⟩
  rw [unitaryFrameMap_mul, h, ← unitaryFrameMap_mul, mul_one]

/-- The special unitary matrix `A diag(1_r, diag(det A⁻¹, 1, …, 1))`, with the same first `r`
columns as the unitary matrix `A`. -/
private def toSpecialUnitary [NeZero m] (A : unitaryGroup (Fin (r + m)) ℂ) :
    specialUnitaryGroup (Fin (r + m)) ℂ :=
  ⟨(A * detCorrection A : unitaryGroup (Fin (r + m)) ℂ),
    mem_specialUnitaryGroup_iff.2 ⟨(A * detCorrection A).property, det_mul_detCorrection A⟩⟩

private theorem continuous_toSpecialUnitary [NeZero m] :
    Continuous (toSpecialUnitary (r := r) (m := m)) := by
  have h : Continuous fun A : unitaryGroup (Fin (r + m)) ℂ ↦
      ((A * detCorrection A : unitaryGroup (Fin (r + m)) ℂ) :
        Matrix (Fin (r + m)) (Fin (r + m)) ℂ) :=
    continuous_subtypeVal.comp (continuous_id.mul continuous_detCorrection)
  exact h.subtype_mk _

private theorem toSpecialUnitary_one [NeZero m] :
    toSpecialUnitary (r := r) (m := m) 1 = 1 :=
  Subtype.ext (by simp [toSpecialUnitary, detCorrection_one])

private theorem specialUnitaryFrameMap_toSpecialUnitary [NeZero m]
    (A : unitaryGroup (Fin (r + m)) ℂ) :
    specialUnitaryFrameMap r m (toSpecialUnitary A) = unitaryFrameMap r m A := by
  -- Both sides have the underlying matrix `A * detCorrection A`, by definition of
  -- `toSpecialUnitary`.
  have h : Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup (toSpecialUnitary A) =
      A * detCorrection A :=
    Subtype.ext (rfl)
  rw [specialUnitaryFrameMap, h, unitaryFrameMap_mul_detCorrection]

/-- For `m ≥ 1`, every orthonormal `r`-frame of `ℂ^(r + m)` consists of the first `r` columns of a
special unitary matrix. -/
theorem surjective_specialUnitaryFrameMap [NeZero m] :
    Function.Surjective (specialUnitaryFrameMap r m) := fun f ↦ by
  obtain ⟨A, rfl⟩ := surjective_unitaryFrameMap (𝕜 := ℂ) (r := r) (m := m) f
  exact ⟨toSpecialUnitary A, specialUnitaryFrameMap_toSpecialUnitary A⟩

/-! ### Local triviality -/

/-- **A local section of the special unitary Stiefel map.** For `m ≥ 1`, near the standard frame
there is a continuous map `s` to `SU(r + m)` with `s f` carrying the standard frame to `f`, and
`s e = 1` at the standard frame `e`. It is the Gram–Schmidt section of the unitary Stiefel map
(`TauCeti.exists_unitaryFrameMap_localSection`), with its determinant corrected in the coordinate
`e_r`, which is not part of the frame. -/
theorem exists_specialUnitaryFrameMap_localSection [NeZero m] :
    ∃ U : Set (finiteOrthonormalFrame ℂ r (r + m)), IsOpen U ∧
      standard ℂ (Nat.le_add_right r m) ∈ U ∧
      ∃ s : finiteOrthonormalFrame ℂ r (r + m) → specialUnitaryGroup (Fin (r + m)) ℂ,
        ContinuousOn s U ∧ s (standard ℂ (Nat.le_add_right r m)) = 1 ∧
          ∀ f ∈ U, specialUnitaryFrameMap r m (s f) = f := by
  obtain ⟨U, hU, hstd, s, hs, hs1, hsec⟩ := exists_unitaryFrameMap_localSection (𝕜 := ℂ) (r := r)
    (m := m)
  refine ⟨U, hU, hstd, fun f ↦ toSpecialUnitary (s f),
    continuous_toSpecialUnitary.comp_continuousOn hs,
    (congrArg toSpecialUnitary hs1).trans toSpecialUnitary_one,
    fun f hf ↦ ?_⟩
  rw [specialUnitaryFrameMap_toSpecialUnitary, hsec f hf]

/-- For `m ≥ 1`, the frame map `SU(r + m) → V_r(ℂ^(r + m))` has a chart with fibre `SU(m)` around
each orthonormal frame. -/
theorem exists_trivialization_specialUnitaryFrameMap [NeZero m]
    (b : finiteOrthonormalFrame ℂ r (r + m)) :
    ∃ e : Bundle.Trivialization (specialUnitaryGroup (Fin m) ℂ) (specialUnitaryFrameMap r m),
      b ∈ e.baseSet := by
  -- `g` carries the standard frame to `b`; translating the local section by `g` gives a section
  -- near `b`.
  obtain ⟨g, rfl⟩ := surjective_specialUnitaryFrameMap (r := r) (m := m) b
  let t : finiteOrthonormalFrame ℂ r (r + m) → finiteOrthonormalFrame ℂ r (r + m) :=
    unitaryMap (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup g⁻¹)
  have ht : Continuous t := continuous_unitaryMap.comp (continuous_const.prodMk continuous_id)
  have hgt (f : finiteOrthonormalFrame ℂ r (r + m)) :
      unitaryMap (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup g) (t f) = f := by
    rw [← unitaryMap_mul, ← map_mul, mul_inv_cancel, map_one, unitaryMap_one]
  obtain ⟨U, hU, hstd, s, hs, -, hsec⟩ := exists_specialUnitaryFrameMap_localSection (r := r)
    (m := m)
  let e := Subgroup.localSectionTrivializationOfCosetFibers (specialUnitaryStabilizer r m)
    (continuous_specialUnitaryFrameMap r m)
    (fun _ _ ↦ specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff) (t ⁻¹' U) (hU.preimage ht)
    (fun f ↦ g * s (t f)) (continuousOn_const.mul (hs.comp ht.continuousOn fun _ hf ↦ hf))
    fun f hf ↦ by rw [specialUnitaryFrameMap_mul, hsec _ hf, hgt]
  refine ⟨e.transFiberHomeomorph (specialUnitaryStabilizerHomeomorph r m).symm, ?_⟩
  simp only [Bundle.Trivialization.transFiberHomeomorph, e,
    Subgroup.localSectionTrivializationOfCosetFibers_baseSet, mem_preimage, t]
  rw [← specialUnitaryFrameMap_mul, inv_mul_cancel, specialUnitaryFrameMap_one]
  exact hstd

/-- For `m ≥ 1`, the frame map `SU(r + m) → V_r(ℂ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, is a
Serre fibration: it is locally trivial with fibre `SU(m)`. -/
theorem specialUnitaryFrameMap_mem_serreFibrations [NeZero m] :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨specialUnitaryFrameMap r m, continuous_specialUnitaryFrameMap r m⟩ :
        _root_.TopCat.of (specialUnitaryGroup (Fin (r + m)) ℂ) ⟶
          _root_.TopCat.of (finiteOrthonormalFrame ℂ r (r + m))) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (F := specialUnitaryGroup (Fin m) ℂ) exists_trivialization_specialUnitaryFrameMap

end TauCeti
