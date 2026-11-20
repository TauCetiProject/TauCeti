/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.StiefelFibration.Unitary

/-!
# The special unitary Stiefel fibration `SU(m) → SU(r + m) → V_r(ℂ^(r + m))`

Applying a special unitary matrix to the standard frame `(e₀, …, e_{r-1})` gives the map
`SU(r + m) → V_r(ℂ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, to the orthonormal `r`-frames
(`TauCeti.specialUnitaryFrameMap`): it reads off the first `r` columns of `A`. Its fibre over the
standard frame is the block subgroup `diag(1_r, SU(m))`, the image of
`Matrix.SpecialUnitaryGroup.fromBlocksOne ℂ r m`, and its fibres are the left cosets of that
subgroup. For `m ≥ 1` the map is surjective and a locally trivial bundle with fibre `SU(m)`, and
hence a Serre fibration. For `r = 1`, where frames are unit vectors, this is the bundle
`SU(n) → SU(1 + n) → S^(2n+1)` of `TauCeti.Topology.Grassmannian.SphereBundle.SpecialUnitary`, and
for `n = 2` the bundle `SU(2) → SU(3) → S⁵` through which the homology of `SU(3)` is computed
from that of its fibre and base.

The charts come from the Gram–Schmidt local section of the unitary Stiefel fibration
(`TauCeti.exists_unitaryFrameMap_localSection`), corrected to determinant `1`. A unitary matrix
`A` has a determinant of modulus `1`, and multiplying the column of `A` with index `r`, the first
column not used by the standard frame, by `conj (det A)` gives a special unitary matrix with the
same first `r` columns. This correction depends continuously on `A` and is trivial for `A = 1`, so
it turns the unitary section into a continuous local section of the special unitary frame map,
equal to `1` at the standard frame (`TauCeti.exists_specialUnitaryFrameMap_localSection`).
Translating it by `SU(r + m)` gives one near every frame, and such a section defines a chart with
fibre the stabilizer of the standard frame (`Subgroup.localSectionTrivializationOfCosetFibers`),
which is `SU(m)`. Over `ℝ` the special unitary group is the special orthogonal group, and the
corresponding fibration is `TauCeti.Topology.Grassmannian.StiefelFibration.Basic`.

## Main definitions

* `TauCeti.specialUnitaryFrameMap`: the map `SU(r + m) → V_r(ℂ^(r + m))`,
  `A ↦ (A e₀, …, A e_{r-1})`.
* `TauCeti.specialUnitaryFrameFiberHomeomorph`: `SU(m)` is homeomorphic to the fibre of this map
  over the standard frame, through `B ↦ diag(1_r, B)`.

## Main results

* `TauCeti.specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff`: the fibres are the left cosets
  of the block subgroup `diag(1_r, SU(m))`.
* `TauCeti.specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff`: the fibre over the standard
  frame is the image of `SU(m)`.
* `TauCeti.surjective_specialUnitaryFrameMap`: for `m ≥ 1`, every orthonormal `r`-frame consists of
  the first `r` columns of a special unitary matrix.
* `TauCeti.exists_specialUnitaryFrameMap_localSection`: a continuous section of the frame map near
  the standard frame, taking the value `1` there.
* `TauCeti.exists_trivialization_specialUnitaryFrameMap`: a chart with fibre `SU(m)` around each
  frame.
* `TauCeti.specialUnitaryFrameMap_mem_serreFibrations`: `SU(r + m) → V_r(ℂ^(r + m))` is a Serre
  fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (Stiefel manifolds and
  the fibrations `SU(n - 1) → SU(n) → S^(2n-1)`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

open InnerProductSpace Matrix Set Topology

noncomputable section

namespace TauCeti

open finiteOrthonormalFrame

variable {r m : ℕ}

/-! ### The frame map `SU(r + m) → V_r(ℂ^(r + m))` -/

variable (r m) in
/-- The special unitary Stiefel map `SU(r + m) → V_r(ℂ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`,
sending a special unitary matrix to its first `r` columns. -/
def specialUnitaryFrameMap (A : specialUnitaryGroup (Fin (r + m)) ℂ) :
    finiteOrthonormalFrame ℂ r (r + m) :=
  unitaryFrameMap r m ⟨A.1, A.2.1⟩

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
  (continuous_unitaryFrameMap ℂ r m).comp (continuous_subtype_val.subtype_mk _)

/-- The frame map is equivariant: `(A B) • e = A • (B • e)`. -/
theorem specialUnitaryFrameMap_mul (A B : specialUnitaryGroup (Fin (r + m)) ℂ) :
    specialUnitaryFrameMap r m (A * B) =
      unitaryMap ⟨A.1, A.2.1⟩ (specialUnitaryFrameMap r m B) :=
  unitaryFrameMap_mul ⟨A.1, A.2.1⟩ ⟨B.1, B.2.1⟩

/-- The frame map of the identity is the standard frame. -/
@[simp]
theorem specialUnitaryFrameMap_one :
    specialUnitaryFrameMap r m 1 = standard ℂ (Nat.le_add_right r m) :=
  unitaryFrameMap_one

/-- The fibre of the frame map over the standard frame is the block subgroup
`diag(1_r, SU(m))`. -/
theorem specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff
    {A : specialUnitaryGroup (Fin (r + m)) ℂ} :
    specialUnitaryFrameMap r m A = specialUnitaryFrameMap r m 1 ↔
      A ∈ (SpecialUnitaryGroup.fromBlocksOne ℂ r m).range := by
  rw [SpecialUnitaryGroup.mem_range_fromBlocksOne_iff,
    ← UnitaryGroup.mem_range_fromBlocksOne_iff (A := ⟨A.1, A.2.1⟩)]
  exact unitaryFrameMap_eq_unitaryFrameMap_one_iff

/-- The fibres of the frame map are the left cosets of the block subgroup `diag(1_r, SU(m))`. -/
theorem specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff
    {A B : specialUnitaryGroup (Fin (r + m)) ℂ} :
    specialUnitaryFrameMap r m A = specialUnitaryFrameMap r m B ↔
      A⁻¹ * B ∈ (SpecialUnitaryGroup.fromBlocksOne ℂ r m).range := by
  rw [← specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff]
  constructor
  · intro h
    rw [specialUnitaryFrameMap_mul, ← h, ← specialUnitaryFrameMap_mul, inv_mul_cancel]
  · intro h
    rw [← mul_inv_cancel_left A B, specialUnitaryFrameMap_mul A, h,
      ← specialUnitaryFrameMap_mul, mul_one]

/-! ### The fibre over the standard frame -/

variable (r m) in
/-- The block embedding `B ↦ diag(1_r, B)` is a homeomorphism of `SU(m)` onto its image. -/
private def specialUnitaryBlockHomeomorph :
    specialUnitaryGroup (Fin m) ℂ ≃ₜ (SpecialUnitaryGroup.fromBlocksOne ℂ r m).range :=
  ((SpecialUnitaryGroup.continuous_fromBlocksOne m).rangeFactorization.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective _ (SpecialUnitaryGroup.fromBlocksOne_injective ℂ r))).trans
    (Homeomorph.setCongr (MonoidHom.coe_range _).symm)

variable (r m) in
/-- The fibre of the frame map over the standard frame is `SU(m)`: the block embedding
`B ↦ diag(1_r, B)` is a homeomorphism of `SU(m)` onto the special unitary matrices fixing the
standard frame. -/
def specialUnitaryFrameFiberHomeomorph :
    specialUnitaryGroup (Fin m) ℂ ≃ₜ
      specialUnitaryFrameMap r m ⁻¹' {specialUnitaryFrameMap r m 1} :=
  (specialUnitaryBlockHomeomorph r m).trans
    (Homeomorph.setCongr <| by
      ext A
      rw [SetLike.mem_coe, mem_preimage, mem_singleton_iff,
        specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff])

@[simp]
theorem coe_specialUnitaryFrameFiberHomeomorph_apply (B : specialUnitaryGroup (Fin m) ℂ) :
    (specialUnitaryFrameFiberHomeomorph r m B : specialUnitaryGroup (Fin (r + m)) ℂ) =
      SpecialUnitaryGroup.fromBlocksOne ℂ r m B :=
  (rfl)

/-- A special unitary matrix fixing the standard frame is the block matrix `diag(1_r, B)` of its
image `B` in `SU(m)`. -/
@[simp]
theorem fromBlocksOne_specialUnitaryFrameFiberHomeomorph_symm_apply
    (A : specialUnitaryFrameMap r m ⁻¹' {specialUnitaryFrameMap r m 1}) :
    SpecialUnitaryGroup.fromBlocksOne ℂ r m ((specialUnitaryFrameFiberHomeomorph r m).symm A) =
      A := by
  rw [← coe_specialUnitaryFrameFiberHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- The identity of `SU(m)` corresponds to the identity of `SU(r + m)` in the fibre. -/
@[simp]
theorem specialUnitaryFrameFiberHomeomorph_one :
    specialUnitaryFrameFiberHomeomorph r m 1 = ⟨1, rfl⟩ :=
  Subtype.ext (by simp)

/-! ### Correcting the determinant -/

section DetCorrection

variable [NeZero m]

/-- The coordinate whose column is rescaled to correct the determinant: the first of the last `m`
coordinates, which no vector of the standard `r`-frame involves. -/
private def detCorrectionIndex : Fin (r + m) :=
  Fin.natAdd r ⟨0, Nat.pos_of_neZero m⟩

/-- The diagonal unitary matrix multiplying the coordinate `detCorrectionIndex` by a unit
complex number `c`. -/
private def detCorrectionDiag {c : ℂ} (hc : c ∈ unitary ℂ) : unitaryGroup (Fin (r + m)) ℂ :=
  ⟨diagonal (Function.update 1 detCorrectionIndex c), diagonal_mem_unitary.2 <|
    Pi.mem_unitary_iff.2 fun k ↦ by
      rcases eq_or_ne k detCorrectionIndex with rfl | hk
      · simpa using hc
      · simp [hk]⟩

/-- The diagonal correction fixes the standard frame, whose vectors avoid the rescaled
coordinate. -/
private theorem unitaryFrameMap_detCorrectionDiag {c : ℂ} (hc : c ∈ unitary ℂ) :
    unitaryFrameMap r m (detCorrectionDiag hc) = unitaryFrameMap r m 1 := by
  refine Subtype.ext <| funext fun i ↦ ?_
  have hi : Fin.castAdd m i ≠ detCorrectionIndex := fun h ↦ by
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, detCorrectionIndex, Fin.val_natAdd] at this
    omega
  ext j
  simp [detCorrectionDiag, hi, -unitaryFrameMap_one, Matrix.one_apply, Pi.single_apply]

/-- The **determinant correction** of a unitary matrix `A`: the column of `A` with index `r` is
multiplied by `conj (det A)`, giving a special unitary matrix with the same first `r` columns. -/
private def detCorrection (A : unitaryGroup (Fin (r + m)) ℂ) :
    specialUnitaryGroup (Fin (r + m)) ℂ :=
  ⟨(A * detCorrectionDiag (Unitary.star_mem (det_of_mem_unitary A.2))).1,
    (A * detCorrectionDiag (Unitary.star_mem (det_of_mem_unitary A.2))).2, by
      simpa [detCorrectionDiag, det_diagonal, Finset.prod_update_of_mem] using
        Unitary.mul_star_self_of_mem (det_of_mem_unitary A.2)⟩

private theorem specialUnitaryFrameMap_detCorrection (A : unitaryGroup (Fin (r + m)) ℂ) :
    specialUnitaryFrameMap r m (detCorrection A) = unitaryFrameMap r m A :=
  (unitaryFrameMap_mul A _).trans <| by
    rw [unitaryFrameMap_detCorrectionDiag, ← unitaryFrameMap_mul, mul_one]

private theorem detCorrection_one : detCorrection (1 : unitaryGroup (Fin (r + m)) ℂ) = 1 :=
  Subtype.ext <| by
    simp [detCorrection, detCorrectionDiag]

private theorem continuous_detCorrection : Continuous (detCorrection (r := r) (m := m)) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, detCorrection, detCorrectionDiag, Submonoid.coe_mul]
  exact continuous_subtype_val.mul (Continuous.matrix_diagonal (continuous_const.update _
    (continuous_star.comp continuous_subtype_val.matrix_det)))

end DetCorrection

/-- For `m ≥ 1`, every orthonormal `r`-frame of `ℂ^(r + m)` consists of the first `r` columns of a
special unitary matrix. -/
theorem surjective_specialUnitaryFrameMap [NeZero m] :
    Function.Surjective (specialUnitaryFrameMap r m) := fun f ↦ by
  obtain ⟨A, rfl⟩ := surjective_unitaryFrameMap (𝕜 := ℂ) (r := r) (m := m) f
  exact ⟨detCorrection A, specialUnitaryFrameMap_detCorrection A⟩

/-! ### Local sections and local triviality -/

/-- **Local section of the special unitary Stiefel map**: for `m ≥ 1`, near the standard frame
there is a continuous map `s` to `SU(r + m)` with `s f` carrying the standard frame to `f`, and
`s e = 1` at the standard frame `e`. It is the Gram–Schmidt section of the unitary Stiefel map
with the column of index `r` multiplied by the conjugate of its determinant. -/
theorem exists_specialUnitaryFrameMap_localSection [NeZero m] :
    ∃ U : Set (finiteOrthonormalFrame ℂ r (r + m)), IsOpen U ∧
      standard ℂ (Nat.le_add_right r m) ∈ U ∧
      ∃ s : finiteOrthonormalFrame ℂ r (r + m) → specialUnitaryGroup (Fin (r + m)) ℂ,
        ContinuousOn s U ∧ s (standard ℂ (Nat.le_add_right r m)) = 1 ∧
          ∀ f ∈ U, specialUnitaryFrameMap r m (s f) = f := by
  obtain ⟨U, hU, hstd, s, hs, hs1, hsec⟩ := exists_unitaryFrameMap_localSection (𝕜 := ℂ) (r := r)
    (m := m)
  exact ⟨U, hU, hstd, detCorrection ∘ s, continuous_detCorrection.comp_continuousOn hs,
    by rw [Function.comp_apply, hs1, detCorrection_one],
    fun f hf ↦ (specialUnitaryFrameMap_detCorrection _).trans (hsec f hf)⟩

/-- For `m ≥ 1`, the frame map `SU(r + m) → V_r(ℂ^(r + m))` has a continuous local section on an
open neighbourhood of each frame. -/
theorem exists_mem_specialUnitaryFrameMap_localSection [NeZero m]
    (b : finiteOrthonormalFrame ℂ r (r + m)) :
    ∃ U : Set (finiteOrthonormalFrame ℂ r (r + m)), IsOpen U ∧ b ∈ U ∧
      ∃ s : finiteOrthonormalFrame ℂ r (r + m) → specialUnitaryGroup (Fin (r + m)) ℂ,
        ContinuousOn s U ∧ ∀ f ∈ U, specialUnitaryFrameMap r m (s f) = f := by
  -- `g` carries the standard frame to `b`; translating the section near the standard frame by
  -- `g` gives a section near `b`.
  obtain ⟨g, rfl⟩ := surjective_specialUnitaryFrameMap (r := r) (m := m) b
  obtain ⟨U, hU, hstd, s, hs, -, hsec⟩ := exists_specialUnitaryFrameMap_localSection (r := r)
    (m := m)
  let t : finiteOrthonormalFrame ℂ r (r + m) → finiteOrthonormalFrame ℂ r (r + m) :=
    unitaryMap ⟨(g⁻¹ : specialUnitaryGroup (Fin (r + m)) ℂ).1, (g⁻¹).2.1⟩
  have ht : Continuous t := continuous_unitaryMap.comp (continuous_const.prodMk continuous_id)
  have hgt (f : finiteOrthonormalFrame ℂ r (r + m)) : unitaryMap ⟨g.1, g.2.1⟩ (t f) = f := by
    have h1 : (⟨g.1, g.2.1⟩ : unitaryGroup (Fin (r + m)) ℂ) * ⟨(g⁻¹).1, (g⁻¹).2.1⟩ = 1 :=
      Subtype.ext ((Submonoid.coe_mul _ g g⁻¹).symm.trans
        (by rw [mul_inv_cancel, OneMemClass.coe_one]; rfl))
    rw [← unitaryMap_mul, h1, unitaryMap_one]
  refine ⟨t ⁻¹' U, hU.preimage ht, ?_, fun f ↦ g * s (t f),
    continuousOn_const.mul (hs.comp ht.continuousOn fun _ hf ↦ hf),
    fun f hf ↦ by rw [specialUnitaryFrameMap_mul, hsec _ hf, hgt]⟩
  simp only [mem_preimage, t, ← specialUnitaryFrameMap_mul, inv_mul_cancel,
    specialUnitaryFrameMap_one]
  exact hstd

/-- For `m ≥ 1`, the frame map `SU(r + m) → V_r(ℂ^(r + m))` has a chart with fibre `SU(m)` around
each orthonormal frame. -/
theorem exists_trivialization_specialUnitaryFrameMap [NeZero m]
    (b : finiteOrthonormalFrame ℂ r (r + m)) :
    ∃ e : Bundle.Trivialization (specialUnitaryGroup (Fin m) ℂ) (specialUnitaryFrameMap r m),
      b ∈ e.baseSet := by
  obtain ⟨U, hU, hb, s, hs, hsec⟩ := exists_mem_specialUnitaryFrameMap_localSection b
  let e := Subgroup.localSectionTrivializationOfCosetFibers
    (SpecialUnitaryGroup.fromBlocksOne ℂ r m).range (continuous_specialUnitaryFrameMap r m)
    (fun _ _ ↦ specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff) U hU s hs hsec
  refine ⟨e.transFiberHomeomorph (specialUnitaryBlockHomeomorph r m).symm, ?_⟩
  simpa only [Bundle.Trivialization.transFiberHomeomorph, e,
    Subgroup.localSectionTrivializationOfCosetFibers_baseSet] using hb

/-- For `m ≥ 1`, the frame map `SU(r + m) → V_r(ℂ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, is a Serre
fibration: it is locally trivial with fibre `SU(m)`. -/
theorem specialUnitaryFrameMap_mem_serreFibrations [NeZero m] :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨specialUnitaryFrameMap r m, continuous_specialUnitaryFrameMap r m⟩ :
        _root_.TopCat.of (specialUnitaryGroup (Fin (r + m)) ℂ) ⟶
          _root_.TopCat.of (finiteOrthonormalFrame ℂ r (r + m))) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (F := specialUnitaryGroup (Fin m) ℂ) exists_trivialization_specialUnitaryFrameMap

end TauCeti
