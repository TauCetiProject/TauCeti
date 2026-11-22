/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.StiefelFibration.Unitary
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# The special unitary Stiefel fibration `SU(m) → SU(r + m) → V_r(𝕜^(r + m))`

For `𝕜 = ℝ` or `ℂ` (any `RCLike 𝕜`), applying a special unitary matrix to the standard frame
`(e₀, …, e_{r-1})` gives the map `SU(r + m) → V_r(𝕜^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, to the
orthonormal `r`-frames (`TauCeti.specialUnitaryFrameMap`): it reads off the first `r` columns of
`A`. Its fibre over the standard frame is the block subgroup `diag(1_r, SU(m))`, the image of
`Matrix.specialUnitaryGroup.fromBlocksOne 𝕜 r m`, and its fibres are the left cosets of that
subgroup. For `m ≥ 1` the map is surjective and a locally trivial bundle with fibre `SU(m)`, and
hence a Serre fibration. Over `ℂ` and for `r = 1` this is the bundle `SU(n) → SU(n + 1) → S^(2n+1)`
of `TauCeti.Topology.Grassmannian.SphereBundle.SpecialUnitary`, for instance
`SU(2) → SU(3) → S⁵`. Over `ℝ` it is the special orthogonal Stiefel fibration
`SO(m) → SO(r + m) → V_r(ℝ^(r + m))` of `TauCeti.Topology.Grassmannian.StiefelFibration.Basic`,
whose statements are specializations of these.

The charts come from the local sections of the unitary Stiefel fibration
(`TauCeti.exists_unitaryFrameMap_localSection`), given by the Gram–Schmidt process. Such a section
takes values in `U(r + m)`; multiplying the last column of each of its values by the conjugate of
its determinant (`Matrix.UnitaryGroup.toSpecialUnitaryAt`) makes it special unitary without
changing the first `r` columns, because `m ≥ 1`, and keeps it continuous. Translating it by
`SU(r + m)` gives a section near every frame, and such a section defines a chart with fibre the
stabilizer of the standard frame (`Subgroup.localSectionTrivializationOfCosetFibers`), which is
`SU(m)`.

For `m = 0` the map is not surjective: `SU(r)` carries the standard frame only to the frames of
determinant `1`, as `TauCeti.finiteOrthonormalFrame.exists_specialUnitary_unitaryMap_eq_iff`
records.

## Main definitions

* `TauCeti.specialUnitaryFrameMap`: the map `SU(r + m) → V_r(𝕜^(r + m))`,
  `A ↦ (A e₀, …, A e_{r-1})`.
* `TauCeti.specialUnitaryFrameFiberHomeomorph`: `SU(m)` is homeomorphic to the fibre of this map
  over the standard frame, through `B ↦ diag(1_r, B)`.

## Main results

* `TauCeti.specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff`: the fibres are the left cosets of
  the stabilizer of the standard frame.
* `TauCeti.specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff`: the fibre over the standard
  frame is the image of `SU(m)`.
* `TauCeti.surjective_specialUnitaryFrameMap`: for `m ≥ 1` every orthonormal `r`-frame of
  `𝕜^(r + m)` consists of the first `r` columns of a special unitary matrix.
* `TauCeti.exists_specialUnitaryFrameMap_localSection`: a continuous section of the frame map near
  the standard frame, taking the value `1` there.
* `TauCeti.exists_trivialization_specialUnitaryFrameMap`: a chart with fibre `SU(m)` around each
  frame.
* `TauCeti.specialUnitaryFrameMap_mem_serreFibrations`: `SU(r + m) → V_r(𝕜^(r + m))` is a Serre
  fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (Stiefel manifolds and
  the fibrations `SU(n - k) → SU(n) → V_k(ℂⁿ)`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

open Matrix Set Topology

noncomputable section

namespace TauCeti

open finiteOrthonormalFrame

variable {𝕜 : Type*} [RCLike 𝕜] {r m : ℕ}

/-! ### The frame map `SU(r + m) → V_r(𝕜^(r + m))` -/

variable (r m) in
/-- The special unitary Stiefel map `SU(r + m) → V_r(𝕜^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`,
sending a special unitary matrix to its first `r` columns. -/
def specialUnitaryFrameMap (A : specialUnitaryGroup (Fin (r + m)) 𝕜) :
    finiteOrthonormalFrame 𝕜 r (r + m) :=
  unitaryMap ⟨A.val, A.property.1⟩ (standard 𝕜 (Nat.le_add_right r m))

/-- In coordinates, the `i`-th vector of `specialUnitaryFrameMap r m A` is the column `A e_i` of
`A`. -/
@[simp]
theorem coe_specialUnitaryFrameMap (A : specialUnitaryGroup (Fin (r + m)) 𝕜) :
    (specialUnitaryFrameMap r m A : Fin r → Fin (r + m) → 𝕜) =
      fun i ↦ (A : Matrix (Fin (r + m)) (Fin (r + m)) 𝕜) *ᵥ Pi.single (Fin.castAdd m i) 1 := by
  rw [specialUnitaryFrameMap, coe_unitaryMap, coe_standard]
  -- `Fin.castAdd m` is by definition `Fin.castLE` along `r ≤ r + m`, and there is no library lemma
  -- rewriting one into the other.
  rfl

variable (𝕜 r m) in
/-- The frame map `SU(r + m) → V_r(𝕜^(r + m))` is continuous. -/
@[fun_prop]
theorem continuous_specialUnitaryFrameMap : Continuous (specialUnitaryFrameMap (𝕜 := 𝕜) r m) :=
  continuous_unitaryMap.comp ((continuous_subtypeVal.subtype_mk _).prodMk continuous_const)

/-- The frame map is equivariant: `(A B) • e = A • (B • e)`. -/
theorem specialUnitaryFrameMap_mul (A B : specialUnitaryGroup (Fin (r + m)) 𝕜) :
    specialUnitaryFrameMap r m (A * B) =
      unitaryMap ⟨A.val, A.property.1⟩ (specialUnitaryFrameMap r m B) :=
  unitaryMap_mul ⟨A.val, A.property.1⟩ ⟨B.val, B.property.1⟩ _

/-- The frame map of the identity is the standard frame. -/
@[simp]
theorem specialUnitaryFrameMap_one :
    specialUnitaryFrameMap r m (1 : specialUnitaryGroup (Fin (r + m)) 𝕜) =
      standard 𝕜 (Nat.le_add_right r m) :=
  unitaryMap_one _

/-- The frame map is the orbit map `A ↦ A • e` of the standard frame `e` under
`specialUnitaryMulAction`. -/
theorem specialUnitaryFrameMap_eq_smul_standard (A : specialUnitaryGroup (Fin (r + m)) 𝕜) :
    letI := specialUnitaryMulAction 𝕜 r (r + m)
    specialUnitaryFrameMap r m A = A • standard 𝕜 (Nat.le_add_right r m) :=
  (specialUnitary_smul_def A _).symm

/-- The fibres of the frame map are the left cosets of the stabilizer of the standard frame. -/
theorem specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff
    {A B : specialUnitaryGroup (Fin (r + m)) 𝕜} :
    specialUnitaryFrameMap r m A = specialUnitaryFrameMap r m B ↔
      A⁻¹ * B ∈ specialUnitaryStabilizer 𝕜 (Nat.le_add_right r m) := by
  let := specialUnitaryMulAction 𝕜 r (r + m)
  simpa only [specialUnitaryFrameMap_eq_smul_standard,
    specialUnitaryStabilizer_eq_stabilizer] using
    smul_eq_smul_iff_inv_mul_mem_stabilizer (standard 𝕜 (Nat.le_add_right r m)) A B

/-- The fibre of the frame map over the standard frame is the block subgroup `diag(1_r, SU(m))`. -/
theorem specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff
    {A : specialUnitaryGroup (Fin (r + m)) 𝕜} :
    specialUnitaryFrameMap r m A = specialUnitaryFrameMap r m 1 ↔
      A ∈ (specialUnitaryGroup.fromBlocksOne 𝕜 r m).range := by
  rw [eq_comm, specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff, inv_one, one_mul,
    range_fromBlocksOne_eq_specialUnitaryStabilizer]

/-- For `m ≥ 1`, every orthonormal `r`-frame of `𝕜^(r + m)` consists of the first `r` columns of a
special unitary matrix. -/
theorem surjective_specialUnitaryFrameMap [NeZero m] :
    Function.Surjective (specialUnitaryFrameMap (𝕜 := 𝕜) r m) :=
  specialUnitary_unitaryMap_standard_surjective (r := r)
    (Nat.lt_add_of_pos_right (Nat.pos_of_neZero m))

/-! ### The fibre over the standard frame -/

variable (𝕜 r m) in
/-- The fibre of the frame map over the standard frame is `SU(m)`: the block embedding
`B ↦ diag(1_r, B)` is a homeomorphism of `SU(m)` onto the special unitary matrices fixing the
standard frame. -/
def specialUnitaryFrameFiberHomeomorph :
    specialUnitaryGroup (Fin m) 𝕜 ≃ₜ
      specialUnitaryFrameMap (𝕜 := 𝕜) r m ⁻¹' {specialUnitaryFrameMap r m 1} :=
  (specialUnitaryStabilizerHomeomorph 𝕜 r m).trans
    (Homeomorph.setCongr <| by
      ext A
      rw [← range_fromBlocksOne_eq_specialUnitaryStabilizer, SetLike.mem_coe, mem_preimage,
        mem_singleton_iff, specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff])

@[simp]
theorem coe_specialUnitaryFrameFiberHomeomorph_apply (B : specialUnitaryGroup (Fin m) 𝕜) :
    (specialUnitaryFrameFiberHomeomorph 𝕜 r m B : specialUnitaryGroup (Fin (r + m)) 𝕜) =
      specialUnitaryGroup.fromBlocksOne 𝕜 r m B :=
  coe_specialUnitaryStabilizerHomeomorph_apply m B

/-- A special unitary matrix fixing the standard frame is the block matrix `diag(1_r, B)` of its
image `B` in `SU(m)`. -/
@[simp]
theorem fromBlocksOne_specialUnitaryFrameFiberHomeomorph_symm_apply
    (A : specialUnitaryFrameMap (𝕜 := 𝕜) r m ⁻¹' {specialUnitaryFrameMap r m 1}) :
    specialUnitaryGroup.fromBlocksOne 𝕜 r m ((specialUnitaryFrameFiberHomeomorph 𝕜 r m).symm A) =
      A := by
  rw [← coe_specialUnitaryFrameFiberHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- The identity of `SU(m)` corresponds to the identity of `SU(r + m)` in the fibre. -/
@[simp]
theorem specialUnitaryFrameFiberHomeomorph_one :
    specialUnitaryFrameFiberHomeomorph 𝕜 r m 1 = ⟨1, rfl⟩ :=
  Subtype.ext (by simp)

/-! ### A local section near the standard frame -/

/-- **A local section of the special unitary Stiefel map.** For `m ≥ 1`, near the standard frame
there is a continuous map `s` to `SU(r + m)` with `s f` carrying the standard frame to `f`, and
`s e = 1` at the standard frame `e`. It is the Gram–Schmidt section of the unitary frame map
(`TauCeti.exists_unitaryFrameMap_localSection`), with the last column of each of its values
multiplied by the conjugate of its determinant: for `m ≥ 1` the last column is not among the
first `r`. -/
theorem exists_specialUnitaryFrameMap_localSection [NeZero m] :
    ∃ U : Set (finiteOrthonormalFrame 𝕜 r (r + m)), IsOpen U ∧
      standard 𝕜 (Nat.le_add_right r m) ∈ U ∧
      ∃ s : finiteOrthonormalFrame 𝕜 r (r + m) → specialUnitaryGroup (Fin (r + m)) 𝕜,
        ContinuousOn s U ∧ s (standard 𝕜 (Nat.le_add_right r m)) = 1 ∧
          ∀ f ∈ U, specialUnitaryFrameMap r m (s f) = f := by
  obtain ⟨U, hU, hstd, s, hs, hs1, hsec⟩ := exists_unitaryFrameMap_localSection (𝕜 := 𝕜) (r := r)
    (m := m)
  -- The last coordinate, which is not one of the first `r`.
  let j : Fin (r + m) := Fin.natAdd r ⟨m - 1, by have := Nat.pos_of_neZero m; omega⟩
  refine ⟨U, hU, hstd, fun f ↦ UnitaryGroup.toSpecialUnitaryAt j (s f),
    (UnitaryGroup.continuous_toSpecialUnitaryAt j).comp_continuousOn hs,
    Subtype.ext ?_, fun f hf ↦ ?_⟩
  · dsimp only
    rw [hs1, UnitaryGroup.toSpecialUnitaryAt_of_det_eq_one j (by simp)]
    rfl
  refine Subtype.ext (funext fun i ↦ ?_)
  have hi : Fin.castAdd m i ≠ j := fun hi ↦ by
    have := congrArg Fin.val hi
    simp only [Fin.val_castAdd, Fin.val_natAdd, j] at this
    omega
  have h := congrArg (fun g : finiteOrthonormalFrame 𝕜 r (r + m) ↦ g.val i) (hsec f hf)
  simp only [coe_unitaryFrameMap] at h
  simp only [coe_specialUnitaryFrameMap]
  rw [UnitaryGroup.toSpecialUnitaryAt_mulVec_single hi, h]

/-! ### Local triviality -/

/-- For `m ≥ 1`, the frame map `SU(r + m) → V_r(𝕜^(r + m))` has a chart with fibre `SU(m)` around
each orthonormal frame. -/
theorem exists_trivialization_specialUnitaryFrameMap [NeZero m]
    (b : finiteOrthonormalFrame 𝕜 r (r + m)) :
    ∃ e : Bundle.Trivialization (specialUnitaryGroup (Fin m) 𝕜) (specialUnitaryFrameMap r m),
      b ∈ e.baseSet := by
  -- `g` carries the standard frame to `b`; translating the local section by `g` gives a section
  -- near `b`.
  let := specialUnitaryMulAction 𝕜 r (r + m)
  have := continuousSMul_specialUnitaryMulAction 𝕜 r (r + m)
  obtain ⟨g, rfl⟩ := surjective_specialUnitaryFrameMap (𝕜 := 𝕜) (r := r) (m := m) b
  obtain ⟨U, hU, hstd, s, hs, -, hsec⟩ := exists_specialUnitaryFrameMap_localSection (𝕜 := 𝕜)
    (r := r) (m := m)
  let t : finiteOrthonormalFrame 𝕜 r (r + m) → finiteOrthonormalFrame 𝕜 r (r + m) :=
    fun f ↦ g⁻¹ • f
  have ht : Continuous t := continuous_const_smul _
  let e := Subgroup.localSectionTrivializationOfCosetFibers
    (specialUnitaryStabilizer 𝕜 (Nat.le_add_right r m)) (continuous_specialUnitaryFrameMap 𝕜 r m)
    (fun _ _ ↦ specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff) (t ⁻¹' U)
    (hU.preimage ht) (fun f ↦ g * s (t f))
    (continuousOn_const.mul (hs.comp ht.continuousOn fun _ hf ↦ hf))
    fun f hf ↦ by
      rw [specialUnitaryFrameMap_eq_smul_standard, mul_smul,
        ← specialUnitaryFrameMap_eq_smul_standard, hsec _ hf, smul_inv_smul]
  refine ⟨e.transFiberHomeomorph (specialUnitaryStabilizerHomeomorph 𝕜 r m).symm, ?_⟩
  simp only [Bundle.Trivialization.transFiberHomeomorph, e,
    Subgroup.localSectionTrivializationOfCosetFibers_baseSet, mem_preimage, t,
    specialUnitaryFrameMap_eq_smul_standard, inv_smul_smul]
  exact hstd

/-- For `m ≥ 1`, the frame map `SU(r + m) → V_r(𝕜^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, is a
Serre fibration: it is locally trivial with fibre `SU(m)`. -/
theorem specialUnitaryFrameMap_mem_serreFibrations [NeZero m] :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨specialUnitaryFrameMap r m, continuous_specialUnitaryFrameMap 𝕜 r m⟩ :
        _root_.TopCat.of (specialUnitaryGroup (Fin (r + m)) 𝕜) ⟶
          _root_.TopCat.of (finiteOrthonormalFrame 𝕜 r (r + m))) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (F := specialUnitaryGroup (Fin m) 𝕜) exists_trivialization_specialUnitaryFrameMap

end TauCeti
