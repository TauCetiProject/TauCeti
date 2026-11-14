/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.StiefelFibration.Unitary

/-!
# The Stiefel fibration `SO(m) → SO(r + m) → V_r(ℝ^(r + m))`

Applying a special orthogonal matrix to the standard frame `(e₀, …, e_{r-1})` gives the map
`SO(r + m) → V_r(ℝ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, to the orthonormal `r`-frames
(`TauCeti.specialOrthogonalFrameMap`): it reads off the first `r` columns of `A`. Its fibre over
the standard frame is the block subgroup `diag(1_r, SO(m))`, the image of
`Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ r m`, and its fibres are the left cosets of that
subgroup. For `m ≥ 1` the map is surjective and a locally trivial bundle with fibre `SO(m)`, and
hence a Serre fibration. For `r = 2` this is the bundle `SO(n) → SO(n + 2) → V₂(ℝ^(n + 2))` whose
homotopy sequence compares `π_(n-1)(SO(n))` with the stable groups.

The charts come from explicit local sections given by the Gram–Schmidt process. Complete a frame
`f` to the family `(f₀, …, f_{r-1}, e_r, …, e_{r+m-1})`. Near the standard frame this family is a
basis, and its normalized Gram–Schmidt orthonormalization is an orthonormal basis whose first `r`
vectors are those of `f`, because they are already orthonormal
(`InnerProductSpace.gramSchmidtNormed_eq_self_of_inner_eq_zero`). The matrix with these columns is
orthogonal, depends continuously on `f` by the continuity of the Gram–Schmidt process, and is the
identity at the standard frame (`TauCeti.exists_unitaryFrameMap_localSection`, the same section for
the unitary Stiefel fibration over `ℝ`), so it has determinant `1` near the standard frame. This
gives a continuous local section near the standard frame, and translating it by `SO(r + m)` gives
one near every frame. Such a section defines a chart with fibre the stabilizer of the standard frame
(`Subgroup.localSectionTrivializationOfCosetFibers`), which is `SO(m)`.

The case `r = 1`, where frames are unit vectors, is
`TauCeti.Topology.Grassmannian.SphereBundle.Basic`, with charts from explicit rotations.

## Main definitions

* `TauCeti.specialOrthogonalFrameMap`: the map `SO(r + m) → V_r(ℝ^(r + m))`,
  `A ↦ (A e₀, …, A e_{r-1})`.
* `TauCeti.specialOrthogonalFrameFiberHomeomorph`: `SO(m)` is homeomorphic to the fibre of this
  map over the standard frame, through `B ↦ diag(1_r, B)`.

## Main results

* `TauCeti.specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_iff`: the fibres are the left
  cosets of the stabilizer of the standard frame.
* `TauCeti.specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_one_iff`: the fibre over the
  standard frame is the image of `SO(m)`.
* `TauCeti.exists_trivialization_specialOrthogonalFrameMap`: a chart with fibre `SO(m)` around each
  frame.
* `TauCeti.specialOrthogonalFrameMap_mem_serreFibrations`: `SO(r + m) → V_r(ℝ^(r + m))` is a Serre
  fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (Stiefel manifolds and
  the fibrations `SO(n - k) → SO(n) → V_k(ℝⁿ)`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 6.35, which compares
  `π_(n-1)(SO(n))` with the stable groups through `V₂(ℝ^(n + 2))`.
-/

public section

open InnerProductSpace Matrix Set Topology

noncomputable section

namespace TauCeti

open finiteOrthonormalFrame

variable {r m : ℕ}

/-! ### The frame map `SO(r + m) → V_r(ℝ^(r + m))` -/

variable (r m) in
/-- The Stiefel map `SO(r + m) → V_r(ℝ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, sending a special
orthogonal matrix to its first `r` columns. -/
def specialOrthogonalFrameMap (A : specialOrthogonalGroup (Fin (r + m)) ℝ) :
    finiteOrthonormalFrame ℝ r (r + m) :=
  unitaryMap ⟨A.1, A.2.1⟩ (standard ℝ (Nat.le_add_right r m))

/-- In coordinates, the `i`-th vector of `specialOrthogonalFrameMap r m A` is the column
`A e_i` of `A`. -/
@[simp]
theorem coe_specialOrthogonalFrameMap (A : specialOrthogonalGroup (Fin (r + m)) ℝ) :
    (specialOrthogonalFrameMap r m A : Fin r → Fin (r + m) → ℝ) =
      fun i ↦ (A : Matrix (Fin (r + m)) (Fin (r + m)) ℝ) *ᵥ Pi.single (Fin.castAdd m i) 1 := by
  rw [specialOrthogonalFrameMap, coe_unitaryMap, coe_standard]
  -- `Fin.castAdd m` is by definition `Fin.castLE` along `r ≤ r + m`, and there is no library lemma
  -- rewriting one into the other.
  rfl

variable (r m) in
/-- The frame map `SO(r + m) → V_r(ℝ^(r + m))` is continuous. -/
theorem continuous_specialOrthogonalFrameMap : Continuous (specialOrthogonalFrameMap r m) :=
  continuous_unitaryMap.comp ((continuous_subtype_val.subtype_mk _).prodMk continuous_const)

/-- The frame map is equivariant: `(A B) • e = A • (B • e)`. -/
theorem specialOrthogonalFrameMap_mul (A B : specialOrthogonalGroup (Fin (r + m)) ℝ) :
    specialOrthogonalFrameMap r m (A * B) =
      unitaryMap ⟨A.1, A.2.1⟩ (specialOrthogonalFrameMap r m B) :=
  unitaryMap_mul ⟨A.1, A.2.1⟩ ⟨B.1, B.2.1⟩ _

/-- The frame map of the identity is the standard frame. -/
@[simp]
theorem specialOrthogonalFrameMap_one :
    specialOrthogonalFrameMap r m 1 = standard ℝ (Nat.le_add_right r m) :=
  unitaryMap_one _

/-- The frame map is the orbit map `A ↦ A • e` of the standard frame `e` under
`specialOrthogonalMulAction`. -/
theorem specialOrthogonalFrameMap_eq_smul_standard (A : specialOrthogonalGroup (Fin (r + m)) ℝ) :
    letI := specialOrthogonalMulAction r (r + m)
    specialOrthogonalFrameMap r m A = A • standard ℝ (Nat.le_add_right r m) :=
  (specialOrthogonal_smul_def A _).symm

/-- The fibres of the frame map are the left cosets of the stabilizer of the standard frame. -/
theorem specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_iff
    {A B : specialOrthogonalGroup (Fin (r + m)) ℝ} :
    specialOrthogonalFrameMap r m A = specialOrthogonalFrameMap r m B ↔
      A⁻¹ * B ∈ specialOrthogonalStabilizer (Nat.le_add_right r m) := by
  have hmem : A⁻¹ * B ∈ specialOrthogonalStabilizer (Nat.le_add_right r m) ↔
      specialOrthogonalFrameMap r m (A⁻¹ * B) = specialOrthogonalFrameMap r m 1 := by
    rw [specialOrthogonalFrameMap_one]
    exact mem_specialOrthogonalStabilizer_iff
  rw [hmem]
  constructor
  · intro h
    rw [specialOrthogonalFrameMap_mul, ← h, ← specialOrthogonalFrameMap_mul, inv_mul_cancel]
  · intro h
    rw [← mul_inv_cancel_left A B, specialOrthogonalFrameMap_mul A, h,
      ← specialOrthogonalFrameMap_mul, mul_one]

/-- The fibre of the frame map over the standard frame is the block subgroup `diag(1_r, SO(m))`. -/
theorem specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_one_iff
    {A : specialOrthogonalGroup (Fin (r + m)) ℝ} :
    specialOrthogonalFrameMap r m A = specialOrthogonalFrameMap r m 1 ↔
      A ∈ (SpecialOrthogonalGroup.fromBlocksOne ℝ r m).range := by
  rw [eq_comm, specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_iff, inv_one, one_mul,
    range_fromBlocksOne_eq_specialOrthogonalStabilizer]

/-- For `m ≥ 1`, every orthonormal `r`-frame of `ℝ^(r + m)` consists of the first `r` columns of a
special orthogonal matrix. -/
theorem surjective_specialOrthogonalFrameMap [NeZero m] :
    Function.Surjective (specialOrthogonalFrameMap r m) :=
  specialOrthogonal_unitaryMap_standard_surjective (r := r)
    (Nat.lt_add_of_pos_right (Nat.pos_of_neZero m))

/-! ### The fibre over the standard frame -/

variable (r m) in
/-- The fibre of the frame map over the standard frame is `SO(m)`: the block embedding
`B ↦ diag(1_r, B)` is a homeomorphism of `SO(m)` onto the special orthogonal matrices fixing the
standard frame. -/
def specialOrthogonalFrameFiberHomeomorph :
    specialOrthogonalGroup (Fin m) ℝ ≃ₜ
      specialOrthogonalFrameMap r m ⁻¹' {specialOrthogonalFrameMap r m 1} :=
  (specialOrthogonalStabilizerHomeomorph r m).trans
    (Homeomorph.setCongr <| by
      ext A
      rw [← range_fromBlocksOne_eq_specialOrthogonalStabilizer, SetLike.mem_coe, mem_preimage,
        mem_singleton_iff, specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_one_iff])

@[simp]
theorem coe_specialOrthogonalFrameFiberHomeomorph_apply (B : specialOrthogonalGroup (Fin m) ℝ) :
    (specialOrthogonalFrameFiberHomeomorph r m B : specialOrthogonalGroup (Fin (r + m)) ℝ) =
      SpecialOrthogonalGroup.fromBlocksOne ℝ r m B :=
  coe_specialOrthogonalStabilizerHomeomorph_apply m B

/-- A special orthogonal matrix fixing the standard frame is the block matrix `diag(1_r, B)` of its
image `B` in `SO(m)`. -/
@[simp]
theorem fromBlocksOne_specialOrthogonalFrameFiberHomeomorph_symm_apply
    (A : specialOrthogonalFrameMap r m ⁻¹' {specialOrthogonalFrameMap r m 1}) :
    SpecialOrthogonalGroup.fromBlocksOne ℝ r m
        ((specialOrthogonalFrameFiberHomeomorph r m).symm A) = A := by
  rw [← coe_specialOrthogonalFrameFiberHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- The identity of `SO(m)` corresponds to the identity of `SO(r + m)` in the fibre. -/
@[simp]
theorem specialOrthogonalFrameFiberHomeomorph_one :
    specialOrthogonalFrameFiberHomeomorph r m 1 = ⟨1, rfl⟩ :=
  Subtype.ext (by simp)

/-! ### A local section near the standard frame -/

/-- The Gram–Schmidt section of the unitary frame map
(`TauCeti.exists_unitaryFrameMap_localSection`) takes values in `SO(r + m)` near the standard frame:
it is `1` there, and its determinant is a continuous function with values `±1`. -/
private theorem exists_specialOrthogonalFrameMap_localSection :
    ∃ U : Set (finiteOrthonormalFrame ℝ r (r + m)), IsOpen U ∧
      standard ℝ (Nat.le_add_right r m) ∈ U ∧
      ∃ s : finiteOrthonormalFrame ℝ r (r + m) → specialOrthogonalGroup (Fin (r + m)) ℝ,
        ContinuousOn s U ∧ ∀ f ∈ U, specialOrthogonalFrameMap r m (s f) = f := by
  obtain ⟨U, hU, hstd, s, hs, hs1, hsec⟩ := exists_unitaryFrameMap_localSection (𝕜 := ℝ) (r := r)
    (m := m)
  have hdet : ContinuousOn (fun f ↦ (s f : Matrix (Fin (r + m)) (Fin (r + m)) ℝ).det) U :=
    continuous_id.matrix_det.comp_continuousOn (continuous_subtype_val.comp_continuousOn hs)
  let V := U ∩ (fun f ↦ (s f : Matrix (Fin (r + m)) (Fin (r + m)) ℝ).det) ⁻¹' Ioi 0
  -- A real unitary matrix has determinant `±1`, so positive determinant means determinant `1`.
  have hmem {f} (hf : f ∈ V) :
      (s f : Matrix (Fin (r + m)) (Fin (r + m)) ℝ) ∈ specialOrthogonalGroup (Fin (r + m)) ℝ := by
    refine ⟨(s f).2, ?_⟩
    rcases mul_self_eq_one_iff.1 (by simpa using (det_of_mem_unitary (s f).2).2) with h | h
    · exact h
    · have := hf.2
      simp only [mem_preimage, mem_Ioi, h] at this
      norm_num at this
  classical
  refine ⟨V, hdet.isOpen_inter_preimage hU isOpen_Ioi, ⟨hstd, by simp [hs1]⟩,
    fun f ↦ if hf : f ∈ V then ⟨s f, hmem hf⟩ else 1, ?_, fun f hf ↦ ?_⟩
  · rw [IsInducing.subtypeVal.continuousOn_iff]
    exact (continuous_subtype_val.comp_continuousOn (hs.mono inter_subset_left)).congr
      fun f (hf : f ∈ V) ↦ by simp [hf]
  · refine Subtype.ext (funext fun i ↦ ?_)
    have h := congrArg (fun g : finiteOrthonormalFrame ℝ r (r + m) ↦ g.1 i) (hsec f hf.1)
    simp only [coe_unitaryFrameMap] at h
    simp [hf, h]

/-! ### Local triviality -/

/-- For `m ≥ 1`, the frame map `SO(r + m) → V_r(ℝ^(r + m))` has a chart with fibre `SO(m)` around
each orthonormal frame. -/
theorem exists_trivialization_specialOrthogonalFrameMap [NeZero m]
    (b : finiteOrthonormalFrame ℝ r (r + m)) :
    ∃ e : Bundle.Trivialization (specialOrthogonalGroup (Fin m) ℝ) (specialOrthogonalFrameMap r m),
      b ∈ e.baseSet := by
  -- `g` carries the standard frame to `b`; translating the Gram–Schmidt section by `g` gives a
  -- section near `b`.
  obtain ⟨g, hg⟩ := surjective_specialOrthogonalFrameMap (r := r) (m := m) b
  let t : finiteOrthonormalFrame ℝ r (r + m) → finiteOrthonormalFrame ℝ r (r + m) :=
    unitaryMap ⟨(g⁻¹ : specialOrthogonalGroup (Fin (r + m)) ℝ).1, (g⁻¹).2.1⟩
  have ht : Continuous t := continuous_unitaryMap.comp (continuous_const.prodMk continuous_id)
  have hgt (f : finiteOrthonormalFrame ℝ r (r + m)) : unitaryMap ⟨g.1, g.2.1⟩ (t f) = f := by
    have h1 : (⟨g.1, g.2.1⟩ : unitaryGroup (Fin (r + m)) ℝ) * ⟨(g⁻¹).1, (g⁻¹).2.1⟩ = 1 :=
      Subtype.ext ((Submonoid.coe_mul _ g g⁻¹).symm.trans
        (by rw [mul_inv_cancel, OneMemClass.coe_one]; rfl))
    rw [← unitaryMap_mul, h1, unitaryMap_one]
  obtain ⟨U, hU, hstd, s, hs, hsec⟩ := exists_specialOrthogonalFrameMap_localSection (r := r)
    (m := m)
  let e := Subgroup.localSectionTrivializationOfCosetFibers
    (specialOrthogonalStabilizer (Nat.le_add_right r m)) (continuous_specialOrthogonalFrameMap r m)
    (fun _ _ ↦ specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_iff) (t ⁻¹' U)
    (hU.preimage ht) (fun f ↦ g * s (t f))
    (continuousOn_const.mul (hs.comp ht.continuousOn fun _ hf ↦ hf))
    fun f hf ↦ by rw [specialOrthogonalFrameMap_mul, hsec _ hf, hgt]
  refine ⟨e.transFiberHomeomorph (specialOrthogonalStabilizerHomeomorph r m).symm, ?_⟩
  simp only [Bundle.Trivialization.transFiberHomeomorph, e,
    Subgroup.localSectionTrivializationOfCosetFibers_baseSet, mem_preimage, t, ← hg,
    ← specialOrthogonalFrameMap_mul, inv_mul_cancel, specialOrthogonalFrameMap_one]
  exact hstd

/-- For `m ≥ 1`, the frame map `SO(r + m) → V_r(ℝ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, is a
Serre fibration: it is locally trivial with fibre `SO(m)`. -/
theorem specialOrthogonalFrameMap_mem_serreFibrations [NeZero m] :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨specialOrthogonalFrameMap r m,
          continuous_specialOrthogonalFrameMap r m⟩ :
        _root_.TopCat.of (specialOrthogonalGroup (Fin (r + m)) ℝ) ⟶
          _root_.TopCat.of (finiteOrthonormalFrame ℝ r (r + m))) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (F := specialOrthogonalGroup (Fin m) ℝ) exists_trivialization_specialOrthogonalFrameMap

end TauCeti
