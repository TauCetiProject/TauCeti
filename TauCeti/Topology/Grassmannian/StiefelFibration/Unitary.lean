/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Quotient.LocalSection
public import TauCeti.Topology.Grassmannian.FrameQuotient
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# The unitary Stiefel fibration `U(m) → U(r + m) → V_r(𝕜^(r + m))`

For `𝕜 = ℝ` or `ℂ` (any `RCLike 𝕜`), applying a unitary matrix to the standard frame
`(e₀, …, e_{r-1})` gives the map `U(r + m) → V_r(𝕜^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, to the
orthonormal `r`-frames (`TauCeti.unitaryFrameMap`): it reads off the first `r` columns of `A`.
It is surjective, its fibre over the standard frame is the block subgroup `diag(1_r, U(m))`, the
image of `Matrix.UnitaryGroup.fromBlocksOne 𝕜 r m`, and its fibres are the left cosets of that
subgroup. It is a locally trivial bundle with fibre `U(m)`, and hence a Serre fibration. Over `ℂ`
and for `r = 2` this is the principal bundle `U(n - 2) → U(n) → V₂(ℂⁿ)` of the ordered orthonormal
two-frames; over `ℝ` it is `O(m) → O(r + m) → V_r(ℝ^(r + m))`. Unlike the special orthogonal case,
there is no condition on `m`: for `m = 0` the map is a homeomorphism `U(r) ≃ₜ V_r(𝕜^r)`.

The charts come from explicit local sections given by the Gram–Schmidt process. Complete a frame
`f` to the family `(f₀, …, f_{r-1}, e_r, …, e_{r+m-1})`. Near the standard frame this family is a
basis, and its normalized Gram–Schmidt orthonormalization is an orthonormal basis whose first `r`
vectors are those of `f`, because they are already orthonormal
(`InnerProductSpace.gramSchmidtNormed_eq_self_of_inner_eq_zero`). The matrix with these columns is
unitary and depends continuously on `f` by the continuity of the Gram–Schmidt process, and it is
the identity at the standard frame (`TauCeti.exists_unitaryFrameMap_localSection`). Translating
this section by `U(r + m)` gives one near every frame, and such a section defines a chart with
fibre the stabilizer of the standard frame (`Subgroup.localSectionTrivializationOfCosetFibers`),
which is `U(m)`. The special orthogonal Stiefel fibration
`TauCeti.Topology.Grassmannian.StiefelFibration.Basic` restricts the same section to the frames
where it has determinant `1`.

## Main definitions

* `TauCeti.unitaryFrameMap`: the map `U(r + m) → V_r(𝕜^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`.
* `TauCeti.unitaryFrameFiberHomeomorph`: `U(m)` is homeomorphic to the fibre of this map over the
  standard frame, through `B ↦ diag(1_r, B)`.

## Main results

* `TauCeti.unitaryFrameMap_eq_unitaryFrameMap_iff`: the fibres are the left cosets of the
  stabilizer of the standard frame.
* `TauCeti.unitaryFrameMap_eq_unitaryFrameMap_one_iff`: the fibre over the standard frame is the
  image of `U(m)`.
* `TauCeti.exists_unitaryFrameMap_localSection`: a continuous section of the frame map near the
  standard frame, taking the value `1` there.
* `TauCeti.exists_trivialization_unitaryFrameMap`: a chart with fibre `U(m)` around each frame.
* `TauCeti.unitaryFrameMap_mem_serreFibrations`: `U(r + m) → V_r(𝕜^(r + m))` is a Serre
  fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (Stiefel manifolds and
  the fibrations `U(n - k) → U(n) → V_k(ℂⁿ)`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

open InnerProductSpace Matrix Set Topology

noncomputable section

namespace TauCeti

open finiteOrthonormalFrame

variable {𝕜 : Type*} [RCLike 𝕜] {r m : ℕ}

/-! ### The frame map `U(r + m) → V_r(𝕜^(r + m))` -/

variable (r m) in
/-- The unitary Stiefel map `U(r + m) → V_r(𝕜^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, sending a
unitary matrix to its first `r` columns. -/
def unitaryFrameMap (A : unitaryGroup (Fin (r + m)) 𝕜) : finiteOrthonormalFrame 𝕜 r (r + m) :=
  unitaryMap A (standard 𝕜 (Nat.le_add_right r m))

/-- In coordinates, the `i`-th vector of `unitaryFrameMap r m A` is the column `A e_i` of `A`. -/
@[simp]
theorem coe_unitaryFrameMap (A : unitaryGroup (Fin (r + m)) 𝕜) :
    (unitaryFrameMap r m A : Fin r → Fin (r + m) → 𝕜) =
      fun i ↦ (A : Matrix (Fin (r + m)) (Fin (r + m)) 𝕜) *ᵥ Pi.single (Fin.castAdd m i) 1 := by
  rw [unitaryFrameMap, coe_unitaryMap, coe_standard]
  -- `Fin.castAdd m` is by definition `Fin.castLE` along `r ≤ r + m`, and there is no library lemma
  -- rewriting one into the other.
  rfl

variable (𝕜 r m) in
/-- The frame map `U(r + m) → V_r(𝕜^(r + m))` is continuous. -/
@[fun_prop]
theorem continuous_unitaryFrameMap : Continuous (unitaryFrameMap (𝕜 := 𝕜) r m) :=
  continuous_unitaryMap.comp (continuous_id.prodMk continuous_const)

/-- The frame map is equivariant: `(A B) • e = A • (B • e)`. -/
theorem unitaryFrameMap_mul (A B : unitaryGroup (Fin (r + m)) 𝕜) :
    unitaryFrameMap r m (A * B) = unitaryMap A (unitaryFrameMap r m B) :=
  unitaryMap_mul A B _

/-- The frame map of the identity is the standard frame. -/
@[simp]
theorem unitaryFrameMap_one :
    unitaryFrameMap r m (1 : unitaryGroup (Fin (r + m)) 𝕜) = standard 𝕜 (Nat.le_add_right r m) :=
  unitaryMap_one _

/-- The fibres of the frame map are the left cosets of the stabilizer of the standard frame. -/
theorem unitaryFrameMap_eq_unitaryFrameMap_iff {A B : unitaryGroup (Fin (r + m)) 𝕜} :
    unitaryFrameMap r m A = unitaryFrameMap r m B ↔
      A⁻¹ * B ∈ unitaryStabilizer 𝕜 (Nat.le_add_right r m) := by
  have hmem : A⁻¹ * B ∈ unitaryStabilizer 𝕜 (Nat.le_add_right r m) ↔
      unitaryFrameMap r m (A⁻¹ * B) = unitaryFrameMap r m 1 := by
    rw [unitaryFrameMap_one]
    exact mem_unitaryStabilizer_iff
  rw [hmem]
  constructor
  · intro h
    rw [unitaryFrameMap_mul, ← h, ← unitaryFrameMap_mul, inv_mul_cancel]
  · intro h
    rw [← mul_inv_cancel_left A B, unitaryFrameMap_mul A, h, ← unitaryFrameMap_mul, mul_one]

/-- The fibre of the frame map over the standard frame is the block subgroup `diag(1_r, U(m))`. -/
theorem unitaryFrameMap_eq_unitaryFrameMap_one_iff {A : unitaryGroup (Fin (r + m)) 𝕜} :
    unitaryFrameMap r m A = unitaryFrameMap r m 1 ↔
      A ∈ (UnitaryGroup.fromBlocksOne 𝕜 r m).range := by
  rw [eq_comm, unitaryFrameMap_eq_unitaryFrameMap_iff, inv_one, one_mul,
    range_fromBlocksOne_eq_unitaryStabilizer]

/-- Every orthonormal `r`-frame of `𝕜^(r + m)` consists of the first `r` columns of a unitary
matrix. -/
theorem surjective_unitaryFrameMap :
    Function.Surjective (unitaryFrameMap (𝕜 := 𝕜) r m) :=
  unitaryMap_standard_surjective (Nat.le_add_right r m)

/-! ### The fibre over the standard frame -/

variable (𝕜 r m) in
/-- The fibre of the frame map over the standard frame is `U(m)`: the block embedding
`B ↦ diag(1_r, B)` is a homeomorphism of `U(m)` onto the unitary matrices fixing the standard
frame. -/
def unitaryFrameFiberHomeomorph :
    unitaryGroup (Fin m) 𝕜 ≃ₜ
      unitaryFrameMap r m ⁻¹' {unitaryFrameMap r m (1 : unitaryGroup (Fin (r + m)) 𝕜)} :=
  (unitaryStabilizerHomeomorph 𝕜 r m).trans
    (Homeomorph.setCongr <| by
      ext A
      rw [← range_fromBlocksOne_eq_unitaryStabilizer, SetLike.mem_coe, mem_preimage,
        mem_singleton_iff, unitaryFrameMap_eq_unitaryFrameMap_one_iff])

@[simp]
theorem coe_unitaryFrameFiberHomeomorph_apply (B : unitaryGroup (Fin m) 𝕜) :
    (unitaryFrameFiberHomeomorph 𝕜 r m B : unitaryGroup (Fin (r + m)) 𝕜) =
      UnitaryGroup.fromBlocksOne 𝕜 r m B :=
  coe_unitaryStabilizerHomeomorph_apply m B

/-- A unitary matrix fixing the standard frame is the block matrix `diag(1_r, B)` of its image `B`
in `U(m)`. -/
@[simp]
theorem fromBlocksOne_unitaryFrameFiberHomeomorph_symm_apply
    (A : unitaryFrameMap r m ⁻¹' {unitaryFrameMap r m (1 : unitaryGroup (Fin (r + m)) 𝕜)}) :
    UnitaryGroup.fromBlocksOne 𝕜 r m ((unitaryFrameFiberHomeomorph 𝕜 r m).symm A) = A := by
  rw [← coe_unitaryFrameFiberHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- The identity of `U(m)` corresponds to the identity of `U(r + m)` in the fibre. -/
@[simp]
theorem unitaryFrameFiberHomeomorph_one :
    unitaryFrameFiberHomeomorph 𝕜 r m 1 = ⟨1, rfl⟩ :=
  Subtype.ext (by simp)

/-! ### A local section near the standard frame by the Gram–Schmidt process -/

/-- The completion `(f₀, …, f_{r-1}, e_r, …, e_{r+m-1})` of a frame by the last `m` standard basis
vectors, as a family of vectors of `EuclideanSpace 𝕜 (Fin (r + m))`. -/
private def frameCompletion (f : finiteOrthonormalFrame 𝕜 r (r + m)) :
    Fin (r + m) → EuclideanSpace 𝕜 (Fin (r + m)) :=
  Fin.append (fun i ↦ WithLp.toLp 2 (f.1 i)) fun j ↦ EuclideanSpace.single (Fin.natAdd r j) 1

private theorem continuous_frameCompletion (k : Fin (r + m)) :
    Continuous fun f : finiteOrthonormalFrame 𝕜 r (r + m) ↦ frameCompletion f k := by
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
  · simp only [frameCompletion, Fin.append_left]
    exact (PiLp.continuous_toLp 2 _).comp ((continuous_apply i).comp continuous_subtype_val)
  · simp only [frameCompletion, Fin.append_right]
    exact continuous_const

/-- The completion of the standard frame is the standard basis. -/
private theorem frameCompletion_standard :
    frameCompletion (standard 𝕜 (Nat.le_add_right r m)) =
      fun k ↦ EuclideanSpace.single k (1 : 𝕜) := by
  funext k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
  · simp only [frameCompletion, Fin.append_left, coe_standard, PiLp.toLp_single]
    -- As above, `Fin.castLE` along `r ≤ r + m` is by definition `Fin.castAdd m`.
    rfl
  · simp [frameCompletion]

/-- The frames whose completion is a basis: the domain of the Gram–Schmidt section. -/
private def frameSectionDomain : Set (finiteOrthonormalFrame 𝕜 r (r + m)) :=
  {f | LinearIndependent 𝕜 (frameCompletion f)}

private theorem isOpen_frameSectionDomain :
    IsOpen (frameSectionDomain (𝕜 := 𝕜) (r := r) (m := m)) := by
  exact (isOpen_setOfPred_linearIndependent (𝕜 := 𝕜) (E := EuclideanSpace 𝕜 (Fin (r + m)))
    (ι := Fin (r + m))).preimage (continuous_pi (continuous_frameCompletion (𝕜 := 𝕜) (r := r)))

private theorem standard_mem_frameSectionDomain :
    standard 𝕜 (Nat.le_add_right r m) ∈ frameSectionDomain := by
  simp only [frameSectionDomain, mem_ofPred_eq, frameCompletion_standard]
  exact EuclideanSpace.orthonormal_single.linearIndependent

/-- The Gram–Schmidt matrix of a frame: its columns are the normalized Gram–Schmidt vectors of the
completion of the frame. -/
private def frameGramSchmidt (f : finiteOrthonormalFrame 𝕜 r (r + m)) :
    Matrix (Fin (r + m)) (Fin (r + m)) 𝕜 :=
  Matrix.of fun a k ↦ WithLp.ofLp (gramSchmidtNormed 𝕜 (frameCompletion f) k) a

private theorem continuousOn_frameGramSchmidt :
    ContinuousOn (frameGramSchmidt (𝕜 := 𝕜) (r := r) (m := m)) frameSectionDomain := by
  have h (k : Fin (r + m)) : ContinuousOn (fun f ↦ gramSchmidtNormed 𝕜 (frameCompletion f) k)
      (frameSectionDomain (𝕜 := 𝕜) (r := r) (m := m)) :=
    ContinuousOn.gramSchmidtNormed (v := fun l f ↦ frameCompletion f l) k
      (fun l _ ↦ (continuous_frameCompletion l).continuousOn) (fun _ hf ↦ hf.linearIndepOn _)
  exact continuousOn_pi.2 fun a ↦ continuousOn_pi.2 fun k ↦
    ((continuous_apply a).comp (PiLp.continuous_ofLp 2 _)).comp_continuousOn (h k)

/-- When the completion of a frame is a basis, its Gram–Schmidt matrix is unitary. -/
private theorem frameGramSchmidt_mem_unitaryGroup {f : finiteOrthonormalFrame 𝕜 r (r + m)}
    (hf : f ∈ frameSectionDomain) :
    frameGramSchmidt f ∈ unitaryGroup (Fin (r + m)) 𝕜 := by
  have h : Orthonormal 𝕜 (gramSchmidtNormed 𝕜 (frameCompletion f)) :=
    gramSchmidtNormed_orthonormal hf
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  refine Matrix.ext fun k l ↦ ?_
  rw [Matrix.mul_apply, Matrix.one_apply, ← orthonormal_iff_ite.1 h k l]
  simp only [frameGramSchmidt, conjTranspose_apply, of_apply, RCLike.star_def, PiLp.inner_apply,
    RCLike.inner_apply]
  exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _

/-- The first `r` columns of the Gram–Schmidt matrix of a frame are the vectors of the frame, since
these vectors are already orthonormal. -/
private theorem frameGramSchmidt_mulVec_single (f : finiteOrthonormalFrame 𝕜 r (r + m))
    (i : Fin r) :
    frameGramSchmidt f *ᵥ Pi.single (Fin.castAdd m i) 1 = f.1 i := by
  have hgs : gramSchmidtNormed 𝕜 (frameCompletion f) (Fin.castAdd m i) = WithLp.toLp 2 (f.1 i) := by
    refine (gramSchmidtNormed_eq_self_of_inner_eq_zero (fun k hk ↦ ?_) ?_).trans ?_
    · obtain ⟨j, rfl⟩ : ∃ j : Fin r, Fin.castAdd m j = k :=
        ⟨⟨k, lt_trans (Fin.lt_def.1 hk) (Fin.castAdd_lt m i)⟩, Fin.ext rfl⟩
      simp only [frameCompletion, Fin.append_left]
      exact f.2.2 fun hji ↦ hk.ne (by rw [hji])
    · simpa [frameCompletion] using f.2.1 i
    · simp [frameCompletion]
  funext a
  rw [mulVec_single_one]
  simp [frameGramSchmidt, hgs]

/-- The Gram–Schmidt matrix of the standard frame is the identity. -/
private theorem frameGramSchmidt_standard :
    frameGramSchmidt (standard 𝕜 (Nat.le_add_right r m)) = 1 := by
  have hgs : gramSchmidtNormed 𝕜 (frameCompletion (standard 𝕜 (Nat.le_add_right r m))) =
      fun k ↦ EuclideanSpace.single k (1 : 𝕜) := by
    rw [frameCompletion_standard]
    funext k
    refine gramSchmidtNormed_eq_self_of_inner_eq_zero (fun l hl ↦ ?_) (by simp)
    simp [EuclideanSpace.inner_single_left, hl.ne']
  refine Matrix.ext fun a k ↦ ?_
  rw [Matrix.one_apply]
  simp [frameGramSchmidt, hgs]

open Classical in
/-- The Gram–Schmidt local section of the frame map near the standard frame, extended by `1`. -/
private def frameSection (f : finiteOrthonormalFrame 𝕜 r (r + m)) : unitaryGroup (Fin (r + m)) 𝕜 :=
  if hf : f ∈ frameSectionDomain then ⟨frameGramSchmidt f, frameGramSchmidt_mem_unitaryGroup hf⟩
  else 1

private theorem coe_frameSection {f : finiteOrthonormalFrame 𝕜 r (r + m)}
    (hf : f ∈ frameSectionDomain) :
    (frameSection f : Matrix (Fin (r + m)) (Fin (r + m)) 𝕜) = frameGramSchmidt f := by
  simp [frameSection, hf]

/-- **Gram–Schmidt local section of the unitary Stiefel map**: near the standard frame there is a
continuous map `s` to `U(r + m)` with `s f` carrying the standard frame to `f`, and `s e = 1` at the
standard frame `e`. The value of `s f` is the matrix whose columns are the normalized Gram–Schmidt
orthonormalization of `(f₀, …, f_{r-1}, e_r, …, e_{r+m-1})`. -/
theorem exists_unitaryFrameMap_localSection :
    ∃ U : Set (finiteOrthonormalFrame 𝕜 r (r + m)), IsOpen U ∧
      standard 𝕜 (Nat.le_add_right r m) ∈ U ∧
      ∃ s : finiteOrthonormalFrame 𝕜 r (r + m) → unitaryGroup (Fin (r + m)) 𝕜, ContinuousOn s U ∧
        s (standard 𝕜 (Nat.le_add_right r m)) = 1 ∧ ∀ f ∈ U, unitaryFrameMap r m (s f) = f := by
  refine ⟨frameSectionDomain, isOpen_frameSectionDomain, standard_mem_frameSectionDomain,
    frameSection, ?_, ?_, fun f hf ↦ ?_⟩
  · rw [IsInducing.subtypeVal.continuousOn_iff]
    exact continuousOn_frameGramSchmidt.congr fun f hf ↦ coe_frameSection hf
  · exact Subtype.ext ((coe_frameSection standard_mem_frameSectionDomain).trans
      frameGramSchmidt_standard)
  · refine Subtype.ext (funext fun i ↦ ?_)
    simp only [coe_unitaryFrameMap]
    rw [coe_frameSection hf, frameGramSchmidt_mulVec_single]

/-! ### Local triviality -/

/-- The frame map `U(r + m) → V_r(𝕜^(r + m))` has a chart with fibre `U(m)` around each orthonormal
frame. -/
theorem exists_trivialization_unitaryFrameMap (b : finiteOrthonormalFrame 𝕜 r (r + m)) :
    ∃ e : Bundle.Trivialization (unitaryGroup (Fin m) 𝕜) (unitaryFrameMap r m), b ∈ e.baseSet := by
  -- `g` carries the standard frame to `b`; translating the Gram–Schmidt section by `g` gives a
  -- section near `b`.
  obtain ⟨g, rfl⟩ := surjective_unitaryFrameMap (𝕜 := 𝕜) (r := r) (m := m) b
  obtain ⟨U, hU, hstd, s, hs, -, hsec⟩ := exists_unitaryFrameMap_localSection (𝕜 := 𝕜) (r := r)
    (m := m)
  let t : finiteOrthonormalFrame 𝕜 r (r + m) → finiteOrthonormalFrame 𝕜 r (r + m) :=
    unitaryMap g⁻¹
  have ht : Continuous t := continuous_unitaryMap.comp (continuous_const.prodMk continuous_id)
  have hgt (f : finiteOrthonormalFrame 𝕜 r (r + m)) : unitaryMap g (t f) = f := by
    rw [← unitaryMap_mul, mul_inv_cancel, unitaryMap_one]
  let e := Subgroup.localSectionTrivializationOfCosetFibers
    (unitaryStabilizer 𝕜 (Nat.le_add_right r m)) (continuous_unitaryFrameMap 𝕜 r m)
    (fun _ _ ↦ unitaryFrameMap_eq_unitaryFrameMap_iff) (t ⁻¹' U) (hU.preimage ht)
    (fun f ↦ g * s (t f)) (continuousOn_const.mul (hs.comp ht.continuousOn fun _ hf ↦ hf))
    fun f hf ↦ by rw [unitaryFrameMap_mul, hsec _ hf, hgt]
  refine ⟨e.transFiberHomeomorph (unitaryStabilizerHomeomorph 𝕜 r m).symm, ?_⟩
  simp only [Bundle.Trivialization.transFiberHomeomorph, e,
    Subgroup.localSectionTrivializationOfCosetFibers_baseSet, mem_preimage, t,
    ← unitaryFrameMap_mul, inv_mul_cancel, unitaryFrameMap_one]
  exact hstd

/-- The frame map `U(r + m) → V_r(𝕜^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, is a Serre fibration:
it is locally trivial with fibre `U(m)`. -/
theorem unitaryFrameMap_mem_serreFibrations :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨unitaryFrameMap r m, continuous_unitaryFrameMap 𝕜 r m⟩ :
        _root_.TopCat.of (unitaryGroup (Fin (r + m)) 𝕜) ⟶
          _root_.TopCat.of (finiteOrthonormalFrame 𝕜 r (r + m))) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (F := unitaryGroup (Fin m) 𝕜) exists_trivialization_unitaryFrameMap

end TauCeti
