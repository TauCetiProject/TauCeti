/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
public import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Grassmannian.Orthonormal
import TauCeti.Topology.Algebra.GroupAction.Transitive

/-!
# Orthonormal frames as homogeneous spaces of unitary groups

For `𝕜 = ℝ` or `ℂ` (any `RCLike 𝕜`), the unitary group `U(N)` acts on the orthonormal
`r`-frames `TauCeti.finiteOrthonormalFrame 𝕜 r N` of `𝕜^N` by applying a matrix to each vector of
the frame (`TauCeti.finiteOrthonormalFrame.unitaryMap`). This action commutes with the action of
`U(r)` by change of frame, and for `r ≤ N` it is transitive: an orthonormal frame extends to an
orthonormal basis, whose vectors are the columns of a unitary matrix. So every orthonormal frame
is the image `A • e` of the standard frame `e = (e₀, …, e_{r-1})`, made of the first `r` columns
of `A`. As `U(N)` is compact and the frames form a Hausdorff space, the orbit map induces a
homeomorphism

`U(N) ⧸ Stab(e) ≃ₜ V_r(𝕜^N)`

(`TauCeti.finiteOrthonormalFrame.unitaryQuotientHomeomorph`). For `N = r + m` the stabilizer of
the standard frame is the block-diagonal subgroup `diag(1_r, U(m))`
(`TauCeti.finiteOrthonormalFrame.range_fromBlocksOne_eq_unitaryStabilizer`), so this identifies
the frames with `U(r + m) / U(m)`. For `𝕜 = ℝ` this is `O(r + m) / O(m)`.

Over `ℝ`, the special orthogonal group `SO(N)` is already transitive when `r < N`: the sign of
the determinant can be corrected by a reflection in a coordinate not used by the standard frame.
This gives `SO(N) ⧸ Stab(e) ≃ₜ V_r(ℝ^N)`
(`TauCeti.finiteOrthonormalFrame.specialOrthogonalQuotientHomeomorph`), with stabilizer
`diag(1_r, SO(m))` when `N = r + m`. In particular the ordered orthonormal two-frames of `ℝⁿ`,
`n ≥ 3`, are `SO(n) / SO(n - 2)`, and those of `ℂⁿ`, `n ≥ 2`, are `U(n) / U(n - 2)`.

For full frames, `r = N`, the stabilizer is trivial: an orthonormal `N`-frame is a basis, so
`U(N)` acts freely on these frames (`TauCeti.finiteOrthonormalFrame.unitaryMap_left_injective`)
and the orbit map of the standard frame is a homeomorphism `U(N) ≃ₜ V_N(𝕜^N)`
(`TauCeti.finiteOrthonormalFrame.unitaryHomeomorph`). The determinant classifies the orbits of
the special unitary group: two frames `A • f` and `A' • f` lie in the same `SU(N)`-orbit exactly
when `det A = det A'` (`TauCeti.finiteOrthonormalFrame.exists_specialUnitary_unitaryMap_eq_iff`).
Over `ℝ`, where `SU(N) = SO(N)` and `det A = ±1`, combining this with the existence, for
`N ≥ 1`, of an orthogonal matrix `ρ` of determinant `-1` such as `diag(1, …, 1, -1)` shows that
the full frames form two `SO(N)`-orbits, `O(N) = SO(N) ⊔ ρ SO(N)`. For `N = 2` these are the
ordered orthonormal two-frames of the plane.

The action `TauCeti.finiteOrthonormalFrame.unitaryMulAction` and the standard frame
`TauCeti.finiteOrthonormalFrame.standard` are defined with the orthonormal frames in
`TauCeti.Topology.Grassmannian.Orthonormal`; the action is a definition rather than an instance.
The homeomorphisms are the topological orbit-stabilizer theorem
`TauCeti.quotientStabilizerHomeomorph` for these actions, and are equivariant.

## Main definitions

* `TauCeti.finiteOrthonormalFrame.unitaryStabilizer`,
  `TauCeti.finiteOrthonormalFrame.specialOrthogonalStabilizer`: the stabilizers of the standard
  frame.
* `TauCeti.finiteOrthonormalFrame.unitaryQuotientHomeomorph`,
  `TauCeti.finiteOrthonormalFrame.specialOrthogonalQuotientHomeomorph`: the frames as quotients
  of the unitary and special orthogonal groups.
* `TauCeti.finiteOrthonormalFrame.unitaryHomeomorph`: the full frames as the unitary group.

## Main results

* `TauCeti.finiteOrthonormalFrame.unitaryMap_standard_surjective`,
  `TauCeti.finiteOrthonormalFrame.specialOrthogonal_unitaryMap_standard_surjective`: transitivity.
* `TauCeti.finiteOrthonormalFrame.range_fromBlocksOne_eq_unitaryStabilizer`,
  `TauCeti.finiteOrthonormalFrame.range_fromBlocksOne_eq_specialOrthogonalStabilizer`: the
  stabilizers are the block-diagonal subgroups.
* `TauCeti.finiteOrthonormalFrame.unitaryMap_left_injective`: the action on full frames is free.
* `TauCeti.finiteOrthonormalFrame.exists_specialUnitary_unitaryMap_eq_iff`: the determinant
  classifies the `SU(N)`-orbits of full frames.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §5.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (Stiefel manifolds
  as homogeneous spaces).
-/

public noncomputable section

open Matrix Function Topology

namespace TauCeti

namespace finiteOrthonormalFrame

variable {𝕜 : Type*} [RCLike 𝕜] {r N : ℕ}

/-- **The unitary group acts transitively on orthonormal frames**: for `r ≤ N`, every orthonormal
`r`-frame of `𝕜^N` is the image of the standard frame under a unitary matrix. -/
theorem unitaryMap_standard_surjective (h : r ≤ N) :
    Surjective fun A : unitaryGroup (Fin N) 𝕜 ↦ unitaryMap A (standard 𝕜 h) := by
  intro f
  -- Extend the frame to an orthonormal basis `b` indexed by `Fin N`; its vectors are the columns
  -- of a unitary matrix.
  let v : Fin N → EuclideanSpace 𝕜 (Fin N) := fun k ↦
    if hk : (k : ℕ) < r then WithLp.toLp 2 (f.1 ⟨k, hk⟩) else 0
  have hv_castLE : ∀ i, v (Fin.castLE h i) = WithLp.toLp 2 (f.1 i) := fun i ↦ by
    simp [v, i.isLt]
  have hv : Orthonormal 𝕜 ((Set.range (Fin.castLE h)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    by_cases hij : i = j
    · subst hij
      simp [Set.domRestrict, hv_castLE, f.2.1 i]
    · have hne : (⟨Fin.castLE h i, i, rfl⟩ : Set.range (Fin.castLE h)) ≠ ⟨Fin.castLE h j, j, rfl⟩ :=
        fun e ↦ hij (Fin.castLE_injective h (congrArg Subtype.val e))
      simp [Set.domRestrict, hv_castLE, orthonormal_iff_ite.1 f.2 i j, hij, hne]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨⟨(EuclideanSpace.basisFun (Fin N) 𝕜).toBasis.toMatrix b,
    (EuclideanSpace.basisFun (Fin N) 𝕜).toMatrix_orthonormalBasis_mem_unitary b⟩, ?_⟩
  refine Subtype.ext <| funext fun i ↦ funext fun k ↦ ?_
  simp [Module.Basis.toMatrix_apply, hb _ ⟨i, rfl⟩, hv_castLE]

variable (𝕜) in
/-- The **stabilizer of the standard frame** in the unitary group: the unitary matrices whose
first `r` columns are the standard basis vectors. -/
def unitaryStabilizer (h : r ≤ N) : Subgroup (unitaryGroup (Fin N) 𝕜) :=
  letI := unitaryMulAction 𝕜 r N
  MulAction.stabilizer _ (standard 𝕜 h)

theorem mem_unitaryStabilizer_iff {h : r ≤ N} {A : unitaryGroup (Fin N) 𝕜} :
    A ∈ unitaryStabilizer 𝕜 h ↔ unitaryMap A (standard 𝕜 h) = standard 𝕜 h :=
  Iff.rfl

variable (𝕜) in
/-- **Orthonormal frames form a homogeneous space of the unitary group**: for `r ≤ N`, the map
`A ↦ A • e` sending a unitary matrix to the image of the standard frame `e` induces a
homeomorphism `U(N) ⧸ Stab(e) ≃ₜ V_r(𝕜^N)`. -/
def unitaryQuotientHomeomorph (h : r ≤ N) :
    unitaryGroup (Fin N) 𝕜 ⧸ unitaryStabilizer 𝕜 h ≃ₜ finiteOrthonormalFrame 𝕜 r N :=
  letI := unitaryMulAction 𝕜 r N
  haveI : MulAction.IsPretransitive (unitaryGroup (Fin N) 𝕜) (finiteOrthonormalFrame 𝕜 r N) :=
    .of_orbit (unitaryMap_standard_surjective h)
  quotientStabilizerHomeomorph _ (standard 𝕜 h)
    (continuous_unitaryMap.comp (continuous_id.prodMk continuous_const))

@[simp]
theorem unitaryQuotientHomeomorph_mk (h : r ≤ N) (A : unitaryGroup (Fin N) 𝕜) :
    unitaryQuotientHomeomorph 𝕜 h (QuotientGroup.mk A) = unitaryMap A (standard 𝕜 h) :=
  letI := unitaryMulAction 𝕜 r N
  haveI : MulAction.IsPretransitive (unitaryGroup (Fin N) 𝕜) (finiteOrthonormalFrame 𝕜 r N) :=
    .of_orbit (unitaryMap_standard_surjective h)
  quotientStabilizerHomeomorph_mk _ (standard 𝕜 h) _ A

/-- The homeomorphism `U(N) ⧸ Stab(e) ≃ₜ V_r(𝕜^N)` is equivariant: left multiplication of cosets
corresponds to applying a unitary matrix to frames. -/
theorem unitaryQuotientHomeomorph_smul (h : r ≤ N) (A : unitaryGroup (Fin N) 𝕜)
    (q : unitaryGroup (Fin N) 𝕜 ⧸ unitaryStabilizer 𝕜 h) :
    unitaryQuotientHomeomorph 𝕜 h (A • q) = unitaryMap A (unitaryQuotientHomeomorph 𝕜 h q) :=
  letI := unitaryMulAction 𝕜 r N
  haveI : MulAction.IsPretransitive (unitaryGroup (Fin N) 𝕜) (finiteOrthonormalFrame 𝕜 r N) :=
    .of_orbit (unitaryMap_standard_surjective h)
  quotientStabilizerHomeomorph_smul _ (standard 𝕜 h) _ A q

/-- The orbit map of the standard frame is a quotient map onto the orthonormal frames. -/
theorem isQuotientMap_unitaryMap_standard (h : r ≤ N) :
    IsQuotientMap fun A : unitaryGroup (Fin N) 𝕜 ↦ unitaryMap A (standard 𝕜 h) :=
  funext (unitaryQuotientHomeomorph_mk (𝕜 := 𝕜) h) ▸
    (unitaryQuotientHomeomorph 𝕜 h).isQuotientMap.comp (QuotientGroup.isQuotientMap_mk _)

/-- **The stabilizer of the standard frame is the block-diagonal subgroup** `diag(1_r, U(m))` of
`U(r + m)`. So the orthonormal `r`-frames of `𝕜^(r + m)` are the homogeneous space
`U(r + m) / U(m)`. -/
theorem range_fromBlocksOne_eq_unitaryStabilizer (m : ℕ) :
    (UnitaryGroup.fromBlocksOne 𝕜 r m).range = unitaryStabilizer 𝕜 (Nat.le_add_right r m) := by
  ext A
  rw [UnitaryGroup.mem_range_fromBlocksOne_iff, mem_unitaryStabilizer_iff, Subtype.ext_iff,
    funext_iff, coe_unitaryMap, coe_standard]
  rfl

/-! ### Real frames and the special orthogonal group -/

/-- The **stabilizer of the standard real frame** in the special orthogonal group `SO(N)`. -/
def specialOrthogonalStabilizer (h : r ≤ N) : Subgroup (specialOrthogonalGroup (Fin N) ℝ) :=
  letI := specialOrthogonalMulAction r N
  MulAction.stabilizer _ (standard ℝ h)

theorem mem_specialOrthogonalStabilizer_iff {h : r ≤ N} {A : specialOrthogonalGroup (Fin N) ℝ} :
    A ∈ specialOrthogonalStabilizer h ↔ unitaryMap ⟨A.1, A.2.1⟩ (standard ℝ h) = standard ℝ h :=
  Iff.rfl

/-- **The special orthogonal group acts transitively on orthonormal real frames** of fewer than
`N` vectors: for `r < N`, every orthonormal `r`-frame of `ℝ^N` is the image of the standard frame
under a special orthogonal matrix. An orthogonal matrix of determinant `-1` is corrected by the
reflection in the last coordinate, which fixes the standard frame. -/
theorem specialOrthogonal_unitaryMap_standard_surjective (h : r < N) :
    Surjective fun A : specialOrthogonalGroup (Fin N) ℝ ↦
      unitaryMap ⟨A.1, A.2.1⟩ (standard ℝ h.le) := by
  intro f
  obtain ⟨A, rfl⟩ := unitaryMap_standard_surjective h.le f
  rcases mul_self_eq_one_iff.1 (by simpa using (det_of_mem_unitary A.2).2) with hA | hA
  · exact ⟨⟨A.1, A.2, hA⟩, rfl⟩
  -- The reflection `D` in the last coordinate `j`, which is not used by the standard frame.
  let j : Fin N := ⟨N - 1, by omega⟩
  let D : unitaryGroup (Fin N) ℝ := ⟨diagonal (Function.update 1 j (-1)),
    diagonal_mem_unitary.2 <| by
      rw [Unitary.mem_iff]
      constructor <;> ext k <;> rcases eq_or_ne k j with rfl | hk <;> simp [*]⟩
  have hD : unitaryMap D (standard ℝ h.le) = standard ℝ h.le := by
    refine Subtype.ext <| funext fun i ↦ ?_
    have hij : Fin.castLE h.le i ≠ j := fun hij ↦ by
      have := congrArg Fin.val hij
      simp only [Fin.val_castLE, j] at this
      omega
    simp [D, hij]
  have hdet : (A * D).1.det = 1 := by
    simp [D, hA, det_diagonal, Finset.prod_update_of_mem]
  exact ⟨⟨(A * D).1, (A * D).2, hdet⟩, (unitaryMap_mul A D _).trans (congrArg _ hD)⟩

/-- **Orthonormal real frames form a homogeneous space of the special orthogonal group**: for
`r < N`, the map `A ↦ A • e` sending a special orthogonal matrix to the image of the standard frame
`e` induces a homeomorphism `SO(N) ⧸ Stab(e) ≃ₜ V_r(ℝ^N)`. -/
def specialOrthogonalQuotientHomeomorph (h : r < N) :
    specialOrthogonalGroup (Fin N) ℝ ⧸ specialOrthogonalStabilizer h.le ≃ₜ
      finiteOrthonormalFrame ℝ r N :=
  letI := specialOrthogonalMulAction r N
  haveI : MulAction.IsPretransitive (specialOrthogonalGroup (Fin N) ℝ)
      (finiteOrthonormalFrame ℝ r N) :=
    .of_orbit (specialOrthogonal_unitaryMap_standard_surjective h)
  quotientStabilizerHomeomorph _ (standard ℝ h.le)
    (continuous_unitaryMap.comp ((continuous_subtype_val.subtype_mk _).prodMk continuous_const))

@[simp]
theorem specialOrthogonalQuotientHomeomorph_mk (h : r < N)
    (A : specialOrthogonalGroup (Fin N) ℝ) :
    specialOrthogonalQuotientHomeomorph h (QuotientGroup.mk A) =
      unitaryMap ⟨A.1, A.2.1⟩ (standard ℝ h.le) :=
  letI := specialOrthogonalMulAction r N
  haveI : MulAction.IsPretransitive (specialOrthogonalGroup (Fin N) ℝ)
      (finiteOrthonormalFrame ℝ r N) :=
    .of_orbit (specialOrthogonal_unitaryMap_standard_surjective h)
  quotientStabilizerHomeomorph_mk _ (standard ℝ h.le) _ A

/-- The homeomorphism `SO(N) ⧸ Stab(e) ≃ₜ V_r(ℝ^N)` is equivariant: left multiplication of
cosets corresponds to applying a special orthogonal matrix to frames. -/
theorem specialOrthogonalQuotientHomeomorph_smul (h : r < N)
    (A : specialOrthogonalGroup (Fin N) ℝ)
    (q : specialOrthogonalGroup (Fin N) ℝ ⧸ specialOrthogonalStabilizer h.le) :
    specialOrthogonalQuotientHomeomorph h (A • q) =
      unitaryMap ⟨A.1, A.2.1⟩ (specialOrthogonalQuotientHomeomorph h q) :=
  letI := specialOrthogonalMulAction r N
  haveI : MulAction.IsPretransitive (specialOrthogonalGroup (Fin N) ℝ)
      (finiteOrthonormalFrame ℝ r N) :=
    .of_orbit (specialOrthogonal_unitaryMap_standard_surjective h)
  quotientStabilizerHomeomorph_smul _ (standard ℝ h.le) _ A q

/-- The orbit map of the standard real frame under `SO(N)` is a quotient map onto the
orthonormal frames, for `r < N`. -/
theorem isQuotientMap_specialOrthogonal_unitaryMap_standard (h : r < N) :
    IsQuotientMap fun A : specialOrthogonalGroup (Fin N) ℝ ↦
      unitaryMap ⟨A.1, A.2.1⟩ (standard ℝ h.le) :=
  funext (specialOrthogonalQuotientHomeomorph_mk h) ▸
    (specialOrthogonalQuotientHomeomorph h).isQuotientMap.comp (QuotientGroup.isQuotientMap_mk _)

/-- **The stabilizer of the standard real frame in `SO(r + m)` is the block-diagonal subgroup**
`diag(1_r, SO(m))`. So for `m ≥ 1` the orthonormal `r`-frames of `ℝ^(r + m)` are the homogeneous
space `SO(r + m) / SO(m)`; for instance the ordered orthonormal two-frames of `ℝⁿ`, `n ≥ 3`, are
`SO(n) / SO(n - 2)`. -/
theorem range_fromBlocksOne_eq_specialOrthogonalStabilizer (m : ℕ) :
    (SpecialOrthogonalGroup.fromBlocksOne ℝ r m).range =
      specialOrthogonalStabilizer (Nat.le_add_right r m) := by
  ext A
  rw [SpecialOrthogonalGroup.mem_range_fromBlocksOne_iff, mem_specialOrthogonalStabilizer_iff,
    Subtype.ext_iff, funext_iff, coe_unitaryMap, coe_standard]
  rfl

/-! ### Full frames -/

/-- **`U(N)` acts freely on orthonormal `N`-frames of `𝕜^N`**: such a frame is an orthonormal basis,
and a matrix is determined by its values on a basis. -/
theorem unitaryMap_left_injective (f : finiteOrthonormalFrame 𝕜 N N) :
    Injective fun A : unitaryGroup (Fin N) 𝕜 ↦ unitaryMap A f := by
  obtain ⟨B, rfl⟩ := unitaryMap_standard_surjective le_rfl f
  intro A A' h
  simp only [← unitaryMap_mul] at h
  -- The images of the standard frame are the columns of `A * B` and `A' * B`.
  have hcol : ((A * B : unitaryGroup (Fin N) 𝕜) : Matrix (Fin N) (Fin N) 𝕜) =
      (A' * B : unitaryGroup (Fin N) 𝕜) := by
    ext i j
    simpa [mulVec_single_one] using congrFun (congrFun (congrArg Subtype.val h) j) i
  exact mul_right_cancel (Subtype.ext hcol)

variable (𝕜 N) in
/-- **The orthonormal `N`-frames of `𝕜^N` are `U(N)`**: `A ↦ A • e`, sending a unitary matrix to
the image of the standard frame, the frame of its columns, is a homeomorphism. -/
def unitaryHomeomorph : unitaryGroup (Fin N) 𝕜 ≃ₜ finiteOrthonormalFrame 𝕜 N N :=
  (continuous_unitaryMap.comp (continuous_id.prodMk continuous_const)).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun A : unitaryGroup (Fin N) 𝕜 ↦ unitaryMap A (standard 𝕜 le_rfl))
      ⟨unitaryMap_left_injective _, unitaryMap_standard_surjective le_rfl⟩)

@[simp]
theorem unitaryHomeomorph_apply (A : unitaryGroup (Fin N) 𝕜) :
    unitaryHomeomorph 𝕜 N A = unitaryMap A (standard 𝕜 le_rfl) :=
  (rfl)

/-- The unitary matrix of a full frame is the matrix whose columns are the vectors of the
frame. -/
@[simp]
theorem coe_unitaryHomeomorph_symm_apply (f : finiteOrthonormalFrame 𝕜 N N) (i j : Fin N) :
    ((unitaryHomeomorph 𝕜 N).symm f : Matrix (Fin N) (Fin N) 𝕜) i j = f.1 j i := by
  obtain ⟨A, rfl⟩ := (unitaryHomeomorph 𝕜 N).surjective f
  rw [Homeomorph.symm_apply_apply]
  simp

/-- **The determinant classifies the `SU(N)`-orbits of orthonormal `N`-frames of `𝕜^N`**: the
frames `A • f` and `A' • f` lie in the same `SU(N)`-orbit exactly when the unitary matrices `A`
and `A'` have the same determinant. Over `ℝ`, where `SU(N) = SO(N)` and the determinant is `±1`,
this theorem together with an orthogonal matrix `ρ` of determinant `-1`, which exists for
`N ≥ 1`, gives two `SO(N)`-orbits; with `unitaryHomeomorph` this is the decomposition
`O(N) = SO(N) ⊔ ρ SO(N)` of the frames, and for `N = 2` it describes the ordered orthonormal
two-frames of the plane. -/
theorem exists_specialUnitary_unitaryMap_eq_iff (f : finiteOrthonormalFrame 𝕜 N N)
    (A A' : unitaryGroup (Fin N) 𝕜) :
    (∃ S : specialUnitaryGroup (Fin N) 𝕜,
        unitaryMap (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup S) (unitaryMap A f) =
          unitaryMap A' f) ↔
      (A : Matrix (Fin N) (Fin N) 𝕜).det = (A' : Matrix (Fin N) (Fin N) 𝕜).det := by
  constructor
  · rintro ⟨S, hS⟩
    rw [← unitaryMap_mul] at hS
    rw [← unitaryMap_left_injective f hS, Submonoid.coe_mul, det_mul]
    simp [(mem_specialUnitaryGroup_iff.1 S.2).2]
  · intro h
    -- `A' A⁻¹ = A' Aᴴ` is special unitary, since `det A' = det A` is a unit scalar.
    have hdet : ((A' * A⁻¹ : unitaryGroup (Fin N) 𝕜) : Matrix (Fin N) (Fin N) 𝕜).det = 1 := by
      simpa [← h, star_eq_conjTranspose, det_conjTranspose] using (det_of_mem_unitary A.2).2
    refine ⟨⟨(A' * A⁻¹ : unitaryGroup (Fin N) 𝕜), mem_specialUnitaryGroup_iff.2
      ⟨(A' * A⁻¹).2, hdet⟩⟩, ?_⟩
    -- The unitary matrix underlying this element of `SU(N)` is `A' * A⁻¹`.
    exact (unitaryMap_mul _ _ _).symm.trans
      (congrArg (unitaryMap · f) (inv_mul_cancel_right A' A))

end finiteOrthonormalFrame

end TauCeti
