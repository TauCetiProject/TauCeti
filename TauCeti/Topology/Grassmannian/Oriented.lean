/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic
public import TauCeti.Topology.Grassmannian.Plucker
public import TauCeti.Topology.Grassmannian.Tautological
public import TauCeti.Topology.SeparatedMap
public import TauCeti.Topology.VectorBundle.Orientation.Proper
public import TauCeti.Topology.VectorBundle.Orientation.Tautological

/-!
# Finite oriented real Grassmannians

For positive rank, the finite oriented Grassmannian is the orientation double cover of the
existing real tautological bundle. Its tautological bundle is pulled back along the
orientation-forgetting projection and has the orientation recorded by each point, supplied by
`TauCeti.VectorBundleOrientationCover.tautologicalOrientation`. The construction uses the
original finite Grassmannian and its original tautological bundle.

The forgetting map is a proper two-sheeted covering, so this carrier is compact. When the
rank equals the ambient dimension it still has two points, corresponding to the two
orientations of the whole space. Rank zero is excluded: its orientation cover has two points
over the one-point Grassmannian, whereas the canonically oriented rank-zero Grassmannian is
conventionally a point. This carrier is therefore defined only for positive rank.

A frame `f` spans an oriented plane `orientedFrameSpan f`: its span, oriented by the basis `f`.
This is continuous, and acting on `f` by a matrix `A` keeps the oriented plane exactly when
`det A > 0`, and otherwise reverses its orientation. On orthonormal frames it is surjective, and
two orthonormal frames span the same oriented plane exactly when they differ by a special
orthogonal matrix. Since orthonormal frames form a compact space and the oriented Grassmannian
is Hausdorff, the oriented Grassmannian is homeomorphic to the orbit space of the orthonormal
`r`-frames of `ℝᴺ` under the special orthogonal group `SO(r)`
(`TauCeti.finiteOrientedGrassmannian.specialOrthogonalOrbitHomeomorph`). The group acts by left
multiplication on the matrix whose rows are the frame vectors, so its orbits are the orbits of
the right action of `SO(r)` on the `N × r` matrices whose columns are the frame vectors.
Forgetting the orientation of `orientedFrameSpan f` gives the span of `f`, so this comparison
lies over the description of the finite Grassmannian by orthonormal frames modulo the orthogonal
group, `TauCeti.finiteGrassmannian.unitaryOrbitHomeomorph`.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §§5, 9.
-/

public section

noncomputable section

open Bundle Set Topology

namespace TauCeti

/-- The finite oriented real Grassmannian in positive rank, as the orientation double cover
of the tautological bundle on the finite real Grassmannian. -/
abbrev finiteOrientedGrassmannian (r : ℕ+) (N : ℕ) : Type :=
  VectorBundleOrientationCover (Fin r → ℝ) (finiteGrassmannian.Tautological ℝ r N) (Fin r)

namespace finiteOrientedGrassmannian

variable {r : ℕ+} {N : ℕ}

/-- Forget the orientation of an oriented plane. This is a continuous map to the existing
finite real Grassmannian. -/
abbrev forget : C(finiteOrientedGrassmannian r N, finiteGrassmannian ℝ r N) :=
  VectorBundleOrientationCover.projection

@[simp]
theorem forget_apply (p : finiteOrientedGrassmannian r N) : forget p = p.proj :=
  (rfl)

/-- Finite oriented Grassmannians are compact. -/
instance : CompactSpace (finiteOrientedGrassmannian r N) :=
  VectorBundleOrientationCover.compactSpace (by simp)

/-- The oriented tautological bundle is the pullback of the original tautological bundle along
orientation forgetting. Its fibre over an oriented plane is that same plane. -/
abbrev Tautological (r : ℕ+) (N : ℕ) : finiteOrientedGrassmannian r N → Type :=
  (forget : finiteOrientedGrassmannian r N → finiteGrassmannian ℝ r N) *ᵖ
    (finiteGrassmannian.Tautological ℝ r N)

/-- In full ambient rank the oriented Grassmannian has two points, rather than one. -/
theorem encard_univ_fullRank :
    (univ : Set (finiteOrientedGrassmannian r r)).encard = 2 := by
  obtain ⟨V⟩ := (finiteGrassmannian.nonempty_iff_le (𝕜 := ℝ) (r := r) (N := r)).2 le_rfl
  have h : (forget : finiteOrientedGrassmannian r r → finiteGrassmannian ℝ r r) ⁻¹' {V} = univ := by
    ext p
    simp [Subsingleton.elim p.proj V]
  rw [← h]
  exact VectorBundleOrientationCover.encard_preimage_proj_singleton (by simp) V

/-- The finite oriented Grassmannians are Hausdorff, being covering spaces of Hausdorff
spaces. -/
instance : T2Space (finiteOrientedGrassmannian r N) :=
  (VectorBundleOrientationCover.isCoveringMap_proj (by simp)).t2Space

open finiteGrassmannian

/-- The oriented plane spanned by a frame: the span of `f`, oriented by the basis `f`. -/
noncomputable def orientedFrameSpan (f : finiteFullRankFrame ℝ r N) :
    finiteOrientedGrassmannian r N :=
  ⟨frameSpan f, (frameBasis f rfl).orientation⟩

/-- Forgetting the orientation of the oriented span of a frame gives its span. -/
@[simp]
theorem proj_orientedFrameSpan (f : finiteFullRankFrame ℝ r N) :
    (orientedFrameSpan f).proj = frameSpan f :=
  (rfl)

/-- The oriented span of a frame `f`, written over any point `V` equal to the span of `f`. -/
theorem orientedFrameSpan_eq_mk (f : finiteFullRankFrame ℝ r N) {V : finiteGrassmannian ℝ r N}
    (hV : frameSpan f = V) : orientedFrameSpan f = ⟨V, (frameBasis f hV).orientation⟩ := by
  subst hV
  rfl

/-- The oriented span of a frame depends continuously on the frame. -/
@[fun_prop]
theorem continuous_orientedFrameSpan :
    Continuous (orientedFrameSpan : finiteFullRankFrame ℝ r N → _) :=
  VectorBundleOrientationCover.continuous_mk_basis_orientation continuous_frameSpan _
    continuous_mk_frameBasis

/-- Acting on a frame by a matrix `A` keeps its oriented span exactly when `det A > 0`. -/
theorem orientedFrameSpan_smul_eq_iff (A : GL (Fin r) ℝ) (f : finiteFullRankFrame ℝ r N) :
    orientedFrameSpan (A • f) = orientedFrameSpan f ↔ 0 < (A : Matrix (Fin r) (Fin r) ℝ).det := by
  rw [orientedFrameSpan_eq_mk (A • f) (frameSpan_smul A f), orientedFrameSpan_eq_mk f rfl,
    VectorBundleOrientationCover.mk_eq_mk_iff, eq_comm, Module.Basis.orientation_eq_iff_det_pos,
    det_frameBasis_smul]

/-- Acting on a frame by a matrix of negative determinant reverses the orientation of its
oriented span. -/
theorem orientedFrameSpan_smul_of_det_neg {A : GL (Fin r) ℝ}
    (hA : (A : Matrix (Fin r) (Fin r) ℝ).det < 0) (f : finiteFullRankFrame ℝ r N) :
    orientedFrameSpan (A • f) = VectorBundleOrientationCover.deck (orientedFrameSpan f) :=
  (VectorBundleOrientationCover.eq_or_eq_deck (by simp) (frameSpan_smul A f)).resolve_left
    fun h ↦ hA.not_gt ((orientedFrameSpan_smul_eq_iff A f).1 h)

/-- Two orthonormal frames span the same oriented plane exactly when they lie in the same orbit
of the special orthogonal group. -/
theorem orientedFrameSpan_toFullRankFrame_eq_iff {f g : finiteOrthonormalFrame ℝ r N} :
    orientedFrameSpan f.toFullRankFrame = orientedFrameSpan g.toFullRankFrame ↔
      g ∈ MulAction.orbit (Matrix.specialOrthogonalGroup (Fin r) ℝ) f := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- The frames differ by an orthogonal matrix, whose determinant `±1` is positive.
    obtain ⟨A, rfl⟩ := frameSpan_toFullRankFrame_eq_iff.1
      (congrArg VectorBundleOrientationCover.proj h)
    rw [finiteOrthonormalFrame.toFullRankFrame_smul, eq_comm, orientedFrameSpan_smul_eq_iff,
      Unitary.val_toUnits_apply] at h
    have hsq := (Matrix.det_of_mem_unitary A.2).2
    rw [star_trivial] at hsq
    have hdet : (A : Matrix (Fin r) (Fin r) ℝ).det = 1 := by nlinarith
    refine ⟨⟨A, Matrix.mem_specialUnitaryGroup_iff.2 ⟨A.2, hdet⟩⟩, ?_⟩
    dsimp only
    rw [finiteOrthonormalFrame.specialUnitaryGroup_smul_def]
    exact congrArg (· • f) (Subtype.ext (Submonoid.coe_inclusion _ _))
  · rintro ⟨A, rfl⟩
    dsimp only
    rw [finiteOrthonormalFrame.specialUnitaryGroup_smul_def,
      finiteOrthonormalFrame.toFullRankFrame_smul, eq_comm, orientedFrameSpan_smul_eq_iff]
    simp [(Matrix.mem_specialUnitaryGroup_iff.1 A.2).2]

/-- Every oriented plane is spanned by an orthonormal frame. -/
theorem surjective_orientedFrameSpan_toFullRankFrame :
    Function.Surjective fun f : finiteOrthonormalFrame ℝ r N ↦
      orientedFrameSpan f.toFullRankFrame := by
  intro p
  obtain ⟨f, hf⟩ := frameSpan_toFullRankFrame_surjective p.proj
  rcases VectorBundleOrientationCover.eq_or_eq_deck (by simp)
      (p := orientedFrameSpan f.toFullRankFrame) (q := p) hf.symm with h | h
  · exact ⟨f, h.symm⟩
  -- Otherwise reverse the orientation by the reflection `A` negating the first frame vector.
  let i₀ : Fin r := ⟨0, r.pos⟩
  let d : Fin r → ℝ := Function.update 1 i₀ (-1)
  have hd (i : Fin r) : d i * d i = 1 := by
    by_cases hi : i = i₀
    · simp [d, hi]
    · simp [d, Function.update_of_ne hi]
  let A : Matrix.unitaryGroup (Fin r) ℝ := ⟨Matrix.diagonal d, Matrix.mem_unitaryGroup_iff.2 <| by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, star_trivial,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext hd)⟩
  have hA : (Unitary.toUnits A : Matrix (Fin r) (Fin r) ℝ).det < 0 := by
    simp [A, d, Matrix.det_diagonal, Finset.prod_update_of_mem]
  refine ⟨A • f, ?_⟩
  dsimp only
  rw [finiteOrthonormalFrame.toFullRankFrame_smul, orientedFrameSpan_smul_of_det_neg hA, h]

/-- The oriented span map on orthonormal frames is a quotient map: it is a continuous surjection
from a compact space onto a Hausdorff space. -/
theorem isQuotientMap_orientedFrameSpan_toFullRankFrame :
    IsQuotientMap fun f : finiteOrthonormalFrame ℝ r N ↦ orientedFrameSpan f.toFullRankFrame :=
  .of_surjective_continuous surjective_orientedFrameSpan_toFullRankFrame
    (continuous_orientedFrameSpan.comp finiteOrthonormalFrame.continuous_toFullRankFrame)

variable (r N) in
/-- The finite oriented Grassmannian is homeomorphic to the space of orbits of orthonormal frames
under the special orthogonal group, by taking the oriented span of a representative frame. -/
noncomputable def specialOrthogonalOrbitHomeomorph :
    MulAction.orbitRel.Quotient (Matrix.specialOrthogonalGroup (Fin r) ℝ)
        (finiteOrthonormalFrame ℝ r N) ≃ₜ finiteOrientedGrassmannian r N :=
  (Homeomorph.Quotient.congrRight
    (r' := Setoid.ker fun f : finiteOrthonormalFrame ℝ r N ↦ orientedFrameSpan f.toFullRankFrame)
    fun _ _ ↦ MulAction.orbitRel_apply.trans
      (orientedFrameSpan_toFullRankFrame_eq_iff.symm.trans eq_comm)).trans
    (IsQuotientMap.homeomorph
      (f := ⟨_, isQuotientMap_orientedFrameSpan_toFullRankFrame.continuous⟩)
      isQuotientMap_orientedFrameSpan_toFullRankFrame)

@[simp]
theorem specialOrthogonalOrbitHomeomorph_mk (f : finiteOrthonormalFrame ℝ r N) :
    specialOrthogonalOrbitHomeomorph r N (Quotient.mk _ f) =
      orientedFrameSpan f.toFullRankFrame :=
  (rfl)

@[simp]
theorem specialOrthogonalOrbitHomeomorph_symm_orientedFrameSpan
    (f : finiteOrthonormalFrame ℝ r N) :
    (specialOrthogonalOrbitHomeomorph r N).symm (orientedFrameSpan f.toFullRankFrame) =
      Quotient.mk _ f :=
  (specialOrthogonalOrbitHomeomorph r N).symm_apply_eq.2
    (specialOrthogonalOrbitHomeomorph_mk f).symm

end finiteOrientedGrassmannian

end TauCeti
