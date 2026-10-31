/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Topology.Grassmannian.Basic

/-!
# Orthonormal frames and compactness of finite Grassmannians

For `𝕜 = ℝ` or `ℂ` (more generally `RCLike 𝕜`), a frame `f : Fin r → Fin N → 𝕜` is orthonormal
when its vectors are orthonormal for the standard inner product, read through the native
coordinate transport `WithLp.toLp 2 : (Fin N → 𝕜) → EuclideanSpace 𝕜 (Fin N)`. Orthonormal
frames form the subspace `TauCeti.finiteOrthonormalFrame 𝕜 r N` of `Fin r → Fin N → 𝕜`; it is
closed and bounded, hence compact.

Every orthonormal frame is a frame (`TauCeti.finiteOrthonormalFrame.toFullRankFrame`). In the
other direction, Mathlib's normalized Gram-Schmidt process `InnerProductSpace.gramSchmidtNormed`
turns a frame into an orthonormal frame with the same span
(`TauCeti.finiteFullRankFrame.orthonormalize`). It is continuous and fixes orthonormal frames,
so the orthonormal frames are a retract of all frames. Consequently the span map restricted to
orthonormal frames is again a quotient map onto the finite Grassmannian
(`TauCeti.finiteGrassmannian.isQuotientMap_frameSpan_toFullRankFrame`), and the finite
Grassmannian is compact.

The unitary group `Matrix.unitaryGroup (Fin r) 𝕜` acts on orthonormal frames by left
multiplication of the matrix of row vectors, restricting the action of `GL (Fin r) 𝕜` on frames.
Two orthonormal frames span the same subspace exactly when they lie in the same unitary orbit,
because a change of basis between orthonormal families is unitary
(`Orthonormal.orthonormal_sum_smul_iff`). Hence the finite Grassmannian is homeomorphic to the
orbit space of orthonormal frames under the unitary group
(`TauCeti.finiteGrassmannian.unitaryOrbitHomeomorph`); for `𝕜 = ℝ` this is the orthogonal group.

The comparison of the frame-quotient description of Grassmannians with orthonormal frames follows
J. Milnor and J. Stasheff, *Characteristic Classes*, §5.
-/

public section

open Set Topology InnerProductSpace

namespace TauCeti

variable (𝕜 : Type*) [RCLike 𝕜] (r N : ℕ)

/-- The orthonormal `r`-frames in the coordinate space `Fin N → 𝕜`, orthonormal for the standard
inner product of `EuclideanSpace 𝕜 (Fin N)`, with the topology inherited from
`Fin r → Fin N → 𝕜`. -/
abbrev finiteOrthonormalFrame : Type _ :=
  {f : Fin r → Fin N → 𝕜 //
    Orthonormal 𝕜 fun i ↦ (WithLp.toLp 2 (f i) : EuclideanSpace 𝕜 (Fin N))}

namespace finiteOrthonormalFrame

variable {𝕜 r N}

/-- An orthonormal frame, regarded as a frame of linearly independent vectors. -/
def toFullRankFrame (f : finiteOrthonormalFrame 𝕜 r N) : finiteFullRankFrame 𝕜 r N :=
  ⟨f.1, f.2.linearIndependent.map' (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).toLinearMap
    (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).ker⟩

@[simp] theorem coe_toFullRankFrame (f : finiteOrthonormalFrame 𝕜 r N) :
    (f.toFullRankFrame : Fin r → Fin N → 𝕜) = f := (rfl)

@[fun_prop]
theorem continuous_toFullRankFrame :
    Continuous (toFullRankFrame : finiteOrthonormalFrame 𝕜 r N → _) :=
  continuous_subtype_val.subtype_mk _

/-- The orthonormal frames carry the subspace topology of the frames. -/
theorem isEmbedding_toFullRankFrame :
    IsEmbedding (toFullRankFrame : finiteOrthonormalFrame 𝕜 r N → _) :=
  .of_comp continuous_toFullRankFrame continuous_subtype_val IsEmbedding.subtypeVal

/-- The orthonormal frames form a compact subset of `Fin r → Fin N → 𝕜`: they are cut out by the
continuous equations `⟪f i, f j⟫ = if i = j then 1 else 0`, and every coordinate of a unit vector
has norm at most one. -/
theorem isCompact_setOf_orthonormal :
    IsCompact {f : Fin r → Fin N → 𝕜 |
      Orthonormal 𝕜 fun i ↦ (WithLp.toLp 2 (f i) : EuclideanSpace 𝕜 (Fin N))} := by
  classical
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · simp only [orthonormal_iff_ite, ofPred_forall]
    refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_eq ?_ continuous_const
    exact Continuous.inner (by fun_prop) (by fun_prop)
  · refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun f hf ↦ ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    refine fun i ↦ (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k ↦ ?_
    simpa [hf.1 i] using PiLp.norm_apply_le (WithLp.toLp 2 (f i) : EuclideanSpace 𝕜 (Fin N)) k

instance : CompactSpace (finiteOrthonormalFrame 𝕜 r N) :=
  isCompact_iff_compactSpace.1 isCompact_setOf_orthonormal

/-- The unitary group acts on orthonormal frames by left multiplication of the matrix of row
vectors: `A • f` has `j`th vector `∑ i, A j i • f i`. -/
instance : SMul (Matrix.unitaryGroup (Fin r) 𝕜) (finiteOrthonormalFrame 𝕜 r N) where
  smul A f := ⟨fun j ↦ ∑ i, (A : Matrix (Fin r) (Fin r) 𝕜) j i • f.1 i, by
    simpa only [WithLp.toLp_sum, WithLp.toLp_smul] using (f.2.orthonormal_sum_smul_iff _).2 <| by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.1 A.2⟩

@[simp] theorem coe_smul (A : Matrix.unitaryGroup (Fin r) 𝕜) (f : finiteOrthonormalFrame 𝕜 r N) :
    ((A • f : finiteOrthonormalFrame 𝕜 r N) : Fin r → Fin N → 𝕜) =
      fun j ↦ ∑ i, (A : Matrix (Fin r) (Fin r) 𝕜) j i • f.1 i := (rfl)

/-- The action of the unitary group on orthonormal frames is the restriction of the action of the
general linear group on frames. -/
theorem toFullRankFrame_smul (A : Matrix.unitaryGroup (Fin r) 𝕜)
    (f : finiteOrthonormalFrame 𝕜 r N) :
    (A • f).toFullRankFrame = Unitary.toUnits A • f.toFullRankFrame := (rfl)

/-- Left multiplication of row vectors is an action of the unitary group on orthonormal
frames. -/
instance : MulAction (Matrix.unitaryGroup (Fin r) 𝕜) (finiteOrthonormalFrame 𝕜 r N) where
  one_smul f := by
    ext j : 2
    simp [Matrix.one_apply]
  mul_smul A B f := by
    ext j : 2
    simp only [coe_smul, Submonoid.coe_mul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
      smul_smul]
    exact Finset.sum_comm

/-- Each unitary matrix acts continuously on orthonormal frames. -/
instance : ContinuousConstSMul (Matrix.unitaryGroup (Fin r) 𝕜) (finiteOrthonormalFrame 𝕜 r N) where
  continuous_const_smul A :=
    isEmbedding_toFullRankFrame.continuous_iff.2 <| by
      simpa only [Function.comp_def, toFullRankFrame_smul] using
        (continuous_const_smul (Unitary.toUnits A)).comp continuous_toFullRankFrame

end finiteOrthonormalFrame

namespace finiteFullRankFrame

variable {𝕜 r N}

/-- The vectors of a frame, transported to `EuclideanSpace 𝕜 (Fin N)`, are linearly
independent. -/
theorem linearIndependent_toLp (f : finiteFullRankFrame 𝕜 r N) :
    LinearIndependent 𝕜 fun i ↦ (WithLp.toLp 2 (f.1 i) : EuclideanSpace 𝕜 (Fin N)) :=
  f.2.map' (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm.toLinearMap
    (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm.ker

/-- The orthonormal frame obtained from a frame by the normalized Gram-Schmidt process for the
standard inner product of `EuclideanSpace 𝕜 (Fin N)`. -/
noncomputable def orthonormalize (f : finiteFullRankFrame 𝕜 r N) : finiteOrthonormalFrame 𝕜 r N :=
  ⟨fun i ↦ WithLp.ofLp (gramSchmidtNormed 𝕜
      (fun j ↦ (WithLp.toLp 2 (f.1 j) : EuclideanSpace 𝕜 (Fin N))) i), by
    simpa only [WithLp.toLp_ofLp] using gramSchmidtNormed_orthonormal f.linearIndependent_toLp⟩

theorem coe_orthonormalize (f : finiteFullRankFrame 𝕜 r N) :
    (orthonormalize f : Fin r → Fin N → 𝕜) = fun i ↦ WithLp.ofLp (gramSchmidtNormed 𝕜
      (fun j ↦ (WithLp.toLp 2 (f.1 j) : EuclideanSpace 𝕜 (Fin N))) i) := (rfl)

/-- Gram-Schmidt orthonormalization depends continuously on the frame. -/
@[fun_prop]
theorem continuous_orthonormalize :
    Continuous (orthonormalize : finiteFullRankFrame 𝕜 r N → _) :=
  .subtype_mk (continuous_pi fun i ↦ (PiLp.continuous_ofLp 2 _).comp <|
    Continuous.gramSchmidtNormed
      (v := fun j (f : finiteFullRankFrame 𝕜 r N) ↦
        (WithLp.toLp 2 (f.1 j) : EuclideanSpace 𝕜 (Fin N)))
      (fun j ↦ (PiLp.continuous_toLp 2 _).comp <|
        (continuous_apply j).comp continuous_subtype_val) linearIndependent_toLp i) _

/-- Gram-Schmidt orthonormalization does not change the span of a frame. -/
@[simp] theorem span_range_orthonormalize (f : finiteFullRankFrame 𝕜 r N) :
    Submodule.span 𝕜 (range (orthonormalize f).1) = Submodule.span 𝕜 (range f.1) := by
  have h := congrArg (Submodule.map (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).toLinearMap)
    ((span_gramSchmidtNormed_range (𝕜 := 𝕜)
      (fun j ↦ (WithLp.toLp 2 (f.1 j) : EuclideanSpace 𝕜 (Fin N)))).trans (span_gramSchmidt 𝕜 _))
  simpa only [Submodule.map_span, ← range_comp, LinearEquiv.coe_coe, WithLp.coe_linearEquiv,
    Function.comp_def, WithLp.ofLp_toLp, coe_orthonormalize] using h

end finiteFullRankFrame

namespace finiteOrthonormalFrame

variable {𝕜 r N}

/-- Gram-Schmidt orthonormalization fixes orthonormal frames, so orthonormal frames are a retract
of all frames. -/
@[simp] theorem orthonormalize_toFullRankFrame (f : finiteOrthonormalFrame 𝕜 r N) :
    f.toFullRankFrame.orthonormalize = f := by
  refine Subtype.ext <| funext fun i ↦ ?_
  apply WithLp.toLp_injective 2
  have hgs : gramSchmidt 𝕜 (fun j ↦ (WithLp.toLp 2 (f.1 j) : EuclideanSpace 𝕜 (Fin N))) =
      fun j ↦ WithLp.toLp 2 (f.1 j) :=
    gramSchmidt_of_orthogonal 𝕜 fun _ _ hij ↦ f.2.2 hij
  simp [finiteFullRankFrame.coe_orthonormalize, gramSchmidtNormed, hgs, f.2.1 i]

end finiteOrthonormalFrame

namespace finiteGrassmannian

variable {𝕜 r N}

/-- Gram-Schmidt orthonormalization does not change the span of a frame. -/
@[simp] theorem frameSpan_toFullRankFrame_orthonormalize (f : finiteFullRankFrame 𝕜 r N) :
    frameSpan f.orthonormalize.toFullRankFrame = frameSpan f := by
  rw [Subtype.ext_iff, coe_frameSpan, coe_frameSpan, finiteOrthonormalFrame.coe_toFullRankFrame]
  exact f.span_range_orthonormalize

/-- Every `r`-dimensional subspace of `Fin N → 𝕜` is spanned by an orthonormal frame. -/
theorem frameSpan_toFullRankFrame_surjective :
    Function.Surjective fun f : finiteOrthonormalFrame 𝕜 r N ↦ frameSpan f.toFullRankFrame :=
  fun V ↦
    let ⟨f, hf⟩ := frameSpan_surjective V
    ⟨f.orthonormalize, (frameSpan_toFullRankFrame_orthonormalize f).trans hf⟩

/-- The finite Grassmannian also carries the quotient topology of the span map on orthonormal
frames. -/
theorem isQuotientMap_frameSpan_toFullRankFrame :
    IsQuotientMap fun f : finiteOrthonormalFrame 𝕜 r N ↦ frameSpan f.toFullRankFrame :=
  IsQuotientMap.of_comp finiteFullRankFrame.continuous_orthonormalize (by fun_prop) <| by
    convert (isQuotientMap_frameSpan : IsQuotientMap (frameSpan : finiteFullRankFrame 𝕜 r N → _))
    exact funext frameSpan_toFullRankFrame_orthonormalize

/-- The finite real and complex Grassmannians are compact. -/
instance : CompactSpace (finiteGrassmannian 𝕜 r N) :=
  frameSpan_toFullRankFrame_surjective.compactSpace (by fun_prop)

@[simp] theorem frameSpan_toFullRankFrame_smul (A : Matrix.unitaryGroup (Fin r) 𝕜)
    (f : finiteOrthonormalFrame 𝕜 r N) :
    frameSpan (A • f).toFullRankFrame = frameSpan f.toFullRankFrame := by
  rw [finiteOrthonormalFrame.toFullRankFrame_smul, frameSpan_smul]

/-- Two orthonormal frames span the same subspace exactly when they lie in the same orbit of the
unitary group. -/
theorem frameSpan_toFullRankFrame_eq_iff {f g : finiteOrthonormalFrame 𝕜 r N} :
    frameSpan f.toFullRankFrame = frameSpan g.toFullRankFrame ↔
      g ∈ MulAction.orbit (Matrix.unitaryGroup (Fin r) 𝕜) f := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- The change of frame is invertible; it is unitary because both frames are orthonormal.
    obtain ⟨A, hA : A • f.toFullRankFrame = g.toFullRankFrame⟩ := frameSpan_eq_frameSpan_iff.1 h
    have hcoe : g.1 = fun j ↦ ∑ i, (A : Matrix (Fin r) (Fin r) 𝕜) j i • f.1 i :=
      (congrArg Subtype.val hA).symm.trans (finiteFullRankFrame.coe_smul A _)
    have hmem : (A : Matrix (Fin r) (Fin r) 𝕜) ∈ Matrix.unitaryGroup (Fin r) 𝕜 := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        ← f.2.orthonormal_sum_smul_iff]
      simpa only [hcoe, WithLp.toLp_sum, WithLp.toLp_smul] using g.2
    exact ⟨⟨A, hmem⟩, Subtype.ext hcoe.symm⟩
  · rintro ⟨A, rfl⟩
    exact (frameSpan_toFullRankFrame_smul A f).symm

variable (𝕜 r N) in
/-- The finite Grassmannian is homeomorphic to the space of orbits of orthonormal frames under the
unitary group, by taking the span of a representative frame. -/
noncomputable def unitaryOrbitHomeomorph :
    MulAction.orbitRel.Quotient (Matrix.unitaryGroup (Fin r) 𝕜) (finiteOrthonormalFrame 𝕜 r N) ≃ₜ
      finiteGrassmannian 𝕜 r N :=
  (Homeomorph.Quotient.congrRight
    (r' := Setoid.ker fun f : finiteOrthonormalFrame 𝕜 r N ↦ frameSpan f.toFullRankFrame)
    fun _ _ ↦ MulAction.orbitRel_apply.trans
      (frameSpan_toFullRankFrame_eq_iff.symm.trans eq_comm)).trans
    (IsQuotientMap.homeomorph (f := ⟨_, by fun_prop⟩) isQuotientMap_frameSpan_toFullRankFrame)

@[simp] theorem unitaryOrbitHomeomorph_mk (f : finiteOrthonormalFrame 𝕜 r N) :
    unitaryOrbitHomeomorph 𝕜 r N (Quotient.mk _ f) = frameSpan f.toFullRankFrame := (rfl)

@[simp] theorem unitaryOrbitHomeomorph_symm_frameSpan (f : finiteOrthonormalFrame 𝕜 r N) :
    (unitaryOrbitHomeomorph 𝕜 r N).symm (frameSpan f.toFullRankFrame) = Quotient.mk _ f :=
  (unitaryOrbitHomeomorph 𝕜 r N).symm_apply_eq.2 (unitaryOrbitHomeomorph_mk f).symm

end finiteGrassmannian

end TauCeti
