/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
import TauCeti.Topology.VectorBundle.OrthonormalFrame.Reduction
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

/-!
# Unitary frames of a fibrewise orthogonal complex structure

Let `E → B` be a continuous Riemannian vector bundle with model fibre `F`, and let `J` be a
fibrewise orthogonal complex structure on `E`: a linear isometry `J b` of each fibre with
`J b (J b v) = -v`. Let `V` be a real inner product space with an orthogonal complex structure
`J₀`, an element of the orthogonal group `unitary (V →L[ℝ] V)`. An orthonormal frame
`φ : V ≃ₗᵢ[ℝ] E b` is *unitary* when it carries `J₀` to `J b`, `φ (J₀ v) = J b (φ v)`. The unitary
frames form the subset `TauCeti.OrthonormalFrameBundle.unitaryFrames F J J₀` of the orthonormal
frame bundle. For an almost Hermitian four-manifold, with `E` its tangent bundle and `J` its
almost complex structure, these are the unitary frames whose bundle is the reduction of the
structure group of the orthonormal frame bundle from `O(4)` to `U(2)`.

Acting by an orthogonal transformation `g` of `V` keeps a unitary frame unitary exactly when `g`
commutes with `J₀` (`TauCeti.OrthonormalFrameBundle.smul_mem_unitaryFrames_iff`). So the
centralizer of `J₀` in the orthogonal group, the unitary group `U(V, J₀)`, acts on the unitary
frames on the right, continuously, freely
(`TauCeti.OrthonormalFrameBundle.unitaryFrames_smul_eq_self_iff`) and transitively on each fibre
(`TauCeti.OrthonormalFrameBundle.exists_unitaryFrames_smul_eq_iff`).

In rank four, when `J` is continuous on the total space, the unitary frames are locally trivial
with fibre `U(V, J₀)`, by trivializations equivariant for the action
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_unitaryFrames`). Over the base set of a
linear trivialization of `E`, read `J` in the local Gram–Schmidt orthonormal frame `σ`: this gives
a continuous family `K y = σ_y⁻¹ ∘ J y ∘ σ_y` of orthogonal complex structures on `V`. For a unit
vector `a` and a vector `c` outside the complex line of `a`, the vectors
`(a, K a, u, K u)`, with `u` the normalized component of `c` orthogonal to `a` and `K a`, form an
orthonormal basis adapted to `K` (`ContinuousLinearMap.adaptedFourBasis`), depending continuously
on `K` while `c` stays outside that complex line. Matching it with an adapted orthonormal basis of
`(V, J₀)` (`OrthonormalBasis.unitaryToAdaptedFourBasis`) corrects `σ` to a continuous local unitary
frame.
As for the positively oriented frames
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_orientedFrames`), dividing by the corrected
frame trivializes the unitary frames, through the construction shared by such reductions
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_of_continuousOn_smul_mem`).

## Main definitions

* `TauCeti.OrthonormalFrameBundle.unitaryFrames F J J₀`: the orthonormal frames carrying `J₀` to
  `J`.
* The right action of `Subgroup.centralizer {J₀}` on `unitaryFrames F J J₀`.

## Main results

* `TauCeti.OrthonormalFrameBundle.smul_mem_unitaryFrames_iff`: an orthogonal transformation keeps
  a unitary frame unitary exactly when it commutes with `J₀`.
* `TauCeti.OrthonormalFrameBundle.unitaryFrames_smul_eq_self_iff`,
  `TauCeti.OrthonormalFrameBundle.exists_unitaryFrames_smul_eq_iff`: the action is free, and
  transitive on fibres.
* `TauCeti.OrthonormalFrameBundle.exists_trivialization_unitaryFrames`: in rank four the unitary
  frames are locally trivial with fibre the centralizer of `J₀`, equivariantly for the action.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Interscience, 1969,
  Chapter IX, §4 (the bundle of unitary frames of an almost Hermitian manifold).
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D
  (the reduction of the structure group to `U(n)` given by an almost complex structure).
-/

public section

noncomputable section

open Bundle Set Module MulOpposite
open scoped Topology RealInnerProductSpace

namespace TauCeti.OrthonormalFrameBundle

section Unitary

variable {B : Type*} {F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] (J : ∀ b, E b ≃ₗᵢ[ℝ] E b) (J₀ : unitary (V →L[ℝ] V))

variable (F) in
/-- The unitary frames of a fibrewise complex structure `J` on `E`, modelled on `(V, J₀)`: the
orthonormal frames `φ : V ≃ₗᵢ[ℝ] E b` carrying `J₀` to `J b`, `φ (J₀ v) = J b (φ v)`. -/
def unitaryFrames : Set (OrthonormalFrameBundle ℝ F E V) :=
  {p | ∀ v, p.frame ((J₀ : V →L[ℝ] V) v) = J p.proj (p.frame v)}

variable {J J₀}

/-- A frame is unitary when it carries `J₀` to `J`. -/
@[simp]
theorem mem_unitaryFrames_iff {p : OrthonormalFrameBundle ℝ F E V} :
    p ∈ unitaryFrames F J J₀ ↔ ∀ v, p.frame ((J₀ : V →L[ℝ] V) v) = J p.proj (p.frame v) :=
  Iff.rfl

/-- The frame `φ` over `y` is unitary when it carries `J₀` to `J y`. -/
theorem mk_mem_unitaryFrames_iff {y : B} {φ : V ≃ₗᵢ[ℝ] E y} :
    (⟨y, φ⟩ : OrthonormalFrameBundle ℝ F E V) ∈ unitaryFrames F J J₀ ↔
      ∀ v, φ ((J₀ : V →L[ℝ] V) v) = J y (φ v) :=
  Iff.rfl

/-- An orthogonal transformation `g` of `V` keeps a unitary frame unitary exactly when `g`
commutes with `J₀`. -/
theorem smul_mem_unitaryFrames_iff {p : OrthonormalFrameBundle ℝ F E V}
    (hp : p ∈ unitaryFrames F J J₀) {g : unitary (V →L[ℝ] V)} :
    op g • p ∈ unitaryFrames F J J₀ ↔ g ∈ Subgroup.centralizer {J₀} := by
  rw [Subgroup.mem_centralizer_singleton_iff, commute_iff_eq, ← Subtype.coe_inj,
    Submonoid.coe_mul, Submonoid.coe_mul, ContinuousLinearMap.ext_iff]
  simp only [mem_unitaryFrames_iff, frame_smul_apply, unop_op, proj_smul,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  -- Both conditions compare `p.frame (g (J₀ v))` with `p.frame (J₀ (g v)) = J (p.frame (g v))`.
  refine forall_congr' fun v ↦ ?_
  rw [← hp, p.frame.injective.eq_iff]

/-- Two unitary frames over the same base point differ by an orthogonal transformation commuting
with `J₀`. -/
theorem exists_mem_centralizer_smul_eq {p q : OrthonormalFrameBundle ℝ F E V}
    (hp : p ∈ unitaryFrames F J J₀) (hq : q ∈ unitaryFrames F J J₀) (h : p.proj = q.proj) :
    ∃ g ∈ Subgroup.centralizer {J₀}, op g • p = q := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_iff.2 h
  exact ⟨g, (smul_mem_unitaryFrames_iff hp).1 hq, rfl⟩

/-- The right action of the centralizer of `J₀`, the unitary group `U(V, J₀)`, on the unitary
frames, by precomposition. -/
instance : MulAction (Subgroup.centralizer {J₀})ᵐᵒᵖ (unitaryFrames F J J₀) where
  smul g p := ⟨op (g.unop : unitary (V →L[ℝ] V)) • p.val,
    (smul_mem_unitaryFrames_iff p.property).2 g.unop.property⟩
  one_smul p := Subtype.ext (one_smul _ p.val)
  mul_smul g h p := Subtype.ext (mul_smul (op (g.unop : unitary (V →L[ℝ] V)))
    (op (h.unop : unitary (V →L[ℝ] V))) p.val)

/-- The action on unitary frames is the action on all orthonormal frames. -/
@[simp]
theorem coe_unitaryFrames_smul (g : (Subgroup.centralizer {J₀})ᵐᵒᵖ) (p : unitaryFrames F J J₀) :
    ((g • p : unitaryFrames F J J₀) : OrthonormalFrameBundle ℝ F E V) =
      op (g.unop : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle ℝ F E V) :=
  rfl

/-- The action of the centralizer of `J₀` on unitary frames is free. -/
@[simp↓]
theorem unitaryFrames_smul_eq_self_iff {g : Subgroup.centralizer {J₀}} {p : unitaryFrames F J J₀} :
    op g • p = p ↔ g = 1 := by
  rw [← Subtype.coe_inj, coe_unitaryFrames_smul, unop_op, smul_eq_self_iff,
    OneMemClass.coe_eq_one]

/-- The action of the centralizer of `J₀` on unitary frames is transitive on fibres: two unitary
frames differ by an element of the centralizer exactly when they lie over the same base point. -/
theorem exists_unitaryFrames_smul_eq_iff {p q : unitaryFrames F J J₀} :
    (∃ g : Subgroup.centralizer {J₀}, op g • p = q) ↔ p.val.proj = q.val.proj := by
  refine ⟨fun ⟨g, h⟩ ↦ by rw [← h, coe_unitaryFrames_smul, proj_smul], fun h ↦ ?_⟩
  obtain ⟨g, hg, hgq⟩ := exists_mem_centralizer_smul_eq p.property q.property h
  exact ⟨⟨g, hg⟩, Subtype.ext hgq⟩

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E] [FiniteDimensional ℝ V]

/-- The right action of the centralizer of `J₀` on unitary frames is continuous. -/
instance : ContinuousSMul (Subgroup.centralizer {J₀})ᵐᵒᵖ (unitaryFrames F J J₀) where
  continuous_smul := ((continuous_op.comp ((continuous_subtypeVal.comp continuous_unop).comp
    continuous_fst)).smul (continuous_subtypeVal.comp continuous_snd)).subtype_mk _

end Unitary

/-! ### Local triviality in rank four -/

section Trivialization

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)]
  (J : ∀ b, E b ≃ₗᵢ[ℝ] E b) {J₀ : unitary (V →L[ℝ] V)}
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] (cF : Module.Basis (Fin 4) ℝ F)
  (β : OrthonormalBasis (Fin 4) ℝ V) (c : V)

/-- The complex structure `J` read in the local Gram–Schmidt frame `σ` of `e`:
`σ_y⁻¹ ∘ J y ∘ σ_y`. -/
private def localStructure (y : B) : unitary (V →L[ℝ] V) :=
  Unitary.linearIsometryEquiv.symm
    (((e.orthonormalFrameAt cF β y).trans (J y)).trans (e.orthonormalFrameAt cF β y).symm)

omit [ContinuousFiberNorm F E] [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)] in
/-- The local frame carries `localStructure` to `J`. -/
private theorem orthonormalFrameAt_localStructure (y : B) (v : V) :
    e.orthonormalFrameAt cF β y ((localStructure J e cF β y : V →L[ℝ] V) v) =
      J y (e.orthonormalFrameAt cF β y v) := by
  simp [localStructure]

omit [ContinuousFiberNorm F E] [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)] in
variable {J} in
private theorem localStructure_localStructure (hJ₂ : ∀ b v, J b (J b v) = -v) (y : B) (v : V) :
    (localStructure J e cF β y : V →L[ℝ] V) ((localStructure J e cF β y : V →L[ℝ] V) v) = -v :=
  (e.orthonormalFrameAt cF β y).injective (by
    rw [orthonormalFrameAt_localStructure, orthonormalFrameAt_localStructure, hJ₂, map_neg])

omit [Fact (finrank ℝ V = 4)] in
variable {J} in
/-- If `J` is continuous on the total space, `localStructure` is continuous over the base set
of `e`. -/
private theorem continuousOn_localStructure
    (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E)) :
    ContinuousOn (localStructure J e cF β) e.baseSet := by
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (continuousOn_clm_apply.2 fun v ↦ ?_)
  refine ((e.continuousOn_orthonormalFrameAt_symm cF β).comp
    (hJ.comp_continuousOn (e.continuousOn_totalSpaceMk_orthonormalFrameAt cF β v))
      fun y hy ↦ hy).congr fun y _ ↦ ?_
  simp [localStructure]

/-- The points of the base set of `e` over which `c` lies outside the complex line of `β 0` for
`localStructure`: there the local frame can be corrected to a unitary frame. -/
private def goodSet : Set B :=
  {y | y ∈ e.baseSet ∧
    (localStructure J e cF β y : V →L[ℝ] V).complexLineResidual (β 0) c ≠ 0}

omit [Fact (finrank ℝ V = 4)] in
variable {J} in
private theorem isOpen_goodSet
    (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E)) :
    IsOpen (goodSet J e cF β c) :=
  ((ContinuousLinearMap.continuous_complexLineResidual (β 0) c).comp_continuousOn
    (continuous_subtypeVal.comp_continuousOn
      (continuousOn_localStructure e cF β hJ))).isOpen_inter_preimage e.open_baseSet isOpen_ne

variable {J e cF β c}

/-- Over the good set, the local frame of `e`, corrected by `unitaryToAdaptedFourBasis`, is unitary,
when `β` is adapted to `J₀`. -/
private theorem smul_symm_apply_one_mem_unitaryFrames (hJ₂ : ∀ b v, J b (J b v) = -v)
    (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v) (hβ₁ : β 1 = (J₀ : V →L[ℝ] V) (β 0))
    (hβ₃ : β 3 = (J₀ : V →L[ℝ] V) (β 2)) {y : B} (hy : y ∈ goodSet J e cF β c) :
    op (β.unitaryToAdaptedFourBasis c (localStructure J e cF β y)) •
      (e.orthonormalFrameBundle cF β).toOpenPartialHomeomorph.symm (y, 1) ∈
        unitaryFrames F J J₀ := by
  simp only [e.orthonormalFrameBundle_symm_apply' cF β, op_one, one_smul, mem_unitaryFrames_iff,
    frame_smul_apply, proj_smul, unop_op]
  intro v
  rw [← OrthonormalBasis.apply_unitaryToAdaptedFourBasis_apply hJ₀ hβ₁ hβ₃
    (localStructure_localStructure e cF β hJ₂ y) hy.2 v]
  exact orthonormalFrameAt_localStructure J e cF β y _

/-- The correction `unitaryToAdaptedFourBasis` of `localStructure` is continuous over the good
set. -/
private theorem continuousOn_unitaryToAdaptedFourBasis_localStructure
    (hJ₂ : ∀ b v, J b (J b v) = -v)
    (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E)) :
    ContinuousOn (fun y ↦ β.unitaryToAdaptedFourBasis c (localStructure J e cF β y))
      (goodSet J e cF β c) :=
  (OrthonormalBasis.continuousOn_unitaryToAdaptedFourBasis β c).comp
    ((continuousOn_localStructure e cF β hJ).mono fun _ hy ↦ hy.1)
    fun y hy ↦ ⟨localStructure_localStructure e cF β hJ₂ y, hy.2⟩

end Trivialization

/-- In rank four, the unitary frames of a continuous fibrewise orthogonal complex structure `J` are
locally trivial with fibre the centralizer of `J₀` in the orthogonal group, the unitary group
`U(V, J₀) ≅ U(2)`, by trivializations equivariant for its right action. This is the local
triviality of the reduction of the orthonormal frame bundle of `E` from `O(4)` to `U(2)` given
by `J`. -/
theorem exists_trivialization_unitaryFrames {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
    [∀ x, InnerProductSpace ℝ (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    [VectorBundle ℝ F E] [ContinuousFiberNorm F E] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {J : ∀ b, E b ≃ₗᵢ[ℝ] E b}
    {J₀ : unitary (V →L[ℝ] V)}
    (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
    (hJ₂ : ∀ b v, J b (J b v) = -v) (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v)
    (hV : finrank ℝ V = 4) (hF : finrank ℝ F = 4) (x : B) :
    ∃ t : Trivialization (Subgroup.centralizer {J₀})
        (fun p : unitaryFrames F J J₀ ↦ (p : OrthonormalFrameBundle ℝ F E V).proj),
      x ∈ t.baseSet ∧ ∀ (g : Subgroup.centralizer {J₀}) (p : unitaryFrames F J J₀),
        (p : OrthonormalFrameBundle ℝ F E V).proj ∈ t.baseSet →
          t (op g • p) = ((t p).1, (t p).2 * g) := by
  have : Fact (finrank ℝ V = 4) := ⟨hV⟩
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  -- An orthonormal basis `β` of `V` adapted to `J₀`, `β 1 = J₀ (β 0)` and `β 3 = J₀ (β 2)`.
  let J₀' : AlmostComplexStructure V :=
    ⟨(J₀ : V →L[ℝ] V).toLinearMap, LinearMap.ext fun v ↦ by simpa using hJ₀ v⟩
  obtain ⟨β, -, hβ₁, hβ₃⟩ := AlmostComplexStructure.exists_unitary_orthonormalBasis_of_norm_eq_one
    (J := J₀') (Unitary.inner_map_map J₀)
    ((stdOrthonormalBasis ℝ V).orthonormal.1 ⟨0, by omega⟩)
  let e := trivializationAt F E x
  let cF := Module.finBasisOfFinrankEq ℝ F hF
  -- Some vector of `β` lies outside the complex line of `β 0` for `J` read at `x`.
  obtain ⟨j, hj⟩ := ContinuousLinearMap.exists_complexLineResidual_ne_zero (by omega)
    (localStructure J e cF β x : V →L[ℝ] V) (β 0) β.toBasis
  rw [OrthonormalBasis.coe_toBasis] at hj
  have hx : x ∈ goodSet J e cF β (β j) := ⟨mem_baseSet_trivializationAt F E x, hj⟩
  -- The local frame of `e`, corrected by `unitaryToAdaptedFourBasis`, is a continuous local unitary
  -- frame over the good set.
  obtain ⟨t, ht, hteq⟩ := exists_trivialization_of_continuousOn_smul_mem
    (U := goodSet J e cF β (β j))
    (fun _ hp _ ↦ smul_mem_unitaryFrames_iff hp)
    (fun _ hy ↦ (e.baseSet_orthonormalFrameBundle cF β).symm ▸ hy.1)
    (fun _ hy ↦ smul_symm_apply_one_mem_unitaryFrames hJ₂ hJ₀ hβ₁.symm hβ₃.symm hy)
    (isOpen_goodSet e cF β (β j) hJ)
    (continuousOn_unitaryToAdaptedFourBasis_localStructure hJ₂ hJ)
    hx
  exact ⟨t, ht ▸ hx, fun g p hp ↦
    (congrArg t (Subtype.ext (coe_unitaryFrames_smul _ _))).trans (hteq g p (ht ▸ hp))⟩

end TauCeti.OrthonormalFrameBundle
