/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Reduction
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Principal

/-!
# Local trivializations of reductions of the orthonormal frame bundle

Let `E → B` be a vector bundle with fibre inner products, let `V` be a real inner product space,
and let `T` be a trivialization of the orthonormal frame bundle of `E` modelled on `V` that is
*equivariant*, `T.orthonormalFrameBundleFiber.IsEquivariant`: it turns the right action of the
orthogonal group `unitary (V →L[ℝ] V)` into right multiplication on the fibre coordinate. Over its
base set every frame is then the local frame `T.symm (y, 1)` acted on by its fibre coordinate
(`Bundle.Trivialization.op_snd_smul_symm_one`).

Let `H` be a subgroup of the orthogonal group and `S` a set of frames such that, for `p ∈ S`,
`op g • p ∈ S` exactly when `g ∈ H` (`TauCeti.OrthonormalFrameBundle.SMulMemIff H S`). The
positively oriented frames of an oriented bundle with `H = SO(n)`, and the unitary frames of a
fibrewise complex structure with `H = U(n)`, are examples: `S` is then the total space of a
reduction of the structure group to `H`. The group `H` then acts on `S` on the right, continuously,
freely (`TauCeti.OrthonormalFrameBundle.SMulMemIff.smul_eq_self_iff`) and transitively on each
fibre (`TauCeti.OrthonormalFrameBundle.SMulMemIff.exists_smul_eq_iff`). If on an open subset `U`
of the base set of `T` the local frame can be corrected into `S` by a continuous map
`c : B → unitary (V →L[ℝ] V)`, that is `op (c y) • T.symm (y, 1) ∈ S`, then `S` is trivial over `U`
with fibre `H`, equivariantly for the right action of `H`
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_of_continuousOn_smul_mem`): a frame `p` of
`S` over `y` goes to `(y, (c y)⁻¹ * (T p).2)`, by the local step shared by all reductions of
structure group (`Bundle.Trivialization.exists_trivialization_of_continuousOn_symm_mem`). This is
how a continuous local section of the reduced frames trivializes a reduction of the structure
group.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.SMulMemIff H S`: an orthogonal transformation carries a frame of
  `S` into `S` exactly when it lies in `H`.
* The right action of `H` on `S`.

## Main results

* `TauCeti.OrthonormalFrameBundle.SMulMemIff.smul_eq_self_iff`,
  `TauCeti.OrthonormalFrameBundle.SMulMemIff.exists_smul_eq_iff`: the action of `H` on `S` is
  free, and transitive on fibres.
* `TauCeti.OrthonormalFrameBundle.exists_trivialization_of_continuousOn_smul_mem`: a set of frames
  stable exactly under `H` is locally trivial with fibre `H` wherever a local frame can be
  corrected into it continuously.
* `TauCeti.OrthonormalFrameBundle.isLocallyTrivialReduction_of_forall_exists_section`: a set of
  frames stable exactly under `H`, with continuous local sections near every point, is a locally
  trivial reduction to `H`.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
-/

public section

noncomputable section

open Bundle Set MulOpposite

namespace TauCeti.OrthonormalFrameBundle

section Action

variable {B : Type*} {F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-- A set `S` of orthonormal frames is carried into itself by exactly the elements of a subgroup
`H` of the orthogonal group: for a frame `p ∈ S`, `op g • p ∈ S` exactly when `g ∈ H`. Then `H`
acts on `S` on the right, freely and transitively on fibres. -/
class SMulMemIff (H : Subgroup (unitary (V →L[ℝ] V))) (S : Set (OrthonormalFrameBundle ℝ F E V)) :
    Prop where
  /-- An orthogonal transformation carries a frame of `S` into `S` exactly when it lies in `H`. -/
  smul_mem_iff {p : OrthonormalFrameBundle ℝ F E V} (hp : p ∈ S) {g : unitary (V →L[ℝ] V)} :
    op g • p ∈ S ↔ g ∈ H

variable {H : Subgroup (unitary (V →L[ℝ] V))} {S : Set (OrthonormalFrameBundle ℝ F E V)}
  [SMulMemIff H S]

/-- Two frames of `S` over the same base point differ by an element of `H`. -/
theorem SMulMemIff.exists_mem_smul_eq {p q : OrthonormalFrameBundle ℝ F E V} (hp : p ∈ S)
    (hq : q ∈ S) (h : p.proj = q.proj) : ∃ g ∈ H, op g • p = q := by
  obtain ⟨g, rfl⟩ := OrthonormalFrameBundle.exists_smul_eq_iff.2 h
  exact ⟨g, (smul_mem_iff (H := H) hp).1 hq, rfl⟩

/-- The frames lying in two sets of frames, stable exactly under `H` and `K`, are stable exactly
under `H ⊓ K`. -/
instance SMulMemIff.inter {K : Subgroup (unitary (V →L[ℝ] V))}
    {T : Set (OrthonormalFrameBundle ℝ F E V)} [SMulMemIff K T] :
    SMulMemIff (H ⊓ K) (S ∩ T) :=
  ⟨fun hp _ ↦ by
    rw [Set.mem_inter_iff, smul_mem_iff (H := H) hp.1, smul_mem_iff (H := K) hp.2,
      Subgroup.mem_inf]⟩

/-- The right action of `H` on `S`, by precomposition: the action of the orthogonal group on
all orthonormal frames, restricted (`TauCeti.reductionMulAction`). -/
instance instMulActionSubtype : MulAction Hᵐᵒᵖ S :=
  reductionMulAction fun _ hp _ hg ↦ (SMulMemIff.smul_mem_iff hp).2 hg

/-- The right action of `H` on `S`, as a direct `SMul` instance, so that instance search finds it
before the generic paths (such as `Algebra.toSMul`) through `MulAction`. -/
instance instSMulSubtype : SMul Hᵐᵒᵖ S :=
  instMulActionSubtype.toSMul

/-- The action on `S` is the action on all orthonormal frames. -/
theorem SMulMemIff.coe_smul (g : Hᵐᵒᵖ) (p : S) :
    ((g • p : S) : OrthonormalFrameBundle ℝ F E V) =
      op (g.unop : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle ℝ F E V) :=
  coe_reductionMulAction_smul _ g p

/-- The action of `g ∈ H` on a point `p` of `S` is the point `op g • p` of `S`, with any proof
that it lies in `S`. -/
theorem SMulMemIff.smul_eq_mk (g : H) (p : S)
    (hgp : op (g : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle ℝ F E V) ∈ S) :
    op g • p = ⟨_, hgp⟩ :=
  reductionMulAction_smul_eq_mk _ g p hgp

/-- A map on `S` takes the value `x` at the point `op g • p` of `S` if it does so at the point
`⟨op g • p, hgp⟩` for every proof `hgp` that it lies in `S`. This turns the equivariance of a
trivialization in the form of `TauCeti.IsLocallyTrivialReduction` into the form of the action. -/
theorem SMulMemIff.apply_smul_eq_of_apply_mk_eq {X : Type*} {f : S → X} {g : H} {p : S} {x : X}
    (h : ∀ hgp : op (g : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle ℝ F E V) ∈ S,
      f ⟨_, hgp⟩ = x) :
    f (op g • p) = x :=
  (congrArg f (smul_eq_mk g p _)).trans (h ((smul_mem_iff p.property).2 g.property))

/-- The action of `H` on `S` is free. -/
@[simp↓]
theorem SMulMemIff.smul_eq_self_iff {g : H} {p : S} : op g • p = p ↔ g = 1 := by
  rw [← Subtype.coe_inj, coe_smul, unop_op, OrthonormalFrameBundle.smul_eq_self_iff,
    OneMemClass.coe_eq_one]

/-- The action of `H` on `S` is transitive on fibres: two frames of `S` differ by an element of
`H` exactly when they lie over the same base point. -/
theorem SMulMemIff.exists_smul_eq_iff {p q : S} :
    (∃ g : H, op g • p = q) ↔ p.val.proj = q.val.proj := by
  refine ⟨fun ⟨g, h⟩ ↦ by rw [← h, coe_smul, proj_smul], fun h ↦ ?_⟩
  obtain ⟨g, hg, hgq⟩ := exists_mem_smul_eq (H := H) p.property q.property h
  exact ⟨⟨g, hg⟩, Subtype.ext ((coe_smul _ p).trans hgq)⟩

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E] [FiniteDimensional ℝ V]

/-- The right action of `H` on `S` is continuous. -/
instance : ContinuousSMul Hᵐᵒᵖ S where
  continuous_smul := Topology.IsInducing.subtypeVal.continuous_iff.2 <|
    ((continuous_op.comp ((continuous_subtypeVal.comp continuous_unop).comp continuous_fst)).smul
      (continuous_subtypeVal.comp continuous_snd)).congr fun p ↦ (SMulMemIff.coe_smul p.1 p.2).symm

end Action

variable {B : Type*} [TopologicalSpace B] {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]
  {T : Trivialization (unitary (V →L[ℝ] V)) (proj : OrthonormalFrameBundle ℝ F E V → B)}

section Reduction

variable {H : Subgroup (unitary (V →L[ℝ] V))} {S : Set (OrthonormalFrameBundle ℝ F E V)}
  {U : Set B} {c : B → unitary (V →L[ℝ] V)} [T.orthonormalFrameBundleFiber.IsEquivariant]
  [SMulMemIff H S]

/-- A set `S` of orthonormal frames, carried into itself by exactly the elements of a subgroup `H`
of the orthogonal group, is trivial with fibre `H`, equivariantly for the right action of `H`,
over every open subset `U` of the base set of an equivariant trivialization `T` on which the local
frame `T.symm (y, 1)` can be corrected into `S` by a continuous `c : B → unitary (V →L[ℝ] V)`. -/
theorem exists_trivialization_of_continuousOn_smul_mem (hUT : U ⊆ T.baseSet)
    (hcS : ∀ y ∈ U, op (c y) • T.toOpenPartialHomeomorph.symm (y, 1) ∈ S) (hU : IsOpen U)
    (hc : ContinuousOn c U) {x : B} (hx : x ∈ U) :
    ∃ t : Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj),
      t.baseSet = U ∧ ∀ (g : H) (p : S)
        (hgp : op (g : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle ℝ F E V) ∈ S),
        (p : OrthonormalFrameBundle ℝ F E V).proj ∈ U → t ⟨_, hgp⟩ = ((t p).1, (t p).2 * g) := by
  have he : ∀ (g : unitary (V →L[ℝ] V)) (p : OrthonormalFrameBundle ℝ F E V),
      p.proj ∈ T.baseSet → (T (op g • p)).2 = (T p).2 * g := fun g p hp ↦
    T.isEquivariant_orthonormalFrameBundleFiber_iff.1 inferInstance p hp g
  exact T.exists_trivialization_of_continuousOn_symm_mem (fun _ _ ↦ rfl) he
    (fun _ hp _ ↦ SMulMemIff.smul_mem_iff (H := H) hp) hUT
    (fun y hy ↦ T.op_smul_symm_one (fun _ _ ↦ rfl) he (hUT hy) (c y) ▸ hcS y hy) hU hc hx

end Reduction

section Section

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] [FiniteDimensional ℝ F]
  {H : Subgroup (unitary (V →L[ℝ] V))} {S : Set (OrthonormalFrameBundle ℝ F E V)} [SMulMemIff H S]

/-- **A set of frames with continuous local sections is a locally trivial reduction.** If `S` is
carried into itself by exactly the elements of `H`, and every point of the base has an open
neighbourhood `U` with a continuous local section `q` of frames of `S` over `U`, then `S` is a
locally trivial reduction of the orthonormal frame bundle to `H`. -/
theorem isLocallyTrivialReduction_of_forall_exists_section
    (hsec : ∀ x : B, ∃ U : Set B, IsOpen U ∧ x ∈ U ∧ ∃ q : B → OrthonormalFrameBundle ℝ F E V,
      (∀ y ∈ U, q y ∈ S ∧ (q y).proj = y) ∧ ContinuousOn q U) :
    IsLocallyTrivialReduction (proj : OrthonormalFrameBundle ℝ F E V → B) H S := by
  refine isLocallyTrivialReduction_iff.2 fun x ↦ ?_
  obtain ⟨U, hU, hxU, q, hqS, hq⟩ := hsec x
  -- The frame `q x` identifies `V` with the model fibre `F`.
  obtain ⟨eV⟩ := (q x).nonempty_linearEquiv
  have : FiniteDimensional ℝ V := LinearEquiv.finiteDimensional eV.symm
  obtain ⟨T, hxT, hT⟩ := exists_trivialization (E := E) (V := V) eV.finrank_eq x
  have : T.orthonormalFrameBundleFiber.IsEquivariant :=
    T.isEquivariant_orthonormalFrameBundleFiber_iff.2 fun p _ g ↦ congrArg Prod.snd (hT g p)
  -- Over `U ∩ T.baseSet` the section is the local frame of `T` corrected by its fibre coordinate.
  have hsrc : ∀ y ∈ U ∩ T.baseSet, q y ∈ T.source := fun y hy ↦
    T.mem_source.2 ((hqS y hy.1).2.symm ▸ hy.2)
  have hqT : ∀ y ∈ U ∩ T.baseSet, T.toOpenPartialHomeomorph.symm (y, (T (q y)).2) = q y :=
    fun y hy ↦ by
      have hpair : (y, (T (q y)).2) = T (q y) :=
        Prod.ext (by rw [T.coe_fst (hsrc y hy), (hqS y hy.1).2]) rfl
      rw [hpair]
      exact T.toOpenPartialHomeomorph.left_inv (hsrc y hy)
  have hcont : ContinuousOn (fun y ↦ T (q y)) (U ∩ T.baseSet) :=
    T.continuousOn_toFun.comp (hq.mono inter_subset_left) hsrc
  obtain ⟨t, ht, hteq⟩ := exists_trivialization_of_continuousOn_smul_mem (T := T) (H := H)
    (S := S) (c := fun y ↦ (T (q y)).2) inter_subset_right (fun y hy ↦ by
      rw [T.op_smul_symm_one (fun _ _ ↦ proj_smul _ _) (fun g p _ ↦ by rw [hT g p]) hy.2, hqT y hy]
      exact (hqS y hy.1).1)
    (hU.inter T.open_baseSet) (continuous_snd.comp_continuousOn hcont) ⟨hxU, hxT⟩
  exact ⟨t, ht ▸ ⟨hxU, hxT⟩, fun g p hgp hp ↦ hteq g p hgp (ht ▸ hp)⟩

end Section

end TauCeti.OrthonormalFrameBundle
