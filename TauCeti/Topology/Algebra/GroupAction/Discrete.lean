/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.MulAction

/-!
# Continuous actions on discrete spaces

This file develops openness properties of continuous group actions on discrete spaces.
For a finite space, the kernel of the action is open and the action factors through a finite
quotient. For an arbitrary discrete space acted on by a compact topological group, every finite
set is fixed pointwise by an open normal subgroup. In particular, each orbit map factors through
a finite quotient. Total disconnectedness of the acting group is not needed: point stabilizers
are clopen, so Mathlib's compact-group clopen-neighborhood theorem applies directly.

For actions on discrete additive groups, the fixed-point subgroups over all open normal
subgroups exhaust the group; the additive group need not be commutative. These results supply
the openness and exhaustion properties used by the finite-quotient system for continuous
cohomology.

Mathlib supplies open point stabilizers, open normal subgroups inside clopen neighborhoods of
the identity in compact groups, and the quotient action on fixed points of a normal subgroup.
We use its fixed-point objects throughout.
-/

public section

namespace TauCeti

universe u v

section Elementwise

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {M : Type v} [TopologicalSpace M] [DiscreteTopology M] [MulAction G M] [ContinuousSMul G M]

/-- A finite set in a discrete continuous action of a compact group is fixed pointwise by a
single open normal subgroup. -/
theorem _root_.Set.Finite.exists_openNormalSubgroup_smul_eq_self {s : Set M} (hs : s.Finite) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, ∀ m ∈ s, u • m = m := by
  let V : Set G := ⋂ m ∈ s, (MulAction.stabilizer G m : Set G)
  have hClopen : IsClopen V :=
    hs.isClopen_biInter fun m _ ↦
      ⟨(MulAction.stabilizer G m).isClosed_of_isOpen (stabilizer_isOpen G m),
        stabilizer_isOpen G m⟩
  have hOne : (1 : G) ∈ V := by
    simp only [V, Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff, one_smul,
      implies_true]
  obtain ⟨U, hU⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hClopen hOne
  refine ⟨U, fun u hu m hm ↦ ?_⟩
  exact MulAction.mem_stabilizer_iff.mp (Set.mem_iInter₂.mp (hU hu) m hm)

/-- Every element of a discrete continuous action of a compact group is fixed by an open
normal subgroup. -/
theorem exists_openNormalSubgroup_smul_eq_self (m : M) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, u • m = m := by
  obtain ⟨U, hU⟩ :=
    (Set.finite_singleton m).exists_openNormalSubgroup_smul_eq_self (G := G)
  exact ⟨U, fun u hu ↦ hU u hu m (Set.mem_singleton m)⟩

/-- A finite family in a discrete continuous action of a compact group has a common open
normal stabilizer. This is the form used for the finite image of a locally constant cochain. -/
theorem exists_openNormalSubgroup_smul_eq_self_range {ι : Type*} [Finite ι] (f : ι → M) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, ∀ i, u • f i = f i := by
  have hrange : (Set.range f).Finite := Set.finite_range f
  obtain ⟨U, hU⟩ :=
    Set.Finite.exists_openNormalSubgroup_smul_eq_self (G := G) hrange
  exact ⟨U, fun u hu i ↦ hU u hu (f i) ⟨i, rfl⟩⟩

/-- The orbit map of a discrete continuous action of a compact group factors through a finite
quotient, using the quotient action on the fixed points of an open normal subgroup. -/
theorem exists_orbitMap_quotient (m : M) :
    ∃ (U : OpenNormalSubgroup G) (f : G ⧸ U.toSubgroup → M),
      ∀ g : G, f (QuotientGroup.mk g) = g • m := by
  obtain ⟨U, hm⟩ := exists_openNormalSubgroup_smul_eq_self (G := G) m
  let mU : MulAction.fixedPoints U.toSubgroup M := ⟨m, fun u ↦ hm u u.2⟩
  refine ⟨U, fun q ↦ (q • mU : MulAction.fixedPoints U.toSubgroup M), fun g ↦ ?_⟩
  exact congrArg Subtype.val (MulAction.coe_quotient_smul_fixedPoints g mU)

end Elementwise

section Kernel

variable (G : Type u) [Group G] (M : Type v) [MulAction G M]

/-- The action kernel is the intersection of all point stabilizers. -/
theorem toPermHom_ker_eq_iInf_stabilizer :
    (MulAction.toPermHom G M).ker = ⨅ m : M, MulAction.stabilizer G m := by
  ext g
  simp only [MonoidHom.mem_ker, Equiv.ext_iff, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, Equiv.Perm.one_apply, Subgroup.mem_iInf,
    MulAction.mem_stabilizer_iff]

/-- The action kernel is the whole group exactly when the action is trivial. -/
@[simp]
theorem toPermHom_ker_eq_top_iff :
    (MulAction.toPermHom G M).ker = ⊤ ↔ ∀ (g : G) (m : M), g • m = m := by
  constructor
  · intro h g m
    have hg : g ∈ (MulAction.toPermHom G M).ker := by rw [h]; exact Subgroup.mem_top g
    exact Equiv.congr_fun (MonoidHom.mem_ker.mp hg) m
  · intro h
    rw [eq_top_iff]
    intro g _
    rw [MonoidHom.mem_ker, Equiv.ext_iff]
    exact h g

/-- An action on a finite space factors through a finite quotient. -/
theorem finite_quotient_toPermHom_ker [Finite M] :
    Finite (G ⧸ (MulAction.toPermHom G M).ker) := by
  exact Finite.of_equiv (MulAction.toPermHom G M).range
    (QuotientGroup.quotientKerEquivRange (MulAction.toPermHom G M)).symm.toEquiv

variable [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- The kernel of a continuous action on a finite discrete space is open. -/
theorem isOpen_toPermHom_ker [Finite M] :
    IsOpen ((MulAction.toPermHom G M).ker : Set G) := by
  rw [toPermHom_ker_eq_iInf_stabilizer, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun m ↦ stabilizer_isOpen G m

/-- The open normal subgroup given by the kernel of a finite discrete action. -/
def openActionKernel [Finite M] : OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup := (MulAction.toPermHom G M).ker
      isOpen' := isOpen_toPermHom_ker G M }
  isNormal' := (MulAction.toPermHom G M).normal_ker

@[simp]
theorem openActionKernel_toSubgroup [Finite M] :
    (openActionKernel G M).toSubgroup = (MulAction.toPermHom G M).ker := by
  ext
  simp only [openActionKernel]

/-- A finite discrete space with a continuous group action is fixed pointwise by an open normal
subgroup. The subgroup can be taken to be the kernel of the action. -/
@[simp]
theorem openActionKernel_smul_eq_self [Finite M] (g : openActionKernel G M) (m : M) :
    (g : G) • m = m := by
  have hg := MonoidHom.mem_ker.mp g.2
  exact Equiv.congr_fun hg m

end Kernel

section FiniteCoefficients

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M]

/-- The fixed points of the action kernel on a finite discrete additive group are the whole group.
The additive group need not be commutative. -/
@[simp]
theorem fixedPoints_openActionKernel_eq_top :
    FixedPoints.addSubgroup (openActionKernel G M).toSubgroup M = ⊤ := by
  rw [eq_top_iff]
  intro m _ g
  exact openActionKernel_smul_eq_self G M g m

end FiniteCoefficients

section Exhaustion

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {M : Type v} [AddGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The fixed-point subgroups over the open normal subgroups of a compact group exhaust a
discrete additive group with a continuous action. The additive group need not be commutative. -/
theorem iSup_fixedPoints_openNormal_eq_top :
    (⨆ U : OpenNormalSubgroup G, FixedPoints.addSubgroup U.toSubgroup M) = ⊤ := by
  rw [eq_top_iff]
  intro m _
  obtain ⟨U, hm⟩ := exists_openNormalSubgroup_smul_eq_self (G := G) m
  apply (le_iSup (fun V : OpenNormalSubgroup G ↦ FixedPoints.addSubgroup V.toSubgroup M) U)
  exact fun u ↦ hm u u.2

end Exhaustion

end TauCeti
