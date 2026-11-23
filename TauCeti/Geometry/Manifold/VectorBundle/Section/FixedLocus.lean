/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompletelyMetrizable
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module

/-!
# Sections with prescribed values on a set

Let `V` be a smooth vector bundle over a manifold `M` and `S` any subset of `M`. The `C^n`
sections of `V` vanishing at every point of `S` form a submodule
(`ContMDiffSection.vanishingOn`), and the sections equal to a given section `s₀` at every point
of `S` form the affine subspace through `s₀` with this direction
(`ContMDiffSection.fixedOn`). These are the parameter spaces of perturbation arguments in which
some data are fixed on a prescribed region, for instance a Riemannian metric kept Euclidean on
closed balls around the critical points of a Morse function, or kept fixed on closed collars of
the boundary, while it is perturbed elsewhere.

Evaluation at a point is continuous for the compact derivative topology
`ContMDiffSection.frameTopology` of any covering system of smooth frames, so both are closed
(`ContMDiffSection.isClosed_vanishingOn`, `ContMDiffSection.isClosed_fixedOn`); no hypothesis
on `S` is needed, since the conditions are imposed pointwise. Over a Lindelöf base
modelled on a locally compact space, with complete model fibre and finite or smooth regularity
`n`, the section space is completely metrizable, and so is each of these closed subsets
(`ContMDiffSection.isCompletelyMetrizableSpace_fixedOn`); in particular they are Baire spaces
(`ContMDiffSection.baireSpace_fixedOn`), in which countable intersections of open dense subsets
are dense.

## Main definitions

* `ContMDiffSection.vanishingOn S`: the submodule of sections vanishing on `S`.
* `ContMDiffSection.fixedOn s₀ S`: the affine subspace of sections equal to `s₀` on `S`.

## Main results

* `ContMDiffSection.direction_fixedOn`: the direction of `fixedOn s₀ S` is `vanishingOn S`.
* `ContMDiffSection.isClosed_vanishingOn`, `ContMDiffSection.isClosed_fixedOn`: both are
  closed in the compact derivative topology.
* `ContMDiffSection.isComplete_fixedOn`: `fixedOn s₀ S` is complete for the uniform structure
  of the section space, over a base modelled on a locally compact space, with
  complete model fibre and finite or smooth regularity `n`.
* `ContMDiffSection.isCompletelyMetrizableSpace_fixedOn`,
  `ContMDiffSection.baireSpace_fixedOn`: if moreover the base is Lindelöf, `fixedOn s₀ S` is
  completely metrizable, hence a Baire space.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §4, for the Baire property of spaces of
  `C^r` maps.
-/

public section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-! ### The submodule of sections vanishing on a set -/

section Algebra

variable (I F n V) in
/-- The `C^n` sections of `V` vanishing at every point of the set `S`: the intersection of the
kernels of evaluation at the points of `S`. -/
def vanishingOn (S : Set M) : Submodule 𝕜 Cₛ^n⟮I; F, V⟯ :=
  ⨅ x ∈ S, LinearMap.ker (evalLinearMap I F n V x)

@[simp]
theorem mem_vanishingOn {S : Set M} {s : Cₛ^n⟮I; F, V⟯} :
    s ∈ vanishingOn I F n V S ↔ ∀ x ∈ S, s x = 0 := by
  simp [vanishingOn]

@[simp]
theorem vanishingOn_empty : vanishingOn I F n V (∅ : Set M) = ⊤ := by
  simp [vanishingOn]

theorem vanishingOn_antitone : Antitone (vanishingOn I F n V : Set M → Submodule 𝕜 _) :=
  fun _ _ hST ↦ biInf_mono hST

theorem vanishingOn_union (S T : Set M) :
    vanishingOn I F n V (S ∪ T) = vanishingOn I F n V S ⊓ vanishingOn I F n V T :=
  iInf_union

/-! ### The affine subspace of sections with prescribed values on a set -/

/-- The `C^n` sections of `V` equal to the section `s₀` at every point of the set `S`, an affine
subspace with direction `vanishingOn S`. -/
def fixedOn (s₀ : Cₛ^n⟮I; F, V⟯) (S : Set M) : AffineSubspace 𝕜 Cₛ^n⟮I; F, V⟯ :=
  AffineSubspace.mk' s₀ (vanishingOn I F n V S)

@[simp]
theorem mem_fixedOn {s₀ s : Cₛ^n⟮I; F, V⟯} {S : Set M} :
    s ∈ fixedOn s₀ S ↔ ∀ x ∈ S, s x = s₀ x := by
  simp [fixedOn, AffineSubspace.mem_mk', sub_eq_zero]

theorem self_mem_fixedOn (s₀ : Cₛ^n⟮I; F, V⟯) (S : Set M) : s₀ ∈ fixedOn s₀ S :=
  AffineSubspace.self_mem_mk' _ _

@[simp]
theorem direction_fixedOn (s₀ : Cₛ^n⟮I; F, V⟯) (S : Set M) :
    (fixedOn s₀ S).direction = vanishingOn I F n V S :=
  AffineSubspace.direction_mk' _ _

@[simp]
theorem fixedOn_empty (s₀ : Cₛ^n⟮I; F, V⟯) : fixedOn s₀ (∅ : Set M) = ⊤ := by
  ext s
  simp

theorem fixedOn_eq_of_mem {s₀ s₁ : Cₛ^n⟮I; F, V⟯} {S : Set M} (h : s₁ ∈ fixedOn s₀ S) :
    fixedOn s₁ S = fixedOn s₀ S := by
  rw [fixedOn, ← direction_fixedOn s₀ S]
  exact AffineSubspace.mk'_eq h

theorem fixedOn_antitone (s₀ : Cₛ^n⟮I; F, V⟯) :
    Antitone (fixedOn s₀ : Set M → AffineSubspace 𝕜 _) :=
  fun _ _ hST ↦ (AffineSubspace.mk'_le_mk'_iff s₀).2 (vanishingOn_antitone hST)

theorem fixedOn_union (s₀ : Cₛ^n⟮I; F, V⟯) (S T : Set M) :
    fixedOn s₀ (S ∪ T) = fixedOn s₀ S ⊓ fixedOn s₀ T := by
  ext s
  simp only [mem_fixedOn, AffineSubspace.mem_inf_iff, mem_union]
  exact ⟨fun h ↦ ⟨fun x hx ↦ h x (.inl hx), fun x hx ↦ h x (.inr hx)⟩,
    fun h x hx ↦ hx.elim (h.1 x) (h.2 x)⟩

end Algebra

/-! ### Closedness and completeness -/

variable [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The sections vanishing on a set form a closed submodule in the compact derivative topology of
any covering frame system. -/
theorem isClosed_vanishingOn (hcover : ∀ x, ∃ i, x ∈ U i) (S : Set M) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsClosed (vanishingOn I F n V S : Set Cₛ^n⟮I; F, V⟯) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have : ∀ x, T2Space (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toHomeomorph.isEmbedding.t2Space
  have h : (vanishingOn I F n V S : Set Cₛ^n⟮I; F, V⟯) = ⋂ x ∈ S, {s | s x = 0} := by
    ext s
    simp
  rw [h]
  exact isClosed_biInter fun x _ ↦
    isClosed_eq (continuous_eval_const e U hU hcover x) continuous_const

/-- The sections equal to a given section on a set form a closed affine subspace in the compact
derivative topology of any covering frame system. -/
theorem isClosed_fixedOn (hcover : ∀ x, ∃ i, x ∈ U i) (s₀ : Cₛ^n⟮I; F, V⟯) (S : Set M) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsClosed (fixedOn s₀ S : Set Cₛ^n⟮I; F, V⟯) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  have := t2Space_frameTopology (I := I) (n := n) e U hU hcover
  refine (AffineSubspace.isClosed_direction_iff _).1 ?_
  rw [direction_fixedOn]
  exact isClosed_vanishingOn e U hU hcover S

section Complete

variable [IsRCLikeNormedField 𝕜] [LocallyCompactSpace E] [CompleteSpace F]
  [ENat.LEInfty n]

/-- Over a base modelled on a locally compact space, with complete model fibre and
finite or smooth regularity `n`, the sections equal to a given section on a set form a complete
subset of the section space. -/
theorem isComplete_fixedOn (hcover : ∀ x, ∃ i, x ∈ U i) (s₀ : Cₛ^n⟮I; F, V⟯) (S : Set M) :
    let _ := frameUniformSpace (I := I) (n := n) e U hU
    IsComplete (fixedOn s₀ S : Set Cₛ^n⟮I; F, V⟯) := by
  let _ := frameUniformSpace (I := I) (n := n) e U hU
  have := completeSpace_frameTopology (I := I) (n := n) e U hU hcover
  have h := isClosed_fixedOn (I := I) (n := n) e U hU hcover s₀ S
  rw [← frameUniformSpace_toTopologicalSpace (I := I) (n := n) e U hU] at h
  exact h.isComplete

/-- Over a Lindelöf base modelled on a locally compact space, with complete model
fibre and finite or smooth regularity `n`, the sections equal to a given section on a set form a
completely metrizable space for the compact derivative topology. -/
theorem isCompletelyMetrizableSpace_fixedOn [LindelofSpace M] (hcover : ∀ x, ∃ i, x ∈ U i)
    (s₀ : Cₛ^n⟮I; F, V⟯) (S : Set M) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsCompletelyMetrizableSpace (fixedOn s₀ S) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have := isCompletelyMetrizableSpace_frameTopology (I := I) (n := n) e U hU hcover
  exact (isClosed_fixedOn (I := I) (n := n) e U hU hcover s₀ S).isCompletelyMetrizableSpace

/-- **Sections with prescribed values form a Baire space.** Over a Lindelöf base
modelled on a locally compact space, with complete model fibre and finite or smooth regularity
`n`, the sections equal to a given section on a set form a Baire space for the compact derivative
topology: a countable intersection of relatively open dense subsets is dense. -/
theorem baireSpace_fixedOn [LindelofSpace M] (hcover : ∀ x, ∃ i, x ∈ U i)
    (s₀ : Cₛ^n⟮I; F, V⟯) (S : Set M) :
    let _ := frameTopology (I := I) (n := n) e U hU
    BaireSpace (fixedOn s₀ S) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have := isCompletelyMetrizableSpace_fixedOn (I := I) (n := n) e U hU hcover s₀ S
  infer_instance

end Complete

end ContMDiffSection
