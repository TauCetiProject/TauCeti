/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Topology.CategoryTheory.Nerve
public import TauCeti.Topology.Homotopy.Extension.Basic

/-!
# Clopen latching loci of étale nerves

An `n + 1`-simplex of the nerve of a category, a string `x₀ ⟶ x₁ ⟶ ⋯ ⟶ xₙ₊₁` of composable
arrows, lies in the image of the `i`-th degeneracy exactly when its `i`-th arrow `xᵢ ⟶ xᵢ₊₁` is
an identity arrow (`CategoryTheory.nerve.mem_range_σ_iff`). This generalizes, and adapts the proof
of, Mathlib's `PartialOrder.mem_range_nerve_σ_iff` from partial orders to arbitrary categories.
The degenerate simplices, the union of these images, form the latching object of the nerve in
each degree.

Now let the total arrows of the category carry a topology and give the strings of composable
arrows the topology of `TauCeti.topologicalNerve`. Each image of a degeneracy is then the
preimage of the set of identity arrows along a continuous map, so it is open or closed when the
identity arrows are, and each degeneracy is an embedding, as in any simplicial space
(`CategoryTheory.SimplicialObject.isEmbedding_σ`). The degenerate locus is a finite union of such
images, so it is open or closed too (`TauCeti.isOpen_nerve_degenerate`,
`TauCeti.isClosed_nerve_degenerate`).

For a topological category whose source is a local homeomorphism (an étale category, such as
a proper étale groupoid presenting an orbifold), with continuous units and Hausdorff arrow
space, the identity arrows form a clopen set: they are the image of a continuous section of the
source, hence open (`TauCeti.isOpen_range_unit`), and the fixed points of the continuous map
`a ↦ 𝟙 a.left`, hence closed (`TauCeti.isClosed_range_unit`).
So each degeneracy is an open and closed embedding
(`TauCeti.isClosedEmbedding_topologicalNerve_σ`, `TauCeti.isOpenEmbedding_topologicalNerve_σ`),
the degenerate locus in each degree is clopen
(`TauCeti.isClopen_nerve_degenerate`), and its inclusion has the homotopy extension property
(`TauCeti.hasHomotopyExtensionProperty_nerve_degenerate`). Its complement, the nondegenerate
locus, is clopen too (`TauCeti.isClopen_nerve_nonDegenerate`). These facts about the latching
inclusions are the input for treating the topological nerve of an étale groupoid as a proper
simplicial space, whose thin realization is built from its skeleta by closed attachments.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public section

open CategoryTheory Topology

universe v u

namespace CategoryTheory.nerve

variable {C : Type u} [Category.{v} C]

/-- A string of composable arrows whose `i`-th arrow is an identity arrow is the `i`-th degeneracy
of its face deleting the `i`-th object. -/
theorem σ_δ_castSucc_eq_self {n : ℕ} (s : ComposableArrows C (n + 1)) {i : Fin (n + 1)}
    {h : s.obj i.castSucc = s.obj i.succ} (hi : s.map (homOfLE i.castSucc_le_succ) = eqToHom h) :
    (nerve C).σ i ((nerve C).δ i.castSucc s) = s := by
  -- Removing the `i`-th object and then repeating the next one reindexes the string along `Φ`,
  -- which moves position `i.castSucc` to `i.succ` and fixes every other position.
  let Φ (j : Fin (n + 2)) : Fin (n + 2) := i.castSucc.succAbove (i.predAbove j)
  have hmono : Monotone Φ :=
    (Fin.strictMono_succAbove _).monotone.comp (Fin.predAbove_right_monotone i)
  -- By definition the nerve acts on strings by whiskering (on objects this is `nerve.σ_obj` and
  -- `nerve.δ_obj`), so the degeneracy of the face is `s` whiskered by `Φ`.
  have hσδ : (nerve C).σ i ((nerve C).δ i.castSucc s) = s.whiskerLeft hmono.functor := rfl
  have hΦ (j : Fin (n + 2)) : (j = i.castSucc ∧ Φ j = i.succ) ∨ Φ j = j := by
    obtain rfl | h := eq_or_ne j i.castSucc
    · simp [Φ]
    · exact .inr (Fin.succAbove_predAbove h)
  -- Each object of the string is joined to its new position by an identity arrow.
  have key (j : Fin (n + 2)) :
      ∃ e : s.obj j = s.obj (Φ j), ∀ hj : j ≤ Φ j, s.map (homOfLE hj) = eqToHom e := by
    have := hΦ j
    generalize Φ j = k at this ⊢
    rcases this with ⟨rfl, rfl⟩ | rfl
    · exact ⟨_, fun _ ↦ hi⟩
    · exact ⟨rfl, fun _ ↦ by simp⟩
  choose e he using key
  have hle (j : Fin (n + 2)) : j ≤ Φ j := by
    rcases hΦ j with ⟨rfl, h⟩ | h
    · exact h ▸ i.castSucc_le_succ
    · exact h.ge
  rw [hσδ]
  refine Functor.ext (fun j ↦ (e j).symm) fun j k f ↦ ?_
  simp only [ComposableArrows.whiskerLeft, Functor.comp_map]
  rw [← eqToHom_comp_iff (e j), ← he j (hle j), ← he k (hle k), ← s.map_comp, ← s.map_comp]
  exact congrArg s.map (Subsingleton.elim _ _)

/-- A simplex of the nerve lies in the image of the `i`-th degeneracy exactly when its `i`-th
arrow is an identity arrow. This generalizes Mathlib's `PartialOrder.mem_range_nerve_σ_iff`
(in `Mathlib/AlgebraicTopology/SimplicialSet/NerveNondegenerate.lean`) from partial orders to
arbitrary categories, and adapts its proof: the converse exhibits the simplex as the degeneracy
of its face (`σ_δ_castSucc_eq_self`). -/
theorem mem_range_σ_iff {n : ℕ} (s : ComposableArrows C (n + 1)) (i : Fin (n + 1)) :
    s ∈ Set.range ((nerve C).σ i) ↔
      s.totalArrow i.castSucc i.succ i.castSucc_le_succ ∈
        Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) := by
  constructor
  · -- The `i`-th degeneracy repeats the `i`-th object, so its `i`-th arrow is an identity.
    rintro ⟨t, rfl⟩
    refine ⟨t.obj i, ((t.totalArrow_whiskerLeft _ _ _ _).trans ?_).symm⟩
    -- The degeneracy reindexes along `SimplexCategory.toCat.map (SimplexCategory.σ i)`, whose
    -- object map is `i.predAbove` by definition (as in Mathlib's `nerve.σ_obj`). Simp only unfolds
    -- that functor into a chain of forgetful functors, so `change` states the reduced positions.
    change t.totalArrow (i.predAbove i.castSucc) (i.predAbove i.succ) _ = _
    simp only [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
    exact ComposableArrows.totalArrow_self (n := n) t i
  · rintro ⟨x, hx⟩
    rw [ComposableArrows.totalArrow_def] at hx
    obtain ⟨rfl, hr, hh⟩ := Quiver.Total.ext_iff.1 hx
    dsimp only at hr hh
    exact ⟨_, σ_δ_castSucc_eq_self s (h := hr)
      (by simpa [comp_eqToHom_iff] using ((conj_eqToHom_iff_heq _ _ rfl hr).2 hh).symm)⟩

end CategoryTheory.nerve

namespace CategoryTheory.SimplicialObject

/-- Each degeneracy of a simplicial space is an embedding: the face deleting the repeated
simplex is a continuous left inverse. -/
theorem isEmbedding_σ (X : SimplicialObject TopCat) {n : ℕ} (i : Fin (n + 1)) :
    IsEmbedding (X.σ i) :=
  .of_leftInverse (f := X.δ i.castSucc)
    (fun x ↦ by rw [← ConcreteCategory.comp_apply, δ_comp_σ_self, ConcreteCategory.id_apply])
    (ContinuousMap.continuous _) (ContinuousMap.continuous _)

end CategoryTheory.SimplicialObject

namespace TauCeti

variable {C : Type u} [Category.{v} C]

/-- The image of the `i`-th degeneracy is the set of strings whose `i`-th arrow is an identity
arrow. -/
private theorem range_nerve_σ_eq_preimage {n : ℕ} (i : Fin (n + 1)) :
    Set.range ((nerve C).σ i) =
      (fun s : ComposableArrows C (n + 1) ↦ s.totalArrow i.castSucc i.succ i.castSucc_le_succ) ⁻¹'
        Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) :=
  Set.ext fun s ↦ nerve.mem_range_σ_iff s i

variable [TopologicalSpace (Quiver.Total C)]

/-- If the identity arrows form a closed set, each degeneracy of the topological nerve is a
closed embedding. -/
theorem isClosedEmbedding_topologicalNerve_σ
    (h : IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) {n : ℕ}
    (i : Fin (n + 1)) :
    IsClosedEmbedding (SimplicialObject.σ (topologicalNerve C) i) :=
  ⟨SimplicialObject.isEmbedding_σ (topologicalNerve C) i, range_nerve_σ_eq_preimage (C := C) i ▸
    h.preimage (ComposableArrows.continuous_totalArrow _ _ _)⟩

/-- If the identity arrows form an open set, each degeneracy of the topological nerve is an open
embedding. -/
theorem isOpenEmbedding_topologicalNerve_σ
    (h : IsOpen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) {n : ℕ}
    (i : Fin (n + 1)) :
    IsOpenEmbedding (SimplicialObject.σ (topologicalNerve C) i) :=
  ⟨SimplicialObject.isEmbedding_σ (topologicalNerve C) i, range_nerve_σ_eq_preimage (C := C) i ▸
    h.preimage (ComposableArrows.continuous_totalArrow _ _ _)⟩

/-- If the identity arrows form a closed set, the degenerate simplices of the topological nerve
form a closed set in each degree. -/
theorem isClosed_nerve_degenerate
    (h : IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) (n : ℕ) :
    IsClosed (X := ComposableArrows C n) ((nerve C).degenerate n) := by
  cases n with
  | zero => exact SSet.degenerate_zero (nerve C) ▸ isClosed_empty
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ]
    exact isClosed_iUnion_of_finite fun i ↦
      (isClosedEmbedding_topologicalNerve_σ h i).isClosed_range

/-- If the identity arrows form an open set, the degenerate simplices of the topological nerve
form an open set in each degree. -/
theorem isOpen_nerve_degenerate
    (h : IsOpen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) (n : ℕ) :
    IsOpen (X := ComposableArrows C n) ((nerve C).degenerate n) := by
  cases n with
  | zero => exact SSet.degenerate_zero (nerve C) ▸ isOpen_empty
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ]
    exact isOpen_iUnion fun i ↦ (isOpenEmbedding_topologicalNerve_σ h i).isOpen_range

variable [TopologicalSpace C] (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
include hu

/-- In a topological category with continuous units and locally homeomorphic source, the identity
arrows form an open set: they are the image of a continuous section of the source. -/
theorem isOpen_range_unit (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    IsOpen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  (hs.isOpenEmbedding_of_comp (f := fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    IsOpenEmbedding.id hu).isOpen_range

/-- In a topological category with continuous units, continuous source and Hausdorff arrow
space, the identity arrows form a closed set: they are a retract of the arrow space. -/
theorem isClosed_range_unit [T2Space (Quiver.Total C)]
    (hl : Continuous (Quiver.Total.left : Quiver.Total C → C)) :
    IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  Function.LeftInverse.isClosed_range (f := Quiver.Total.left) (fun _ ↦ rfl) hl hu

variable [T2Space (Quiver.Total C)]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
include hs

/-- In a topological category with continuous units, locally homeomorphic source and Hausdorff
arrow space, the identity arrows form a clopen set. -/
theorem isClopen_range_unit : IsClopen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  ⟨isClosed_range_unit hu hs.continuous, isOpen_range_unit hu hs⟩

/-- **The latching loci of an étale nerve are clopen.** In a topological category with
continuous units, locally homeomorphic source and Hausdorff arrow space, the degenerate
simplices of the topological nerve form a clopen set in each degree. -/
theorem isClopen_nerve_degenerate (n : ℕ) :
    IsClopen (X := ComposableArrows C n) ((nerve C).degenerate n) :=
  ⟨isClosed_nerve_degenerate (isClopen_range_unit hu hs).isClosed n,
    isOpen_nerve_degenerate (isClopen_range_unit hu hs).isOpen n⟩

/-- In a topological category with continuous units, locally homeomorphic source and Hausdorff
arrow space, the nondegenerate simplices of the topological nerve form a clopen set in each
degree. -/
theorem isClopen_nerve_nonDegenerate (n : ℕ) :
    IsClopen (X := ComposableArrows C n) ((nerve C).nonDegenerate n) :=
  (isClopen_nerve_degenerate hu hs n).compl

/-- In a topological category with continuous units, locally homeomorphic source and Hausdorff
arrow space, the inclusion of the degenerate simplices of the topological nerve has the homotopy
extension property in each degree. -/
theorem hasHomotopyExtensionProperty_nerve_degenerate (n : ℕ) :
    HasHomotopyExtensionProperty (X := ComposableArrows C n) ((nerve C).degenerate n) :=
  (isClopen_nerve_degenerate hu hs n).hasHomotopyExtensionProperty

end TauCeti
