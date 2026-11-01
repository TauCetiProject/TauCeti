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
an identity arrow (`CategoryTheory.nerve.mem_range_σ_iff`). The degenerate simplices, the union
of these images, form the latching object of the nerve in each degree.

Now let the total arrows of the category carry a topology and give the strings of composable
arrows the topology of `TauCeti.topologicalNerve`. Each image of a degeneracy is then the
preimage of the set of identity arrows along a continuous map, so it is open or closed when the
identity arrows are. The degenerate locus is a finite union of such images, so it is open or
closed too (`TauCeti.isOpen_nerve_degenerate`, `TauCeti.isClosed_nerve_degenerate`).

For a topological category whose source is a local homeomorphism (an étale category, such as
a proper étale groupoid presenting an orbifold), with continuous units and Hausdorff arrow
space, the identity arrows form a clopen set: they are the image of a continuous section of the
source, hence open, and the fixed points of the continuous map `a ↦ 𝟙 a.left`, hence closed.
So each degeneracy is an open and closed embedding
(`TauCeti.isClosedEmbedding_topologicalNerve_σ`, `TauCeti.isOpenEmbedding_topologicalNerve_σ`),
the degenerate locus in each degree is clopen
(`TauCeti.isClopen_nerve_degenerate`), and its inclusion has the homotopy extension property
(`TauCeti.hasHomotopyExtensionProperty_nerve_degenerate`). Degeneracies are always embeddings
(`TauCeti.isEmbedding_topologicalNerve_σ`). These facts about the latching inclusions are the
input for treating the topological nerve of an étale groupoid as a proper simplicial space, whose
thin realization is built from its skeleta by closed attachments.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public section

open CategoryTheory Topology

universe v u

namespace CategoryTheory.nerve

variable {C : Type u} [Category.{v} C]

/-- The arrow of a string of composable arrows between two equal positions is an identity
arrow. -/
private theorem totalArrow_of_eq {n : ℕ} (s : ComposableArrows C n) {j k : Fin (n + 1)}
    (h : j = k) (hjk : j ≤ k) :
    s.totalArrow j k hjk = ⟨s.obj j, s.obj j, 𝟙 (s.obj j)⟩ := by
  subst h
  simp [ComposableArrows.totalArrow_def]

/-- A simplex of the nerve lies in the image of the `i`-th degeneracy exactly when its `i`-th
arrow is an identity arrow. -/
theorem mem_range_σ_iff {n : ℕ} (s : ComposableArrows C (n + 1)) (i : Fin (n + 1)) :
    s ∈ Set.range ((nerve C).σ i) ↔
      s.totalArrow i.castSucc i.succ i.castSucc_le_succ ∈
        Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) := by
  constructor
  · -- The `i`-th degeneracy repeats the `i`-th object, so its `i`-th arrow is an identity.
    rintro ⟨t, rfl⟩
    exact ⟨_, ((t.totalArrow_whiskerLeft _ _ _ _).trans (totalArrow_of_eq t
      ((Fin.predAbove_castSucc_self i).trans (Fin.predAbove_succ_self i).symm) _)).symm⟩
  · rintro ⟨x, hx⟩
    rw [ComposableArrows.totalArrow_def] at hx
    obtain ⟨rfl, hr, hh⟩ := Quiver.Total.ext_iff.1 hx
    dsimp only at hr hh
    have hi : s.map (homOfLE i.castSucc_le_succ) = eqToHom hr := by
      have h := (conj_eqToHom_iff_heq _ _ rfl hr).2 hh
      rw [eqToHom_refl, Category.id_comp, eq_comm, comp_eqToHom_iff, Category.id_comp] at h
      exact h
    -- Removing the `i`-th object and then repeating the next one reindexes the string along `Φ`,
    -- which moves position `i.castSucc` to `i.succ` and fixes every other position.
    let Φ (j : Fin (n + 2)) : Fin (n + 2) := i.castSucc.succAbove (i.predAbove j)
    have hΦ (j : Fin (n + 2)) : (j = i.castSucc ∧ Φ j = i.succ) ∨ Φ j = j := by
      dsimp only [Φ]
      rcases lt_trichotomy j i.castSucc with h | rfl | h
      · right
        rw [Fin.predAbove_of_le_castSucc _ _ h.le,
          Fin.succAbove_of_castSucc_lt _ _ (by simpa using h), Fin.castSucc_castPred]
      · simp
      · right
        rw [Fin.predAbove_of_castSucc_lt _ _ h, Fin.succAbove_of_le_castSucc _ _ (by
          simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_pred] at h ⊢; omega),
          Fin.succ_pred]
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
    have hmono : Monotone Φ :=
      (Fin.strictMono_succAbove _).monotone.comp (Fin.predAbove_right_monotone i)
    have hmap (j k : Fin (n + 2)) (f : j ⟶ k) (h : Φ j ≤ Φ k) :
        s.map (homOfLE h) = eqToHom (e j).symm ≫ s.map f ≫ eqToHom (e k) := by
      rw [← eqToHom_comp_iff (e j), ← he j (hle j), ← he k (hle k), ← s.map_comp, ← s.map_comp]
      exact congrArg s.map (Subsingleton.elim _ _)
    -- The degeneracy of the face reindexes `s` along `Φ`, by definition of the nerve.
    exact ⟨(nerve C).δ i.castSucc s, Functor.ext (fun j ↦ (e j).symm)
      fun (j k : Fin (n + 2)) (f : j ⟶ k) ↦ hmap j k f (hmono f.le)⟩

end CategoryTheory.nerve

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

/-- Each degeneracy of the topological nerve is an embedding: the face deleting the repeated
object is a continuous left inverse. -/
theorem isEmbedding_topologicalNerve_σ {n : ℕ} (i : Fin (n + 1)) :
    IsEmbedding (SimplicialObject.σ (topologicalNerve C) i) :=
  .of_leftInverse (f := SimplicialObject.δ (topologicalNerve C) i.castSucc)
    (fun s ↦ SSet.δ_comp_σ_self_apply (S := nerve C) i s)
    (ContinuousMap.continuous _) (ContinuousMap.continuous _)

/-- If the identity arrows form a closed set, each degeneracy of the topological nerve is a
closed embedding. -/
theorem isClosedEmbedding_topologicalNerve_σ
    (h : IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) {n : ℕ}
    (i : Fin (n + 1)) :
    IsClosedEmbedding (SimplicialObject.σ (topologicalNerve C) i) :=
  ⟨isEmbedding_topologicalNerve_σ i, range_nerve_σ_eq_preimage (C := C) i ▸
    h.preimage (ComposableArrows.continuous_totalArrow _ _ _)⟩

/-- If the identity arrows form an open set, each degeneracy of the topological nerve is an open
embedding. -/
theorem isOpenEmbedding_topologicalNerve_σ
    (h : IsOpen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) {n : ℕ}
    (i : Fin (n + 1)) :
    IsOpenEmbedding (SimplicialObject.σ (topologicalNerve C) i) :=
  ⟨isEmbedding_topologicalNerve_σ i, range_nerve_σ_eq_preimage (C := C) i ▸
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

variable [TopologicalSpace C] [T2Space (Quiver.Total C)]
  (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
include hu hs

/-- In a topological category with continuous units, locally homeomorphic source and Hausdorff
arrow space, the identity arrows form a clopen set. They are the image of a continuous section
of the source, hence open, and a retract of the Hausdorff arrow space, hence closed. -/
theorem isClopen_range_unit : IsClopen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  ⟨Function.LeftInverse.isClosed_range (f := Quiver.Total.left) (fun _ ↦ rfl) hs.continuous hu,
    (hs.isOpenEmbedding_of_comp (f := fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
      IsOpenEmbedding.id hu).isOpen_range⟩

/-- **The latching loci of an étale nerve are clopen.** In a topological category with
continuous units, locally homeomorphic source and Hausdorff arrow space, the degenerate
simplices of the topological nerve form a clopen set in each degree. -/
theorem isClopen_nerve_degenerate (n : ℕ) :
    IsClopen (X := ComposableArrows C n) ((nerve C).degenerate n) :=
  ⟨isClosed_nerve_degenerate (isClopen_range_unit hu hs).isClosed n,
    isOpen_nerve_degenerate (isClopen_range_unit hu hs).isOpen n⟩

/-- In a topological category with continuous units, locally homeomorphic source and Hausdorff
arrow space, the inclusion of the degenerate simplices of the topological nerve has the homotopy
extension property in each degree. -/
theorem hasHomotopyExtensionProperty_nerve_degenerate (n : ℕ) :
    HasHomotopyExtensionProperty (X := ComposableArrows C n) ((nerve C).degenerate n) :=
  (isClopen_nerve_degenerate hu hs n).hasHomotopyExtensionProperty

end TauCeti
