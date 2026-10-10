/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
import Mathlib.Data.Fintype.Option

/-!
# Based van Kampen for finite open covers

Homomorphisms out of the fundamental groups of a finite open cover glue uniquely when they
agree on each pairwise intersection, provided the double and triple intersections are path
connected and every member contains the basepoint. The overlaps may differ from pair to pair.
This gives the universal property needed to compute a fundamental group by successively
adjoining cover members, without requiring a single common overlap.

The finite iteration uses the two-set van Kampen theorem. Compatibility at a new step follows
from uniqueness on the cover of its overlap by the previous pairwise intersections; their
double intersections are precisely the original triple intersections.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.20.
* R. Brown, *Topology and Groupoids*, 3rd ed., Section 6.7.
-/

public section

open Set Topology

universe u v w

namespace TauCeti

variable {K : Type w} [Monoid K]

/-- **The based van Kampen theorem for a finite open cover, in universal-property form.**
Pairwise compatible homomorphisms out of the fundamental groups of the cover members extend
uniquely to the ambient fundamental group. Repeated indices in the double-intersection
hypothesis include path connectedness of the individual members. No common pairwise
intersection is required, and the target can be any monoid. -/
theorem existsUnique_vanKampenDesc_finite {X : Type v} [TopologicalSpace X]
    {ι : Type u} [Finite ι] (U : ι → Set X) (x : X)
    (hOpen : ∀ i, IsOpen (U i)) (hCover : ∀ y, ∃ i, y ∈ U i)
    (hx : ∀ i, x ∈ U i) (hDouble : ∀ i j, IsPathConnected (U i ∩ U j))
    (hTriple : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (f : ∀ i, FundamentalGroup (U i) ⟨x, hx i⟩ →* K)
    (hcompat : ∀ i j,
      (f i).comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
          ⟨x, hx i, hx j⟩) =
        (f j).comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
          ⟨x, hx i, hx j⟩)) :
    ∃! d : FundamentalGroup X x →* K, ∀ i,
      d.comp (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hx i⟩) = f i := by
  classical
  let P (ι : Type u) : Prop := ∀ (X : Type v) [TopologicalSpace X]
      (U : ι → Set X) (x : X),
      (∀ i, IsOpen (U i)) → (∀ y, ∃ i, y ∈ U i) →
      ∀ (hx : ∀ i, x ∈ U i),
      (∀ i j, IsPathConnected (U i ∩ U j)) →
      (∀ i j k, IsPathConnected (U i ∩ U j ∩ U k)) →
      ∀ (f : ∀ i, FundamentalGroup (U i) ⟨x, hx i⟩ →* K),
      (∀ i j, (f i).comp (FundamentalGroup.map
          (ContinuousMap.inclusion inter_subset_left) ⟨x, hx i, hx j⟩) =
        (f j).comp (FundamentalGroup.map
          (ContinuousMap.inclusion inter_subset_right) ⟨x, hx i, hx j⟩)) →
      ∃! d : FundamentalGroup X x →* K, ∀ i,
        d.comp (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hx i⟩) = f i
  have hP : P ι := by
    -- Reindexing preserves the universal property, so finite-type induction has no data choices.
    apply Finite.induction_empty_option (P := P)
    · intro α β e ih X _ U x hOpen hCover hx hDouble hTriple f hcompat
      obtain ⟨d, hd, huniq⟩ := ih X (fun i ↦ U (e i)) x
        (fun i ↦ hOpen (e i))
        (fun y ↦ by obtain ⟨i, hi⟩ := hCover y; exact ⟨e.symm i, by simpa using hi⟩)
        (fun i ↦ hx (e i)) (fun i j ↦ hDouble (e i) (e j))
        (fun i j k ↦ hTriple (e i) (e j) (e k))
        (fun i ↦ f (e i)) (fun i j ↦ hcompat (e i) (e j))
      exact ⟨d, fun i ↦ by obtain ⟨j, rfl⟩ := e.surjective i; exact hd j, fun d' hd' ↦
        huniq d' (fun i ↦ hd' (e i))⟩
    -- An empty family cannot cover a space equipped with a basepoint.
    · intro X _ U x hOpen hCover hx hDouble hTriple f hcompat
      obtain ⟨i, _⟩ := hCover x
      exact i.elim
    · intro α _ ih X _ U x hOpen hCover hx hDouble hTriple f hcompat
      have hnhds : ∀ y, ∃ i, U i ∈ 𝓝 y := fun y ↦ by
        obtain ⟨i, hi⟩ := hCover y
        exact ⟨i, (hOpen i).mem_nhds hi⟩
      suffices ∃ d : FundamentalGroup X x →* K, ∀ i,
          d.comp (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hx i⟩) = f i by
        obtain ⟨d, hd⟩ := this
        exact ⟨d, hd, fun d' hd' ↦ vanKampenWide_hom_ext hnhds hx hDouble
          (fun i ↦ (hd' i).trans (hd i).symm)⟩
      let A : Set X := ⋃ i : α, U (some i)
      let B : Set X := U none
      rcases isEmpty_or_nonempty α with hempty | hnonempty
      · -- A single cover member is the whole space; the lift merely retypes its points.
        have hBcover : ∀ y, y ∈ B := by
          intro y
          obtain ⟨i, hi⟩ := hCover y
          cases i with
          | none => exact hi
          | some i => exact (hempty.false i).elim
        let toB : C(X, B) := ⟨fun y ↦ ⟨y, hBcover y⟩, continuous_id.subtype_mk hBcover⟩
        refine ⟨(f none).comp (FundamentalGroup.map toB x), ?_⟩
        intro i
        cases i with
        | some i => exact (hempty.false i).elim
        | none =>
          -- Retyping into the sole cover member and forgetting the subtype preserves each path.
          ext g
          induction g using Path.Homotopic.Quotient.ind
          rfl
      · let := hnonempty
        -- Glue on the union of the previous members, viewed as its own ambient space.
        have hxA : x ∈ A := mem_iUnion.mpr ⟨Classical.arbitrary α, hx _⟩
        have hUA (i : α) : U (some i) ⊆ A := subset_iUnion (fun j ↦ U (some j)) i
        let V (i : α) : Set A := Subtype.val ⁻¹' U (some i)
        let r (i : α) : C(V i, U (some i)) :=
          (ContinuousMap.subtypeVal A).restrictPreimage (U (some i))
        let b : A := ⟨x, hxA⟩
        let hxV (i : α) : b ∈ V i := hx (some i)
        let fv (i : α) : FundamentalGroup (V i) ⟨b, hxV i⟩ →* K :=
          (f (some i)).comp (FundamentalGroup.map (r i) ⟨b, hxV i⟩)
        have hVcompat (i j : α) :
            (fv i).comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
              ⟨b, hxV i, hxV j⟩) =
            (fv j).comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
              ⟨b, hxV i, hxV j⟩) := by
          let rij : C(↥(V i ∩ V j), ↥(U (some i) ∩ U (some j))) :=
            (ContinuousMap.subtypeVal A).restrictPreimage (U (some i) ∩ U (some j))
          have h := congrArg (fun g ↦ g.comp (FundamentalGroup.map rij ⟨b, hxV i, hxV j⟩))
            (hcompat (some i) (some j))
          dsimp only [fv]
          erw [MonoidHom.comp_assoc, ← FundamentalGroup.map_comp,
            MonoidHom.comp_assoc, ← FundamentalGroup.map_comp] at h ⊢
          exact h
        obtain ⟨dA, hdA, _⟩ := ih A V b
          (fun i ↦ (hOpen (some i)).preimage continuous_subtype_val)
          (fun y ↦ by obtain ⟨i, hi⟩ := mem_iUnion.mp y.2; exact ⟨i, hi⟩)
          hxV
          (fun i j ↦ by
            simpa only [V, ← preimage_inter] using
              (hDouble (some i) (some j)).preimage_coe (inter_subset_left.trans (hUA i)))
          (fun i j k ↦ by
            simpa only [V, ← preimage_inter] using
              (hTriple (some i) (some j) (some k)).preimage_coe
                ((inter_subset_left.trans inter_subset_left).trans (hUA i)))
          fv hVcompat
        -- Transport the recursive restrictions back to the original cover-member carriers.
        have hdA' (i : α) : dA.comp
            (FundamentalGroup.map (ContinuousMap.inclusion (hUA i)) ⟨x, hx (some i)⟩) =
              f (some i) := by
          let e : C(U (some i), V i) :=
            ⟨fun y ↦ ⟨⟨y.1, hUA i y.2⟩, y.2⟩,
              (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
          have h := congrArg (fun g ↦ g.comp (FundamentalGroup.map e ⟨x, hx (some i)⟩)) (hdA i)
          have hr : (FundamentalGroup.map (r i) ⟨b, hxV i⟩).comp
              (FundamentalGroup.map e ⟨x, hx (some i)⟩) = MonoidHom.id _ := by
            -- These inverse retypings preserve the underlying path, including its endpoints.
            ext g
            induction g using Path.Homotopic.Quotient.ind
            rfl
          have he : (FundamentalGroup.map (ContinuousMap.subtypeVal (V i)) ⟨b, hxV i⟩).comp
              (FundamentalGroup.map e ⟨x, hx (some i)⟩) =
                FundamentalGroup.map (ContinuousMap.inclusion (hUA i)) ⟨x, hx (some i)⟩ :=
            (FundamentalGroup.map_comp (ContinuousMap.subtypeVal (V i)) e _).symm
          dsimp only [fv] at h
          erw [MonoidHom.comp_assoc, he, MonoidHom.comp_assoc, hr, MonoidHom.comp_id] at h
          exact h
        -- The pieces covering A ∩ B have the original triple intersections as double overlaps.
        have hABcompat : dA.comp (FundamentalGroup.map
              (ContinuousMap.inclusion inter_subset_left) ⟨x, hxA, hx none⟩) =
            (f none).comp (FundamentalGroup.map
              (ContinuousMap.inclusion inter_subset_right) ⟨x, hxA, hx none⟩) := by
          let W (i : α) : Set ↥(A ∩ B) := Subtype.val ⁻¹' U (some i)
          let z : ↥(A ∩ B) := ⟨x, hxA, hx none⟩
          have hxW (i : α) : z ∈ W i := hx (some i)
          apply vanKampenWide_hom_ext (U := W) (x := z) _ hxW
          · intro i j
            have hset : W i ∩ W j = ((↑) : ↥(A ∩ B) → X) ⁻¹'
                (U (some i) ∩ U (some j) ∩ B) := by
              ext y
              exact ⟨fun h ↦ ⟨h, y.2.2⟩, fun h ↦ h.1⟩
            rw [hset]
            exact (hTriple (some i) (some j) none).preimage_coe
              (subset_inter (inter_subset_left.trans inter_subset_left |>.trans (hUA i))
                inter_subset_right)
          · intro i
            let q : C(W i, ↥(U (some i) ∩ B)) :=
              ⟨fun y ↦ ⟨y.1.1, y.2, y.1.2.2⟩,
                (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
            have h := congrArg (fun g ↦ g.comp (FundamentalGroup.map q ⟨z, hxW i⟩))
              (hcompat (some i) none)
            have hi := congrArg (fun g ↦ g.comp (FundamentalGroup.map
              ((ContinuousMap.inclusion inter_subset_left).comp q) ⟨z, hxW i⟩)) (hdA' i)
            repeat' erw [MonoidHom.comp_assoc, ← FundamentalGroup.map_comp] at h
            repeat' erw [MonoidHom.comp_assoc, ← FundamentalGroup.map_comp] at hi
            repeat' erw [MonoidHom.comp_assoc, ← FundamentalGroup.map_comp]
            exact hi.trans h
          · intro y
            obtain ⟨i, hi⟩ := mem_iUnion.mp y.2.1
            exact ⟨i, ((hOpen (some i)).preimage continuous_subtype_val).mem_nhds hi⟩
        have hpcA : IsPathConnected A := by
          refine ⟨x, hxA, ?_⟩
          intro y hy
          obtain ⟨i, hi⟩ := mem_iUnion.mp hy
          have hp : IsPathConnected (U (some i)) := by simpa using hDouble (some i) (some i)
          exact (hp.joinedIn x (hx _) y hi).mono (hUA i)
        have hpcB : IsPathConnected B := by simpa only [B, inter_self] using hDouble none none
        have hpcAB : IsPathConnected (A ∩ B) := by
          refine ⟨x, ⟨hxA, hx none⟩, ?_⟩
          intro y hy
          obtain ⟨i, hi⟩ := mem_iUnion.mp hy.1
          exact ((hDouble (some i) none).joinedIn x ⟨hx _, hx _⟩ y ⟨hi, hy.2⟩).mono
            (inter_subset_inter_left B (hUA i))
        have hcoverAB : interior A ∪ interior B = univ := by
          rw [(isOpen_iUnion fun i ↦ hOpen (some i)).interior_eq, (hOpen none).interior_eq]
          apply eq_univ_of_forall
          intro y
          obtain ⟨i, hi⟩ := hCover y
          cases i with
          | none => exact Or.inr hi
          | some i => exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
        -- The final binary descent restricts to every previous member and to the new member.
        let d := vanKampenDesc hcoverAB hpcA hpcB hpcAB hxA (hx none) dA (f none) hABcompat
        refine ⟨d, ?_⟩
        intro i
        cases i with
        | none =>
          exact vanKampenDesc_comp_map_right hcoverAB hpcA hpcB hpcAB hxA (hx none)
            dA (f none) hABcompat
        | some i =>
          have h := congrArg (fun g ↦ g.comp (FundamentalGroup.map
            (ContinuousMap.inclusion (hUA i)) ⟨x, hx (some i)⟩))
            (vanKampenDesc_comp_map_left hcoverAB hpcA hpcB hpcAB hxA (hx none)
              dA (f none) hABcompat)
          erw [MonoidHom.comp_assoc, ← FundamentalGroup.map_comp] at h
          exact h.trans (hdA' i)
  exact hP X U x hOpen hCover hx hDouble hTriple f hcompat

end TauCeti
