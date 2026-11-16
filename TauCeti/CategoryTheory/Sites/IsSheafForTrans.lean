/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Topology.Category.TopCat.Opens
import TauCeti.CategoryTheory.Sites.IsSheafFor

/-!
# Transitivity and transport of the sheaf condition for covers of opens

Let `W` be an open set, `Y i ≤ W` opens for which a presheaf of types `F` satisfies the sheaf
condition, and `S` a sieve on `W` whose members each lie in some `Y i`. If `F` is a sheaf for the
restriction of `S` to each `Y i` and separated for the restriction of `S` to each `Y i ⊓ Y j`,
then `F` is a sheaf for `S`: sections over the members of `S` glue first over each `Y i`, the
gluings agree on the overlaps `Y i ⊓ Y j`, and so glue over `W`.

Mathlib's `CategoryTheory.Presieve.isSheafFor_trans` proves a transitivity statement of this
kind for sieves on an arbitrary category, but it asks for the sheaf condition of `S` restricted to
*every* open contained in some `Y i`. Since there is at most one morphism between two opens, two
sections over `Y i` and `Y j` are compatible as soon as they agree on `Y i ⊓ Y j`, so here the
hypotheses concern only the opens `Y i` and `Y i ⊓ Y j`. This makes the statement usable when the
sheaf condition is known only on a basis of opens closed under finite intersections, such as the
rational subsets of an adic spectrum, where a cover is refined by covering each of its members.

The sheaf condition can also be transported between presheaves on different spaces. Let `φ` be a
monotone map of opens preserving binary meets, and suppose that sections of `F` over the opens in
a family `S` closed under binary meets correspond bijectively, compatibly with restriction, to
sections of `G` over their images under `φ`. Then `F` satisfies the sheaf condition for a family
of opens in `S` exactly when `G` does for the images. This reduces the sheaf condition over an open
such as the rational subset `R(T/s)` of an adic spectrum to the corresponding condition on another
space, along a meet-preserving map of opens.

## Main results

* `TauCeti.TopologicalSpace.Opens.isSheafFor_trans` : the transitivity statement.
* `TauCeti.TopologicalSpace.Opens.isSheafFor_ofArrows_iff_of_equiv` : the sheaf condition for a
  cover holds exactly when it holds for the transported cover, along bijections of sections that
  commute with restriction and a meet-preserving map of opens.
-/

public section

open CategoryTheory Opposite _root_.TopologicalSpace

universe u w

namespace TauCeti.TopologicalSpace.Opens

variable {X : Type u} [_root_.TopologicalSpace X] {F : (Opens X)ᵒᵖ ⥤ Type w}

/-- **Transitivity of the sheaf condition along a cover of an open set.** Let `Y i ≤ W` be opens
covering `W` in the sense that `F` is a sheaf for the family of inclusions `Y i ⟶ W`, and let `S`
be a sieve on `W` each of whose members lies in some `Y i`. If `F` is a sheaf for the restriction
of `S` to every `Y i`, and separated for the restriction of `S` to every `Y i ⊓ Y j`, then `F` is
a sheaf for `S`.

Compare `CategoryTheory.Presieve.isSheafFor_trans`, which instead asks for the sheaf condition of
the restriction of `S` to every open contained in some `Y i`. -/
theorem isSheafFor_trans {W : Opens X} {ι : Type*} (Y : ι → Opens X) (hY : ∀ i, Y i ≤ W)
    (S : Sieve W) (hR : (Presieve.ofArrows Y fun i ↦ homOfLE (hY i)).IsSheafFor F)
    (hS : ∀ i, (S.pullback (homOfLE (hY i))).arrows.IsSheafFor F)
    (hS₂ : ∀ i j, (S.pullback
      (homOfLE (inf_le_left.trans (hY i)) : Y i ⊓ Y j ⟶ W)).arrows.IsSeparatedFor F)
    (hSY : ∀ ⦃V : Opens X⦄ (f : V ⟶ W), S f → ∃ i, V ≤ Y i) :
    S.arrows.IsSheafFor F := by
  intro x hx
  -- glue the restriction of `x` to each `Y i`
  choose t ht ht' using fun i ↦ hS i (x.pullback (homOfLE (hY i))) (hx.pullback _)
  -- the glued sections restrict to amalgamations of `x` on `Y i ⊓ Y j`, so they agree there
  have hcompat : Presieve.Arrows.Compatible F (fun i ↦ homOfLE (hY i)) t := by
    refine (Presieve.Arrows.compatible_homOfLE_iff hY t).2 fun i j ↦ ?_
    -- Arrows between opens encode proofs of inclusion, so proof irrelevance identifies
    -- the composite arrows indexing `x` with those in `x.pullback`.
    refine hS₂ i j (x.pullback _) _ _ (fun V g hg ↦ ?_) (fun V g hg ↦ ?_)
    · rw [← Functor.map_comp_apply, ← op_comp,
        ht i (g ≫ homOfLE inf_le_left) (by simpa using hg)]
      rfl
    · rw [← Functor.map_comp_apply, ← op_comp,
        ht j (g ≫ homOfLE inf_le_right) (by simpa using hg)]
      rfl
  obtain ⟨s, hs, hs'⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hR t hcompat
  refine ⟨s, fun V f hf ↦ ?_, fun s' hs'' ↦ hs' s' fun i ↦ ht' i _ fun V g hg ↦ ?_⟩
  · -- `s` restricts to `x` on every member of `S`, through the `Y i` containing it
    obtain ⟨i, hi⟩ := hSY f hf
    obtain rfl : f = homOfLE hi ≫ homOfLE (hY i) := Subsingleton.elim _ _
    rw [op_comp, Functor.map_comp_apply, hs i]
    exact ht i _ hf
  · -- any other amalgamation restricts to the amalgamation of `x` on each `Y i`
    rw [← Functor.map_comp_apply, ← op_comp, hs'' _ hg]
    -- `FamilyOfElements.pullback` evaluates `x` at the composite arrow
    rfl

/-- **The sheaf condition for a cover transports along compatible bijections of sections.** Let
`φ` be a monotone map of opens preserving binary meets, `F` a presheaf of types on `X` and `G` one
on `Y`, `S` a family of opens of `X` closed under binary meets and containing `W` and every `U i`,
and `U i ≤ W` a family of opens of `X`. If sections of `F` over each `V ∈ S` below `W` correspond
bijectively to sections of `G` over `φ V`, compatibly with restriction, then `F` satisfies the
sheaf condition for the family `U i ≤ W` exactly when `G` satisfies it for the family
`φ (U i) ≤ φ W`. -/
theorem isSheafFor_ofArrows_iff_of_equiv {Y : Type*} [_root_.TopologicalSpace Y]
    {G : (Opens Y)ᵒᵖ ⥤ Type w} (φ : Opens X → Opens Y) (hφ : Monotone φ)
    (hφinf : ∀ V V', φ (V ⊓ V') = φ V ⊓ φ V') {S : Set (Opens X)}
    (hSinf : ∀ V ∈ S, ∀ V' ∈ S, V ⊓ V' ∈ S) {W : Opens X} (hW : W ∈ S)
    {ι : Type*} {U : ι → Opens X} (hU : ∀ i, U i ∈ S) (hUW : ∀ i, U i ≤ W)
    (σ : ∀ V ∈ S, V ≤ W → (F.obj (op V) ≃ G.obj (op (φ V))))
    (hσ : ∀ (V V' : Opens X) (hV : V ∈ S) (hV' : V' ∈ S) (hVW : V ≤ W) (h : V' ≤ V)
      (x : F.obj (op V)), σ V' hV' (h.trans hVW) (F.map (homOfLE h).op x) =
        G.map (homOfLE (hφ h)).op (σ V hV hVW x)) :
    (Presieve.ofArrows U fun i ↦ homOfLE (hUW i)).IsSheafFor F ↔
      (Presieve.ofArrows (fun i ↦ φ (U i)) fun i ↦ homOfLE (hφ (hUW i))).IsSheafFor G := by
  rw [Presieve.isSheafFor_arrows_iff, Presieve.isSheafFor_arrows_iff]
  have hl (i j : ι) : (homOfLE inf_le_left : φ (U i) ⊓ φ (U j) ⟶ φ (U i)) =
      homOfLE (hφinf (U i) (U j)).ge ≫ homOfLE (hφ (inf_le_left : U i ⊓ U j ≤ U i)) := rfl
  have hr (i j : ι) : (homOfLE inf_le_right : φ (U i) ⊓ φ (U j) ⟶ φ (U j)) =
      homOfLE (hφinf (U i) (U j)).ge ≫ homOfLE (hφ (inf_le_right : U i ⊓ U j ≤ U j)) := rfl
  refine ⟨fun hF y hy ↦ ?_, fun hG x hx ↦ ?_⟩
  · -- pull `y` back along `σ`, glue in `F`, and push the gluing forward
    have hx : Presieve.Arrows.Compatible F (fun i ↦ homOfLE (hUW i))
        (fun i ↦ (σ (U i) (hU i) (hUW i)).symm (y i)) := by
      rw [Presieve.Arrows.compatible_homOfLE_iff]
      intro i j
      have hUij := hSinf _ (hU i) _ (hU j)
      refine (σ _ hUij (inf_le_left.trans (hUW i))).injective ?_
      rw [hσ _ _ (hU i) hUij (hUW i) inf_le_left,
        hσ _ _ (hU j) hUij (hUW j) inf_le_right, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      have h := (Presieve.Arrows.compatible_homOfLE_iff _ y).mp hy i j
      rw [hl, hr, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply] at h
      -- the map `φ (U i ⊓ U j) = φ (U i) ⊓ φ (U j)` is an identification of opens
      refine (?_ : Function.Injective (G.map (homOfLE (hφinf (U i) (U j)).ge).op)) h
      intro a b hab
      have hab' := congrArg (G.map (homOfLE (hφinf (U i) (U j)).le).op) hab
      rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
        Subsingleton.elim (homOfLE (hφinf (U i) (U j)).le ≫ homOfLE (hφinf (U i) (U j)).ge) (𝟙 _),
        op_id, CategoryTheory.Functor.map_id] at hab'
    obtain ⟨t, ht, hu⟩ := hF _ hx
    refine ⟨σ W hW le_rfl t, fun i ↦ ?_, fun c hc ↦ ?_⟩
    · rw [← hσ W (U i) hW (hU i) le_rfl (hUW i), ht i, Equiv.apply_symm_apply]
    · have h := hu ((σ W hW le_rfl).symm c) fun i ↦ by
        refine (σ (U i) (hU i) (hUW i)).injective ?_
        rw [hσ W (U i) hW (hU i) le_rfl (hUW i), Equiv.apply_symm_apply, hc i,
          Equiv.apply_symm_apply]
      rw [← h, Equiv.apply_symm_apply]
  · -- push `x` forward along `σ`, glue in `G`, and pull the gluing back
    have hy : Presieve.Arrows.Compatible G (fun i ↦ homOfLE (hφ (hUW i)))
        (fun i ↦ σ (U i) (hU i) (hUW i) (x i)) := by
      rw [Presieve.Arrows.compatible_homOfLE_iff]
      intro i j
      have hUij := hSinf _ (hU i) _ (hU j)
      rw [hl, hr, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
        ← hσ _ _ (hU i) hUij (hUW i) inf_le_left, ← hσ _ _ (hU j) hUij (hUW j) inf_le_right,
        (Presieve.Arrows.compatible_homOfLE_iff hUW x).mp hx i j]
    obtain ⟨c, hc, hcu⟩ := hG _ hy
    refine ⟨(σ W hW le_rfl).symm c, fun i ↦ ?_, fun t ht ↦ ?_⟩
    · apply (σ (U i) (hU i) (hUW i)).injective
      have := hσ W (U i) hW (hU i) le_rfl (hUW i) ((σ W hW le_rfl).symm c)
      rw [Equiv.apply_symm_apply] at this
      exact this.trans (hc i)
    · apply (σ W hW le_rfl).injective
      rw [Equiv.apply_symm_apply]
      refine hcu _ fun i ↦ ?_
      have := hσ W (U i) hW (hU i) le_rfl (hUW i) t
      rw [ht i] at this
      exact this.symm

end TauCeti.TopologicalSpace.Opens
