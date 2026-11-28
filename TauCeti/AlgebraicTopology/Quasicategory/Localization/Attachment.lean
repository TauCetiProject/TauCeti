/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import TauCeti.AlgebraicTopology.Quasicategory.CoherentIso

/-!
# Attaching walking equivalences

For a simplicial set `C` and a set `W` of its edges, `C.equivalenceAttachment W` is the
pushout attaching a coherent isomorphism along every edge in `W`. A map from `C` to
a quasicategory extends across this pushout exactly when it inverts every edge of `W`.
Maps sending the marked edges to degenerate edges extend using constant maps on the
attached copies. The pushout itself need not be a quasicategory.

## References

* R. Haugseng, [*Introduction to ∞-Categories*]
  (https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Haugseng-intro.pdf),
  §6.5, especially the walking-equivalence pushout in the proof of Proposition 6.5.3
  and the localization construction in Corollary 6.5.4.
-/

public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet

/-- Attach one coherent isomorphism along each edge in `W`. -/
noncomputable def equivalenceAttachment (C : SSet.{u}) (W : Set (C _⦋1⦌)) : SSet.{u} :=
  pushout (Sigma.desc (fun w : W ↦ yonedaEquiv.symm w.val))
    (Limits.Sigma.map (fun _ : W ↦ coherentIso.edgeInclusion))

namespace equivalenceAttachment

variable {C D B : SSet.{u}} (W : Set (C _⦋1⦌))

/-- The canonical map to the attachment. -/
noncomputable def ι : C ⟶ C.equivalenceAttachment W := pushout.inl _ _

/-- The map from the coproduct of coherent isomorphisms to the attachment. -/
noncomputable def ofCoproduct : (∐ fun _ : W ↦ coherentIso.{u}) ⟶
    C.equivalenceAttachment W := pushout.inr _ _

/-- The canonical map from the coherent-isomorphism summand indexed by `w`
into the pushout. -/
noncomputable def ofEdge (w : W) : coherentIso ⟶ C.equivalenceAttachment W :=
  Sigma.ι (fun _ : W ↦ coherentIso.{u}) w ≫ ofCoproduct W

@[reassoc (attr := simp)]
lemma ι_ofCoproduct (w : W) :
    Sigma.ι (fun _ : W ↦ coherentIso.{u}) w ≫ ofCoproduct W = ofEdge W w := (rfl)

/-- The defining pushout square of the attachment. -/
theorem isPushout : IsPushout
    (Sigma.desc (fun w : W ↦ yonedaEquiv.symm w.val))
    (Limits.Sigma.map (fun _ : W ↦ coherentIso.edgeInclusion)) (ι W) (ofCoproduct W) :=
  IsPushout.of_hasPushout _ _

instance : Mono (ι W) :=
  (MorphismProperty.monomorphisms SSet).of_isPushout (isPushout W)
    (inferInstanceAs (Mono (Limits.Sigma.map (fun _ : W ↦ coherentIso.edgeInclusion))))

/-- The forward edge of an attached coherent isomorphism is the corresponding marked edge. -/
@[reassoc (attr := simp)]
lemma edgeInclusion_ofEdge (w : W) :
    coherentIso.edgeInclusion ≫ ofEdge W w = yonedaEquiv.symm w.val ≫ ι W := by
  have h := congrArg (fun f ↦ Sigma.ι (fun _ : W ↦ Δ[1]) w ≫ f) (isPushout W).w
  simpa using h.symm

/-- Descent to the attachment from maps agreeing along every marked edge. -/
noncomputable def desc (f : C ⟶ D) (g : W → (coherentIso ⟶ D))
    (h : ∀ w, coherentIso.edgeInclusion ≫ g w = yonedaEquiv.symm w.val ≫ f) :
    C.equivalenceAttachment W ⟶ D :=
  (isPushout W).desc f (Sigma.desc g) (by
    apply Sigma.hom_ext
    intro w
    simpa using (h w).symm)

@[reassoc (attr := simp)]
lemma ι_desc (f : C ⟶ D) (g : W → (coherentIso ⟶ D)) (h) :
    ι W ≫ desc W f g h = f := (isPushout W).inl_desc _ _ _

@[reassoc (attr := simp)]
lemma ofCoproduct_desc (f : C ⟶ D) (g : W → (coherentIso ⟶ D)) (h) :
    ofCoproduct W ≫ desc W f g h = Sigma.desc g := (isPushout W).inr_desc _ _ _

@[reassoc (attr := simp)]
lemma ofEdge_desc (f : C ⟶ D) (g : W → (coherentIso ⟶ D)) (h) (w : W) :
    ofEdge W w ≫ desc W f g h = g w := by
  rw [← ι_ofCoproduct, Category.assoc, ofCoproduct_desc, Sigma.ι_comp_desc]

/-- Maps out of the attachment are determined by their restrictions to `C` and every
attached coherent isomorphism. -/
@[ext]
theorem hom_ext {f g : C.equivalenceAttachment W ⟶ D}
    (hC : ι W ≫ f = ι W ≫ g) (hW : ∀ w, ofEdge W w ≫ f = ofEdge W w ≫ g) :
    f = g := by
  apply (isPushout W).hom_ext hC
  apply Sigma.hom_ext
  intro w
  simpa using hW w

/-- Reconstructing a map from its restrictions gives the original map. -/
@[simp]
lemma desc_restrict (f : C.equivalenceAttachment W ⟶ D) :
    desc W (ι W ≫ f) (fun w ↦ ofEdge W w ≫ f)
      (fun w ↦ by simp) = f := by
  apply hom_ext <;> simp

/-- A simplicial map preserving marked edges induces a map of attachments. -/
noncomputable def map {V : Set (D _⦋1⦌)} (f : C ⟶ D)
    (hf : ∀ w : W, f.app _ w.val ∈ V) :
    C.equivalenceAttachment W ⟶ D.equivalenceAttachment V :=
  desc W (f ≫ ι V) (fun w ↦ ofEdge V ⟨f.app _ w.val, hf w⟩)
    (fun w ↦ by simp [yonedaEquiv_symm_comp])

@[reassoc (attr := simp)]
lemma ι_map {V : Set (D _⦋1⦌)} (f : C ⟶ D) (hf : ∀ w : W, f.app _ w.val ∈ V) :
    ι W ≫ map W f hf = f ≫ ι V := ι_desc W _ _ _

@[reassoc (attr := simp)]
lemma ofEdge_map {V : Set (D _⦋1⦌)} (f : C ⟶ D) (hf : ∀ w : W, f.app _ w.val ∈ V)
    (w : W) :
    ofEdge W w ≫ map W f hf = ofEdge V ⟨f.app _ w.val, hf w⟩ := ofEdge_desc W _ _ _ w

/-- The identity map induces the identity on attachments. -/
@[simp]
lemma map_id : map W (𝟙 C) (fun w ↦ w.property) = 𝟙 (C.equivalenceAttachment W) := by
  apply hom_ext <;> simp

/-- Induced attachment maps preserve composition. -/
lemma map_comp {V : Set (D _⦋1⦌)} {U : Set (B _⦋1⦌)} (f : C ⟶ D) (g : D ⟶ B)
    (hf : ∀ w : W, f.app _ w.val ∈ V) (hg : ∀ v : V, g.app _ v.val ∈ U) :
    map W (f ≫ g) (fun w ↦ hg ⟨_, hf w⟩) = map W f hf ≫ map V g hg := by
  apply hom_ext <;> simp

/-- Descent is compatible with postcomposition. -/
@[reassoc]
lemma desc_comp (f : C ⟶ D) (g : W → (coherentIso ⟶ D)) (h) (k : D ⟶ B) :
    desc W f g h ≫ k = desc W (f ≫ k) (fun w ↦ g w ≫ k)
      (fun w ↦ by rw [← Category.assoc, h w, Category.assoc]) := by
  apply hom_ext <;> simp

/-- Every marked edge becomes an equivalence in the attachment. No fibrancy is assumed. -/
theorem isEquivalence_map (w : W) :
    (Edge.mk' ((ι W).app _ w.val)).IsEquivalence := by
  have h : yonedaEquiv (yonedaEquiv.symm w.val ≫ ι W) = (ι W).app _ w.val :=
    (yonedaEquiv_comp _ _).trans
      (congrArg ((ι W).app _) (yonedaEquiv.apply_symm_apply w.val))
  exact h ▸ isEquivalence_of_extension_coherentIso (edgeInclusion_ofEdge W w)

/-- Any extension across the attachment sends every marked edge to an equivalence,
without a fibrancy assumption on the target. -/
theorem isEquivalence_of_extension {f : C ⟶ D} {g : C.equivalenceAttachment W ⟶ D}
    (h : ι W ≫ g = f) (w : W) : (Edge.mk' (f.app _ w.val)).IsEquivalence := by
  subst f
  exact (Edge.isEquivalence_iff_of_edge_eq (by
    simp only [Edge.map_edge, Edge.mk'_edge, NatTrans.comp_app, types_comp_apply])).1
      ((isEquivalence_map W w).map g)

/-- A map to a quasicategory extends across the attachment if and only if it sends
all the marked edges to equivalences. -/
theorem exists_extension_iff [Quasicategory D] (f : C ⟶ D) :
    (∃ g : C.equivalenceAttachment W ⟶ D, ι W ≫ g = f) ↔
      ∀ w : W, (Edge.mk' (f.app _ w.val)).IsEquivalence := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨g, hg⟩ w
    exact isEquivalence_of_extension W hg w
  · have h' (w : W) : ∃ g : coherentIso ⟶ D,
        coherentIso.edgeInclusion ≫ g = yonedaEquiv.symm w.val ≫ f :=
      (exists_extension_coherentIso_iff _).2 (by
        rw [yonedaEquiv_symm_comp, yonedaEquiv.apply_symm_apply]
        exact h w)
    choose g hg using h'
    exact ⟨desc W f g hg, ι_desc W f g hg⟩

/-- When a map sends each marked edge to the degenerate edge at a specified vertex,
it extends by the constant map on each attached coherent isomorphism. -/
noncomputable def descOfDegenerate (p : C ⟶ B) (b : W → B _⦋0⦌)
    (h : ∀ w, p.app _ w.val = B.σ 0 (b w)) : C.equivalenceAttachment W ⟶ B :=
  desc W p (fun w ↦ const (b w)) (fun w ↦ by
    rw [comp_const, yonedaEquiv_symm_comp, h w, σ_zero_eq_yonedaEquiv_const,
      yonedaEquiv.symm_apply_apply])

@[reassoc (attr := simp)]
lemma ι_descOfDegenerate (p : C ⟶ B) (b : W → B _⦋0⦌) (h) :
    ι W ≫ descOfDegenerate W p b h = p := ι_desc W _ _ _

@[reassoc (attr := simp)]
lemma ofEdge_descOfDegenerate (p : C ⟶ B) (b : W → B _⦋0⦌) (h) (w : W) :
    ofEdge W w ≫ descOfDegenerate W p b h = const (b w) := ofEdge_desc W _ _ _ w

section StandardEdge

private noncomputable def stdSimplexOneHom :
    (Δ[1] : SSet.{u}).equivalenceAttachment {yonedaEquiv (𝟙 Δ[1])} ⟶ coherentIso :=
  desc _ coherentIso.edgeInclusion (fun _ ↦ 𝟙 coherentIso) (fun v ↦ by
    rw [Set.mem_singleton_iff.1 v.property]
    simp)

@[reassoc (attr := simp)]
private lemma ι_stdSimplexOneHom :
    ι {yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))} ≫ stdSimplexOneHom =
      coherentIso.edgeInclusion := ι_desc _ _ _ _

@[reassoc (attr := simp)]
private lemma ofEdge_stdSimplexOneHom
    (w : ({yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))} : Set (Δ[1] _⦋1⦌))) :
    ofEdge _ w ≫ stdSimplexOneHom = 𝟙 coherentIso := ofEdge_desc _ _ _ _ w

private lemma stdSimplexOneHom_ofEdge :
    stdSimplexOneHom.{u} ≫ ofEdge _ ⟨_, Set.mem_singleton _⟩ = 𝟙 _ := by
  apply hom_ext
  · simp
  · intro v
    have hv : v = ⟨_, Set.mem_singleton _⟩ :=
      Subtype.ext (Set.mem_singleton_iff.1 v.property)
    simp [hv]

/-- Attaching a coherent isomorphism to the distinguished edge of the standard interval
gives the coherent isomorphism itself. -/
noncomputable def stdSimplexOneIso :
    (Δ[1] : SSet.{u}).equivalenceAttachment {yonedaEquiv (𝟙 Δ[1])} ≅ coherentIso where
  hom := stdSimplexOneHom
  inv := ofEdge _ ⟨_, Set.mem_singleton _⟩
  hom_inv_id := stdSimplexOneHom_ofEdge
  inv_hom_id := ofEdge_stdSimplexOneHom _

@[simp]
lemma stdSimplexOneIso_inv :
    stdSimplexOneIso.{u}.inv = ofEdge _ ⟨_, Set.mem_singleton _⟩ := (rfl)

@[reassoc (attr := simp)]
lemma ι_stdSimplexOneIso_hom :
    ι {yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))} ≫ stdSimplexOneIso.hom =
      coherentIso.edgeInclusion := ι_stdSimplexOneHom

end StandardEdge

end equivalenceAttachment

end SSet
