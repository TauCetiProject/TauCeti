/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import Mathlib.Topology.Constructions.SumProd

/-!
# The topological double along a subset

`TauCeti.DoubleAlong A` is the native topological pushout of the inclusion `A ↪ X` with itself.
The subset need not be open or closed. The two copies have a common continuous retraction, the
fold, so each copy is embedded even for arbitrary `A`. The swap exchanges the two copies and
fixes precisely their common image, namely the image of `A`.

Closedness of `A` is reserved for the separation and countability results in `Separation`.
This construction concerns topological spaces: an analytic doubled atlas and an antiholomorphic
involution require additional chart compatibility.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, the double of a
  bordered Riemann surface.
-/

public section

open CategoryTheory Limits Topology Set

universe u v

namespace TauCeti

variable {X : Type u} [TopologicalSpace X]

/-- Two copies of a space glued by the identity along a subset, with the native pushout topology.
No openness, closedness, or separation assumption is imposed. -/
@[expose] noncomputable def DoubleAlong (A : Set X) : Type u :=
  (pushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
    (TopCat.ofHom (ContinuousMap.subtypeVal A)) : TopCat)

namespace DoubleAlong

variable (A : Set X)

noncomputable instance : TopologicalSpace (DoubleAlong A) :=
  inferInstanceAs (TopologicalSpace
    (pushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A)) : TopCat))

/-- The first copy of the original space in its double. -/
noncomputable def inl : C(X, DoubleAlong A) :=
  (pushout.inl (TopCat.ofHom (ContinuousMap.subtypeVal A))
    (TopCat.ofHom (ContinuousMap.subtypeVal A))).hom

/-- The second copy of the original space in its double. -/
noncomputable def inr : C(X, DoubleAlong A) :=
  (pushout.inr (TopCat.ofHom (ContinuousMap.subtypeVal A))
    (TopCat.ofHom (ContinuousMap.subtypeVal A))).hom

/-- The first continuous sheet map is the native pushout injection. -/
theorem inl_eq_pushout_inl : inl A =
    (pushout.inl (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A))).hom := by
  unfold inl
  rfl

/-- The second continuous sheet map is the native pushout injection. -/
theorem inr_eq_pushout_inr : inr A =
    (pushout.inr (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A))).hom := by
  unfold inr
  rfl

/-- The two inclusions agree at every point of the glued subset. -/
theorem inl_coe_eq_inr (x : A) : inl A x = inr A x :=
  congrArg (fun f : TopCat.of A ⟶ _ ↦ f x) (pushout.condition
    (f := TopCat.ofHom (ContinuousMap.subtypeVal A))
    (g := TopCat.ofHom (ContinuousMap.subtypeVal A)))

-- Native same-universe descent bootstraps the fold and swap before the sum quotient is known.
-- The public `desc` below uses that quotient and permits an arbitrary target universe.
private noncomputable def descSame {Y : Type u} [TopologicalSpace Y] (f g : C(X, Y))
    (h : ∀ x : A, f x = g x) : C(DoubleAlong A, Y) :=
  (pushout.desc (f := TopCat.ofHom (ContinuousMap.subtypeVal A))
    (g := TopCat.ofHom (ContinuousMap.subtypeVal A)) (TopCat.ofHom f) (TopCat.ofHom g) (by
    ext x
    exact h x)).hom

@[simp]
private theorem descSame_inl {Y : Type u} [TopologicalSpace Y] (f g : C(X, Y))
    (h : ∀ x : A, f x = g x) (x : X) : descSame A f g h (inl A x) = f x := by
  exact congrArg (fun k : TopCat.of X ⟶ _ ↦ k x) (pushout.inl_desc
    (f := TopCat.ofHom (ContinuousMap.subtypeVal A))
    (g := TopCat.ofHom (ContinuousMap.subtypeVal A)) _ _ _)

@[simp]
private theorem descSame_inr {Y : Type u} [TopologicalSpace Y] (f g : C(X, Y))
    (h : ∀ x : A, f x = g x) (x : X) : descSame A f g h (inr A x) = g x := by
  exact congrArg (fun k : TopCat.of X ⟶ _ ↦ k x) (pushout.inr_desc
    (f := TopCat.ofHom (ContinuousMap.subtypeVal A))
    (g := TopCat.ofHom (ContinuousMap.subtypeVal A)) _ _ _)

/-- Every point of the double lies on one of its two copies. -/
theorem exists_inl_or_inr (z : DoubleAlong A) :
    (∃ x, inl A x = z) ∨ ∃ x, inr A x = z :=
  Types.eq_or_eq_of_isPushout
    ((forget TopCat).map_isPushout
      (IsPushout.of_hasPushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
        (TopCat.ofHom (ContinuousMap.subtypeVal A)))) z

@[elab_as_elim]
theorem induction_on {P : DoubleAlong A → Prop} (z : DoubleAlong A)
    (hl : ∀ x, P (inl A x)) (hr : ∀ x, P (inr A x)) : P z := by
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := exists_inl_or_inr A z
  · exact hl x
  · exact hr x

/-- Continuous maps from the double agree if they agree on both copies. -/
@[ext]
theorem hom_ext {Y : Type v} [TopologicalSpace Y] {f g : C(DoubleAlong A, Y)}
    (hl : ∀ x, f (inl A x) = g (inl A x)) (hr : ∀ x, f (inr A x) = g (inr A x)) : f = g := by
  ext z
  exact induction_on A z hl hr

/-- The fold sends a point of either copy to its original point. -/
noncomputable def fold : C(DoubleAlong A, X) :=
  descSame A (ContinuousMap.id X) (ContinuousMap.id X) fun _ ↦ rfl

@[simp]
theorem fold_inl (x : X) : fold A (inl A x) = x := descSame_inl _ _ _ _ _

@[simp]
theorem fold_inr (x : X) : fold A (inr A x) = x := descSame_inr _ _ _ _ _

/-- Each sheet is embedded, even when the glued subset is not closed. -/
theorem isEmbedding_inl : IsEmbedding (inl A) :=
  Function.LeftInverse.isEmbedding (fold_inl A)
    (fold A).continuous (inl A).continuous

/-- Each sheet is embedded, even when the glued subset is not closed. -/
theorem isEmbedding_inr : IsEmbedding (inr A) :=
  Function.LeftInverse.isEmbedding (fold_inr A)
    (fold A).continuous (inr A).continuous

@[simp]
theorem inl_eq_inl_iff {x y : X} : inl A x = inl A y ↔ x = y :=
  (isEmbedding_inl A).injective.eq_iff

@[simp]
theorem inr_eq_inr_iff {x y : X} : inr A x = inr A y ↔ x = y :=
  (isEmbedding_inr A).injective.eq_iff

/-- Points on opposite sheets are identified exactly along the glued subset. -/
@[simp]
theorem inl_eq_inr_iff {x y : X} : inl A x = inr A y ↔ x = y ∧ x ∈ A := by
  have h := Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    ((forget TopCat).map_isPushout
      (IsPushout.of_hasPushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
        (TopCat.ofHom (ContinuousMap.subtypeVal A)))).isColimit
    Subtype.val_injective x y
  -- Forgetting the native pushout identifies its cocone maps with the continuous sheet maps.
  change inl A x = inr A y ↔ (∃ a : A, a.val = x ∧ a.val = y) at h
  rw [h]
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨ha.symm.trans hb, ha ▸ a.property⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨⟨x, hx⟩, rfl, rfl⟩

@[simp]
theorem inr_eq_inl_iff {x y : X} : inr A x = inl A y ↔ x = y ∧ x ∈ A := by
  rw [eq_comm, inl_eq_inr_iff]
  constructor <;> rintro ⟨rfl, hx⟩ <;> exact ⟨rfl, hx⟩

/-- The sheet-exchanging involution of the double. -/
noncomputable def swap : DoubleAlong A ≃ₜ DoubleAlong A where
  toFun := descSame A (inr A) (inl A) fun x ↦ (inl_coe_eq_inr A x).symm
  invFun := descSame A (inr A) (inl A) fun x ↦ (inl_coe_eq_inr A x).symm
  left_inv z := induction_on A z (by simp) (by simp)
  right_inv z := induction_on A z (by simp) (by simp)
  continuous_toFun := (descSame A _ _ _).continuous
  continuous_invFun := (descSame A _ _ _).continuous

@[simp]
theorem swap_inl (x : X) : swap A (inl A x) = inr A x := descSame_inl _ _ _ _ _

@[simp]
theorem swap_inr (x : X) : swap A (inr A x) = inl A x := descSame_inr _ _ _ _ _

@[simp]
theorem swap_swap (z : DoubleAlong A) : swap A (swap A z) = z :=
  (swap A).left_inv z

@[simp]
theorem fold_swap (z : DoubleAlong A) : fold A (swap A z) = fold A z :=
  induction_on A z (by simp) (by simp)

/-- The swap fixes exactly the glued subset on the two copies. -/
@[simp]
theorem swap_eq_self_iff (z : DoubleAlong A) : swap A z = z ↔ fold A z ∈ A := by
  induction z using induction_on A with
  | hl x => simp
  | hr x => simp

/-- The fixed locus is the image of the glued subset on either sheet. -/
theorem fixed_locus : {z | swap A z = z} = inl A '' A := by
  ext z
  rw [mem_ofPred_eq, swap_eq_self_iff]
  exact induction_on A z (by simp) (by simp)

/-- The canonical map from the disjoint union of the two sheets. -/
noncomputable def quotientMap : C(X ⊕ X, DoubleAlong A) :=
  ⟨Sum.elim (inl A) (inr A), (inl A).continuous.sumElim (inr A).continuous⟩

/-- The canonical sum map evaluates by the appropriate continuous sheet inclusion. -/
theorem coe_quotientMap : ⇑(quotientMap A) = Sum.elim (inl A) (inr A) := by
  simp [quotientMap]

@[simp]
theorem quotientMap_inl (x : X) : quotientMap A (Sum.inl x) = inl A x := by simp [quotientMap]

@[simp]
theorem quotientMap_inr (x : X) : quotientMap A (Sum.inr x) = inr A x := by simp [quotientMap]

theorem quotientMap_surjective : Function.Surjective (quotientMap A) := by
  intro z
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := exists_inl_or_inr A z
  · exact ⟨Sum.inl x, rfl⟩
  · exact ⟨Sum.inr x, rfl⟩

/-- The pushout topology is exactly the topology detected on both sheets. -/
theorem isClosed_iff (s : Set (DoubleAlong A)) :
    IsClosed s ↔ IsClosed (inl A ⁻¹' s) ∧ IsClosed (inr A ⁻¹' s) :=
  TauCeti.TopCat.isClosed_iff_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) s

/-- The canonical sum map is a quotient map for every glued subset. It need not be open. -/
theorem isQuotientMap_quotientMap : IsQuotientMap (quotientMap A) := by
  refine isQuotientMap_iff_isClosed.2 ⟨quotientMap_surjective A, fun s ↦ ?_⟩
  rw [isClosed_iff, isClosed_sum_iff]
  rfl

/-- Define a continuous map into an arbitrary universe from maps agreeing on the glued subset.
The construction uses the native quotient-map lift. -/
noncomputable def desc {Y : Type v} [TopologicalSpace Y] (f g : C(X, Y))
    (h : ∀ x : A, f x = g x) : C(DoubleAlong A, Y) :=
  (isQuotientMap_quotientMap A).lift
    ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩ (by
      intro x y hxy
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg f ((inl_eq_inl_iff A).1 hxy)
        | inr y =>
          obtain ⟨rfl, hx⟩ := (inl_eq_inr_iff A).1 hxy
          exact h ⟨x, hx⟩
      | inr x =>
        cases y with
        | inl y =>
          obtain ⟨rfl, hx⟩ := (inr_eq_inl_iff A).1 hxy
          exact (h ⟨x, hx⟩).symm
        | inr y => exact congrArg g ((inr_eq_inr_iff A).1 hxy))

@[simp]
theorem desc_inl {Y : Type v} [TopologicalSpace Y] (f g : C(X, Y))
    (h : ∀ x : A, f x = g x) (x : X) : desc A f g h (inl A x) = f x := by
  unfold desc
  simpa only [ContinuousMap.comp_apply, quotientMap_inl, ContinuousMap.coe_mk, Sum.elim_inl] using
    congrArg (fun k : C(X ⊕ X, Y) ↦ k (Sum.inl x))
      ((isQuotientMap_quotientMap A).lift_comp
        (⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩ : C(X ⊕ X, Y)) _)

@[simp]
theorem desc_inr {Y : Type v} [TopologicalSpace Y] (f g : C(X, Y))
    (h : ∀ x : A, f x = g x) (x : X) : desc A f g h (inr A x) = g x := by
  unfold desc
  simpa only [ContinuousMap.comp_apply, quotientMap_inr, ContinuousMap.coe_mk, Sum.elim_inr] using
    congrArg (fun k : C(X ⊕ X, Y) ↦ k (Sum.inr x))
      ((isQuotientMap_quotientMap A).lift_comp
        (⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩ : C(X ⊕ X, Y)) _)

/-- Continuity on the double can be checked on its two sheets, for an arbitrary target space. -/
theorem continuous_iff {Y : Type v} [TopologicalSpace Y] {f : DoubleAlong A → Y} :
    Continuous f ↔ Continuous (f ∘ inl A) ∧ Continuous (f ∘ inr A) := by
  rw [(isQuotientMap_quotientMap A).continuous_iff]
  have hcomp : f ∘ quotientMap A = Sum.elim (f ∘ inl A) (f ∘ inr A) := by
    funext x
    cases x <;> rfl
  rw [hcomp, continuous_sumElim]

/-- Fibres of the canonical sum quotient have at most two points, without a closedness premise. -/
theorem finite_fiber_quotientMap (z : DoubleAlong A) :
    (quotientMap A ⁻¹' {z}).Finite := by
  refine (Set.toFinite {Sum.inl (fold A z), Sum.inr (fold A z)}).subset ?_
  intro w hw
  have h := congrArg (fold A) (mem_singleton_iff.1 hw)
  cases w with
  | inl x =>
    simp only [quotientMap_inl, fold_inl] at h
    simp [h]
  | inr x =>
    simp only [quotientMap_inr, fold_inr] at h
    simp [h]

/-- A double of a compact space is compact, even if the glued subset is not closed. -/
instance [CompactSpace X] : CompactSpace (DoubleAlong A) :=
  (quotientMap_surjective A).compactSpace (quotientMap A).continuous

end DoubleAlong
end TauCeti
