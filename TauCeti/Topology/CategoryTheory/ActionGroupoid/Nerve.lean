/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import TauCeti.Topology.CategoryTheory.ActionGroupoid
public import TauCeti.Topology.CategoryTheory.Nerve

/-!
# The topological nerve and classifying space of an action groupoid

Let a topological monoid `G` act continuously on `X`, and give Mathlib's native action category
`CategoryTheory.ActionCategory G X` the object and total-arrow topologies of
`TauCeti.Topology.CategoryTheory.ActionGroupoid`. A string of `n` composable arrows
`x₀ ⟶ x₁ ⟶ ⋯ ⟶ xₙ` is then determined by its first point `x₀` and the labels `gₖ` of its
consecutive arrows, with `xₖ₊₁ = gₖ • xₖ`. This file proves that these coordinates identify the
`n`-simplices of the topological nerve with `X × Gⁿ` as topological spaces
(`TauCeti.ActionGroupoid.nerveHomeomorph`). So the topology of `TauCeti.topologicalNerve`, built
from all arrows of a string, is the iterated fiber-product topology of composable strings. Every
label is retained, including labels acting trivially.

For a group action, the orbit of any vertex of a simplex is the same. This gives an augmentation
of the topological nerve over the orbit space `MulAction.orbitRel.Quotient G X`
(`TauCeti.ActionGroupoid.coarseAugmentation`), and hence the continuous surjective coarse map
`TauCeti.ActionGroupoid.coarseMap` from the fat classifying space `B(G ⋉ X)` to the coarse space
`X / G`, sending each point to the orbit of any vertex of its simplex (`coarseMap_ι`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112,
  Section 3.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Topology MulOpposite
open CategoryTheory.ActionCategory

namespace TauCeti.ActionGroupoid

section Monoid

variable {G X : Type*} [Monoid G] [MulAction G X] {n : ℕ}

/-- In a string of composable arrows of an action category, the arrow from the `i`-th object to
itself has label `1`. -/
private theorem hom_map_homOfLE_refl (F : ComposableArrows (ActionCategory G X) n)
    (i : Fin (n + 1)) : (F.map (homOfLE (le_refl i))).hom = (1 : G) := by
  simp

/-- In a string of composable arrows of an action category, the label of the arrow from the `i`-th
to the `(k + 1)`-th object is the `k`-th consecutive label times the label of the arrow from the
`i`-th to the `k`-th object. -/
private theorem hom_map_homOfLE_succ (F : ComposableArrows (ActionCategory G X) n)
    {i : Fin (n + 1)} {k : Fin n} (hik : i ≤ k.castSucc) :
    (F.map (homOfLE (hik.trans k.castSucc_le_succ))).hom =
      ((F.map (homOfLE k.castSucc_le_succ)).hom : G) * (F.map (homOfLE hik)).hom := by
  rw [← homOfLE_comp, F.map_comp, ActionCategory.comp_hom]

/-- The point underlying the `i`-th object of a string of composable arrows of an action category
is the label of the arrow from the first object, applied to the first point. -/
private theorem back_obj (F : ComposableArrows (ActionCategory G X) n) (i : Fin (n + 1)) :
    (F.obj i).back = ((F.map (homOfLE (Fin.zero_le i))).hom : G) • (F.obj 0).back :=
  (F.map (homOfLE (Fin.zero_le i))).map_val.symm

/-- Induction over the arrows `i ⟶ j` of a string of composable arrows, adding one consecutive
arrow at a time. -/
private theorem le_induction {P : ∀ i j : Fin (n + 1), i ≤ j → Prop}
    (refl : ∀ i, P i i le_rfl)
    (succ : ∀ i (k : Fin n) (hik : i ≤ k.castSucc), P i k.castSucc hik →
      P i k.succ (hik.trans k.castSucc_le_succ))
    (i j : Fin (n + 1)) (hij : i ≤ j) : P i j hij := by
  induction j using Fin.induction with
  | zero => obtain rfl := Fin.le_zero_iff.1 hij; exact refl 0
  | succ k ih =>
    by_cases hik : i ≤ k.castSucc
    · exact succ i k hik (ih hik)
    · obtain rfl : i = k.succ := le_antisymm hij (Fin.castSucc_lt_iff_succ_le.1 (not_le.1 hik))
      exact refl _

/-- Two strings of composable arrows of an action category with the same first point and the
same consecutive labels are equal. -/
theorem nerve_ext {F F' : ComposableArrows (ActionCategory G X) n}
    (h₀ : (F.obj 0).back = (F'.obj 0).back)
    (h : ∀ k : Fin n, (F.map (homOfLE k.castSucc_le_succ)).hom =
      ((F'.map (homOfLE k.castSucc_le_succ)).hom : G)) : F = F' := by
  have hlabel : ∀ i j (hij : i ≤ j),
      (F.map (homOfLE hij)).hom = ((F'.map (homOfLE hij)).hom : G) :=
    le_induction (fun i ↦ by rw [hom_map_homOfLE_refl F, hom_map_homOfLE_refl F'])
      fun i k hik ih ↦ by rw [hom_map_homOfLE_succ F hik, hom_map_homOfLE_succ F' hik, ih, h]
  have hobj (i : Fin (n + 1)) : F.obj i = F'.obj i := by
    rw [← back_coe (F.obj i), ← back_coe (F'.obj i), back_obj F i, back_obj F' i, h₀, hlabel]
  refine ComposableArrows.ext hobj fun i hi ↦ Functor.Elements.Hom.ext ?_
  simp only [ComposableArrows.map', ActionCategory.comp_hom, eqToHom_hom, one_mul, mul_one]
  exact hlabel _ _ _

/-- The consecutive labels of a string built by `ComposableArrows.mkOfObjOfMapSucc` are the labels
of the given arrows. -/
private theorem hom_map_mkOfObjOfMapSucc (obj : Fin (n + 1) → ActionCategory G X)
    (mapSucc : ∀ k : Fin n, obj k.castSucc ⟶ obj k.succ) (k : Fin n) :
    ((ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map (homOfLE k.castSucc_le_succ)).hom =
      ((mapSucc k).hom : G) :=
  congrArg (fun f ↦ Functor.Elements.Hom.hom f)
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc k.1 k.2)

variable [TopologicalSpace G] [TopologicalSpace X]

/-- The first point of a string of composable arrows depends continuously on the string. -/
@[fun_prop]
theorem continuous_back_obj_zero :
    Continuous fun F : ComposableArrows (ActionCategory G X) n ↦ (F.obj 0).back :=
  ((objectHomeomorph G X).continuous.comp <|
    (continuous_source G X).comp (ComposableArrows.continuous_totalArrow 0 0 le_rfl)).congr
      fun F ↦ by simp

/-- Each consecutive label of a string of composable arrows depends continuously on the string. -/
@[fun_prop]
theorem continuous_label_succ (k : Fin n) :
    Continuous fun F : ComposableArrows (ActionCategory G X) n ↦
      ((F.map (homOfLE k.castSucc_le_succ)).hom : G) :=
  ((continuous_label G X).comp (ComposableArrows.continuous_totalArrow k.castSucc k.succ
    k.castSucc_le_succ)).congr fun F ↦ by simp [ComposableArrows.totalArrow_def]

variable [ContinuousMul G] [ContinuousSMul G X]

/-- A map into strings of `n` composable arrows of an action category is continuous exactly when
the first point and the consecutive labels of the string depend continuously on the argument. -/
theorem continuous_nerve_iff {Y : Type*} [TopologicalSpace Y]
    {f : Y → ComposableArrows (ActionCategory G X) n} :
    Continuous f ↔ Continuous (fun y ↦ ((f y).obj 0).back) ∧
      ∀ k : Fin n, Continuous fun y ↦ (((f y).map (homOfLE k.castSucc_le_succ)).hom : G) := by
  refine ⟨fun hf ↦ ⟨continuous_back_obj_zero.comp hf, fun k ↦ (continuous_label_succ k).comp hf⟩,
    fun ⟨h₀, h⟩ ↦ ?_⟩
  have hlabel : ∀ i j (hij : i ≤ j),
      Continuous fun y ↦ (((f y).map (homOfLE hij)).hom : G) :=
    le_induction
      (fun i ↦ continuous_const.congr fun y ↦ (hom_map_homOfLE_refl (f y) i).symm)
      fun i k hik ih ↦ ((h k).mul ih).congr fun y ↦ (hom_map_homOfLE_succ (f y) hik).symm
  refine ComposableArrows.continuous_iff.2 fun i j hij ↦
    (arrowHomeomorph G X).isInducing.continuous_iff.2 <|
      ((hlabel i j hij).prodMk ((hlabel 0 i (Fin.zero_le i)).smul h₀)).congr fun y ↦ ?_
  simp only [Function.comp_apply, ComposableArrows.totalArrow_def, arrowHomeomorph_apply]
  rw [back_obj (f y) i, Pi.smul_apply']

variable (G X n) in
/-- The `n`-simplices of the topological nerve of an action groupoid are homeomorphic to `X × Gⁿ`,
by recording the first point and the labels of the consecutive arrows of a string. The string with
first point `x` and labels `g` has `k`-th point `gₖ₋₁ ⋯ g₀ • x`. -/
def nerveHomeomorph : ComposableArrows (ActionCategory G X) n ≃ₜ X × (Fin n → G) where
  toFun F := ((F.obj 0).back, fun k ↦ (F.map (homOfLE k.castSucc_le_succ)).hom)
  invFun p := ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ ((Fin.partialProd (fun k ↦ MulOpposite.op (p.2 k)) i).unop • p.1 : X))
    fun k ↦ Functor.Elements.homMk (p.2 k) (by
      rw [Fin.partialProd_succ, MulOpposite.unop_mul, MulOpposite.unop_op, mul_smul]; rfl)
  left_inv F := nerve_ext (by simp [ComposableArrows.mkOfObjOfMapSucc_obj]) fun k ↦ by
    rw [hom_map_mkOfObjOfMapSucc]
  right_inv p := Prod.ext (by simp [ComposableArrows.mkOfObjOfMapSucc_obj]) <| funext fun k ↦ by
    dsimp only
    rw [hom_map_mkOfObjOfMapSucc]
  continuous_toFun := continuous_back_obj_zero.prodMk (continuous_pi continuous_label_succ)
  continuous_invFun := continuous_nerve_iff.2
    ⟨by simpa [ComposableArrows.mkOfObjOfMapSucc_obj] using continuous_fst,
      fun k ↦ ((continuous_apply k).comp continuous_snd).congr fun p ↦ by
        rw [hom_map_mkOfObjOfMapSucc, Function.comp_apply]⟩

@[simp]
theorem nerveHomeomorph_apply (F : ComposableArrows (ActionCategory G X) n) :
    nerveHomeomorph G X n F =
      ((F.obj 0).back, fun k ↦ (F.map (homOfLE k.castSucc_le_succ)).hom) := (rfl)

/-- The `i`-th point of the string with first point `x` and consecutive labels `g` is
`gᵢ₋₁ ⋯ g₀ • x`. -/
@[simp]
theorem back_obj_nerveHomeomorph_symm (p : X × (Fin n → G)) (i : Fin (n + 1)) :
    (((nerveHomeomorph G X n).symm p).obj i).back =
      (Fin.partialProd (fun k ↦ MulOpposite.op (p.2 k)) i).unop • p.1 := (rfl)

end Monoid

section Group

universe u

variable {G X : Type u} [Group G] [MulAction G X] {n : ℕ}

/-- All points of a string of composable arrows of an action groupoid lie in one orbit. -/
theorem quotient_mk_back_obj (F : ComposableArrows (ActionCategory G X) n) (i : Fin (n + 1)) :
    (⟦(F.obj i).back⟧ : MulAction.orbitRel.Quotient G X) = ⟦(F.obj 0).back⟧ := by
  rw [back_obj F i, MulAction.orbitRel.Quotient.quotient_smul_eq]

variable [TopologicalSpace G] [TopologicalSpace X]

variable (G X) in
/-- The augmentation of the topological nerve of an action groupoid, with degeneracies forgotten,
over the orbit space: a string of composable arrows goes to the orbit of its first point, which is
the orbit of each of its points (`quotient_mk_back_obj`). -/
def coarseAugmentation :
    SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve (ActionCategory G X) ⟶
      (Functor.const _).obj (TopCat.of (MulAction.orbitRel.Quotient G X)) where
  app _ := TopCat.ofHom ⟨fun F ↦ ⟦(F.obj 0).back⟧, continuous_quot_mk.comp continuous_back_obj_zero⟩
  naturality _ _ f := by
    ext F
    exact quotient_mk_back_obj F _

/-- The coarse augmentation sends a string of composable arrows to the orbit of its first point. -/
theorem coarseAugmentation_app_apply (m : SemiSimplexCategoryᵒᵖ)
    (F : ComposableArrows (ActionCategory G X)
      (SemiSimplexCategory.toSimplexCategory.obj m.unop).len) :
    (coarseAugmentation G X).app m F = ⟦(F.obj 0).back⟧ := (rfl)

variable (G X) in
/-- The coarse map `B(G ⋉ X) → X / G` from the fat classifying space of an action groupoid to its
orbit space, sending a point of a simplex to the orbit of any vertex of that simplex
(`coarseMap_ι`). -/
def coarseMap :
    fatClassifyingSpace (ActionCategory G X) ⟶ TopCat.of (MulAction.orbitRel.Quotient G X) :=
  fatRealization.augment (coarseAugmentation G X)

/-- The coarse map sends a point of the simplex of a string of composable arrows to the orbit of
any point of the string. -/
theorem coarseMap_ι (m : SemiSimplexCategory)
    (F : ComposableArrows (ActionCategory G X) (SemiSimplexCategory.toSimplexCategory.obj m).len)
    (t : SemiSimplexCategory.toTop.obj m) (i : Fin (_ + 1)) :
    coarseMap G X (fatRealization.ι _ m (F, t)) = ⟦(F.obj i).back⟧ :=
  (fatRealization.augment_ι (coarseAugmentation G X) m F t).trans (quotient_mk_back_obj F i).symm

/-- The coarse map is surjective: each orbit is the image of the vertex of a `0`-simplex. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap G X) := by
  refine Quotient.ind fun x ↦ ?_
  -- The topological simplex of `⦋0⦌ₛ` is that of `⦋0⦌`, which is nonempty.
  obtain ⟨t⟩ : Nonempty (SimplexCategory.toTop.{u}.obj
    (SemiSimplexCategory.toSimplexCategory.obj (SemiSimplexCategory.mk 0))) := inferInstance
  exact ⟨fatRealization.ι _ (SemiSimplexCategory.mk 0)
    (ComposableArrows.mk₀ (x : ActionCategory G X), t), coarseMap_ι _ _ _ 0⟩

end Group

end TauCeti.ActionGroupoid
