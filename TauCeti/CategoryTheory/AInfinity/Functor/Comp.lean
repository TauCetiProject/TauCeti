/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Functor.Component

/-!
# Composition of A-infinity functors

The composite of `A∞` functors `ℱ : ℬ ⟶ 𝒞` and `𝒢 : 𝒞 ⟶ 𝒟`, with object maps `F` and `G`, has
object map `G ∘ F`, and its bar map is the composite of the bar maps of `ℱ` and `𝒢`.  In terms of
suspended Taylor components, its component on a composable word of `ℬ` is the sum, over all ways of
cutting the word into consecutive nonempty blocks, of the component of `𝒢` applied to the
components of `ℱ` on the blocks.  With the unit and associativity laws, this makes `A∞`
categories and `A∞` functors into a category.

An `A∞` functor is stored as an `A∞` morphism from the total algebra of morphisms of its source to
that of the category induced from its target along its object map.  So the bar map of `ℱ` lands in
the bar construction of `𝒞.induced F`, while that of `𝒢` starts from the bar construction of `𝒞`.
The two are joined by the **induced morphism** `𝒢.inducedHom F`, an `A∞` morphism from the total
algebra of `𝒞.induced F` to that of `𝒟.induced (G ∘ F)`: on a composable string of the induced
category, its components are those of `𝒢` on the image string in `𝒞`
(`TauCeti.AInfinityFunctor.component_inducedHom_homInclusion`), and on any other string they vanish.

When `F` is not injective, a string which is not composable in `𝒞.induced F` can become composable
in `𝒞`, so the map of total modules from `𝒞.induced F` to `𝒞` does not intertwine the bar
differentials, and the `A∞` equation of the induced morphism is not a pullback of that of `𝒢`.  It
is checked word by word instead (see `TauCeti/CategoryTheory/Graded/ComposableWords.lean`): on a
non-composable word both sides vanish, and on a composable word both sides lie in a single hom
module, on which the map of total modules of `𝒟.induced (G ∘ F)` is injective and carries both
sides to the corresponding sides of the `A∞` equation of `𝒢`.

## Main definitions

* `TauCeti.AInfinityFunctor.inducedHom`: the `A∞` morphism induced by an `A∞` functor between the
  categories induced along a map of objects and along its composite with the object map.
* `TauCeti.AInfinityFunctor.comp`: the composite of `A∞` functors.

## Main results

* `TauCeti.AInfinityFunctor.component_inducedHom_homInclusion`: on a composable string, the
  components of the induced morphism are those of the functor on the image string.
* `TauCeti.AInfinityFunctor.isPathCompatible_component_inducedHom`: the components of the induced
  morphism are path-compatible.
* `TauCeti.AInfinityFunctor.inducedHom_id` and `TauCeti.AInfinityFunctor.inducedHom_comp`: the
  morphism induced by the identity functor is the identity, and the morphism induced by a composite
  is the composite of the induced morphisms.
* `TauCeti.AInfinityFunctor.comp_map`: the map of a composite on Hom modules is the composite of
  the maps.
* `TauCeti.AInfinityFunctor.id_comp`, `TauCeti.AInfinityFunctor.comp_id` and
  `TauCeti.AInfinityFunctor.comp_assoc`: the unit and associativity laws.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 7.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), for `A∞` functors as morphisms of bar constructions over a map of objects and their
  composition.
-/

public section

namespace TauCeti

open GradedLinearQuiver GradedLinearQuiver.InducedQuiver ReducedTensorWords

universe u₀ u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w

variable {R : Type w} [CommRing R] {C : Type u₂} {D : Type u₃}
  [GradedLinearQuiver.{u₂, v₂, w} R C] [GradedLinearQuiver.{u₃, v₃, w} R D]
  {𝒞 : AInfinityCategory R C} {𝒟 : AInfinityCategory R D}

namespace AInfinityFunctor

/-! ### The induced morphism -/

section Induced

variable {B : Type u₀} (𝒢 : AInfinityFunctor 𝒞 𝒟) (F : B → C)

/-- The pairs of objects `p i = (sᵢ, tᵢ)` of a string of morphisms `sᵢ ⟶ tᵢ` form a composable
string: the source of each morphism is the target of the next one. -/
private def IsComposablePairs {α : Type*} {n : ℕ} (p : Fin n → α × α) : Prop :=
  ∀ i (h : i + 1 < n), (p ⟨i + 1, h⟩).2 = (p ⟨i, by omega⟩).1

/-- The Taylor map of the induced morphism on words of length `n`: on a composable string of
morphisms `sᵢ ⟶ tᵢ` of the category induced along `F`, the component from `⟨s (n - 1)⟩` to
`⟨t 0⟩` of the Taylor map of `𝒢` on the same morphisms; on any other string, zero. -/
private noncomputable def inducedTaylorComponent : (n : ℕ) →
    MultilinearMap R (fun _ : Fin n ↦ TotalHom R (InducedQuiver C F))
      (TotalHom R (InducedQuiver D (𝒢.obj ∘ F)))
  | 0 => 0
  | n + 1 => by
    classical
    exact MultilinearMap.fromDirectSumEquiv fun p ↦
      if IsComposablePairs p then
        (homInclusion (R := R) (C := InducedQuiver D (𝒢.obj ∘ F)) ⟨(p (Fin.last n)).1.obj⟩
            ⟨(p 0).2.obj⟩ ∘ₗ
          homProjection (R := R) (C := InducedQuiver D 𝒢.obj) ⟨F (p (Fin.last n)).1.obj⟩
            ⟨F (p 0).2.obj⟩).compMultilinearMap
          (((𝒢.toAInfinityHom.taylor ∘ₗ of R _ ⟨n + 1, n.succ_pos⟩).compMultilinearMap
              (PiTensorProduct.tprod R (s := fun _ : Fin (n + 1) ↦ TotalHom R C))).compLinearMap
            fun i ↦ homInclusion (R := R) (F (p i).1.obj) (F (p i).2.obj))
      else 0

/-- The Taylor map of the induced morphism. -/
private noncomputable def inducedTaylor :
    ReducedTensorWords R (TotalHom R (InducedQuiver C F)) →ₗ[R]
      TotalHom R (InducedQuiver D (𝒢.obj ∘ F)) :=
  DirectSum.toModule R _ _ fun n ↦ PiTensorProduct.lift (inducedTaylorComponent 𝒢 F n.1)

/-- On a composable string of morphisms, the Taylor map of the induced morphism is the component
between the endpoints of the Taylor map of `𝒢`. -/
private theorem inducedTaylor_of_tprod_of_isComposablePairs {n : ℕ}
    (s t : Fin (n + 1) → InducedQuiver C F) (x : ∀ i, homModule (R := R) (s i) (t i))
    (h : IsComposablePairs fun i ↦ (s i, t i)) :
    inducedTaylor 𝒢 F (of R _ ⟨n + 1, n.succ_pos⟩
        (PiTensorProduct.tprod R fun i ↦ homInclusion (s i) (t i) (x i))) =
      homInclusion (R := R) (C := InducedQuiver D (𝒢.obj ∘ F)) ⟨(s (Fin.last n)).obj⟩ ⟨(t 0).obj⟩
        (homProjection (R := R) (C := InducedQuiver D 𝒢.obj) ⟨F (s (Fin.last n)).obj⟩
          ⟨F (t 0).obj⟩ (𝒢.toAInfinityHom.taylor (of R _ ⟨n + 1, n.succ_pos⟩
            (PiTensorProduct.tprod R fun i ↦
              homInclusion (R := R) (F (s i).obj) (F (t i).obj) (x i))))) := by
  classical
  rw [inducedTaylor, toModule_of, PiTensorProduct.lift.tprod]
  simp only [inducedTaylorComponent, homInclusion_eq_lof]
  rw [MultilinearMap.fromDirectSumEquiv_lof (p := fun i ↦ (s i, t i))]
  simp [h]

/-- On a string of morphisms which is not composable, the Taylor map of the induced morphism
vanishes. -/
private theorem inducedTaylor_of_tprod_of_not_isComposablePairs {n : ℕ}
    (s t : Fin (n + 1) → InducedQuiver C F) (x : ∀ i, homModule (R := R) (s i) (t i))
    (h : ¬ IsComposablePairs fun i ↦ (s i, t i)) :
    inducedTaylor 𝒢 F (of R _ ⟨n + 1, n.succ_pos⟩
        (PiTensorProduct.tprod R fun i ↦ homInclusion (s i) (t i) (x i))) = 0 := by
  classical
  rw [inducedTaylor, toModule_of, PiTensorProduct.lift.tprod]
  simp only [inducedTaylorComponent, homInclusion_eq_lof]
  rw [MultilinearMap.fromDirectSumEquiv_lof (p := fun i ↦ (s i, t i))]
  simp [h]

/-- A natural-indexed string of pairs of objects is composable exactly when the string of its pairs
is. -/
private theorem isComposablePairs_iff {n : ℕ} (a b : ℕ → InducedQuiver C F) :
    (IsComposablePairs fun i : Fin (n + 1) ↦ (a i, b i)) ↔ IsComposableString a b (n + 1) :=
  ⟨fun h ↦ ⟨fun i hi ↦ h i hi⟩, fun h i hi ↦ h.eq i hi⟩

/-- On a word along a composable string, the Taylor map of the induced morphism is the component
between the endpoints of the Taylor map of `𝒢` on the image of the word. -/
private theorem inducedTaylor_of_isComposableString {n : ℕ} (hn : 0 < n)
    {a b : ℕ → InducedQuiver C F} {z : ℕ → TotalHom R (InducedQuiver C F)}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : IsComposableString a b n) :
    inducedTaylor 𝒢 F (of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i)) =
      homInclusion (R := R) (C := InducedQuiver D (𝒢.obj ∘ F)) ⟨(a (n - 1)).obj⟩ ⟨(b 0).obj⟩
        (homProjection (R := R) (C := InducedQuiver D 𝒢.obj) ⟨F (a (n - 1)).obj⟩ ⟨F (b 0).obj⟩
          (𝒢.toAInfinityHom.taylor (ReducedTensorWords.map (R := R) (totalHomMap R F)
            (of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i))))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  choose g hg using fun i : Fin (m + 1) ↦ hz i i.isLt
  have hzg : (fun i : Fin (m + 1) ↦ z i) = fun i : Fin (m + 1) ↦ homInclusion (a i) (b i) (g i) :=
    funext fun i ↦ (hg i).symm
  rw [hzg, map_of_tprod, inducedTaylor_of_tprod_of_isComposablePairs 𝒢 F (fun i ↦ a i)
    (fun i ↦ b i) g ((isComposablePairs_iff F a b).2 hab)]
  simp only [totalHomMap_homInclusion]
  rfl

/-- On a word along a string which is not composable, the Taylor map of the induced morphism
vanishes. -/
private theorem inducedTaylor_of_not_isComposableString {n : ℕ} (hn : 0 < n)
    {a b : ℕ → InducedQuiver C F} {z : ℕ → TotalHom R (InducedQuiver C F)}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : ¬ IsComposableString a b n) :
    inducedTaylor 𝒢 F (of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  choose g hg using fun i : Fin (m + 1) ↦ hz i i.isLt
  have hzg : (fun i : Fin (m + 1) ↦ z i) = fun i : Fin (m + 1) ↦ homInclusion (a i) (b i) (g i) :=
    funext fun i ↦ (hg i).symm
  rw [hzg]
  exact inducedTaylor_of_tprod_of_not_isComposablePairs 𝒢 F _ _ g
    (mt (isComposablePairs_iff F a b).1 hab)

/-- The Taylor map of the induced morphism sends composable words from `X` to `Y` to morphisms from
`⟨X.obj⟩` to `⟨Y.obj⟩`, and non-composable words to zero. -/
private theorem isWordPathCompatible_inducedTaylor :
    IsWordPathCompatible (fun X : InducedQuiver C F ↦ (⟨X.obj⟩ : InducedQuiver D (𝒢.obj ∘ F)))
      (inducedTaylor 𝒢 F) where
  mem_range_of_mem_composableWords {X Y} {w} hw := by
    refine composableWords_induction (fun n hn a b z hz hab ha hb ↦ ?_) (by simp)
      (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
      (fun r x hx ↦ by rw [map_smul]; exact Submodule.smul_mem _ r hx) hw
    rw [inducedTaylor_of_isComposableString 𝒢 F hn hz hab, ← ha, ← hb]
    exact LinearMap.mem_range_self _ _
  eq_zero_of_mem_nonComposableWords {w} hw := by
    refine nonComposableWords_induction (fun n hn a b z hz hab ↦ ?_) (by simp)
      (fun x y hx hy ↦ by rw [map_add, hx, hy, add_zero])
      (fun r x hx ↦ by rw [map_smul, hx, smul_zero]) hw
    exact inducedTaylor_of_not_isComposableString 𝒢 F hn hz hab

/-- **The Taylor maps of the induced morphism and of `𝒢` agree on composable words**, through the
maps of total modules of the induced categories. -/
private theorem totalHomMap_inducedTaylor {X Y : InducedQuiver C F}
    {w : ReducedTensorWords R (TotalHom R (InducedQuiver C F))} (hw : w ∈ composableWords R X Y) :
    totalHomMap R (𝒢.obj ∘ F) (inducedTaylor 𝒢 F w) =
      (totalHomMap R 𝒢.obj ∘ₗ 𝒢.toAInfinityHom.taylor)
        (ReducedTensorWords.map (R := R) (totalHomMap R F) w) := by
  refine composableWords_induction (fun n hn a b z hz hab _ _ ↦ ?_) (by simp)
    (fun x y hx hy ↦ by simp only [map_add, hx, hy]) (fun r x hx ↦ by simp only [map_smul, hx]) hw
  have hmem := 𝒢.isWordPathCompatible_taylor.mem_range_of_mem_composableWords
    (map_mem_composableWords (φ := fun X : InducedQuiver C F ↦ F X.obj) (Θ := totalHomMap R F)
      (fun X Y f ↦ by rw [totalHomMap_homInclusion]; exact LinearMap.mem_range_self _ _)
      (of_tprod_mem_composableWords hn hz hab))
  have e := congrArg (totalHomMap R 𝒢.obj) (homInclusion_homProjection_of_mem_range hmem)
  rw [totalHomMap_homInclusion] at e
  rw [inducedTaylor_of_isComposableString 𝒢 F hn hz hab, totalHomMap_homInclusion,
    LinearMap.comp_apply]
  exact e

/-- The Taylor map of the induced morphism has degree zero between the suspended gradings. -/
private theorem isHomogeneous_inducedTaylor :
    LinearMap.IsHomogeneous (inducedTaylor 𝒢 F)
      (gradedPiece ((𝒞.induced F).grading.shift 1))
      ((𝒟.induced (𝒢.obj ∘ F)).grading.shift 1).piece 0 := by
  rw [(𝒞.induced F).grading_eq, (𝒟.induced (𝒢.obj ∘ F)).grading_eq, LinearMap.isHomogeneous_def]
  intro E w hw
  rw [add_zero]
  refine gradedPiece_induction (motive := fun w ↦ inducedTaylor 𝒢 F w ∈ _) hw
    (fun n hn e x hx hE ↦ ?_) (by simp)
    (fun u v _ _ hu hv ↦ by rw [map_add]; exact add_mem hu hv)
    (fun r u _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ r hu)
  subst hE
  refine multilinearMap_apply_mem_of_mem_totalGrading_piece (d := fun i ↦ e i + 1)
    (f := (inducedTaylor 𝒢 F ∘ₗ of R _ ⟨n, hn⟩).compMultilinearMap
      (PiTensorProduct.tprod R (s := fun _ : Fin n ↦ TotalHom R (InducedQuiver C F))))
    (fun s t y hy ↦ ?_) fun i ↦ by simpa only [InternalGrading.shift_piece] using hx i
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
  by_cases h : IsComposablePairs fun i ↦ (s i, t i)
  · rw [inducedTaylor_of_tprod_of_isComposablePairs 𝒢 F s t y h, InternalGrading.shift_piece,
      homInclusion_mem_totalGrading_piece_iff]
    have hword := mem_gradedPiece_of_tprod (𝒞.grading.shift 1) m.succ_pos
      (fun i ↦ homInclusion (R := R) (F (s i).obj) (F (t i).obj) (y i)) e fun i ↦ by
        rw [InternalGrading.shift_piece, 𝒞.grading_eq, homInclusion_mem_totalGrading_piece_iff]
        exact hy i
    have h' := 𝒢.toAInfinityHom.isHomogeneous_taylor.map_mem hword
    rw [add_zero, InternalGrading.shift_piece, (𝒟.induced 𝒢.obj).grading_eq] at h'
    exact homProjection_mem_piece h' _ _
  · rw [inducedTaylor_of_tprod_of_not_isComposablePairs 𝒢 F s t y h]
    exact zero_mem _

/-- **The `A∞` equation of the induced morphism.** On non-composable words both sides vanish.  On
a composable word both sides are morphisms in a single hom module, on which the map of total
modules of `𝒟.induced (𝒢.obj ∘ F)` is injective, and it carries both sides to the two sides of the
`A∞` equation of `𝒢` on the image word. -/
private theorem inducedTaylor_comp_barDifferential :
    (𝒟.induced (𝒢.obj ∘ F)).taylor ∘ₗ coalgHom R (inducedTaylor 𝒢 F) =
      inducedTaylor 𝒢 F ∘ₗ (𝒞.induced F).barDifferential := by
  have hτ := 𝒢.isWordPathCompatible_inducedTaylor F
  have hbF : (𝒞.induced F).barDifferential = gradedCoderiv
      ((totalGrading R (InducedQuiver C F)).shift 1) (𝒞.induced F).taylor 1 := by
    rw [AInfinityAlgebra.barDifferential_def, (𝒞.induced F).grading_eq]
  have hbC : 𝒞.barDifferential = gradedCoderiv ((totalGrading R C).shift 1) 𝒞.taylor 1 := by
    rw [AInfinityAlgebra.barDifferential_def, 𝒞.grading_eq]
  rw [hbF]
  refine ((𝒟.induced (𝒢.obj ∘ F)).isWordPathCompatible_taylor.comp_coalgHom hτ
    fun X Y h ↦ InducedQuiver.ext (congrArg (fun Z : InducedQuiver D (𝒢.obj ∘ F) ↦ Z.obj) h)
    ).eq_of_totalHomMap_eq
    (hτ.comp_gradedCoderiv (𝒞.induced F).isWordPathCompatible_taylor 1 1) fun X Y w hw ↦ ?_
  simp only [LinearMap.comp_apply]
  have hφw : ReducedTensorWords.map (R := R) (totalHomMap R F) w ∈
      composableWords R (F X.obj) (F Y.obj) :=
    map_mem_composableWords
      (fun X Y f ↦ by rw [totalHomMap_homInclusion]; exact LinearMap.mem_range_self _ _) hw
  have hg : 𝒢.toAInfinityHom.barMap (ReducedTensorWords.map (R := R) (totalHomMap R F) w) ∈
      composableWords R (⟨F X.obj⟩ : InducedQuiver D 𝒢.obj) ⟨F Y.obj⟩ := by
    rw [𝒢.toAInfinityHom.barMap_eq_coalgHom]
    exact 𝒢.isWordPathCompatible_taylor.coalgHom_mem_composableWords hφw
  -- The `A∞` equation of `𝒢` on the image word.
  have hbar := LinearMap.congr_fun 𝒢.toAInfinityHom.taylor_comp_barMap
    (ReducedTensorWords.map (R := R) (totalHomMap R F) w)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hbC] at hbar
  rw [𝒟.totalHomMap_taylor_induced (𝒢.obj ∘ F) (hτ.coalgHom_mem_composableWords hw),
    map_coalgHom_of_mem_composableWords (fun X Y v hv ↦ 𝒢.totalHomMap_inducedTaylor F hv) hw,
    𝒢.totalHomMap_inducedTaylor F
      ((𝒞.induced F).isWordPathCompatible_taylor.gradedCoderiv_mem_composableWords 1 1 hw),
    LinearMap.comp_apply,
    map_gradedCoderiv_of_mem_composableWords
      (LinearMap.isHomogeneous_shift_piece_iff.2 isHomogeneous_totalHomMap)
      (fun X Y v hv ↦ 𝒞.totalHomMap_taylor_induced F hv) 1 hw,
    ← hbar, 𝒟.totalHomMap_taylor_induced 𝒢.obj hg, 𝒢.toAInfinityHom.barMap_eq_coalgHom,
    ← LinearMap.comp_apply (ReducedTensorWords.map (R := R) _), map_comp_coalgHom]

/-- The Taylor map of the induced morphism is the only map from words which is path-compatible like
it and agrees with the Taylor map of `𝒢` on composable words through the maps of total modules. -/
private theorem eq_inducedTaylor {t : ReducedTensorWords R (TotalHom R (InducedQuiver C F)) →ₗ[R]
      TotalHom R (InducedQuiver D (𝒢.obj ∘ F))}
    (ht : IsWordPathCompatible
      (fun X : InducedQuiver C F ↦ (⟨X.obj⟩ : InducedQuiver D (𝒢.obj ∘ F))) t)
    (h : ∀ X Y : InducedQuiver C F, ∀ w ∈ composableWords R X Y,
      totalHomMap R (𝒢.obj ∘ F) (t w) = totalHomMap R 𝒢.obj
        (𝒢.toAInfinityHom.taylor (ReducedTensorWords.map (R := R) (totalHomMap R F) w))) :
    t = inducedTaylor 𝒢 F :=
  ht.eq_of_totalHomMap_eq (𝒢.isWordPathCompatible_inducedTaylor F) fun X Y w hw ↦
    (h X Y w hw).trans (𝒢.totalHomMap_inducedTaylor F hw).symm

/-- **The `A∞` morphism induced by an `A∞` functor** `𝒢 : 𝒞 ⟶ 𝒟` along a map of objects
`F : B → C`: the `A∞` morphism from the total algebra of morphisms of `𝒞.induced F` to that of
`𝒟.induced (𝒢.obj ∘ F)` whose components on a composable string are those of `𝒢` on the image
string (`TauCeti.AInfinityFunctor.component_inducedHom_homInclusion`), and whose components on any
other string vanish. -/
noncomputable def inducedHom :
    AInfinityHom (𝒞.induced F).toAInfinityAlgebra (𝒟.induced (𝒢.obj ∘ F)).toAInfinityAlgebra :=
  AInfinityHom.ofTaylor (inducedTaylor 𝒢 F) (𝒢.isHomogeneous_inducedTaylor F)
    (𝒢.inducedTaylor_comp_barDifferential F)

private theorem taylor_inducedHom : (𝒢.inducedHom F).taylor = inducedTaylor 𝒢 F :=
  AInfinityHom.taylor_ofTaylor _ _ _

/-- The components of the induced morphism send composable strings from `X` to `Y` to morphisms
from `⟨X.obj⟩` to `⟨Y.obj⟩`, and other strings to zero. -/
theorem isPathCompatible_component_inducedHom (n : ℕ) :
    IsPathCompatible (fun X : InducedQuiver C F ↦ (⟨X.obj⟩ : InducedQuiver D (𝒢.obj ∘ F)))
      ((𝒢.inducedHom F).component n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [AInfinityHom.component_zero]
    exact ⟨fun _ _ ↦ zero_mem _, fun _ _ _ _ _ _ _ ↦ rfl⟩
  · refine (𝒢.inducedHom F).isWordPathCompatible_taylor_iff.1 ?_ n hn
    rw [taylor_inducedHom]
    exact 𝒢.isWordPathCompatible_inducedTaylor F

/-- **The components of the induced morphism on a composable string** `X₀, …, Xₙ` of the category
induced along `F` are the components of `𝒢` on the image string `F X₀, …, F Xₙ`. -/
theorem component_inducedHom_homInclusion {n : ℕ} (X : Fin (n + 1) → InducedQuiver C F)
    (x : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    (𝒢.inducedHom F).component n (fun i ↦ homInclusion _ _ (x i)) =
      homInclusion (R := R) (C := InducedQuiver D (𝒢.obj ∘ F)) ⟨(X 0).obj⟩ ⟨(X (Fin.last n)).obj⟩
        (𝒢.component (fun k ↦ F (X k).obj) x) := by
  rcases n with _ | n
  · simp
  have hX : IsComposablePairs fun i : Fin (n + 1) ↦ (X i.rev.castSucc, X i.rev.succ) :=
    fun i hi ↦ congrArg X <| Fin.ext <| by
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_rev]
      omega
  rw [AInfinityHom.component_apply _ _ n.succ_pos, taylor_inducedHom, (𝒞.induced F).grading_eq]
  simp only [koszulTwist_homInclusion]
  rw [inducedTaylor_of_tprod_of_isComposablePairs 𝒢 F _ _ _ hX, component_apply,
    AInfinityHom.component_apply _ _ n.succ_pos, 𝒞.grading_eq]
  simp only [koszulTwist_homInclusion]
  rw [show X (Fin.last n).rev.castSucc = X 0 by simp,
    show X (Fin.rev 0).succ = X (Fin.last (n + 1)) by simp]
  rfl

/-- The linear part of the induced morphism sends a morphism `X ⟶ Y` of the category induced along
`F` to its image under `𝒢`, between `⟨X.obj⟩` and `⟨Y.obj⟩`. -/
theorem linearPart_inducedHom_homInclusion (X Y : InducedQuiver C F)
    (f : homModule (R := R) X Y) :
    (𝒢.inducedHom F).linearPart (homInclusion X Y f) =
      homInclusion (R := R) (C := InducedQuiver D (𝒢.obj ∘ F)) ⟨X.obj⟩ ⟨Y.obj⟩
        (𝒢.map (F X.obj) (F Y.obj) f) := by
  rw [AInfinityHom.linearPart_apply, taylor_inducedHom, ofLetter_eq_of_tprod, map_apply,
    AInfinityHom.linearPart_apply, ofLetter_eq_of_tprod]
  exact inducedTaylor_of_tprod_of_isComposablePairs 𝒢 F (n := 0) (fun _ ↦ X) (fun _ ↦ Y)
    (fun _ ↦ f) fun i hi ↦ absurd hi (by omega)

/-- The map of total modules of the category induced along the identity undoes the linear part of
the identity functor. -/
private theorem totalHomMap_linearPart_id (x : TotalHom R C) :
    totalHomMap R (AInfinityFunctor.id 𝒞).obj
      ((AInfinityFunctor.id 𝒞).toAInfinityHom.linearPart x) = x := by
  induction x using totalHom_induction with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | homInclusion X Y f =>
    rw [← homInclusion_map, totalHomMap_homInclusion]
    exact congrArg (homInclusion X Y) (id_map_apply 𝒞 f)

/-- The Taylor map of the identity functor is its linear part applied to the letter of a word. -/
private theorem taylor_id_apply (y : ReducedTensorWords R (TotalHom R C)) :
    (AInfinityFunctor.id 𝒞).toAInfinityHom.taylor y =
      (AInfinityFunctor.id 𝒞).toAInfinityHom.linearPart (letter R _ y) :=
  (LinearMap.congr_fun (AInfinityStrictHom.taylor_toAInfinityHom _) y).trans
    (LinearMap.congr_fun (AInfinityStrictHom.linearPart_toAInfinityHom _) _).symm

/-- **The morphism induced by the identity functor is the identity.** -/
@[simp]
theorem inducedHom_id :
    (AInfinityFunctor.id 𝒞).inducedHom F = AInfinityHom.id (𝒞.induced F).toAInfinityAlgebra := by
  have h (w : ReducedTensorWords R (TotalHom R (InducedQuiver C F))) :
      totalHomMap R F (letter R _ w) = totalHomMap R (AInfinityFunctor.id 𝒞).obj
        ((AInfinityFunctor.id 𝒞).toAInfinityHom.taylor
          (ReducedTensorWords.map (R := R) (totalHomMap R F) w)) := by
    rw [taylor_id_apply, ← LinearMap.comp_apply (letter R _), letter_comp_map, LinearMap.comp_apply,
      totalHomMap_linearPart_id]
  -- The object map of the identity functor is the identity, so the letter projection is
  -- path-compatible along the identification of the two induced quivers.
  exact AInfinityHom.ext ((taylor_inducedHom _ F).trans
    ((eq_inducedTaylor (AInfinityFunctor.id 𝒞) F isWordPathCompatible_letter
      fun _ _ w _ ↦ h w).symm.trans (AInfinityHom.taylor_id _).symm))

end Induced

/-! ### Composition -/

section Comp

variable {A : Type u₁} [GradedLinearQuiver.{u₁, v₁, w} R A] {ℬ : AInfinityCategory R A}
  (𝒢 : AInfinityFunctor 𝒞 𝒟) (ℱ : AInfinityFunctor ℬ 𝒞)

/-- The **composite** `𝒢 ∘ ℱ` of `A∞` functors `ℱ : ℬ ⟶ 𝒞` and `𝒢 : 𝒞 ⟶ 𝒟`: its object map is
`𝒢.obj ∘ ℱ.obj`, and its `A∞` morphism of total algebras is that of `ℱ` followed by the morphism
induced by `𝒢` along `ℱ.obj` (`TauCeti.AInfinityFunctor.inducedHom`), so its bar map is the
composite of the bar maps. -/
-- Expose the object map so the types of the characteristic Hom-map equations reduce.
@[expose]
noncomputable def comp : AInfinityFunctor ℬ 𝒟 where
  obj := 𝒢.obj ∘ ℱ.obj
  toAInfinityHom := (𝒢.inducedHom ℱ.obj).comp ℱ.toAInfinityHom
  isPathCompatible_component_of_pos n hn := by
    refine ((𝒢.inducedHom ℱ.obj).comp ℱ.toAInfinityHom).isWordPathCompatible_taylor_iff.1 ?_ n hn
    rw [AInfinityHom.taylor_comp, ℱ.toAInfinityHom.barMap_eq_coalgHom, taylor_inducedHom]
    exact (𝒢.isWordPathCompatible_inducedTaylor ℱ.obj).comp_coalgHom
      ℱ.isWordPathCompatible_taylor fun _ _ h ↦ congrArg InducedQuiver.obj h

@[simp]
theorem comp_obj (X : A) : (𝒢.comp ℱ).obj X = 𝒢.obj (ℱ.obj X) := (rfl)

/-- The `A∞` morphism of total algebras of a composite is that of the first functor followed by the
morphism induced by the second. -/
theorem comp_toAInfinityHom :
    (𝒢.comp ℱ).toAInfinityHom = (𝒢.inducedHom ℱ.obj).comp ℱ.toAInfinityHom := (rfl)

/-- **The map of a composite on Hom modules is the composite of the maps**: the arity-one component
of `𝒢 ∘ ℱ` is `g₁ ∘ f₁`. -/
@[simp]
theorem comp_map (X Y : A) :
    (𝒢.comp ℱ).map X Y = 𝒢.map (ℱ.obj X) (ℱ.obj Y) ∘ₗ ℱ.map X Y := by
  ext f
  apply homInclusion_injective (C := InducedQuiver D (𝒢.comp ℱ).obj) ⟨X⟩ ⟨Y⟩
  rw [homInclusion_map]
  refine (LinearMap.congr_fun (AInfinityHom.linearPart_comp (𝒢.inducedHom ℱ.obj)
    ℱ.toAInfinityHom) (homInclusion X Y f)).trans ?_
  rw [LinearMap.comp_apply, ← homInclusion_map, linearPart_inducedHom_homInclusion]
  rfl

/-- Composing with the identity `A∞` functor on the left leaves an `A∞` functor unchanged. -/
@[simp]
theorem id_comp : (AInfinityFunctor.id 𝒞).comp ℱ = ℱ :=
  AInfinityFunctor.ext rfl <| heq_of_eq <|
    (congrArg (AInfinityHom.comp · ℱ.toAInfinityHom) (inducedHom_id ℱ.obj)).trans
      (AInfinityHom.id_comp _)

/-- Composing with the identity `A∞` functor on the right leaves an `A∞` functor unchanged. -/
@[simp]
theorem comp_id : 𝒢.comp (AInfinityFunctor.id 𝒞) = 𝒢 := by
  have hbar : (AInfinityFunctor.id 𝒞).toAInfinityHom.barMap =
      ReducedTensorWords.map (R := R) (AInfinityFunctor.id 𝒞).toAInfinityHom.linearPart :=
    (AInfinityStrictHom.barMap_toAInfinityHom _).trans ((AInfinityStrictHom.barMap_def _).trans
      (congrArg _ (AInfinityStrictHom.linearPart_toAInfinityHom _).symm))
  have hι (X Y : C) (f : homModule (R := R) X Y) :
      (AInfinityFunctor.id 𝒞).toAInfinityHom.linearPart (homInclusion X Y f) ∈
        LinearMap.range (homInclusion (R := R)
          (C := InducedQuiver C (AInfinityFunctor.id 𝒞).obj) ⟨X⟩ ⟨Y⟩) := by
    rw [← homInclusion_map]
    exact LinearMap.mem_range_self _ _
  have h₁ : IsWordPathCompatible
      (fun X : C ↦ (⟨X⟩ : InducedQuiver D (𝒢.obj ∘ (AInfinityFunctor.id 𝒞).obj)))
      ((𝒢.inducedHom (AInfinityFunctor.id 𝒞).obj).taylor ∘ₗ
        (AInfinityFunctor.id 𝒞).toAInfinityHom.barMap) := by
    rw [taylor_inducedHom, hbar]
    exact (𝒢.isWordPathCompatible_inducedTaylor _).comp_map hι
      fun X Y h ↦ congrArg InducedQuiver.obj h
  have h (X Y : C) (w : ReducedTensorWords R (TotalHom R C)) (hw : w ∈ composableWords R X Y) :
      totalHomMap R (𝒢.obj ∘ (AInfinityFunctor.id 𝒞).obj)
        (((𝒢.inducedHom (AInfinityFunctor.id 𝒞).obj).taylor ∘ₗ
          (AInfinityFunctor.id 𝒞).toAInfinityHom.barMap) w) =
        totalHomMap R 𝒢.obj (𝒢.toAInfinityHom.taylor w) := by
    have hid : totalHomMap R (AInfinityFunctor.id 𝒞).obj ∘ₗ
        (AInfinityFunctor.id 𝒞).toAInfinityHom.linearPart = LinearMap.id :=
      LinearMap.ext totalHomMap_linearPart_id
    rw [taylor_inducedHom, hbar, LinearMap.comp_apply,
      𝒢.totalHomMap_inducedTaylor _ (map_mem_composableWords hι hw), LinearMap.comp_apply,
      ← LinearMap.comp_apply (ReducedTensorWords.map (R := R) _), ← map_comp, hid, map_id,
      LinearMap.id_apply]
  -- The object map of the identity functor is the identity, so both Taylor maps take values in
  -- the same total module.
  exact AInfinityFunctor.ext rfl <| heq_of_eq <| AInfinityHom.ext <|
    (AInfinityHom.taylor_comp _ _).trans
      (h₁.eq_of_totalHomMap_eq 𝒢.isWordPathCompatible_taylor h)

variable {K : Type u₄} [GradedLinearQuiver.{u₄, v₄, w} R K] {𝒦 : AInfinityCategory R K}

/-- The Taylor map of a composite of `A∞` functors is the Taylor map of the morphism induced by the
second functor after the bar map of the first. -/
private theorem taylor_comp_apply (ℋ : AInfinityFunctor 𝒟 𝒦)
    (x : ReducedTensorWords R (TotalHom R C)) :
    (ℋ.comp 𝒢).toAInfinityHom.taylor x =
      inducedTaylor ℋ 𝒢.obj (coalgHom R 𝒢.toAInfinityHom.taylor x) := by
  have h : ((ℋ.inducedHom 𝒢.obj).comp 𝒢.toAInfinityHom).taylor =
      inducedTaylor ℋ 𝒢.obj ∘ₗ coalgHom R 𝒢.toAInfinityHom.taylor := by
    rw [AInfinityHom.taylor_comp, taylor_inducedHom, 𝒢.toAInfinityHom.barMap_eq_coalgHom]
  exact LinearMap.congr_fun h x

/-- **The morphism induced by a composite of `A∞` functors** `ℋ ∘ 𝒢` along `F` is the morphism
induced by `𝒢` along `F` followed by the morphism induced by `ℋ` along `𝒢.obj ∘ F`. -/
theorem inducedHom_comp {B : Type u₀} (F : B → C) (ℋ : AInfinityFunctor 𝒟 𝒦) :
    (ℋ.comp 𝒢).inducedHom F = (ℋ.inducedHom (𝒢.obj ∘ F)).comp (𝒢.inducedHom F) := by
  have ht : IsWordPathCompatible
      (fun X : InducedQuiver C F ↦ (⟨X.obj⟩ : InducedQuiver K (ℋ.obj ∘ (𝒢.obj ∘ F))))
      (inducedTaylor ℋ (𝒢.obj ∘ F) ∘ₗ coalgHom R (inducedTaylor 𝒢 F)) :=
    (ℋ.isWordPathCompatible_inducedTaylor (𝒢.obj ∘ F)).comp_coalgHom
      (𝒢.isWordPathCompatible_inducedTaylor F)
      fun X Y h ↦ InducedQuiver.ext (congrArg (fun Z : InducedQuiver D (𝒢.obj ∘ F) ↦ Z.obj) h)
  have h (X Y : InducedQuiver C F) (w : ReducedTensorWords R (TotalHom R (InducedQuiver C F)))
      (hw : w ∈ composableWords R X Y) :
      totalHomMap R (ℋ.obj ∘ (𝒢.obj ∘ F))
          ((inducedTaylor ℋ (𝒢.obj ∘ F) ∘ₗ coalgHom R (inducedTaylor 𝒢 F)) w) =
        totalHomMap R (ℋ.comp 𝒢).obj ((ℋ.comp 𝒢).toAInfinityHom.taylor
          (ReducedTensorWords.map (R := R) (totalHomMap R F) w)) := by
    have hφw : ReducedTensorWords.map (R := R) (totalHomMap R F) w ∈
        composableWords R (F X.obj) (F Y.obj) :=
      map_mem_composableWords
        (fun X Y f ↦ by rw [totalHomMap_homInclusion]; exact LinearMap.mem_range_self _ _) hw
    have e₁ : totalHomMap R (ℋ.obj ∘ (𝒢.obj ∘ F))
          ((inducedTaylor ℋ (𝒢.obj ∘ F) ∘ₗ coalgHom R (inducedTaylor 𝒢 F)) w) =
        (totalHomMap R ℋ.obj ∘ₗ ℋ.toAInfinityHom.taylor) (coalgHom R
          (totalHomMap R 𝒢.obj ∘ₗ 𝒢.toAInfinityHom.taylor)
            (ReducedTensorWords.map (R := R) (totalHomMap R F) w)) := by
      rw [LinearMap.comp_apply, ℋ.totalHomMap_inducedTaylor (𝒢.obj ∘ F)
          ((𝒢.isWordPathCompatible_inducedTaylor F).coalgHom_mem_composableWords hw),
        map_coalgHom_of_mem_composableWords (fun X Y v hv ↦ 𝒢.totalHomMap_inducedTaylor F hv) hw]
    have e₂ : totalHomMap R (ℋ.obj ∘ 𝒢.obj) (inducedTaylor ℋ 𝒢.obj
          (coalgHom R 𝒢.toAInfinityHom.taylor
            (ReducedTensorWords.map (R := R) (totalHomMap R F) w))) =
        (totalHomMap R ℋ.obj ∘ₗ ℋ.toAInfinityHom.taylor) (coalgHom R
          (totalHomMap R 𝒢.obj ∘ₗ 𝒢.toAInfinityHom.taylor)
            (ReducedTensorWords.map (R := R) (totalHomMap R F) w)) := by
      rw [ℋ.totalHomMap_inducedTaylor 𝒢.obj
          (𝒢.isWordPathCompatible_taylor.coalgHom_mem_composableWords hφw),
        ← LinearMap.comp_apply (ReducedTensorWords.map (R := R) _), map_comp_coalgHom]
    have e₃ : totalHomMap R (ℋ.comp 𝒢).obj ((ℋ.comp 𝒢).toAInfinityHom.taylor
          (ReducedTensorWords.map (R := R) (totalHomMap R F) w)) =
        totalHomMap R (ℋ.obj ∘ 𝒢.obj) (inducedTaylor ℋ 𝒢.obj
          (coalgHom R 𝒢.toAInfinityHom.taylor
            (ReducedTensorWords.map (R := R) (totalHomMap R F) w))) :=
      congrArg (totalHomMap R (ℋ.comp 𝒢).obj) (taylor_comp_apply 𝒢 ℋ _)
    exact e₁.trans (e₂.symm.trans e₃.symm)
  have hR : ((ℋ.inducedHom (𝒢.obj ∘ F)).comp (𝒢.inducedHom F)).taylor =
      inducedTaylor ℋ (𝒢.obj ∘ F) ∘ₗ coalgHom R (inducedTaylor 𝒢 F) := by
    rw [AInfinityHom.taylor_comp, (𝒢.inducedHom F).barMap_eq_coalgHom, taylor_inducedHom,
      taylor_inducedHom]
  -- The object maps `(ℋ.comp 𝒢).obj ∘ F` and `ℋ.obj ∘ (𝒢.obj ∘ F)` agree definitionally.
  exact AInfinityHom.ext ((taylor_inducedHom _ F).trans
    (((ℋ.comp 𝒢).eq_inducedTaylor F ht h).symm.trans hR.symm))

/-- Composition of `A∞` functors is associative. -/
@[simp]
theorem comp_assoc (ℋ : AInfinityFunctor 𝒟 𝒦) : (ℋ.comp 𝒢).comp ℱ = ℋ.comp (𝒢.comp ℱ) :=
  AInfinityFunctor.ext rfl <| heq_of_eq <|
    (congrArg (AInfinityHom.comp · ℱ.toAInfinityHom) (𝒢.inducedHom_comp ℱ.obj ℋ)).trans
      (AInfinityHom.comp_assoc _ _ _)

end Comp

end AInfinityFunctor

end TauCeti
