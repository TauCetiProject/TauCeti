/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Nerve

/-!
# The nerve as iterated fiber products of arrows

For a category with topologies on objects and total arrows, continuous source, units and
composition, the topology of its nerve agrees with the usual iterated fiber-product topology.
`CategoryTheory.ComposableArrows.precompHomeomorph` splits a string into its first arrow and
its remaining string, with the matching endpoint equation. In degree zero,
`CategoryTheory.ComposableArrows.zeroHomeomorph` identifies the nerve with the object space.
Thus the topology defined by recording all composite arrows introduces no extra topology
beyond that of composable strings. Recording all arrows exhibits `ComposableArrows C n` as a
subspace of a finite product of copies of `Quiver.Total C` (`isEmbedding_totalArrowTuple`), so
separation (`T₀`, `T₁`, `T₂`, regular, `T₃`) and countability axioms pass automatically from
`Quiver.Total C` to every level of the nerve, while compactness and `σ`-compactness pass via the
iterated fiber-product decomposition (`compactSpace`, `sigmaCompactSpace`). These identifications
apply to topological groupoids without discarding any isotropy arrows.

Composition is required to be continuous on the subspace of pairs with matching endpoints.
No topology on individual hom types and no new category or groupoid carrier is used.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Section 2.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public section

open CategoryTheory Set Topology

universe v u

namespace CategoryTheory.ComposableArrows

section ArrowTuple

variable {C : Type u} [Category.{v} C] {n : ℕ}

/-- Evaluation of a string of `n` composable arrows on all pairs `(i, j)` with `i ≤ j`. -/
def totalArrowTuple (F : ComposableArrows C n) :
    {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2} → Quiver.Total C :=
  fun p ↦ F.totalArrow p.1.1 p.1.2 p.2

@[simp]
theorem totalArrowTuple_apply (F : ComposableArrows C n)
    (p : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2}) :
    F.totalArrowTuple p = F.totalArrow p.1.1 p.1.2 p.2 :=
  (rfl)

variable [TopologicalSpace (Quiver.Total C)]

/-- `ComposableArrows C n` embeds into the finite product of copies of `Quiver.Total C` indexed by
pairs `i ≤ j` in `Fin (n + 1)`. -/
theorem isEmbedding_totalArrowTuple : IsEmbedding (totalArrowTuple (C := C) (n := n)) := by
  refine ⟨⟨?_⟩, fun F G h ↦ ext_of_totalArrow fun i j hij ↦ congrFun h ⟨(i, j), hij⟩⟩
  simp only [instTopologicalSpace, Pi.topologicalSpace, induced_iInf, induced_compose,
    Function.comp_def, totalArrowTuple_apply]
  refine le_antisymm ?_ ?_
  · exact le_iInf fun p ↦ iInf_le_of_le p.1.1 (iInf_le_of_le p.1.2 (iInf_le _ p.2))
  · exact le_iInf fun i ↦ le_iInf fun j ↦ le_iInf fun hij ↦
      iInf_le_of_le (⟨(i, j), hij⟩ : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2}) le_rfl

instance instT0Space [T0Space (Quiver.Total C)] : T0Space (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.t0Space

instance instT1Space [T1Space (Quiver.Total C)] : T1Space (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.t1Space

instance instT2Space [T2Space (Quiver.Total C)] : T2Space (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.t2Space

instance instRegularSpace [RegularSpace (Quiver.Total C)] : RegularSpace (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.isInducing.regularSpace

instance instT3Space [T3Space (Quiver.Total C)] : T3Space (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.t3Space

instance instFirstCountableTopology [FirstCountableTopology (Quiver.Total C)] :
    FirstCountableTopology (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.firstCountableTopology

instance instSecondCountableTopology [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.secondCountableTopology

end ArrowTuple

variable {C : Type u} [Category.{v} C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]

/-- Vertices depend continuously on a string when source is continuous. -/
@[fun_prop]
theorem continuous_obj
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    {n : ℕ} (i : Fin (n + 1)) : Continuous fun F : ComposableArrows C n ↦ F.obj i := by
  simpa only [Function.comp_def, totalArrow_left] using
    hs.comp (continuous_totalArrow i i le_rfl)

/-- The zero-simplices of the topological nerve are the objects, with their original topology. -/
def zeroHomeomorph
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    ComposableArrows C 0 ≃ₜ C where
  toFun F := F.obj 0
  invFun := mk₀
  left_inv F := ext₀ rfl
  right_inv _ := rfl
  continuous_toFun := continuous_obj hs 0
  continuous_invFun := continuous_iff.2 fun i j hij ↦ by
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i j
    simpa [totalArrow_def, mk₀] using hu

@[simp]
theorem zeroHomeomorph_apply
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (F : ComposableArrows C 0) : zeroHomeomorph hs hu F = F.obj 0 := (rfl)

@[simp]
theorem zeroHomeomorph_symm_apply
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (x : C) : (zeroHomeomorph hs hu).symm x = mk₀ x := (rfl)

variable
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
  (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
  (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
    (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C))

include hs hu hc in
/-- Prepending a continuous family of arrows to a continuous family of strings is continuous,
provided the endpoints match. -/
theorem continuous_precomp {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    {a : Y → Quiver.Total C} {F : Y → ComposableArrows C n}
    (ha : Continuous a) (hF : Continuous F) (h : ∀ y, (a y).right = (F y).left) :
    Continuous fun y ↦ (F y).precomp ((a y).hom ≫ eqToHom (h y)) := by
  apply continuous_iff.2
  -- A prepended string has unit, first-edge, composite, and tail-arrow cases.
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  cases i with
  | zero =>
    cases j with
    | zero =>
      simpa only [totalArrow_def, precomp, Precomp.obj, Precomp.map,
        Function.comp_def] using hu.comp (hs.comp ha)
    | succ j =>
      cases j with
      | zero =>
        convert ha using 1
        funext y
        exact totalArrow_precomp_zero_one (a y) (F y) (h y)
      | succ j =>
        have ht := (continuous_totalArrow (⟨0, by omega⟩ : Fin (n + 1))
          ⟨j + 1, by omega⟩ (Nat.zero_le _)).comp hF
        have hp : Continuous fun y ↦
            (⟨(a y, (F y).totalArrow ⟨0, by omega⟩ ⟨j + 1, by omega⟩ (Nat.zero_le _)),
              by simpa only [totalArrow_left] using h y⟩ :
              {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}) :=
          (ha.prodMk ht).subtype_mk _
        convert hc.comp hp using 1
        funext y
        conv_lhs => simp only [Fin.zero_eta]
        rw [totalArrow_precomp_zero_succ_succ (F y) ((a y).hom ≫ eqToHom (h y)) j (by omega)]
        simp only [Function.comp_apply, totalArrow_def, Category.assoc]
  | succ i =>
    cases j with
    | zero => simp only [Fin.mk_le_mk] at hij; omega
    | succ j =>
      have ht := (continuous_totalArrow ⟨i, by omega⟩ ⟨j, by omega⟩ (by
        simp only [Fin.mk_le_mk] at hij ⊢
        omega)).comp hF
      convert ht using 1
      funext y
      exact totalArrow_precomp_succ_succ (F y) ((a y).hom ≫ eqToHom (h y))
        ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp only [Fin.mk_le_mk] at hij ⊢; omega)

include hs hu hc in
/-- A string of `n + 1` arrows is the fiber product of the arrow space and the space of
`n`-strings, over target and the first vertex. The fiber product has its subspace topology. -/
def precompHomeomorph (n : ℕ) :
    ComposableArrows C (n + 1) ≃ₜ
      {p : Quiver.Total C × ComposableArrows C n // p.1.right = p.2.left} where
  -- Explicit vertices make the matching endpoint equation definitional, without unfolding
  -- the opaque total-arrow accessor in the dependent inverse construction.
  toFun F := ⟨(⟨F.obj' 0, F.obj' 1, F.map' 0 1⟩, F.δ₀), rfl⟩
  invFun p := p.1.2.precomp (p.1.1.hom ≫ eqToHom p.2)
  left_inv F := by
    -- The first vertex of the tail and vertex 1 have different native accessor expressions.
    dsimp only
    erw [eqToHom_refl, Category.comp_id]
    obtain ⟨F, X, f, rfl⟩ := precomp_surjective F
    rfl
  right_inv := by
    rintro ⟨⟨⟨x, z, f⟩, F⟩, h⟩
    dsimp only at h
    subst z
    apply Subtype.ext
    -- Align the endpoint accessors before simplifying the dependent arrow.
    dsimp only
    erw [eqToHom_refl, Category.comp_id]
    simp only [precomp_δ₀]
    rfl
  continuous_toFun := by
    have ht := continuous_totalArrow (C := C) (⟨0, by omega⟩ : Fin (n + 2))
      ⟨1, by omega⟩ (Nat.zero_le _)
    simp_rw [totalArrow_def] at ht
    exact (ht.prodMk (continuous_whiskerLeft (Fin.succFunctor (n + 1)))).subtype_mk _
  continuous_invFun := continuous_precomp hs hu hc
    (continuous_fst.comp continuous_subtype_val)
    (continuous_snd.comp continuous_subtype_val) (fun p ↦ p.2)

@[simp]
theorem precompHomeomorph_apply (n : ℕ) (F : ComposableArrows C (n + 1)) :
    (precompHomeomorph hs hu hc n F).val = (F.totalArrow 0 1 (Fin.zero_le _), F.δ₀) := by
  simp only [totalArrow_def]
  rfl

@[simp]
theorem precompHomeomorph_symm_apply (n : ℕ)
    (p : {p : Quiver.Total C × ComposableArrows C n // p.1.right = p.2.left}) :
    (precompHomeomorph hs hu hc n).symm p =
      p.1.2.precomp (p.1.1.hom ≫ eqToHom p.2) := (rfl)

include hs hu hc in
/-- A family of nonempty strings is continuous exactly when its first arrow and its tail are
continuous. Together with `zeroHomeomorph`, this characterizes the iterated fiber-product
topology without testing the nonconsecutive composite arrows. -/
theorem continuous_iff_first_tail {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    {F : Y → ComposableArrows C (n + 1)} :
    Continuous F ↔
      (Continuous fun y ↦ (F y).totalArrow 0 1 (Fin.zero_le _)) ∧
      Continuous fun y ↦ (F y).δ₀ := by
  rw [← (precompHomeomorph hs hu hc n).comp_continuous_iff]
  simp only [continuous_induced_rng, continuous_prodMk, Function.comp_def,
    precompHomeomorph_apply]

variable (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))

include hs ht in
/-- When objects are Hausdorff and both source and target are continuous, the matching-endpoint
locus in `Quiver.Total C × ComposableArrows C n` is closed. -/
theorem isClosed_eq_right_left [T2Space C] (n : ℕ) :
    IsClosed {p : Quiver.Total C × ComposableArrows C n | p.1.right = p.2.left} :=
  isClosed_eq (ht.comp continuous_fst) ((continuous_obj hs 0).comp continuous_snd)

include hs ht hu hc in
/-- When `C` is Hausdorff, `Quiver.Total C` is compact, and source, target, units, and composition
are continuous, every nerve level `ComposableArrows C n` is compact. -/
theorem compactSpace [T2Space C] [CompactSpace (Quiver.Total C)] :
    ∀ n : ℕ, CompactSpace (ComposableArrows C n)
  | 0 =>
    have hsurj : Function.Surjective (Quiver.Total.left : Quiver.Total C → C) :=
      fun x ↦ ⟨⟨x, x, 𝟙 x⟩, rfl⟩
    have : CompactSpace C := hsurj.compactSpace hs
    (zeroHomeomorph hs hu).symm.compactSpace
  | n + 1 =>
    have := compactSpace n
    have : CompactSpace {p : Quiver.Total C × ComposableArrows C n // p.1.right = p.2.left} :=
      (isClosed_eq_right_left hs ht n).isClosedEmbedding_subtypeVal.compactSpace
    (precompHomeomorph hs hu hc n).symm.compactSpace

include hs ht hu hc in
/-- When `C` is Hausdorff, `Quiver.Total C` is `σ`-compact, and source, target, units, and
composition are continuous, every nerve level `ComposableArrows C n` is `σ`-compact. -/
theorem sigmaCompactSpace [T2Space C] [SigmaCompactSpace (Quiver.Total C)] :
    ∀ n : ℕ, SigmaCompactSpace (ComposableArrows C n)
  | 0 =>
    have hsurj : Function.Surjective (Quiver.Total.left : Quiver.Total C → C) :=
      fun x ↦ ⟨⟨x, x, 𝟙 x⟩, rfl⟩
    have : SigmaCompactSpace C :=
      isSigmaCompact_univ_iff.1 (hsurj.range_eq ▸ isSigmaCompact_range hs)
    (zeroHomeomorph hs hu).isClosedEmbedding.sigmaCompactSpace
  | n + 1 =>
    have := sigmaCompactSpace n
    have : SigmaCompactSpace {p : Quiver.Total C × ComposableArrows C n // p.1.right = p.2.left} :=
      (isClosed_eq_right_left hs ht n).sigmaCompactSpace
    (precompHomeomorph hs hu hc n).isClosedEmbedding.sigmaCompactSpace

end CategoryTheory.ComposableArrows

namespace TauCeti

section TopologicalNerveInstances

variable {C : Type u} [Category.{v} C] [TopologicalSpace (Quiver.Total C)] (Δ : SimplexCategoryᵒᵖ)

instance instT0SpaceTopologicalNerve [T0Space (Quiver.Total C)] :
    T0Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T0Space (ComposableArrows C Δ.unop.len))

instance instT1SpaceTopologicalNerve [T1Space (Quiver.Total C)] :
    T1Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T1Space (ComposableArrows C Δ.unop.len))

instance instT2SpaceTopologicalNerve [T2Space (Quiver.Total C)] :
    T2Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T2Space (ComposableArrows C Δ.unop.len))

instance instRegularSpaceTopologicalNerve [RegularSpace (Quiver.Total C)] :
    RegularSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (RegularSpace (ComposableArrows C Δ.unop.len))

instance instT3SpaceTopologicalNerve [T3Space (Quiver.Total C)] :
    T3Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T3Space (ComposableArrows C Δ.unop.len))

instance instFirstCountableTopologyTopologicalNerve [FirstCountableTopology (Quiver.Total C)] :
    FirstCountableTopology ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (FirstCountableTopology (ComposableArrows C Δ.unop.len))

instance instSecondCountableTopologyTopologicalNerve [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (SecondCountableTopology (ComposableArrows C Δ.unop.len))

instance instCompactSpaceTopologicalNerve [CompactSpace (ComposableArrows C Δ.unop.len)] :
    CompactSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (CompactSpace (ComposableArrows C Δ.unop.len))

instance instSigmaCompactSpaceTopologicalNerve [SigmaCompactSpace (ComposableArrows C Δ.unop.len)] :
    SigmaCompactSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (SigmaCompactSpace (ComposableArrows C Δ.unop.len))

instance instLindelofSpaceTopologicalNerve [LindelofSpace (ComposableArrows C Δ.unop.len)] :
    LindelofSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (LindelofSpace (ComposableArrows C Δ.unop.len))

end TopologicalNerveInstances

end TauCeti
