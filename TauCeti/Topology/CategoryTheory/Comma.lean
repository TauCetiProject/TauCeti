/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Comma.Groupoid
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Weak fiber products of topological groupoids

Let `L : A ⥤ T` and `R : B ⥤ T` be functors between categories whose objects and total arrows
(`Quiver.Total`) carry topologies, as for topological groupoids. For groupoids `A`, `B` and `T`,
the comma category `CategoryTheory.Comma L R` is their weak fiber product: its objects are the
triples `(a, h, b)` with `h : L a ⟶ R b`, and its arrows are the pairs of arrows of `A` and `B`
forming commuting squares with these structure arrows.

This file gives `Comma L R` its topologies. An object is topologized by its left object, its
structure arrow as a total arrow of `T`, and its right object; an arrow is topologized by its
source, its target and its two components, as total arrows of `A` and `B`. As for the topological
nerve, recording the target as well as the source makes source and target continuous with no
hypothesis on `T`. With these topologies:

* source and target are continuous, and units, composition and inversion are continuous when they
  are in `A` and `B`;
* objects and arrows are Hausdorff, respectively second countable, when the spaces they are
  recorded in are;
* when `A` is a groupoid, the arrows are homeomorphic to the fiber product of the objects with the
  total arrows of `A` and `B` over the objects of `A` and `B`
  (`CategoryTheory.Comma.totalHomeomorph`), provided `L` and `R` are continuous on total arrows
  and the target maps of `A` and `B`, composition in `T` and inversion in `A` are continuous;
* consequently the source is a local homeomorphism when the sources of `A` and `B` are
  (`CategoryTheory.Comma.isLocalHomeomorph_source`), and so is the target when `A` and `B` are
  groupoids with continuous inversion (`CategoryTheory.Comma.isLocalHomeomorph_target`);
* the source-target map is proper when those of `A` and `B` are and the arrows of `T` are
  Hausdorff (`CategoryTheory.Comma.isProperMap_source_target`).

So the weak fiber product of two proper étale groupoids with continuous inversion over a
topological groupoid with continuous composition and Hausdorff arrows, along functors that are
continuous on total arrows, is again proper étale, without any transversality
hypothesis: transversality only enters when the object and arrow spaces are required to be
manifolds. Every arrow of the factors is retained, including isotropy acting trivially.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open Filter Topology

namespace CategoryTheory.Comma

variable {A B T : Type*} [Category A] [Category B] [Category T] {L : A ⥤ T} {R : B ⥤ T}

section Topology

variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace (Quiver.Total T)]

/-- The topology on the objects of a comma category, induced by the left object, the structure
arrow as a total arrow of `T`, and the right object. -/
instance instTopologicalSpace : TopologicalSpace (Comma L R) :=
  TopologicalSpace.induced
    (fun X : Comma L R ↦ (X.left, (⟨_, _, X.hom⟩ : Quiver.Total T), X.right)) inferInstance

/-- An object of a comma category is determined by its left object, its structure arrow as a
total arrow, and its right object, and its topology is induced by these coordinates. -/
theorem isEmbedding_left_totalHom_right :
    IsEmbedding (fun X : Comma L R ↦ (X.left, (⟨_, _, X.hom⟩ : Quiver.Total T), X.right)) := by
  refine ⟨⟨rfl⟩, ?_⟩
  rintro ⟨l, r, h⟩ ⟨l', r', h'⟩ he
  simp only [Prod.mk.injEq, Quiver.Total.mk.injEq] at he
  obtain ⟨rfl, ⟨-, -, hh⟩, rfl⟩ := he
  cases eq_of_heq hh
  rfl

/-- A map into the objects of a comma category is continuous exactly when its left object,
structure arrow and right object are. -/
theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {g : Y → Comma L R} :
    Continuous g ↔ Continuous (fun y ↦ (g y).left) ∧
      Continuous (fun y ↦ (⟨_, _, (g y).hom⟩ : Quiver.Total T)) ∧
        Continuous (fun y ↦ (g y).right) := by
  rw [isEmbedding_left_totalHom_right.continuous_iff, continuous_prodMk, continuous_prodMk]
  rfl

/-- The left object of an object of a comma category depends continuously on it. -/
@[fun_prop]
theorem continuous_left : Continuous (Comma.left : Comma L R → A) :=
  (continuous_iff.mp continuous_id).1

/-- The structure arrow of an object of a comma category depends continuously on it. -/
@[fun_prop]
theorem continuous_totalHom :
    Continuous (fun X : Comma L R ↦ (⟨_, _, X.hom⟩ : Quiver.Total T)) :=
  (continuous_iff.mp continuous_id).2.1

/-- The right object of an object of a comma category depends continuously on it. -/
@[fun_prop]
theorem continuous_right : Continuous (Comma.right : Comma L R → B) :=
  (continuous_iff.mp continuous_id).2.2

/-- The objects of a comma category are Hausdorff when its coordinates are. -/
instance instT2Space [T2Space A] [T2Space B] [T2Space (Quiver.Total T)] : T2Space (Comma L R) :=
  isEmbedding_left_totalHom_right.t2Space

/-- The objects of a comma category are second countable when its coordinates are. -/
instance instSecondCountableTopology [SecondCountableTopology A] [SecondCountableTopology B]
    [SecondCountableTopology (Quiver.Total T)] : SecondCountableTopology (Comma L R) :=
  isEmbedding_left_totalHom_right.isInducing.secondCountableTopology

variable [TopologicalSpace (Quiver.Total A)] [TopologicalSpace (Quiver.Total B)]

/-- The topology on the total arrows of a comma category, induced by the source, the target and
the two components as total arrows of `A` and `B`. -/
instance instTopologicalSpaceTotal : TopologicalSpace (Quiver.Total (Comma L R)) :=
  TopologicalSpace.induced
    (fun f : Quiver.Total (Comma L R) ↦ (f.left, f.right,
      (⟨_, _, f.hom.left⟩ : Quiver.Total A), (⟨_, _, f.hom.right⟩ : Quiver.Total B)))
    inferInstance

/-- An arrow of a comma category is determined by its source, its target and its two
components, and its topology is induced by these coordinates. -/
theorem isEmbedding_total :
    IsEmbedding (fun f : Quiver.Total (Comma L R) ↦ (f.left, f.right,
      (⟨_, _, f.hom.left⟩ : Quiver.Total A), (⟨_, _, f.hom.right⟩ : Quiver.Total B))) := by
  refine ⟨⟨rfl⟩, ?_⟩
  rintro ⟨X, Y, f⟩ ⟨X', Y', f'⟩ he
  simp only [Prod.mk.injEq, Quiver.Total.mk.injEq] at he
  obtain ⟨rfl, rfl, ⟨-, -, hl⟩, ⟨-, -, hr⟩⟩ := he
  rw [hom_ext f f' (eq_of_heq hl) (eq_of_heq hr)]

/-- A map into the total arrows of a comma category is continuous exactly when its source,
target and two components are. -/
theorem continuous_total_iff {Y : Type*} [TopologicalSpace Y]
    {g : Y → Quiver.Total (Comma L R)} :
    Continuous g ↔ Continuous (fun y ↦ (g y).left) ∧ Continuous (fun y ↦ (g y).right) ∧
      Continuous (fun y ↦ (⟨_, _, (g y).hom.left⟩ : Quiver.Total A)) ∧
        Continuous (fun y ↦ (⟨_, _, (g y).hom.right⟩ : Quiver.Total B)) := by
  rw [isEmbedding_total.continuous_iff, continuous_prodMk, continuous_prodMk, continuous_prodMk]
  rfl

/-- The source map of a comma category is continuous. -/
@[fun_prop]
theorem continuous_source :
    Continuous (Quiver.Total.left : Quiver.Total (Comma L R) → Comma L R) :=
  (continuous_total_iff.mp continuous_id).1

/-- The target map of a comma category is continuous. -/
@[fun_prop]
theorem continuous_target :
    Continuous (Quiver.Total.right : Quiver.Total (Comma L R) → Comma L R) :=
  (continuous_total_iff.mp continuous_id).2.1

/-- The left component of an arrow of a comma category depends continuously on it. -/
@[fun_prop]
theorem continuous_homLeft :
    Continuous (fun f : Quiver.Total (Comma L R) ↦ (⟨_, _, f.hom.left⟩ : Quiver.Total A)) :=
  (continuous_total_iff.mp continuous_id).2.2.1

/-- The right component of an arrow of a comma category depends continuously on it. -/
@[fun_prop]
theorem continuous_homRight :
    Continuous (fun f : Quiver.Total (Comma L R) ↦ (⟨_, _, f.hom.right⟩ : Quiver.Total B)) :=
  (continuous_total_iff.mp continuous_id).2.2.2

/-- The arrows of a comma category are Hausdorff when its objects and the arrows of `A` and `B`
are. -/
instance instT2SpaceTotal [T2Space (Comma L R)] [T2Space (Quiver.Total A)]
    [T2Space (Quiver.Total B)] : T2Space (Quiver.Total (Comma L R)) :=
  isEmbedding_total.t2Space

/-- The arrows of a comma category are second countable when its objects and the arrows of `A`
and `B` are. -/
instance instSecondCountableTopologyTotal [SecondCountableTopology (Comma L R)]
    [SecondCountableTopology (Quiver.Total A)] [SecondCountableTopology (Quiver.Total B)] :
    SecondCountableTopology (Quiver.Total (Comma L R)) :=
  isEmbedding_total.isInducing.secondCountableTopology

/-- The unit map of a comma category is continuous when those of `A` and `B` are. -/
theorem continuous_unit (hA : Continuous fun a : A ↦ (⟨a, a, 𝟙 a⟩ : Quiver.Total A))
    (hB : Continuous fun b : B ↦ (⟨b, b, 𝟙 b⟩ : Quiver.Total B)) :
    Continuous fun X : Comma L R ↦ (⟨X, X, 𝟙 X⟩ : Quiver.Total (Comma L R)) :=
  continuous_total_iff.mpr ⟨continuous_id, continuous_id,
    by simpa [Function.comp_def] using hA.comp continuous_left,
    by simpa [Function.comp_def] using hB.comp continuous_right⟩

/-- Composition in a comma category is continuous on composable pairs of total arrows when it is
in `A` and `B`. -/
theorem continuous_comp
    (hA : Continuous fun p : {p : Quiver.Total A × Quiver.Total A // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total A))
    (hB : Continuous fun p : {p : Quiver.Total B × Quiver.Total B // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total B)) :
    Continuous fun p : {p : Quiver.Total (Comma L R) × Quiver.Total (Comma L R) //
        p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ :
        Quiver.Total (Comma L R)) := by
  refine continuous_total_iff.mpr ⟨by fun_prop, by fun_prop, ?_, ?_⟩
  · convert hA.comp (Continuous.subtype_mk (p := fun q ↦ q.1.right = q.2.left)
      ((continuous_homLeft.comp (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_homLeft.comp (continuous_snd.comp continuous_subtype_val)))
      fun p : {p : Quiver.Total (Comma L R) × Quiver.Total (Comma L R) //
        p.1.right = p.2.left} ↦ congrArg Comma.left p.2) using 1
    funext p
    simp [eqToHom_left]
  · convert hB.comp (Continuous.subtype_mk (p := fun q ↦ q.1.right = q.2.left)
      ((continuous_homRight.comp (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_homRight.comp (continuous_snd.comp continuous_subtype_val)))
      fun p : {p : Quiver.Total (Comma L R) × Quiver.Total (Comma L R) //
        p.1.right = p.2.left} ↦ congrArg Comma.right p.2) using 1
    funext p
    simp [eqToHom_right]

/-- Inversion in the comma category of two groupoids is continuous when it is in both
factors. -/
theorem continuous_inverse [IsGroupoid A] [IsGroupoid B]
    (hA : Continuous fun f : Quiver.Total A ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total A))
    (hB : Continuous fun f : Quiver.Total B ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total B)) :
    Continuous fun f : Quiver.Total (Comma L R) ↦
      (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total (Comma L R)) :=
  continuous_total_iff.mpr ⟨continuous_target, continuous_source,
    by simpa [Function.comp_def] using hA.comp continuous_homLeft,
    by simpa [Function.comp_def] using hB.comp continuous_homRight⟩

/-- Sending an arrow of a comma category to its source and its two components is continuous. -/
@[fun_prop]
theorem continuous_totalEquiv [IsGroupoid A] :
    Continuous (totalEquiv : Quiver.Total (Comma L R) ≃ _) :=
  ((continuous_source.prodMk (continuous_homLeft.prodMk continuous_homRight)).subtype_mk
    fun _ ↦ ⟨rfl, rfl⟩).congr fun f ↦ Subtype.ext (totalEquiv_apply_coe f).symm

/-- When `A` is a groupoid, the arrow of a comma category with prescribed source and components
depends continuously on these data, provided the target maps of `A` and `B`, inversion in `A`, the
functors `L` and `R` on total arrows and composition in `T` are continuous. -/
theorem continuous_totalEquiv_symm [IsGroupoid A]
    (htA : Continuous (Quiver.Total.right : Quiver.Total A → A))
    (htB : Continuous (Quiver.Total.right : Quiver.Total B → B))
    (hinv : Continuous fun f : Quiver.Total A ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total A))
    (hL : Continuous fun f : Quiver.Total A ↦ (⟨_, _, L.map f.hom⟩ : Quiver.Total T))
    (hR : Continuous fun f : Quiver.Total B ↦ (⟨_, _, R.map f.hom⟩ : Quiver.Total T))
    (hcomp : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total T)) :
    Continuous (totalEquiv : Quiver.Total (Comma L R) ≃ _).symm := by
  set P := {p : Comma L R × Quiver.Total A × Quiver.Total B //
    p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right}
  have hX : Continuous fun p : P ↦ p.1.1 := continuous_fst.comp continuous_subtype_val
  have ha : Continuous fun p : P ↦ p.1.2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
  have hb : Continuous fun p : P ↦ p.1.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
  -- The structure arrow of the target is the composite `L a⁻¹ ≫ X.hom ≫ R b`.
  have hfirst : Continuous fun p : P ↦
      (⟨_, _, L.map (inv p.1.2.1.hom) ≫ eqToHom (congrArg L.obj p.2.1) ≫ p.1.1.hom⟩ :
        Quiver.Total T) :=
    hcomp.comp (Continuous.subtype_mk (p := fun q ↦ q.1.right = q.2.left)
      ((hL.comp (hinv.comp ha)).prodMk (continuous_totalHom.comp hX))
        fun p : P ↦ congrArg L.obj p.2.1)
  have hhom : Continuous fun p : P ↦
      (⟨_, _, (L.map (inv p.1.2.1.hom) ≫ eqToHom (congrArg L.obj p.2.1) ≫ p.1.1.hom) ≫
        eqToHom (congrArg R.obj p.2.2.symm) ≫ R.map p.1.2.2.hom⟩ : Quiver.Total T) :=
    hcomp.comp (Continuous.subtype_mk (p := fun q ↦ q.1.right = q.2.left)
      (hfirst.prodMk (hR.comp hb)) fun p : P ↦ congrArg R.obj p.2.2.symm)
  rw [continuous_total_iff]
  simp only [totalEquiv_symm_apply_left, totalEquiv_symm_apply_right,
    totalEquiv_symm_apply_hom_left, totalEquiv_symm_apply_hom_right]
  refine ⟨hX, continuous_iff.mpr ⟨htA.comp ha, ?_, htB.comp hb⟩, ha, hb⟩
  convert hhom using 1
  funext p
  obtain ⟨⟨X, ⟨a, a', α⟩, ⟨b, b', β⟩⟩, ha, hb⟩ := p
  dsimp only at ha hb
  subst ha hb
  simp

/-- When `A` is a groupoid, the arrows of the comma category are homeomorphic to the fiber
product of its objects with the total arrows of `A` and `B` over the objects of `A` and `B`,
provided the target maps of `A` and `B`, inversion in `A`, the functors `L` and `R` on total
arrows and composition in `T` are continuous. -/
noncomputable def totalHomeomorph [IsGroupoid A]
    (htA : Continuous (Quiver.Total.right : Quiver.Total A → A))
    (htB : Continuous (Quiver.Total.right : Quiver.Total B → B))
    (hinv : Continuous fun f : Quiver.Total A ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total A))
    (hL : Continuous fun f : Quiver.Total A ↦ (⟨_, _, L.map f.hom⟩ : Quiver.Total T))
    (hR : Continuous fun f : Quiver.Total B ↦ (⟨_, _, R.map f.hom⟩ : Quiver.Total T))
    (hcomp : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total T)) :
    Quiver.Total (Comma L R) ≃ₜ
      {p : Comma L R × Quiver.Total A × Quiver.Total B //
        p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right} where
  toEquiv := totalEquiv
  continuous_toFun := continuous_totalEquiv
  continuous_invFun := continuous_totalEquiv_symm htA htB hinv hL hR hcomp

/-- The homeomorphism `CategoryTheory.Comma.totalHomeomorph` is `CategoryTheory.Comma.totalEquiv`.
-/
@[simp]
theorem coe_totalHomeomorph [IsGroupoid A]
    (htA : Continuous (Quiver.Total.right : Quiver.Total A → A))
    (htB : Continuous (Quiver.Total.right : Quiver.Total B → B))
    (hinv : Continuous fun f : Quiver.Total A ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total A))
    (hL : Continuous fun f : Quiver.Total A ↦ (⟨_, _, L.map f.hom⟩ : Quiver.Total T))
    (hR : Continuous fun f : Quiver.Total B ↦ (⟨_, _, R.map f.hom⟩ : Quiver.Total T))
    (hcomp : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total T)) :
    ⇑(totalHomeomorph htA htB hinv hL hR hcomp) = totalEquiv := (rfl)

/-- The inverse of `CategoryTheory.Comma.totalHomeomorph` is the inverse of
`CategoryTheory.Comma.totalEquiv`. -/
@[simp]
theorem coe_totalHomeomorph_symm [IsGroupoid A]
    (htA : Continuous (Quiver.Total.right : Quiver.Total A → A))
    (htB : Continuous (Quiver.Total.right : Quiver.Total B → B))
    (hinv : Continuous fun f : Quiver.Total A ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total A))
    (hL : Continuous fun f : Quiver.Total A ↦ (⟨_, _, L.map f.hom⟩ : Quiver.Total T))
    (hR : Continuous fun f : Quiver.Total B ↦ (⟨_, _, R.map f.hom⟩ : Quiver.Total T))
    (hcomp : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total T)) :
    ⇑(totalHomeomorph htA htB hinv hL hR hcomp).symm = totalEquiv.symm := (rfl)

/-- Given local inverses `eA` and `eB` of the sources of `A` and `B`, the points of the fiber
product of the objects of a comma category with the total arrows of `A` and `B` whose components
lie in the sources of `eA` and `eB` are homeomorphic, by projection to the object, to the objects
whose left and right objects lie in the targets of `eA` and `eB`. -/
private def fstHomeomorph (eA : OpenPartialHomeomorph (Quiver.Total A) A)
    (eB : OpenPartialHomeomorph (Quiver.Total B) B) (hA : Quiver.Total.left = ⇑eA)
    (hB : Quiver.Total.left = ⇑eB) :
    {q : {p : Comma L R × Quiver.Total A × Quiver.Total B //
        p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right} |
      q.1.2.1 ∈ eA.source ∧ q.1.2.2 ∈ eB.source} ≃ₜ
      {X : Comma L R | X.left ∈ eA.target ∧ X.right ∈ eB.target} :=
  -- The local inverses are sections of the sources, and the source of a component of a point
  -- of the fiber product is the corresponding part of its object.
  have hsymA {x : A} (hx : x ∈ eA.target) : (eA.symm x).left = x :=
    (congrFun hA _).trans (eA.right_inv hx)
  have hsymB {x : B} (hx : x ∈ eB.target) : (eB.symm x).left = x :=
    (congrFun hB _).trans (eB.right_inv hx)
  have hleftA (q : {p : Comma L R × Quiver.Total A × Quiver.Total B //
      p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right}) : q.1.1.left = eA q.1.2.1 :=
    q.2.1.symm.trans (congrFun hA _)
  have hleftB (q : {p : Comma L R × Quiver.Total A × Quiver.Total B //
      p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right}) : q.1.1.right = eB q.1.2.2 :=
    q.2.2.symm.trans (congrFun hB _)
  { toFun q := ⟨q.1.1.1, by
      rw [Set.mem_ofPred_eq, hleftA q.1, hleftB q.1]
      exact ⟨eA.map_source q.2.1, eB.map_source q.2.2⟩⟩
    invFun X := ⟨⟨(X.1, eA.symm X.1.left, eB.symm X.1.right), hsymA X.2.1, hsymB X.2.2⟩,
      eA.map_target X.2.1, eB.map_target X.2.2⟩
    left_inv q := by
      obtain ⟨⟨⟨X, a, b⟩, hpa, hpb⟩, hqa, hqb⟩ := q
      have hla : eA.symm X.left = a := by
        rw [hleftA ⟨⟨X, a, b⟩, hpa, hpb⟩]
        exact eA.left_inv hqa
      have hlb : eB.symm X.right = b := by
        rw [hleftB ⟨⟨X, a, b⟩, hpa, hpb⟩]
        exact eB.left_inv hqb
      simp [hla, hlb]
    right_inv X := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      refine continuous_subtype_val.prodMk (.prodMk ?_ ?_)
      · exact eA.continuousOn_symm.comp_continuous (continuous_left.comp continuous_subtype_val)
          fun X ↦ X.2.1
      · exact eB.continuousOn_symm.comp_continuous
          (continuous_right.comp continuous_subtype_val) fun X ↦ X.2.2 }

/-- The projection from the fiber product of the objects of a comma category with the total
arrows of `A` and `B` to the objects is a local homeomorphism when the sources of `A` and `B`
are: near a point, it is inverted by the local inverses of the two source maps. -/
private theorem isLocalHomeomorph_fst
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B)) :
    IsLocalHomeomorph fun p : {p : Comma L R × Quiver.Total A × Quiver.Total B //
      p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right} ↦ p.1.1 := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro p
  obtain ⟨eA, haA, hA⟩ := hsA p.1.2.1
  obtain ⟨eB, hbB, hB⟩ := hsB p.1.2.2
  -- Near `p`, the projection is `fstHomeomorph` followed by the inclusion of an open set.
  have hUo : IsOpen {q : {p : Comma L R × Quiver.Total A × Quiver.Total B //
      p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right} | q.1.2.1 ∈ eA.source ∧
        q.1.2.2 ∈ eB.source} :=
    (eA.open_source.preimage (continuous_fst.comp (continuous_snd.comp
      continuous_subtype_val))).inter
      (eB.open_source.preimage (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))
  have hVo : IsOpen {X : Comma L R | X.left ∈ eA.target ∧ X.right ∈ eB.target} :=
    (eA.open_target.preimage continuous_left).inter (eB.open_target.preimage continuous_right)
  exact ⟨_, hUo.mem_nhds ⟨haA, hbB⟩,
    hVo.isOpenEmbedding_subtypeVal.comp (fstHomeomorph eA eB hA hB).isOpenEmbedding⟩

/-- The source of the comma category of a groupoid `A` and a category `B` is a local
homeomorphism when the sources of `A` and `B` are, provided the target of `B`, inversion in `A`,
the functors `L` and `R` on total arrows and composition in `T` are continuous. -/
theorem isLocalHomeomorph_source [IsGroupoid A]
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B))
    (htB : Continuous (Quiver.Total.right : Quiver.Total B → B))
    (hinv : Continuous fun f : Quiver.Total A ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total A))
    (hL : Continuous fun f : Quiver.Total A ↦ (⟨_, _, L.map f.hom⟩ : Quiver.Total T))
    (hR : Continuous fun f : Quiver.Total B ↦ (⟨_, _, R.map f.hom⟩ : Quiver.Total T))
    (hcomp : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total T)) :
    IsLocalHomeomorph (Quiver.Total.left : Quiver.Total (Comma L R) → Comma L R) := by
  -- The target of `A` is its source after inversion.
  have htA : Continuous (Quiver.Total.right : Quiver.Total A → A) := hsA.continuous.comp hinv
  convert (isLocalHomeomorph_fst hsA hsB).comp
    (totalHomeomorph htA htB hinv hL hR hcomp).isLocalHomeomorph using 1
  funext f
  simp

/-- The target of the comma category of two groupoids is a local homeomorphism when their
sources are, provided inversion in `A` and `B`, the functors `L` and `R` on total arrows and
composition in `T` are continuous. -/
theorem isLocalHomeomorph_target [IsGroupoid A] [IsGroupoid B]
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B))
    (hinvA : Continuous fun f : Quiver.Total A ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total A))
    (hinvB : Continuous fun f : Quiver.Total B ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total B))
    (hL : Continuous fun f : Quiver.Total A ↦ (⟨_, _, L.map f.hom⟩ : Quiver.Total T))
    (hR : Continuous fun f : Quiver.Total B ↦ (⟨_, _, R.map f.hom⟩ : Quiver.Total T))
    (hcomp : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total T)) :
    IsLocalHomeomorph (Quiver.Total.right : Quiver.Total (Comma L R) → Comma L R) := by
  have hinv := continuous_inverse (L := L) (R := R) hinvA hinvB
  have hinvol : Function.Involutive fun f : Quiver.Total (Comma L R) ↦
      (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total (Comma L R)) :=
    fun f ↦ by simp
  -- The target is the source after inversion, which is an involutive homeomorphism.
  let ι : Quiver.Total (Comma L R) ≃ₜ Quiver.Total (Comma L R) :=
    { toFun f := ⟨f.right, f.left, inv f.hom⟩
      invFun f := ⟨f.right, f.left, inv f.hom⟩
      left_inv := hinvol
      right_inv := hinvol
      continuous_toFun := hinv
      continuous_invFun := hinv }
  exact (isLocalHomeomorph_source hsA hsB (hsB.continuous.comp hinvB) hinvA hL hR hcomp).comp
    ι.isLocalHomeomorph

/-- The source-target map of a comma category is proper when those of `A` and `B` are, provided
the functors `L` and `R` on total arrows and composition in `T` are continuous and the arrows of
`T` are Hausdorff. Neither `T` nor the functors need to be proper. -/
theorem isProperMap_source_target [T2Space (Quiver.Total T)]
    (hpA : IsProperMap fun f : Quiver.Total A ↦ (f.left, f.right))
    (hpB : IsProperMap fun f : Quiver.Total B ↦ (f.left, f.right))
    (hL : Continuous fun f : Quiver.Total A ↦ (⟨_, _, L.map f.hom⟩ : Quiver.Total T))
    (hR : Continuous fun f : Quiver.Total B ↦ (⟨_, _, R.map f.hom⟩ : Quiver.Total T))
    (hcomp : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total T)) :
    IsProperMap fun f : Quiver.Total (Comma L R) ↦ (f.left, f.right) := by
  refine isProperMap_iff_ultrafilter.mpr ⟨by fun_prop, fun 𝒰 ⟨X, Y⟩ h ↦ ?_⟩
  have hX : Tendsto Quiver.Total.left (𝒰 : Filter (Quiver.Total (Comma L R))) (𝓝 X) :=
    (continuous_fst.tendsto _).comp h
  have hY : Tendsto Quiver.Total.right (𝒰 : Filter (Quiver.Total (Comma L R))) (𝓝 Y) :=
    (continuous_snd.tendsto _).comp h
  -- The components converge by properness of `A` and `B`.
  obtain ⟨⟨a, a', α⟩, ha, haU⟩ := hpA.ultrafilter_le_nhds_of_tendsto
    (𝒰 := 𝒰.map fun f : Quiver.Total (Comma L R) ↦ (⟨_, _, f.hom.left⟩ : Quiver.Total A))
    (y := (X.left, Y.left)) (by
      simpa [Function.comp_def] using
        ((continuous_left.tendsto X).comp hX).prodMk_nhds ((continuous_left.tendsto Y).comp hY))
  obtain ⟨⟨b, b', β⟩, hb, hbU⟩ := hpB.ultrafilter_le_nhds_of_tendsto
    (𝒰 := 𝒰.map fun f : Quiver.Total (Comma L R) ↦ (⟨_, _, f.hom.right⟩ : Quiver.Total B))
    (y := (X.right, Y.right)) (by
      simpa [Function.comp_def] using
        ((continuous_right.tendsto X).comp hX).prodMk_nhds ((continuous_right.tendsto Y).comp hY))
  simp only [Prod.mk.injEq] at ha hb
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hb
  rw [Ultrafilter.coe_map] at haU hbU
  -- The square commutes in the limit, by continuity of composition and uniqueness of limits.
  have hw : L.map α ≫ Y.hom = X.hom ≫ R.map β := by
    let S := {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left}
    have hu : Tendsto (fun f : Quiver.Total (Comma L R) ↦
        (⟨((⟨_, _, L.map f.hom.left⟩ : Quiver.Total T), ⟨_, _, f.right.hom⟩), rfl⟩ : S))
        𝒰 (𝓝 ⟨((⟨_, _, L.map α⟩ : Quiver.Total T), ⟨_, _, Y.hom⟩), rfl⟩) :=
      tendsto_subtype_rng.mpr (((hL.tendsto _).comp haU).prodMk_nhds
        ((continuous_totalHom.tendsto Y).comp hY))
    have hv : Tendsto (fun f : Quiver.Total (Comma L R) ↦
        (⟨((⟨_, _, f.left.hom⟩ : Quiver.Total T), ⟨_, _, R.map f.hom.right⟩), rfl⟩ : S))
        𝒰 (𝓝 ⟨((⟨_, _, X.hom⟩ : Quiver.Total T), ⟨_, _, R.map β⟩), rfl⟩) :=
      tendsto_subtype_rng.mpr (((continuous_totalHom.tendsto X).comp hX).prodMk_nhds
        ((hR.tendsto _).comp hbU))
    have := tendsto_nhds_unique ((hcomp.tendsto _).comp hu)
      (((hcomp.tendsto _).comp hv).congr fun f ↦ by simp)
    simpa using this
  refine ⟨⟨X, Y, ⟨α, β, hw⟩⟩, rfl, ?_⟩
  exact isEmbedding_total.tendsto_nhds_iff.mpr
    (hX.prodMk_nhds (hY.prodMk_nhds (Tendsto.prodMk_nhds haU hbU)))

end Topology

end CategoryTheory.Comma
