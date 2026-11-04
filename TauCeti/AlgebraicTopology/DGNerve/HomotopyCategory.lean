/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import TauCeti.AlgebraicTopology.DGNerve.Basic
import TauCeti.CategoryTheory.EqToHom

/-!
# The homotopy category of the differential graded nerve

The homotopy category of the differential graded nerve `N_dg(C)` of a differential graded category
`C` is the homotopy category `H⁰(C)`, whose morphisms are the closed degree-zero morphisms modulo
boundaries. This identifies the shadow of `N_dg(C)` among ordinary categories, so that statements
about the `∞`-category `N_dg(C)` can be compared with statements about `H⁰(C)`. Mathlib's homotopy
category of a simplicial set is defined through its `2`-truncation for every simplicial set, so the
comparison does not involve horn filling.

The canonical functor `H⁰(C) ⥤ ho(N_dg(C))` is the identity on objects and sends the class of a
closed morphism to its edge. A morphism `η` of degree `-1` with `d η = f - f'` is the coherence of a
`2`-simplex with edges `f`, the identity and `f'`, so homotopic morphisms give the same morphism of
`ho(N_dg(C))`; the zero homotopy gives a `2`-simplex with edges `f`, `g` and their composite. In the
other direction an edge goes to the class of the closed morphism it carries, and a `2`-simplex
becomes a commutative triangle of classes because its coherence `η` satisfies `d η = g ∘ f - h`. The
two functors are inverse to each other on the nose.

## Main definitions

* `TauCeti.dgNerve.toHomotopyCategory`: the canonical functor `H⁰(C) ⥤ ho(N_dg(C))`.
* `TauCeti.dgNerve.fromHomotopyCategory`: the functor `ho(N_dg(C)) ⥤ H⁰(C)` sending an edge to the
  class of its closed morphism.
* `TauCeti.dgNerve.homotopyCategoryEquiv`: the resulting isomorphism of categories, as an
  equivalence.

## Main results

* `TauCeti.DGNerve.Simplex.homOf_comp_homOf`: the edges of a `2`-simplex form a commutative
  triangle in `H⁰(C)`.
* `TauCeti.dgNerve.toHomotopyCategory_comp_fromHomotopyCategory` and
  `TauCeti.dgNerve.fromHomotopyCategory_comp_toHomotopyCategory`: the two functors are inverse
  isomorphisms of categories.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Remark 1.3.1.11.
-/

public section

open CategoryTheory Finset Simplicial

namespace TauCeti

universe v u

namespace DGNerve

namespace Simplex

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-- **A `2`-simplex commutes in the homotopy category**: the classes of its edges `f : X 0 ⟶ X 1`
and `g : X 1 ⟶ X 2` compose to the class of its edge `h : X 0 ⟶ X 2`, since its coherence
`η` satisfies `d η = g ∘ f - h`. -/
@[reassoc]
theorem homOf_comp_homOf (x : Simplex R C 2) :
    DGHomotopyCategory.homOf R _ (x.coh_empty_mem_dgCycles 0 1 (by decide)) ≫
        DGHomotopyCategory.homOf R _ (x.coh_empty_mem_dgCycles 1 2 (by decide)) =
      DGHomotopyCategory.homOf R _ (x.coh_empty_mem_dgCycles 0 2 (by decide)) := by
  rw [DGHomotopyCategory.homOf_comp, DGHomotopyCategory.homOf_eq_iff, mem_dgBoundaries,
    dgCompZero_def]
  exact ⟨_, x.dgDifferential_coh_two⟩

end Simplex

end DGNerve

open DGNerve SSet

namespace dgNerve

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- The `2`-simplex `TauCeti.DGNerve.Simplex.mk₂` witnesses that the edge of `h` is a composite of
the edges of `f` and `g`. -/
private noncomputable def compStructMk₂ {X₀ X₁ X₂ : C} (f : dgCycles R X₀ X₁)
    (g : dgCycles R X₁ X₂) (h : dgCycles R X₀ X₂) (η : DGHom R (-1) X₀ X₂)
    (hη : dgDifferential R (-1) η = dgCompZero R f.1 g.1 - h.1) :
    (edgeMk R C f).CompStruct (edgeMk R C g) (edgeMk R C h) :=
  .mk (Simplex.mk₂ f g h η hη) ((Simplex.mk₂_map_δ_two f g h η hη).trans (edgeMk_edge R C f).symm)
    ((Simplex.mk₂_map_δ_zero f g h η hη).trans (edgeMk_edge R C g).symm)
    ((Simplex.mk₂_map_δ_one f g h η hη).trans (edgeMk_edge R C h).symm)

/-- In the homotopy category of the differential graded nerve, the edge of `h` is the composite of
the edges of `f` and `g` when `d η = g ∘ f - h`. -/
private lemma homMk_comp_homMk_of_dgDifferential_eq {X₀ X₁ X₂ : C} (f : dgCycles R X₀ X₁)
    (g : dgCycles R X₁ X₂) (h : dgCycles R X₀ X₂) (η : DGHom R (-1) X₀ X₂)
    (hη : dgDifferential R (-1) η = dgCompZero R f.1 g.1 - h.1) :
    HomotopyCategory.homMk (edgeMk R C f) ≫ HomotopyCategory.homMk (edgeMk R C g) =
      HomotopyCategory.homMk (edgeMk R C h) :=
  HomotopyCategory.homMk_comp_homMk (compStructMk₂ R C f g h η hη)

/-- The edge of the identity is the identity of the homotopy category. -/
private lemma homMk_edgeMk_dgId (X : C) :
    HomotopyCategory.homMk (edgeMk R C ⟨dgId R X, (mem_dgCycles R).2 (dgDifferential_dgId R X)⟩) =
      𝟙 _ := by
  rw [edgeMk_dgId, HomotopyCategory.homMk_id]

/-- Closed morphisms with the same homotopy class give the same morphism of the homotopy category
of the differential graded nerve. -/
private lemma homMk_edgeMk_eq_of_homOf_eq {X Y : C} {f f' : dgCycles R X Y}
    (h : DGHomotopyCategory.homOf R f.1 f.2 = DGHomotopyCategory.homOf R f'.1 f'.2) :
    HomotopyCategory.homMk (edgeMk R C f) = HomotopyCategory.homMk (edgeMk R C f') := by
  obtain ⟨η, hη⟩ := (mem_dgBoundaries R).1 ((DGHomotopyCategory.homOf_eq_iff R f.2 f'.2).1 h)
  rw [← homMk_comp_homMk_of_dgDifferential_eq R C f
    ⟨dgId R Y, (mem_dgCycles R).2 (dgDifferential_dgId R Y)⟩ f' η
    (by rw [hη, dgCompZero_def, dgComp_dgId]), homMk_edgeMk_dgId, Category.comp_id]

/-- The edge of a composite is the composite of the edges. -/
private lemma homMk_edgeMk_comp {X Y Z : C} (f : dgCycles R X Y) (g : dgCycles R Y Z) :
    HomotopyCategory.homMk (edgeMk R C f) ≫ HomotopyCategory.homMk (edgeMk R C g) =
      HomotopyCategory.homMk (edgeMk R C ⟨_, dgCompZero_mem_dgCycles R f.2 g.2⟩) :=
  homMk_comp_homMk_of_dgDifferential_eq R C f g _ 0 (by rw [map_zero, sub_self])

/-- A chosen closed degree-zero representative of a morphism of the homotopy category of `C`. -/
private noncomputable def rep {X Y : DGHomotopyCategory R C} (φ : X ⟶ Y) :
    dgCycles R X.underlying Y.underlying :=
  ⟨_, (exists_dgHomotopyClass_eq R (X := X.underlying) (Y := Y.underlying) φ).choose_spec.choose⟩

/-- The chosen representative of a morphism of the homotopy category of `C` represents it. -/
private lemma homOf_rep {X Y : DGHomotopyCategory R C} (φ : X ⟶ Y) :
    DGHomotopyCategory.homOf R (rep R C φ).1 (rep R C φ).2 = φ :=
  (DGHomotopyCategory.homOf_def R _ _).trans
    (exists_dgHomotopyClass_eq R (X := X.underlying) (Y := Y.underlying) φ).choose_spec.choose_spec

/-- The canonical functor from the homotopy category `H⁰(C)` of a differential graded category
to the homotopy category of its differential graded nerve: it is the identity on objects and sends
the class of a closed degree-zero morphism to its edge. -/
noncomputable def toHomotopyCategory :
    DGHomotopyCategory R C ⥤ (dgNerve R C).HomotopyCategory where
  obj X := HomotopyCategory.mk ((dgNerveEquiv R C).symm X.underlying)
  map φ := HomotopyCategory.homMk (edgeMk R C (rep R C φ))
  map_id X :=
    (homMk_edgeMk_eq_of_homOf_eq R C ((homOf_rep R C _).trans
      (DGHomotopyCategory.homOf_dgId R X.underlying).symm)).trans
        (homMk_edgeMk_dgId R C X.underlying)
  map_comp φ ψ := by
    rw [homMk_edgeMk_comp]
    refine homMk_edgeMk_eq_of_homOf_eq R C ?_
    exact (homOf_rep R C _).trans
      ((congrArg₂ (· ≫ ·) (homOf_rep R C φ) (homOf_rep R C ψ)).symm.trans
        (DGHomotopyCategory.homOf_comp R _ _ (rep R C φ).2 (rep R C ψ).2))

/-- The canonical functor sends an object of `C` to its vertex of the differential graded nerve. -/
@[simp]
theorem toHomotopyCategory_obj (X : DGHomotopyCategory R C) :
    (toHomotopyCategory R C).obj X = HomotopyCategory.mk ((dgNerveEquiv R C).symm X.underlying) :=
  (rfl)

/-- The canonical functor sends the class of a closed degree-zero morphism to its edge. -/
@[simp]
theorem toHomotopyCategory_map_homOf {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    (toHomotopyCategory R C).map (DGHomotopyCategory.homOf R f hf) =
      eqToHom (toHomotopyCategory_obj R C (DGHomotopyCategory.of R X)) ≫
        HomotopyCategory.homMk (edgeMk R C ⟨f, hf⟩) ≫
          eqToHom (toHomotopyCategory_obj R C (DGHomotopyCategory.of R Y)).symm :=
  (conj_eqToHom_iff_heq _ _ _ (toHomotopyCategory_obj R C _)).2
    (heq_of_eq (homMk_edgeMk_eq_of_homOf_eq R C (homOf_rep R C _)))

/-- The class in `H⁰(C)` of the closed degree-zero morphism carried by an edge of the differential
graded nerve. -/
private noncomputable def edgeHom {x y : (dgNerve R C) _⦋0⦌} (e : (dgNerve R C).Edge x y) :
    DGHomotopyCategory.of R (dgNerveEquiv R C x) ⟶ DGHomotopyCategory.of R (dgNerveEquiv R C y) :=
  eqToHom (by
      rw [dgNerveEquiv_apply]
      exact congrArg (fun z : (dgNerve R C) _⦋0⦌ ↦ DGHomotopyCategory.of R (Simplex.obj z 0))
        e.src_eq.symm) ≫
    DGHomotopyCategory.homOf R _ (Simplex.coh_empty_mem_dgCycles (n := 1) e.edge 0 1 (by decide)) ≫
      eqToHom (by
        rw [dgNerveEquiv_apply]
        exact congrArg (fun z : (dgNerve R C) _⦋0⦌ ↦ DGHomotopyCategory.of R (Simplex.obj z 0))
          e.tgt_eq)

/-- `TauCeti.dgNerve.edgeHom` in terms of any morphism heterogeneously equal to the coherence of
the edge. -/
private lemma edgeHom_eq {x y : (dgNerve R C) _⦋0⦌} (e : (dgNerve R C).Edge x y) {X Y : C}
    (hX : Simplex.obj x 0 = X) (hY : Simplex.obj y 0 = Y) (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y)
    (h : Simplex.coh (n := 1) e.edge 0 1 ∅ 0 (by decide) (empty_subset _) (by simp) ≍ f) :
    edgeHom R C e = eqToHom (by rw [dgNerveEquiv_apply, hX]) ≫ DGHomotopyCategory.homOf R f hf ≫
      eqToHom (by rw [dgNerveEquiv_apply, hY]) := by
  obtain ⟨s, rfl, rfl⟩ := e
  subst hX hY
  obtain rfl := eq_of_heq h
  rfl

/-- The degenerate edge at a vertex represents the identity. -/
private lemma edgeHom_id (x : (dgNerve R C) _⦋0⦌) : edgeHom R C (Edge.id x) = 𝟙 _ := by
  rw [edgeHom_eq R C (Edge.id x) rfl rfl (dgId R (Simplex.obj x 0))
    ((mem_dgCycles R).2 (dgDifferential_dgId R _))
    (by rw [Edge.id_edge, dgNerve_σ]; exact heq_of_eq (Simplex.coh_map_σ_zero x)),
    DGHomotopyCategory.homOf_dgId]
  simp

/-- The three edges of a `2`-simplex of the differential graded nerve form a commutative triangle
of homotopy classes. -/
private lemma edgeHom_comp_edgeHom {x₀ x₁ x₂ : (dgNerve R C) _⦋0⦌} {e₀₁ : (dgNerve R C).Edge x₀ x₁}
    {e₁₂ : (dgNerve R C).Edge x₁ x₂} {e₀₂ : (dgNerve R C).Edge x₀ x₂}
    (h : e₀₁.CompStruct e₁₂ e₀₂) :
    edgeHom R C e₀₁ ≫ edgeHom R C e₁₂ = edgeHom R C e₀₂ := by
  let σ : Simplex R C 2 := h.simplex
  have h₀ : Simplex.obj x₀ 0 = σ.obj 0 := by
    rw [← e₀₁.src_eq, ← h.d₂, dgNerve_δ_obj, dgNerve_δ_obj]
    simp [σ]
  have h₁ : Simplex.obj x₁ 0 = σ.obj 1 := by
    rw [← e₁₂.src_eq, ← h.d₀, dgNerve_δ_obj, dgNerve_δ_obj]
    simp [σ]
  have h₂ : Simplex.obj x₂ 0 = σ.obj 2 := by
    rw [← e₁₂.tgt_eq, ← h.d₀, dgNerve_δ_obj, dgNerve_δ_obj]
    simp [σ]
  rw [edgeHom_eq R C e₀₁ h₀ h₁ _ (σ.coh_empty_mem_dgCycles 0 1 (by decide))
      (by rw [← h.d₂, dgNerve_δ]; exact heq_of_eq σ.coh_map_δ_two),
    edgeHom_eq R C e₁₂ h₁ h₂ _ (σ.coh_empty_mem_dgCycles 1 2 (by decide))
      (by rw [← h.d₀, dgNerve_δ]; exact heq_of_eq σ.coh_map_δ_zero),
    edgeHom_eq R C e₀₂ h₀ h₂ _ (σ.coh_empty_mem_dgCycles 0 2 (by decide))
      (by rw [← h.d₁, dgNerve_δ]; exact heq_of_eq σ.coh_map_δ_one)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Simplex.homOf_comp_homOf_assoc]

/-- The functor from the homotopy category of the differential graded nerve to the homotopy
category `H⁰(C)`: it is the identity on objects and sends an edge to the class of the closed
degree-zero morphism it carries. It is inverse to `TauCeti.dgNerve.toHomotopyCategory`. -/
noncomputable def fromHomotopyCategory :
    (dgNerve R C).HomotopyCategory ⥤ DGHomotopyCategory R C :=
  Truncated.HomotopyCategory.lift (fun x ↦ DGHomotopyCategory.of R (dgNerveEquiv R C x))
    (fun e ↦ edgeHom R C (Edge.ofTruncated e)) (fun x ↦ edgeHom_id R C x)
    (fun h ↦ edgeHom_comp_edgeHom R C (Edge.CompStruct.ofTruncated h))

/-- The inverse functor sends a vertex of the differential graded nerve to its object. -/
@[simp]
theorem fromHomotopyCategory_obj_mk (x : (dgNerve R C) _⦋0⦌) :
    (fromHomotopyCategory R C).obj (HomotopyCategory.mk x) =
      DGHomotopyCategory.of R (dgNerveEquiv R C x) :=
  (rfl)

/-- The inverse functor sends an edge to `TauCeti.dgNerve.edgeHom`. -/
private lemma fromHomotopyCategory_map_homMk {x y : (dgNerve R C) _⦋0⦌}
    (e : (dgNerve R C).Edge x y) :
    (fromHomotopyCategory R C).map (HomotopyCategory.homMk e) = edgeHom R C e := by
  unfold fromHomotopyCategory
  exact Truncated.HomotopyCategory.lift_map_homMk _ (fun e ↦ edgeHom R C (Edge.ofTruncated e))
    (fun x ↦ edgeHom_id R C x) (fun h ↦ edgeHom_comp_edgeHom R C (Edge.CompStruct.ofTruncated h))
    e.toTruncated

/-- The inverse functor sends an edge to the class of any morphism heterogeneously equal to the
coherence of the edge. -/
theorem fromHomotopyCategory_map_homMk_heq {x y : (dgNerve R C) _⦋0⦌}
    (e : (dgNerve R C).Edge x y) {X Y : C} (hX : Simplex.obj x 0 = X) (hY : Simplex.obj y 0 = Y)
    (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y)
    (h : Simplex.coh (n := 1) e.edge 0 1 ∅ 0 (by decide) (empty_subset _) (by simp) ≍ f) :
    (fromHomotopyCategory R C).map (HomotopyCategory.homMk e) ≍ DGHomotopyCategory.homOf R f hf :=
  (conj_eqToHom_iff_heq' _ _ _ _).1
    ((fromHomotopyCategory_map_homMk R C e).trans (edgeHom_eq R C e hX hY f hf h))

/-- The inverse functor sends the edge of a closed degree-zero morphism to its class. -/
@[simp]
theorem fromHomotopyCategory_map_homMk_edgeMk {X Y : C} (f : dgCycles R X Y) :
    (fromHomotopyCategory R C).map (HomotopyCategory.homMk (edgeMk R C f)) =
      eqToHom (by rw [fromHomotopyCategory_obj_mk, Equiv.apply_symm_apply]) ≫
        DGHomotopyCategory.homOf R f.1 f.2 ≫
          eqToHom (by rw [fromHomotopyCategory_obj_mk, Equiv.apply_symm_apply]) :=
  (conj_eqToHom_iff_heq' _ _ _ _).2 (fromHomotopyCategory_map_homMk_heq R C (edgeMk R C f)
    (by rw [dgNerveEquiv_symm_apply, Simplex.vertex_obj])
    (by rw [dgNerveEquiv_symm_apply, Simplex.vertex_obj]) f.1 f.2
    (by rw [edgeMk_edge]; exact heq_of_eq (Simplex.edge_coh_zero_one f)))

/-- **Inverse functors, first composite**: the canonical functor
`TauCeti.dgNerve.toHomotopyCategory` followed by `TauCeti.dgNerve.fromHomotopyCategory` is the
identity of `H⁰(C)`. -/
theorem toHomotopyCategory_comp_fromHomotopyCategory :
    toHomotopyCategory R C ⋙ fromHomotopyCategory R C = 𝟭 _ := by
  refine CategoryTheory.Functor.hext
    (fun X ↦ DGHomotopyCategory.ext R ((dgNerveEquiv R C).apply_symm_apply _)) (fun X Y φ ↦ ?_)
  have hX : Simplex.obj ((dgNerveEquiv R C).symm X.underlying) 0 = X.underlying := by
    rw [dgNerveEquiv_symm_apply, Simplex.vertex_obj]
  have hY : Simplex.obj ((dgNerveEquiv R C).symm Y.underlying) 0 = Y.underlying := by
    rw [dgNerveEquiv_symm_apply, Simplex.vertex_obj]
  exact (fromHomotopyCategory_map_homMk_heq R C (edgeMk R C (rep R C φ)) hX hY _ (rep R C φ).2
    (by rw [edgeMk_edge]; exact heq_of_eq (Simplex.edge_coh_zero_one _))).trans
      (heq_of_eq (homOf_rep R C φ))

/-- **Inverse functors, second composite**: `TauCeti.dgNerve.fromHomotopyCategory` followed by the
canonical functor `TauCeti.dgNerve.toHomotopyCategory` is the identity of the homotopy category of
the differential graded nerve. -/
theorem fromHomotopyCategory_comp_toHomotopyCategory :
    fromHomotopyCategory R C ⋙ toHomotopyCategory R C = 𝟭 _ := by
  refine Truncated.HomotopyCategory.functor_ext
    (fun x ↦ congrArg HomotopyCategory.mk ((dgNerveEquiv R C).symm_apply_apply x))
    (fun x y e ↦ (conj_eqToHom_iff_heq _ _ _
      (congrArg HomotopyCategory.mk ((dgNerveEquiv R C).symm_apply_apply y))).2 ?_)
  let e' : (dgNerve R C).Edge x y := Edge.ofTruncated e
  let c : dgCycles R (Simplex.obj (n := 1) e'.edge 0) (Simplex.obj (n := 1) e'.edge 1) :=
    ⟨_, Simplex.coh_empty_mem_dgCycles (n := 1) e'.edge 0 1 (by decide)⟩
  have hX : Simplex.obj x 0 = Simplex.obj (n := 1) e'.edge 0 :=
    congrArg (fun z : (dgNerve R C) _⦋0⦌ ↦ Simplex.obj z 0) e'.src_eq.symm
  have hY : Simplex.obj y 0 = Simplex.obj (n := 1) e'.edge 1 :=
    congrArg (fun z : (dgNerve R C) _⦋0⦌ ↦ Simplex.obj z 0) e'.tgt_eq.symm
  have h₁ := fromHomotopyCategory_map_homMk_heq R C e' hX hY c.1 c.2 HEq.rfl
  have h₂ : (toHomotopyCategory R C).map ((fromHomotopyCategory R C).map
      (HomotopyCategory.homMk e')) ≍
        (toHomotopyCategory R C).map (DGHomotopyCategory.homOf R c.1 c.2) :=
    (toHomotopyCategory R C).map_heq
      (congrArg (DGHomotopyCategory.of R) ((dgNerveEquiv_apply R C x).trans hX))
      (congrArg (DGHomotopyCategory.of R) ((dgNerveEquiv_apply R C y).trans hY)) h₁
  have h₃ : HomotopyCategory.homMk (edgeMk R C c) ≍ HomotopyCategory.homMk e' := by
    obtain ⟨hs, ht, h⟩ := (Arrow.mk_eq_mk_iff _ _).1
      (Truncated.HomotopyCategory.congr_arrowMk_homMk (edgeMk R C c).toTruncated e
        ((edgeMk_edge R C c).trans (Simplex.eq_edge (R := R) e'.edge).symm))
    exact (conj_eqToHom_iff_heq _ _ hs ht).1 h
  exact (h₂.trans ((conj_eqToHom_iff_heq _ _ _ (toHomotopyCategory_obj R C _)).1
    (toHomotopyCategory_map_homOf R C c.1 c.2))).trans h₃

/-- **The homotopy category of the differential graded nerve** is the homotopy category `H⁰(C)` of
the differential graded category. The equivalence is an isomorphism of categories: its functor is
the canonical functor `TauCeti.dgNerve.toHomotopyCategory`, its inverse is
`TauCeti.dgNerve.fromHomotopyCategory`, and both composites are identities. -/
noncomputable def homotopyCategoryEquiv :
    DGHomotopyCategory R C ≌ (dgNerve R C).HomotopyCategory where
  functor := toHomotopyCategory R C
  inverse := fromHomotopyCategory R C
  unitIso := eqToIso (toHomotopyCategory_comp_fromHomotopyCategory R C).symm
  counitIso := eqToIso (fromHomotopyCategory_comp_toHomotopyCategory R C)
  functor_unitIso_comp X := by simp [eqToHom_map]

/-- The functor of `TauCeti.dgNerve.homotopyCategoryEquiv` is the canonical functor. -/
@[simp]
theorem homotopyCategoryEquiv_functor :
    (homotopyCategoryEquiv R C).functor = toHomotopyCategory R C :=
  (rfl)

/-- The inverse of `TauCeti.dgNerve.homotopyCategoryEquiv` is
`TauCeti.dgNerve.fromHomotopyCategory`. -/
@[simp]
theorem homotopyCategoryEquiv_inverse :
    (homotopyCategoryEquiv R C).inverse = fromHomotopyCategory R C :=
  (rfl)

end dgNerve

end TauCeti
