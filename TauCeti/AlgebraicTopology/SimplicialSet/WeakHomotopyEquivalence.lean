/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Core
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.WeaklyContractible

/-!
# Weak homotopy equivalences of simplicial sets

A map `f : X ⟶ Y` of simplicial sets is a *weak homotopy equivalence*
(`SSet.IsWeakHomotopyEquivalence`) when, for every Kan complex `Z`, precomposition with `f` induces
a bijection `π₀ Fun(Y, Z) → π₀ Fun(X, Z)` on the connected components of the simplicial sets of
maps. This is the definition of Kerodon, which tests `f` against Kan complexes rather than through
geometric realization; it does not use the realization-based weak equivalences of
`TauCeti/AlgebraicTopology/SimplicialSet/WeakEquivalence.lean`.

The vertices of `Fun(X, Z) = (ihom X).obj Z` are the maps `X ⟶ Z` (`SSet.ihomObj₀Equiv`) and its
edges between two such vertices are the simplicial homotopies between them
(`SSet.ihomEdgeEquiv`). When `Z` is a Kan complex, two maps therefore lie in the same connected
component of `Fun(X, Z)` exactly when they are homotopic, so that `f` is a weak homotopy equivalence
exactly when it induces a bijection on homotopy classes of maps into every Kan complex
(`SSet.isWeakHomotopyEquivalence_iff_homotopy`).

Weak homotopy equivalences contain the isomorphisms, are stable under composition and satisfy
two out of three. Every simplicial homotopy equivalence is a weak homotopy equivalence, and between
Kan complexes the converse holds. A simplicial set `K` is weakly contractible in the sense of
`SSet.IsWeaklyContractible` exactly when its map to `Δ[0]` is a weak homotopy equivalence, which is
Kerodon's definition of weak contractibility.

## Main declarations

* `SSet.ihomObj₀Equiv`: the vertices of `Fun(X, Z)` are the maps `X ⟶ Z`.
* `SSet.ihomEdgeEquiv`: the edges of `Fun(X, Z)` between two maps are the homotopies between them.
* `SSet.π₀_mk_ihomObj₀Equiv_symm_eq_iff`: for a Kan complex `Z`, two maps `X ⟶ Z` lie in the same
  connected component of `Fun(X, Z)` exactly when they are homotopic.
* `SSet.IsWeakHomotopyEquivalence`: weak homotopy equivalences of simplicial sets.
* `SSet.isWeakHomotopyEquivalence_iff_homotopy`: the characterization through homotopy classes.
* `SSet.IsWeakHomotopyEquivalence.of_homotopy`: homotopy equivalences are weak homotopy
  equivalences, and `SSet.isWeakHomotopyEquivalence_iff_exists_homotopy_inverse`: between Kan
  complexes, weak homotopy equivalences are homotopy equivalences.
* `SSet.IsWeakHomotopyEquivalence.of_precomp`, `SSet.IsWeakHomotopyEquivalence.of_postcomp`:
  two out of three.
* `SSet.isWeaklyContractible_iff_isWeakHomotopyEquivalence`: `K` is weakly contractible exactly
  when `K ⟶ Δ[0]` is a weak homotopy equivalence.

## References

* J. Lurie, *Kerodon*, Definition 3.1.7.12 (Tag 00UA), Proposition 3.1.7.13 (Tag 00UB) and
  Definition 3.2.4.16 (Tag 04GW).
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed Limits

open scoped Simplicial

universe u

namespace SSet

variable {X Y Z : SSet.{u}}

section MappingSpace

variable (X Z) in
/-- The vertices of the simplicial set `Fun(X, Z)` of maps are the maps `X ⟶ Z`: a vertex `v`
corresponds to the map evaluating at `v`, and a map `f` to the vertex adjoint to
`X ⊗ Δ[0] ⟶ X ⟶ Z`. -/
noncomputable def ihomObj₀Equiv : ((ihom X).obj Z) _⦋0⦌ ≃ (X ⟶ Z) where
  toFun v := lift (𝟙 X) (const v) ≫ (ihom.ev X).app Z
  invFun f := yonedaEquiv (curry (fst X Δ[0] ≫ f))
  left_inv v := by
    apply yonedaEquiv.symm.injective
    have h : fst X Δ[0] ≫ lift (𝟙 X) (const v) = X ◁ const v := by
      ext : 1 <;> simp
    rw [Equiv.symm_apply_apply, yonedaEquiv_symm_zero, curry_eq_iff, uncurry_eq,
      ← Category.assoc, h]
  right_inv f := by
    have h : (const (yonedaEquiv (curry (fst X Δ[0] ≫ f))) : X ⟶ (ihom X).obj Z) =
        stdSimplex.isTerminalObj₀.from X ≫ curry (fst X Δ[0] ≫ f) := by
      conv_rhs => rw [← yonedaEquiv.symm_apply_apply (curry (fst X Δ[0] ≫ f)),
        yonedaEquiv_symm_zero]
      exact (comp_const _ _).symm
    dsimp only
    rw [h, lift_curry_ihom_ev_app, lift_fst_assoc, Category.id_comp]

/-- The map corresponding to a vertex of `Fun(X, Z)` evaluates at that vertex. -/
lemma ihomObj₀Equiv_apply (v : ((ihom X).obj Z) _⦋0⦌) :
    ihomObj₀Equiv X Z v = lift (𝟙 X) (const v) ≫ (ihom.ev X).app Z :=
  (rfl)

/-- The vertex of `Fun(X, Z)` corresponding to a map `f : X ⟶ Z` is adjoint to
`X ⊗ Δ[0] ⟶ X ⟶ Z`. -/
lemma yonedaEquiv_symm_ihomObj₀Equiv_symm (f : X ⟶ Z) :
    yonedaEquiv.symm ((ihomObj₀Equiv X Z).symm f) = curry (fst X Δ[0] ≫ f) :=
  yonedaEquiv.symm_apply_apply (curry (fst X Δ[0] ≫ f))

/-- Precomposition `Fun(Y, Z) ⟶ Fun(X, Z)` with `f : X ⟶ Y` acts on vertices by precomposition. -/
@[simp]
lemma pre_app_app_ihomObj₀Equiv_symm (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((pre f).app Z).app _ ((ihomObj₀Equiv Y Z).symm g) = (ihomObj₀Equiv X Z).symm (f ≫ g) := by
  apply yonedaEquiv.symm.injective
  rw [← yonedaEquiv_symm_comp, yonedaEquiv_symm_ihomObj₀Equiv_symm,
    yonedaEquiv_symm_ihomObj₀Equiv_symm, curry_pre_app, whiskerRight_fst_assoc]

/-- Restricting the homotopy defined by a `1`-simplex `s` of `Fun(X, Z)` to an end of the cylinder
gives the map corresponding to the matching face of `s`. -/
private lemma whiskerLeft_δ_uncurry_yonedaEquiv_symm (s : ((ihom X).obj Z) _⦋1⦌) (i : Fin 2) :
    X ◁ stdSimplex.δ i ≫ uncurry (yonedaEquiv.symm s) =
      fst X Δ[0] ≫ ihomObj₀Equiv X Z (((ihom X).obj Z).δ i s) := by
  rw [← uncurry_natural_left, stdSimplex.δ_comp_yonedaEquiv_symm,
    ← (ihomObj₀Equiv X Z).symm_apply_apply (((ihom X).obj Z).δ i s),
    yonedaEquiv_symm_ihomObj₀Equiv_symm, uncurry_curry, Equiv.apply_symm_apply]

variable (f g : X ⟶ Z)

/-- The edges of `Fun(X, Z)` between the vertices corresponding to maps `f` and `g` are the
simplicial homotopies from `f` to `g`, through the tensor-hom adjunction. -/
noncomputable def ihomEdgeEquiv :
    Edge ((ihomObj₀Equiv X Z).symm f) ((ihomObj₀Equiv X Z).symm g) ≃ Homotopy f g where
  toFun e := Homotopy.mk' (uncurry (yonedaEquiv.symm e.edge))
    (by
      have h := whiskerLeft_δ_uncurry_yonedaEquiv_symm e.edge 1
      rw [e.src_eq, Equiv.apply_symm_apply, whiskerLeft_stdSimplex_δ_one, Category.assoc] at h
      simpa using lift (𝟙 X) (stdSimplex.isTerminalObj₀.from X) ≫= h)
    (by
      have h := whiskerLeft_δ_uncurry_yonedaEquiv_symm e.edge 0
      rw [e.tgt_eq, Equiv.apply_symm_apply, whiskerLeft_stdSimplex_δ_zero, Category.assoc] at h
      simpa using lift (𝟙 X) (stdSimplex.isTerminalObj₀.from X) ≫= h)
  invFun H := Edge.mk (yonedaEquiv (curry H.h))
    (by
      apply yonedaEquiv.symm.injective
      rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply, ← curry_natural_left,
        whiskerLeft_stdSimplex_δ_one, Category.assoc, H.h₀, yonedaEquiv_symm_ihomObj₀Equiv_symm])
    (by
      apply yonedaEquiv.symm.injective
      rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply, ← curry_natural_left,
        whiskerLeft_stdSimplex_δ_zero, Category.assoc, H.h₁, yonedaEquiv_symm_ihomObj₀Equiv_symm])
  left_inv e := by
    ext
    simp
  right_inv H := by
    apply RelativeMorphism.Homotopy.ext
    simp

/-- The homotopy defined by an edge of `Fun(X, Z)` is its uncurried `1`-simplex. -/
@[simp]
lemma ihomEdgeEquiv_apply_h
    (e : Edge ((ihomObj₀Equiv X Z).symm f) ((ihomObj₀Equiv X Z).symm g)) :
    (ihomEdgeEquiv f g e).h = uncurry (yonedaEquiv.symm e.edge) :=
  (rfl)

/-- The edge defined by a homotopy is its curried form. -/
@[simp]
lemma ihomEdgeEquiv_symm_apply_edge (H : Homotopy f g) :
    ((ihomEdgeEquiv f g).symm H).edge = yonedaEquiv (curry H.h) :=
  (rfl)

variable {f g} in
/-- Homotopic maps `X ⟶ Z` lie in the same connected component of `Fun(X, Z)`. -/
lemma Homotopy.π₀_mk_ihomObj₀Equiv_symm_eq (H : Homotopy f g) :
    π₀.mk ((ihomObj₀Equiv X Z).symm f) = π₀.mk ((ihomObj₀Equiv X Z).symm g) :=
  π₀.sound ((ihomEdgeEquiv f g).symm H)

/-- For a Kan complex `Z`, two maps `X ⟶ Z` lie in the same connected component of `Fun(X, Z)`
exactly when they are homotopic. -/
lemma π₀_mk_ihomObj₀Equiv_symm_eq_iff [KanComplex Z] :
    π₀.mk ((ihomObj₀Equiv X Z).symm f) = π₀.mk ((ihomObj₀Equiv X Z).symm g) ↔
      Nonempty (Homotopy f g) := by
  rw [π₀.mk_eq_mk_iff_nonempty_edge, (ihomEdgeEquiv f g).nonempty_congr]

variable (X Z) in
/-- Every connected component of `Fun(X, Z)` is the component of a map `X ⟶ Z`. -/
lemma π₀_mk_ihomObj₀Equiv_symm_surjective :
    Function.Surjective fun f : X ⟶ Z ↦ π₀.mk ((ihomObj₀Equiv X Z).symm f) :=
  π₀.mk_surjective.comp (ihomObj₀Equiv X Z).symm.surjective

/-- Precomposition with `f : X ⟶ Y` sends the component of `g : Y ⟶ Z` in `Fun(Y, Z)` to the
component of `f ≫ g` in `Fun(X, Z)`. -/
lemma mapπ₀_pre_app_π₀_mk_ihomObj₀Equiv_symm (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapπ₀ ((pre f).app Z) (π₀.mk ((ihomObj₀Equiv Y Z).symm g)) =
      π₀.mk ((ihomObj₀Equiv X Z).symm (f ≫ g)) := by
  rw [mapπ₀_mk, pre_app_app_ihomObj₀Equiv_symm]

/-- Precomposition with a composite acts on connected components of mapping spaces as the
composite of the precompositions. -/
lemma mapπ₀_pre_app_comp (f : X ⟶ Y) (g : Y ⟶ Z) (W : SSet.{u}) :
    mapπ₀ ((pre (f ≫ g)).app W) = mapπ₀ ((pre f).app W) ∘ mapπ₀ ((pre g).app W) := by
  funext c
  rw [pre_map, NatTrans.comp_app, Function.comp_apply, mapπ₀_comp_apply]

end MappingSpace

/-- A map `f : X ⟶ Y` of simplicial sets is a *weak homotopy equivalence* if, for every Kan complex
`Z` in the same universe, precomposition with `f` induces a bijection
`π₀ Fun(Y, Z) → π₀ Fun(X, Z)` on connected components of the simplicial sets of maps. -/
class IsWeakHomotopyEquivalence (f : X ⟶ Y) : Prop where
  bijective_mapπ₀_pre_app (Z : SSet.{u}) [KanComplex Z] :
    Function.Bijective (mapπ₀ ((pre f).app Z))

/-- A map is a weak homotopy equivalence exactly when it induces a bijection on homotopy classes of
maps into every Kan complex `Z`: every map `X ⟶ Z` is homotopic to one factoring through `f`, and
two maps `Y ⟶ Z` are homotopic as soon as their composites with `f` are. -/
lemma isWeakHomotopyEquivalence_iff_homotopy (f : X ⟶ Y) :
    IsWeakHomotopyEquivalence f ↔ ∀ (Z : SSet.{u}) [KanComplex Z],
      (∀ g : X ⟶ Z, ∃ h : Y ⟶ Z, Nonempty (Homotopy (f ≫ h) g)) ∧
        ∀ h h' : Y ⟶ Z, Nonempty (Homotopy (f ≫ h) (f ≫ h')) → Nonempty (Homotopy h h') := by
  refine ⟨fun hf Z _ ↦ ⟨fun g ↦ ?_, fun h h' H ↦ ?_⟩, fun H ↦ ⟨fun Z _ ↦ ⟨?_, ?_⟩⟩⟩
  · obtain ⟨c, hc⟩ := (hf.bijective_mapπ₀_pre_app Z).2 (π₀.mk ((ihomObj₀Equiv X Z).symm g))
    obtain ⟨h, rfl⟩ := π₀_mk_ihomObj₀Equiv_symm_surjective Y Z c
    rw [mapπ₀_pre_app_π₀_mk_ihomObj₀Equiv_symm, π₀_mk_ihomObj₀Equiv_symm_eq_iff] at hc
    exact ⟨h, hc⟩
  · rw [← π₀_mk_ihomObj₀Equiv_symm_eq_iff]
    apply (hf.bijective_mapπ₀_pre_app Z).1
    rwa [mapπ₀_pre_app_π₀_mk_ihomObj₀Equiv_symm, mapπ₀_pre_app_π₀_mk_ihomObj₀Equiv_symm,
      π₀_mk_ihomObj₀Equiv_symm_eq_iff]
  · intro c c' hcc'
    obtain ⟨h, rfl⟩ := π₀_mk_ihomObj₀Equiv_symm_surjective Y Z c
    obtain ⟨h', rfl⟩ := π₀_mk_ihomObj₀Equiv_symm_surjective Y Z c'
    rw [mapπ₀_pre_app_π₀_mk_ihomObj₀Equiv_symm, mapπ₀_pre_app_π₀_mk_ihomObj₀Equiv_symm,
      π₀_mk_ihomObj₀Equiv_symm_eq_iff] at hcc'
    exact (π₀_mk_ihomObj₀Equiv_symm_eq_iff _ _).2 ((H Z).2 h h' hcc')
  · intro c
    obtain ⟨g, rfl⟩ := π₀_mk_ihomObj₀Equiv_symm_surjective X Z c
    obtain ⟨h, hh⟩ := (H Z).1 g
    exact ⟨π₀.mk ((ihomObj₀Equiv Y Z).symm h), by
      rwa [mapπ₀_pre_app_π₀_mk_ihomObj₀Equiv_symm, π₀_mk_ihomObj₀Equiv_symm_eq_iff]⟩

namespace IsWeakHomotopyEquivalence

variable (f : X ⟶ Y)

/-- If `f : X ⟶ Y` is a weak homotopy equivalence, every map from `X` to a Kan complex is homotopic
to the composite of `f` with a map from `Y`. -/
lemma exists_homotopy [IsWeakHomotopyEquivalence f] [KanComplex Z] (g : X ⟶ Z) :
    ∃ h : Y ⟶ Z, Nonempty (Homotopy (f ≫ h) g) :=
  (((isWeakHomotopyEquivalence_iff_homotopy f).1 ‹_› Z).1 g)

/-- If `f : X ⟶ Y` is a weak homotopy equivalence, two maps from `Y` to a Kan complex are homotopic
as soon as their composites with `f` are. -/
lemma nonempty_homotopy [IsWeakHomotopyEquivalence f] [KanComplex Z] {h h' : Y ⟶ Z}
    (H : Nonempty (Homotopy (f ≫ h) (f ≫ h'))) : Nonempty (Homotopy h h') :=
  (((isWeakHomotopyEquivalence_iff_homotopy f).1 ‹_› Z).2 h h' H)

/-- Every isomorphism of simplicial sets is a weak homotopy equivalence. -/
instance of_isIso [IsIso f] : IsWeakHomotopyEquivalence f where
  bijective_mapπ₀_pre_app Z _ := by
    refine Function.bijective_iff_has_inverse.2
      ⟨mapπ₀ ((pre (inv f)).app Z), fun c ↦ ?_, fun c ↦ ?_⟩
    · rw [← Function.comp_apply (f := mapπ₀ _), ← mapπ₀_pre_app_comp, IsIso.inv_hom_id, pre_id,
        NatTrans.id_app, mapπ₀_id_apply]
    · rw [← Function.comp_apply (f := mapπ₀ _), ← mapπ₀_pre_app_comp, IsIso.hom_inv_id, pre_id,
        NatTrans.id_app, mapπ₀_id_apply]

/-- A composite of weak homotopy equivalences is a weak homotopy equivalence. -/
instance comp (g : Y ⟶ Z) [IsWeakHomotopyEquivalence f] [IsWeakHomotopyEquivalence g] :
    IsWeakHomotopyEquivalence (f ≫ g) where
  bijective_mapπ₀_pre_app W _ := by
    rw [mapπ₀_pre_app_comp]
    exact (bijective_mapπ₀_pre_app (f := f) W).comp (bijective_mapπ₀_pre_app W)

/-- If `f` and `f ≫ g` are weak homotopy equivalences, then so is `g`. -/
lemma of_precomp (g : Y ⟶ Z) [IsWeakHomotopyEquivalence f]
    [IsWeakHomotopyEquivalence (f ≫ g)] : IsWeakHomotopyEquivalence g where
  bijective_mapπ₀_pre_app W _ := by
    have h := bijective_mapπ₀_pre_app (f := f ≫ g) W
    rwa [mapπ₀_pre_app_comp, Function.Bijective.of_comp_iff' (bijective_mapπ₀_pre_app W)] at h

/-- If `g` and `f ≫ g` are weak homotopy equivalences, then so is `f`. -/
lemma of_postcomp (g : Y ⟶ Z) [IsWeakHomotopyEquivalence g]
    [IsWeakHomotopyEquivalence (f ≫ g)] : IsWeakHomotopyEquivalence f where
  bijective_mapπ₀_pre_app W _ := by
    have h := bijective_mapπ₀_pre_app (f := f ≫ g) W
    rwa [mapπ₀_pre_app_comp, Function.Bijective.of_comp_iff _ (bijective_mapπ₀_pre_app W)] at h

/-- A simplicial homotopy equivalence is a weak homotopy equivalence. -/
lemma of_homotopy {g : Y ⟶ X} (H₁ : Homotopy (f ≫ g) (𝟙 X)) (H₂ : Homotopy (g ≫ f) (𝟙 Y)) :
    IsWeakHomotopyEquivalence f := by
  rw [isWeakHomotopyEquivalence_iff_homotopy]
  refine fun Z _ ↦ ⟨fun φ ↦ ⟨g ≫ φ, ?_⟩, fun h h' ⟨K⟩ ↦ ?_⟩
  · have H := H₁.postcomp φ
    rw [Category.assoc, Category.id_comp] at H
    exact ⟨H⟩
  · rw [← π₀_mk_ihomObj₀Equiv_symm_eq_iff]
    have e₁ := (H₂.postcomp h).π₀_mk_ihomObj₀Equiv_symm_eq
    have e₂ := (K.precomp g).π₀_mk_ihomObj₀Equiv_symm_eq
    have e₃ := (H₂.postcomp h').π₀_mk_ihomObj₀Equiv_symm_eq
    simp only [Category.assoc, Category.id_comp] at e₁ e₂ e₃
    exact e₁.symm.trans (e₂.trans e₃)

/-- A weak homotopy equivalence with nonempty target has nonempty source, as maps into the empty
Kan complex detect. -/
lemma nonempty [IsWeakHomotopyEquivalence f] [Y.Nonempty] : X.Nonempty := by
  by_contra hX
  obtain ⟨h, -⟩ := exists_homotopy f
    ((isInitialOfNotNonempty hX).to ((Functor.const SimplexCategoryᵒᵖ).obj PEmpty))
  obtain ⟨y⟩ := ‹Y.Nonempty›
  exact (h.app _ y).elim

end IsWeakHomotopyEquivalence

/-- A map between Kan complexes is a weak homotopy equivalence exactly when it is a simplicial
homotopy equivalence. -/
lemma isWeakHomotopyEquivalence_iff_exists_homotopy_inverse [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) : IsWeakHomotopyEquivalence f ↔
      ∃ g : Y ⟶ X, Nonempty (Homotopy (f ≫ g) (𝟙 X)) ∧ Nonempty (Homotopy (g ≫ f) (𝟙 Y)) := by
  refine ⟨fun _ ↦ ?_, fun ⟨g, ⟨H₁⟩, ⟨H₂⟩⟩ ↦ .of_homotopy f H₁ H₂⟩
  obtain ⟨g, ⟨H⟩⟩ := IsWeakHomotopyEquivalence.exists_homotopy f (𝟙 X)
  refine ⟨g, ⟨H⟩, IsWeakHomotopyEquivalence.nonempty_homotopy f ?_⟩
  have H' := H.postcomp f
  rw [Category.assoc, Category.id_comp, ← Category.comp_id f] at H'
  exact ⟨H'⟩

/-- A simplicial set `K` is weakly contractible exactly when its map to `Δ[0]` is a weak homotopy
equivalence. -/
lemma isWeaklyContractible_iff_isWeakHomotopyEquivalence {K : SSet.{u}} (p : K ⟶ Δ[0]) :
    IsWeaklyContractible K ↔ IsWeakHomotopyEquivalence p := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ⟨fun Z _ ↦ ?_⟩⟩
  · rw [isWeakHomotopyEquivalence_iff_homotopy]
    refine fun Z _ ↦ ⟨fun g ↦ ?_, fun h h' ⟨H⟩ ↦ ?_⟩
    · obtain ⟨z, H⟩ := IsWeaklyContractible.exists_homotopy_const g
      exact ⟨const z, by rwa [comp_const]⟩
    · obtain ⟨x⟩ := IsWeaklyContractible.nonempty (K := K)
      have hx : (const x : Δ[0] ⟶ K) ≫ p = 𝟙 _ := stdSimplex.isTerminalObj₀.hom_ext _ _
      have H' := H.precomp (const x : Δ[0] ⟶ K)
      rw [← Category.assoc, ← Category.assoc, hx, Category.id_comp, Category.id_comp] at H'
      exact ⟨H'⟩
  · obtain ⟨x⟩ := IsWeakHomotopyEquivalence.nonempty p
    refine ⟨evalAt x Z, ⟨.ofEq (congrArg _ (constMaps_evalAt K x Z))⟩, ?_⟩
    -- Write `M = Fun(K, Z)`. Both `evalAt x Z ≫ constMaps K Z` and `𝟙 M` are adjoint to maps
    -- `K ⟶ Fun(M, Z)`: the evaluation map `E` and its precomposite with the constant map at `x`.
    let M := (ihom K).obj Z
    let E : K ⟶ (ihom M).obj Z := curry (lift (snd M K) (fst M K) ≫ (ihom.ev K).app Z)
    -- Since `p` is a weak homotopy equivalence, `E` is homotopic to a map through `Δ[0]`, which
    -- is unchanged by precomposition with the constant map at `x`.
    obtain ⟨H⟩ : Nonempty (Homotopy (const x ≫ E) E) := by
      obtain ⟨h, ⟨H⟩⟩ := IsWeakHomotopyEquivalence.exists_homotopy p E
      have hc : (const x : K ⟶ K) ≫ p = p := stdSimplex.isTerminalObj₀.hom_ext _ _
      have e := (H.precomp (const x : K ⟶ K)).π₀_mk_ihomObj₀Equiv_symm_eq
      rw [← Category.assoc, hc] at e
      exact (π₀_mk_ihomObj₀Equiv_symm_eq_iff _ _).1 (e.symm.trans H.π₀_mk_ihomObj₀Equiv_symm_eq)
    -- Transposing this homotopy across the swap `K ⊗ M ≅ M ⊗ K` gives the required homotopy.
    have H' := (H.uncurry.precomp (lift (snd K M) (fst K M))).curry
    have h₁ : curry (lift (snd K M) (fst K M) ≫ uncurry E) = 𝟙 M := by
      have hs : lift (snd K M) (fst K M) ≫ lift (snd M K) (fst M K) = 𝟙 _ := by
        ext : 1 <;> simp
      rw [uncurry_curry, ← Category.assoc, hs, Category.id_comp, ← uncurry_id_eq_ev,
        curry_uncurry]
    have h₂ : curry (lift (snd K M) (fst K M) ≫ uncurry (const x ≫ E)) =
        evalAt x Z ≫ constMaps K Z := by
      have hev : evalAt x Z = lift (const x) (𝟙 M) ≫ (ihom.ev K).app Z := by
        have h := curry_evalAt x (uncurry (𝟙 M))
        rwa [curry_uncurry, Category.id_comp, uncurry_id_eq_ev] at h
      have hs : lift (snd K M) (fst K M) ≫ M ◁ const x ≫ lift (snd M K) (fst M K) =
          snd K M ≫ lift (const x) (𝟙 M) := by
        ext : 1 <;> simp
      rw [evalAt_constMaps, uncurry_natural_left, uncurry_curry, hev, reassoc_of% hs]
    rw [h₁, h₂] at H'
    exact ⟨H'⟩

/-- The map from a weakly contractible simplicial set to `Δ[0]` is a weak homotopy equivalence. -/
instance {K : SSet.{u}} [IsWeaklyContractible K] (p : K ⟶ Δ[0]) :
    IsWeakHomotopyEquivalence p :=
  (isWeaklyContractible_iff_isWeakHomotopyEquivalence p).1 ‹_›

end SSet
