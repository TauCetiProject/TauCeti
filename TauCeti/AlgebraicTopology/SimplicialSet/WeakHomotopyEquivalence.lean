/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
(`SSet.ihomEdgeEquiv`), see `TauCeti/AlgebraicTopology/SimplicialSet/Homotopy.lean`. When `Z` is a
Kan complex, two maps therefore lie in the same connected component of `Fun(X, Z)` exactly when
they are homotopic (`SSet.π₀_mk_ihomObj₀Equiv_symm_eq_iff`), so that `f` is a weak homotopy
equivalence exactly when it induces a bijection on homotopy classes of maps into every Kan complex
(`SSet.isWeakHomotopyEquivalence_iff_homotopy`).

Weak homotopy equivalences contain the isomorphisms, are stable under composition and satisfy
two out of three. Every simplicial homotopy equivalence is a weak homotopy equivalence, and between
Kan complexes the converse holds. A simplicial set `K` is weakly contractible in the sense of
`SSet.IsWeaklyContractible` exactly when its map to `Δ[0]` is a weak homotopy equivalence, which is
Kerodon's definition of weak contractibility.

## Main declarations

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
  · have H := H₂.postcomp h
    have H' := H₂.postcomp h'
    rw [Category.assoc, Category.id_comp] at H H'
    obtain ⟨H⟩ := H.nonempty_symm
    obtain ⟨H⟩ := H.nonempty_trans (K.precomp g)
    exact H.nonempty_trans H'

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
    let E : K ⟶ (ihom M).obj Z := curry ((β_ M K).hom ≫ (ihom.ev K).app Z)
    -- Since `p` is a weak homotopy equivalence, `E` is homotopic to a map through `Δ[0]`, which
    -- is unchanged by precomposition with the constant map at `x`.
    obtain ⟨H⟩ : Nonempty (Homotopy (const x ≫ E) E) := by
      obtain ⟨h, ⟨H⟩⟩ := IsWeakHomotopyEquivalence.exists_homotopy p E
      have hc : (const x : K ⟶ K) ≫ p = p := stdSimplex.isTerminalObj₀.hom_ext _ _
      have H' := H.precomp (const x : K ⟶ K)
      rw [← Category.assoc, hc] at H'
      obtain ⟨H'⟩ := H'.nonempty_symm
      exact H'.nonempty_trans H
    -- Transposing this homotopy across the braiding `K ⊗ M ≅ M ⊗ K` gives the required homotopy.
    have H' := (H.uncurry.precomp (β_ K M).hom).curry
    have h₁ : curry ((β_ K M).hom ≫ uncurry E) = 𝟙 M := by
      rw [uncurry_curry, SymmetricCategory.symmetry_assoc, ← uncurry_id_eq_ev, curry_uncurry]
    have h₂ : curry ((β_ K M).hom ≫ uncurry (const x ≫ E)) = evalAt x Z ≫ constMaps K Z := by
      have hs : (β_ K M).hom ≫ M ◁ const x ≫ (β_ M K).hom = snd K M ≫ lift (const x) (𝟙 M) := by
        ext : 1 <;> simp
      rw [evalAt_constMaps, uncurry_natural_left, uncurry_curry, evalAt_eq, reassoc_of% hs]
    rw [h₁, h₂] at H'
    exact ⟨H'⟩

/-- The map from a weakly contractible simplicial set to `Δ[0]` is a weak homotopy equivalence. -/
instance {K : SSet.{u}} [IsWeaklyContractible K] (p : K ⟶ Δ[0]) :
    IsWeakHomotopyEquivalence p :=
  (isWeaklyContractible_iff_isWeakHomotopyEquivalence p).1 ‹_›

end SSet
