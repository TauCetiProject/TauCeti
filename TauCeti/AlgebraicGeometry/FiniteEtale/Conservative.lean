/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Exactness
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Conservativity of geometric fibre functors over a connected base

Let `x : Spec Ω ⟶ S` be a geometric point of a scheme `S`, with `Ω` separably closed. The
geometric fibre `FiniteEtaleScheme.fiber x` of a finite étale `S`-scheme `Z` is nonempty exactly
when the image of `x` lies in the image of `Z`. When `S` is connected, the image of a finite
étale morphism is open and closed, so it is either empty or all of `S`; hence a finite étale
`S`-scheme is empty exactly when its geometric fibre at `x` is.

From this we deduce that over a connected base the geometric fibre functor reflects
epimorphisms, monomorphisms and isomorphisms. This is the axiom (G6) for a fibre functor in the
sense of Lenstra, that is, the field `reflectsIsos` of Mathlib's
`CategoryTheory.PreGaloisCategory.FiberFunctor`.

## Main results

* `TauCeti.FiniteEtaleScheme.nonempty_fiber_obj_iff_range_subset_range`: the geometric fibre
  of `Z` at `x` is nonempty if and only if the image of `x` lies in the image of `Z`.
* `TauCeti.FiniteEtaleScheme.nonempty_fiber_obj_iff_nonempty`: over a connected base, the
  geometric fibre of `Z` is nonempty if and only if `Z` is nonempty.
* Over a connected base, `FiniteEtaleScheme.fiber x` reflects epimorphisms and monomorphisms.
  As finite étale schemes form a balanced category, it then reflects isomorphisms by Mathlib's
  `CategoryTheory.Functor.reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms`.

For epimorphisms, the complement of the image of `f : X ⟶ Y` is open and closed in `Y`, hence a
finite étale `S`-scheme. A point of its geometric fibre would lift through `f` by surjectivity
on fibres, which is impossible, so the complement is empty. For monomorphisms we apply this to
the diagonal of `f`, which is a split monomorphism, hence an isomorphism once it is an
epimorphism.

## References

* H. W. Lenstra, *Galois theory for schemes*, Definition 3.1 and Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The geometric fibre of a finite étale `S`-scheme `Z` at `x : Spec Ω ⟶ S` is nonempty if and
only if the image of `x` lies in the image of `Z`. -/
theorem nonempty_fiber_obj_iff_range_subset_range (x : Spec (.of Ω) ⟶ S)
    (Z : FiniteEtaleScheme S) :
    Nonempty ((fiber x).obj Z) ↔ Set.range x ⊆ Set.range Z.obj.hom := by
  constructor
  · rintro ⟨y⟩ _ ⟨p, rfl⟩
    let g := (fiberCompInclIso x).hom.app Z y
    exact ⟨g.left p, by rw [← Scheme.Hom.comp_apply]; exact congrArg (· p) (Over.w g)⟩
  · intro h
    obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
    obtain ⟨z, hz⟩ := h ⟨p, rfl⟩
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback z p hz
    -- The base change `W` of `Z` to `Spec Ω` has the point `w`. If its finite set were empty,
    -- `W` would be initial, hence empty, as the classification is an equivalence.
    by_contra hW
    have hi : IsInitial ((pullback x).obj Z) :=
      (IsInitial.isInitialIffObj (equivOfIsSepClosed Ω).functor _).symm
        ((Concrete.initial_iff_empty_of_preserves_of_reflects _).mpr
          (not_nonempty_iff.mp hW)).some
    have : IsEmpty ((pullback x).obj Z).obj.left := isInitial_iff_isEmpty.mp
      ⟨hi.isInitialObj ((finiteEtaleSchemeProperty (Spec (.of Ω))).ι ⋙ Over.forget _) _⟩
    exact this.false w

/-- Over a connected base `S`, a finite étale `S`-scheme is nonempty if and only if its
geometric fibre at a geometric point `x` is nonempty: its image is open and closed in `S`. -/
theorem nonempty_fiber_obj_iff_nonempty [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S)
    (Z : FiniteEtaleScheme S) : Nonempty ((fiber x).obj Z) ↔ Nonempty Z.obj.left := by
  rw [nonempty_fiber_obj_iff_range_subset_range]
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  refine ⟨fun h ↦ ⟨(h ⟨p, rfl⟩).choose⟩, fun ⟨z⟩ ↦ ?_⟩
  have : IsClopen (Set.range Z.obj.hom) :=
    ⟨Z.obj.hom.isClosedMap.isClosed_range, Z.obj.hom.isOpenMap.isOpen_range⟩
  rw [this.eq_univ ⟨_, z, rfl⟩]
  exact Set.subset_univ _

/-- Over a connected base, a geometric fibre functor reflects epimorphisms: if `f` is surjective
on geometric fibres, the complement of its image is a finite étale scheme with empty geometric
fibre, hence empty. -/
instance [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S) : (fiber x).ReflectsEpimorphisms where
  reflects {X Y} f hf := by
    rw [epi_iff_surjective]
    let U : Y.obj.left.Opens :=
      ⟨(Set.range f.hom.left)ᶜ, f.hom.left.isClosedMap.isClosed_range.isOpen_compl⟩
    have hU : IsClosed (U : Set Y.obj.left) := f.hom.left.isOpenMap.isOpen_range.isClosed_compl
    let v := clopenSubschemeι U hU
    refine ⟨fun y ↦ by_contra fun hy ↦ ?_⟩
    -- The complement `U` of the image contains `y`, so its geometric fibre has a point `a`, whose
    -- image in the fibre of `Y` comes from a point `b` of the fibre of `X`.
    obtain ⟨q, -⟩ : y ∈ Set.range v.hom.left := by
      rw [range_clopenSubschemeι_hom_left]
      exact hy
    obtain ⟨a⟩ := (nonempty_fiber_obj_iff_nonempty x (clopenSubscheme U hU)).mpr ⟨q⟩
    obtain ⟨b, hb⟩ := surjective_of_epi (FintypeCat.incl.map ((fiber x).map f)) ((fiber x).map v a)
    -- The corresponding lifts of `x` to `X` and to `U` agree in `Y`. Here `hb` is stated for
    -- `FintypeCat.incl.map ((fiber x).map f)`, which is `(fiber x ⋙ FintypeCat.incl).map f`.
    have h₁ := NatTrans.naturality_apply (fiberCompInclIso x).hom f b
    have h₂ := NatTrans.naturality_apply (fiberCompInclIso x).hom v a
    have h : (fiberCompInclIso x).hom.app X b ≫ f.hom =
        (fiberCompInclIso x).hom.app _ a ≫ v.hom := by
      simpa using h₁.symm.trans ((congrArg ((fiberCompInclIso x).hom.app Y) hb).trans h₂)
    obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
    have hp := congrArg (fun g : Over.mk x ⟶ Y.obj ↦ g.left p) h
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at hp
    have hv : v.hom.left (((fiberCompInclIso x).hom.app _ a).left p) ∈ (U : Set Y.obj.left) :=
      range_clopenSubschemeι_hom_left U hU ▸ Set.mem_range_self _
    exact hv ⟨_, hp⟩

/-- Over a connected base, a geometric fibre functor reflects monomorphisms: if `f` is injective
on geometric fibres, its diagonal is an epimorphism on fibres, hence an epimorphism, and a split
monomorphism. -/
instance [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S) : (fiber x).ReflectsMonomorphisms where
  reflects {X Y} f hf := by
    -- Adapted from Mathlib's `ReflectsMonomorphisms` instance for
    -- `CategoryTheory.PreGaloisCategory.FiberFunctor` in
    -- `Mathlib/CategoryTheory/Galois/Basic.lean`, which uses that fibre functors reflect
    -- isomorphisms; here we only know that `fiber x` reflects epimorphisms.
    have : IsIso ((fiber x).map (pullback.fst f f)) := by
      rw [← PreservesPullback.iso_hom_fst]
      have := isIso_fst_of_mono ((fiber x).map f)
      infer_instance
    have : IsIso ((fiber x).map (pullback.diagonal f)) := isIso_of_comp_hom_eq_id _ (by
      rw [← Functor.map_comp, pullback.diagonal_fst, CategoryTheory.Functor.map_id])
    have : Epi (pullback.diagonal f) := (fiber x).epi_of_epi_map inferInstance
    have : IsIso (pullback.diagonal f) := isIso_of_epi_of_isSplitMono _
    exact (pullback.isIso_diagonal_iff f).mp this

end TauCeti.FiniteEtaleScheme
