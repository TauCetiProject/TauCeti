/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Marked.Limits
public import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Mapping simplicial sets of marked simplicial sets

For marked simplicial sets `X` and `Y` there are two simplicial sets of maps from `X` to `Y`:

* `Map♭(X, Y)`, whose `n`-simplices are the morphisms of marked simplicial sets
  `Δ[n]♭ × X ⟶ Y`;
* `Map♯(X, Y)`, whose `n`-simplices are the morphisms of marked simplicial sets
  `Δ[n]♯ × X ⟶ Y`.

Both have the morphisms `X ⟶ Y` as vertices. An edge of either is a homotopy
`h : Δ[1] × X ⟶ Y`. In `Map♭(X, Y)` it is only required that both ends of `h` preserve the
marked edges; in `Map♯(X, Y)` the edge `(a, e)` must be sent to a marked edge for every edge `a`
of `Δ[1]` and every marked edge `e` of `X`, so in particular each track `h(-, x)` of a vertex `x`
is marked. For a quasicategory `C` marked at its equivalences, `Map♭(X, C)` is a quasicategory
and `Map♯(X, C)` is its largest Kan complex (HTT Remark 3.1.3.1); for `X = K♭` the former is the
functor quasicategory `Fun(K, C)`. These are the mapping spaces of the marked models of
fibrations.

The two are related by the inclusion `Map♯(X, Y) ⟶ Map♭(X, Y)` induced by the identities
`Δ[n]♭ ⟶ Δ[n]♯`, which is a bijection on vertices.

## Main definitions

* `TauCeti.MarkedSSet.mapFlat X`: the functor `Y ↦ Map♭(X, Y)`.
* `TauCeti.MarkedSSet.mapSharp X`: the functor `Y ↦ Map♯(X, Y)`.
* `TauCeti.MarkedSSet.mapSharpToMapFlat X`: the inclusion `Map♯(X, -) ⟶ Map♭(X, -)`.

## Main results

* `TauCeti.MarkedSSet.mapFlat.obj₀Equiv`, `TauCeti.MarkedSSet.mapSharp.obj₀Equiv`: the vertices
  of both mapping simplicial sets are the morphisms `X ⟶ Y`.
* `TauCeti.MarkedSSet.mono_mapSharpToMapFlat_app`: `Map♯(X, Y)` is a simplicial subset of
  `Map♭(X, Y)`, with the same vertices (`TauCeti.MarkedSSet.mapFlat.obj₀Equiv_mapSharpToMapFlat`).

## References

* J. Lurie, *Higher Topos Theory*, §3.1.3, in particular Remark 3.1.3.1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial

universe u

namespace TauCeti

namespace MarkedSSet

/-- Every edge of `Δ[0]♭` is marked. -/
lemma mem_flat_stdSimplex₀_marked (e : Δ[0] _⦋1⦌) : e ∈ (flat.obj Δ[0] : MarkedSSet.{u}).marked :=
  ⟨SSet.stdSimplex.obj₀Equiv.symm 0, SSet.stdSimplex.objEquiv.injective (Subsingleton.elim _ _)⟩

/-- `Δ[0]♭` is a terminal marked simplicial set. -/
def isTerminalFlatStdSimplex₀ : IsTerminal (flat.obj Δ[0] : MarkedSSet.{u}) :=
  IsTerminal.ofUniqueHom
    (fun X ↦ ⟨SSet.stdSimplex.isTerminalObj₀.from X.toSSet, fun _ _ ↦
      mem_flat_stdSimplex₀_marked _⟩)
    (fun _ _ ↦ hom_ext SSet.stdSimplex.ext₀)

variable (X : MarkedSSet.{u})

/-- The functor `Y ↦ Map♭(X, Y)`: the `n`-simplices of `Map♭(X, Y)` are the morphisms of
marked simplicial sets `Δ[n]♭ × X ⟶ Y`. -/
@[expose]
def mapFlat : MarkedSSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} (SSet.stdSimplex ⋙ flat ⋙ tensorRight X)

/-- The functor `Y ↦ Map♯(X, Y)`: the `n`-simplices of `Map♯(X, Y)` are the morphisms of
marked simplicial sets `Δ[n]♯ × X ⟶ Y`. -/
@[expose]
def mapSharp : MarkedSSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} (SSet.stdSimplex ⋙ sharp ⋙ tensorRight X)

variable {X} {Y Y' : MarkedSSet.{u}}

namespace mapFlat

/-- The `n`-simplices of `Map♭(X, Y)` are the morphisms `Δ[n]♭ × X ⟶ Y`. -/
def objEquiv {n : ℕ} : ((mapFlat X).obj Y) _⦋n⦌ ≃ (flat.obj Δ[n] ⊗ X ⟶ Y) :=
  Equiv.ulift

/-- The simplicial operators of `Map♭(X, Y)` act by precomposition. -/
@[simp]
lemma objEquiv_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (φ : ((mapFlat X).obj Y) _⦋n⦌) :
    objEquiv (((mapFlat X).obj Y).map f.op φ) =
      flat.map (SSet.stdSimplex.map f) ▷ X ≫ objEquiv φ :=
  (rfl)

/-- The functoriality of `Map♭(X, -)` is by postcomposition. -/
@[simp]
lemma objEquiv_map_app {n : ℕ} (g : Y ⟶ Y') (φ : ((mapFlat X).obj Y) _⦋n⦌) :
    objEquiv (((mapFlat X).map g).app _ φ) = objEquiv φ ≫ g :=
  (rfl)

/-- The vertices of `Map♭(X, Y)` are the morphisms `X ⟶ Y`. -/
def obj₀Equiv : ((mapFlat X).obj Y) _⦋0⦌ ≃ (X ⟶ Y) :=
  objEquiv.trans ((whiskerRightIso (isTerminalFlatStdSimplex₀.uniqueUpToIso
    isTerminalTensorUnit) X ≪≫ λ_ X).homCongr (Iso.refl Y))

@[simp]
lemma obj₀Equiv_map_app (g : Y ⟶ Y') (φ : ((mapFlat X).obj Y) _⦋0⦌) :
    obj₀Equiv (((mapFlat X).map g).app _ φ) = obj₀Equiv φ ≫ g := by
  simp [obj₀Equiv]

end mapFlat

namespace mapSharp

/-- The `n`-simplices of `Map♯(X, Y)` are the morphisms `Δ[n]♯ × X ⟶ Y`. -/
def objEquiv {n : ℕ} : ((mapSharp X).obj Y) _⦋n⦌ ≃ (sharp.obj Δ[n] ⊗ X ⟶ Y) :=
  Equiv.ulift

/-- The simplicial operators of `Map♯(X, Y)` act by precomposition. -/
@[simp]
lemma objEquiv_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (φ : ((mapSharp X).obj Y) _⦋n⦌) :
    objEquiv (((mapSharp X).obj Y).map f.op φ) =
      sharp.map (SSet.stdSimplex.map f) ▷ X ≫ objEquiv φ :=
  (rfl)

/-- The functoriality of `Map♯(X, -)` is by postcomposition. -/
@[simp]
lemma objEquiv_map_app {n : ℕ} (g : Y ⟶ Y') (φ : ((mapSharp X).obj Y) _⦋n⦌) :
    objEquiv (((mapSharp X).map g).app _ φ) = objEquiv φ ≫ g :=
  (rfl)

/-- The vertices of `Map♯(X, Y)` are the morphisms `X ⟶ Y`. -/
def obj₀Equiv : ((mapSharp X).obj Y) _⦋0⦌ ≃ (X ⟶ Y) :=
  objEquiv.trans ((whiskerRightIso
    ((isTerminalSharpObj SSet.stdSimplex.isTerminalObj₀).uniqueUpToIso isTerminalTensorUnit) X ≪≫
      λ_ X).homCongr (Iso.refl Y))

@[simp]
lemma obj₀Equiv_map_app (g : Y ⟶ Y') (φ : ((mapSharp X).obj Y) _⦋0⦌) :
    obj₀Equiv (((mapSharp X).map g).app _ φ) = obj₀Equiv φ ≫ g := by
  simp [obj₀Equiv]

end mapSharp

variable (X) in
/-- The inclusion `Map♯(X, Y) ⟶ Map♭(X, Y)`, precomposing with the identities
`Δ[n]♭ × X ⟶ Δ[n]♯ × X`. -/
def mapSharpToMapFlat : mapSharp X ⟶ mapFlat X where
  app Y :=
    { app n := ↾fun (φ : ((mapSharp X).obj Y).obj n) ↦
        ULift.up (flatToSharp.app (SSet.stdSimplex.obj n.unop) ▷ X ≫ φ.down)
      naturality _ _ f := by
        ext φ
        exact ULift.ext (hom_ext rfl) }

@[simp]
lemma mapFlat.objEquiv_mapSharpToMapFlat {n : ℕ} (φ : ((mapSharp X).obj Y) _⦋n⦌) :
    mapFlat.objEquiv (((mapSharpToMapFlat X).app Y).app _ φ) =
      flatToSharp.app Δ[n] ▷ X ≫ mapSharp.objEquiv φ :=
  (rfl)

/-- The inclusion `Map♯(X, Y) ⟶ Map♭(X, Y)` is the identity on vertices. -/
@[simp]
lemma mapFlat.obj₀Equiv_mapSharpToMapFlat (φ : ((mapSharp X).obj Y) _⦋0⦌) :
    mapFlat.obj₀Equiv (((mapSharpToMapFlat X).app Y).app _ φ) = mapSharp.obj₀Equiv φ := by
  simp only [mapFlat.obj₀Equiv, mapSharp.obj₀Equiv, Equiv.trans_apply, Iso.homCongr_apply,
    mapFlat.objEquiv_mapSharpToMapFlat]
  simp only [Iso.trans_inv, whiskerRightIso_inv, Iso.refl_hom, Category.comp_id, Category.assoc,
    ← comp_whiskerRight_assoc]
  rw [(isTerminalSharpObj SSet.stdSimplex.isTerminalObj₀).hom_ext (_ ≫ flatToSharp.app Δ[0])]

/-- `Map♯(X, Y)` is a simplicial subset of `Map♭(X, Y)`. -/
instance mono_mapSharpToMapFlat_app : Mono ((mapSharpToMapFlat X).app Y) := by
  have (n : SimplexCategoryᵒᵖ) : Mono (((mapSharpToMapFlat X).app Y).app n) := by
    refine (mono_iff_injective _).2 fun φ ψ h ↦ ULift.ext (hom_ext ?_)
    ext m z
    -- Precomposition with `Δ[n]♭ × X ⟶ Δ[n]♯ × X`, the identity of `Δ[n] × X`, leaves the
    -- components of a morphism unchanged.
    exact congrArg (fun χ ↦ (ULift.down χ).hom.app m z) h
  exact NatTrans.mono_of_mono_app _

end MarkedSSet

end TauCeti
