/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Topology.Category.TopCat.Basic

import Mathlib.Data.Fintype.Sigma

/-!
# Fibres of morphisms in `TopCat`

The fibre `TopCat.Hom.fiber p b` of a morphism `p : E ⟶ B` over a point `b` is the preimage
`p ⁻¹' {b}` with the subspace topology, and `TopCat.Hom.fiberι p b` is its inclusion into `E`.
A commutative square from `p` to `p'`, such as a map of fibrations, induces maps between the
fibres (`CategoryTheory.CommSq.fiberMap`), functorially in horizontal composition of squares.

The names and the dot-notation shape follow Mathlib's scheme-theoretic fibres
`AlgebraicGeometry.Scheme.Hom.fiber` and `AlgebraicGeometry.Scheme.Hom.fiberι`.
-/

public section

open CategoryTheory

universe u

namespace TopCat.Hom

variable {E B : TopCat.{u}}

/-- The fibre `p ⁻¹' {b}` of a morphism `p : E ⟶ B` over a point `b`, with the subspace
topology. -/
abbrev fiber (p : E ⟶ B) (b : B) : TopCat.{u} := TopCat.of (p ⁻¹' {b})

/-- The inclusion of the fibre of `p` over `b` into `E`. -/
def fiberι (p : E ⟶ B) (b : B) : p.fiber b ⟶ E := TopCat.ofHom ⟨Subtype.val, by fun_prop⟩

@[simp]
lemma fiberι_apply (p : E ⟶ B) (b : B) (x : p.fiber b) : p.fiberι b x = x.1 := (rfl)

@[reassoc (attr := simp)]
lemma fiberι_comp (p : E ⟶ B) (b : B) : p.fiberι b ≫ p = TopCat.const b := by
  ext x
  exact x.2

/-- The composite of two maps with finite fibres has finite fibres. -/
theorem finite_fibers_comp {E B X : TopCat.{u}} (p : E ⟶ B) (q : B ⟶ X)
    (hfinp : ∀ b, Finite ↥(p ⁻¹' {b})) (hfinq : ∀ x, Finite ↥(q ⁻¹' {x})) :
    ∀ x, Finite ↥((p ≫ q) ⁻¹' {x}) := by
  intro x
  let fq : Fintype ↥(q ⁻¹' {x}) :=
    Classical.choice ((finite_iff_nonempty_fintype _).mp (hfinq x))
  let fp : ∀ b : ↥(q ⁻¹' {x}), Fintype ↥(p ⁻¹' {b.1}) := fun b =>
    Classical.choice ((finite_iff_nonempty_fintype _).mp (hfinp b.1))
  let fs : Fintype (Σ b : ↥(q ⁻¹' {x}), ↥(p ⁻¹' {b.1})) :=
    @Sigma.instFintype _ _ fp fq
  apply @Finite.of_injective _ _ (Fintype.finite fs)
    (fun e : ↥((p ≫ q) ⁻¹' {x}) =>
      (⟨⟨p e, by
          simpa only [Set.mem_preimage, Set.mem_singleton_iff,
            ConcreteCategory.comp_apply] using e.property⟩,
        ⟨e, by simp⟩⟩ : Σ b : ↥(q ⁻¹' {x}), ↥(p ⁻¹' {b.1})))
  intro e e' h
  apply Subtype.ext
  exact congrArg (fun z : Σ b : ↥(q ⁻¹' {x}), ↥(p ⁻¹' {b.1}) => (z.2 : E)) h

end TopCat.Hom

namespace CategoryTheory.CommSq

variable {E B E' B' E'' B'' : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B'} {p'' : E'' ⟶ B''}
  {f : E ⟶ E'} {g : B ⟶ B'} {f' : E' ⟶ E''} {g' : B' ⟶ B''}

/-- A map of fibrations, that is, a commutative square from `p` to `p'`, maps the fibre of `p`
over `b` to the fibre of `p'` over `g b`. -/
def fiberMap (sq : CommSq f p p' g) (b : B) : p.fiber b ⟶ p'.fiber (g b) :=
  TopCat.ofHom
    { toFun x := ⟨f x.1, by
        rw [Set.mem_preimage, Set.mem_singleton_iff, ← ConcreteCategory.comp_apply, sq.w,
          ConcreteCategory.comp_apply, x.2]⟩
      continuous_toFun := by fun_prop }

@[simp]
lemma fiberMap_apply_coe (sq : CommSq f p p' g) (b : B) (x : p.fiber b) :
    (sq.fiberMap b x : E') = f x.1 := (rfl)

@[reassoc (attr := simp)]
lemma fiberMap_comp_fiberι (sq : CommSq f p p' g) (b : B) :
    sq.fiberMap b ≫ p'.fiberι (g b) = p.fiberι b ≫ f := (rfl)

/-- The identity square induces the identity on fibres. -/
@[simp]
lemma fiberMap_id (sq : CommSq (𝟙 E) p p (𝟙 B)) (b : B) : sq.fiberMap b = 𝟙 _ := (rfl)

/-- The composite of the maps on fibres induced by two squares is the map on fibres induced by
their horizontal composite.  It is stated in this direction so that `simp` can use it: the
middle map `p'` cannot be recovered from the composite square, as for `eqToHom_trans`. -/
@[reassoc (attr := simp)]
lemma fiberMap_comp_fiberMap (sq : CommSq f p p' g) (sq' : CommSq f' p' p'' g') (b : B) :
    sq.fiberMap b ≫ sq'.fiberMap (g b) = (sq.horiz_comp sq').fiberMap b := (rfl)

end CategoryTheory.CommSq
