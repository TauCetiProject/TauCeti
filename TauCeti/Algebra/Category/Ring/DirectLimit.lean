/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Directed colimits in `CommRingCat` as direct limits of algebras

Let `F : I ⥤ CommRingCat` be a diagram over a directed preorder `I`, and `i₀ : I` a stage. On the
tail `{i : I // i₀ ≤ i}` above `i₀`, each `F.obj i` is an `F.obj i₀`-algebra through
`F.map (homOfLE _)`, and so is `colimit F` through `colimit.ι F i₀`. The maps of `F` between the
stages of the tail are then `F.obj i₀`-algebra maps, and Mathlib's generic direct limit of this
directed system of algebras is the categorical colimit: there is an `F.obj i₀`-algebra
isomorphism from it to `colimit F` sending the canonical map from each stage to the colimit
injection. Results about direct limits of algebras, such as base change along them, thereby apply
to colimits of directed diagrams in `CommRingCat`.

## Main results

* `CategoryTheory.Functor.exists_directLimit_tail_algEquiv_colimit`: the direct limit of the tail
  above `i₀`, with the maps of `F` as transition maps, is isomorphic to `colimit F` as an
  `F.obj i₀`-algebra, compatibly with the maps from the stages.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe u

/-- The direct limit of the tail of `F` above the stage `i₀` is the colimit of `F`, as an
`F.obj i₀`-algebra: there are `F.obj i₀`-algebra transition maps on the stages `F.obj i` with
`i₀ ≤ i`, which are the maps of `F`, and an `F.obj i₀`-algebra isomorphism from their direct limit
to `colimit F` that sends the canonical map from each stage to the colimit injection. -/
theorem exists_directLimit_tail_algEquiv_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I) :
    let J := {i : I // i₀ ≤ i}
    letI : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
    letI : IsDirectedOrder J := ⟨fun i j ↦ by
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
      exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
    letI : ∀ j : J, Algebra (F.obj i₀) (F.obj j.val) :=
      fun j ↦ (F.map (homOfLE j.property)).hom.toAlgebra
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (colimit.ι F i₀).hom.toAlgebra
    ∃ (f : ∀ i j : J, i ≤ j → F.obj i.val →ₐ[F.obj i₀] F.obj j.val)
      (hf : DirectedSystem (fun j : J ↦ F.obj j.val) (f · · ·)),
      (∀ i j h x, f i j h x = (F.map (homOfLE h)).hom x) ∧
      letI := hf
      ∃ e : DirectLimit (fun j : J ↦ F.obj j.val) f ≃ₐ[F.obj i₀] (colimit F : CommRingCat.{u}),
        ∀ j x, e (DirectLimit.Algebra.of _ f j x) = (colimit.ι F j.val).hom x := by
  -- With `Nonempty I`, the directed preorder `I` is filtered, as the colimit-representative
  -- lemmas `Concrete.colimit_exists_rep` and `Concrete.colimit_exists_of_rep_eq` below need.
  have : Nonempty I := ⟨i₀⟩
  let : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) := (colimit.ι F i₀).hom.toAlgebra
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let : ∀ j : J, Algebra (F.obj i₀) (F.obj j.val) :=
    fun j ↦ (F.map (homOfLE j.property)).hom.toAlgebra
  let trans (i j : J) (h : i ≤ j) : F.obj i.val →ₐ[F.obj i₀] F.obj j.val :=
    { (F.map (homOfLE h)).hom with
      commutes' := fun a ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f a)
        (F.map_comp (homOfLE i.property) (homOfLE h)).symm }
  let incl (j : J) : F.obj j.val →ₐ[F.obj i₀] (colimit F : CommRingCat.{u}) :=
    { (colimit.ι F j.val).hom with
      commutes' := fun a ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f a)
        (colimit.w F (homOfLE j.property)) }
  have : DirectedSystem (fun j : J ↦ F.obj j.val) (trans · · ·) :=
    { map_self := fun i a ↦ by
        -- Expose the functor map defining this DirectLimit transition.
        change F.map (homOfLE (le_refl i.val)) a = a
        simp
      map_map := fun _ _ _ hij hjk a ↦
        (ConcreteCategory.congr_hom (F.map_comp (homOfLE hij) (homOfLE hjk)) a).symm }
  let g := DirectLimit.Algebra.lift _ trans _ incl fun i j h a ↦
    ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) a
  -- Both compatibilities hold by construction: `trans i j h` is `F.map (homOfLE h)` with an
  -- algebra-map proof attached, and `g (of j x) = incl j x` is `DirectLimit.Algebra.lift_of`.
  refine ⟨trans, inferInstance, fun _ _ _ _ ↦ rfl, AlgEquiv.ofBijective g ⟨?_, ?_⟩,
    fun _ _ ↦ rfl⟩
  · intro x y hxy
    obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk _ x
    obtain ⟨j, b, rfl⟩ := DirectLimit.exists_eq_mk _ y
    -- Expose the defining lift on representatives for the colimit equality criterion.
    change colimit.ι F i.val a = colimit.ι F j.val b at hxy
    obtain ⟨k, u, v, he⟩ := Concrete.colimit_exists_of_rep_eq F a b hxy
    exact Quotient.sound ⟨⟨k, i.property.trans (leOfHom u)⟩, leOfHom u, leOfHom v, he⟩
  · intro r
    obtain ⟨i, a, ha⟩ := Concrete.colimit_exists_rep F r
    obtain ⟨j, h₀j, hij⟩ := exists_ge_ge i₀ i
    refine ⟨DirectLimit.Algebra.of _ trans ⟨j, h₀j⟩ (F.map (homOfLE hij) a), ?_⟩
    -- Expose the lift on this representative for colimit naturality.
    change colimit.ι F j (F.map (homOfLE hij) a) = r
    exact (ConcreteCategory.congr_hom (colimit.w F (homOfLE hij)) a).trans ha

end CategoryTheory.Functor
