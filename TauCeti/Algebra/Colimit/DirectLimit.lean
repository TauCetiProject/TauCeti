/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Directed colimits of monoids and algebras

Basic API for Mathlib's generic `DirectLimit G f` of a directed system of monoids or groups `G i`
with monoid homomorphisms as transition maps, and of a directed system of `A`-algebras with
`A`-algebra transition maps.

Mathlib equips `DirectLimit G f` with its monoid and group structures and bundles the canonical
maps from the components as linear maps and ring homomorphisms. Here they are bundled as monoid
homomorphisms `TauCeti.DirectLimit.Monoid.of G f i : G i →* DirectLimit G f`, with the universal
property `TauCeti.DirectLimit.Monoid.lift`. The canonical map, its universal property, their
compatibility lemmas and `TauCeti.DirectLimit.Monoid.hom_ext` follow Mathlib's
`DirectLimit.Ring.of`, `DirectLimit.Ring.lift` and `DirectLimit.Ring.hom_ext` in
`Mathlib/Algebra/Colimit/DirectLimit.lean`, with monoid homomorphisms in place of ring
homomorphisms. Every element of the direct limit comes from some component, and the index set is
directed, so every finite subset of the direct limit lies in the image of a single component
(`TauCeti.DirectLimit.Monoid.exists_subset_range_of`). This is how properties defined by finitely
many elements at a time pass to direct limits.

## Main declarations

* `TauCeti.DirectLimit.Monoid.of`: the canonical map from a component, as a monoid homomorphism.
* `TauCeti.DirectLimit.Monoid.lift`: the universal property of the direct limit of monoids.
* `TauCeti.DirectLimit.Monoid.hom_ext`: monoid homomorphisms out of the direct limit agree when
  they agree on every component.
* `TauCeti.DirectLimit.Monoid.exists_subset_range_of`: every finite subset of the direct limit lies
  in the image of a single component.
* `TauCeti.DirectLimit.Algebra.of_comp_f`: the canonical maps into a direct limit of algebras are
  compatible with the transition maps. This is the algebra version of
  `Ring.DirectLimit.of_comp_f` in `TauCeti/Algebra/Colimit/Ring.lean`.
-/

public section

namespace TauCeti

namespace DirectLimit.Monoid

open _root_.DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
  {f : ∀ _ _ h, T h} [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι] [∀ i, MulOneClass (G i)]
  [∀ i j h, MonoidHomClass (T h) (G i) (G j)]

variable (G f) in
/-- The canonical map from a component to the direct limit, as a monoid homomorphism. -/
def of (i : ι) : G i →* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (one_def i).symm
  map_mul' x y := (mul_def i x y).symm

@[simp]
theorem of_apply (i : ι) (x : G i) : of G f i x = ⟦⟨i, x⟩⟧ := (rfl)

theorem of_f {i j : ι} (hij : i ≤ j) (x : G i) : of G f j (f i j hij x) = of G f i x :=
  .symm <| eq_of_le ..

variable {P : Type*} [MulOneClass P]

variable (G f) in
/-- The universal property of the direct limit of monoids: monoid homomorphisms from the components
which are compatible with the transition maps induce a monoid homomorphism out of the direct
limit. -/
-- `MonoidHom` is spelled out because the source dot-notation lint reads a `→*` result as a
-- function arrow taking an explicit `DirectLimit` argument, which `lift` does not have.
def lift (g : ∀ i, G i →* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    MonoidHom (DirectLimit G f) P where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  map_one' := lift_one _ _
  map_mul' := lift_mul _ _

variable (g : ∀ i, G i →* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp]
theorem lift_mk (i : ι) (x : G i) : lift G f g Hg ⟦⟨i, x⟩⟧ = g i x := (rfl)

theorem lift_of (i : ι) (x : G i) : lift G f g Hg (of G f i x) = g i x := (rfl)

@[simp]
theorem lift_comp_of (i : ι) : (lift G f g Hg).comp (of G f i) = g i :=
  MonoidHom.ext (lift_of g Hg i)

@[ext]
theorem hom_ext {g₁ g₂ : DirectLimit G f →* P}
    (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) : g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact DFunLike.congr_fun (h i) x

/-- Every finite subset of the direct limit of a directed system of monoids lies in the image of a
single component. -/
theorem exists_subset_range_of (s : Finset (DirectLimit G f)) :
    ∃ i, (s : Set (DirectLimit G f)) ⊆ Set.range (of G f i) := by
  refine Directed.exists_mem_subset_of_finset_subset_biUnion
    (directed_of_isDirected_le fun i j hij => ?_) fun z _ => ?_
  · -- The images increase along the index set, by compatibility with the transitions.
    rintro _ ⟨x, rfl⟩
    exact ⟨f i j hij x, of_f hij x⟩
  · obtain ⟨i, x, rfl⟩ := exists_eq_mk f z
    exact Set.mem_iUnion.2 ⟨i, x, rfl⟩

end DirectLimit.Monoid

namespace DirectLimit.Algebra

variable {A ι : Type*} [CommSemiring A] [Preorder ι] {B : ι → Type*} [∀ i, Semiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι]

open _root_.DirectLimit.Algebra

/-- The canonical maps into a direct limit of algebras are compatible with the transition
maps. -/
@[simp]
theorem of_comp_f {i j : ι} (hij : i ≤ j) : (of B f j).comp (f i j hij) = of B f i :=
  AlgHom.ext fun _ ↦ of_f _ _

end DirectLimit.Algebra

end TauCeti

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe u

/-- The direct limit of the tail above a chosen stage is its categorical ring colimit,
as an algebra over that stage. -/
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
      letI := hf
      Nonempty (DirectLimit (fun j : J ↦ F.obj j.val) f ≃ₐ[F.obj i₀]
        (colimit F : CommRingCat.{u})) := by
  classical
  have : Nonempty I := ⟨i₀⟩
  let S := F.obj i₀
  let R := colimit F
  let : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let T : J → Type u := fun j ↦ F.obj j.val
  let : ∀ j, CommRing (T j) := fun j ↦ inferInstance
  let : ∀ j, Algebra S (T j) := fun j ↦ (F.map (homOfLE j.property)).hom.toAlgebra
  let trans (i j : J) (h : i ≤ j) : T i →ₐ[S] T j :=
    { (F.map (homOfLE h)).hom with
      commutes' := fun a ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f a)
        (F.map_comp (homOfLE i.property) (homOfLE h)).symm }
  let incl (j : J) : T j →ₐ[S] R :=
    { (colimit.ι F j.val).hom with
      commutes' := fun a ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f a)
        (colimit.w F (homOfLE j.property)) }
  have : DirectedSystem T (trans · · ·) :=
    { map_self := fun i a ↦ by
        -- Expose the functor map defining this DirectLimit transition.
        change F.map (homOfLE (le_refl i.val)) a = a
        simp
      map_map := fun _ _ _ hij hjk a ↦ by
        exact (ConcreteCategory.congr_hom
          (F.map_comp (homOfLE hij) (homOfLE hjk)) a).symm }
  let g : DirectLimit T trans →ₐ[S] R :=
    DirectLimit.Algebra.lift T trans R incl fun i j h a ↦
      ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) a
  refine ⟨trans, inferInstance, ⟨AlgEquiv.ofBijective g ⟨?_, ?_⟩⟩⟩
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
    refine ⟨DirectLimit.Algebra.of T trans ⟨j, h₀j⟩ (F.map (homOfLE hij) a), ?_⟩
    -- Expose the lift on this representative for colimit naturality.
    change colimit.ι F j (F.map (homOfLE hij) a) = r
    exact (ConcreteCategory.congr_hom (colimit.w F (homOfLE hij)) a).trans ha


end CategoryTheory.Functor
