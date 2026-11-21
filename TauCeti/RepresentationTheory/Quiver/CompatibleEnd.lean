/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.Noetherian.Basic


/-!
# Compatible endomorphisms of a representation of a quiver

A representation `T` of a quiver `D` over a commutative ring `R` assigns an `R`-module to each
vertex and a linear map to each edge; this is a prefunctor `D ⥤q ModuleCat R`. In Nori's
construction of the universal abelian category attached to a representation of a diagram, a
*diagram* is a quiver with a distinguished identity edge at each vertex, with no composition
imposed; this is Mathlib's `ReflQuiver`, and a representation of a diagram is a
`CategoryTheory.ReflPrefunctor D (ModuleCat R)`, written `D ⥤rq ModuleCat R`, which sends every
distinguished identity edge to the identity. Everything below except the treatment of identity
edges applies to the underlying prefunctor.

For a subdiagram, given by a set `S` of vertices and a set `E` of edges, the algebra `End(T|S,E)`
consists of the families `(x_v)_{v ∈ S}` of endomorphisms `x_v` of `T v` that commute with `T f`
for every edge `f : a ⟶ b` of `E` with both endpoints in `S`, in the sense that
`T f ∘ x_a = x_b ∘ T f`. Edges of `E` with an endpoint outside `S` impose no condition. These
algebras, their restriction homomorphisms to smaller subdiagrams, and the finiteness of
`End(T|S,E)` for finite `S` are the input to the coalgebra `colim End(T|S,E)^∨` whose finite
comodules form Nori's diagram category.

The edge set may be infinite: the vertex set alone controls finiteness, since the edge conditions
cut out a submodule of the finite product `∏_{v ∈ S} End(T v)`. Distinguished identity edges and
edges represented by zero impose no condition, while forgetting other edges can enlarge the
algebra; at a single vertex the algebra is the centralizer of the loops of `E` there.

## Main definitions

* `Prefunctor.compatibleEnd T S E`: the subalgebra `End(T|S,E)` of
  `∀ v : S, Module.End R (T.obj v)`.
* `Prefunctor.compatibleEndRestrict T hS hE`: the restriction homomorphism
  `End(T|S,E) →ₐ[R] End(T|S',E')` for `S' ⊆ S` and `E' ⊆ E`.

## Main results

* `Prefunctor.mem_compatibleEnd_iff`: the defining commutation equations.
* `Prefunctor.compatibleEnd_union`, `Prefunctor.compatibleEnd_antitone`,
  `Prefunctor.compatibleEnd_empty`: dependence on the edge set.
* `Prefunctor.compatibleEnd_insert_of_forall`: an edge whose equation holds for every family
  imposes no condition; in particular so do zero edges
  (`Prefunctor.compatibleEnd_insert_of_map_eq_zero`), edges leaving the vertex set
  (`Prefunctor.compatibleEnd_insert_of_notMem`) and, for a representation of a diagram,
  distinguished identity edges (`CategoryTheory.ReflPrefunctor.compatibleEnd_insert_id`).
* `Prefunctor.mem_compatibleEnd_singleton_iff`: at a single vertex, the compatible
  endomorphisms are the centralizer of the loops of `E`.
* `Prefunctor.compatibleEndRestrict_id`, `Prefunctor.compatibleEndRestrict_comp`:
  functoriality of restriction.
* `Prefunctor.instFiniteCompatibleEnd`: over a Noetherian ring, with finite vertex
  modules and finitely many vertices, `End(T|S,E)` is a finite module; in particular it is
  finite-dimensional over a field.

## References

* A. Huber, S. Müller-Stach, *Periods and Nori motives*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 65, Springer (2017), §§7.1–7.2, Definitions 7.1.1 and 7.1.3.
* A. Huber, S. Müller-Stach, *On the relation between Nori motives and Kontsevich periods*,
  Appendix B (2014), for the version over a Noetherian ring.
-/

public section

universe w v u u'

namespace Prefunctor

variable {R : Type u'} [CommRing R] {D : Type u} [Quiver.{v} D]
variable (T : D ⥤q ModuleCat.{w} R)

/-- The algebra `End(T|S,E)` of compatible endomorphisms of a representation `T` of a quiver on
the subdiagram with vertex set `S` and edge set `E`: the families `(x_v)_{v ∈ S}` of
endomorphisms of the vertex modules with `T f ∘ x_a = x_b ∘ T f` for each edge `f : a ⟶ b` in
`E` whose endpoints both lie in `S`. -/
def compatibleEnd (S : Set D) (E : Set (Quiver.Total D)) :
    Subalgebra R (∀ v : S, Module.End R (T.obj v)) where
  carrier := {x | ∀ e ∈ E, ∀ (hl : e.left ∈ S) (hr : e.right ∈ S),
    (T.map e.hom).hom ∘ₗ x ⟨e.left, hl⟩ = x ⟨e.right, hr⟩ ∘ₗ (T.map e.hom).hom}
  mul_mem' {x y} hx hy e he hl hr := by
    simp only [Pi.mul_apply, Module.End.mul_eq_comp]
    rw [← LinearMap.comp_assoc, hx e he hl hr, LinearMap.comp_assoc, hy e he hl hr,
      LinearMap.comp_assoc]
  add_mem' {x y} hx hy e he hl hr := by
    simp only [Pi.add_apply, LinearMap.comp_add, LinearMap.add_comp, hx e he hl hr,
      hy e he hl hr]
  algebraMap_mem' r e _ hl hr := by
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      LinearMap.smul_comp, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]

variable {T}

/-- Membership in `End(T|S,E)` is the system of commutation equations along the edges of `E`
with both endpoints in `S`. -/
theorem mem_compatibleEnd_iff {S : Set D} {E : Set (Quiver.Total D)}
    {x : ∀ v : S, Module.End R (T.obj v)} :
    x ∈ T.compatibleEnd S E ↔ ∀ e ∈ E, ∀ (hl : e.left ∈ S) (hr : e.right ∈ S),
      (T.map e.hom).hom ∘ₗ x ⟨e.left, hl⟩ = x ⟨e.right, hr⟩ ∘ₗ (T.map e.hom).hom :=
  Iff.rfl

/-- The pointwise form of the commutation equation satisfied by a compatible endomorphism. -/
theorem map_apply_of_mem_compatibleEnd {S : Set D} {E : Set (Quiver.Total D)}
    {x : ∀ v : S, Module.End R (T.obj v)} (hx : x ∈ T.compatibleEnd S E) {e : Quiver.Total D}
    (he : e ∈ E) (hl : e.left ∈ S) (hr : e.right ∈ S) (m : T.obj e.left) :
    T.map e.hom (x ⟨e.left, hl⟩ m) = x ⟨e.right, hr⟩ (T.map e.hom m) :=
  LinearMap.congr_fun (hx e he hl hr) m

section Edges

variable (T) (S : Set D)

/-- Imposing the conditions of two edge sets is imposing those of their union. -/
theorem compatibleEnd_union (E E' : Set (Quiver.Total D)) :
    T.compatibleEnd S (E ∪ E') = T.compatibleEnd S E ⊓ T.compatibleEnd S E' := by
  ext x
  simp only [Algebra.mem_inf, mem_compatibleEnd_iff, Set.mem_union, or_imp, forall_and]

/-- More edges impose more conditions. -/
theorem compatibleEnd_antitone : Antitone (T.compatibleEnd S) :=
  fun _ _ hE _ hx e he ↦ hx e (hE he)

/-- With no edges, every family of endomorphisms is compatible. -/
@[simp]
theorem compatibleEnd_empty : T.compatibleEnd S ∅ = ⊤ :=
  eq_top_iff.2 fun _ _ _ he ↦ he.elim

/-- An edge whose commutation equation holds for every family of endomorphisms imposes no
condition. -/
theorem compatibleEnd_insert_of_forall {e : Quiver.Total D}
    (h : ∀ (x : ∀ v : S, Module.End R (T.obj v)) (hl : e.left ∈ S) (hr : e.right ∈ S),
      (T.map e.hom).hom ∘ₗ x ⟨e.left, hl⟩ = x ⟨e.right, hr⟩ ∘ₗ (T.map e.hom).hom)
    (E : Set (Quiver.Total D)) : T.compatibleEnd S (insert e E) = T.compatibleEnd S E := by
  refine le_antisymm (T.compatibleEnd_antitone S (Set.subset_insert _ _))
    fun x hx e' he' hl hr ↦ ?_
  obtain rfl | he' := he'
  · exact h x hl hr
  · exact hx e' he' hl hr

/-- An edge represented by the zero map imposes no condition. -/
theorem compatibleEnd_insert_of_map_eq_zero {e : Quiver.Total D} (he : T.map e.hom = 0)
    (E : Set (Quiver.Total D)) : T.compatibleEnd S (insert e E) = T.compatibleEnd S E :=
  T.compatibleEnd_insert_of_forall S (fun _ _ _ ↦ by simp [he]) E

/-- An edge with an endpoint outside the vertex set imposes no condition. -/
theorem compatibleEnd_insert_of_notMem {e : Quiver.Total D} (he : e.left ∉ S ∨ e.right ∉ S)
    (E : Set (Quiver.Total D)) : T.compatibleEnd S (insert e E) = T.compatibleEnd S E :=
  T.compatibleEnd_insert_of_forall S (fun _ hl hr ↦ (he.elim (· hl) (· hr)).elim) E

end Edges

/-- At a single vertex `v`, a family of endomorphisms is compatible exactly when its value at `v`
commutes with the maps representing the loops at `v` that belong to `E`. -/
theorem mem_compatibleEnd_singleton_iff {v : D} {E : Set (Quiver.Total D)}
    {x : ∀ w : ({v} : Set D), Module.End R (T.obj w)} :
    x ∈ T.compatibleEnd {v} E ↔
      x ⟨v, rfl⟩ ∈ Subalgebra.centralizer R
        {f | ∃ g : v ⟶ v, ⟨v, v, g⟩ ∈ E ∧ (T.map g).hom = f} := by
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · rintro hx _ ⟨g, hg, rfl⟩
    exact hx _ hg rfl rfl
  · rintro hx ⟨l, r, g⟩ he (rfl : l = v) (rfl : r = l)
    exact hx _ ⟨g, he, rfl⟩

section Restrict

variable (T)

/-- The restriction homomorphism `End(T|S,E) →ₐ[R] End(T|S',E')` to a subdiagram, forgetting the
components at vertices outside `S'`. -/
def compatibleEndRestrict {S S' : Set D} {E E' : Set (Quiver.Total D)} (hS : S' ⊆ S)
    (hE : E' ⊆ E) : T.compatibleEnd S E →ₐ[R] T.compatibleEnd S' E' where
  toFun x := ⟨fun v ↦ (x : ∀ v : S, Module.End R (T.obj v)) (Set.inclusion hS v),
    fun e he hl hr ↦ x.property e (hE he) (hS hl) (hS hr)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_compatibleEndRestrict_apply {S S' : Set D} {E E' : Set (Quiver.Total D)}
    (hS : S' ⊆ S) (hE : E' ⊆ E) (x : T.compatibleEnd S E) (v : S') :
    (T.compatibleEndRestrict hS hE x : ∀ v : S', Module.End R (T.obj v)) v =
      (x : ∀ v : S, Module.End R (T.obj v)) (Set.inclusion hS v) :=
  (rfl)

/-- Restriction to the same subdiagram is the identity. -/
@[simp]
theorem compatibleEndRestrict_id (S : Set D) (E : Set (Quiver.Total D)) :
    T.compatibleEndRestrict (subset_refl S) (subset_refl E) = AlgHom.id R _ :=
  (rfl)

/-- Restrictions compose. -/
@[simp]
theorem compatibleEndRestrict_comp {S S' S'' : Set D} {E E' E'' : Set (Quiver.Total D)}
    (hS : S' ⊆ S) (hE : E' ⊆ E) (hS' : S'' ⊆ S') (hE' : E'' ⊆ E') :
    (T.compatibleEndRestrict hS' hE').comp (T.compatibleEndRestrict hS hE) =
      T.compatibleEndRestrict (hS'.trans hS) (hE'.trans hE) :=
  (rfl)

end Restrict

/-- Over a Noetherian ring, the algebra of compatible endomorphisms on finitely many vertices with
finite vertex modules is a finite module, whatever the edge set. In particular it is
finite-dimensional over a field. -/
instance instFiniteCompatibleEnd [IsNoetherianRing R] {S : Set D} [Finite S]
    [∀ v : S, Module.Finite R (T.obj v)] (E : Set (Quiver.Total D)) :
    Module.Finite R (T.compatibleEnd S E) :=
  Module.IsNoetherian.finite R (Subalgebra.toSubmodule (T.compatibleEnd S E))

end Prefunctor

namespace CategoryTheory.ReflPrefunctor

variable {R : Type u'} [CommRing R] {D : Type u} [ReflQuiver.{v} D]
variable (T : D ⥤rq ModuleCat.{w} R) (S : Set D)

/-- For a representation of a diagram, a distinguished identity edge imposes no condition. -/
@[simp]
theorem compatibleEnd_insert_id (v : D) (E : Set (Quiver.Total D)) :
    T.compatibleEnd S (insert ⟨v, v, 𝟙rq v⟩ E) = T.compatibleEnd S E :=
  T.compatibleEnd_insert_of_forall S (fun _ _ _ ↦ by simp) E

end CategoryTheory.ReflPrefunctor
