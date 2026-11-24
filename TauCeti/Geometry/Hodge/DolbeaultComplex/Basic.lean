/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Supported
public import TauCeti.Geometry.Hodge.Conjugation

/-!
# Real Dolbeault complexes

A real Dolbeault complex is a complex vector space `A` with a bigrading by types
`(r, s) ∈ ℤ × ℤ`, a conjugation carrying type `(r, s)` to type `(s, r)`, and two operators `∂`
and `∂bar` of bidegrees `(1, 0)` and `(0, 1)` which square to zero, anticommute and are exchanged by
the conjugation. The total differential `d = ∂ + ∂bar` then squares to zero and commutes with the
conjugation, so the real points form a real cochain complex whose complexification carries the
type decomposition. The complex-valued smooth forms on a complex manifold, with their type
decomposition and the operators `∂` and `∂bar`, are the motivating example; logarithmic forms along
a normal crossings divisor are another. No boundedness of the grading is assumed.

The bigrading is a family of complex subspaces `𝒜 : ℤ × ℤ → Submodule ℂ A`, and the results
that need the type components of a vector assume that it is an internal direct sum, as
`DirectSum.Decomposition 𝒜`. The Deligne complex of a real Dolbeault complex is built in
`TauCeti.Geometry.Hodge.DolbeaultComplex.Deligne.Basic` from the operators and type projections
whose interaction is recorded here.

## Main definitions

* `TauCeti.Hodge.DolbeaultComplex`: a real Dolbeault complex on a bigraded complex vector space.
* `TauCeti.Hodge.DolbeaultComplex.d`: its total differential `∂ + ∂bar`.
* `TauCeti.Hodge.DolbeaultComplex.Hom`: a morphism of real Dolbeault complexes, a complex-linear
  map preserving types and commuting with conjugation, `∂` and `∂bar`.

## Main results

* `TauCeti.Hodge.DolbeaultComplex.d_d`: the total differential squares to zero.
* `TauCeti.Hodge.DolbeaultComplex.conj_d`: the total differential commutes with conjugation.
* `TauCeti.Hodge.DolbeaultComplex.del_delBar_d`: `∂∂bar` kills the image of `d`.
* `TauCeti.Hodge.DolbeaultComplex.del_mem_iSup`, `TauCeti.Hodge.DolbeaultComplex.delBar_mem_iSup`
  and `TauCeti.Hodge.DolbeaultComplex.conj_mem_iSup`: the operators move sums of type pieces as
  their bidegrees prescribe, and so does `TauCeti.Hodge.DolbeaultComplex.d_mem_iSup`; in
  particular `d` raises the total degree by one
  (`TauCeti.Hodge.DolbeaultComplex.d_mem_iSup_degree`).
* `TauCeti.Hodge.DolbeaultComplex.conj_supportedProj`: conjugation carries the projection onto a
  set of types to the projection onto the set of exchanged types.
* `TauCeti.Hodge.DolbeaultComplex.supportedProj_d_supportedProj_eq_zero`: `π_S d π_T = 0` when
  `d` carries no type in `T` into `S`.
* `TauCeti.Hodge.DolbeaultComplex.twistProj_mem_iSup`: the projections to the real twists preserve
  every sum of type pieces stable under exchanging the two indices, and they commute with the total
  differential (`TauCeti.Hodge.DolbeaultComplex.d_twistProj`).

## References

* J. I. Burgos Gil, J. Kramer, U. Kühn, *Cohomological arithmetic Chow rings*, J. Inst. Math.
  Jussieu 6 (2007), §5.
-/

public section

namespace TauCeti.Hodge

universe u

variable {A : Type u} [AddCommGroup A] [Module ℂ A]

/-- A real Dolbeault complex on a complex vector space `A` bigraded by the types `𝒜 (r, s)`:
a conjugation carrying type `(r, s)` to type `(s, r)`, and complex-linear operators `∂` and `∂bar`
of bidegrees `(1, 0)` and `(0, 1)` which square to zero, anticommute and are exchanged by the
conjugation. -/
@[ext]
structure DolbeaultComplex (𝒜 : ℤ × ℤ → Submodule ℂ A) where
  /-- The conjugation, whose real points are the underlying real complex. -/
  conj : Conjugation A
  /-- Conjugation carries type `(r, s)` to type `(s, r)`. -/
  conj_mem : ∀ {r s : ℤ} {x : A}, x ∈ 𝒜 (r, s) → conj.toEquiv x ∈ 𝒜 (s, r)
  /-- The operator `∂`. -/
  del : A →ₗ[ℂ] A
  /-- The operator `∂bar`. -/
  delBar : A →ₗ[ℂ] A
  /-- `∂` has bidegree `(1, 0)`. -/
  del_mem : ∀ {r s : ℤ} {x : A}, x ∈ 𝒜 (r, s) → del x ∈ 𝒜 (r + 1, s)
  /-- `∂bar` has bidegree `(0, 1)`. -/
  delBar_mem : ∀ {r s : ℤ} {x : A}, x ∈ 𝒜 (r, s) → delBar x ∈ 𝒜 (r, s + 1)
  /-- `∂` squares to zero. -/
  del_del : ∀ x, del (del x) = 0
  /-- `∂bar` squares to zero. -/
  delBar_delBar : ∀ x, delBar (delBar x) = 0
  /-- `∂` and `∂bar` anticommute. -/
  del_delBar_add_delBar_del : ∀ x, del (delBar x) + delBar (del x) = 0
  /-- Conjugation exchanges `∂` and `∂bar`. -/
  conj_del : ∀ x, conj.toEquiv (del x) = delBar (conj.toEquiv x)

namespace DolbeaultComplex

variable {𝒜 : ℤ × ℤ → Submodule ℂ A} (X : DolbeaultComplex 𝒜)

/-- The total differential `d = ∂ + ∂bar` of a real Dolbeault complex. -/
def d : A →ₗ[ℂ] A := X.del + X.delBar

theorem d_apply (x : A) : X.d x = X.del x + X.delBar x :=
  (rfl)

/-- `∂bar∂ = -∂∂bar`. -/
theorem delBar_del (x : A) : X.delBar (X.del x) = -X.del (X.delBar x) :=
  eq_neg_of_add_eq_zero_right (X.del_delBar_add_delBar_del x)

/-- Conjugation exchanges `∂bar` and `∂`. -/
theorem conj_delBar (x : A) : X.conj.toEquiv (X.delBar x) = X.del (X.conj.toEquiv x) := by
  have h := congrArg X.conj.toEquiv (X.conj_del (X.conj.toEquiv x))
  rwa [X.conj.apply_apply, X.conj.apply_apply, eq_comm] at h

/-- Conjugation carries `∂∂bar` to `-∂∂bar`. -/
theorem conj_del_delBar (x : A) :
    X.conj.toEquiv (X.del (X.delBar x)) = -X.del (X.delBar (X.conj.toEquiv x)) := by
  rw [conj_del, conj_delBar, delBar_del]

/-- The total differential commutes with conjugation. -/
theorem conj_d (x : A) : X.conj.toEquiv (X.d x) = X.d (X.conj.toEquiv x) := by
  rw [d_apply, d_apply, map_add, conj_del, conj_delBar, add_comm]

/-- The total differential squares to zero. -/
@[simp]
theorem d_d (x : A) : X.d (X.d x) = 0 := by
  simp only [d_apply, map_add, del_del, delBar_delBar, delBar_del]
  abel

/-- `∂∂bar∂ = 0`. -/
@[simp]
theorem del_delBar_del (x : A) : X.del (X.delBar (X.del x)) = 0 := by
  rw [delBar_del, map_neg, del_del, neg_zero]

/-- `∂∂bar∂bar = 0`. -/
@[simp]
theorem del_delBar_delBar (x : A) : X.del (X.delBar (X.delBar x)) = 0 := by
  rw [delBar_delBar, map_zero]

/-- `∂∂bar` kills the image of the total differential. -/
@[simp]
theorem del_delBar_d (x : A) : X.del (X.delBar (X.d x)) = 0 := by
  simp [d_apply]

/-- The total differential kills the image of `∂∂bar`. -/
@[simp]
theorem d_del_delBar (x : A) : X.d (X.del (X.delBar x)) = 0 := by
  simp [d_apply, del_del, delBar_del]

/-- `∂` carries a sum of type pieces indexed by `S` into the sum indexed by `T` when `T` contains
the shift by `(1, 0)` of every type in `S`. -/
theorem del_mem_iSup {S T : Set (ℤ × ℤ)} (hST : ∀ i ∈ S, (i.1 + 1, i.2) ∈ T) {x : A}
    (hx : x ∈ ⨆ i : S, 𝒜 i) : X.del x ∈ ⨆ i : T, 𝒜 i :=
  TauCeti.DirectSum.map_mem_iSup X.del (fun _ _ ↦ X.del_mem) hST hx

/-- `∂bar` carries a sum of type pieces indexed by `S` into the sum indexed by `T` when `T` contains
the shift by `(0, 1)` of every type in `S`. -/
theorem delBar_mem_iSup {S T : Set (ℤ × ℤ)} (hST : ∀ i ∈ S, (i.1, i.2 + 1) ∈ T) {x : A}
    (hx : x ∈ ⨆ i : S, 𝒜 i) : X.delBar x ∈ ⨆ i : T, 𝒜 i :=
  TauCeti.DirectSum.map_mem_iSup X.delBar (fun _ _ ↦ X.delBar_mem) hST hx

/-- The total differential carries a sum of type pieces indexed by `S` into the sum indexed by
`T` when `T` contains both shifts of every type in `S`. -/
theorem d_mem_iSup {S T : Set (ℤ × ℤ)} (hST : ∀ i ∈ S, (i.1 + 1, i.2) ∈ T ∧ (i.1, i.2 + 1) ∈ T)
    {x : A} (hx : x ∈ ⨆ i : S, 𝒜 i) : X.d x ∈ ⨆ i : T, 𝒜 i := by
  rw [d_apply]
  exact add_mem (X.del_mem_iSup (fun i hi ↦ (hST i hi).1) hx)
    (X.delBar_mem_iSup (fun i hi ↦ (hST i hi).2) hx)

/-- The total differential carries the sum of the type pieces of total degree `n` into the sum of
those of total degree `n + 1`. -/
theorem d_mem_iSup_degree {n m : ℤ} (h : n + 1 = m) {x : A}
    (hx : x ∈ ⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n}, 𝒜 i) :
    X.d x ∈ ⨆ i : {i : ℤ × ℤ | i.1 + i.2 = m}, 𝒜 i :=
  X.d_mem_iSup (fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega) hx

/-- Conjugation carries a sum of type pieces indexed by `S` into the sum indexed by `T` when `T`
contains the exchange of every type in `S`. -/
theorem conj_mem_iSup {S T : Set (ℤ × ℤ)} (hST : ∀ i ∈ S, i.swap ∈ T) {x : A}
    (hx : x ∈ ⨆ i : S, 𝒜 i) : X.conj.toEquiv x ∈ ⨆ i : T, 𝒜 i :=
  TauCeti.DirectSum.map_mem_iSup X.conj.toEquiv (fun _ _ ↦ X.conj_mem) hST hx

/-- The projection to a real twist preserves a sum of type pieces indexed by a set stable under
exchanging the two indices. -/
theorem twistProj_mem_iSup {S : Set (ℤ × ℤ)} (hS : ∀ i ∈ S, i.swap ∈ S) (p : ℤ) {x : A}
    (hx : x ∈ ⨆ i : S, 𝒜 i) : X.conj.twistProj p x ∈ ⨆ i : S, 𝒜 i := by
  rw [Conjugation.twistProj_apply]
  exact Submodule.smul_of_tower_mem _ _ (add_mem hx (Submodule.smul_of_tower_mem _ _
    (X.conj_mem_iSup hS hx)))

/-- The total differential commutes with the projections to the real twists. -/
theorem d_twistProj (p : ℤ) (x : A) : X.d (X.conj.twistProj p x) = X.conj.twistProj p (X.d x) :=
  X.conj.map_twistProj X.conj (conj_d X) p x

section Decomposition

variable [DirectSum.Decomposition 𝒜]

open TauCeti.DirectSum

/-- Conjugation carries the projection onto the types in `S` to the projection onto the types in
`T`, when `T` is the set of exchanged types of `S`. -/
theorem conj_supportedProj {S T : Set (ℤ × ℤ)} (hST : ∀ i, i.swap ∈ T ↔ i ∈ S) (x : A) :
    X.conj.toEquiv (supportedProj 𝒜 S x) = supportedProj 𝒜 T (X.conj.toEquiv x) :=
  map_supportedProj X.conj.toEquiv (e := Prod.swap) (fun _ _ ↦ X.conj_mem) hST x

/-- The projection onto the types in `S` kills the total differential of the projection onto the
types in `T` when `d` carries no type in `T` into `S`. -/
theorem supportedProj_d_supportedProj_eq_zero {S T : Set (ℤ × ℤ)}
    (h : ∀ i ∈ T, (i.1 + 1, i.2) ∉ S ∧ (i.1, i.2 + 1) ∉ S) (y : A) :
    supportedProj 𝒜 S (X.d (supportedProj 𝒜 T y)) = 0 :=
  supportedProj_eq_zero_of_disjoint disjoint_compl_right
    (X.d_mem_iSup (T := Sᶜ) h (supportedProj_mem_iSup 𝒜 T y))

end Decomposition

section Hom

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ℬ : ℤ × ℤ → Submodule ℂ B}

/-- A morphism of real Dolbeault complexes: a complex-linear map preserving types and commuting
with conjugation, `∂` and `∂bar`. -/
structure Hom (X : DolbeaultComplex 𝒜) (Y : DolbeaultComplex ℬ) where
  /-- The underlying complex-linear map. -/
  toLinearMap : A →ₗ[ℂ] B
  /-- The map preserves types. -/
  map_mem' : ∀ {i : ℤ × ℤ} {x : A}, x ∈ 𝒜 i → toLinearMap x ∈ ℬ i
  /-- The map commutes with conjugation. -/
  map_conj' : ∀ x, toLinearMap (X.conj.toEquiv x) = Y.conj.toEquiv (toLinearMap x)
  /-- The map commutes with `∂`. -/
  map_del' : ∀ x, toLinearMap (X.del x) = Y.del (toLinearMap x)
  /-- The map commutes with `∂bar`. -/
  map_delBar' : ∀ x, toLinearMap (X.delBar x) = Y.delBar (toLinearMap x)

namespace Hom

variable {X} {Y : DolbeaultComplex ℬ}

instance : FunLike (Hom X Y) A B where
  coe f := f.toLinearMap
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (Hom X Y) ℂ A B where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

@[simp]
theorem coe_toLinearMap (f : Hom X Y) : ⇑f.toLinearMap = f :=
  (rfl)

/-- Morphisms of real Dolbeault complexes agreeing on every vector are equal. -/
@[ext]
theorem ext {f g : Hom X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

theorem map_mem (f : Hom X Y) {i : ℤ × ℤ} {x : A} (hx : x ∈ 𝒜 i) : f x ∈ ℬ i :=
  f.map_mem' hx

@[simp]
theorem map_conj (f : Hom X Y) (x : A) : f (X.conj.toEquiv x) = Y.conj.toEquiv (f x) :=
  f.map_conj' x

@[simp]
theorem map_del (f : Hom X Y) (x : A) : f (X.del x) = Y.del (f x) :=
  f.map_del' x

@[simp]
theorem map_delBar (f : Hom X Y) (x : A) : f (X.delBar x) = Y.delBar (f x) :=
  f.map_delBar' x

/-- A morphism of real Dolbeault complexes commutes with the total differentials. -/
@[simp]
theorem map_d (f : Hom X Y) (x : A) : f (X.d x) = Y.d (f x) := by
  rw [d_apply, d_apply, map_add, map_del, map_delBar]

/-- A morphism of real Dolbeault complexes carries the sum of the type pieces indexed by `S` into
the corresponding sum. -/
theorem map_mem_iSup (f : Hom X Y) {S : Set (ℤ × ℤ)} {x : A} (hx : x ∈ ⨆ i : S, 𝒜 i) :
    f x ∈ ⨆ i : S, ℬ i :=
  TauCeti.DirectSum.map_mem_iSup f (e := id) (fun _ _ ↦ f.map_mem) (fun _ ↦ id) hx

/-- A morphism of real Dolbeault complexes commutes with the projections onto a set of types. -/
theorem map_supportedProj [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]
    (f : Hom X Y) (S : Set (ℤ × ℤ)) (x : A) :
    f (TauCeti.DirectSum.supportedProj 𝒜 S x) = TauCeti.DirectSum.supportedProj ℬ S (f x) :=
  TauCeti.DirectSum.map_supportedProj f (ℳ := 𝒜) (𝒩 := ℬ) (e := id) (fun _ _ ↦ f.map_mem)
    (fun _ ↦ Iff.rfl) x

variable (X) in
/-- The identity morphism of a real Dolbeault complex. -/
def id : Hom X X where
  toLinearMap := LinearMap.id
  map_mem' hx := hx
  map_conj' _ := rfl
  map_del' _ := rfl
  map_delBar' _ := rfl

@[simp]
theorem id_toLinearMap : (Hom.id X).toLinearMap = LinearMap.id :=
  (rfl)

@[simp]
theorem id_apply (x : A) : Hom.id X x = x :=
  (rfl)

variable {C : Type*} [AddCommGroup C] [Module ℂ C] {𝒞 : ℤ × ℤ → Submodule ℂ C}
  {Z : DolbeaultComplex 𝒞}

/-- The composite of two morphisms of real Dolbeault complexes. -/
def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_mem' hx := g.map_mem (f.map_mem hx)
  map_conj' x := by simp only [LinearMap.comp_apply, coe_toLinearMap, map_conj]
  map_del' x := by simp only [LinearMap.comp_apply, coe_toLinearMap, map_del]
  map_delBar' x := by simp only [LinearMap.comp_apply, coe_toLinearMap, map_delBar]

@[simp]
theorem comp_toLinearMap (g : Hom Y Z) (f : Hom X Y) :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap :=
  (rfl)

@[simp]
theorem comp_apply (g : Hom Y Z) (f : Hom X Y) (x : A) : g.comp f x = g (f x) :=
  (rfl)

/-- Left identity law for morphisms of real Dolbeault complexes. -/
@[simp]
theorem id_comp (f : Hom X Y) : (Hom.id Y).comp f = f := by
  ext x
  rfl

/-- Right identity law for morphisms of real Dolbeault complexes. -/
@[simp]
theorem comp_id (f : Hom X Y) : f.comp (Hom.id X) = f := by
  ext x
  rfl

/-- Associativity of composition of morphisms of real Dolbeault complexes. -/
theorem comp_assoc {D : Type*} [AddCommGroup D] [Module ℂ D] {𝒟 : ℤ × ℤ → Submodule ℂ D}
    {W : DolbeaultComplex 𝒟} (h : Hom Z W) (g : Hom Y Z) (f : Hom X Y) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

end Hom

end Hom

end DolbeaultComplex

end TauCeti.Hodge
