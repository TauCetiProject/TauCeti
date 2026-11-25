/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Center.Linear
public import TauCeti.RepresentationTheory.OfMulAction.CosetLift
public import TauCeti.RepresentationTheory.Smooth.Category

/-!
# The centre of the category of smooth representations

For a commutative ring `A` and a topological group `G`, the *smooth centre*
`TauCeti.SmoothCenter A G` is the centre `CatCenter (SmoothRep A G)` of the category of smooth
representations: the endomorphisms `z` of the identity functor, a family of intertwining maps
`z_V : V → V` commuting with every morphism. It is a commutative ring, written `Z(G, A)`, and an
`A`-algebra through the scalar endomorphisms `a ↦ (v ↦ a • v)`, as is the centre of any linear
category (`TauCeti.CategoryTheory.Center.Linear`). Mathlib's `CatCenter.app`,
`CatCenter.naturality` and `CatCenter.ext` give evaluation, commutation with morphisms and equality
tested on every object (here `TauCeti.SmoothCenter.ext`, on every vector), and Mathlib's action of
`CatCenter C` on morphisms (`CatCenter.smul_eq`, `CatCenter.smul_eq'`) is the action of `Z(G, A)`
on `Hom_G(V, W)`, compatible from both sides.

An element of `Z(G, A)` restricts to subrepresentations and passes to quotients
(`TauCeti.SmoothCenter.app_subtype`, `TauCeti.SmoothCenter.app_mkQ`). It is determined by its
values on the permutation representations `A[G ⧸ U]` for `U` open
(`TauCeti.SmoothCenter.ext_of_ofMulAction_quotient`), or, for locally profinite `G`, compact open
(`TauCeti.SmoothCenter.ext_of_ofMulAction_quotient_isCompact`): a vector `v` fixed by `U` is the
image of the coset `U` under the intertwining map `A[G ⧸ U] → V`, `g U ↦ ρ g v`. Both come from
`TauCeti.SmoothCenter.ext_of_ofMulAction_quotient_of_exists_le_stabilizer`. On a `G`-invariant
vector, and so on every trivial representation, `z` acts by a scalar `scalar z`
(`TauCeti.SmoothCenter.app_apply_of_forall_eq`, `TauCeti.SmoothCenter.app_trivial_apply`), and
`scalar` is an `A`-algebra homomorphism `Z(G, A) → A`. For a trivial group the smooth centre is
`A` (`TauCeti.SmoothCenter.algEquivOfSubsingleton`).

## Main definitions

* `TauCeti.SmoothCenter A G`: the centre of the category `SmoothRep A G`, a commutative
  `A`-algebra.
* `TauCeti.SmoothCenter.scalar`: the `A`-algebra homomorphism sending `z` to the scalar by which
  it acts on every trivial representation.
* `TauCeti.SmoothCenter.algEquivOfSubsingleton`: for a trivial group, `A ≃ₐ[A] Z(G, A)`.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, 1987
  manuscript, §1.8, p. 8 (the centre and its action on morphisms and extensions).
-/

public section

open CategoryTheory Representation

universe w u v

namespace TauCeti

variable (A : Type u) [CommRing A] (G : Type v) [Group G] [TopologicalSpace G]

/-- The **smooth centre** `Z(G, A)`: the centre `CatCenter (SmoothRep A G)` of the category of
smooth representations, the ring of natural endomorphisms of its identity functor. -/
abbrev SmoothCenter : Type _ :=
  CatCenter (SmoothRep.{w} A G)

namespace SmoothCenter

variable {A G}

/-- The image of `a : A` in the smooth centre acts on every smooth representation by `a`. -/
@[simp] lemma algebraMap_app_hom_hom_apply (a : A) (V : SmoothRep.{w} A G) (v : V.obj) :
    ((algebraMap A (SmoothCenter.{w} A G) a).app V).hom.hom v = a • v :=
  (rfl)

/-- Two elements of the smooth centre are equal if they act alike on every vector of every smooth
representation. -/
@[ext] lemma ext {z z' : SmoothCenter.{w} A G}
    (h : ∀ (V : SmoothRep.{w} A G) (v : V.obj), (z.app V).hom.hom v = (z'.app V).hom.hom v) :
    z = z' :=
  CatCenter.ext _ _ fun V ↦ ObjectProperty.hom_ext _ <| Rep.hom_ext <|
    IntertwiningMap.ext <| LinearMap.ext (h V)

/-- **The centre restricts to subrepresentations**: on a subrepresentation `W` of a smooth
representation `V`, an element `z` of the smooth centre acts as it acts on `V`. -/
lemma app_subtype (z : SmoothCenter.{w} A G) {V : SmoothRep.{w} A G}
    (W : Subrepresentation V.obj.ρ) (x : W.toSubmodule) :
    ((z.app (SmoothRep.of W.toRepresentation)).hom.hom x : V.obj) = (z.app V).hom.hom x := by
  have := congr($(z.naturality (X := SmoothRep.of W.toRepresentation) (Y := V)
    (ObjectProperty.homMk (Rep.ofHom W.subtype))).hom.hom x)
  simpa using this.symm

variable [SeparatelyContinuousMul G] in
/-- **The centre passes to quotients**: on the quotient of a smooth representation `V` by a
subrepresentation `W`, an element `z` of the smooth centre acts on the class of `v` as the class
of `z_V v`. -/
lemma app_mkQ (z : SmoothCenter.{w} A G) {V : SmoothRep.{w} A G}
    (W : Subrepresentation V.obj.ρ) (v : V.obj) :
    (z.app (SmoothRep.of W.quotient)).hom.hom (W.toSubmodule.mkQ v) =
      W.toSubmodule.mkQ ((z.app V).hom.hom v) := by
  have := congr($(z.naturality (X := V) (Y := SmoothRep.of W.quotient)
    (ObjectProperty.homMk (Rep.ofHom (W.toSubmodule.mkQ.intertwiningMap_of_isIntertwiningMap _ _
      fun _ _ ↦ rfl)))).hom.hom v)
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom] at this
  exact this

section Generators

/-! ### Generators: the permutation representations `A[G ⧸ U]`

The permutation representations `A[G ⧸ U]` live in `Type (max u v)`, so the statements of this
section are about `SmoothCenter.{max u v} A G`. -/

variable [SeparatelyContinuousMul G]

/-- The value of `z` at a vector `v` fixed by an open subgroup `U` is the image of `z` applied to
the coset `U` of `A[G ⧸ U]` under the intertwining map `g U ↦ ρ g v`. -/
lemma app_apply_eq_cosetLift (z : SmoothCenter.{max u v} A G) (V : SmoothRep.{max u v} A G)
    (U : OpenSubgroup G) {v : V.obj} (hv : (U : Subgroup G) ≤ V.obj.ρ.stabilizer v) :
    (z.app V).hom.hom v = V.obj.ρ.cosetLift U v hv
      ((z.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G))))).hom.hom
        (MonoidAlgebra.single ((1 : G) : G ⧸ (U : Subgroup G)) 1)) := by
  have := congr($(z.naturality (X := SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G))))
    (Y := V) (ObjectProperty.homMk (Rep.ofHom (V.obj.ρ.cosetLift U v hv)))).hom.hom
      (MonoidAlgebra.single ((1 : G) : G ⧸ (U : Subgroup G)) 1))
  simpa using this

/-- **Permutation representations detect the smooth centre**, relative to a class `P` of open
subgroups such that every vector of every smooth representation is fixed by some `U` in `P`: two
elements of `Z(G, A)` that agree on `A[G ⧸ U]` for every `U` in `P` are equal. -/
lemma ext_of_ofMulAction_quotient_of_exists_le_stabilizer (P : OpenSubgroup G → Prop)
    (hP : ∀ (V : SmoothRep.{max u v} A G) (v : V.obj),
      ∃ U : OpenSubgroup G, P U ∧ (U : Subgroup G) ≤ V.obj.ρ.stabilizer v)
    {z z' : SmoothCenter.{max u v} A G}
    (h : ∀ U : OpenSubgroup G, P U →
      z.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G)))) =
        z'.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G))))) :
    z = z' := by
  ext V v
  obtain ⟨U, hPU, hU⟩ := hP V v
  rw [app_apply_eq_cosetLift z V U hU, app_apply_eq_cosetLift z' V U hU, h U hPU]

/-- **The permutation representations `A[G ⧸ U]` detect the smooth centre**: two elements of
`Z(G, A)` that agree on `A[G ⧸ U]` for every open subgroup `U` are equal. -/
lemma ext_of_ofMulAction_quotient {z z' : SmoothCenter.{max u v} A G}
    (h : ∀ U : OpenSubgroup G, z.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G)))) =
      z'.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G))))) :
    z = z' :=
  ext_of_ofMulAction_quotient_of_exists_le_stabilizer (fun _ ↦ True)
    (fun V v ↦ ⟨⟨V.obj.ρ.stabilizer v, IsSmooth.isOpen_stabilizer v⟩, trivial, le_rfl⟩)
    fun U _ ↦ h U

/-- The scalar by which an element `z` of the smooth centre acts on every trivial representation
(`app_trivial_apply`), read off as the coefficient of `z` applied to the basis vector of the
permutation representation `A[G ⧸ G]` on the single coset of `G`. It is an `A`-algebra
homomorphism `Z(G, A) → A`. -/
noncomputable def scalar : SmoothCenter.{max u v} A G →ₐ[A] A where
  toFun z :=
    (z.app (SmoothRep.of (ofMulAction A G (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))))).hom.hom
    (MonoidAlgebra.single ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) 1) |>.coeff
      ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))
  map_one' := by simp
  map_mul' z z' := by
    dsimp only
    set X := SmoothRep.of (ofMulAction A G (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)))
    set q : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G) :=
      ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))
    -- `A[G ⧸ G]` is one-dimensional, so `z` sends its basis vector to a multiple of it.
    have hz : (z.app X).hom.hom (.single q 1) =
        .single q (((z.app X).hom.hom (.single q 1)).coeff q) := by
      have : Subsingleton (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) :=
        QuotientGroup.subsingleton_quotient_top
      let : One (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) := ⟨(1 : G)⟩
      exact ((MonoidAlgebra.uniqueLinearEquiv A _).symm_apply_apply _).symm
    set c := ((z.app X).hom.hom (.single q 1)).coeff q
    rw [CatCenter.mul_app, ObjectProperty.FullSubcategory.comp_hom, Rep.hom_comp,
      IntertwiningMap.comp_apply, hz, ← mul_one c, ← MonoidAlgebra.smul_single', map_smul]
    simp
  map_zero' := by simp
  map_add' _ _ := by
    dsimp only
    exact DFunLike.congr_fun (MonoidAlgebra.coeff_add _ _) _
  commutes' a := by
    dsimp only
    rw [algebraMap_app_hom_hom_apply]
    simp

/-- An element `z` of the smooth centre sends the basis vector of `A[G ⧸ G]` to `scalar z`
times it. -/
lemma app_single_one_top (z : SmoothCenter.{max u v} A G) :
    (z.app (SmoothRep.of (ofMulAction A G (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))))).hom.hom
        (MonoidAlgebra.single ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) 1) =
      MonoidAlgebra.single ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) (scalar z) := by
  have : Subsingleton (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) :=
    QuotientGroup.subsingleton_quotient_top
  let : One (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) := ⟨(1 : G)⟩
  exact ((MonoidAlgebra.uniqueLinearEquiv A _).symm_apply_apply _).symm

/-- **The smooth centre acts on invariant vectors by a scalar**: on a `G`-invariant vector `v`,
an element `z` of `Z(G, A)` acts as the scalar `scalar z`. -/
lemma app_apply_of_forall_eq (z : SmoothCenter.{max u v} A G) (V : SmoothRep.{max u v} A G)
    {v : V.obj} (hv : ∀ g, V.obj.ρ g v = v) :
    (z.app V).hom.hom v = scalar z • v := by
  have hv' : ((⊤ : OpenSubgroup G) : Subgroup G) ≤ V.obj.ρ.stabilizer v := fun g _ ↦ by
    rw [mem_stabilizer]
    exact hv g
  rw [app_apply_eq_cosetLift z V ⊤ hv', app_single_one_top, cosetLift_single, map_one,
    one_apply_eq_self]

/-- **The smooth centre acts on a trivial representation by a scalar**: on a trivial
representation `M`, an element `z` of `Z(G, A)` acts as the scalar `scalar z`. -/
lemma app_trivial_apply (z : SmoothCenter.{max u v} A G) (M : Type (max u v)) [AddCommGroup M]
    [Module A M] (m : M) :
    (z.app (SmoothRep.of (trivial A G M))).hom.hom m = scalar z • m :=
  app_apply_of_forall_eq z _ fun _ ↦ rfl

variable (A G) in
/-- **The smooth centre of a trivial group is the coefficient ring**: for a group with one
element, `A → Z(G, A)` is an isomorphism, with inverse `scalar`, since every vector is invariant. -/
noncomputable def algEquivOfSubsingleton [Subsingleton G] : A ≃ₐ[A] SmoothCenter.{max u v} A G :=
  AlgEquiv.ofAlgHom (Algebra.ofId A _) scalar (by
    ext z V v
    rw [AlgHom.comp_apply, Algebra.ofId_apply, algebraMap_app_hom_hom_apply,
      AlgHom.id_apply, app_apply_of_forall_eq z V fun g ↦ by simp [Subsingleton.elim g 1]])
    (AlgHom.ext scalar.commutes)

/-- `algEquivOfSubsingleton` sends `a` to the scalar `a`. -/
@[simp] lemma algEquivOfSubsingleton_apply [Subsingleton G] (a : A) :
    algEquivOfSubsingleton A G a = algebraMap A _ a :=
  (rfl)

/-- The inverse of `algEquivOfSubsingleton` is `scalar`. -/
@[simp] lemma algEquivOfSubsingleton_symm_apply [Subsingleton G]
    (z : SmoothCenter.{max u v} A G) :
    (algEquivOfSubsingleton A G).symm z = scalar z :=
  (rfl)

end Generators

section Compact

/-- **Compact open permutation representations detect the smooth centre**: for a locally
profinite group `G`, two elements of `Z(G, A)` that agree on `A[G ⧸ U]` for every compact open
subgroup `U` are equal. -/
lemma ext_of_ofMulAction_quotient_isCompact [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    {z z' : SmoothCenter.{max u v} A G}
    (h : ∀ U : OpenSubgroup G, IsCompact (U : Set G) →
      z.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G)))) =
        z'.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G))))) :
    z = z' :=
  ext_of_ofMulAction_quotient_of_exists_le_stabilizer (fun U ↦ IsCompact (U : Set G))
    (fun V v ↦ mem_smoothVectors_iff_exists_isCompact_openSubgroup.1
      (IsSmooth.mem_smoothVectors (ρ := V.obj.ρ) v)) h

end Compact

end SmoothCenter

end TauCeti
