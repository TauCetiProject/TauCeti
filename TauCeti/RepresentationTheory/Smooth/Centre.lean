/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Center.Linear
public import TauCeti.RepresentationTheory.OfMulAction.CosetLift
public import TauCeti.RepresentationTheory.Smooth.Category

/-!
# The centre of the category of smooth representations

For a commutative ring `A` and a topological group `G`, the *smooth centre*
`TauCeti.SmoothCentre A G` is the centre `CatCenter (SmoothRep A G)` of the category of smooth
representations: the endomorphisms `z` of the identity functor, a family of intertwining maps
`z_V : V → V` commuting with every morphism. It is a commutative ring, written `Z(G, A)`, and an
`A`-algebra through the scalar endomorphisms `a ↦ (v ↦ a • v)` (Mathlib's
`CategoryTheory.Linear.toCatCenter`). Mathlib's `CatCenter.app`, `CatCenter.naturality` and
`CatCenter.ext` give evaluation, commutation with morphisms and equality tested on every object,
and Mathlib's action of `CatCenter C` on morphisms (`CatCenter.smul_eq`, `CatCenter.smul_eq'`) is
the action of `Z(G, A)` on `Hom_G(V, W)`, compatible from both sides.

An element of `Z(G, A)` restricts to subrepresentations and passes to quotients
(`TauCeti.SmoothCentre.app_subtype`, `TauCeti.SmoothCentre.app_mkQ`). It is determined by its
values on the permutation representations `A[G ⧸ U]` for `U` open
(`TauCeti.SmoothCentre.ext_of_ofMulAction_quotient`), or, for locally profinite `G`, compact open
(`TauCeti.SmoothCentre.ext_of_ofMulAction_quotient_isCompact`): a vector `v` fixed by `U` is the
image of the coset `U` under the intertwining map `A[G ⧸ U] → V`, `g U ↦ ρ g v`. On a `G`-invariant
vector, `z` acts by the scalar by which it acts on the trivial representation `A`
(`TauCeti.SmoothCentre.app_apply_of_forall_eq`), so for a trivial group the smooth centre is
`A` (`TauCeti.SmoothCentre.algEquivOfSubsingleton`).

## Main definitions

* `TauCeti.SmoothCentre A G`: the centre of the category `SmoothRep A G`, a commutative
  `A`-algebra.
* `TauCeti.SmoothCentre.scalar z`: the scalar by which `z` acts on the trivial representation `A`.
* `TauCeti.SmoothCentre.algEquivOfSubsingleton`: for a trivial group, `A ≃ₐ[A] Z(G, A)`.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, 1987
  manuscript, §1.8, p. 8 (the centre and its action on morphisms and extensions).
-/

@[expose] public section

open CategoryTheory Representation

universe w u v

namespace TauCeti

variable (A : Type u) [CommRing A] (G : Type v) [Group G] [TopologicalSpace G]

/-- The **smooth centre** `Z(G, A)`: the centre `CatCenter (SmoothRep A G)` of the category of
smooth representations, the ring of natural endomorphisms of its identity functor. -/
abbrev SmoothCentre : Type _ :=
  CatCenter (SmoothRep.{w} A G)

namespace SmoothCentre

/-- The smooth centre is a commutative ring: the centre of any category is commutative. -/
instance instCommRing : CommRing (SmoothCentre.{w} A G) where
  mul_comm := mul_comm'

/-- The smooth centre is an `A`-algebra: `a : A` acts on every smooth representation as the
scalar `a` (Mathlib's `CategoryTheory.Linear.toCatCenter`). -/
instance instAlgebra : Algebra A (SmoothCentre.{w} A G) :=
  (Linear.toCatCenter A (SmoothRep.{w} A G)).toAlgebra

variable {A G}

/-- The image of `a : A` in the smooth centre acts on every smooth representation by `a`. -/
@[simp] lemma algebraMap_app_hom_hom_apply (a : A) (V : SmoothRep.{w} A G) (v : V.obj) :
    ((algebraMap A (SmoothCentre.{w} A G) a).app V).hom.hom v = a • v :=
  (rfl)

/-- **The centre restricts to subrepresentations**: on a subrepresentation `W` of a smooth
representation `V`, an element `z` of the smooth centre acts as it acts on `V`. -/
lemma app_subtype (z : SmoothCentre.{w} A G) {V : SmoothRep.{w} A G}
    (W : Subrepresentation V.obj.ρ) (x : W.toSubmodule) :
    ((z.app (SmoothRep.of W.toRepresentation)).hom.hom x : V.obj) = (z.app V).hom.hom x := by
  have := congr($(z.naturality (X := SmoothRep.of W.toRepresentation) (Y := V)
    (ObjectProperty.homMk (Rep.ofHom W.subtype))).hom.hom x)
  simpa using this.symm

variable [SeparatelyContinuousMul G] in
/-- **The centre passes to quotients**: on the quotient of a smooth representation `V` by a
subrepresentation `W`, an element `z` of the smooth centre acts on the class of `v` as the class
of `z_V v`. -/
lemma app_mkQ (z : SmoothCentre.{w} A G) {V : SmoothRep.{w} A G}
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
section are about `SmoothCentre.{max u v} A G`. -/

variable [SeparatelyContinuousMul G]

/-- The value of `z` at a vector `v` fixed by an open subgroup `U` is the image of `z` applied to
the coset `U` of `A[G ⧸ U]` under the intertwining map `g U ↦ ρ g v`. -/
lemma app_apply_eq_cosetLift (z : SmoothCentre.{max u v} A G) (V : SmoothRep.{max u v} A G)
    (U : OpenSubgroup G) {v : V.obj} (hv : (U : Subgroup G) ≤ V.obj.ρ.stabilizer v) :
    (z.app V).hom.hom v = V.obj.ρ.cosetLift U v hv
      ((z.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G))))).hom.hom
        (MonoidAlgebra.single ((1 : G) : G ⧸ (U : Subgroup G)) 1)) := by
  have := congr($(z.naturality (X := SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G))))
    (Y := V) (ObjectProperty.homMk (Rep.ofHom (V.obj.ρ.cosetLift U v hv)))).hom.hom
      (MonoidAlgebra.single ((1 : G) : G ⧸ (U : Subgroup G)) 1))
  simpa using this

/-- **The permutation representations `A[G ⧸ U]` detect the smooth centre**: two elements of
`Z(G, A)` that agree on `A[G ⧸ U]` for every open subgroup `U` are equal. -/
lemma ext_of_ofMulAction_quotient {z z' : SmoothCentre.{max u v} A G}
    (h : ∀ U : OpenSubgroup G, z.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G)))) =
      z'.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G))))) :
    z = z' := by
  refine CatCenter.ext _ _ fun V ↦ ObjectProperty.hom_ext _ <| Rep.hom_ext <|
    IntertwiningMap.ext <| LinearMap.ext fun v ↦ ?_
  change (z.app V).hom.hom v = (z'.app V).hom.hom v
  let U : OpenSubgroup G := ⟨V.obj.ρ.stabilizer v, IsSmooth.isOpen_stabilizer v⟩
  rw [app_apply_eq_cosetLift z V U le_rfl, app_apply_eq_cosetLift z' V U le_rfl, h U]

/-- The scalar by which an element `z` of the smooth centre acts on the trivial representation
`A`, realised as the permutation representation `A[G ⧸ G]` on the single coset of `G`. -/
noncomputable def scalar (z : SmoothCentre.{max u v} A G) : A :=
  (z.app (SmoothRep.of (ofMulAction A G (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))))).hom.hom
    (MonoidAlgebra.single ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) 1) |>.coeff
      ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))

omit [SeparatelyContinuousMul G] in
/-- Every element of `A[G ⧸ G]` is a multiple of the basis vector of its single coset. -/
private lemma eq_single_one_quotient_top
    (x : MonoidAlgebra A (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))) :
    x = MonoidAlgebra.single ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))
      (x.coeff ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))) := by
  ext y
  obtain rfl : y = ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) := by
    induction y using QuotientGroup.induction_on with
    | H g => exact QuotientGroup.eq.2 trivial
  simp

/-- **The smooth centre acts on invariant vectors by a scalar**: on a `G`-invariant vector `v`,
an element `z` of `Z(G, A)` acts as the scalar `scalar z` by which it acts on the trivial
representation `A`. -/
lemma app_apply_of_forall_eq (z : SmoothCentre.{max u v} A G) (V : SmoothRep.{max u v} A G)
    {v : V.obj} (hv : ∀ g, V.obj.ρ g v = v) :
    (z.app V).hom.hom v = scalar z • v := by
  have hv' : ((⊤ : OpenSubgroup G) : Subgroup G) ≤ V.obj.ρ.stabilizer v := fun g _ ↦ by
    rw [mem_stabilizer]
    exact hv g
  have hx := eq_single_one_quotient_top
    ((z.app (SmoothRep.of (ofMulAction A G (G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G))))).hom.hom
      (MonoidAlgebra.single ((1 : G) : G ⧸ ((⊤ : OpenSubgroup G) : Subgroup G)) 1))
  rw [app_apply_eq_cosetLift z V ⊤ hv', hx, cosetLift_single, map_one, one_apply_eq_self]
  rfl

/-- The image of `a : A` in the smooth centre acts on the trivial representation by `a`. -/
@[simp] lemma scalar_algebraMap (a : A) :
    scalar (algebraMap A (SmoothCentre.{max u v} A G) a) = a := by
  rw [scalar, algebraMap_app_hom_hom_apply]
  simp

variable (A G) in
/-- **The smooth centre of a trivial group is the coefficient ring**: for a group with one
element, `A → Z(G, A)` is an isomorphism, with inverse `scalar`, since every vector is invariant. -/
noncomputable def algEquivOfSubsingleton [Subsingleton G] : A ≃ₐ[A] SmoothCentre.{max u v} A G :=
  AlgEquiv.ofBijective (Algebra.ofId A _)
    ⟨Function.LeftInverse.injective (g := scalar) scalar_algebraMap,
      Function.RightInverse.surjective (g := scalar) fun z ↦ by
        refine CatCenter.ext _ _ fun V ↦ ObjectProperty.hom_ext _ <| Rep.hom_ext <|
          IntertwiningMap.ext <| LinearMap.ext fun v ↦ ?_
        change ((algebraMap A (SmoothCentre.{max u v} A G) (scalar z)).app V).hom.hom v =
          (z.app V).hom.hom v
        rw [app_apply_of_forall_eq z V fun g ↦ by simp [Subsingleton.elim g 1]]
        simp⟩

/-- `algEquivOfSubsingleton` sends `a` to the scalar `a`. -/
@[simp] lemma algEquivOfSubsingleton_apply [Subsingleton G] (a : A) :
    algEquivOfSubsingleton A G a = algebraMap A _ a := by
  rfl

end Generators

section Compact

/-- **Compact open permutation representations detect the smooth centre**: for a locally
profinite group `G`, two elements of `Z(G, A)` that agree on `A[G ⧸ U]` for every compact open
subgroup `U` are equal. -/
lemma ext_of_ofMulAction_quotient_isCompact [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    {z z' : SmoothCentre.{max u v} A G}
    (h : ∀ U : OpenSubgroup G, IsCompact (U : Set G) →
      z.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G)))) =
        z'.app (SmoothRep.of (ofMulAction A G (G ⧸ (U : Subgroup G))))) :
    z = z' := by
  refine CatCenter.ext _ _ fun V ↦ ObjectProperty.hom_ext _ <| Rep.hom_ext <|
    IntertwiningMap.ext <| LinearMap.ext fun v ↦ ?_
  change (z.app V).hom.hom v = (z'.app V).hom.hom v
  obtain ⟨U, hUc, hU⟩ :=
    mem_smoothVectors_iff_exists_isCompact_openSubgroup.1
      (IsSmooth.mem_smoothVectors (ρ := V.obj.ρ) v)
  rw [app_apply_eq_cosetLift z V U hU, app_apply_eq_cosetLift z' V U hU, h U hUc]

end Compact

end SmoothCentre

end TauCeti
