/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Group

/-!
# Group and integral-module carriers of relative homotopy groups

Let `X = (X, A, a₀)` be a based pair and let `n` be the cardinality of the index type `N`. The
relative homotopy set `π_{n+1}(X, A, a₀) = TauCeti.RelHomotopyGroup N X` is a group for `n ≥ 1`
and a commutative group for `n ≥ 2`. This file packages these groups as functors on based pairs,
with the algebra that holds in each range of degrees.

* For `n ≥ 1`, `π_{n+1}(X, A, a₀)` is a functor to `GrpCat`, and the boundary map
  `π_{n+1}(X, A, a₀) → π_n(A, a₀)` is a natural transformation of group-valued functors.
* For `n ≥ 1`, the abelianization of `π_{n+1}(X, A, a₀)` is a functor to `ModuleCat ℤ`, whose
  underlying abelian groups are those of Mathlib's `GrpCat.abelianize`. The quotient map onto it
  turns products into sums and is natural, and a morphism from it to a `ℤ`-module `M` is the same
  as a homomorphism from `π_{n+1}(X, A, a₀)` to the additive group of `M`. This is the integral
  module available in every degree at least two: `π_2(X, A, a₀)` need not be commutative, so a
  homomorphism from it to an abelian group, such as relative homology, is a morphism out of its
  abelianization.
* For `n ≥ 2`, the commutative group `π_{n+1}(X, A, a₀)` is itself a functor to `ModuleCat ℤ`,
  naturally isomorphic to its abelianization.

## Main declarations

* `TauCeti.RelHomotopyGroup.grpFunctor`: `π_{n+1}(X, A, a₀)` as a functor to `GrpCat`.
* `TauCeti.BasedTopPair.subspaceHomotopyGroupFunctor`: `π_n(A, a₀)` as a functor to `GrpCat`.
* `TauCeti.RelHomotopyGroup.boundaryNatTrans`: the boundary map as a natural transformation.
* `TauCeti.RelHomotopyGroup.abelianizationFunctor`: the abelianization of `π_{n+1}(X, A, a₀)` as
  a functor to `ModuleCat ℤ`, with the quotient map `TauCeti.RelHomotopyGroup.toAbelianization`
  and its universal property `TauCeti.RelHomotopyGroup.abelianizationLift`.
* `TauCeti.RelHomotopyGroup.moduleFunctor`: `π_{n+1}(X, A, a₀)` as a functor to `ModuleCat ℤ`
  for `n ≥ 2`, and `TauCeti.RelHomotopyGroup.moduleFunctorIsoAbelianizationFunctor`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.1, for relative homotopy groups, their group
  structure in degrees at least two, and their commutativity in degrees at least three.
-/

public section

noncomputable section

universe u v

open CategoryTheory

namespace TauCeti

namespace RelHomotopyGroup

variable (N : Type v) [DecidableEq N]

/-! ### The group-valued functor and the boundary map -/

/-- The relative homotopy groups `π_{n+1}(X, A, a₀)`, for `n ≥ 1`, as a functor from based pairs
to groups. -/
@[expose, simps obj map]
def grpFunctor [Nonempty N] : BasedTopPair.{u} ⥤ GrpCat.{max u v} where
  obj X := GrpCat.of (RelHomotopyGroup N X)
  map f := GrpCat.ofHom (mapHom f)
  map_id _ := GrpCat.hom_ext mapHom_id
  map_comp f g := GrpCat.hom_ext (mapHom_comp f g).symm

end RelHomotopyGroup

namespace BasedTopPair

variable (N : Type v) [DecidableEq N]

/-- The homotopy groups `π_n(A, a₀)` of the subspace of a based pair `(X, A, a₀)` at its
basepoint, for `n ≥ 1`, as a functor from based pairs to groups. This is the target of the
boundary map of relative homotopy groups. -/
@[expose, simps obj map]
def subspaceHomotopyGroupFunctor [Nonempty N] : BasedTopPair.{u} ⥤ GrpCat.{max u v} where
  obj X := GrpCat.of (HomotopyGroup N X.pair.snd X.basepoint)
  map f := GrpCat.ofHom (HomotopyGroup.mapHom (TopPair.Hom.snd f.toTopPairHom).hom
    f.map_basepoint)
  map_id _ := GrpCat.hom_ext <| MonoidHom.ext HomotopyGroup.map_id_apply
  map_comp _ _ := GrpCat.hom_ext <| MonoidHom.ext fun _ =>
    (HomotopyGroup.map_comp_apply _ _ _ _ _).symm

end BasedTopPair

namespace RelHomotopyGroup

variable (N : Type v) [DecidableEq N]

/-- The boundary map `π_{n+1}(X, A, a₀) → π_n(A, a₀)`, for `n ≥ 1`, as a natural transformation
of group-valued functors on based pairs. -/
def boundaryNatTrans [Nonempty N] :
    grpFunctor.{u} N ⟶ BasedTopPair.subspaceHomotopyGroupFunctor N where
  app _ := GrpCat.ofHom boundaryHom
  naturality _ _ f := GrpCat.hom_ext (boundaryHom_comp_mapHom f)

@[simp]
theorem boundaryNatTrans_app [Nonempty N] (X : BasedTopPair.{u}) :
    (boundaryNatTrans N).app X = GrpCat.ofHom boundaryHom :=
  (rfl)

/-! ### The abelianization as an integral module -/

section Abelianization

/-- The abelianization of `π_{n+1}(X, A, a₀)`, for `n ≥ 1`, as a functor from based pairs to
`ℤ`-modules. In degree two, where `π_2(X, A, a₀)` need not be commutative, this is the integral
module through which every homomorphism to an abelian group factors
(`TauCeti.RelHomotopyGroup.abelianizationLift`). -/
@[expose]
def abelianizationFunctor [Nonempty N] : BasedTopPair.{u} ⥤ ModuleCat.{max u v} ℤ where
  obj X := ModuleCat.of ℤ (Additive (Abelianization (RelHomotopyGroup N X)))
  map f := ModuleCat.ofHom (MonoidHom.toAdditive (Abelianization.map (mapHom f))).toIntLinearMap
  map_id _ := by
    ext a
    simp
  map_comp _ _ := by
    ext a
    simp

/-- The underlying abelian groups of `TauCeti.RelHomotopyGroup.abelianizationFunctor` are those of
Mathlib's abelianization functor `GrpCat.abelianize`, applied to `π_{n+1}(X, A, a₀)`. -/
def abelianizationFunctorCompForget₂Iso [Nonempty N] :
    abelianizationFunctor.{u} N ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat ≅
      grpFunctor N ⋙ GrpCat.abelianize ⋙ CommGrpCat.toAddCommGrp :=
  -- Both functors send a morphism `f` to the additive form of `Abelianization.map (mapHom f)`:
  -- `GrpCat.abelianize` is defined by `Abelianization.lift (Abelianization.of.comp _)`, which
  -- is `Abelianization.map` by definition (`Abelianization.lift_of_comp`).
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

variable {N} [Nonempty N] {X Y : BasedTopPair.{u}}

/-- The quotient map from `π_{n+1}(X, A, a₀)` onto its abelianization, for `n ≥ 1`. It carries
products to sums (`TauCeti.RelHomotopyGroup.toAbelianization_mul`). -/
def toAbelianization (a : RelHomotopyGroup N X) :
    Additive (Abelianization (RelHomotopyGroup N X)) :=
  Additive.ofMul (Abelianization.of a)

@[simp]
theorem toAbelianization_mul (a b : RelHomotopyGroup N X) :
    toAbelianization (a * b) = toAbelianization a + toAbelianization b :=
  (rfl)

@[simp]
theorem toAbelianization_one : toAbelianization (1 : RelHomotopyGroup N X) = 0 :=
  (rfl)

@[simp]
theorem toAbelianization_inv (a : RelHomotopyGroup N X) :
    toAbelianization a⁻¹ = -toAbelianization a :=
  (rfl)

/-- Two elements of `π_{n+1}(X, A, a₀)` have the same image in the abelianization exactly when
their quotient lies in the commutator subgroup. -/
theorem toAbelianization_eq_toAbelianization_iff {a b : RelHomotopyGroup N X} :
    toAbelianization a = toAbelianization b ↔ a * b⁻¹ ∈ commutator (RelHomotopyGroup N X) :=
  Additive.ofMul.injective.eq_iff.trans <| by
    rw [← div_eq_one, ← map_div, ← MonoidHom.mem_ker, Abelianization.ker_of, div_eq_mul_inv]

/-- The quotient map onto the abelianization is surjective: every element of the abelianization
of `π_{n+1}(X, A, a₀)` is represented by an element of `π_{n+1}(X, A, a₀)`. -/
theorem toAbelianization_surjective :
    Function.Surjective (toAbelianization : RelHomotopyGroup N X → _) :=
  Additive.ofMul.surjective.comp QuotientGroup.mk_surjective

/-- The quotient map onto the abelianization is natural in the based pair. -/
@[simp]
theorem abelianizationFunctor_map_toAbelianization (f : X ⟶ Y) (a : RelHomotopyGroup N X) :
    (abelianizationFunctor N).map f (toAbelianization a) = toAbelianization (map f a) :=
  congrArg (fun b => Additive.ofMul (Abelianization.of b)) (mapHom_apply f a)

/-- Two morphisms out of the abelianization of `π_{n+1}(X, A, a₀)` agree when they agree on the
image of `π_{n+1}(X, A, a₀)`. -/
theorem abelianization_hom_ext {M : ModuleCat.{max u v} ℤ}
    {φ ψ : (abelianizationFunctor N).obj X ⟶ M}
    (h : ∀ a : RelHomotopyGroup N X, φ (toAbelianization a) = ψ (toAbelianization a)) :
    φ = ψ := by
  ext a
  obtain ⟨b, rfl⟩ := toAbelianization_surjective a
  exact h b

/-- A homomorphism from `π_{n+1}(X, A, a₀)` to the underlying group of a `ℤ`-module `M`, written
multiplicatively, induces a morphism from the abelianization of `π_{n+1}(X, A, a₀)` to `M`. -/
def abelianizationLift {M : ModuleCat.{max u v} ℤ}
    (φ : RelHomotopyGroup N X →* Multiplicative M) : (abelianizationFunctor N).obj X ⟶ M :=
  ModuleCat.ofHom
    { toFun := MonoidHom.toAdditiveLeft (Abelianization.lift φ)
      map_add' := map_add _
      map_smul' n a := by
        simpa using map_intCast_smul (MonoidHom.toAdditiveLeft (Abelianization.lift φ)) ℤ ℤ n a }

@[simp]
theorem abelianizationLift_toAbelianization {M : ModuleCat.{max u v} ℤ}
    (φ : RelHomotopyGroup N X →* Multiplicative M) (a : RelHomotopyGroup N X) :
    abelianizationLift φ (toAbelianization a) = (φ a).toAdd :=
  (rfl)

/-- Every morphism out of the abelianization of `π_{n+1}(X, A, a₀)` is the lift of its composite
with the quotient map. -/
theorem abelianizationLift_unique {M : ModuleCat.{max u v} ℤ}
    (φ : RelHomotopyGroup N X →* Multiplicative M) (ψ : (abelianizationFunctor N).obj X ⟶ M)
    (h : ∀ a, ψ (toAbelianization a) = (φ a).toAdd) : ψ = abelianizationLift φ :=
  abelianization_hom_ext fun a => by rw [h, abelianizationLift_toAbelianization]

end Abelianization

/-! ### The integral module in degrees at least three -/

section Module

variable {X Y : BasedTopPair.{u}}

/-- The relative homotopy groups `π_{n+1}(X, A, a₀)`, for `n ≥ 2`, as a functor from based pairs
to `ℤ`-modules: in these degrees they are commutative groups. -/
@[expose]
def moduleFunctor [Nontrivial N] : BasedTopPair.{u} ⥤ ModuleCat.{max u v} ℤ where
  obj X := ModuleCat.of ℤ (Additive (RelHomotopyGroup N X))
  map f := ModuleCat.ofHom (MonoidHom.toAdditive (mapHom f)).toIntLinearMap
  map_id _ := by
    ext a
    simp
  map_comp _ _ := by
    ext a
    simp

variable {N}

@[simp]
theorem moduleFunctor_map_ofMul [Nontrivial N] (f : X ⟶ Y) (a : RelHomotopyGroup N X) :
    (moduleFunctor N).map f (Additive.ofMul a) = Additive.ofMul (map f a) :=
  congrArg Additive.ofMul (mapHom_apply f a)

variable (N)

/-- For `n ≥ 2`, the integral module `π_{n+1}(X, A, a₀)` is naturally isomorphic to its
abelianization: the quotient map is an isomorphism because the group is already commutative. -/
def moduleFunctorIsoAbelianizationFunctor [Nontrivial N] :
    moduleFunctor.{u} N ≅ abelianizationFunctor N :=
  NatIso.ofComponents
    (fun X => (MulEquiv.toAdditive
      (Abelianization.equivOfComm (H := RelHomotopyGroup N X))).toIntLinearEquiv.toModuleIso)
    fun f => by
      ext a
      rfl

variable {N}

@[simp]
theorem moduleFunctorIsoAbelianizationFunctor_hom_app_ofMul [Nontrivial N]
    (a : RelHomotopyGroup N X) :
    (moduleFunctorIsoAbelianizationFunctor N).hom.app X (Additive.ofMul a) = toAbelianization a :=
  (rfl)

@[simp]
theorem moduleFunctorIsoAbelianizationFunctor_inv_app_toAbelianization [Nontrivial N]
    (a : RelHomotopyGroup N X) :
    (moduleFunctorIsoAbelianizationFunctor N).inv.app X (toAbelianization a) = Additive.ofMul a :=
  (rfl)

/-- For `n ≥ 2`, the quotient map from `π_{n+1}(X, A, a₀)` onto its abelianization is
bijective. -/
theorem toAbelianization_bijective [Nontrivial N] :
    Function.Bijective (toAbelianization : RelHomotopyGroup N X → _) :=
  ((moduleFunctorIsoAbelianizationFunctor N).app X).toLinearEquiv.bijective.comp
    Additive.ofMul.bijective

end Module

end RelHomotopyGroup

end TauCeti
