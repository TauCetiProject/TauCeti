/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.GroupTheory.QuotientGroup.Basic
public import TauCeti.RepresentationTheory.FreeOfBasis
import TauCeti.GroupTheory.GroupAction.Free

/-!
# Maps and equivalences of permutation representations

`MulActionHom.toRepRes` linearly extends a map equivariant along a monoid homomorphism
to a morphism of permutation representations with restricted target action. It respects
identity and composition. `Rep.ofMulAction_hom_ext` tests morphism equality on basis vectors.

For a monoid `G`, equivariantly equivalent `G`-sets carry equivalent permutation
representations, and the permutation representation on a disjoint union is the product of
the representations on its two pieces.

For a group `G` and a subgroup `H`, the permutation representation `k[G ⧸ H]` interpolates
between the two extremes `H = ⊤` and `H = ⊥`.  This file identifies those extremes: the cosets
of the whole group carry the trivial representation, and the cosets of the trivial subgroup
carry the left regular representation.

Both identifications go through `ofMulActionIsoCongr`, which turns a `G`-equivariant equivalence
of `G`-sets into an isomorphism of the permutation representations they carry.

For a free action of a group `G` on `X`, every point is a unique translate of the chosen
representative of its orbit, so the permutation representation `k[X]` is free over the group
ring, with basis the chosen representatives of the orbits. In particular it is a projective
object of `Rep k G`.

## Main definitions

* `TauCeti.ofMulActionIsoCongr`: an equivariant equivalence of `G`-sets induces an isomorphism
  of permutation representations.
* `TauCeti.ofMulActionSumEquiv`: the permutation representation on a disjoint union is the
  product of the permutation representations on the pieces.
* `TauCeti.quotientIsoCongr`: equal subgroups give isomorphic permutation representations.
* `TauCeti.quotientTopIsoTrivial`: `k[G ⧸ ⊤] ≅ k` with the trivial action.
* `TauCeti.quotientBotIsoLeftRegular`: `k[G ⧸ ⊥] ≅ k[G]` with the left regular action.
* `TauCeti.ofMulActionIsoFree`: for a free action, `k[X]` is the free representation on the
  orbits.

## Main results

* `TauCeti.projective_ofMulAction`: the permutation representation of a free action is
  projective.

The equivalences and isomorphisms come with lemmas reading them and their inverses on basis
elements. For the coset representations, these bases are indexed by `G ⧸ H`.

-/

public section

open CategoryTheory

namespace Rep

/-- Morphisms out of a permutation representation are determined by their values on basis
vectors with coefficient one. -/
@[ext]
theorem ofMulAction_hom_ext {k G X : Type*} [Ring k] [Monoid G] [MulAction G X]
    {A : Rep k G} {f g : ofMulAction k G X ⟶ A}
    (h : ∀ x, f.hom (MonoidAlgebra.single x 1) = g.hom (MonoidAlgebra.single x 1)) : f = g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring (h x)

end Rep

namespace MulActionHom

universe u v v' v'' w

variable {k : Type u} [Ring k] {G : Type v} {H : Type v'} {K : Type v''}
  [Monoid G] [Monoid H] [Monoid K]
  {X Y Z : Type w} [MulAction G X] [MulAction H Y] [MulAction K Z]
  {φ : G →* H} {ψ : H →* K}

/-- Linear extension of a map equivariant along a monoid homomorphism, with the target
representation restricted along that homomorphism. -/
noncomputable def toRepRes (f : X →ₑ[φ] Y) :
    Rep.ofMulAction k G X ⟶ Rep.res φ (Rep.ofMulAction k H Y) :=
  Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k f.toFun
      isIntertwining' g := by
        refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
        simp [Representation.ofMulAction_single, f.map_smul'] }

/-- The underlying linear map sends coefficients along the equivariant function. -/
@[simp]
theorem toRepRes_hom_toLinearMap (f : X →ₑ[φ] Y) :
    (dsimp% only (f.toRepRes (k := k)).hom.toLinearMap) =
      MonoidAlgebra.mapDomainLinearMap k k f.toFun :=
  (rfl)

-- Explicit toFun projections let simp evaluate bundled constructors without unfolding the
-- FunLike instance across module boundaries.
/-- Linear extension sends a basis vector to the basis vector indexed by its image. -/
@[simp]
theorem toRepRes_hom_single (f : X →ₑ[φ] Y) (x : X) (r : k) :
    (dsimp% only ((f.toRepRes (k := k)).hom (MonoidAlgebra.single x r))) =
      MonoidAlgebra.single (f.toFun x) r := by
  simp [toRepRes]

/-- Linear extension of the identity is the identity morphism. -/
@[simp]
theorem toRepRes_id :
    (MulActionHom.id G (X := X)).toRepRes (k := k) (φ := MonoidHom.id G) =
      𝟙 (Rep.ofMulAction k G X) := by
  apply Rep.ofMulAction_hom_ext
  intro x
  simp [MulActionHom.id]

/-- Linear extension respects composition, restricting the second morphism along the first
homomorphism. -/
@[simp]
theorem toRepRes_comp (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) :
    (g.comp f (κ := ⟨rfl⟩)).toRepRes (k := k) (φ := ψ.comp φ) =
      f.toRepRes ≫ (Rep.resFunctor φ).map g.toRepRes := by
  apply Rep.ofMulAction_hom_ext
  intro x
  simp only [Rep.hom_comp, ← Representation.IntertwiningMap.toLinearMap_apply]
  simp only [Representation.IntertwiningMap.comp_toLinearMap, Rep.resMap_hom_toLinearMap,
    toRepRes_hom_toLinearMap, LinearMap.comp_apply, MonoidAlgebra.mapDomainLinearMap_single]
  rfl

end MulActionHom

namespace TauCeti

universe u v w w'

open CategoryTheory

section Congr

variable {G : Type v} [Monoid G]

section Semiring

variable (k : Type u) [Semiring k] {X : Type w} {Y : Type w'} [MulAction G X] [MulAction G Y]

/-- A `G`-equivariant equivalence of `G`-sets induces an equivalence of the permutation
representations on their free modules. -/
noncomputable def ofMulActionEquivCongr (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    (Representation.ofMulAction k G X).Equiv (Representation.ofMulAction k G Y) :=
  .mk (MonoidAlgebra.mapDomainLinearEquiv k k e) fun _ => by ext; simp [he]

@[simp]
theorem ofMulActionEquivCongr_apply_single (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (x : X) (r : k) :
    ofMulActionEquivCongr k e he (MonoidAlgebra.single x r) = MonoidAlgebra.single (e x) r := by
  simp [ofMulActionEquivCongr]

@[simp]
theorem ofMulActionEquivCongr_symm_apply_single (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (y : Y) (r : k) :
    (ofMulActionEquivCongr k e he).symm (MonoidAlgebra.single y r) =
      MonoidAlgebra.single (e.symm y) r := by
  simp [ofMulActionEquivCongr]

/-- The permutation representation on a disjoint union of `G`-sets is the product of the
permutation representations on the two pieces. -/
noncomputable def ofMulActionSumEquiv :
    (Representation.ofMulAction k G (X ⊕ Y)).Equiv
      ((Representation.ofMulAction k G X).prod (Representation.ofMulAction k G Y)) :=
  .mk ((MonoidAlgebra.coeffLinearEquiv k).trans <| (Finsupp.sumFinsuppLEquivProdFinsupp k).trans <|
      ((MonoidAlgebra.coeffLinearEquiv k).prodCongr (MonoidAlgebra.coeffLinearEquiv k)).symm)
    fun _ ↦ by ext (_ | _) <;> simp [Representation.ofMulAction_single]

@[simp]
theorem ofMulActionSumEquiv_apply_single_inl (x : X) (r : k) :
    ofMulActionSumEquiv k (Y := Y) (G := G) (MonoidAlgebra.single (.inl x) r) =
      (MonoidAlgebra.single x r, 0) := by
  simp [ofMulActionSumEquiv]

@[simp]
theorem ofMulActionSumEquiv_apply_single_inr (y : Y) (r : k) :
    ofMulActionSumEquiv k (X := X) (G := G) (MonoidAlgebra.single (.inr y) r) =
      (0, MonoidAlgebra.single y r) := by
  simp [ofMulActionSumEquiv]

@[simp]
theorem ofMulActionSumEquiv_symm_apply_single_inl (x : X) (r : k) :
    (ofMulActionSumEquiv k (Y := Y) (G := G)).symm (MonoidAlgebra.single x r, 0) =
      MonoidAlgebra.single (.inl x) r :=
  (ofMulActionSumEquiv k).symm_apply_eq.mpr (ofMulActionSumEquiv_apply_single_inl k x r).symm

@[simp]
theorem ofMulActionSumEquiv_symm_apply_single_inr (y : Y) (r : k) :
    (ofMulActionSumEquiv k (X := X) (G := G)).symm (0, MonoidAlgebra.single y r) =
      MonoidAlgebra.single (.inr y) r :=
  (ofMulActionSumEquiv k).symm_apply_eq.mpr (ofMulActionSumEquiv_apply_single_inr k y r).symm

end Semiring

-- Objects of `Rep k G` carry an `AddCommGroup`, so `Rep.ofMulAction k G X` needs `k[X]` to be
-- one; Mathlib declares `Rep.ofMulAction` in its `ring` section for exactly this reason, and
-- everything below is stated in terms of it.  An isomorphism in `Rep k G` also compares two
-- objects of the same category, so here `X` and `Y` share a universe.
variable (k : Type u) [Ring k] {X Y : Type w} [MulAction G X] [MulAction G Y]

/-- A `G`-equivariant equivalence of `G`-sets induces an isomorphism of the permutation
representations they carry. -/
noncomputable def ofMulActionIsoCongr (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    Rep.ofMulAction k G X ≅ Rep.ofMulAction k G Y :=
  Rep.mkIso (ofMulActionEquivCongr k e he)

-- `simp` reduces the carriers of the `abbrev`s `Rep.ofMulAction`, `Rep.leftRegular` and
-- `Rep.trivial` (e.g. to `k[X]`) in implicit type arguments before it looks a term up, so the
-- `simp` lemmas evaluating this file's isomorphisms on basis elements state their left-hand sides
-- through `dsimp% only`, as in #8315.
@[simp]
theorem ofMulActionIsoCongr_hom_hom_single (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (x : X) (r : k) :
    (dsimp% only ((ofMulActionIsoCongr k e he).hom.hom (MonoidAlgebra.single x r))) =
      MonoidAlgebra.single (e x) r := by
  simp [ofMulActionIsoCongr, ofMulActionEquivCongr]

@[simp]
theorem ofMulActionIsoCongr_inv_hom_single (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (y : Y) (r : k) :
    (dsimp% only ((ofMulActionIsoCongr k e he).inv.hom (MonoidAlgebra.single y r))) =
      MonoidAlgebra.single (e.symm y) r := by
  simp [ofMulActionIsoCongr, ofMulActionEquivCongr]

end Congr

section Quotient

variable (k : Type u) [Ring k] {G : Type v} [Group G]

/-- Equal subgroups have the same cosets, so they carry isomorphic permutation
representations. -/
noncomputable def quotientIsoCongr {H K : Subgroup G} (h : H = K) :
    Rep.ofMulAction k G (G ⧸ H) ≅ Rep.ofMulAction k G (G ⧸ K) :=
  ofMulActionIsoCongr k (Subgroup.quotientEquivOfEq h) fun _ q => by
    induction q using QuotientGroup.induction_on with
    | H x => rfl

@[simp]
theorem quotientIsoCongr_hom_hom_single {H K : Subgroup G} (h : H = K) (q : G ⧸ H) (r : k) :
    (dsimp% only ((quotientIsoCongr k h).hom.hom (MonoidAlgebra.single q r))) =
      MonoidAlgebra.single (Subgroup.quotientEquivOfEq h q) r :=
  ofMulActionIsoCongr_hom_hom_single k _ _ q r

@[simp]
theorem quotientIsoCongr_inv_hom_single {H K : Subgroup G} (h : H = K) (q : G ⧸ K) (r : k) :
    (dsimp% only ((quotientIsoCongr k h).inv.hom (MonoidAlgebra.single q r))) =
      MonoidAlgebra.single (Subgroup.quotientEquivOfEq h.symm q) r :=
  ofMulActionIsoCongr_inv_hom_single k _ _ q r

-- Not `@[simp]`: `simp` proves it from `quotientIsoCongr_hom_hom_single` and
-- `Subgroup.quotientEquivOfEq_mk`, so simpNF rejects it. The left-hand side is still stated
-- through `dsimp% only`, so that `simp only [this lemma]` fires.
/-- The basis element indexed by the coset of a representative, in the forward direction. -/
theorem quotientIsoCongr_hom_hom_single_mk {H K : Subgroup G} (h : H = K) (x : G) (r : k) :
    (dsimp% only ((quotientIsoCongr k h).hom.hom (MonoidAlgebra.single (x : G ⧸ H) r))) =
      MonoidAlgebra.single (x : G ⧸ K) r :=
  quotientIsoCongr_hom_hom_single k h _ r

-- Not `@[simp]`, as for `quotientIsoCongr_hom_hom_single_mk`: `simp` first rewrites the left-hand
-- side with `quotientIsoCongr_inv_hom_single`.
/-- The basis element indexed by the coset of a representative, in the inverse direction. -/
theorem quotientIsoCongr_inv_hom_single_mk {H K : Subgroup G} (h : H = K) (x : G) (r : k) :
    (dsimp% only ((quotientIsoCongr k h).inv.hom (MonoidAlgebra.single (x : G ⧸ K) r))) =
      MonoidAlgebra.single (x : G ⧸ H) r :=
  quotientIsoCongr_inv_hom_single k h _ r

/-- The permutation representation of `G` on the cosets of the trivial subgroup is the left
regular representation. -/
noncomputable def quotientBotIsoLeftRegular :
    Rep.ofMulAction k G (G ⧸ (⊥ : Subgroup G)) ≅ Rep.leftRegular k G :=
  ofMulActionIsoCongr k QuotientGroup.quotientBot.toEquiv quotientBot_equivariant

@[simp]
theorem quotientBotIsoLeftRegular_hom_hom_single (q : G ⧸ (⊥ : Subgroup G)) (r : k) :
    (dsimp% only ((quotientBotIsoLeftRegular k).hom.hom (MonoidAlgebra.single q r))) =
      MonoidAlgebra.single (QuotientGroup.quotientBot q) r :=
  ofMulActionIsoCongr_hom_hom_single k QuotientGroup.quotientBot.toEquiv
    quotientBot_equivariant q r

-- Not `@[simp]`: `simp` first rewrites the left-hand side with
-- `quotientBotIsoLeftRegular_hom_hom_single`, so simpNF rejects it. The left-hand side is still
-- stated through `dsimp% only`, so that `simp only [this lemma]` fires.
/-- The basis element indexed by the coset of a representative is sent to that
representative. -/
theorem quotientBotIsoLeftRegular_hom_hom_single_mk (x : G) (r : k) :
    (dsimp% only ((quotientBotIsoLeftRegular k).hom.hom
        (MonoidAlgebra.single (x : G ⧸ (⊥ : Subgroup G)) r))) =
      MonoidAlgebra.single x r :=
  quotientBotIsoLeftRegular_hom_hom_single k _ r

@[simp]
theorem quotientBotIsoLeftRegular_inv_hom_single (x : G) (r : k) :
    (dsimp% only ((quotientBotIsoLeftRegular k).inv.hom (MonoidAlgebra.single x r))) =
      MonoidAlgebra.single (x : G ⧸ (⊥ : Subgroup G)) r :=
  ofMulActionIsoCongr_inv_hom_single k QuotientGroup.quotientBot.toEquiv
    quotientBot_equivariant _ r

end Quotient

section QuotientTop

-- Mathlib's `Rep.ofMulActionSubsingletonIsoTrivial` compares `Rep.ofMulAction k G H` with
-- `Rep.trivial k G k`, so it needs the `G`-set `H` to live in the universe of `k`; for
-- `H = G ⧸ ⊤` that forces `G` into the universe of `k` as well.
variable (k : Type u) [Ring k] {G : Type u} [Group G]

/-- The permutation representation of `G` on the cosets of the whole group is the trivial
representation: there is only one coset. -/
noncomputable def quotientTopIsoTrivial :
    Rep.ofMulAction k G (G ⧸ (⊤ : Subgroup G)) ≅ Rep.trivial k G k :=
  haveI := QuotientGroup.subsingleton_quotient_top (G := G)
  Rep.ofMulActionSubsingletonIsoTrivial k G (G ⧸ (⊤ : Subgroup G))

@[simp]
theorem quotientTopIsoTrivial_hom_hom_single (q : G ⧸ (⊤ : Subgroup G)) (r : k) :
    (dsimp% only ((quotientTopIsoTrivial k).hom.hom (MonoidAlgebra.single q r))) = r := by
  have := QuotientGroup.subsingleton_quotient_top (G := G)
  rw [Subsingleton.elim q 1]
  simp [quotientTopIsoTrivial, Representation.ofMulActionSubsingletonEquivTrivial]

@[simp]
theorem quotientTopIsoTrivial_inv_hom_apply (r : k) :
    (dsimp% only ((quotientTopIsoTrivial k).inv.hom r)) =
      MonoidAlgebra.single ((1 : G) : G ⧸ (⊤ : Subgroup G)) r := by
  have := QuotientGroup.subsingleton_quotient_top (G := G)
  simp [quotientTopIsoTrivial, Representation.ofMulActionSubsingletonEquivTrivial]

end QuotientTop

section Free

open _root_.MulAction (orbitRel selfEquivOrbitsQuotientProd)

variable (k : Type u) [CommRing k] {G : Type u} [Group G] (X : Type u) [MulAction G X]
  [IsCancelSMul G X]

/-- **The permutation representation of a free action is free over the group ring**, with
basis the chosen representatives `q.out` of the orbits: the generator `single q (single g r)` of
the free representation corresponds to `single (g • q.out) r`. -/
noncomputable def ofMulActionIsoFree :
    Rep.ofMulAction k G X ≅ Rep.free k G (orbitRel.Quotient G X) :=
  (Rep.mkIso ((Representation.ofMulAction k G X).freeEquivOfBasis (MonoidAlgebra.basis X k)
    ((Equiv.sigmaEquivProd _ G).trans
      (selfEquivOrbitsQuotientProd IsCancelSMul.stabilizer_eq_bot).symm) fun g h q ↦ by
        simp [mul_smul])).symm

/-- The generator `single q (single g r)` of the free representation corresponds to the basis
vector `single (g • q.out) r` of the permutation representation. -/
@[simp]
theorem ofMulActionIsoFree_inv_hom_single (q : orbitRel.Quotient G X) (g : G) (r : k) :
    (dsimp% only ((ofMulActionIsoFree k X).inv.hom
        (Finsupp.single q (MonoidAlgebra.single g r)))) =
      MonoidAlgebra.single (g • q.out) r := by
  rw [ofMulActionIsoFree, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  simp

/-- The basis vector `single (g • q.out) r` of the permutation representation corresponds to the
generator `single q (single g r)` of the free representation. -/
@[simp]
theorem ofMulActionIsoFree_hom_hom_single (q : orbitRel.Quotient G X) (g : G) (r : k) :
    (dsimp% only ((ofMulActionIsoFree k X).hom.hom (MonoidAlgebra.single (g • q.out) r))) =
      Finsupp.single q (MonoidAlgebra.single g r) := by
  rw [← ofMulActionIsoFree_inv_hom_single, Rep.hom_inv_apply]

/-- The permutation representation of a free action is projective. -/
instance projective_ofMulAction : Projective (Rep.ofMulAction k G X) :=
  Projective.of_iso (ofMulActionIsoFree k X).symm inferInstance

end Free

end TauCeti
