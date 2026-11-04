/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Exact

/-!
# Pullback and change of groups for associated local coefficient systems

Let `p : E ⟶ B` and `q : F ⟶ C` be quotient covering maps of actions of groups `G` and `H`, in the
sense of Mathlib's `IsQuotientCoveringMap`, and let `f : E ⟶ F` be a continuous map equivariant
along a group homomorphism `φ : G →* H` and lying over `b : B ⟶ C` (`p ≫ b = f ≫ q`).

Over each point `x` of `B`, restricting `f` to the fibre `p ⁻¹' {x}` lands in `q ⁻¹' {b x}` and
intertwines the `G`-action with the `H`-action restricted along `φ`. Because covering-space
monodromy commutes with maps of covers over maps of bases (`IsCoveringMap.coe_monodromy_map`), the
resulting linear maps on formal sums of sheets assemble into a natural transformation
`IsQuotientCoveringMap.permutationRepFunctorResMap` from `hG.permutationRepFunctor k` to the
restriction along `φ` of `hH.permutationRepFunctor k` pulled back along `b`.

For a commutative ring `k`, representations `A` of `G` and `M` of `H`, and a compatible morphism
`ψ : A ⟶ Rep.res φ M`, applying `MonoidHom.coinvariantsTensorMap φ ψ` fibrewise gives a morphism
of local coefficient systems on `B`
(`IsQuotientCoveringMap.associatedLocalSystemChangeOfGroupsMap`):

`L_A ⟶ b^* L_M`,

sending the class of `a ⊗ [e]` over `x` to the class of `ψ a ⊗ [f e]` over `b x`.

When `A = Rep.res φ M` and `ψ` is the identity, this morphism is an isomorphism of local systems
(`IsQuotientCoveringMap.associatedLocalSystemPullbackIso`), for *every* group homomorphism
`φ : G →* H` with no injectivity or surjectivity hypothesis. Even when `f` is neither injective nor
surjective on sheets, choosing any sheet `e ∈ p ⁻¹' {x}` identifies `(Rep.res φ M ⊗ k[p⁻¹ x])_G`
with `M` and `f e ∈ q ⁻¹' {b x}` identifies `(M ⊗ k[q⁻¹ (b x)])_H` with `M`
(`IsQuotientCoveringMap.associatedLocalSystemFiberIso`), and in these sheet coordinates the map on
tensor coinvariants is the identity on `M`. For general `ψ : A ⟶ Rep.res φ M`, the change-of-groups
morphism factors as `associatedLocalSystemMap` followed by the pullback isomorphism
(`IsQuotientCoveringMap.associatedLocalSystemChangeOfGroupsMap_eq`).

## Main definitions

* `IsQuotientCoveringMap.fiberRepresentationResHom`: the equivariant map on fibre permutation
  representations over a point.
* `IsQuotientCoveringMap.permutationRepFunctorResMap`: the natural transformation of fibre
  permutation representation functors along a map of quotient covers.
* `IsQuotientCoveringMap.associatedLocalSystemChangeOfGroupsMap`: the morphism `L_A ⟶ b^* L_M` of
  associated local systems induced by `ψ : A ⟶ Rep.res φ M`.
* `IsQuotientCoveringMap.associatedLocalSystemPullbackIso`: the canonical isomorphism
  `L_{Res(φ)(M)} ≅ b^* L_M` of local coefficient systems on `B`.

## Main results

* `IsQuotientCoveringMap.associatedLocalSystemChangeOfGroupsMap_app_comp_fiberIso_hom`:
  compatibility of the change-of-groups morphism with sheet coordinates.
* `IsQuotientCoveringMap.associatedLocalSystemChangeOfGroupsMap_eq`: factorization of the
  change-of-groups morphism through `associatedLocalSystemPullbackIso`.
* `IsQuotientCoveringMap.associatedLocalSystemChangeOfGroupsMap_id`,
  `IsQuotientCoveringMap.associatedLocalSystemChangeOfGroupsMap_comp`: identity and composition
  laws for maps of quotient covers.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections III.1 and III.8.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G)

/-- A map `f : E ⟶ F` over `b : B ⟶ C` sends the fibre of `p` over `x` into the fibre of `q` over
`b.hom x`. -/
private def coverFiberMap {F C : TopCat.{u}} {q : F ⟶ C} (f : E ⟶ F) (b : B ⟶ C)
    (hb : p ≫ b = f ≫ q) (x : B) (e : p ⁻¹' {x}) : q ⁻¹' {b.hom x} :=
  ⟨f e.1,
    have he : p e.1 = x := e.2
    (ConcreteCategory.congr_hom hb e.1).symm.trans (congrArg b.hom he)⟩

/-- The fibre map intertwines the `G`-action on `p ⁻¹' {x}` with the `H`-action on
`q ⁻¹' {b.hom x}` restricted along `φ`. -/
private lemma coverFiberMap_smul
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (x : B) (g : G) (e : p ⁻¹' {x}) :
    letI := hG.mulActionFiber x
    letI := hH.mulActionFiber (b.hom x)
    coverFiberMap f b hb x (g • e) = φ g • coverFiberMap f b hb x e := by
  let := hG.mulActionFiber x
  let := hH.mulActionFiber (b.hom x)
  exact Subtype.ext (hf g e)

section Permutation

variable (k : Type u) [Ring k]

/-- The morphism of fibre permutation representations over `x` induced by an equivariant map of
quotient covers along `φ : G →* H`. -/
def fiberRepresentationResHom
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (x : B) :
    Rep.of (hG.fiberRepresentation k x) ⟶
      Rep.res φ (Rep.of (hH.fiberRepresentation k (b.hom x))) :=
  Rep.ofHom
    { toLinearMap := Finsupp.lmapDomain k k (coverFiberMap f b hb x)
      isIntertwining' g := by
        let := hG.mulActionFiber x
        let := hH.mulActionFiber (b.hom x)
        refine Finsupp.lhom_ext fun e r ↦ ?_
        simp [coverFiberMap_smul hG hH f hf b hb x g e] }

/-- On a basis vector at sheet `e`, the fibre representation map evaluates to the basis vector at
its image sheet `e'` over `b.hom x`. -/
theorem fiberRepresentationResHom_hom_single
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    (x : B) (e : p ⁻¹' {x}) (e' : q ⁻¹' {b.hom x}) (he : f e = e') (r : k) :
    (hG.fiberRepresentationResHom k hH f hf b hb x).hom (Finsupp.single e r) =
      Finsupp.single e' r := by
  obtain rfl : e' = coverFiberMap f b hb x e := Subtype.ext he.symm
  simp [fiberRepresentationResHom]

/-- Along the identity map of a quotient cover, `fiberRepresentationResHom` is the identity linear
map on formal sums of sheets. -/
theorem fiberRepresentationResHom_id_hom_apply (x : B) (v : p ⁻¹' {x} →₀ k) :
    (hG.fiberRepresentationResHom k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ rfl) (𝟙 B) rfl
      x).hom v = v := by
  refine LinearMap.congr_fun (f := (hG.fiberRepresentationResHom k hG (𝟙 E) (φ := MonoidHom.id G)
      (fun _ _ ↦ rfl) (𝟙 B) rfl x).hom.toLinearMap) (g := LinearMap.id)
    (Finsupp.lhom_ext fun e r ↦ ?_) v
  exact hG.fiberRepresentationResHom_hom_single k hG (𝟙 E) (fun _ _ ↦ rfl) (𝟙 B) rfl x e e rfl r

/-- Along a composite of maps of quotient covers, `fiberRepresentationResHom` is the composite of
the two linear maps on formal sums of sheets. -/
theorem fiberRepresentationResHom_comp_hom_apply
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H)
    {D W : TopCat.{u}} {r : D ⟶ W} {K : Type u} [Group K] [MulAction K D]
    (hK : IsQuotientCoveringMap r K)
    {φ : G →* H} {φ' : H →* K}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e) (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    (f' : F ⟶ D) (hf' : ∀ h y, f' (h • y) = φ' h • f' y) (b' : C ⟶ W) (hb' : q ≫ b' = f' ≫ r)
    (x : B) (v : p ⁻¹' {x} →₀ k) :
    (hG.fiberRepresentationResHom k hK (f ≫ f') (φ := φ'.comp φ)
        (fun g e ↦ by simp [hf, hf']) (b ≫ b')
        (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]) x).hom v =
      (hH.fiberRepresentationResHom k hK f' hf' b' hb' (b.hom x)).hom
        ((hG.fiberRepresentationResHom k hH f hf b hb x).hom v) := by
  refine LinearMap.congr_fun
    (f := (hG.fiberRepresentationResHom k hK (f ≫ f') (φ := φ'.comp φ)
      (fun g e ↦ by simp [hf, hf']) (b ≫ b')
      (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]) x).hom.toLinearMap)
    (g := (hH.fiberRepresentationResHom k hK f' hf' b' hb' (b.hom x)).hom.toLinearMap ∘ₗ
      (hG.fiberRepresentationResHom k hH f hf b hb x).hom.toLinearMap)
    (Finsupp.lhom_ext fun e s ↦ ?_) v
  let e₁ : q ⁻¹' {b.hom x} := coverFiberMap f b hb x e
  let e₂ : r ⁻¹' {(b ≫ b').hom x} := coverFiberMap f' b' hb' (b.hom x) e₁
  rw [LinearMap.comp_apply]
  exact (hG.fiberRepresentationResHom_hom_single k hK (f ≫ f') _ (b ≫ b') _ x e e₂ rfl s).trans <|
    (hH.fiberRepresentationResHom_hom_single k hK f' hf' b' hb' (b.hom x) e₁ e₂ rfl s).symm.trans
      (congrArg (hH.fiberRepresentationResHom k hK f' hf' b' hb' (b.hom x)).hom
        (hG.fiberRepresentationResHom_hom_single k hH f hf b hb x e e₁ rfl s).symm)

/-- An equivariant map of quotient covers induces a natural transformation from the fibre
permutation representation functor of the source cover to the restricted functor of the target
cover pulled back along `b`. -/
def permutationRepFunctorResMap
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) :
    hG.permutationRepFunctor k ⟶
      FundamentalGroupoid.map b.hom ⋙ hH.permutationRepFunctor k ⋙ Rep.resFunctor φ where
  app x := hG.fiberRepresentationResHom k hH f hf b hb x.as
  naturality {x y} γ := by
    refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| Finsupp.lhom_ext fun e r ↦ ?_
    have hqf : ⇑q ∘ ⇑f.hom = ⇑b.hom ∘ ⇑p.hom :=
      funext fun z ↦ (ConcreteCategory.congr_hom hb z).symm
    have hmon : coverFiberMap f b hb y.as (hG.isCoveringMap.monodromy γ e) =
        hH.isCoveringMap.monodromy (γ.map b.hom) (coverFiberMap f b hb x.as e) :=
      Subtype.ext (hG.isCoveringMap.coe_monodromy_map hH.isCoveringMap hqf γ e
        (coverFiberMap f b hb x.as e) rfl).symm
    -- Expose the underlying linear maps of the composite morphisms of representations so that
    -- `Finsupp` evaluation applies on the single-sheet generator.
    change (hG.fiberRepresentationResHom k hH f hf b hb y.as).hom
        (((hG.permutationRepFunctor k).map γ).hom (Finsupp.single e r)) =
      ((hH.permutationRepFunctor k).map ((FundamentalGroupoid.map b.hom).map γ)).hom
        ((hG.fiberRepresentationResHom k hH f hf b hb x.as).hom (Finsupp.single e r))
    rw [permutationRepFunctor_map_hom_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      hG.fiberRepresentationResHom_hom_single k hH f hf b hb y.as _
        (coverFiberMap f b hb y.as (hG.isCoveringMap.monodromy γ e)) rfl,
      hG.fiberRepresentationResHom_hom_single k hH f hf b hb x.as e
        (coverFiberMap f b hb x.as e) rfl]
    exact ((hH.permutationRepFunctor_map_hom_apply k ((FundamentalGroupoid.map b.hom).map γ)
        (Finsupp.single (coverFiberMap f b hb x.as e) r)).trans <|
      (Finsupp.mapDomain_single (a := coverFiberMap f b hb x.as e) (b := r)).trans
        (congrArg (Finsupp.single · r) hmon.symm)).symm

@[simp]
theorem permutationRepFunctorResMap_app
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (x : FundamentalGroupoid B) :
    (hG.permutationRepFunctorResMap k hH f hf b hb).app x =
      hG.fiberRepresentationResHom k hH f hf b hb x.as :=
  (rfl)

end Permutation

section AssociatedLocalSystem

variable (k : Type u) [CommRing k]

/-- **Change of groups on associated local coefficient systems.** Given quotient covers `p : E ⟶ B`
and `q : F ⟶ C`, a map `f : E ⟶ F` equivariant along `φ : G →* H` over `b : B ⟶ C`, and a
compatible morphism of representations `ψ : A ⟶ Rep.res φ M`, this is the induced morphism of local
coefficient systems `L_A ⟶ b^* L_M` on `B`, sending `⟦a ⊗ [e]⟧` to `⟦ψ a ⊗ [f e]⟧`. -/
def associatedLocalSystemChangeOfGroupsMap
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M) :
    hG.associatedLocalSystem k A ⟶
      (LocalCoefficientSystem.pullback b.hom).obj (hH.associatedLocalSystem k M) where
  app x := φ.coinvariantsTensorMap ψ ((hG.permutationRepFunctorResMap k hH f hf b hb).app x)
  naturality {x y} γ :=
    φ.coinvariantsTensorMap_naturality ψ
      ((hG.permutationRepFunctorResMap k hH f hf b hb).app x)
      ((hG.permutationRepFunctorResMap k hH f hf b hb).app y)
      ((hG.permutationRepFunctor k).map γ)
      ((hH.permutationRepFunctor k).map ((FundamentalGroupoid.map b.hom).map γ))
      ((hG.permutationRepFunctorResMap k hH f hf b hb).naturality γ).symm

/-- Over `x`, the change-of-groups morphism of associated local systems is the tensor-coinvariant
map induced by `ψ` and `fiberRepresentationResHom`. -/
@[simp]
theorem associatedLocalSystemChangeOfGroupsMap_app
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M) (x : FundamentalGroupoid B) :
    (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ).app x =
      φ.coinvariantsTensorMap ψ (hG.fiberRepresentationResHom k hH f hf b hb x.as) :=
  (rfl)

/-- On a pure tensor class `⟦a ⊗ v⟧`, the change-of-groups morphism sends `a` via `ψ` and pushes
formal sums of sheets forward via `fiberRepresentationResHom`. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
theorem associatedLocalSystemChangeOfGroupsMap_app_coinvariantsTensorMk
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M)
    (x : FundamentalGroupoid B) (a : A) (v : p ⁻¹' {x.as} →₀ k) :
    ((hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ).app x).hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a v) =
      Rep.coinvariantsTensorMk M (Rep.of (hH.fiberRepresentation k (b.hom x.as))) (ψ.hom a)
        ((hG.fiberRepresentationResHom k hH f hf b hb x.as).hom v) :=
  φ.coinvariantsTensorMap_mk ψ (hG.fiberRepresentationResHom k hH f hf b hb x.as) a v

/-- On a tensor class at a single sheet `e`, the change-of-groups morphism sends `⟦a ⊗ r[e]⟧` to
`⟦ψ a ⊗ r[e']⟧`, where `e'` is the image sheet `f e` over `b.hom x.as`. -/
theorem associatedLocalSystemChangeOfGroupsMap_app_coinvariantsTensorMk_single
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M)
    (x : FundamentalGroupoid B) (a : A)
    (e : p ⁻¹' {x.as}) (e' : q ⁻¹' {b.hom x.as}) (he : f e = e') (r : k) :
    ((hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ).app x).hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
          (Finsupp.single e r)) =
      Rep.coinvariantsTensorMk M (Rep.of (hH.fiberRepresentation k (b.hom x.as))) (ψ.hom a)
        (Finsupp.single e' r) :=
  (φ.coinvariantsTensorMap_mk ψ
    (hG.fiberRepresentationResHom k hH f hf b hb x.as) a (Finsupp.single e r)).trans
    (congrArg
      (Rep.coinvariantsTensorMk M (Rep.of (hH.fiberRepresentation k (b.hom x.as))) (ψ.hom a))
      (hG.fiberRepresentationResHom_hom_single k hH f hf b hb x.as e e' he r))

/-- Under the sheet identifications at `e` and its image `e'` over `b.hom x.as`, the
change-of-groups morphism of associated local systems is the underlying linear map of `ψ`. -/
@[reassoc]
theorem associatedLocalSystemChangeOfGroupsMap_app_comp_fiberIso_hom
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M)
    {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as})
    (e' : q ⁻¹' {((FundamentalGroupoid.map b.hom).obj x).as}) (he : f e = e') :
    ((hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ).app x) ≫
        (hH.associatedLocalSystemFiberIso k M e').hom =
      (hG.associatedLocalSystemFiberIso k A e).hom ≫ ModuleCat.ofHom ψ.hom.toLinearMap := by
  apply (cancel_epi (hG.associatedLocalSystemFiberIso k A e).inv).1
  rw [Iso.inv_hom_id_assoc]
  refine ModuleCat.hom_ext <| LinearMap.ext fun a ↦ ?_
  -- The pulled-back fibre over `x` and the fibre over `b.hom x.as` agree by definition of
  -- `pullback`, so the composite is evaluated in term mode rather than via `rw`.
  exact (congrArg ((hH.associatedLocalSystemFiberIso k M e').hom.hom ∘
      ((hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ).app x).hom)
    (hG.associatedLocalSystemFiberIso_inv_apply k A e a)).trans <|
    (congrArg (hH.associatedLocalSystemFiberIso k M e').hom.hom
      (hG.associatedLocalSystemChangeOfGroupsMap_app_coinvariantsTensorMk_single k hH f hf b hb ψ
        x a e e' he 1)).trans <|
    (hH.associatedLocalSystemFiberIso_hom_coinvariantsTensorMk k M e' e' (ψ.hom a) 1).trans
      (by simp)

/-- For the restricted representation `Rep.res φ M`, the change-of-groups morphism is an
isomorphism on every fibre: in sheet coordinates at any sheet `e` over `x` and its image `f e` over
`b.hom x.as`, it is the identity on `M`. -/
instance isIso_associatedLocalSystemChangeOfGroupsMap_id
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (M : Rep.{u} k H) :
    IsIso (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb (𝟙 (Rep.res φ M))) := by
  have : ∀ x : FundamentalGroupoid B,
      IsIso ((hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb
        (𝟙 (Rep.res φ M))).app x) := fun x ↦ by
    obtain ⟨e₀, he₀⟩ := hG.surjective x.as
    let e : p ⁻¹' {x.as} := ⟨e₀, he₀⟩
    let e' : q ⁻¹' {((FundamentalGroupoid.map b.hom).obj x).as} := coverFiberMap f b hb x.as e
    let f_app : (hG.associatedLocalSystem k (Rep.res φ M)).obj x ⟶
        (hH.associatedLocalSystem k M).obj ((FundamentalGroupoid.map b.hom).obj x) :=
      (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb (𝟙 (Rep.res φ M))).app x
    have hf_app : IsIso f_app := by
      have hcomp : f_app =
          (hG.associatedLocalSystemFiberIso k (Rep.res φ M) e).hom ≫
            (hH.associatedLocalSystemFiberIso k M e').inv := by
        rw [Iso.eq_comp_inv]
        exact (hG.associatedLocalSystemChangeOfGroupsMap_app_comp_fiberIso_hom k hH f hf b hb
          (𝟙 (Rep.res φ M)) e e' rfl).trans (Category.comp_id _)
      rw [hcomp]
      infer_instance
    exact hf_app
  exact NatIso.isIso_of_isIso_app _

/-- **Pullback of associated local coefficient systems along a map of quotient covers.** For an
equivariant map `f : E ⟶ F` along any group homomorphism `φ : G →* H` lying over `b : B ⟶ C` and a
representation `M` of `H`, the local system on `B` associated to the restricted representation
`Rep.res φ M` is canonically isomorphic to the pullback along `b` of the local system on `C`
associated to `M`. -/
def associatedLocalSystemPullbackIso
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (M : Rep.{u} k H) :
    hG.associatedLocalSystem k (Rep.res φ M) ≅
      (LocalCoefficientSystem.pullback b.hom).obj (hH.associatedLocalSystem k M) :=
  asIso (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb (𝟙 (Rep.res φ M)))

/-- The forward morphism of `associatedLocalSystemPullbackIso` is the change-of-groups morphism for
the identity of `Rep.res φ M`. -/
@[simp]
theorem associatedLocalSystemPullbackIso_hom
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (M : Rep.{u} k H) :
    (hG.associatedLocalSystemPullbackIso k hH f hf b hb M).hom =
      hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb (𝟙 (Rep.res φ M)) :=
  (rfl)

/-- On a tensor class at a single sheet `e`, the pullback isomorphism sends `⟦m ⊗ r[e]⟧` to
`⟦m ⊗ r[e']⟧`, where `e'` is the image sheet `f e` over `b.hom x.as`. -/
theorem associatedLocalSystemPullbackIso_hom_app_coinvariantsTensorMk_single
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (M : Rep.{u} k H)
    (x : FundamentalGroupoid B) (m : M)
    (e : p ⁻¹' {x.as}) (e' : q ⁻¹' {b.hom x.as}) (he : f e = e') (r : k) :
    ((hG.associatedLocalSystemPullbackIso k hH f hf b hb M).hom.app x).hom
        (Rep.coinvariantsTensorMk (Rep.res φ M) (Rep.of (hG.fiberRepresentation k x.as)) m
          (Finsupp.single e r)) =
      Rep.coinvariantsTensorMk M (Rep.of (hH.fiberRepresentation k (b.hom x.as))) m
        (Finsupp.single e' r) :=
  hG.associatedLocalSystemChangeOfGroupsMap_app_coinvariantsTensorMk_single k hH f hf b hb
    (𝟙 (Rep.res φ M)) x m e e' he r

/-- On a tensor class at the image sheet `e'`, the inverse pullback isomorphism sends
`⟦m ⊗ r[e']⟧` back to `⟦m ⊗ r[e]⟧`. -/
theorem associatedLocalSystemPullbackIso_inv_app_coinvariantsTensorMk_single
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (M : Rep.{u} k H)
    (x : FundamentalGroupoid B) (m : M)
    (e : p ⁻¹' {x.as}) (e' : q ⁻¹' {b.hom x.as}) (he : f e = e') (r : k) :
    ((hG.associatedLocalSystemPullbackIso k hH f hf b hb M).inv.app x).hom
        (Rep.coinvariantsTensorMk M (Rep.of (hH.fiberRepresentation k (b.hom x.as))) m
          (Finsupp.single e' r)) =
      Rep.coinvariantsTensorMk (Rep.res φ M) (Rep.of (hG.fiberRepresentation k x.as)) m
        (Finsupp.single e r) := by
  apply (ModuleCat.mono_iff_injective
    ((hG.associatedLocalSystemPullbackIso k hH f hf b hb M).hom.app x)).mp inferInstance
  have hcancel := (hG.associatedLocalSystemPullbackIso k hH f hf b hb M).inv_hom_id_app x
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcancel) _).trans
    (hG.associatedLocalSystemPullbackIso_hom_app_coinvariantsTensorMk_single k hH f hf b hb M
      x m e e' he r).symm

/-- **Factorization of change-of-groups morphisms of local systems.** For `ψ : A ⟶ Rep.res φ M`,
the change-of-groups morphism `L_A ⟶ b^* L_M` is the coefficient map induced by `ψ` followed by
the pullback isomorphism `L_{Res(φ)(M)} ≅ b^* L_M`. -/
theorem associatedLocalSystemChangeOfGroupsMap_eq
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M) :
    hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ =
      hG.associatedLocalSystemMap k ψ ≫
        (hG.associatedLocalSystemPullbackIso k hH f hf b hb M).hom := by
  refine NatTrans.ext <| funext fun x ↦
    Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a v ↦ ?_)
  exact (φ.coinvariantsTensorMap_mk ψ
      ((hG.permutationRepFunctorResMap k hH f hf b hb).app x) a v).trans <|
    (φ.coinvariantsTensorMap_mk (𝟙 (Rep.res φ M))
      ((hG.permutationRepFunctorResMap k hH f hf b hb).app x) (ψ.hom a) v).symm.trans
      (congrArg ((hG.associatedLocalSystemPullbackIso k hH f hf b hb M).hom.app x).hom
        (hG.associatedLocalSystemMap_app_coinvariantsTensorMk k ψ x a v).symm)

/-- Precomposing the change-of-groups morphism with a morphism of `G`-representations composes the
compatible coefficient map on the left. -/
@[simp, reassoc]
theorem associatedLocalSystemMap_comp_changeOfGroupsMap
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A A' : Rep.{u} k G} {M : Rep.{u} k H} (α : A' ⟶ A) (ψ : A ⟶ Rep.res φ M) :
    hG.associatedLocalSystemMap k α ≫
        hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ =
      hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb (α ≫ ψ) := by
  rw [hG.associatedLocalSystemChangeOfGroupsMap_eq k hH f hf b hb ψ,
    hG.associatedLocalSystemChangeOfGroupsMap_eq k hH f hf b hb (α ≫ ψ),
    associatedLocalSystemMap_comp_assoc]

/-- Postcomposing the change-of-groups morphism with a pulled-back morphism of `H`-representations
composes the compatible coefficient map with the restricted morphism on the right. -/
@[simp, reassoc]
theorem associatedLocalSystemChangeOfGroupsMap_comp_pullback_map
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {M M' : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M) (β : M ⟶ M') :
    hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ ≫
        (LocalCoefficientSystem.pullback b.hom).map (hH.associatedLocalSystemMap k β) =
      hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb
        (ψ ≫ (Rep.resFunctor φ).map β) := by
  refine NatTrans.ext <| funext fun x ↦
    Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a v ↦ ?_)
  -- Evaluate both composites on a pure tensor class `⟦a ⊗ v⟧`.
  change (((hH.associatedLocalSystemMap k β).app ((FundamentalGroupoid.map b.hom).obj x)).hom
      (((hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ).app x).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a v))) =
    ((hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb
      (ψ ≫ (Rep.resFunctor φ).map β)).app x).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a v)
  exact (congrArg ((hH.associatedLocalSystemMap k β).app _).hom
    (φ.coinvariantsTensorMap_mk ψ
      ((hG.permutationRepFunctorResMap k hH f hf b hb).app x) a v)).trans
    ((hH.associatedLocalSystemMap_app_coinvariantsTensorMk k β _ (ψ.hom a) _).trans
      (φ.coinvariantsTensorMap_mk (ψ ≫ (Rep.resFunctor φ).map β)
        ((hG.permutationRepFunctorResMap k hH f hf b hb).app x) a v).symm)

/-- `associatedLocalSystemPullbackIso` is natural in the representation `M` of `H`. -/
@[reassoc]
theorem associatedLocalSystemPullbackIso_hom_naturality
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {M M' : Rep.{u} k H} (β : M ⟶ M') :
    hG.associatedLocalSystemMap k ((Rep.resFunctor φ).map β) ≫
        (hG.associatedLocalSystemPullbackIso k hH f hf b hb M').hom =
      (hG.associatedLocalSystemPullbackIso k hH f hf b hb M).hom ≫
        (LocalCoefficientSystem.pullback b.hom).map (hH.associatedLocalSystemMap k β) := by
  rw [associatedLocalSystemPullbackIso_hom, associatedLocalSystemPullbackIso_hom,
    associatedLocalSystemMap_comp_changeOfGroupsMap,
    associatedLocalSystemChangeOfGroupsMap_comp_pullback_map, Category.id_comp, Category.comp_id]

end AssociatedLocalSystem

section Functoriality

variable (k : Type u) [CommRing k]

/-- Along the identity map of a quotient cover, the change-of-groups morphism for `ψ : A ⟶ A'`
followed by `pullbackIdIso` is `associatedLocalSystemMap k ψ`. -/
@[simp]
theorem associatedLocalSystemChangeOfGroupsMap_id {A A' : Rep.{u} k G} (ψ : A ⟶ A') :
    hG.associatedLocalSystemChangeOfGroupsMap k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ rfl)
        (𝟙 B) rfl ψ ≫
      (LocalCoefficientSystem.pullbackIdIso.{u, u, u} B).hom.app
        (hG.associatedLocalSystem k A') =
      hG.associatedLocalSystemMap k ψ := by
  refine NatTrans.ext <| funext fun x ↦
    Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a v ↦ ?_)
  -- `pullback (.id B)` and `𝟭 _` agree on fibres only by definition, so the identity component of
  -- `pullbackIdIso` is applied in term mode on a pure tensor class `⟦a ⊗ v⟧`.
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (LocalCoefficientSystem.pullbackIdIso_hom_app_app B (hG.associatedLocalSystem k A') x))
    (((hG.associatedLocalSystemChangeOfGroupsMap k hG (𝟙 E) (φ := MonoidHom.id G)
      (fun _ _ ↦ rfl) (𝟙 B) rfl ψ).app x).hom
      (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a v))).trans <|
    ((MonoidHom.id G).coinvariantsTensorMap_mk ψ
      ((hG.permutationRepFunctorResMap k hG (𝟙 E) (fun _ _ ↦ rfl) (𝟙 B) rfl).app x) a v).trans <|
    (congrArg (Rep.coinvariantsTensorMk A' ((hG.permutationRepFunctor k).obj x) (ψ.hom a))
      (hG.fiberRepresentationResHom_id_hom_apply k x.as v)).trans
      (hG.associatedLocalSystemMap_app_coinvariantsTensorMk k ψ x a v).symm

/-- Along a composite of maps of quotient covers, the change-of-groups morphism factors as the
composite of the two change-of-groups morphisms, up to `pullbackCompIso`. -/
theorem associatedLocalSystemChangeOfGroupsMap_comp
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H)
    {D W : TopCat.{u}} {r : D ⟶ W} {K : Type u} [Group K] [MulAction K D]
    (hK : IsQuotientCoveringMap r K)
    {φ : G →* H} {φ' : H →* K}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e) (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    (f' : F ⟶ D) (hf' : ∀ h y, f' (h • y) = φ' h • f' y) (b' : C ⟶ W) (hb' : q ≫ b' = f' ≫ r)
    {A : Rep.{u} k G} {M : Rep.{u} k H} {N : Rep.{u} k K}
    (ψ : A ⟶ Rep.res φ M) (ψ' : M ⟶ Rep.res φ' N) :
    hG.associatedLocalSystemChangeOfGroupsMap k hK (f ≫ f') (φ := φ'.comp φ)
        (fun g e ↦ by simp [hf, hf']) (b ≫ b')
        (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc])
        (ψ ≫ (Rep.resFunctor φ).map ψ') =
      hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ ≫
        (LocalCoefficientSystem.pullback b.hom).map
          (hH.associatedLocalSystemChangeOfGroupsMap k hK f' hf' b' hb' ψ') ≫
        (LocalCoefficientSystem.pullbackCompIso.{u, u, u, u} b.hom b'.hom).inv.app
          (hK.associatedLocalSystem k N) := by
  refine NatTrans.ext <| funext fun x ↦
    Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a v ↦ ?_)
  -- As in `associatedLocalSystemChangeOfGroupsMap_id`, `pullbackCompIso` acts between fibres that
  -- agree by definition, so both composites are evaluated on `⟦a ⊗ v⟧` in term mode.
  have hrhs := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (LocalCoefficientSystem.pullbackCompIso_inv_app_app b.hom b'.hom
        (hK.associatedLocalSystem k N) x))
    ((((LocalCoefficientSystem.pullback b.hom).map
      (hH.associatedLocalSystemChangeOfGroupsMap k hK f' hf' b' hb' ψ')).app x).hom
      (((hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ).app x).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a v)))
  exact ((φ'.comp φ).coinvariantsTensorMap_mk (ψ ≫ (Rep.resFunctor φ).map ψ')
      ((hG.permutationRepFunctorResMap k hK (f ≫ f') (fun g e ↦ by simp [hf, hf']) (b ≫ b')
        _).app x) a v).trans <|
    (congrArg (Rep.coinvariantsTensorMk N
        ((hK.permutationRepFunctor k).obj ((FundamentalGroupoid.map (b ≫ b').hom).obj x))
        ((ψ ≫ (Rep.resFunctor φ).map ψ').hom a))
      (hG.fiberRepresentationResHom_comp_hom_apply k hH hK f hf b hb f' hf' b' hb' x.as
        v)).trans <|
    (φ'.coinvariantsTensorMap_mk ψ'
      ((hH.permutationRepFunctorResMap k hK f' hf' b' hb').app
        ((FundamentalGroupoid.map b.hom).obj x)) (ψ.hom a)
      (((hG.permutationRepFunctorResMap k hH f hf b hb).app x).hom v)).symm.trans <|
    (congrArg (((LocalCoefficientSystem.pullback b.hom).map
        (hH.associatedLocalSystemChangeOfGroupsMap k hK f' hf' b' hb' ψ')).app x).hom
      (φ.coinvariantsTensorMap_mk ψ
        ((hG.permutationRepFunctorResMap k hH f hf b hb).app x) a v).symm).trans hrhs.symm

/-- Along a composite of maps of quotient covers, `associatedLocalSystemPullbackIso` factors as
the composite of the two pullback isomorphisms, up to `pullbackCompIso`. -/
theorem associatedLocalSystemPullbackIso_hom_comp
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H)
    {D W : TopCat.{u}} {r : D ⟶ W} {K : Type u} [Group K] [MulAction K D]
    (hK : IsQuotientCoveringMap r K)
    {φ : G →* H} {φ' : H →* K}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e) (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    (f' : F ⟶ D) (hf' : ∀ h y, f' (h • y) = φ' h • f' y) (b' : C ⟶ W) (hb' : q ≫ b' = f' ≫ r)
    (N : Rep.{u} k K) :
    (hG.associatedLocalSystemPullbackIso k hK (f ≫ f') (φ := φ'.comp φ)
        (fun g e ↦ by simp [hf, hf']) (b ≫ b')
        (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]) N).hom =
      (hG.associatedLocalSystemPullbackIso k hH f hf b hb (Rep.res φ' N)).hom ≫
        (LocalCoefficientSystem.pullback b.hom).map
          (hH.associatedLocalSystemPullbackIso k hK f' hf' b' hb' N).hom ≫
        (LocalCoefficientSystem.pullbackCompIso.{u, u, u, u} b.hom b'.hom).inv.app
          (hK.associatedLocalSystem k N) := by
  have h := hG.associatedLocalSystemChangeOfGroupsMap_comp k hH hK f hf b hb f' hf' b' hb'
    (𝟙 (Rep.res (φ'.comp φ) N)) (𝟙 (Rep.res φ' N))
  rw [(Rep.resFunctor φ).map_id, Category.id_comp] at h
  exact h

end Functoriality

end IsQuotientCoveringMap
