/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Exact

/-!
# Pullback and functoriality of associated local coefficient systems

Let `p : E ⟶ B` and `q : F ⟶ C` be quotient covering maps of actions of groups `G` and `H`, in the
sense of Mathlib's `IsQuotientCoveringMap`, and let `f : E ⟶ F` be a continuous map equivariant
along a group homomorphism `φ : G →* H` and lying over `b : B ⟶ C` (`p ≫ b = f ≫ q`).

For a commutative ring `k`, representations `A` of `G` and `D` of `H`, and a compatible morphism
`ξ : A ⟶ Rep.res φ D`, `IsQuotientCoveringMap.associatedLocalSystemMapOver` is the induced morphism
of local coefficient systems on `B`:

`L_A ⟶ b^* L_D`,

sending the class of `a ⊗ [e]` over `x` to the class of `ξ a ⊗ [f e]` over `b x`. Choosing any
sheet `e ∈ p ⁻¹' {x}` identifies `(A ⊗ k[p⁻¹ x])_G` with `A` and its image `f e ∈ q ⁻¹' {b x}`
identifies `(D ⊗ k[q⁻¹ (b x)])_H` with `D` (`IsQuotientCoveringMap.associatedLocalSystemFiberIso`),
and in these sheet coordinates the morphism is the underlying linear map of `ξ`
(`IsQuotientCoveringMap.associatedLocalSystemMapOver_app_comp_fiberIso_hom`).

When `A = Rep.res φ D` and `ξ` is the identity, this morphism is an isomorphism of local systems
(`IsQuotientCoveringMap.associatedLocalSystemPullbackIso`), for *every* group homomorphism
`φ : G →* H` with no injectivity or surjectivity hypothesis: even when `f` is neither injective nor
surjective on sheets, in sheet coordinates at `e` and `f e` the fibre map is the identity on `D`.
For general `ξ : A ⟶ Rep.res φ D`, the morphism `associatedLocalSystemMapOver` factors as
`associatedLocalSystemMap` followed by the pullback isomorphism
(`IsQuotientCoveringMap.associatedLocalSystemMapOver_eq`).

## Main definitions

* `IsQuotientCoveringMap.associatedLocalSystemPullbackIso`: the canonical isomorphism
  `L_{Res(φ)(D)} ≅ b^* L_D` of local coefficient systems on `B`.

## Main results

* `IsQuotientCoveringMap.associatedLocalSystemMapOver_app_comp_fiberIso_hom`:
  compatibility of `associatedLocalSystemMapOver` with sheet coordinates.
* `IsQuotientCoveringMap.isIso_associatedLocalSystemMapOver_id`: for `𝟙 (Rep.res φ D)`,
  `associatedLocalSystemMapOver` is an isomorphism of local systems.
* `IsQuotientCoveringMap.associatedLocalSystemMapOver_eq`: factorization of
  `associatedLocalSystemMapOver` through `associatedLocalSystemPullbackIso`.
* `IsQuotientCoveringMap.associatedLocalSystemMapOver_id`,
  `IsQuotientCoveringMap.associatedLocalSystemMapOver_comp`: identity and composition laws for
  maps of quotient covers.

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

section Permutation

variable (k : Type u) [Ring k]

/-- Along the identity map of a quotient cover, `permutationRepMap` acts as the identity on formal
sums of sheets over each point. -/
theorem permutationRepMap_id_app_hom_apply (x : FundamentalGroupoid B) (v : p ⁻¹' {x.as} →₀ k) :
    ((hG.permutationRepMap k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ rfl) (𝟙 B) rfl).app x).hom
      v = v := by
  induction v using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add v₁ v₂ h₁ h₂ => exact (map_add _ v₁ v₂).trans (congrArg₂ (· + ·) h₁ h₂)
  | single e r =>
    exact (hG.permutationRepMap_app_hom_single k hG (φ := MonoidHom.id G) (𝟙 E) (fun _ _ ↦ rfl)
      (𝟙 B) rfl x e r).trans
      (congrArg (Finsupp.single · r) (Subtype.ext (CommSq.fiberMap_apply_coe _ _ _)))

/-- Along a composite of maps of quotient covers, `permutationRepMap` acts on formal sums of sheets
as the composite of the two fibre maps. -/
theorem permutationRepMap_comp_app_hom_apply
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H)
    {S W : TopCat.{u}} {r : S ⟶ W} {K : Type u} [Group K] [MulAction K S]
    (hK : IsQuotientCoveringMap r K)
    {φ : G →* H} {φ' : H →* K}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e) (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    (f' : F ⟶ S) (hf' : ∀ h y, f' (h • y) = φ' h • f' y) (b' : C ⟶ W) (hb' : q ≫ b' = f' ≫ r)
    (x : FundamentalGroupoid B) (v : p ⁻¹' {x.as} →₀ k) :
    ((hG.permutationRepMap k hK (f ≫ f') (φ := φ'.comp φ)
        (fun g e ↦ by simp [hf, hf']) (b ≫ b')
        (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc])).app x).hom v =
      ((hH.permutationRepMap k hK f' hf' b' hb').app ((FundamentalGroupoid.map b.hom).obj x)).hom
        (((hG.permutationRepMap k hH f hf b hb).app x).hom v) := by
  have hcomp : p ≫ (b ≫ b') = (f ≫ f') ≫ r := by
    rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]
  let m₁ := ((hG.permutationRepMap k hK (f ≫ f') (φ := φ'.comp φ)
    (fun g e ↦ by simp [hf, hf']) (b ≫ b') hcomp).app x).hom
  let m₂ := ((hG.permutationRepMap k hH f hf b hb).app x).hom
  let m₃ := ((hH.permutationRepMap k hK f' hf' b' hb').app
    ((FundamentalGroupoid.map b.hom).obj x)).hom
  induction v using Finsupp.induction_linear with
  | zero =>
    exact (map_zero m₁).trans ((map_zero m₃).symm.trans (congrArg m₃ (map_zero m₂).symm))
  | add v₁ v₂ h₁ h₂ =>
    exact (map_add m₁ v₁ v₂).trans <| (congrArg₂ (· + ·) h₁ h₂).trans <|
      (map_add m₃ (m₂ v₁) (m₂ v₂)).symm.trans (congrArg m₃ (map_add m₂ v₁ v₂).symm)
  | single e s =>
    have he : (CommSq.mk hcomp.symm).fiberMap x.as e =
        (CommSq.mk hb'.symm).fiberMap (b x.as) ((CommSq.mk hb.symm).fiberMap x.as e) :=
      Subtype.ext <| (CommSq.fiberMap_apply_coe (CommSq.mk hcomp.symm) x.as e).trans <|
        (congrArg f'.hom (CommSq.fiberMap_apply_coe (CommSq.mk hb.symm) x.as e).symm).trans
          (CommSq.fiberMap_apply_coe (CommSq.mk hb'.symm) (b x.as) _).symm
    exact (hG.permutationRepMap_app_hom_single k hK (φ := φ'.comp φ) (f ≫ f') _ (b ≫ b')
      hcomp x e s).trans <|
      (congrArg (Finsupp.single · s) he).trans <|
      (hH.permutationRepMap_app_hom_single k hK f' hf' b' hb'
        ((FundamentalGroupoid.map b.hom).obj x) ((CommSq.mk hb.symm).fiberMap x.as e) s).symm.trans
        (congrArg m₃ (hG.permutationRepMap_app_hom_single k hH f hf b hb x e s).symm)

end Permutation

section AssociatedLocalSystem

variable (k : Type u) [CommRing k]

/-- On a pure tensor class `⟦a ⊗ v⟧`, `associatedLocalSystemMapOver` sends `a` via `ξ` and pushes
formal sums of sheets forward via `permutationRepMap`. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
theorem associatedLocalSystemMapOver_app_coinvariantsTensorMk
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {D : Rep.{u} k H} (ξ : A ⟶ Rep.res φ D)
    (x : FundamentalGroupoid B) (a : A) (v : p ⁻¹' {x.as} →₀ k) :
    ((hG.associatedLocalSystemMapOver k hH f hf b hb ξ).app x).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a v) =
      Rep.coinvariantsTensorMk D
        ((hH.permutationRepFunctor k).obj ((FundamentalGroupoid.map b.hom).obj x)) (ξ.hom a)
        (((hG.permutationRepMap k hH f hf b hb).app x).hom v) := by
  let L := ((hG.associatedLocalSystemMapOver k hH f hf b hb ξ).app x).hom
  let mk₁ := Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a
  let mk₂ := Rep.coinvariantsTensorMk D
    ((hH.permutationRepFunctor k).obj ((FundamentalGroupoid.map b.hom).obj x)) (ξ.hom a)
  let P := ((hG.permutationRepMap k hH f hf b hb).app x).hom
  induction v using Finsupp.induction_linear with
  | zero =>
    exact (congrArg L (map_zero mk₁)).trans <|
      (map_zero L).trans ((map_zero mk₂).symm.trans (congrArg mk₂ (map_zero P).symm))
  | add v₁ v₂ h₁ h₂ =>
    exact (congrArg L (map_add mk₁ v₁ v₂)).trans <| (map_add L (mk₁ v₁) (mk₁ v₂)).trans <|
      (congrArg₂ (· + ·) h₁ h₂).trans <|
      (map_add mk₂ (P v₁) (P v₂)).symm.trans (congrArg mk₂ (map_add P v₁ v₂).symm)
  | single e r =>
    exact (hG.associatedLocalSystemMapOver_app_mk_single k hH f hf b hb ξ x a e r).trans
      (congrArg mk₂ (hG.permutationRepMap_app_hom_single k hH f hf b hb x e r).symm)

/-- Under the sheet identifications at `e` and its image `e'` over `b.hom x.as`,
`associatedLocalSystemMapOver` is the underlying linear map of `ξ`. -/
@[reassoc]
theorem associatedLocalSystemMapOver_app_comp_fiberIso_hom
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {D : Rep.{u} k H} (ξ : A ⟶ Rep.res φ D)
    {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as})
    (e' : q ⁻¹' {((FundamentalGroupoid.map b.hom).obj x).as}) (he : f e = e') :
    ((hG.associatedLocalSystemMapOver k hH f hf b hb ξ).app x) ≫
        (hH.associatedLocalSystemFiberIso k D e').hom =
      (hG.associatedLocalSystemFiberIso k A e).hom ≫ ModuleCat.ofHom ξ.hom.toLinearMap := by
  obtain rfl : e' = (CommSq.mk hb.symm).fiberMap x.as e :=
    Subtype.ext (he.symm.trans (CommSq.fiberMap_apply_coe _ _ _).symm)
  apply (cancel_epi (hG.associatedLocalSystemFiberIso k A e).inv).1
  rw [Iso.inv_hom_id_assoc]
  refine ModuleCat.hom_ext <| LinearMap.ext fun a ↦ ?_
  -- The pulled-back fibre over `x` and the fibre over `b.hom x.as` agree by definition of
  -- `pullback`, so the composite is evaluated in term mode rather than via `rw`.
  let e₁ := (CommSq.mk hb.symm).fiberMap x.as e
  exact (congrArg ((hH.associatedLocalSystemFiberIso k D e₁).hom.hom ∘
      ((hG.associatedLocalSystemMapOver k hH f hf b hb ξ).app x).hom)
    (hG.associatedLocalSystemFiberIso_inv_apply k A e a)).trans <|
    (congrArg (hH.associatedLocalSystemFiberIso k D e₁).hom.hom
      (hG.associatedLocalSystemMapOver_app_mk_single k hH f hf b hb ξ x a e 1)).trans <|
    (hH.associatedLocalSystemFiberIso_hom_coinvariantsTensorMk k D e₁ e₁ (ξ.hom a) 1).trans
      (by simp)

/-- For the restricted representation `Rep.res φ D`, `associatedLocalSystemMapOver` is an
isomorphism on every fibre: in sheet coordinates at any sheet `e` over `x` and its image `f e` over
`b.hom x.as`, it is the identity on `D`. -/
instance isIso_associatedLocalSystemMapOver_id
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (D : Rep.{u} k H) :
    IsIso (hG.associatedLocalSystemMapOver k hH f hf b hb (𝟙 (Rep.res φ D))) := by
  have : ∀ x : FundamentalGroupoid B,
      IsIso ((hG.associatedLocalSystemMapOver k hH f hf b hb
        (𝟙 (Rep.res φ D))).app x) := fun x ↦ by
    obtain ⟨e₀, he₀⟩ := hG.surjective x.as
    let e : p ⁻¹' {x.as} := ⟨e₀, he₀⟩
    let e' : q ⁻¹' {((FundamentalGroupoid.map b.hom).obj x).as} :=
      (CommSq.mk hb.symm).fiberMap x.as e
    let f_app : (hG.associatedLocalSystem k (Rep.res φ D)).obj x ⟶
        (hH.associatedLocalSystem k D).obj ((FundamentalGroupoid.map b.hom).obj x) :=
      (hG.associatedLocalSystemMapOver k hH f hf b hb (𝟙 (Rep.res φ D))).app x
    have hf_app : IsIso f_app := by
      have hcomp : f_app =
          (hG.associatedLocalSystemFiberIso k (Rep.res φ D) e).hom ≫
            (hH.associatedLocalSystemFiberIso k D e').inv := by
        rw [Iso.eq_comp_inv]
        exact (hG.associatedLocalSystemMapOver_app_comp_fiberIso_hom k hH f hf b hb
          (𝟙 (Rep.res φ D)) e e'
          (CommSq.fiberMap_apply_coe (CommSq.mk hb.symm) x.as e).symm).trans
          (Category.comp_id _)
      rw [hcomp]
      infer_instance
    exact hf_app
  exact NatIso.isIso_of_isIso_app _

/-- **Pullback of associated local coefficient systems along a map of quotient covers.** For an
equivariant map `f : E ⟶ F` along any group homomorphism `φ : G →* H` lying over `b : B ⟶ C` and a
representation `D` of `H`, the local system on `B` associated to the restricted representation
`Rep.res φ D` is canonically isomorphic to the pullback along `b` of the local system on `C`
associated to `D`. -/
def associatedLocalSystemPullbackIso
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (D : Rep.{u} k H) :
    hG.associatedLocalSystem k (Rep.res φ D) ≅
      (LocalCoefficientSystem.pullback b.hom).obj (hH.associatedLocalSystem k D) :=
  asIso (hG.associatedLocalSystemMapOver k hH f hf b hb (𝟙 (Rep.res φ D)))

/-- The forward morphism of `associatedLocalSystemPullbackIso` is `associatedLocalSystemMapOver`
for the identity of `Rep.res φ D`. -/
@[simp]
theorem associatedLocalSystemPullbackIso_hom
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (D : Rep.{u} k H) :
    (hG.associatedLocalSystemPullbackIso k hH f hf b hb D).hom =
      hG.associatedLocalSystemMapOver k hH f hf b hb (𝟙 (Rep.res φ D)) :=
  (rfl)

/-- On a tensor class at a single sheet `e`, the pullback isomorphism sends `⟦d ⊗ r[e]⟧` to
`⟦d ⊗ r[f e]⟧`. -/
@[simp↓]
theorem associatedLocalSystemPullbackIso_hom_app_mk_single
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (D : Rep.{u} k H)
    (x : FundamentalGroupoid B) (d : D) (e : p ⁻¹' {x.as}) (r : k) :
    ((hG.associatedLocalSystemPullbackIso k hH f hf b hb D).hom.app x).hom
        (Rep.coinvariantsTensorMk (Rep.res φ D) ((hG.permutationRepFunctor k).obj x) d
          (Finsupp.single e r)) =
      Rep.coinvariantsTensorMk D
        ((hH.permutationRepFunctor k).obj ((FundamentalGroupoid.map b.hom).obj x)) d
        (Finsupp.single ((CommSq.mk hb.symm).fiberMap x.as e) r) :=
  hG.associatedLocalSystemMapOver_app_mk_single k hH f hf b hb (𝟙 (Rep.res φ D)) x d e r

/-- On a tensor class at the image sheet `f e`, the inverse pullback isomorphism sends
`⟦d ⊗ r[f e]⟧` back to `⟦d ⊗ r[e]⟧`. -/
@[simp↓]
theorem associatedLocalSystemPullbackIso_inv_app_mk_single
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (D : Rep.{u} k H)
    (x : FundamentalGroupoid B) (d : D) (e : p ⁻¹' {x.as}) (r : k) :
    ((hG.associatedLocalSystemPullbackIso k hH f hf b hb D).inv.app x).hom
        (Rep.coinvariantsTensorMk D
          ((hH.permutationRepFunctor k).obj ((FundamentalGroupoid.map b.hom).obj x)) d
          (Finsupp.single ((CommSq.mk hb.symm).fiberMap x.as e) r)) =
      Rep.coinvariantsTensorMk (Rep.res φ D) ((hG.permutationRepFunctor k).obj x) d
        (Finsupp.single e r) := by
  apply (ModuleCat.mono_iff_injective
    ((hG.associatedLocalSystemPullbackIso k hH f hf b hb D).hom.app x)).mp inferInstance
  have hcancel := (hG.associatedLocalSystemPullbackIso k hH f hf b hb D).inv_hom_id_app x
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcancel) _).trans
    (hG.associatedLocalSystemPullbackIso_hom_app_mk_single k hH f hf b hb D x d e r).symm

/-- **Factorization of change-of-groups morphisms of local systems.** For `ξ : A ⟶ Rep.res φ D`,
`associatedLocalSystemMapOver` is the coefficient map induced by `ξ` followed by the pullback
isomorphism `L_{Res(φ)(D)} ≅ b^* L_D`. -/
theorem associatedLocalSystemMapOver_eq
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {D : Rep.{u} k H} (ξ : A ⟶ Rep.res φ D) :
    hG.associatedLocalSystemMapOver k hH f hf b hb ξ =
      hG.associatedLocalSystemMap k ξ ≫
        (hG.associatedLocalSystemPullbackIso k hH f hf b hb D).hom := by
  refine NatTrans.ext <| funext fun x ↦
    Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a v ↦ ?_)
  exact (hG.associatedLocalSystemMapOver_app_coinvariantsTensorMk k hH f hf b hb ξ x a v).trans <|
    (hG.associatedLocalSystemMapOver_app_coinvariantsTensorMk k hH f hf b hb
      (𝟙 (Rep.res φ D)) x (ξ.hom a) v).symm.trans
      (congrArg ((hG.associatedLocalSystemPullbackIso k hH f hf b hb D).hom.app x).hom
        (hG.associatedLocalSystemMap_app_coinvariantsTensorMk k ξ x a v).symm)

/-- Precomposing `associatedLocalSystemMapOver` with a morphism of `G`-representations composes the
compatible coefficient map on the left. -/
@[simp, reassoc]
theorem associatedLocalSystemMap_comp_mapOver
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A A' : Rep.{u} k G} {D : Rep.{u} k H} (α : A' ⟶ A) (ξ : A ⟶ Rep.res φ D) :
    hG.associatedLocalSystemMap k α ≫
        hG.associatedLocalSystemMapOver k hH f hf b hb ξ =
      hG.associatedLocalSystemMapOver k hH f hf b hb (α ≫ ξ) := by
  rw [hG.associatedLocalSystemMapOver_eq k hH f hf b hb ξ,
    hG.associatedLocalSystemMapOver_eq k hH f hf b hb (α ≫ ξ),
    associatedLocalSystemMap_comp_assoc]

/-- Postcomposing `associatedLocalSystemMapOver` with a pulled-back morphism of `H`-representations
composes the compatible coefficient map with the restricted morphism on the right. -/
@[simp, reassoc]
theorem associatedLocalSystemMapOver_comp_pullback_map
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {A : Rep.{u} k G} {D D' : Rep.{u} k H} (ξ : A ⟶ Rep.res φ D) (β : D ⟶ D') :
    hG.associatedLocalSystemMapOver k hH f hf b hb ξ ≫
        (LocalCoefficientSystem.pullback b.hom).map (hH.associatedLocalSystemMap k β) =
      hG.associatedLocalSystemMapOver k hH f hf b hb
        (ξ ≫ (Rep.resFunctor φ).map β) := by
  refine NatTrans.ext <| funext fun x ↦
    Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a v ↦ ?_)
  -- Evaluate both composites on a pure tensor class `⟦a ⊗ v⟧`.
  change (((hH.associatedLocalSystemMap k β).app ((FundamentalGroupoid.map b.hom).obj x)).hom
      (((hG.associatedLocalSystemMapOver k hH f hf b hb ξ).app x).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a v))) =
    ((hG.associatedLocalSystemMapOver k hH f hf b hb
      (ξ ≫ (Rep.resFunctor φ).map β)).app x).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a v)
  exact (congrArg ((hH.associatedLocalSystemMap k β).app _).hom
    (hG.associatedLocalSystemMapOver_app_coinvariantsTensorMk k hH f hf b hb ξ x a v)).trans
    ((hH.associatedLocalSystemMap_app_coinvariantsTensorMk k β _ (ξ.hom a) _).trans
      (hG.associatedLocalSystemMapOver_app_coinvariantsTensorMk k hH f hf b hb
        (ξ ≫ (Rep.resFunctor φ).map β) x a v).symm)

/-- `associatedLocalSystemPullbackIso` is natural in the representation `D` of `H`. -/
@[reassoc]
theorem associatedLocalSystemPullbackIso_hom_naturality
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    {D D' : Rep.{u} k H} (β : D ⟶ D') :
    hG.associatedLocalSystemMap k ((Rep.resFunctor φ).map β) ≫
        (hG.associatedLocalSystemPullbackIso k hH f hf b hb D').hom =
      (hG.associatedLocalSystemPullbackIso k hH f hf b hb D).hom ≫
        (LocalCoefficientSystem.pullback b.hom).map (hH.associatedLocalSystemMap k β) := by
  rw [associatedLocalSystemPullbackIso_hom, associatedLocalSystemPullbackIso_hom,
    associatedLocalSystemMap_comp_mapOver,
    associatedLocalSystemMapOver_comp_pullback_map, Category.id_comp, Category.comp_id]

end AssociatedLocalSystem

section Functoriality

variable (k : Type u) [CommRing k]

/-- Along the identity map of a quotient cover, `associatedLocalSystemMapOver` for `ξ : A ⟶ A'`
followed by `pullbackIdIso` is `associatedLocalSystemMap k ξ`. -/
@[simp]
theorem associatedLocalSystemMapOver_id {A A' : Rep.{u} k G} (ξ : A ⟶ A') :
    hG.associatedLocalSystemMapOver k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ rfl)
        (𝟙 B) rfl ξ ≫
      (LocalCoefficientSystem.pullbackIdIso.{u, u, u} B).hom.app
        (hG.associatedLocalSystem k A') =
      hG.associatedLocalSystemMap k ξ := by
  refine NatTrans.ext <| funext fun x ↦
    Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a v ↦ ?_)
  -- `pullback (.id B)` and `𝟭 _` agree on fibres only by definition, so the identity component of
  -- `pullbackIdIso` is applied in term mode on a pure tensor class `⟦a ⊗ v⟧`.
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (LocalCoefficientSystem.pullbackIdIso_hom_app_app B (hG.associatedLocalSystem k A') x))
    (((hG.associatedLocalSystemMapOver k hG (𝟙 E) (φ := MonoidHom.id G)
      (fun _ _ ↦ rfl) (𝟙 B) rfl ξ).app x).hom
      (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a v))).trans <|
    (hG.associatedLocalSystemMapOver_app_coinvariantsTensorMk k hG (φ := MonoidHom.id G)
      (𝟙 E) (fun _ _ ↦ rfl) (𝟙 B) rfl ξ x a v).trans <|
    (congrArg (Rep.coinvariantsTensorMk A' ((hG.permutationRepFunctor k).obj x) (ξ.hom a))
      (hG.permutationRepMap_id_app_hom_apply k x v)).trans
      (hG.associatedLocalSystemMap_app_coinvariantsTensorMk k ξ x a v).symm

/-- Along a composite of maps of quotient covers, `associatedLocalSystemMapOver` factors as the
composite of the two morphisms, up to `pullbackCompIso`. -/
theorem associatedLocalSystemMapOver_comp
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H)
    {S W : TopCat.{u}} {r : S ⟶ W} {K : Type u} [Group K] [MulAction K S]
    (hK : IsQuotientCoveringMap r K)
    {φ : G →* H} {φ' : H →* K}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e) (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    (f' : F ⟶ S) (hf' : ∀ h y, f' (h • y) = φ' h • f' y) (b' : C ⟶ W) (hb' : q ≫ b' = f' ≫ r)
    {A : Rep.{u} k G} {D : Rep.{u} k H} {V : Rep.{u} k K}
    (ξ : A ⟶ Rep.res φ D) (ζ : D ⟶ Rep.res φ' V) :
    hG.associatedLocalSystemMapOver k hK (f ≫ f') (φ := φ'.comp φ)
        (fun g e ↦ by simp [hf, hf']) (b ≫ b')
        (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc])
        (ξ ≫ (Rep.resFunctor φ).map ζ) =
      hG.associatedLocalSystemMapOver k hH f hf b hb ξ ≫
        (LocalCoefficientSystem.pullback b.hom).map
          (hH.associatedLocalSystemMapOver k hK f' hf' b' hb' ζ) ≫
        (LocalCoefficientSystem.pullbackCompIso.{u, u, u, u} b.hom b'.hom).inv.app
          (hK.associatedLocalSystem k V) := by
  refine NatTrans.ext <| funext fun x ↦
    Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a v ↦ ?_)
  -- As in `associatedLocalSystemMapOver_id`, `pullbackCompIso` acts between fibres that agree by
  -- definition, so both composites are evaluated on `⟦a ⊗ v⟧` in term mode.
  have hrhs := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (LocalCoefficientSystem.pullbackCompIso_inv_app_app b.hom b'.hom
        (hK.associatedLocalSystem k V) x))
    ((((LocalCoefficientSystem.pullback b.hom).map
      (hH.associatedLocalSystemMapOver k hK f' hf' b' hb' ζ)).app x).hom
      (((hG.associatedLocalSystemMapOver k hH f hf b hb ξ).app x).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a v)))
  exact (hG.associatedLocalSystemMapOver_app_coinvariantsTensorMk k hK (φ := φ'.comp φ)
      (f ≫ f') (fun g e ↦ by simp [hf, hf']) (b ≫ b') _
      (ξ ≫ (Rep.resFunctor φ).map ζ) x a v).trans <|
    (congrArg (Rep.coinvariantsTensorMk V
        ((hK.permutationRepFunctor k).obj ((FundamentalGroupoid.map (b ≫ b').hom).obj x))
        ((ξ ≫ (Rep.resFunctor φ).map ζ).hom a))
      (hG.permutationRepMap_comp_app_hom_apply k hH hK f hf b hb f' hf' b' hb' x v)).trans <|
    (hH.associatedLocalSystemMapOver_app_coinvariantsTensorMk k hK f' hf' b' hb' ζ
      ((FundamentalGroupoid.map b.hom).obj x) (ξ.hom a)
      (((hG.permutationRepMap k hH f hf b hb).app x).hom v)).symm.trans <|
    (congrArg (((LocalCoefficientSystem.pullback b.hom).map
        (hH.associatedLocalSystemMapOver k hK f' hf' b' hb' ζ)).app x).hom
      (hG.associatedLocalSystemMapOver_app_coinvariantsTensorMk k hH f hf b hb ξ x a v).symm).trans
      hrhs.symm

/-- Along a composite of maps of quotient covers, `associatedLocalSystemPullbackIso` factors as
the composite of the two pullback isomorphisms, up to `pullbackCompIso`. -/
theorem associatedLocalSystemPullbackIso_hom_comp
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H)
    {S W : TopCat.{u}} {r : S ⟶ W} {K : Type u} [Group K] [MulAction K S]
    (hK : IsQuotientCoveringMap r K)
    {φ : G →* H} {φ' : H →* K}
    (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e) (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
    (f' : F ⟶ S) (hf' : ∀ h y, f' (h • y) = φ' h • f' y) (b' : C ⟶ W) (hb' : q ≫ b' = f' ≫ r)
    (V : Rep.{u} k K) :
    (hG.associatedLocalSystemPullbackIso k hK (f ≫ f') (φ := φ'.comp φ)
        (fun g e ↦ by simp [hf, hf']) (b ≫ b')
        (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]) V).hom =
      (hG.associatedLocalSystemPullbackIso k hH f hf b hb (Rep.res φ' V)).hom ≫
        (LocalCoefficientSystem.pullback b.hom).map
          (hH.associatedLocalSystemPullbackIso k hK f' hf' b' hb' V).hom ≫
        (LocalCoefficientSystem.pullbackCompIso.{u, u, u, u} b.hom b'.hom).inv.app
          (hK.associatedLocalSystem k V) := by
  have h := hG.associatedLocalSystemMapOver_comp k hH hK f hf b hb f' hf' b' hb'
    (𝟙 (Rep.res (φ'.comp φ) V)) (𝟙 (Rep.res φ' V))
  rw [(Rep.resFunctor φ).map_id, Category.id_comp] at h
  exact h

end Functoriality

end IsQuotientCoveringMap
