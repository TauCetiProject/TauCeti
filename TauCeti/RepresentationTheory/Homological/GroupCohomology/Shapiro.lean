/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import TauCeti.RepresentationTheory.Homological.Resolution
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Resolution

public import TauCeti.RepresentationTheory.Coinduced
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Shapiro's isomorphism is restriction followed by evaluation

For a subgroup `S ≤ G` and an `S`-representation `A`, Mathlib's Shapiro isomorphism
`groupCohomology.coindIso A n : Hⁿ(G, Coind_S^G A) ≅ Hⁿ(S, A)` is constructed through `Ext`: it
compares the bar resolution of `S` with the restriction to `S` of the bar resolution of `G`. This
file identifies it with an explicit map. It is the change-of-group map

`Hⁿ(G, Coind_S^G A) ⟶ Hⁿ(S, Res_S Coind_S^G A) ⟶ Hⁿ(S, A)`,

restriction to `S` followed by the counit `Res_S Coind_S^G A ⟶ A` of restriction–coinduction,
which evaluates a function `G → A` at `1`. On inhomogeneous cochains it sends
`c : Gⁿ → Coind_S^G A` to `(s₁, …, sₙ) ↦ c (s₁, …, sₙ) 1`.

The explicit form is what makes Shapiro's isomorphism usable against the rest of Mathlib's
functoriality: it is a `groupCohomology.map`, so it composes with restriction and coefficient maps
by `groupCohomology.map_comp`. In particular it is what identifies restriction with the unit of the
adjunction under Shapiro's lemma, the step that turns the counit of the finite-index adjunction into
a corestriction satisfying `cor ∘ res = [G : S]`.

## Main results

* `TauCeti.groupCohomology.coindIso_hom`: `(coindIso A n).hom` is
  `groupCohomology.map S.subtype ((resCoindAdjunction k S.subtype).counit.app A) n`.
* `TauCeti.groupCohomology.coindIso_hom_naturality`: consequently, Shapiro's isomorphism is natural
  in the coefficients.
* `TauCeti.groupCohomology.map_resCoindToHom_comp_coindIso_hom`: on the adjunct `B ⟶ Coind_S^G A`
  of `f : Res_S B ⟶ A`, Shapiro's isomorphism is the change-of-group map induced by `f`.
* `groupCohomology.map_id_eq_zero_iff_of_comp_eq_resCoindToHom`: a morphism into a
  representation coinduced from `S ≤ G` kills a class of `Hⁿ(G, -)` exactly when its adjunct does
  on `S`, read through a bijection `f : S → Γ` and a homomorphism `Γ → G` restricting along `f` to
  the inclusion of `S`.
* `TauCeti.groupCohomology.map_unit_comp_coindIso_hom`: read through Shapiro's isomorphism,
  restriction to `S` is the map induced by the unit `B ⟶ Coind_S^G Res_S B`.

* `TauCeti.groupCohomology.δ_comp_coindIso_hom`: Shapiro's isomorphism intertwines the
  connecting maps of a short exact sequence and its coinduction.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter III, §6 (Shapiro's lemma) and Chapter III, §8.
-/

public section

open CategoryTheory Finsupp Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (A : Rep.{u} k S)

/-- The inhomogeneous-cochain map underlying Shapiro's isomorphism, evaluated on a cochain and a
tuple: going from `Gⁿ → Coind_S^G A` to `Hom_G(Gⁿ ⊗ k[G], Coind_S^G A)`, to
`Hom_S(Res_S (Gⁿ ⊗ k[G]), A)`, to `Hom_S(Sⁿ ⊗ k[S], A)` along the bar resolution of `S`, and back to
`Sⁿ → A` gives `c ↦ ((s₁, …, sₙ) ↦ c (s₁, …, sₙ) 1)`. -/
private theorem shapiroCochains_apply (i : ℕ) (c : (Fin i → G) → coind S.subtype A)
    (s : Fin i → S) :
    ((inhomogeneousCochainsIso A).inv.f i).hom
      ((((HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda k (Rep k S)).obj A).rightOp.mapHomologicalComplex _).map
          (TauCeti.Rep.barComplex.resChainMap (k := k) S.subtype)).op).f i).hom
      (((linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).inv.f i).hom
      (((inhomogeneousCochainsIso (coind S.subtype A)).hom.f i).hom c))) s =
      (c (S.subtype ∘ s)).1 1 := by
  -- Unfolding the two cochain isomorphisms, the value is the Shapiro adjunct of `freeLift c`
  -- evaluated on the image of the basis element `s` under the bar resolution along `S ≤ G`.
  refine Eq.trans (b := ((resCoindHomEquiv.{u} S.subtype (free k G (Fin i → G)) A).symm
    (freeLift k G (coind S.subtype A) c)).hom
      (((TauCeti.Rep.barComplex.resChainMap (k := k) S.subtype).f i).hom
        (single s (MonoidAlgebra.single 1 1)))) rfl ?_
  rw [TauCeti.Rep.barComplex.resChainMap_f, TauCeti.Rep.barComplex.resHom_single]
  simp

/-- The chain-level form of `coindIso_hom`. -/
private theorem shapiroCochains :
    (inhomogeneousCochainsIso (coind S.subtype A)).hom ≫
      (linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).inv ≫
      (HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda k (Rep k S)).obj A).rightOp.mapHomologicalComplex _).map
          (TauCeti.Rep.barComplex.resChainMap (k := k) S.subtype)).op ≫
      (inhomogeneousCochainsIso A).inv =
    cochainsMap S.subtype ((resCoindAdjunction k S.subtype).counit.app A) :=
  HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext (LinearMap.ext fun c =>
    funext fun s => shapiroCochains_apply S A i c s)

/-- **Shapiro's isomorphism is restriction followed by evaluation at `1`.** The isomorphism
`Hⁿ(G, Coind_S^G A) ≅ Hⁿ(S, A)` of `groupCohomology.coindIso` is the change-of-group map along
`S ≤ G` induced by the counit `Res_S Coind_S^G A ⟶ A` of restriction–coinduction. -/
theorem coindIso_hom (n : ℕ) :
    (coindIso A n).hom = map S.subtype ((resCoindAdjunction k S.subtype).counit.app A) n := by
  -- `resFunctor` is pinned: with `k` and its universe left open, instance search for the
  -- restricted resolution first fails slowly.
  -- `coindIso` is by definition the homology of the Shapiro cochain isomorphism followed by the
  -- comparison, through `Ext`, of the restricted bar resolution of `G` with the bar resolution
  -- of `S`. The unfolding is taken from `Iso.trans_hom`, not restated and proved by `rfl`:
  -- restated, its `Ext` objects carry fresh instance terms and the kernel unfolds `Ext` to match.
  have e : (coindIso A n).hom = _ := Iso.trans_hom _ _
  rw [e, Iso.symm_hom, TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap A
    ((resFunctor.{u} (k := k) S.subtype).mapProjectiveResolution (barResolution k G))
    (TauCeti.Rep.barComplex.resChainMap S.subtype)
    (TauCeti.Rep.barComplex.resChainMap_f_zero_comp_π S.subtype) n]
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n)
      ((Category.assoc _ _ _).trans (shapiroCochains S A)))

/-- **Shapiro's isomorphism is natural in the coefficients**: for a morphism `φ : A ⟶ B` of
`S`-representations, it intertwines the maps induced by `Coind_S^G φ` and by `φ`. -/
@[reassoc]
theorem coindIso_hom_naturality {B : Rep.{u} k S} (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id G) ((coindFunctor k S.subtype).map φ) n ≫ (coindIso B n).hom =
      (coindIso A n).hom ≫ map (MonoidHom.id S) φ n := by
  rw [coindIso_hom, coindIso_hom, ← map_comp, ← map_comp]
  exact map_congr rfl (congrArg (fun f => f.hom.toLinearMap)
    ((resCoindAdjunction k S.subtype).counit.naturality φ)).symm n

/-- **Shapiro's isomorphism on an adjunct.** For a `G`-representation `B` and a morphism
`f : Res_S B ⟶ A`, the map induced by the adjunct `B ⟶ Coind_S^G A` of `f`, followed by Shapiro's
isomorphism, is the change-of-group map `Hⁿ(G, B) ⟶ Hⁿ(S, A)` induced by `f` along `S ≤ G`. -/
theorem map_resCoindToHom_comp_coindIso_hom {B : Rep.{u} k G} (f : res S.subtype B ⟶ A)
    (n : ℕ) :
    map (MonoidHom.id G) (resCoindToHom S.subtype B A f) n ≫ (coindIso A n).hom =
      map S.subtype f n := by
  rw [coindIso_hom, ← map_comp]
  -- The adjunct followed by the counit is `f` again.
  congr 1
  exact ((resCoindAdjunction k S.subtype).homEquiv_counit _ _ _).symm.trans
    ((resCoindHomEquiv.{u} S.subtype B A).toEquiv.symm_apply_apply f)

/-- **Restriction through Shapiro's lemma.** For a `G`-representation `B`, the map induced by the
unit `B ⟶ Coind_S^G Res_S B` of restriction–coinduction, followed by Shapiro's isomorphism, is
restriction `Hⁿ(G, B) ⟶ Hⁿ(S, Res_S B)`. -/
theorem map_unit_comp_coindIso_hom (B : Rep.{u} k G) (n : ℕ) :
    map (MonoidHom.id G) ((resCoindAdjunction k S.subtype).unit.app B) n ≫
      (coindIso (res S.subtype B) n).hom = map S.subtype (𝟙 (res S.subtype B)) n := by
  rw [coindIso_hom, ← map_comp, (resCoindAdjunction k S.subtype).left_triangle_components B]
  -- `(MonoidHom.id G).comp S.subtype` is `S.subtype` by definition.
  rfl

/-- Shapiro's isomorphism intertwines the connecting maps of a short exact sequence and
its coinduction to the ambient group. -/
@[reassoc]
theorem δ_comp_coindIso_hom {X : ShortComplex (Rep k S)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ (hX.map_of_exact (coindFunctor k S.subtype)) i j hij ≫ (coindIso X.X₁ j).hom =
      (coindIso X.X₃ i).hom ≫ δ hX i j hij := by
  rw [coindIso_hom, coindIso_hom]
  exact TauCeti.groupCohomology.δ_naturality S.subtype
    (hX.map_of_exact (coindFunctor k S.subtype)) hX
    { τ₁ := (resCoindAdjunction k S.subtype).counit.app X.X₁
      τ₂ := (resCoindAdjunction k S.subtype).counit.app X.X₂
      τ₃ := (resCoindAdjunction k S.subtype).counit.app X.X₃
      comm₁₂ := ((resCoindAdjunction k S.subtype).counit.naturality X.f).symm
      comm₂₃ := ((resCoindAdjunction k S.subtype).counit.naturality X.g).symm } i j hij

end TauCeti.groupCohomology

namespace groupCohomology

open TauCeti.groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

/-- **Shapiro's lemma through an identification of the subgroup.** Let `S ≤ G`, let `f : S →* Γ` be
bijective and `r : Γ →* G` restrict back to the inclusion of `S` (`r (f s) = s`), and let
`φ : Res_r X ⟶ B`. Suppose that `u : X ⟶ M`, followed by an isomorphism
`M ≅ Coind_S^G (Res_f B)`, is the adjunct of `φ` read on `S`. Then `u` kills a class of
`Hⁿ(G, X)` exactly when `φ` kills it along `r`. For the semi-local units at a place of a number
field, `Γ` is the local Galois group and `f` identifies the decomposition group with it. -/
theorem map_id_eq_zero_iff_of_comp_eq_resCoindToHom {Γ : Type u} [Group Γ] {X M : Rep.{u} k G}
    {B : Rep.{u} k Γ} {f : S →* Γ} (hf : Function.Bijective f) {r : Γ →* G}
    (hr : ∀ s, r (f s) = s) (φ : res r X ⟶ B) (ψ : res S.subtype X ⟶ res f B)
    (hψ : ψ.hom.toLinearMap = φ.hom.toLinearMap) (u : X ⟶ M)
    (e : M ≅ coind S.subtype (res f B)) (hu : u ≫ e.hom = resCoindToHom S.subtype X (res f B) ψ)
    (n : ℕ) (x : groupCohomology X n) :
    map (MonoidHom.id G) u n x = 0 ↔ map r φ n x = 0 := by
  -- Shapiro's lemma: `ψ` on `Hⁿ(S, -)` is `u` followed by two isomorphisms
  have hS : map S.subtype ψ n x = (coindIso (res f B) n).hom
      (map (MonoidHom.id G) e.hom n (map (MonoidHom.id G) u n x)) := by
    rw [← map_resCoindToHom_comp_coindIso_hom, ← hu, map_id_comp, ModuleCat.comp_apply,
      ModuleCat.comp_apply]
  -- `ψ` is `φ` along `r`, followed by the isomorphism along the bijection `f`
  have hD : map S.subtype ψ n = map r φ n ≫ map f (𝟙 (res f B)) n :=
    (map_congr (MonoidHom.ext fun s ↦ (hr s).symm) hψ n).trans (map_comp r f φ (𝟙 _) n)
  have hc : Function.Injective (coindIso (res f B) n).hom :=
    (coindIso (res f B) n).toLinearEquiv.injective
  have he : Function.Injective (map (MonoidHom.id G) e.hom n) :=
    ((functor k G n).mapIso e).toLinearEquiv.injective
  -- the map along the bijection `f` is the `hom` of Mathlib's `mapIso` for the inverse of `f`
  have hd : Function.Injective (map f (𝟙 (res f B)) n) :=
    (mapIso (MulEquiv.ofBijective f hf).symm (LinearEquiv.refl k B.V)
      (fun _ ↦ LinearMap.ext fun _ ↦ by simp) n (A := res f B)).toLinearEquiv.injective
  refine (map_eq_zero_iff _ he).symm.trans <| (map_eq_zero_iff _ hc).symm.trans ?_
  rw [← hS, hD]
  exact map_eq_zero_iff _ hd

end groupCohomology
