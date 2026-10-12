/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.GroupTheory.Index.Basic
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup
import TauCeti.RepresentationTheory.Homological.GroupHomology.Induced
import TauCeti.RepresentationTheory.Homological.GroupHomology.LowDegree
import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Delta
import TauCeti.RepresentationTheory.Induction.DimensionShift

/-!
# The transfer along group isomorphisms

For a finite-index subgroup `S` of a group `G` and a group isomorphism `e : G ≃* G'` carrying `S`
onto `S'`, the transfer `Hₙ(G, M) ⟶ Hₙ(S, Res_S M)` is compatible with `e`.

This moves transfer computations between isomorphic groups and their corresponding subgroups.
For example, the Galois group of a layer of a class formation is identified with its image in a
larger Galois group. Tate restriction below degree `-1` is the transfer read along that
identification, so its functoriality along a tower of layers needs this compatibility.

## Main results

* `TauCeti.groupHomology.map_comp_transfer_congrOfMapEq`: the transfer is compatible with a group
  isomorphism and a compatible map of coefficients.
-/

public section

universe u

open CategoryTheory Rep

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {R G G' : Type u} [CommRing R] [Group G] [Group G']

variable (e : G ≃* G') {S : Subgroup G} {S' : Subgroup G'} (he : S.map (e : G →* G') = S')

-- The inductive step of `transfer_res_equiv`. This dimension-shifting argument, and the degree-zero
-- case of `transfer_res_equiv`, are adapted from `transfer_trans` in `Transfer/Trans.lean`.
private theorem transfer_res_equiv_succ [S.FiniteIndex]
    {Y : ShortComplex (Rep.{u} R G')} (hY : Y.ShortExact) (n : ℕ)
    (hY₂ : Limits.IsZero (groupHomology (res S'.subtype Y.X₂) (n + 1))) :
    haveI := S.finiteIndex_of_map_eq (e : G →* G') e.surjective he
    (transfer (res (e : G →* G') Y.X₁) S n ≫ map (Subgroup.congrOfMapEq e he : S →* S')
        (Rep.isIntertwiningMap_res_res Y.X₁ (Subgroup.subtype_comp_congrOfMapEq e he)).toRes n =
      map (e : G →* G') (𝟙 _) n ≫ transfer Y.X₁ S' n) →
    transfer (res (e : G →* G') Y.X₃) S (n + 1) ≫ map (Subgroup.congrOfMapEq e he : S →* S')
        (Rep.isIntertwiningMap_res_res Y.X₃
          (Subgroup.subtype_comp_congrOfMapEq e he)).toRes (n + 1) =
      map (e : G →* G') (𝟙 _) (n + 1) ≫ transfer Y.X₃ S' (n + 1) := by
  have := S.finiteIndex_of_map_eq (e : G →* G') e.surjective he
  intro ih
  have hX := (shortExact_res (e : G →* G')).2 hY
  have hYS' := (shortExact_res S'.subtype).2 hY
  have hc := Subgroup.subtype_comp_congrOfMapEq e he
  refine (mono_δ_of_isZero hYS' n hY₂).right_cancellation _ _ ?_
  -- Paste, as terms, the squares `δ_naturality` along `S →* S'`, `δ_comp_transfer` over `G`, `ih`,
  -- `δ_naturality` along `e` and `δ_comp_transfer` over `G'`: the objects appear both as
  -- restrictions of `Y.Xᵢ` and as projections of restricted short complexes, which `rw` and `simp`
  -- do not identify.
  exact (Category.assoc _ _ _).trans <|
    (whisker_eq _ (δ_naturality _ ((shortExact_res S.subtype).2 hX) hYS'
      ⟨(Rep.isIntertwiningMap_res_res Y.X₁ hc).toRes, (Rep.isIntertwiningMap_res_res Y.X₂ hc).toRes,
        (Rep.isIntertwiningMap_res_res Y.X₃ hc).toRes,
        Rep.isIntertwiningMap_res_res_toRes_naturality hc Y.f,
        Rep.isIntertwiningMap_res_res_toRes_naturality hc Y.g⟩ (n + 1) n rfl).symm).trans <|
    (δ_comp_transfer_assoc S hX (n + 1) n rfl _).symm.trans <|
    (whisker_eq _ ih).trans <|
    (δ_naturality_assoc _ hX hY (𝟙 _) (n + 1) n rfl _).trans <|
    whisker_eq _ (δ_comp_transfer S' hY (n + 1) n rfl)

-- The case of identity coefficients of `map_comp_transfer_congrOfMapEq`.
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
private theorem transfer_res_equiv [S.FiniteIndex] (N : Rep.{u} R G') (n : ℕ) :
    haveI := S.finiteIndex_of_map_eq (e : G →* G') e.surjective he
    transfer (res (e : G →* G') N) S n ≫ map (Subgroup.congrOfMapEq e he : S →* S')
        (Rep.isIntertwiningMap_res_res N (Subgroup.subtype_comp_congrOfMapEq e he)).toRes n =
      map (e : G →* G') (𝟙 _) n ≫ transfer N S' n := by
  have := S.finiteIndex_of_map_eq (e : G →* G') e.surjective he
  induction n generalizing N with
  | zero =>
    -- On `H₀`, the coinvariants, the transfer is the relative transfer (`transfer_zero_H0π`).
    rw [← cancel_epi (H0π _)]
    ext m
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [transfer_zero_H0π, H0π_comp_map_apply, H0π_comp_map_apply, transfer_zero_H0π,
      Representation.IsIntertwiningMap.toRes_hom_apply]
    exact (H0π_eq_iff _).2 <|
      Representation.relTransfer_map_sub_mem e LinearMap.id (fun _ _ ↦ rfl) he m
  | succ n ih =>
    -- Shift dimension along `dimensionShiftDown N ⟶ Ind_⊥^G' N ⟶ N`. The casts along
    -- `dimensionShiftDownSES_X₂/X₃` are needed: without them unification times out.
    exact dimensionShiftDownSES_X₃ N ▸
      transfer_res_equiv_succ e he (dimensionShiftDownSES_shortExact N) n
        (dimensionShiftDownSES_X₂ N ▸ isZero_res_indBot_succ S' N.V n) (ih _)

/-- **The transfer is compatible with a group isomorphism.** Let `e : G ≃* G'` carry `S` onto `S'`
and let `φ : M ⟶ Res_e N`. Then the transfers `Hₙ(G, M) ⟶ Hₙ(S, Res_S M)` and
`Hₙ(G', N) ⟶ Hₙ(S', Res_S' N)` commute with the maps induced by `(e, φ)` over `G` and by its
restriction `(e|_S, Res_S φ)` over `S`. This extends `TauCeti.groupHomology.map_comp_transfer`, the
case where `e` is the identity, to a change of group. -/
@[reassoc, elementwise]
theorem map_comp_transfer_congrOfMapEq [S.FiniteIndex] {M : Rep.{u} R G}
    {N : Rep.{u} R G'} (φ : M ⟶ res (e : G →* G') N) (n : ℕ) :
    haveI := S.finiteIndex_of_map_eq (e : G →* G') e.surjective he
    map (e : G →* G') φ n ≫ transfer N S' n =
      transfer M S n ≫ map (Subgroup.congrOfMapEq e he : S →* S') ((resFunctor S.subtype).map φ ≫
        (Rep.isIntertwiningMap_res_res N (Subgroup.subtype_comp_congrOfMapEq e he)).toRes) n := by
  -- Split the map over `S` at `Res_S φ`, then paste the naturality square of `φ` with the case of
  -- identity coefficients. `map_comp` recombines the maps over `G` into
  -- `map (e.comp (MonoidHom.id G)) (φ ≫ resMap _ (𝟙 _))`, which is `map e φ` by `map_congr`.
  have := S.finiteIndex_of_map_eq (e : G →* G') e.surjective he
  refine ((whisker_eq _ (map_comp (MonoidHom.id S) _ _ _ n)).trans ?_).symm
  rw [← map_comp_transfer_assoc, transfer_res_equiv e he N, ← map_comp_assoc]
  exact congrArg (· ≫ transfer N S' n) (map_congr (MonoidHom.comp_id _) (by simp) n)

end TauCeti.groupHomology
