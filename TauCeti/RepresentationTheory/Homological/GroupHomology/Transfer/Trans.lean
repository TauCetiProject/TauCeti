/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup
import TauCeti.RepresentationTheory.Homological.GroupHomology.Induced
import TauCeti.RepresentationTheory.Homological.GroupHomology.LowDegree
import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Delta
import TauCeti.RepresentationTheory.Induction.DimensionShift

/-!
# Transitivity of the transfer

For finite-index subgroups `K ≤ H ≤ G`, the transfer in group homology is transitive: transferring
from `G` to `H` and then from `H` to `K` is the transfer from `G` to `K`, once `K.subgroupOf H` is
identified with `K`. This lets a transfer to a small subgroup be computed in stages through an
intermediate subgroup; it is what makes Tate restriction below degree `-1` functorial along a tower
of layers of a class formation.

## Main results

* `TauCeti.groupHomology.transfer_trans`: the transfer is transitive along a tower of subgroups.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter III, §9.
-/

public section

universe u

open CategoryTheory Rep

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {R G : Type u} [CommRing R] [Group G] {K H : Subgroup G} (hKH : K ≤ H)

-- The inductive step of `transfer_trans`: the connecting map of `X` restricted to `K` is injective
-- in degree `n + 1` when `X.X₂` has no homology there over `K`, and the transfer commutes with the
-- connecting maps (`δ_comp_transfer`).
private theorem transfer_trans_succ [K.FiniteIndex] [H.FiniteIndex] {X : ShortComplex (Rep.{u} R G)}
    (hX : X.ShortExact) (n : ℕ) (hX₂ : Limits.IsZero (groupHomology (res K.subtype X.X₂) (n + 1)))
    (ih : transfer X.X₁ H n ≫ transfer (res H.subtype X.X₁) (K.subgroupOf H) n ≫
      map (Subgroup.subgroupOfEquivOfLe hKH : K.subgroupOf H →* K)
        (Rep.isIntertwiningMap_res_res X.X₁
          (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH)).toRes n = transfer X.X₁ K n) :
    transfer X.X₃ H (n + 1) ≫ transfer (res H.subtype X.X₃) (K.subgroupOf H) (n + 1) ≫
      map (Subgroup.subgroupOfEquivOfLe hKH : K.subgroupOf H →* K)
        (Rep.isIntertwiningMap_res_res X.X₃
          (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH)).toRes (n + 1) =
        transfer X.X₃ K (n + 1) := by
  have hH := (shortExact_res H.subtype).2 hX
  have hK := (shortExact_res K.subtype).2 hX
  have hc := Subgroup.subtype_comp_subgroupOfEquivOfLe hKH
  refine (mono_δ_of_isZero hK n hX₂).right_cancellation _ _ ?_
  -- Naturality of the connecting maps along `K.subgroupOf H ≃* K`, for the morphism of short
  -- complexes identifying the two restrictions of each `X.Xᵢ`.
  rw [Category.assoc, Category.assoc, ← δ_naturality _ ((shortExact_res _).2 hH) hK
    ⟨(Rep.isIntertwiningMap_res_res X.X₁ hc).toRes, (Rep.isIntertwiningMap_res_res X.X₂ hc).toRes,
      (Rep.isIntertwiningMap_res_res X.X₃ hc).toRes,
      Rep.isIntertwiningMap_res_res_toRes_naturality hc X.f,
      Rep.isIntertwiningMap_res_res_toRes_naturality hc X.g⟩]
  -- Pasting the transfer squares as terms: the objects appear both as restrictions of `X.Xᵢ` and
  -- as projections of restricted short complexes, which `rw` and `simp` do not identify.
  exact (congrArg (_ ≫ ·) (δ_comp_transfer_assoc (K.subgroupOf H) hH (n + 1) n rfl _).symm).trans <|
    (δ_comp_transfer_assoc H hX (n + 1) n rfl _).symm.trans <|
    (congrArg (_ ≫ ·) ih).trans (δ_comp_transfer K hX (n + 1) n rfl)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
/-- **The transfer is transitive along a tower of finite-index subgroups** `K ≤ H ≤ G`: the
transfer `Hₙ(G, M) ⟶ Hₙ(H, Res_H M)` followed by the transfer to `K.subgroupOf H` is the transfer
`Hₙ(G, M) ⟶ Hₙ(K, Res_K M)`. Here `K.subgroupOf H`, which is `K` viewed as a subgroup of `H`, is
identified with `K` by the change-of-group map along `Subgroup.subgroupOfEquivOfLe hKH`, under
which the two restrictions of `M` agree (`Rep.isIntertwiningMap_res_res`). This is the
transitivity of the transfer described in Brown, Chapter III, §9. -/
@[reassoc]
theorem transfer_trans [K.FiniteIndex] (M : Rep.{u} R G) (n : ℕ) :
    haveI := Subgroup.finiteIndex_of_le hKH
    transfer M H n ≫ transfer (res H.subtype M) (K.subgroupOf H) n ≫
      map (Subgroup.subgroupOfEquivOfLe hKH : K.subgroupOf H →* K)
        (Rep.isIntertwiningMap_res_res M (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH)).toRes n =
      transfer M K n := by
  have := Subgroup.finiteIndex_of_le hKH
  induction n generalizing M with
  | zero =>
    -- On `H₀`, the coinvariants, the transfer is the relative transfer (`transfer_zero_H0π`).
    rw [← cancel_epi (H0π M)]
    ext m
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [transfer_zero_H0π, transfer_zero_H0π, transfer_zero_H0π, H0π_comp_map_apply,
      Representation.IsIntertwiningMap.toRes_hom_apply]
    exact (H0π_eq_iff _).2 (Representation.relTransfer_relTransfer_sub_relTransfer_mem hKH m)
  | succ n ih =>
    -- Shift dimension along `dimensionShiftDown M ⟶ Ind_⊥^G M ⟶ M`. The casts along
    -- `dimensionShiftDownSES_X₂/X₃` are needed: without them unification times out.
    exact dimensionShiftDownSES_X₃ M ▸
      transfer_trans_succ hKH (dimensionShiftDownSES_shortExact M) n
        (dimensionShiftDownSES_X₂ M ▸ isZero_res_indBot_succ K M.V n) (ih _)


end TauCeti.groupHomology
