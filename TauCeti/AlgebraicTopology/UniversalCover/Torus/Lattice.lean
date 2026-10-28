/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.ActingGroup
public import TauCeti.Topology.Covering.Quotient
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# The universal cover and fundamental group of a lattice quotient

Let `L` be a discrete additive subgroup of a topological additive group `E`, for instance a
lattice in a finite-dimensional real or complex vector space. Then `L` acts on `E` by translation,
and the orbit projection `q : E → E / L` onto the standard orbit space
`AddAction.orbitRel.Quotient L E` is a quotient covering map for this action
(`AddSubgroup.isAddQuotientCoveringMap_quotientMk`, in `TauCeti.Topology.Covering.Quotient`).
A discrete submodule `L` of a topological module, the carrier used for complex tori, enters
through `L.toAddSubgroup`, whose orbit space is definitionally that of `L`.

Consequently:

* when `E` is preconnected, translation identifies `L` with the deck group of `q`
  (`AddSubgroup.orbitRelQuotientDeckMulEquiv`);
* when `E` is commutative and simply connected, for instance a real topological vector space, `q`
  is the universal cover of `E / L` and the fundamental group of `E / L` at every point is `L`
  (`AddSubgroup.orbitRelQuotientFundamentalGroupEquiv`).

The isomorphism `π₁(E / L, x) ≃* Multiplicative L` sends the class of a loop to its period
displacement `Γ 1 - Γ 0`, for any lift `Γ : I → E` of the loop
(`AddSubgroup.orbitRelQuotientFundamentalGroupEquiv_fromPath`). Since `L` is commutative, it does
not depend on a choice of lift of the basepoint. It is natural: a continuous additive map
`f : E → E'` carrying `L` into `L'` acts on fundamental groups of the quotients, through any
continuous map of quotients induced by `f`, as the restriction of `f` to the lattices
(`AddSubgroup.orbitRelQuotientFundamentalGroupEquiv_map`).

For a full lattice in a finite-dimensional complex vector space, this computes the universal
cover, the deck group, and the fundamental group of a complex torus.

## Main declarations

* `AddSubgroup.orbitRelQuotientDeckMulEquiv`: for preconnected `E`, the lattice is the deck group
  of the orbit projection.
* `AddSubgroup.orbitRelQuotientFundamentalGroupEquiv`: for simply connected `E`, the fundamental
  group of `E / L` is `L`.
* `AddSubgroup.orbitRelQuotientFundamentalGroupEquiv_apply_eq_iff`: a loop class corresponds to
  `l` exactly when its monodromy translates a lift of the basepoint by `l`.
* `AddSubgroup.orbitRelQuotientFundamentalGroupEquiv_fromPath`: the period displacement of a lift.
* `AddSubgroup.orbitRelQuotientFundamentalGroupEquiv_map`: naturality in lattice-preserving maps.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1.

The fundamental-group comparison is Mathlib's `IsAddQuotientCoveringMap.fundamentalGroupEquiv`
(Junyan Xu), and the deck-group comparison is `TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv`.
-/

public section

open unitInterval

namespace AddSubgroup

section AddGroup

variable {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  (L : AddSubgroup E) [DiscreteTopology L]

/-- For preconnected `E`, translation identifies a discrete additive subgroup `L` with the deck
group of the orbit projection `E → E / L`. -/
noncomputable def orbitRelQuotientDeckMulEquiv [PreconnectedSpace E] :
    Multiplicative L ≃* deck (_root_.Quotient.mk (AddAction.orbitRel L E)) :=
  TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv
    (L.isAddQuotientCoveringMap_quotientMk.toMultiplicative _)

/-- The deck transformation attached to `l` is translation by `l`. -/
@[simp]
theorem orbitRelQuotientDeckMulEquiv_apply [PreconnectedSpace E] (l : Multiplicative L) (v : E) :
    (L.orbitRelQuotientDeckMulEquiv l).1 v = (l.toAdd : E) + v :=
  TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv_apply _ l v

end AddGroup

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  (L : AddSubgroup E) [DiscreteTopology L]

variable [SimplyConnectedSpace E]

/-- For simply connected `E`, the fundamental group of the quotient `E / L` by a discrete
additive subgroup is `L`, at every basepoint. A loop class corresponds to the element of `L` by
which its monodromy translates a lift of the basepoint
(`AddSubgroup.orbitRelQuotientFundamentalGroupEquiv_apply_eq_iff`); the choice of lift does not
matter because `L` is commutative. -/
noncomputable def orbitRelQuotientFundamentalGroupEquiv (x : AddAction.orbitRel.Quotient L E) :
    FundamentalGroup (AddAction.orbitRel.Quotient L E) x ≃* Multiplicative L :=
  (L.isAddQuotientCoveringMap_quotientMk.fundamentalGroupEquiv ⟨x.out, x.out_eq⟩).trans
    MulOpposite.opMulEquiv.symm

/-- A loop class at `x` corresponds to `l ∈ L` exactly when its monodromy moves a lift `e` of
`x` to `l + e`. -/
theorem orbitRelQuotientFundamentalGroupEquiv_apply_eq_iff {x : AddAction.orbitRel.Quotient L E}
    (e : _root_.Quotient.mk (AddAction.orbitRel L E) ⁻¹' {x})
    (γ : FundamentalGroup (AddAction.orbitRel.Quotient L E) x) (l : Multiplicative L) :
    L.orbitRelQuotientFundamentalGroupEquiv x γ = l ↔
      (L.isAddQuotientCoveringMap_quotientMk.isCoveringMap.monodromy γ.toPath e : E) =
        (l.toAdd : E) + e := by
  have hq := L.isAddQuotientCoveringMap_quotientMk
  rw [orbitRelQuotientFundamentalGroupEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_eq,
    hq.fundamentalGroupEquiv_eq _ e]
  exact hq.fundamentalGroupToMulOpposite_apply_eq_iff.trans eq_comm

/-- **Period displacement.** The class of a loop `γ` in `E / L` corresponds to `Γ 1 - Γ 0`, for
any continuous lift `Γ : I → E` of `γ`. -/
theorem orbitRelQuotientFundamentalGroupEquiv_fromPath {x : AddAction.orbitRel.Quotient L E}
    (γ : Path x x) (Γ : C(I, E)) (hΓ : _root_.Quotient.mk (AddAction.orbitRel L E) ∘ Γ = γ) :
    ((L.orbitRelQuotientFundamentalGroupEquiv x (.fromPath (.mk γ))).toAdd : E) = Γ 1 - Γ 0 := by
  have hq := L.isAddQuotientCoveringMap_quotientMk
  have h0 : _root_.Quotient.mk (AddAction.orbitRel L E) (Γ 0) = x :=
    congrFun hΓ 0 |>.trans γ.source
  set l := L.orbitRelQuotientFundamentalGroupEquiv x (.fromPath (.mk γ))
  have hl := (L.orbitRelQuotientFundamentalGroupEquiv_apply_eq_iff ⟨Γ 0, h0⟩ _ l).1 rfl
  rw [hq.isCoveringMap.monodromy_eq_apply_one hΓ rfl] at hl
  rw [hl, add_sub_cancel_right]

/-- **Naturality.** Let `f : E → E'` be a continuous additive map and `φ : E / L → E' / L'` a
continuous map induced by `f`, so that `f` carries `L` into `L'`. On fundamental groups, `φ` acts
as the restriction of `f` to the lattices. -/
theorem orbitRelQuotientFundamentalGroupEquiv_map {E' : Type*} [AddCommGroup E']
    [TopologicalSpace E'] [IsTopologicalAddGroup E'] [SimplyConnectedSpace E']
    (L' : AddSubgroup E') [DiscreteTopology L'] (f : E →+ E') (hf : Continuous f)
    (φ : C(AddAction.orbitRel.Quotient L E, AddAction.orbitRel.Quotient L' E'))
    (hφ : ∀ v, φ (_root_.Quotient.mk _ v) = _root_.Quotient.mk (AddAction.orbitRel L' E') (f v))
    (x : AddAction.orbitRel.Quotient L E)
    (γ : FundamentalGroup (AddAction.orbitRel.Quotient L E) x) :
    ((L'.orbitRelQuotientFundamentalGroupEquiv (φ x) (FundamentalGroup.map φ x γ)).toAdd : E') =
      f (L.orbitRelQuotientFundamentalGroupEquiv x γ).toAdd := by
  have hq := L.isAddQuotientCoveringMap_quotientMk
  rw [← FundamentalGroup.fromPath_mk_out γ]
  generalize Quotient.out γ.toPath = γ
  obtain ⟨Γ, hΓ, -⟩ := hq.isCoveringMap.exists_path_lifts γ x.out (by simp)
  have hfΓ : _root_.Quotient.mk (AddAction.orbitRel L' E') ∘ (⟨f, hf⟩ : C(E, E')).comp Γ =
      γ.map φ.continuous := by
    ext t
    have ht : _root_.Quotient.mk _ (Γ t) = γ t := congrFun hΓ t
    simp [← ht, hφ]
  have h' := L'.orbitRelQuotientFundamentalGroupEquiv_fromPath _ _ hfΓ
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk] at h'
  rw [TauCeti.FundamentalGroup.map_fromPath, h',
    L.orbitRelQuotientFundamentalGroupEquiv_fromPath γ Γ hΓ, map_sub]

end AddSubgroup
