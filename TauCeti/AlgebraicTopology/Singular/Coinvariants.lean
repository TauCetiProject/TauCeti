/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Transfer
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct
public import TauCeti.CategoryTheory.Limits.Shapes.SingleObj
public import TauCeti.Topology.Category.TopCat.Action

/-!
# Singular chains of a quotient covering are coinvariants

Let a group `G` act on a space `E` so that `p : E ⟶ B` is the quotient covering map of the action,
in the sense of Mathlib's `IsQuotientCoveringMap`. The action is the functor
`E.actionFunctor G : SingleObj G ⥤ TopCat` sending the unique object to `E`, and `p` is a cocone
`hG.cocone` over it. This file shows that the singular simplicial set, and the singular chain
complex with any coefficients, of `B` are the coinvariants of those of `E`:

* `IsQuotientCoveringMap.isColimitMapCoconeToSSet`: the singular simplicial set of `B` is the
  quotient of that of `E` by `G`: every singular simplex of `B` lifts to `E`, and any two lifts of
  the same simplex differ by an element of `G`.
* `IsQuotientCoveringMap.isColimitMapCoconeSingularChainComplex`: hence `C(B; R)` is the colimit
  `C(E; R)_G` of the action of `G` on `C(E; R)` by the chain maps `g_*`, for coefficients `R` in
  any preadditive category with coproducts, since the simplicial chain complex preserves
  colimits.

Neither statement needs `G` to be finite. Taking coinvariants is not exact, so the corresponding
statement for homology fails in general. It holds when `G` is finite and multiplication by `|G|` is
invertible on `R`: the transfer `t` of the finite covering `p` satisfies `t ≫ p_* = |G| • 𝟙` and
`p_* ≫ t = ∑_{g ∈ G} g_*`, which makes the colimit absolute
(`CategoryTheory.Limits.SingleObj.isColimitMapCoconeOfTransfer`), so it survives homology:

* `IsQuotientCoveringMap.isColimitMapCoconeSingularHomology`: `Hₙ(B; R) ≅ Hₙ(E; R)_G` through
  `p_*` when `|G|` is invertible on `R`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.G (Proposition 3G.1), for the transfer and the averaging argument, stated there for
  cohomology with field coefficients and invariants; the homology and coinvariant form here is
  its dual.
* K. S. Brown, *Cohomology of Groups*, Springer GTM 87, Chapter VII, for the Cartan–Leray
  spectral sequence, which starts from the identification `C(E)_G = C(B)`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti.TopCat

universe w v u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{w}} {p : E ⟶ B} {G : Type*} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G)

/-- The quotient covering map `p : E ⟶ B`, as a cocone over the action of `G` on `E`. -/
@[expose, simps]
def cocone : Cocone (@TopCat.actionFunctor E G _ _ hG.toContinuousConstSMul) where
  pt := B
  ι :=
    { app _ := p
      naturality _ _ g := by ext e; exact hG.map_smul g }

/-- **The singular simplicial set of the base of a quotient covering is the quotient of that of
the total space.** For the quotient covering map `p : E ⟶ B` of an action of a group `G`, the
singular simplicial set of `B` is the colimit of the action of `G` on the singular simplicial set
of `E`, with legs `p_*`. -/
def isColimitMapCoconeToSSet : IsColimit (TopCat.toSSet.mapCocone hG.cocone) :=
  evaluationJointlyReflectsColimits _ fun n ↦ by
    have hp := hG.isCoveringMap
    let x : SimplexCategory.toTop.{w}.obj n.unop := SimplexCategory.toTopInitialVertex _
    refine SingleObj.Types.isColimitOf _ (fun σ ↦ ?_) fun τ τ' h ↦ ?_
    · -- A singular simplex `σ` of `B` lifts through `p`, starting at any point over `σ x`.
      obtain ⟨e, he⟩ := hG.surjective (simplexMap σ x)
      obtain ⟨τ, hτ, -⟩ := (hp.bijOn_simplexMap_apply σ x).surjOn (show e ∈ p ⁻¹' {_} from he)
      exact ⟨τ, hτ⟩
    · -- Two lifts `τ` and `τ'` of one simplex differ at `x` by some `g`, so `τ = g • τ'`.
      have hσ := hp.bijOn_simplexMap_apply ((TopCat.toSSet.map p).app n τ') x
      obtain ⟨g, hg⟩ := hG.apply_eq_iff_mem_orbit.mp ((hσ.mapsTo h).trans (hσ.mapsTo rfl).symm)
      refine ⟨g, hσ.injOn ?_ h ?_⟩
      · exact (((evaluation _ _).obj n).mapCocone
          (TopCat.toSSet.mapCocone hG.cocone)).w_apply
          (j := SingleObj.star G) (j' := SingleObj.star G) g τ'
      · -- The `SingleObj` action is `g • τ' = (toSSet.map (actionFunctor.map g)).app n τ'`, so
        -- `g` acts on singular simplices by postcomposition with `g • ·` (`simplexMap_app`).
        have := hG.toContinuousConstSMul
        change simplexMap ((TopCat.toSSet.map ((E.actionFunctor G).map g)).app n τ') x = _
        rw [simplexMap_app, ContinuousMap.comp_apply]
        exact (TopCat.actionFunctor_map_apply ..).trans hg

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)

/-- **The singular chains of the base of a quotient covering are coinvariants.** For the quotient
covering map `p : E ⟶ B` of an action of a group `G`, the singular chain complex `C(B; R)` is the
colimit `C(E; R)_G` of the action of `G` on `C(E; R)` by the chain maps `g_*`, with legs `p_*`. -/
def isColimitMapCoconeSingularChainComplex :
    IsColimit (((singularChainComplexFunctor C).obj R).mapCocone hG.cocone) :=
  isColimitOfPreserves ((SSet.chainComplexFunctor C).obj R) hG.isColimitMapCoconeToSSet

/-- **The singular homology of the base of a finite quotient covering is coinvariants.** For the
quotient covering map `p : E ⟶ B` of an action of a finite group `G`, and coefficients `R` on
which multiplication by `|G|` is invertible, `Hₙ(B; R)` is the colimit `Hₙ(E; R)_G` of the action
of `G` on `Hₙ(E; R)`, with legs `p_*`. -/
def isColimitMapCoconeSingularHomology [Fintype G] [CategoryWithHomology C] (n : ℕ)
    [IsIso (Fintype.card G • 𝟙 R)] :
    IsColimit (((singularHomologyFunctor C n).obj R).mapCocone hG.cocone) := by
  have := hG.toContinuousConstSMul
  let F := (singularChainComplexFunctor C).obj R
  -- Singular chains are additive in the coefficients, so `|G|` stays invertible on `C(E; R)` and
  -- `C(B; R)`. By `TopCat.actionFunctor_obj` and `cocone_pt` (both `rfl`), these are the acted-on
  -- object and the cocone point of `F.mapCocone hG.cocone`.
  have : IsIso (Fintype.card G • 𝟙 ((E.actionFunctor G ⋙ F).obj (SingleObj.star G))) :=
    (singularChainComplexFunctor C ⋙ (evaluation _ _).obj E).isIso_nsmul_id_obj _ R
  have : IsIso (Fintype.card G • 𝟙 (F.mapCocone hG.cocone).pt) :=
    (singularChainComplexFunctor C ⋙ (evaluation _ _).obj B).isIso_nsmul_id_obj _ R
  refine SingleObj.isColimitMapCoconeOfTransfer (F.mapCocone hG.cocone)
    (hG.isCoveringMap.singularTransfer hG.finite_fiber R)
    (HomologicalComplex.homologyFunctor C _ n) ?_ ?_
  -- The leg of `F.mapCocone hG.cocone` is `F.map p`, which is `p_*` by
  -- `singularChainComplexFunctor_obj_map` (`rfl`).
  · exact hG.isCoveringMap.singularTransfer_comp_chainComplexMap hG.finite_fiber R fun b ↦ by
      obtain ⟨e, he⟩ := hG.surjective b
      rw [Nat.card_congr (hG.fiberEquivGroup ⟨e, he⟩), Nat.card_eq_fintype_card]
  -- `F` sends the action of `g` to `(g • ·)_*`.
  · simp only [Functor.comp_map, TopCat.actionFunctor_map]
    exact hG.chainComplexMap_comp_singularTransfer R

end IsQuotientCoveringMap
