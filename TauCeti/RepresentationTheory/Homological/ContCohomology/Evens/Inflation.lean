/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
public import TauCeti.Topology.Algebra.Group.Quotient.Basic

/-!
# Inflation of the index-two Evens graph cocycle

Let `N` be a normal subgroup contained in an open subgroup `U` of a topological group `G`. The
image `U / N` is open in `G / N`, has the same index as `U`, and the quotient map restricts to a
homomorphism `U → U / N`; these are `TauCeti.quotientOpenSubgroup` and
`TauCeti.quotientOpenSubgroupMap`. This file proves that the two-point graph cocycle commutes
with pullback along that quotient map. Consequently, degree-two inflation carries the
graph-cocycle class for `U / N` to the graph-cocycle class for `U`.

The coefficient object used by explicit inflation is the fixed-point subgroup of the ambient
trivial `𝔽₂` module. The additive equivalence `trivialF2QuotientEquivFixedPoints` identifies it
with the trivial `𝔽₂` module constructed directly on `G / N`; its forward map is used before
inflation in the class-level statement.

## Main definitions

* `TauCeti.ContCohomology.trivialF2QuotientEquivFixedPoints`: trivial coefficients on the
  quotient identified with the fixed points of the ambient trivial coefficients.

## Main results

* `TauCeti.ContCohomology.evensGraphCochain_quotient`: the graph-cochain formula commutes with the
  quotient map.
* `TauCeti.ContCohomology.explicitInfl2_evensGraphCocycle`: inflation of the quotient
  graph-cocycle class is the ambient graph-cocycle class.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

namespace TauCeti.ContCohomology

universe u

section Coefficients

variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- Trivial `𝔽₂` coefficients on `G / N` are additively equivalent to the `N`-fixed points of
the ambient trivial coefficients. -/
noncomputable def trivialF2QuotientEquivFixedPoints :
    (trivialF2 (G ⧸ N)).V ≃+ FixedPoints.addSubgroup N (trivialF2 G).V where
  toFun x := ⟨(trivialF2Equiv G).symm (trivialF2Equiv (G ⧸ N) x), by
    rw [FixedPoints.mem_addSubgroup]
    intro n
    simp only [Subgroup.smul_def, TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]⟩
  invFun x := (trivialF2Equiv (G ⧸ N)).symm (trivialF2Equiv G x.1)
  left_inv x := by simp
  right_inv x := by ext; simp
  map_add' x y := by
    apply Subtype.ext
    apply (trivialF2Equiv G).injective
    simp

/-- The coefficient equivalence does not change the underlying `ZMod 2` value. -/
@[simp]
theorem trivialF2Equiv_apply_trivialF2QuotientEquivFixedPoints
    (x : (trivialF2 (G ⧸ N)).V) :
    trivialF2Equiv G (trivialF2QuotientEquivFixedPoints N x : (trivialF2 G).V) =
      trivialF2Equiv (G ⧸ N) x := by
  simp [trivialF2QuotientEquivFixedPoints]

/-- The coefficient equivalence is equivariant for the quotient actions. -/
theorem trivialF2QuotientEquivFixedPoints_smul (q : G ⧸ N)
    (x : (trivialF2 (G ⧸ N)).V) :
    trivialF2QuotientEquivFixedPoints N (q • x) =
      q • trivialF2QuotientEquivFixedPoints N x := by
  apply Subtype.ext
  induction q using QuotientGroup.induction_on with
  | H g =>
    apply (trivialF2Equiv G).injective
    rw [coe_quotient_smul_fixedPoints_addSubgroup,
      coe_smul_fixedPoints_addSubgroup]
    simp

end Coefficients

section GraphCochain

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} [N.Normal] (U : OpenSubgroup G)

/-- A homomorphism on `U / N`, pulled back to `U` along the quotient map. -/
def evensInflatedHom
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2)) :
    U.toSubgroup →* Multiplicative (ZMod 2) :=
  α.comp (quotientOpenSubgroupMap N U)

/-- The pulled-back homomorphism evaluates the original at the image in `U / N`. -/
@[simp]
theorem evensInflatedHom_apply
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2)) (u : U.toSubgroup) :
    evensInflatedHom U α u = α (quotientOpenSubgroupMap N U u) :=
  (rfl)

/-- Pullback of a continuous homomorphism on `U / N` is continuous on `U`. -/
theorem continuous_evensInflatedHom
    {α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2)}
    (hα : Continuous α) : Continuous (evensInflatedHom U α) :=
  hα.comp (continuous_quotientOpenSubgroupMap N U)

/-- Extension by zero commutes with pullback from `G / N`, provided `N ≤ U`. -/
theorem evensExtend_quotient (hNU : N ≤ U)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2)) (g : G) :
    evensExtend U.toSubgroup (evensInflatedHom U α) g =
      evensExtend (quotientOpenSubgroup N U).toSubgroup α (g : G ⧸ N) := by
  by_cases hg : g ∈ U
  · have hq : (g : G ⧸ N) ∈ quotientOpenSubgroup N U :=
      (mem_quotientOpenSubgroup_mk_iff N U hNU g).2 hg
    rw [evensExtend_of_mem hg, evensExtend_of_mem hq, evensInflatedHom_apply]
    exact congrArg (fun u => Multiplicative.toAdd (α u))
      (Subtype.ext (coe_quotientOpenSubgroupMap N U ⟨g, hg⟩))
  · have hq : (g : G ⧸ N) ∉ quotientOpenSubgroup N U :=
      mt (mem_quotientOpenSubgroup_mk_iff N U hNU g).1 hg
    rw [evensExtend_of_notMem hg, evensExtend_of_notMem hq]

/-- The first Shapiro component commutes with pullback from `G / N`. -/
theorem evensB1_quotient (hNU : N ≤ U) (s : G)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2)) (g : G) :
    evensB1 U.toSubgroup s (evensInflatedHom U α) g =
      evensB1 (quotientOpenSubgroup N U).toSubgroup (s : G ⧸ N) α (g : G ⧸ N) := by
  by_cases hg : g ∈ U
  · have hq : (g : G ⧸ N) ∈ quotientOpenSubgroup N U :=
      (mem_quotientOpenSubgroup_mk_iff N U hNU g).2 hg
    rw [evensB1_of_mem hg, evensB1_of_mem hq, evensExtend_quotient U hNU]
  · have hq : (g : G ⧸ N) ∉ quotientOpenSubgroup N U :=
      mt (mem_quotientOpenSubgroup_mk_iff N U hNU g).1 hg
    rw [evensB1_of_notMem hg, evensB1_of_notMem hq, evensExtend_quotient U hNU]
    rfl

/-- The second Shapiro component commutes with pullback from `G / N`. -/
theorem evensBs_quotient (hNU : N ≤ U) (s : G)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2)) (g : G) :
    evensBs U.toSubgroup s (evensInflatedHom U α) g =
      evensBs (quotientOpenSubgroup N U).toSubgroup (s : G ⧸ N) α (g : G ⧸ N) := by
  rw [evensBs_apply, evensBs_apply, evensB1_quotient U hNU]
  rfl

/-- **The two-point graph cochain commutes with the quotient map.** This is the cochain-level
inflation identity: the graph cochain of a class on `U / N`, evaluated on the images of two
elements of `G`, is the graph cochain of the pulled-back class on `U`. -/
theorem evensGraphCochain_quotient (hNU : N ≤ U) (s : G)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2)) (g h : G) :
    evensGraphCochain U.toSubgroup s (evensInflatedHom U α) (g, h) =
      evensGraphCochain (quotientOpenSubgroup N U).toSubgroup (s : G ⧸ N) α
        ((g : G ⧸ N), (h : G ⧸ N)) := by
  by_cases hg : g ∈ U
  · have hq : (g : G ⧸ N) ∈ quotientOpenSubgroup N U :=
      (mem_quotientOpenSubgroup_mk_iff N U hNU g).2 hg
    rw [evensGraphCochain_of_mem hg, evensGraphCochain_of_mem hq,
      evensB1_quotient U hNU, evensBs_quotient U hNU]
  · have hq : (g : G ⧸ N) ∉ quotientOpenSubgroup N U :=
      mt (mem_quotientOpenSubgroup_mk_iff N U hNU g).1 hg
    rw [evensGraphCochain_of_notMem hg, evensGraphCochain_of_notMem hq,
      evensB1_quotient U hNU, evensB1_quotient U hNU, evensBs_quotient U hNU]

end GraphCochain

section GraphClass

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} [N.Normal]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `G` acts continuously on the ambient trivial coefficients. The name is given explicitly:
the sibling `Evens` files carry the same local instance, so an anonymous one here would be
auto-assigned the name `Evens.Restriction` already owns, and the plain name is taken by
`Evens.Corestriction`. -/
local instance continuousSMul_trivialF2_ambient : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- The quotient graph cocycle, which is `evensGraphCocycle` for the open subgroup `U / N` of
`G / N`, with its values transported to the fixed-point coefficient object expected by explicit
inflation. -/
noncomputable def evensGraphCocycleFixedPoints (U : OpenSubgroup G) (hNU : N ≤ U)
    (hU : U.toSubgroup.index = 2) (s : G) (hs : s ∉ U)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) : Z2 (G ⧸ N) (FixedPoints.addSubgroup N (trivialF2 G).V) :=
  cocyclesMap2 (G ⧸ N) (trivialF2 (G ⧸ N)).V (G ⧸ N)
      (FixedPoints.addSubgroup N (trivialF2 G).V) (ContinuousMonoidHom.id (G ⧸ N))
      (trivialF2QuotientEquivFixedPoints N).toAddMonoidHom continuous_of_discreteTopology
      (fun q x => by simpa using trivialF2QuotientEquivFixedPoints_smul N q x)
    (evensGraphCocycle (quotientOpenSubgroup N U) (s : G ⧸ N) α
      ((quotientOpenSubgroup_index N U hNU).trans hU)
      (mt (mem_quotientOpenSubgroup_mk_iff N U hNU s).1 hs) hα)

/-- The fixed-point-valued graph cocycle is obtained by applying the coefficient equivalence
pointwise to the quotient graph cocycle. -/
@[simp]
theorem coe_evensGraphCocycleFixedPoints (U : OpenSubgroup G) (hNU : N ≤ U)
    (hU : U.toSubgroup.index = 2) (s : G) (hs : s ∉ U)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    (evensGraphCocycleFixedPoints U hNU hU s hs α hα :
        (G ⧸ N) × (G ⧸ N) → FixedPoints.addSubgroup N (trivialF2 G).V) =
      fun p => trivialF2QuotientEquivFixedPoints N
        ((trivialF2Equiv (G ⧸ N)).symm
          (evensGraphCochain (quotientOpenSubgroup N U).toSubgroup (s : G ⧸ N) α p)) := by
  funext p
  obtain ⟨q, r⟩ := p
  rw [evensGraphCocycleFixedPoints, cocyclesMap2_apply, coe_evensGraphCocycle]
  simp

/-- **Inflation carries the quotient graph-cocycle class to the ambient graph-cocycle class.**
The quotient class is first transported from the directly constructed trivial `𝔽₂` module on
`G / N` to the fixed-point coefficient object expected by explicit inflation. -/
theorem explicitInfl2_evensGraphCocycle (U : OpenSubgroup G) (hNU : N ≤ U)
    (hU : U.toSubgroup.index = 2) (s : G) (hs : s ∉ U)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    explicitInfl2 G (trivialF2 G).V N
        (evensGraphCocycleFixedPoints U hNU hU s hs α hα :
          H2 (G ⧸ N) (FixedPoints.addSubgroup N (trivialF2 G).V)) =
      (evensGraphCocycle U s (evensInflatedHom U α) hU hs
        (continuous_evensInflatedHom U hα) : H2 G (trivialF2 G).V) := by
  rw [explicitInfl2_mk]
  apply congrArg (fun z : Z2 G (trivialF2 G).V => (z : H2 G (trivialF2 G).V))
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  apply (trivialF2Equiv G).injective
  rw [cocyclesMap2_apply]
  simp only [AddSubgroup.coe_subtype]
  rw [coe_evensGraphCocycleFixedPoints]
  simp only [ContinuousMonoidHom.quotientMk_apply, coe_evensGraphCocycle,
    trivialF2Equiv_apply_trivialF2QuotientEquivFixedPoints, AddEquiv.apply_symm_apply]
  exact (evensGraphCochain_quotient U hNU s α g h).symm

end GraphClass

end TauCeti.ContCohomology
