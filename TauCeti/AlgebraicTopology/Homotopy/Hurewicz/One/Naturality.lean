/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# Naturality of the Hurewicz map in degree one

The Hurewicz map `π₁(X, x) → H₁(X; ℤ)` of `TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic`
is natural in continuous maps, with respect to the map induced on the first homology group of the
singular chain complex, and it does not depend on the base point: changing the base point along a
path, which conjugates loops by the path, does not change their homology classes.

## Main results

* `TauCeti.HurewiczOne.homologyMap_H₁AddEquivHomology_hurewiczAb`: naturality of the Hurewicz
  map on the abelianized fundamental group.
* `TauCeti.HurewiczOne.homologyMap_hurewiczHomologyAddEquiv`: the same for the Hurewicz
  isomorphism of path-connected spaces.
* `TauCeti.HurewiczOne.hurewicz₁_fundamentalGroupMulEquivOfPath`: the Hurewicz map is invariant
  under the change of base point along a path.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1.
-/

public section

noncomputable section

open CategoryTheory Convexity Simplicial unitInterval TauCeti.TopCat

namespace TauCeti.HurewiczOne

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

lemma map_mem_cycles₁ {c : ((singularChains ℤ).obj X).X 1} (hc : c ∈ cycles₁ X) :
    ((singularChains ℤ).map f).f 1 c ∈ cycles₁ Y := by
  have hc' : ((singularChains ℤ).obj X).d 1 0 c = 0 := mem_cycles₁_iff.1 hc
  exact mem_cycles₁ (by rw [HomologicalComplex.Hom.comm_apply, hc', map_zero])

/-- The map induced on the first homology group of the singular chain complex sends the class of
a `1`-cycle to the class of its image. -/
lemma homologyMap_H₁AddEquivHomology_mk (c : cycles₁ X) :
    (HomologicalComplex.homologyMap ((singularChains ℤ).map f) 1).hom
        (H₁AddEquivHomology X (H₁.mk c)) =
      H₁AddEquivHomology Y
        (H₁.mk ⟨((singularChains ℤ).map f).f 1 c, map_mem_cycles₁ f c.2⟩) := by
  let z := ((singularChains ℤ).obj X).moduleCatCyclesMk (c : ((singularChains ℤ).obj X).X 1) 0
    (by simp) c.2
  have hz : (((singularChains ℤ).obj X).iCycles 1).hom z = c :=
    ((singularChains ℤ).obj X).iCycles_moduleCatCyclesMk 1 _ 0 (by simp) c.2
  have h₁ := congr($(HomologicalComplex.homologyπ_naturality ((singularChains ℤ).map f) 1).hom z)
  have h₂ := congr($(HomologicalComplex.cyclesMap_i ((singularChains ℤ).map f) 1).hom z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
  rw [H₁AddEquivHomology_mk c z hz, h₁]
  refine (H₁AddEquivHomology_mk _ _ ?_).symm
  rw [h₂, hz]

-- Not a simp lemma: `TauCeti.singularChainComplexFunctor_obj_map` rewrites the chain map inside
-- the left-hand side first, so the `simpNF` linter rejects it.
lemma homologyMap_H₁AddEquivHomology_loopClass {x : X} (γ : Path x x) :
    (HomologicalComplex.homologyMap ((singularChains ℤ).map f) 1).hom
        (H₁AddEquivHomology X (loopClass γ)) =
      H₁AddEquivHomology Y (loopClass (γ.map (f.hom).continuous)) := by
  rw [loopClass_def, homologyMap_H₁AddEquivHomology_mk, loopClass_def]
  congr 2
  refine Subtype.ext ((singularChains_map_f_pathChain f _).trans
    (congrArg (pathChain ℤ) (ContinuousMap.ext fun t ↦ ?_)))
  simp

/-- **Naturality of the Hurewicz map**: for a continuous map `f`, the map induced on the first
homology group of the singular chain complex corresponds to the map induced on fundamental
groups. -/
theorem homologyMap_H₁AddEquivHomology_hurewiczAb {x : X}
    (a : Additive (Abelianization (FundamentalGroup X x))) :
    (HomologicalComplex.homologyMap ((singularChains ℤ).map f) 1).hom
        (H₁AddEquivHomology X (hurewiczAb x a)) =
      H₁AddEquivHomology Y (hurewiczAb (f x) (Additive.ofMul (Abelianization.map
        (FundamentalGroup.map f.hom x) a.toMul))) := by
  induction a using Additive.rec with | ofMul a =>
  induction a using Quot.ind with | mk p =>
  obtain ⟨p⟩ := p
  induction p using Path.Homotopic.Quotient.ind with | mk γ =>
  have hmap : FundamentalGroup.map f.hom x (FundamentalGroup.fromPath (.mk γ)) =
      FundamentalGroup.fromPath (.mk (γ.map f.hom.continuous)) := rfl
  rw [Abelianization.mk_eq_of, toMul_ofMul, Abelianization.map_of, hmap, hurewiczAb_ofMul_of_mk,
    hurewiczAb_ofMul_of_mk, homologyMap_H₁AddEquivHomology_loopClass]

/-- **Naturality of the Hurewicz isomorphism** of path-connected spaces. -/
theorem homologyMap_hurewiczHomologyAddEquiv [PathConnectedSpace X] [PathConnectedSpace Y]
    {x : X} (a : Additive (Abelianization (FundamentalGroup X x))) :
    (HomologicalComplex.homologyMap ((singularChains ℤ).map f) 1).hom
        (hurewiczHomologyAddEquiv x a) =
      hurewiczHomologyAddEquiv (f x) (Additive.ofMul (Abelianization.map
        (FundamentalGroup.map f.hom x) a.toMul)) := by
  rw [hurewiczHomologyAddEquiv_apply, hurewiczHomologyAddEquiv_apply,
    homologyMap_H₁AddEquivHomology_hurewiczAb]

/-- **Independence of the base point**: the Hurewicz map is invariant under the change of base
point along a path. -/
-- Not a simp lemma: `FundamentalGroup.fundamentalGroupMulEquivOfPath_apply` is a simp lemma and
-- rewrites the left-hand side first, so the `simpNF` linter rejects it.
theorem hurewicz₁_fundamentalGroupMulEquivOfPath {x x' : X} (p : Path x x')
    (a : FundamentalGroup X x) :
    hurewicz₁ X x' (FundamentalGroup.fundamentalGroupMulEquivOfPath p a) = hurewicz₁ X x a := by
  obtain ⟨a⟩ := a
  induction a using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_apply]
  dsimp only
  rw [← Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans, hurewicz₁_mk,
    hurewicz₁_mk]
  congr 1
  refine (loopClass_eq_iff _ _).2 ?_
  have h₁ := pathChain_add_sub_trans_mem_boundaries₁ p.symm (γ.trans p)
  have h₂ := pathChain_add_sub_trans_mem_boundaries₁ γ p
  have h₃ := pathChain_add_symm_mem_boundaries₁ p.symm
  rw [Path.symm_symm] at h₃
  have := add_mem (sub_mem (neg_mem h₁) h₂) h₃
  convert this using 1
  abel

end TauCeti.HurewiczOne
