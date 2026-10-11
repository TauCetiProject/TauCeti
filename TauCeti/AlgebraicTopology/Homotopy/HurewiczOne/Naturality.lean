/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.HurewiczOne

/-!
# Naturality of the Hurewicz map in degree one

The Hurewicz map `π₁(X, x) → H₁(X; ℤ)` of `TauCeti.AlgebraicTopology.Homotopy.HurewiczOne` is
natural in continuous maps, and it does not depend on the base point: changing the base point
along a path, which conjugates loops by the path, does not change their homology classes.

## Main definitions and results

* `TauCeti.HurewiczOne.H₁Map`: the map induced by a continuous map on `1`-cycles modulo
  boundaries.
* `TauCeti.HurewiczOne.H₁Map_hurewiczAb`: naturality of the Hurewicz map on the abelianized
  fundamental group.
* `TauCeti.HurewiczOne.hurewicz₁_fundamentalGroupMulEquivOfPath`: the Hurewicz map is invariant
  under the change of base point along a path.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1.
-/

public section

noncomputable section

open CategoryTheory Convexity Simplicial unitInterval

namespace TauCeti.HurewiczOne

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

lemma map_simplex₁ (g : C(I, X)) :
    (TopCat.toSSet.map f).app _ (simplex₁ g) = simplex₁ ((f.hom).comp g) := by
  apply (Y.toSSetObjEquiv _).injective
  rw [TopCat.toSSetObjEquiv_toSSet_map_app, toSSetObjEquiv_simplex₁, toSSetObjEquiv_simplex₁,
    ContinuousMap.comp_assoc]

lemma map_chain₁ (g : C(I, X)) :
    ((singularChains ℤ).map f).f 1 (chain₁ g) = chain₁ ((f.hom).comp g) := by
  rw [singularChains_map_f_simplexChain, map_simplex₁]

lemma map_d (n m : ℕ) (c : Chains X n) :
    ((singularChains ℤ).map f).f m (((singularChains ℤ).obj X).d n m c) =
      ((singularChains ℤ).obj Y).d n m (((singularChains ℤ).map f).f n c) :=
  congr($(((singularChains ℤ).map f).comm n m).hom c).symm

lemma map_mem_cycles₁ {c : Chains X 1} (hc : c ∈ cycles₁ X) :
    ((singularChains ℤ).map f).f 1 c ∈ cycles₁ Y :=
  mem_cycles₁ (by rw [← map_d, show ((singularChains ℤ).obj X).d 1 0 c = 0 from hc, map_zero])

lemma map_mem_boundaries₁ {c : Chains X 1} (hc : c ∈ boundaries₁ X) :
    ((singularChains ℤ).map f).f 1 c ∈ boundaries₁ Y := by
  obtain ⟨y, rfl⟩ := hc
  exact mem_boundaries₁ (((singularChains ℤ).map f).f 2 y) (map_d f 2 1 y).symm

/-- The map induced on `1`-cycles modulo boundaries by a continuous map. -/
def H₁Map : H₁ X →+ H₁ Y :=
  QuotientAddGroup.map _ _
    (((((singularChains ℤ).map f).f 1).hom.toAddMonoidHom.comp (cycles₁ X).subtype).codRestrict
      _ fun c ↦ map_mem_cycles₁ f c.2)
    fun _ hc ↦ AddSubgroup.mem_comap.2 (AddSubgroup.mem_addSubgroupOf.2
      (map_mem_boundaries₁ f (AddSubgroup.mem_addSubgroupOf.1 hc)))

lemma H₁Map_loopClass {x : X} (γ : Path x x) :
    H₁Map f (loopClass γ) = loopClass (γ.map (f.hom).continuous) := by
  rw [loopClass_def, loopClass_def, H₁Map, QuotientAddGroup.map_mk]
  congr 1
  exact Subtype.ext (map_chain₁ f γ.toContinuousMap)

/-- **Naturality of the Hurewicz map**: for a continuous map `f`, the map induced on `1`-cycles
modulo boundaries corresponds to the map induced on fundamental groups. -/
theorem H₁Map_hurewiczAb {x : X} (a : Additive (Abelianization (FundamentalGroup X x))) :
    H₁Map f (hurewiczAb x a) =
      hurewiczAb (f x) (Additive.ofMul (Abelianization.map
        (FundamentalGroup.map (f.hom) x) a.toMul)) := by
  induction a using Additive.rec with | ofMul a =>
  induction a using QuotientGroup.induction_on with | H p =>
  obtain ⟨γ, rfl⟩ : ∃ γ : Path x x, Path.Homotopic.Quotient.mk γ = p :=
    Quotient.exists_rep (s := Path.Homotopic.setoid x x) p
  change H₁Map f (hurewiczAb x (Additive.ofMul (Abelianization.of _))) =
    hurewiczAb (f x) (Additive.ofMul (Abelianization.of _))
  rw [hurewiczAb_ofMul_of, H₁Map_loopClass]
  exact (hurewiczAb_ofMul_of (f x) _).symm

/-- **Independence of the base point**: the Hurewicz map is invariant under the change of base
point along a path. -/
theorem hurewicz₁_fundamentalGroupMulEquivOfPath {x x' : X} (p : Path x x')
    (a : FundamentalGroup X x) :
    hurewicz₁ X x' (FundamentalGroup.fundamentalGroupMulEquivOfPath p a) = hurewicz₁ X x a := by
  obtain ⟨γ, rfl⟩ : ∃ γ : Path x x, Path.Homotopic.Quotient.mk γ = a :=
    Quotient.exists_rep (s := Path.Homotopic.setoid x x) a
  change Multiplicative.ofAdd (loopClass (p.symm.trans (γ.trans p))) =
    Multiplicative.ofAdd (loopClass γ)
  congr 1
  rw [loopClass_def, loopClass_def, QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub]
  have h₁ := chain₁_add_sub_trans_mem p.symm (γ.trans p)
  have h₂ := chain₁_add_sub_trans_mem γ p
  have h₃ := chain₁_add_symm_mem p.symm
  rw [Path.symm_symm] at h₃
  have := add_mem (sub_mem (neg_mem h₁) h₂) h₃
  convert this using 1
  abel

end TauCeti.HurewiczOne
