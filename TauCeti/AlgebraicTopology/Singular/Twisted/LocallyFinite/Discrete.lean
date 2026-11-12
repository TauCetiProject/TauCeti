/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.TotallyDisconnected

/-!
# Zeroth Borel–Moore homology of discrete spaces

On a discrete space every family of coefficients on point simplices is locally finite. The
boundary into degree zero vanishes, so zeroth Borel–Moore homology is the product of the fibres
of the local coefficient system, without a finite-support condition. This includes infinite
discrete spaces and is the degree-zero computation needed for duality on zero-dimensional
manifolds.

## References

* G. E. Bredon, *Sheaf Theory*, 2nd ed., Chapter V.
* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits SimplexCategory Simplicial Topology

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- Every family of point coefficients on a discrete space is locally finite. -/
theorem isLocallyFiniteChain_zero_of_discreteTopology [DiscreteTopology X]
    (c : ∀ s : (TopCat.toSSet.obj X) _⦋0⦌, L.obj (initialVertex s)) :
    IsLocallyFiniteChain L c := by
  rw [isLocallyFiniteChain_iff]
  intro x
  refine ⟨{x}, (isOpen_discrete _).mem_nhds (Set.mem_singleton x),
    (Set.finite_singleton (TopCat.toSSetObj₀Equiv.symm x)).subset ?_⟩
  rintro s ⟨_, y, ⟨z, rfl⟩, hy⟩
  apply Set.mem_singleton_iff.mpr
  apply TopCat.toSSetObj₀Equiv.injective
  rw [Equiv.apply_symm_apply]
  exact (congrArg (TopCat.simplexMap s) (Subsingleton.elim z _)).symm.trans
    (Set.mem_singleton_iff.mp hy)

/-- The locally finite zero-chains on a discrete space form the full module of point
coefficients. -/
@[simp]
theorem locallyFiniteChains_zero_eq_top [DiscreteTopology X] :
    locallyFiniteChains L 0 = ⊤ := by
  exact top_unique fun c _ ↦
    mem_locallyFiniteChains.mpr (isLocallyFiniteChain_zero_of_discreteTopology L c)

/-- Read a locally finite zero-chain on a discrete space as its family of point coefficients. -/
def locallyFiniteChainsZeroEquivPi [DiscreteTopology X] :
    locallyFiniteChains L 0 ≃ₗ[R] ∀ x : X, L.obj (FundamentalGroupoid.mk x) :=
  (LinearEquiv.ofTop _ (locallyFiniteChains_zero_eq_top L)).trans
    ((LinearEquiv.piCongrRight fun s ↦
      (eqToIso (congrArg L.obj (initialVertex_zero s))).toLinearEquiv).trans
        (LinearEquiv.piCongrLeft R (fun x : X ↦ L.obj (FundamentalGroupoid.mk x))
          TopCat.toSSetObj₀Equiv))

/-- The coefficient at a point is the coefficient of its point simplex. -/
@[simp]
theorem locallyFiniteChainsZeroEquivPi_apply [DiscreteTopology X]
    (c : locallyFiniteChains L 0) (x : X) :
    locallyFiniteChainsZeroEquivPi L c x =
      (c : ∀ s, L.obj (initialVertex s)) (TopCat.toSSetObj₀Equiv.symm x) := by
  rfl

/-- The inverse product identification has exactly the prescribed coefficient at each point. -/
@[simp]
theorem locallyFiniteChainsZeroEquivPi_symm_apply [DiscreteTopology X]
    (a : ∀ x : X, L.obj (FundamentalGroupoid.mk x)) (x : X) :
    ((locallyFiniteChainsZeroEquivPi L).symm a : ∀ s, L.obj (initialVertex s))
      (TopCat.toSSetObj₀Equiv.symm x) = a x :=
  congrFun ((locallyFiniteChainsZeroEquivPi L).apply_symm_apply a) x

/-- On a totally disconnected space, the boundary of a locally finite one-chain vanishes. -/
@[simp]
theorem locallyFiniteBoundary_zero_eq_zero [TotallyDisconnectedSpace X] :
    locallyFiniteBoundary L 0 = 0 := by
  ext c s
  simp [coe_locallyFiniteBoundary, locallyFiniteBoundaryFun_apply]

/-- Zeroth Borel–Moore homology of a discrete space is the product of the coefficient fibres.
There is no countability or finite-support restriction on this product. -/
def borelMooreHomologyZeroIsoPi [DiscreteTopology X] :
    borelMooreHomology L 0 ≅ ModuleCat.of R (∀ x : X, L.obj (FundamentalGroupoid.mk x)) :=
  (locallyFiniteChainComplex L).isoHomologyι₀ ≪≫
    ((locallyFiniteChainComplex L).pOpcyclesIso 1 0 (by simp)
      (by simp)).symm ≪≫
    eqToIso (locallyFiniteChainComplex_X L 0) ≪≫
    (locallyFiniteChainsZeroEquivPi L).toModuleIso

/-- The product description of a zero-chain's homology class records its actual point
coefficients. -/
@[reassoc (attr := simp)]
theorem pOpcycles_borelMooreHomologyZeroIsoPi_hom [DiscreteTopology X] :
    (locallyFiniteChainComplex L).pOpcycles 0 ≫
      (locallyFiniteChainComplex L).isoHomologyι₀.inv ≫
        (borelMooreHomologyZeroIsoPi L).hom =
      eqToHom (locallyFiniteChainComplex_X L 0) ≫
        (locallyFiniteChainsZeroEquivPi L).toModuleIso.hom := by
  simp [borelMooreHomologyZeroIsoPi]

/-- A family of point coefficients determines the class of the corresponding locally finite
zero-chain. This describes the inverse of the product isomorphism. -/
theorem borelMooreHomologyZeroIsoPi_inv [DiscreteTopology X] :
    (borelMooreHomologyZeroIsoPi L).inv =
      (locallyFiniteChainsZeroEquivPi L).toModuleIso.inv ≫
        eqToHom (locallyFiniteChainComplex_X L 0).symm ≫
          (locallyFiniteChainComplex L).pOpcycles 0 ≫
            (locallyFiniteChainComplex L).isoHomologyι₀.inv := by
  apply (cancel_mono (borelMooreHomologyZeroIsoPi L).hom).1
  simp only [Category.assoc, Iso.inv_hom_id,
    pOpcycles_borelMooreHomologyZeroIsoPi_hom, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

end TauCeti.LocalCoefficientSystem
