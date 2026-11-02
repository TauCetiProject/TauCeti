/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Naturality
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Torus.Lattice

/-!
# The first homology of a lattice quotient

Let `L` be a discrete additive subgroup of a simply connected topological additive commutative
group `E`, for instance a lattice in a finite-dimensional real or complex vector space, and let
`E / L` be the standard orbit space `AddAction.orbitRel.Quotient L E`. The first singular homology
group of `E / L` with integer coefficients is `L`
(`AddSubgroup.orbitRelQuotientFirstHomologyEquiv`). The isomorphism is the composite of the
Hurewicz isomorphism `H₁(E / L; ℤ) ≅ π₁(E / L)ᵃᵇ` (`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`)
with the identification `π₁(E / L) ≅ L` of `AddSubgroup.orbitRelQuotientFundamentalGroupEquiv`,
the fundamental group being already commutative.

It sends the class of a loop at any point of `E / L` to its period displacement `Γ 1 - Γ 0`, for
any lift `Γ : I → E` of the loop (`AddSubgroup.orbitRelQuotientFirstHomologyEquiv_loopClass`). It is
natural: a continuous additive map `f : E → E'` carrying `L` into `L'` acts on first homology,
through any continuous map of quotients induced by `f`, as the restriction of `f` to the lattices
(`AddSubgroup.orbitRelQuotientFirstHomologyEquiv_singularHomologyMap`).

For a full lattice in a finite-dimensional complex vector space, this identifies the first integral
homology of a complex torus with its period lattice, naturally in the homomorphisms of tori induced
by lattice-preserving linear maps. A discrete submodule `L` of a topological module enters through
`L.toAddSubgroup`, whose orbit space is definitionally that of `L`.

Singular chains with integer coefficients are defined on spaces in the lowest universe, so `E` is a
type in `Type`.

## Main declarations

* `AddSubgroup.orbitRelQuotientFirstHomologyEquiv`: the isomorphism `H₁(E / L; ℤ) ≃ₗ[ℤ] L`.
* `AddSubgroup.orbitRelQuotientFirstHomologyEquiv_hurewiczHomologyAddEquiv`: the Hurewicz class of a
  loop class at any base point corresponds to its image in `L` under the fundamental-group
  identification.
* `AddSubgroup.orbitRelQuotientFirstHomologyEquiv_loopClass`: the period displacement of a lift.
* `AddSubgroup.orbitRelQuotientFirstHomologyEquiv_singularHomologyMap`: naturality in
  lattice-preserving maps.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1.
* A. Hatcher, *Algebraic Topology*, Theorem 2A.1 for the Hurewicz isomorphism in degree one.
-/

public section

noncomputable section

open unitInterval TauCeti TauCeti.HurewiczOne

namespace AddSubgroup

variable {E : Type} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [SimplyConnectedSpace E] (L : AddSubgroup E) [DiscreteTopology L]

/-- **The first homology of a lattice quotient is the lattice.** For a discrete additive subgroup
`L` of a simply connected topological additive commutative group `E`, the first singular homology
group with integer coefficients of `E / L` is `L`: the inverse of the Hurewicz isomorphism at the
class of `0`, followed by the abelianization of `L.orbitRelQuotientFundamentalGroupEquiv`. The
choice of base point does not matter
(`AddSubgroup.orbitRelQuotientFirstHomologyEquiv_hurewiczHomologyAddEquiv`). -/
def orbitRelQuotientFirstHomologyEquiv :
    ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient L E))).homology 1 ≃ₗ[ℤ] L :=
  ((hurewiczHomologyAddEquiv (X := TopCat.of (AddAction.orbitRel.Quotient L E))
      (_root_.Quotient.mk _ 0)).symm.trans
    (MulEquiv.toAdditiveLeft ((L.orbitRelQuotientFundamentalGroupEquiv _).abelianizationCongr.trans
      Abelianization.equivOfComm.symm))).toIntLinearEquiv

/-- The Hurewicz class of a loop class `γ` at any point `x` of `E / L` corresponds to the element
of `L` attached to `γ` by `L.orbitRelQuotientFundamentalGroupEquiv`. -/
@[simp]
theorem orbitRelQuotientFirstHomologyEquiv_hurewiczHomologyAddEquiv
    (x : AddAction.orbitRel.Quotient L E)
    (γ : FundamentalGroup (AddAction.orbitRel.Quotient L E) x) :
    L.orbitRelQuotientFirstHomologyEquiv
        (hurewiczHomologyAddEquiv (X := TopCat.of (AddAction.orbitRel.Quotient L E)) x
          (Additive.ofMul (Abelianization.of γ))) =
      (L.orbitRelQuotientFundamentalGroupEquiv x γ).toAdd := by
  -- Move the loop class to the base point of the definition, which changes neither its Hurewicz
  -- class nor its image in `L`.
  let p := PathConnectedSpace.somePath x (_root_.Quotient.mk (AddAction.orbitRel L E) 0)
  rw [← hurewiczHomologyAddEquiv_fundamentalGroupMulEquivOfPath
      (X := TopCat.of (AddAction.orbitRel.Quotient L E)) p γ,
    ← L.orbitRelQuotientFundamentalGroupEquiv_fundamentalGroupMulEquivOfPath p γ,
    orbitRelQuotientFirstHomologyEquiv, AddEquiv.coe_toIntLinearEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]
  simp

/-- The inverse of `AddSubgroup.orbitRelQuotientFirstHomologyEquiv` sends `l` to the Hurewicz class
of the loop class at any point `x` of `E / L` that corresponds to `l`. -/
theorem orbitRelQuotientFirstHomologyEquiv_symm_apply (x : AddAction.orbitRel.Quotient L E)
    (l : L) :
    L.orbitRelQuotientFirstHomologyEquiv.symm l =
      hurewiczHomologyAddEquiv (X := TopCat.of (AddAction.orbitRel.Quotient L E)) x
        (Additive.ofMul (Abelianization.of
          ((L.orbitRelQuotientFundamentalGroupEquiv x).symm (Multiplicative.ofAdd l)))) := by
  rw [LinearEquiv.symm_apply_eq, orbitRelQuotientFirstHomologyEquiv_hurewiczHomologyAddEquiv,
    MulEquiv.apply_symm_apply, toAdd_ofAdd]

/-- **Period displacement.** The homology class of a loop `γ` in `E / L` corresponds to
`Γ 1 - Γ 0`, for any continuous lift `Γ : I → E` of `γ`. -/
theorem orbitRelQuotientFirstHomologyEquiv_loopClass {x : AddAction.orbitRel.Quotient L E}
    (γ : Path x x) (Γ : C(I, E)) (hΓ : _root_.Quotient.mk (AddAction.orbitRel L E) ∘ Γ = γ) :
    (L.orbitRelQuotientFirstHomologyEquiv
        (H₁AddEquivHomology _ (loopClass (X := TopCat.of (AddAction.orbitRel.Quotient L E)) γ)) :
          E) = Γ 1 - Γ 0 := by
  rw [← hurewiczHomologyAddEquiv_ofMul_of_mk,
    orbitRelQuotientFirstHomologyEquiv_hurewiczHomologyAddEquiv,
    L.orbitRelQuotientFundamentalGroupEquiv_fromPath γ Γ hΓ]

/-- **Naturality.** Let `f : E → E'` be a continuous additive map and `φ : E / L → E' / L'` a
continuous map induced by `f`, so that `f` carries `L` into `L'`. On first homology, `φ` acts as
the restriction of `f` to the lattices. -/
theorem orbitRelQuotientFirstHomologyEquiv_singularHomologyMap {E' : Type} [AddCommGroup E']
    [TopologicalSpace E'] [IsTopologicalAddGroup E'] [SimplyConnectedSpace E']
    (L' : AddSubgroup E') [DiscreteTopology L'] (f : E →+ E') (hf : Continuous f)
    (φ : C(AddAction.orbitRel.Quotient L E, AddAction.orbitRel.Quotient L' E'))
    (hφ : ∀ v, φ (_root_.Quotient.mk _ v) = _root_.Quotient.mk (AddAction.orbitRel L' E') (f v))
    (c : ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient L E))).homology 1) :
    (L'.orbitRelQuotientFirstHomologyEquiv (ContinuousMap.singularHomologyMap ℤ 1 φ c) : E') =
      f (L.orbitRelQuotientFirstHomologyEquiv c) := by
  let x := _root_.Quotient.mk (AddAction.orbitRel L E) 0
  obtain ⟨a, rfl⟩ := (hurewiczHomologyAddEquiv (X := TopCat.of (AddAction.orbitRel.Quotient L E))
    x).surjective c
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
  -- `Abelianization G` is the quotient of `G` by its commutator subgroup and `Abelianization.of`
  -- is `QuotientGroup.mk'`; Mathlib states no surjectivity lemma for `Abelianization.of` itself.
  obtain ⟨γ, rfl⟩ : ∃ γ, Abelianization.of γ = a := QuotientGroup.mk'_surjective _ a
  rw [ContinuousMap.singularHomologyMap, homologyMap_hurewiczHomologyAddEquiv, toMul_ofMul,
    Abelianization.map_of, orbitRelQuotientFirstHomologyEquiv_hurewiczHomologyAddEquiv,
    orbitRelQuotientFirstHomologyEquiv_hurewiczHomologyAddEquiv]
  exact L.orbitRelQuotientFundamentalGroupEquiv_map L' f hf φ hφ x γ

end AddSubgroup
