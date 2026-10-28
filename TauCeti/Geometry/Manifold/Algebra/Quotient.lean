/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Prod
public import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup

/-!
# Quotients of normed spaces by discrete submodules are Lie groups

Let `L` be a discrete submodule of a locally compact normed space `E` over a nontrivially normed
field `𝕜`. The translation action of `L` on `E` is free and properly discontinuous
(`Submodule.properlyDiscontinuousVAdd_of_discreteTopology`) and acts by `C^n` maps
(`SetLike.contMDiffConstVAdd`), so its standard orbit space `AddAction.orbitRel.Quotient L E` is a
`C^n` manifold (`TauCeti.instIsManifoldAddQuotient`) and the orbit projection
`E → AddAction.orbitRel.Quotient L E` is a `C^n` local diffeomorphism
(`TauCeti.isLocalDiffeomorph_addQuotientMk`). This file proves that the quotient, with the
additive group structure of `E ⧸ L` (`Submodule.orbitRelQuotientAddEquiv`), is a `C^n` additive
Lie group. Addition and negation are smooth because near each point of the quotient they are read
through smooth local sections of the orbit projection, namely its local inverses
(`IsLocalDiffeomorph.lieAddGroup`).

For a discrete subgroup `L : Submodule ℤ E` of a finite-dimensional complex vector space `E` and
`n = ω`, this makes `E / L` a complex Lie group. When `L` is moreover a full lattice,
`IsZLattice ℝ L`, the quotient is the complex torus `E / L`; it is compact
(`Submodule.instCompactSpaceOrbitRelQuotient`), Hausdorff
(`t2Space_of_properlyDiscontinuousVAdd_of_t2Space`), connected (`Quotient.instConnectedSpace`)
and second countable (`Submodule.instSecondCountableTopologyOrbitRelQuotient`).

For discrete submodules `L` of `E` and `L'` of `E'`, the quotient of `E × E'` by the product
`L.prod L'` is `C^n` diffeomorphic to the product of the quotients of `E` by `L` and of `E'` by
`L'`, by the additive equivalence `Submodule.orbitRelQuotientProdAddEquiv`. Its inverse is smooth
because it sends `(a, b)` to the sum of the images of `(a, 0)` and `(0, b)`, each descended from
the inclusion of a factor. For full lattices this identifies the complex torus of the product
lattice, a full lattice by `Submodule.instIsZLatticeProd`, with the product of the two complex
tori.

## Main results

* `Submodule.instLieAddGroupOrbitRelQuotient`: the quotient of a locally compact normed space by a
  discrete submodule is a `C^n` additive Lie group; for `𝕜 = ℂ` and `n = ω` it is a complex Lie
  group.
* `Submodule.orbitRelQuotientProdDiffeomorph`: the quotient of `E × E'` by `L.prod L'` is `C^n`
  diffeomorphic to the product of the quotients by `L` and by `L'`, by an additive equivalence.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [LocallyCompactSpace E] {R : Type*} [Ring R] [Module R E] (L : Submodule R E)
  [DiscreteTopology L] {n : ℕ∞ω}

/-- The quotient of a locally compact normed space `E` over `𝕜` by a discrete submodule `L` is a
`C^n` additive Lie group, for its quotient manifold structure and the additive group structure of
`E ⧸ L`. For a discrete subgroup `L : Submodule ℤ E` of a finite-dimensional complex vector space
`E` and `n = ω` it is a complex Lie group. -/
instance Submodule.instLieAddGroupOrbitRelQuotient :
    LieAddGroup 𝓘(𝕜, E) n (AddAction.orbitRel.Quotient L E) :=
  IsLocalDiffeomorph.lieAddGroup
    (AddMonoidHom.mk' (_root_.Quotient.mk (AddAction.orbitRel L E)) L.orbitRelQuotient_mk_add)
    TauCeti.isLocalDiffeomorph_addQuotientMk _root_.Quotient.mk_surjective

section Prod

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [LocallyCompactSpace E']
  [Module R E'] (L' : Submodule R E') [DiscreteTopology L']

/-- The quotient of `E × E'` by the product `L.prod L'` of discrete submodules is `C^n`
diffeomorphic to the product of the quotients of `E` by `L` and of `E'` by `L'`; as a map it is
the additive equivalence `Submodule.orbitRelQuotientProdAddEquiv`. For lattices `L` and `L'` in
finite-dimensional complex vector spaces and `n = ω`, this is the biholomorphic isomorphism of
complex Lie groups between the complex torus `(E × E') / (L × L')` and the product of the complex
tori `E / L` and `E' / L'`. -/
def Submodule.orbitRelQuotientProdDiffeomorph :
    Diffeomorph 𝓘(𝕜, E × E') (𝓘(𝕜, E).prod 𝓘(𝕜, E'))
      (AddAction.orbitRel.Quotient (L.prod L') (E × E'))
      (AddAction.orbitRel.Quotient L E × AddAction.orbitRel.Quotient L' E') n where
  toEquiv := L.orbitRelQuotientProdAddEquiv L'
  contMDiff_toFun := by
    have hL : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n (_root_.Quotient.mk (AddAction.orbitRel L E)) :=
      TauCeti.isLocalDiffeomorph_addQuotientMk.contMDiff
    have hL' : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E') n (_root_.Quotient.mk (AddAction.orbitRel L' E')) :=
      TauCeti.isLocalDiffeomorph_addQuotientMk.contMDiff
    have hcomp : L.orbitRelQuotientProdAddEquiv L' ∘
        _root_.Quotient.mk (AddAction.orbitRel (L.prod L') (E × E')) =
          fun x ↦ (_root_.Quotient.mk _ x.1, _root_.Quotient.mk _ x.2) :=
      funext <| L.orbitRelQuotientProdAddEquiv_mk L'
    rw [AddEquiv.coe_toEquiv,
      ← (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E × E')) (n := n)).contMDiff_comp_iff
        _root_.Quotient.mk_surjective le_rfl, hcomp]
    exact (hL.comp contDiff_fst.contMDiff).prodMk (hL'.comp contDiff_snd.contMDiff)
  contMDiff_invFun := by
    -- The inverse sends `(a, b)` to `e.symm (a, 0) + e.symm (0, b)`. Each summand is descended
    -- from an inclusion of a factor into `E × E'`, and addition on the quotient is smooth.
    set e := L.orbitRelQuotientProdAddEquiv L'
    have hq : ContMDiff 𝓘(𝕜, E × E') 𝓘(𝕜, E × E') n
        (_root_.Quotient.mk (AddAction.orbitRel (L.prod L') (E × E'))) :=
      TauCeti.isLocalDiffeomorph_addQuotientMk.contMDiff
    have h₁ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E × E') n fun a ↦ e.symm (a, 0) := by
      have hcomp : (fun a ↦ e.symm (a, 0)) ∘ _root_.Quotient.mk (AddAction.orbitRel L E) =
          _root_.Quotient.mk (AddAction.orbitRel (L.prod L') (E × E')) ∘ fun x ↦ (x, 0) :=
        funext fun x ↦ by
          simp only [Function.comp_apply]
          rw [← L'.orbitRelQuotient_mk_zero, L.orbitRelQuotientProdAddEquiv_symm_mk]
      rw [← (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E)) (n := n)).contMDiff_comp_iff
        _root_.Quotient.mk_surjective le_rfl, hcomp]
      exact hq.comp (contDiff_id.prodMk contDiff_const).contMDiff
    have h₂ : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E × E') n fun b ↦ e.symm (0, b) := by
      have hcomp : (fun b ↦ e.symm (0, b)) ∘ _root_.Quotient.mk (AddAction.orbitRel L' E') =
          _root_.Quotient.mk (AddAction.orbitRel (L.prod L') (E × E')) ∘ fun y ↦ (0, y) :=
        funext fun y ↦ by
          simp only [Function.comp_apply]
          rw [← L.orbitRelQuotient_mk_zero, L.orbitRelQuotientProdAddEquiv_symm_mk]
      rw [← (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E')) (n := n)).contMDiff_comp_iff
        _root_.Quotient.mk_surjective le_rfl, hcomp]
      exact hq.comp (contDiff_const.prodMk contDiff_id).contMDiff
    have h : ⇑e.symm = fun z ↦ e.symm (z.1, 0) + e.symm (0, z.2) :=
      funext fun z ↦ by rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [AddEquiv.coe_toEquiv_symm, h]
    exact (h₁.comp contMDiff_fst).add (h₂.comp contMDiff_snd)

/-- As a map, the diffeomorphism `Submodule.orbitRelQuotientProdDiffeomorph` is the additive
equivalence `Submodule.orbitRelQuotientProdAddEquiv`. -/
@[simp]
theorem Submodule.coe_orbitRelQuotientProdDiffeomorph :
    ⇑(L.orbitRelQuotientProdDiffeomorph L' (𝕜 := 𝕜) (n := n)) =
      L.orbitRelQuotientProdAddEquiv L' :=
  (rfl)

/-- As a map, the inverse of `Submodule.orbitRelQuotientProdDiffeomorph` is the inverse of the
additive equivalence `Submodule.orbitRelQuotientProdAddEquiv`. -/
@[simp]
theorem Submodule.coe_orbitRelQuotientProdDiffeomorph_symm :
    ⇑(L.orbitRelQuotientProdDiffeomorph L' (𝕜 := 𝕜) (n := n)).symm =
      (L.orbitRelQuotientProdAddEquiv L').symm :=
  (rfl)

end Prod
