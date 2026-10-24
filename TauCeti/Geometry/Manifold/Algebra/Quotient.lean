/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
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

A `C^n` semilinear map `f : E → E'` carrying `L` into a discrete submodule `L'` of `E'` induces the
additive map `Submodule.orbitRelQuotientMap` of quotients, and this map is `C^n`, because its
composite with the orbit projection of `E` is the composite of `f` with the orbit projection of
`E'`. For complex tori this is the holomorphic homomorphism `E / L → E' / L'` induced by a complex
linear map `f` with `f(L) ⊆ L'`: take `n = ω` and the restriction of scalars of `f` to `ℤ`, which
is smooth since a linear map out of a finite-dimensional space is continuous. Likewise a
continuous linear equivalence carrying `L` onto `L'` induces a biholomorphic isomorphism of complex
tori.

## Main results

* `Submodule.instLieAddGroupOrbitRelQuotient`: the quotient of a locally compact normed space by a
  discrete submodule is a `C^n` additive Lie group; for `𝕜 = ℂ` and `n = ω` it is a complex Lie
  group.
* `Submodule.contMDiff_orbitRelQuotientMap`: a `C^n` semilinear map carrying `L` into `L'` induces
  a `C^n` map of quotients.
* `Submodule.orbitRelQuotientDiffeomorph`: a semilinear equivalence carrying `L` onto `L'` which is
  `C^n` in both directions induces a `C^n` diffeomorphism of quotients, which is additive.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Sections 1.1
  and 1.2.
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

section Map

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [LocallyCompactSpace E']
  {R' : Type*} [Ring R'] [Module R' E'] (L' : Submodule R' E') [DiscreteTopology L']

/-- A semilinear map `f : E → E'` carrying `L` into `L'` which is `C^n` induces a `C^n` map from
the quotient of `E` by `L` to the quotient of `E'` by `L'`. For a complex linear map `f` between
finite-dimensional complex vector spaces with `f(L) ⊆ L'` for lattices `L` and `L'`, applied to
`n = ω` and the restriction of scalars of `f` to `ℤ`, this is the holomorphic homomorphism of
complex tori `E / L → E' / L'` induced by `f`. -/
theorem Submodule.contMDiff_orbitRelQuotientMap {τ : R →+* R'} (f : E →ₛₗ[τ] E')
    (h : L ≤ L'.comap f) (hf : ContDiff 𝕜 n f) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n (L.orbitRelQuotientMap L' f h) := by
  have hcomp : L.orbitRelQuotientMap L' f h ∘ _root_.Quotient.mk (AddAction.orbitRel L E) =
      _root_.Quotient.mk (AddAction.orbitRel L' E') ∘ f :=
    funext <| L.orbitRelQuotientMap_mk L' f h
  rw [← (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E)) (n := n)).contMDiff_comp_iff
    _root_.Quotient.mk_surjective le_rfl, hcomp]
  exact TauCeti.isLocalDiffeomorph_addQuotientMk.contMDiff.comp hf.contMDiff

variable {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- A semilinear equivalence `e : E ≃ E'` carrying `L` onto `L'` which is `C^n` in both directions
induces a `C^n` diffeomorphism from the quotient of `E` by `L` to the quotient of `E'` by `L'`; as
a map it is the additive equivalence `Submodule.orbitRelQuotientCongr`. For a continuous complex
linear equivalence carrying a lattice `L` onto a lattice `L'`, applied to `n = ω` and the
restriction of scalars to `ℤ`, this is the biholomorphic isomorphism of complex tori
`E / L ≃ E' / L'` induced by `e`. -/
def Submodule.orbitRelQuotientDiffeomorph (e : E ≃ₛₗ[σ] E') (he : L.map (e : E →ₛₗ[σ] E') = L')
    (hf : ContDiff 𝕜 n e) (hg : ContDiff 𝕜 n e.symm) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') (AddAction.orbitRel.Quotient L E)
      (AddAction.orbitRel.Quotient L' E') n where
  toEquiv := (L.orbitRelQuotientCongr L' e he).toEquiv
  contMDiff_toFun := by
    have h := L.contMDiff_orbitRelQuotientMap L' (e : E →ₛₗ[σ] E')
      (Submodule.map_le_iff_le_comap.1 he.le) hf
    rwa [← L.coe_orbitRelQuotientCongr L' e he, AddMonoidHom.coe_ofClass] at h
  contMDiff_invFun := by
    have he' := (Submodule.map_symm_eq_iff e).2 he
    have h := L'.contMDiff_orbitRelQuotientMap L (e.symm : E' →ₛₗ[σ'] E)
      (Submodule.map_le_iff_le_comap.1 he'.le) hg
    rwa [← L'.coe_orbitRelQuotientCongr L e.symm he', AddMonoidHom.coe_ofClass,
      ← L.orbitRelQuotientCongr_symm L' e he] at h

/-- As a map, the diffeomorphism of quotients induced by `e` is the additive equivalence
`Submodule.orbitRelQuotientCongr` induced by `e`. -/
@[simp]
theorem Submodule.coe_orbitRelQuotientDiffeomorph (e : E ≃ₛₗ[σ] E')
    (he : L.map (e : E →ₛₗ[σ] E') = L') (hf : ContDiff 𝕜 n e) (hg : ContDiff 𝕜 n e.symm) :
    ⇑(L.orbitRelQuotientDiffeomorph L' e he hf hg) = L.orbitRelQuotientCongr L' e he :=
  (rfl)

/-- The inverse of the diffeomorphism of quotients induced by `e` is the diffeomorphism induced
by `e.symm`. -/
@[simp]
theorem Submodule.orbitRelQuotientDiffeomorph_symm (e : E ≃ₛₗ[σ] E')
    (he : L.map (e : E →ₛₗ[σ] E') = L') (hf : ContDiff 𝕜 n e) (hg : ContDiff 𝕜 n e.symm) :
    (L.orbitRelQuotientDiffeomorph L' e he hf hg).symm =
      L'.orbitRelQuotientDiffeomorph L e.symm ((Submodule.map_symm_eq_iff e).2 he) hg hf := by
  ext x
  rw [← Diffeomorph.toEquiv_coe_symm]
  exact DFunLike.congr_fun (L.orbitRelQuotientCongr_symm L' e he) x

end Map
