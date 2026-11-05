/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Basic
public import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup
public import TauCeti.Topology.Algebra.Module.Submodule
import Mathlib.Analysis.LocallyConvex.HahnBanach
import TauCeti.Algebra.Module.ZLattice.Ker
import TauCeti.Algebra.Module.ZLattice.Quotient
import TauCeti.Geometry.Manifold.Immersion.Basic

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

For discrete submodules `L` of `E` and `L'` of `E'`, the quotient of `E × E'` by the product
`L.prod L'` is `C^n` diffeomorphic to the product of the quotients of `E` by `L` and of `E'` by
`L'`, by the additive equivalence `Submodule.orbitRelQuotientProdAddEquiv`. For full lattices this
identifies the complex torus of the product lattice, a full lattice by
`Submodule.instIsZLatticeProd`, with the product of the two complex tori.

Immersions descend in the same way: a map of quotients induced by a `C^n` immersion of the
ambient spaces is a `C^n` immersion, because the orbit projections are local diffeomorphisms. For
a subspace `V` of `E` with a closed complement, the inclusion of `V` is an immersion, so the map
`V / (L ∩ V) → E / L` it induces is an immersion. When moreover `V / (L ∩ V)` is compact, for
instance when `L ∩ V` is a full lattice in `V`, this map is a `C^n` embedding. For a complex
linear map `f : E → E'` carrying a full lattice `L` into a discrete subgroup `L'`, this embeds the
complex torus `ker f / (L ∩ ker f)` holomorphically into `E / L`, with image the identity
component of the kernel `f⁻¹(L') / L` of the induced homomorphism of complex Lie groups
(`Submodule.range_orbitRelQuotientMap_ker_subtype`).

## Main results

* `Submodule.instLieAddGroupOrbitRelQuotient`: the quotient of a locally compact normed space by a
  discrete submodule is a `C^n` additive Lie group; for `𝕜 = ℂ` and `n = ω` it is a complex Lie
  group.
* `Submodule.contMDiff_orbitRelQuotient_of_comp_mk`: a map of quotients by discrete submodules
  induced by a `C^n` map of the ambient spaces is `C^n`.
* `Submodule.contMDiff_orbitRelQuotientMap`: a `C^n` semilinear map carrying `L` into `L'` induces
  a `C^n` map of quotients.
* `Submodule.isImmersion_orbitRelQuotient_of_comp_mk`: a map of quotients by discrete submodules
  induced by a `C^n` immersion of the ambient spaces is a `C^n` immersion.
* `Submodule.orbitRelQuotientDiffeomorph`: a semilinear equivalence carrying `L` onto `L'` which is
  `C^n` in both directions induces a `C^n` diffeomorphism of quotients, which is additive.
* `Submodule.orbitRelQuotientProdDiffeomorph`: the quotient of `E × E'` by `L.prod L'` is `C^n`
  diffeomorphic to the product of the quotients by `L` and by `L'`, by an additive equivalence.
* `Submodule.isImmersion_orbitRelQuotientMap_subtype`: for a subspace `V` with a closed
  complement, the map `V / (L ∩ V) → E / L` induced by the inclusion is a `C^n` immersion.
* `Submodule.isSmoothEmbedding_orbitRelQuotientMap_subtype`: if moreover `V / (L ∩ V)` is
  compact, this map is a `C^n` embedding.
* `Submodule.isSmoothEmbedding_orbitRelQuotientMap_ker_subtype`: for a real or complex linear map
  `f` carrying a full lattice `L` into a discrete subgroup, the torus `ker f / (L ∩ ker f)` embeds
  into `E / L`; for complex `f` the embedding is holomorphic.

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

variable {L} in
/-- A map `g` of quotients by discrete submodules that is induced by a `C^n` map `f` of the ambient
spaces, in the sense that `g` sends the class of `x` to the class of `f x`, is `C^n`. -/
theorem Submodule.contMDiff_orbitRelQuotient_of_comp_mk {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [LocallyCompactSpace F] {S : Type*} [Ring S] [Module S F]
    {P : Submodule S F} [DiscreteTopology P]
    {g : AddAction.orbitRel.Quotient L E → AddAction.orbitRel.Quotient P F} {f : E → F}
    (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n f)
    (hg : g ∘ _root_.Quotient.mk (AddAction.orbitRel L E) =
      _root_.Quotient.mk (AddAction.orbitRel P F) ∘ f) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n g := by
  rw [← (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E)) (n := n)).contMDiff_comp_iff
    _root_.Quotient.mk_surjective le_rfl, hg]
  exact TauCeti.isLocalDiffeomorph_addQuotientMk.contMDiff.comp hf

variable {L} in
/-- A map `g` of quotients by discrete submodules that is induced by a `C^n` immersion `f` of the
ambient spaces, in the sense that `g` sends the class of `x` to the class of `f x`, is a `C^n`
immersion: near the class of `x`, `g` is `f` read through the orbit projections, which are local
diffeomorphisms. -/
theorem Submodule.isImmersion_orbitRelQuotient_of_comp_mk {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [LocallyCompactSpace F] {S : Type*} [Ring S] [Module S F]
    {P : Submodule S F} [DiscreteTopology P]
    {g : AddAction.orbitRel.Quotient L E → AddAction.orbitRel.Quotient P F} {f : E → F}
    (hf : Manifold.IsImmersion 𝓘(𝕜, E) 𝓘(𝕜, F) n f)
    (hg : g ∘ _root_.Quotient.mk (AddAction.orbitRel L E) =
      _root_.Quotient.mk (AddAction.orbitRel P F) ∘ f) :
    Manifold.IsImmersion 𝓘(𝕜, E) 𝓘(𝕜, F) n g := by
  refine Manifold.IsImmersionOfComplement.isImmersion (F := hf.complement) fun y ↦ ?_
  induction y using _root_.Quotient.inductionOn with | h x => ?_
  have h := TauCeti.isImmersionAtOfComplement_isLocalDiffeomorphAt_comp
    (TauCeti.isLocalDiffeomorph_addQuotientMk (G := P) (f x))
    (hf.isImmersionOfComplement_complement x)
  rw [← hg] at h
  exact (TauCeti.isImmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff
    (TauCeti.isLocalDiffeomorph_addQuotientMk (G := L) x)).1 h

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
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n (L.orbitRelQuotientMap L' f h) :=
  Submodule.contMDiff_orbitRelQuotient_of_comp_mk hf.contMDiff <|
    funext <| L.orbitRelQuotientMap_mk L' f h

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
    have h₁ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E × E') n fun a ↦ e.symm (a, 0) :=
      Submodule.contMDiff_orbitRelQuotient_of_comp_mk (f := fun x ↦ (x, 0))
        (contDiff_id.prodMk contDiff_const).contMDiff <| funext fun x ↦ by
          simp only [Function.comp_apply]
          rw [← L'.orbitRelQuotient_mk_zero, L.orbitRelQuotientProdAddEquiv_symm_mk]
    have h₂ : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E × E') n fun b ↦ e.symm (0, b) :=
      Submodule.contMDiff_orbitRelQuotient_of_comp_mk (f := fun y ↦ (0, y))
        (contDiff_const.prodMk contDiff_id).contMDiff <| funext fun y ↦ by
          simp only [Function.comp_apply]
          rw [← L.orbitRelQuotient_mk_zero, L.orbitRelQuotientProdAddEquiv_symm_mk]
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

section Subtorus

/-- For a subspace `V` of `E` with a closed complement and a discrete subgroup `L` of `E`, the map
`V / (L ∩ V) → E / L` induced by the inclusion of `V` is a `C^n` immersion. It need not be an
embedding: a line of irrational slope in `ℝ²` meets `ℤ²` only in `0`, and its image in `ℝ² / ℤ²` is
dense. -/
theorem Submodule.isImmersion_orbitRelQuotientMap_subtype (L : Submodule ℤ E) [DiscreteTopology L]
    (V : Submodule 𝕜 E) [LocallyCompactSpace V] (hV : V.ClosedComplemented) :
    Manifold.IsImmersion 𝓘(𝕜, V) 𝓘(𝕜, E) n
      ((ZLattice.comap 𝕜 L V.subtype).orbitRelQuotientMap L (V.subtype.restrictScalars ℤ)
        le_rfl) := by
  obtain ⟨p, hp⟩ := hV
  have hι : V.subtypeL.HasLeftInverse := ⟨p, fun x ↦ hp x⟩
  exact Submodule.isImmersion_orbitRelQuotient_of_comp_mk hι.isImmersion <|
    funext <| (ZLattice.comap 𝕜 L V.subtype).orbitRelQuotientMap_mk L _ le_rfl

/-- For a subspace `V` of `E` with a closed complement and a discrete subgroup `L` of `E` such that
`V / (L ∩ V)` is compact, the map `V / (L ∩ V) → E / L` induced by the inclusion of `V` is a `C^n`
embedding, with closed image. Compactness holds when `L ∩ V` is a full lattice in a
finite-dimensional real space `V`; for complex `V` and `n = ω`, this is a holomorphic embedding of
the complex torus `V / (L ∩ V)` into `E / L`. -/
theorem Submodule.isSmoothEmbedding_orbitRelQuotientMap_subtype (L : Submodule ℤ E)
    [DiscreteTopology L] (V : Submodule 𝕜 E) [LocallyCompactSpace V]
    [CompactSpace (AddAction.orbitRel.Quotient (ZLattice.comap 𝕜 L V.subtype) V)]
    (hV : V.ClosedComplemented) :
    Manifold.IsSmoothEmbedding 𝓘(𝕜, V) 𝓘(𝕜, E) n
      ((ZLattice.comap 𝕜 L V.subtype).orbitRelQuotientMap L (V.subtype.restrictScalars ℤ)
        le_rfl) := by
  refine ⟨L.isImmersion_orbitRelQuotientMap_subtype V hV, ?_⟩
  -- A continuous injection of a compact space into a Hausdorff space is an embedding.
  refine (Continuous.isClosedEmbedding ?_ ?_).isEmbedding
  · exact Submodule.continuous_orbitRelQuotientMap _ _ _ continuous_subtype_val
  · exact (Submodule.orbitRelQuotientMap_injective_iff _ _ _ _).2 le_rfl

/-- Let a linear map `f : E → E'` over `𝕜 = ℝ` or `ℂ` carry a full lattice `L` into a discrete
subgroup `L'`. Then the map of quotients `ker f / (L ∩ ker f) → E / L` induced by the inclusion of
`ker f` is a `C^n` embedding of the torus `ker f / (L ∩ ker f)`, whose full lattice is
`ZLattice.isZLattice_comap_ker_subtype`. Its image is the identity component of the kernel
`f⁻¹(L') / L` of the map `E / L → E' / L'` induced by `f`
(`Submodule.range_orbitRelQuotientMap_ker_subtype`). For `𝕜 = ℂ` and `n = ω`, this is a
holomorphic embedding of complex tori. -/
theorem Submodule.isSmoothEmbedding_orbitRelQuotientMap_ker_subtype {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    [FiniteDimensional ℝ E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedSpace 𝕜 E'] [IsScalarTower ℝ 𝕜 E'] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {L' : Submodule ℤ E'} [DiscreteTopology L'] (f : E →ₗ[𝕜] E')
    (hf : L.map (f.restrictScalars ℤ) ≤ L') :
    Manifold.IsSmoothEmbedding 𝓘(𝕜, LinearMap.ker f) 𝓘(𝕜, E) n
      ((ZLattice.comap 𝕜 L (LinearMap.ker f).subtype).orbitRelQuotientMap L
        ((LinearMap.ker f).subtype.restrictScalars ℤ) le_rfl) := by
  have := ZLattice.isZLattice_comap_ker_subtype L f hf
  have : FiniteDimensional ℝ (LinearMap.ker f) :=
    .of_injective ((LinearMap.ker f).subtype.restrictScalars ℝ) (LinearMap.ker f).injective_subtype
  have : FiniteDimensional 𝕜 (LinearMap.ker f) := .of_restrictScalars_finite ℝ 𝕜 _
  exact L.isSmoothEmbedding_orbitRelQuotientMap_subtype _ (.of_finiteDimensional _)

end Subtorus
