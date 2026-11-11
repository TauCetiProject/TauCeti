/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Basic
public import TauCeti.Algebra.Module.ZLattice.Quotient
public import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Algebra.Subgroup
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup
public import TauCeti.Topology.Algebra.Module.Submodule
public import TauCeti.Topology.Covering.Quotient
import Mathlib.Analysis.LocallyConvex.HahnBanach
import TauCeti.Algebra.Module.ZLattice.Ker
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Topology.Algebra.Module.DiscretePreimage

/-!
# Smooth quotients by discrete subgroups and submodules

## Discrete subgroups of Lie groups

For a discrete subgroup `N` of a Lie group `G`, the coset space `G ⧸ N` is a manifold
with the same model as `G`, and the projection is a local diffeomorphism
(`Subgroup.isLocalDiffeomorph_quotientMk`). Neither normality nor local compactness is needed.
If `N` is normal, the quotient is a Lie group, and smooth homomorphisms trivial on `N`
descend smoothly (`Subgroup.contMDiff_quotientGroup_lift`). These results apply to discrete
normal subgroups, including finite central kernels of representations.

The covering input is Mathlib's `Subgroup.isQuotientCoveringMap`. The charts and local
diffeomorphism use `IsLocalHomeomorph.isManifold_chartedSpaceOfRightInverse` and
`IsLocalHomeomorph.isLocalDiffeomorph_chartedSpaceOfRightInverse`. The Lie group structure
and smooth descent criterion use `IsLocalDiffeomorph.lieGroup` and
`IsLocalDiffeomorph.contMDiff_comp_iff`, respectively.

## Discrete submodules of normed spaces

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

That identity component is an open subgroup of the kernel, so the kernel is a union of
translates of the torus `ker f / (L ∩ ker f)`. Translating the charts of this torus makes the
kernel a `C^n` Lie group modelled on `ker f`
(`AddSubgroup.lieAddGroup_chartedSpaceOfIsOpenEmbedding`) whose inclusion into `E / L` is a `C^n`
embedding. For complex `f` the kernel is thus a closed
complex Lie subgroup of `E / L`, and the torus `ker f / (L ∩ ker f)` is biholomorphic onto its
identity component.

## Main results

### Discrete subgroups

The following results also have additive counterparts in the `AddSubgroup` namespace.

* `Subgroup.isLocalDiffeomorph_quotientMk`: the coset projection by a discrete subgroup is a
  local diffeomorphism.
* `Subgroup.instLieGroupDiscreteQuotient`: the quotient by a discrete normal subgroup is a
  Lie group.
* `Subgroup.contMDiff_quotient_iff`: smoothness on the coset space is equivalent to smoothness
  after composition with the projection.
* `Subgroup.contMDiff_quotientGroup_lift`: a smooth homomorphism killing a discrete normal
  subgroup descends smoothly to the quotient group.

### Discrete submodules

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
* `Submodule.instLieAddGroupKerOrbitRelQuotientMap`: the kernel `f⁻¹(L') / L` of the induced map
  `E / L → E' / L'` is a `C^n` additive Lie group modelled on `ker f`; for complex `f` it is a
  complex Lie group.
* `Submodule.isSmoothEmbedding_subtypeVal_ker_orbitRelQuotientMap`: the inclusion of that kernel
  into `E / L` is a `C^n` embedding.
* `Submodule.isOpenEmbedding_orbitRelQuotientToKerOrbitRelQuotientMap`,
  `Submodule.isLocalDiffeomorph_orbitRelQuotientToKerOrbitRelQuotientMap`: the torus
  `ker f / (L ∩ ker f)` is an open subgroup of the kernel, included by a `C^n` local
  diffeomorphism.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 21.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Sections 1.1
  and 1.2.
-/

public section

open scoped Manifold ContDiff

noncomputable section

open Topology

namespace Subgroup

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace H G]
  (N : Subgroup G) [DiscreteTopology N]

/-- The charts on the native coset space are pushed forward from the Lie group along the
covering projection. -/
@[to_additive /-- The charts on the native additive coset space are pushed forward from the
additive Lie group along the covering projection. -/]
instance instChartedSpaceDiscreteQuotient : ChartedSpace H (G ⧸ N) :=
  N.isLocalHomeomorph_quotientMk.chartedSpace QuotientGroup.mk_surjective

variable [LieGroup I n G]

omit [IsTopologicalGroup G] [DiscreteTopology N] in
/-- Right multiplication by a subgroup element is a smooth deck transformation. -/
@[to_additive /-- Translation by a subgroup element is a smooth deck transformation. -/]
private theorem quotientMk_smooth_deck (z w : G)
    (h : (QuotientGroup.mk z : G ⧸ N) = QuotientGroup.mk w) :
    ∃ φ : G → G, ContMDiffAt I I n φ z ∧ φ z = w ∧
      QuotientGroup.mk (s := N) ∘ φ =ᶠ[nhds z] QuotientGroup.mk (s := N) := by
  have hn : z⁻¹ * w ∈ N := QuotientGroup.eq.mp h
  refine ⟨fun x ↦ x * (z⁻¹ * w), (contMDiff_id.mul contMDiff_const).contMDiffAt,
    by simp, Filter.Eventually.of_forall fun x ↦ ?_⟩
  exact QuotientGroup.eq.mpr (by simpa using N.inv_mem hn)

/-- A discrete subgroup's native coset space is a manifold, with the same model as the group. -/
@[to_additive /-- A discrete additive subgroup's native coset space is a manifold, with the same
model as the additive group. -/]
instance instIsManifoldDiscreteQuotient : IsManifold I n (G ⧸ N) :=
  (isLocalHomeomorph_quotientMk N).isManifold_chartedSpaceOfRightInverse (I := I) (n := n)
    QuotientGroup.mk_surjective.hasRightInverse.choose_spec (quotientMk_smooth_deck N)

/-- The native coset projection is a local diffeomorphism for the pushed-forward charts. -/
@[to_additive /-- The native additive coset projection is a local diffeomorphism for the
pushed-forward charts. -/]
theorem isLocalDiffeomorph_quotientMk :
    IsLocalDiffeomorph I I n (QuotientGroup.mk (s := N)) :=
  (isLocalHomeomorph_quotientMk N).isLocalDiffeomorph_chartedSpaceOfRightInverse (I := I) (n := n)
    QuotientGroup.mk_surjective.hasRightInverse.choose_spec (quotientMk_smooth_deck N)

/-- Quotients by discrete normal subgroups are Lie groups for their native group structure
and the covering charts. -/
@[to_additive /-- Quotients by discrete normal additive subgroups are additive Lie groups for
their native additive group structure and the covering charts. -/]
instance instLieGroupDiscreteQuotient [N.Normal] : LieGroup I n (G ⧸ N) :=
  (isLocalDiffeomorph_quotientMk (I := I) (n := n) N).lieGroup
    (QuotientGroup.mk' N) QuotientGroup.mk_surjective

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

/-- A map out of the native coset space is smooth if and only if it is smooth on the covering
group, for any differentiability order `m ≤ n`, where `n` is the regularity of the group. -/
@[to_additive /-- A map out of the native additive coset space is smooth if and only if it is
smooth on the covering additive group, for any differentiability order `m ≤ n`, where `n` is the
regularity of the additive group. -/]
theorem contMDiff_quotient_iff {m : ℕ∞ω} (hm : m ≤ n) (f : G ⧸ N → M) :
    ContMDiff I I' m f ↔ ContMDiff I I' m (f ∘ QuotientGroup.mk (s := N)) :=
  ((isLocalDiffeomorph_quotientMk (I := I) (n := n) N).contMDiff_comp_iff
    QuotientGroup.mk_surjective hm).symm

/-- A smooth homomorphism killing a discrete normal subgroup descends smoothly to the native
quotient group. The target need only be a charted monoid, such as an endomorphism monoid;
its operations need not be smooth. -/
@[to_additive /-- A smooth additive homomorphism killing a discrete normal additive subgroup
descends smoothly to the native quotient additive group. The target need only be a charted
additive monoid; its operations need not be smooth. -/]
theorem contMDiff_quotientGroup_lift [N.Normal] [Monoid M] (f : G →* M) (hN : N ≤ f.ker)
    {m : ℕ∞ω} (hm : m ≤ n) (hf : ContMDiff I I' m f) :
    ContMDiff I I' m (QuotientGroup.lift N f hN) := by
  apply (N.contMDiff_quotient_iff (I := I) hm _).mpr
  simpa only [Function.comp_def, QuotientGroup.lift_mk] using hf

end Subgroup

end

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
    [FiniteDimensional ℝ E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {L' : Submodule ℤ E'}
    [DiscreteTopology L'] (f : E →ₗ[𝕜] E') (hf : L.map (f.restrictScalars ℤ) ≤ L') :
    Manifold.IsSmoothEmbedding 𝓘(𝕜, LinearMap.ker f) 𝓘(𝕜, E) n
      ((ZLattice.comap 𝕜 L (LinearMap.ker f).subtype).orbitRelQuotientMap L
        ((LinearMap.ker f).subtype.restrictScalars ℤ) le_rfl) := by
  -- `ZLattice.isZLattice_comap_ker_subtype` counts ranks over `ℝ`; give `E'` the real structure
  -- obtained by restricting scalars.
  let : NormedSpace ℝ E' := NormedSpace.restrictScalars ℝ 𝕜 E'
  have : IsScalarTower ℝ 𝕜 E' := Real.isScalarTower
  have := ZLattice.isZLattice_comap_ker_subtype L f hf
  have : FiniteDimensional ℝ (LinearMap.ker f) :=
    .of_injective ((LinearMap.ker f).subtype.restrictScalars ℝ) (LinearMap.ker f).injective_subtype
  have : FiniteDimensional 𝕜 (LinearMap.ker f) := .of_restrictScalars_finite ℝ 𝕜 _
  exact L.isSmoothEmbedding_orbitRelQuotientMap_subtype _ (.of_finiteDimensional _)

end Subtorus

section Kernel

open Topology

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E] [FiniteDimensional ℝ E] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (L : Submodule ℤ E) [DiscreteTopology L]
  [IsZLattice ℝ L] {L' : Submodule ℤ E'} [DiscreteTopology L'] (f : E →ₗ[𝕜] E')
  (h : L ≤ L'.comap (f.restrictScalars ℤ))

/-- The torus `ker f / (L ∩ ker f)` is an open subgroup of the kernel `f⁻¹(L') / L` of the map
`E / L → E' / L'` induced by `f`. -/
theorem Submodule.isOpenEmbedding_orbitRelQuotientToKerOrbitRelQuotientMap :
    IsOpenEmbedding (L.orbitRelQuotientToKerOrbitRelQuotientMap f h) := by
  set j := (ZLattice.comap 𝕜 L (LinearMap.ker f).subtype).orbitRelQuotientMap L
    ((LinearMap.ker f).subtype.restrictScalars ℤ) le_rfl
  have hemb := (Submodule.isSmoothEmbedding_orbitRelQuotientMap_ker_subtype (n := 0) L f
    (Submodule.map_le_iff_le_comap.2 h)).isEmbedding
  have hcoe : Subtype.val ∘ L.orbitRelQuotientToKerOrbitRelQuotientMap f h = j :=
    funext (L.coe_orbitRelQuotientToKerOrbitRelQuotientMap f h)
  refine ⟨IsEmbedding.subtypeVal.of_comp_iff.1 (hcoe ▸ hemb), ?_⟩
  have : FiniteDimensional 𝕜 E := .of_restrictScalars_finite ℝ 𝕜 E
  obtain ⟨U, hU, hUK⟩ := Submodule.exists_isOpen_inter_orbitRelQuotient_mk_image_preimage L f
    (LinearMap.continuous_of_finiteDimensional f) (Submodule.map_le_iff_le_comap.2 h)
  have hK : ((L.orbitRelQuotientMap L' (f.restrictScalars ℤ) h).ker :
      Set (AddAction.orbitRel.Quotient L E)) =
        _root_.Quotient.mk (AddAction.orbitRel L E) '' (f ⁻¹' L') := by
    simp [Submodule.ker_orbitRelQuotientMap]
  have hj : Set.range j = _root_.Quotient.mk (AddAction.orbitRel L E) '' (LinearMap.ker f) :=
    (Submodule.range_orbitRelQuotientMap _ _ _ _).trans <| congrArg _ <| by ext; simp
  -- The range is the trace of `U` on the kernel.
  convert hU.preimage continuous_subtype_val using 1
  ext ⟨z, hz⟩
  have hzK : z ∈ _root_.Quotient.mk (AddAction.orbitRel L E) '' (f ⁻¹' L') := hK ▸ hz
  have hzU : z ∈ U ↔ z ∈ Set.range j := by
    rw [hj, ← hUK, Set.mem_inter_iff, and_iff_left hzK]
  rw [Set.mem_preimage, hzU]
  exact ⟨fun ⟨t, ht⟩ ↦ ⟨t, (congrFun hcoe t).symm.trans (congrArg Subtype.val ht)⟩,
    fun ⟨t, ht⟩ ↦ ⟨t, Subtype.ext ((congrFun hcoe t).trans ht)⟩⟩

/-- The kernel `f⁻¹(L') / L` of the homomorphism `E / L → E' / L'` induced by `f` is charted on
`ker f`: near each of its points it is a translate of the torus `ker f / (L ∩ ker f)`, which is an
open subgroup of the kernel. -/
noncomputable instance Submodule.instChartedSpaceKerOrbitRelQuotientMap :
    ChartedSpace (LinearMap.ker f) (L.orbitRelQuotientMap L' (f.restrictScalars ℤ) h).ker :=
  AddSubgroup.chartedSpaceOfIsOpenEmbedding _ (L.orbitRelQuotientToKerOrbitRelQuotientMap f h)
    (Submodule.isOpenEmbedding_orbitRelQuotientToKerOrbitRelQuotientMap L f h)

/-- For the charts `Submodule.instChartedSpaceKerOrbitRelQuotientMap`, the inclusion of the torus
`ker f / (L ∩ ker f)` into the kernel `f⁻¹(L') / L` is a `C^n` local diffeomorphism. Since it is
also an open embedding (`Submodule.isOpenEmbedding_orbitRelQuotientToKerOrbitRelQuotientMap`), it
identifies the torus with the identity component of the kernel; for `𝕜 = ℂ` and `n = ω` this
identification is biholomorphic. -/
theorem Submodule.isLocalDiffeomorph_orbitRelQuotientToKerOrbitRelQuotientMap :
    IsLocalDiffeomorph 𝓘(𝕜, LinearMap.ker f) 𝓘(𝕜, LinearMap.ker f) n
      (L.orbitRelQuotientToKerOrbitRelQuotientMap f h) :=
  AddSubgroup.isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding _

private theorem isImmersion_coe_orbitRelQuotientToKerOrbitRelQuotientMap :
    Manifold.IsImmersion 𝓘(𝕜, LinearMap.ker f) 𝓘(𝕜, E) n fun t ↦
      (L.orbitRelQuotientToKerOrbitRelQuotientMap f h t : AddAction.orbitRel.Quotient L E) := by
  -- Followed by the inclusion of the kernel, the codomain restriction is the map of quotients
  -- induced by the inclusion of `ker f`.
  simpa only [Submodule.coe_orbitRelQuotientToKerOrbitRelQuotientMap] using
    (Submodule.isSmoothEmbedding_orbitRelQuotientMap_ker_subtype L f
      (Submodule.map_le_iff_le_comap.2 h)).isImmersion

/-- **The kernel of an induced homomorphism of tori is a Lie group.** Let a linear map
`f : E → E'` over `𝕜 = ℝ` or `ℂ` carry a full lattice `L` into a discrete subgroup `L'`. The kernel
`f⁻¹(L') / L` of the map `E / L → E' / L'` induced by `f`, with the charts
`Submodule.instChartedSpaceKerOrbitRelQuotientMap` modelled on `ker f`, is a `C^n` additive Lie
group. For `𝕜 = ℂ` and `n = ω` it is a complex Lie group. -/
instance Submodule.instLieAddGroupKerOrbitRelQuotientMap :
    LieAddGroup 𝓘(𝕜, LinearMap.ker f) n (L.orbitRelQuotientMap L' (f.restrictScalars ℤ) h).ker :=
  AddSubgroup.lieAddGroup_chartedSpaceOfIsOpenEmbedding _
    (isImmersion_coe_orbitRelQuotientToKerOrbitRelQuotientMap L f h)

/-- **The kernel of an induced homomorphism of tori is an embedded Lie subgroup.** Let a linear
map `f : E → E'` over `𝕜 = ℝ` or `ℂ` carry a full lattice `L` into a discrete subgroup `L'`. The
inclusion into `E / L` of the kernel `f⁻¹(L') / L` of the induced map `E / L → E' / L'` is a `C^n`
embedding. For `𝕜 = ℂ` and `n = ω` this makes the kernel a closed complex Lie subgroup of the
complex torus `E / L`; it is closed by `Submodule.isClosed_orbitRelQuotient_mk_image_preimage`. -/
theorem Submodule.isSmoothEmbedding_subtypeVal_ker_orbitRelQuotientMap :
    Manifold.IsSmoothEmbedding 𝓘(𝕜, LinearMap.ker f) 𝓘(𝕜, E) n
      (Subtype.val : (L.orbitRelQuotientMap L' (f.restrictScalars ℤ) h).ker →
        AddAction.orbitRel.Quotient L E) :=
  AddSubgroup.isSmoothEmbedding_subtypeVal_chartedSpaceOfIsOpenEmbedding _
    (isImmersion_coe_orbitRelQuotientToKerOrbitRelQuotientMap L f h)

end Kernel
