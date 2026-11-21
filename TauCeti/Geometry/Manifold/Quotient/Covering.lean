/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Topology.Covering.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Quotient coverings by local diffeomorphisms

Let a group `G` act on a manifold `M`, and let `q : M → N` be a quotient covering map for this
action (`IsQuotientCoveringMap q G`): a quotient map whose fibres are the `G`-orbits, every point of
`M` having a neighbourhood disjoint from its nontrivial translates. Suppose that `q` is moreover a
`C^n` local diffeomorphism onto a manifold `N`. This is the situation of the projection of a
manifold onto its quotient by a free properly discontinuous group of diffeomorphisms, with `N` any
manifold structure on the quotient for which the projection is a local diffeomorphism, for
instance a Riemannian covering `X → X / H`.

The smooth structure of `M` then determines that of the action and of the functions on `N`:

* each translation `x ↦ g • x` is `C^n`, since its composite with `q` is `q` itself
  (`IsQuotientCoveringMap.contMDiffConstSMul`);
* a `C^m` map on `M` that is constant on the `G`-orbits, `m ≤ n`, is the pullback `f' ∘ q` of a
  `C^m` map `f'` on `N` (`IsQuotientCoveringMap.exists_contMDiff_comp_eq`).

For the orbit space `M ⧸ G` with its quotient manifold structure, the descended map is
`TauCeti.MulAction.orbitRelQuotientLift`; the statements here apply to an arbitrary target `N`
of a quotient covering map, without identifying it with the orbit space.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

open scoped Manifold ContDiff

namespace IsQuotientCoveringMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {G : Type*} [Group G] [MulAction G M] {q : M → N} {m n : ℕ∞ω}

/-- **Translations are smooth.** If a quotient covering map `q : M → N` for an action of `G` is a
`C^n` local diffeomorphism, then `G` acts on `M` by `C^n` maps: the composite of `x ↦ g • x` with
`q` is `q` itself. -/
theorem contMDiffConstSMul (hq : IsQuotientCoveringMap q G) (hp : IsLocalDiffeomorph I I' n q) :
    ContMDiffConstSMul I n G M where
  contMDiff_const_smul g := by
    refine ContMDiff.of_comp_isLocalDiffeomorph hp (hq.continuous_const_smul g) ?_
    have hcomp : q ∘ (g • ·) = q := funext fun _ ↦ hq.map_smul g
    rw [hcomp]
    exact hp.contMDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H'' : Type*}
  [TopologicalSpace H''] {J : ModelWithCorners 𝕜 F H''} {P : Type*} [TopologicalSpace P]
  [ChartedSpace H'' P]

/-- **Descent of invariant maps.** If a quotient covering map `q : M → N` for an action of `G` is a
`C^n` local diffeomorphism and `m ≤ n`, then every `C^m` map `f` on `M` that is constant on the
`G`-orbits is the pullback `f' ∘ q` of a `C^m` map `f'` on `N`. -/
theorem exists_contMDiff_comp_eq (hq : IsQuotientCoveringMap q G)
    (hp : IsLocalDiffeomorph I I' n q) (hm : m ≤ n) {f : M → P} (hf : ContMDiff I J m f)
    (hinv : ∀ (g : G) (x : M), f (g • x) = f x) :
    ∃ f' : N → P, ContMDiff I' J m f' ∧ f' ∘ q = f := by
  have hsurj := hq.surjective
  have hcomp : (f ∘ Function.surjInv hsurj) ∘ q = f := funext fun x ↦ by
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.1 (Function.surjInv_eq hsurj (q x))
    simp only [Function.comp_apply, ← hg, hinv]
  refine ⟨f ∘ Function.surjInv hsurj, (hp.contMDiff_comp_iff hsurj hm).1 ?_, hcomp⟩
  rwa [hcomp]

end IsQuotientCoveringMap
