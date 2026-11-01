/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import TauCeti.Geometry.Manifold.Quotient.Descent
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Descending sections to quotient manifolds

Let a group `G` act freely and properly discontinuously by `C^n` maps on a `C^n` manifold `M`, so
that the orbit projection `q : M → M / G` onto `MulAction.orbitRel.Quotient G M` is a surjective
`C^n` local diffeomorphism (`TauCeti.isLocalDiffeomorph_quotientMk`). Let `V` be a fibre bundle
over the orbit space. A section `s` of the pullback bundle `q *ᵖ V` assigns to `x : M` a point
`s x` of the fibre `V (q x)`. If `s` is invariant, that is, `s (g • x)` and `s x` are the same
point of `V (q x) = V (q (g • x))`, it descends to the section
`TauCeti.MulAction.orbitRelQuotientDLift s hs` of `V`, which sends `q x` to `s x`. Every section of
`V` is the descent of its pullback along `q`, and the descent is unique
(`TauCeti.MulAction.eq_orbitRelQuotientDLift_iff`).

This file shows that for `m ≤ n` the descended section is `C^m` exactly when `s` is a `C^m`
section of `q *ᵖ V`. Conversely, a section of `V` is `C^m` exactly when its pullback along the
orbit projection is, by `IsLocalDiffeomorph.contMDiff_section_iff_pullback` applied to the
surjective local diffeomorphism `q`. The pullback bundle is Mathlib's `Bundle.Pullback` along
the orbit projection bundled as the `C^n` map `TauCeti.orbitRelQuotientMkContMDiffMap`, so it
carries Mathlib's pullback fibre bundle structure, and its vector bundle structure when `V` is a
vector bundle.

Over `𝕜 = ℂ` with `n = m = ∞` this is the holomorphic descent of sections: an invariant holomorphic
section of the pullback of a holomorphic vector bundle along the quotient map by a free, properly
discontinuous group of biholomorphisms descends to a holomorphic section on the quotient manifold.
The smoothness statements need no linear structure on the fibres.

## Main results

* `TauCeti.contMDiffAt_orbitRelQuotientDLift_iff`, `TauCeti.contMDiff_orbitRelQuotientDLift_iff`:
  the descent of an invariant family `s x : V (q x)` is `C^m`, at the orbit of a point or
  globally, exactly when `x ↦ s x`, read in the total space of `V`, is.
* `TauCeti.contMDiffAt_orbitRelQuotientDLift_iff_pullback`,
  `TauCeti.contMDiff_orbitRelQuotientDLift_iff_pullback`: the descent of an invariant section of
  `q *ᵖ V` is `C^m` exactly when that section is.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§4–5 (holomorphic functions through coverings).
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {m n : ℕ∞ω}
  {G M : Type*} [Group G] [MulAction G M] [TopologicalSpace M] [ChartedSpace H M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M]
  [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : MulAction.orbitRel.Quotient G M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ q, TopologicalSpace (V q)] [FiberBundle F V]

section TotalSpace

variable {s : ∀ x, V (Quotient.mk (MulAction.orbitRel G M) x)}
  {hs : ∀ (g : G) (x : M), s (g • x) ≍ s x}

omit [TopologicalSpace M] [ChartedSpace H M] [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
  [IsManifold I n M] [ContMDiffConstSMul I n G M] [NormedAddCommGroup F]
  [TopologicalSpace (TotalSpace F V)] [∀ q, TopologicalSpace (V q)] [FiberBundle F V] in
/-- The descended section, read in the total space of `V` and composed with the orbit projection,
is `y ↦ s y`. -/
theorem totalSpaceMk_orbitRelQuotientDLift_comp_mk :
    (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientDLift s hs q)) ∘
        Quotient.mk (MulAction.orbitRel G M) =
      fun y ↦ TotalSpace.mk' F (Quotient.mk (MulAction.orbitRel G M) y) (s y) :=
  funext fun y ↦ by rw [Function.comp_apply, MulAction.orbitRelQuotientDLift_mk]

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, the
descent of an invariant family `s x : V (q x)` over the orbit projection `q` is a section of `V`
which is `C^m` at the orbit of `x` exactly when `y ↦ s y`, read in the total space of `V`, is
`C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientDLift_iff (hm : m ≤ n) {x : M} :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) m
        (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientDLift s hs q))
        (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I (I.prod 𝓘(𝕜, F)) m
        (fun y ↦ TotalSpace.mk' F (Quotient.mk (MulAction.orbitRel G M) y) (s y)) x := by
  rw [← (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G) x).contMDiffAt_comp_iff hm,
    totalSpaceMk_orbitRelQuotientDLift_comp_mk]

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, the
descent of an invariant family `s x : V (q x)` over the orbit projection `q` is a `C^m` section of
`V` exactly when `y ↦ s y`, read in the total space of `V`, is `C^m`. -/
theorem contMDiff_orbitRelQuotientDLift_iff (hm : m ≤ n) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) m
        (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientDLift s hs q)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F)) m
        (fun y ↦ TotalSpace.mk' F (Quotient.mk (MulAction.orbitRel G M) y) (s y)) := by
  rw [← (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G)).contMDiff_comp_iff
    Quotient.mk_surjective hm, totalSpaceMk_orbitRelQuotientDLift_comp_mk]

end TotalSpace

variable (I n G M) in
/-- The orbit projection of a free, properly discontinuous action by `C^n` maps on a `C^n`
manifold, bundled as a `C^n` map. Bundles pulled back along it carry Mathlib's pullback bundle
structures.

The body is exposed so that the fibre of a pullback bundle along this map at `x` is
definitionally the fibre at the orbit of `x`; sections of the pullback are then exactly families
`s x : V (Quotient.mk _ x)`, as `TauCeti.MulAction.orbitRelQuotientDLift` takes them. -/
@[expose]
def orbitRelQuotientMkContMDiffMap : C^n⟮I, M; I, MulAction.orbitRel.Quotient G M⟯ :=
  ⟨Quotient.mk _, (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G)).contMDiff⟩

@[simp]
theorem coe_orbitRelQuotientMkContMDiffMap :
    ⇑(orbitRelQuotientMkContMDiffMap I n G M) = Quotient.mk (MulAction.orbitRel G M) :=
  (rfl)

section Pullback

variable [∀ q, Nonempty (V q)]

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, the
descent of an invariant section `s` of the pullback of `V` along the orbit projection is `C^m` at
the orbit of `x` exactly when `s` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientDLift_iff_pullback (hm : m ≤ n)
    {s : ∀ x, ((orbitRelQuotientMkContMDiffMap I n G M : M → _) *ᵖ V) x}
    (hs : ∀ (g : G) (x : M), s (g • x) ≍ s x) {x : M} :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) m
        (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientDLift (V := V) s hs q))
        (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I (I.prod 𝓘(𝕜, F)) m (fun y ↦ TotalSpace.mk' F y (s y)) x := by
  refine (contMDiffAt_orbitRelQuotientDLift_iff hm).trans ?_
  rw [Pullback.contMDiffAt_iff _
    ((orbitRelQuotientMkContMDiffMap I n G M).contMDiff.of_le hm).contMDiffAt]
  -- `Pullback.lift` sends `⟨y, s y⟩` to `⟨q y, s y⟩`, and `q y` is `Quotient.mk _ y` by the
  -- exposed definition of `q`; the dependent pair cannot be rewritten, so this is by unfolding.
  exact (and_iff_right contMDiffAt_id).symm

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, the
descent of an invariant section `s` of the pullback of `V` along the orbit projection is a `C^m`
section of `V` exactly when `s` is a `C^m` section of the pullback. -/
theorem contMDiff_orbitRelQuotientDLift_iff_pullback (hm : m ≤ n)
    {s : ∀ x, ((orbitRelQuotientMkContMDiffMap I n G M : M → _) *ᵖ V) x}
    (hs : ∀ (g : G) (x : M), s (g • x) ≍ s x) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) m
        (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientDLift (V := V) s hs q)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F)) m (fun y ↦ TotalSpace.mk' F y (s y)) := by
  refine (contMDiff_orbitRelQuotientDLift_iff hm).trans ?_
  rw [Pullback.contMDiff_iff _ ((orbitRelQuotientMkContMDiffMap I n G M).contMDiff.of_le hm)]
  -- `Pullback.lift` sends `⟨y, s y⟩` to `⟨q y, s y⟩`, and `q y` is `Quotient.mk _ y` by the
  -- exposed definition of `q`; the dependent pair cannot be rewritten, so this is by unfolding.
  exact (and_iff_right contMDiff_id).symm

end Pullback

end TauCeti
