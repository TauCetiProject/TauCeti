/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.Descent
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Descending sections of bundles to quotient manifolds

Let a group `G` act freely and properly discontinuously by `C^n` maps on a `C^n` manifold `M`, and
let `V` be a fibre bundle over the orbit space `M ⧸ G`. A section `t` of the pullback of `V` along
the orbit projection `q : M → M ⧸ G` assigns to each `x : M` a vector `t x` of the fibre of `V`
over `q x`. When `t` is invariant under `G`, that is, `t (g • x) = t x` in the common fibre over
`q (g • x) = q x`, it descends to a section `TauCeti.MulAction.orbitRelQuotientRec t ht` of `V`
whose value at `q x` is `t x`. Every section of `V` arises in this way from exactly one invariant
section upstairs, its pullback (`TauCeti.MulAction.eq_orbitRelQuotientRec_iff`,
`TauCeti.MulAction.orbitRelQuotientRec_apply_mk`).

This file shows that the descended section is `C^m` for `m ≤ n` exactly when `t` is, read as a
map `x ↦ (q x, t x)` into the total space of `V` or, equivalently, as a section of Mathlib's
pullback bundle `q *ᵖ V`. The continuous analogue,
`TauCeti.continuous_section_orbitRelQuotientRec_iff`, needs no manifold structure. The orbit
projection is a surjective `C^n` local diffeomorphism (`TauCeti.isLocalDiffeomorph_quotientMk`),
so regularity can be tested after composing with it. This extends the descent of invariant maps
(`TauCeti.contMDiff_orbitRelQuotientLift_iff`) from maps into a fixed manifold to sections of a
bundle over the quotient. Likewise, a section of `V` is `C^m` exactly when its pullback along
the orbit projection is (`IsLocalDiffeomorph.contMDiff_section_iff_pullback`).

Over `𝓘(ℂ, E)` with `n = m = ∞` this is holomorphic descent of sections: the holomorphic sections
of a holomorphic vector bundle over a quotient of a complex manifold by a free properly
discontinuous group of biholomorphisms are the invariant holomorphic sections of its pullback.

## Main results

* `TauCeti.contMDiffAt_section_orbitRelQuotientRec_iff`,
  `TauCeti.contMDiff_section_orbitRelQuotientRec_iff`: the descended section is `C^m`, at the orbit
  of a point or globally, exactly when the invariant section upstairs is.
* `TauCeti.contMDiffAt_pullback_section_iff_orbitRelQuotientRec`,
  `TauCeti.contMDiff_pullback_section_iff_orbitRelQuotientRec`: the same, with the invariant
  section read as a section of the pullback bundle along the orbit projection.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§4–5 (holomorphic maps through coverings).
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {G M : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
  {F : Type*} {V : MulAction.orbitRel.Quotient G M → Type*}
  {t : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x)}
  {ht : ∀ (g : G) (x : M), t (g • x) ≍ t x}

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F V)] [∀ q, TopologicalSpace (V q)] {m n : ℕ∞ω}
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M]
  [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M] [FiberBundle F V]

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, the
descent of an invariant section is `C^m` at the orbit of `x` exactly when the section upstairs is
`C^m` at `x`. -/
theorem contMDiffAt_section_orbitRelQuotientRec_iff (hm : m ≤ n) {x : M} :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) m
        (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientRec t ht q))
        (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I (I.prod 𝓘(𝕜, F)) m
        (fun y ↦ TotalSpace.mk' F (Quotient.mk (MulAction.orbitRel G M) y) (t y)) x := by
  rw [← (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G) x).contMDiffAt_comp_iff hm]
  simp only [Function.comp_def, MulAction.orbitRelQuotientRec_mk]

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, the
descent of an invariant section is `C^m` exactly when the section upstairs is. For holomorphic
actions on complex manifolds, this is the holomorphic descent of invariant holomorphic
sections. -/
theorem contMDiff_section_orbitRelQuotientRec_iff (hm : m ≤ n) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) m
        (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientRec t ht q)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F)) m
        fun x ↦ TotalSpace.mk' F (Quotient.mk (MulAction.orbitRel G M) x) (t x) := by
  rw [← (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G)).contMDiff_comp_iff
    Quotient.mk_surjective hm]
  simp only [Function.comp_def, MulAction.orbitRelQuotientRec_mk]

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, an
invariant section of the pullback bundle of `V` along the orbit projection is `C^m` at `x` exactly
when its descent to a section of `V` is `C^m` at the orbit of `x`. -/
theorem contMDiffAt_pullback_section_iff_orbitRelQuotientRec [∀ q, Nonempty (V q)] (hm : m ≤ n)
    {x : M} :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) m
        (fun y ↦ TotalSpace.mk' F
          (E := ⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
            C(M, MulAction.orbitRel.Quotient G M)) *ᵖ V) y (t y)) x ↔
      ContMDiffAt I (I.prod 𝓘(𝕜, F)) m
        (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientRec t ht q))
        (Quotient.mk (MulAction.orbitRel G M) x) := by
  refine Iff.trans ?_ ((isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G) x)
    |>.contMDiffAt_section_iff_pullback (f := (⟨Quotient.mk _, continuous_quotient_mk'⟩ :
      C(M, MulAction.orbitRel.Quotient G M))) hm (σ := MulAction.orbitRelQuotientRec t ht)).symm
  simp only [ContinuousMap.coe_mk, MulAction.orbitRelQuotientRec_mk]

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, an
invariant section of the pullback bundle of `V` along the orbit projection is `C^m` exactly when
its descent to a section of `V` is. -/
theorem contMDiff_pullback_section_iff_orbitRelQuotientRec [∀ q, Nonempty (V q)] (hm : m ≤ n) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) m
        (fun x ↦ TotalSpace.mk' F
          (E := ⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
            C(M, MulAction.orbitRel.Quotient G M)) *ᵖ V) x (t x)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F)) m
        (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientRec t ht q)) := by
  refine Iff.trans ?_ ((isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G))
    |>.contMDiff_section_iff_pullback (f := (⟨Quotient.mk _, continuous_quotient_mk'⟩ :
      C(M, MulAction.orbitRel.Quotient G M))) Quotient.mk_surjective hm
      (σ := MulAction.orbitRelQuotientRec t ht)).symm
  simp only [ContinuousMap.coe_mk, MulAction.orbitRelQuotientRec_mk]

end TauCeti
