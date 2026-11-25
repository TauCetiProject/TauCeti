/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.RestrictScalars
public import TauCeti.Geometry.Manifold.Instances.OnePoint.SimpleSphere
public import TauCeti.Geometry.Manifold.MFDeriv.InjectivePoint
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity

/-!
# Somewhere injective maps from Riemann surfaces

Let `S` be a Riemann surface, regarded as a real surface through the model `𝓘(ℝ, ℂ)`, and let
`u : S → N` be a map into a real manifold. A point `z` is an injective point of `u`
(`TauCeti.IsInjectivePoint 𝓘(ℝ, ℂ) I u z`) when the real derivative of `u` at `z` is injective and
no other point of `S` has the image `u z`, and `u` is somewhere injective when it has an injective
point. In the theory of pseudoholomorphic curves, the somewhere injective curves are the simple
ones: they do not factor through a branched cover of degree greater than one. This file proves the
direction that holds for every map which is `C¹` near its injective point, with no condition on the
factor.

* **Somewhere injective maps factor only through covers of degree one.** If `u = v ∘ π` for a
  finite holomorphic map `π : S → S'` from a compact Riemann surface to a connected one, and `u`
  is `C¹` at an injective point, then `π` has degree one
  (`TauCeti.IsInjectivePoint.degree_eq_one`, `TauCeti.IsSomewhereInjective.degree_eq_one`), so it
  is a biholomorphism (`TauCeti.IsSomewhereInjective.exists_biholomorph_coe_eq`). Near an injective
  point `u` is injective (`ContMDiffAt.exists_mem_nhds_injOn`), hence so is `π`, and `π` has a
  fibre consisting of a single point; so its degree, the sum of the local multiplicities over that
  fibre, is one (`TauCeti.RiemannSurface.degree_eq_one_of_injOn`). In particular a map factoring
  through a cover of degree greater than one, such as a multiple cover `v ∘ π` of a curve `v`, is
  not somewhere injective (`TauCeti.not_isSomewhereInjective_comp`).
* **Spheres.** A somewhere injective `C¹` map of the Riemann sphere is a simple sphere in the sense
  of `TauCeti.IsSimpleSphere` (`TauCeti.IsSomewhereInjective.isSimpleSphere`).
* **Reparametrization.** Precomposing with a biholomorphism `a : S'' → S` of Riemann surfaces
  carries the injective points of `u` at `a z` to those of `u ∘ a` at `z`
  (`Diffeomorph.isInjectivePoint_comp_biholomorph_iff`), so somewhere injectivity is a property of
  the unparametrized curve (`Diffeomorph.isSomewhereInjective_comp_biholomorph_iff`). Invariance
  under diffeomorphisms of the target is `Diffeomorph.isInjectivePoint_diffeomorph_comp_iff`.

The converse, that a nonconstant closed pseudoholomorphic curve which factors only through covers
of degree one has an injective point, rests on the factorization of every such curve through a
somewhere injective one (McDuff–Salamon, Proposition 2.5.1) and is not proved here.

## References

* C. Wendl, *Lectures on holomorphic curves in symplectic and contact geometry*,
  arXiv:1011.1690, Definitions 4.4 and 4.5 and Proposition 4.3.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012, §2.5.
-/

public section

open Function Set
open scoped Manifold ContDiff

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]

namespace TauCeti

open RiemannSurface

section Degree

variable {S S' : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) 1 S]
  [CompactSpace S] [T2Space S] [TopologicalSpace S'] [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) 1 S']
  [T2Space S'] [PreconnectedSpace S'] {π : FiniteHolomorphicMap S S'} {v : S' → N}

/-- **A map with an injective point factors only through covers of degree one.** If `v ∘ π`, for
a finite holomorphic map `π` from a compact Riemann surface to a connected one, is `C¹` at an
injective point, then `π` has degree one. No regularity is asked of `v`. -/
theorem IsInjectivePoint.degree_eq_one {z : S} (h : IsInjectivePoint 𝓘(ℝ, ℂ) I (v ∘ π) z)
    (hc : ContMDiffAt 𝓘(ℝ, ℂ) I 1 (v ∘ π) z) : degree π = 1 := by
  obtain ⟨t, ht, hinj⟩ := hc.exists_mem_nhds_injOn one_ne_zero h.injective_mfderiv
  exact degree_eq_one_of_injOn π ht hinj.of_comp fun _ hz ↦ h.eq_of_apply_eq (congrArg v hz)

/-- **Somewhere injective maps factor only through covers of degree one.** If `v ∘ π`, for a finite
holomorphic map `π` from a compact Riemann surface to a connected one, is `C¹` and somewhere
injective, then `π` has degree one. No regularity is asked of `v`. -/
theorem IsSomewhereInjective.degree_eq_one (h : IsSomewhereInjective 𝓘(ℝ, ℂ) I (v ∘ π))
    (hc : ContMDiff 𝓘(ℝ, ℂ) I 1 (v ∘ π)) : degree π = 1 := by
  obtain ⟨z, hz⟩ := isSomewhereInjective_iff.1 h
  exact hz.degree_eq_one (hc z)

/-- If `v ∘ π`, for a finite holomorphic map `π` from a compact Riemann surface to a connected
one, is `C¹` and somewhere injective, then `π` is a biholomorphism. -/
theorem IsSomewhereInjective.exists_biholomorph_coe_eq
    (h : IsSomewhereInjective 𝓘(ℝ, ℂ) I (v ∘ π)) (hc : ContMDiff 𝓘(ℝ, ℂ) I 1 (v ∘ π)) :
    ∃ a : S ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ S', ⇑a = π :=
  ⟨biholomorphOfDegreeEqOne π (h.degree_eq_one hc), biholomorphOfDegreeEqOne_toFun ..⟩

/-- **Multiple covers are not somewhere injective.** A `C¹` map factoring as `v ∘ π` through a
finite holomorphic map `π` of degree greater than one, from a compact Riemann surface to a
connected one, has no injective point. -/
theorem not_isSomewhereInjective_comp (hπ : 1 < degree π) (hc : ContMDiff 𝓘(ℝ, ℂ) I 1 (v ∘ π)) :
    ¬IsSomewhereInjective 𝓘(ℝ, ℂ) I (v ∘ π) :=
  fun h ↦ hπ.ne' (h.degree_eq_one hc)

end Degree

/-! ### Spheres -/

section Sphere

variable {u : OnePoint ℂ → N}

/-- A map of the Riemann sphere which is `C¹` at an injective point is a simple sphere. -/
theorem IsInjectivePoint.isSimpleSphere {z : OnePoint ℂ} (h : IsInjectivePoint 𝓘(ℝ, ℂ) I u z)
    (hc : ContMDiffAt 𝓘(ℝ, ℂ) I 1 u z) : IsSimpleSphere u := by
  obtain ⟨t, ht, hinj⟩ := hc.exists_mem_nhds_injOn one_ne_zero h.injective_mfderiv
  exact isSimpleSphere_of_injOn ht hinj fun _ hw ↦ h.eq_of_apply_eq hw

/-- **Somewhere injective spheres are simple.** A `C¹` somewhere injective map of the Riemann
sphere is a simple sphere. -/
theorem IsSomewhereInjective.isSimpleSphere (h : IsSomewhereInjective 𝓘(ℝ, ℂ) I u)
    (hc : ContMDiff 𝓘(ℝ, ℂ) I 1 u) : IsSimpleSphere u := by
  obtain ⟨z, hz⟩ := isSomewhereInjective_iff.1 h
  exact hz.isSimpleSphere (hc z)

end Sphere

end TauCeti

/-! ### Reparametrization by biholomorphisms -/

namespace Diffeomorph

open TauCeti

variable {S S'' : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S'']
  [ChartedSpace ℂ S'']

/-- Precomposing with a biholomorphism `a` of Riemann surfaces carries the injective points of `u`
at `a z` to injective points of `u ∘ a` at `z`, and conversely. -/
@[simp]
theorem isInjectivePoint_comp_biholomorph_iff (a : S'' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ S) {u : S → N} {z : S''} :
    IsInjectivePoint 𝓘(ℝ, ℂ) I (u ∘ a) z ↔ IsInjectivePoint 𝓘(ℝ, ℂ) I u (a z) := by
  simpa only [modelWithCornersSelf_restrictScalars, coe_restrictScalars] using
    (a.restrictScalars ℝ).isInjectivePoint_comp_diffeomorph_iff (I'' := I) (f := u) (x := z)
      (by simp)

/-- Precomposing with a biholomorphism of Riemann surfaces preserves somewhere injectivity. -/
@[simp]
theorem isSomewhereInjective_comp_biholomorph_iff (a : S'' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ S) {u : S → N} :
    IsSomewhereInjective 𝓘(ℝ, ℂ) I (u ∘ a) ↔ IsSomewhereInjective 𝓘(ℝ, ℂ) I u := by
  simpa only [modelWithCornersSelf_restrictScalars, coe_restrictScalars] using
    (a.restrictScalars ℝ).isSomewhereInjective_comp_diffeomorph_iff (I'' := I) (f := u)
      (by simp)

end Diffeomorph
