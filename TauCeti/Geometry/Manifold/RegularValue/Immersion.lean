/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.Geometry.Manifold.RegularValue.Open

/-!
# Maps of injective differential into regular levels

Let `f : M → N` map a boundaryless manifold modelled on a finite-dimensional space `E` into
any charted space modelled on a finite-dimensional space `F`. Suppose `g : P → M` maps a
neighbourhood of an interior point `q₀` into the level `f⁻¹(c)`, where `P` has dimension
`dim E - dim F`. If `f` is regular and `C¹` at `g q₀`, and `g` is `C¹` at `q₀` with injective
differential there, then every point of the level sufficiently close to `g q₀` belongs to
`g '' S`, for any prescribed neighbourhood `S` of `q₀`.

Locally the level is a manifold of dimension `dim E - dim F`, and the inverse function theorem
makes the induced map into that level a local diffeomorphism at `q₀`. No regularity or `C¹`
hypotheses are needed away from the chosen points.

For a curve `δ` in a level of dimension one near a parameter `s₀`, injectivity of the differential
amounts to nonzero velocity at `s₀`. For instance, if a function on a surface is regular and `C¹`
at `δ s₀`, and the curve is `C¹` with nonzero velocity there and lies in its zero set near `s₀`,
then every zero sufficiently close to `δ s₀` lies on the prescribed curve segment.

## Main results

* `TauCeti.IsRegularPoint.eventually_mem_image`: a map with injective differential covers a
  level of a map into any charted target locally under regularity and `C¹` hypotheses only at
  the chosen points.
* `TauCeti.IsRegularPoint.eventually_mem_image_of_curveVelocity_ne_zero`: the corresponding
  pointwise result for a curve in a level of dimension one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 (regular level sets) and Theorem 4.5 (the inverse function
  theorem for manifolds).
-/

public section

open Filter Function Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {f : M → F} {c : F}

private theorem eventually_mem_range_of_isRegularValue (hreg : IsRegularValue I 𝓘(𝕜, F) f c)
    (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(𝕜, F) 1 f x)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 G H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J 1 P]
    (hdim : finrank 𝕜 G + finrank 𝕜 F = finrank 𝕜 E)
    {g : P → M} (hg : ContMDiff J I 1 g) (hgc : ∀ q, f (g q) = c) {q₀ : P}
    (hinj : Injective (mfderiv J I g q₀)) (hq₀ : J.IsInteriorPoint q₀) :
    ∀ᶠ x in 𝓝 (g q₀), f x = c → x ∈ range g := by
  have : CompleteSpace G := FiniteDimensional.completeSpace 𝕜 G
  have hn : finrank 𝕜 E - finrank 𝕜 F = finrank 𝕜 G := by omega
  let := regularLevelChartedSpace hf hreg hn
  have := isManifold_regularLevel le_rfl hf hreg hn
  have hi := (isImmersionOfComplement_coe_regularLevel le_rfl hf hreg hn).isImmersion
  let g' : P → {x : M // f x = c} := fun q ↦ ⟨g q, hgc q⟩
  have hg' : ContMDiff J 𝓘(𝕜, Fin (finrank 𝕜 G) → 𝕜) 1 g' :=
    (ContMDiff.iff_comp_isImmersion hi).2 ⟨hg.continuous.subtype_mk _, hg⟩
  have hinj' : Injective (mfderiv J 𝓘(𝕜, Fin (finrank 𝕜 G) → 𝕜) g' q₀) := by
    -- Expose the factorization through the subtype so that mfderiv_comp matches syntactically.
    rw [show g = Subtype.val ∘ g' from rfl, mfderiv_comp q₀
      (hi.contMDiff.mdifferentiableAt one_ne_zero) (hg'.mdifferentiableAt one_ne_zero),
      ContinuousLinearMap.coe_comp] at hinj
    exact hinj.of_comp
  have hloc : IsLocalDiffeomorphAt J 𝓘(𝕜, Fin (finrank 𝕜 G) → 𝕜) 1 g' q₀ :=
    isLocalDiffeomorphAt_of_injective_mfderiv hg'.contMDiffOn isOpen_univ (mem_univ q₀) hq₀
      le_rfl hinj' (by simp)
  have hmem : ∀ᶠ y in 𝓝 (g' q₀), y ∈ range g' :=
    hloc.localInverse_eventuallyEq_right.mono fun y hy ↦ ⟨hloc.localInverse y, hy⟩
  rw [nhds_subtype_eq_comap, eventually_comap] at hmem
  filter_upwards [hmem] with x hx hxc
  obtain ⟨q, hq⟩ := hx ⟨x, hxc⟩ rfl
  exact ⟨q, congrArg Subtype.val hq⟩

private theorem eventually_mem_image_normedSpace
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 G H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J 1 P]
    {g : P → M} {q₀ : P} (hreg : IsRegularPoint I 𝓘(𝕜, F) f (g q₀))
    (hf : ContMDiffAt I 𝓘(𝕜, F) 1 f (g q₀))
    (hdim : finrank 𝕜 G + finrank 𝕜 F = finrank 𝕜 E)
    {S : Set P} (hS : S ∈ 𝓝 q₀) (hg : ContMDiffAt J I 1 g q₀)
    (hgc : ∀ᶠ q in 𝓝 q₀, f (g q) = c)
    (hinj : Injective (mfderiv J I g q₀)) (hq₀ : J.IsInteriorPoint q₀) :
    ∀ᶠ x in 𝓝 (g q₀), f x = c → x ∈ g '' S := by
  have hnear := ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hf).and
    (hreg.eventually_isRegularPoint hf le_rfl)
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := eventually_nhds_iff.mp hnear
  let U' : TopologicalSpace.Opens M := ⟨U, hUopen⟩
  have hsource := (eventually_mem_set.mpr hS).and (hgc.and
    (((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hg).and
      (hg.continuousAt.eventually_mem (hUopen.mem_nhds hUmem))))
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := eventually_nhds_iff.mp hsource
  let V' : TopologicalSpace.Opens P := ⟨V, hVopen⟩
  let g' : V' → U' := fun q ↦ ⟨g q, (hVsub q q.property).2.2.2⟩
  have hg' : ContMDiff J I 1 g' := by
    apply (ContMDiff.subtypeVal_comp_iff U' g').mp
    exact fun q ↦ ((hVsub q q.property).2.2.1.comp q
      (contMDiff_subtypeVal q)).contMDiffWithinAt
  have hregU : IsRegularValue I 𝓘(𝕜, F) (f ∘ (Subtype.val : U' → M)) c :=
    isRegularValue_iff.mpr fun p _ ↦ (hUsub p p.property).2.comp (isRegularPoint_subtype_val p)
  have hinj' : Injective (mfderiv J I g' ⟨q₀, hVmem⟩) := by
    intro v w hvw
    apply hinj
    have hg'val : (Subtype.val : U' → M) ∘ g' = g ∘ (Subtype.val : V' → P) := rfl
    rw [← Manifold.mfderiv_comp_subtype_val_apply (x := (⟨q₀, hVmem⟩ : V')) v,
      ← Manifold.mfderiv_comp_subtype_val_apply (x := (⟨q₀, hVmem⟩ : V')) w, ← hg'val,
      Manifold.mfderiv_subtype_val_comp_apply, Manifold.mfderiv_subtype_val_comp_apply]
    exact hvw
  have hmem := eventually_mem_range_of_isRegularValue hregU
    (fun p _ ↦ (hUsub p p.property).1.comp p (contMDiff_subtypeVal p)) hdim hg'
    (fun q ↦ (hVsub q q.property).2.1) hinj'
    (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mpr hq₀)
  have hmap := map_nhds_subtypeVal_eq_nhds (g' ⟨q₀, hVmem⟩).property
    (hUopen.mem_nhds hUmem)
  rw [← hmap, eventually_map]
  filter_upwards [hmem] with x hx hxc
  obtain ⟨q, hq⟩ := hx hxc
  exact ⟨q, (hVsub q q.property).1, congrArg Subtype.val hq⟩

section ChartedTarget

variable {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 F H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N] {f : M → N} {c : N}

/-- A map `g` into a level near an interior point `q₀`, with injective differential and source
dimension `dim E - dim F`, covers that level near `g q₀`. The target of the defining map may be any
charted space modelled on `F`. Regularity of `f` and `C¹` regularity of both maps are required
only at the chosen points; the image can be restricted to any source neighbourhood `S`. -/
theorem IsRegularPoint.eventually_mem_image
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 G H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J 1 P]
    {g : P → M} {q₀ : P} (hreg : IsRegularPoint I K f (g q₀))
    (hf : ContMDiffAt I K 1 f (g q₀))
    (hdim : finrank 𝕜 G + finrank 𝕜 F = finrank 𝕜 E)
    {S : Set P} (hS : S ∈ 𝓝 q₀) (hg : ContMDiffAt J I 1 g q₀)
    (hgc : ∀ᶠ q in 𝓝 q₀, f (g q) = c)
    (hinj : Injective (mfderiv J I g q₀)) (hq₀ : J.IsInteriorPoint q₀) :
    ∀ᶠ x in 𝓝 (g q₀), f x = c → x ∈ g '' S := by
  have hchart : IsRegularPoint K 𝓘(𝕜, F) (extChartAt K (f (g q₀))) (f (g q₀)) := by
    rw [isRegularPoint_iff, mfderiv_extChartAt_eq_id]
    exact fun v ↦ ⟨v, rfl⟩
  have hmem := eventually_mem_image_normedSpace (hchart.comp hreg)
    (contMDiffAt_iff_target.mp hf).2 hdim hS hg
    (hgc.mono fun q hq ↦ congrArg (extChartAt K (f (g q₀))) hq) hinj hq₀
  exact hmem.mono fun x hx hxc ↦ hx (congrArg (extChartAt K (f (g q₀))) hxc)

/-- A curve with nonzero velocity in a level of dimension one covers that level locally.
The defining function need only be regular and `C¹` at `δ s₀`, the curve need only be `C¹`
at `s₀`, and its values need lie in the level only near `s₀`. Coverage holds using parameters
in any prescribed neighbourhood `S` of `s₀`. -/
theorem IsRegularPoint.eventually_mem_image_of_curveVelocity_ne_zero
    {δ : 𝕜 → M} {s₀ : 𝕜} (hreg : IsRegularPoint I K f (δ s₀))
    (hf : ContMDiffAt I K 1 f (δ s₀))
    (hdim : finrank 𝕜 F + 1 = finrank 𝕜 E) {S : Set 𝕜} (hS : S ∈ 𝓝 s₀)
    (hδ : ContMDiffAt 𝓘(𝕜, 𝕜) I 1 δ s₀) (hδc : ∀ᶠ s in 𝓝 s₀, f (δ s) = c)
    (hv : Manifold.curveVelocity I δ s₀ ≠ 0) :
    ∀ᶠ x in 𝓝 (δ s₀), f x = c → x ∈ δ '' S := by
  apply hreg.eventually_mem_image hf (by rw [finrank_self, add_comm, hdim]) hS hδ hδc
    _ BoundarylessManifold.isInteriorPoint
  rw [(Manifold.hasMFDerivAt_curveVelocity (hδ.mdifferentiableAt one_ne_zero)).mfderiv]
  exact smul_left_injective 𝕜 hv

end ChartedTarget

end TauCeti
