/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback

/-!
# Pulling back domain-dependent almost complex structures along diffeomorphisms

A `Cʳ` diffeomorphism `g : M → N` of targets pulls a jointly `Cⁿ` domain-dependent almost complex
structure `J` on `N`, parametrized by `P`, back to a jointly `Cⁿ` domain-dependent structure on
`M` whenever `n + 1 ≤ r`:

`(g^* J)(p, x) = (dg_x)⁻¹ ∘ J(p, g x) ∘ dg_x`.

Freezing the domain point gives the pullback `TauCeti.ContMDiffAlmostComplexStructure.pullback`
of the frozen structure, which supplies the regularity of the family through
`TauCeti.ContMDiffAlmostComplexStructure.contMDiff_pullback_family`. Read in a chart `ψ` of `N`
and the chart `g ≫ ψ` of `M`, the pulled-back structure is the original one read in `ψ`.

## Main declarations

* `TauCeti.ContMDiffAlmostComplexStructureFamily.pullback`: the pulled-back family.
* `TauCeti.ContMDiffAlmostComplexStructureFamily.mfderiv_pullback_apply`: the differentials of
  `g` are complex linear from `g^* J` to `J`.
* `TauCeti.ContMDiffAlmostComplexStructureFamily.freeze_pullback`: freezing commutes with
  pullback.
* `TauCeti.ContMDiffAlmostComplexStructureFamily.pullback_const`: pulling back commutes with
  regarding a structure as a domain-independent family.
* `TauCeti.ContMDiffAlmostComplexStructureFamily.chartField_pullback`,
  `TauCeti.ContMDiffAlmostComplexStructureFamily.chartField_pullback_trans`: `g^* J` read in a
  chart `χ = ψ ∘ g` of `M`, such as `g ≫ ψ`, is `J` read in `ψ`. No differentiability of the
  charts is needed: where `ψ` or `ψ⁻¹` is not differentiable, neither is its composite with `g`
  or `g⁻¹`, and both sides vanish.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 and Appendix B.
-/

public noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti

namespace ContMDiffAlmostComplexStructureFamily

variable {E H M H' N EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {n r : ℕ∞}

/-- The pullback `g^* J` of a domain-dependent structure along a `Cʳ` diffeomorphism `g` of the
targets with `n + 1 ≤ r`: `(g^* J)(p, x) = (dg_x)⁻¹ ∘ J(p, g x) ∘ dg_x`. -/
def pullback (g : M ≃ₘ^r⟮I, I'⟯ N) (J : ContMDiffAlmostComplexStructureFamily I' N IP P n)
    (hnr : n + 1 ≤ r) : ContMDiffAlmostComplexStructureFamily I M IP P n :=
  ofContMDiff
    (fun q ↦ (ContMDiffAlmostComplexStructure.pullback g (J.freeze q.1) hnr).toEndomorphism q.2)
    (ContMDiffAlmostComplexStructure.contMDiff_pullback_family g hnr (J := J.freeze)
      (J.contMDiff.congr fun _ ↦ by rw [freeze_toEndomorphism_apply]))
    (fun q v ↦ (ContMDiffAlmostComplexStructure.pullback g (J.freeze q.1) hnr).apply_apply q.2 v)

variable (g : M ≃ₘ^r⟮I, I'⟯ N) (J : ContMDiffAlmostComplexStructureFamily I' N IP P n)
  (hnr : n + 1 ≤ r)

/-- Freezing the domain point commutes with pullback. -/
@[simp]
theorem freeze_pullback (p : P) :
    (J.pullback g hnr).freeze p = (J.freeze p).pullback g hnr := by
  ext x v
  simp only [freeze_toEndomorphism_apply, pullback, ofContMDiff_toEndomorphism_apply]

/-- The pulled-back family at `(p, x)` is `(dg_x)⁻¹ ∘ J(p, g x) ∘ dg_x`. -/
theorem pullback_tangentEndomorphism_apply (q : P × M) (v : TangentSpace I q.2) :
    (J.pullback g hnr).tangentEndomorphism q v =
      (mfderiv I I' g q.2).inverse (J.tangentEndomorphism (q.1, g q.2) (mfderiv I I' g q.2 v)) := by
  rw [← freeze_apply, freeze_pullback, ContMDiffAlmostComplexStructure.pullback_apply,
    freeze_apply]

/-- The differentials of `g` are complex linear from `g^* J` to `J`. -/
@[simp]
theorem mfderiv_pullback_apply (q : P × M) (v : TangentSpace I q.2) :
    mfderiv I I' g q.2 ((J.pullback g hnr).tangentEndomorphism q v) =
      J.tangentEndomorphism (q.1, g q.2) (mfderiv I I' g q.2 v) := by
  rw [← freeze_apply, freeze_pullback, ContMDiffAlmostComplexStructure.mfderiv_pullback_apply,
    freeze_apply]


/-- A structure independent of the domain point pulls back to the pullback of the structure. -/
@[simp]
theorem pullback_const (K : ContMDiffAlmostComplexStructure I' n N) :
    (const (IP := IP) (P := P) K).pullback g hnr = const (K.pullback g hnr) := by
  ext q v
  simp only [pullback, ofContMDiff_toEndomorphism_apply, const_toEndomorphism_apply, freeze_const]

section ChartField

variable {D G : Type*} [TopologicalSpace D] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Transport in charts.** Let `χ` be a chart of `M` and `ψ` a chart of `N` with
`χ = ψ ∘ g` and `χ⁻¹ = g⁻¹ ∘ ψ⁻¹`, such as `g ≫ ψ`. Read in a chart `φ` of the domain and in
`χ`, the pulled-back structure `g^* J` is `J` read in `φ` and `ψ`. -/
theorem chartField_pullback (φ : OpenPartialHomeomorph P D) {χ : OpenPartialHomeomorph M G}
    {ψ : OpenPartialHomeomorph N G} (hχ : ⇑χ = ψ ∘ g) (hχs : ⇑χ.symm = g.symm ∘ ψ.symm) :
    (J.pullback g hnr).chartField φ χ = J.chartField φ ψ := by
  have hr : (r : ℕ∞ω) ≠ 0 := ENat.coe_ne_zero_of_add_one_le hnr
  funext z v
  set y := g.symm (ψ.symm v) with hy_def
  have hy : g y = ψ.symm v := g.apply_symm_apply _
  ext w
  rw [chartField_apply, chartField_apply, freeze_pullback,
    ContMDiffAlmostComplexStructure.chartPushforward_apply,
    ContMDiffAlmostComplexStructure.chartPushforward_apply, hχs, hχ, Function.comp_apply,
    ← hy_def]
  beta_reduce
  rw [← hy]
  -- Where `ψ` or `ψ⁻¹` is not differentiable, neither is its composite with `g` or `g⁻¹`, and
  -- both sides vanish.
  by_cases hψ : MDifferentiableAt I' 𝓘(ℝ, G) ψ (g y)
  swap
  · have hψg : ¬MDifferentiableAt I 𝓘(ℝ, G) (ψ ∘ g) y := by
      rwa [g.mdifferentiableAt_comp_diffeomorph_iff hr]
    rw [mfderiv_zero_of_not_mdifferentiableAt hψ, mfderiv_zero_of_not_mdifferentiableAt hψg]
    rfl
  by_cases hψs : MDifferentiableAt 𝓘(ℝ, G) I' ψ.symm v
  swap
  · have hψgs : ¬MDifferentiableAt 𝓘(ℝ, G) I (g.symm ∘ ψ.symm) v := by
      rwa [g.symm.mdifferentiableAt_comp_iff hr]
    rw [mfderiv_zero_of_not_mdifferentiableAt hψs, mfderiv_zero_of_not_mdifferentiableAt hψgs]
    -- Both sides apply linear maps to the zero vector, read in tangent spaces equal to `E`.
    erw [zero_apply]
    simp only [map_zero]
    erw [map_zero, map_zero]
  have h1 (u : TangentSpace I y) : mfderiv I 𝓘(ℝ, G) (ψ ∘ g) y u =
      mfderiv I' 𝓘(ℝ, G) ψ (g y) (mfderiv I I' g y u) :=
    mfderiv_comp_apply y hψ (g.mdifferentiable hr y) u
  have h2 (u : TangentSpace 𝓘(ℝ, G) v) : mfderiv 𝓘(ℝ, G) I (g.symm ∘ ψ.symm) v u =
      mfderiv I' I g.symm (ψ.symm v) (mfderiv 𝓘(ℝ, G) I' ψ.symm v u) :=
    mfderiv_comp_apply v (g.symm.mdifferentiable hr _) hψs u
  rw [h1]
  -- `h2` is stated at the base point `(g.symm ∘ ψ.symm) v`, which is `y` by definition.
  erw [h2]
  rw [ContMDiffAlmostComplexStructure.mfderiv_pullback_apply, ← hy,
    Diffeomorph.mfderiv_apply_mfderiv_symm_apply g hr]

/-- **Transport in charts.** Read in a chart `φ` of the domain and the chart `g ≫ ψ` of `M`, the
pulled-back structure `g^* J` is `J` read in `φ` and `ψ`. -/
@[simp]
theorem chartField_pullback_trans (φ : OpenPartialHomeomorph P D)
    (ψ : OpenPartialHomeomorph N G) :
    (J.pullback g hnr).chartField φ (g.toHomeomorph.toOpenPartialHomeomorph.trans ψ) =
      J.chartField φ ψ :=
  J.chartField_pullback g hnr φ rfl rfl

end ChartField

end ContMDiffAlmostComplexStructureFamily

end TauCeti
