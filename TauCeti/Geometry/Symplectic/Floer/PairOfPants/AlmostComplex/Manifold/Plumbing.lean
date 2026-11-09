/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Plumbing

/-!
# Plumbed pair-of-pants almost complex data on a manifold

Glue the output of one pair of pants into an input `q ≠ ∞` of another, with the actual
manifold almost complex data of `TauCeti.SmoothTwoForm.Compatible.pairOfPantsAlmostComplex` on
both pieces and matching period-one structures on the glued ends. The result,
`TauCeti.SmoothTwoForm.Compatible.plumbedAlmostComplex`, is a smooth almost complex structure on
the target for each point `w` of the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, where `ψ` is the
affine plumbing map of neck length `L`. It uses the inserted structure, read through
`TauCeti.ThricePuncturedSphere.Puncture.plumbingPreimage`, on the half-neck `Re z > L/2` of the
end `q`, and the receiving structure elsewhere.

On each tangent fiber it is the linear plumbed structure `TauCeti.Floer.plumbedAlmostComplex`
(`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_plumbedAlmostComplex`). It is tame,
and compatible when the end structures are compatible. It equals the receiving structure off
the collar `Re z > L - 2` and the inserted structure deep in the end `Re z > 2`. The main result,
`TauCeti.SmoothTwoForm.Compatible.contMDiff_plumbedAlmostComplex`, says that for neck lengths
`L > 4` it is jointly smooth in the neck length, the domain point and the target point, as a
section of the tangent endomorphism bundle along the target projection. Near the moving seam
both formulas are the same cylindrical structure, so no regularity is lost there.

This supplies the almost complex data of the broken-product ends of the four-punctured-sphere
families on an actual target manifold, alongside the smooth plumbed Hamiltonian perturbation
`TauCeti.Floer.contMDiffAt_plumbedPerturbation`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 10.9.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 9.
-/

public noncomputable section

open Bundle Set Real Manifold Topology Function
open scoped ContDiff
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {Jₐ Jᵦ : SmoothAlmostComplexStructure I M}
  (hₐ : σ.Compatible Jₐ) (hᵦ : σ.Compatible Jᵦ)
  {Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M}
  {hJa : ∀ r t, σ.Tames (Ja r t)} {hJb : ∀ r t, σ.Tames (Jb r t)}
  {hJap : ∀ r, Periodic (Ja r) 1} {hJbp : ∀ r, Periodic (Jb r) 1}
  {hJas : ∀ r, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((Ja r p.1).toEndomorphism p.2))}
  {hJbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((Jb r p.1).toEndomorphism p.2))}
  {q : Puncture} {L : ℝ} {w : ThricePuncturedSphere} {hw : (w : ℂ) ≠ q.plumbingMap L 1}

open Classical in
/-- Almost complex data on the target over the four-punctured sphere obtained by plumbing the
output of the first pair of pants into the input `q` of the second. The seam is at longitudinal
coordinate `L/2`. For `L > 4`, `q ≠ ∞` and matching period-one end data, the two formulas agree
near the seam. -/
def plumbedAlmostComplex (Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJa : ∀ r t, σ.Tames (Ja r t)) (hJb : ∀ r t, σ.Tames (Jb r t))
    (hJap : ∀ r, Periodic (Ja r) 1) (hJbp : ∀ r, Periodic (Jb r) 1)
    (hJas : ∀ r, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((Ja r p.1).toEndomorphism p.2)))
    (hJbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((Jb r p.1).toEndomorphism p.2)))
    (q : Puncture) (L : ℝ) (w : ThricePuncturedSphere) (hw : (w : ℂ) ≠ q.plumbingMap L 1) :
    SmoothAlmostComplexStructure I M :=
  if L / 2 < (q.endCoord w).re then
    hₐ.pairOfPantsAlmostComplex Ja hJa hJap hJas (q.plumbingPreimage L w hw)
  else hᵦ.pairOfPantsAlmostComplex Jb hJb hJbp hJbs w

open Classical in
/-- The two formulas defining the plumbed structure. -/
theorem plumbedAlmostComplex_def :
    hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJbp hJas hJbs q L w hw =
      if L / 2 < (q.endCoord w).re then
        hₐ.pairOfPantsAlmostComplex Ja hJa hJap hJas (q.plumbingPreimage L w hw)
      else hᵦ.pairOfPantsAlmostComplex Jb hJb hJbp hJbs w := (rfl)

/-- On every tangent fiber, the plumbed structure is the linear plumbed structure of the fiber
values of the end data. -/
theorem almostComplexStructureAt_plumbedAlmostComplex (x : M) :
    (hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJbp hJas hJbs q L w
        hw).almostComplexStructureAt x =
      Floer.plumbedAlmostComplex (V := TangentSpace I x) (M := Unit) (hₐ.compatibleAt x)
        (hᵦ.compatibleAt x)
        (fun r t (_ : Unit) => (Ja r t).almostComplexStructureAt x)
        (fun r t (_ : Unit) => (Jb r t).almostComplexStructureAt x)
        (fun r t _ => hₐ.isNondegenerate.tames_iff.mp (hJa r t) x)
        (fun r t _ => hᵦ.isNondegenerate.tames_iff.mp (hJb r t) x) q L w () := by
  rw [plumbedAlmostComplex_def, Floer.plumbedAlmostComplex_def]
  split_ifs
  · rw [almostComplexStructureAt_pairOfPantsAlmostComplex, coe_plumbingPreimage]
  · rw [almostComplexStructureAt_pairOfPantsAlmostComplex]

/-- The plumbed structure is tamed by the given two-form, regardless of the neck length. -/
theorem tames_plumbedAlmostComplex :
    σ.Tames (hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJbp hJas hJbs q L w hw) := by
  rw [plumbedAlmostComplex_def]
  split_ifs
  · exact tames_pairOfPantsAlmostComplex hₐ Ja hJa hJap hJas _
  · exact tames_pairOfPantsAlmostComplex hᵦ Jb hJb hJbp hJbs _

/-- Compatible end data give a compatible plumbed structure. -/
theorem compatible_plumbedAlmostComplex
    (hJac : ∀ r t, σ.Compatible (Ja r t)) (hJbc : ∀ r t, σ.Compatible (Jb r t)) :
    σ.Compatible (hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJbp hJas hJbs q L w hw) := by
  rw [plumbedAlmostComplex_def]
  split_ifs
  · exact compatible_pairOfPantsAlmostComplex hₐ Ja hJa hJap hJas hJac _
  · exact compatible_pairOfPantsAlmostComplex hᵦ Jb hJb hJbp hJbs hJbc _

/-- Outside the width-two collar at the receiving cut, the glued structure is the receiving
structure. -/
theorem plumbedAlmostComplex_of_re_endCoord_le (hq : q ≠ inf) (hab : Jb q = Ja inf)
    (hwL : (q.endCoord w).re ≤ L - 2) :
    hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJbp hJas hJbs q L w hw =
      hᵦ.pairOfPantsAlmostComplex Jb hJb hJbp hJbs w := by
  refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
  rw [almostComplexStructureAt_plumbedAlmostComplex,
    almostComplexStructureAt_pairOfPantsAlmostComplex]
  exact Floer.plumbedAlmostComplex_of_re_endCoord_le _ _ hq (by rw [hab]) hwL ()

/-- Deep in the receiving end, the glued structure is the inserted structure at the point that
the plumbing map sends to `w`. This formula holds on an open set independent of the neck
length. -/
theorem plumbedAlmostComplex_eq_inserted (hq : q ≠ inf) (hab : Jb q = Ja inf)
    (hw₂ : 2 < (q.endCoord w).re) :
    hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJbp hJas hJbs q L w hw =
      hₐ.pairOfPantsAlmostComplex Ja hJa hJap hJas (q.plumbingPreimage L w hw) := by
  refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
  rw [almostComplexStructureAt_plumbedAlmostComplex,
    almostComplexStructureAt_pairOfPantsAlmostComplex, coe_plumbingPreimage]
  exact Floer.plumbedAlmostComplex_eq_inserted _ _ hq (by rw [hab]) hw₂ ()

/-- **Joint smoothness of the plumbed structure.** Smooth end data give a structure that is
`C^n` along any `C^n` family of neck lengths greater than four, points of the corresponding
four-punctured spheres, and target points. As for
`TauCeti.SmoothTwoForm.Compatible.contMDiff_pairOfPantsAlmostComplex`, the family may also
depend on independent external manifold parameters. -/
theorem contMDiff_plumbedAlmostComplex (hq : q ≠ inf) (hab : Jb q = Ja inf)
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n]
    {l : N → ℝ} {f : N → ℂ} {b : N → M} (hl : ContMDiff I' 𝓘(ℝ) n l)
    (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) (hl₄ : ∀ p, 4 < l p)
    (hS : ∀ p, f p ≠ 0 ∧ f p ≠ 1) (hS' : ∀ p, f p ≠ q.plumbingMap (l p) 1) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) (b p)
        ((hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJbp hJas hJbs q (l p) ⟨f p, hS p⟩
          (hS' p)).toEndomorphism (b p))) := by
  intro p₀
  have hre : ContinuousAt (fun p => (q.endCoord (f p)).re) p₀ :=
    ((q.contDiffAt_re_endCoord (ne_endCenter (hS p₀) q) (n := 0)).continuousAt).comp
      hf.continuous.continuousAt
  -- These two open regions cover the moving seam; on each we use one smooth piece.
  rcases lt_or_ge (q.endCoord (f p₀)).re (l p₀ - 2) with hlt | hge
  · refine (contMDiff_pairOfPantsAlmostComplex hᵦ Jb hJb hJbp hJbs hf hb hS
      p₀).congr_of_eventuallyEq ?_
    have hdiff : ContinuousAt (fun p => l p - 2 - (q.endCoord (f p)).re) p₀ :=
      ((hl.continuous.continuousAt).sub continuousAt_const).sub hre
    filter_upwards [hdiff.eventually (lt_mem_nhds (by linarith :
      (0 : ℝ) < l p₀ - 2 - (q.endCoord (f p₀)).re))] with p hp
    rw [plumbedAlmostComplex_of_re_endCoord_le hₐ hᵦ hq hab
      (by rw [Subtype.coe_mk]; linarith)]
  · -- The inserted piece also moves with the length through the inverse plumbing map.
    have hg : ContMDiff I' 𝓘(ℝ, ℂ) n
        (fun p => (q.plumbingPreimage (l p) ⟨f p, hS p⟩ (hS' p) : ℂ)) := by
      convert q.contDiff_inverse_plumbingMap.comp_contMDiff (hl.prodMk_space hf) using 1
      -- `convert` absorbs the two instance paths to `NormedSpace ℝ ℂ`; the functions agree.
      funext p
      exact coe_plumbingPreimage q (l p) ⟨f p, hS p⟩ (hS' p)
    refine (contMDiff_pairOfPantsAlmostComplex hₐ Ja hJa hJap hJas hg hb
      (fun p => (q.plumbingPreimage (l p) ⟨f p, hS p⟩ (hS' p)).2)
      p₀).congr_of_eventuallyEq ?_
    filter_upwards [hre.eventually (lt_mem_nhds (by linarith [hl₄ p₀] :
      (2 : ℝ) < (q.endCoord (f p₀)).re))] with p hp
    rw [plumbedAlmostComplex_eq_inserted hₐ hᵦ hq hab hp]

end TauCeti.SmoothTwoForm.Compatible
