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

Composing two pair-of-pants products glues the output of one pair of pants `S'` into an input
`q ∈ {0, 1}` of another `S`, along the affine plumbing map
`ψ = TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L` of neck length `L`. The glued domain
is the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`. This file glues the domain-dependent almost
complex structures of the two pieces, on the tangent bundle of a manifold `M` with a nondegenerate
two-form `σ`, such as a closed symplectic manifold.

Each piece carries the structure `TauCeti.SmoothTwoForm.Compatible.pairOfPantsAlmostComplex`
built from a compatible base structure and three jointly smooth period-one families of tame end
structures. When the output family of `S'` is the input family of `S` at `q`, the two structures
agree on the cylindrical part of the neck, where both are this common end structure
(`TauCeti.SmoothTwoForm.Compatible.pairOfPantsAlmostComplex_plumbingMap`). The glued structure
`TauCeti.SmoothTwoForm.Compatible.plumbedAlmostComplex` uses the inserted structure, read through
`w ↦ (w - c_q) / ψ'`, on the half `Re z > L/2` of the end `q`, and the receiving structure
elsewhere.

* On every tangent fiber it is the linear plumbed structure `TauCeti.Floer.plumbedAlmostComplex`
  (`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_plumbedAlmostComplex`).
* It is tamed by `σ`, and compatible with `σ` when the end structures are.
* Off the width-two collar `Re z > L - 2` of the end `q` it is the receiving structure, and off
  the width-two collar `Re z < 2 - L` of the end at `∞` its pullback along `ψ` is the inserted
  structure.
* For `L > 4` it is smooth jointly in the neck length, the domain point and the target point, as a
  section of the tangent endomorphism bundle
  (`TauCeti.SmoothTwoForm.Compatible.contMDiff_plumbedAlmostComplex`).

Together with the plumbed Hamiltonian perturbation `TauCeti.Floer.plumbedPerturbation`, this is the
Floer datum on the broken ends of the families of four-punctured spheres that compare the two
compositions of pair-of-pants products, for a manifold target.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 10.9.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 9.
-/

public noncomputable section

open Bundle Set Real Manifold Topology
open scoped ContDiff
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {Jₐ Jᵦ : SmoothAlmostComplexStructure I M}
  (hₐ : σ.Compatible Jₐ) (hᵦ : σ.Compatible Jᵦ)
  (Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M)
  (hJa : ∀ r t, σ.Tames (Ja r t)) (hJb : ∀ r t, σ.Tames (Jb r t))
  (hJap : ∀ r, Function.Periodic (Ja r) 1)
  (hJas : ∀ r, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((Ja r p.1).toEndomorphism p.2)))
  (hJbp : ∀ r, Function.Periodic (Jb r) 1)
  (hJbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((Jb r p.1).toEndomorphism p.2)))
  {q : Puncture} {L : ℝ}

/-- The pair-of-pants structures of the two pieces agree on the cylindrical plumbing overlap,
where both are the common end structure. -/
theorem pairOfPantsAlmostComplex_plumbingMap (hab : Jb q = Ja inf) {w : ℂ}
    (hw : w ≠ 0 ∧ w ≠ 1) (hψ : q.plumbingMap L w ≠ 0 ∧ q.plumbingMap L w ≠ 1)
    (h₁ : (inf.endCoord w).re ≤ -2) (h₂ : 2 ≤ q.endSign * ((inf.endCoord w).re + L)) :
    hᵦ.pairOfPantsAlmostComplex Jb hJb hJbp hJbs ⟨q.plumbingMap L w, hψ⟩ =
      hₐ.pairOfPantsAlmostComplex Ja hJa hJap hJas ⟨w, hw⟩ := by
  ext x v
  have heq : (hᵦ.pairOfPantsAlmostComplex Jb hJb hJbp hJbs
        ⟨q.plumbingMap L w, hψ⟩).almostComplexStructureAt x =
      (hₐ.pairOfPantsAlmostComplex Ja hJa hJap hJas ⟨w, hw⟩).almostComplexStructureAt x := by
    rw [almostComplexStructureAt_pairOfPantsAlmostComplex,
      almostComplexStructureAt_pairOfPantsAlmostComplex]
    exact Floer.pairOfPantsAlmostComplex_plumbingMap (hₐ.compatibleAt x) (hᵦ.compatibleAt x)
      (by simp only [hab]) h₁ h₂ ()
  simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using
    congrArg (fun A : AlmostComplexStructure (TangentSpace I x) => A v) heq

/-- Almost complex data on the tangent bundle over the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`
obtained by plumbing the output of the first pair of pants into the input `q` of the second, with
neck length `L`. On the half `Re z > L/2` of the end `q` it is the structure of the first pair of
pants at `(w - c_q) / ψ'`, and elsewhere the structure of the second. For `L > 4`, `q ≠ ∞` and
matching end data the two formulas agree near the seam. -/
def plumbedAlmostComplex (q : Puncture) (L : ℝ) (w : ℂ)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) : SmoothAlmostComplexStructure I M :=
  if L / 2 < (q.endCoord w).re then
    hₐ.pairOfPantsAlmostComplex Ja hJa hJap hJas
      ⟨(w - q.endCenter) / q.plumbingFactor L,
        q.sub_endCenter_div_plumbingFactor_ne_zero_and_ne_one L hw⟩
  else hᵦ.pairOfPantsAlmostComplex Jb hJb hJbp hJbs ⟨w, hw.1⟩

/-- The two formulas defining the plumbed structure. -/
theorem plumbedAlmostComplex_def (w : ℂ) (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) :
    hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs q L w hw =
      if L / 2 < (q.endCoord w).re then
        hₐ.pairOfPantsAlmostComplex Ja hJa hJap hJas
          ⟨(w - q.endCenter) / q.plumbingFactor L,
            q.sub_endCenter_div_plumbingFactor_ne_zero_and_ne_one L hw⟩
      else hᵦ.pairOfPantsAlmostComplex Jb hJb hJbp hJbs ⟨w, hw.1⟩ := (rfl)

/-- On every tangent fiber, the plumbed structure is the linear plumbed structure of the fiberwise
end data. -/
theorem almostComplexStructureAt_plumbedAlmostComplex (w : ℂ)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (x : M) :
    (hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs q L w
        hw).almostComplexStructureAt x =
      Floer.plumbedAlmostComplex (V := TangentSpace I x) (hₐ.compatibleAt x) (hᵦ.compatibleAt x)
        (fun r t (_ : Unit) => (Ja r t).almostComplexStructureAt x)
        (fun r t (_ : Unit) => (Jb r t).almostComplexStructureAt x)
        (fun r t _ => hₐ.isNondegenerate.tames_iff.mp (hJa r t) x)
        (fun r t _ => hᵦ.isNondegenerate.tames_iff.mp (hJb r t) x) q L w () := by
  rw [plumbedAlmostComplex_def, Floer.plumbedAlmostComplex_def]
  split_ifs <;> exact almostComplexStructureAt_pairOfPantsAlmostComplex _ _ _ _ _ _ x

/-- The plumbed structure is tamed by the two-form, regardless of the neck length. -/
theorem tames_plumbedAlmostComplex (w : ℂ) (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) :
    σ.Tames (hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs q L w hw) := by
  rw [plumbedAlmostComplex_def]
  split_ifs
  · exact tames_pairOfPantsAlmostComplex _ _ _ _ _ _
  · exact tames_pairOfPantsAlmostComplex _ _ _ _ _ _

/-- Compatible end data give a compatible plumbed structure. -/
theorem compatible_plumbedAlmostComplex (hJac : ∀ r t, σ.Compatible (Ja r t))
    (hJbc : ∀ r t, σ.Compatible (Jb r t)) (w : ℂ)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) :
    σ.Compatible (hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs q L w hw) := by
  rw [plumbedAlmostComplex_def]
  split_ifs
  · exact compatible_pairOfPantsAlmostComplex _ _ _ _ _ hJac _
  · exact compatible_pairOfPantsAlmostComplex _ _ _ _ _ hJbc _

/-- Outside the width-two collar at the receiving cut, the glued structure is the structure of the
receiving pair of pants. -/
theorem plumbedAlmostComplex_of_re_endCoord_le (hq : q ≠ inf) (hab : Jb q = Ja inf) {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (hle : (q.endCoord w).re ≤ L - 2) :
    hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs q L w hw =
      hᵦ.pairOfPantsAlmostComplex Jb hJb hJbp hJbs ⟨w, hw.1⟩ := by
  ext x v
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    ← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_plumbedAlmostComplex,
    almostComplexStructureAt_pairOfPantsAlmostComplex,
    Floer.plumbedAlmostComplex_of_re_endCoord_le _ _ hq (by simp only [hab]) hle]

/-- Outside the width-two collar at the inserted cut, the glued structure pulls back along the
plumbing map to the structure of the inserted pair of pants. -/
theorem plumbedAlmostComplex_plumbingMap (hq : q ≠ inf) (hab : Jb q = Ja inf) {w : ℂ}
    (hw : w ≠ 0 ∧ w ≠ 1)
    (hψ : (q.plumbingMap L w ≠ 0 ∧ q.plumbingMap L w ≠ 1) ∧
      q.plumbingMap L w ≠ q.plumbingMap L 1)
    (h : 2 - L ≤ (inf.endCoord w).re) :
    hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs q L (q.plumbingMap L w) hψ =
      hₐ.pairOfPantsAlmostComplex Ja hJa hJap hJas ⟨w, hw⟩ := by
  ext x v
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    ← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_plumbedAlmostComplex,
    almostComplexStructureAt_pairOfPantsAlmostComplex,
    Floer.plumbedAlmostComplex_plumbingMap _ _ hq (by simp only [hab]) hw.1 h]

/-- Deep in the receiving end, the glued structure is the inserted structure in the affine
plumbing coordinate. This formula holds on an open set independent of the neck length. -/
theorem plumbedAlmostComplex_eq_inserted (hq : q ≠ inf) (hab : Jb q = Ja inf) {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (h2 : 2 < (q.endCoord w).re) :
    hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs q L w hw =
      hₐ.pairOfPantsAlmostComplex Ja hJa hJap hJas
        ⟨(w - q.endCenter) / q.plumbingFactor L,
          q.sub_endCenter_div_plumbingFactor_ne_zero_and_ne_one L hw⟩ := by
  ext x v
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    ← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_plumbedAlmostComplex,
    almostComplexStructureAt_pairOfPantsAlmostComplex,
    Floer.plumbedAlmostComplex_eq_inserted _ _ hq (by simp only [hab]) h2]

/-- **Joint smoothness of the plumbed structure.** For neck lengths `L > 4`, the plumbed structure
is `C^n` jointly in the neck length, the domain point and the target point, along any `C^n`
family of these avoiding the punctures, as a section of the tangent endomorphism bundle. The
family may depend on further manifold parameters. -/
theorem contMDiff_plumbedAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] (hq : q ≠ inf) (hab : Jb q = Ja inf)
    {ℓ : N → ℝ} {f : N → ℂ} {b : N → M} (hℓ : ContMDiff I' 𝓘(ℝ) n ℓ)
    (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) (hL : ∀ p, 4 < ℓ p)
    (hS : ∀ p, (f p ≠ 0 ∧ f p ≠ 1) ∧ f p ≠ q.plumbingMap (ℓ p) 1) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) (b p)
        ((hₐ.plumbedAlmostComplex hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs q (ℓ p) (f p)
          (hS p)).toEndomorphism (b p))) := by
  intro p
  have hc : f p ≠ q.endCenter := ne_endCenter (hS p).1 q
  have hcont : ContinuousAt (fun p => (q.endCoord (f p)).re) p :=
    (q.contDiffAt_re_endCoord hc (n := 0)).continuousAt.comp hf.continuous.continuousAt
  -- The two open regions `Re z < L - 2` and `Re z > 2` of the end `q` cover the moving seam;
  -- on each the plumbed structure is one smooth pair-of-pants structure.
  rcases lt_or_ge (q.endCoord (f p)).re (ℓ p - 2) with hlt | hge
  · refine ((hᵦ.contMDiff_pairOfPantsAlmostComplex Jb hJb hJbp hJbs hf hb
      (fun p => (hS p).1)) p).congr_of_eventuallyEq ?_
    have hdiff : ContinuousAt (fun p => ℓ p - 2 - (q.endCoord (f p)).re) p :=
      ((hℓ.continuous.continuousAt).sub continuousAt_const).sub hcont
    filter_upwards [hdiff.eventually (lt_mem_nhds (by linarith : 0 < ℓ p - 2 - _))] with p' hp'
    rw [plumbedAlmostComplex_of_re_endCoord_le hₐ hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs hq hab
      (hS p') (by linarith)]
  · have h2 : 2 < (q.endCoord (f p)).re := by linarith [hL p]
    -- The inserted piece moves with the length through the inverse plumbing map.
    have hg : ContMDiff I' 𝓘(ℝ, ℂ) n
        (fun p => (f p - q.endCenter) / q.plumbingFactor (ℓ p)) :=
      (q.contDiff_inverse_plumbingMap (n := n)).contMDiff.comp (hℓ.prodMk_space hf)
    refine ((hₐ.contMDiff_pairOfPantsAlmostComplex Ja hJa hJap hJas hg hb fun p =>
      q.sub_endCenter_div_plumbingFactor_ne_zero_and_ne_one _ (hS p)) p).congr_of_eventuallyEq ?_
    filter_upwards [hcont.eventually (lt_mem_nhds h2)] with p' hp'
    rw [plumbedAlmostComplex_eq_inserted hₐ hᵦ Ja Jb hJa hJb hJap hJas hJbp hJbs hq hab
      (hS p') hp']

end TauCeti.SmoothTwoForm.Compatible
