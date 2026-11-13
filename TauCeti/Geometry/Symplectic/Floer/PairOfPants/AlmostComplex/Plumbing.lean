/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Basic
public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Plumbing

/-!
# Almost complex data on plumbed pairs of pants

Glue the output of one pair of pants into an input `q` of another, with matching period-one
almost complex structures on the glued ends. The structures on the two pieces agree on the
cylindrical overlap, so they define an almost complex structure on the four-punctured sphere
`ℂ ∖ {0, 1, ψ(1)}`, where `ψ` is the affine plumbing map. This supplies almost complex data
for the broken-product ends of a four-punctured-sphere family.

`plumbedAlmostComplex` uses the inserted structure on the half-neck `Re z > L/2` and the
receiving structure elsewhere. It is tame, and compatible when the end structures are
compatible. The restriction formulas identify it with the original structures outside fixed
width-two collars. For neck length `L > 4` it is smooth jointly in the length, domain point
and external manifold parameter. In particular the moving seam introduces no loss of
regularity: near it both formulas are the same cylindrical structure.

The structures act on a fixed symplectic vector space; the external parameter may be a target
point. The construction on the tangent bundle of a manifold target, which applies this one in
each tangent fiber, is `TauCeti.SmoothTwoForm.Compatible.plumbedAlmostComplex`.
The two pieces may use different compatible base structures in their Cayley constructions.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 10.9.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 9.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {Jₐ Jᵦ : AlmostComplexStructure V}
  (hₐ : ω.Compatible Jₐ) (hᵦ : ω.Compatible Jᵦ)
  {Ja Jb : Puncture → ℝ → M → AlmostComplexStructure V}
  {hJa : ∀ r t x, ω.Tames (Ja r t x)} {hJb : ∀ r t x, ω.Tames (Jb r t x)}
  {q : Puncture} {L : ℝ}

/-- The structures on the two pairs of pants match on the cylindrical plumbing overlap. -/
theorem pairOfPantsAlmostComplex_plumbingMap (hab : Jb q = Ja inf) {w : ℂ}
    (h₁ : (inf.endCoord w).re ≤ -2) (h₂ : 2 ≤ q.endSign * ((inf.endCoord w).re + L))
    (x : M) :
    pairOfPantsAlmostComplex hᵦ Jb hJb (q.plumbingMap L w) x =
      pairOfPantsAlmostComplex hₐ Ja hJa w x := by
  have hw : w ≠ 0 := by
    simpa using inf.ne_endCenter_of_re_endCoord_ne_zero (by linarith : (inf.endCoord w).re < 0).ne
  rw [pairOfPantsAlmostComplex_eq_endStructure hᵦ
      (by rw [re_endCoord_plumbingMap q L hw]; exact h₂),
    pairOfPantsAlmostComplex_eq_endStructure (q := inf) hₐ (by simp; linarith),
    endCoord_plumbingMap q L hw, Complex.add_im, Complex.ofReal_im, add_zero, hab]

open Classical in
/-- Almost complex data on the four-punctured sphere obtained by plumbing the output of the
first pair of pants into the input `q` of the second. The seam is at longitudinal coordinate
`L/2`. For `L > 4`, `q ≠ ∞` and matching period-one end data, the formulas agree near the seam. -/
def plumbedAlmostComplex (Ja Jb : Puncture → ℝ → M → AlmostComplexStructure V)
    (hJa : ∀ r t x, ω.Tames (Ja r t x)) (hJb : ∀ r t x, ω.Tames (Jb r t x))
    (q : Puncture) (L : ℝ) (w : ℂ) (x : M) : AlmostComplexStructure V :=
  if L / 2 < (q.endCoord w).re then
    pairOfPantsAlmostComplex hₐ Ja hJa ((w - q.endCenter) / q.plumbingFactor L) x
  else pairOfPantsAlmostComplex hᵦ Jb hJb w x

open Classical in
/-- The two formulas defining the plumbed structure. -/
theorem plumbedAlmostComplex_def (w : ℂ) (x : M) :
    plumbedAlmostComplex hₐ hᵦ Ja Jb hJa hJb q L w x =
      if L / 2 < (q.endCoord w).re then
        pairOfPantsAlmostComplex hₐ Ja hJa ((w - q.endCenter) / q.plumbingFactor L) x
      else pairOfPantsAlmostComplex hᵦ Jb hJb w x := (rfl)

/-- The plumbed structure is tame, regardless of the neck length. -/
theorem tames_plumbedAlmostComplex (w : ℂ) (x : M) :
    ω.Tames (plumbedAlmostComplex hₐ hᵦ Ja Jb hJa hJb q L w x) := by
  rw [plumbedAlmostComplex_def]
  split_ifs <;> exact tames_pairOfPantsAlmostComplex _ _ _

/-- Compatible end data give a compatible plumbed structure. -/
theorem compatible_plumbedAlmostComplex
    (hJac : ∀ r t x, ω.Compatible (Ja r t x)) (hJbc : ∀ r t x, ω.Compatible (Jb r t x))
    (w : ℂ) (x : M) :
    ω.Compatible (plumbedAlmostComplex hₐ hᵦ Ja Jb hJa hJb q L w x) := by
  rw [plumbedAlmostComplex_def]
  split_ifs
  · exact compatible_pairOfPantsAlmostComplex hₐ hJac _ _
  · exact compatible_pairOfPantsAlmostComplex hᵦ hJbc _ _

/-- Outside the width-two collar at the receiving cut, the glued structure is unchanged. -/
theorem plumbedAlmostComplex_of_re_endCoord_le (hq : q ≠ inf) (hab : Jb q = Ja inf)
    {w : ℂ} (hw : (q.endCoord w).re ≤ L - 2) (x : M) :
    plumbedAlmostComplex hₐ hᵦ Ja Jb hJa hJb q L w x =
      pairOfPantsAlmostComplex hᵦ Jb hJb w x := by
  rw [plumbedAlmostComplex_def]
  split_ifs with h
  · have hc : w ≠ q.endCenter :=
      q.ne_endCenter_of_re_endCoord_ne_zero (by linarith : 0 < (q.endCoord w).re).ne'
    have hre := re_endCoord_inf_sub_endCenter_div q L hc
    rw [← pairOfPantsAlmostComplex_plumbingMap (L := L) hₐ hᵦ hab (by linarith)
      (by rw [endSign_eq_one hq]; linarith) x, plumbingMap_sub_endCenter_div]
  · rfl

/-- Outside the width-two collar at the inserted cut, the glued structure pulls back to the
original structure on the inserted pair of pants. -/
theorem plumbedAlmostComplex_plumbingMap (hq : q ≠ inf) (hab : Jb q = Ja inf)
    {w : ℂ} (hw : w ≠ 0) (h : 2 - L ≤ (inf.endCoord w).re) (x : M) :
    plumbedAlmostComplex hₐ hᵦ Ja Jb hJa hJb q L (q.plumbingMap L w) x =
      pairOfPantsAlmostComplex hₐ Ja hJa w x := by
  rw [plumbedAlmostComplex_def, re_endCoord_plumbingMap q L hw]
  split_ifs with h'
  · rw [plumbingMap_sub_endCenter_div_plumbingFactor]
  · exact pairOfPantsAlmostComplex_plumbingMap hₐ hᵦ hab (by linarith)
      (by rw [endSign_eq_one hq]; linarith) x

/-- Deep in the receiving end, the glued structure is the inserted structure in the affine
plumbing coordinate. This formula holds on an open set independent of the neck length. -/
theorem plumbedAlmostComplex_eq_inserted (hq : q ≠ inf) (hab : Jb q = Ja inf)
    {w : ℂ} (hw : 2 < (q.endCoord w).re) (x : M) :
    plumbedAlmostComplex hₐ hᵦ Ja Jb hJa hJb q L w x =
      pairOfPantsAlmostComplex hₐ Ja hJa ((w - q.endCenter) / q.plumbingFactor L) x := by
  have hc : w ≠ q.endCenter :=
    q.ne_endCenter_of_re_endCoord_ne_zero (by linarith : 0 < (q.endCoord w).re).ne'
  have hre := re_endCoord_inf_sub_endCenter_div q L hc
  have h := plumbedAlmostComplex_plumbingMap (L := L) (hJa := hJa) (hJb := hJb)
    hₐ hᵦ hq hab
    (q.sub_endCenter_div_plumbingFactor_ne_zero L hc) (by linarith) x
  rwa [plumbingMap_sub_endCenter_div] at h

end TauCeti.Floer

namespace TauCeti.Floer

variable {M V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {Jₐ Jᵦ : AlmostComplexStructure V}
  (hₐ : ω.Compatible Jₐ) (hᵦ : ω.Compatible Jᵦ)
  {Ja Jb : Puncture → ℝ → M → AlmostComplexStructure V}
  {hJa : ∀ r t x, ω.Tames (Ja r t x)} {hJb : ∀ r t x, ω.Tames (Jb r t x)}
  {q : Puncture} {L : ℝ}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- Smooth end data give a structure smooth jointly in neck length, domain point and external
parameter on the total space of four-punctured spheres with neck length greater than four. -/
theorem contMDiffAt_plumbedAlmostComplex {n : ℕ∞} (hq : q ≠ inf)
    (hJap : ∀ r, Periodic (Ja r) 1) (hJbp : ∀ r, Periodic (Jb r) 1)
    (hJas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (Ja r p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (Jb r p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hab : Jb q = Ja inf) (hL : 4 < L) {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × (ℂ × M) => LinearMap.toContinuousLinearMap
        (plumbedAlmostComplex hₐ hᵦ Ja Jb hJa hJb q p.1 p.2.1 p.2.2).toLinearMap)
      (L, (w, x)) := by
  have hc : w ≠ q.endCenter := ne_endCenter hw.1 q
  have hcont : ContinuousAt (fun p : ℝ × (ℂ × M) => (q.endCoord p.2.1).re) (L, (w, x)) :=
    ContinuousAt.comp (g := fun w => (q.endCoord w).re) (f := fun p : ℝ × (ℂ × M) => p.2.1)
      (q.contDiffAt_re_endCoord hc (n := 0)).continuousAt
      (continuousAt_fst.comp continuousAt_snd)
  -- These two open regions cover the moving seam; on each we use one smooth piece.
  rcases lt_or_ge (q.endCoord w).re (L - 2) with hlt | hge
  · refine ((contMDiffAt_pairOfPantsAlmostComplex (hJ := hJb) hᵦ hJbp hJbs ⟨w, hw.1⟩ x).comp
      (L, (w, x)) contMDiffAt_snd).congr_of_eventuallyEq ?_
    have hdiff : ContinuousAt (fun p : ℝ × (ℂ × M) =>
        p.1 - 2 - (q.endCoord p.2.1).re) (L, (w, x)) :=
      (continuousAt_fst.sub continuousAt_const).sub hcont
    filter_upwards [hdiff.eventually (lt_mem_nhds (by linarith : 0 < L - 2 - (q.endCoord w).re))]
      with p hp
    rw [plumbedAlmostComplex_of_re_endCoord_le hₐ hᵦ hq hab
      (by linarith : (q.endCoord p.2.1).re ≤ p.1 - 2)]
    rfl
  · have h2 : 2 < (q.endCoord w).re := by linarith
    have hw' := (q.plumbingPreimage L ⟨w, hw.1⟩ hw.2).2
    rw [coe_plumbingPreimage] at hw'
    -- The inserted piece also moves with the length through the inverse plumbing map.
    have hf := (q.contDiff_inverse_plumbingMap (n := n)).contDiffAt (x := (L, w))
    have hcoord : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
        (fun p : ℝ × (ℂ × M) => (p.2.1 - q.endCenter) / q.plumbingFactor p.1) (L, (w, x)) :=
      hf.contMDiffAt.comp (f := fun p : ℝ × (ℂ × M) => (p.1, p.2.1)) (L, (w, x))
        (contMDiffAt_fst.prodMk_space (contMDiffAt_fst.comp _ contMDiffAt_snd))
    refine ((contMDiffAt_pairOfPantsAlmostComplex (hJ := hJa) hₐ hJap hJas ⟨_, hw'⟩ x).comp
      (L, (w, x)) (hcoord.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))).congr_of_eventuallyEq ?_
    filter_upwards [hcont.eventually (lt_mem_nhds h2)] with p hp
    rw [plumbedAlmostComplex_eq_inserted hₐ hᵦ hq hab hp]
    rfl

end TauCeti.Floer
