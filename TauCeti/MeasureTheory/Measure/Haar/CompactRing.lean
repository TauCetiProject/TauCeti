/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MvPolynomial
public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus
public import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Haar measure on compact rings

Let `A` be a compact Hausdorff topological ring and `μ` its additive Haar probability measure. (A
locally compact ring carrying an additive Haar probability measure is compact, so the statements
below assume local compactness only.)

* Multiplication by a unit, on either side, is a continuous additive automorphism of `A`, so it
  carries `μ` to an additive Haar probability measure, which is `μ` by uniqueness
  (`TauCeti.map_mul_left_eq_self_of_isUnit`, `TauCeti.map_mul_right_eq_self_of_isUnit`).
* If a compact group `G` embeds continuously and multiplicatively into `A` with open image `U`
  (for instance a compact open subgroup of `A^×`, or `GL_n(O)` inside `M_n(O)`), then the
  normalized Haar measure `haarProb G` is the restriction of `μ` to `U`, pulled back to `G` and
  divided by `μ U` (`TauCeti.haarProb_eq_smul_comap`). Indeed that measure is left invariant,
  because left multiplication by the image of `g` preserves `μ`, and it is a Haar probability
  measure.
* If `A` is moreover a second-countable integral domain without isolated points, the zero set of
  a nonzero polynomial in finitely many variables over `A` is closed and null for the product of
  copies of `μ` (`TauCeti.measure_pi_setOf_eval_eq_zero_of_compactRing`), as `μ` has no atoms;
  this holds for every locally compact such ring. With isolated points it fails: over a finite
  field `F_q`, `X ^ q - X` vanishes everywhere. It also fails for rings that are not domains: on
  the Boolean ring `(ℤ/2)^ℕ`, `X ^ 2 - X` vanishes everywhere.

## References

* J.-P. Serre, *Quelques applications du théorème de densité de Chebotarev*, Publ. Math. IHÉS 54
  (1981), Introduction and §6.4, proof of Proposition 13.
-/

public section

open MeasureTheory Set Topology

namespace TauCeti

section Units

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]
  [IsProbabilityMeasure μ]

/-- A surjective continuous additive endomorphism of a locally compact group preserves its
additive Haar probability measure. -/
private theorem map_eq_self_of_addMonoidHom (f : A →+ A) (hf : Continuous f)
    (hsurj : Function.Surjective f) : μ.map f = μ := by
  have : (μ.map f).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure μ f hf hsurj
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- **Left multiplication by a unit preserves additive Haar probability.** -/
theorem map_mul_left_eq_self_of_isUnit {u : A} (hu : IsUnit u) : μ.map (u * ·) = μ :=
  map_eq_self_of_addMonoidHom μ (AddMonoidHom.mulLeft u) (continuous_const.mul continuous_id)
    fun y => ⟨↑hu.unit⁻¹ * y, by simp [← mul_assoc]⟩

/-- **Right multiplication by a unit preserves additive Haar probability.** -/
theorem map_mul_right_eq_self_of_isUnit {u : A} (hu : IsUnit u) : μ.map (· * u) = μ :=
  map_eq_self_of_addMonoidHom μ (AddMonoidHom.mulRight u) (continuous_id.mul continuous_const)
    fun y => ⟨y * ↑hu.unit⁻¹, by simp [mul_assoc]⟩

/-- Left multiplication by a unit preserves the additive Haar probability of every measurable
set. -/
theorem measure_preimage_mul_left_of_isUnit {u : A} (hu : IsUnit u) {s : Set A}
    (hs : MeasurableSet s) : μ ((u * ·) ⁻¹' s) = μ s := by
  conv_rhs => rw [← map_mul_left_eq_self_of_isUnit μ hu]
  have hm : Measurable fun x : A => u * x := by fun_prop
  rw [Measure.map_apply hm hs]

variable [T2Space A] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **Haar measure on a compact open group of units.** Let `f` be a continuous injective
multiplicative map from a compact group `G` into a compact Hausdorff ring `A`, with open image.
Then the normalized Haar measure of `G` is the additive Haar probability of `A` restricted to the
image of `f`, pulled back along `f` and normalized by the measure of the image. -/
theorem haarProb_eq_smul_comap (f : G →* A) (hf : Continuous f) (hinj : Function.Injective f)
    (hopen : IsOpen (range f)) : haarProb G = (μ (range f))⁻¹ • μ.comap f := by
  have hemb : MeasurableEmbedding f :=
    (hf.isClosedEmbedding hinj).measurableEmbedding
  have hU0 : μ (range f) ≠ 0 := (hopen.measure_pos μ (range_nonempty f)).ne'
  have hUtop : μ (range f) ≠ ⊤ := measure_ne_top μ _
  let ν : Measure G := (μ (range f))⁻¹ • μ.comap f
  have hν (s : Set G) : ν s = (μ (range f))⁻¹ * μ (f '' s) := by
    simp [ν, hemb.comap_apply]
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν, image_univ, ENNReal.inv_mul_cancel hU0 hUtop]⟩
  have hunit (g : G) : IsUnit (f g) := (Group.isUnit g).map f
  have : ν.IsMulLeftInvariant := by
    refine ⟨fun g => Measure.ext fun s hs => ?_⟩
    have hm : Measurable fun x : G => g * x := by fun_prop
    rw [Measure.map_apply hm hs, hν, hν]
    congr 1
    have himage : f '' ((g * ·) ⁻¹' s) = (f g * ·) ⁻¹' (f '' s) := by
      ext y
      simp only [mem_image, mem_preimage]
      refine ⟨fun ⟨x, hx, hxy⟩ => ⟨g * x, hx, by rw [map_mul, hxy]⟩, fun ⟨x, hx, hxy⟩ => ?_⟩
      refine ⟨g⁻¹ * x, by simpa using hx, ?_⟩
      rw [map_mul, hxy, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    rw [himage, measure_preimage_mul_left_of_isUnit μ (hunit g) (hemb.measurableSet_image' hs)]
  have : ν.IsOpenPosMeasure := ⟨fun s hs hne => by
    rw [hν]
    refine mul_ne_zero (ENNReal.inv_ne_zero.2 hUtop) ?_
    have hopen' : IsOpen (f '' s) :=
      (IsOpenEmbedding.mk (hf.isClosedEmbedding hinj).toIsEmbedding hopen).isOpenMap s hs
    exact (hopen'.measure_pos μ (hne.image f)).ne'⟩
  have : ν.IsHaarMeasure := { }
  exact (Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν (haarProb G)).symm

end Units

section ZeroLocus

variable {A : Type*} [CommRing A] [IsDomain A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [T1Space A] [SecondCountableTopology A] [PerfectSpace A]
  [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]

/-- **Null zero loci.** Over a locally compact Hausdorff second-countable topological integral
domain without isolated points, such as a compact one, the zero set of a nonzero polynomial in
finitely many variables is closed and null for the product of copies of an additive Haar measure
(Serre, *Quelques applications
du théorème de densité de Chebotarev*, Introduction, for the null trace-zero locus). -/
theorem measure_pi_setOf_eval_eq_zero_of_compactRing {ι : Type*} [Fintype ι]
    {P : MvPolynomial ι A} (hP : P ≠ 0) :
    IsClosed {x : ι → A | MvPolynomial.eval x P = 0} ∧
      Measure.pi (fun _ : ι => μ) {x | MvPolynomial.eval x P = 0} = 0 :=
  ⟨isClosed_eq (MvPolynomial.continuous_eval P) continuous_const,
    MvPolynomial.measure_pi_setOfPred_eval_eq_zero (fun _ => μ) P hP⟩

end ZeroLocus

end TauCeti
