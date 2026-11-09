/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TateGauge.NormDatum
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer

/-!
# Compatible normed Tate structures

A norm datum on a Hausdorff topological Tate ring gives a genuine ring norm. On a ring
with its additive group uniformity, this norm induces exactly the original uniformity.
We install it as an explicitly chosen `NormedCommRing` structure, retaining the original
uniform space definitionally; completeness therefore transfers without a new completion.
The chosen topological pseudo-uniformiser becomes a multiplicative pseudo-uniformiser
for this norm.

The construction does not assert that an arbitrary compatible norm is Tate. It selects
the gauge norm attached to the datum, and none of the alternative normed structures or
their properties are registered as global instances.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371
  (2015), §2.4 and Remark 2.4.4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Filter Topology
open scoped Uniformity

namespace TauCeti.Huber

variable {A : Type*} [CommRing A]

section RingNorm

variable [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] (d : TateNormDatum A)

/-- The gauge of a norm datum on a Hausdorff ring, as a genuine ring norm. -/
noncomputable def tateRingNorm : RingNorm A :=
  { tateNorm d with
    eq_zero_of_map_eq_zero' := fun x hx ↦ by
      simpa using (tateNorm_eq_zero_iff d).mp hx }

/-- The ring norm is the original gauge seminorm pointwise. -/
@[simp]
theorem tateRingNorm_apply (x : A) : tateRingNorm d x = tateNorm d x := (rfl)

end RingNorm

section Uniformity

variable [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [T2Space A]
  (d : TateNormDatum A)

/-- The gauge ring norm induces the original additive group uniformity. -/
theorem uniformity_tateRingNorm :
    𝓤 A = @uniformity A (tateRingNorm d).toNormedRing.toUniformSpace := by
  let n := (tateRingNorm d).toNormedRing
  -- The ring-norm metric is defined by the norm of the difference. Use its explicit
  -- instance here, so the original and the new uniformities can be compared.
  have hd (x y : A) : @dist A n.toDist x y = tateNorm d (-x + y) := rfl
  have hb := (tateNorm_hasBasis_nhds_zero d).uniformity_of_nhds_zero
  refine hb.eq_of_same_basis ((@Metric.uniformity_basis_dist A n.toPseudoMetricSpace).congr
    (fun _ ↦ Iff.rfl) ?_)
  intro ε _
  ext p
  simp only [Set.mem_ofPred_eq, hd, sub_eq_neg_add]

/-- The explicitly chosen gauge normed ring, with the original uniformity and topology.
This is an abbreviation so that the inherited ring and uniform space remain definitionally
unchanged for consumers. It is not a global instance: different data can give different norms. -/
noncomputable abbrev tateNormedCommRing : NormedCommRing A :=
  { (tateRingNorm d).toNormedRing, ‹CommRing A› with
    toMetricSpace := (tateRingNorm d).toNormedRing.toMetricSpace.replaceUniformity
      (uniformity_tateRingNorm d) }

/-- The compatible normed structure has the gauge norm. -/
@[simp]
theorem norm_tateNormedCommRing (x : A) :
    @norm A (tateNormedCommRing d).toNorm x = tateNorm d x := (rfl)

/-- The compatible normed structure retains the original commutative ring. -/
@[simp]
theorem commRing_tateNormedCommRing :
    (tateNormedCommRing d).toCommRing = (inferInstance : CommRing A) := (rfl)

/-- The compatible normed structure retains the original uniform space. -/
@[simp]
theorem uniformSpace_tateNormedCommRing :
    (tateNormedCommRing d).toUniformSpace = (inferInstance : UniformSpace A) := (rfl)

/-- Completeness of the original additive group uniformity is preserved. -/
theorem completeSpace_tateNormedCommRing [CompleteSpace A] :
    @CompleteSpace A (tateNormedCommRing d).toUniformSpace := by
  rw [uniformSpace_tateNormedCommRing]
  infer_instance

/-- The selected gauge norm is ultrametric. -/
theorem isUltrametricDist_tateNormedCommRing :
    letI := tateNormedCommRing d
    IsUltrametricDist A := by
  have h := isNonarchimedean_tateNorm d
  let := tateNormedCommRing d
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm h

variable [Nontrivial A]

/-- The selected gauge norm is normalized at one on a nonzero ring. -/
theorem normOneClass_tateNormedCommRing :
    letI := tateNormedCommRing d
    NormOneClass A := by
  let := tateNormedCommRing d
  exact ⟨tateNorm_one d⟩

/-- The chosen topological pseudo-uniformiser becomes a multiplicative pseudo-uniformiser
for the compatible gauge norm. -/
noncomputable def tateNormedPseudoUniformizer :
    letI := tateNormedCommRing d
    NormedRing.PseudoUniformizer A := by
  letI := tateNormedCommRing d
  have hnorm : ‖(d.pseudoUniformizer : A)‖ = d.radius := by
    simpa using tateNorm_pseudoUniformizer_mul d 1
  exact
    { unit := d.pseudoUniformizer
      norm_mul := fun x ↦ by
        simpa only [hnorm, norm_tateNormedCommRing] using tateNorm_pseudoUniformizer_mul d x
      norm_pos := hnorm.symm ▸ d.radius_pos
      norm_lt_one := hnorm.symm ▸ d.radius_lt_one }

/-- The chosen multiplicative pseudo-uniformiser has the original unit. -/
@[simp]
theorem tateNormedPseudoUniformizer_unit :
    letI := tateNormedCommRing d
    (tateNormedPseudoUniformizer d).unit = d.pseudoUniformizer := (rfl)

/-- The gauge makes a nonzero Hausdorff ring with norm datum normed Tate. -/
theorem isTate_tateNormedCommRing :
    letI := tateNormedCommRing d
    NormedRing.IsTate A := by
  let := tateNormedCommRing d
  exact ⟨⟨tateNormedPseudoUniformizer d⟩⟩

end Uniformity

end TauCeti.Huber
