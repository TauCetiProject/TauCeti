/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.MeasureTheory.Measure.Haar.CompactRing
public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus
public import TauCeti.RingTheory.MvPolynomial.FractionRing
public import TauCeti.Topology.Instances.Matrix

/-!
# Haar-null zero loci of polynomials on open matrix groups

Let `R` be a locally compact, second countable, `T₁` topological domain without isolated
points, with fraction field `E`, for instance the ring of integers `O_E` of a finite extension
`E` of `ℚ_ℓ`. A nonzero polynomial in finitely many variables with coefficients in `E` vanishes
only on a null set of `R`-points, for every σ-finite translation-invariant measure on the
coordinate space, in particular for every additive Haar measure
(`MvPolynomial.measure_setOf_eval_algebraMap_eq_zero`). Indeed such a measure is absolutely
continuous with respect to the product of additive Haar measures of `R`
(`MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure`), for which the zero locus of a
nonzero polynomial over `R` is null (`MvPolynomial.measure_pi_setOfPred_eval_eq_zero`), and
clearing the denominators of the coefficients reduces the case of `E` to that of `R`
(`MvPolynomial.exists_ne_zero_eval_algebraMap_eq_zero_iff_eval_eq_zero`).

For matrices this gives the "Null zero loci" statement of Serre's density argument: if `G` is a
compact group embedded with open image in `M_n(R)`, for instance an open subgroup of `GL_n(O_E)`,
then the zero set on `G` of a nonzero polynomial over `E` in the matrix entries is null for the
normalized Haar measure of `G` (`Matrix.haarProb_setOf_eval_algebraMap_eq_zero`), so a polynomial
vanishing on a subset of `G` of positive measure is zero
(`Matrix.mvPolynomial_eq_zero_of_haarProb_ne_zero`). This combines the identification of
`haarProb G` with normalized restricted additive Haar measure
(`MeasureTheory.Measure.haarProb_eq_smul_comap`) with the nullity in `M_n(R)`.

## Main results

* `MvPolynomial.measure_setOf_eval_algebraMap_eq_zero`: the `R`-points of the zero locus of a
  nonzero polynomial over `E` are null for every σ-finite translation-invariant measure.
* `Matrix.measure_setOf_eval_algebraMap_eq_zero`: the same on `M_n(R)`.
* `Matrix.haarProb_setOf_eval_algebraMap_eq_zero`: the zero set on a compact open matrix group of
  a nonzero polynomial over `E` is Haar-null.

## References

* J.-P. Serre, *Quelques applications du théorème de densité de Chebotarev*, Publ. Math. IHÉS 54
  (1981), §6.4, proof of Proposition 13.
-/

public section

open MeasureTheory Measure Set Topology TauCeti

namespace MvPolynomial

variable {R E ι : Type*} [CommRing R] [IsDomain R] [Field E] [Algebra R E] [IsFractionRing R E]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [T1Space R] [(𝓝[≠] (0 : R)).NeBot] [MeasurableSpace R]
  [BorelSpace R] [Finite ι]

/-- **Null zero loci for invariant measures.** Let `R` be a locally compact, second countable,
`T₁` topological domain without isolated points. The zero locus in `R^ι` of a nonzero
polynomial over `R` is null for every σ-finite translation-invariant measure on `R^ι`, for
instance every additive Haar measure. -/
theorem measure_setOf_eval_eq_zero (μ : Measure (ι → R)) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (Q : MvPolynomial ι R) (hQ : Q ≠ 0) : μ {x | eval x Q = 0} = 0 := by
  have := Fintype.ofFinite ι
  exact absolutelyContinuous_isAddHaarMeasure μ (Measure.pi fun _ : ι ↦ (addHaar : Measure R))
    (measure_pi_setOfPred_eval_eq_zero _ Q hQ)

/-- **Null zero loci over the fraction field.** Let `R` be a locally compact, second countable,
`T₁` topological domain without isolated points, with fraction field `E`. The `R`-points of
the zero locus of a nonzero polynomial over `E` are null for every σ-finite translation-invariant
measure on `R^ι`. -/
theorem measure_setOf_eval_algebraMap_eq_zero (μ : Measure (ι → R)) [SigmaFinite μ]
    [μ.IsAddLeftInvariant] (P : MvPolynomial ι E) (hP : P ≠ 0) :
    μ {x | eval (algebraMap R E ∘ x) P = 0} = 0 := by
  obtain ⟨Q, hQ, hPQ⟩ := exists_ne_zero_eval_algebraMap_eq_zero_iff_eval_eq_zero R P hP
  simpa only [hPQ] using measure_setOf_eval_eq_zero μ Q hQ

end MvPolynomial

namespace Matrix

variable {R E : Type*} [CommRing R] [IsDomain R] [Field E] [Algebra R E] [IsFractionRing R E]
  [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
  [(𝓝[≠] (0 : R)).NeBot] [MeasurableSpace R] [BorelSpace R]

section Measure

variable [LocallyCompactSpace R] [T1Space R] {m n : Type*} [Finite m] [Finite n]

/-- **Null zero loci on matrices.** Let `R` be a locally compact, second countable, `T₁`
topological domain without isolated points, with fraction field `E`. The set of matrices in
`M_{m × n}(R)` at which a nonzero polynomial over `E` in the entries vanishes is null for every
σ-finite translation-invariant measure, for instance every additive Haar measure. -/
theorem measure_setOf_eval_algebraMap_eq_zero (μ : Measure (Matrix m n R)) [SigmaFinite μ]
    [μ.IsAddLeftInvariant] (P : MvPolynomial (m × n) E) (hP : P ≠ 0) :
    μ {M | MvPolynomial.eval (fun p ↦ algebraMap R E (M p.1 p.2)) P = 0} = 0 := by
  let e : Matrix m n R ≃ᵐ (m × n → R) :=
    (Matrix.ofMeasurableEquiv m n R).symm.trans (MeasurableEquiv.curry m n R).symm
  let f : Matrix m n R →ₙ+ (m × n → R) :=
    { toFun := e
      map_add' := fun M N ↦ by ext p; simp [e, Function.uncurry_def, Matrix.row_apply] }
  have : SigmaFinite (μ.map e) := e.sigmaFinite_map
  have : (μ.map e).IsAddLeftInvariant := isAddLeftInvariant_map f e.measurable e.surjective
  have hset : e ⁻¹' {x | MvPolynomial.eval (algebraMap R E ∘ x) P = 0} =
      {M | MvPolynomial.eval (fun p ↦ algebraMap R E (M p.1 p.2)) P = 0} := by
    ext M
    simp [e, Function.comp_def, Function.uncurry_def, Matrix.row_apply]
  have h := MvPolynomial.measure_setOf_eval_algebraMap_eq_zero (μ.map e) P hP
  rwa [e.map_apply, hset] at h

end Measure

section Group

variable [CompactSpace R] [T2Space R] {n : Type*} [Fintype n] [DecidableEq n] {G : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G]

/-- **Haar-null zero sets on compact open matrix groups.** Let `R` be a compact, second countable
Hausdorff topological domain without isolated points, with fraction field `E`, and let `f` embed a
compact group `G` continuously and multiplicatively into `M_n(R)` with open image, as for an open
subgroup of `GL_n(R)`. The set of `g ∈ G` at which a nonzero polynomial over `E` in the matrix
entries of `f g` vanishes is null for the normalized Haar measure of `G`. -/
theorem haarProb_setOf_eval_algebraMap_eq_zero (f : G →* Matrix n n R) (hf : Continuous f)
    (hinj : Function.Injective f) (hopen : IsOpen (range f)) (P : MvPolynomial (n × n) E)
    (hP : P ≠ 0) :
    haarProb G {g | MvPolynomial.eval (fun p ↦ algebraMap R E (f g p.1 p.2)) P = 0} = 0 := by
  let μ : Measure (Matrix n n R) := addHaar
  have hemb : MeasurableEmbedding f :=
    (IsOpenEmbedding.mk (hf.isClosedEmbedding hinj).toIsEmbedding hopen).measurableEmbedding
  rw [haarProb_eq_smul_comap μ f hf hinj hopen, smul_apply, smul_eq_mul]
  refine mul_eq_zero_of_right _ ?_
  rw [hemb.comap_apply]
  refine measure_mono_null ?_ (measure_setOf_eval_algebraMap_eq_zero μ P hP)
  exact image_subset_iff.2 fun _ hg ↦ hg

/-- **Polynomials vanishing on a set of positive Haar measure.** With `R`, `E` and the compact
open matrix group `f : G →* M_n(R)` as in `Matrix.haarProb_setOf_eval_algebraMap_eq_zero`, a
polynomial over `E` in the matrix entries that vanishes on a subset of `G` of positive Haar
measure is zero. -/
theorem mvPolynomial_eq_zero_of_haarProb_ne_zero (f : G →* Matrix n n R) (hf : Continuous f)
    (hinj : Function.Injective f) (hopen : IsOpen (range f)) {P : MvPolynomial (n × n) E}
    {S : Set G} (hS : haarProb G S ≠ 0)
    (h : ∀ g ∈ S, MvPolynomial.eval (fun p ↦ algebraMap R E (f g p.1 p.2)) P = 0) : P = 0 := by
  by_contra hP
  exact hS <| measure_mono_null (fun g hg ↦ h g hg) <|
    haarProb_setOf_eval_algebraMap_eq_zero f hf hinj hopen P hP

end Group

end Matrix
