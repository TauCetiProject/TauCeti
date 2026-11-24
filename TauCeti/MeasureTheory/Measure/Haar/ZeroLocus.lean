/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.MeasureTheory.Measure.Haar.CompactRing
public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus

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
(`MvPolynomial.exists_ne_zero_forall_eval_algebraMap_eq_zero_iff`).

For matrices this gives the "Null zero loci" statement of Serre's density argument: if `G` is a
compact group embedded with open image in `M_n(R)`, for instance an open subgroup of `GL_n(O_E)`,
then the zero set on `G` of a nonzero polynomial over `E` in the matrix entries is null for the
normalized Haar measure of `G` (`Matrix.haarProb_setOf_eval_algebraMap_eq_zero`), so a polynomial
vanishing on a subset of `G` of positive measure is zero
(`Matrix.eq_zero_of_forall_eval_algebraMap_eq_zero`). This combines the identification of
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

/-- **Clearing denominators.** A nonzero polynomial over the fraction field `E` of a domain `R`
has a nonzero multiple over `R` with the same zero locus on `R`-points. -/
theorem exists_ne_zero_forall_eval_algebraMap_eq_zero_iff (P : MvPolynomial ι E) (hP : P ≠ 0) :
    ∃ Q : MvPolynomial ι R, Q ≠ 0 ∧
      ∀ x : ι → R, eval (algebraMap R E ∘ x) P = 0 ↔ eval x Q = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) P.coeffs
  have hb0 : algebraMap R E b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.prop
  obtain ⟨Q, hQ⟩ : C (algebraMap R E b) * P ∈ range (map (algebraMap R E)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.1 hc
    rw [mem_support_iff, coeff_C_mul] at hm
    rw [coeff_C_mul]
    obtain ⟨a, ha⟩ := hb _ (coeff_mem_coeffs m (right_ne_zero_of_mul hm))
    exact ⟨a, by rw [ha, Algebra.smul_def]⟩
  refine ⟨Q, fun h ↦ ?_, fun x ↦ ?_⟩
  · rw [h, map_zero, eq_comm, mul_eq_zero, C_eq_zero] at hQ
    exact hQ.elim hb0 hP
  · have := congrArg (eval (algebraMap R E ∘ x)) hQ
    have h2 : eval₂ (algebraMap R E) (algebraMap R E ∘ x) Q = algebraMap R E (eval x Q) := by
      rw [eval, coe_eval₂Hom, eval₂_comp_left, RingHom.comp_id]
    rw [eval_map, h2, eval_mul, eval_C] at this
    rw [← mul_eq_zero_iff_left hb0, ← this, FaithfulSMul.algebraMap_eq_zero_iff]

variable [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
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
  obtain ⟨Q, hQ, hPQ⟩ := exists_ne_zero_forall_eval_algebraMap_eq_zero_iff (R := R) P hP
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
    { toFun := fun M p ↦ M p.1 p.2
      map_add' := fun _ _ ↦ rfl }
  have hfe : ⇑f = ⇑e := rfl
  have : SigmaFinite (μ.map e) := e.sigmaFinite_map
  have : (μ.map e).IsAddLeftInvariant := by
    rw [← hfe]
    exact isAddLeftInvariant_map f (hfe ▸ e.measurable) (hfe ▸ e.surjective)
  have h := MvPolynomial.measure_setOf_eval_algebraMap_eq_zero (μ.map e) P hP
  rwa [e.map_apply] at h

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
  have : CompactSpace (Matrix n n R) := inferInstanceAs (CompactSpace (n → n → R))
  let μ : Measure (Matrix n n R) := addHaar
  have hemb : MeasurableEmbedding f :=
    (IsOpenEmbedding.mk (hf.isClosedEmbedding hinj).toIsEmbedding hopen).measurableEmbedding
  rw [haarProb_eq_smul_comap μ f hf hinj hopen, smul_apply, smul_eq_mul]
  refine mul_eq_zero_of_right _ ?_
  change μ.comap f (f ⁻¹' {M | MvPolynomial.eval (fun p ↦ algebraMap R E (M p.1 p.2)) P = 0}) = 0
  rw [hemb.comap_preimage]
  exact measure_mono_null inter_subset_left (measure_setOf_eval_algebraMap_eq_zero μ P hP)

/-- **Polynomials vanishing on a set of positive Haar measure.** With `R`, `E` and the compact
open matrix group `f : G →* M_n(R)` as in `Matrix.haarProb_setOf_eval_algebraMap_eq_zero`, a
polynomial over `E` in the matrix entries that vanishes on a subset of `G` of positive Haar
measure is zero. -/
theorem eq_zero_of_forall_eval_algebraMap_eq_zero (f : G →* Matrix n n R) (hf : Continuous f)
    (hinj : Function.Injective f) (hopen : IsOpen (range f)) {P : MvPolynomial (n × n) E}
    {S : Set G} (hS : haarProb G S ≠ 0)
    (h : ∀ g ∈ S, MvPolynomial.eval (fun p ↦ algebraMap R E (f g p.1 p.2)) P = 0) : P = 0 := by
  by_contra hP
  exact hS <| measure_mono_null (fun g hg ↦ h g hg) <|
    haarProb_setOf_eval_algebraMap_eq_zero f hf hinj hopen P hP

end Group

end Matrix
