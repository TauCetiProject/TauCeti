/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Complex

/-!
# The Haar character of units of products of rings

For a locally compact topological ring `R`, a unit `x` of `R` acts on the additive group of `R` by
left multiplication and scales every additive Haar measure by its distributive Haar character
`MeasureTheory.distribHaarChar R x`. This file computes that character in the cases needed to
assemble Haar characters of adele rings from local data.

* On a product `R × S` the character of a unit is the product of the characters of its two
  components, and on a finite product `Π i, R i` it is the product of the characters of the
  coordinates: product Haar measures are products on boxes.
* The character is transported along ring isomorphisms that are homeomorphisms.
* On a finite-dimensional real normed algebra `A`, multiplication by `x` is an `ℝ`-linear map of
  determinant `Algebra.norm ℝ x`, so the character is `|Algebra.norm ℝ x|`. In particular it is
  `|x|` on `ℝ` and `|z|²` on `ℂ`.
* For every regular Haar measure `μ`, multiplication by `x` pushes `μ` forward to
  `(distribHaarChar R x)⁻¹ • μ`.

## Main results

* `MeasureTheory.distribHaarChar_prod`, `MeasureTheory.distribHaarChar_pi`: products.
* `MeasureTheory.distribHaarChar_map_ringEquiv`: transport along a ring isomorphism.
* `MeasureTheory.distribHaarChar_eq_nnnorm_algebraNorm`, `MeasureTheory.distribHaarChar_real`,
  `MeasureTheory.distribHaarChar_complex`: real normed algebras.
* `MeasureTheory.Measure.map_smul_eq_inv_distribHaarChar_smul`: the pushforward of a Haar measure
  under multiplication.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., §3.5, pp. 186–189 (the modulus of an automorphism, and restricted Haar products).
-/

public section

open MeasureTheory Measure Set TopologicalSpace
open scoped NNReal ENNReal Pointwise

namespace MeasureTheory

section Pushforward

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A]
  [MeasurableSpace A] [BorelSpace A]

/-- **Pushforward of Haar measure under a distributive action.** The action of `g` pushes every
regular additive Haar measure `μ` forward to `(distribHaarChar A g)⁻¹ • μ`. -/
theorem Measure.map_smul_eq_inv_distribHaarChar_smul (μ : Measure A) [μ.IsAddHaarMeasure]
    [μ.Regular] (g : G) :
    μ.map (g • ·) = (distribHaarChar A g)⁻¹ • μ := by
  have hmeas : Measurable fun a : A ↦ g • a := (continuous_const_smul g).measurable
  ext s hs
  have hpre : (fun a : A ↦ g • a) ⁻¹' s = g⁻¹ • s := by
    ext a
    simp [Set.mem_smul_set_iff_inv_smul_mem]
  rw [map_apply hmeas hs, hpre, ← distribHaarChar_mul μ g⁻¹ s, map_inv, smul_apply,
    ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (distribHaarChar_pos (A := A)).ne']

end Pushforward

section Monoid

variable {R S : Type*} [Monoid R] [Monoid S]

/-- The action of a unit of `R × S` on a rectangle is the rectangle of the actions of its
components. -/
private theorem units_smul_prod (x : (R × S)ˣ) (s : Set R) (t : Set S) :
    x • (s ×ˢ t) =
      (Units.map (MonoidHom.fst R S) x • s) ×ˢ (Units.map (MonoidHom.snd R S) x • t) := by
  ext ⟨a, b⟩
  simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_prod]
  simp [Units.smul_def]

/-- The action of a unit of `Π i, T i` on a box is the box of the actions of its coordinates. -/
private theorem units_smul_pi {ι : Type*} {T : ι → Type*} [∀ i, Monoid (T i)] (x : (Π i, T i)ˣ)
    (s : ∀ i, Set (T i)) :
    x • univ.pi s = univ.pi fun i ↦ Units.map (Pi.evalMonoidHom T i) x • s i := by
  ext a
  simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_univ_pi]
  simp [Units.smul_def]

end Monoid

section Ring

variable {R S : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [Ring S] [TopologicalSpace S] [IsTopologicalRing S] [LocallyCompactSpace S]

/-- A positive compact set has finite positive mass for every additive Haar measure. -/
private theorem measure_positiveCompacts_ne_zero_ne_top {X : Type*} [AddGroup X]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    (K : PositiveCompacts X) :
    μ K ≠ 0 ∧ μ K ≠ ∞ :=
  ⟨(measure_pos_of_nonempty_interior μ K.interior_nonempty).ne', K.isCompact.measure_ne_top⟩

/-- **The Haar character of a product.** A unit of `R × S` scales Haar measure on `R × S` by the
product of the characters of its components. -/
theorem distribHaarChar_prod [SecondCountableTopology R] [SecondCountableTopology S]
    (x : (R × S)ˣ) :
    distribHaarChar (R × S) x =
      distribHaarChar R (Units.map (MonoidHom.fst R S) x) *
        distribHaarChar S (Units.map (MonoidHom.snd R S) x) := by
  borelize R S
  let μ : Measure R := addHaar
  let ν : Measure S := addHaar
  obtain ⟨hK0, hKtop⟩ := measure_positiveCompacts_ne_zero_ne_top μ (Classical.arbitrary _)
  obtain ⟨hL0, hLtop⟩ := measure_positiveCompacts_ne_zero_ne_top ν (Classical.arbitrary _)
  set K : Set R := ((Classical.arbitrary (PositiveCompacts R) : PositiveCompacts R) : Set R)
  set L : Set S := ((Classical.arbitrary (PositiveCompacts S) : PositiveCompacts S) : Set S)
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.prod ν) (s := K ×ˢ L) ?_ ?_ ?_
  · rw [prod_prod]
    exact mul_ne_zero hK0 hL0
  · rw [prod_prod]
    exact ENNReal.mul_ne_top hKtop hLtop
  · rw [units_smul_prod, prod_prod, prod_prod, ← distribHaarChar_mul, ← distribHaarChar_mul,
      ENNReal.coe_mul]
    ring

variable {ι : Type*} [Fintype ι] {T : ι → Type*} [∀ i, Ring (T i)] [∀ i, TopologicalSpace (T i)]
  [∀ i, IsTopologicalRing (T i)] [∀ i, LocallyCompactSpace (T i)]

/-- **The Haar character of a finite product.** A unit of `Π i, T i` scales Haar measure on
`Π i, T i` by the product of the characters of its coordinates. -/
theorem distribHaarChar_pi [∀ i, SecondCountableTopology (T i)] (x : (Π i, T i)ˣ) :
    distribHaarChar (Π i, T i) x =
      ∏ i, distribHaarChar (T i) (Units.map (Pi.evalMonoidHom T i) x) := by
  let _ (i : ι) : MeasurableSpace (T i) := borel (T i)
  have _ (i : ι) : BorelSpace (T i) := ⟨rfl⟩
  let μ (i : ι) : Measure (T i) := addHaar
  let K (i : ι) : PositiveCompacts (T i) := Classical.arbitrary _
  have hK (i : ι) := measure_positiveCompacts_ne_zero_ne_top (μ i) (K i)
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ)
    (s := univ.pi fun i ↦ (K i : Set (T i))) ?_ ?_ ?_
  · rw [pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hK i).1
  · rw [pi_pi]
    exact ENNReal.prod_ne_top fun i _ ↦ (hK i).2
  · rw [units_smul_pi, pi_pi, pi_pi, ENNReal.ofNNReal_finsetProd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ (distribHaarChar_mul (μ i) _ _).symm

/-- **Transport of the Haar character.** A ring isomorphism `e : R ≃+* S` which is a
homeomorphism preserves Haar characters. -/
theorem distribHaarChar_map_ringEquiv (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) (x : Rˣ) :
    distribHaarChar S (Units.map e.toMonoidHom x) = distribHaarChar R x := by
  borelize R S
  let f : R ≃ₜ+ S := { e.toAddEquiv with continuous_toFun := he, continuous_invFun := he' }
  let μ : Measure R := addHaar
  have _ : (μ.map f).IsAddHaarMeasure := f.isAddHaarMeasure_map μ
  have _ : (μ.map f).Regular := Regular.map f.toHomeomorph
  have hf : MeasurableEmbedding f := f.toHomeomorph.measurableEmbedding
  let K : PositiveCompacts R := Classical.arbitrary _
  obtain ⟨hK0, hKtop⟩ := measure_positiveCompacts_ne_zero_ne_top μ K
  have himage (t : Set R) : μ.map f (f '' t) = μ t := by
    rw [hf.map_apply, Set.preimage_image_eq _ f.injective]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.map f) (s := f '' K)
    (by rwa [himage]) (by rwa [himage]) ?_
  have hsmul : Units.map e.toMonoidHom x • f '' K = f '' (x • (K : Set R)) := by
    ext b
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨x • a, ⟨a, ha, rfl⟩, by simp [f, Units.smul_def]⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨f a, ⟨a, ha, rfl⟩, by simp [f, Units.smul_def]⟩
  rw [hsmul, himage, himage, distribHaarChar_mul]

end Ring

section RealAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

/-- **The Haar character of a finite-dimensional real algebra.** Multiplication by a unit `x` is
an `ℝ`-linear map of determinant `Algebra.norm ℝ x`, so it scales Haar measure by
`|Algebra.norm ℝ x|`. -/
theorem distribHaarChar_eq_nnnorm_algebraNorm (x : Aˣ) :
    distribHaarChar A x = ‖Algebra.norm ℝ (x : A)‖₊ := by
  borelize A
  let μ : Measure A := addHaar
  let K : PositiveCompacts A := Classical.arbitrary _
  obtain ⟨hK0, hKtop⟩ := measure_positiveCompacts_ne_zero_ne_top μ K
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := K) hK0 hKtop ?_
  have hsmul : x • (K : Set A) = Algebra.lmul ℝ A (x : A) '' K := by
    ext b
    simp [Set.mem_smul_set, Units.smul_def]
  rw [hsmul, addHaar_image_linearMap, ← Algebra.norm_apply, ← Real.eNorm_eq_ofReal_abs,
    eNorm_eq_nnNorm]

/-- The Haar character of `ℝ` is the absolute value. -/
theorem distribHaarChar_real (x : ℝˣ) : distribHaarChar ℝ x = ‖(x : ℝ)‖₊ := by
  rw [distribHaarChar_eq_nnnorm_algebraNorm, Algebra.norm_self, MonoidHom.id_apply]

/-- The Haar character of `ℂ` is the square of the absolute value. -/
theorem distribHaarChar_complex (z : ℂˣ) : distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 := by
  rw [distribHaarChar_eq_nnnorm_algebraNorm, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]
  ext
  simp

end RealAlgebra

end MeasureTheory
