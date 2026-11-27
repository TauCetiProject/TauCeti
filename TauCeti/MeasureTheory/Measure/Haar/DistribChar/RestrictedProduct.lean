/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Matrix
public import TauCeti.Topology.Instances.Matrix
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Topology.Algebra.RestrictedProduct.SecondCountable

/-!
# The Haar character of the general linear group over a restricted product

Let `𝔸 = Πʳ v, [R v, O v]` be the restricted product of a countable family of commutative locally
compact second countable topological rings `R v` with respect to compact open subrings `O v`, for
instance the finite adele ring of a Dedekind domain. The group `GL ι 𝔸` acts on the column vectors
`ι → 𝔸`, and this file computes its distributive Haar character factorwise:

`distribHaarChar (ι → 𝔸) g = ∏ᶠ v, distribHaarChar (ι → R v) g_v`,

where `g_v` is the image of `g` in `GL ι (R v)` under the evaluation `𝔸 →+* R v`. The product is
finitary because `g_v` has entries, and inverse entries, in `O v` at all but finitely many `v`,
and then it preserves `O vᶥ` (`Matrix.GeneralLinearGroup.eventually_map_evalRingHom_smul_univ_pi`).

The proof identifies `ι → 𝔸` with the restricted product `Πʳ v, [ι → R v, O vᶥ]`
(`TauCeti.addPiRestrictedProductContinuousAddEquiv`), on which the restricted product of the local
Haar measures giving `O vᶥ` mass one is a Haar measure (`TauCeti.restrictedAddHaar`). Under this
identification the translate of the integral vectors `Ôᶥ` by `g` is the coordinate box with factors
`g_v • O vᶥ`, whose measure is the finitary product of the local Haar characters.

## Main results

* `MeasureTheory.distribHaarChar_pi_restrictedProduct`: the Haar character of `GL ι 𝔸` on
  `ι → 𝔸` is the finitary product of the Haar characters of its factors.

## References

* A. Weil, *Basic Number Theory*, Chapter I, §2 (the module of an automorphism) and Chapter IV, §1
  (restricted products of locally compact groups and their Haar measures).
-/

public section
noncomputable section

open Filter Matrix Set RestrictedProduct TauCeti
open scoped NNReal ENNReal Pointwise RestrictedProduct

variable {P ι : Type*} {R : P → Type*} {S : P → Type*} [∀ v, CommRing (R v)]
  [∀ v, SetLike (S v) (R v)] [∀ v, SubringClass (S v) (R v)] {O : ∀ v, S v}
  [Fintype ι] [DecidableEq ι]

namespace MeasureTheory

variable [Countable P] [∀ v, TopologicalSpace (R v)] [∀ v, IsTopologicalRing (R v)]
  [∀ v, LocallyCompactSpace (R v)] [∀ v, SecondCountableTopology (R v)]
  [hO : Fact (∀ v, IsOpen (O v : Set (R v)))] [∀ v, CompactSpace (O v)]

/-- **The Haar character of `GL_n` over a restricted product.** Over the restricted product
`𝔸 = Πʳ v, [R v, O v]` of a countable family of commutative locally compact second countable
rings with respect to compact open subrings, an invertible matrix `g` scales additive Haar measure
on `ι → 𝔸` by the finitary product over `v` of the factors by which its images
`g_v ∈ GL ι (R v)` scale additive Haar measure on `ι → R v`. -/
theorem distribHaarChar_pi_restrictedProduct (g : GL ι (Πʳ v, [R v, O v])) :
    distribHaarChar (ι → Πʳ v, [R v, O v]) g =
      ∏ᶠ v, distribHaarChar (ι → R v) (GeneralLinearGroup.map (evalRingHom R v) g) := by
  let _ (v : P) : MeasurableSpace (R v) := borel _
  have _ (v : P) : BorelSpace (R v) := ⟨rfl⟩
  have hOc (v : P) : IsCompact (O v : Set (R v)) := isCompact_iff_compactSpace.2 inferInstance
  have _ : SecondCountableTopology (Πʳ v, [R v, O v]) :=
    secondCountableTopology_of_cofinite (.of_forall hO.out)
  -- The local Haar measures giving the integral vectors `O vᶥ` mass one.
  let B (v : P) : AddSubgroup (ι → R v) := AddSubgroup.pi univ fun _ ↦ AddSubgroup.ofClass (O v)
  have hB (v : P) : (B v : Set (ι → R v)) = univ.pi fun _ ↦ (O v : Set (R v)) := by
    simp only [B, AddSubgroup.coe_pi, AddSubgroup.coe_ofClass]
  have hBopen (v : P) : IsOpen (B v : Set (ι → R v)) :=
    hB v ▸ isOpen_set_pi finite_univ fun _ _ ↦ hO.out v
  have _ : Fact (∀ v, IsOpen (B v : Set (ι → R v))) := ⟨hBopen⟩
  let L (v : P) : TopologicalSpace.PositiveCompacts (ι → R v) :=
    ⟨⟨B v, hB v ▸ isCompact_univ_pi fun _ ↦ hOc v⟩,
      ⟨0, by rw [(hBopen v).interior_eq]; exact zero_mem (B v)⟩⟩
  let ν (v : P) : Measure (ι → R v) := Measure.addHaarMeasure (L v)
  have hν (v : P) : ν v (B v) = 1 := Measure.addHaarMeasure_self
  -- Transport their restricted product to `ι → 𝔸` along the swap of coordinates.
  let Φ := addPiRestrictedProductContinuousAddEquiv (n := ι) O hO.out
  let e := Φ.symm.toHomeomorph.toMeasurableEquiv
  let μ : Measure (ι → Πʳ v, [R v, O v]) := (restrictedAddHaar B ν (.of_forall hν)).map e
  have _ : μ.IsAddHaarMeasure := Φ.symm.isAddHaarMeasure_map _
  -- The translate of the integral vectors by `h` is the box with factors `h_v • O vᶥ`, whose
  -- measure is the finitary product of the local Haar characters.
  let s : Set (ι → Πʳ v, [R v, O v]) := univ.pi fun _ ↦ box fun v ↦ (O v : Set (R v))
  -- `e` is `Φ.symm` viewed as a measurable equivalence, so the two have the same coercion.
  have he : ⇑e = (addPiRestrictedProduct O).symm :=
    coe_addPiRestrictedProductContinuousAddEquiv_symm O hO.out
  have hloc (h : GL ι (Πʳ v, [R v, O v])) (v : P) :
      ν v (GeneralLinearGroup.map (evalRingHom R v) h • univ.pi fun _ ↦ (O v : Set (R v))) =
        distribHaarChar (ι → R v) (GeneralLinearGroup.map (evalRingHom R v) h) := by
    rw [← hB, ← distribHaarChar_mul, hν, mul_one]
  have hmeas (h : GL ι (Πʳ v, [R v, O v])) :
      μ (h • s) = (∏ᶠ v, distribHaarChar (ι → R v) (GeneralLinearGroup.map (evalRingHom R v) h)
        : ℝ≥0) := by
    rw [MeasurableEquiv.map_apply, he, h.preimage_addPiRestrictedProduct_symm_smul,
      restrictedAddHaar_box_eq_finprod _ _ _
        (h.eventually_map_evalRingHom_smul_univ_pi.mono fun v hv ↦ by rw [hB, hv]),
      finprod_congr (hloc h)]
    exact (ENNReal.ofNNRealHom.map_finprod_of_injective ENNReal.coe_injective _).symm
  have hs : μ s = 1 := by
    simpa using hmeas 1
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := s) (by simp [hs])
    (by simp [hs]) ?_
  rw [hmeas, hs, mul_one]

end MeasureTheory
