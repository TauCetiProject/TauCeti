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

/-!
# The Haar character of the general linear group over a restricted product

Let `𝔸 = Πʳ v, [R v, O v]` be the restricted product of a countable family of commutative locally
compact second countable topological rings `R v` with respect to compact open subrings `O v`, for
instance the finite adele ring of the ring of integers of a number field. The group `GL ι 𝔸` acts
on the column vectors `ι → 𝔸`, and this file computes its distributive Haar character factorwise:

`distribHaarChar (ι → 𝔸) g = ∏ᶠ v, distribHaarChar (ι → R v) g_v`,

where `g_v` is the image of `g` in `GL ι (R v)` under the evaluation `𝔸 →+* R v`. The product is
finitary because `g_v` has entries, and inverse entries, in `O v` at all but finitely many `v`,
and then it preserves `O vᶥ`
(`Matrix.GeneralLinearGroup.eventually_map_evalRingHom_smul_univ_pi_eq_self`).

The proof identifies `ι → 𝔸` with the restricted product `Πʳ v, [ι → R v, O vᶥ]`
(`TauCeti.addPiRestrictedProductContinuousAddEquiv`), on which the restricted product of the local
Haar measures giving `O vᶥ` mass one is a Haar measure (`TauCeti.restrictedAddHaar`). Under this
identification the translate of the integral vectors `Ôᶥ` by `g` is the coordinate box with factors
`g_v • O vᶥ`, whose measure is the finitary product of the local Haar characters.

## Main results

* `ContinuousAddEquiv.distribHaarChar_eq_finprod_of_restrictedProduct`: the common factorwise
  formula for coordinatewise actions, including scalar and matrix multiplication.
* `Matrix.GeneralLinearGroup.hasFiniteMulSupport_distribHaarChar_pi_restrictedProduct`: the local
  factors have finite multiplicative support, allowing the finitary product to be split or
  evaluated as a finite product.
* `Matrix.GeneralLinearGroup.distribHaarChar_pi_restrictedProduct_eq_finprod`: the Haar character
  of `GL ι 𝔸` on `ι → 𝔸` is the finitary product of the Haar characters of its factors.

## References

* A. Weil, *Basic Number Theory*, Chapter I, §2 (the module of an automorphism) and Chapter IV, §1
  (restricted products of locally compact groups and their Haar measures).
-/

public section
noncomputable section

open Filter Matrix Set RestrictedProduct TauCeti
open scoped NNReal ENNReal Pointwise RestrictedProduct

namespace MeasureTheory

section Factorwise

variable {P A Γ : Type*} {H Λ : P → Type*} [Countable P]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [Group Γ] [DistribMulAction Γ A] [ContinuousConstSMul Γ A]
  [∀ v, AddCommGroup (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalAddGroup (H v)] [∀ v, LocallyCompactSpace (H v)]
  [∀ v, SecondCountableTopology (H v)] [∀ v, Group (Λ v)]
  [∀ v, DistribMulAction (Λ v) (H v)] [∀ v, ContinuousConstSMul (Λ v) (H v)]

omit [Countable P] [∀ v, SecondCountableTopology (H v)] in
/-- Local image-set Haar scaling factors have finite multiplicative support when the actions
preserve compact open reference subgroups at all but finitely many places. -/
theorem hasFiniteMulSupport_distribHaarChar (B : ∀ v, AddSubgroup (H v))
    (hBo : ∀ v, IsOpen (B v : Set (H v))) (hBc : ∀ v, IsCompact (B v : Set (H v)))
    (a : ∀ v, Λ v) (ha : ∀ᶠ v in cofinite, a v • (B v : Set (H v)) = B v) :
    Function.HasFiniteMulSupport fun v ↦ distribHaarChar (H v) (a v) := by
  refine hasFiniteMulSupport_iff_eventually_eq_one.mpr (ha.mono fun v hv ↦ ?_)
  let _ : MeasurableSpace (H v) := borel _
  have _ : BorelSpace (H v) := ⟨rfl⟩
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.addHaar)
    ((hBo v).measure_pos _ ⟨0, (B v).zero_mem⟩).ne' (hBc v).measure_ne_top
  simp only [hv, ENNReal.coe_one, one_mul]

end Factorwise

end MeasureTheory

namespace ContinuousAddEquiv

open MeasureTheory

variable {P A Γ : Type*} {H Λ : P → Type*} [Countable P]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [Group Γ] [DistribMulAction Γ A] [ContinuousConstSMul Γ A]
  [∀ v, AddCommGroup (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalAddGroup (H v)] [∀ v, LocallyCompactSpace (H v)]
  [∀ v, SecondCountableTopology (H v)] [∀ v, Group (Λ v)]
  [∀ v, DistribMulAction (Λ v) (H v)] [∀ v, ContinuousConstSMul (Λ v) (H v)]
  {B : ∀ v, AddSubgroup (H v)} [hBo : Fact (∀ v, IsOpen (B v : Set (H v)))]

/-- An action identified with coordinatewise actions on a restricted product has Haar character
equal to the finitary product of the local image-set scaling factors, provided those actions
preserve the compact open reference subgroups at almost every place. -/
theorem distribHaarChar_eq_finprod_of_restrictedProduct
    (Φ : A ≃ₜ+ Πʳ v, [H v, B v]) (hBc : ∀ v, IsCompact (B v : Set (H v)))
    (g : Γ) (a : ∀ v, Λ v) (ha : ∀ᶠ v in cofinite, a v • (B v : Set (H v)) = B v)
    (hΦ : ∀ x v, Φ (g • x) v = a v • Φ x v) :
    distribHaarChar A g = ∏ᶠ v, distribHaarChar (H v) (a v) := by
  have _ : SecondCountableTopology (Πʳ v, [H v, B v]) :=
    secondCountableTopology_of_cofinite (.of_forall hBo.out)
  have _ : SecondCountableTopology A := Φ.toHomeomorph.secondCountableTopology
  let _ : MeasurableSpace A := borel _
  have _ : BorelSpace A := ⟨rfl⟩
  let _ (v : P) : MeasurableSpace (H v) := borel _
  have _ (v : P) : BorelSpace (H v) := ⟨rfl⟩
  let L (v : P) : TopologicalSpace.PositiveCompacts (H v) :=
    ⟨⟨B v, hBc v⟩, ⟨0, by rw [(hBo.out v).interior_eq]; exact (B v).zero_mem⟩⟩
  let ν (v : P) := Measure.addHaarMeasure (L v)
  have hν (v : P) : ν v (B v) = 1 := Measure.addHaarMeasure_self
  let e := Φ.symm.toHomeomorph.toMeasurableEquiv
  let μ : Measure A := (restrictedAddHaar B ν (.of_forall hν)).map e
  have he : ⇑e = Φ.symm := Homeomorph.toMeasurableEquiv_coe _
  have _ : μ.IsAddHaarMeasure := by
    simpa only [μ, he] using Φ.symm.isAddHaarMeasure_map
      (restrictedAddHaar B ν (.of_forall hν))
  let s : Set A := Φ ⁻¹' box fun v ↦ (B v : Set (H v))
  have hs : e ⁻¹' s = box fun v ↦ (B v : Set (H v)) := by
    ext x
    simp [s, he]
  have hgs : e ⁻¹' (g • s) = box fun v ↦ a v • (B v : Set (H v)) := by
    ext y
    rw [mem_preimage, he, mem_smul_set_iff_inv_smul_mem]
    simp only [s, mem_preimage, mem_box]
    apply forall_congr'
    intro v
    have heq : a v • Φ (g⁻¹ • Φ.symm y) v = y v := by
      rw [← hΦ, smul_inv_smul, Φ.apply_symm_apply]
    rw [← heq, Set.smul_mem_smul_set_iff]
  have hloc (v : P) : ν v (a v • (B v : Set (H v))) =
      (distribHaarChar (H v) (a v) : ℝ≥0∞) := by
    rw [← distribHaarChar_mul, hν, mul_one]
  have hsμ : μ s = 1 := by
    simp [μ, MeasurableEquiv.map_apply, hs, hν]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := s)
    (by simp [hsμ]) (by simp [hsμ]) ?_
  rw [hsμ, mul_one, MeasurableEquiv.map_apply, hgs,
    restrictedAddHaar_box_eq_finprod _ _ _ ha, finprod_congr hloc]
  exact (ENNReal.ofNNRealHom.map_finprod_of_injective ENNReal.coe_injective _).symm

end ContinuousAddEquiv

variable {P ι : Type*} {R : P → Type*} {S : P → Type*} [∀ v, CommRing (R v)]
  [∀ v, SetLike (S v) (R v)] [∀ v, SubringClass (S v) (R v)] {O : ∀ v, S v}
  [Fintype ι] [DecidableEq ι]

namespace Matrix.GeneralLinearGroup

open MeasureTheory

variable [Countable P] [∀ v, TopologicalSpace (R v)] [∀ v, IsTopologicalRing (R v)]
  [∀ v, LocallyCompactSpace (R v)] [∀ v, SecondCountableTopology (R v)]
  [hO : Fact (∀ v, IsOpen (O v : Set (R v)))] [∀ v, CompactSpace (O v)]

omit [Countable P] [∀ v, SecondCountableTopology (R v)] in
/-- The local Haar characters of a matrix over a restricted product have finite multiplicative
support: almost every factor preserves the compact open integral vectors. -/
theorem hasFiniteMulSupport_distribHaarChar_pi_restrictedProduct
    (g : GL ι (Πʳ v, [R v, O v])) :
    Function.HasFiniteMulSupport fun v ↦
      distribHaarChar (ι → R v) (GeneralLinearGroup.map (evalRingHom R v) g) := by
  apply hasFiniteMulSupport_distribHaarChar
    (fun v ↦ AddSubgroup.pi univ fun _ : ι ↦ AddSubgroup.ofClass (O v))
    (fun v ↦ isOpen_set_pi finite_univ fun _ _ ↦ hO.out v)
    (fun v ↦ isCompact_univ_pi fun _ ↦
      isCompact_iff_compactSpace.2 (inferInstance : CompactSpace (O v)))
  exact g.eventually_map_evalRingHom_smul_univ_pi_eq_self

/-- **The Haar character of `GL_n` over a restricted product.** For compact open reference
subrings, the image-set scaling factor on column vectors equals the finitary product of the
local image-set scaling factors. -/
theorem distribHaarChar_pi_restrictedProduct_eq_finprod (g : GL ι (Πʳ v, [R v, O v])) :
    distribHaarChar (ι → Πʳ v, [R v, O v]) g =
      ∏ᶠ v, distribHaarChar (ι → R v) (GeneralLinearGroup.map (evalRingHom R v) g) := by
  have _ : SecondCountableTopology (Πʳ v, [R v, O v]) :=
    secondCountableTopology_of_cofinite (.of_forall hO.out)
  let B (v : P) : AddSubgroup (ι → R v) := AddSubgroup.pi univ fun _ ↦ AddSubgroup.ofClass (O v)
  have _ : Fact (∀ v, IsOpen (B v : Set (ι → R v))) :=
    ⟨fun v ↦ isOpen_set_pi finite_univ fun _ _ ↦ hO.out v⟩
  let Φ : (ι → Πʳ v, [R v, O v]) ≃ₜ+ Πʳ v, [ι → R v, B v] :=
    addPiRestrictedProductContinuousAddEquiv (n := ι) (fun _ ↦ O) (fun _ ↦ hO.out)
  have hBc (v : P) : IsCompact (B v : Set (ι → R v)) :=
    isCompact_univ_pi fun _ ↦
      isCompact_iff_compactSpace.2 (inferInstance : CompactSpace (O v))
  let a (v : P) : GL ι (R v) := GeneralLinearGroup.map (evalRingHom R v) g
  have ha : ∀ᶠ v in cofinite, a v • (B v : Set (ι → R v)) = B v :=
    g.eventually_map_evalRingHom_smul_univ_pi_eq_self
  have hcoord (x : ι → Πʳ v, [R v, O v]) (v : P) : Φ x v = fun j ↦ x j v := by
    ext j
    simp only [Φ, coe_addPiRestrictedProductContinuousAddEquiv, addPiRestrictedProduct_apply]
  have hΦ (x : ι → Πʳ v, [R v, O v]) (v : P) : Φ (g • x) v = a v • Φ x v := by
    simpa only [hcoord] using funext fun j ↦ g.smul_apply_apply_restrictedProduct x j v
  exact Φ.distribHaarChar_eq_finprod_of_restrictedProduct hBc g a ha hΦ

end Matrix.GeneralLinearGroup
