/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledHull
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units

/-!
# Spectral pole pushing for rational simple fractions

Let `K ⊆ ℂ` be a compact set, `A ⊆ ℂ` a prescribed set of poles, and `a ∉ K`. If `A` meets the
connected component of `a` in `Kᶜ` whenever `a ∈ filledHull K`, then `(z - a)⁻¹` is uniformly
approximable on `K` by rational functions `p / q` whose finite poles lie in `A \ K`.

The proof applies Mathlib's spectral pole-pushing theorem
(`Subalgebra.spectrum_eq_union_sUnion_connectedComponentIn` and
`Subalgebra.isBounded_connectedComponentIn_spectrum_compl`) to the uniform closure in `C(K, ℂ)` of
the algebra of rational functions with poles in `A \ K`.

## Main results

* `IsCompact.exists_rational_norm_inv_sub_lt`: uniform rational approximation of a simple fraction
  `(z - a)⁻¹` on `K` with poles in `A \ K`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.7, p. 29.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.6.
-/

public section

open Metric Polynomial Set

namespace TauCeti

/-- The complex subalgebra of `C(K, ℂ)` consisting of functions represented on `K` by a rational
function `p / q` with `q ≠ 0` and all roots of `q` in `A \ K`. -/
private noncomputable def rationalSubalgebra (K A : Set ℂ) : Subalgebra ℂ C(K, ℂ) where
  carrier := {g : C(K, ℂ) | ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
    ∀ z : K, g z = p.eval (z : ℂ) / q.eval (z : ℂ)}
  mul_mem' := by
    rintro _ _ ⟨p₁, q₁, hq₁, hA₁, hg₁⟩ ⟨p₂, q₂, hq₂, hA₂, hg₂⟩
    refine ⟨p₁ * p₂, q₁ * q₂, mul_ne_zero hq₁ hq₂, fun z hz ↦ ?_, fun z ↦ ?_⟩
    · rcases (by simpa [eval_mul] using hz : q₁.eval z = 0 ∨ q₂.eval z = 0) with h | h
      · exact hA₁ z h
      · exact hA₂ z h
    · simp [hg₁ z, hg₂ z, div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨p₁, q₁, hq₁, hA₁, hg₁⟩ ⟨p₂, q₂, hq₂, hA₂, hg₂⟩
    refine ⟨p₁ * q₂ + p₂ * q₁, q₁ * q₂, mul_ne_zero hq₁ hq₂, fun z hz ↦ ?_, fun z ↦ ?_⟩
    · rcases (by simpa [eval_mul] using hz : q₁.eval z = 0 ∨ q₂.eval z = 0) with h | h
      · exact hA₁ z h
      · exact hA₂ z h
    · have h1 : q₁.eval (z : ℂ) ≠ 0 := fun h ↦ (hA₁ z h).2 z.property
      have h2 : q₂.eval (z : ℂ) ≠ 0 := fun h ↦ (hA₂ z h).2 z.property
      simp only [ContinuousMap.add_apply, hg₁ z, hg₂ z, eval_add, eval_mul]
      rw [div_add_div _ _ h1 h2, mul_comm (q₁.eval (z : ℂ)) (p₂.eval (z : ℂ))]
  algebraMap_mem' c := ⟨C c, 1, one_ne_zero, fun _ h ↦ by simp at h, fun _ ↦ by simp⟩

/-- The coordinate map `z ↦ z` belongs to `rationalSubalgebra K A`. -/
private theorem mem_rationalSubalgebra_coord (K A : Set ℂ) :
    (⟨Subtype.val, continuous_subtypeVal⟩ : C(K, ℂ)) ∈ rationalSubalgebra K A :=
  ⟨X, 1, one_ne_zero, fun _ h ↦ by simp at h, fun _ ↦ by simp⟩

/-- For any `b ∈ A \ K`, the simple fraction `z ↦ (b - z)⁻¹` belongs to `rationalSubalgebra K A`. -/
private theorem mem_rationalSubalgebra_inv_sub {K A : Set ℂ} {b : ℂ} (hb : b ∈ A \ K) :
    ∃ y ∈ rationalSubalgebra K A, ∀ z : K, y z = (b - (z : ℂ))⁻¹ := by
  have hcont : Continuous (fun z : K ↦ (b - (z : ℂ))⁻¹) :=
    (continuous_const.sub continuous_subtypeVal).inv₀ fun z h ↦
      hb.2 (sub_eq_zero.mp (by simpa using h) ▸ z.property)
  refine ⟨⟨_, hcont⟩, ⟨1, C b - X, ?_, ?_, fun z ↦ by simp⟩, fun _ ↦ rfl⟩
  · intro h
    have := congrArg (eval (b + 1)) h
    simp at this
  · intro z hz
    have hbz : b = z := sub_eq_zero.mp (by simpa using hz)
    exact hbz ▸ hb

/-- **Simple-fraction rational Runge approximation.** If `K ⊆ ℂ` is compact, `a ∉ K`, and `A ⊆ ℂ`
meets `connectedComponentIn Kᶜ a` whenever `a ∈ filledHull K`, then `(z - a)⁻¹` is uniformly
approximable on `K` by rational functions whose finite poles lie in `A \ K`. -/
theorem _root_.IsCompact.exists_rational_norm_inv_sub_lt {K A : Set ℂ} (hK : IsCompact K)
    {a : ℂ} (ha : a ∉ K) (hA : a ∈ filledHull K → (A ∩ connectedComponentIn Kᶜ a).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
      ∀ z ∈ K, ‖(z - a)⁻¹ - p.eval z / q.eval z‖ < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R := rationalSubalgebra K A
  let S := R.topologicalClosure
  let : IsClosed (S : Set C(K, ℂ)) := R.isClosed_topologicalClosure
  let evalAt (z : K) : S →ₐ[ℂ] ℂ := (ContinuousMap.evalAlgHom ℂ ℂ z).comp S.val
  have hevalAt (z : K) (u : S) : evalAt z u = (u : C(K, ℂ)) z := by
    simp only [evalAt, AlgHom.comp_apply, Subalgebra.val_apply, ContinuousMap.evalAlgHom_apply]
  have heval_mk (z : K) (u : C(K, ℂ)) (hu : u ∈ S) : evalAt z ⟨u, hu⟩ = u z :=
    hevalAt z ⟨u, hu⟩
  let x₀ : C(K, ℂ) := ⟨Subtype.val, continuous_subtypeVal⟩
  let x : S := ⟨x₀, R.le_topologicalClosure (mem_rationalSubalgebra_coord K A)⟩
  have heval_sub (b : ℂ) (z : K) : evalAt z (algebraMap ℂ S b - x) = b - (z : ℂ) := by
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, heval_mk,
      ContinuousMap.coe_mk]
  have hx : spectrum ℂ x₀ = K := by
    rw [ContinuousMap.spectrum_eq_range]
    exact Subtype.range_coe
  have houtside (b : ℂ) (hb : b ∈ A \ K) : b ∉ spectrum ℂ x := by
    obtain ⟨y, hyR, hyval⟩ := mem_rationalSubalgebra_inv_sub hb
    rw [spectrum.notMem_iff, isUnit_iff_exists_inv]
    refine ⟨⟨y, R.le_topologicalClosure hyR⟩, Subtype.ext <| ContinuousMap.ext fun z ↦ ?_⟩
    have hz : evalAt z ((algebraMap ℂ S b - x) * ⟨y, R.le_topologicalClosure hyR⟩) =
        evalAt z 1 := by
      rw [map_mul, map_one, heval_sub, heval_mk, hyval z]
      exact mul_inv_cancel₀ (sub_ne_zero.mpr fun h : b = (z : ℂ) ↦ hb.2 (h ▸ z.property))
    rwa [hevalAt, hevalAt, OneMemClass.coe_one, ContinuousMap.one_apply] at hz
  have hspec : a ∉ spectrum ℂ x := by
    intro haspec
    have hbd := Subalgebra.isBounded_connectedComponentIn_spectrum_compl S x haspec
    have hcoe : (x : C(K, ℂ)) = x₀ := rfl
    rw [hcoe, hx] at hbd
    obtain ⟨b, hbA, hbc⟩ := hA (mem_filledHull_iff.mpr hbd)
    apply houtside b ⟨hbA, connectedComponentIn_subset _ _ hbc⟩
    rw [Subalgebra.spectrum_eq_union_sUnion_connectedComponentIn S x, hcoe, hx]
    exact Or.inr <| mem_biUnion ⟨haspec, ha⟩ hbc
  have hu : IsUnit (x - algebraMap ℂ S a) := by
    simpa only [neg_sub] using (spectrum.notMem_iff.mp hspec).neg
  let v : S := ↑hu.unit⁻¹
  have hv (z : K) : (v : C(K, ℂ)) z = ((z : ℂ) - a)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have h := congrArg (evalAt z) hu.unit.inv_mul
    have hxsub : evalAt z (x - algebraMap ℂ S a) = (z : ℂ) - a := by
      rw [← neg_sub (algebraMap ℂ S a) x, map_neg, heval_sub, neg_sub]
    rw [map_mul, map_one, IsUnit.unit_spec, hxsub, hevalAt] at h
    exact h
  obtain ⟨g, ⟨p, q, hq, hqA, hgval⟩, hdist⟩ := Metric.mem_closure_iff.mp v.property ε hε
  refine ⟨p, q, hq, hqA, fun z hz ↦ ?_⟩
  rw [← hgval ⟨z, hz⟩, ← hv ⟨z, hz⟩]
  exact lt_of_le_of_lt ((v.val - g).norm_coe_le_norm ⟨z, hz⟩) (by simpa [dist_eq_norm] using hdist)

end TauCeti
