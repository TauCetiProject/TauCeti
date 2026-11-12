/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units

/-!
# Runge approximation of simple fractions

If a compact set `K` is filled in an open subset `Ω` of the complex plane, every simple
fraction with pole outside `K` is uniformly approximable on `K` by functions holomorphic on `Ω`.
Neither `K` nor `Ω` needs to be connected. This is the simple-fraction form of Runge's theorem
used to replace the rational kernels in finite-rank holomorphic approximation operators.

The proof uses Mathlib's spectral description of closed subalgebras: an extra spectral point
fills its entire bounded complementary component. Applied to the closed algebra of holomorphic
restrictions, filledness rules out such a component because it meets the complement of `Ω`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1.
* Mathlib's `ContinuousMap.spectrum_eq_range`, `Subalgebra.spectrum_sUnion_connectedComponentIn` and
  `Subalgebra.spectrum_isBounded_connectedComponentIn` supply the closed-algebra pole-pushing
  argument.
-/

public section

open Set
open scoped Topology

namespace TauCeti

variable {K Ω : Set ℂ}

/-- **Runge approximation for a simple fraction.** On a compact set filled in `Ω`, a simple
fraction whose pole avoids that compact set is uniformly approximable by functions holomorphic
on all of `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_inv_sub_lt (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a : ℂ} (ha : a ∉ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε := by
  -- Work in the uniform closure of the restriction algebra; the coordinate has ambient spectrum K.
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : TopologicalSpace.Opens ℂ := ⟨Ω, hΩ⟩
  let ρ := ContinuousMap.compRightAlgHom ℂ ℂ
    (⟨Set.inclusion hKΩ, continuous_inclusion hKΩ⟩ : C(K, U))
  let φ := ρ.comp (holomorphicFunctions U).val
  let R := φ.range
  let S := R.topologicalClosure
  let : IsClosed (S : Set C(K, ℂ)) := R.isClosed_topologicalClosure
  let x : S := ⟨φ (HolomorphicFunctions.of U id differentiable_id.differentiableOn),
    R.le_topologicalClosure ⟨_, rfl⟩⟩
  have hxval (z : K) : (x : C(K, ℂ)) z = z := by
    simp [x, φ, ρ]
  have hx : spectrum ℂ (x : C(K, ℂ)) = K := by
    rw [ContinuousMap.spectrum_eq_range]
    have hxmap : (x : C(K, ℂ)) = ⟨Subtype.val, continuous_subtype_val⟩ :=
      ContinuousMap.ext hxval
    rw [hxmap]
    exact Subtype.range_coe
  -- Poles outside Ω already have a holomorphic inverse. Filledness then excludes every extra
  -- spectral component, since such a component would be bounded and would have to meet Ωᶜ.
  have houtside (b : ℂ) (hb : b ∉ Ω) : b ∉ spectrum ℂ x := by
    have hd : DifferentiableOn ℂ (fun z : ℂ ↦ (b - z)⁻¹) Ω :=
      (differentiableOn_const b |>.sub differentiableOn_id).inv fun z hz ↦
        sub_ne_zero.mpr fun h : b = z ↦ hb (h.symm ▸ hz)
    let y := φ (HolomorphicFunctions.of U (fun z : ℂ ↦ (b - z)⁻¹) hd)
    have hy : y ∈ S := R.le_topologicalClosure ⟨_, rfl⟩
    rw [spectrum.notMem_iff, isUnit_iff_exists_inv]
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    simpa [y, φ, ρ, hxval] using
      mul_inv_cancel₀ (sub_ne_zero.mpr fun h : b = (z : ℂ) ↦ hb (h ▸ hKΩ z.property))
  have hspec : a ∉ spectrum ℂ x := by
    intro haspec
    have hbounded := Subalgebra.spectrum_isBounded_connectedComponentIn S x haspec
    rw [hx] at hbounded
    have hnot := (isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
      hK.isClosed hΩ hKΩ).mp hfill a ⟨mem_filledHull_iff.mpr hbounded, ha⟩
    obtain ⟨b, hb, hbΩ⟩ := Set.not_subset.mp hnot
    apply houtside b hbΩ
    rw [Subalgebra.spectrum_sUnion_connectedComponentIn S x]
    exact Or.inr <| mem_biUnion ⟨haspec, (by rwa [hx])⟩ <| by rwa [hx]
  have hu : IsUnit (x - algebraMap ℂ S a) := by
    have h := (spectrum.notMem_iff.mp hspec).neg
    simpa only [neg_sub] using h
  -- The inverse in the closed algebra is the desired fraction. Approximate it by an element
  -- of the restriction algebra and recover its ambient holomorphic representative.
  let v : S := ↑hu.unit⁻¹
  have hv (z : K) : (v : C(K, ℂ)) z = ((z : ℂ) - a)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have h := congrArg (fun f : S ↦ (f : C(K, ℂ)) z) hu.unit.inv_mul
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one,
      Subalgebra.coe_algebraMap, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
      ContinuousMap.one_apply, algebraMap_apply, smul_eq_mul, mul_one, IsUnit.unit_spec,
      hxval] using h
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp v.property ε hε
  obtain ⟨g', rfl⟩ := hg
  refine ⟨HolomorphicFunctions.extend g', HolomorphicFunctions.differentiableOn_extend g',
    fun z hz ↦ ?_⟩
  rw [HolomorphicFunctions.extend_apply g' ⟨z, hKΩ hz⟩, ← hv ⟨z, hz⟩]
  exact lt_of_le_of_lt ((v.val - φ g').norm_coe_le_norm ⟨z, hz⟩)
    (by simpa [dist_eq_norm] using hdist)

end TauCeti
