/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Group.SliceIntegral
public import TauCeti.RepresentationTheory.Smooth.CompactSupport
import TauCeti.MeasureTheory.Group.OpenSubgroup
import TauCeti.Topology.Algebra.Group.LocallyConstant.CompactSupport
import TauCeti.Topology.Algebra.Support

/-!
# Descent of invariant distributions to a slice

Let a topological group `Γ` act on a topological group `G` by conjugation through a continuous
homomorphism `j : Γ →* G`, and let `X ⊆ C` be a slice for this action with closed stabiliser
`H ⊆ Γ` (`TauCeti.IsSlice j H X C`, in `TauCeti.Topology.Algebra.Group.Slice`). For a test function
`Ψ` on `Γ × G` (a locally constant function with compact support,
`LocallyConstant.compactlySupported`, with values in a real normed space `E`) and a left invariant
measure `μ` on `H`, the fibre integral `TauCeti.fiberIntegral j μ Ψ` over the `H`-orbits descends to
a test function on `C`, which is the restriction of a test function on `G`
(`TauCeti.IsSlice.exists_eq_fiberIntegral`, in `TauCeti.MeasureTheory.Group.SliceIntegral`).

The main theorem is the descent of invariant distributions
(`TauCeti.IsSlice.map_eq_zero_of_integral_eq_zero_of_eq_fiberIntegral`): let `μ` be left invariant
and finite on compact sets, and let `I` be a linear map on the test functions on `G` that is
invariant under conjugation by `j Γ` and only depends on the restriction of a test function to
`C`. If `Ψ` integrates to zero along `Γ` at every point of `X`, that is `∫ γ, Ψ (γ, y) = 0` for a
Haar measure on `Γ` and every `y ∈ X`, then `I` vanishes on every test function whose restriction
to `C` is the fibre integral of `Ψ`.

The proof follows Harish-Chandra's descent along a slice. Choose an open subgroup `U ⊆ Γ` under
which `Ψ` is invariant on the right in the first variable; finitely many cosets `r U` cover the
`Γ`-support of `Ψ`, and `Ψ (γ, y) = ∑_r 1_{r U} (γ) Ψ (r, y)`. The fibre integral of the piece
supported on `r U` is the translate, under conjugation by `j r`, of the fibre integral of the
piece `1_U (γ) Ψ (r, y)`, so invariance of `I` replaces every piece by one supported on `U`. The sum
of those pieces is `1_U (γ) ∑_r Ψ (r, y)`, so its fibre integral vanishes on `C` once
`∑_r Ψ (r, y) = 0` for `y ∈ X`. This holds because `∫ γ, Ψ (γ, y)` is the measure of `U` times
`∑_r Ψ (r, y)`: a nonzero sum would force a nonzero piece, whose support `r U` lies in the compact
support of `Ψ`, so `U` would have finite positive measure and the integral could not vanish
(`OpenSubgroup.sum_eq_zero_of_integral_eq_zero`).

## Main results

* `TauCeti.IsSlice.map_eq_zero_of_integral_eq_zero_of_eq_fiberIntegral`: the descent of invariant
  distributions.

## References

* Harish-Chandra, *Harmonic analysis on reductive p-adic groups*, notes by G. van Dijk, Lecture
  Notes in Mathematics 162, Springer, 1970 (descent of invariant distributions to a slice).
* The statement adapts the declaration `New.IsInvariantDistribution.eq_zero_of_isImage` of the
  formal proof `[ShortProof]`, grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright
  2026 Anthropic PBC), file `src/Lib/Adelic/TraceFormula/FibreIntegral.lean`. Here the test
  functions are those of `LocallyConstant.compactlySupported`, the invariance of the linear map is
  stated through `TauCeti.compactlySupportedRep`, and the proof is written independently.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology LocallyConstant

namespace TauCeti

variable {Γ G E F : Type*} [Group Γ] [Group G] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : Type*} [Ring R] [Module R E] [AddCommGroup F] [Module R F] {j : Γ →* G}
  {H : Subgroup Γ} {X C : Set G}

section Descent

variable [TopologicalSpace Γ] [TopologicalSpace G] [IsTopologicalGroup Γ] [IsTopologicalGroup G]

variable {U : OpenSubgroup Γ} {T : Finset (Γ ⧸ U.toSubgroup)}

open scoped Classical in
/-- The pieces `Φ q : (γ, y) ↦ 1_U (γ) Ψ (q.out * γ, y)` of a test function `Ψ` on `Γ × G`, for the
cosets `q` of an open subgroup `U`, are test functions. If `T` contains every coset meeting the
projection to `Γ` of the support of `Ψ`, the fibre integral of `Ψ` is the sum of the fibre integrals
of the pieces at `(q.out⁻¹ * γ, y)` over the cosets `q` in `T`. -/
private theorem exists_fiberIntegral_eq_sum [MeasurableSpace H] [OpensMeasurableSpace H]
    (hj : Continuous j) (hH : IsClosed (H : Set Γ)) (μ : Measure H) [IsFiniteMeasureOnCompacts μ]
    (Ψ : compactlySupported R (Γ × G) E)
    (hT : ∀ a z, (Ψ : LocallyConstant (Γ × G) E) (a, z) ≠ 0 → (a : Γ ⧸ U.toSubgroup) ∈ T) :
    ∃ Φ : Γ ⧸ U.toSubgroup → compactlySupported R (Γ × G) E,
      (∀ q a z, (Φ q : LocallyConstant (Γ × G) E) (a, z) =
        if a ∈ U then (Ψ : LocallyConstant (Γ × G) E) (q.out * a, z) else 0) ∧
      ∀ γ y, fiberIntegral j μ Ψ γ y =
        ∑ q ∈ T, fiberIntegral j μ (Φ q : LocallyConstant (Γ × G) E) (q.out⁻¹ * γ) y := by
  -- `Φ q` is the translate `(γ, y) ↦ Ψ (q.out * γ, y)`, cut off along the clopen set `U × G`.
  have hUcl : IsClopen ((U : Set Γ) ×ˢ (univ : Set G)) := U.isClopen.prod isClopen_univ
  set τ : Γ ⧸ U.toSubgroup → compactlySupported R (Γ × G) E := fun q =>
    compactlySupportedRep R (Γ × G) (Γ × G) E (q.out⁻¹, 1) Ψ
  set Φ : Γ ⧸ U.toSubgroup → compactlySupported R (Γ × G) E := fun q =>
    ⟨(τ q : LocallyConstant (Γ × G) E).indicator hUcl,
      indicator_mem_compactlySupported_of_mem (τ q).property hUcl⟩
  have hΦ (q : Γ ⧸ U.toSubgroup) (a : Γ) (z : G) : (Φ q : LocallyConstant (Γ × G) E) (a, z) =
      if a ∈ U then (Ψ : LocallyConstant (Γ × G) E) (q.out * a, z) else 0 := by
    simp [Φ, τ, LocallyConstant.indicator_apply, Set.indicator_apply]
  refine ⟨Φ, hΦ, fun γ y => ?_⟩
  simp only [fiberIntegral_apply]
  rw [← integral_finsetSum _ fun q _ => integrable_fiberIntegral_integrand hj hH μ (Φ q) _ y]
  congr 1
  funext h
  rw [← QuotientGroup.sum_ite_out_inv_mul_mem (fun a => hT a ((j h)⁻¹ * y * j h))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hΦ]
  simp only [OpenSubgroup.mem_toSubgroup, mul_assoc, mul_inv_cancel_left]

/-- The descent of invariant distributions, for complete `E`
(`TauCeti.IsSlice.map_eq_zero_of_integral_eq_zero_of_eq_fiberIntegral`). -/
private theorem IsSlice.map_eq_zero_of_completeSpace [CompleteSpace E] [T2Space G]
    [WeaklyLocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace Γ]
    [OpensMeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSpace H] [OpensMeasurableSpace H]
    [MeasurableMul H] (hs : IsSlice j H X C) (hj : Continuous j)
    (hH : IsClosed (H : Set Γ)) (ν : Measure Γ) [ν.IsHaarMeasure] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (I : compactlySupported R G E →ₗ[R] F)
    (hI : ∀ γ f, I (compactlySupportedRep R (ConjAct G) G E (ConjAct.toConjAct (j γ)) f) = I f)
    (hIC : ∀ f : compactlySupported R G E, (∀ c ∈ C, (f : LocallyConstant G E) c = 0) → I f = 0)
    (Ψ : compactlySupported R (Γ × G) E)
    (hΨ : ∀ y ∈ X, ∫ γ, (Ψ : LocallyConstant (Γ × G) E) (γ, y) ∂ν = 0)
    (f : compactlySupported R G E)
    (hf : ∀ γ, ∀ y ∈ X, (f : LocallyConstant G E) (j γ * y * (j γ)⁻¹) = fiberIntegral j μ Ψ γ y) :
    I f = 0 := by
  classical
  obtain ⟨U, T, hUψ, hT⟩ :=
    exists_openSubgroup_finset_forall_mul_fst_eq (mem_compactlySupported.1 Ψ.property)
  have hsum (y : G) (hy : y ∈ X) : ∑ q ∈ T, (Ψ : LocallyConstant (Γ × G) E) (q.out, y) = 0 :=
    OpenSubgroup.sum_eq_zero_of_integral_eq_zero ν U
      ((mem_compactlySupported.1 Ψ.property).comp_prodMk_left y) (fun a u hu => hUψ u hu a y)
      (fun a => hT a y) (hΨ y hy)
  obtain ⟨Φ, hΦ, hΦsum⟩ := exists_fiberIntegral_eq_sum hj hH μ Ψ hT
  choose g hg using fun q => hs.exists_eq_fiberIntegral hj μ (Φ q)
  set Rq : Γ ⧸ U.toSubgroup → compactlySupported R G E := fun q =>
    compactlySupportedRep R (ConjAct G) G E (ConjAct.toConjAct (j q.out)) (g q)
  have hsum_apply (P : Γ ⧸ U.toSubgroup → compactlySupported R G E) (x : G) :
      ((∑ q ∈ T, P q : compactlySupported R G E) : LocallyConstant G E) x =
        ∑ q ∈ T, (P q : LocallyConstant G E) x := by
    rw [Submodule.coe_sum]
    exact map_sum (LocallyConstant.evalAddMonoidHom x) _ _
  -- On `C`, `f` is the sum of the conjugates `Rq q` of the `g q`.
  have h₁ : I f = ∑ q ∈ T, I (Rq q) := by
    rw [← map_sum, ← sub_eq_zero, ← map_sub]
    refine hIC _ fun c hc => ?_
    obtain ⟨γ, y, hy, rfl⟩ := (hs.mem_iff c).1 hc
    have hR : ∀ q, (Rq q : LocallyConstant G E) (j γ * y * (j γ)⁻¹) =
        fiberIntegral j μ (Φ q) (q.out⁻¹ * γ) y := fun q => by
      rw [← hg q _ y hy]
      simp only [Rq, compactlySupportedRep_apply_coe, ConjAct.smul_def, map_mul, map_inv,
        ConjAct.ofConjAct_toConjAct, inv_inv]
      congr 1
      group
    simp only [Submodule.coe_sub, LocallyConstant.coe_sub, Pi.sub_apply, hsum_apply, hR,
      hf γ y hy, hΦsum γ y, sub_self]
  -- The sum of the `g q` vanishes on `C`, since the sum of the pieces vanishes on `Γ × X`.
  have h₂ : I (∑ q ∈ T, g q) = 0 := by
    refine hIC _ fun c hc => ?_
    obtain ⟨γ, y, hy, rfl⟩ := (hs.mem_iff c).1 hc
    simp only [hsum_apply, hg _ γ y hy]
    rw [← fiberIntegral_finsetSum μ T fun q _ =>
      integrable_fiberIntegral_integrand hj hH μ (Φ q) _ y, fiberIntegral_apply]
    refine integral_eq_zero_of_ae (ae_of_all _ fun h => ?_)
    simp only [Finset.sum_apply, hΦ, Pi.zero_apply]
    split_ifs with hγh
    · have hX := hs.inv_conj_mem h.property hy
      rw [← hsum _ hX]
      exact Finset.sum_congr rfl fun q _ => hUψ _ hγh _ _
    · simp
  rw [h₁]
  simpa [Rq, hI, ← map_sum] using h₂

/-- **Descent of invariant distributions to a slice.** Let `X ⊆ C` be a slice for the conjugation
action of `Γ` on a Hausdorff, locally compact, totally disconnected group `G` through a continuous
`j`, with closed stabiliser `H` carrying a left invariant measure `μ` finite on compact sets, and
let `ν` be a Haar measure on `Γ`. Test functions take values in a real normed space `E` that is a
module over a ring `R`. Let `I` be an `R`-linear map from the test functions on `G` to an `R`-module
`F` that is invariant under conjugation by `j Γ` and vanishes on the test functions vanishing on
`C`. If a test function `Ψ` on `Γ × G`
satisfies `∫ γ, Ψ (γ, y) ∂ν = 0` for every `y ∈ X`, then `I f = 0` for every test function `f`
whose value at `j γ * y * (j γ)⁻¹` is the fibre integral of `Ψ` at `(γ, y)` for all `γ` and
`y ∈ X`. Such an `f` exists by `TauCeti.IsSlice.exists_eq_fiberIntegral`. -/
theorem IsSlice.map_eq_zero_of_integral_eq_zero_of_eq_fiberIntegral [T2Space G]
    [WeaklyLocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace Γ]
    [OpensMeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSpace H] [OpensMeasurableSpace H]
    [MeasurableMul H] (hs : IsSlice j H X C) (hj : Continuous j)
    (hH : IsClosed (H : Set Γ)) (ν : Measure Γ) [ν.IsHaarMeasure] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (I : compactlySupported R G E →ₗ[R] F)
    (hI : ∀ γ f, I (compactlySupportedRep R (ConjAct G) G E (ConjAct.toConjAct (j γ)) f) = I f)
    (hIC : ∀ f : compactlySupported R G E, (∀ c ∈ C, (f : LocallyConstant G E) c = 0) → I f = 0)
    (Ψ : compactlySupported R (Γ × G) E)
    (hΨ : ∀ y ∈ X, ∫ γ, (Ψ : LocallyConstant (Γ × G) E) (γ, y) ∂ν = 0)
    (f : compactlySupported R G E)
    (hf : ∀ γ, ∀ y ∈ X, (f : LocallyConstant G E) (j γ * y * (j γ)⁻¹) = fiberIntegral j μ Ψ γ y) :
    I f = 0 := by
  by_cases hE : CompleteSpace E
  · exact hs.map_eq_zero_of_completeSpace hj hH ν μ I hI hIC Ψ hΨ f hf
  -- Without completeness every Bochner integral into `E` is `0`, so `f` vanishes on `C`.
  refine hIC f fun c hc => ?_
  obtain ⟨γ, y, hy, rfl⟩ := (hs.mem_iff c).1 hc
  rw [hf γ y hy, fiberIntegral_apply, integral_of_not_completeSpace hE]

end Descent

end TauCeti
