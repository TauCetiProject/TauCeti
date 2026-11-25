/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.DefiningFunction
public import TauCeti.Geometry.Manifold.IntegralCurve.LevelRetraction

/-!
# A collar projection of a Riemann surface with boundary through its Schottky double

Let `M` be a Hausdorff, second-countable Riemann surface with compact boundary `A`, and `D` its
Schottky double, with sheet swap `τ` and seam `inl '' A`, the fixed set of `τ`. This file
constructs a *collar projection* of `M`: a map `ρ : M → M` from an open neighbourhood `U` of the
boundary onto the boundary, fixing the boundary, which is smooth when read on the double through
the fold (`TauCeti.SchottkyDouble.exists_collarProjection`). These are the collar hypotheses of
`TauCeti.SchottkyDouble.contMDiffOn_coordChange_doubledBundleCore`, under which a complex core
constant along the fibres of `ρ` has a smooth double.

The construction goes through the double. A smooth defining function `g` of the seam which is odd
under `τ` (`TauCeti.SchottkyDouble.exists_odd_definingFunction`) has the seam as a compact regular
zero level, and `τ` reverses its sign and fixes the zero level. Flowing to the zero level along a
field which `τ` reverses gives a smooth retraction `r` of a neighbourhood `W` of the seam onto the
seam, invariant under `τ` on `W`
(`TauCeti.exists_contMDiff_retraction_zeroLevel_of_involutive_of_eqOn`, here
`TauCeti.SchottkyDouble.exists_retraction_seam`).

The collar projection is `ρ x = fold (r (inl x))` on `U = inl⁻¹ W`. Since `r` is invariant under
`τ`, a point and its mirror image have the same image, so `ρ ∘ fold = fold ∘ r` on `fold⁻¹ U`.
The fold is not differentiable across the seam, but it is smooth read within the first copy of
`M` (`TauCeti.SchottkyDouble.contMDiffOn_fold_range_inl`), and `r` maps `fold⁻¹ U` into the seam,
which lies in the first copy; so `fold ∘ r`, hence `ρ ∘ fold`, is smooth on `fold⁻¹ U`.

## Main results

* `TauCeti.SchottkyDouble.exists_retraction_seam`: a smooth retraction of a neighbourhood of the
  seam onto the seam, invariant under the sheet swap.
* `TauCeti.SchottkyDouble.exists_collarProjection`: a collar projection of `M` which is smooth
  when read on the double through the fold, and smooth on `M`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.3, for the doubled bundle built on a collar.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, Section 5, for collars
  obtained by flowing to a regular level.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti.SchottkyDouble

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid] [T2Space M] [SecondCountableTopology M]

local notation "A" => (borderedInterior M : Set M)ᶜ
local notation "D" => SchottkyDouble M

/-- **An invariant retraction onto the seam.** If the boundary of `M` is compact, there are a
smooth map `r` of the Schottky double fixing the seam pointwise and an open neighbourhood `W` of
the seam such that `r` maps `W` into the seam and is invariant under the sheet swap on `W`. -/
theorem exists_retraction_seam (hA : IsCompact A) :
    ∃ r : D → D, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ r ∧ (∀ z ∈ DoubleAlong.inl A '' A, r z = z) ∧
      ∃ W, IsOpen W ∧ DoubleAlong.inl A '' A ⊆ W ∧
        ∀ z ∈ W, r z ∈ DoubleAlong.inl A '' A ∧ r (DoubleAlong.swap A z) = r z := by
  obtain ⟨g, hg, hodd, hzero, -, hderiv⟩ := exists_odd_definingFunction (M := M)
  have hK : g ⁻¹' {0} = DoubleAlong.inl A '' A := ext fun z ↦ hzero z
  -- The differential of `g` is positive on `i` at the seam, so it does not vanish there.
  have hreg (z : D) (hz : g z = 0) : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ) g z ≠ 0 := fun h ↦ by
    have h' := hderiv z ((hzero z).1 hz)
    rw [show mvfderiv 𝓘(ℝ, ℂ) g z = 0 by simp [mvfderiv, h]] at h'
    exact h'.ne rfl
  -- The swap fixes the seam.
  have hfix (z : D) (hz : g z = 0) : swapDiffeomorph ∞ z = z := by
    obtain ⟨a, ha, rfl⟩ := (hzero z).1 hz
    simpa only [coe_swapDiffeomorph, DoubleAlong.swap_eq_self_iff, DoubleAlong.fold_inl] using ha
  obtain ⟨r, hr, hr0, W, hW, hKW, hrW⟩ :=
    exists_contMDiff_retraction_zeroLevel_of_involutive_of_eqOn hg
      (hK ▸ hA.image (DoubleAlong.inl A).continuous) hreg (swapDiffeomorph ∞)
      (by simp only [coe_swapDiffeomorph, DoubleAlong.swap_swap, implies_true])
      (by simpa only [coe_swapDiffeomorph] using hodd) hfix
  rw [hK] at hKW
  refine ⟨r, hr, fun z hz ↦ hr0 z ((hzero z).2 hz), W, hW, hKW, fun z hz ↦ ?_⟩
  obtain ⟨h0, hτ⟩ := hrW z hz
  exact ⟨(hzero _).1 h0, by simpa only [coe_swapDiffeomorph] using hτ⟩

/-- **A collar projection through the double.** If the boundary `A` of `M` is compact, there are an
open neighbourhood `U` of `A` and a map `ρ : M → M` which maps `U` into `A`, fixes `A` pointwise,
is smooth on `U`, and is smooth on `fold⁻¹ U` when read on the Schottky double through the fold.

The last property is the regularity required of a collar projection by
`TauCeti.SchottkyDouble.contMDiffOn_coordChange_doubledBundleCore`. -/
theorem exists_collarProjection (hA : IsCompact A) :
    ∃ U : Set M, IsOpen U ∧ A ⊆ U ∧ ∃ ρ : M → M, MapsTo ρ U A ∧ (∀ x ∈ A, ρ x = x) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel ∞ (ρ ∘ DoubleAlong.fold A)
        (DoubleAlong.fold A ⁻¹' U) ∧
      ContMDiffOn closedUpperHalfPlaneModel closedUpperHalfPlaneModel ∞ ρ U := by
  obtain ⟨r, hr, hr0, W, hW, hKW, hrW⟩ := exists_retraction_seam hA
  set U := DoubleAlong.inl A ⁻¹' W
  -- Over `U`, `r` takes the same value at a point and at its mirror image in the first copy.
  have hr_inl :
      ∀ z ∈ DoubleAlong.fold A ⁻¹' U, r z = r (DoubleAlong.inl A (DoubleAlong.fold A z)) :=
    fun z hz ↦ by
      induction z using DoubleAlong.induction_on with
      | hl x => rw [DoubleAlong.fold_inl]
      | hr x =>
        rw [mem_preimage, DoubleAlong.fold_inr] at hz
        rw [DoubleAlong.fold_inr, ← DoubleAlong.swap_inl, (hrW _ hz).2]
  have hrU : MapsTo r (DoubleAlong.fold A ⁻¹' U) (DoubleAlong.inl A '' A) := fun z hz ↦
    hr_inl z hz ▸ (hrW _ hz).1
  -- On `fold⁻¹ U` the collar projection read through the fold is `fold ∘ r`.
  have hfold : ContMDiffOn 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel ∞
      (fun z ↦ DoubleAlong.fold A (r (DoubleAlong.inl A (DoubleAlong.fold A z))))
      (DoubleAlong.fold A ⁻¹' U) :=
    (contMDiffOn_fold_range_inl.comp hr.contMDiffOn
      (hrU.mono_right (image_subset_range _ _))).congr fun z hz ↦ by
        simp only [Function.comp_apply, hr_inl z hz]
  refine ⟨U, hW.preimage (DoubleAlong.inl A).continuous, fun a ha ↦ hKW ⟨a, ha, rfl⟩,
    fun x ↦ DoubleAlong.fold A (r (DoubleAlong.inl A x)), fun x hx ↦ ?_, fun a ha ↦ ?_, hfold,
    ?_⟩
  · obtain ⟨a, ha, h⟩ := (hrW _ hx).1
    beta_reduce
    rw [← h, DoubleAlong.fold_inl]
    exact ha
  · beta_reduce
    rw [hr0 _ ⟨a, ha, rfl⟩, DoubleAlong.fold_inl]
  · refine (hfold.comp (isSmoothEmbedding_inl le_rfl).contMDiff.contMDiffOn fun x hx ↦ ?_).congr
      fun x _ ↦ ?_
    · rwa [mem_preimage, mem_preimage, DoubleAlong.fold_inl]
    · simp only [Function.comp_apply, DoubleAlong.fold_inl]

end TauCeti.SchottkyDouble
