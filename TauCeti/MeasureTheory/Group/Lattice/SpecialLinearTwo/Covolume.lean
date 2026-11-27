/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.Lattice.SpecialLinearTwo.Basic

/-!
# The covolume of `SL(2, ℤ)` in `SL(2, ℝ)`

Normalize the Haar measure of `SL(2, ℝ)` as in `Matrix.SpecialLinearGroup.instMeasureSpaceSL2R`:
the orbit map `g ↦ g • i` pushes it forward to the hyperbolic area `dx dy / y²` of `ℍ`, and the
stabilizer `K` of `i` has mass one. In this normalization `SL(2, ℤ)` has covolume `π / 6`, half the
area `π / 3` of the modular fundamental domain `𝒟ᵒ`: the central element `-1 ∈ SL(2, ℤ)` acts
trivially on `ℍ` but freely on `SL(2, ℝ)`.

The proof counts. Let `D` be a fundamental domain for `SL(2, ℤ)` acting on `SL(2, ℝ)` by left
multiplication, and `A` the preimage of `𝒟ᵒ` under the orbit map, of measure `π / 3`. Unfolding
over `D`, `μ(A) = ∫_D #{γ : γ⁻¹ g • i ∈ 𝒟ᵒ} dg`. For almost every `g` the orbit of `g • i` meets
`𝒟ᵒ`, and then exactly two elements `γ` qualify, `γ₀` and `-γ₀`
(`ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo`). So `μ(A) = 2 μ(D)`.

## Main results

* `Matrix.SpecialLinearGroup.two_mul_volume_of_isFundamentalDomain`: every fundamental domain `D`
  of the left action of `SL(2, ℤ)` on `SL(2, ℝ)` has `2 μ(D) = π / 3`.
* `Matrix.SpecialLinearGroup.covolume_range_map_intCast`: the covolume of the left action is
  `π / 6`.
* `Matrix.SpecialLinearGroup.covolume_op_range_map_intCast`: so is the covolume of the right
  action `g ↦ g γ`, the covolume of the lattice `SL(2, ℤ)` (`Subgroup.IsLattice`).

## References

* Frederick M. Goodman, Pierre de la Harpe, Vaughan F. R. Jones, *Coxeter Graphs and Towers of
  Algebras*, Springer, 1989, §3.3.
-/

public section

open MeasureTheory Measure Set UpperHalfPlane
open scoped MatrixGroups ENNReal Pointwise Real

namespace Matrix.SpecialLinearGroup

/-- **Two elements bring a point into `𝒟ᵒ`.** If `γ₀ • w ∈ 𝒟ᵒ`, then exactly two elements `γ` of
the image of `SL(2, ℤ)` in `SL(2, ℝ)` have `γ⁻¹ • w ∈ 𝒟ᵒ`, namely `γ₀⁻¹` and `-γ₀⁻¹`. -/
private theorem tsum_indicator_eq_two {w : ℍ} {γ₀ : SL(2, ℤ)} (h : γ₀ • w ∈ ModularGroup.fdo) :
    ∑' γ : (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range,
      (ModularGroup.fdo : Set ℍ).indicator (1 : ℍ → ℝ≥0∞) ((γ : SL(2, ℝ))⁻¹ • w) = 2 := by
  classical
  set ι := (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ))
  have hsmul (δ : SL(2, ℤ)) (z : ℍ) : (ι δ)⁻¹ • z = δ⁻¹ • z := by simp [ι, ← map_inv]
  set a : ι.range := ⟨ι γ₀⁻¹, γ₀⁻¹, rfl⟩
  set b : ι.range := ⟨ι (-γ₀⁻¹), -γ₀⁻¹, rfl⟩
  have hab : a ≠ b := by
    intro hab
    have h1 : γ₀⁻¹ = -γ₀⁻¹ := map_intCast_injective (R := ℝ) (congrArg Subtype.val hab)
    have h2 : (1 : SL(2, ℤ)) = -1 := by simpa using congrArg (γ₀ * ·) h1
    have h3 := congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h2
    norm_num at h3
  have hga : (ModularGroup.fdo : Set ℍ).indicator (1 : ℍ → ℝ≥0∞) ((a : SL(2, ℝ))⁻¹ • w) = 1 :=
    indicator_of_mem (by simpa [a, hsmul] using h) _
  have hgb : (ModularGroup.fdo : Set ℍ).indicator (1 : ℍ → ℝ≥0∞) ((b : SL(2, ℝ))⁻¹ • w) = 1 :=
    indicator_of_mem (by simpa [b, hsmul, ModularGroup.SL_neg_smul] using h) _
  rw [tsum_eq_sum (s := {a, b}) fun γ hγ ↦ ?_, Finset.sum_pair hab, hga, hgb, one_add_one_eq_two]
  refine indicator_of_notMem (fun hδ ↦ ?_) _
  obtain ⟨_, δ, rfl⟩ := γ
  rw [hsmul] at hδ
  have hδ' : (δ⁻¹ * γ₀⁻¹) • (γ₀ • w) ∈ ModularGroup.fdo := by
    rwa [mul_smul, inv_smul_smul]
  -- so `δ⁻¹ γ₀⁻¹ = ±1`, that is `δ = γ₀⁻¹` or `δ = -γ₀⁻¹`
  have hδ'' : δ = γ₀⁻¹ ∨ δ = -γ₀⁻¹ := by
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo h hδ' with h1 | h1
    · exact Or.inl (by simpa using mul_eq_one_iff_inv_eq.mp h1)
    · have : (-δ)⁻¹ * γ₀⁻¹ = 1 := by rw [inv_neg, neg_mul, h1, neg_neg]
      exact Or.inr (by simpa [neg_eq_iff_eq_neg] using mul_eq_one_iff_inv_eq.mp this)
  rcases hδ'' with rfl | rfl <;> simp [a, b] at hγ

/-- **Every fundamental domain of `SL(2, ℤ)` has measure `π / 6`.** If `D` is a fundamental domain
for `SL(2, ℤ)` acting on `SL(2, ℝ)` by left multiplication, then `2 μ(D) = π / 3`, the area of
the modular fundamental domain. -/
theorem two_mul_volume_of_isFundamentalDomain {D : Set SL(2, ℝ)}
    (hD : IsFundamentalDomain (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range D volume) :
    2 * volume D = ENNReal.ofReal (π / 3) := by
  set A : Set SL(2, ℝ) := (· • I) ⁻¹' ModularGroup.fdo
  have hcont : Continuous fun g : SL(2, ℝ) ↦ g • I := continuous_id.smul continuous_const
  have hA : MeasurableSet A := ModularGroup.isOpen_fdo.measurableSet.preimage hcont.measurable
  have hvolA : volume A = ENNReal.ofReal (π / 3) := by
    rw [volume_preimage_smul_I, ← measure_congr ModularGroup.fd_ae_eq_fdo, ModularGroup.volume_fd]
  rw [← hvolA, ← lintegral_indicator_one hA, hD.lintegral_eq_tsum',
    ← lintegral_tsum (f := fun γ (x : SL(2, ℝ)) ↦ A.indicator 1 (γ⁻¹ • x)) fun γ ↦
      ((measurable_one.indicator hA).comp (measurable_const_smul γ⁻¹)).aemeasurable,
    ← setLIntegral_const]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [measurePreserving_smul_I.quasiMeasurePreserving.ae
    ModularGroup.ae_exists_smul_mem_fdo] with g ⟨γ₀, hγ₀⟩
  rw [← tsum_indicator_eq_two hγ₀]
  refine tsum_congr fun γ ↦ ?_
  rw [Subgroup.smul_def, Subgroup.coe_inv, smul_eq_mul, ← mul_smul]
  -- `A.indicator 1` is `𝒟ᵒ.indicator 1` composed with the orbit map
  exact (indicator_comp_right (· • I)).symm

/-- **The covolume of `SL(2, ℤ)` acting on `SL(2, ℝ)` by left multiplication** is `π / 6`. -/
theorem covolume_range_map_intCast :
    covolume (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range SL(2, ℝ) =
      ENNReal.ofReal (π / 6) := by
  obtain ⟨D, -, hD⟩ := Subgroup.exists_isFundamentalDomain_mul_left
    (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range volume
  rw [hD.covolume_eq_volume]
  have h := two_mul_volume_of_isFundamentalDomain hD
  have h6 : ENNReal.ofReal (π / 3) = 2 * ENNReal.ofReal (π / 6) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
    ring_nf
  rw [h6] at h
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 h

/-- **The covolume of the lattice `SL(2, ℤ)` in `SL(2, ℝ)`** is `π / 6`: the covolume of its right
action `g ↦ g γ`, in the normalization of the Haar measure for which the orbit map `g ↦ g • i`
pushes it forward to the hyperbolic area. -/
theorem covolume_op_range_map_intCast :
    covolume (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range.op SL(2, ℝ) =
      ENNReal.ofReal (π / 6) := by
  obtain ⟨_, -, hD⟩ := Subgroup.exists_isFundamentalDomain_mul_left
    (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range volume
  exact (Subgroup.covolume_op_eq_covolume (hD.hasFundamentalDomain _)).trans
    covolume_range_map_intCast

end Matrix.SpecialLinearGroup
