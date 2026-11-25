/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Decomposition
public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Sl2
public import TauCeti.Algebra.Lie.Sl2.Weyl.Automorphism

/-!
# Reflections of restricted roots

Let `θ` be a Cartan involution of a real Lie algebra `𝔤₀`, `𝔞` a maximal abelian subspace of its
`-1`-eigenspace `𝔭`, and `λ` a restricted root with coroot `H'_λ`
(`LieEquiv.IsCartanInvolution.restrictedCoroot`). The reflection

`s_λ ν = ν - ν(H'_λ) λ`

of `𝔞*` is realized by an automorphism of `𝔤₀`. For nonzero `E ∈ 𝔤_λ`, the operators `ad E` and
`ad F` of the `𝔰𝔩₂` triple `(H'_λ, E, F)` of `λ`
(`LieEquiv.IsCartanInvolution.isSl2Triple_restrictedCoroot`) are nilpotent
(`LieEquiv.IsCartanInvolution.isNilpotent_ad_of_mem_restrictedRootSpace`), and its Weyl
automorphism `exp(ad E) exp(-ad F) exp(ad E)` (`TauCeti.weylAut`) carries `𝔤_ν` into `𝔤_{s_λ ν}`.
Consequently `s_λ` permutes the restricted roots and preserves their multiplicities
`m_ν = dim 𝔤_ν`. This is the reflection step of the restricted root system (Knapp, Ch. VI,
Prop. 6.52, realizes `s_λ` inside `K_θ` by `e^{ad((π/2)(E' + θE'))}`; the Weyl automorphism of the
triple used here is a product of three exponentials of nilpotent operators, following Humphreys,
§14.3, and the root-space version `TauCeti.exists_lieEquiv_forall_mem_rootSpace`).

## Main results

* `LieEquiv.IsCartanInvolution.exists_lieEquiv_forall_mem_restrictedRootSpace`: an automorphism
  of `𝔤₀` carrying each `𝔤_ν` into `𝔤_{s_λ ν}`.
* `LieEquiv.IsCartanInvolution.sub_smul_mem_restrictedRoots`: `s_λ` maps `Σ` to `Σ`.
* `LieEquiv.IsCartanInvolution.finrank_restrictedRootSpace_sub_smul`: `m_{s_λ ν} = m_ν`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4, Proposition 6.52.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §14.3.
-/

public section

open LieAlgebra LieModule Module

namespace LieEquiv.IsCartanInvolution

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}
  (hθ : θ.IsCartanInvolution) (h𝔞 : θ.IsMaximalAbelianInP 𝔞)

/-- **The reflection of a restricted root is realized by an automorphism.** For a restricted root
`λ` there is an automorphism of `𝔤₀` carrying every `𝔤_ν` into `𝔤_{s_λ ν}`, where
`s_λ ν = ν - ν(H'_λ) λ`: the Weyl automorphism of the `𝔰𝔩₂` triple of `λ`. Adapted from
`TauCeti.exists_lieEquiv_forall_mem_rootSpace` for root spaces of a Cartan subalgebra. -/
theorem exists_lieEquiv_forall_mem_restrictedRootSpace {μ : Dual ℝ 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) :
    ∃ τ : L ≃ₗ⁅ℝ⁆ L, ∀ (ν : Dual ℝ 𝔞) (z : L), z ∈ 𝔞.restrictedRootSpace ν →
      τ z ∈ 𝔞.restrictedRootSpace (ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ) := by
  let _ : LieAlgebra ℚ L := TauCeti.ratLieAlgebra ℝ L
  obtain ⟨hμ0, hsp⟩ := Submodule.mem_restrictedRoots.mp hμ
  obtain ⟨E, hE, hE0⟩ := (Submodule.ne_bot_iff _).mp hsp
  obtain ⟨F, hF, t⟩ := hθ.exists_isSl2Triple_restrictedCoroot h𝔞 hμ0 hE hE0
  have hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0 := fun _ hx _ hy ↦ h𝔞.lie_eq_zero hx hy
  refine ⟨TauCeti.weylAut t
    (hθ.isNilpotent_ad_of_mem_restrictedRootSpace h𝔞.le_cartanP hab hμ0
      hE).exists_pow_apply_eq_zero
    (hθ.isNilpotent_ad_of_mem_restrictedRootSpace h𝔞.le_cartanP hab (neg_ne_zero.mpr hμ0)
      hF).exists_pow_apply_eq_zero,
    fun ν z hz ↦ Submodule.mem_restrictedRootSpace.mpr fun H ↦ ?_⟩
  have hye := Submodule.mem_restrictedRootSpace.mp hE H
  have hyf : ⁅(H : L), F⁆ = -(μ H • F) := by
    simpa only [LinearMap.neg_apply, neg_smul] using Submodule.mem_restrictedRootSpace.mp hF H
  rw [TauCeti.lie_weylAut_apply _ _ t hye hyf (Submodule.mem_restrictedRootSpace.mp hz H)
    (hθ.restrictedCoroot_lie_eq_smul_of_mem_restrictedRootSpace h𝔞.le_cartanP μ hz)]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm]

/-- **The multiplicities are invariant under reflections**: `dim 𝔤_{s_λ ν} = dim 𝔤_ν` for a
restricted root `λ` and every `ν ∈ 𝔞*`. -/
theorem finrank_restrictedRootSpace_sub_smul {μ : Dual ℝ 𝔞} (hμ : μ ∈ 𝔞.restrictedRoots)
    (ν : Dual ℝ 𝔞) :
    finrank ℝ (𝔞.restrictedRootSpace (ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ)) =
      finrank ℝ (𝔞.restrictedRootSpace ν) := by
  have := hθ.finiteDimensional
  obtain ⟨τ, hτ⟩ := hθ.exists_lieEquiv_forall_mem_restrictedRootSpace h𝔞 hμ
  have hle (γ : Dual ℝ 𝔞) : finrank ℝ (𝔞.restrictedRootSpace γ) ≤
      finrank ℝ (𝔞.restrictedRootSpace
        (γ - γ (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ)) := by
    rw [← LinearEquiv.finrank_map_eq τ.toLinearEquiv]
    exact Submodule.finrank_mono (Submodule.map_le_iff_le_comap.mpr fun z hz ↦ hτ γ z hz)
  refine le_antisymm ?_ (hle ν)
  have h := hle (ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ)
  rwa [hθ.sub_smul_sub_smul_restrictedCoroot h𝔞.le_cartanP
    (Submodule.mem_restrictedRoots.mp hμ).1] at h

/-- **Reflections permute the restricted roots**: if `λ` and `ν` are restricted roots, so is
`s_λ ν = ν - ν(H'_λ) λ`. -/
theorem sub_smul_mem_restrictedRoots {μ ν : Dual ℝ 𝔞} (hμ : μ ∈ 𝔞.restrictedRoots)
    (hν : ν ∈ 𝔞.restrictedRoots) :
    ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ ∈ 𝔞.restrictedRoots := by
  have := hθ.finiteDimensional
  obtain ⟨hν0, hνsp⟩ := Submodule.mem_restrictedRoots.mp hν
  refine Submodule.mem_restrictedRoots.mpr ⟨fun h ↦ hν0 ?_, fun h ↦ hνsp ?_⟩
  · rw [← hθ.sub_smul_sub_smul_restrictedCoroot h𝔞.le_cartanP
      (Submodule.mem_restrictedRoots.mp hμ).1 ν, h]
    simp
  · rw [← Submodule.finrank_eq_zero, ← hθ.finrank_restrictedRootSpace_sub_smul h𝔞 hμ ν, h,
      finrank_bot]

end LieEquiv.IsCartanInvolution
