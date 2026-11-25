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
(`LieEquiv.IsCartanInvolution.isSl2Triple_restrictedCoroot`) are locally nilpotent, and its Weyl
automorphism `exp(ad E) exp(-ad F) exp(ad E)` (`TauCeti.weylAut`) carries `𝔤_ν` into `𝔤_{s_λ ν}`.
Consequently `s_λ` permutes the restricted roots and preserves their multiplicities
`m_ν = dim 𝔤_ν`. This is the reflection step of the restricted root system (Knapp, Ch. VI,
Prop. 6.52, realizes `s_λ` inside `K_θ` by `e^{ad((π/2)(E' + θE'))}`; the Weyl automorphism of the
triple used here is a product of three exponentials of nilpotent operators).

## Main results

* `Submodule.exists_pow_ad_apply_eq_zero_of_mem_restrictedRootSpace`: if the restricted root
  spaces of `𝔞` span a Noetherian Lie algebra over a domain of characteristic zero, then `ad E` is
  locally nilpotent for `E` in a restricted root space of a nonzero functional.
* `LieEquiv.IsCartanInvolution.exists_lieEquiv_forall_mem_restrictedRootSpace`: an automorphism
  of `𝔤₀` carrying each `𝔤_ν` into `𝔤_{s_λ ν}`.
* `LieEquiv.IsCartanInvolution.sub_smul_mem_restrictedRoots`: `s_λ` maps `Σ` to `Σ`.
* `LieEquiv.IsCartanInvolution.finrank_restrictedRootSpace_sub_smul`: `m_{s_λ ν} = m_ν`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4, Proposition 6.52.
-/

public section

open LieAlgebra LieModule Module

namespace Submodule

variable {R L : Type*} [CommRing R] [IsDomain R] [CharZero R] [LieRing L] [LieAlgebra R L]
  [IsTorsionFree R L] [IsNoetherian R L] {𝔞 : Submodule R L} {μ : Dual R 𝔞} {x : L}

/-- **`ad E` is locally nilpotent on a nonzero restricted root space.** If the restricted root
spaces of `𝔞` span the Lie algebra, and `E ∈ 𝔤_μ` with `μ ≠ 0`, then every element is killed
by a power of `ad E`: `(ad E)^k` carries `𝔤_ν` into `𝔤_{ν + kμ}`, and only finitely many
restricted root spaces are nonzero. -/
theorem exists_pow_ad_apply_eq_zero_of_mem_restrictedRootSpace
    (hspan : ⨆ ν : Dual R 𝔞, 𝔞.restrictedRootSpace ν = ⊤) (hμ : μ ≠ 0)
    (hx : x ∈ 𝔞.restrictedRootSpace μ) (y : L) : ∃ k, ((ad R L x) ^ k) y = 0 := by
  have hpow (ν : Dual R 𝔞) (k : ℕ) {z : L} (hz : z ∈ 𝔞.restrictedRootSpace ν) :
      ((ad R L x) ^ k) z ∈ 𝔞.restrictedRootSpace (ν + k • μ) := by
    induction k with
    | zero => simpa using hz
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ad_apply, succ_nsmul', ← add_assoc, add_comm ν μ,
        add_assoc]
      exact lie_mem_restrictedRootSpace hx ih
  have hfin : {ν : Dual R 𝔞 | 𝔞.restrictedRootSpace ν ≠ ⊥}.Finite :=
    finite_ne_bot_of_iSupIndep iSupIndep_restrictedRootSpace
  obtain ⟨H, hH⟩ := not_forall.mp fun h ↦ hμ (LinearMap.ext h)
  have hone (ν : Dual R 𝔞) {z : L} (hz : z ∈ 𝔞.restrictedRootSpace ν) :
      ∃ k, ((ad R L x) ^ k) z = 0 := by
    have hinj : Function.Injective fun k : ℕ ↦ ν + k • μ := fun k l hkl ↦ by
      have h := LinearMap.congr_fun (add_left_cancel hkl) H
      simp only [LinearMap.smul_apply, nsmul_eq_mul] at h
      exact_mod_cast mul_right_cancel₀ hH h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 𝔞.restrictedRootSpace (ν + k • μ) = ⊥ := by
      by_contra! h
      exact Set.infinite_of_injective_forall_mem hinj h hfin
    exact ⟨k, (Submodule.eq_bot_iff _).mp hk _ (hpow ν k hz)⟩
  have hy : y ∈ ⨆ ν : Dual R 𝔞, 𝔞.restrictedRootSpace ν := hspan ▸ mem_top
  refine iSup_induction _ (motive := fun y ↦ ∃ k, ((ad R L x) ^ k) y = 0) hy hone
    ⟨0, map_zero _⟩ fun z w ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨max a b, ?_⟩
  rw [map_add, End.pow_map_zero_of_le (le_max_left a b) ha,
    End.pow_map_zero_of_le (le_max_right a b) hb, add_zero]

end Submodule

namespace LieEquiv.IsCartanInvolution

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}

/-- For a Cartan involution `θ` and an abelian subspace `𝔞` of `𝔭`, `ad E` is locally nilpotent
for `E` in the restricted root space of a nonzero functional. -/
theorem exists_pow_ad_apply_eq_zero_of_mem_restrictedRootSpace (hθ : θ.IsCartanInvolution)
    (h𝔞 : 𝔞 ≤ θ.cartanP) (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) {μ : Dual ℝ 𝔞} (hμ : μ ≠ 0)
    {x : L} (hx : x ∈ 𝔞.restrictedRootSpace μ) (y : L) : ∃ k, ((ad ℝ L x) ^ k) y = 0 :=
  have := hθ.finiteDimensional
  Submodule.exists_pow_ad_apply_eq_zero_of_mem_restrictedRootSpace
    (hθ.iSup_restrictedRootSpace_eq_top h𝔞 hab) hμ hx y

variable (hθ : θ.IsCartanInvolution) (h𝔞 : θ.IsMaximalAbelianInP 𝔞)

/-- **The reflection of a restricted root is realized by an automorphism.** For a restricted root
`λ` there is an automorphism of `𝔤₀` carrying every `𝔤_ν` into `𝔤_{s_λ ν}`, where
`s_λ ν = ν - ν(H'_λ) λ`: the Weyl automorphism of the `𝔰𝔩₂` triple of `λ`. -/
theorem exists_lieEquiv_forall_mem_restrictedRootSpace {μ : Dual ℝ 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) :
    ∃ τ : L ≃ₗ⁅ℝ⁆ L, ∀ (ν : Dual ℝ 𝔞) (z : L), z ∈ 𝔞.restrictedRootSpace ν →
      τ z ∈ 𝔞.restrictedRootSpace (ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ) := by
  let _ : LieAlgebra ℚ L := TauCeti.ratLieAlgebra ℝ L
  obtain ⟨hμ0, hsp⟩ := Submodule.mem_restrictedRoots.mp hμ
  obtain ⟨E, hE, hE0⟩ := (Submodule.ne_bot_iff _).mp hsp
  have t := hθ.isSl2Triple_restrictedCoroot h𝔞 hμ0 hE hE0
  set F := (2 / (killingForm ℝ L E (θ E) * μ ((hθ.killingEquivDual h𝔞.le_cartanP).symm μ))) •
    θ E
  have hF : F ∈ 𝔞.restrictedRootSpace (-μ) :=
    Submodule.smul_mem _ _ (apply_mem_restrictedRootSpace_neg h𝔞.le_cartanP hE)
  have hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0 := fun _ hx _ hy ↦ h𝔞.lie_eq_zero hx hy
  refine ⟨TauCeti.weylAut t
    (hθ.exists_pow_ad_apply_eq_zero_of_mem_restrictedRootSpace h𝔞.le_cartanP hab hμ0 hE)
    (hθ.exists_pow_ad_apply_eq_zero_of_mem_restrictedRootSpace h𝔞.le_cartanP hab
      (neg_ne_zero.mpr hμ0) hF), fun ν z hz ↦ Submodule.mem_restrictedRootSpace.mpr fun H ↦ ?_⟩
  have hye := Submodule.mem_restrictedRootSpace.mp hE H
  have hyf : ⁅(H : L), F⁆ = -(μ H • F) := by
    simpa only [LinearMap.neg_apply, neg_smul] using Submodule.mem_restrictedRootSpace.mp hF H
  rw [TauCeti.lie_weylAut_apply _ _ t hye hyf (Submodule.mem_restrictedRootSpace.mp hz H)
    (hθ.restrictedCoroot_lie_eq_smul_of_mem_restrictedRootSpace h𝔞.le_cartanP μ hz)]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm]

include hθ h𝔞 in
/-- The reflection `s_λ` is an involution of `𝔞*`: `s_λ (s_λ ν) = ν`. -/
theorem sub_smul_sub_smul_eq {μ : Dual ℝ 𝔞} (hμ : μ ≠ 0) (ν : Dual ℝ 𝔞) :
    (ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ) -
        (ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ)
          (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ = ν := by
  have h2 := hθ.apply_restrictedCoroot h𝔞.le_cartanP hμ
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, h2, smul_eq_mul]
  module

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
  rwa [sub_smul_sub_smul_eq hθ h𝔞 (Submodule.mem_restrictedRoots.mp hμ).1] at h

/-- **Reflections permute the restricted roots**: if `λ` and `ν` are restricted roots, so is
`s_λ ν = ν - ν(H'_λ) λ`. -/
theorem sub_smul_mem_restrictedRoots {μ ν : Dual ℝ 𝔞} (hμ : μ ∈ 𝔞.restrictedRoots)
    (hν : ν ∈ 𝔞.restrictedRoots) :
    ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ ∈ 𝔞.restrictedRoots := by
  have := hθ.finiteDimensional
  obtain ⟨hν0, hνsp⟩ := Submodule.mem_restrictedRoots.mp hν
  refine Submodule.mem_restrictedRoots.mpr ⟨fun h ↦ hν0 ?_, fun h ↦ hνsp ?_⟩
  · rw [← hθ.sub_smul_sub_smul_eq h𝔞 (Submodule.mem_restrictedRoots.mp hμ).1 ν, h]
    simp
  · rw [← Submodule.finrank_eq_zero, ← hθ.finrank_restrictedRootSpace_sub_smul h𝔞 hμ ν, h,
      finrank_bot]

end LieEquiv.IsCartanInvolution
