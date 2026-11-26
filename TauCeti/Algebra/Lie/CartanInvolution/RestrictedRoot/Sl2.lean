/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Vector
public import TauCeti.Algebra.Lie.Sl2.Spectrum
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Reflection

/-!
# The `𝔰𝔩₂` triple of a restricted root and integrality

Let `θ` be a Cartan involution of a Lie algebra `𝔤₀` over an ordered field `K`, `𝔞` a maximal
abelian subspace of its `-1`-eigenspace `𝔭`, and `λ` a restricted root of `(𝔤₀, 𝔞)`. With
`H_λ ∈ 𝔞` the vector representing `λ` under the Killing form `B` on `𝔞`
(`LieEquiv.IsCartanInvolution.killingEquivDual`), the *restricted coroot* is
`H'_λ = 2 H_λ / λ(H_λ) = 2 H_λ / B(H_λ, H_λ)`, so that `λ(H'_λ) = 2`.

For nonzero `E ∈ 𝔤_λ`, `B(E, θE) < 0`, `[E, θE] = B(E, θE) H_λ`, and `θE ∈ 𝔤_{-λ}`, so
`(H'_λ, E, c θE)` with `c = 2 / (B(E, θE) λ(H_λ))` is an `𝔰𝔩₂` triple
(`LieEquiv.IsCartanInvolution.isSl2Triple_restrictedCoroot`). Over `ℝ`, rescaling `E` to
`E' = √(-c) E` gives the triple `(H'_λ, E', -θE')` used to realize the reflection `s_λ` inside
`K_θ` (Knapp, Ch. VI, Prop. 6.52; `LieEquiv.IsCartanInvolution.exists_isSl2Triple_neg_apply`).

The adjoint action of this triple on the finite-dimensional `𝔤₀` has integer `H'_λ`-eigenvalues,
so `ν(H'_λ) ∈ ℤ` whenever `𝔤_ν ≠ 0`
(`LieEquiv.IsCartanInvolution.exists_int_apply_restrictedCoroot`): the restricted roots are
crystallographic for the pairing with the coroots. Applying this to `λ` and `cλ` in both
directions, the multiples of a restricted root that are restricted roots are among `±λ/2`, `±λ`,
`±2λ` (`LieEquiv.IsCartanInvolution.mem_of_smul_mem_restrictedRoots`).

## Main definitions

* `LieEquiv.IsCartanInvolution.restrictedCoroot`: the coroot `H'_λ = 2 H_λ / λ(H_λ)` in `𝔞`.

## Main results

* `LieEquiv.IsCartanInvolution.apply_restrictedCoroot`: `λ(H'_λ) = 2` for `λ ≠ 0`.
* `LieEquiv.IsCartanInvolution.restrictedCoroot_injective`: distinct functionals have distinct
  coroots.
* `LieEquiv.IsCartanInvolution.isSl2Triple_restrictedCoroot`: `(H'_λ, E, c θE)` is an `𝔰𝔩₂`
  triple for nonzero `E ∈ 𝔤_λ`.
* `LieEquiv.IsCartanInvolution.exists_isSl2Triple_restrictedCoroot`: some `F ∈ 𝔤_{-λ}` completes
  `(H'_λ, E)` to an `𝔰𝔩₂` triple.
* `LieEquiv.IsCartanInvolution.exists_isSl2Triple_neg_apply`: over `ℝ`, a positive multiple `E'`
  of `E` gives the `𝔰𝔩₂` triple `(H'_λ, E', -θE')`.
* `LieEquiv.IsCartanInvolution.exists_int_apply_restrictedCoroot`: `ν(H'_λ) ∈ ℤ` for every `ν`
  with `𝔤_ν ≠ 0`.
* `LieEquiv.IsCartanInvolution.mem_of_smul_mem_restrictedRoots`: if `λ` and `cλ` are restricted
  roots, then `c ∈ {±1/2, ±1, ±2}`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4, Proposition 6.52.
-/

public section

open LieAlgebra LieModule Module

namespace LieEquiv.IsCartanInvolution

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L} {𝔞 : Submodule K L}

/-! ### The restricted coroot -/

section Coroot

variable (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)

/-- The **restricted coroot** `H'_λ = 2 H_λ / λ(H_λ)` of a functional `λ` on `𝔞`, where `H_λ ∈ 𝔞`
represents `λ` under the Killing form (`LieEquiv.IsCartanInvolution.killingEquivDual`). Since
`λ(H_λ) = B(H_λ, H_λ)`, this is `2 H_λ / B(H_λ, H_λ)`. -/
noncomputable def restrictedCoroot (μ : Dual K 𝔞) : 𝔞 :=
  (2 / μ ((hθ.killingEquivDual h𝔞).symm μ)) • (hθ.killingEquivDual h𝔞).symm μ

theorem restrictedCoroot_def (μ : Dual K 𝔞) :
    hθ.restrictedCoroot h𝔞 μ =
      (2 / μ ((hθ.killingEquivDual h𝔞).symm μ)) • (hθ.killingEquivDual h𝔞).symm μ :=
  (rfl)

/-- **`λ(H'_λ) = 2`** for `λ ≠ 0`. -/
@[simp]
theorem apply_restrictedCoroot {μ : Dual K 𝔞} (hμ : μ ≠ 0) :
    μ (hθ.restrictedCoroot h𝔞 μ) = 2 := by
  rw [restrictedCoroot_def, map_smul, smul_eq_mul,
    div_mul_cancel₀ _ (hθ.apply_killingEquivDual_symm_pos h𝔞 hμ).ne']

/-- The reflection `s_λ ν = ν - ν(H'_λ) λ` is an involution of `𝔞*`: `s_λ (s_λ ν) = ν`. This is
Mathlib's `Module.involutive_reflection` for the reflection in `λ` along evaluation at `H'_λ`. -/
theorem sub_smul_sub_smul_restrictedCoroot {μ : Dual K 𝔞} (hμ : μ ≠ 0) (ν : Dual K 𝔞) :
    (ν - ν (hθ.restrictedCoroot h𝔞 μ) • μ) -
        (ν - ν (hθ.restrictedCoroot h𝔞 μ) • μ) (hθ.restrictedCoroot h𝔞 μ) • μ = ν := by
  have h2 : Dual.eval K 𝔞 (hθ.restrictedCoroot h𝔞 μ) μ = 2 := by
    simpa only [Dual.eval_apply] using hθ.apply_restrictedCoroot h𝔞 hμ
  simpa only [reflection_apply, Dual.eval_apply] using involutive_reflection h2 ν

/-- The restricted coroot of a nonzero functional is nonzero. -/
theorem restrictedCoroot_ne_zero {μ : Dual K 𝔞} (hμ : μ ≠ 0) :
    hθ.restrictedCoroot h𝔞 μ ≠ 0 := by
  intro h
  have := hθ.apply_restrictedCoroot h𝔞 hμ
  rw [h, map_zero] at this
  exact two_ne_zero this.symm

/-- The restricted coroot of `cλ` is `c⁻¹ H'_λ`. -/
@[simp]
theorem restrictedCoroot_smul (μ : Dual K 𝔞) (c : K) :
    hθ.restrictedCoroot h𝔞 (c • μ) = c⁻¹ • hθ.restrictedCoroot h𝔞 μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [restrictedCoroot_def]
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp [restrictedCoroot_def]
  have hpos := (hθ.apply_killingEquivDual_symm_pos h𝔞 hμ).ne'
  simp only [restrictedCoroot_def, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  field_simp

/-- The restricted coroot of `-λ` is `-H'_λ`. -/
@[simp]
theorem restrictedCoroot_neg (μ : Dual K 𝔞) :
    hθ.restrictedCoroot h𝔞 (-μ) = -hθ.restrictedCoroot h𝔞 μ := by
  rw [← neg_one_smul K μ, restrictedCoroot_smul, inv_neg, inv_one, neg_one_smul]

/-- A functional is recovered from its coroot: `λ = (2 / B(H'_λ, H'_λ)) B(H'_λ, ·)`. -/
theorem eq_smul_killingEquivDual_restrictedCoroot (μ : Dual K 𝔞) :
    μ = (2 / killingForm K L (hθ.restrictedCoroot h𝔞 μ) (hθ.restrictedCoroot h𝔞 μ)) •
      hθ.killingEquivDual h𝔞 (hθ.restrictedCoroot h𝔞 μ) := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp [restrictedCoroot_def]
  have hm := (hθ.apply_killingEquivDual_symm_pos h𝔞 hμ).ne'
  rw [← hθ.killingEquivDual_apply_apply h𝔞]
  simp only [restrictedCoroot_def, map_smul, LinearEquiv.apply_symm_apply, LinearMap.smul_apply,
    smul_eq_mul, smul_smul]
  conv_lhs => rw [← one_smul K μ]
  congr 1
  field_simp

/-- **Distinct functionals have distinct coroots.** -/
theorem restrictedCoroot_injective : Function.Injective (hθ.restrictedCoroot h𝔞) :=
  fun μ ν h ↦ by
    rw [hθ.eq_smul_killingEquivDual_restrictedCoroot h𝔞 μ,
      hθ.eq_smul_killingEquivDual_restrictedCoroot h𝔞 ν, h]

/-- On the restricted root space `𝔤_ν`, the coroot `H'_λ` acts by `ν(H'_λ)`. -/
theorem restrictedCoroot_lie_eq_smul_of_mem_restrictedRootSpace {ν : Dual K 𝔞} (μ : Dual K 𝔞)
    {x : L} (hx : x ∈ 𝔞.restrictedRootSpace ν) :
    ⁅(hθ.restrictedCoroot h𝔞 μ : L), x⁆ =
      ν (hθ.restrictedCoroot h𝔞 μ) • x :=
  Submodule.mem_restrictedRootSpace.mp hx _

end Coroot

/-! ### The `𝔰𝔩₂` triple of a restricted root -/

section Sl2

variable (hθ : θ.IsCartanInvolution) (h𝔞 : θ.IsMaximalAbelianInP 𝔞)

/-- **The `𝔰𝔩₂` triple of a restricted root.** For a nonzero `E` in the root space `𝔤_λ` of a
nonzero `λ`, `(H'_λ, E, c θE)` with `c = 2 / (B(E, θE) λ(H_λ))` is an `𝔰𝔩₂` triple
(Knapp, Prop. 6.52). -/
theorem isSl2Triple_restrictedCoroot {μ : Dual K 𝔞} (hμ : μ ≠ 0) {E : L}
    (hE : E ∈ 𝔞.restrictedRootSpace μ) (hE0 : E ≠ 0) :
    IsSl2Triple (hθ.restrictedCoroot h𝔞.le_cartanP μ : L) E
      ((2 / (killingForm K L E (θ E) *
        μ ((hθ.killingEquivDual h𝔞.le_cartanP).symm μ))) • θ E) := by
  have hB := (hθ.killingForm_apply_apply_neg hE0).ne
  have hpos := (hθ.apply_killingEquivDual_symm_pos h𝔞.le_cartanP hμ).ne'
  have hθE := apply_mem_restrictedRootSpace_neg h𝔞.le_cartanP hE
  have h2 := hθ.apply_restrictedCoroot h𝔞.le_cartanP hμ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hθ.restrictedCoroot_ne_zero h𝔞.le_cartanP hμ
  · rw [lie_smul, hθ.lie_apply_eq_smul_killingEquivDual_symm h𝔞 hE, smul_smul,
      restrictedCoroot_def, Submodule.coe_smul]
    congr 1
    field_simp
  · rw [hθ.restrictedCoroot_lie_eq_smul_of_mem_restrictedRootSpace h𝔞.le_cartanP μ hE, h2,
      two_smul, two_nsmul]
  · rw [lie_smul,
      hθ.restrictedCoroot_lie_eq_smul_of_mem_restrictedRootSpace h𝔞.le_cartanP μ hθE]
    simp only [LinearMap.neg_apply, h2, two_nsmul]
    module

/-- For a nonzero `E` in the root space `𝔤_λ` of a nonzero `λ`, some `F ∈ 𝔤_{-λ}` completes
`(H'_λ, E)` to an `𝔰𝔩₂` triple. -/
theorem exists_isSl2Triple_restrictedCoroot {μ : Dual K 𝔞} (hμ : μ ≠ 0) {E : L}
    (hE : E ∈ 𝔞.restrictedRootSpace μ) (hE0 : E ≠ 0) :
    ∃ F ∈ 𝔞.restrictedRootSpace (-μ),
      IsSl2Triple (hθ.restrictedCoroot h𝔞.le_cartanP μ : L) E F :=
  ⟨_, Submodule.smul_mem _ _ (apply_mem_restrictedRootSpace_neg h𝔞.le_cartanP hE),
    hθ.isSl2Triple_restrictedCoroot h𝔞 hμ hE hE0⟩

/-- **The symmetric `𝔰𝔩₂` triple of a restricted root**, over `ℝ`: for a nonzero `E ∈ 𝔤_λ`,
`λ ≠ 0`, some positive multiple `E'` of `E` gives the `𝔰𝔩₂` triple `(H'_λ, E', -θE')`
(Knapp, Prop. 6.52). -/
theorem exists_isSl2Triple_neg_apply {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L} (hθ : θ.IsCartanInvolution)
    (h𝔞 : θ.IsMaximalAbelianInP 𝔞) {μ : Dual ℝ 𝔞} (hμ : μ ≠ 0) {E : L}
    (hE : E ∈ 𝔞.restrictedRootSpace μ) (hE0 : E ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      IsSl2Triple (hθ.restrictedCoroot h𝔞.le_cartanP μ : L) (c • E) (-θ (c • E)) := by
  set a := killingForm ℝ L E (θ E) * μ ((hθ.killingEquivDual h𝔞.le_cartanP).symm μ)
  have ha : a < 0 := mul_neg_of_neg_of_pos (hθ.killingForm_apply_apply_neg hE0)
    (hθ.apply_killingEquivDual_symm_pos h𝔞.le_cartanP hμ)
  have hpos : 0 < -2 / a := div_pos_of_neg_of_neg (by norm_num) ha
  set c := Real.sqrt (-2 / a)
  have hc : 0 < c := Real.sqrt_pos.mpr hpos
  have hsq : c * c = -2 / a := Real.mul_self_sqrt hpos.le
  have t := hθ.isSl2Triple_restrictedCoroot h𝔞 hμ (Submodule.smul_mem _ c hE)
    (smul_ne_zero hc.ne' hE0)
  have hcoef : 2 / (killingForm ℝ L (c • E) (θ (c • E)) *
      μ ((hθ.killingEquivDual h𝔞.le_cartanP).symm μ)) = -1 := by
    have : killingForm ℝ L (c • E) (θ (c • E)) *
        μ ((hθ.killingEquivDual h𝔞.le_cartanP).symm μ) = c * c * a := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, a]
      ring
    rw [this, hsq, div_mul_cancel₀ _ ha.ne]
    norm_num
  rw [hcoef, neg_one_smul] at t
  exact ⟨c, hc, t⟩

/-! ### Integrality -/

/-- **Integrality of restricted roots.** If `λ` is a restricted root and `𝔤_ν ≠ 0`, then
`ν(H'_λ)` is an integer: the `H'_λ`-eigenvalues of the adjoint action of the `𝔰𝔩₂` triple of `λ`
on the finite-dimensional `𝔤₀` are integers. -/
theorem exists_int_apply_restrictedCoroot {μ ν : Dual K 𝔞} (hμ : μ ∈ 𝔞.restrictedRoots)
    (hν : 𝔞.restrictedRootSpace ν ≠ ⊥) :
    ∃ z : ℤ, ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) = z := by
  have := hθ.finiteDimensional
  obtain ⟨hμ0, hμsp⟩ := Submodule.mem_restrictedRoots.mp hμ
  obtain ⟨E, hE, hE0⟩ := (Submodule.ne_bot_iff _).mp hμsp
  obtain ⟨X, hX, hX0⟩ := (Submodule.ne_bot_iff _).mp hν
  exact TauCeti.exists_int_of_lie_h_eq_smul (M := L)
    (hθ.isSl2Triple_restrictedCoroot h𝔞 hμ0 hE hE0)
    (hθ.restrictedCoroot_lie_eq_smul_of_mem_restrictedRootSpace h𝔞.le_cartanP μ hX) hX0

include hθ h𝔞 in
/-- **The multiples of a restricted root.** If `λ` and `cλ` are restricted roots, then
`c ∈ {±1/2, ±1, ±2}`: both `(cλ)(H'_λ) = 2c` and `λ(H'_{cλ}) = 2/c` are integers. -/
theorem mem_of_smul_mem_restrictedRoots {μ : Dual K 𝔞} (hμ : μ ∈ 𝔞.restrictedRoots) {c : K}
    (hc : c • μ ∈ 𝔞.restrictedRoots) :
    c ∈ ({1 / 2, -(1 / 2), 1, -1, 2, -2} : Set K) := by
  have hμ0 := (Submodule.mem_restrictedRoots.mp hμ).1
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (Submodule.mem_restrictedRoots.mp hc).1 (zero_smul K μ)
  have hsp := (Submodule.mem_restrictedRoots.mp hμ).2
  have hcsp := (Submodule.mem_restrictedRoots.mp hc).2
  obtain ⟨a, ha⟩ := hθ.exists_int_apply_restrictedCoroot h𝔞 hμ hcsp
  obtain ⟨b, hb⟩ := hθ.exists_int_apply_restrictedCoroot h𝔞 hc hsp
  rw [LinearMap.smul_apply, hθ.apply_restrictedCoroot h𝔞.le_cartanP hμ0, smul_eq_mul] at ha
  rw [hθ.restrictedCoroot_smul h𝔞.le_cartanP μ c, map_smul,
    hθ.apply_restrictedCoroot h𝔞.le_cartanP hμ0, smul_eq_mul] at hb
  have hab : (a : K) * b = 4 := by
    rw [← ha, ← hb]
    field_simp
    norm_num
  have hab' : a * b = 4 := by exact_mod_cast hab
  have hdvd : a.natAbs ∣ 4 := by
    have := Int.natAbs_dvd_natAbs.mpr ⟨b, hab'.symm⟩
    simpa using this
  have hle : a.natAbs ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hcA : c = (a : K) / 2 := by rw [ha.symm]; ring
  have hcases : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2 ∨ a = 4 ∨ a = -4 := by
    interval_cases h : a.natAbs <;> omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [hcA]

end Sl2

end LieEquiv.IsCartanInvolution
