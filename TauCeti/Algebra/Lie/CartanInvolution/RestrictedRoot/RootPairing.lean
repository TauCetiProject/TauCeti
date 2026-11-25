/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Reflection
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import Mathlib.LinearAlgebra.RootSystem.Basic

/-!
# The restricted root pairing

Let `θ` be a Cartan involution of a real Lie algebra `𝔤₀` and `𝔞` a maximal abelian subspace of
its `-1`-eigenspace `𝔭`. The restricted roots `Σ ⊆ 𝔞*`, with the coroots
`H'_λ = 2 H_λ / B(H_λ, H_λ)` (`LieEquiv.IsCartanInvolution.restrictedCoroot`), form a
crystallographic root system for the evaluation pairing of `𝔞*` with `𝔞`, possibly nonreduced
(Knapp, Ch. VI, §5; Helgason, Ch. VII, §2). This is the `RootPairing` packaging of the restricted
root system (`LieEquiv.IsCartanInvolution.restrictedRootPairing`).

The ingredients are:

* the reflections `s_λ ν = ν - ν(H'_λ) λ` permute `Σ`
  (`LieEquiv.IsCartanInvolution.sub_smul_mem_restrictedRoots`);
* the coroots are compatible with the reflections, `H'_{s_λ ν} = H'_ν - λ(H'_ν) H'_λ`
  (`LieEquiv.IsCartanInvolution.restrictedCoroot_sub_smul`), since `H ↦ H - λ(H) H'_λ` is the
  `B`-orthogonal reflection of `𝔞` in `H_λ`
  (`LieEquiv.IsCartanInvolution.killingForm_reflection_restrictedCoroot`);
* the pairings `ν(H'_λ)` are integers
  (`LieEquiv.IsCartanInvolution.exists_int_apply_restrictedCoroot`);
* the roots span `𝔞*`: an `H ∈ 𝔞` on which every restricted root vanishes acts by `0` on every
  restricted root space, hence is central, hence `B(H, H) = 0` and `H = 0`
  (`LieEquiv.IsCartanInvolution.span_restrictedRoots_eq_top`).

## Main definitions

* `LieEquiv.IsCartanInvolution.restrictedRootPairing`: the restricted root pairing, a
  `RootPairing` indexed by `Σ` on `(𝔞*, 𝔞)`.

## Main results

* `LieEquiv.IsCartanInvolution.restrictedCoroot_sub_smul`: `H'_{s_λ ν} = H'_ν - λ(H'_ν) H'_λ`.
* `LieEquiv.IsCartanInvolution.restrictedCoroot_injective`: distinct functionals have distinct
  coroots.
* `LieEquiv.IsCartanInvolution.span_restrictedRoots_eq_top`: the restricted roots span `𝔞*`.
* `LieEquiv.IsCartanInvolution.isCrystallographic_restrictedRootPairing`,
  `LieEquiv.IsCartanInvolution.isRootSystem_restrictedRootPairing`: the restricted root pairing
  is crystallographic and a root system.
* `LieEquiv.IsCartanInvolution.exists_restrictedRootPairing`: the roadmap's existence form.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §5.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter VII, §2.
-/

public section

open LieAlgebra LieModule Module Set

namespace LieEquiv.IsCartanInvolution

/-! ### Compatibility of the coroots with the reflections -/

section Coroot

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L} {𝔞 : Submodule K L}
  (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)

/-- `ν(H_λ) = λ(H_ν)`: both are `B(H_λ, H_ν)`. -/
theorem apply_killingEquivDual_symm_comm (μ ν : Dual K 𝔞) :
    ν ((hθ.killingEquivDual h𝔞).symm μ) = μ ((hθ.killingEquivDual h𝔞).symm ν) := by
  rw [← hθ.killingForm_killingEquivDual_symm h𝔞 ν,
    ← hθ.killingForm_killingEquivDual_symm h𝔞 μ, traceForm_comm]

/-- The reflection `H ↦ H - λ(H) H'_λ` of `𝔞` is orthogonal for the Killing form. -/
theorem killingForm_reflection_restrictedCoroot (μ : Dual K 𝔞) (H H' : 𝔞) :
    killingForm K L (H - μ H • hθ.restrictedCoroot h𝔞 μ : 𝔞)
        (H' - μ H' • hθ.restrictedCoroot h𝔞 μ : 𝔞) =
      killingForm K L H H' := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  have hm := (hθ.apply_killingEquivDual_symm_pos h𝔞 hμ).ne'
  have hB (X : 𝔞) : killingForm K L ((hθ.killingEquivDual h𝔞).symm μ : L) X = μ X :=
    hθ.killingForm_killingEquivDual_symm h𝔞 μ X
  have hB' (X : 𝔞) : killingForm K L (X : L) ((hθ.killingEquivDual h𝔞).symm μ : L) = μ X := by
    rw [traceForm_comm, hB]
  simp only [restrictedCoroot_def, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hB, hB']
  field_simp
  ring

/-- `H_{s_λ ν} = H_ν - λ(H_ν) H'_λ`: the vector representing `s_λ ν` is the orthogonal
reflection of the vector representing `ν`. -/
theorem killingEquivDual_symm_sub_smul (μ ν : Dual K 𝔞) :
    (hθ.killingEquivDual h𝔞).symm (ν - ν (hθ.restrictedCoroot h𝔞 μ) • μ) =
      (hθ.killingEquivDual h𝔞).symm ν -
        μ ((hθ.killingEquivDual h𝔞).symm ν) • hθ.restrictedCoroot h𝔞 μ := by
  rw [map_sub, map_smul, restrictedCoroot_def, map_smul, smul_eq_mul,
    hθ.apply_killingEquivDual_symm_comm h𝔞 μ ν, smul_smul]
  congr 2
  ring

/-- **Compatibility of the coroots with the reflections.** The coroot of
`s_λ ν = ν - ν(H'_λ) λ` is `H'_ν - λ(H'_ν) H'_λ`. -/
theorem restrictedCoroot_sub_smul (μ ν : Dual K 𝔞) :
    hθ.restrictedCoroot h𝔞 (ν - ν (hθ.restrictedCoroot h𝔞 μ) • μ) =
      hθ.restrictedCoroot h𝔞 ν - μ (hθ.restrictedCoroot h𝔞 ν) • hθ.restrictedCoroot h𝔞 μ := by
  -- `s_λ ν (H_{s_λ ν}) = B(H_{s_λ ν}, H_{s_λ ν}) = B(H_ν, H_ν) = ν(H_ν)`.
  have hval : (ν - ν (hθ.restrictedCoroot h𝔞 μ) • μ)
      ((hθ.killingEquivDual h𝔞).symm (ν - ν (hθ.restrictedCoroot h𝔞 μ) • μ)) =
        ν ((hθ.killingEquivDual h𝔞).symm ν) := by
    rw [← hθ.killingForm_killingEquivDual_symm h𝔞,
      hθ.killingEquivDual_symm_sub_smul h𝔞 μ ν, hθ.killingForm_reflection_restrictedCoroot h𝔞 μ,
      hθ.killingForm_killingEquivDual_symm h𝔞]
  rw [restrictedCoroot_def, hval, hθ.killingEquivDual_symm_sub_smul h𝔞 μ ν,
    hθ.restrictedCoroot_def h𝔞 ν, map_smul, smul_eq_mul, smul_sub, smul_smul]

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

end Coroot

/-! ### The restricted root pairing -/

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}
  (hθ : θ.IsCartanInvolution) (h𝔞 : θ.IsMaximalAbelianInP 𝔞)

include hθ h𝔞 in
/-- An element of `𝔞` on which every restricted root vanishes is zero. -/
theorem eq_zero_of_forall_restrictedRoots_apply_eq_zero {H : 𝔞}
    (hH : ∀ μ ∈ 𝔞.restrictedRoots, μ H = 0) : H = 0 := by
  have hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0 := fun _ hx _ hy ↦ h𝔞.lie_eq_zero hx hy
  have had : toEnd ℝ L L (H : L) = 0 := by
    ext x
    have hx : x ∈ ⨆ μ : Dual ℝ 𝔞, 𝔞.restrictedRootSpace μ := by
      rw [hθ.iSup_restrictedRootSpace_eq_top h𝔞.le_cartanP hab]
      exact Submodule.mem_top
    rw [LinearMap.zero_apply, toEnd_apply_apply]
    induction hx using Submodule.iSup_induction' with
    | mem ν y hy =>
      rw [Submodule.mem_restrictedRootSpace.mp hy H]
      by_cases hν : ν = 0
      · simp [hν]
      by_cases hbot : 𝔞.restrictedRootSpace ν = ⊥
      · rw [hbot, Submodule.mem_bot] at hy
        simp [hy]
      rw [hH ν (Submodule.mem_restrictedRoots.mpr ⟨hν, hbot⟩), zero_smul]
    | zero => exact lie_zero _
    | add y z _ _ hy hz => rw [lie_add, hy, hz, add_zero]
  by_contra hne
  have hpos := hθ.killingForm_apply_self_pos_of_mem_cartanP (h𝔞.le_cartanP H.property)
    (Submodule.coe_eq_zero.not.mpr hne)
  rw [traceForm_apply_apply, had, LinearMap.zero_comp, map_zero] at hpos
  exact lt_irrefl _ hpos

include hθ h𝔞 in
/-- **The restricted roots span `𝔞*`.** -/
theorem span_restrictedRoots_eq_top : Submodule.span ℝ 𝔞.restrictedRoots = ⊤ := by
  have := hθ.finiteDimensional
  apply Submodule.eq_top_of_finrank_eq
  have hco : (Submodule.span ℝ 𝔞.restrictedRoots).dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun H hH ↦ ?_
    rw [Submodule.mem_dualCoannihilator] at hH
    exact hθ.eq_zero_of_forall_restrictedRoots_apply_eq_zero h𝔞 fun μ hμ ↦
      hH μ (Submodule.subset_span hμ)
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span ℝ 𝔞.restrictedRoots)
  rw [hco, finrank_bot, add_zero] at h
  rw [h, Subspace.dual_finrank_eq]

include hθ in
variable (𝔞) in
/-- The restricted roots form a finite set. -/
theorem finite_restrictedRoots : 𝔞.restrictedRoots.Finite :=
  have := hθ.finiteDimensional
  Submodule.finite_restrictedRoots

/-- The coroot map restricted to the restricted roots, as an embedding. -/
@[expose] noncomputable def restrictedCorootEmbedding : 𝔞.restrictedRoots ↪ 𝔞 where
  toFun μ := hθ.restrictedCoroot h𝔞.le_cartanP μ
  inj' _ _ h := Subtype.ext <| hθ.restrictedCoroot_injective h𝔞.le_cartanP h

/-- **The restricted root pairing.** For a Cartan involution `θ` of a real Lie algebra and a
maximal abelian subspace `𝔞` of `𝔭`, the root pairing indexed by the restricted roots `Σ`, on
`(𝔞*, 𝔞)` with the evaluation pairing, with roots `λ` and coroots
`H'_λ = 2 H_λ / B(H_λ, H_λ)`. -/
@[expose] noncomputable def restrictedRootPairing : RootPairing 𝔞.restrictedRoots ℝ (Dual ℝ 𝔞) 𝔞 :=
  have := hθ.finiteDimensional
  have : Finite 𝔞.restrictedRoots := (hθ.finite_restrictedRoots 𝔞).to_subtype
  RootPairing.mk' LinearMap.id (Function.Embedding.subtype _)
    (hθ.restrictedCorootEmbedding h𝔞)
    (fun μ ↦ hθ.apply_restrictedCoroot h𝔞.le_cartanP
      (Submodule.mem_restrictedRoots.mp μ.property).1)
    (by
      rintro μ - ⟨ν, rfl⟩
      exact ⟨⟨_, hθ.sub_smul_mem_restrictedRoots h𝔞 μ.property ν.property⟩, by
        simp [preReflection_apply]; rfl⟩)
    (by
      rintro μ - ⟨ν, rfl⟩
      refine ⟨⟨_, hθ.sub_smul_mem_restrictedRoots h𝔞 μ.property ν.property⟩, ?_⟩
      simp only [restrictedCorootEmbedding, preReflection_apply, LinearMap.id_apply]
      exact hθ.restrictedCoroot_sub_smul h𝔞.le_cartanP μ ν)

@[simp]
theorem restrictedRootPairing_toLinearMap_apply (f : Dual ℝ 𝔞) (H : 𝔞) :
    (hθ.restrictedRootPairing h𝔞).toLinearMap f H = f H :=
  rfl

@[simp]
theorem restrictedRootPairing_root (μ : 𝔞.restrictedRoots) :
    (hθ.restrictedRootPairing h𝔞).root μ = μ :=
  rfl

@[simp]
theorem restrictedRootPairing_coroot (μ : 𝔞.restrictedRoots) :
    (hθ.restrictedRootPairing h𝔞).coroot μ = hθ.restrictedCoroot h𝔞.le_cartanP μ :=
  rfl

/-- The pairing of `λ` with the coroot of `μ` is `λ(H'_μ)`. -/
theorem restrictedRootPairing_pairing (μ ν : 𝔞.restrictedRoots) :
    (hθ.restrictedRootPairing h𝔞).pairing μ ν =
      (μ : Dual ℝ 𝔞) (hθ.restrictedCoroot h𝔞.le_cartanP ν) :=
  rfl

/-- **The restricted root pairing is crystallographic**: `λ(H'_μ) ∈ ℤ`. -/
theorem isCrystallographic_restrictedRootPairing :
    (hθ.restrictedRootPairing h𝔞).IsCrystallographic := by
  refine ⟨fun μ ν ↦ ?_⟩
  obtain ⟨z, hz⟩ := hθ.exists_int_apply_restrictedCoroot h𝔞 ν.property
    (Submodule.mem_restrictedRoots.mp μ.property).2
  exact ⟨z, by rw [restrictedRootPairing_pairing, hz, algebraMap_int_eq, Int.coe_castRingHom]⟩

/-- **The restricted root pairing is a root system**: the roots span `𝔞*` and the coroots span
`𝔞`. -/
theorem isRootSystem_restrictedRootPairing :
    (hθ.restrictedRootPairing h𝔞).IsRootSystem := by
  have := hθ.finiteDimensional
  have : Fintype 𝔞.restrictedRoots := (hθ.finite_restrictedRoots 𝔞).fintype
  have := hθ.isCrystallographic_restrictedRootPairing h𝔞
  have hroot : (hθ.restrictedRootPairing h𝔞).rootSpan ℝ = ⊤ := by
    simp only [RootPairing.rootSpan, restrictedRootPairing, RootPairing.mk']
    rw [Function.Embedding.coe_subtype, Subtype.range_coe]
    exact hθ.span_restrictedRoots_eq_top h𝔞
  exact ⟨hroot, (RootPairing.rootSpan_eq_top_iff _).mp hroot⟩

include hθ h𝔞 in
/-- **The restricted root system** (roadmap form, §1.2): the restricted roots of a Cartan
involution of a real Lie algebra form a crystallographic root system, possibly nonreduced, for the
evaluation pairing of `𝔞*` with `𝔞`. -/
theorem exists_restrictedRootPairing :
    ∃ P : RootPairing 𝔞.restrictedRoots ℝ (Dual ℝ 𝔞) 𝔞,
      (∀ (f : Dual ℝ 𝔞) (x : 𝔞), P.toLinearMap f x = f x) ∧
      (∀ i, P.root i = (i : Dual ℝ 𝔞)) ∧ P.IsCrystallographic ∧ P.IsRootSystem :=
  ⟨hθ.restrictedRootPairing h𝔞, fun _ _ ↦ rfl, fun _ ↦ rfl,
    hθ.isCrystallographic_restrictedRootPairing h𝔞, hθ.isRootSystem_restrictedRootPairing h𝔞⟩

end LieEquiv.IsCartanInvolution
