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
(Knapp, Ch. VI, §4, Corollary 6.53; Helgason, Ch. VII, §2). This is the `RootPairing` packaging
of the restricted root system (`LieEquiv.IsCartanInvolution.restrictedRootPairing`).

The ingredients are:

* the reflections `s_λ ν = ν - ν(H'_λ) λ` permute `Σ`
  (`LieEquiv.IsCartanInvolution.sub_smul_mem_restrictedRoots`);
* the pairings `ν(H'_λ)` are integers
  (`LieEquiv.IsCartanInvolution.exists_int_apply_restrictedCoroot`);
* the roots span `𝔞*`: an `H ∈ 𝔞` on which every restricted root vanishes acts by `0` on every
  restricted root space, hence is central, hence `B(H, H) = 0` and `H = 0`
  (`LieEquiv.IsCartanInvolution.span_restrictedRoots_eq_top`).

Over a field of characteristic zero, these imply that the coroots are compatible with the
reflections and span `𝔞` (`RootPairing.mk''`, `RootPairing.isRootSystem_mk''`).

## Main definitions

* `LieEquiv.IsCartanInvolution.restrictedRootPairing`: the restricted root pairing, a
  `RootPairing` indexed by `Σ` on `(𝔞*, 𝔞)`.

## Main results

* `LieEquiv.IsCartanInvolution.span_restrictedRoots_eq_top`: the restricted roots of an abelian
  subspace of `𝔭` span `𝔞*`.
* `LieEquiv.IsCartanInvolution.isCrystallographic_restrictedRootPairing`,
  `LieEquiv.IsCartanInvolution.isRootSystem_restrictedRootPairing`: the restricted root pairing
  is crystallographic and a root system.
* `LieEquiv.IsCartanInvolution.exists_restrictedRootPairing`: the restricted roots carry a
  crystallographic root system structure for the evaluation pairing of `𝔞*` with `𝔞`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4, Corollary 6.53.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter VII, §2.
-/

public section

open LieAlgebra LieModule Module Set

namespace LieEquiv.IsCartanInvolution

/-! ### Finiteness of the roots and the coroot embedding -/

section Coroot

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L} {𝔞 : Submodule K L}
  (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)

include hθ in
variable (𝔞) in
/-- The restricted roots form a finite set. -/
theorem finite_restrictedRoots : 𝔞.restrictedRoots.Finite :=
  have := hθ.finiteDimensional
  Submodule.finite_restrictedRoots

/-- The coroot map restricted to the restricted roots, as an embedding. -/
noncomputable def restrictedCorootEmbedding : 𝔞.restrictedRoots ↪ 𝔞 where
  toFun μ := hθ.restrictedCoroot h𝔞 μ
  inj' _ _ h := Subtype.ext <| hθ.restrictedCoroot_injective h𝔞 h

@[simp]
theorem restrictedCorootEmbedding_apply (μ : 𝔞.restrictedRoots) :
    hθ.restrictedCorootEmbedding h𝔞 μ = hθ.restrictedCoroot h𝔞 μ :=
  (rfl)

end Coroot

/-! ### The restricted roots span -/

section Span

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}
  (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP) (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0)

include hθ h𝔞 hab in
/-- An element of an abelian subspace `𝔞 ⊆ 𝔭` on which every restricted root vanishes is zero. -/
theorem eq_zero_of_forall_restrictedRoots_apply_eq_zero {H : 𝔞}
    (hH : ∀ μ ∈ 𝔞.restrictedRoots, μ H = 0) : H = 0 := by
  have had : toEnd ℝ L L (H : L) = 0 := by
    ext x
    have hx : x ∈ ⨆ μ : Dual ℝ 𝔞, 𝔞.restrictedRootSpace μ := by
      rw [hθ.iSup_restrictedRootSpace_eq_top h𝔞 hab]
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
  have hpos := hθ.killingForm_apply_self_pos_of_mem_cartanP (h𝔞 H.property)
    (Submodule.coe_eq_zero.not.mpr hne)
  rw [traceForm_apply_apply, had, LinearMap.zero_comp, map_zero] at hpos
  exact lt_irrefl _ hpos

include hθ h𝔞 hab in
/-- **The restricted roots span `𝔞*`** for an abelian subspace `𝔞` of `𝔭`. -/
theorem span_restrictedRoots_eq_top : Submodule.span ℝ 𝔞.restrictedRoots = ⊤ := by
  have := hθ.finiteDimensional
  apply Submodule.eq_top_of_finrank_eq
  have hco : (Submodule.span ℝ 𝔞.restrictedRoots).dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun H hH ↦ ?_
    rw [Submodule.mem_dualCoannihilator] at hH
    exact hθ.eq_zero_of_forall_restrictedRoots_apply_eq_zero h𝔞 hab fun μ hμ ↦
      hH μ (Submodule.subset_span hμ)
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span ℝ 𝔞.restrictedRoots)
  rw [hco, finrank_bot, add_zero] at h
  rw [h, Subspace.dual_finrank_eq]

end Span

/-! ### The restricted root pairing -/

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}
  (hθ : θ.IsCartanInvolution) (h𝔞 : θ.IsMaximalAbelianInP 𝔞)

include hθ h𝔞 in
/-- The span of the restricted roots, in the form `RootPairing.mk''` takes it. -/
private theorem span_range_restrictedRoots_eq_top :
    Submodule.span ℝ (range (Function.Embedding.subtype (· ∈ 𝔞.restrictedRoots))) = ⊤ := by
  rw [Function.Embedding.coe_subtype, Subtype.range_coe]
  exact hθ.span_restrictedRoots_eq_top h𝔞.le_cartanP fun _ hx _ hy ↦ h𝔞.lie_eq_zero hx hy

/-- **The restricted root pairing.** For a Cartan involution `θ` of a real Lie algebra and a
maximal abelian subspace `𝔞` of `𝔭`, the root pairing indexed by the restricted roots `Σ`, on
`(𝔞*, 𝔞)` with the evaluation pairing, with roots `λ` and coroots
`H'_λ = 2 H_λ / B(H_λ, H_λ)`. -/
noncomputable def restrictedRootPairing : RootPairing 𝔞.restrictedRoots ℝ (Dual ℝ 𝔞) 𝔞 :=
  have := hθ.finiteDimensional
  have : Finite 𝔞.restrictedRoots := (hθ.finite_restrictedRoots 𝔞).to_subtype
  RootPairing.mk'' LinearMap.id (Function.Embedding.subtype _)
    (hθ.restrictedCorootEmbedding h𝔞.le_cartanP)
    (fun μ ↦ hθ.apply_restrictedCoroot h𝔞.le_cartanP
      (Submodule.mem_restrictedRoots.mp μ.property).1)
    (by
      rintro μ - ⟨ν, rfl⟩
      exact ⟨⟨_, hθ.sub_smul_mem_restrictedRoots h𝔞 μ.property ν.property⟩, by
        simp only [Function.Embedding.coe_subtype, preReflection_apply, LinearMap.flip_apply,
          LinearMap.id_apply, restrictedCorootEmbedding_apply]⟩)
    (hθ.span_range_restrictedRoots_eq_top h𝔞)

@[simp]
theorem restrictedRootPairing_toLinearMap_apply (f : Dual ℝ 𝔞) (H : 𝔞) :
    (hθ.restrictedRootPairing h𝔞).toLinearMap f H = f H :=
  (rfl)

@[simp]
theorem restrictedRootPairing_root (μ : 𝔞.restrictedRoots) :
    (hθ.restrictedRootPairing h𝔞).root μ = μ :=
  (rfl)

@[simp]
theorem restrictedRootPairing_coroot (μ : 𝔞.restrictedRoots) :
    (hθ.restrictedRootPairing h𝔞).coroot μ = hθ.restrictedCoroot h𝔞.le_cartanP μ :=
  (rfl)

/-- The pairing of `λ` with the coroot of `μ` is `λ(H'_μ)`. -/
@[simp]
theorem restrictedRootPairing_pairing (μ ν : 𝔞.restrictedRoots) :
    (hθ.restrictedRootPairing h𝔞).pairing μ ν =
      (μ : Dual ℝ 𝔞) (hθ.restrictedCoroot h𝔞.le_cartanP ν) :=
  (rfl)

/-- **The restricted root pairing is crystallographic**: `λ(H'_μ) ∈ ℤ`. -/
instance isCrystallographic_restrictedRootPairing :
    (hθ.restrictedRootPairing h𝔞).IsCrystallographic := by
  refine ⟨fun μ ν ↦ ?_⟩
  obtain ⟨z, hz⟩ := hθ.exists_int_apply_restrictedCoroot h𝔞 ν.property
    (Submodule.mem_restrictedRoots.mp μ.property).2
  exact ⟨z, by simp [hz]⟩

/-- **The restricted root pairing is a root system**: the roots span `𝔞*` and the coroots span
`𝔞`. -/
instance isRootSystem_restrictedRootPairing :
    (hθ.restrictedRootPairing h𝔞).IsRootSystem := by
  have := hθ.finiteDimensional
  have : Finite 𝔞.restrictedRoots := (hθ.finite_restrictedRoots 𝔞).to_subtype
  exact RootPairing.isRootSystem_mk'' (hsp := hθ.span_range_restrictedRoots_eq_top h𝔞)
    (hθ.isCrystallographic_restrictedRootPairing h𝔞).exists_value

include hθ h𝔞 in
/-- **The restricted root system**: the restricted roots of a Cartan involution of a real Lie
algebra form a crystallographic root system, possibly nonreduced, for the evaluation pairing of
`𝔞*` with `𝔞`. -/
theorem exists_restrictedRootPairing :
    ∃ P : RootPairing 𝔞.restrictedRoots ℝ (Dual ℝ 𝔞) 𝔞,
      (∀ (f : Dual ℝ 𝔞) (x : 𝔞), P.toLinearMap f x = f x) ∧
      (∀ i, P.root i = (i : Dual ℝ 𝔞)) ∧ P.IsCrystallographic ∧ P.IsRootSystem :=
  ⟨hθ.restrictedRootPairing h𝔞, hθ.restrictedRootPairing_toLinearMap_apply h𝔞,
    hθ.restrictedRootPairing_root h𝔞,
    inferInstance, inferInstance⟩

end LieEquiv.IsCartanInvolution
