/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.RootPairing
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectionPerm
public import TauCeti.LinearAlgebra.RootSystem.Indivisible
public import TauCeti.LinearAlgebra.RootSystem.EquivComp
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The indivisible subsystem and Weyl-invariance of restricted roots

Let `θ` be a Cartan involution of a real Lie algebra `𝔤₀` and `𝔞` a maximal abelian
subspace of its `-1`-eigenspace `𝔭`. Building on `LieEquiv.IsCartanInvolution.restrictedRootPairing`
(`TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.RootPairing`), this file proves that the
restricted root multiplicities `m_ν = dim 𝔤_ν` are invariant under the restricted Weyl group
`W(Σ)` (`LieEquiv.IsCartanInvolution.finrank_restrictedRootSpace_smul`).

A restricted root system need not be reduced (`2λ` may occur alongside `λ`). Passing to the
**indivisible restricted roots** `Σ_indiv = {λ ∈ Σ | ∀ γ ∈ Σ, 2 • γ ≠ λ}`
(`Submodule.indivisibleRestrictedRoots`) yields a reduced crystallographic root system
(`LieEquiv.IsCartanInvolution.indivisibleRestrictedRootPairing`) with the same Weyl group on `𝔞*`
and `𝔞` (`LieEquiv.IsCartanInvolution.restrictedWeylGroupEquiv`), because `s_{2λ} = s_λ`.

## Main definitions

* `Submodule.indivisibleRestrictedRoots`: the indivisible restricted roots `λ ∈ Σ` not equal
  to `2 • γ` for any `γ ∈ Σ`.
* `LieEquiv.IsCartanInvolution.indivisibleRestrictedRootPairing`: the reduced crystallographic root
  system of indivisible restricted roots.
* `LieEquiv.IsCartanInvolution.restrictedWeylGroupEquiv`: the canonical isomorphism between the Weyl
  groups of `Σ` and `Σ_indiv`, intertwining their actions on `𝔞*` and `𝔞`.

## Main results

* `LieEquiv.IsCartanInvolution.finrank_restrictedRootSpace_smul`: `W(Σ)`-invariance of the
  restricted root space multiplicities `m_ν = dim 𝔤_ν`.
* `LieEquiv.IsCartanInvolution.mem_indivisibleRestrictedRoots_or_exists_eq_two_smul`: every
  restricted root is either indivisible or twice an indivisible restricted root.
* `LieEquiv.IsCartanInvolution.sub_smul_mem_indivisibleRestrictedRoots`: reflections preserve
  `Σ_indiv`.
* `LieEquiv.IsCartanInvolution.range_weightHom_indivisibleRestrictedRootPairing_eq` and
  `LieEquiv.IsCartanInvolution.range_coweightHom_indivisibleRestrictedRootPairing_eq`: `Σ` and
  `Σ_indiv` generate the same Weyl group on `𝔞*` and on `𝔞`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4–5.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter VII, §2.
-/

public section

open LieAlgebra LieModule Module

namespace Submodule

section Indivisible

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The **indivisible restricted roots** of a submodule `𝔞` of a Lie algebra: those restricted
roots `λ ∈ Σ` not equal to `(2 : R) • γ` for any `γ ∈ Σ`. -/
def indivisibleRestrictedRoots (𝔞 : Submodule R L) : Set (Dual R 𝔞) :=
  {μ ∈ 𝔞.restrictedRoots | ∀ γ ∈ 𝔞.restrictedRoots, (2 : R) • γ ≠ μ}

variable {𝔞 : Submodule R L} {μ : Dual R 𝔞}

@[simp]
theorem mem_indivisibleRestrictedRoots :
    μ ∈ 𝔞.indivisibleRestrictedRoots ↔
      μ ∈ 𝔞.restrictedRoots ∧ ∀ γ ∈ 𝔞.restrictedRoots, (2 : R) • γ ≠ μ :=
  Iff.rfl

/-- Every indivisible restricted root is a restricted root. -/
theorem indivisibleRestrictedRoots_subset :
    𝔞.indivisibleRestrictedRoots ⊆ 𝔞.restrictedRoots :=
  fun _ h ↦ h.left

/-- An indivisible restricted root is nonzero. -/
theorem ne_zero_of_mem_indivisibleRestrictedRoots (hμ : μ ∈ 𝔞.indivisibleRestrictedRoots) :
    μ ≠ 0 :=
  (mem_restrictedRoots.mp hμ.left).left

/-- If `R` is a domain and `L` is torsion-free and Noetherian over `R`, there are finitely many
indivisible restricted roots for each submodule `𝔞`. -/
theorem finite_indivisibleRestrictedRoots [IsDomain R] [IsTorsionFree R L] [IsNoetherian R L] :
    𝔞.indivisibleRestrictedRoots.Finite :=
  finite_restrictedRoots.subset indivisibleRestrictedRoots_subset

/-- The zero subspace has no indivisible restricted roots. -/
@[simp]
theorem indivisibleRestrictedRoots_bot :
    (⊥ : Submodule R L).indivisibleRestrictedRoots = ∅ := by
  simp [indivisibleRestrictedRoots]

end Indivisible

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- Over a field, a restricted root `λ` is indivisible iff `(1 / 2) • λ` is not a restricted root
(in characteristic `2`, both conditions hold for every restricted root since `2 = 0` and
`1 / 2 = 0`). -/
theorem mem_indivisibleRestrictedRoots_iff_half_notMem {𝔞 : Submodule K L}
    {μ : Dual K 𝔞} :
    μ ∈ 𝔞.indivisibleRestrictedRoots ↔
      μ ∈ 𝔞.restrictedRoots ∧ (1 / 2 : K) • μ ∉ 𝔞.restrictedRoots := by
  by_cases h2 : (2 : K) = 0
  · simp only [mem_indivisibleRestrictedRoots, one_div, h2, inv_zero, zero_smul]
    exact ⟨fun h ↦ ⟨h.1, fun h0 ↦ (mem_restrictedRoots.mp h0).1 rfl⟩,
      fun h ↦ ⟨h.1, fun _ _ h0 ↦ (mem_restrictedRoots.mp h.1).1 h0.symm⟩⟩
  · simp only [mem_indivisibleRestrictedRoots, one_div, and_congr_right_iff]
    intro _
    constructor
    · intro h hhalf
      exact h _ hhalf (by rw [smul_smul, mul_inv_cancel₀ h2, one_smul])
    · intro h γ hγ h2γ
      apply h
      convert hγ using 1
      rw [← h2γ, smul_smul, inv_mul_cancel₀ h2, one_smul]

end Submodule

namespace LieEquiv

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {θ : L ≃ₗ⁅R⁆ L} {𝔞 : Submodule R L}

/-- For `𝔞 ⊆ 𝔭`, `-λ` is an indivisible restricted root exactly when `λ` is. -/
theorem neg_mem_indivisibleRestrictedRoots_iff (h𝔞 : 𝔞 ≤ θ.cartanP) {μ : Dual R 𝔞} :
    -μ ∈ 𝔞.indivisibleRestrictedRoots ↔ μ ∈ 𝔞.indivisibleRestrictedRoots := by
  simp only [Submodule.mem_indivisibleRestrictedRoots, neg_mem_restrictedRoots_iff h𝔞,
    and_congr_right_iff]
  intro _
  constructor <;> intro h γ hγ h2
  · exact h (-γ) ((neg_mem_restrictedRoots_iff h𝔞).mpr hγ) (by rwa [smul_neg, neg_inj])
  · exact h (-γ) ((neg_mem_restrictedRoots_iff h𝔞).mpr hγ) (by rw [smul_neg, h2, neg_neg])

end LieEquiv

namespace LieEquiv.IsCartanInvolution

open Submodule

section OrderedField

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L} {𝔞 : Submodule K L}
  (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)

variable (h𝔞_max : θ.IsMaximalAbelianInP 𝔞)

include hθ h𝔞_max in
/-- If `λ` and `λ / 2` are both restricted roots, then `λ / 2` is indivisible. -/
theorem mem_indivisibleRestrictedRoots_of_half_mem {μ : Dual K 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) (hhalf : (1 / 2 : K) • μ ∈ 𝔞.restrictedRoots) :
    (1 / 2 : K) • μ ∈ 𝔞.indivisibleRestrictedRoots := by
  -- Otherwise `λ / 4` would also be a restricted root, contradicting
  -- `mem_of_smul_mem_restrictedRoots`.
  refine mem_indivisibleRestrictedRoots_iff_half_notMem.mpr ⟨hhalf, fun hquarter ↦ ?_⟩
  rw [smul_smul] at hquarter
  have hmem := hθ.mem_of_smul_mem_restrictedRoots h𝔞_max hμ hquarter
  norm_num at hmem

include hθ h𝔞_max in
/-- **Decomposition into indivisible restricted roots.** Every restricted root is either
indivisible, or twice the indivisible restricted root `(1 / 2) • λ`. -/
theorem mem_indivisibleRestrictedRoots_or_exists_eq_two_smul {μ : Dual K 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) :
    μ ∈ 𝔞.indivisibleRestrictedRoots ∨
      ∃ γ ∈ 𝔞.indivisibleRestrictedRoots, μ = (2 : K) • γ := by
  by_cases hhalf : (1 / 2 : K) • μ ∈ 𝔞.restrictedRoots
  · refine Or.inr ⟨(1 / 2 : K) • μ,
      hθ.mem_indivisibleRestrictedRoots_of_half_mem h𝔞_max hμ hhalf, ?_⟩
    rw [smul_smul]
    norm_num
  · exact Or.inl (mem_indivisibleRestrictedRoots_iff_half_notMem.mpr ⟨hμ, hhalf⟩)

include hθ h𝔞_max in
/-- Two indivisible restricted roots that are scalar multiples of each other agree up to sign:
the reducedness property of `Σ_indiv`. -/
theorem eq_or_eq_neg_of_mem_indivisibleRestrictedRoots {μ ν : Dual K 𝔞}
    (hμ : μ ∈ 𝔞.indivisibleRestrictedRoots) (hν : ν ∈ 𝔞.indivisibleRestrictedRoots)
    {c : K} (hc : ν = c • μ) : μ = ν ∨ μ = -ν := by
  rw [mem_indivisibleRestrictedRoots_iff_half_notMem] at hμ hν
  have hmem := hθ.mem_of_smul_mem_restrictedRoots h𝔞_max hμ.left (hc ▸ hν.left)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (hc ▸ hν.left) hμ.right
  · have hneg : (1 / 2 : K) • μ ∈ 𝔞.restrictedRoots := by
      have heq : (1 / 2 : K) • μ = -ν := by
        rw [hc]
        module
      rw [heq, neg_mem_restrictedRoots_iff h𝔞_max.le_cartanP]
      exact hν.left
    exact absurd hneg hμ.right
  · exact Or.inl (by rw [hc, one_smul])
  · exact Or.inr (by rw [hc]; module)
  · have hhalf : (1 / 2 : K) • ν ∈ 𝔞.restrictedRoots := by
      have heq : (1 / 2 : K) • ν = μ := by
        rw [hc, smul_smul]
        norm_num
      rw [heq]
      exact hμ.left
    exact absurd hhalf hν.right
  · have hhalf : (1 / 2 : K) • ν ∈ 𝔞.restrictedRoots := by
      have heq : (1 / 2 : K) • ν = -μ := by
        rw [hc]
        module
      rw [heq, neg_mem_restrictedRoots_iff h𝔞_max.le_cartanP]
      exact hμ.left
    exact absurd hhalf hν.right

end OrderedField

section RootSystem

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}

/-- The type of indivisible restricted roots of `𝔞` is finite. -/
theorem finite_indivisibleRestrictedRoots_subtype (hθ : θ.IsCartanInvolution)
    (𝔞 : Submodule ℝ L) :
    Finite 𝔞.indivisibleRestrictedRoots :=
  have := hθ.finiteDimensional
  Submodule.finite_indivisibleRestrictedRoots.to_subtype

section Pairing

variable (hθ : θ.IsCartanInvolution) (h𝔞 : θ.IsMaximalAbelianInP 𝔞)

/-- Evaluating a root functional of `Σ` at `H : 𝔞` is evaluating `μ` at `H`.

Not a `simp` lemma: `simp` proves this from `restrictedRootPairing_root` and
`restrictedRootPairing_toLinearMap_apply`. -/
theorem restrictedRootPairing_root'_apply (μ : 𝔞.restrictedRoots) (H : 𝔞) :
    (hθ.restrictedRootPairing h𝔞).root' μ H = (μ : Dual ℝ 𝔞) H := by
  simp [RootPairing.root']

/-- Evaluating `w • μ` at `H : 𝔞` is evaluating `μ` at the coweight action of `w` on `H`. -/
theorem restrictedRootPairing_weylGroup_smul_apply
    (w : (hθ.restrictedRootPairing h𝔞).weylGroup) (μ : Dual ℝ 𝔞) (H : 𝔞) :
    (w • μ) H = μ ((w : (hθ.restrictedRootPairing h𝔞).Aut).coweightEquiv H) :=
  RootPairing.weylGroup_smul_dual_apply (hθ.restrictedRootPairing h𝔞)
    (restrictedRootPairing_toLinearMap_apply hθ h𝔞) w μ H

@[simp]
theorem restrictedRootPairing_reflection_apply (μ : 𝔞.restrictedRoots) (ν : Dual ℝ 𝔞) :
    (hθ.restrictedRootPairing h𝔞).reflection μ ν =
      ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • (μ : Dual ℝ 𝔞) := by
  simp [RootPairing.reflection_apply, RootPairing.coroot']

@[simp]
theorem restrictedRootPairing_coreflection_apply (μ : 𝔞.restrictedRoots) (H : 𝔞) :
    (hθ.restrictedRootPairing h𝔞).coreflection μ H =
      H - (μ : Dual ℝ 𝔞) H • hθ.restrictedCoroot h𝔞.le_cartanP μ := by
  simp [RootPairing.coreflection_apply, RootPairing.root']

@[simp]
theorem restrictedRootPairing_reflectionPerm_apply (μ ν : 𝔞.restrictedRoots) :
    ((hθ.restrictedRootPairing h𝔞).reflectionPerm μ ν : Dual ℝ 𝔞) =
      (ν : Dual ℝ 𝔞) -
        ((ν : Dual ℝ 𝔞) (hθ.restrictedCoroot h𝔞.le_cartanP μ)) •
          (μ : Dual ℝ 𝔞) := by
  rw [← restrictedRootPairing_root hθ h𝔞, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_root]
  simp

/-- **Weyl-invariance of restricted root multiplicities.** For every `w ∈ W(Σ)` and every
`ν ∈ 𝔞*`, `dim 𝔤_{w • ν} = dim 𝔤_ν`. -/
theorem finrank_restrictedRootSpace_smul (w : (hθ.restrictedRootPairing h𝔞).weylGroup)
    (ν : Dual ℝ 𝔞) :
    finrank ℝ (𝔞.restrictedRootSpace (w • ν)) =
      finrank ℝ (𝔞.restrictedRootSpace ν) := by
  rw [Subgroup.smul_def]
  obtain ⟨w, hw⟩ := w
  induction hw using RootPairing.weylGroup.induction generalizing ν with
  | mem μ =>
    rw [RootPairing.Equiv.reflection_smul, restrictedRootPairing_reflection_apply]
    exact hθ.finrank_restrictedRootSpace_sub_smul h𝔞 μ.property ν
  | one => rw [one_smul]
  | mul x y _ _ ihx ihy =>
    rw [mul_smul, ihx (y • ν), ihy ν]

/-- **Weyl-invariance of restricted root multiplicities** on root indices: `m_{w λ} = m_λ` for
every `w ∈ W(Σ)` and `λ ∈ Σ`. -/
theorem finrank_restrictedRootSpace_weylGroupToPerm
    (w : (hθ.restrictedRootPairing h𝔞).weylGroup) (μ : 𝔞.restrictedRoots) :
    finrank ℝ (𝔞.restrictedRootSpace
        ((hθ.restrictedRootPairing h𝔞).weylGroupToPerm w μ : Dual ℝ 𝔞)) =
      finrank ℝ (𝔞.restrictedRootSpace μ) := by
  have hroot : ((hθ.restrictedRootPairing h𝔞).weylGroupToPerm w μ : Dual ℝ 𝔞) =
      w • (μ : Dual ℝ 𝔞) := by
    simpa only [restrictedRootPairing_root] using
      ((hθ.restrictedRootPairing h𝔞).weylGroup_apply_root w μ).symm
  rw [hroot]
  exact hθ.finrank_restrictedRootSpace_smul h𝔞 w μ

/-- **Weyl-invariance of restricted roots**: `w • ν ∈ Σ` iff `ν ∈ Σ`. -/
theorem smul_mem_restrictedRoots_iff (w : (hθ.restrictedRootPairing h𝔞).weylGroup)
    {ν : Dual ℝ 𝔞} :
    w • ν ∈ 𝔞.restrictedRoots ↔ ν ∈ 𝔞.restrictedRoots := by
  have := hθ.finiteDimensional
  have h0 : w • ν = 0 ↔ ν = 0 :=
    ⟨fun h ↦ by simpa [h] using (inv_smul_smul w ν).symm, fun h ↦ by simp [h]⟩
  have hbot : 𝔞.restrictedRootSpace (w • ν) ≠ ⊥ ↔ 𝔞.restrictedRootSpace ν ≠ ⊥ :=
    not_congr <| by
      rw [← Submodule.finrank_eq_zero (R := ℝ), hθ.finrank_restrictedRootSpace_smul h𝔞 w ν,
        Submodule.finrank_eq_zero]
  rw [mem_restrictedRoots, mem_restrictedRoots, hbot]
  exact and_congr_left fun _ ↦ not_congr h0

/-- **Weyl-invariance of indivisible restricted roots**:
`w • ν ∈ Σ_indiv` iff `ν ∈ Σ_indiv`. -/
theorem smul_mem_indivisibleRestrictedRoots_iff
    (w : (hθ.restrictedRootPairing h𝔞).weylGroup) {ν : Dual ℝ 𝔞} :
    w • ν ∈ 𝔞.indivisibleRestrictedRoots ↔ ν ∈ 𝔞.indivisibleRestrictedRoots := by
  simp only [Submodule.mem_indivisibleRestrictedRoots_iff_half_notMem,
    hθ.smul_mem_restrictedRoots_iff h𝔞 w]
  have hhalf : (1 / 2 : ℝ) • (w • ν) = w • ((1 / 2 : ℝ) • ν) :=
    ((w : (hθ.restrictedRootPairing h𝔞).Aut).weightEquiv.map_smul (1 / 2 : ℝ) ν).symm
  rw [hhalf, hθ.smul_mem_restrictedRoots_iff h𝔞 w]

end Pairing

section Indivisible

variable (hθ : θ.IsCartanInvolution) (h𝔞 : θ.IsMaximalAbelianInP 𝔞)

include hθ h𝔞 in
/-- **Reflections permute the indivisible restricted roots**: if `λ ∈ Σ` and `ν ∈ Σ_indiv`,
then `s_λ ν ∈ Σ_indiv`. -/
theorem sub_smul_mem_indivisibleRestrictedRoots {μ ν : Dual ℝ 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) (hν : ν ∈ 𝔞.indivisibleRestrictedRoots) :
    ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • μ ∈
      𝔞.indivisibleRestrictedRoots := by
  rw [← hθ.restrictedRootPairing_reflection_apply h𝔞 ⟨μ, hμ⟩ ν,
    ← RootPairing.Equiv.reflection_smul, ← RootPairing.weylGroup.ofIdx_smul]
  exact (hθ.smul_mem_indivisibleRestrictedRoots_iff h𝔞
    (RootPairing.weylGroup.ofIdx (hθ.restrictedRootPairing h𝔞) ⟨μ, hμ⟩)).mpr hν

/-- An index `μ : 𝔞.restrictedRoots` is indivisible for `restrictedRootPairing` iff `μ` lies in
`𝔞.indivisibleRestrictedRoots`. -/
@[simp]
theorem isIndivisible_restrictedRootPairing_iff (μ : 𝔞.restrictedRoots) :
    (hθ.restrictedRootPairing h𝔞).IsIndivisible μ ↔
      (μ : Dual ℝ 𝔞) ∈ 𝔞.indivisibleRestrictedRoots := by
  simp only [RootPairing.isIndivisible_iff, restrictedRootPairing_root,
    Submodule.mem_indivisibleRestrictedRoots, Subtype.coe_prop, true_and, Subtype.forall]

/-- Canonical equivalence between the indivisible indices of `hθ.restrictedRootPairing h𝔞` and
the subtype `𝔞.indivisibleRestrictedRoots`. -/
def indivisibleRestrictedRootsEquiv :
    {μ : 𝔞.restrictedRoots // (hθ.restrictedRootPairing h𝔞).IsIndivisible μ} ≃
      𝔞.indivisibleRestrictedRoots where
  toFun μ := ⟨μ.val.val, (hθ.isIndivisible_restrictedRootPairing_iff h𝔞 μ.val).mp μ.property⟩
  invFun μ := ⟨⟨μ.val, μ.property.left⟩,
    (hθ.isIndivisible_restrictedRootPairing_iff h𝔞 _).mpr μ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The reduced restricted root system.** The indivisible restricted roots `Σ_indiv` and their
coroots form a reduced crystallographic root system on `(𝔞*, 𝔞)`. -/
noncomputable def indivisibleRestrictedRootPairing :
    RootPairing 𝔞.indivisibleRestrictedRoots ℝ (Dual ℝ 𝔞) 𝔞 :=
  have := hθ.finiteDimensional
  have : Finite 𝔞.restrictedRoots := Submodule.finite_restrictedRoots.to_subtype
  (hθ.restrictedRootPairing h𝔞).indivisible.map
    (hθ.indivisibleRestrictedRootsEquiv h𝔞)
    (LinearEquiv.refl ℝ (Dual ℝ 𝔞))
    (LinearEquiv.refl ℝ 𝔞)

@[simp]
theorem indivisibleRestrictedRootPairing_toLinearMap_apply (f : Dual ℝ 𝔞) (x : 𝔞) :
    (hθ.indivisibleRestrictedRootPairing h𝔞).toLinearMap f x = f x := by
  simp [indivisibleRestrictedRootPairing, RootPairing.map]

@[simp]
theorem indivisibleRestrictedRootPairing_root_apply (μ : 𝔞.indivisibleRestrictedRoots) :
    (hθ.indivisibleRestrictedRootPairing h𝔞).root μ = μ := by
  simp [indivisibleRestrictedRootPairing, RootPairing.map, indivisibleRestrictedRootsEquiv]

/-- Evaluating a root functional of `Σ_indiv` at `H : 𝔞` is evaluating `μ` at `H`.

Not a `simp` lemma: `simp` proves this from `indivisibleRestrictedRootPairing_root_apply` and
`indivisibleRestrictedRootPairing_toLinearMap_apply`. -/
theorem indivisibleRestrictedRootPairing_root'_apply (μ : 𝔞.indivisibleRestrictedRoots)
    (H : 𝔞) :
    (hθ.indivisibleRestrictedRootPairing h𝔞).root' μ H = (μ : Dual ℝ 𝔞) H := by
  simp [RootPairing.root']

/-- Evaluating a flipped coroot functional of `Σ_indiv` at `H : 𝔞` is evaluating `μ` at `H`.

Not a `simp` lemma: `RootPairing.coroot'` is an abbreviation for `LinearMap.flip`, so `simp`
rewrites the left-hand side via `LinearMap.flip_apply`. -/
theorem indivisibleRestrictedRootPairing_flip_coroot'_apply
    (μ : 𝔞.indivisibleRestrictedRoots) (H : 𝔞) :
    (hθ.indivisibleRestrictedRootPairing h𝔞).flip.coroot' μ H = (μ : Dual ℝ 𝔞) H := by
  simp [RootPairing.coroot']

/-- Evaluating `w • μ` at `H : 𝔞` is evaluating `μ` at the coweight action of `w` on `H`. -/
theorem indivisibleRestrictedRootPairing_weylGroup_smul_apply
    (w : (hθ.indivisibleRestrictedRootPairing h𝔞).weylGroup) (μ : Dual ℝ 𝔞) (H : 𝔞) :
    (w • μ) H = μ ((w : (hθ.indivisibleRestrictedRootPairing h𝔞).Aut).coweightEquiv H) :=
  RootPairing.weylGroup_smul_dual_apply (hθ.indivisibleRestrictedRootPairing h𝔞)
    (fun _ _ ↦ by simp) w μ H

@[simp]
theorem indivisibleRestrictedRootPairing_coroot_apply (μ : 𝔞.indivisibleRestrictedRoots) :
    (hθ.indivisibleRestrictedRootPairing h𝔞).coroot μ =
      hθ.restrictedCoroot h𝔞.le_cartanP μ := by
  simp [indivisibleRestrictedRootPairing, RootPairing.map, indivisibleRestrictedRootsEquiv]

@[simp]
theorem indivisibleRestrictedRootPairing_pairing_apply (ν μ : 𝔞.indivisibleRestrictedRoots) :
    (hθ.indivisibleRestrictedRootPairing h𝔞).pairing ν μ =
      (ν : Dual ℝ 𝔞) (hθ.restrictedCoroot h𝔞.le_cartanP μ) := by
  simp [RootPairing.pairing]

@[simp]
theorem indivisibleRestrictedRootPairing_reflection_apply (μ : 𝔞.indivisibleRestrictedRoots)
    (ν : Dual ℝ 𝔞) :
    (hθ.indivisibleRestrictedRootPairing h𝔞).reflection μ ν =
      ν - ν (hθ.restrictedCoroot h𝔞.le_cartanP μ) • (μ : Dual ℝ 𝔞) := by
  simp [RootPairing.reflection_apply, RootPairing.coroot']

@[simp]
theorem indivisibleRestrictedRootPairing_coreflection_apply
    (μ : 𝔞.indivisibleRestrictedRoots) (H : 𝔞) :
    (hθ.indivisibleRestrictedRootPairing h𝔞).coreflection μ H =
      H - (μ : Dual ℝ 𝔞) H • hθ.restrictedCoroot h𝔞.le_cartanP μ := by
  simp [RootPairing.coreflection_apply, RootPairing.root']

@[simp]
theorem indivisibleRestrictedRootPairing_reflectionPerm_apply
    (μ ν : 𝔞.indivisibleRestrictedRoots) :
    ((hθ.indivisibleRestrictedRootPairing h𝔞).reflectionPerm μ ν : Dual ℝ 𝔞) =
      (ν : Dual ℝ 𝔞) -
        ((ν : Dual ℝ 𝔞) (hθ.restrictedCoroot h𝔞.le_cartanP μ)) •
          (μ : Dual ℝ 𝔞) := by
  rw [← indivisibleRestrictedRootPairing_root_apply hθ h𝔞, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_root]
  simp

/-- The indivisible restricted root system is crystallographic. -/
instance isCrystallographic_indivisibleRestrictedRootPairing :
    (hθ.indivisibleRestrictedRootPairing h𝔞).IsCrystallographic :=
  have := hθ.finiteDimensional
  have : Finite 𝔞.restrictedRoots := Submodule.finite_restrictedRoots.to_subtype
  ((hθ.restrictedRootPairing h𝔞).indivisible.equivMap _ _ _).toHom.isValuedIn ℤ

/-- The indivisible restricted root system is a root system. -/
instance isRootSystem_indivisibleRestrictedRootPairing :
    (hθ.indivisibleRestrictedRootPairing h𝔞).IsRootSystem := by
  have := hθ.finiteDimensional
  have : Finite 𝔞.restrictedRoots := Submodule.finite_restrictedRoots.to_subtype
  dsimp only [indivisibleRestrictedRootPairing]
  infer_instance

/-- **The indivisible restricted root system is reduced.** -/
instance isReduced_indivisibleRestrictedRootPairing :
    (hθ.indivisibleRestrictedRootPairing h𝔞).IsReduced :=
  have := hθ.finiteDimensional
  have : Finite 𝔞.restrictedRoots := Submodule.finite_restrictedRoots.to_subtype
  ((hθ.restrictedRootPairing h𝔞).indivisible.equivMap _ _ _).isReduced

include hθ h𝔞 in
/-- **The indivisible restricted roots span `𝔞*`.** -/
theorem span_indivisibleRestrictedRoots_eq_top :
    Submodule.span ℝ 𝔞.indivisibleRestrictedRoots = ⊤ := by
  have hr : Set.range (hθ.indivisibleRestrictedRootPairing h𝔞).root =
      𝔞.indivisibleRestrictedRoots := by
    ext μ
    simp only [Set.mem_range, indivisibleRestrictedRootPairing_root_apply]
    exact ⟨fun ⟨ν, hν⟩ ↦ hν ▸ ν.property, fun hμ ↦ ⟨⟨μ, hμ⟩, rfl⟩⟩
  rw [← hr]
  exact RootPairing.IsRootSystem.span_root_eq_top

end Indivisible

section WeylEquiv

variable (hθ : θ.IsCartanInvolution) (h𝔞 : θ.IsMaximalAbelianInP 𝔞)

/-- **The reflections of `Σ` and `Σ_indiv` on `𝔞*` coincide**, since `s_{2λ} = s_λ`. -/
theorem range_reflection_indivisibleRestrictedRootPairing_eq :
    Set.range (hθ.indivisibleRestrictedRootPairing h𝔞).reflection =
      Set.range (hθ.restrictedRootPairing h𝔞).reflection := by
  have := hθ.finiteDimensional
  have : Finite 𝔞.restrictedRoots := Submodule.finite_restrictedRoots.to_subtype
  rw [indivisibleRestrictedRootPairing, RootPairing.range_map_reflection_refl,
    RootPairing.range_reflection_indivisible]

/-- **The coreflections of `Σ` and `Σ_indiv` on `𝔞` coincide**, since `s_{2λ} = s_λ`. -/
theorem range_coreflection_indivisibleRestrictedRootPairing_eq :
    Set.range (hθ.indivisibleRestrictedRootPairing h𝔞).coreflection =
      Set.range (hθ.restrictedRootPairing h𝔞).coreflection := by
  have := hθ.finiteDimensional
  have : Finite 𝔞.restrictedRoots := Submodule.finite_restrictedRoots.to_subtype
  rw [indivisibleRestrictedRootPairing, RootPairing.range_map_coreflection_refl,
    RootPairing.range_coreflection_indivisible]

/-- **Same Weyl group on `𝔞*`**: the image of `W(Σ_indiv)` in `GL(𝔞*)` equals that of
`W(Σ)`. -/
theorem range_weightHom_indivisibleRestrictedRootPairing_eq :
    MonoidHom.range
        ((RootPairing.Equiv.weightHom (hθ.indivisibleRestrictedRootPairing h𝔞)).domRestrict
          (hθ.indivisibleRestrictedRootPairing h𝔞).weylGroup) =
      MonoidHom.range
        ((RootPairing.Equiv.weightHom (hθ.restrictedRootPairing h𝔞)).domRestrict
          (hθ.restrictedRootPairing h𝔞).weylGroup) := by
  rw [RootPairing.range_weylGroup_weightHom, RootPairing.range_weylGroup_weightHom,
    hθ.range_reflection_indivisibleRestrictedRootPairing_eq h𝔞]

/-- **Same Weyl group on `𝔞`**: the image of `W(Σ_indiv)` in `GL(𝔞)ᵐᵒᵖ` equals that of
`W(Σ)`. -/
theorem range_coweightHom_indivisibleRestrictedRootPairing_eq :
    MonoidHom.range
        ((RootPairing.Equiv.coweightHom (hθ.indivisibleRestrictedRootPairing h𝔞)).domRestrict
          (hθ.indivisibleRestrictedRootPairing h𝔞).weylGroup) =
      MonoidHom.range
        ((RootPairing.Equiv.coweightHom (hθ.restrictedRootPairing h𝔞)).domRestrict
          (hθ.restrictedRootPairing h𝔞).weylGroup) := by
  rw [RootPairing.range_weylGroup_coweightHom, RootPairing.range_weylGroup_coweightHom,
    Set.range_comp MulOpposite.op, Set.range_comp MulOpposite.op,
    hθ.range_coreflection_indivisibleRestrictedRootPairing_eq h𝔞]

/-- **The isomorphism `W(Σ) ≃* W(Σ_indiv)`** identifying the Weyl groups of the restricted root
system and its indivisible reduced subsystem via their common action on `𝔞*`. -/
noncomputable def restrictedWeylGroupEquiv :
    (hθ.restrictedRootPairing h𝔞).weylGroup ≃*
      (hθ.indivisibleRestrictedRootPairing h𝔞).weylGroup :=
  RootPairing.weylGroupEquivOfRangeReflectionEq
    (hθ.restrictedRootPairing h𝔞)
    (hθ.indivisibleRestrictedRootPairing h𝔞)
    (hθ.range_reflection_indivisibleRestrictedRootPairing_eq h𝔞).symm

/-- `restrictedWeylGroupEquiv` commutes with the action on `𝔞*`. -/
@[simp]
theorem restrictedWeylGroupEquiv_smul (w : (hθ.restrictedRootPairing h𝔞).weylGroup)
    (ν : Dual ℝ 𝔞) :
    hθ.restrictedWeylGroupEquiv h𝔞 w • ν = w • ν :=
  RootPairing.weylGroupEquivOfRangeReflectionEq_smul _ _ _ w ν

/-- `restrictedWeylGroupEquiv` preserves the coweight action on `𝔞`.

Not a `simp` lemma: `simp` rewrites the left-hand side via
`RootPairing.Equiv.coweightEquiv_apply`. -/
theorem coweightEquiv_restrictedWeylGroupEquiv
    (w : (hθ.restrictedRootPairing h𝔞).weylGroup) (H : 𝔞) :
    (hθ.restrictedWeylGroupEquiv h𝔞 w :
        (hθ.indivisibleRestrictedRootPairing h𝔞).Aut).coweightEquiv H =
      (w : (hθ.restrictedRootPairing h𝔞).Aut).coweightEquiv H := by
  have := hθ.finiteDimensional
  refine Module.eval_apply_injective ℝ (LinearMap.ext fun f ↦ ?_)
  rw [Dual.eval_apply, Dual.eval_apply,
    ← hθ.indivisibleRestrictedRootPairing_weylGroup_smul_apply h𝔞,
    ← hθ.restrictedRootPairing_weylGroup_smul_apply h𝔞,
    hθ.restrictedWeylGroupEquiv_smul]

/-- **Weyl-invariance of restricted root multiplicities** for `W(Σ_indiv)`. -/
theorem finrank_restrictedRootSpace_indivisible_smul
    (w : (hθ.indivisibleRestrictedRootPairing h𝔞).weylGroup) (ν : Dual ℝ 𝔞) :
    finrank ℝ (𝔞.restrictedRootSpace (w • ν)) =
      finrank ℝ (𝔞.restrictedRootSpace ν) := by
  have hw :=
    hθ.restrictedWeylGroupEquiv_smul h𝔞 ((hθ.restrictedWeylGroupEquiv h𝔞).symm w) ν
  rw [MulEquiv.apply_symm_apply] at hw
  rw [hw]
  exact hθ.finrank_restrictedRootSpace_smul h𝔞 _ ν

end WeylEquiv

end RootSystem

end LieEquiv.IsCartanInvolution
