/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Logic.Function.Basic
public import TauCeti.RepresentationTheory.Crystal.WeightTwist
public import TauCeti.RepresentationTheory.LSPath.Crystal.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import TauCeti.RepresentationTheory.LSPath.Concatenation
import TauCeti.RepresentationTheory.LSPath.LinearMap
import TauCeti.RepresentationTheory.LSPath.PartialInverse

/-!
# Categorical operations and simple-root strings on path crystals

This file equips the normal crystals of integral piecewise-linear paths from
`TauCeti.RepresentationTheory.LSPath.Crystal.Basic` with their categorical operations and
rank-one/isolated-node string examples:

* central straight paths `t ↦ t • f χ` (including the constant path `1` at `χ = 0`) realize the
  one-element central crystals `TauCeti.NormalCrystal.central` (`centralStraightIso`, `centralHom`,
  `oneHom`);
* path reversal `π ↦ π.reverse` preserves integral paths and gives an involutive strict crystal
  isomorphism `TauCeti.PLPath.reverseIso` from `(normalCrystal hf hF).dual` to
  `normalCrystal hf hF`;
* path concatenation `(π₁, π₂) ↦ π₁ * π₂` preserves crystal-admissible sets and integral paths and
  induces strict crystal morphisms `TauCeti.PLPath.mulOnHom` and `TauCeti.PLPath.mulHom` from the
  Kashiwara tensor product, compatible with the tensor associator and crystal duality and having the
  constant path `oneHom` as left and right identity;
* linear maps preserving the lattice embedding and the simple-coroot height forms push
  crystal-admissible sets and integral paths forward and induce strict crystal morphisms and
  isomorphisms (`TauCeti.PLPath.mapHom`, `TauCeti.PLPath.mapIso`);
* for any isolated simple node `i` (in particular on every rank-one root datum), the three-element
  simple-root string `{straight α_i, simpleRootBent, straight (-α_i)}` is crystal-admissible, and
  iterated concatenations `straight (-α_i)^n * straight α_i^n` witness that the zero-weight fibre
  of `normalCrystal` and the set of integral paths are infinite
  (`TauCeti.PLPath.infinite_zero_weight_normalCrystal_of_isolated`,
  `TauCeti.PLPath.infinite_isIntegralPath_of_isolated`).

## Main definitions

* `TauCeti.PLPath.centralStraightIso`, `TauCeti.PLPath.centralHom`, `TauCeti.PLPath.oneHom`:
  central straight paths and the constant path `1` as strict morphisms from
  `TauCeti.NormalCrystal.central`.
* `TauCeti.PLPath.reverseIso`: path reversal as a strict crystal isomorphism from
  `(normalCrystal hf hF).dual` to `normalCrystal hf hF`.
* `TauCeti.PLPath.mulOnHom`, `TauCeti.PLPath.mulHom`: path concatenation as strict crystal
  morphisms from the Kashiwara tensor product.
* `TauCeti.PLPath.mapHom`, `TauCeti.PLPath.mapIso`: strict crystal morphisms and isomorphisms
  induced by compatible linear maps and equivalences.
* `TauCeti.PLPath.simpleRootBent`: the zero-weight bent path at the middle of an isolated
  simple-root string.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1–2.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

public section

namespace TauCeti.PLPath

open Module Relation Set
open scoped Pointwise

section Realization

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-! ### Central straight paths and the constant path -/

section Central

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem apply_eq_zero_of_forall_coroot_eq_zero
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {χ : X} (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (i : b.support) :
    F i (f χ) = 0 := by
  simp [hF, RootPairing.coroot', hχ i]

/-- For a weight `χ` annihilating the simple coroots, the singleton `{straight 𝕜 (f χ)}` is
crystal-admissible: all simple-coroot heights along the straight path vanish, so every raising and
lowering operator returns `none`. -/
theorem isCrystalSet_singleton_straight
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {χ : X} (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    IsCrystalSet b f F {straight 𝕜 (f χ)} := by
  have hFχ := apply_eq_zero_of_forall_coroot_eq_zero hF hχ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ rfl
    exact ⟨χ, (endpoint_straight (f χ)).symm⟩
  · rintro _ rfl i
    exact ⟨0, by simp [hFχ i]⟩
  · rintro i _ π' hr rfl
    have hnone : raise (F i) (f (P.root i)) (straight 𝕜 (f χ)) = none := by
      rw [raise_eq_none_iff]
      simp [hFχ i]
    simp [hnone] at hr
  · rintro i _ π' hl rfl
    have hnone : lower (F i) (f (P.root i)) (straight 𝕜 (f χ)) = none := by
      rw [lower_eq_none_iff]
      simp [hFχ i]
    simp [hnone] at hl

/-- Every straight path along a central weight is an integral path. -/
theorem isIntegralPath_straight_of_forall_coroot_eq_zero
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {χ : X} (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    IsIntegralPath b f F (straight 𝕜 (f χ)) :=
  (isCrystalSet_singleton_straight hF hχ).subset_isIntegralPath rfl

/-- The constant path `1` is an integral path. -/
@[simp]
theorem isIntegralPath_one : IsIntegralPath b f F (1 : PLPath 𝕜 V) := by
  rw [isIntegralPath_iff]
  refine ⟨⟨0, by simp⟩, fun π' hwalk i ↦ ?_⟩
  have h1 : π' = 1 := by
    induction hwalk with
    | refl => rfl
    | tail _ hstep ih =>
      subst ih
      obtain ⟨j, hr | hl⟩ := rootStep_iff.mp hstep
      · simp [raise_eq_none_iff.mpr (by simp : (-1 : 𝕜) < (1 : PLPath 𝕜 V).minHeight (F j))] at hr
      · simp [lower_eq_none_iff.mpr
          (by simp : F j (1 : PLPath 𝕜 V).endpoint - (1 : PLPath 𝕜 V).minHeight (F j) < 1)] at hl
  exact ⟨0, by simp [h1]⟩

/-- The singleton path crystal `{straight 𝕜 (f χ)}` of a central weight `χ` is strictly isomorphic
to the one-element central crystal `NormalCrystal.central χ hχ`. -/
noncomputable def centralStraightIso (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    NormalCrystal.StrictIso (NormalCrystal.central χ hχ)
      (normalCrystalOn hf hF (isCrystalSet_singleton_straight hF hχ)) where
  toEquiv :=
    { toFun := fun _ ↦ ⟨straight 𝕜 (f χ), rfl⟩
      invFun := fun _ ↦ PUnit.unit
      left_inv := fun _ ↦ rfl
      right_inv := fun ⟨_, h⟩ ↦ Subtype.ext h.symm }
  wt_toFun _ := hf (by simp)
  e_toFun i _ := by simp [apply_eq_zero_of_forall_coroot_eq_zero hF hχ i]

@[simp]
theorem centralStraightIso_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (u : PUnit) :
    (centralStraightIso hf hF χ hχ u).1 = straight 𝕜 (f χ) :=
  (rfl)

/-- Embed the one-element central crystal of `χ` into `normalCrystal` as `straight 𝕜 (f χ)`. -/
noncomputable def centralHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    NormalCrystal.StrictHom (NormalCrystal.central χ hχ) (normalCrystal hf hF) :=
  (embedHom (isCrystalSet_singleton_straight hF hχ)).comp
    (centralStraightIso hf hF χ hχ).toStrictHom

@[simp]
theorem centralHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (u : PUnit) :
    (centralHom hf hF χ hχ u).1 = straight 𝕜 (f χ) := by
  simp [centralHom]

/-- The unit embedding of the trivial zero-weight crystal into `normalCrystal` as the constant path
`1`. -/
noncomputable def oneHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    NormalCrystal.StrictHom (NormalCrystal.central (P := P) (b := b) 0 (by simp))
      (normalCrystal hf hF) :=
  centralHom hf hF 0 (by simp)

@[simp]
theorem oneHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (u : PUnit) :
    (oneHom hf hF u).1 = 1 := by
  simp [oneHom]

end Central

/-! ### Path reversal and crystal duality -/

section Reversal

/-- Preimage under path reversal preserves crystal-admissibility. -/
theorem IsCrystalSet.preimage_reverse
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) :
    IsCrystalSet b f F (reverse ⁻¹' S) where
  endpoint_mem_range {π} hπ := by
    obtain ⟨μ, hμ⟩ := hS.endpoint_mem_range hπ
    exact ⟨-μ, by rw [map_neg, hμ, endpoint_reverse, neg_neg]⟩
  exists_minHeight_eq_intCast {π} hπ i := by
    obtain ⟨μ, hμ⟩ := hS.endpoint_mem_range hπ
    obtain ⟨z, hz⟩ := hS.exists_minHeight_eq_intCast hπ i
    refine ⟨z - P.coroot' i μ, ?_⟩
    have hrev := minHeight_reverse (f := F i) π.reverse
    rw [reverse_reverse] at hrev
    rw [hrev, hz, ← hμ, hF, Int.cast_sub]
  mem_of_raise_eq_some {i π π'} hr hπ := by
    have hl : lower (F i) (f (P.root i)) π.reverse = some π'.reverse := by
      rw [lower_reverse, hr, Option.map_some]
    exact hS.mem_of_lower_eq_some hl hπ
  mem_of_lower_eq_some {i π π'} hl hπ := by
    have hr : raise (F i) (f (P.root i)) π.reverse = some π'.reverse := by
      rw [raise_reverse, hl, Option.map_some]
    exact hS.mem_of_raise_eq_some hr hπ

/-- A path is integral if and only if its reversal is integral. -/
theorem isIntegralPath_reverse_iff
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {π : PLPath 𝕜 V} :
    IsIntegralPath b f F π.reverse ↔ IsIntegralPath b f F π := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hmem : π.reverse.reverse ∈ reverse ⁻¹' {ρ | IsIntegralPath b f F ρ} := by
      simpa using h
    exact (isCrystalSet_setOf_isIntegralPath.preimage_reverse hF).subset_isIntegralPath
      (by simpa using hmem)
  · exact (isCrystalSet_setOf_isIntegralPath.preimage_reverse hF).subset_isIntegralPath
      (by simpa using h)

theorem IsIntegralPath.reverse
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {π : PLPath 𝕜 V} (h : IsIntegralPath b f F π) :
    IsIntegralPath b f F π.reverse :=
  (isIntegralPath_reverse_iff hF).mpr h

/-- **Path reversal realizes crystal duality**: `π ↦ π.reverse` is a strict isomorphism from the
dual of Littelmann's integral-path crystal to itself. -/
noncomputable def reverseIso (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    NormalCrystal.StrictIso (normalCrystal hf hF).dual (normalCrystal hf hF) where
  toEquiv :=
    { toFun := fun π ↦ ⟨π.1.reverse, π.2.reverse hF⟩
      invFun := fun π ↦ ⟨π.1.reverse, π.2.reverse hF⟩
      left_inv := fun π ↦ Subtype.ext (reverse_reverse π.1)
      right_inv := fun π ↦ Subtype.ext (reverse_reverse π.1) }
  wt_toFun π := hf (by simp)
  e_toFun i π := by simp [normalCrystalOn_e_eq_map_iff, raise_reverse]

@[simp]
theorem reverseIso_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (π : {π : PLPath 𝕜 V | IsIntegralPath b f F π}) :
    (reverseIso hf hF π).1 = π.1.reverse :=
  (rfl)

@[simp]
theorem reverseIso_symm_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (π : {π : PLPath 𝕜 V | IsIntegralPath b f F π}) :
    ((reverseIso hf hF).symm π).1 = π.1.reverse := by
  have h := congrArg (fun x ↦ x.1.reverse) ((reverseIso hf hF).apply_symm_apply π)
  rwa [reverseIso_apply, reverse_reverse] at h

/-- Applying `reverseIso` twice returns the original integral path. -/
@[simp]
theorem reverseIso_reverseIso (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (π : {π : PLPath 𝕜 V | IsIntegralPath b f F π}) :
    reverseIso hf hF (reverseIso hf hF π) = π :=
  Subtype.ext (reverse_reverse π.1)

end Reversal

/-! ### Path concatenation and crystal tensor products -/

section Concatenation

private theorem exists_gap_eq_intCast
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S₁ S₂ : Set (PLPath 𝕜 V)} (h₁ : IsCrystalSet b f F S₁) (h₂ : IsCrystalSet b f F S₂)
    {π₁ π₂ : PLPath 𝕜 V} (hπ₁ : π₁ ∈ S₁) (hπ₂ : π₂ ∈ S₂) (i : b.support) :
    ∃ n : ℤ, F i π₁.endpoint - π₁.minHeight (F i) + π₂.minHeight (F i) = (n : 𝕜) := by
  obtain ⟨μ₁, hμ₁⟩ := h₁.endpoint_mem_range hπ₁
  obtain ⟨z₁, hz₁⟩ := h₁.exists_minHeight_eq_intCast hπ₁ i
  obtain ⟨z₂, hz₂⟩ := h₂.exists_minHeight_eq_intCast hπ₂ i
  exact ⟨P.coroot' i μ₁ - z₁ + z₂, by rw [← hμ₁, hF, hz₁, hz₂]; push_cast; ring⟩

/-- Pointwise concatenation `S₁ * S₂` of two crystal-admissible path sets is crystal-admissible. -/
theorem IsCrystalSet.mul (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S₁ S₂ : Set (PLPath 𝕜 V)} (h₁ : IsCrystalSet b f F S₁) (h₂ : IsCrystalSet b f F S₂) :
    IsCrystalSet b f F (S₁ * S₂) where
  endpoint_mem_range := by
    rintro _ ⟨π₁, hπ₁, π₂, hπ₂, rfl⟩
    obtain ⟨μ₁, hμ₁⟩ := h₁.endpoint_mem_range hπ₁
    obtain ⟨μ₂, hμ₂⟩ := h₂.endpoint_mem_range hπ₂
    exact ⟨μ₁ + μ₂, by rw [map_add, hμ₁, hμ₂, endpoint_mul]⟩
  exists_minHeight_eq_intCast := by
    rintro _ ⟨π₁, hπ₁, π₂, hπ₂, rfl⟩ i
    obtain ⟨μ₁, hμ₁⟩ := h₁.endpoint_mem_range hπ₁
    obtain ⟨z₁, hz₁⟩ := h₁.exists_minHeight_eq_intCast hπ₁ i
    obtain ⟨z₂, hz₂⟩ := h₂.exists_minHeight_eq_intCast hπ₂ i
    refine ⟨min z₁ (P.coroot' i μ₁ + z₂), ?_⟩
    rw [minHeight_mul, hz₁, hz₂, ← hμ₁, hF, ← Int.cast_add, Int.cast_min]
  mem_of_raise_eq_some := by
    rintro i _ ρ' hr ⟨π₁, hπ₁, π₂, hπ₂, rfl⟩
    rw [raise_mul (exists_gap_eq_intCast hF h₁ h₂ hπ₁ hπ₂ i)] at hr
    split_ifs at hr
    · obtain ⟨π₁', hπ₁', rfl⟩ := Option.map_eq_some_iff.mp hr
      exact ⟨π₁', h₁.mem_of_raise_eq_some hπ₁' hπ₁, π₂, hπ₂, rfl⟩
    · obtain ⟨π₂', hπ₂', rfl⟩ := Option.map_eq_some_iff.mp hr
      exact ⟨π₁, hπ₁, π₂', h₂.mem_of_raise_eq_some hπ₂' hπ₂, rfl⟩
  mem_of_lower_eq_some := by
    rintro i _ ρ' hl ⟨π₁, hπ₁, π₂, hπ₂, rfl⟩
    rw [lower_mul (exists_gap_eq_intCast hF h₁ h₂ hπ₁ hπ₂ i)] at hl
    split_ifs at hl
    · obtain ⟨π₁', hπ₁', rfl⟩ := Option.map_eq_some_iff.mp hl
      exact ⟨π₁', h₁.mem_of_lower_eq_some hπ₁' hπ₁, π₂, hπ₂, rfl⟩
    · obtain ⟨π₂', hπ₂', rfl⟩ := Option.map_eq_some_iff.mp hl
      exact ⟨π₁, hπ₁, π₂', h₂.mem_of_lower_eq_some hπ₂' hπ₂, rfl⟩

/-- **Concatenation preserves integral paths.** -/
theorem IsIntegralPath.mul (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {π₁ π₂ : PLPath 𝕜 V} (h₁ : IsIntegralPath b f F π₁) (h₂ : IsIntegralPath b f F π₂) :
    IsIntegralPath b f F (π₁ * π₂) :=
  (isCrystalSet_setOf_isIntegralPath.mul hF isCrystalSet_setOf_isIntegralPath).subset_isIntegralPath
    ⟨π₁, h₁, π₂, h₂, rfl⟩

/-- Concatenation powers of an integral path are integral paths. -/
theorem IsIntegralPath.pow (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {π : PLPath 𝕜 V} (h : IsIntegralPath b f F π) (n : ℕ) :
    IsIntegralPath b f F (π ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact ih.mul hF h

/-- Path concatenation induces a strict crystal morphism from the Kashiwara tensor product of two
`normalCrystalOn` crystals to any `normalCrystalOn` crystal containing their concatenations. -/
noncomputable def mulOnHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S₁ S₂ T : Set (PLPath 𝕜 V)} (h₁ : IsCrystalSet b f F S₁) (h₂ : IsCrystalSet b f F S₂)
    (hT : IsCrystalSet b f F T) (hmul : ∀ ⦃π₁⦄, π₁ ∈ S₁ → ∀ ⦃π₂⦄, π₂ ∈ S₂ → π₁ * π₂ ∈ T) :
    NormalCrystal.StrictHom
      ((normalCrystalOn hf hF h₁).tensor (normalCrystalOn hf hF h₂))
      (normalCrystalOn hf hF hT) where
  toFun x := ⟨x.1.1 * x.2.1, hmul x.1.2 x.2.2⟩
  wt_toFun x := hf (by simp)
  e_toFun i x := by
    obtain ⟨x₁, x₂⟩ := x
    by_cases hle : (normalCrystalOn hf hF h₂).ε i x₂ ≤ (normalCrystalOn hf hF h₁).φ i x₁
    · have hle' : -x₂.1.minHeight (F i) ≤ F i x₁.1.endpoint - x₁.1.minHeight (F i) := by
        have : ((normalCrystalOn hf hF h₂).ε i x₂ : 𝕜) ≤ (normalCrystalOn hf hF h₁).φ i x₁ := by
          exact_mod_cast hle
        simpa [cast_normalCrystalOn_ε, cast_normalCrystalOn_φ] using this
      simp [NormalCrystal.tensor_e_of_le hle, Option.map_map, normalCrystalOn_e_eq_map_iff,
        Function.comp_def, raise_mul_of_le (x := f (P.root i)) hle']
    · have hlt : (normalCrystalOn hf hF h₁).φ i x₁ < (normalCrystalOn hf hF h₂).ε i x₂ :=
        Nat.lt_of_not_ge hle
      have hr : F i x₁.1.endpoint - x₁.1.minHeight (F i) + 1 ≤ -x₂.1.minHeight (F i) := by
        have : (((normalCrystalOn hf hF h₁).φ i x₁ + 1 : ℕ) : 𝕜) ≤
            (normalCrystalOn hf hF h₂).ε i x₂ := by exact_mod_cast hlt
        simpa [cast_normalCrystalOn_φ, cast_normalCrystalOn_ε] using this
      simp [NormalCrystal.tensor_e_of_lt hlt, Option.map_map, normalCrystalOn_e_eq_map_iff,
        Function.comp_def, raise_mul_of_add_one_le (x := f (P.root i)) hr]

@[simp]
theorem mulOnHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S₁ S₂ T : Set (PLPath 𝕜 V)} (h₁ : IsCrystalSet b f F S₁) (h₂ : IsCrystalSet b f F S₂)
    (hT : IsCrystalSet b f F T) (hmul : ∀ ⦃π₁⦄, π₁ ∈ S₁ → ∀ ⦃π₂⦄, π₂ ∈ S₂ → π₁ * π₂ ∈ T)
    (x : S₁ × S₂) :
    (mulOnHom hf hF h₁ h₂ hT hmul x).1 = x.1.1 * x.2.1 :=
  (rfl)

/-- **Path concatenation realizes the crystal tensor product** (with Kashiwara's tie convention) as
a strict morphism `(normalCrystal hf hF) ⊗ (normalCrystal hf hF) → normalCrystal hf hF`. -/
noncomputable def mulHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    NormalCrystal.StrictHom
      ((normalCrystal hf hF).tensor (normalCrystal hf hF))
      (normalCrystal hf hF) :=
  mulOnHom hf hF isCrystalSet_setOf_isIntegralPath isCrystalSet_setOf_isIntegralPath
    isCrystalSet_setOf_isIntegralPath fun _ h₁ _ h₂ ↦ h₁.mul hF h₂

@[simp]
theorem mulHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (x : {π : PLPath 𝕜 V | IsIntegralPath b f F π} × {π : PLPath 𝕜 V | IsIntegralPath b f F π}) :
    (mulHom hf hF x).1 = x.1.1 * x.2.1 :=
  (rfl)

/-- Associativity of path concatenation matches the crystal tensor associator. -/
theorem mulHom_comp_tensorAssoc (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    ((mulHom hf hF).comp
        ((NormalCrystal.StrictHom.id (normalCrystal hf hF)).tensor (mulHom hf hF))).comp
        ((normalCrystal hf hF).tensorAssoc (normalCrystal hf hF) (normalCrystal hf hF)) =
      (mulHom hf hF).comp
        ((mulHom hf hF).tensor (NormalCrystal.StrictHom.id (normalCrystal hf hF))) :=
  NormalCrystal.StrictHom.ext fun _ ↦ Subtype.ext (by simp [mul_assoc])

/-- Reversing a concatenation matches the swapped dual tensor morphism `(B ⊗ B)^∨ → B^∨ ⊗ B^∨`. -/
theorem reverseIso_comp_mulHom_dual (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    (reverseIso hf hF).toStrictHom.comp (mulHom hf hF).dual =
      ((mulHom hf hF).comp
        ((reverseIso hf hF).toStrictHom.tensor (reverseIso hf hF).toStrictHom)).comp
        ((normalCrystal hf hF).dualTensor (normalCrystal hf hF)) :=
  NormalCrystal.StrictHom.ext fun _ ↦ Subtype.ext (by simp)

/-- Concatenating the constant path `1` (the image of `oneHom`) on the left returns the path. -/
@[simp]
theorem mulHom_oneHom_left (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (u : PUnit) (x : {π : PLPath 𝕜 V | IsIntegralPath b f F π}) :
    mulHom hf hF (oneHom hf hF u, x) = x :=
  Subtype.ext (by simp)

/-- Concatenating the constant path `1` (the image of `oneHom`) on the right returns the path. -/
@[simp]
theorem mulHom_oneHom_right (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (x : {π : PLPath 𝕜 V | IsIntegralPath b f F π}) (u : PUnit) :
    mulHom hf hF (x, oneHom hf hF u) = x :=
  Subtype.ext (by simp)

end Concatenation

/-! ### Functoriality under compatible linear maps -/

section LinearMap

variable {W : Type*} [AddCommGroup W] [Module 𝕜 W]
  {f' : X →+ W} {F' : b.support → Dual 𝕜 W}

/-- Compatible linear maps preserve crystal-admissible sets of paths, even when `g` collapses
stationary directions in the kernel of all simple coroots. -/
theorem IsCrystalSet.image_map {g : V →ₗ[𝕜] W}
    (hgf : ∀ x, g (f x) = f' x) (hFg : ∀ i, (F' i).comp g = F i)
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) :
    IsCrystalSet b f' F' ((·.map g) '' S) where
  endpoint_mem_range := by
    rintro _ ⟨π, hπ, rfl⟩
    obtain ⟨μ, hμ⟩ := hS.endpoint_mem_range hπ
    exact ⟨μ, by rw [← hgf, hμ, endpoint_map]⟩
  exists_minHeight_eq_intCast := by
    rintro _ ⟨π, hπ, rfl⟩ i
    obtain ⟨z, hz⟩ := hS.exists_minHeight_eq_intCast hπ i
    exact ⟨z, by rw [minHeight_map, hFg i, hz]⟩
  mem_of_raise_eq_some := by
    rintro i _ ρ hr ⟨π, hπ, rfl⟩
    rw [← hgf (P.root i), raise_map π (hFg i), Option.map_eq_some_iff] at hr
    obtain ⟨π', hπ', hmap⟩ := hr
    exact ⟨π', hS.mem_of_raise_eq_some hπ' hπ, hmap⟩
  mem_of_lower_eq_some := by
    rintro i _ ρ hl ⟨π, hπ, rfl⟩
    rw [← hgf (P.root i), lower_map π (hFg i), Option.map_eq_some_iff] at hl
    obtain ⟨π', hπ', hmap⟩ := hl
    exact ⟨π', hS.mem_of_lower_eq_some hπ' hπ, hmap⟩

/-- Compatible linear maps send integral paths to integral paths. -/
theorem IsIntegralPath.map {g : V →ₗ[𝕜] W}
    (hgf : ∀ x, g (f x) = f' x) (hFg : ∀ i, (F' i).comp g = F i)
    {π : PLPath 𝕜 V} (h : IsIntegralPath b f F π) :
    IsIntegralPath b f' F' (π.map g) :=
  (isCrystalSet_setOf_isIntegralPath.image_map hgf hFg).subset_isIntegralPath ⟨π, h, rfl⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- If a linear map `g` intertwines two weight realizations `(f, F)` and `(f', F')` and `F'` agrees
with the simple coroots on `f'(X)`, then so does `F` on `f(X)`. -/
theorem apply_eq_coroot'_of_comp
    (hF' : ∀ (i : b.support) (x : X), F' i (f' x) = (P.coroot' i x : 𝕜))
    {g : V →ₗ[𝕜] W} (hgf : ∀ x, g (f x) = f' x) (hFg : ∀ i, (F' i).comp g = F i)
    (i : b.support) (x : X) :
    F i (f x) = (P.coroot' i x : 𝕜) := by
  rw [← hFg i, LinearMap.comp_apply, hgf, hF']

/-- A linear map intertwining two realizations `(f, F)` and `(f', F')` induces a strict crystal
morphism between their integral-path crystals. -/
noncomputable def mapHom (hf' : Function.Injective f')
    (hF' : ∀ (i : b.support) (x : X), F' i (f' x) = (P.coroot' i x : 𝕜))
    (g : V →ₗ[𝕜] W) (hgf : ∀ x, g (f x) = f' x) (hFg : ∀ i, (F' i).comp g = F i) :
    NormalCrystal.StrictHom
      (normalCrystal (f := f) (F := F) (hf'.of_comp_eq hgf)
        (apply_eq_coroot'_of_comp hF' hgf hFg))
      (normalCrystal hf' hF') where
  toFun π := ⟨π.1.map g, π.2.map hgf hFg⟩
  wt_toFun π := hf' (by
    rw [apply_normalCrystalOn_wt, endpoint_map, ← hgf, apply_normalCrystalOn_wt])
  e_toFun i π := by simp [normalCrystalOn_e_eq_map_iff, ← hgf, raise_map π.1 (hFg i)]

@[simp]
theorem mapHom_apply (hf' : Function.Injective f')
    (hF' : ∀ (i : b.support) (x : X), F' i (f' x) = (P.coroot' i x : 𝕜))
    (g : V →ₗ[𝕜] W) (hgf : ∀ x, g (f x) = f' x) (hFg : ∀ i, (F' i).comp g = F i)
    (π : {π : PLPath 𝕜 V | IsIntegralPath b f F π}) :
    (mapHom hf' hF' g hgf hFg π).1 = π.1.map g :=
  (rfl)

/-- A linear equivalence intertwining two realizations induces a strict crystal isomorphism between
their integral-path crystals. -/
noncomputable def mapIso (hf' : Function.Injective f')
    (hF' : ∀ (i : b.support) (x : X), F' i (f' x) = (P.coroot' i x : 𝕜))
    (e : V ≃ₗ[𝕜] W) (hef : ∀ x, e (f x) = f' x) (hFe : ∀ i, (F' i).comp e.toLinearMap = F i) :
    NormalCrystal.StrictIso
      (normalCrystal (f := f) (F := F) (hf'.of_comp_eq hef)
        (apply_eq_coroot'_of_comp hF' hef hFe))
      (normalCrystal hf' hF') := by
  have hef_symm (x : X) : e.symm (f' x) = f x := e.symm_apply_eq.mpr (hef x).symm
  have hFe_symm (i : b.support) : (F i).comp e.symm.toLinearMap = F' i := by
    ext w
    simp [← hFe i]
  refine
    { toEquiv :=
        { toFun := mapHom hf' hF' e.toLinearMap hef hFe
          invFun := mapHom (f := f') (F := F') (hf'.of_comp_eq hef)
            (apply_eq_coroot'_of_comp hF' hef hFe) e.symm.toLinearMap hef_symm hFe_symm
          left_inv := fun π ↦ Subtype.ext (by simp)
          right_inv := fun π ↦ Subtype.ext (by simp) }
      wt_toFun := (mapHom hf' hF' e.toLinearMap hef hFe).wt_toFun
      e_toFun := (mapHom hf' hF' e.toLinearMap hef hFe).e_toFun }

@[simp]
theorem mapIso_apply (hf' : Function.Injective f')
    (hF' : ∀ (i : b.support) (x : X), F' i (f' x) = (P.coroot' i x : 𝕜))
    (e : V ≃ₗ[𝕜] W) (hef : ∀ x, e (f x) = f' x) (hFe : ∀ i, (F' i).comp e.toLinearMap = F i)
    (π : {π : PLPath 𝕜 V | IsIntegralPath b f F π}) :
    (mapIso hf' hF' e hef hFe π).1 = π.1.map e.toLinearMap :=
  (rfl)

@[simp]
theorem mapIso_symm_apply (hf' : Function.Injective f')
    (hF' : ∀ (i : b.support) (x : X), F' i (f' x) = (P.coroot' i x : 𝕜))
    (e : V ≃ₗ[𝕜] W) (hef : ∀ x, e (f x) = f' x) (hFe : ∀ i, (F' i).comp e.toLinearMap = F i)
    (π : {π : PLPath 𝕜 W | IsIntegralPath b f' F' π}) :
    ((mapIso hf' hF' e hef hFe).symm π).1 = π.1.map e.symm.toLinearMap := by
  have h := congrArg (fun x ↦ x.1.map e.symm.toLinearMap)
    ((mapIso hf' hF' e hef hFe).apply_symm_apply π)
  rw [mapIso_apply, map_map] at h
  simpa using h

end LinearMap

/-! ### Isolated simple-root strings and infiniteness of the zero-weight fibre -/

section SimpleRootString

variable (𝕜) in
/-- The zero-weight bent path `-(1/2) α_i` followed by `(1/2) α_i` obtained by lowering the
straight simple-root path `t ↦ t • α_i` once. -/
noncomputable def simpleRootBent (f : X →+ V) (i : b.support) : PLPath 𝕜 V :=
  straight 𝕜 (-(2 : 𝕜)⁻¹ • f (P.root i)) * straight 𝕜 ((2 : 𝕜)⁻¹ • f (P.root i))

@[simp]
theorem endpoint_simpleRootBent (i : b.support) :
    (simpleRootBent 𝕜 f i).endpoint = 0 := by
  simp [simpleRootBent]

@[simp]
theorem reverse_simpleRootBent (i : b.support) :
    (simpleRootBent 𝕜 f i).reverse = simpleRootBent 𝕜 f i := by
  simp [simpleRootBent]

theorem minHeight_simpleRootBent_self
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    (simpleRootBent 𝕜 f i).minHeight (F i) = -1 := by
  rw [simpleRootBent, neg_smul, minHeight_straight_neg_mul_straight]
  simp only [map_smul, smul_eq_mul, apply_root_eq_two hF i]
  norm_num

/-- Lowering the straight simple-root path `t ↦ t • α_i` gives `simpleRootBent`. -/
theorem lower_straight_root
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    lower (F i) (f (P.root i)) (straight 𝕜 (f (P.root i))) = some (simpleRootBent 𝕜 f i) := by
  have hv := apply_root_eq_two hF i
  rw [lower_straight (by linarith : (1 : 𝕜) ≤ F i (f (P.root i))), hv]
  congr 1
  have hrefl :
      preReflection (f (P.root i)) (F i) ((2 : 𝕜)⁻¹ • f (P.root i)) =
        -(2 : 𝕜)⁻¹ • f (P.root i) := by
    rw [preReflection_apply, map_smul, hv, smul_eq_mul]
    have h1 : (2 : 𝕜)⁻¹ * 2 = 1 := inv_mul_cancel₀ two_ne_zero
    rw [h1, one_smul]
    module
  have hsub : (1 - (2 : 𝕜)⁻¹) = (2 : 𝕜)⁻¹ := by norm_num
  rw [hrefl, hsub, simpleRootBent]

/-- Raising `simpleRootBent` recovers `straight 𝕜 (f (P.root i))`. -/
theorem raise_simpleRootBent
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    raise (F i) (f (P.root i)) (simpleRootBent 𝕜 f i) = some (straight 𝕜 (f (P.root i))) :=
  (lower_eq_some_iff (apply_root_eq_two hF i)).mp (lower_straight_root hF i)

/-- Lowering `simpleRootBent` gives the opposite straight simple-root path `t ↦ -t • α_i`. -/
theorem lower_simpleRootBent
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    lower (F i) (f (P.root i)) (simpleRootBent 𝕜 f i) = some (straight 𝕜 (-f (P.root i))) := by
  conv_lhs => rw [← reverse_simpleRootBent (f := f) i]
  rw [lower_reverse, raise_simpleRootBent hF i, Option.map_some, reverse_straight]

/-- Raising `straight 𝕜 (-f (P.root i))` gives `simpleRootBent`. -/
theorem raise_straight_neg_root
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    raise (F i) (f (P.root i)) (straight 𝕜 (-f (P.root i))) = some (simpleRootBent 𝕜 f i) :=
  (lower_eq_some_iff (apply_root_eq_two hF i)).mp (lower_simpleRootBent hF i)

/-- For an isolated simple node `i` (`⟨α_i, α_j^∨⟩ = 0` for all `j ≠ i`, in particular in rank
one), the three-element simple-root string `{straight α_i, simpleRootBent, straight (-α_i)}` is
crystal-admissible. -/
theorem isCrystalSet_simpleRootString
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support)
    (hi : ∀ j : b.support, j ≠ i → P.pairing i.1 j.1 = 0) :
    IsCrystalSet b f F
      {straight 𝕜 (f (P.root i)), simpleRootBent 𝕜 f i, straight 𝕜 (-f (P.root i))} := by
  have hv := apply_root_eq_two hF i
  have hFj {j : b.support} (hj : j ≠ i) : F j (f (P.root i)) = 0 := by
    rw [hF, P.root_coroot'_eq_pairing, hi j hj, Int.cast_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ (rfl | rfl | rfl)
    · exact ⟨P.root i, (endpoint_straight _).symm⟩
    · exact ⟨0, by simp⟩
    · exact ⟨-P.root i, by simp⟩
  · intro π hπ j
    by_cases hj : j = i
    · subst hj
      rcases hπ with rfl | rfl | rfl
      · exact ⟨0, by simp [hv]⟩
      · exact ⟨-1, by simp [minHeight_simpleRootBent_self hF j]⟩
      · exact ⟨-2, by simp [hv]⟩
    · rcases hπ with rfl | rfl | rfl <;> exact ⟨0, by simp [simpleRootBent, hFj hj]⟩
  · intro j π π' hr hπ
    by_cases hj : j = i
    · subst hj
      rcases hπ with rfl | rfl | rfl
      · nomatch hr.symm.trans (by simp [hv] : _ = none)
      · rw [raise_simpleRootBent hF j, Option.some.injEq] at hr; exact hr ▸ Or.inl rfl
      · rw [raise_straight_neg_root hF j, Option.some.injEq] at hr; exact hr ▸ Or.inr (Or.inl rfl)
    · rcases hπ with rfl | rfl | rfl <;>
        nomatch hr.symm.trans (by simp [simpleRootBent, hFj hj] : _ = none)
  · intro j π π' hl hπ
    by_cases hj : j = i
    · subst hj
      rcases hπ with rfl | rfl | rfl
      · rw [lower_straight_root hF j, Option.some.injEq] at hl; exact hl ▸ Or.inr (Or.inl rfl)
      · rw [lower_simpleRootBent hF j, Option.some.injEq] at hl; exact hl ▸ Or.inr (Or.inr rfl)
      · nomatch hl.symm.trans (by simp [hv] : _ = none)
    · rcases hπ with rfl | rfl | rfl <;>
        nomatch hl.symm.trans (by simp [simpleRootBent, hFj hj] : _ = none)

/-- For an isolated simple node `i`, the straight simple-root path `straight 𝕜 (f (P.root i))` is
an integral path. -/
theorem isIntegralPath_straight_root
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support)
    (hi : ∀ j : b.support, j ≠ i → P.pairing i.1 j.1 = 0) :
    IsIntegralPath b f F (straight 𝕜 (f (P.root i))) :=
  (isCrystalSet_simpleRootString hF i hi).subset_isIntegralPath (Or.inl rfl)

private theorem infinite_subtype_endpoint_eq_zero_isIntegralPath_of_isolated
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support)
    (hi : ∀ j : b.support, j ≠ i → P.pairing i.1 j.1 = 0) :
    Infinite {π : PLPath 𝕜 V // π.endpoint = 0 ∧ IsIntegralPath b f F π} := by
  have hv := apply_root_eq_two hF i
  have hpos_int := isIntegralPath_straight_root hF i hi
  have hneg_int : IsIntegralPath b f F (straight 𝕜 (-f (P.root i))) := by
    simpa using hpos_int.reverse hF
  refine Infinite.of_injective
    (fun n : ℕ ↦ ⟨straight 𝕜 (-f (P.root i)) ^ n * straight 𝕜 (f (P.root i)) ^ n,
      by simp [← straight_natCast_smul], (hneg_int.pow hF n).mul hF (hpos_int.pow hF n)⟩)
    fun m n hmn ↦ ?_
  have hmin (k : ℕ) :
      (straight 𝕜 (-f (P.root i)) ^ k * straight 𝕜 (f (P.root i)) ^ k).minHeight (F i) =
        -((2 * k : ℕ) : 𝕜) := by
    rw [← straight_natCast_smul, ← straight_natCast_smul, smul_neg,
      minHeight_straight_neg_mul_straight]
    simp only [map_smul, smul_eq_mul, hv, Nat.cast_mul, Nat.cast_ofNat]
    rw [min_eq_right (neg_nonpos.mpr (by positivity)), mul_comm]
  have hval :
      straight 𝕜 (-f (P.root i)) ^ m * straight 𝕜 (f (P.root i)) ^ m =
        straight 𝕜 (-f (P.root i)) ^ n * straight 𝕜 (f (P.root i)) ^ n :=
    congrArg Subtype.val hmn
  have heq : -((2 * m : ℕ) : 𝕜) = -((2 * n : ℕ) : 𝕜) := by
    rw [← hmin m, ← hmin n, hval]
  have hnat : 2 * m = 2 * n := Nat.cast_injective (R := 𝕜) (neg_inj.mp heq)
  omega

/-- **The ambient integral-path crystal has an infinite zero-weight fibre** whenever `b.support`
contains an isolated simple node `i` (in particular for every rank-one root datum): the paths
`straight 𝕜 (-f α_i) ^ n * straight 𝕜 (f α_i) ^ n` all have weight `0`, while `ε_i` takes the
distinct values `2 n` on them. -/
theorem infinite_zero_weight_normalCrystal_of_isolated (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support)
    (hi : ∀ j : b.support, j ≠ i → P.pairing i.1 j.1 = 0) :
    Infinite
      {x : {π : PLPath 𝕜 V | IsIntegralPath b f F π} // (normalCrystal hf hF).wt x = 0} := by
  have := infinite_subtype_endpoint_eq_zero_isIntegralPath_of_isolated hF i hi
  exact Infinite.of_injective
    (fun x : {π : PLPath 𝕜 V // π.endpoint = 0 ∧ IsIntegralPath b f F π} ↦
      ⟨⟨x.1, x.2.2⟩, normalCrystalOn_wt_eq_iff.mpr (by simp [x.2.1])⟩)
    fun _ _ h ↦ Subtype.ext (congrArg (fun z ↦ z.1.1) h)

/-- Over any rank-one root datum (`Nonempty b.support` and `Subsingleton b.support`), the
zero-weight fibre of Littelmann's ambient integral-path crystal is infinite. -/
theorem infinite_zero_weight_normalCrystal [Nonempty b.support] [Subsingleton b.support]
    (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    Infinite
      {x : {π : PLPath 𝕜 V | IsIntegralPath b f F π} // (normalCrystal hf hF).wt x = 0} := by
  obtain ⟨i⟩ := ‹Nonempty b.support›
  exact infinite_zero_weight_normalCrystal_of_isolated hf hF i
    fun j hj ↦ absurd (Subsingleton.elim j i) hj

/-- Whenever `b.support` contains an isolated simple node `i`, the set of integral paths is
infinite. -/
theorem infinite_isIntegralPath_of_isolated
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support)
    (hi : ∀ j : b.support, j ≠ i → P.pairing i.1 j.1 = 0) :
    Infinite {π : PLPath 𝕜 V | IsIntegralPath b f F π} := by
  have := infinite_subtype_endpoint_eq_zero_isIntegralPath_of_isolated hF i hi
  exact Infinite.of_injective
    (fun x : {π : PLPath 𝕜 V // π.endpoint = 0 ∧ IsIntegralPath b f F π} ↦ ⟨x.1, x.2.2⟩)
    fun _ _ h ↦ Subtype.ext (congrArg (fun z ↦ z.1) h)

/-- Over any rank-one root datum, Littelmann's ambient crystal of integral paths is infinite. -/
theorem infinite_isIntegralPath [Nonempty b.support] [Subsingleton b.support]
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    Infinite {π : PLPath 𝕜 V | IsIntegralPath b f F π} := by
  obtain ⟨i⟩ := ‹Nonempty b.support›
  exact infinite_isIntegralPath_of_isolated hF i fun j hj ↦ absurd (Subsingleton.elim j i) hj

end SimpleRootString

end Realization

end TauCeti.PLPath
