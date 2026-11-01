/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Vector

/-!
# The structure constants of the pinned Chevalley system

`TauCeti.DynkinType.chevalleySystem` names a root vector `e_α` of the pinned rational Lie algebra
`TauCeti.DynkinType.lieAlgebra` for every root number `α : Fin t.numRoots` of
`TauCeti.DynkinType.simplyConnectedRootDatum`, and these root vectors form a Chevalley system for
the signed Chevalley involution `ω`. This file records the integers `N_{α,β}` with

```text
⁅e_α, e_β⁆ = N_{α,β} e_{α+β}      whenever α + β is a root,
```

as the integer-valued function `TauCeti.DynkinType.structureConstant` on pairs of root numbers,
with the convention `N_{α,β} = 0` when `α + β` is not a root. Chevalley's theorem pins the value up
to sign: `N_{α,β} = ±(r + 1)`, where `r` is the largest integer with `β - r α` a root, the
descending root-string coefficient `chainBotCoeff α β` of the pinned datum. The constants are
skew-symmetric, and compatibility of the root vectors with `ω` gives the Chevalley relation
`N_{-α,-β} = -N_{α,β}`. Root sums and root strings are read in the integral datum throughout, so
that the constants can be used in the root numbering without passing through the Lie weights.

When `α + β` is neither a root nor zero the bracket `⁅e_α, e_β⁆` vanishes, so together with the
normalization `⁅e_α, e_{-α}⁆ = h_α` of `TauCeti.DynkinType.lie_chevalleySystem_reflectionPerm_self`
the structure constants describe every bracket of two root vectors. These integers are the input
to the Chevalley commutator formula for the root subgroups `x_α(u) = Σₙ uⁿ ρ(e_α)⁽ⁿ⁾`.

## Main definitions

* `TauCeti.DynkinType.structureConstant`: the integer `N_{α,β}`.

## Main results

* `TauCeti.DynkinType.lie_chevalleySystem_eq_structureConstant_zsmul` and
  `TauCeti.DynkinType.eq_structureConstant_iff`: the defining bracket equation and its uniqueness.
* `TauCeti.DynkinType.structureConstant_eq_natCast_or_eq_neg_natCast`: `N_{α,β} = ±(r + 1)`.
* `TauCeti.DynkinType.structureConstant_ne_zero` and `TauCeti.DynkinType.structureConstant_eq_zero`:
  the constant vanishes exactly when `α + β` is not a root.
* `TauCeti.DynkinType.structureConstant_skew`: `N_{β,α} = -N_{α,β}`.
* `TauCeti.DynkinType.structureConstant_reflectionPerm_self_reflectionPerm_self`:
  `N_{-α,-β} = -N_{α,β}`.
* `TauCeti.DynkinType.lie_chevalleySystem_eq_zero`: `⁅e_α, e_β⁆ = 0` when `α + β` is neither a
  root nor zero.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 1, Theorem 1.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling LieModule

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **The structure constants of the pinned Chevalley system.** For root numbers `α` and `β`, the
integer `N_{α,β}` with `⁅e_α, e_β⁆ = N_{α,β} e_γ` when root `γ` of the pinned datum is the sum of
roots `α` and `β`, and `0` when `α + β` is not a root. Here `e` is
`TauCeti.DynkinType.chevalleySystem`. When `α + β` is a root, the value is `±(r + 1)` for
`r = chainBotCoeff α β`, by `TauCeti.DynkinType.structureConstant_eq_natCast_or_eq_neg_natCast`. -/
def structureConstant (α β : Fin t.numRoots) : ℤ :=
  if h : ∃ γ, (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β then
    (t.isChevalleySystem_chevalleySystem ht).intStructureConstant (t.rootEquiv ht α)
      (t.rootEquiv ht β) (t.rootEquiv ht h.choose) (LieSubalgebra.isNonZero_coe_root _)
      (coe_rootEquiv_eq_add_iff.2 h.choose_spec)
  else 0

variable {t ht}

/-- At a genuine root sum `γ = α + β`, the structure constant is the integer structure constant
of the weight-indexed Chevalley system at the three enumerated roots. -/
private theorem structureConstant_eq_intStructureConstant {α β γ : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β) :
    t.structureConstant ht α β =
      (t.isChevalleySystem_chevalleySystem ht).intStructureConstant (t.rootEquiv ht α)
        (t.rootEquiv ht β) (t.rootEquiv ht γ) (LieSubalgebra.isNonZero_coe_root _)
        (coe_rootEquiv_eq_add_iff.2 h) := by
  have hex : ∃ γ, (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β := ⟨γ, h⟩
  -- The sum determines `γ`, so the chosen index is `γ`; the proof arguments then agree.
  have key : ∀ γ' (h' : (t.simplyConnectedRootDatum ht).root γ' =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β), γ' = γ →
      (t.isChevalleySystem_chevalleySystem ht).intStructureConstant (t.rootEquiv ht α)
          (t.rootEquiv ht β) (t.rootEquiv ht γ') (LieSubalgebra.isNonZero_coe_root _)
          (coe_rootEquiv_eq_add_iff.2 h') =
        (t.isChevalleySystem_chevalleySystem ht).intStructureConstant (t.rootEquiv ht α)
          (t.rootEquiv ht β) (t.rootEquiv ht γ) (LieSubalgebra.isNonZero_coe_root _)
          (coe_rootEquiv_eq_add_iff.2 h) := by
    rintro _ _ rfl
    rfl
  -- A `calc` rather than `rw`: closing a rewrite by `rfl` would compare the two choices.
  calc t.structureConstant ht α β = _ := dite_eq_left hex
    _ = _ := key _ hex.choose_spec
      ((t.simplyConnectedRootDatum ht).root.injective (hex.choose_spec.trans h.symm))

/-- **The structure-constant equation.** If root `γ` of the pinned datum is the sum of roots `α`
and `β`, then `⁅e_α, e_β⁆ = N_{α,β} e_γ`. -/
theorem lie_chevalleySystem_eq_structureConstant_zsmul {α β γ : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β) :
    ⁅t.chevalleySystem ht α, t.chevalleySystem ht β⁆ =
      t.structureConstant ht α β • t.chevalleySystem ht γ := by
  rw [structureConstant_eq_intStructureConstant h]
  simpa only [extendRootFamily_rootEquiv] using
    (t.isChevalleySystem_chevalleySystem ht).lie_eq_intStructureConstant_zsmul _ _ _
      (LieSubalgebra.isNonZero_coe_root _) (coe_rootEquiv_eq_add_iff.2 h)

/-- **The structure constant is determined by the bracket.** If root `γ` of the pinned datum is the
sum of roots `α` and `β`, an integer is `N_{α,β}` exactly when it is the coefficient of `e_γ` in
`⁅e_α, e_β⁆`. -/
theorem eq_structureConstant_iff {α β γ : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β) (z : ℤ) :
    z = t.structureConstant ht α β ↔
      ⁅t.chevalleySystem ht α, t.chevalleySystem ht β⁆ = z • t.chevalleySystem ht γ := by
  rw [structureConstant_eq_intStructureConstant h]
  simpa only [extendRootFamily_rootEquiv] using
    (t.isChevalleySystem_chevalleySystem ht).eq_intStructureConstant_iff _ _ _
      (LieSubalgebra.isNonZero_coe_root _) (coe_rootEquiv_eq_add_iff.2 h) z

/-- **Chevalley's theorem on structure constants.** If `α + β` is a root, then
`N_{α,β} = ±(r + 1)`, where `r = chainBotCoeff α β` is the largest integer with `β - r α` a root
of the pinned datum. -/
theorem structureConstant_eq_natCast_or_eq_neg_natCast {α β : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∈
      Set.range (t.simplyConnectedRootDatum ht).root) :
    t.structureConstant ht α β = ((t.simplyConnectedRootDatum ht).chainBotCoeff α β + 1 : ℕ) ∨
      t.structureConstant ht α β =
        -(((t.simplyConnectedRootDatum ht).chainBotCoeff α β + 1 : ℕ) : ℤ) := by
  rw [← chainBotCoeff_rootEquiv h]
  obtain ⟨γ, hγ⟩ := h
  rw [structureConstant_eq_intStructureConstant hγ]
  exact (t.isChevalleySystem_chevalleySystem ht).intStructureConstant_eq_natCast_or_eq_neg_natCast
    _ _ _ (LieSubalgebra.isNonZero_coe_root _) (LieSubalgebra.isNonZero_coe_root _)
    (LieSubalgebra.isNonZero_coe_root _) (coe_rootEquiv_eq_add_iff.2 hγ)

/-- The structure constant of a genuine root sum is nonzero. -/
theorem structureConstant_ne_zero {α β : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∈
      Set.range (t.simplyConnectedRootDatum ht).root) :
    t.structureConstant ht α β ≠ 0 := by
  rcases structureConstant_eq_natCast_or_eq_neg_natCast h with h | h <;> rw [h] <;> omega

/-- The structure constant vanishes when `α + β` is not a root. -/
theorem structureConstant_eq_zero {α β : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root) :
    t.structureConstant ht α β = 0 := by
  rw [structureConstant, dite_eq_right_iff]
  exact fun hex => (h hex).elim

/-- **Skew-symmetry of the structure constants**: `N_{β,α} = -N_{α,β}`. -/
theorem structureConstant_skew (α β : Fin t.numRoots) :
    t.structureConstant ht β α = -t.structureConstant ht α β := by
  by_cases h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∈
      Set.range (t.simplyConnectedRootDatum ht).root
  · obtain ⟨γ, hγ⟩ := h
    refine ((eq_structureConstant_iff (hγ.trans (add_comm _ _)) _).2 ?_).symm
    rw [← lie_skew, lie_chevalleySystem_eq_structureConstant_zsmul hγ, neg_smul]
  · rw [structureConstant_eq_zero h, structureConstant_eq_zero (by rwa [add_comm]), neg_zero]

/-- **The Chevalley relation**: `N_{-α,-β} = -N_{α,β}`, where the negative of a root number `α` is
its reflection `reflectionPerm α α` in itself. It holds because the Chevalley involution sends
`e_α` to `-e_{-α}`. -/
@[simp] theorem structureConstant_reflectionPerm_self_reflectionPerm_self (α β : Fin t.numRoots) :
    t.structureConstant ht ((t.simplyConnectedRootDatum ht).reflectionPerm α α)
        ((t.simplyConnectedRootDatum ht).reflectionPerm β β) =
      -t.structureConstant ht α β := by
  have hneg (γ : Fin t.numRoots) : (t.simplyConnectedRootDatum ht).root
      ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) =
        -(t.simplyConnectedRootDatum ht).root γ := by
    simp
  by_cases h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∈
      Set.range (t.simplyConnectedRootDatum ht).root
  · obtain ⟨γ, hγ⟩ := h
    have hγ' : (t.simplyConnectedRootDatum ht).root
        ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) =
          (t.simplyConnectedRootDatum ht).root
              ((t.simplyConnectedRootDatum ht).reflectionPerm α α) +
            (t.simplyConnectedRootDatum ht).root
              ((t.simplyConnectedRootDatum ht).reflectionPerm β β) := by
      rw [hneg, hneg, hneg, hγ, neg_add]
    refine ((eq_structureConstant_iff hγ' _).2 ?_).symm
    -- Apply the Chevalley involution to the bracket equation at `α`, `β` and `γ`.
    simpa only [LieEquiv.map_lie, map_zsmul, chevalleyInvolution_chevalleySystem, neg_lie, lie_neg,
      neg_neg, smul_neg, neg_smul] using
      congrArg (t.chevalleyInvolution ht) (lie_chevalleySystem_eq_structureConstant_zsmul hγ)
  · rw [structureConstant_eq_zero h, structureConstant_eq_zero, neg_zero]
    rintro ⟨δ, hδ⟩
    refine h ⟨(t.simplyConnectedRootDatum ht).reflectionPerm δ δ, ?_⟩
    rw [hneg, hδ, hneg, hneg, neg_add, neg_neg, neg_neg]

/-- **Brackets at non-roots vanish.** If `α + β` is neither a root of the pinned datum nor zero,
then `⁅e_α, e_β⁆ = 0`. -/
theorem lie_chevalleySystem_eq_zero {α β : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (h₀ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ≠ 0) :
    ⁅t.chevalleySystem ht α, t.chevalleySystem ht β⁆ = 0 := by
  have hbot : rootSpace (t.cartanSubalgebra ht)
      (((t.rootEquiv ht α : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) :
          t.cartanSubalgebra ht → ℚ) +
        (t.rootEquiv ht β : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht))) = ⊥ := by
    by_contra hne
    -- Otherwise the sum is a weight, nonzero because it is nonzero on some Cartan generator.
    let χ : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) := ⟨_, hne⟩
    have hχ : χ.IsNonZero := fun hχ => h₀ (coe_rootEquiv_add_eq_zero_iff.1 hχ)
    obtain ⟨γ, hγ⟩ := t.exists_coe_rootEquiv_eq ht hχ
    exact h ⟨γ, coe_rootEquiv_eq_add_iff.1 (congrArg DFunLike.coe hγ)⟩
  simpa only [extendRootFamily_rootEquiv] using
    (t.isChevalleySystem_chevalleySystem ht).toIsSl2System.lie_eq_zero_of_rootSpace_add_eq_bot
      _ _ hbot

end

end TauCeti.DynkinType
