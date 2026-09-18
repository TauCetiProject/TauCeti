/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.MeasureTheory.Group.FundamentalDomain

/-!
# Fundamental domains for the two groups acting on `ℍ`

A congruence subgroup `Γ ≤ SL(2, ℤ)` reaches `ℍ` two ways: through its image in `PSL(2, ℤ)`, the
group that acts faithfully and the one every fundamental-domain statement about `ℍ` is phrased
for, and through `Γ.map (mapGL ℝ)` inside `GL(2, ℝ)`, the group a modular form is slashed by and
the only one large enough to contain a Hecke double-coset representative. This file records when a
fundamental domain for the first is one for the second.

There is no coercion `PSL(2, ℤ) → GL(2, ℝ)` to read that along: opposite lifts `γ` and `-γ` of one
class have distinct images under `mapGL ℝ`. What is true is that **each class acts as any of its
lifts does** — `UpperHalfPlane.pslMk_smul` and `Matrix.SpecialLinearGroup.pslMk_smul_set`.

## Main results

* `TauCeti.isFundamentalDomain_map_mapGL`: for `Γ ⊓ center = ⊥`, a fundamental domain for
  the image of `Γ` in `PSL(2, ℤ)` is one for its image in `GL(2, ℝ)`.

The hypothesis is not a convenience. Without it the statement is false: if `-I ∈ Γ` then `-I` is a
*non-identity* element of `Γ.map (mapGL ℝ)` acting *trivially* on `ℍ`, so `(-I) • S = S` and
`MeasureTheory.IsFundamentalDomain` fails its a.e.-disjointness requirement for every `S` of
positive measure. Passing to `PSL(2, ℤ)` is exactly what removes that element. `Γ ⊓ center = ⊥`
holds for `Γ₁(N)` and `Γ(N)` at every level except `N = 1` and `N = 2`, the two where `-1 ≡ 1`
(so level `0`, where the congruence is an equation in `ℤ`, is on the good side alongside `N ≥ 3`);
`SL(2, ℤ)` is the case `N = 1`, and `Γ₀(N)` fails at every level.
-/

public section

open MeasureTheory Matrix ModularGroup UpperHalfPlane

open scoped MatrixGroups Pointwise

namespace TauCeti

/-- **A fundamental domain for the image of `Γ` in `PSL(2, ℤ)` is one for its image in
`GL(2, ℝ)`**, provided `Γ` meets the centre of `SL(2, ℤ)` trivially.

Without that hypothesis the statement is false: `-I ∈ Γ` would put a non-identity element of
`Γ.map (mapGL ℝ)` acting trivially on `ℍ`, so `(-I) • S = S` and a.e.-disjointness fails for every
`S` of positive measure. The module docstring says where each side of the statement is used. -/
theorem isFundamentalDomain_map_mapGL {Γ : Subgroup SL(2, ℤ)} {μ : Measure ℍ}
    (hΓ : Γ ⊓ Subgroup.center SL(2, ℤ) = ⊥) {S : Set ℍ}
    (hS : IsFundamentalDomain (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) S μ) :
    IsFundamentalDomain (Γ.map (SpecialLinearGroup.mapGL ℝ)) S μ := by
  refine ⟨hS.nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [hS.ae_covers] with x hx
    obtain ⟨q, hq⟩ := hx
    obtain ⟨γ, hγΓ, hγq⟩ := q.2
    refine ⟨⟨SpecialLinearGroup.mapGL ℝ γ, ⟨γ, hγΓ, rfl⟩⟩, ?_⟩
    rw [MulAction.subgroup_smul_def] at hq ⊢
    rwa [← hγq, QuotientGroup.mk'_apply, pslMk_smul, sl_moeb] at hq
  · intro g₁ g₂ hne
    obtain ⟨γ₁, h₁Γ, h₁⟩ := g₁.2
    obtain ⟨γ₂, h₂Γ, h₂⟩ := g₂.2
    have hγne : γ₁ ≠ γ₂ := fun h ↦ hne (Subtype.ext (by rw [← h₁, ← h₂, h]))
    have hqne : (⟨QuotientGroup.mk γ₁, ⟨γ₁, h₁Γ, rfl⟩⟩ :
          Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) ≠
        ⟨QuotientGroup.mk γ₂, ⟨γ₂, h₂Γ, rfl⟩⟩ := by
      intro h
      have hmem : γ₁⁻¹ * γ₂ ∈ Γ ⊓ Subgroup.center SL(2, ℤ) :=
        ⟨Γ.mul_mem (Γ.inv_mem h₁Γ) h₂Γ, QuotientGroup.eq.mp (congrArg Subtype.val h)⟩
      rw [hΓ, Subgroup.mem_bot] at hmem
      exact hγne (inv_mul_eq_one.mp hmem)
    have hdisj := hS.aedisjoint hqne
    simp only [Function.onFun, MulAction.subgroup_smul_def,
      Matrix.SpecialLinearGroup.pslMk_smul_set, ModularGroup.sl_smul_set] at hdisj
    simp only [Function.onFun, MulAction.subgroup_smul_def, ← h₁, ← h₂]
    -- `sl_smul_set` leaves the `GL`-translate spelled with the coercion, the goal spells it
    -- `mapGL ℝ γ`; `mapGL` is defined as that coercion, so the two terms are the same.
    exact hdisj

end TauCeti
