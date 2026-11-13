/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator
import TauCeti.RingTheory.Nilpotent.RootString.Basic

/-!
# The Chevalley commutator formula for root strings of length at most three

Let `x_α(u) = ∑ₙ uⁿ ρ(e_α)⁽ⁿ⁾` be the root subgroups of the pinned Chevalley system on a
Kostant-stable lattice, over a commutative ring of values. For two linearly independent roots
`α` and `β`, Chevalley's commutator formula expresses

```text
⁅x_α(u), x_β(v)⁆ = x_α(u) x_β(v) x_α(u)⁻¹ x_β(v)⁻¹ = ∏ x_{iα+jβ}(c_{ij} uⁱ vʲ)
```

as a product over the roots `iα + jβ` with `i, j > 0`, in increasing `i + j`. This file proves
the formula, with coefficients given by the native structure constants `N_{α,β}`, in the
three cases in which at most two roots `iα + jβ` occur and both have `j = 1`:

* `α + β` is neither a root nor zero: the root subgroups commute;
* `α + β` is a root but `2α + β` and `α + 2β` are not:
  `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v)`;
* `α + β` and `2α + β` are roots but `3α + β` and `α + 2β` are not:
  `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v) x_{2α+β}(M_{α,β,2} u² v)`, where
  `M_{α,β,2} = N_{α,β} N_{α,α+β} / 2` is the integer with `(ad e_α)² e_β / 2 = M_{α,β,2} e_{2α+β}`.

The division by two is exact in `ℤ`: by Chevalley's theorem `N_{α,β} = ±(r + 1)` and
`N_{α,α+β} = ±(r + 2)` for `r` the largest integer with `β - rα` a root. So the formulas hold
over every commutative ring, in every characteristic. Together with the case `-β = α`, which is
not a commutator relation, these cover every pair of roots in the simply laced types and every
pair in the types `B`, `C` and `F₄` up to exchanging `α` and `β`. The remaining pairs of type
`G₂` are treated by the straightening relations in the `G2` subdirectory of this one.

The proofs transport the integral exponential identities
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq` and
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul`, which also give the
corresponding relations for the numbered Kostant root subgroups in
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.Basic`; here the bracket
hypotheses are derived from the root datum rather than assumed.

## Main results

* `TauCeti.DynkinType.commute_chevalleyRootSubgroup`: root subgroups of roots whose sum is
  neither a root nor zero commute.
* `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_root_eq_add`: the one-factor
  commutator formula.
* `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq`: the
  two-factor commutator formula along the root string `β`, `α + β`, `2α + β`.
* `TauCeti.DynkinType.chevalleyRootSubgroup_mul_of_add_eq_of_add_eq`: the corresponding
  two-factor product relation.
* `TauCeti.DynkinType.chevalleyRootSubgroup_mul_of_add`: the single-term product relation
  `x_α(u) x_β(v) = x_β(v) x_{α+β}(N_{α,β} u v) x_α(u)` when `e_{α+β}` commutes with `e_α` and
  `e_β`, for every Dynkin type.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieModule TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid} {α β γ δ : Fin t.numRoots}

/-- A root sum `γ = α + β` makes the roots `α` and `β` linearly independent, so a combination
`a α + b β` with natural coefficients and `a ≠ 0` does not vanish. -/
private theorem ne_zero_of_eq_nsmul_root_add_nsmul_root
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    {a b : ℕ} (ha : a ≠ 0) {w : Fin t.rank → ℤ}
    (hw : w = a • (t.simplyConnectedRootDatum ht).root α +
      b • (t.simplyConnectedRootDatum ht).root β) :
    w ≠ 0 := by
  have := t.isReduced_simplyConnectedRootDatum ht
  rintro rfl
  rw [← natCast_zsmul, ← natCast_zsmul] at hw
  have h := (LinearIndependent.pair_iff.1
    ((t.simplyConnectedRootDatum ht).linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩) _ _
      hw.symm).1
  omega

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
    ∀ v ∈ M, ρ u v ∈ M)
  (hnil : ∀ i, IsNilpotent
    (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

/-- **Root subgroups commute when the roots do not sum to a root.** If `α + β` is neither a root
nor zero, then `x_α(u)` and `x_β(v)` commute, over every commutative ring of values. -/
theorem commute_chevalleyRootSubgroup
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (h₀ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ≠ 0)
    (A : CommAlgCat ℤ) (u v : A) :
    Commute (chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u))
      (chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)) := by
  have hdp := dividedPower_chevalleySystem_smul_mem ρ M hM hnil
  apply Units.ext
  simpa only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd] using
    (commute_baseChangeExp M (commute_of_lie_eq_zero ρ (lie_chevalleySystem_eq_zero h h₀))
      (hdp α) (hdp β) u v).eq

/-- **The one-factor Chevalley commutator formula.** If `γ = α + β` is a root while `2α + β` and
`α + 2β` are not, then `⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v)` over every commutative ring of
values. In the simply laced types this covers every pair of roots whose sum is a root. -/
theorem commutatorElement_chevalleyRootSubgroup_of_root_eq_add
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hα : 2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβ : (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
        (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) := by
  have hαγ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ =
      2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β := by
    rw [hγ]; module
  have hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β := by
    rw [hγ]; module
  refine commutatorElement_chevalleyRootSubgroup_of_lie_eq ρ M hM hnil
    (lie_chevalleySystem_eq_structureConstant_zsmul hγ)
    (lie_chevalleySystem_eq_zero (hαγ ▸ hα)
      (ne_zero_of_eq_nsmul_root_add_nsmul_root hγ (a := 2) (b := 1) two_ne_zero
        (by rw [hαγ, one_nsmul])))
    (lie_chevalleySystem_eq_zero (hβγ ▸ hβ)
      (ne_zero_of_eq_nsmul_root_add_nsmul_root hγ (a := 1) (b := 2) one_ne_zero
        (by rw [hβγ, one_nsmul]))) A u v

/-- Reordering root-subgroup elements with sum roots `α + β` and `2α + β`, when the
further sums `3α + β` and `α + 2β` are not roots, uses the integral Chevalley coefficients. -/
theorem chevalleyRootSubgroup_mul_of_add_eq_of_add_eq
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hαδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil γ A
          (.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (.ofAdd (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
            (u ^ 2 * v))) *
        chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) := by
  let c := t.structureConstant ht α β
  let d := t.structureConstant ht α β * t.structureConstant ht α γ / 2
  let E := fun i => ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht i))
  have hzαδ := lie_chevalleySystem_eq_zero_of_add_eq hδ hαδ
  have hzβγ := lie_chevalleySystem_eq_zero_of_add_eq (hγ.trans (add_comm _ _)) hβγ
  -- The nonvanishing brackets, scaled so that the coefficient of `e_δ` is twice an integer.
  have hαβ := lie_chevalleySystem_eq_structureConstant_zsmul hγ
  have hcαγ : (1 * c) • ⁅t.chevalleySystem ht α, t.chevalleySystem ht γ⁆ =
      (((2 : ℕ) : ℤ) * d) • t.chevalleySystem ht δ := by
    rw [lie_chevalleySystem_eq_structureConstant_zsmul hδ, smul_smul, Nat.cast_ofNat, one_mul,
      Int.mul_ediv_cancel' (two_dvd_structureConstant_mul_structureConstant hγ)]
  have hxy : E α * E β = E β * E α + c • E γ := mul_eq_mul_add_zsmul_of_lie_eq ρ hαβ
  have hxz : E α * (c • E γ) = (c • E γ) * E α + 2 • (d • E δ) := by
    simpa only [one_zsmul] using zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ hcαγ
  -- Divided-power stability of the root vectors and of their integral multiples.
  have hdp := dividedPower_chevalleySystem_smul_mem ρ M hM hnil
  have hscaled := dividedPower_zsmul_chevalleySystem_smul_mem ρ M hM hnil
  have hn := isNilpotent_apply_ι_chevalleySystem ρ hnil
  apply Units.ext
  simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
  rw [← baseChangeExp_zsmul c M (hdp γ) (hscaled c γ) (hn γ),
    ← baseChangeExp_zsmul d M (hdp δ) (hscaled d δ) (hn δ)]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul M hxy hxz
    ((commute_of_lie_eq_zero ρ hzαδ).smul_right d) ((commute_of_lie_eq_zero ρ hzβγ).smul_right c)
    (hn α) (hn β) ((hn γ).smul c) (hdp α) (hdp β) (hscaled c γ) (hscaled d δ) u v

/-- **The two-factor Chevalley commutator formula.** If `γ = α + β` and `δ = 2α + β` are roots
while `3α + β` and `α + 2β` are not, then over every commutative ring of values

```text
⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v) x_δ(M u² v),    M = N_{α,β} N_{α,γ} / 2,
```

where `M` is the integer with `(ad e_α)² e_β / 2 = M e_δ`; the division is exact. In the types
`B`, `C` and `F₄` this covers every pair `α`, `β` with `2α + β` a root. -/
theorem commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hαδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
          (.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (.ofAdd (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
            (u ^ 2 * v))) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨hβδ, hβδ₀⟩ :=
    RootPairing.root_add_root_notMem_range_root_and_ne_zero_of_root_eq_add_of_root_eq_add
      (t.simplyConnectedRootDatum ht) hγ hδ
  have hprod := chevalleyRootSubgroup_mul_of_add_eq_of_add_eq ρ M hM hnil hγ hδ hαδ hβγ A u v
  have hcomm := (commute_chevalleyRootSubgroup_of_lie_eq_zero ρ M hM hnil
    (lie_chevalleySystem_eq_zero_of_add_eq (hγ.trans (add_comm _ _)) hβγ) A v
    ((t.structureConstant ht α β : A) * (u * v))).mul_right
      (commute_chevalleyRootSubgroup ρ M hM hnil hβδ hβδ₀ A v
        (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) * (u ^ 2 * v)))
  rw [commutatorElement_def, hprod, mul_inv_cancel_right,
    mul_assoc (chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v)), hcomm.eq, mul_inv_cancel_right]

/-- The single-term Chevalley product relation, when the sum-root vector commutes with both
input vectors. No restriction on Dynkin type or root lengths is required. -/
theorem chevalleyRootSubgroup_mul_of_add
    {i j k : Fin t.numRoots}
    (hij : (t.simplyConnectedRootDatum ht).root k =
      (t.simplyConnectedRootDatum ht).root i + (t.simplyConnectedRootDatum ht).root j)
    (hik : ⁅t.chevalleySystem ht i, t.chevalleySystem ht k⁆ = 0)
    (hjk : ⁅t.chevalleySystem ht j, t.chevalleySystem ht k⁆ = 0)
    (A : CommAlgCat ℤ) (u v : A) :
    chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil j A (Multiplicative.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil j A (Multiplicative.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil k A
          (Multiplicative.ofAdd ((t.structureConstant ht i j : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd u) :=
  chevalleyRootSubgroup_mul_of_lie_eq ρ M hM hnil
    (lie_chevalleySystem_eq_structureConstant_zsmul hij) hik hjk A u v

end

end TauCeti.DynkinType
