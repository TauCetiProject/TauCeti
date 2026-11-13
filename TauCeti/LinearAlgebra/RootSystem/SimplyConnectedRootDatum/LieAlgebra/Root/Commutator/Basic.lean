/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.DoublyLaced

/-!
# The Chevalley commutator formula for root strings of length at most three

Let `x_α(u) = ∑ₙ uⁿ ρ(e_α)⁽ⁿ⁾` be the root subgroups of the pinned Chevalley system on a
Kostant-stable lattice, over a commutative ring of values. For two linearly independent roots
`α` and `β`, Chevalley's commutator formula expresses

```text
⁅x_α(u), x_β(v)⁆ = x_α(u) x_β(v) x_α(u)⁻¹ x_β(v)⁻¹ = ∏ x_{iα+jβ}(c_{ij} uⁱ vʲ)
```

as a product over the roots `iα + jβ` with `i, j > 0`, in increasing `i + j`. This file proves
the formula, with coefficients given by the native structure constants `N_{α,β}`, in the four
cases in which at most two roots `iα + jβ` occur:

* `α + β` is neither a root nor zero: the root subgroups commute;
* `α + β` is a root but `2α + β` and `α + 2β` are not:
  `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v)`;
* `α + β` and `2α + β` are roots but `3α + β` and `α + 2β` are not:
  `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v) x_{2α+β}(M_{α,β,2} u² v)`, where
  `M_{α,β,2} = N_{α,β} N_{α,α+β} / 2` is the integer with `(ad e_α)² e_β / 2 = M_{α,β,2} e_{2α+β}`;
* `α + β` and `α + 2β` are roots but `2α + β` and `α + 3β` are not:
  `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v) x_{α+2β}(-M_{β,α,2} u v²)`, where
  `M_{β,α,2} = N_{β,α} N_{β,α+β} / 2`.

The division by two is exact in `ℤ`: by Chevalley's theorem `N_{α,β} = ±(r + 1)` and
`N_{α,α+β} = ±(r + 2)` for `r` the largest integer with `β - rα` a root. So the formulas hold
over every commutative ring, in every characteristic. Together with the case `-β = α`, which is
not a commutator relation, these cover every pair of roots in the simply laced types and in the
doubly laced types `B`, `C` and `F₄`. The remaining pairs of type `G₂` are treated by the
straightening relations in the `G2` subdirectory of this one.

## Main results

* `TauCeti.DynkinType.commute_chevalleyRootSubgroup`: root subgroups of roots whose sum is
  neither a root nor zero commute.
* `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_root_eq_add`: the one-factor
  commutator formula.
* `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_root_eq_two_nsmul_add`: the
  two-factor commutator formula along `{α + β, 2α + β}`.
* `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_root_eq_add_two_nsmul`: the
  two-factor commutator formula along `{α + β, α + 2β}`.
* `TauCeti.DynkinType.chevalleyRootSubgroup_mul_of_add`: the single-term product relation
  `x_α(u) x_β(v) = x_β(v) x_{α+β}(N_{α,β} u v) x_α(u)` when `e_{α+β}` commutes with `e_α` and
  `e_β`, for every Dynkin type.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter VI, §1, no. 3.
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

/-- **The two-factor Chevalley commutator formula, short root first.** If `γ = α + β` and
`δ = 2α + β` are roots while `3α + β` and `α + 2β` are not, then over every commutative ring of
values

```text
⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v) x_δ(M u² v),    M = N_{α,β} N_{α,γ} / 2,
```

where `M` is the integer with `(ad e_α)² e_β / 2 = M e_δ`; the division is exact. In the types
`B`, `C` and `F₄` this covers every pair `α`, `β` with `2α + β` a root. -/
theorem commutatorElement_chevalleyRootSubgroup_of_root_eq_two_nsmul_add
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hα : 3 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβ : (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
          (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (Multiplicative.ofAdd
            (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
              (u ^ 2 * v))) := by
  have hδ' : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ := by
    rw [hδ, hγ]; module
  have hαδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ =
      3 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β := by
    rw [hδ]; module
  have hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β := by
    rw [hγ]; module
  exact commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq ρ M hM hnil
    hγ hδ' (hαδ ▸ hα) (hβγ ▸ hβ) A u v

/-- **The two-factor Chevalley commutator formula, long root first.** If `γ = α + β` and
`δ = α + 2β` are roots while `2α + β` and `α + 3β` are not, then over every commutative ring of
values

```text
⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v) x_δ(-M u v²),    M = N_{β,α} N_{β,γ} / 2,
```

where `M` is the integer with `(ad e_β)² e_α / 2 = M e_δ`; the division is exact. This is
`commutatorElement_chevalleyRootSubgroup_of_root_eq_two_nsmul_add` with the roles of `α` and `β`
exchanged: the coefficient of `x_δ` is `c_{12} = -M_{β,α,2}`. -/
theorem commutatorElement_chevalleyRootSubgroup_of_root_eq_add_two_nsmul
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β)
    (hα : 2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβ : (t.simplyConnectedRootDatum ht).root α + 3 • (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
          (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (Multiplicative.ofAdd
            (((-(t.structureConstant ht β α * t.structureConstant ht β γ / 2) : ℤ) : A) *
              (u * v ^ 2))) := by
  have hδ' : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ := by
    rw [hδ, hγ]; module
  have hβδ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + 3 • (t.simplyConnectedRootDatum ht).root β := by
    rw [hδ]; module
  have hαγ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ =
      2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β := by
    rw [hγ]; module
  exact commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_rev_eq ρ M hM hnil
    hγ hδ' (hβδ ▸ hβ) (hαγ ▸ hα) A u v

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
