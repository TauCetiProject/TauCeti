/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
import TauCeti.RingTheory.Nilpotent.BaseChangeAction

/-!
# The Chevalley commutator formula when at most one root `iα + jβ` occurs

Let `x_α(u) = ∑ₙ uⁿ ρ(e_α)⁽ⁿ⁾` be the root subgroups of the pinned Chevalley system on a
Kostant-stable lattice, over a commutative ring of values. For two linearly independent roots
`α` and `β`, Chevalley's commutator formula expresses

```text
⁅x_α(u), x_β(v)⁆ = x_α(u) x_β(v) x_α(u)⁻¹ x_β(v)⁻¹ = ∏ x_{iα+jβ}(c_{ij} uⁱ vʲ)
```

as a product over the roots `iα + jβ` with `i, j > 0`, in increasing `i + j`. This file proves
the formula, with coefficients given by the native structure constants `N_{α,β}`, in the two
cases in which at most one root `iα + jβ` occurs:

* `α + β` is neither a root nor zero: the root subgroups commute;
* `α + β` is a root but `2α + β` and `α + 2β` are not:
  `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v)`.

The formulas hold over every commutative ring, in every characteristic. The two-factor case, in
which `α + β` and `2α + β` are roots but `3α + β` and `α + 2β` are not, is
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq` in the sibling
file `DoublyLaced`. Together with the case `-β = α`, which is not a commutator relation, these
cover every pair of roots in the simply laced types and every pair in the types `B`, `C` and
`F₄` up to exchanging `α` and `β`. In type `G₂` they do not cover every pair: the `G2`
subdirectory of this one gives straightening relations for the short–long pairs whose
`α`-string through `β` has four roots, and the short–short pairs whose sum is a root, for which
`2α + β` and `α + 2β` are both roots, are not treated here.

The one-factor formula specializes
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_lie_eq`; here the bracket
hypotheses are derived from the root datum rather than assumed.

## Main results

* `TauCeti.DynkinType.commute_chevalleyRootSubgroup`: root subgroups of roots whose sum is
  neither a root nor zero commute.
* `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_root_eq_add`: the one-factor
  commutator formula.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieModule TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid} {α β γ : Fin t.numRoots}

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
  have := t.isReduced_simplyConnectedRootDatum ht
  have hne :=
    (t.simplyConnectedRootDatum ht).nsmul_root_add_nsmul_root_ne_zero_of_add_mem_range_root ⟨γ, hγ⟩
  refine commutatorElement_chevalleyRootSubgroup_of_lie_eq ρ M hM hnil
    (lie_chevalleySystem_eq_structureConstant_zsmul hγ)
    (lie_chevalleySystem_eq_zero (hαγ ▸ hα)
      (by simpa only [hαγ, one_nsmul] using hne 2 1 two_ne_zero))
    (lie_chevalleySystem_eq_zero (hβγ ▸ hβ)
      (by simpa only [hβγ, one_nsmul] using hne 1 2 one_ne_zero)) A u v

end

end TauCeti.DynkinType
