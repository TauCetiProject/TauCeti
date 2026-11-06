/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator
import TauCeti.RingTheory.Nilpotent.RootString.Basic

/-!
# The Chevalley commutator formula for the pinned root subgroups

For a valid Dynkin type `t`, let `x_γ(u) = ∑ₙ uⁿ ρ(e_γ)⁽ⁿ⁾` be the root subgroups
`TauCeti.DynkinType.chevalleyRootSubgroup` of the named root vectors `e_γ` of the pinned Chevalley
system, on the points of a Kostant-stable lattice over a commutative ring. This file proves the
Chevalley commutator formula, in Steinberg's normalization
`⁅x, y⁆ = x y x⁻¹ y⁻¹` (Mathlib's `commutatorElement`), for every pair of roots `α`, `β` of the
pinned datum in the following cases:

* `α + β` is neither a root nor zero: `x_α(u)` and `x_β(v)` commute;
* `γ = α + β` is a root while `2α + β` and `α + 2β` are not:
  `⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v)`;
* `γ = α + β` and `δ = 2α + β` are roots while `3α + β` and `α + 2β` are not:
  `⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v) x_δ(M_{α,β,2} u² v)`.

Here `N_{α,β}` is the structure constant `TauCeti.DynkinType.structureConstant` and
`M_{α,β,2} = N_{α,β} N_{α,α+β} / 2` is the integer with `(ad e_α)² e_β / 2 = M_{α,β,2} e_δ`. The
division is exact (`TauCeti.DynkinType.two_dvd_structureConstant_mul_structureConstant`): by
Chevalley's theorem the two factors are `±(r + 1)` and `±(r + 2)` for the root-string coefficient
`r` of `α` through `β`.

Every pair of linearly independent roots of a type other than `G₂` falls under one of these
cases, possibly after exchanging `α` and `β` (which inverts the commutator); in a simply-laced
type only the first two occur. The relations hold over every commutative ring of points, with no
factorial inverted. They specialize the commutator identities for integral nilpotent exponentials
`TauCeti.baseChangeExp_conj_of_commutator_eq` and
`TauCeti.baseChangeExp_conj_of_commutator_eq_two_nsmul` to the root vectors of the pinned
Chevalley system, whose brackets are given by the structure constants.

## Main results

* `TauCeti.DynkinType.commute_chevalleyRootSubgroup`: the commuting case.
* `TauCeti.DynkinType.two_dvd_structureConstant_mul_structureConstant`: `N_{α,β} N_{α,α+β}` is
  even.
* `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_add_eq`: the case of a single
  further root `α + β`.
* `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq`: the case of the
  further roots `α + β` and `2α + β`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling LieModule TensorProduct TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid}

/-! ## Root-sum arithmetic in the pinned datum -/

/-- Two roots of the pinned datum whose sum is a root are linearly independent. -/
private theorem linearIndependent_root_of_root_eq_add {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β) :
    LinearIndependent ℤ
      ![(t.simplyConnectedRootDatum ht).root α, (t.simplyConnectedRootDatum ht).root β] :=
  have := isReduced_simplyConnectedRootDatum t ht
  (t.simplyConnectedRootDatum ht).linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩

/-- If `α + β` is a root, then no combination `m α + n β` with `m ≠ 0` vanishes. -/
private theorem ne_zero_of_eq_zsmul_root_add_zsmul_root {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    {x : Fin t.rank → ℤ} {m n : ℤ} (hm : m ≠ 0)
    (hx : x = m • (t.simplyConnectedRootDatum ht).root α +
      n • (t.simplyConnectedRootDatum ht).root β) :
    x ≠ 0 := by
  rintro rfl
  exact hm (LinearIndependent.pair_iff.1 (linearIndependent_root_of_root_eq_add hγ) m n hx.symm).1

/-- If `γ = α + β` is a root, then `β + γ = α + 2β` is nonzero. -/
private theorem root_add_root_ne_zero_right {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β) :
    (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ≠ 0 :=
  ne_zero_of_eq_zsmul_root_add_zsmul_root hγ (m := 1) (n := 2) one_ne_zero (by rw [hγ]; module)

/-! ## Parity of the second structure constant -/

/-- **`M_{α,β,2}` is an integer.** If `γ = α + β` is a root of the pinned datum, then
`N_{α,β} N_{α,γ}` is even, so that `(ad e_α)² e_β / 2 = (N_{α,β} N_{α,γ} / 2) e_{2α+β}` has an
integral coefficient. By Chevalley's theorem the two factors are `±(r + 1)` and `±(r + 2)`, where
`r` is the root-string coefficient of `α` through `β`. -/
theorem two_dvd_structureConstant_mul_structureConstant {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β) :
    2 ∣ t.structureConstant ht α β * t.structureConstant ht α γ := by
  by_cases hδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ ∈
      Set.range (t.simplyConnectedRootDatum ht).root
  · -- The root-string coefficient of `α` through `γ = β + α` is one more than through `β`.
    have hchain := (t.simplyConnectedRootDatum ht).chainBotCoeff_of_add
      (linearIndependent_root_of_root_eq_add hγ) (hγ.trans (add_comm _ _))
    set r := (t.simplyConnectedRootDatum ht).chainBotCoeff α β
    have heven : (2 : ℤ) ∣ ((r + 1 : ℕ) : ℤ) * ((r + 1 + 1 : ℕ) : ℤ) := by
      exact_mod_cast (Nat.even_mul_succ_self (r + 1)).two_dvd
    rcases structureConstant_eq_natCast_or_eq_neg_natCast (α := α) (β := β) ⟨γ, hγ⟩
      with h₁ | h₁ <;>
    rcases structureConstant_eq_natCast_or_eq_neg_natCast hδ with h₂ | h₂ <;>
    · rw [h₁, h₂, hchain]
      simpa only [neg_mul, mul_neg, neg_neg, dvd_neg] using heven
  · rw [structureConstant_eq_zero hδ, mul_zero]
    exact dvd_zero 2

/-! ## The commutator formula -/

section Lattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

include hM hnil in
/-- The lattice is stable under the divided powers of every integral multiple of a root vector. -/
private theorem dividedPower_zsmul_chevalleySystem_smul_mem (c : ℤ) (γ : Fin t.numRoots) (n : ℕ) :
    ∀ v ∈ M, Associative.dividedPower n
      (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ))) • v ∈ M := by
  intro v hv
  rw [Associative.dividedPower_zsmul, smul_assoc]
  exact M.zsmul_mem (dividedPower_chevalleySystem_smul_mem ρ M hM hnil γ n v hv) _

/-- The inverse of `x_γ(u)` is `x_γ(-u)`. -/
private theorem chevalleyRootSubgroup_ofAdd_inv (γ : Fin t.numRoots) (A : CommAlgCat ℤ) (u : A) :
    (chevalleyRootSubgroup ρ M hM hnil γ A (Multiplicative.ofAdd u))⁻¹ =
      chevalleyRootSubgroup ρ M hM hnil γ A (Multiplicative.ofAdd (-u)) := by
  rw [← map_inv, ofAdd_neg]

/-- **Root subgroups of non-adjacent roots commute.** If `α + β` is neither a root of the pinned
datum nor zero, then `x_α(u)` and `x_β(v)` commute. -/
theorem commute_chevalleyRootSubgroup {α β : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (h₀ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ≠ 0)
    (A : CommAlgCat ℤ) (u v : Multiplicative A) :
    Commute (chevalleyRootSubgroup ρ M hM hnil α A u)
      (chevalleyRootSubgroup ρ M hM hnil β A v) := by
  refine Units.ext ?_
  simp only [Units.val_mul, chevalleyRootSubgroup_val]
  exact commute_baseChangeExp M (commute_of_lie_eq_zero ρ (lie_chevalleySystem_eq_zero h h₀))
    _ _ _ _

/-- The conjugation form of the class-two commutator relation:
`x_α(u) x_β(v) x_α(u)⁻¹ = x_β(v) x_γ(N_{α,β} u v)`. -/
private theorem chevalleyRootSubgroup_conj_of_add_eq {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hαγ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) *
        (chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u))⁻¹ =
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil γ A
          (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) := by
  -- `α + γ = 2α + β` and `β + γ = α + 2β` are nonzero, so those brackets vanish.
  have hcxz := commute_of_lie_eq_zero ρ <| lie_chevalleySystem_eq_zero hαγ <|
    ne_zero_of_eq_zsmul_root_add_zsmul_root hγ (m := 2) (n := 1) two_ne_zero (by rw [hγ]; module)
  have hcyz := commute_of_lie_eq_zero ρ
    (lie_chevalleySystem_eq_zero hβγ (root_add_root_ne_zero_right hγ))
  rw [chevalleyRootSubgroup_ofAdd_inv]
  refine Units.ext ?_
  simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
  rw [← baseChangeExp_zsmul _ M (dividedPower_chevalleySystem_smul_mem ρ M hM hnil γ)
    (dividedPower_zsmul_chevalleySystem_smul_mem ρ M hM hnil _ γ)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil γ)]
  exact baseChangeExp_conj_of_commutator_eq M
    (mul_eq_mul_add_zsmul_of_lie_eq ρ (lie_chevalleySystem_eq_structureConstant_zsmul hγ))
    (hcxz.smul_right _) (hcyz.smul_right _) (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil β) _ _ _ u v

/-- **The Chevalley commutator formula with one further root.** If `γ = α + β` is a root of the
pinned datum while `2α + β = α + γ` and `α + 2β = β + γ` are not, then over every commutative ring

```text
⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v),
```

where `N_{α,β}` is the structure constant `TauCeti.DynkinType.structureConstant`. -/
theorem commutatorElement_chevalleyRootSubgroup_of_add_eq {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hαγ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
        (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) := by
  rw [commutatorElement_def, chevalleyRootSubgroup_conj_of_add_eq ρ M hM hnil hγ hαγ hβγ,
    (commute_chevalleyRootSubgroup ρ M hM hnil hβγ (root_add_root_ne_zero_right hγ) A _ _).eq,
    mul_inv_cancel_right]

/-- The conjugation form of the commutator relation along the chain `β`, `α + β`, `2α + β`:
`x_α(u) x_β(v) x_α(u)⁻¹ = x_β(v) x_γ(N_{α,β} u v) x_δ(M_{α,β,2} u² v)`. -/
private theorem chevalleyRootSubgroup_conj_of_add_eq_of_add_eq {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hαδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) *
        (chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u))⁻¹ =
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil γ A
          (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (Multiplicative.ofAdd (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 :
            ℤ) : A) * (u ^ 2 * v))) := by
  set c := t.structureConstant ht α β
  set d := t.structureConstant ht α β * t.structureConstant ht α γ / 2
  have hd : 2 * d = c * t.structureConstant ht α γ :=
    Int.mul_ediv_cancel' (two_dvd_structureConstant_mul_structureConstant hγ)
  -- `⁅e_α, c e_γ⁆ = c N_{α,γ} e_δ = 2 d e_δ`.
  have hxz : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht α)) *
        (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ))) =
      c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ)) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht α)) +
        2 • (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht δ))) := by
    simpa only [one_zsmul] using zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := 1) (q := c)
      (r := d) (n := 2) (by
        rw [lie_chevalleySystem_eq_structureConstant_zsmul hδ, smul_smul, Nat.cast_ofNat, hd,
          one_mul])
  -- `α + δ = 3α + β` and `β + γ = α + 2β` are nonzero, so those brackets vanish.
  have hcxw := commute_of_lie_eq_zero ρ <| lie_chevalleySystem_eq_zero hαδ <|
    ne_zero_of_eq_zsmul_root_add_zsmul_root hγ (m := 3) (n := 1) three_ne_zero
      (by rw [hδ, hγ]; module)
  have hcyz := commute_of_lie_eq_zero ρ <|
    lie_chevalleySystem_eq_zero hβγ (root_add_root_ne_zero_right hγ)
  rw [chevalleyRootSubgroup_ofAdd_inv]
  refine Units.ext ?_
  simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
  rw [← baseChangeExp_zsmul _ M (dividedPower_chevalleySystem_smul_mem ρ M hM hnil γ)
      (dividedPower_zsmul_chevalleySystem_smul_mem ρ M hM hnil c γ)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ),
    ← baseChangeExp_zsmul _ M (dividedPower_chevalleySystem_smul_mem ρ M hM hnil δ)
      (dividedPower_zsmul_chevalleySystem_smul_mem ρ M hM hnil d δ)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil δ)]
  exact baseChangeExp_conj_of_commutator_eq_two_nsmul M
    (mul_eq_mul_add_zsmul_of_lie_eq ρ (lie_chevalleySystem_eq_structureConstant_zsmul hγ)) hxz
    (hcxw.smul_right d) (hcyz.smul_right c) (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil β)
    ((isNilpotent_apply_ι_chevalleySystem ρ hnil γ).smul c) _ _ _ _ u v

/-- **The Chevalley commutator formula with the further roots `α + β` and `2α + β`.** If
`γ = α + β` and `δ = 2α + β = α + γ` are roots of the pinned datum while `3α + β = α + δ` and
`α + 2β = β + γ` are not, then over every commutative ring

```text
⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v) x_δ(M_{α,β,2} u² v),
```

where `M_{α,β,2} = N_{α,β} N_{α,γ} / 2` is the integer with `(ad e_α)² e_β / 2 = M_{α,β,2} e_δ`.
The division is exact by `TauCeti.DynkinType.two_dvd_structureConstant_mul_structureConstant`. -/
theorem commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hαδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
          (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (Multiplicative.ofAdd (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 :
            ℤ) : A) * (u ^ 2 * v))) := by
  -- `β + δ = 2γ` is neither a root nor zero, so `x_β` commutes with `x_δ` as well as with `x_γ`.
  have hβδ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root δ =
      2 • (t.simplyConnectedRootDatum ht).root γ := by
    rw [hδ, hγ]
    module
  have hβδ' : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root δ ∉
      Set.range (t.simplyConnectedRootDatum ht).root := by
    have := isReduced_simplyConnectedRootDatum t ht
    rw [hβδ]
    exact (t.simplyConnectedRootDatum ht).nsmul_notMem_range_root
  have hβδ₀ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root δ ≠ 0 :=
    ne_zero_of_eq_zsmul_root_add_zsmul_root hγ (m := 2) (n := 2) two_ne_zero
      (by rw [hβδ, hγ]; module)
  have hcomm (p q : Multiplicative A) :
      Commute (chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v))
        (chevalleyRootSubgroup ρ M hM hnil γ A p * chevalleyRootSubgroup ρ M hM hnil δ A q) :=
    (commute_chevalleyRootSubgroup ρ M hM hnil hβγ (root_add_root_ne_zero_right hγ) A _ p).mul_right
      (commute_chevalleyRootSubgroup ρ M hM hnil hβδ' hβδ₀ A _ q)
  rw [commutatorElement_def,
    chevalleyRootSubgroup_conj_of_add_eq_of_add_eq ρ M hM hnil hγ hδ hαδ hβγ, mul_assoc _ _
      (chevalleyRootSubgroup ρ M hM hnil δ A _), (hcomm _ _).eq, mul_inv_cancel_right]

end Lattice

end

end TauCeti.DynkinType
