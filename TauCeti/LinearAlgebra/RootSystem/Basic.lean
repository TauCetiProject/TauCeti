/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Basic facts about root systems

Elementary consequences of the definition of a root system that need no further theory.

## Main results

* `RootPairing.nonempty_of_isRootSystem`: a root system on a nontrivial module has a root.
* `RootPairing.finite_weight_of_isRootSystem`: the weight module of a finite root system is finitely
  generated.
* `RootPairing.not_isOfFinAddOrder_root`: in characteristic zero, a root has infinite additive
  order.
* `RootPairing.reflection_reflection_of_pairing_eq_zero`: reflecting in `i` then `j` when
  `P.pairing i j = 0` subtracts both coroot projections independently.
* `RootPairing.commute_reflectionPerm_of_isOrthogonal` and
  `RootPairing.reflectionPerm_comm_of_isOrthogonal`: reflection permutations of orthogonal roots
  commute.
* `RootPairing.reflection_reflection_reflection_of_pairing_eq_neg_one`,
  `RootPairing.reflection_braid_of_pairing_eq_neg_one`, and
  `RootPairing.reflectionPerm_braid_of_pairing_eq_neg_one`: the symmetric `-1` braid formula and
  braid laws for reflections and root indices.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A root system on a nontrivial module has a root. -/
lemma nonempty_of_isRootSystem [Nontrivial M] (P : RootPairing ι R M N) [P.IsRootSystem] :
    Nonempty ι := by
  by_contra! h
  have hspan := IsRootSystem.span_root_eq_top (P := P)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

/-- On a finite root system, the weight module is finitely generated because it is spanned by the
finite set of roots. -/
theorem finite_weight_of_isRootSystem (P : RootPairing ι R M N) [Finite ι] [P.IsRootSystem] :
    Module.Finite R M :=
  Module.finite_def.mpr
    (IsRootSystem.span_root_eq_top (P := P) ▸ Submodule.fg_span (Set.finite_range P.root))

/-- **A root has infinite additive order** in characteristic zero: `n • α = 0` pairs with `α^∨`
to `2 n = 0`. -/
theorem not_isOfFinAddOrder_root [CharZero R] (P : RootPairing ι R M N) (i : ι) :
    ¬IsOfFinAddOrder (P.root i) := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  rintro ⟨n, hn, hnα⟩
  have h := congrArg (P.coroot' i) hnα
  simp only [map_nsmul, root_coroot'_eq_pairing, pairing_same, map_zero, nsmul_eq_mul] at h
  have h' : ((n * 2 : ℕ) : R) = 0 := by exact_mod_cast h
  rw [Nat.cast_eq_zero] at h'
  omega

/-- Reflecting in `i` and then in `j` when `P.pairing i j = 0` subtracts the `i`-th and
`j`-th coroot projections independently. -/
theorem reflection_reflection_of_pairing_eq_zero (P : RootPairing ι R M N) {i j : ι}
    (h0 : P.pairing i j = 0) (y : M) :
    P.reflection j (P.reflection i y) =
      y - P.coroot' i y • P.root i - P.coroot' j y • P.root j := by
  rw [reflection_apply, reflection_apply, map_sub, map_smul, root_coroot'_eq_pairing, h0,
    smul_eq_mul, mul_zero, sub_zero]

/-- Reflection permutations of orthogonal roots commute. -/
theorem commute_reflectionPerm_of_isOrthogonal (P : RootPairing ι R M N) {i j : ι}
    (h : P.IsOrthogonal i j) :
    Commute (P.reflectionPerm i) (P.reflectionPerm j) :=
  Equiv.ext fun r ↦ P.root.injective <| by
    simpa only [Equiv.Perm.coe_mul, Function.comp_apply, root_reflectionPerm,
      ← mul_apply_eq_comp] using
      DFunLike.congr_fun (P.isOrthogonal_comm i j h).eq (P.root r)

/-- Pointwise commutation of reflection permutations at orthogonal roots. -/
theorem reflectionPerm_comm_of_isOrthogonal (P : RootPairing ι R M N) {i j : ι}
    (h : P.IsOrthogonal i j) (r : ι) :
    P.reflectionPerm i (P.reflectionPerm j r) = P.reflectionPerm j (P.reflectionPerm i r) :=
  congrArg (fun π : Equiv.Perm ι ↦ π r) (P.commute_reflectionPerm_of_isOrthogonal h).eq

/-- When `P.pairing i j = -1`, reflecting `P.root i` across `j` gives `P.root i + P.root j`. -/
theorem root_reflectionPerm_of_pairing_eq_neg_one (P : RootPairing ι R M N) {i j : ι}
    (hij : P.pairing i j = -1) :
    P.root (P.reflectionPerm j i) = P.root i + P.root j := by
  rw [root_reflectionPerm, reflection_apply_root, hij, neg_one_smul, sub_neg_eq_add]

/-- When `P.pairing i j = -1` and `P.pairing j i = -1`, `sᵢ j` and `sⱼ i` are the same root index.
-/
theorem reflectionPerm_eq_reflectionPerm_of_pairing_eq_neg_one (P : RootPairing ι R M N) {i j : ι}
    (hij : P.pairing i j = -1) (hji : P.pairing j i = -1) :
    P.reflectionPerm i j = P.reflectionPerm j i :=
  P.root.injective <| by
    rw [P.root_reflectionPerm_of_pairing_eq_neg_one hji,
      P.root_reflectionPerm_of_pairing_eq_neg_one hij, add_comm]

/-- Symmetric `-1` braid formula: when `P.pairing i j = -1` and `P.pairing j i = -1`, the
three-fold reflection `sⱼ sᵢ sⱼ` is the reflection in the sum root `αᵢ + αⱼ`. -/
theorem reflection_reflection_reflection_of_pairing_eq_neg_one (P : RootPairing ι R M N) {i j : ι}
    (hij : P.pairing i j = -1) (hji : P.pairing j i = -1) (y : M) :
    P.reflection j (P.reflection i (P.reflection j y)) =
      y - (P.coroot' i y + P.coroot' j y) • (P.root i + P.root j) := by
  have hmul : P.reflection j (P.reflection i (P.reflection j y)) =
      P.reflection (P.reflectionPerm j i) y := by
    rw [P.reflection_reflectionPerm]; rfl
  rw [hmul, reflection_apply, coroot'_reflectionPerm, LinearMap.comp_apply, LinearEquiv.coe_coe,
    reflection_apply, map_sub, map_smul, root_coroot'_eq_pairing, hji, smul_eq_mul, mul_neg_one,
    sub_neg_eq_add, P.root_reflectionPerm_of_pairing_eq_neg_one hij]

/-- Length-3 braid law for reflections of roots with symmetric pairing `-1`. -/
theorem reflection_braid_of_pairing_eq_neg_one (P : RootPairing ι R M N) {i j : ι}
    (hij : P.pairing i j = -1) (hji : P.pairing j i = -1) :
    P.reflection i * P.reflection j * P.reflection i =
      P.reflection j * P.reflection i * P.reflection j := by
  rw [← P.reflection_reflectionPerm, ← P.reflection_reflectionPerm,
    P.reflectionPerm_eq_reflectionPerm_of_pairing_eq_neg_one hij hji]

/-- Pointwise length-3 braid law for reflections of roots with symmetric pairing `-1`. -/
theorem reflection_braid_apply_of_pairing_eq_neg_one (P : RootPairing ι R M N) {i j : ι}
    (hij : P.pairing i j = -1) (hji : P.pairing j i = -1) (y : M) :
    P.reflection i (P.reflection j (P.reflection i y)) =
      P.reflection j (P.reflection i (P.reflection j y)) :=
  DFunLike.congr_fun (P.reflection_braid_of_pairing_eq_neg_one hij hji) y

/-- Length-3 braid law on root indices for roots with symmetric pairing `-1`. -/
theorem reflectionPerm_braid_of_pairing_eq_neg_one (P : RootPairing ι R M N) {i j : ι}
    (hij : P.pairing i j = -1) (hji : P.pairing j i = -1) (r : ι) :
    P.reflectionPerm i (P.reflectionPerm j (P.reflectionPerm i r)) =
      P.reflectionPerm j (P.reflectionPerm i (P.reflectionPerm j r)) :=
  P.root.injective <| by
    simpa only [root_reflectionPerm] using
      P.reflection_braid_apply_of_pairing_eq_neg_one hij hji (P.root r)

end RootPairing
