/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Braid
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ParabolicQuotient

/-!
# Demazure operators on parabolic cosets

Let `P` be a root datum with weight lattice `M` and base `b`, let `W` be its Weyl group, and for a
reduced word `ω = k₁ ⋯ kᵣ` in the simple reflections write `D_ω = D_{k₁} ⋯ D_{kᵣ}` for the product
of the integral Demazure operators along `ω` (`RootPairing.demazureOperator`). By word
independence, `D_ω` depends only on the Weyl group element `w = s_{k₁} ⋯ s_{kᵣ}`.

This file treats the Levi and wall cases of the Demazure operators.

* **Levi case.** If `f ∈ ℤ[M]` is invariant under a standard parabolic subgroup `W_J`, then
  `D_v f = f` for every `v ∈ W_J`, and `D_w f` depends only on the coset `w W_J`.
* **Wall case.** For a dominant weight `λ`, whose stabilizer is the parabolic subgroup generated
  by the simple reflections in the walls through `λ`, the Demazure character `D_w(e^λ)` depends
  only on the orbit weight `w λ`, that is, on the coset `w W_λ ∈ W / W_λ`. So for `λ` on a wall
  the Demazure characters are indexed by `W / W_λ`, the index set of the Schubert varieties of
  `G / P_λ` and of the initial directions of the Lakshmibai–Seshadri paths of shape `λ`.
* **Demazure recursion.** Writing `χ_ξ = D_w(e^λ)` for any reduced word of any `w` with
  `w λ = ξ`, a simple Demazure operator acts on these characters by
  `Dᵢ χ_ξ = χ_{sᵢ ξ}` when `⟨ξ, αᵢ^∨⟩ ≥ 0` and `Dᵢ χ_ξ = χ_ξ` when `⟨ξ, αᵢ^∨⟩ ≤ 0`.
  This is the recursion through which Demazure characters are compared with characters of path
  crystals.

Behind all of these is the operator identity `Dᵢ D_ω = D_ω` when `sᵢ` is a left descent of `w`
(`RootPairing.demazureOperator_mul_prod_map_demazureOperator_of_isLeftDescent`), which combines
`Dᵢ² = Dᵢ` with word independence.

## Main results

* `RootPairing.prod_map_demazureOperator_apply_eq_self_of_mem_parabolic`: the Levi case,
  `D_v f = f` for `v ∈ W_J` and `W_J`-invariant `f`.
* `RootPairing.prod_map_demazureOperator_apply_eq_of_inv_mul_mem_parabolic`: `D_w f` depends only
  on the coset `w W_J` for `W_J`-invariant `f`.
* `RootPairing.prod_map_demazureOperator_single_eq_of_smul_eq`: the wall case, `D_w(e^λ)` depends
  only on `w λ` for dominant `λ`.
* `RootPairing.demazureOperator_prod_map_demazureOperator_single_of_coroot'_nonneg` and
  `RootPairing.demazureOperator_prod_map_demazureOperator_single_of_coroot'_nonpos`: the Demazure
  recursion on orbit weights.

## References

* M. Demazure, *Désingularisation des variétés de Schubert généralisées*, Ann. Sci. École
  Norm. Sup. (4) 7 (1974), §2.
* S. Kumar, *Kac–Moody Groups, their Flag Varieties and Representation Theory*, Progress in
  Mathematics 204, Birkhäuser (2002), §8.1 and §8.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, §14.
-/

public section

noncomputable section

namespace RootPairing

open AddMonoidAlgebra CoxeterSystem TauCeti

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N) [Finite ι]
  [P.IsReduced] (b : P.Base)

/-! ### The Levi case: invariants of a standard parabolic subgroup -/

/-- **The Levi case.** Let `f ∈ ℤ[M]` be invariant under the standard parabolic subgroup `W_J`,
in the sense that its coefficients are constant on `W_J`-orbits. Then `D_v f = f` for every
reduced word of every `v ∈ W_J`. -/
theorem prod_map_demazureOperator_apply_eq_self_of_mem_parabolic {J : Set b.support}
    {f : AddMonoidAlgebra ℤ M}
    (hf : ∀ v ∈ (weylCoxeterSystem P b).parabolic J, ∀ x, f.coeff (v • x) = f.coeff x)
    {ν : List b.support} (hν : (weylCoxeterSystem P b).IsReduced ν)
    (hνJ : (weylCoxeterSystem P b).wordProd ν ∈ (weylCoxeterSystem P b).parabolic J) :
    (ν.map fun m : b.support ↦ P.demazureOperator m).prod f = f := by
  -- Every letter of `ν` spells a simple reflection of `W_J`, so its Demazure operator fixes `f`.
  have hletter : ∀ i ∈ ν, P.demazureOperator i f = f := fun i hi ↦ by
    have hs := (weylCoxeterSystem P b).simple_mem_parabolic_of_isReduced ν hν hνJ i hi
    rw [weylCoxeterSystem_simple] at hs
    refine (P.demazureOperator_eq_self_iff i).mpr (AddMonoidAlgebra.ext (Finsupp.ext fun x ↦ ?_))
    simpa [← LinearEquiv.coe_inv] using hf _ hs x
  clear hν hνJ
  induction ν with
  | nil => simp
  | cons a ν ih =>
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp,
      ih fun i hi ↦ hletter i (List.mem_cons_of_mem a hi), hletter a List.mem_cons_self]

/-- The Demazure operator along a reduced word of `w` agrees, on a `W_J`-invariant element, with
the Demazure operator along a reduced word of the minimal representative of the coset `w W_J`. -/
private theorem prod_map_demazureOperator_apply_eq_of_isMinimalCosetRep {J : Set b.support}
    {f : AddMonoidAlgebra ℤ M}
    (hf : ∀ v ∈ (weylCoxeterSystem P b).parabolic J, ∀ x, f.coeff (v • x) = f.coeff x)
    {ω μ : List b.support} (hω : (weylCoxeterSystem P b).IsReduced ω)
    (hμ : (weylCoxeterSystem P b).IsReduced μ)
    (hμJ : (weylCoxeterSystem P b).IsMinimalCosetRep J ((weylCoxeterSystem P b).wordProd μ))
    (h : ((weylCoxeterSystem P b).wordProd μ)⁻¹ * (weylCoxeterSystem P b).wordProd ω ∈
      (weylCoxeterSystem P b).parabolic J) :
    (ω.map fun m : b.support ↦ P.demazureOperator m).prod f =
      (μ.map fun m : b.support ↦ P.demazureOperator m).prod f := by
  set cs := weylCoxeterSystem P b
  -- Write `w = u v` with `u = π μ` minimal and `v ∈ W_J`; then `μ ++ ν` is a reduced word for `w`.
  obtain ⟨ν, hν, hνv⟩ := cs.exists_isReduced ((cs.wordProd μ)⁻¹ * cs.wordProd ω)
  have hprod : cs.wordProd (μ ++ ν) = cs.wordProd ω := by
    rw [cs.wordProd_append, ← hνv, mul_inv_cancel_left]
  have hred : cs.IsReduced (μ ++ ν) := by
    have hlen := cs.length_mul_of_isMinimalCosetRep hμJ h
    rw [mul_inv_cancel_left] at hlen
    rw [CoxeterSystem.IsReduced, hprod, hlen, hνv, hμ.eq, hν.eq, List.length_append]
  rw [← P.prod_map_demazureOperator_eq_of_wordProd_eq b hred hω hprod, List.map_append,
    List.prod_append, mul_apply_eq_comp,
    P.prod_map_demazureOperator_apply_eq_self_of_mem_parabolic b hf hν (hνv ▸ h)]

/-- **Demazure operators on cosets.** On an element of `ℤ[M]` invariant under the standard
parabolic subgroup `W_J`, the Demazure operator `D_w` along a reduced word of `w` depends only on
the coset `w W_J`. -/
theorem prod_map_demazureOperator_apply_eq_of_inv_mul_mem_parabolic {J : Set b.support}
    {f : AddMonoidAlgebra ℤ M}
    (hf : ∀ v ∈ (weylCoxeterSystem P b).parabolic J, ∀ x, f.coeff (v • x) = f.coeff x)
    {ω ω' : List b.support} (hω : (weylCoxeterSystem P b).IsReduced ω)
    (hω' : (weylCoxeterSystem P b).IsReduced ω')
    (h : ((weylCoxeterSystem P b).wordProd ω)⁻¹ * (weylCoxeterSystem P b).wordProd ω' ∈
      (weylCoxeterSystem P b).parabolic J) :
    (ω.map fun m : b.support ↦ P.demazureOperator m).prod f =
      (ω'.map fun m : b.support ↦ P.demazureOperator m).prod f := by
  set cs := weylCoxeterSystem P b
  -- Compare both sides with a reduced word of the minimal representative of the common coset.
  obtain ⟨v, hv, hmin⟩ := cs.exists_isMinimalCosetRep J (cs.wordProd ω)
  obtain ⟨μ, hμ, hμu⟩ := cs.exists_isReduced (cs.wordProd ω * v)
  rw [hμu] at hmin
  have hμω : (cs.wordProd μ)⁻¹ * cs.wordProd ω ∈ cs.parabolic J := by
    rw [← hμu, mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem hv
  have hμω' : (cs.wordProd μ)⁻¹ * cs.wordProd ω' ∈ cs.parabolic J := by
    have := mul_mem hμω h
    rwa [mul_assoc, mul_inv_cancel_left] at this
  rw [P.prod_map_demazureOperator_apply_eq_of_isMinimalCosetRep b hf hω hμ hmin hμω,
    P.prod_map_demazureOperator_apply_eq_of_isMinimalCosetRep b hf hω' hμ hmin hμω']

/-! ### The wall case: Demazure characters of a dominant weight -/

variable {P b} [P.flip.IsReduced] {lam : M}

/-- A basis element `c e^λ` at a dominant weight `λ` is invariant under the parabolic subgroup of
the walls through `λ`, which is its stabilizer. -/
private lemma coeff_single_smul_of_mem_parabolic (hlam : lam ∈ dominantChamber P b) (c : ℤ)
    {v : P.weylGroup} (hv : v ∈ (weylCoxeterSystem P b).parabolic (P.wallIndices b lam)) (x : M) :
    (single lam c).coeff (v • x) = (single lam c).coeff x := by
  rw [P.parabolic_wallIndices_eq_stabilizer b hlam, MulAction.mem_stabilizer_iff] at hv
  conv_lhs => rw [← hv]
  simp only [coeff_single]
  exact Finsupp.single_apply_left (MulAction.injective v) lam x c

/-- **The wall case: Demazure characters are indexed by orbit weights.** For a dominant weight
`λ`, the Demazure character `D_w(c e^λ)` along a reduced word of `w` depends only on the orbit
weight `w λ`, that is, on the coset of `w` in `W / W_λ`. -/
theorem prod_map_demazureOperator_single_eq_of_smul_eq (hlam : lam ∈ dominantChamber P b)
    (c : ℤ) {ω ω' : List b.support} (hω : (weylCoxeterSystem P b).IsReduced ω)
    (hω' : (weylCoxeterSystem P b).IsReduced ω')
    (h : (weylCoxeterSystem P b).wordProd ω • lam = (weylCoxeterSystem P b).wordProd ω' • lam) :
    (ω.map fun m : b.support ↦ P.demazureOperator m).prod (single lam c) =
      (ω'.map fun m : b.support ↦ P.demazureOperator m).prod (single lam c) :=
  P.prod_map_demazureOperator_apply_eq_of_inv_mul_mem_parabolic b
    (fun _ hv ↦ coeff_single_smul_of_mem_parabolic hlam c hv) hω hω'
    ((inv_mul_mem_parabolic_wallIndices_iff hlam).mpr h.symm)

/-- **The Demazure recursion, raising case.** Let `λ` be dominant, `ω` a reduced word of `w` and
`αᵢ` a simple root with `⟨w λ, αᵢ^∨⟩ ≥ 0`. Then `Dᵢ D_w(c e^λ) = D_{w'}(c e^λ)` for every reduced
word `ω'` of an element `w'` with `w' λ = sᵢ (w λ)`. -/
theorem demazureOperator_prod_map_demazureOperator_single_of_coroot'_nonneg
    (hlam : lam ∈ dominantChamber P b) (c : ℤ) {ω ω' : List b.support}
    (hω : (weylCoxeterSystem P b).IsReduced ω) (hω' : (weylCoxeterSystem P b).IsReduced ω')
    {i : b.support} (hi : 0 ≤ P.coroot' i ((weylCoxeterSystem P b).wordProd ω • lam))
    (h : (weylCoxeterSystem P b).wordProd ω' • lam =
      P.reflection i ((weylCoxeterSystem P b).wordProd ω • lam)) :
    P.demazureOperator i ((ω.map fun m : b.support ↦ P.demazureOperator m).prod (single lam c)) =
      (ω'.map fun m : b.support ↦ P.demazureOperator m).prod (single lam c) := by
  set cs := weylCoxeterSystem P b
  by_cases hdesc : cs.IsLeftDescent (cs.wordProd ω) i
  · -- Then `⟨w λ, αᵢ^∨⟩ = 0`, so `sᵢ` fixes `w λ` and `Dᵢ` is absorbed into `D_w`.
    have hzero : P.coroot' i (cs.wordProd ω • lam) = 0 :=
      le_antisymm (coroot'_smul_nonpos_of_isLeftDescent hlam hdesc) hi
    rw [← mul_apply_eq_comp,
      P.demazureOperator_mul_prod_map_demazureOperator_of_isLeftDescent b hω hdesc]
    refine prod_map_demazureOperator_single_eq_of_smul_eq hlam c hω hω' ?_
    rw [h, reflection_apply, hzero, zero_smul, sub_zero]
  · -- Otherwise `i :: ω` is a reduced word of `sᵢ w`.
    have hred : cs.IsReduced (i :: ω) := by
      rw [CoxeterSystem.IsReduced, cs.wordProd_cons, cs.not_isLeftDescent_iff.mp hdesc, hω.eq,
        List.length_cons]
    have key := prod_map_demazureOperator_single_eq_of_smul_eq hlam c hred hω' ?_
    · rwa [List.map_cons, List.prod_cons, mul_apply_eq_comp] at key
    rw [h, cs.wordProd_cons, mul_smul, weylCoxeterSystem_simple, weylGroup.ofIdx_smul,
      Equiv.reflection_smul]

/-- **The Demazure recursion, stationary case.** Let `λ` be dominant, `ω` a reduced word of `w`
and `αᵢ` a simple root with `⟨w λ, αᵢ^∨⟩ ≤ 0`. Then `Dᵢ D_w(c e^λ) = D_w(c e^λ)`. -/
theorem demazureOperator_prod_map_demazureOperator_single_of_coroot'_nonpos
    (hlam : lam ∈ dominantChamber P b) (c : ℤ) {ω : List b.support}
    (hω : (weylCoxeterSystem P b).IsReduced ω) {i : b.support}
    (hi : P.coroot' i ((weylCoxeterSystem P b).wordProd ω • lam) ≤ 0) :
    P.demazureOperator i ((ω.map fun m : b.support ↦ P.demazureOperator m).prod (single lam c)) =
      (ω.map fun m : b.support ↦ P.demazureOperator m).prod (single lam c) := by
  by_cases hdesc : (weylCoxeterSystem P b).IsLeftDescent ((weylCoxeterSystem P b).wordProd ω) i
  · rw [← mul_apply_eq_comp,
      P.demazureOperator_mul_prod_map_demazureOperator_of_isLeftDescent b hω hdesc]
  · -- Then `⟨w λ, αᵢ^∨⟩ = 0`, so `sᵢ` fixes `w λ`.
    have hzero : P.coroot' i ((weylCoxeterSystem P b).wordProd ω • lam) = 0 :=
      le_antisymm hi (coroot'_smul_nonneg_of_not_isLeftDescent hlam hdesc)
    refine demazureOperator_prod_map_demazureOperator_single_of_coroot'_nonneg hlam c hω hω
      hzero.ge ?_
    rw [reflection_apply, hzero, zero_smul, sub_zero]

end RootPairing
