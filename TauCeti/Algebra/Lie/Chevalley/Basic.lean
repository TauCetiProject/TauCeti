/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.RootSystem.Chain
public import TauCeti.Algebra.Lie.FullCartan

import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# The integral Chevalley Lie algebra over a full cocharacter lattice

Let `P : RootPairing ι ℤ X Y` be a finite root datum over `ℤ`. A split reductive group with root
datum `P` has Lie algebra decomposed into its full cocharacter lattice `Y` (retaining any central
torus, without assuming coroots span `Y` or split off integrally) and one root line `ℤ eᵢ` for each
`i : ι`.

This file defines extensional integer Chevalley structure-constant tables `P.ChevalleyConstants`
(`⁅eᵢ, e_{-i}⁆ = H_{αᵢ∨}`, `|Nᵢⱼ| = P.chainBotCoeff i j + 1`, skew-symmetry, opposition symmetry,
and three-root Jacobi identities) and constructs the `ℤ`-Lie algebra
`RootPairing.ChevalleyLieAlgebra c` on `TauCeti.FullCartan Y ι`, sharing the generic full-Cartan
carrier and generator-reduction Lie axioms with `Matrix.FullShellLieAlgebra` without restricting to
simply-laced norm-two shells.

## Main definitions and results

* `RootPairing.tripleRootCoeff`: the `l`-th root coordinate of `⁅eᵢ, ⁅eⱼ, eₖ⁆⁆`.
* `RootPairing.ChevalleyConstants`, `RootPairing.ChevalleyConstants.isReduced`,
  `RootPairing.ChevalleyConstants.ofIsEmpty`: Chevalley structure-constant tables on `P`, proof that
  their existence forces `P.IsReduced`, and the unique table when `ι` is empty.
* `RootPairing.ChevalleyLieAlgebra`, `RootPairing.ChevalleyLieAlgebra.cartan`,
  `RootPairing.ChevalleyLieAlgebra.root`, `RootPairing.ChevalleyLieAlgebra.basis`: the `ℤ`-Lie
  algebra on `Y × (ι →₀ ℤ)` and its `ℤ`-basis indexed by `J ⊕ ι`.
* `RootPairing.ChevalleyLieAlgebra.mem_center_iff`,
  `RootPairing.ChevalleyLieAlgebra.center_eq_map_iInf_ker`,
  `RootPairing.ChevalleyLieAlgebra.cartanEquivOfIsEmpty`: center over the full cocharacter lattice
  and abelian identification with `Y` when `ι` is empty.

## References

* C. Chevalley, *Sur certains groupes simples*, Tohoku Math. J. (2) **7** (1955), 14--66.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016), §§1--2.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, Chapter 1.
-/

public section

open Module Set

namespace RootPairing

section Constants

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

open scoped Classical in
/-- The `l`-th root coordinate of `⁅eᵢ, ⁅eⱼ, eₖ⁆⁆` for a candidate integer structure-constant
table `N` on `P`: `-⟨αᵢ, αⱼ∨⟩` at `l = i` when `αⱼ + αₖ = 0`, `Nᵢₘ * Nⱼₖ` when `αₘ = αⱼ + αₖ` and
`αₗ = αᵢ + αₘ`, and `0` otherwise. -/
noncomputable def tripleRootCoeff (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ) (i j k l : ι) : ℤ :=
  (if P.root j + P.root k = 0 ∧ l = i then -P.pairing i j else 0) +
    if h : ∃ m, P.root m = P.root j + P.root k then
      if P.root l = P.root i + P.root h.choose then N i h.choose * N j k else 0
    else 0

open scoped Classical in
/-- When `αⱼ + αₖ = 0`, `P.tripleRootCoeff N i j k l` is `-P.pairing i j` at `l = i` and `0`
otherwise. -/
theorem tripleRootCoeff_of_add_eq_zero (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hjk : P.root j + P.root k = 0) :
    P.tripleRootCoeff N i j k l = if l = i then -P.pairing i j else 0 := by
  rw [tripleRootCoeff, dite_eq_right (fun ⟨m, hm⟩ ↦ P.ne_zero m (hm.trans hjk)), add_zero]
  by_cases hli : l = i <;> simp [hjk, hli]

open scoped Classical in
/-- When `αₘ = αⱼ + αₖ`, `P.tripleRootCoeff N i j k l` is `N i m * N j k` if `αₗ = αᵢ + αₘ` and
`0` otherwise. -/
theorem tripleRootCoeff_of_root_eq_add (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k m l : ι} (hm : P.root m = P.root j + P.root k) :
    P.tripleRootCoeff N i j k l = if P.root l = P.root i + P.root m then N i m * N j k else 0 := by
  have hex : ∃ m', P.root m' = P.root j + P.root k := ⟨m, hm⟩
  rw [tripleRootCoeff, ite_eq_right (fun h ↦ P.ne_zero m (hm.trans h.1)), zero_add,
    dite_eq_left hex, P.root.injective (hex.choose_spec.trans hm.symm)]

/-- When `αⱼ + αₖ` is neither a root nor zero, `P.tripleRootCoeff N i j k l` vanishes. -/
theorem tripleRootCoeff_of_notMem_of_add_ne_zero (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hnot : P.root j + P.root k ∉ range P.root) (hne : P.root j + P.root k ≠ 0) :
    P.tripleRootCoeff N i j k l = 0 := by
  classical
  rw [tripleRootCoeff, ite_eq_right (fun h ↦ hne h.1),
    dite_eq_right (fun ⟨m, hm⟩ ↦ hnot ⟨m, hm⟩), add_zero]

/-- `P.tripleRootCoeff N i j k l` vanishes whenever `P.root l ≠ P.root i + P.root j + P.root k`. -/
theorem tripleRootCoeff_eq_zero_of_ne_sum (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hl : P.root l ≠ P.root i + P.root j + P.root k) :
    P.tripleRootCoeff N i j k l = 0 := by
  classical
  by_cases hjk0 : P.root j + P.root k = 0
  · rw [P.tripleRootCoeff_of_add_eq_zero _ hjk0,
      ite_eq_right (by rintro rfl; exact hl (by rw [add_assoc, hjk0, add_zero]))]
  · by_cases hex : ∃ m, P.root m = P.root j + P.root k
    · obtain ⟨m, hm⟩ := hex
      rw [P.tripleRootCoeff_of_root_eq_add _ hm,
        ite_eq_right (fun h ↦ hl (by rw [h, hm, add_assoc]))]
    · exact P.tripleRootCoeff_of_notMem_of_add_ne_zero _ (fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩) hjk0

variable [Finite ι]

/-- **Chevalley integer structure constants** on a finite integral root pairing `P`: an extensional
table `structConst : ι → ι → ℤ` vanishing outside root sums, skew-symmetric, having absolute value
`P.chainBotCoeff i j + 1` on root sums, negated by root opposition, and satisfying the three-root
Jacobi identities on coroot and root coordinates. -/
@[ext]
structure ChevalleyConstants (P : RootPairing ι ℤ X Y) where
  /-- The integer coefficient `Nᵢⱼ` of `eₖ` in `⁅eᵢ, eⱼ⁆` when `αₖ = αᵢ + αⱼ`, else `0`. -/
  structConst : ι → ι → ℤ
  /-- Non-root sums carry zero structure constant, leaving no unconstrained entries. -/
  structConst_eq_zero_of_notMem_range (i j : ι) :
    P.root i + P.root j ∉ range P.root → structConst i j = 0
  /-- Skew-symmetry `Nⱼᵢ = -Nᵢⱼ`. -/
  structConst_swap (i j : ι) : structConst j i = -structConst i j
  /-- Chevalley normalization `|Nᵢⱼ| = pᵢⱼ + 1` whenever `αᵢ + αⱼ` is a root. -/
  natAbs_structConst {i j k : ι} :
    P.root k = P.root i + P.root j → (structConst i j).natAbs = P.chainBotCoeff i j + 1
  /-- Compatibility with root opposition: `N_{-i, -j} = -Nᵢⱼ`. -/
  structConst_reflectionPerm (i j : ι) :
    structConst (P.reflectionPerm i i) (P.reflectionPerm j j) = -structConst i j
  /-- Cartan component of the three-root Jacobi identity when `αᵢ + αⱼ + αₖ = 0`. -/
  coroot_jacobi {i j k : ι} : P.root i + P.root j + P.root k = 0 →
    structConst j k • P.coroot i + structConst k i • P.coroot j + structConst i j • P.coroot k = 0
  /-- Root-coordinate component of the three-root Jacobi identity. -/
  root_jacobi (i j k l : ι) :
    P.tripleRootCoeff structConst i j k l + P.tripleRootCoeff structConst j k i l +
      P.tripleRootCoeff structConst k i j l = 0

namespace ChevalleyConstants

variable {P : RootPairing ι ℤ X Y} (c : P.ChevalleyConstants)

/-- Two Chevalley constant tables agree as soon as they agree on pairs summing to a root. -/
theorem ext_of_mem_range {c₁ c₂ : P.ChevalleyConstants}
    (h : ∀ i j, P.root i + P.root j ∈ range P.root → c₁.structConst i j = c₂.structConst i j) :
    c₁ = c₂ := by
  ext i j
  by_cases hij : P.root i + P.root j ∈ range P.root
  · exact h i j hij
  · rw [c₁.structConst_eq_zero_of_notMem_range i j hij,
      c₂.structConst_eq_zero_of_notMem_range i j hij]

@[simp]
theorem structConst_self (i : ι) : c.structConst i i = 0 := by
  have := c.structConst_swap i i; omega

theorem structConst_eq_zero_of_add_eq_zero {i j : ι} (h : P.root i + P.root j = 0) :
    c.structConst i j = 0 :=
  c.structConst_eq_zero_of_notMem_range i j fun ⟨k, hk⟩ ↦ P.ne_zero k (hk.trans h)

theorem structConst_ne_zero {i j k : ι} (h : P.root k = P.root i + P.root j) :
    c.structConst i j ≠ 0 := by
  have := c.natAbs_structConst h; omega

theorem structConst_eq_natCast_or_eq_neg_natCast {i j k : ι}
    (h : P.root k = P.root i + P.root j) :
    c.structConst i j = (P.chainBotCoeff i j + 1 : ℕ) ∨
      c.structConst i j = -((P.chainBotCoeff i j + 1 : ℕ) : ℤ) := by
  rcases Int.natAbs_eq (c.structConst i j) with hp | hn
  · exact .inl (hp.trans (by rw [c.natAbs_structConst h]))
  · exact .inr (hn.trans (by rw [c.natAbs_structConst h]))

include c in
/-- A finite integral root pairing admitting Chevalley structure constants is reduced. -/
theorem isReduced : P.IsReduced := by
  -- Skew-symmetry forces `N_{i,i} = 0`, whereas `2 αᵢ ∈ Φ` would require `|N_{i,i}| = p + 1 ≥ 1`.
  have : Module.IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive ℤ Y := .of_isPerfPair P.toLinearMap.flip
  have hno2 (i : ι) : P.root i + P.root i ∉ range P.root := fun ⟨k, hk⟩ ↦ by
    have hnat := c.natAbs_structConst hk; rw [c.structConst_self] at hnat; omega
  have h14 {a b} (h : P.pairingIn ℤ a b = 1 ∧ P.pairingIn ℤ b a = 4) : False :=
    hno2 a ⟨b, by have := (P.pairingIn_one_four_iff ℤ a b).mp h; rwa [two_smul] at this⟩
  have hn14 {a b} (h : P.pairingIn ℤ a b = -1 ∧ P.pairingIn ℤ b a = -4) : False :=
    hno2 a ⟨P.reflectionPerm b b, by
      rw [root_reflectionPerm, reflection_apply_self,
        (P.pairingIn_neg_one_neg_four_iff ℤ a b).mp h, neg_smul, neg_neg, two_smul]⟩
  rw [P.isReduced_iff']
  intro i j hij hdep
  have hp := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have hcox : P.pairingIn ℤ i j * P.pairingIn ℤ j i = 4 :=
    (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hdep
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | (rw [h.1, h.2] at hcox; omega)
    | exact (h14 h).elim
    | exact (h14 ⟨h.2, h.1⟩).elim
    | exact (hn14 h).elim
    | exact (hn14 ⟨h.2, h.1⟩).elim
    | exact absurd ((P.pairingIn_two_two_iff ℤ i j).mp h) hij
    | exact (P.pairingIn_neg_two_neg_two_iff ℤ i j).mp h

/-- The unique Chevalley structure-constant table on a root-free datum `[IsEmpty ι]`. -/
def ofIsEmpty (P : RootPairing ι ℤ X Y) [IsEmpty ι] : P.ChevalleyConstants where
  structConst := isEmptyElim
  structConst_eq_zero_of_notMem_range := isEmptyElim
  structConst_swap := isEmptyElim
  natAbs_structConst {i} := isEmptyElim i
  structConst_reflectionPerm := isEmptyElim
  coroot_jacobi {i} := isEmptyElim i
  root_jacobi := isEmptyElim

instance [IsEmpty ι] : Unique P.ChevalleyConstants where
  default := ofIsEmpty P
  uniq _ := by ext i; exact isEmptyElim i

end ChevalleyConstants

end Constants

/-! ## The full reductive integral Chevalley Lie algebra -/

section LieAlgebra

variable {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
  {P : RootPairing ι ℤ X Y}

/-- **The integral Chevalley Lie algebra** of a root datum `P` over its full cocharacter group `Y`,
realized on `TauCeti.FullCartan Y ι` (`Y × (ι →₀ ℤ)`) so that no splitting of `Y` into central and
coroot summands is assumed. -/
def ChevalleyLieAlgebra {P : RootPairing ι ℤ X Y} (_c : P.ChevalleyConstants) : Type _ :=
  TauCeti.FullCartan Y ι

namespace ChevalleyLieAlgebra

variable (c : P.ChevalleyConstants)

noncomputable instance : AddCommGroup (ChevalleyLieAlgebra c) :=
  inferInstanceAs (AddCommGroup (TauCeti.FullCartan Y ι))

/-- Identification of `ChevalleyLieAlgebra c` with its underlying product `Y × (ι →₀ ℤ)`. -/
noncomputable def equivProd : ChevalleyLieAlgebra c ≃ₗ[ℤ] Y × (ι →₀ ℤ) :=
  TauCeti.FullCartan.equivProd Y ι

/-- The Cartan vector `H_y` attached to a cocharacter `y : Y`, as a `ℤ`-linear embedding. -/
noncomputable def cartan : Y →ₗ[ℤ] ChevalleyLieAlgebra c :=
  TauCeti.FullCartan.cartan Y ι

/-- The Chevalley root vector `eᵢ` attached to a root index `i : ι`. -/
noncomputable def root (i : ι) : ChevalleyLieAlgebra c :=
  TauCeti.FullCartan.root Y ι i

@[simp]
theorem equivProd_cartan (y : Y) : equivProd c (cartan c y) = (y, 0) :=
  TauCeti.FullCartan.equivProd_cartan y

@[simp]
theorem equivProd_root (i : ι) : equivProd c (root c i) = (0, Finsupp.single i 1) :=
  TauCeti.FullCartan.equivProd_root i

theorem cartan_injective : Function.Injective (cartan c) :=
  TauCeti.FullCartan.cartan_injective

theorem root_ne_zero (i : ι) : root c i ≠ 0 :=
  TauCeti.FullCartan.root_ne_zero i

variable {c} in
/-- Two `ℤ`-linear maps out of `ChevalleyLieAlgebra c` agree once they agree on all Cartan vectors
and on all root vectors. -/
theorem linearMap_ext {N : Type*} [AddCommGroup N] {f g : ChevalleyLieAlgebra c →ₗ[ℤ] N}
    (hc : ∀ y, f (cartan c y) = g (cartan c y)) (hr : ∀ i, f (root c i) = g (root c i)) :
    f = g :=
  TauCeti.FullCartan.linearMap_ext hc hr

open scoped Classical in
/-- The bracket `⁅eᵢ, eⱼ⁆` of two root vectors: `H_{αᵢ∨}` when `αᵢ + αⱼ = 0`, `Nᵢⱼ eₖ` when
`αₖ = αᵢ + αⱼ`, and `0` otherwise. -/
noncomputable def rootBracket (i j : ι) : ChevalleyLieAlgebra c :=
  if P.root i + P.root j = 0 then cartan c (P.coroot i)
  else if h : ∃ k, P.root k = P.root i + P.root j then c.structConst i j • root c h.choose
  else 0

theorem rootBracket_of_add_eq_zero {i j : ι} (h : P.root i + P.root j = 0) :
    rootBracket c i j = cartan c (P.coroot i) := by
  classical rw [rootBracket, ite_eq_left h]

@[simp]
theorem rootBracket_reflectionPerm_right (i : ι) :
    rootBracket c i (P.reflectionPerm i i) = cartan c (P.coroot i) :=
  rootBracket_of_add_eq_zero c (by simp)

theorem rootBracket_of_root_eq_add {i j k : ι} (h : P.root k = P.root i + P.root j) :
    rootBracket c i j = c.structConst i j • root c k := by
  classical
  have hex : ∃ m, P.root m = P.root i + P.root j := ⟨k, h⟩
  rw [rootBracket, ite_eq_right (fun h0 ↦ P.ne_zero k (h.trans h0)), dite_eq_left hex,
    P.root.injective (hex.choose_spec.trans h.symm)]

theorem rootBracket_of_notMem_of_add_ne_zero {i j : ι}
    (hnot : P.root i + P.root j ∉ range P.root) (hne : P.root i + P.root j ≠ 0) :
    rootBracket c i j = 0 := by
  classical rw [rootBracket, ite_eq_right hne, dite_eq_right (fun ⟨k, hk⟩ ↦ hnot ⟨k, hk⟩)]

open scoped Classical in
@[simp]
theorem equivProd_rootBracket_fst (i j : ι) :
    (equivProd c (rootBracket c i j)).1 = if P.root i + P.root j = 0 then P.coroot i else 0 := by
  by_cases h0 : P.root i + P.root j = 0
  · rw [rootBracket_of_add_eq_zero c h0, equivProd_cartan, ite_eq_left h0]
  · rw [ite_eq_right h0]
    by_cases hm : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hm; simp [rootBracket_of_root_eq_add c hk]
    · simp [rootBracket_of_notMem_of_add_ne_zero c (fun ⟨k, hk⟩ ↦ hm ⟨k, hk⟩) h0]

open scoped Classical in
@[simp]
theorem equivProd_rootBracket_snd_apply (i j l : ι) :
    (equivProd c (rootBracket c i j)).2 l =
      if P.root l = P.root i + P.root j then c.structConst i j else 0 := by
  by_cases h0 : P.root i + P.root j = 0
  · rw [rootBracket_of_add_eq_zero c h0, ite_eq_right (fun hl ↦ P.ne_zero l (hl.trans h0))]; simp
  · by_cases hm : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hm
      rw [rootBracket_of_root_eq_add c hk]
      by_cases hlk : l = k
      · subst hlk; simp [hk]
      · rw [ite_eq_right (fun hl ↦ hlk (P.root.injective (hl.trans hk.symm)))]; simp [hlk]
    · rw [rootBracket_of_notMem_of_add_ne_zero c (fun ⟨k, hk⟩ ↦ hm ⟨k, hk⟩) h0,
        ite_eq_right (fun hl ↦ hm ⟨l, hl⟩)]; simp

@[simp]
theorem rootBracket_self (i : ι) : rootBracket c i i = 0 := by
  have hself : P.root i + P.root i ≠ 0 := by
    rw [ne_eq, add_eq_zero_iff_eq_neg, P.root_eq_neg_iff]; exact P.ne_neg i
  exact (equivProd c).injective (Prod.ext (by simp [hself]) (by ext l; simp))

theorem rootBracket_swap (i j : ι) : rootBracket c j i = -rootBracket c i j := by
  classical
  apply (equivProd c).injective; rw [map_neg]; ext1
  · rw [equivProd_rootBracket_fst, Prod.fst_neg, equivProd_rootBracket_fst]
    by_cases h0 : P.root i + P.root j = 0
    · have h0' : P.root j + P.root i = 0 := by rw [add_comm, h0]
      rw [ite_eq_left h0', ite_eq_left h0,
        P.coroot_eq_neg_iff.mpr (P.root_eq_neg_iff.mp (add_eq_zero_iff_eq_neg.mp h0'))]
    · rw [ite_eq_right (add_comm (P.root i) (P.root j) ▸ h0), ite_eq_right h0, neg_zero]
  · ext l
    rw [equivProd_rootBracket_snd_apply, Prod.snd_neg, Finsupp.coe_neg, Pi.neg_apply,
      equivProd_rootBracket_snd_apply, add_comm (P.root j) (P.root i), c.structConst_swap i j]
    by_cases hl : P.root l = P.root i + P.root j <;> simp [hl]

/-- The `ℤ`-bilinear bracket on `ChevalleyLieAlgebra c`, determined by `⁅H_y, H_z⁆ = 0`,
`⁅H_y, eⱼ⁆ = ⟨αⱼ, y⟩ eⱼ`, `⁅eᵢ, H_z⁆ = -⟨αᵢ, z⟩ eᵢ`, and `⁅eᵢ, eⱼ⁆ = rootBracket c i j`. -/
noncomputable def bracketBilin :
    ChevalleyLieAlgebra c →ₗ[ℤ] ChevalleyLieAlgebra c →ₗ[ℤ] ChevalleyLieAlgebra c :=
  TauCeti.FullCartan.bracketBilin (fun i ↦ P.toLinearMap (P.root i)) (rootBracket c)

noncomputable instance : Bracket (ChevalleyLieAlgebra c) (ChevalleyLieAlgebra c) :=
  ⟨fun x y ↦ bracketBilin c x y⟩

@[simp]
theorem bracketBilin_apply_apply (x y : ChevalleyLieAlgebra c) : bracketBilin c x y = ⁅x, y⁆ :=
  (rfl)

@[simp]
theorem cartan_lie_cartan (y z : Y) : ⁅cartan c y, cartan c z⁆ = 0 :=
  TauCeti.FullCartan.bracketBilin_cartan_cartan _ _ y z

@[simp]
theorem cartan_lie_root (y : Y) (i : ι) :
    ⁅cartan c y, root c i⁆ = P.toLinearMap (P.root i) y • root c i :=
  TauCeti.FullCartan.bracketBilin_cartan_root _ _ y i

@[simp]
theorem root_lie_cartan (i : ι) (y : Y) :
    ⁅root c i, cartan c y⁆ = -(P.toLinearMap (P.root i) y • root c i) :=
  TauCeti.FullCartan.bracketBilin_root_cartan _ _ i y

@[simp]
theorem root_lie_root (i j : ι) : ⁅root c i, root c j⁆ = rootBracket c i j :=
  TauCeti.FullCartan.bracketBilin_root_root _ _ i j

private theorem cartan_lie_rootBracket (y : Y) (i j : ι) :
    ⁅cartan c y, rootBracket c i j⁆ =
      (P.toLinearMap (P.root i) y + P.toLinearMap (P.root j) y) • rootBracket c i j := by
  by_cases h0 : P.root i + P.root j = 0
  · have hsum : P.toLinearMap (P.root i) y + P.toLinearMap (P.root j) y = 0 := by
      rw [← LinearMap.add_apply, ← map_add, h0, map_zero, LinearMap.zero_apply]
    rw [rootBracket_of_add_eq_zero c h0, cartan_lie_cartan, hsum, zero_smul]
  · by_cases hex : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hex
      rw [rootBracket_of_root_eq_add c hk, ← bracketBilin_apply_apply, map_smul,
        bracketBilin_apply_apply, cartan_lie_root, hk, map_add, LinearMap.add_apply, smul_comm]
    · rw [rootBracket_of_notMem_of_add_ne_zero c (fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩) h0,
        ← bracketBilin_apply_apply, map_zero, smul_zero]

open scoped Classical in
private theorem equivProd_root_lie_rootBracket_fst (i j k : ι) :
    (equivProd c ⁅root c i, rootBracket c j k⁆).1 =
      if P.root i + P.root j + P.root k = 0 then c.structConst j k • P.coroot i else 0 := by
  by_cases hjk0 : P.root j + P.root k = 0
  · have hsum : P.root i + P.root j + P.root k ≠ 0 := by
      rw [add_assoc, hjk0, add_zero]; exact P.ne_zero i
    simp [rootBracket_of_add_eq_zero c hjk0, hsum]
  · by_cases hex : ∃ m, P.root m = P.root j + P.root k
    · obtain ⟨m, hm⟩ := hex
      rw [rootBracket_of_root_eq_add c hm, ← bracketBilin_apply_apply, map_smul,
        bracketBilin_apply_apply, map_smul, Prod.smul_fst, root_lie_root, equivProd_rootBracket_fst]
      have hiff : P.root i + P.root m = 0 ↔ P.root i + P.root j + P.root k = 0 := by
        rw [hm, add_assoc]
      by_cases him : P.root i + P.root m = 0 <;> simp [him, hiff.symm]
    · have hsum : P.root i + P.root j + P.root k ≠ 0 := fun h0 ↦
        hex ⟨P.reflectionPerm i i, P.root_reflectionPerm_self_eq_add_of_add_add_eq_zero h0⟩
      simp [rootBracket_of_notMem_of_add_ne_zero c (fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩) hjk0,
        ← bracketBilin_apply_apply, hsum]

private theorem equivProd_root_lie_rootBracket_snd_apply (i j k l : ι) :
    (equivProd c ⁅root c i, rootBracket c j k⁆).2 l = P.tripleRootCoeff c.structConst i j k l := by
  classical
  by_cases hjk0 : P.root j + P.root k = 0
  · rw [rootBracket_of_add_eq_zero c hjk0, root_lie_cartan,
      P.tripleRootCoeff_of_add_eq_zero c.structConst hjk0]
    by_cases hli : l = i
    · subst hli; simp [P.root_coroot_eq_pairing]
    · simp [hli]
  · by_cases hex : ∃ m, P.root m = P.root j + P.root k
    · obtain ⟨m, hm⟩ := hex
      rw [rootBracket_of_root_eq_add c hm, P.tripleRootCoeff_of_root_eq_add c.structConst hm,
        ← bracketBilin_apply_apply, map_smul, bracketBilin_apply_apply, map_smul, Prod.smul_snd,
        Finsupp.coe_smul, Pi.smul_apply, root_lie_root, equivProd_rootBracket_snd_apply,
        smul_eq_mul]
      by_cases hlm : P.root l = P.root i + P.root m <;> simp [hlm, mul_comm]
    · have hnot : P.root j + P.root k ∉ range P.root := fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩
      simp [rootBracket_of_notMem_of_add_ne_zero c hnot hjk0,
        P.tripleRootCoeff_of_notMem_of_add_ne_zero c.structConst hnot hjk0,
        ← bracketBilin_apply_apply]

private theorem jacobi_root_root_root (i j k : ι) :
    ⁅root c i, rootBracket c j k⁆ + ⁅root c j, rootBracket c k i⁆ +
      ⁅root c k, rootBracket c i j⁆ = 0 := by
  classical
  apply (equivProd c).injective
  rw [map_add, map_add, map_zero]
  ext1
  · simp only [Prod.fst_add, Prod.fst_zero, equivProd_root_lie_rootBracket_fst]
    by_cases h0 : P.root i + P.root j + P.root k = 0
    · rw [ite_eq_left h0, ite_eq_left (by rw [← h0]; abel), ite_eq_left (by rw [← h0]; abel)]
      exact c.coroot_jacobi h0
    · rw [ite_eq_right h0, ite_eq_right (fun h ↦ h0 (by rw [← h]; abel)),
        ite_eq_right (fun h ↦ h0 (by rw [← h]; abel)), add_zero, add_zero]
  · ext l
    simpa [equivProd_root_lie_rootBracket_snd_apply] using c.root_jacobi i j k l

protected theorem add_lie (x y z : ChevalleyLieAlgebra c) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ :=
  LinearMap.congr_fun ((bracketBilin c).map_add x y) z

protected theorem lie_add (x y z : ChevalleyLieAlgebra c) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ :=
  (bracketBilin c x).map_add y z

protected theorem lie_self (x : ChevalleyLieAlgebra c) : ⁅x, x⁆ = 0 :=
  TauCeti.FullCartan.bracketBilin_self (rootBracket_swap c) (rootBracket_self c) x

protected theorem leibniz_lie (x y z : ChevalleyLieAlgebra c) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ :=
  TauCeti.FullCartan.bracketBilin_leibniz (rootBracket_swap c)
    (cartan_lie_rootBracket c) (jacobi_root_root_root c) x y z

protected theorem lie_zsmul (r : ℤ) (x y : ChevalleyLieAlgebra c) : ⁅x, r • y⁆ = r • ⁅x, y⁆ :=
  (bracketBilin c x).map_smul r y

noncomputable instance instLieRing : LieRing (ChevalleyLieAlgebra c) where
  add_lie := ChevalleyLieAlgebra.add_lie c
  lie_add := ChevalleyLieAlgebra.lie_add c
  lie_self := ChevalleyLieAlgebra.lie_self c
  leibniz_lie := ChevalleyLieAlgebra.leibniz_lie c

noncomputable instance instLieAlgebra : LieAlgebra ℤ (ChevalleyLieAlgebra c) where
  lie_smul := ChevalleyLieAlgebra.lie_zsmul c

theorem root_lie_root_of_add_eq_zero {i j : ι} (h : P.root i + P.root j = 0) :
    ⁅root c i, root c j⁆ = cartan c (P.coroot i) := by
  rw [root_lie_root, rootBracket_of_add_eq_zero c h]

theorem root_lie_root_reflectionPerm (i : ι) :
    ⁅root c i, root c (P.reflectionPerm i i)⁆ = cartan c (P.coroot i) := by
  rw [root_lie_root, rootBracket_reflectionPerm_right]

theorem root_lie_root_of_root_eq_add {i j k : ι} (h : P.root k = P.root i + P.root j) :
    ⁅root c i, root c j⁆ = c.structConst i j • root c k := by
  rw [root_lie_root, rootBracket_of_root_eq_add c h]

theorem root_lie_root_of_notMem_of_add_ne_zero {i j : ι}
    (hnot : P.root i + P.root j ∉ range P.root) (hne : P.root i + P.root j ≠ 0) :
    ⁅root c i, root c j⁆ = 0 := by
  rw [root_lie_root, rootBracket_of_notMem_of_add_ne_zero c hnot hne]

/-! ### Center over the full cocharacter lattice -/

@[simp]
theorem equivProd_cartan_lie_snd (y : Y) (x : ChevalleyLieAlgebra c) (i : ι) :
    (equivProd c ⁅cartan c y, x⁆).2 i = P.toLinearMap (P.root i) y * (equivProd c x).2 i := by
  let coord : ChevalleyLieAlgebra c →ₗ[ℤ] ℤ :=
    (Finsupp.lapply i).comp ((LinearMap.snd ℤ Y (ι →₀ ℤ)).comp (equivProd c).toLinearMap)
  have h : coord.comp (bracketBilin c (cartan c y)) = P.toLinearMap (P.root i) y • coord := by
    refine linearMap_ext (by simp [coord]) fun j ↦ ?_
    by_cases hij : i = j
    · subst hij; simp [coord]
    · simp [coord, Ne.symm hij]
  exact LinearMap.congr_fun h x

/-- The centralizer of the full Cartan lattice `Y` in `ChevalleyLieAlgebra c` is its image under
`cartan c`. -/
theorem forall_cartan_lie_eq_zero_iff (x : ChevalleyLieAlgebra c) :
    (∀ y, ⁅cartan c y, x⁆ = 0) ↔ x ∈ LinearMap.range (cartan c) := by
  refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ z ↦ hy ▸ cartan_lie_cartan c z y⟩
  have hroot : (equivProd c x).2 = 0 := by
    ext i
    have h := equivProd_cartan_lie_snd c (P.coroot i) x i
    rw [hx, map_zero, Prod.snd_zero, Finsupp.zero_apply,
      (P.root_coroot_eq_pairing i i).trans (P.pairing_same i)] at h
    simp only [Finsupp.zero_apply]; omega
  exact ⟨(equivProd c x).1, (equivProd c).injective
    (by rw [equivProd_cartan]; exact Prod.ext rfl hroot.symm)⟩

@[simp]
theorem forall_lie_cartan_eq_zero_iff (y : Y) :
    (∀ x : ChevalleyLieAlgebra c, ⁅x, cartan c y⁆ = 0) ↔
      ∀ i : ι, P.toLinearMap (P.root i) y = 0 :=
  ⟨fun hy i ↦ by simpa using congrArg (fun z ↦ (equivProd c z).2 i) (hy (root c i)),
   fun hw ↦ LinearMap.congr_fun <| linearMap_ext (f := (bracketBilin c).flip (cartan c y)) (g := 0)
     (by simp) fun i ↦ by simp [hw i]⟩

/-- An element of `ChevalleyLieAlgebra c` is central if and only if its root coordinates vanish and
its Cartan coordinate is annihilated by every root of `P`. -/
theorem mem_center_iff (x : ChevalleyLieAlgebra c) :
    x ∈ _root_.LieAlgebra.center ℤ (ChevalleyLieAlgebra c) ↔
      (equivProd c x).2 = 0 ∧ ∀ i : ι, P.toLinearMap (P.root i) (equivProd c x).1 = 0 := by
  refine ⟨fun hx ↦ ?_, fun ⟨hroot, hweight⟩ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := (forall_cartan_lie_eq_zero_iff c x).mp fun y ↦ hx (cartan c y)
    exact ⟨by simp, by simpa using (forall_lie_cartan_eq_zero_iff c y).mp hx⟩
  · have hx : x = cartan c (equivProd c x).1 :=
      (equivProd c).injective (by rw [equivProd_cartan]; exact Prod.ext rfl hroot)
    rw [hx]
    exact (forall_lie_cartan_eq_zero_iff c _).mpr hweight

/-- The center of `ChevalleyLieAlgebra c`, as a `ℤ`-submodule, is the Cartan image of the common
kernel of all roots on `Y`. -/
theorem center_eq_map_iInf_ker :
    (_root_.LieAlgebra.center ℤ (ChevalleyLieAlgebra c)).toSubmodule =
      Submodule.map (cartan c) (⨅ i : ι, LinearMap.ker (P.toLinearMap (P.root i))) := by
  ext x
  refine ⟨fun hx ↦ ?_,
    fun ⟨y, hy, hx⟩ ↦ hx ▸ (forall_lie_cartan_eq_zero_iff c y).mpr (by simpa using hy)⟩
  obtain ⟨y, rfl⟩ := (forall_cartan_lie_eq_zero_iff c x).mp fun y ↦ hx (cartan c y)
  exact ⟨y, by simpa using (forall_lie_cartan_eq_zero_iff c y).mp hx, rfl⟩

/-! ### The root-free datum `Φ = ∅` -/

/-- When the root index type `ι` is empty, `ChevalleyLieAlgebra c` is abelian. -/
instance instIsLieAbelianOfIsEmpty [IsEmpty ι] : IsLieAbelian (ChevalleyLieAlgebra c) :=
  ⟨fun x y ↦ by
    have h0 : bracketBilin c = 0 :=
      linearMap_ext (fun _ ↦ linearMap_ext (by simp) isEmptyElim) isEmptyElim
    simpa using congr($h0 x y)⟩

/-- When `ι` is empty, `cartan c` identifies the full cocharacter group `Y` with
`ChevalleyLieAlgebra c`. -/
noncomputable def cartanEquivOfIsEmpty [IsEmpty ι] : Y ≃ₗ[ℤ] ChevalleyLieAlgebra c :=
  LinearEquiv.ofLinearMap (cartan c) ((LinearMap.fst ℤ Y (ι →₀ ℤ)).comp (equivProd c).toLinearMap)
    (LinearMap.ext fun x ↦ (equivProd c).injective <|
      Prod.ext (by simp) (by ext i; exact isEmptyElim i))
    (LinearMap.ext fun y ↦ by simp)

@[simp]
theorem cartanEquivOfIsEmpty_apply [IsEmpty ι] (y : Y) : cartanEquivOfIsEmpty c y = cartan c y :=
  (rfl)

@[simp]
theorem cartanEquivOfIsEmpty_symm_apply [IsEmpty ι] (x : ChevalleyLieAlgebra c) :
    (cartanEquivOfIsEmpty c).symm x = (equivProd c x).1 :=
  (rfl)

/-! ### Integral Chevalley basis -/

section Basis

variable {J : Type*} (bY : Basis J ℤ Y)

/-- **The integral Chevalley basis** of `ChevalleyLieAlgebra c` attached to a `ℤ`-basis `bY` of the
full cocharacter group `Y`, indexed by `J ⊕ ι`. Its scalar extension `(basis c bY).baseChange R`
gives an `R`-basis of `R ⊗[ℤ] ChevalleyLieAlgebra c` over every commutative ring `R`. -/
noncomputable def basis : Basis (J ⊕ ι) ℤ (ChevalleyLieAlgebra c) :=
  (bY.prod (Finsupp.basisSingleOne : Basis ι ℤ (ι →₀ ℤ))).map (equivProd c).symm

@[simp]
theorem basis_inl (j : J) : basis c bY (.inl j) = cartan c (bY j) :=
  (equivProd c).injective (by simp [basis])

@[simp]
theorem basis_inr (i : ι) : basis c bY (.inr i) = root c i :=
  (equivProd c).injective (by simp [basis])

@[simp]
theorem basis_repr_inl (x : ChevalleyLieAlgebra c) (j : J) :
    (basis c bY).repr x (.inl j) = bY.repr (equivProd c x).1 j := by simp [basis]

@[simp]
theorem basis_repr_inr (x : ChevalleyLieAlgebra c) (i : ι) :
    (basis c bY).repr x (.inr i) = (equivProd c x).2 i := by simp [basis]

end Basis

end ChevalleyLieAlgebra

end LieAlgebra

end RootPairing
