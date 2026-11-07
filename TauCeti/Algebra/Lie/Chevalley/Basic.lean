/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The integral Chevalley Lie algebra over a full cocharacter lattice

Let `P : RootPairing ι ℤ X Y` be a finite root datum over `ℤ`. A split reductive group with root
datum `P` has Lie algebra decomposed into its full cocharacter lattice `Y` (retaining any central
torus, without assuming coroots span `Y` or split off integrally) and one root line `ℤ eᵢ` for each
`i : ι`.

This file defines extensional integer Chevalley structure-constant tables `P.ChevalleyConstants`
(`⁅eᵢ, e_{-i}⁆ = H_{αᵢ∨}`, `|Nᵢⱼ| = P.chainBotCoeff i j + 1`, skew-symmetry, opposition symmetry,
and three-root Jacobi identities) and constructs the `ℤ`-Lie algebra
`RootPairing.ChevalleyLieAlgebra c` on `Y × (ι →₀ ℤ)`, following the full-Cartan carrier pattern of
`Matrix.FullShellLieAlgebra` without restricting to simply-laced norm-two shells.

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
open scoped TensorProduct

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
theorem tripleRootCoeff_of_add_eq_zero (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hjk : P.root j + P.root k = 0) :
    P.tripleRootCoeff N i j k l = if l = i then -P.pairing i j else 0 := by
  rw [tripleRootCoeff, dite_eq_right (fun ⟨m, hm⟩ ↦ P.ne_zero m (hm.trans hjk)), add_zero]
  by_cases hli : l = i <;> simp [hjk, hli]

open scoped Classical in
theorem tripleRootCoeff_of_root_eq_add (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k m l : ι} (hm : P.root m = P.root j + P.root k) :
    P.tripleRootCoeff N i j k l = if P.root l = P.root i + P.root m then N i m * N j k else 0 := by
  have hex : ∃ m', P.root m' = P.root j + P.root k := ⟨m, hm⟩
  rw [tripleRootCoeff, ite_eq_right (fun h ↦ P.ne_zero m (hm.trans h.1)), zero_add,
    dite_eq_left hex, P.root.injective (hex.choose_spec.trans hm.symm)]

theorem tripleRootCoeff_of_notMem_of_add_ne_zero (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hnot : P.root j + P.root k ∉ range P.root) (hne : P.root j + P.root k ≠ 0) :
    P.tripleRootCoeff N i j k l = 0 := by
  classical
  rw [tripleRootCoeff, ite_eq_right (fun h ↦ hne h.1),
    dite_eq_right (fun ⟨m, hm⟩ ↦ hnot ⟨m, hm⟩), add_zero]

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
/-- Any finite integral root pairing admitting Chevalley structure constants is reduced: skew
symmetry forces `N_{i,i} = 0`, whereas `2 αᵢ ∈ Φ` would require `|N_{i,i}| = p + 1 ≥ 1`. -/
theorem isReduced : P.IsReduced := by
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
realized on the product `Y × (ι →₀ ℤ)` so that no splitting of `Y` into central and coroot summands
is assumed. -/
def ChevalleyLieAlgebra {P : RootPairing ι ℤ X Y} (_c : P.ChevalleyConstants) : Type _ :=
  Y × (ι →₀ ℤ)

namespace ChevalleyLieAlgebra

variable (c : P.ChevalleyConstants)

noncomputable instance : AddCommGroup (ChevalleyLieAlgebra c) :=
  inferInstanceAs (AddCommGroup (Y × (ι →₀ ℤ)))

/-- Identification of `ChevalleyLieAlgebra c` with its underlying product `Y × (ι →₀ ℤ)`. -/
noncomputable def equivProd : ChevalleyLieAlgebra c ≃ₗ[ℤ] Y × (ι →₀ ℤ) :=
  LinearEquiv.refl ℤ _

/-- The Cartan vector `H_y` attached to a cocharacter `y : Y`, as a `ℤ`-linear embedding. -/
noncomputable def cartan : Y →ₗ[ℤ] ChevalleyLieAlgebra c :=
  (equivProd c).symm.toLinearMap ∘ₗ LinearMap.inl ℤ Y (ι →₀ ℤ)

/-- The Chevalley root vector `eᵢ` attached to a root index `i : ι`. -/
noncomputable def root (i : ι) : ChevalleyLieAlgebra c :=
  (equivProd c).symm (0, Finsupp.single i 1)

@[simp] theorem equivProd_cartan (y : Y) : equivProd c (cartan c y) = (y, 0) := by simp [cartan]

@[simp]
theorem equivProd_root (i : ι) : equivProd c (root c i) = (0, Finsupp.single i 1) := by simp [root]

theorem cartan_injective : Function.Injective (cartan c) := fun _ _ h ↦ by
  simpa using congrArg (fun u ↦ (equivProd c u).1) h

theorem root_ne_zero (i : ι) : root c i ≠ 0 := fun h ↦ by
  simpa using congrArg (fun u ↦ (equivProd c u).2 i) h

variable {c} in
/-- Two `ℤ`-linear maps out of `ChevalleyLieAlgebra c` agree once they agree on all Cartan vectors
and on all root vectors. -/
theorem linearMap_ext {N : Type*} [AddCommGroup N] {f g : ChevalleyLieAlgebra c →ₗ[ℤ] N}
    (hc : ∀ y, f (cartan c y) = g (cartan c y)) (hr : ∀ i, f (root c i) = g (root c i)) :
    f = g := by
  have key : f ∘ₗ (equivProd c).symm.toLinearMap = g ∘ₗ (equivProd c).symm.toLinearMap :=
    LinearMap.prod_ext (LinearMap.ext hc) (Finsupp.lhom_ext' fun i ↦ LinearMap.ext_ring (hr i))
  simpa using congr($key ∘ₗ (equivProd c).toLinearMap)

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

/-- The action `y ↦ (eᵢ ↦ ⟨αᵢ, y⟩ eᵢ)` of `Y` on the root part. -/
private noncomputable def cartanAction : Y →ₗ[ℤ] (ι →₀ ℤ) →ₗ[ℤ] ChevalleyLieAlgebra c :=
  (Finsupp.linearCombination ℤ fun i ↦ (P.toLinearMap (P.root i)).smulRight (root c i)).flip

/-- Bilinear extension of `rootBracket` to `ι →₀ ℤ`. -/
private noncomputable def rootPart : (ι →₀ ℤ) →ₗ[ℤ] (ι →₀ ℤ) →ₗ[ℤ] ChevalleyLieAlgebra c :=
  Finsupp.linearCombination ℤ fun i ↦ Finsupp.linearCombination ℤ fun j ↦ rootBracket c i j

/-- The `ℤ`-bilinear bracket on `ChevalleyLieAlgebra c`, determined by `⁅H_y, H_z⁆ = 0`,
`⁅H_y, eⱼ⁆ = ⟨αⱼ, y⟩ eⱼ`, `⁅eᵢ, H_z⁆ = -⟨αᵢ, z⟩ eᵢ`, and `⁅eᵢ, eⱼ⁆ = rootBracket c i j`. -/
noncomputable def bracketBilin :
    ChevalleyLieAlgebra c →ₗ[ℤ] ChevalleyLieAlgebra c →ₗ[ℤ] ChevalleyLieAlgebra c :=
  let fst := LinearMap.fst ℤ Y (ι →₀ ℤ) ∘ₗ (equivProd c).toLinearMap
  let snd := LinearMap.snd ℤ Y (ι →₀ ℤ) ∘ₗ (equivProd c).toLinearMap
  (cartanAction c).compl₁₂ fst snd - ((cartanAction c).compl₁₂ fst snd).flip +
    (rootPart c).compl₁₂ snd snd

noncomputable instance : Bracket (ChevalleyLieAlgebra c) (ChevalleyLieAlgebra c) :=
  ⟨fun x y ↦ bracketBilin c x y⟩

@[simp]
theorem bracketBilin_apply_apply (x y : ChevalleyLieAlgebra c) : bracketBilin c x y = ⁅x, y⁆ := rfl

protected theorem add_lie (x y z : ChevalleyLieAlgebra c) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  rw [← bracketBilin_apply_apply, map_add, LinearMap.add_apply]; rfl

protected theorem lie_add (x y z : ChevalleyLieAlgebra c) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ :=
  (bracketBilin c x).map_add y z

private theorem lie_zero' (x : ChevalleyLieAlgebra c) : ⁅x, (0 : ChevalleyLieAlgebra c)⁆ = 0 :=
  (bracketBilin c x).map_zero

private theorem lie_neg' (x y : ChevalleyLieAlgebra c) : ⁅x, -y⁆ = -⁅x, y⁆ :=
  (bracketBilin c x).map_neg y

protected theorem lie_zsmul (r : ℤ) (x y : ChevalleyLieAlgebra c) : ⁅x, r • y⁆ = r • ⁅x, y⁆ :=
  (bracketBilin c x).map_smul r y

@[simp]
theorem cartan_lie_cartan (y z : Y) : ⁅cartan c y, cartan c z⁆ = 0 := by
  simp [← bracketBilin_apply_apply, bracketBilin, cartanAction, rootPart]

@[simp]
theorem cartan_lie_root (y : Y) (i : ι) :
    ⁅cartan c y, root c i⁆ = P.toLinearMap (P.root i) y • root c i := by
  simp [← bracketBilin_apply_apply, bracketBilin, cartanAction, rootPart]

@[simp]
theorem root_lie_cartan (i : ι) (y : Y) :
    ⁅root c i, cartan c y⁆ = -(P.toLinearMap (P.root i) y • root c i) := by
  simp [← bracketBilin_apply_apply, bracketBilin, cartanAction, rootPart]

@[simp]
theorem root_lie_root (i j : ι) : ⁅root c i, root c j⁆ = rootBracket c i j := by
  simp [← bracketBilin_apply_apply, bracketBilin, cartanAction, rootPart]

protected theorem lie_skew (x y : ChevalleyLieAlgebra c) : ⁅y, x⁆ = -⁅x, y⁆ := by
  have key : (bracketBilin c).flip = -bracketBilin c := by
    refine linearMap_ext (fun _ ↦ linearMap_ext (by simp) (by simp))
      fun i ↦ linearMap_ext (by simp) fun j ↦ ?_
    simp [rootBracket_swap c i j]
  simpa using congr($key x y)

protected theorem lie_self (x : ChevalleyLieAlgebra c) : ⁅x, x⁆ = 0 := by
  let q : ChevalleyLieAlgebra c →+ ChevalleyLieAlgebra c :=
    { toFun u := ⁅u, u⁆
      map_zero' := (bracketBilin c 0).map_zero
      map_add' u v := by
        rw [ChevalleyLieAlgebra.add_lie, ChevalleyLieAlgebra.lie_add,
          ChevalleyLieAlgebra.lie_add, ChevalleyLieAlgebra.lie_skew c u v]; abel }
  exact congr($(linearMap_ext (f := q.toIntLinearMap) (g := 0) (by simp [q]) (by simp [q])) x)

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
      rw [rootBracket_of_root_eq_add c hm, ChevalleyLieAlgebra.lie_zsmul, map_smul, Prod.smul_fst,
        root_lie_root, equivProd_rootBracket_fst]
      have hiff : P.root i + P.root m = 0 ↔ P.root i + P.root j + P.root k = 0 := by
        rw [hm, add_assoc]
      by_cases him : P.root i + P.root m = 0 <;> simp [him, hiff.symm]
    · have hsum : P.root i + P.root j + P.root k ≠ 0 := fun h0 ↦ hex
        ⟨P.reflectionPerm i i, by
          rw [P.root_reflectionPerm, P.reflection_apply_self]
          calc -P.root i = P.root i + P.root j + P.root k - P.root i := by rw [h0, zero_sub]
            _ = P.root j + P.root k := by abel⟩
      simp [rootBracket_of_notMem_of_add_ne_zero c (fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩) hjk0, lie_zero',
        hsum]

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
        ChevalleyLieAlgebra.lie_zsmul, map_smul, Prod.smul_snd, Finsupp.coe_smul, Pi.smul_apply,
        root_lie_root, equivProd_rootBracket_snd_apply, smul_eq_mul]
      by_cases hlm : P.root l = P.root i + P.root m <;> simp [hlm, mul_comm]
    · have hnot : P.root j + P.root k ∉ range P.root := fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩
      simp [rootBracket_of_notMem_of_add_ne_zero c hnot hjk0,
        P.tripleRootCoeff_of_notMem_of_add_ne_zero c.structConst hnot hjk0, lie_zero']

private theorem jacobi_cartan_cartan_root (y z : Y) (k : ι) :
    ⁅cartan c y, ⁅cartan c z, root c k⁆⁆ + ⁅cartan c z, ⁅root c k, cartan c y⁆⁆ +
      ⁅root c k, ⁅cartan c y, cartan c z⁆⁆ = 0 := by
  simp only [cartan_lie_root, root_lie_cartan, cartan_lie_cartan, ChevalleyLieAlgebra.lie_zsmul,
    lie_neg', lie_zero', smul_smul, mul_comm (P.toLinearMap (P.root k) y)]
  abel

private theorem jacobi_cartan_root_root (y : Y) (i j : ι) :
    ⁅cartan c y, ⁅root c i, root c j⁆⁆ + ⁅root c i, ⁅root c j, cartan c y⁆⁆ +
      ⁅root c j, ⁅cartan c y, root c i⁆⁆ = 0 := by
  rw [root_lie_root, root_lie_cartan, cartan_lie_root, lie_neg', ChevalleyLieAlgebra.lie_zsmul,
    ChevalleyLieAlgebra.lie_zsmul, root_lie_root, root_lie_root, rootBracket_swap c i j, smul_neg]
  by_cases h0 : P.root i + P.root j = 0
  · rw [rootBracket_of_add_eq_zero c h0, cartan_lie_cartan, zero_add]
    have hsum : P.toLinearMap (P.root i) y + P.toLinearMap (P.root j) y = 0 := by
      rw [← LinearMap.add_apply, ← map_add, h0, map_zero, LinearMap.zero_apply]
    rw [← neg_add_rev, ← add_smul, hsum, zero_smul, neg_zero]
  · by_cases hex : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hex
      rw [rootBracket_of_root_eq_add c hk, ChevalleyLieAlgebra.lie_zsmul, cartan_lie_root,
        smul_smul, smul_smul, smul_smul, hk, map_add, LinearMap.add_apply, mul_add, add_smul,
        mul_comm (P.toLinearMap (P.root j) y), mul_comm (P.toLinearMap (P.root i) y)]
      abel
    · simp [rootBracket_of_notMem_of_add_ne_zero c (fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩) h0, lie_zero']

private theorem jacobi_root_root_root (i j k : ι) :
    ⁅root c i, ⁅root c j, root c k⁆⁆ + ⁅root c j, ⁅root c k, root c i⁆⁆ +
      ⁅root c k, ⁅root c i, root c j⁆⁆ = 0 := by
  classical
  apply (equivProd c).injective
  rw [map_add, map_add, map_zero, root_lie_root, root_lie_root, root_lie_root]
  ext1
  · simp only [Prod.fst_add, Prod.fst_zero, equivProd_root_lie_rootBracket_fst]
    by_cases h0 : P.root i + P.root j + P.root k = 0
    · rw [ite_eq_left h0, ite_eq_left (by rw [← h0]; abel), ite_eq_left (by rw [← h0]; abel)]
      exact c.coroot_jacobi h0
    · rw [ite_eq_right h0, ite_eq_right (fun h ↦ h0 (by rw [← h]; abel)),
        ite_eq_right (fun h ↦ h0 (by rw [← h]; abel)), add_zero, add_zero]
  · ext l
    simpa [equivProd_root_lie_rootBracket_snd_apply] using c.root_jacobi i j k l

private theorem jacobi_gen_gen (u v : Y ⊕ ι) (z : ChevalleyLieAlgebra c) :
    let gen : Y ⊕ ι → ChevalleyLieAlgebra c := Sum.elim (cartan c) (root c)
    ⁅gen u, ⁅gen v, z⁆⁆ + ⁅gen v, ⁅z, gen u⁆⁆ + ⁅z, ⁅gen u, gen v⁆⁆ = 0 := by
  intro gen
  have key : bracketBilin c (gen u) ∘ₗ bracketBilin c (gen v) +
      bracketBilin c (gen v) ∘ₗ (bracketBilin c).flip (gen u) +
      (bracketBilin c).flip (bracketBilin c (gen u) (gen v)) = 0 := by
    refine linearMap_ext (fun y ↦ ?_) fun k ↦ ?_ <;>
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.flip_apply,
        bracketBilin_apply_apply, LinearMap.zero_apply] <;>
      rcases u with y₁ | i <;> rcases v with y₂ | j <;> simp only [gen, Sum.elim_inl, Sum.elim_inr]
    · simp [lie_zero']
    · rw [← add_rotate]; exact jacobi_cartan_cartan_root c y y₁ j
    · rw [add_rotate]; exact jacobi_cartan_cartan_root c y₂ y i
    · rw [← add_rotate]; exact jacobi_cartan_root_root c y i j
    · exact jacobi_cartan_cartan_root c y₁ y₂ k
    · exact jacobi_cartan_root_root c y₁ j k
    · rw [add_rotate]; exact jacobi_cartan_root_root c y₂ k i
    · exact jacobi_root_root_root c i j k
  simpa using congr($key z)

protected theorem lie_jacobi (x y z : ChevalleyLieAlgebra c) :
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  have h₂ (u : Y ⊕ ι) (y z : ChevalleyLieAlgebra c) :
      ⁅Sum.elim (cartan c) (root c) u, ⁅y, z⁆⁆ + ⁅y, ⁅z, Sum.elim (cartan c) (root c) u⁆⁆ +
        ⁅z, ⁅Sum.elim (cartan c) (root c) u, y⁆⁆ = 0 := by
    have key : bracketBilin c (Sum.elim (cartan c) (root c) u) ∘ₗ (bracketBilin c).flip z +
        (bracketBilin c).flip (bracketBilin c z (Sum.elim (cartan c) (root c) u)) +
        bracketBilin c z ∘ₗ bracketBilin c (Sum.elim (cartan c) (root c) u) = 0 :=
      linearMap_ext (fun y ↦ by simpa using jacobi_gen_gen c u (.inl y) z)
        fun j ↦ by simpa using jacobi_gen_gen c u (.inr j) z
    simpa [add_rotate] using congr($key y)
  have key : (bracketBilin c).flip ⁅y, z⁆ + bracketBilin c y ∘ₗ bracketBilin c z +
      bracketBilin c z ∘ₗ (bracketBilin c).flip y = 0 :=
    linearMap_ext (fun y' ↦ by simpa using h₂ (.inl y') y z)
      fun i ↦ by simpa using h₂ (.inr i) y z
  simpa using congr($key x)

noncomputable instance instLieRing : LieRing (ChevalleyLieAlgebra c) where
  add_lie := ChevalleyLieAlgebra.add_lie c
  lie_add := ChevalleyLieAlgebra.lie_add c
  lie_self := ChevalleyLieAlgebra.lie_self c
  leibniz_lie x y z := by
    have h := ChevalleyLieAlgebra.lie_jacobi c x y z
    rw [ChevalleyLieAlgebra.lie_skew c x z, lie_neg', ChevalleyLieAlgebra.lie_skew c ⁅x, y⁆ z] at h
    calc ⁅x, ⁅y, z⁆⁆ = ⁅x, ⁅y, z⁆⁆ - (⁅x, ⁅y, z⁆⁆ + -⁅y, ⁅x, z⁆⁆ + -⁅⁅x, y⁆, z⁆) := by
          rw [h, sub_zero]
      _ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by abel

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
    exact ⟨by simp, (forall_lie_cartan_eq_zero_iff c y).mp hx⟩
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
theorem cartanEquivOfIsEmpty_apply [IsEmpty ι] (y : Y) : cartanEquivOfIsEmpty c y = cartan c y := by
  rfl

@[simp]
theorem cartanEquivOfIsEmpty_symm_apply [IsEmpty ι] (x : ChevalleyLieAlgebra c) :
    (cartanEquivOfIsEmpty c).symm x = (equivProd c x).1 := by rfl

/-! ### Integral Chevalley basis and scalar extension -/

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

/-- Scalar extension of the integral Chevalley basis to `R ⊗[ℤ] ChevalleyLieAlgebra c` over any
commutative ring `R`. -/
noncomputable abbrev baseChangeBasis (R : Type*) [CommRing R] :
    Basis (J ⊕ ι) R (R ⊗[ℤ] ChevalleyLieAlgebra c) :=
  (basis c bY).baseChange R

theorem baseChangeBasis_inl (R : Type*) [CommRing R] (j : J) :
    baseChangeBasis c bY R (.inl j) = 1 ⊗ₜ[ℤ] cartan c (bY j) := by simp [baseChangeBasis]

theorem baseChangeBasis_inr (R : Type*) [CommRing R] (i : ι) :
    baseChangeBasis c bY R (.inr i) = 1 ⊗ₜ[ℤ] root c i := by simp [baseChangeBasis]

end Basis

end ChevalleyLieAlgebra

end LieAlgebra

end RootPairing
