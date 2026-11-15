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

import Mathlib.Tactic.IntervalCases
import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# The integral Chevalley Lie algebra over a full cocharacter lattice

For a finite integral root datum `P : RootPairing ι ℤ X Y`, this file defines extensional integer
Chevalley structure-constant tables `P.ChevalleyConstants`, proves `ChevalleyConstants.isReduced`,
and constructs the `ℤ`-Lie algebra `RootPairing.ChevalleyLieAlgebra c` on `TauCeti.FullCartan Y ι`
(sharing the full-Cartan carrier and generator-reduction axioms with `Matrix.FullShellLieAlgebra`
without assuming coroots span or split off in `Y`), together with its center (`mem_center_iff`,
`center_eq_map_iInf_ker`), root-free case (`cartanEquivOfIsEmpty`), and `ℤ`-basis (`basis`).

## References

* C. Chevalley, *Sur certains groupes simples*, Tohoku Math. J. (2) **7** (1955), 14--66.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016), §§1--2.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, Chapter 1.
-/

public section

open Module Set
open TauCeti (FullCartan)

namespace RootPairing

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

open Classical in
/-- The `l`-th root coordinate of `⁅eᵢ, ⁅eⱼ, eₖ⁆⁆` for a candidate integer structure-constant
table `N` on `P`: `-⟨αᵢ, αⱼ∨⟩` at `l = i` when `αⱼ + αₖ = 0`, `Nᵢₘ * Nⱼₖ` when `αₘ = αⱼ + αₖ` and
`αₗ = αᵢ + αₘ`, and `0` otherwise. -/
noncomputable def tripleRootCoeff (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ) (i j k l : ι) : ℤ :=
  (if P.root j + P.root k = 0 ∧ l = i then -P.pairing i j else 0) +
    P.rootSumElim j k fun m _ ↦ if P.root l = P.root i + P.root m then N i m * N j k else 0

open Classical in
/-- For `αⱼ + αₖ = 0`, `P.tripleRootCoeff N i j k l` is `-P.pairing i j` at `l = i` and `0` else. -/
theorem tripleRootCoeff_of_add_eq_zero (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hjk : P.root j + P.root k = 0) :
    P.tripleRootCoeff N i j k l = if l = i then -P.pairing i j else 0 := by
  rw [tripleRootCoeff, P.rootSumElim_of_add_eq_zero hjk, add_zero]
  by_cases hli : l = i <;> simp [hjk, hli]

open Classical in
/-- When `αₘ = αⱼ + αₖ`, `P.tripleRootCoeff N i j k l` is `N i m * N j k` at `αₗ = αᵢ + αₘ`. -/
theorem tripleRootCoeff_of_root_eq_add (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k m l : ι} (hm : P.root m = P.root j + P.root k) :
    P.tripleRootCoeff N i j k l = if P.root l = P.root i + P.root m then N i m * N j k else 0 := by
  rw [tripleRootCoeff, ite_eq_right (fun h ↦ P.ne_zero m (hm.trans h.1)), zero_add,
    P.rootSumElim_of_root_eq_add hm]

/-- When `αⱼ + αₖ` is neither a root nor zero, `P.tripleRootCoeff N i j k l` vanishes. -/
theorem tripleRootCoeff_of_notMem_of_add_ne_zero (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hnot : P.root j + P.root k ∉ range P.root) (hne : P.root j + P.root k ≠ 0) :
    P.tripleRootCoeff N i j k l = 0 := by
  classical
  rw [tripleRootCoeff, ite_eq_right (fun h ↦ hne h.1), P.rootSumElim_of_notMem_range hnot, add_zero]

/-- `P.tripleRootCoeff N i j k l` vanishes whenever `P.root l ≠ P.root i + P.root j + P.root k`. -/
theorem tripleRootCoeff_eq_zero_of_ne_sum (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hl : P.root l ≠ P.root i + P.root j + P.root k) :
    P.tripleRootCoeff N i j k l = 0 := by
  classical
  by_cases hjk0 : P.root j + P.root k = 0
  · rw [P.tripleRootCoeff_of_add_eq_zero _ hjk0,
      ite_eq_right (by rintro rfl; exact hl (by rw [add_assoc, hjk0, add_zero]))]
  · by_cases hmem : P.root j + P.root k ∈ range P.root
    · obtain ⟨m, hm⟩ := hmem
      rw [P.tripleRootCoeff_of_root_eq_add _ hm,
        ite_eq_right (fun h ↦ hl (by rw [h, hm, add_assoc]))]
    · exact P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hmem hjk0

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
  ext i j; by_cases hij : P.root i + P.root j ∈ range P.root
  · exact h i j hij
  · rw [c₁.structConst_eq_zero_of_notMem_range i j hij,
      c₂.structConst_eq_zero_of_notMem_range i j hij]

@[simp] theorem structConst_self (i : ι) : c.structConst i i = 0 := by
  have := c.structConst_swap i i; omega

theorem structConst_eq_zero_of_add_eq_zero {i j : ι} (h : P.root i + P.root j = 0) :
    c.structConst i j = 0 :=
  c.structConst_eq_zero_of_notMem_range i j fun ⟨k, hk⟩ ↦ P.ne_zero k (hk.trans h)

theorem structConst_ne_zero {i j k : ι} (h : P.root k = P.root i + P.root j) :
    c.structConst i j ≠ 0 := by have := c.natAbs_structConst h; omega

theorem structConst_eq_natCast_or_eq_neg_natCast {i j k : ι} (h : P.root k = P.root i + P.root j) :
    c.structConst i j = (P.chainBotCoeff i j + 1 : ℕ) ∨
      c.structConst i j = -((P.chainBotCoeff i j + 1 : ℕ) : ℤ) :=
  c.natAbs_structConst h ▸ Int.natAbs_eq (c.structConst i j)

include c in
/-- A finite integral root pairing admitting Chevalley structure constants is reduced. -/
theorem isReduced : P.IsReduced := by
  -- Skew-symmetry forces `N_{i,i} = 0`, whereas `2 αᵢ ∈ Φ` would require `|N_{i,i}| = p + 1 ≥ 1`.
  have : Module.IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive ℤ Y := .of_isPerfPair P.toLinearMap.flip
  have hno2 (a b : ι) (h : P.root b = (2 : ℤ) • P.root a) : False := by
    have hnat := c.natAbs_structConst (two_smul ℤ (P.root a) ▸ h)
    rw [c.structConst_self] at hnat; omega
  rw [P.isReduced_iff']; intro i j hij hdep
  have hcox : P.pairing i j * P.pairing j i = 4 :=
    P.coxeterWeight_eq_four_iff_not_linearIndependent.mpr hdep
  have hle : (P.pairing i j).natAbs ≤ 4 :=
    Nat.le_of_dvd (by decide) ⟨(P.pairing j i).natAbs, by rw [← Int.natAbs_mul, hcox]; rfl⟩
  have hbnd : -4 ≤ P.pairing i j ∧ P.pairing i j ≤ 4 := ⟨by omega, by omega⟩
  have hcases : (P.pairing i j = 2 ∧ P.pairing j i = 2) ∨
      (P.pairing i j = -2 ∧ P.pairing j i = -2) ∨
      (P.pairing i j = 1 ∧ P.pairing j i = 4) ∨ (P.pairing j i = 1 ∧ P.pairing i j = 4) ∨
      (P.pairing i j = -1 ∧ P.pairing j i = -4) ∨ (P.pairing j i = -1 ∧ P.pairing i j = -4) := by
    obtain ⟨_, _⟩ := hbnd; interval_cases P.pairing i j <;> omega
  rcases hcases with h | h | h | h | h | h
  · exact absurd ((P.pairing_two_two_iff i j).mp h) hij
  · exact (P.pairing_neg_two_neg_two_iff i j).mp h
  · exact (hno2 i j ((P.pairing_one_four_iff i j).mp h)).elim
  · exact (hno2 j i ((P.pairing_one_four_iff j i).mp h)).elim
  · exact (hno2 i (P.reflectionPerm j j) (by
      simpa [neg_smul] using congrArg Neg.neg ((P.pairing_neg_one_neg_four_iff i j).mp h))).elim
  · exact (hno2 j (P.reflectionPerm i i) (by
      simpa [neg_smul] using congrArg Neg.neg ((P.pairing_neg_one_neg_four_iff j i).mp h))).elim

/-- The unique Chevalley structure-constant table on a root-free datum `[IsEmpty ι]`. -/
def ofIsEmpty (P : RootPairing ι ℤ X Y) [IsEmpty ι] : P.ChevalleyConstants :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim, fun {i} ↦ isEmptyElim i, isEmptyElim,
    fun {i} ↦ isEmptyElim i, isEmptyElim⟩

instance [IsEmpty ι] : Unique P.ChevalleyConstants :=
  ⟨⟨ofIsEmpty P⟩, fun _ ↦ by ext i; exact isEmptyElim i⟩

end ChevalleyConstants

/-! ## The full reductive integral Chevalley Lie algebra -/

/-- **The integral Chevalley Lie algebra** of a root datum `P` over its full cocharacter group `Y`,
realized on `TauCeti.FullCartan Y ι` (`Y × (ι →₀ ℤ)`). -/
def ChevalleyLieAlgebra {P : RootPairing ι ℤ X Y} (_c : P.ChevalleyConstants) : Type _ :=
  TauCeti.FullCartan Y ι

namespace ChevalleyLieAlgebra

variable {P : RootPairing ι ℤ X Y} (c : P.ChevalleyConstants)

noncomputable instance : AddCommGroup (ChevalleyLieAlgebra c) :=
  inferInstanceAs (AddCommGroup (TauCeti.FullCartan Y ι))

/-- Identification of `ChevalleyLieAlgebra c` with its underlying product `Y × (ι →₀ ℤ)`. -/
noncomputable def equivProd : ChevalleyLieAlgebra c ≃ₗ[ℤ] Y × (ι →₀ ℤ) := FullCartan.equivProd Y ι

/-- The Cartan vector `H_y` attached to a cocharacter `y : Y`, as a `ℤ`-linear embedding. -/
noncomputable def cartan : Y →ₗ[ℤ] ChevalleyLieAlgebra c := FullCartan.cartan Y ι

/-- The Chevalley root vector `eᵢ` attached to a root index `i : ι`. -/
noncomputable def root (i : ι) : ChevalleyLieAlgebra c := FullCartan.root Y ι i

@[simp] theorem equivProd_cartan (y : Y) : equivProd c (cartan c y) = (y, 0) :=
  FullCartan.equivProd_cartan y

@[simp] theorem equivProd_root (i : ι) : equivProd c (root c i) = (0, Finsupp.single i 1) :=
  FullCartan.equivProd_root i

theorem cartan_injective : Function.Injective (cartan c) := FullCartan.cartan_injective

theorem root_ne_zero (i : ι) : root c i ≠ 0 := FullCartan.root_ne_zero i

variable {c} in
/-- Two `ℤ`-linear maps out of `ChevalleyLieAlgebra c` agree once they agree on all Cartan and root
vectors. -/
theorem linearMap_ext {N : Type*} [AddCommGroup N] {f g : ChevalleyLieAlgebra c →ₗ[ℤ] N}
    (hc : ∀ y, f (cartan c y) = g (cartan c y)) (hr : ∀ i, f (root c i) = g (root c i)) : f = g :=
  FullCartan.linearMap_ext hc hr

open Classical in
/-- The bracket `⁅eᵢ, eⱼ⁆` of two root vectors: `H_{αᵢ∨}` when `αᵢ + αⱼ = 0`, `Nᵢⱼ eₖ` when
`αₖ = αᵢ + αⱼ`, and `0` otherwise. -/
noncomputable def rootBracket (i j : ι) : ChevalleyLieAlgebra c :=
  if P.root i + P.root j = 0 then cartan c (P.coroot i)
  else P.rootSumElim i j fun k _ ↦ c.structConst i j • root c k

theorem rootBracket_of_add_eq_zero {i j : ι} (h : P.root i + P.root j = 0) :
    rootBracket c i j = cartan c (P.coroot i) := by classical rw [rootBracket, ite_eq_left h]

@[simp] theorem rootBracket_reflectionPerm_right (i : ι) :
    rootBracket c i (P.reflectionPerm i i) = cartan c (P.coroot i) :=
  rootBracket_of_add_eq_zero c (by simp)

theorem rootBracket_of_root_eq_add {i j k : ι} (h : P.root k = P.root i + P.root j) :
    rootBracket c i j = c.structConst i j • root c k := by
  classical
  rw [rootBracket, ite_eq_right (fun h0 ↦ P.ne_zero k (h.trans h0)), P.rootSumElim_of_root_eq_add h]

theorem rootBracket_of_notMem_of_add_ne_zero {i j : ι} (hnot : P.root i + P.root j ∉ range P.root)
    (hne : P.root i + P.root j ≠ 0) : rootBracket c i j = 0 := by
  classical rw [rootBracket, ite_eq_right hne, P.rootSumElim_of_notMem_range hnot]

open Classical in
@[simp] theorem equivProd_rootBracket_fst (i j : ι) :
    (equivProd c (rootBracket c i j)).1 = if P.root i + P.root j = 0 then P.coroot i else 0 := by
  by_cases h0 : P.root i + P.root j = 0
  · simp [rootBracket_of_add_eq_zero c h0, h0]
  · by_cases hmem : P.root i + P.root j ∈ range P.root
    · obtain ⟨k, hk⟩ := hmem; simp [rootBracket_of_root_eq_add c hk, h0]
    · simp [rootBracket_of_notMem_of_add_ne_zero c hmem h0, h0]

open Classical in
@[simp] theorem equivProd_rootBracket_snd_apply (i j l : ι) :
    (equivProd c (rootBracket c i j)).2 l =
      if P.root l = P.root i + P.root j then c.structConst i j else 0 := by
  by_cases h0 : P.root i + P.root j = 0
  · rw [rootBracket_of_add_eq_zero c h0, ite_eq_right (fun hl ↦ P.ne_zero l (hl.trans h0))]; simp
  · by_cases hmem : P.root i + P.root j ∈ range P.root
    · obtain ⟨k, hk⟩ := hmem; rw [rootBracket_of_root_eq_add c hk]
      by_cases hlk : l = k
      · subst hlk; simp [hk]
      · rw [ite_eq_right (fun hl ↦ hlk (P.root.injective (hl.trans hk.symm)))]; simp [hlk]
    · rw [rootBracket_of_notMem_of_add_ne_zero c hmem h0,
        ite_eq_right (fun hl ↦ hmem ⟨l, hl⟩)]; simp

@[simp] theorem rootBracket_self (i : ι) : rootBracket c i i = 0 := by
  classical
  have hself : P.root i + P.root i ≠ 0 := by
    rw [ne_eq, add_eq_zero_iff_eq_neg, P.root_eq_neg_iff]; exact P.ne_neg i
  exact (equivProd c).injective (Prod.ext (by simp [hself]) (by ext l; simp))

theorem rootBracket_swap (i j : ι) : rootBracket c j i = -rootBracket c i j := by
  classical
  apply (equivProd c).injective; rw [map_neg]; ext1
  · simp only [equivProd_rootBracket_fst, Prod.fst_neg, add_comm (P.root j)]
    split_ifs with h0
    · exact P.coroot_eq_neg_iff.mpr
        (P.root_eq_neg_iff.mp (add_eq_zero_iff_eq_neg.mp (add_comm (P.root i) _ ▸ h0)))
    · exact neg_zero.symm
  · ext l
    simp only [equivProd_rootBracket_snd_apply, Prod.snd_neg, Finsupp.coe_neg, Pi.neg_apply,
      add_comm (P.root j), c.structConst_swap i j]
    split_ifs <;> simp

/-- The `ℤ`-bilinear bracket on `ChevalleyLieAlgebra c`, determined by `⁅H_y, H_z⁆ = 0`,
`⁅H_y, eⱼ⁆ = ⟨αⱼ, y⟩ eⱼ`, `⁅eᵢ, H_z⁆ = -⟨αᵢ, z⟩ eᵢ`, and `⁅eᵢ, eⱼ⁆ = rootBracket c i j`. -/
noncomputable def bracketBilin :
    ChevalleyLieAlgebra c →ₗ[ℤ] ChevalleyLieAlgebra c →ₗ[ℤ] ChevalleyLieAlgebra c :=
  FullCartan.bracketBilin (fun i ↦ P.toLinearMap (P.root i)) (rootBracket c)

noncomputable instance : Bracket (ChevalleyLieAlgebra c) (ChevalleyLieAlgebra c) :=
  ⟨fun x y ↦ bracketBilin c x y⟩

@[simp] theorem bracketBilin_apply_apply (x y : ChevalleyLieAlgebra c) :
    bracketBilin c x y = ⁅x, y⁆ := (rfl)

private theorem bracket_zsmul (r : ℤ) (x y : ChevalleyLieAlgebra c) : ⁅x, r • y⁆ = r • ⁅x, y⁆ :=
  (bracketBilin c x).map_smul r y

private theorem bracket_zero (x : ChevalleyLieAlgebra c) : ⁅x, (0 : ChevalleyLieAlgebra c)⁆ = 0 :=
  (bracketBilin c x).map_zero

@[simp] theorem cartan_lie_cartan (y z : Y) : ⁅cartan c y, cartan c z⁆ = 0 :=
  FullCartan.bracketBilin_cartan_cartan _ _ y z

@[simp] theorem cartan_lie_root (y : Y) (i : ι) :
    ⁅cartan c y, root c i⁆ = P.toLinearMap (P.root i) y • root c i :=
  FullCartan.bracketBilin_cartan_root _ _ y i

@[simp] theorem root_lie_cartan (i : ι) (y : Y) :
    ⁅root c i, cartan c y⁆ = -(P.toLinearMap (P.root i) y • root c i) :=
  FullCartan.bracketBilin_root_cartan _ _ i y

@[simp] theorem root_lie_root (i j : ι) : ⁅root c i, root c j⁆ = rootBracket c i j :=
  FullCartan.bracketBilin_root_root _ _ i j

private theorem cartan_lie_rootBracket (y : Y) (i j : ι) :
    ⁅cartan c y, rootBracket c i j⁆ =
      (P.toLinearMap (P.root i) y + P.toLinearMap (P.root j) y) • rootBracket c i j := by
  by_cases h0 : P.root i + P.root j = 0
  · simp [rootBracket_of_add_eq_zero c h0, ← LinearMap.add_apply, ← map_add, h0]
  · by_cases hmem : P.root i + P.root j ∈ range P.root
    · obtain ⟨k, hk⟩ := hmem
      simpa [rootBracket_of_root_eq_add c hk, bracket_zsmul, hk] using smul_comm ..
    · simp [rootBracket_of_notMem_of_add_ne_zero c hmem h0, bracket_zero]

open Classical in
private theorem equivProd_root_lie_rootBracket_fst (i j k : ι) :
    (equivProd c ⁅root c i, rootBracket c j k⁆).1 =
      if P.root i + P.root j + P.root k = 0 then c.structConst j k • P.coroot i else 0 := by
  by_cases hjk0 : P.root j + P.root k = 0
  · simp [rootBracket_of_add_eq_zero c hjk0,
      show P.root i + P.root j + P.root k ≠ 0 by simpa [add_assoc, hjk0] using P.ne_zero i]
  · by_cases hmem : P.root j + P.root k ∈ range P.root
    · obtain ⟨m, hm⟩ := hmem
      simp [rootBracket_of_root_eq_add c hm, bracket_zsmul, add_assoc, ← hm]
    · have hsum : P.root i + P.root j + P.root k ≠ 0 := fun h0 ↦
        hmem ⟨P.reflectionPerm i i, P.root_reflectionPerm_self_eq_add_of_add_add_eq_zero h0⟩
      simp [rootBracket_of_notMem_of_add_ne_zero c hmem hjk0, bracket_zero, hsum]

private theorem equivProd_root_lie_rootBracket_snd_apply (i j k l : ι) :
    (equivProd c ⁅root c i, rootBracket c j k⁆).2 l = P.tripleRootCoeff c.structConst i j k l := by
  classical
  by_cases hjk0 : P.root j + P.root k = 0
  · rw [rootBracket_of_add_eq_zero c hjk0, root_lie_cartan,
      P.tripleRootCoeff_of_add_eq_zero c.structConst hjk0]
    by_cases hli : l = i <;> simp [hli, P.root_coroot_eq_pairing]
  · by_cases hmem : P.root j + P.root k ∈ range P.root
    · obtain ⟨m, hm⟩ := hmem
      simp [rootBracket_of_root_eq_add c hm, P.tripleRootCoeff_of_root_eq_add c.structConst hm,
        bracket_zsmul, mul_comm (c.structConst j k) (c.structConst i m)]
    · simp [rootBracket_of_notMem_of_add_ne_zero c hmem hjk0,
        P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hmem hjk0, bracket_zero]

private theorem jacobi_root_root_root (i j k : ι) :
    ⁅root c i, rootBracket c j k⁆ + ⁅root c j, rootBracket c k i⁆ +
      ⁅root c k, rootBracket c i j⁆ = 0 := by
  classical
  apply (equivProd c).injective; rw [map_add, map_add, map_zero]; ext1
  · simp only [Prod.fst_add, Prod.fst_zero, equivProd_root_lie_rootBracket_fst]
    by_cases h0 : P.root i + P.root j + P.root k = 0
    · rw [ite_eq_left h0, ite_eq_left (by rw [← h0]; abel), ite_eq_left (by rw [← h0]; abel)]
      exact c.coroot_jacobi h0
    · rw [ite_eq_right h0, ite_eq_right (fun h ↦ h0 (by rw [← h]; abel)),
        ite_eq_right (fun h ↦ h0 (by rw [← h]; abel)), add_zero, add_zero]
  · ext l; simpa [equivProd_root_lie_rootBracket_snd_apply] using c.root_jacobi i j k l

noncomputable instance instLieRing : LieRing (ChevalleyLieAlgebra c) where
  add_lie x y z := by exact LinearMap.congr_fun ((bracketBilin c).map_add x y) z
  lie_add x y z := by exact (bracketBilin c x).map_add y z
  lie_self x := by exact FullCartan.bracketBilin_self (rootBracket_swap c) (rootBracket_self c) x
  leibniz_lie x y z := by
    exact FullCartan.bracketBilin_leibniz (rootBracket_swap c)
      (cartan_lie_rootBracket c) (jacobi_root_root_root c) x y z

noncomputable instance instLieAlgebra : LieAlgebra ℤ (ChevalleyLieAlgebra c) where
  lie_smul r x y := by exact bracket_zsmul c r x y

theorem root_lie_root_of_add_eq_zero {i j : ι} (h : P.root i + P.root j = 0) :
    ⁅root c i, root c j⁆ = cartan c (P.coroot i) :=
  (root_lie_root c i j).trans (rootBracket_of_add_eq_zero c h)

theorem root_lie_root_reflectionPerm (i : ι) :
    ⁅root c i, root c (P.reflectionPerm i i)⁆ = cartan c (P.coroot i) :=
  (root_lie_root c i _).trans (rootBracket_reflectionPerm_right c i)

theorem root_lie_root_of_root_eq_add {i j k : ι} (h : P.root k = P.root i + P.root j) :
    ⁅root c i, root c j⁆ = c.structConst i j • root c k :=
  (root_lie_root c i j).trans (rootBracket_of_root_eq_add c h)

theorem root_lie_root_of_notMem_of_add_ne_zero {i j : ι}
    (hnot : P.root i + P.root j ∉ range P.root) (hne : P.root i + P.root j ≠ 0) :
    ⁅root c i, root c j⁆ = 0 :=
  (root_lie_root c i j).trans (rootBracket_of_notMem_of_add_ne_zero c hnot hne)

/-! ### Center over the full cocharacter lattice -/

@[simp] theorem equivProd_cartan_lie_snd (y : Y) (x : ChevalleyLieAlgebra c) (i : ι) :
    (equivProd c ⁅cartan c y, x⁆).2 i = P.toLinearMap (P.root i) y * (equivProd c x).2 i := by
  let coord : ChevalleyLieAlgebra c →ₗ[ℤ] ℤ :=
    (Finsupp.lapply i).comp ((LinearMap.snd ℤ Y (ι →₀ ℤ)).comp (equivProd c).toLinearMap)
  have h : coord.comp (bracketBilin c (cartan c y)) = P.toLinearMap (P.root i) y • coord :=
    linearMap_ext (by simp [coord]) fun j ↦ by by_cases hij : i = j <;> simp [coord, hij]
  exact LinearMap.congr_fun h x

/-- The centralizer of `Y` in `ChevalleyLieAlgebra c` is its image under `cartan c`. -/
theorem forall_cartan_lie_eq_zero_iff (x : ChevalleyLieAlgebra c) :
    (∀ y, ⁅cartan c y, x⁆ = 0) ↔ x ∈ LinearMap.range (cartan c) := by
  refine ⟨fun hx ↦ ⟨(equivProd c x).1, (equivProd c).injective (Prod.ext (by simp) ?_)⟩,
    fun ⟨y, hy⟩ z ↦ hy ▸ cartan_lie_cartan c z y⟩
  ext i; have h := equivProd_cartan_lie_snd c (P.coroot i) x i
  rw [hx, map_zero, Prod.snd_zero, Finsupp.zero_apply,
    (P.root_coroot_eq_pairing i i).trans (P.pairing_same i)] at h
  simp only [equivProd_cartan, Finsupp.zero_apply]; omega

@[simp] theorem forall_lie_cartan_eq_zero_iff (y : Y) :
    (∀ x : ChevalleyLieAlgebra c, ⁅x, cartan c y⁆ = 0) ↔
      ∀ i : ι, P.toLinearMap (P.root i) y = 0 :=
  ⟨fun hy i ↦ by simpa using congrArg (fun z ↦ (equivProd c z).2 i) (hy (root c i)),
   fun hw ↦ LinearMap.congr_fun <| linearMap_ext (f := (bracketBilin c).flip (cartan c y)) (g := 0)
     (by simp) fun i ↦ by simp [hw i]⟩

/-- An element of `ChevalleyLieAlgebra c` is central iff its root coordinates vanish and its Cartan
coordinate is annihilated by every root of `P`. -/
theorem mem_center_iff (x : ChevalleyLieAlgebra c) :
    x ∈ _root_.LieAlgebra.center ℤ (ChevalleyLieAlgebra c) ↔
      (equivProd c x).2 = 0 ∧ ∀ i : ι, P.toLinearMap (P.root i) (equivProd c x).1 = 0 := by
  refine ⟨fun hx ↦ ?_, fun ⟨hroot, hweight⟩ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := (forall_cartan_lie_eq_zero_iff c x).mp fun y ↦ hx (cartan c y)
    exact ⟨by simp, by simpa using (forall_lie_cartan_eq_zero_iff c y).mp hx⟩
  · have hx : x = cartan c (equivProd c x).1 :=
      (equivProd c).injective (Prod.ext (by simp) (by simp [hroot]))
    rw [hx]; exact (forall_lie_cartan_eq_zero_iff c _).mpr hweight

/-- The center of `ChevalleyLieAlgebra c`, as a `ℤ`-submodule, is the Cartan image of the common
kernel of all roots on `Y`. -/
theorem center_eq_map_iInf_ker :
    (_root_.LieAlgebra.center ℤ (ChevalleyLieAlgebra c)).toSubmodule =
      Submodule.map (cartan c) (⨅ i : ι, LinearMap.ker (P.toLinearMap (P.root i))) := by
  ext x; refine ⟨fun hx ↦ ?_,
    fun ⟨y, hy, hx⟩ ↦ hx ▸ (forall_lie_cartan_eq_zero_iff c y).mpr (by simpa using hy)⟩
  obtain ⟨y, rfl⟩ := (forall_cartan_lie_eq_zero_iff c x).mp fun y ↦ hx (cartan c y)
  exact ⟨y, by simpa using (forall_lie_cartan_eq_zero_iff c y).mp hx, rfl⟩

/-! ### The root-free datum `Φ = ∅` -/

instance instIsLieAbelianOfIsEmpty [IsEmpty ι] : IsLieAbelian (ChevalleyLieAlgebra c) :=
  ⟨fun x y ↦ congr($(linearMap_ext (f := bracketBilin c) (g := 0)
    (fun _ ↦ linearMap_ext (by simp) isEmptyElim) isEmptyElim) x y)⟩

/-- When `ι` is empty, `cartan c` identifies `Y` with `ChevalleyLieAlgebra c`. -/
noncomputable def cartanEquivOfIsEmpty [IsEmpty ι] : Y ≃ₗ[ℤ] ChevalleyLieAlgebra c :=
  LinearEquiv.ofLinearMap (cartan c) ((LinearMap.fst ℤ Y (ι →₀ ℤ)).comp (equivProd c).toLinearMap)
    (LinearMap.ext fun _ ↦ (equivProd c).injective <|
      Prod.ext (by simp) (by ext i; exact isEmptyElim i)) (LinearMap.ext fun _ ↦ by simp)

@[simp] theorem cartanEquivOfIsEmpty_apply [IsEmpty ι] (y : Y) :
    cartanEquivOfIsEmpty c y = cartan c y := (rfl)

@[simp] theorem cartanEquivOfIsEmpty_symm_apply [IsEmpty ι] (x : ChevalleyLieAlgebra c) :
    (cartanEquivOfIsEmpty c).symm x = (equivProd c x).1 := (rfl)

/-! ### Integral Chevalley basis -/

variable {J : Type*} (bY : Basis J ℤ Y)

/-- **The integral Chevalley basis** of `ChevalleyLieAlgebra c` attached to a `ℤ`-basis `bY` of `Y`,
indexed by `J ⊕ ι`. -/
noncomputable def basis : Basis (J ⊕ ι) ℤ (ChevalleyLieAlgebra c) :=
  (bY.prod (Finsupp.basisSingleOne : Basis ι ℤ (ι →₀ ℤ))).map (equivProd c).symm

@[simp] theorem basis_inl (j : J) : basis c bY (.inl j) = cartan c (bY j) :=
  (equivProd c).injective (by simp [basis])

@[simp] theorem basis_inr (i : ι) : basis c bY (.inr i) = root c i :=
  (equivProd c).injective (by simp [basis])

@[simp] theorem basis_repr_inl (x : ChevalleyLieAlgebra c) (j : J) :
    (basis c bY).repr x (.inl j) = bY.repr (equivProd c x).1 j := by simp [basis]

@[simp] theorem basis_repr_inr (x : ChevalleyLieAlgebra c) (i : ι) :
    (basis c bY).repr x (.inr i) = (equivProd c x).2 i := by simp [basis]

end ChevalleyLieAlgebra

end RootPairing
