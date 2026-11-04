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
datum `P` has Lie algebra decomposed into the Lie algebra of its maximal torus, whose integral form
is the full cocharacter lattice `Y` (retaining any central torus), and one root line `ℤ eᵢ` for
each root index `i : ι`. Unlike the semisimple coroot-span lattice, `Y` need not be spanned by the
coroots and need not split integrally into central and coroot summands.

This file packages the integer structure-constant tables `P.ChevalleyConstants` compatible with the
Chevalley normalization `⁅eᵢ, e_{-i}⁆ = H_{αᵢ∨}` and constructs the resulting integral Lie algebra
`RootPairing.ChevalleyLieAlgebra c` on the product carrier `Y × (ι →₀ ℤ)`, following the
full-Cartan carrier pattern of `Matrix.FullShellLieAlgebra`
(`TauCeti.Algebra.Lie.NormTwoShell.FullCartan.Basic`) without restricting to simply-laced norm-two
shells.

Every root-sum bracket `⁅eᵢ, eⱼ⁆ = Nᵢⱼ eₖ` has Chevalley size `|Nᵢⱼ| = pᵢⱼ + 1` where
`pᵢⱼ = P.chainBotCoeff i j`, skew-symmetry `Nⱼᵢ = -Nᵢⱼ`, Chevalley-involution symmetry
`N_{-i, -j} = -Nᵢⱼ`, and the three-root Jacobi identities on coroot and root coordinates. From
these equations alone — with no division by `2`, no Killing form, and no splitting of `Y` — the
bilinear bracket on `Y × (ι →₀ ℤ)` makes `ChevalleyLieAlgebra c` a `ℤ`-Lie algebra whose center is
the Cartan image of the common kernel of all roots on `Y`. When `ι` is empty, the unique table
`ChevalleyConstants.ofIsEmpty` makes `ChevalleyLieAlgebra c` an abelian `ℤ`-Lie algebra canonically
isomorphic to `Y`. Given any `ℤ`-basis `bY` of `Y`, `ChevalleyLieAlgebra.basis` adjoins the root
vectors to form a `ℤ`-basis of `ChevalleyLieAlgebra c`, whose scalar extension gives an `R`-basis
of `R ⊗[ℤ] ChevalleyLieAlgebra c` over every commutative ring `R`.

## Main definitions

* `RootPairing.tripleRootCoeff`: the `l`-th root coordinate of `⁅eᵢ, ⁅eⱼ, eₖ⁆⁆` for a candidate
  structure-constant table on `P`.
* `RootPairing.ChevalleyConstants`: an extensional table of Chevalley integer structure constants
  on a finite integral root pairing `P`.
* `RootPairing.ChevalleyConstants.ofIsEmpty`: the canonical table on a root-free datum.
* `RootPairing.ChevalleyLieAlgebra`: the integral Lie algebra `Y × (ι →₀ ℤ)` over the full
  cocharacter group `Y`.
* `RootPairing.ChevalleyLieAlgebra.cartan`, `RootPairing.ChevalleyLieAlgebra.root`: the Cartan
  embedding `Y →ₗ[ℤ] ChevalleyLieAlgebra c` and root vectors `ι → ChevalleyLieAlgebra c`.
* `RootPairing.ChevalleyLieAlgebra.basis`: the `ℤ`-basis indexed by `J ⊕ ι` attached to a `ℤ`-basis
  `J` of `Y`.

## Main results

* `RootPairing.ChevalleyLieAlgebra.instLieRing`, `RootPairing.ChevalleyLieAlgebra.instLieAlgebra`:
  `ChevalleyLieAlgebra c` is a Lie algebra over `ℤ`.
* `RootPairing.ChevalleyLieAlgebra.mem_center_iff`,
  `RootPairing.ChevalleyLieAlgebra.center_eq_map_iInf_ker`: the center is the Cartan image of the
  common kernel of the roots on `Y`.
* `RootPairing.ChevalleyLieAlgebra.instIsLieAbelianOfIsEmpty`,
  `RootPairing.ChevalleyLieAlgebra.cartanEquivOfIsEmpty`: for an empty root set, the Chevalley Lie
  algebra is abelian and linearly equivalent to `Y`.

## References

* C. Chevalley, *Sur certains groupes simples*, Tohoku Math. J. (2) **7** (1955), 14--66.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016), §§1--2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.1--4.2.
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
noncomputable def tripleRootCoeff (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    (i j k l : ι) : ℤ :=
  (if P.root j + P.root k = 0 ∧ l = i then -P.pairing i j else 0) +
    if h : ∃ m, P.root m = P.root j + P.root k then
      if P.root l = P.root i + P.root h.choose then N i h.choose * N j k else 0
    else 0

open scoped Classical in
theorem tripleRootCoeff_of_add_eq_zero (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hjk : P.root j + P.root k = 0) :
    P.tripleRootCoeff N i j k l = if l = i then -P.pairing i j else 0 := by
  have hnot : ¬∃ m, P.root m = P.root j + P.root k := fun ⟨m, hm⟩ ↦ P.ne_zero m (hm.trans hjk)
  rw [tripleRootCoeff, dite_eq_right hnot, add_zero]
  by_cases hli : l = i <;> simp [hjk, hli]

open scoped Classical in
theorem tripleRootCoeff_of_root_eq_add (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k m l : ι} (hm : P.root m = P.root j + P.root k) :
    P.tripleRootCoeff N i j k l = if P.root l = P.root i + P.root m then N i m * N j k else 0 := by
  have hne : P.root j + P.root k ≠ 0 := fun h ↦ P.ne_zero m (hm.trans h)
  have hex : ∃ m', P.root m' = P.root j + P.root k := ⟨m, hm⟩
  have hchoose : hex.choose = m := P.root.injective (hex.choose_spec.trans hm.symm)
  rw [tripleRootCoeff, ite_eq_right (fun h ↦ hne h.1), zero_add, dite_eq_left hex, hchoose]

theorem tripleRootCoeff_of_notMem_of_add_ne_zero (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ)
    {i j k l : ι} (hnot : P.root j + P.root k ∉ range P.root) (hne : P.root j + P.root k ≠ 0) :
    P.tripleRootCoeff N i j k l = 0 := by
  classical
  have hex : ¬∃ m, P.root m = P.root j + P.root k := fun ⟨m, hm⟩ ↦ hnot ⟨m, hm⟩
  rw [tripleRootCoeff, ite_eq_right (fun h ↦ hne h.1), dite_eq_right hex, add_zero]

variable [Finite ι]

/-- **Chevalley integer structure constants** on a finite integral root pairing `P`: an
extensional integer table `structConst : ι → ι → ℤ` vanishing outside root sums, skew-symmetric,
having absolute value `P.chainBotCoeff i j + 1` on every root sum, negated by the root opposition
`i ↦ P.reflectionPerm i i`, and satisfying the three-root Jacobi identities on coroot and root
coordinates. -/
@[ext]
structure ChevalleyConstants (P : RootPairing ι ℤ X Y) where
  /-- The integer coefficient `Nᵢⱼ` of `eₖ` in `⁅eᵢ, eⱼ⁆` when `αₖ = αᵢ + αⱼ`, and `0` when
  `αᵢ + αⱼ` is not a root. -/
  structConst : ι → ι → ℤ
  /-- Pairs of roots whose sum is not a root carry zero structure constant, so `structConst` has
  no unconstrained entries. -/
  structConst_eq_zero_of_notMem_range (i j : ι) :
    P.root i + P.root j ∉ range P.root → structConst i j = 0
  /-- Skew-symmetry `Nⱼᵢ = -Nᵢⱼ`. -/
  structConst_swap (i j : ι) : structConst j i = -structConst i j
  /-- Chevalley normalization `|Nᵢⱼ| = pᵢⱼ + 1` whenever `αᵢ + αⱼ` is a root. -/
  natAbs_structConst {i j k : ι} :
    P.root k = P.root i + P.root j → (structConst i j).natAbs = P.chainBotCoeff i j + 1
  /-- Compatibility with the Chevalley involution: `N_{-i, -j} = -Nᵢⱼ`. -/
  structConst_reflectionPerm (i j : ι) :
    structConst (P.reflectionPerm i i) (P.reflectionPerm j j) = -structConst i j
  /-- The Cartan component of the three-root Jacobi identity when `αᵢ + αⱼ + αₖ = 0`. -/
  coroot_jacobi {i j k : ι} :
    P.root i + P.root j + P.root k = 0 →
      structConst j k • P.coroot i + structConst k i • P.coroot j +
        structConst i j • P.coroot k = 0
  /-- The root-coordinate component of the three-root Jacobi identity. -/
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
  have h := c.structConst_swap i i
  omega

theorem structConst_eq_zero_of_add_eq_zero {i j : ι} (h : P.root i + P.root j = 0) :
    c.structConst i j = 0 :=
  c.structConst_eq_zero_of_notMem_range i j fun ⟨k, hk⟩ ↦ P.ne_zero k (hk.trans h)

theorem structConst_ne_zero {i j k : ι} (h : P.root k = P.root i + P.root j) :
    c.structConst i j ≠ 0 := by
  have hnat := c.natAbs_structConst h
  omega

theorem structConst_eq_natCast_or_eq_neg_natCast {i j k : ι}
    (h : P.root k = P.root i + P.root j) :
    c.structConst i j = (P.chainBotCoeff i j + 1 : ℕ) ∨
      c.structConst i j = -((P.chainBotCoeff i j + 1 : ℕ) : ℤ) := by
  have hnat : (c.structConst i j).natAbs = P.chainBotCoeff i j + 1 := c.natAbs_structConst h
  rcases Int.natAbs_eq (c.structConst i j) with hpos | hneg
  · exact Or.inl (hpos.trans (by rw [hnat]))
  · exact Or.inr (hneg.trans (by rw [hnat]))

/-- The unique Chevalley structure-constant table on a root-free datum `[IsEmpty ι]`. -/
def ofIsEmpty (P : RootPairing ι ℤ X Y) [IsEmpty ι] : P.ChevalleyConstants where
  structConst i := isEmptyElim i
  structConst_eq_zero_of_notMem_range i := isEmptyElim i
  structConst_swap i := isEmptyElim i
  natAbs_structConst {i} := isEmptyElim i
  structConst_reflectionPerm i := isEmptyElim i
  coroot_jacobi {i} := isEmptyElim i
  root_jacobi i := isEmptyElim i

instance [IsEmpty ι] : Unique P.ChevalleyConstants where
  default := ofIsEmpty P
  uniq c := by ext i; exact isEmptyElim i

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

@[simp]
theorem equivProd_cartan (y : Y) : equivProd c (cartan c y) = (y, 0) := by
  simp [cartan]

@[simp]
theorem equivProd_root (i : ι) : equivProd c (root c i) = (0, Finsupp.single i 1) := by
  simp [root]

theorem cartan_injective : Function.Injective (cartan c) := fun y z h ↦ by
  simpa using congrArg (fun u ↦ (equivProd c u).1) h

theorem root_ne_zero (i : ι) : root c i ≠ 0 := by
  intro h
  have h0 := congrArg (fun u ↦ (equivProd c u).2 i) h
  simp at h0

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
  classical
  rw [rootBracket, ite_eq_left h]

@[simp]
theorem rootBracket_reflectionPerm_right (i : ι) :
    rootBracket c i (P.reflectionPerm i i) = cartan c (P.coroot i) :=
  rootBracket_of_add_eq_zero c (by simp)

theorem rootBracket_of_root_eq_add {i j k : ι} (h : P.root k = P.root i + P.root j) :
    rootBracket c i j = c.structConst i j • root c k := by
  classical
  have hne : P.root i + P.root j ≠ 0 := fun h0 ↦ P.ne_zero k (h.trans h0)
  have hex : ∃ m, P.root m = P.root i + P.root j := ⟨k, h⟩
  have hchoose : hex.choose = k := P.root.injective (hex.choose_spec.trans h.symm)
  rw [rootBracket, ite_eq_right hne, dite_eq_left hex, hchoose]

theorem rootBracket_of_notMem_of_add_ne_zero {i j : ι}
    (hnot : P.root i + P.root j ∉ range P.root) (hne : P.root i + P.root j ≠ 0) :
    rootBracket c i j = 0 := by
  classical
  have hex : ¬∃ k, P.root k = P.root i + P.root j := fun ⟨k, hk⟩ ↦ hnot ⟨k, hk⟩
  rw [rootBracket, ite_eq_right hne, dite_eq_right hex]

open scoped Classical in
@[simp]
theorem equivProd_rootBracket_fst (i j : ι) :
    (equivProd c (rootBracket c i j)).1 = if P.root i + P.root j = 0 then P.coroot i else 0 := by
  by_cases h0 : P.root i + P.root j = 0
  · rw [rootBracket_of_add_eq_zero c h0, equivProd_cartan, ite_eq_left h0]
  · rw [ite_eq_right h0]
    by_cases hm : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hm
      rw [rootBracket_of_root_eq_add c hk, map_smul, equivProd_root, Prod.smul_fst, smul_zero]
    · have hnot : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hm ⟨k, hk⟩
      rw [rootBracket_of_notMem_of_add_ne_zero c hnot h0, map_zero, Prod.fst_zero]

open scoped Classical in
@[simp]
theorem equivProd_rootBracket_snd_apply (i j l : ι) :
    (equivProd c (rootBracket c i j)).2 l =
      if P.root l = P.root i + P.root j then c.structConst i j else 0 := by
  by_cases h0 : P.root i + P.root j = 0
  · have hne : P.root l ≠ P.root i + P.root j := fun hl ↦ P.ne_zero l (hl.trans h0)
    rw [rootBracket_of_add_eq_zero c h0, equivProd_cartan, ite_eq_right hne, Finsupp.zero_apply]
  · by_cases hm : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hm
      rw [rootBracket_of_root_eq_add c hk, map_smul, equivProd_root, Prod.smul_snd,
        Finsupp.coe_smul, Pi.smul_apply]
      by_cases hlk : l = k
      · subst hlk
        rw [ite_eq_left hk, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      · have hne : P.root l ≠ P.root i + P.root j :=
          fun hl ↦ hlk (P.root.injective (hl.trans hk.symm))
        simp [hne, hlk]
    · have hnot : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hm ⟨k, hk⟩
      have hne : P.root l ≠ P.root i + P.root j := fun hl ↦ hm ⟨l, hl⟩
      rw [rootBracket_of_notMem_of_add_ne_zero c hnot h0, ite_eq_right hne, map_zero, Prod.snd_zero,
        Finsupp.zero_apply]

@[simp]
theorem rootBracket_self (i : ι) : rootBracket c i i = 0 := by
  classical
  have hself : P.root i + P.root i ≠ 0 := by
    rw [ne_eq, add_eq_zero_iff_eq_neg, P.root_eq_neg_iff]
    exact P.ne_neg i
  apply (equivProd c).injective
  rw [map_zero]
  ext1
  · rw [equivProd_rootBracket_fst, ite_eq_right hself, Prod.fst_zero]
  · ext l
    rw [equivProd_rootBracket_snd_apply, c.structConst_self, ite_self, Prod.snd_zero,
      Finsupp.zero_apply]

theorem rootBracket_swap (i j : ι) : rootBracket c j i = -rootBracket c i j := by
  classical
  apply (equivProd c).injective
  rw [map_neg]
  ext1
  · rw [equivProd_rootBracket_fst, Prod.fst_neg, equivProd_rootBracket_fst]
    by_cases h0 : P.root i + P.root j = 0
    · have h0' : P.root j + P.root i = 0 := by rw [add_comm]; exact h0
      have hcoroot : P.coroot j = -P.coroot i :=
        P.coroot_eq_neg_iff.mpr (P.root_eq_neg_iff.mp (add_eq_zero_iff_eq_neg.mp h0'))
      rw [ite_eq_left h0', ite_eq_left h0, hcoroot]
    · have h0' : P.root j + P.root i ≠ 0 := by rw [add_comm]; exact h0
      rw [ite_eq_right h0', ite_eq_right h0, neg_zero]
  · ext l
    rw [equivProd_rootBracket_snd_apply, Prod.snd_neg, Finsupp.coe_neg, Pi.neg_apply,
      equivProd_rootBracket_snd_apply, add_comm (P.root j) (P.root i), c.structConst_swap i j]
    by_cases hl : P.root l = P.root i + P.root j <;> simp [hl]

/-- The action `y ↦ (eᵢ ↦ ⟨αᵢ, y⟩ eᵢ)` of `Y` on the root part. -/
private noncomputable def cartanAction :
    Y →ₗ[ℤ] (ι →₀ ℤ) →ₗ[ℤ] ChevalleyLieAlgebra c :=
  (Finsupp.linearCombination ℤ fun i : ι ↦
    (P.toLinearMap (P.root i)).smulRight (root c i)).flip

/-- Bilinear extension of `rootBracket` to `ι →₀ ℤ`. -/
private noncomputable def rootPart :
    (ι →₀ ℤ) →ₗ[ℤ] (ι →₀ ℤ) →ₗ[ℤ] ChevalleyLieAlgebra c :=
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
theorem bracketBilin_apply_apply (x y : ChevalleyLieAlgebra c) :
    bracketBilin c x y = ⁅x, y⁆ :=
  (rfl)

protected theorem add_lie (x y z : ChevalleyLieAlgebra c) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ :=
  by rw [← bracketBilin_apply_apply, map_add, LinearMap.add_apply]; rfl

protected theorem lie_add (x y z : ChevalleyLieAlgebra c) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ :=
  (bracketBilin c x).map_add y z

protected theorem zero_lie (x : ChevalleyLieAlgebra c) : ⁅(0 : ChevalleyLieAlgebra c), x⁆ = 0 :=
  by rw [← bracketBilin_apply_apply, map_zero, LinearMap.zero_apply]

protected theorem lie_zero (x : ChevalleyLieAlgebra c) : ⁅x, (0 : ChevalleyLieAlgebra c)⁆ = 0 :=
  (bracketBilin c x).map_zero

protected theorem neg_lie (x y : ChevalleyLieAlgebra c) : ⁅-x, y⁆ = -⁅x, y⁆ :=
  by rw [← bracketBilin_apply_apply, map_neg, LinearMap.neg_apply, bracketBilin_apply_apply]

protected theorem lie_neg (x y : ChevalleyLieAlgebra c) : ⁅x, -y⁆ = -⁅x, y⁆ :=
  (bracketBilin c x).map_neg y

protected theorem zsmul_lie (r : ℤ) (x y : ChevalleyLieAlgebra c) : ⁅r • x, y⁆ = r • ⁅x, y⁆ :=
  by rw [← bracketBilin_apply_apply, map_smul, LinearMap.smul_apply, bracketBilin_apply_apply]

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
    refine linearMap_ext (fun y ↦ linearMap_ext (fun z ↦ ?_) fun j ↦ ?_)
      fun i ↦ linearMap_ext (fun z ↦ ?_) fun j ↦ ?_ <;>
      simp only [LinearMap.flip_apply, LinearMap.neg_apply, bracketBilin_apply_apply]
    · simp
    · simp
    · simp
    · rw [root_lie_root, root_lie_root, rootBracket_swap c i j]
  simpa using congr($key x y)

protected theorem lie_self (x : ChevalleyLieAlgebra c) : ⁅x, x⁆ = 0 := by
  let q : ChevalleyLieAlgebra c →+ ChevalleyLieAlgebra c :=
    { toFun u := ⁅u, u⁆
      map_zero' := ChevalleyLieAlgebra.zero_lie c 0
      map_add' u v := by
        rw [ChevalleyLieAlgebra.add_lie, ChevalleyLieAlgebra.lie_add,
          ChevalleyLieAlgebra.lie_add, ChevalleyLieAlgebra.lie_skew c u v]
        abel }
  have key : q.toIntLinearMap = 0 := linearMap_ext (by simp [q]) (by simp [q])
  exact congr($key x)

open scoped Classical in
private theorem equivProd_root_lie_rootBracket_fst (i j k : ι) :
    (equivProd c ⁅root c i, rootBracket c j k⁆).1 =
      if P.root i + P.root j + P.root k = 0 then c.structConst j k • P.coroot i else 0 := by
  by_cases hjk0 : P.root j + P.root k = 0
  · have hsum : P.root i + P.root j + P.root k ≠ 0 := by
      rw [add_assoc, hjk0, add_zero]; exact P.ne_zero i
    rw [rootBracket_of_add_eq_zero c hjk0, root_lie_cartan, map_neg, map_smul, equivProd_root,
      Prod.fst_neg, Prod.smul_fst, smul_zero, neg_zero, ite_eq_right hsum]
  · by_cases hex : ∃ m, P.root m = P.root j + P.root k
    · obtain ⟨m, hm⟩ := hex
      rw [rootBracket_of_root_eq_add c hm, ChevalleyLieAlgebra.lie_zsmul, map_smul, Prod.smul_fst,
        root_lie_root, equivProd_rootBracket_fst]
      have hiff : P.root i + P.root m = 0 ↔ P.root i + P.root j + P.root k = 0 := by
        rw [hm, add_assoc]
      by_cases him : P.root i + P.root m = 0
      · rw [ite_eq_left him, ite_eq_left (hiff.mp him)]
      · rw [ite_eq_right him, ite_eq_right (mt hiff.mpr him), smul_zero]
    · have hnot : P.root j + P.root k ∉ range P.root := fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩
      have hsum : P.root i + P.root j + P.root k ≠ 0 := by
        intro h0
        apply hex
        refine ⟨P.reflectionPerm i i, ?_⟩
        rw [P.root_reflectionPerm, P.reflection_apply_self]
        calc -P.root i = P.root i + P.root j + P.root k - P.root i := by rw [h0, zero_sub]
          _ = P.root j + P.root k := by abel
      rw [rootBracket_of_notMem_of_add_ne_zero c hnot hjk0, ChevalleyLieAlgebra.lie_zero,
        map_zero, Prod.fst_zero, ite_eq_right hsum]

private theorem equivProd_root_lie_rootBracket_snd_apply (i j k l : ι) :
    (equivProd c ⁅root c i, rootBracket c j k⁆).2 l = P.tripleRootCoeff c.structConst i j k l := by
  classical
  by_cases hjk0 : P.root j + P.root k = 0
  · rw [rootBracket_of_add_eq_zero c hjk0, root_lie_cartan,
      P.tripleRootCoeff_of_add_eq_zero c.structConst hjk0, map_neg, map_smul, equivProd_root,
      Prod.snd_neg, Prod.smul_snd, Finsupp.coe_neg, Finsupp.coe_smul, Pi.neg_apply, Pi.smul_apply]
    have hpair : P.toLinearMap (P.root i) (P.coroot j) = P.pairing i j :=
      P.root_coroot_eq_pairing i j
    by_cases hli : l = i
    · subst hli
      simp [hpair]
    · simp [hli]
  · by_cases hex : ∃ m, P.root m = P.root j + P.root k
    · obtain ⟨m, hm⟩ := hex
      rw [rootBracket_of_root_eq_add c hm, P.tripleRootCoeff_of_root_eq_add c.structConst hm,
        ChevalleyLieAlgebra.lie_zsmul, map_smul, Prod.smul_snd, Finsupp.coe_smul, Pi.smul_apply,
        root_lie_root, equivProd_rootBracket_snd_apply, smul_eq_mul]
      by_cases hlm : P.root l = P.root i + P.root m
      · rw [ite_eq_left hlm, ite_eq_left hlm, mul_comm]
      · rw [ite_eq_right hlm, ite_eq_right hlm, mul_zero]
    · have hnot : P.root j + P.root k ∉ range P.root := fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩
      rw [rootBracket_of_notMem_of_add_ne_zero c hnot hjk0,
        P.tripleRootCoeff_of_notMem_of_add_ne_zero c.structConst hnot hjk0,
        ChevalleyLieAlgebra.lie_zero, map_zero, Prod.snd_zero, Finsupp.zero_apply]

private theorem jacobi_cartan_cartan_root (y z : Y) (k : ι) :
    ⁅cartan c y, ⁅cartan c z, root c k⁆⁆ + ⁅cartan c z, ⁅root c k, cartan c y⁆⁆ +
      ⁅root c k, ⁅cartan c y, cartan c z⁆⁆ = 0 := by
  simp only [cartan_lie_root, root_lie_cartan, cartan_lie_cartan, ChevalleyLieAlgebra.lie_zsmul,
    ChevalleyLieAlgebra.lie_neg, ChevalleyLieAlgebra.lie_zero, smul_smul,
    mul_comm (P.toLinearMap (P.root k) y)]
  abel

private theorem jacobi_cartan_root_root (y : Y) (i j : ι) :
    ⁅cartan c y, ⁅root c i, root c j⁆⁆ + ⁅root c i, ⁅root c j, cartan c y⁆⁆ +
      ⁅root c j, ⁅cartan c y, root c i⁆⁆ = 0 := by
  classical
  rw [root_lie_root, root_lie_cartan, cartan_lie_root, ChevalleyLieAlgebra.lie_neg,
    ChevalleyLieAlgebra.lie_zsmul, ChevalleyLieAlgebra.lie_zsmul, root_lie_root, root_lie_root,
    rootBracket_swap c i j, smul_neg]
  by_cases h0 : P.root i + P.root j = 0
  · rw [rootBracket_of_add_eq_zero c h0, cartan_lie_cartan, zero_add]
    have hsum : P.toLinearMap (P.root i) y + P.toLinearMap (P.root j) y = 0 := by
      rw [← LinearMap.add_apply, ← map_add, h0, map_zero, LinearMap.zero_apply]
    calc -(P.toLinearMap (P.root j) y • cartan c (P.coroot i)) +
          -(P.toLinearMap (P.root i) y • cartan c (P.coroot i))
        = -((P.toLinearMap (P.root i) y + P.toLinearMap (P.root j) y) • cartan c (P.coroot i)) := by
          rw [add_smul]; abel
      _ = 0 := by rw [hsum, zero_smul, neg_zero]
  · by_cases hex : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hex
      rw [rootBracket_of_root_eq_add c hk, ChevalleyLieAlgebra.lie_zsmul, cartan_lie_root,
        smul_smul, smul_smul, smul_smul, hk, map_add, LinearMap.add_apply, mul_add, add_smul,
        mul_comm (P.toLinearMap (P.root j) y), mul_comm (P.toLinearMap (P.root i) y)]
      abel
    · have hnot : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩
      rw [rootBracket_of_notMem_of_add_ne_zero c hnot h0, ChevalleyLieAlgebra.lie_zero, smul_zero,
        smul_zero, neg_zero, add_zero, add_zero]

private theorem jacobi_root_root_root (i j k : ι) :
    ⁅root c i, ⁅root c j, root c k⁆⁆ + ⁅root c j, ⁅root c k, root c i⁆⁆ +
      ⁅root c k, ⁅root c i, root c j⁆⁆ = 0 := by
  classical
  apply (equivProd c).injective
  rw [map_add, map_add, map_zero, root_lie_root, root_lie_root, root_lie_root]
  ext1
  · rw [Prod.fst_add, Prod.fst_add, Prod.fst_zero, equivProd_root_lie_rootBracket_fst,
      equivProd_root_lie_rootBracket_fst, equivProd_root_lie_rootBracket_fst]
    by_cases h0 : P.root i + P.root j + P.root k = 0
    · have h1 : P.root j + P.root k + P.root i = 0 := by abel_nf at h0 ⊢; exact h0
      have h2 : P.root k + P.root i + P.root j = 0 := by abel_nf at h0 ⊢; exact h0
      rw [ite_eq_left h0, ite_eq_left h1, ite_eq_left h2]
      exact c.coroot_jacobi h0
    · have h1 : P.root j + P.root k + P.root i ≠ 0 := fun h ↦ h0 (by abel_nf at h ⊢; exact h)
      have h2 : P.root k + P.root i + P.root j ≠ 0 := fun h ↦ h0 (by abel_nf at h ⊢; exact h)
      rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, add_zero, add_zero]
  · ext l
    rw [Prod.snd_add, Prod.snd_add, Prod.snd_zero, Finsupp.coe_add, Finsupp.coe_add,
      Finsupp.coe_zero, Pi.add_apply, Pi.add_apply, Pi.zero_apply,
      equivProd_root_lie_rootBracket_snd_apply, equivProd_root_lie_rootBracket_snd_apply,
      equivProd_root_lie_rootBracket_snd_apply]
    exact c.root_jacobi i j k l

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
    · simp [ChevalleyLieAlgebra.lie_zero]
    · rw [add_rotate, add_rotate]
      exact jacobi_cartan_cartan_root c _ _ _
    · rw [add_rotate]
      exact jacobi_cartan_cartan_root c _ _ _
    · rw [add_rotate, add_rotate]
      exact jacobi_cartan_root_root c _ _ _
    · exact jacobi_cartan_cartan_root c _ _ _
    · exact jacobi_cartan_root_root c _ _ _
    · rw [add_rotate]
      exact jacobi_cartan_root_root c _ _ _
    · exact jacobi_root_root_root c _ _ _
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
    rw [ChevalleyLieAlgebra.lie_skew c x z, ChevalleyLieAlgebra.lie_neg,
      ChevalleyLieAlgebra.lie_skew c ⁅x, y⁆ z] at h
    calc ⁅x, ⁅y, z⁆⁆ = ⁅x, ⁅y, z⁆⁆ -
          (⁅x, ⁅y, z⁆⁆ + -⁅y, ⁅x, z⁆⁆ + -⁅⁅x, y⁆, z⁆) := by rw [h, sub_zero]
      _ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by abel

noncomputable instance instLieAlgebra : LieAlgebra ℤ (ChevalleyLieAlgebra c) where
  lie_smul := ChevalleyLieAlgebra.lie_zsmul c

@[simp]
theorem root_lie_root_of_add_eq_zero {i j : ι} (h : P.root i + P.root j = 0) :
    ⁅root c i, root c j⁆ = cartan c (P.coroot i) := by
  rw [root_lie_root, rootBracket_of_add_eq_zero c h]

@[simp]
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
    apply linearMap_ext
    · intro z; simp [coord]
    · intro j
      by_cases hij : i = j
      · subst hij; simp [coord]
      · simp [coord, Ne.symm hij]
  exact LinearMap.congr_fun h x

/-- The centralizer of the full Cartan lattice `Y` in `ChevalleyLieAlgebra c` is its image under
`cartan c`. -/
theorem forall_cartan_lie_eq_zero_iff (x : ChevalleyLieAlgebra c) :
    (∀ y, ⁅cartan c y, x⁆ = 0) ↔ x ∈ LinearMap.range (cartan c) := by
  constructor
  · intro hx
    have hroot : (equivProd c x).2 = 0 := by
      ext i
      have h := equivProd_cartan_lie_snd c (P.coroot i) x i
      have htwo : P.toLinearMap (P.root i) (P.coroot i) = 2 :=
        (P.root_coroot_eq_pairing i i).trans (P.pairing_same i)
      rw [hx, map_zero, Prod.snd_zero, Finsupp.zero_apply, htwo] at h
      simp only [Finsupp.zero_apply]
      omega
    refine ⟨(equivProd c x).1, (equivProd c).injective ?_⟩
    rw [equivProd_cartan]
    exact Prod.ext rfl hroot.symm
  · rintro ⟨y, rfl⟩ z
    exact cartan_lie_cartan c z y

@[simp]
theorem forall_lie_cartan_eq_zero_iff (y : Y) :
    (∀ x : ChevalleyLieAlgebra c, ⁅x, cartan c y⁆ = 0) ↔
      ∀ i : ι, P.toLinearMap (P.root i) y = 0 := by
  constructor
  · intro hy i
    have h := congrArg (fun z ↦ (equivProd c z).2 i) (hy (root c i))
    simpa using h
  · intro hweight
    have h : (bracketBilin c).flip (cartan c y) = 0 := by
      apply linearMap_ext
      · intro z; simp
      · intro i; simp [hweight i]
    exact LinearMap.congr_fun h

/-- An element of `ChevalleyLieAlgebra c` is central if and only if its root coordinates vanish and
its Cartan coordinate is annihilated by every root of `P`. -/
theorem mem_center_iff (x : ChevalleyLieAlgebra c) :
    x ∈ _root_.LieAlgebra.center ℤ (ChevalleyLieAlgebra c) ↔
      (equivProd c x).2 = 0 ∧ ∀ i : ι, P.toLinearMap (P.root i) (equivProd c x).1 = 0 := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (forall_cartan_lie_eq_zero_iff c x).mp fun y ↦ hx (cartan c y)
    simp only [equivProd_cartan, true_and]
    exact (forall_lie_cartan_eq_zero_iff c y).mp hx
  · rintro ⟨hroot, hweight⟩
    have hx : x = cartan c (equivProd c x).1 :=
      (equivProd c).injective (by rw [equivProd_cartan]; exact Prod.ext rfl hroot)
    rw [hx]
    exact (forall_lie_cartan_eq_zero_iff c (equivProd c x).1).mpr hweight

/-- The center of `ChevalleyLieAlgebra c`, as a `ℤ`-submodule, is the Cartan image of the common
kernel of all roots on `Y`. -/
theorem center_eq_map_iInf_ker :
    (_root_.LieAlgebra.center ℤ (ChevalleyLieAlgebra c)).toSubmodule =
      Submodule.map (cartan c) (⨅ i : ι, LinearMap.ker (P.toLinearMap (P.root i))) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (forall_cartan_lie_eq_zero_iff c x).mp fun y ↦ hx (cartan c y)
    exact ⟨y, by simpa using (forall_lie_cartan_eq_zero_iff c y).mp hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (forall_lie_cartan_eq_zero_iff c y).mpr (by simpa using hy)

/-! ### The root-free datum `Φ = ∅` -/

/-- When the root index type `ι` is empty, `ChevalleyLieAlgebra c` is abelian. -/
instance instIsLieAbelianOfIsEmpty [IsEmpty ι] : IsLieAbelian (ChevalleyLieAlgebra c) :=
  ⟨fun x y ↦ by
    have h0 : bracketBilin c = 0 :=
      linearMap_ext (fun _ ↦ linearMap_ext (by simp) fun i ↦ isEmptyElim i)
        fun i ↦ isEmptyElim i
    simpa using congr($h0 x y)⟩

/-- When `ι` is empty, `cartan c` identifies the full cocharacter group `Y` with
`ChevalleyLieAlgebra c`. -/
noncomputable def cartanEquivOfIsEmpty [IsEmpty ι] : Y ≃ₗ[ℤ] ChevalleyLieAlgebra c :=
  LinearEquiv.ofLinearMap (cartan c) ((LinearMap.fst ℤ Y (ι →₀ ℤ)).comp (equivProd c).toLinearMap)
    (LinearMap.ext fun x ↦ (equivProd c).injective <| by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearEquiv.coe_toLinearMap, equivProd_cartan, LinearMap.id_apply]
      refine Prod.ext rfl ?_
      ext i
      exact isEmptyElim i)
    (LinearMap.ext fun y ↦ by simp)

@[simp]
theorem cartanEquivOfIsEmpty_apply [IsEmpty ι] (y : Y) :
    cartanEquivOfIsEmpty c y = cartan c y :=
  (rfl)

@[simp]
theorem cartanEquivOfIsEmpty_symm_apply [IsEmpty ι] (x : ChevalleyLieAlgebra c) :
    (cartanEquivOfIsEmpty c).symm x = (equivProd c x).1 :=
  (rfl)

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
    (basis c bY).repr x (.inl j) = bY.repr (equivProd c x).1 j := by
  simp [basis]

@[simp]
theorem basis_repr_inr (x : ChevalleyLieAlgebra c) (i : ι) :
    (basis c bY).repr x (.inr i) = (equivProd c x).2 i := by
  simp [basis]

/-- Scalar extension of the integral Chevalley basis to `R ⊗[ℤ] ChevalleyLieAlgebra c` over any
commutative ring `R`. -/
noncomputable abbrev baseChangeBasis (R : Type*) [CommRing R] :
    Basis (J ⊕ ι) R (R ⊗[ℤ] ChevalleyLieAlgebra c) :=
  (basis c bY).baseChange R

@[simp]
theorem baseChangeBasis_inl (R : Type*) [CommRing R] (j : J) :
    baseChangeBasis c bY R (.inl j) = 1 ⊗ₜ[ℤ] cartan c (bY j) := by
  simp [baseChangeBasis]

@[simp]
theorem baseChangeBasis_inr (R : Type*) [CommRing R] (i : ι) :
    baseChangeBasis c bY R (.inr i) = 1 ⊗ₜ[ℤ] root c i := by
  simp [baseChangeBasis]

end Basis

end ChevalleyLieAlgebra

end LieAlgebra

end RootPairing
