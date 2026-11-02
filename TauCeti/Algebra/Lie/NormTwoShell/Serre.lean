/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Basic
public import TauCeti.Algebra.Lie.Presentation.Serre

/-!
# The Serre presentation of the signed Lie algebra of a simply laced Cartan matrix

Let `B : Matrix I I ℤ` be positive definite with diagonal entries `2` and nonpositive off-diagonal
entries, that is, the Cartan matrix of a simply laced Dynkin diagram, possibly disconnected, with
its vertices linearly ordered. The norm-two shell `Φ` of `B` is then the root system of the diagram,
with simple roots `αᵢ = Pi.single i 1`, and `Matrix.ShellLieAlgebra B` is the Frenkel--Kac Lie
algebra over `ℤ` built on it.

This file shows that its Chevalley generators

```text
Hᵢ = H_(αᵢ),    Eᵢ = x_(αᵢ),    Fᵢ = x_(-αᵢ)
```

satisfy Serre's relations for `B` (`Matrix.ShellLieAlgebra.isSerreSystem`), so that the universal
property `TauCeti.serreLift` of the Serre presentation `Matrix.ToLieAlgebra ℤ B` gives a
homomorphism to `Matrix.ShellLieAlgebra B` sending the presented generators to `Hᵢ`, `Eᵢ`, `Fᵢ`.
This homomorphism is surjective (`Matrix.ShellLieAlgebra.serreLift_surjective`): over `ℤ`, the
`Eᵢ` and `Fᵢ` generate `Matrix.ShellLieAlgebra B` as a Lie ring
(`Matrix.ShellLieAlgebra.lieSpan_chevalleyE_chevalleyF_eq_top`).

The negative generator `Fᵢ` is the section vector of `-αᵢ`, and no sign normalization is needed:
the ordered sign `ε(αᵢ, -αᵢ)` is `1`, since the ordered form only sees strictly lower triangular
entries of `B`, so `⁅Eᵢ, Fᵢ⁆ = Hᵢ` holds on the nose.

The Serre relations themselves are instances of a statement about arbitrary roots
(`Matrix.ShellLieAlgebra.ad_root_pow_lie_root`): for roots `a ≠ -b` with pairing `p = ⟪a, b⟫`, the
iterated bracket `(ad x_a) ^ (-p).toNat ⁅x_a, x_b⁆` vanishes, because positive definiteness confines
`p` to `{-1, 0, 1, 2}` and the root strings through `b` have length at most two. Generation is the
height induction `Matrix.PosDef.normTwoShell_nonneg_induction`: every positive root is reached from
a simple root by adding simple roots without leaving `Φ`, and each such step is a bracket with some
`Eᵢ` up to a sign; the negative roots are reached in the same way with the `Fᵢ`, and the Cartan
lattice is spanned by the `Hᵢ = ⁅Eᵢ, Fᵢ⁆`.

Injectivity of the homomorphism, which would identify `Matrix.ShellLieAlgebra B` with the Serre
presentation, is not addressed here.

## Main definitions

* `Matrix.ShellLieAlgebra.chevalleyE`, `Matrix.ShellLieAlgebra.chevalleyF`: the root vectors of the
  simple roots and of their negatives.

## Main results

* `Matrix.ShellLieAlgebra.ad_root_pow_lie_root`: the Serre relation for two arbitrary roots.
* `Matrix.ShellLieAlgebra.isSerreSystem`: the Chevalley generators are a Serre system for `B`.
* `Matrix.ShellLieAlgebra.lieSpan_chevalleyE_chevalleyF_eq_top`: the `Eᵢ` and `Fᵢ` generate.
* `Matrix.ShellLieAlgebra.serreLift_surjective`: the Serre presentation maps onto
  `Matrix.ShellLieAlgebra B`.

## References

* I. B. Frenkel and V. G. Kac, *Basic representations of affine Lie algebras and dual resonance
  models*, Invent. Math. **62** (1980), 23--66.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix.ShellLieAlgebra

open LieAlgebra TauCeti

variable {I : Type*} [Fintype I] [LinearOrder I] (B : Matrix I I ℤ)

/-! ### Root strings of length at most two -/

variable {B} in
/-- **The Serre relation for two roots**, for a positive definite `B` with even diagonal: if `a` and
`b` are roots with `a + b ≠ 0` and pairing `p = ⟪a, b⟫`, then
`(ad x_a) ^ (-p).toNat ⁅x_a, x_b⁆ = 0`. The pairing is `2` when `a = b`, and otherwise lies in
`{-1, 0, 1}`. -/
theorem ad_root_pow_lie_root (hB : B.PosDef) (hev : ∀ i, Even (B i i)) {a b : B.normTwoShell}
    (hab : (a : I → ℤ) + b ≠ 0) :
    letI := lieRing hB hev
    (ad ℤ (ShellLieAlgebra B) (root B a) ^ (-((a : I → ℤ) ⬝ᵥ B *ᵥ b)).toNat)
      ⁅root B a, root B b⁆ = 0 := by
  let _ := lieRing hB hev
  have hS := hB.isHermitian.isSymm
  by_cases heq : a = b
  · subst heq
    rw [ShellLieAlgebra.lie_self hS hev, map_zero]
  have hle := hB.dotProduct_mulVec_le_one hev a.2 b.2 (Subtype.coe_injective.ne heq)
  have hge := hB.neg_one_le_dotProduct_mulVec hev a.2 b.2 fun h ↦ hab (by rw [h, neg_add_cancel])
  rcases (by omega : 0 ≤ (a : I → ℤ) ⬝ᵥ B *ᵥ b ∨ (a : I → ℤ) ⬝ᵥ B *ᵥ b = -1) with hp | hp
  · rw [root_lie_root, rootBracket_eq_zero_of_nonneg hS hp, map_zero]
  -- The string `b, a + b` stops at `a + b`, which pairs to `1` with `a`.
  have hm : (a : I → ℤ) + b ∈ B.normTwoShell := (hS.add_mem_normTwoShell_iff a.2 b.2).2 hp
  have hp' : 0 ≤ (a : I → ℤ) ⬝ᵥ B *ᵥ ((⟨_, hm⟩ : B.normTwoShell) : I → ℤ) := by
    rw [mulVec_add, dotProduct_add, mem_normTwoShell.mp a.2, hp]
    norm_num
  rw [hp, neg_neg, Int.toNat_one, pow_one, ad_apply, root_lie_root, rootBracket_of_mem hm,
    ShellLieAlgebra.lie_units_smul, root_lie_root, rootBracket_eq_zero_of_nonneg hS hp', smul_zero]

/-! ### The Chevalley generators -/

/-- The raising Chevalley generator `Eᵢ = x_(αᵢ)`: the root vector of the simple root
`αᵢ = Pi.single i 1`, for `B` with diagonal entries `2`. -/
noncomputable def chevalleyE (hdiag : ∀ i, B i i = 2) (i : I) : ShellLieAlgebra B :=
  root B ⟨Pi.single i 1, single_mem_normTwoShell (hdiag i)⟩

/-- The lowering Chevalley generator `Fᵢ = x_(-αᵢ)`: the root vector of the negative of the simple
root `αᵢ = Pi.single i 1`, for `B` with diagonal entries `2`. -/
noncomputable def chevalleyF (hdiag : ∀ i, B i i = 2) (i : I) : ShellLieAlgebra B :=
  root B ⟨-Pi.single i 1, neg_mem_normTwoShell.mpr (single_mem_normTwoShell (hdiag i))⟩

/-- `Eᵢ` is the root vector of the simple root `αᵢ`. -/
theorem chevalleyE_def (hdiag : ∀ i, B i i = 2) (i : I) :
    chevalleyE B hdiag i = root B ⟨Pi.single i 1, single_mem_normTwoShell (hdiag i)⟩ :=
  (rfl)

/-- `Fᵢ` is the root vector of the negative simple root `-αᵢ`. -/
theorem chevalleyF_def (hdiag : ∀ i, B i i = 2) (i : I) :
    chevalleyF B hdiag i =
      root B ⟨-Pi.single i 1, neg_mem_normTwoShell.mpr (single_mem_normTwoShell (hdiag i))⟩ :=
  (rfl)

variable {B}

/-- **The Chevalley generators of `Matrix.ShellLieAlgebra B` are a Serre system for `B`**, for a
positive definite `B` with diagonal entries `2` and nonpositive off-diagonal entries: the
generators `Hᵢ = H_(αᵢ)`, `Eᵢ = x_(αᵢ)` and `Fᵢ = x_(-αᵢ)` satisfy Serre's relations for `B`. -/
theorem isSerreSystem (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) :
    letI := lieRing hB fun i ↦ hdiag i ▸ even_two
    IsSerreSystem ℤ B (fun i ↦ cartan B (Pi.single i 1)) (chevalleyE B hdiag)
      (chevalleyF B hdiag) := by
  have hev : ∀ i, Even (B i i) := fun i ↦ hdiag i ▸ even_two
  let _ := lieRing hB hev
  have hS := hB.isHermitian.isSymm
  have single_dotProduct_mulVec_single (i j : I) :
      (Pi.single i 1 : I → ℤ) ⬝ᵥ B *ᵥ Pi.single j 1 = B i j := by
    simp
  have single_add_single_ne_zero (i j : I) : (Pi.single i 1 : I → ℤ) + Pi.single j 1 ≠ 0 :=
    fun h ↦ by
      have := congr_fun h i
      rcases eq_or_ne i j with rfl | hij <;> simp_all
  refine
    { lie_H_H := fun i j ↦ cartan_lie_cartan _ _
      lie_E_F_self := fun i ↦ ?_
      lie_E_F_of_ne := fun i j hij ↦ ?_
      lie_H_E := fun i j ↦ ?_
      lie_H_F := fun i j ↦ ?_
      ad_pow_lie_E_E := fun i j ↦ ?_
      ad_pow_lie_F_F := fun i j ↦ ?_ }
  · rw [chevalleyE_def, chevalleyF_def, root_lie_root,
      rootBracket_of_add_eq_zero (add_neg_cancel _)]
    simp
  · rw [chevalleyE_def, chevalleyF_def, root_lie_root]
    refine rootBracket_eq_zero_of_nonneg hS ?_
    rw [mulVec_neg, dotProduct_neg, single_dotProduct_mulVec_single, neg_nonneg]
    exact hoff i j hij
  · rw [chevalleyE_def, cartan_lie_root, single_dotProduct_mulVec_single]
  · rw [chevalleyF_def, cartan_lie_root, mulVec_neg, dotProduct_neg,
      single_dotProduct_mulVec_single, neg_smul]
  · have h := ad_root_pow_lie_root hB hev
      (a := ⟨Pi.single i 1, single_mem_normTwoShell (hdiag i)⟩)
      (b := ⟨Pi.single j 1, single_mem_normTwoShell (hdiag j)⟩) (single_add_single_ne_zero i j)
    rwa [single_dotProduct_mulVec_single] at h
  · have h := ad_root_pow_lie_root hB hev
      (a := ⟨-Pi.single i 1, neg_mem_normTwoShell.mpr (single_mem_normTwoShell (hdiag i))⟩)
      (b := ⟨-Pi.single j 1, neg_mem_normTwoShell.mpr (single_mem_normTwoShell (hdiag j))⟩)
      (by rw [← neg_add, neg_ne_zero]; exact single_add_single_ne_zero i j)
    rwa [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg,
      single_dotProduct_mulVec_single] at h

/-! ### Generation -/

/-- **The Chevalley generators generate `Matrix.ShellLieAlgebra B` over `ℤ`**, for a positive
definite `B` with diagonal entries `2` and nonpositive off-diagonal entries: the Lie subring
generated by the `Eᵢ = x_(αᵢ)` and the `Fᵢ = x_(-αᵢ)` is everything. Every root vector is, up to
sign, an iterated bracket of the `Eᵢ` or of the `Fᵢ`, and the Cartan lattice is spanned by the
`⁅Eᵢ, Fᵢ⁆ = H_(αᵢ)`. -/
theorem lieSpan_chevalleyE_chevalleyF_eq_top (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) :
    letI := lieRing hB fun i ↦ hdiag i ▸ even_two
    LieSubalgebra.lieSpan ℤ (ShellLieAlgebra B)
      (Set.range (chevalleyE B hdiag) ∪ Set.range (chevalleyF B hdiag)) = ⊤ := by
  have hev : ∀ i, Even (B i i) := fun i ↦ hdiag i ▸ even_two
  let _ := lieRing hB hev
  set K := LieSubalgebra.lieSpan ℤ (ShellLieAlgebra B)
    (Set.range (chevalleyE B hdiag) ∪ Set.range (chevalleyF B hdiag))
  have hE (i : I) : chevalleyE B hdiag i ∈ K := LieSubalgebra.subset_lieSpan (.inl ⟨i, rfl⟩)
  have hF (i : I) : chevalleyF B hdiag i ∈ K := LieSubalgebra.subset_lieSpan (.inr ⟨i, rfl⟩)
  -- A root vector `x_c` lies in `K` once its bracket with a generator is `±x_c`.
  have step {x y : ShellLieAlgebra B} {c : B.normTwoShell} (hx : x ∈ K) (hy : y ∈ K)
      (h : ∃ u : ℤˣ, ⁅x, y⁆ = u • root B c) : root B c ∈ K := by
    obtain ⟨u, hu⟩ := h
    have : root B c = u • ⁅x, y⁆ := by rw [hu, smul_smul, Int.units_mul_self, one_smul]
    rw [this, Units.smul_def]
    exact K.smul_mem _ (K.lie_mem hx hy)
  -- The positive root vectors, by height induction.
  have hpos (a : I → ℤ) (ha : a ∈ B.normTwoShell) (hnn : 0 ≤ a) : root B ⟨a, ha⟩ ∈ K := by
    refine PosDef.normTwoShell_nonneg_induction (motive := fun a ↦ ∀ ha, root B ⟨a, ha⟩ ∈ K) hB
      hdiag hoff (fun i _ ↦ hE i) (fun a i ha _ hai ih _ ↦ step (hE i) (ih ha) ?_) ha hnn ha
    have hm : Pi.single i 1 + a ∈ B.normTwoShell := by rwa [add_comm]
    -- The bracket `⁅Eᵢ, x_a⁆` lands on the root `αᵢ + a`; the induction indexes it as `a + αᵢ`.
    have hc : (⟨_, hm⟩ : B.normTwoShell) = ⟨_, hai⟩ := Subtype.ext (add_comm _ _)
    rw [chevalleyE_def, root_lie_root, rootBracket_of_mem hm, hc]
    exact ⟨_, rfl⟩
  -- The negative root vectors, by height induction on their negatives.
  have hneg (a : I → ℤ) (ha : -a ∈ B.normTwoShell) (hnn : 0 ≤ a) : root B ⟨-a, ha⟩ ∈ K := by
    refine PosDef.normTwoShell_nonneg_induction (motive := fun a ↦ ∀ ha, root B ⟨-a, ha⟩ ∈ K) hB
      hdiag hoff (fun i _ ↦ hF i) (fun a i ha _ hai ih _ ↦ step (hF i) (ih ?_) ?_)
      (neg_mem_normTwoShell.mp ha) hnn ha
    · exact neg_mem_normTwoShell.mpr ha
    have hm : -Pi.single i 1 + -a ∈ B.normTwoShell := by
      rwa [← neg_add_rev, neg_mem_normTwoShell]
    -- The bracket `⁅Fᵢ, x_(-a)⁆` lands on the root `-αᵢ + -a`; the induction indexes it as
    -- `-(a + αᵢ)`.
    have hc : (⟨_, hm⟩ : B.normTwoShell) =
        ⟨-(a + Pi.single i 1), neg_mem_normTwoShell.mpr hai⟩ :=
      Subtype.ext (neg_add_rev _ _).symm
    rw [chevalleyF_def, root_lie_root, rootBracket_of_mem hm, hc]
    exact ⟨_, rfl⟩
  have hroot (c : B.normTwoShell) : root B c ∈ K := by
    rcases hB.nonneg_or_nonpos_of_mem_normTwoShell hev hoff c.2 with h | h
    · exact hpos c c.2 h
    · have := hneg (-c) (by rw [neg_neg]; exact c.2) (neg_nonneg.mpr h)
      simpa only [neg_neg] using this
  have hcartan (i : I) : cartan B (Pi.single i 1) ∈ K := by
    rw [← (isSerreSystem hB hdiag hoff).lie_E_F_self i]
    exact K.lie_mem (hE i) (hF i)
  -- The integral basis lies in `K`.
  have hspan : Submodule.span ℤ (Set.range (basis B)) ≤ K.toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i | c, rfl⟩
    · rw [basis_inl]
      exact hcartan i
    · rw [basis_inr]
      exact hroot c
  rw [(basis B).span_eq] at hspan
  exact eq_top_iff.mpr fun x _ ↦ hspan Submodule.mem_top

/-- **The Serre presentation maps onto `Matrix.ShellLieAlgebra B`**, for a positive definite `B`
with diagonal entries `2` and nonpositive off-diagonal entries: the homomorphism
`Matrix.ToLieAlgebra ℤ B →ₗ⁅ℤ⁆ Matrix.ShellLieAlgebra B` sending the presented generators to the
Chevalley generators `H_(αᵢ)`, `x_(αᵢ)`, `x_(-αᵢ)` is surjective. -/
protected theorem serreLift_surjective (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) :
    letI := lieRing hB fun i ↦ hdiag i ▸ even_two
    Function.Surjective (serreLift (isSerreSystem hB hdiag hoff)) :=
  let _ := lieRing hB fun i ↦ hdiag i ▸ even_two
  TauCeti.serreLift_surjective _ (lieSpan_chevalleyE_chevalleyF_eq_top hB hdiag hoff)

end Matrix.ShellLieAlgebra
