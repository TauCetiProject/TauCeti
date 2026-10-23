/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# An object killed by a product of coprime integers splits

Let `X` be an object of a preadditive category such that `(m * n) • 𝟙 X = 0`, where `m` and `n`
are coprime integers, witnessed by a Bézout identity `a * m + b * n = 1`. Then `X` is the binary
biproduct of the kernels of `m • 𝟙 X` and `n • 𝟙 X`. The inclusions are the kernel inclusions,
and the projections are the factorisations of `(b * n) • 𝟙 X` and `(a * m) • 𝟙 X` through them.
The first is killed by `m` and the second by `n`, because `X` is killed by `m * n`, and their sum is
the identity.

For a commutative group scheme `G` killed by `m * n`, this is the decomposition
`G ≅ G[m] × G[n]` into its `m`-torsion and its `n`-torsion.

## Main definitions

* `CategoryTheory.Limits.BinaryBicone.ofCoprimeKernelForks`: the binary bicone on the two kernels
  with vertex `X`.

## Main results

* `CategoryTheory.Limits.BinaryBicone.isBilimitOfCoprimeKernelForks`: this bicone is a bilimit,
  so `X` is the biproduct of the two kernels.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics
  Studies 108, Princeton University Press, 1985, 1.10.14–1.10.15.
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] {X Y : C} {a b m n : ℤ}

/-- The inclusion of a kernel of `m • 𝟙 X` is killed by `m`. -/
private theorem zsmul_ι_eq_zero (c : KernelFork (m • 𝟙 X)) : m • c.ι = 0 := by
  rw [← Category.comp_id c.ι, ← Preadditive.comp_zsmul]
  exact KernelFork.condition c

/-- **The splitting of an object killed by a product of coprime integers.** Let `X` satisfy
`(m * n) • 𝟙 X = 0`, where `a * m + b * n = 1`, and let `c₁` and `c₂` be limit kernel forks of
`m • 𝟙 X` and `n • 𝟙 X`. This is the binary bicone with vertex `X` whose inclusions are the kernel
inclusions `c₁.ι` and `c₂.ι`, and whose projections are the factorisations of `(b * n) • 𝟙 X`
through `c₁` and of `(a * m) • 𝟙 X` through `c₂`. It is a bilimit
(`BinaryBicone.isBilimitOfCoprimeKernelForks`). -/
-- Reducible so that the vertex is `X` and the inclusions are `c₁.ι` and `c₂.ι` up to reducible
-- unfolding: lemmas about the bicone are then stated, and rewrite, through `X`.
@[simps pt inl inr]
noncomputable abbrev BinaryBicone.ofCoprimeKernelForks (hab : a * m + b * n = 1)
    (hX : (m * n) • 𝟙 X = 0) {c₁ : KernelFork (m • 𝟙 X)} (hc₁ : IsLimit c₁)
    {c₂ : KernelFork (n • 𝟙 X)} (hc₂ : IsLimit c₂) : BinaryBicone c₁.pt c₂.pt where
  pt := X
  fst := (KernelFork.IsLimit.lift' hc₁ ((b * n) • 𝟙 X) (by
    simp only [Preadditive.zsmul_comp, Category.id_comp]
    linear_combination (norm := module) b • hX)).1
  snd := (KernelFork.IsLimit.lift' hc₂ ((a * m) • 𝟙 X) (by
    simp only [Preadditive.zsmul_comp, Category.id_comp]
    linear_combination (norm := module) a • hX)).1
  inl := c₁.ι
  inr := c₂.ι
  inl_fst := by
    refine Fork.IsLimit.hom_ext hc₁ ?_
    simp only [Category.assoc, (KernelFork.IsLimit.lift' hc₁ _ _).2, Preadditive.comp_zsmul,
      Category.comp_id, Category.id_comp]
    linear_combination (norm := module) hab • c₁.ι - a • zsmul_ι_eq_zero c₁
  inl_snd := by
    refine Fork.IsLimit.hom_ext hc₂ ?_
    simp only [Category.assoc, (KernelFork.IsLimit.lift' hc₂ _ _).2, Preadditive.comp_zsmul,
      Category.comp_id, zero_comp]
    linear_combination (norm := module) a • zsmul_ι_eq_zero c₁
  inr_fst := by
    refine Fork.IsLimit.hom_ext hc₁ ?_
    simp only [Category.assoc, (KernelFork.IsLimit.lift' hc₁ _ _).2, Preadditive.comp_zsmul,
      Category.comp_id, zero_comp]
    linear_combination (norm := module) b • zsmul_ι_eq_zero c₂
  inr_snd := by
    refine Fork.IsLimit.hom_ext hc₂ ?_
    simp only [Category.assoc, (KernelFork.IsLimit.lift' hc₂ _ _).2, Preadditive.comp_zsmul,
      Category.comp_id, Category.id_comp]
    linear_combination (norm := module) hab • c₂.ι - b • zsmul_ι_eq_zero c₂

variable (hab : a * m + b * n = 1) (hX : (m * n) • 𝟙 X = 0) {c₁ : KernelFork (m • 𝟙 X)}
  (hc₁ : IsLimit c₁) {c₂ : KernelFork (n • 𝟙 X)} (hc₂ : IsLimit c₂)

/-- The first projection of `BinaryBicone.ofCoprimeKernelForks`, followed by the inclusion of the
kernel of `m • 𝟙 X`, is multiplication by `b * n`. -/
@[reassoc]
theorem BinaryBicone.ofCoprimeKernelForks_fst_ι :
    (ofCoprimeKernelForks hab hX hc₁ hc₂).fst ≫ c₁.ι = (b * n) • 𝟙 X :=
  (KernelFork.IsLimit.lift' hc₁ _ _).2

/-- The second projection of `BinaryBicone.ofCoprimeKernelForks`, followed by the inclusion of the
kernel of `n • 𝟙 X`, is multiplication by `a * m`. -/
@[reassoc]
theorem BinaryBicone.ofCoprimeKernelForks_snd_ι :
    (ofCoprimeKernelForks hab hX hc₁ hc₂).snd ≫ c₂.ι = (a * m) • 𝟙 X :=
  (KernelFork.IsLimit.lift' hc₂ _ _).2

/-- **An object killed by a product of coprime integers is the biproduct of the two kernels.** If
`(m * n) • 𝟙 X = 0` and `a * m + b * n = 1`, then `X`, with the kernel inclusions of `m • 𝟙 X` and
`n • 𝟙 X` and the projections of `BinaryBicone.ofCoprimeKernelForks`, is a binary biproduct of the
two kernels. -/
noncomputable def BinaryBicone.isBilimitOfCoprimeKernelForks :
    (BinaryBicone.ofCoprimeKernelForks hab hX hc₁ hc₂).IsBilimit :=
  isBinaryBilimitOfTotal _ <| by
    have h : (b * n) • 𝟙 X + (a * m) • 𝟙 X = 𝟙 X := by
      linear_combination (norm := module) hab • 𝟙 X
    -- The vertex is `X` and the inclusions are `c₁.ι` and `c₂.ι` by definition.
    exact (congrArg₂ (· + ·) (ofCoprimeKernelForks_fst_ι hab hX hc₁ hc₂)
      (ofCoprimeKernelForks_snd_ι hab hX hc₁ hc₂)).trans h

end CategoryTheory.Limits
