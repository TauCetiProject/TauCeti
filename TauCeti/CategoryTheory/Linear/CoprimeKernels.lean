/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.CategoryTheory.Linear.Kernels

/-!
# An object killed by a product of coprime scalars splits

Let `X` be an object of an `R`-linear category, for a commutative semiring `R`, such that
`(m * n) • 𝟙 X = 0`, where `m` and `n` are coprime elements of `R`, witnessed by a Bézout identity
`a * m + b * n = 1`. Then `X` is the binary biproduct of the kernels of `m • 𝟙 X` and `n • 𝟙 X`.
The inclusions are the kernel inclusions, and the projections are the factorisations of
`(b * n) • 𝟙 X` and `(a * m) • 𝟙 X` through them. The first is killed by `m` and the second by `n`,
because `X` is killed by `m * n`, and their sum is the identity.

Every preadditive category is `ℤ`-linear, so this applies to coprime integers `m` and `n`. For a
commutative group scheme `G` killed by `m * n`, this is the decomposition `G ≅ G[m] × G[n]` into its
`m`-torsion and its `n`-torsion.

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

variable {R : Type*} [CommSemiring R] {C : Type*} [Category C] [Preadditive C] [Linear R C] {X : C}
  {a b m n : R}

/-- **The splitting of an object killed by a product of coprime scalars.** Let `X` satisfy
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
    rw [Linear.smul_comp, Category.id_comp, smul_smul, mul_assoc, mul_comm n, mul_smul, hX,
      smul_zero])).1
  snd := (KernelFork.IsLimit.lift' hc₂ ((a * m) • 𝟙 X) (by
    rw [Linear.smul_comp, Category.id_comp, smul_smul, mul_assoc, mul_smul, hX, smul_zero])).1
  inl := c₁.ι
  inr := c₂.ι
  inl_fst := Fork.IsLimit.hom_ext hc₁ <| by
    simpa [(KernelFork.IsLimit.lift' hc₁ _ _).2, add_smul, mul_smul] using
      congrArg (· • c₁.ι) hab
  inl_snd := Fork.IsLimit.hom_ext hc₂ <| by
    simp [(KernelFork.IsLimit.lift' hc₂ _ _).2, mul_smul]
  inr_fst := Fork.IsLimit.hom_ext hc₁ <| by
    simp [(KernelFork.IsLimit.lift' hc₁ _ _).2, mul_smul]
  inr_snd := Fork.IsLimit.hom_ext hc₂ <| by
    simpa [(KernelFork.IsLimit.lift' hc₂ _ _).2, add_smul, mul_smul] using
      congrArg (· • c₂.ι) hab

variable (hab : a * m + b * n = 1) (hX : (m * n) • 𝟙 X = 0) {c₁ : KernelFork (m • 𝟙 X)}
  (hc₁ : IsLimit c₁) {c₂ : KernelFork (n • 𝟙 X)} (hc₂ : IsLimit c₂)

/-- The first projection of `BinaryBicone.ofCoprimeKernelForks`, followed by the inclusion of the
kernel of `m • 𝟙 X`, is multiplication by `b * n`. -/
@[simp, reassoc]
theorem BinaryBicone.ofCoprimeKernelForks_fst_ι :
    (ofCoprimeKernelForks hab hX hc₁ hc₂).fst ≫ c₁.ι = (b * n) • 𝟙 X :=
  (KernelFork.IsLimit.lift' hc₁ _ _).2

/-- The second projection of `BinaryBicone.ofCoprimeKernelForks`, followed by the inclusion of the
kernel of `n • 𝟙 X`, is multiplication by `a * m`. -/
@[simp, reassoc]
theorem BinaryBicone.ofCoprimeKernelForks_snd_ι :
    (ofCoprimeKernelForks hab hX hc₁ hc₂).snd ≫ c₂.ι = (a * m) • 𝟙 X :=
  (KernelFork.IsLimit.lift' hc₂ _ _).2

/-- **An object killed by a product of coprime scalars is the biproduct of the two kernels.** If
`(m * n) • 𝟙 X = 0` and `a * m + b * n = 1`, then `X`, with the kernel inclusions of `m • 𝟙 X` and
`n • 𝟙 X` and the projections of `BinaryBicone.ofCoprimeKernelForks`, is a binary biproduct of the
two kernels. -/
noncomputable def BinaryBicone.isBilimitOfCoprimeKernelForks :
    (BinaryBicone.ofCoprimeKernelForks hab hX hc₁ hc₂).IsBilimit :=
  isBinaryBilimitOfTotal _ <| by
    -- The rewrites see through the reducible bicone: its inclusions are `c₁.ι` and `c₂.ι`.
    rw [ofCoprimeKernelForks_fst_ι, ofCoprimeKernelForks_snd_ι, ← add_smul, add_comm, hab,
      one_smul]

end CategoryTheory.Limits
