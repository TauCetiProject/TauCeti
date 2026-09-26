/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Module
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CompactModule

/-!
# Abelian pro-`p` groups with a continuous action as modules over `ℤ_p[[Γ]]`

An abelian pro-`p` group `A` is a `ℤ_p`-module through the `p`-adic power
(`TauCeti.IsProP.module`), and with its topology it is a compact `ℤ_p`-module in the sense of
`TauCeti.IsCompactModule`. When a profinite group `Γ` acts continuously on `A` by group
automorphisms, the action is `ℤ_p`-linear, because a continuous homomorphism of pro-`p` groups
commutes with `p`-adic powers, so `A` is a compact `ℤ_p`-module with a continuous `Γ`-action and
the general construction of `TauCeti.IsCompactModule.completedGroupAlgebraModule` makes it a
topological module over the completed group algebra `ℤ_p[[Γ]]`, in which each `γ : Γ` acts as it
does on `A`.

This is the shape of Labute's relation module in the classification of Demushkin groups: for
`X` the kernel of the orientation character on a free pro-`p` group `F`, the topological
abelianization `E = X ⧸ (X, X)` is an abelian pro-`p` group on which `Γ = F ⧸ X` acts continuously
by conjugation, and the module structure over `Λ = ℤ_p[[Γ]]` used in his Theorems 5 and 6 is the
one constructed here (Labute, §4, p. 121).

## Main definitions

* `TauCeti.IsProP.completedGroupAlgebraModule`: the `ℤ_p[[Γ]]`-module structure on an abelian
  pro-`p` group with a continuous action of a profinite group `Γ`.

## Main results

* `TauCeti.IsProP.completedGroupAlgebraModule_of_smul`,
  `TauCeti.IsProP.isScalarTower_completedGroupAlgebraModule`,
  `TauCeti.IsProP.continuousSMul_completedGroupAlgebraModule`: the group elements act as `Γ`
  does, the structure extends the `ℤ_p`-module structure, and it is topological.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4, p. 121.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.3.
-/

public section

namespace TauCeti.IsProP

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A] [TotallyDisconnectedSpace A]

section Module

variable (Γ : Type*) [Group Γ] [MulDistribMulAction Γ A] [TopologicalSpace Γ] [CompactSpace Γ]
  [SeparatelyContinuousMul Γ] [ContinuousSMul Γ A]

/-- **An abelian pro-`p` group with a continuous action of a profinite group `Γ` is a module over
the completed group algebra `ℤ_p[[Γ]]`**, in which a group element acts as it does on the group
(`TauCeti.IsProP.completedGroupAlgebraModule_of_smul`). This is the general construction
`TauCeti.IsCompactModule.completedGroupAlgebraModule` for the compact `ℤ_p`-module
`TauCeti.IsProP.module`; the prime and the acting group are not determined by `A`, so it is a
definition rather than an instance, introduced with `letI := hA.completedGroupAlgebraModule Γ`. -/
@[instance_reducible]
noncomputable def completedGroupAlgebraModule (hA : IsProP p A) :
    Module (completedGroupAlgebra ℤ_[p] Γ) (Additive A) :=
  letI := hA.module
  letI := hA.smulCommClass_module (Γ := Γ)
  hA.isCompactModule.completedGroupAlgebraModule Γ

variable {Γ}

/-- **A group element acts as itself**: `of ℤ_[p] Γ γ • x = γ • x`. Not a simp lemma: `simp`
already proves it through `TauCeti.IsCompactModule.completedGroupAlgebraModule_smul` and
`TauCeti.IsCompactModule.completedSMul_of`, since the module structure is instance-reducible. -/
theorem completedGroupAlgebraModule_of_smul (hA : IsProP p A) (γ : Γ) (x : Additive A) :
    letI := hA.completedGroupAlgebraModule Γ
    completedGroupAlgebra.of ℤ_[p] Γ γ • x = γ • x :=
  letI := hA.module
  letI := hA.smulCommClass_module (Γ := Γ)
  (hA.isCompactModule.completedGroupAlgebraModule_smul _ _).trans
    (hA.isCompactModule.completedSMul_of γ x)

variable (Γ)

/-- The `ℤ_p[[Γ]]`-module structure extends the `ℤ_p`-module structure `TauCeti.IsProP.module`. -/
theorem isScalarTower_completedGroupAlgebraModule (hA : IsProP p A) :
    letI := hA.module
    letI := hA.completedGroupAlgebraModule Γ
    IsScalarTower ℤ_[p] (completedGroupAlgebra ℤ_[p] Γ) (Additive A) :=
  letI := hA.module
  letI := hA.smulCommClass_module (Γ := Γ)
  hA.isCompactModule.isScalarTower_completedGroupAlgebraModule

/-- The `ℤ_p[[Γ]]`-module structure on an abelian pro-`p` group is topological. -/
theorem continuousSMul_completedGroupAlgebraModule (hA : IsProP p A) :
    letI := hA.completedGroupAlgebraModule Γ
    ContinuousSMul (completedGroupAlgebra ℤ_[p] Γ) (Additive A) :=
  letI := hA.module
  letI := hA.smulCommClass_module (Γ := Γ)
  hA.isCompactModule.continuousSMul_completedGroupAlgebraModule

end Module

end TauCeti.IsProP
