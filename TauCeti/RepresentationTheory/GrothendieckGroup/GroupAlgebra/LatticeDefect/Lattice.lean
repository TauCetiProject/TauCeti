/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Finite
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.Basic
public import TauCeti.RepresentationTheory.Lattice

/-!
# The lattice defect of a lattice

Let `k` be a commutative ring of characteristic `ℓ` and `G` a monoid. For a `G`-module `V` which
is finitely generated and has no `ℓ`-torsion, such as a `G`-stable lattice, the lattice defect
`[k ⊗_ℤ (V ⧸ ℓV)] - [k ⊗_ℤ V[ℓ]]` is the reduction class `[k ⊗_ℤ V]`
(`TauCeti.latticeDefect_eq_reductionK0`): the torsion term vanishes, and since `ℓ = 0` in `k`, the
reduction of the quotient map `V → V ⧸ ℓV` is an isomorphism `k ⊗_ℤ V ≅ k ⊗_ℤ (V ⧸ ℓV)`.

For the permutation lattice `ℤ[X] = X →₀ ℤ` of a finite `G`-set `X`, whose reduction is the
permutation representation `k[X]` (`TauCeti.baseChangeComapEquiv`), so its reduction class is the
permutation class (`TauCeti.reductionK0_finsupp_int`), and this gives
`latticeDefect ℤ[X] = [k[X]]` (`TauCeti.latticeDefect_finsupp_int`).

Two lattices `V` and `W` with equivalent rationalizations `ℚ ⊗_ℤ V ≅ ℚ ⊗_ℤ W` have the same
reduction class over every field `k`
(`TauCeti.reductionK0_eq_of_nonempty_equiv_baseChange_rat`), although their reductions need not
be isomorphic: for `G` of order `2`, the permutation lattice `ℤ[G]` and the
lattice `ℤ ⊕ ℤ(-1)` have isomorphic rationalizations, but modulo `2` the first reduces to the
indecomposable `𝔽₂[G]` and the second to two trivial lines. Clearing denominators in a rational
equivalence gives equivariant maps `f : V → W` and `f' : W → V` whose composites are
multiplication by a nonzero integer `s`
(`Representation.Equiv.exists_intertwiningMap_comp_eq_smul`). In characteristic zero `s` is
invertible in `k`, so `f` reduces to an isomorphism. In characteristic `ℓ`, `f` is injective with
finite cokernel, so the two lattices have the same lattice defect
(`TauCeti.latticeDefect_eq_of_finiteIndex`), which is their reduction class.

## Main results

* `TauCeti.latticeDefect_eq_reductionK0`: the defect of a lattice is its reduction class.
* `TauCeti.reductionK0_finsupp_int`: the reduction class of the permutation lattice `ℤ[X]` is the
  permutation class `[k[X]]`.
* `TauCeti.latticeDefect_finsupp_int`: the defect of the permutation lattice `ℤ[X]` is the
  permutation class `[k[X]]`.
* `TauCeti.reductionK0_eq_of_nonempty_equiv_baseChange_rat_of_charP` and
  `TauCeti.reductionK0_eq_of_nonempty_equiv_baseChange_rat`: lattices with equivalent
  rationalizations have the same reduction class, in characteristic `ℓ` over any commutative ring,
  and over every field.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (2006), Chapter I, Lemma 2.12, the same
  statement for finitely generated `ℤ_p[G]`-modules with isomorphic `ℚ_p`-rationalizations.
-/

public section

open scoped TensorProduct

namespace TauCeti

attribute [local instance high] Submodule.module Submodule.Quotient.module TensorProduct.instModule

universe u

section CommRing

variable (k G : Type u) [CommRing k] [Monoid G] (ℓ : ℕ)

/-- **The lattice defect of a lattice is its reduction class**: in characteristic `ℓ`, a `G`-module
`V` with `V ⧸ ℓV` finite and without `ℓ`-torsion has defect `[k ⊗_ℤ V]`. Since `ℓ = 0` in `k`, the
reduction of `V ⧸ ℓV` is that of `V` (`TauCeti.reductionK0_quotSMulTop`). -/
theorem latticeDefect_eq_reductionK0 [CharP k ℓ] (V : Type u) [AddCommGroup V]
    [DistribMulAction G V] [Finite (QuotSMulTop (ℓ : ℤ) V)]
    [Subsingleton (Submodule.torsionBy ℤ V ℓ)] :
    haveI := finite_baseChange_of_finite_quotSMulTop k ℓ V
    latticeDefect k G ℓ V = reductionK0 k (Representation.ofDistribMulAction ℤ G V) := by
  have := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) V)
  let ρ := Representation.ofDistribMulAction ℤ G V
  rw [latticeDefect_def, reductionK0_eq_zero_of_subsingleton k (ρ.torsionBy ℓ), sub_zero,
    reductionK0_quotSMulTop k ℓ]

/-- **Lattices with equivalent rationalizations have the same reduction class** in
characteristic `ℓ`: for finitely generated torsion-free `G`-modules `V` and `W` with
`ℚ ⊗_ℤ V ≅ ℚ ⊗_ℤ W`, the classes `[k ⊗_ℤ V]` and `[k ⊗_ℤ W]` agree. The reductions themselves need
not be isomorphic. -/
theorem reductionK0_eq_of_nonempty_equiv_baseChange_rat_of_charP
    [Fact ℓ.Prime] [CharP k ℓ] (V W : Type u)
    [AddCommGroup V] [DistribMulAction G V] [Module.Finite ℤ V] [IsAddTorsionFree V]
    [AddCommGroup W] [DistribMulAction G W] [Module.Finite ℤ W] [IsAddTorsionFree W]
    (h : Nonempty ((Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G V)).Equiv
      (Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G W)))) :
    reductionK0 k (Representation.ofDistribMulAction ℤ G V) =
      reductionK0 k (Representation.ofDistribMulAction ℤ G W) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨f, hf, hfin⟩ := h.some.exists_injective_finite_quotient_range
  let g : V →+[G] W :=
    { f.toLinearMap.toAddMonoidHom with
      map_smul' := fun a v ↦ Representation.IntertwiningMap.isIntertwining _ _ f a v }
  have : Finite (W ⧸ (g : V →+ W).range) := hfin
  have : (g : V →+ W).range.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  rw [← latticeDefect_eq_reductionK0 k G ℓ V, ← latticeDefect_eq_reductionK0 k G ℓ W]
  exact latticeDefect_eq_of_finiteIndex k G ℓ g hf

section Permutation

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction Finsupp.comapDistribMulAction
  comapSMulCommClass

/-- **The reduction class of a permutation lattice** `ℤ[X] = X →₀ ℤ`, on which `G` acts by
pushing the support forward (`Finsupp.comapDistribMulAction`), is the permutation class `[k[X]]`. -/
theorem reductionK0_finsupp_int (X : Type u) [MulAction G X] [Finite X] :
    reductionK0 k (Representation.ofDistribMulAction ℤ G (X →₀ ℤ)) = permK0 k G X := by
  rw [reductionK0_def, permK0_eq_of_equiv k X _ (baseChangeComapEquiv ℤ k G X).symm]

/-- **The lattice defect of a permutation lattice** `ℤ[X] = X →₀ ℤ`, on which `G` acts by pushing
the support forward (`Finsupp.comapDistribMulAction`), is the permutation class `[k[X]]` in
characteristic `ℓ ≠ 0`. -/
theorem latticeDefect_finsupp_int [CharP k ℓ] [NeZero ℓ] (X : Type u) [MulAction G X] [Finite X] :
    latticeDefect k G ℓ (X →₀ ℤ) = permK0 k G X := by
  rw [latticeDefect_eq_reductionK0, reductionK0_finsupp_int]

end Permutation

end CommRing

variable (k G : Type u) [Field k] [Monoid G]

/-- **Lattices with equivalent rationalizations have the same reduction class**, over every field
`k`: for finitely generated torsion-free `G`-modules `V` and `W` with `ℚ ⊗_ℤ V ≅ ℚ ⊗_ℤ W`, the
classes `[k ⊗_ℤ V]` and `[k ⊗_ℤ W]` in `G₀(k[G])` agree. In characteristic zero the reductions are
isomorphic; in characteristic `ℓ` they need not be. -/
theorem reductionK0_eq_of_nonempty_equiv_baseChange_rat (V W : Type u)
    [AddCommGroup V] [DistribMulAction G V] [Module.Finite ℤ V] [IsAddTorsionFree V]
    [AddCommGroup W] [DistribMulAction G W] [Module.Finite ℤ W] [IsAddTorsionFree W]
    (h : Nonempty ((Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G V)).Equiv
      (Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G W)))) :
    reductionK0 k (Representation.ofDistribMulAction ℤ G V) =
      reductionK0 k (Representation.ofDistribMulAction ℤ G W) := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k ℓ with hp | rfl
  · have := Fact.mk hp
    exact reductionK0_eq_of_nonempty_equiv_baseChange_rat_of_charP k G ℓ V W h
  have := (CharP.charP_zero_iff_charZero k).mp hℓ
  -- Clear denominators: `f' ∘ f` and `f ∘ f'` are multiplication by a nonzero integer `s`.
  obtain ⟨e⟩ := h
  obtain ⟨f, f', s, hf'f, hff'⟩ := e.exists_intertwiningMap_comp_eq_smul (nonZeroDivisors ℤ)
    (fun s ↦ .of_ne_zero (nonZeroDivisors.coe_ne_zero s))
    fun s ↦ .of_ne_zero (nonZeroDivisors.coe_ne_zero s)
  -- After base change to `k`, multiplication by `s` is invertible, so `f` becomes bijective.
  have hs : IsUnit ((s : ℤ) : k) :=
    (Int.cast_ne_zero.mpr (nonZeroDivisors.coe_ne_zero s)).isUnit
  have hbij := Representation.IntertwiningMap.baseChange_bijective_of_comp_eq_smul
    hf'f hff' k hs hs
  exact reductionK0_congr_baseChange k ((f.baseChange k).ofBijective hbij)

end TauCeti
