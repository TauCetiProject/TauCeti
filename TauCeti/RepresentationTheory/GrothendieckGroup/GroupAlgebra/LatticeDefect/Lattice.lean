/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Finite
public import TauCeti.Algebra.Module.QuotSMulTop
public import TauCeti.RepresentationTheory.Lattice
public import TauCeti.Algebra.GroupAction.QuotientAddGroup

/-!
# Reduction classes of integral lattices

For a finitely generated torsion-free abelian group with a distributive monoid action, the
lattice defect in characteristic `ℓ` is its reduction class. Consequently an equivariant
inclusion with finite cokernel preserves that class. This comparison uses exact Grothendieck
classes: the reduced representations need not be isomorphic.

The proofs use the additive lattice defect and its vanishing on finite modules, together with
the fact that quotienting by `ℓ` before extending scalars to characteristic `ℓ` does not change
the resulting representation. Clearing denominators using
`TauCeti.exists_injective_finite_quotient_range_of_nonempty_equiv` then shows that integral
lattices with isomorphic rationalizations have the same reduction class over every field.
In characteristic zero the two maps supplied by
`Representation.Equiv.exists_intertwiningMap_comp_eq_smul` become inverse after dividing by
their nonzero integer scalar.

## Main results

* `TauCeti.latticeDefect_eq_reductionK0_of_subsingleton_torsionBy`: when the scalar torsion is
  trivial, the defect equals the reduction class.
* `TauCeti.reductionK0_eq_of_injective_of_finite_quotient_range`: finite-index inclusions preserve
  reduction classes in prime characteristic.
* `TauCeti.reductionK0_eq_of_nonempty_equiv_baseChange_rat`: isomorphic rationalizations give
  equal reduction classes over every field.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Section VII.3, (7.3.3).
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, Chapter I, Lemma 2.12.
-/

public section

namespace TauCeti

open Function TensorProduct
open scoped MonoidAlgebra Pointwise

attribute [local instance high] Submodule.module Submodule.Quotient.module TensorProduct.instModule

universe u

section ScalarCharacteristic

variable (k G : Type u) [CommRing k] [Monoid G] (ℓ : ℕ) [NeZero ℓ]

/-- For a finitely generated integral module with trivial `ℓ`-torsion, the lattice defect is
its reduction class over a coefficient ring in which `ℓ` vanishes. -/
@[simp]
theorem latticeDefect_eq_reductionK0_of_subsingleton_torsionBy (V : Type u)
    [AddCommGroup V] [DistribMulAction G V] [Module.Finite ℤ V]
    [Subsingleton (Submodule.torsionBy ℤ V ℓ)] (hℓ : (ℓ : k) = 0) :
    latticeDefect k G ℓ V = reductionK0 k (Representation.ofDistribMulAction ℤ G V) := by
  rw [latticeDefect_def,
    reductionK0_eq_zero_of_subsingleton k
      ((Representation.ofDistribMulAction ℤ G V).torsionBy (ℓ : ℤ)), sub_zero,
    reductionK0_quotSMulTop k _ (ℓ : ℤ) (by simpa using hℓ)]

end ScalarCharacteristic

section PrimeCharacteristic

variable (k G : Type u) [CommRing k] [Monoid G] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]

include ℓ

/-- An injective equivariant map with finite cokernel between finitely generated integral
modules with trivial `ℓ`-torsion identifies their reduction classes in characteristic `ℓ`. -/
theorem reductionK0_eq_of_injective_of_finite_quotient_range {V W : Type u}
    [AddCommGroup V] [DistribMulAction G V] [Module.Finite ℤ V]
    [Subsingleton (Submodule.torsionBy ℤ V ℓ)]
    [AddCommGroup W] [DistribMulAction G W] [Module.Finite ℤ W]
    [Subsingleton (Submodule.torsionBy ℤ W ℓ)]
    (f : V →+[G] W) (hf : Injective f) (hfin : Finite (W ⧸ (f : V →+ W).range)) :
    reductionK0 k (Representation.ofDistribMulAction ℤ G V) =
      reductionK0 k (Representation.ofDistribMulAction ℤ G W) := by
  let N := (f : V →+ W).range
  have hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N := fun g x hx ↦ by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨g • y, map_smul f g y⟩
  let : DistribMulAction G (W ⧸ N) := N.quotientDistribMulAction hN
  let q : W →+[G] (W ⧸ N) :=
    { QuotientAddGroup.mk' N with
      map_smul' := fun g x ↦ (N.quotientDistribMulAction_smul_mk hN g x).symm }
  have hex : Exact f q := AddMonoidHom.exact_iff.mpr (QuotientAddGroup.ker_mk' N)
  rw [← latticeDefect_eq_reductionK0_of_subsingleton_torsionBy k G ℓ V (by simp),
    ← latticeDefect_eq_reductionK0_of_subsingleton_torsionBy k G ℓ W (by simp)]
  exact latticeDefect_eq_of_exact_of_finite k G ℓ f q hf hex
    (QuotientAddGroup.mk'_surjective N)

/-- Integral lattices with equivalent rationalizations have equal reduction classes in prime
characteristic. Their reductions themselves need not be equivalent representations. -/
theorem reductionK0_eq_of_nonempty_equiv_baseChange_rat_of_prime_char {V W : Type u}
    [AddCommGroup V] [DistribMulAction G V] [Module.Finite ℤ V] [Module.IsTorsionFree ℤ V]
    [AddCommGroup W] [DistribMulAction G W] [Module.Finite ℤ W] [Module.IsTorsionFree ℤ W]
    (h : Nonempty ((Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G V)).Equiv
      (Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G W)))) :
    reductionK0 k (Representation.ofDistribMulAction ℤ G V) =
      reductionK0 k (Representation.ofDistribMulAction ℤ G W) := by
  obtain ⟨f, hf, hfin⟩ := exists_injective_finite_quotient_range_of_nonempty_equiv h
  exact reductionK0_eq_of_injective_of_finite_quotient_range k G ℓ f hf hfin

end PrimeCharacteristic

section Field

variable (k G : Type u) [Field k] [Monoid G]
  {V W : Type u}
  [AddCommGroup V] [DistribMulAction G V] [Module.Finite ℤ V] [Module.IsTorsionFree ℤ V]
  [AddCommGroup W] [DistribMulAction G W] [Module.Finite ℤ W] [Module.IsTorsionFree ℤ W]

-- In characteristic zero the maps obtained by clearing denominators become inverse after
-- dividing by their nonzero integer scalar. No semisimplicity or finiteness of `G` is needed.
private theorem reductionK0_eq_of_nonempty_equiv_baseChange_rat_of_charZero [CharZero k]
    (h : Nonempty ((Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G V)).Equiv
      (Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G W)))) :
    reductionK0 k (Representation.ofDistribMulAction ℤ G V) =
      reductionK0 k (Representation.ofDistribMulAction ℤ G W) := by
  obtain ⟨e⟩ := h
  obtain ⟨f, f', s, hf'f, hff'⟩ := e.exists_intertwiningMap_comp_eq_smul (nonZeroDivisors ℤ)
    (fun s ↦ .of_ne_zero (nonZeroDivisors.coe_ne_zero s))
    fun s ↦ .of_ne_zero (nonZeroDivisors.coe_ne_zero s)
  have hs : ((s : ℤ) : k) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.coe_ne_zero s)
  obtain ⟨e'⟩ := nonempty_equiv_baseChange_of_comp_eq_smul
    (A := k) f f' (s : ℤ) hf'f hff' (isUnit_iff_ne_zero.mpr hs)
  exact reductionK0_congr_baseChange k e'

/-- Integral lattices with equivalent rationalizations have equal reduction classes over every
field, even when the reduced representations are not equivalent. -/
theorem reductionK0_eq_of_nonempty_equiv_baseChange_rat
    (h : Nonempty ((Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G V)).Equiv
      (Representation.baseChange ℚ (Representation.ofDistribMulAction ℤ G W)))) :
    reductionK0 k (Representation.ofDistribMulAction ℤ G V) =
      reductionK0 k (Representation.ofDistribMulAction ℤ G W) := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists k
  let : CharP k ℓ := hℓ
  rcases CharP.char_is_prime_or_zero k ℓ with hp | rfl
  · let : Fact ℓ.Prime := ⟨hp⟩
    exact reductionK0_eq_of_nonempty_equiv_baseChange_rat_of_prime_char k G ℓ h
  · let : CharZero k := CharP.charP_to_charZero k
    exact reductionK0_eq_of_nonempty_equiv_baseChange_rat_of_charZero k G h

end Field

end TauCeti
