/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Finite
public import TauCeti.Algebra.Module.QuotSMulTop
public import TauCeti.Algebra.Module.Torsion.Free
public import TauCeti.RepresentationTheory.Lattice

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

* `TauCeti.latticeDefect_eq_reductionK0`: the defect of an integral lattice in prime
  characteristic equals its reduction class.
* `TauCeti.reductionK0_eq_of_injective_of_finite_cokernel`: finite-index inclusions preserve
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

section PrimeCharacteristic

variable (k G : Type u) [CommRing k] [Monoid G] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]

include ℓ

/-- For a finitely generated torsion-free integral module, the lattice defect is the class of
its scalar extension to characteristic `ℓ`. -/
@[simp]
theorem latticeDefect_eq_reductionK0 (V : Type u) [AddCommGroup V] [DistribMulAction G V]
    [Module.Finite ℤ V] [Module.IsTorsionFree ℤ V] :
    latticeDefect k G ℓ V = reductionK0 k (Representation.ofDistribMulAction ℤ G V) := by
  rw [latticeDefect_def,
    reductionK0_eq_zero_of_subsingleton k
      ((Representation.ofDistribMulAction ℤ G V).torsionBy (ℓ : ℤ)), sub_zero,
    reductionK0_quotSMulTop k _ (ℓ : ℤ) (by simp)]

/-- An injective equivariant map with finite cokernel between finitely generated torsion-free
integral modules identifies their reduction classes in characteristic `ℓ`. -/
theorem reductionK0_eq_of_injective_of_finite_cokernel {V W : Type u}
    [AddCommGroup V] [DistribMulAction G V] [Module.Finite ℤ V] [Module.IsTorsionFree ℤ V]
    [AddCommGroup W] [DistribMulAction G W] [Module.Finite ℤ W] [Module.IsTorsionFree ℤ W]
    (f : V →+[G] W) (hf : Injective f)
    [Finite (W ⧸ f.toAddMonoidHom.toIntLinearMap.range)] :
    reductionK0 k (Representation.ofDistribMulAction ℤ G V) =
      reductionK0 k (Representation.ofDistribMulAction ℤ G W) := by
  let m := f.toAddMonoidHom.toIntLinearMap
  let σ := Representation.ofDistribMulAction ℤ G W
  let τ := σ.quotient m.range fun g x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨g • y, map_smul f g y⟩
  let : DistribMulAction G (W ⧸ m.range) := DistribMulAction.compHom _ τ
  let q : W →+[G] (W ⧸ m.range) :=
    { m.range.mkQ.toAddMonoidHom with
      map_smul' := fun g x => by
        change m.range.mkQ (σ g x) = τ g (m.range.mkQ x)
        -- The quotient representation is defined by the maps induced by `σ g`.
        rfl }
  have hex : Exact f q := LinearMap.exact_iff.mpr (Submodule.ker_mkQ m.range)
  rw [← latticeDefect_eq_reductionK0 k G ℓ V, ← latticeDefect_eq_reductionK0 k G ℓ W]
  exact latticeDefect_eq_of_exact_of_finite k G ℓ f q hf hex
    (Submodule.mkQ_surjective m.range)

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
  let : Finite (W ⧸ f.toAddMonoidHom.toIntLinearMap.range) := hfin
  exact reductionK0_eq_of_injective_of_finite_cokernel k G ℓ f hf

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
  have hcomp (x : k ⊗[ℤ] V) :
      f'.baseChange k (f.baseChange k x) = ((s : ℤ) : k) • x := by
    have hc : f'.toLinearMap ∘ₗ f.toLinearMap = (s : ℤ) • LinearMap.id :=
      LinearMap.ext hf'f
    change ((f'.baseChange k).toLinearMap ∘ₗ (f.baseChange k).toLinearMap) x = _
    rw [Representation.IntertwiningMap.toLinearMap_baseChange,
      Representation.IntertwiningMap.toLinearMap_baseChange,
      ← LinearMap.baseChange_comp, hc, LinearMap.baseChange_smul, LinearMap.baseChange_id,
      LinearMap.smul_apply, LinearMap.id_apply, ← IsScalarTower.algebraMap_smul k (s : ℤ) x]
    simp
  have hcomp' (x : k ⊗[ℤ] W) :
      f.baseChange k (f'.baseChange k x) = ((s : ℤ) : k) • x := by
    have hc : f.toLinearMap ∘ₗ f'.toLinearMap = (s : ℤ) • LinearMap.id :=
      LinearMap.ext hff'
    change ((f.baseChange k).toLinearMap ∘ₗ (f'.baseChange k).toLinearMap) x = _
    rw [Representation.IntertwiningMap.toLinearMap_baseChange,
      Representation.IntertwiningMap.toLinearMap_baseChange,
      ← LinearMap.baseChange_comp, hc, LinearMap.baseChange_smul, LinearMap.baseChange_id,
      LinearMap.smul_apply, LinearMap.id_apply, ← IsScalarTower.algebraMap_smul k (s : ℤ) x]
    simp
  have hf : Bijective (f.baseChange k) := by
    refine ⟨fun x y hxy ↦ (smul_right_injective _ hs) ?_, fun y ↦ ?_⟩
    · simpa only [hcomp] using congrArg (f'.baseChange k) hxy
    · refine ⟨((s : ℤ) : k)⁻¹ • f'.baseChange k y, ?_⟩
      rw [map_smul, hcomp', smul_smul, inv_mul_cancel₀ hs, one_smul]
  rw [reductionK0_def, reductionK0_def]
  apply ExactK0.of_congr
  exact (Representation.asModuleLinearEquivOfEquiv
    ((f.baseChange k).ofBijective hf)).toFGModuleCatIso

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
