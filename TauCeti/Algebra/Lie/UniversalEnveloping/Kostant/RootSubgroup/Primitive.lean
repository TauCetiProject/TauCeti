/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.Algebra.Module.Primitive.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TauCeti.Algebra.Lie.Sl2.Spectrum
import TauCeti.Algebra.Lie.Sl2.Straightening
import TauCeti.Algebra.Module.Primitive.Submodule

/-!
# Primitive images of Kostant root operators in `sl₂` triples

Let `M ≤ V` be a Kostant-stable integral lattice with an integral basis `b` spanning `V` over
`ℚ`. Whenever two root generators `e i` and `e opp` act on `V` as the raising and lowering elements
of an `sl₂` triple `(H, ρ(e i), ρ(e opp))` whose Cartan operator `H` acts diagonally on `b` with
bounded integral eigenvalues, the integral root operator
`kostantRootOperator e h ρ M hM i : M →ₗ[ℤ] M` has a primitive vector in its image.

This holds for every Kostant-stable weight lattice with bounded weights without any restriction on
rank, root-string length, or fundamental-weight summands, including adjoint lattices where no
primitive image vector lies in a two-step root string. It provides the lattice-primitivity input
for closed-immersion and parameter-faithfulness theorems on Chevalley root subgroups across all
isogeny types.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.exists_isPrimitive_kostantRootOperator_of_isSl2Triple`:
  integral root-operator primitivity for any Kostant-stable weight lattice with bounded integral
  weights carrying an `sl₂` triple.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§7.2 and 27.1.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Associative

section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

/-- Internal helper for `exists_isPrimitive_kostantRootOperator_of_isSl2Triple`: produces a nonzero
power of `kostantRootOperator` hitting `N! • b j` for a positive-weight primitive basis vector
`b j`. Kept private because its return shape is tailored to the prime-adic factorial argument
below. -/
private theorem exists_pow_kostantRootOperator_eq_factorial_smul
    {L ι κ V η : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
    (e : ι → L) (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
    (b : Module.Basis η ℤ M) (hspan : Submodule.span ℚ (Set.range fun r => (b r : V)) = ⊤)
    {i opp : ι} {H : Module.End ℚ V}
    (hsl2 : IsSl2Triple H (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))))
    {wt : η → ℤ} (hwt : ∀ r, H (b r : V) = (wt r : ℚ) • (b r : V))
    (hbdd_below : BddBelow (Set.range wt)) (hbdd_above : BddAbove (Set.range wt)) :
    ∃ (j : η) (N : ℕ) (m₀ : M),
      N ≠ 0 ∧ (kostantRootOperator e h ρ M hM i ^ N) m₀ = N.factorial • b j := by
  let E := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
  let F := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))
  let op := kostantRootOperator e h ρ M hM i
  obtain ⟨j, hjpos, hP⟩ :=
    hsl2.exists_pos_weight_and_hasPrimitiveVectorWith_of_span_eq_top hspan
      (fun h0 => hsl2.h_ne_zero (LinearMap.ext fun x => congrArg (· x) h0))
      hwt hbdd_below hbdd_above
  have hEj : E (b j : V) = 0 := hP.lie_e
  let N : ℕ := (wt j).toNat
  have hN_eq : (N : ℤ) = wt j := Int.toNat_of_nonneg hjpos.le
  let m₀ : M := ⟨(dividedPower N F) (b j : V),
    dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM opp N (b j).property⟩
  have hcoe_pow (k : ℕ) (x : M) : (((op ^ k) x : M) : V) = (E ^ k) (x : V) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp,
        coe_kostantRootOperator_apply, ih]
  refine ⟨j, N, m₀, by omega, Subtype.ext ?_⟩
  rw [hcoe_pow, AddSubgroupClass.coe_nsmul]
  have hdiv :
      (E ^ N) (m₀ : V) = N.factorial • ((dividedPower N E) ((dividedPower N F) (b j : V))) := by
    rw [dividedPower_def, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_inv_smul₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))]
  rw [hdiv, TauCeti.Sl2.dividedPower_e_apply_dividedPower_f_apply_eq_self_of_eq_zero
    hsl2.lie_e_f hsl2.lie_h_f_nsmul hEj
    (by rw [hwt j, ← hN_eq, Int.cast_natCast])]

/-- If `e i` and `e opp` act on a Kostant-stable lattice `M` with spanning basis `b` as the
raising and lowering elements of an `sl₂` triple `(H, ρ(e i), ρ(e opp))` whose Cartan operator `H`
acts diagonally on `b` with bounded integral eigenvalues, then `kostantRootOperator e h ρ M hM i`
has a primitive vector in its image. -/
theorem exists_isPrimitive_kostantRootOperator_of_isSl2Triple
    {L ι κ V η : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
    (e : ι → L) (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
    (b : Module.Basis η ℤ M) (hspan : Submodule.span ℚ (Set.range fun r => (b r : V)) = ⊤)
    {i opp : ι} {H : Module.End ℚ V}
    (hsl2 : IsSl2Triple H (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))))
    {wt : η → ℤ} (hwt : ∀ r, H (b r : V) = (wt r : ℚ) • (b r : V))
    (hbdd_below : BddBelow (Set.range wt)) (hbdd_above : BddAbove (Set.range wt)) :
    ∃ m : M, IsPrimitive (kostantRootOperator e h ρ M hM i m) := by
  let : Module.Free ℤ M := Module.Free.of_basis b
  obtain ⟨j, N, m₀, hN_ne, hopN⟩ :=
    exists_pow_kostantRootOperator_eq_factorial_smul e h ρ M hM b hspan hsl2 hwt
      hbdd_below hbdd_above
  set op := kostantRootOperator e h ρ M hM i
  refine op.exists_isPrimitive_apply_iff.mpr fun p hp => ?_
  by_contra! hdiv
  have hpow_div (k : ℕ) : ∃ w : M, (p ^ k) • w = (op ^ k) m₀ := by
    induction k with
    | zero => exact ⟨m₀, by simp⟩
    | succ k ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨u, hu⟩ := hdiv w
      exact ⟨u, by
        rw [pow_succ, mul_smul, hu, ← map_nsmul, hw, pow_succ', mul_apply_eq_comp]⟩
  obtain ⟨w, hw⟩ := hpow_div N
  rw [hopN] at hw
  have hc := congrArg (b.coord j) hw
  simp only [map_nsmul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, nsmul_eq_mul, mul_one] at hc
  have hdvd : p ^ N ∣ N.factorial :=
    Int.natCast_dvd_natCast.mp ⟨b.coord j w, by exact_mod_cast hc.symm⟩
  have : Fact p.Prime := ⟨hp⟩
  exact absurd ((Nat.pow_dvd_iff_le_multiplicity hp.ne_one (Nat.factorial_ne_zero N)).mp hdvd)
    (not_le_of_gt (multiplicity_factorial_lt_of_ne_zero p hN_ne))

end

end TauCeti.UniversalEnvelopingAlgebra
