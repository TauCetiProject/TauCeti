/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.Pi

/-!
# Additive maps on integer lattices are bounded by the coordinates

Let `a : L →+ (ι → ℤ)` be an injective additive map from an abelian group `L` to the integer
vectors indexed by a finite type `ι`, so that `L` is a lattice with integer coordinates `a P i`.
Every additive map `φ : L →+ K` to a linearly ordered field is then bounded by the `ℓ¹`-norm of
the coordinates: `|φ P| ≤ C * ∑ i, |a P i|` for a constant `C` and all `P`
(`AddMonoidHom.exists_abs_le_mul_sum_abs`), with one constant for any finite family of such maps
(`AddMonoidHom.exists_forall_abs_le_mul_sum_abs`). In particular the sum `∑ i, |a P i|`, which is at
least one for `P ≠ 0`, controls every linear functional on `L` uniformly, including on elements
with arbitrarily large coordinates.

The proof extends `φ` along `a` to an additive map `ψ : (ι → ℤ) →+ K`, which is possible because
`K` is a divisible abelian group and hence an injective `ℤ`-module (Baer's criterion,
`Module.Baer.of_divisible`). Then `φ P = ∑ i, a P i • ψ (eᵢ)` for the standard basis vectors
`eᵢ`, and `C = ∑ i, |ψ (eᵢ)|` works.

This is the estimate used to compare the first Chern class pairing on the periodic domains of a
Heegaard diagram with the multiplicities of their boundaries along the attaching curves, in the
winding argument for admissibility (`TauCeti.LowDimTopology.Heegaard.Winding`).
-/

public section

namespace AddMonoidHom

/-- An additive map `φ` on an abelian group `L` with injective integer coordinates
`a : L →+ (ι → ℤ)` is bounded by the `ℓ¹`-norm of the coordinates: `|φ P| ≤ C * ∑ i, |a P i|`
for some constant `C` and all `P`. -/
theorem exists_abs_le_mul_sum_abs {L ι K : Type*} [AddCommGroup L] [Fintype ι] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (φ : L →+ K) {a : L →+ (ι → ℤ)}
    (ha : Function.Injective a) :
    ∃ C : K, ∀ P, |φ P| ≤ C * ∑ i, |(a P i : K)| := by
  classical
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible K).extension_property_addMonoidHom a ha φ
  set e : ι → K := fun i => ψ fun j => if i = j then 1 else 0
  refine ⟨∑ i, |e i|, fun P => ?_⟩
  have hφ : φ P = ∑ i, (a P i : K) * e i := by
    have h := LinearMap.pi_apply_eq_sum_univ ψ.toIntLinearMap (a P)
    simp only [coe_toIntLinearMap, zsmul_eq_mul] at h
    rw [← hψ, coe_comp, Function.comp_apply, h]
  rw [hφ, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun j => |e j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    (abs_nonneg _)

/-- A finite family of additive maps `φ k` on an abelian group `L` with injective integer
coordinates `a : L →+ (ι → ℤ)` is bounded by one multiple of the `ℓ¹`-norm of the coordinates:
`|φ k P| ≤ C * ∑ i, |a P i|` for some constant `C ≥ 0` and all `k` and `P`. -/
theorem exists_forall_abs_le_mul_sum_abs {L ι κ K : Type*} [AddCommGroup L] [Fintype ι]
    [Finite κ] [Field K] [LinearOrder K] [IsStrictOrderedRing K] (φ : κ → L →+ K)
    {a : L →+ (ι → ℤ)} (ha : Function.Injective a) :
    ∃ C : K, 0 ≤ C ∧ ∀ k P, |φ k P| ≤ C * ∑ i, |(a P i : K)| := by
  have := Fintype.ofFinite κ
  choose C hC using fun k => (φ k).exists_abs_le_mul_sum_abs ha
  refine ⟨∑ k, |C k|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun k P => (hC k P).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => abs_nonneg _))⟩
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k))

end AddMonoidHom
