/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.Algebra.Module.LinearMap.Iterate

/-!
# Semilinear endomorphisms of finite-dimensional spaces

An injective linear endomorphism of a finite-dimensional vector space is surjective
(`LinearMap.surjective_of_injective`). The same holds for an endomorphism that is semilinear with
respect to a surjective ring endomorphism `σ` of the scalars: such a map carries a basis to a
linearly independent family, so its range has full dimension. The main example is the Frobenius
of an isocrystal, which is semilinear with respect to an automorphism of the coefficient field.

If nonzero scalar difference operators are surjective, a linear dependence among iterates
transfers this solvability to the equation `Φ x - x = v` for semilinear endomorphisms.
-/

public section

namespace LinearMap

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {σ : K →+* K} [RingHomSurjective σ]

/-- An injective endomorphism of a finite-dimensional vector space that is semilinear with
respect to a surjective ring endomorphism of the scalars is surjective. -/
theorem surjective_of_injectiveₛₗ {f : V →ₛₗ[σ] V} (hf : Function.Injective f) :
    Function.Surjective f := by
  have hσ : Function.Bijective σ := ⟨σ.injective, RingHomSurjective.is_surjective⟩
  have hrank : Module.rank K V = Module.rank K (range f) :=
    rank_eq_of_equiv_equiv σ
      (AddEquiv.ofBijective f.rangeRestrict.toAddMonoidHom
        ⟨fun x y h => hf (congrArg Subtype.val h), f.surjective_rangeRestrict⟩)
      hσ fun r x => Subtype.ext (map_smulₛₗ f r x)
  rw [← range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (congrArg Cardinal.toNat hrank).symm

open Finset Function

/-- If every nonzero scalar difference operator for `σ` is surjective, then `Φ - 1` is
surjective for every finite-dimensional `σ`-semilinear endomorphism. -/
theorem surjective_sub_id_of_surjective_sum_mul_iterate {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (σ : K ≃+* K)
    (hσ : ∀ (s : Finset ℕ) (a : ℕ → K), (∃ i ∈ s, a i ≠ 0) →
      Surjective (fun x : K => ∑ i ∈ s, a i * σ^[i] x))
    (Φ : V →ₛₗ[(σ : K →+* K)] V) : Surjective (fun x => Φ x - x) := by
  classical
  intro v
  -- The first `finrank + 1` iterates of the target vector satisfy a nonzero relation.
  let n := Module.finrank K V
  let u (i : Fin (n + 1)) := Φ^[n - i.val] v
  have hu : ¬ LinearIndependent K u := by
    intro h
    simpa [n] using h.fintype_card_le_finrank
  obtain ⟨a, ha, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hu
  -- Untwist each relation coefficient by the corresponding Frobenius power.
  let c (i : Fin (n + 1)) := σ.symm^[n - i.val] (a i)
  have hinverse : LeftInverse σ σ.symm := σ.apply_symm_apply
  have hinv (i : Fin (n + 1)) : σ^[n - i.val] (c i) = a i := hinverse.iterate _ _
  let d (i : ℕ) := if hi : i < n + 1 then c ⟨i, hi⟩ else 0
  have hd : ∃ i ∈ Finset.range (n + 1), d i ≠ 0 := by
    refine ⟨i₀, Finset.mem_range.mpr i₀.isLt, ?_⟩
    simp only [d, i₀.isLt, dite_true, Fin.eta]
    intro hi
    apply hi₀
    rw [← hinv i₀, hi]
    exact iterate_fixed (map_zero σ) _
  obtain ⟨z, hz⟩ := hσ _ d hd (-1)
  let w (i : Fin (n + 1)) := (c i * σ^[i.val] z) • v
  have hsum : ∑ i, w i = -v := by
    have hz' : (∑ i : Fin (n + 1), c i * σ^[i.val] z) = -1 := by
      rw [sum_fin_eq_sum_range]
      refine (sum_congr rfl fun i hi => ?_).trans hz
      have hil : i < n + 1 := Finset.mem_range.mp hi
      simp only [d, dite_eq_left hil]
    simp only [w, ← sum_smul, hz', neg_one_smul]
  have hiter (i : Fin (n + 1)) :
      Φ^[n - i.val] (w i) = σ^[n] z • (a i • u i) := by
    rw [TauCeti.iterate_map_smulₛₗ Φ, RingEquiv.coe_toRingHom, iterate_map_mul, hinv,
      ← iterate_add_apply, Nat.sub_add_cancel (by omega : i.val ≤ n), smul_smul, mul_comm]
  -- The iterated terms sum to zero, and their starting terms sum to `-v`.
  refine ⟨∑ i : Fin (n + 1), ∑ j ∈ Finset.range (n - i.val), Φ^[j] (w i), ?_⟩
  dsimp only
  rw [map_sum, ← sum_sub_distrib]
  have htel (n : ℕ) (x : V) :
      Φ (∑ j ∈ Finset.range n, Φ^[j] x) - ∑ j ∈ Finset.range n, Φ^[j] x = Φ^[n] x - x := by
    simp only [map_sum, ← sum_sub_distrib, ← iterate_succ_apply']
    exact sum_range_sub (fun j => Φ^[j] x) n
  simp_rw [htel, hiter]
  rw [sum_sub_distrib, ← smul_sum, ha, smul_zero, hsum, zero_sub, neg_neg]

end LinearMap
