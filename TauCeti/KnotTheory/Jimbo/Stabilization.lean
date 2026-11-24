/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.StrandInclusion
import TauCeti.GroupTheory.SpecificGroups.Braid.HeckeSkein

/-!
# Markov stabilization of the Jimbo weighted trace

Adding a strand and a positive crossing multiplies the weighted trace by `q ^ N`;
a negative crossing multiplies it by `q ^ (-N)`. These identities hold over any
commutative ring with a unit parameter, including at `q = 1`, without dividing by
the quantum dimension or by `q - q⁻¹`.

The added strand keeps its colour under the included braid. Consequently, in the
diagonal coefficient of a stabilized braid, only the colour-preserving part of the
last crossing survives. The weighted partial trace of that crossing supplies the
stabilization factor. These are the two Markov laws needed for writhe normalization.
Together with the Hecke spanning decomposition of the braid group algebra, they also show
that the weighted trace of every nonempty braid is divisible by the quantum dimension
`∑ a : Fin N, jimboWeight q a` over any commutative ring and unit parameter
(`TauCeti.KnotTheory.sum_jimboWeight_dvd_jimboWeightedTrace`).

## References

* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553 (enhanced Yang-Baxter operators and their weighted traces).
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388.

We use the strand-inclusion coefficient formula and the two-colour partial trace
from the companion modules `StrandInclusion` and `Enhancement`.
-/

public section

open Function Finsupp
open scoped BigOperators

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {N n : ℕ}

private theorem stabilized_diagonal (q : Rˣ) (b : BraidGroup (n + 1))
    (w : Fin (n + 1) → Fin N) (c : Fin N) :
    (jimbo (Fin N) q (BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)) :
        Module.End R ((Fin (n + 2) → Fin N) →₀ R))
        (single (Fin.snoc w c) 1) (Fin.snoc w c) =
      (jimbo (Fin N) q b : Module.End R ((Fin (n + 1) → Fin N) →₀ R))
        (single w 1) w *
      (jimboGenerator q (0 : Fin 2) 1 (single ![w (Fin.last n), c] 1))
        ![w (Fin.last n), c] := by
  classical
  have hj : BraidGroup.strand (Fin.last n) = (Fin.last n).castSucc := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.last n) = Fin.last (n + 1) := Fin.ext (by simp)
  have hswap : Fin.snoc w c ∘ Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1)) =
      Fin.snoc (update w (Fin.last n) c) (w (Fin.last n)) := by
    rw [Equiv.comp_swap_eq_update]
    simp [← Fin.snoc_update, Fin.update_snoc_last]
  have hswap₂ : (![w (Fin.last n), c] : Fin 2 → Fin N) ∘ Equiv.swap 0 1 =
      ![c, w (Fin.last n)] := by
    ext i; fin_cases i <;> simp
  simp only [map_mul, Units.val_mul, mul_apply_eq_comp, jimbo_sigma, jimboUnit_val,
    hj, hk, jimboGenerator_single_one, Fin.snoc_castSucc, Fin.snoc_last,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hpair : (![c, w (Fin.last n)] : Fin 2 → Fin N) = ![w (Fin.last n), c] ↔
      w (Fin.last n) = c := by
    simp [funext_iff, Fin.forall_fin_two, eq_comm]
  rcases lt_trichotomy (w (Fin.last n)) c with h | h | h
  · simp only [h.ne, h, ↓reduceIte, hswap, hswap₂,
      jimbo_strandIncl_single_snoc_apply_snoc, single_apply, hpair, mul_zero]
  · simp only [h, ↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      jimbo_strandIncl_single_snoc_apply_snoc, single_eq_same, mul_one, mul_comm]
  · simp only [h.ne.symm, h.not_gt, ↓reduceIte, hswap, hswap₂, map_add, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, jimbo_strandIncl_single_snoc_apply_snoc,
      single_apply, hpair, zero_add, mul_one, mul_comm]

/-- Positive Markov stabilization multiplies the weighted trace by `q ^ N`. -/
@[simp]
theorem jimboWeightedTrace_stabilize (q : Rˣ) (b : BraidGroup (n + 1)) :
    jimboWeightedTrace (N := N) q
        (BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)) =
      ↑(q ^ N) * jimboWeightedTrace (N := N) q b := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 2) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, stabilized_diagonal]
  have hweight (w : Fin (n + 1) → Fin N) (c : Fin N) :
      (∏ i : Fin (n + 2), jimboWeight q ((Fin.snoc w c : Fin (n + 2) → Fin N) i)) =
        (∏ i, jimboWeight q (w i)) * jimboWeight q c := by
    rw [Fin.prod_univ_castSucc]
    simp
  simp only [hweight]
  rw [Finset.sum_comm, jimboWeightedTrace_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  calc
    _ = ((jimbo (Fin N) q b : Module.End R ((Fin (n + 1) → Fin N) →₀ R))
          (single w 1) w * ∏ i, jimboWeight q (w i)) *
        (∑ c : Fin N,
          (jimboGenerator q (0 : Fin 2) 1 (single ![w (Fin.last n), c] 1))
            ![w (Fin.last n), c] * jimboWeight q c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by rw [sum_jimboGenerator_coeff_mul_weight, ite_eq_left rfl]; ring

/-- Negative Markov stabilization multiplies the weighted trace by `q ^ (-N)`. -/
@[simp]
theorem jimboWeightedTrace_stabilizeInv (q : Rˣ) (b : BraidGroup (n + 1)) :
    jimboWeightedTrace (N := N) q
        (BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹) =
      ↑((q⁻¹) ^ N) * jimboWeightedTrace (N := N) q b := by
  have h := jimboWeightedTrace_skein (N := N) q (BraidGroup.strandIncl b) 1 (Fin.last n)
  simp only [mul_one, jimboWeightedTrace_stabilize, jimboWeightedTrace_strandIncl] at h
  have hs := jimboWeight_sum (N := N) q
  linear_combination -h - jimboWeightedTrace (N := N) q b * hs

/-- Over any commutative ring `R` and at any unit parameter `q : Rˣ`, the unnormalized weighted
Jimbo trace of a nonempty braid is divisible by the quantum dimension `[N]_q`. -/
theorem sum_jimboWeight_dvd_jimboWeightedTrace (q : Rˣ) (b : BraidGroup (n + 1)) :
    (∑ a : Fin N, jimboWeight q a) ∣ jimboWeightedTrace (N := N) q b := by
  let δ : R := ∑ a : Fin N, jimboWeight q a
  let z : R := (q : R) - ↑q⁻¹
  induction n with
  | zero =>
    rw [BraidGroup.eq_one_of_le_one le_rfl b, jimboWeightedTrace_one, pow_one]
  | succ m ih =>
    let φ : MonoidAlgebra R (BraidGroup (m + 2)) →ₗ[R] R :=
      Finsupp.linearCombination R (jimboWeightedTrace (N := N) q) ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
    have hφ (g : BraidGroup (m + 2)) (r : R) :
        φ (MonoidAlgebra.single g r) = r * jimboWeightedTrace (N := N) q g := by
      simp [φ, MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single]
    have hle : BraidGroup.strandSpan R m ⊔ BraidGroup.heckeSkein R z (m + 2) ≤
        Submodule.comap φ (Ideal.span {δ}) := by
      refine sup_le ((BraidGroup.strandSpan_le_iff _).mpr ⟨fun d ↦ ?_, fun d e ↦ ?_⟩)
        ((BraidGroup.heckeSkein_le_iff _ _).mpr fun b c i ↦ ?_) <;>
        simp only [Submodule.mem_comap, Ideal.mem_span_singleton]
      · rw [hφ, one_mul, jimboWeightedTrace_strandIncl]
        exact dvd_mul_left δ _
      · rw [hφ, one_mul, jimboWeightedTrace_mul_comm, ← mul_assoc, ← map_mul,
          jimboWeightedTrace_stabilize]
        exact dvd_mul_of_dvd_right (ih (e * d)) _
      · rw [BraidGroup.heckeRelator_def, map_sub, map_sub, hφ, hφ, hφ,
          one_mul, one_mul, jimboWeightedTrace_skein]
        simp [z]
    rw [BraidGroup.strandSpan_sup_heckeSkein_eq_top, top_le_iff] at hle
    have hb : MonoidAlgebra.single b 1 ∈ Submodule.comap φ (Ideal.span {δ}) :=
      hle ▸ Submodule.mem_top
    simpa only [Submodule.mem_comap, Ideal.mem_span_singleton, hφ, one_mul] using hb

end TauCeti.KnotTheory
