/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.TwoEven.KernelSpan
public import TauCeti.Topology.Algebra.Group.Profinite.Free.SuccessiveApproximation.Basic

/-!
# Constrained approximation at the second dyadic even-rank normal form

Let `F` be the free pro-`2` group on an even number `n ≥ 4` of generators and let

`r_f = x₁² (x₁, x₂) x₃^(2^f) (x₃, x₄) ⋯ (x_{n-1}, x_n)`.

For the orientation with values `χ(x₂) = -1`, `χ(x₄) = (1 - 2^f)⁻¹`, and `1`
elsewhere, corrections are made inside the kernel of the exponent sum at `x₄`. Elements of this
kernel in the first term of the lower `2`-central series are killed by `χ`. Labute's constrained
span and graded-functional statements therefore feed the general successive-approximation theorem: a
relator with the same degree-one class as `r_f`, lying in that exponent-sum kernel and killed by
the coordinate crossed homomorphisms, is the image of `r_f` under an automorphism whose changes
of all the free generators stay in the exponent-sum kernel.

This is the limit step in the second even-rank family of Labute's classification, the family with
orientation image `{ ±1 } × U^(f)`. It turns the infinitesimal Lemmas 3 and 4 proved in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.TwoEven.KernelSpan` into an exact
equality of relators.

## Main result

* `exists_continuousMulEquiv_apply_demushkinWordTwoEven_zero_eq_of_isCrossedHom_eq_zero`:
  the constrained successive-approximation theorem at `r_f`.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  Lemmas 3–4 and the proof of Theorem 6.
-/

public section

namespace TauCeti.freeProP

open Subgroup

variable {n : ℕ} {χ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ}

/-- **Constrained successive approximation for the second dyadic even-rank family** (Labute,
§4, Lemmas 3–4 and Theorem 6). Let `n ≥ 4` be even, `f ≥ 2`, and let `χ` take the
normal-form
values `χ(x₂) = -1`, `χ(x₄)(1 - 2^f) = 1`, and `χ(x_i) = 1` otherwise. If a relator
`r` has the same class in `gr₁(F)` as
`w = x₁² (x₁, x₂) x₃^(2^f) (x₃, x₄) ⋯`, lies in the kernel of the exponent sum at
`x₄`, and is killed by every coordinate crossed homomorphism for `χ` except the one at `x₂`,
then an automorphism `e` of `F` carries `w` to `r`. Moreover every generator change
`x_i⁻¹ e(x_i)` lies in the kernel of the exponent sum at `x₄`.

The last clause records that the approximation preserves the orientation: an element of the
exponent-sum kernel which lies in `λ₁(F)` is killed by `χ` at these marked values. -/
theorem exists_continuousMulEquiv_apply_demushkinWordTwoEven_zero_eq_of_isCrossedHom_eq_zero
    (hn : Even n) (hn3 : 3 < n) {f : ℕ} (hf : 2 ≤ f)
    (h₁ : χ (of ⟨1, by omega⟩) = -1)
    (h₃ : (χ (of ⟨3, hn3⟩) : ℤ_[2]) * (1 - 2 ^ f) = 1)
    (hχ : ∀ j : Fin n, j ≠ ⟨1, by omega⟩ → j ≠ ⟨3, hn3⟩ → χ (of j) = 1)
    (r : pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1)
    (hρ : gradedMk 2 (freeProP 2 (Fin n)) 1
        ⟨demushkinWordTwoEven 0 f n (freeProPGen 2 n),
          demushkinWordTwoEven_mem_pLowerCentralSeries_one (dvd_zero 2) (by omega) n _⟩ =
      gradedMk 2 (freeProP 2 (Fin n)) 1 r)
    (hrX : (r : freeProP 2 (Fin n)) ∈ exponentSumKer 2 (Fin n) ⟨3, hn3⟩)
    (hrD : ∀ i : Fin n, i ≠ ⟨1, by omega⟩ →
      crossedHom χ (Pi.single i 1) r = 0) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      (∀ i, (of i)⁻¹ * e (of i) ∈ exponentSumKer 2 (Fin n) ⟨3, hn3⟩) ∧
        e (demushkinWordTwoEven 0 f n (freeProPGen 2 n)) = r := by
  classical
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₃ : Fin n := ⟨3, hn3⟩
  let w : pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 :=
    ⟨demushkinWordTwoEven 0 f n (freeProPGen 2 n),
      demushkinWordTwoEven_mem_pLowerCentralSeries_one (dvd_zero 2) (by omega) n _⟩
  let X := exponentSumKer 2 (Fin n) i₃
  let Z : Set (freeProP 2 (Fin n)) := {z | z ∈ X ∧
    ∀ i : Fin n, i ≠ i₁ → crossedHom χ (Pi.single i 1) z = 0}
  refine exists_continuousMulEquiv_apply_eq Z (fun _ ↦ X) (fun _ ↦ isClosed_exponentSumKer i₃)
    ?_ w r hρ ?_ ?_
  · intro ω hω _ c hc
    dsimp only [X] at hω hc ⊢
    rw [mem_exponentSumKer_iff] at hc ⊢
    rw [toAdd_exponentSum_basisModification, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [Pi.smul_apply, Pi.add_apply, mem_exponentSumKer_iff.mp (hω j), add_zero]
    by_cases hj : j = i₃
    · subst j
      simp [hc]
    · simp [hj]
  · intro φ hφ hφX
    dsimp only [X] at hφX
    let ωφ : Fin n → pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 := fun i ↦
        (⟨(of i)⁻¹ * φ (of i), hφ (of i)⟩ :
          pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1)
    have hφeq : φ = basisModification ωφ :=
      hom_ext fun i ↦ by rw [basisModification_of, mul_inv_cancel_left]
    have hωχ (j : Fin n) : χ (ωφ j) = 1 :=
      χ.apply_eq_one_of_mem_exponentSumKer_of_mem_pLowerCentralSeries_one
        (i := i₃) (fun k hk ↦ by
          by_cases hk₁ : k = i₁
          · rw [hk₁, h₁, neg_one_sq]
          · rw [hχ k hk₁ hk, one_pow]) (hφX j) (hφ (of j))
    have hφwX : φ w ∈ X := by
      rw [hφeq]
      exact (by
        rw [mem_exponentSumKer_iff, toAdd_exponentSum_basisModification, Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro j _
        rw [Pi.smul_apply, Pi.add_apply, mem_exponentSumKer_iff.mp (hφX j), add_zero]
        by_cases hj : j = i₃
        · subst j
          simp [w, i₃]
        · simp [hj])
    refine ⟨mul_mem (inv_mem hφwX) hrX, ?_⟩
    intro i hi
    have hφw : crossedHom χ (Pi.single i 1) (φ w) = 0 := by
      rw [hφeq]
      have hθ : ∀ k, χ (basisModification ωφ (freeProPGen 2 n k)) =
          χ (freeProPGen 2 n k) := fun k ↦ by
        by_cases hk : k < n
        · rw [freeProPGen_of_lt 2 hk, basisModification_of, map_mul, hωχ, mul_one]
        · rw [freeProPGen_eq_one_of_le 2 (not_lt.mp hk), map_one]
      rw [TauCeti.map_demushkinWordTwoEven]
      exact (isCrossedHom_crossedHom χ (Pi.single i 1)).map_demushkinWordTwoEven_eq_zero
        (by omega)
        (x := ⇑(basisModification ωφ) ∘ freeProPGen 2 n)
        (by
          rw [Function.comp_apply, hθ, freeProPGen_of_lt 2 (by omega), h₁]
          norm_num)
        (by rw [Function.comp_apply, hθ, freeProPGen_of_lt 2 hn3]; exact h₃)
        fun k hk₁ hk₃ ↦ by
          rw [Function.comp_apply, hθ]
          by_cases hk : k < n
          · rw [freeProPGen_of_lt 2 hk]
            exact hχ _ (fun e ↦ hk₁ (congrArg Fin.val e))
              (fun e ↦ hk₃ (congrArg Fin.val e))
          · rw [freeProPGen_eq_one_of_le 2 (not_lt.mp hk), map_one]
    simp [(isCrossedHom_crossedHom χ (Pi.single i 1)).map_mul,
      (isCrossedHom_crossedHom χ (Pi.single i 1)).map_inv, hφw, hrD i hi]
  · intro m hm z hz
    have hzX : gradedMk 2 (freeProP 2 (Fin n)) (m + 1) z ∈
        gradedPieceOf 2 X (m + 1) :=
      gradedMk_mem_gradedPieceOf hz.1
    have hzD : ∀ i : Fin n, i ≠ i₁ →
        (isCrossedHom_crossedHom χ (Pi.single i 1)).gradedFunctional
          ((isProP_freeProP 2 (Fin n)).mem_unitsPrincipal_one χ) (continuous_crossedHom χ _)
          (m + 1) (gradedMk 2 (freeProP 2 (Fin n)) (m + 1) z) = 0 := by
      intro i hi
      exact (isCrossedHom_crossedHom χ _).gradedFunctional_gradedMk _ _ _ _ (c := 0)
        (by rw [hz.2 i hi, mul_zero]) |>.trans (by simp)
    have hzδ :=
      (mem_map_basisModificationDelta_demushkinWordTwoEven_iff_forall_gradedFunctional_eq_zero
        hn hn3 hf hm h₁ h₃ hχ hzX).2 hzD
    obtain ⟨v, hv, hvz⟩ := Submodule.mem_map.mp hzδ
    choose ω hωX hωv using fun i ↦
      mem_gradedPieceOf_iff.mp (Submodule.mem_pi.mp hv i (Set.mem_univ i))
    refine ⟨ω, hωX, ?_⟩
    rw [funext hωv, hvz]

end TauCeti.freeProP
