/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
import TauCeti.LinearAlgebra.BilinearForm.Henselian
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Bilinear
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SquareClasses
import TauCeti.RingTheory.Henselian.Basic

/-!
# Odd-prime uniqueness for diagonal Jordan forms over `ℤ_p`

Positive-scale rank and square-class extraction from an orthogonal sum of odd cyclic modules
(via `TauCeti.FiniteBilinearModule.nonempty_isometry_pi_oddCyclic_iff`, built on
`TauCeti.FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff`), together with minimal-rank
uniqueness for diagonal Jordan forms over `ℤ_p` (`p ≠ 2`) (Nikulin, Theorem 1.9.1), proved via
`LinearMap.BilinForm.iIsOrtho.equivalent_of_card_eq_of_isSquare_prod_mul_prod`.

## Main results

* `TauCeti.FiniteQuadraticModule.forall_pos_card_filter_eq_and_isSquare_of_isometry_pi_oddCyclic`
* `LinearMap.BilinForm.equivalent_of_iIsOrtho_of_isometry_pi_oddCyclic`

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Theorem 1.9.1.
-/

public section

open Finset

namespace TauCeti.FiniteQuadraticModule

/-- From a bilinear isometry between orthogonal sums of odd cyclic generators `q_{θᵢ}^{(p)}(p^{kᵢ})`
and `q_{ηⱼ}^{(p)}(p^{lⱼ})` lifting `uᵢ, vⱼ ∈ ℤ_pˣ` modulo `p`, every positive scale `m ≥ 1` has
equal rank `#{i | kᵢ = m} = #{j | lⱼ = m}` and square product `(∏_{kᵢ = m} uᵢ) (∏_{lⱼ = m} vⱼ)`
in `ℤ_pˣ`. -/
theorem forall_pos_card_filter_eq_and_isSquare_of_isometry_pi_oddCyclic
    {p : ℕ} [Fact p.Prime] {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hp_odd : Odd p) {θ : ι → ℤ} {η : κ → ℤ}
    (hθ : ∀ i, (p : ℤ_[p]) ∣ (u i : ℤ_[p]) - θ i)
    (hη : ∀ j, (p : ℤ_[p]) ∣ (v j : ℤ_[p]) - η j)
    (hdisc : Nonempty (TauCeti.FiniteBilinearModule.Isometry
      (pi fun i ↦ oddCyclic (p ^ k i) hp_odd.pow (θ i)).toFiniteBilinearModule
      (pi fun j ↦ oddCyclic (p ^ l j) hp_odd.pow (η j)).toFiniteBilinearModule)) :
    ∀ m, 0 < m → #{i | k i = m} = #{j | l j = m} ∧
      IsSquare ((∏ i with k i = m, u i) * ∏ j with l j = m, v j) := by
  classical
  have hp : p ≠ 2 := fun h ↦ by subst h; exact absurd hp_odd (by decide)
  have hclass := (TauCeti.FiniteBilinearModule.nonempty_isometry_pi_oddCyclic_iff hp_odd k l
    (fun i ↦ PadicInt.isCoprime_of_isUnit_of_dvd_sub (u i).isUnit (hθ i))
    (fun j ↦ PadicInt.isCoprime_of_isUnit_of_dvd_sub (v j).isUnit (hη j))).mp hdisc
  intro m hm
  refine ⟨(hclass m hm).1, ?_⟩
  rw [← Units.isSquare_coe_iff, Units.val_mul, Units.coe_prod, Units.coe_prod]
  exact (TauCeti.PadicInt.isSquare_prod_mul_prod_iff_legendreSym_eq hp
    {i : ι | k i = m} {j : κ | l j = m}
    (fun i ↦ (u i : ℤ_[p])) (fun j ↦ (v j : ℤ_[p])) θ η
    (fun i _ ↦ (u i).isUnit) (fun j _ ↦ (v j).isUnit)
    (fun i _ ↦ hθ i) (fun j _ ↦ hη j)).mpr (hclass m hm).2

end TauCeti.FiniteQuadraticModule

namespace LinearMap.BilinForm

/-- **Minimal-rank uniqueness over `ℤ_p` at an odd prime.** Let `p` be an odd prime and let
`B₁` and `B₂` be `ℤ_p`-bilinear forms presented in diagonal Jordan bases `b` and `c` with
`B₁ (b i) (b i) = uᵢ p^{kᵢ}` (`kᵢ ≠ 0`) and `B₂ (c j) (c j) = vⱼ p^{lⱼ}` (`lⱼ ≠ 0`). If the
corresponding orthogonal sums of odd cyclic generators for integer lifts `θᵢ ≡ uᵢ (mod p)` and
`ηⱼ ≡ vⱼ (mod p)` are bilinearly isometric, then `B₁` and `B₂` are equivalent over `ℤ_p`. -/
theorem equivalent_of_iIsOrtho_of_isometry_pi_oddCyclic {p : ℕ} [Fact p.Prime]
    {P₁ P₂ ι κ : Type*} [AddCommGroup P₁] [Module ℤ_[p] P₁]
    [AddCommGroup P₂] [Module ℤ_[p] P₂] [Fintype ι] [Fintype κ]
    (B₁ : LinearMap.BilinForm ℤ_[p] P₁) (B₂ : LinearMap.BilinForm ℤ_[p] P₂)
    {b : Module.Basis ι ℤ_[p] P₁} {c : Module.Basis κ ℤ_[p] P₂}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : B₁.iIsOrtho b) (hc : B₂.iIsOrtho c)
    (hbu : ∀ i, B₁ (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hcv : ∀ j, B₂ (c j) (c j) = v j * (p : ℤ_[p]) ^ l j)
    (hk : ∀ i, k i ≠ 0) (hl : ∀ j, l j ≠ 0)
    (hp_odd : Odd p) {θ : ι → ℤ} {η : κ → ℤ}
    (hθ : ∀ i, (p : ℤ_[p]) ∣ (u i : ℤ_[p]) - θ i)
    (hη : ∀ j, (p : ℤ_[p]) ∣ (v j : ℤ_[p]) - η j)
    (hdisc : Nonempty (TauCeti.FiniteBilinearModule.Isometry
      (TauCeti.FiniteQuadraticModule.pi fun i ↦
        TauCeti.FiniteQuadraticModule.oddCyclic (p ^ k i) hp_odd.pow (θ i)).toFiniteBilinearModule
      (TauCeti.FiniteQuadraticModule.pi fun j ↦
        TauCeti.FiniteQuadraticModule.oddCyclic (p ^ l j) hp_odd.pow
          (η j)).toFiniteBilinearModule)) :
    B₁.Equivalent B₂ := by
  classical
  have hp : p ≠ 2 := fun h ↦ by subst h; exact absurd hp_odd (by decide)
  have hpos :=
    TauCeti.FiniteQuadraticModule.forall_pos_card_filter_eq_and_isSquare_of_isometry_pi_oddCyclic
      hp_odd hθ hη hdisc
  refine hb.equivalent_of_card_eq_of_isSquare_prod_mul_prod (PadicInt.isUnit_two hp)
    hc hbu hcv (fun m ↦ ?_) (fun m ↦ ?_)
  · obtain rfl | hm := Nat.eq_zero_or_pos m
    · simp [hk, hl]
    · exact (hpos m hm).1
  · obtain rfl | hm := Nat.eq_zero_or_pos m
    · simp [hk, hl]
    · exact (hpos m hm).2

end LinearMap.BilinForm
