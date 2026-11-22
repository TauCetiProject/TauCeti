/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
import TauCeti.Data.Fintype.Fiber
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Refinement
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Henselian
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SquareClasses
import TauCeti.RingTheory.Henselian.Basic

/-!
# Odd-prime uniqueness for diagonal Jordan forms over `ℤ_p`

Fiberwise unit-square-class uniqueness for diagonal Jordan forms over `ℤ_p` (`p ≠ 2`), together
with positive-scale rank and square-class extraction from an orthogonal sum of odd cyclic modules
and minimal-rank uniqueness over `ℤ_p`.

## Main results

* `TauCeti.FiniteQuadraticModule.forall_pos_card_filter_eq_and_isSquare_of_isometry_pi_oddCyclic`
* `LinearMap.BilinForm.equivalent_of_iIsOrtho_of_forall_fiber`
* `LinearMap.BilinForm.equivalent_of_iIsOrtho_of_isometry_pi_oddCyclic`
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
  have hodd_card : Odd (Nat.card (pi fun i ↦ oddCyclic (p ^ k i) hp_odd.pow (θ i))) := by
    rw [Nat.card_pi]
    exact Finset.prod_induction _ Odd (fun _ _ ha hb ↦ ha.mul hb) odd_one fun i _ ↦ by
      rw [natCard_oddCyclic]; exact hp_odd.pow
  have hquad : Nonempty (Isometry
      (pi fun i ↦ oddCyclic (p ^ k i) hp_odd.pow (θ i))
      (pi fun j ↦ oddCyclic (p ^ l j) hp_odd.pow (η j))) :=
    (nonempty_isometry_iff_bilinear_isometry_of_odd hodd_card).mpr hdisc
  have hclass := (nonempty_isometry_pi_oddCyclic_iff hp_odd k l
    (fun i ↦ PadicInt.isCoprime_of_isUnit_of_dvd_sub (u i).isUnit (hθ i))
    (fun j ↦ PadicInt.isCoprime_of_isUnit_of_dvd_sub (v j).isUnit (hη j))).mp hquad
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

/-- **Fiberwise equivalence of odd-prime `ℤ_p`-bilinear forms.** Once two diagonal Jordan forms
over `ℤ_p` (`p ≠ 2`) match along `σ : ι ≃ κ` and agree in square class on every scale fiber `m`,
the bilinear forms are equivalent over `ℤ_p`. -/
theorem equivalent_of_iIsOrtho_of_forall_fiber {p : ℕ} [Fact p.Prime]
    {P₁ P₂ ι κ : Type*} [AddCommGroup P₁] [Module ℤ_[p] P₁]
    [AddCommGroup P₂] [Module ℤ_[p] P₂] [Fintype ι]
    (B₁ : LinearMap.BilinForm ℤ_[p] P₁) (B₂ : LinearMap.BilinForm ℤ_[p] P₂) (hp : p ≠ 2)
    {b : Module.Basis ι ℤ_[p] P₁} {c : Module.Basis κ ℤ_[p] P₂}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : B₁.iIsOrtho b) (hc : B₂.iIsOrtho c)
    (hbu : ∀ i, B₁ (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hcv : ∀ j, B₂ (c j) (c j) = v j * (p : ℤ_[p]) ^ l j)
    (σ : ι ≃ κ) (hσ : ∀ i, l (σ i) = k i)
    (hfiber : ∀ m : ℕ, IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v (σ i))) :
    B₁.Equivalent B₂ := by
  classical
  let := (PadicInt.isUnit_two hp).invertible
  have hdiag := TauCeti.equivalent_weightedSumSquares_mul_of_forall_fiber_of_isUnit_two
    (PadicInt.isUnit_two hp) k (fun m ↦ (p : ℤ_[p]) ^ m) u (fun i ↦ v (σ i)) hfiber
  have h1_quad : B₁.toQuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares ℤ_[p] fun i ↦ (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) := by
    simpa only [hbu] using hb.equivalent_weightedSumSquares
  have h2_quad : B₂.toQuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares ℤ_[p] fun i ↦ (v (σ i) : ℤ_[p]) * (p : ℤ_[p]) ^ k i) := by
    simpa only [Module.Basis.reindex_apply, Equiv.symm_symm, hcv, hσ] using
      (hc.reindex σ.symm).equivalent_weightedSumSquares
  exact (hb.isSymm.equivalent_iff_toQuadraticMap_equivalent
    hc.isSymm (PadicInt.isUnit_two hp).mem_nonZeroDivisors).mpr
    (h1_quad.trans (hdiag.trans h2_quad.symm))

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
  obtain ⟨σ, hσ⟩ := Function.exists_equiv_of_occCount_eq (u := k) (v := l) fun m ↦ by
    rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter]
    obtain rfl | hm := eq_or_ne m 0
    · simp [hk, hl]
    · exact (hpos m (Nat.pos_of_ne_zero hm)).1
  have hσi : ∀ i, l (σ i) = k i := congrFun hσ
  refine B₁.equivalent_of_iIsOrtho_of_forall_fiber B₂ hp hb hc hbu hcv σ hσi fun m ↦ ?_
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · simp [hk]
  · rw [Finset.prod_filter_equiv k l v m σ hσi]; exact (hpos m hm).2

end LinearMap.BilinForm
