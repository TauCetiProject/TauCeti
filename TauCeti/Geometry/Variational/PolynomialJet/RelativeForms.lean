/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Variational.PolynomialJet.Relative
public import TauCeti.RingTheory.Kaehler.DeRham.Polynomial
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal

/-!
# Relative vertical forms and the unsigned double-differential complex

On the algebra `TauCeti.RelJetAlgebra.VertForms B ι α` of relative vertical Kähler forms over a
commutative ring `B`, the algebraic exterior derivative `dAlg` and the Lie-derivative lifts
`totalDerivForm δ i` of total differentiation commute (`Derivation.extDeriv_deRhamLieDeriv`), and
`totalDerivForm δ i` and `totalDerivForm δ j` commute whenever `δ i` and `δ j` commute. Every
vertical form lies in a finite-order stage `vertStage B ι α r`, preserved by `vertStageDAlg` and
shifted by at most one order by `vertStageTotalDerivForm`.

Tensoring with the constant-coefficient horizontal exterior algebra `ExteriorAlgebra R (ι →₀ R)`
gives the vertical operator `dAlgTensor`, which squares to zero over any commutative ring `R` and
any index type `ι` (`dAlgTensor_dAlgTensor`). Over a finite base index type `[Fintype ι]`, the
unsigned horizontal operator `horizDerivUnsigned δ` and `dAlgTensor` form a pair of commuting
operators for arbitrary base derivations `δ` (`dAlgTensor_horizDerivUnsigned`). Whenever the base
derivations `δ i` and `δ j` commute, `horizDerivUnsigned δ` also squares to zero
(`horizDerivUnsigned_horizDerivUnsigned`), yielding the unsigned double-differential complex over
any commutative ring `R` (without characteristic restrictions).

## Main definitions

* `TauCeti.RelJetAlgebra.VertForms`, `TauCeti.RelJetAlgebra.dAlg`,
  `TauCeti.RelJetAlgebra.totalDerivForm`, `TauCeti.RelJetAlgebra.vertStage`,
  `TauCeti.RelJetAlgebra.vertStageDAlg`, `TauCeti.RelJetAlgebra.vertStageTotalDerivForm`: the
  relative vertical de Rham complex, its total-derivative Lie actions, and their finite-stage linear
  restrictions.
* `TauCeti.RelJetAlgebra.dAlgTensor` and `TauCeti.RelJetAlgebra.horizDerivUnsigned`: the vertical
  and (for `[Fintype ι]`) unsigned horizontal operators on
  `VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)`.

## Main results

* `TauCeti.RelJetAlgebra.totalDerivForm_comm`: commuting base derivations induce commuting
  total-derivative actions on vertical forms.
* `TauCeti.RelJetAlgebra.vertStageDAlg_vertStageDAlg`,
  `TauCeti.RelJetAlgebra.vertStageDAlg_vertStageTotalDerivForm`,
  `TauCeti.RelJetAlgebra.vertStageTotalDerivForm_comm`: finite-stage square-zero and commutation
  laws for `vertStageDAlg` and `vertStageTotalDerivForm`.
* `TauCeti.RelJetAlgebra.dAlgTensor_dAlgTensor`: `dAlgTensor² = 0` (for arbitrary `ι` and `δ`).
* `TauCeti.RelJetAlgebra.dAlgTensor_horizDerivUnsigned`: commutation of `dAlgTensor` with
  `horizDerivUnsigned` (for `[Fintype ι]` and arbitrary `δ`).
* `TauCeti.RelJetAlgebra.horizDerivUnsigned_horizDerivUnsigned`: `(D_H⁰)² = 0` when `[Fintype ι]`
  and the base derivations commute, completing the unsigned double-differential complex.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, for relative jet algebras and
  finite jet-order filtrations.
* R. E. Borcherds, *Quantum Field Theory* (lecture notes), for the unsigned double-differential
  presentation on `Ω_alg ⊗ Λ_H`.
-/

public section

open ExteriorAlgebra KaehlerDifferential MvPolynomial TensorProduct

namespace TauCeti.RelJetAlgebra

noncomputable section

section VerticalComplex

variable (B ι α : Type*) [CommRing B]

/-- The algebra of relative algebraic vertical forms on `RelJetAlgebra B ι α` over `B`. -/
abbrev VertForms :=
  ExteriorAlgebra (RelJetAlgebra B ι α) (Ω[RelJetAlgebra B ι α⁄B])

/-- The algebraic vertical exterior derivative on `VertForms B ι α`. -/
abbrev dAlg : VertForms B ι α →ₗ[B] VertForms B ι α :=
  KaehlerDeRham.extDeriv B (RelJetAlgebra B ι α)

/-- The subalgebra of vertical forms supported on field-jet coordinates of order at most `r`. -/
def vertStage (r : ℕ) : Subalgebra B (VertForms B ι α) :=
  KaehlerDeRham.supportedForms B {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r}

variable {B ι α}

variable {R : Type*} [CommRing R] [Algebra R B]

/-- The Lie-derivative action of total differentiation `totalDeriv δ i` on relative vertical
forms `VertForms B ι α`. -/
def totalDerivForm (δ : ι → Derivation R B B) (i : ι) : Module.End R (VertForms B ι α) :=
  (totalDeriv δ i).deRhamLieDeriv (fun b ↦ by simp)

/-- On vertical generator one-forms `duᵃ_I`, `totalDerivForm δ i` shifts `I ↦ I + eᵢ`. -/
@[simp]
theorem totalDerivForm_ι_D_X (δ : ι → Derivation R B B) (i : ι) (a : α) (I : ι →₀ ℕ) :
    totalDerivForm δ i
        (ExteriorAlgebra.ι (RelJetAlgebra B ι α)
          (KaehlerDifferential.D B (RelJetAlgebra B ι α) (X (a, I)))) =
      ExteriorAlgebra.ι (RelJetAlgebra B ι α)
        (KaehlerDifferential.D B (RelJetAlgebra B ι α) (X (a, I + Finsupp.single i 1))) := by
  simp [totalDerivForm]

/-- Commuting base derivations yield commuting total-derivative actions on vertical forms. -/
theorem totalDerivForm_comm {δ : ι → Derivation R B B} {i j : ι}
    (hδ : ∀ b, δ i (δ j b) = δ j (δ i b)) (ω : VertForms B ι α) :
    totalDerivForm δ i (totalDerivForm δ j ω) = totalDerivForm δ j (totalDerivForm δ i ω) :=
  Derivation.commute_deRhamLieDeriv_of_lie_eq_zero (fun b ↦ by simp) (fun b ↦ by simp)
    (Derivation.ext fun p ↦ by
      rw [Derivation.commutator_apply, zero_apply, sub_eq_zero,
        totalDeriv_comm hδ p]) ω

/-- `vertStage B ι α r` is the supported-form subalgebra on coordinates of order at most `r`. -/
theorem vertStage_eq_supportedForms (r : ℕ) :
    vertStage B ι α r =
      KaehlerDeRham.supportedForms B {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r} := by
  rfl

/-- Increasing the jet-order bound enlarges the vertical stage subalgebra. -/
theorem vertStage_mono : Monotone (vertStage B ι α) := by
  intro r s hrs
  exact KaehlerDeRham.supportedForms_mono fun _ h ↦ h.trans hrs

/-- Every vertical form belongs to some finite vertical stage. -/
theorem exists_mem_vertStage (ω : VertForms B ι α) : ∃ r, ω ∈ vertStage B ι α r := by
  obtain ⟨s, hs⟩ := KaehlerDeRham.exists_finset_mem_supportedForms ω
  refine ⟨s.sup (fun aI ↦ aI.2.degree), ?_⟩
  exact KaehlerDeRham.supportedForms_mono
    (fun aI haI ↦ Finset.le_sup (f := fun x : α × (ι →₀ ℕ) ↦ x.2.degree) haI) hs

/-- `totalDerivForm δ i` raises the vertical stage by at most one. -/
theorem totalDerivForm_mem_vertStage (δ : ι → Derivation R B B) (i : ι) {r : ℕ}
    {ω : VertForms B ι α} (hω : ω ∈ vertStage B ι α r) :
    totalDerivForm δ i ω ∈ vertStage B ι α (r + 1) :=
  KaehlerDeRham.deRhamLieDeriv_mem_supportedForms (fun b ↦ by simp)
    (fun _ h ↦ le_trans h (Nat.le_succ r))
    (fun _ hp ↦ by
      rw [← stage_eq_supported]
      exact totalDeriv_mem_stage δ i (by rw [stage_eq_supported]; exact hp))
    hω

variable (B ι α) in
/-- The algebraic vertical exterior derivative restricted to a finite vertical stage. -/
def vertStageDAlg (r : ℕ) : vertStage B ι α r →ₗ[B] vertStage B ι α r :=
  (dAlg B ι α).restrict
    (p := (vertStage B ι α r).toSubmodule)
    (q := (vertStage B ι α r).toSubmodule)
    fun _ hω ↦ KaehlerDeRham.extDeriv_mem_supportedForms hω

@[simp]
theorem coe_vertStageDAlg (r : ℕ) (ω : vertStage B ι α r) :
    (vertStageDAlg B ι α r ω : VertForms B ι α) = dAlg B ι α ω := by
  rfl

/-- Finite-stage vertical exterior differentiation commutes with stage inclusions. -/
@[simp]
theorem vertStageDAlg_inclusion {r s : ℕ} (hrs : r ≤ s) (ω : vertStage B ι α r) :
    vertStageDAlg B ι α s (Subalgebra.inclusion (vertStage_mono hrs) ω) =
      Subalgebra.inclusion (vertStage_mono hrs) (vertStageDAlg B ι α r ω) := by
  apply Subtype.ext
  simp

/-- Finite-stage vertical exterior differentiation squares to zero. -/
@[simp]
theorem vertStageDAlg_vertStageDAlg (r : ℕ) (ω : vertStage B ι α r) :
    vertStageDAlg B ι α r (vertStageDAlg B ι α r ω) = 0 := by
  apply Subtype.ext
  simp

/-- Total differentiation on vertical forms as an `R`-linear map between consecutive finite
vertical stages. -/
def vertStageTotalDerivForm (δ : ι → Derivation R B B) (i : ι) (r : ℕ) :
    vertStage B ι α r →ₗ[R] vertStage B ι α (r + 1) :=
  (totalDerivForm δ i).restrict
    (p := (vertStage B ι α r).toSubmodule.restrictScalars R)
    (q := (vertStage B ι α (r + 1)).toSubmodule.restrictScalars R)
    fun _ hω ↦ totalDerivForm_mem_vertStage δ i hω

@[simp]
theorem coe_vertStageTotalDerivForm (δ : ι → Derivation R B B) (i : ι) (r : ℕ)
    (ω : vertStage B ι α r) :
    (vertStageTotalDerivForm δ i r ω : VertForms B ι α) = totalDerivForm δ i ω := by
  rfl

/-- Finite-stage vertical total differentiation commutes with stage inclusions. -/
@[simp]
theorem vertStageTotalDerivForm_inclusion (δ : ι → Derivation R B B) (i : ι) {r s : ℕ}
    (hrs : r ≤ s) (ω : vertStage B ι α r) :
    vertStageTotalDerivForm δ i s (Subalgebra.inclusion (vertStage_mono hrs) ω) =
      Subalgebra.inclusion (vertStage_mono (Nat.add_le_add_right hrs 1))
        (vertStageTotalDerivForm δ i r ω) := by
  apply Subtype.ext
  simp

/-- Finite-stage vertical exterior differentiation commutes with `vertStageTotalDerivForm` at
stage `r + 1`. -/
theorem vertStageDAlg_vertStageTotalDerivForm (δ : ι → Derivation R B B) (i : ι) (r : ℕ)
    (ω : vertStage B ι α r) :
    vertStageDAlg B ι α (r + 1) (vertStageTotalDerivForm δ i r ω) =
      vertStageTotalDerivForm δ i r (vertStageDAlg B ι α r ω) := by
  apply Subtype.ext
  simp only [coe_vertStageDAlg, coe_vertStageTotalDerivForm]
  exact Derivation.extDeriv_deRhamLieDeriv (totalDeriv δ i) (fun b ↦ by simp) (ω : VertForms B ι α)

/-- Commuting base derivations yield commuting `vertStageTotalDerivForm` maps at stage `r + 2`. -/
theorem vertStageTotalDerivForm_comm {δ : ι → Derivation R B B} {i j : ι}
    (hδ : ∀ b, δ i (δ j b) = δ j (δ i b)) (r : ℕ) (ω : vertStage B ι α r) :
    vertStageTotalDerivForm δ i (r + 1) (vertStageTotalDerivForm δ j r ω) =
      vertStageTotalDerivForm δ j (r + 1) (vertStageTotalDerivForm δ i r ω) := by
  apply Subtype.ext
  simp only [coe_vertStageTotalDerivForm]
  exact totalDerivForm_comm hδ (ω : VertForms B ι α)

end VerticalComplex

section UnsignedDoubleComplex

variable (R B ι α : Type*) [CommRing R] [CommRing B] [Algebra R B]

/-- The vertical differential `d_alg ⊗ id` on `VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)`. -/
def dAlgTensor :
    Module.End R (VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :=
  ((dAlg B ι α).restrictScalars R).rTensor (ExteriorAlgebra R (ι →₀ R))

variable {R B ι α}

/-- Action of `dAlgTensor` on a pure tensor `ω ⊗ₜ β`. -/
@[simp]
theorem dAlgTensor_tmul (ω : VertForms B ι α) (β : ExteriorAlgebra R (ι →₀ R)) :
    dAlgTensor R B ι α (ω ⊗ₜ[R] β) = dAlg B ι α ω ⊗ₜ[R] β := by
  rfl

/-- `dAlgTensor` squares to zero. -/
@[simp]
theorem dAlgTensor_dAlgTensor (x : VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :
    dAlgTensor R B ι α (dAlgTensor R B ι α x) = 0 := by
  have hsq : ((dAlg B ι α).restrictScalars R).comp ((dAlg B ι α).restrictScalars R) = 0 :=
    LinearMap.ext fun ω ↦ KaehlerDeRham.extDeriv_extDeriv ω
  rw [dAlgTensor, ← LinearMap.rTensor_comp_apply, hsq, LinearMap.rTensor_zero, LinearMap.zero_apply]

/-- The unsigned horizontal differential `D_H⁰(ω ⊗ₜ β) = ∑ μ, (D_μ ω) ⊗ₜ (dx^μ ∧ β)` on
`VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)`. -/
def horizDerivUnsigned [Fintype ι] (δ : ι → Derivation R B B) :
    Module.End R (VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :=
  ∑ i : ι, TensorProduct.map (totalDerivForm δ i)
    (LinearMap.mulLeft R (ExteriorAlgebra.ι R (Finsupp.single i (1 : R))))

/-- Action of `horizDerivUnsigned δ` on a pure tensor `ω ⊗ₜ β`. -/
@[simp]
theorem horizDerivUnsigned_tmul [Fintype ι] (δ : ι → Derivation R B B) (ω : VertForms B ι α)
    (β : ExteriorAlgebra R (ι →₀ R)) :
    horizDerivUnsigned δ (ω ⊗ₜ[R] β) =
      ∑ i : ι, totalDerivForm δ i ω ⊗ₜ[R]
        (ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) * β) := by
  simp [horizDerivUnsigned]

/-- **Commutation of `dAlgTensor` and `horizDerivUnsigned`**: for any family of base derivations
`δ`, the vertical differential `d_alg ⊗ id` and the unsigned horizontal operator `D_H⁰` commute
with no sign. -/
theorem dAlgTensor_horizDerivUnsigned [Fintype ι] (δ : ι → Derivation R B B)
    (x : VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :
    dAlgTensor R B ι α (horizDerivUnsigned δ x) =
      horizDerivUnsigned δ (dAlgTensor R B ι α x) := by
  simp only [dAlgTensor, horizDerivUnsigned, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.rTensor_map, LinearMap.map_rTensor]
  congr 2
  ext ω
  exact Derivation.extDeriv_deRhamLieDeriv (totalDeriv δ i) (fun b ↦ by simp) ω

/-- **Nilpotency of the unsigned horizontal differential**: `(D_H⁰)² = 0` whenever the base
derivations commute, over any commutative ring `R` (including in characteristic two). -/
theorem horizDerivUnsigned_horizDerivUnsigned [Fintype ι] {δ : ι → Derivation R B B}
    (hδ : ∀ i j b, δ i (δ j b) = δ j (δ i b))
    (x : VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :
    horizDerivUnsigned δ (horizDerivUnsigned δ x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul ω β =>
    have hdiag (i : ι) :
        totalDerivForm δ i (totalDerivForm δ i ω) ⊗ₜ[R]
            (ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) *
              (ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) * β)) = 0 := by
      rw [← mul_assoc]
      simp
    have hswap (i j : ι) :
        totalDerivForm δ j (totalDerivForm δ i ω) ⊗ₜ[R]
            (ExteriorAlgebra.ι R (Finsupp.single j (1 : R)) *
              (ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) * β)) +
          totalDerivForm δ i (totalDerivForm δ j ω) ⊗ₜ[R]
            (ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) *
              (ExteriorAlgebra.ι R (Finsupp.single j (1 : R)) * β)) = 0 := by
      rw [totalDerivForm_comm (hδ j i), ← TensorProduct.tmul_add, ← mul_assoc, ← mul_assoc,
        ← add_mul, ExteriorAlgebra.ι_add_mul_swap]
      simp
    simp only [horizDerivUnsigned_tmul, map_sum]
    exact Finset.sum_sum_eq_zero_of_diag Finset.univ
      (fun i _ ↦ hdiag i) (fun i _ j _ _ ↦ hswap i j)
  | add x y hx hy => simp [hx, hy]

end UnsignedDoubleComplex

end

end TauCeti.RelJetAlgebra
