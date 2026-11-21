/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.Geometry.Variational.PolynomialJet.Basic
public import TauCeti.RingTheory.Kaehler.DeRham.Basic
public import TauCeti.RingTheory.Kaehler.DeRham.LieDerivative
public import TauCeti.RingTheory.Kaehler.DeRham.Polynomial
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal
import TauCeti.RingTheory.Derivation.BaseChange

/-!
# Relative polynomial jet algebras and the unsigned double-differential complex

Given a commutative `R`-algebra `B` equipped with a family of base derivations
`δ : ι → Derivation R B B` (for instance `B = MvPolynomial ι R` with `δ = MvPolynomial.pderiv`,
or a ring of smooth functions on an open domain with coordinate partial derivatives), the
**relative polynomial jet algebra** `TauCeti.RelJetAlgebra B ι α` is the polynomial algebra
`MvPolynomial (α × (ι →₀ ℕ)) B` in symmetric field-jet coordinates `uᵃ_I` with coefficients in `B`.

The total derivative `TauCeti.RelJetAlgebra.totalDeriv δ i` differentiates coefficients via `δ i`
and shifts jet coordinates `uᵃ_I ↦ uᵃ_(I+eᵢ)`. It satisfies the fundamental variational commutator
identity with vertical partial derivatives:
`pderiv (a, I) (totalDeriv δ i p) = totalDeriv δ i (pderiv (a, I) p) + pderiv (a, I - eᵢ) p`
(with the second term absent when `I i = 0`).

On the algebra `VertForms B ι α` of relative vertical Kähler forms over `B`, the exterior
derivative `dAlg` and the Lie-derivative lifts `totalDerivForm δ i` of total differentiation
commute (`dAlg_totalDerivForm`), and `totalDerivForm δ i` and `totalDerivForm δ j` commute
whenever `δ i` and `δ j` commute. Tensoring with the constant-coefficient horizontal exterior
algebra `ExteriorAlgebra R (ι →₀ R)` yields the unsigned double-differential complex with commuting
square-zero differentials `dAlgTensor` and `horizDerivUnsigned`, over any commutative ring `R`
(without characteristic restrictions).

## Main definitions

* `TauCeti.RelJetAlgebra`: `MvPolynomial (α × (ι →₀ ℕ)) B`.
* `TauCeti.RelJetAlgebra.totalDeriv`: total differentiation along `∂ i`.
* `TauCeti.RelJetAlgebra.stage`: finite-order subalgebra of jet order at most `r`.
* `TauCeti.RelJetAlgebra.polyJetEquivRel`: `R`-algebra isomorphism
  `PolynomialJet R ι α ≃ₐ[R] RelJetAlgebra (MvPolynomial ι R) ι α`.
* `TauCeti.RelJetAlgebra.VertForms`, `TauCeti.RelJetAlgebra.dAlg`,
  `TauCeti.RelJetAlgebra.totalDerivForm`, `TauCeti.RelJetAlgebra.vertStage`: the relative vertical
  de Rham complex and its total-derivative Lie actions.
* `TauCeti.RelJetAlgebra.dAlgTensor` and `TauCeti.RelJetAlgebra.horizDerivUnsigned`: the commuting
  square-zero differentials on `VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)`.

## Main results

* `TauCeti.RelJetAlgebra.pderiv_totalDeriv`: commutator of vertical partial differentiation and
  total differentiation.
* `TauCeti.RelJetAlgebra.polyJetEquivRel_totalDeriv` and
  `TauCeti.RelJetAlgebra.polyJetEquivRel_mem_stage_iff`: compatibility with `PolynomialJet`.
* `TauCeti.RelJetAlgebra.dAlg_totalDerivForm`: `d_alg` commutes with `totalDerivForm ∂ i`.
* `TauCeti.RelJetAlgebra.dAlgTensor_horizDerivUnsigned` and
  `TauCeti.RelJetAlgebra.horizDerivUnsigned_horizDerivUnsigned`: commuting and square-zero
  relations of the unsigned double-differential complex.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, for relative jet algebras and
  total-derivative commutators.
* R. E. Borcherds, *Quantum Field Theory* (lecture notes), for the unsigned double-differential
  presentation on `Ω_alg ⊗ Λ_H`.
-/

public section

open ExteriorAlgebra KaehlerDifferential MvPolynomial TensorProduct

namespace TauCeti

/-- Polynomial expressions in symmetric field-jet coordinates `α × (ι →₀ ℕ)` with coefficients in
an arbitrary base commutative semiring `B`. -/
abbrev RelJetAlgebra (B ι α : Type*) [CommSemiring B] :=
  MvPolynomial (α × (ι →₀ ℕ)) B

namespace RelJetAlgebra

noncomputable section

section TotalDeriv

variable {R B ι α : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]

/-- The `R`-algebra isomorphism `MvPolynomial σ R ⊗[R] B ≃ₐ[R] MvPolynomial σ B`. -/
private def tensorBaseEquiv (R B σ : Type*) [CommSemiring R] [CommSemiring B] [Algebra R B] :
    MvPolynomial σ R ⊗[R] B ≃ₐ[R] MvPolynomial σ B :=
  (Algebra.TensorProduct.comm R (MvPolynomial σ R) B).trans
    ((MvPolynomial.algebraTensorAlgEquiv R B).restrictScalars R)

private theorem tensorBaseEquiv_one_tmul (b : B) :
    tensorBaseEquiv R B (α × (ι →₀ ℕ)) (1 ⊗ₜ[R] b) = C b := by
  simp [tensorBaseEquiv, Algebra.smul_def, MvPolynomial.algebraMap_eq]

private theorem tensorBaseEquiv_X_tmul_one (v : α × (ι →₀ ℕ)) :
    tensorBaseEquiv R B (α × (ι →₀ ℕ)) (X v ⊗ₜ[R] 1) = X v := by
  simp [tensorBaseEquiv]

private theorem tensorBaseEquiv_symm_C (b : B) :
    (tensorBaseEquiv R B (α × (ι →₀ ℕ))).symm (C b) = 1 ⊗ₜ[R] b := by
  apply (tensorBaseEquiv R B (α × (ι →₀ ℕ))).injective
  rw [AlgEquiv.apply_symm_apply, tensorBaseEquiv_one_tmul]

private theorem tensorBaseEquiv_symm_X (v : α × (ι →₀ ℕ)) :
    (tensorBaseEquiv R B (α × (ι →₀ ℕ))).symm (X v) = X v ⊗ₜ[R] 1 := by
  apply (tensorBaseEquiv R B (α × (ι →₀ ℕ))).injective
  rw [AlgEquiv.apply_symm_apply, tensorBaseEquiv_X_tmul_one]

/-- Coefficient-wise lift of a base derivation `d : Derivation R B B` to `RelJetAlgebra B ι α`,
obtained from `Derivation.baseChange` along `MvPolynomial _ R`. -/
private def coeffDeriv (d : Derivation R B B) :
    Derivation R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α) where
  toLinearMap :=
    (tensorBaseEquiv R B (α × (ι →₀ ℕ))).toLinearMap.comp
      (((d.baseChange (MvPolynomial (α × (ι →₀ ℕ)) R)).toLinearMap.restrictScalars R).comp
        (tensorBaseEquiv R B (α × (ι →₀ ℕ))).symm.toLinearMap)
  map_one_eq_zero' := by
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Derivation.map_one_eq_zero, map_zero]
  leibniz' p q := by
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearMap.coe_restrictScalars,
      Derivation.coeFn_coe, map_mul, Derivation.leibniz, smul_eq_mul, map_add,
      AlgEquiv.apply_symm_apply]

private theorem coeffDeriv_C (d : Derivation R B B) (b : B) :
    coeffDeriv (ι := ι) (α := α) d (C b) = C (d b) := by
  simp [coeffDeriv, tensorBaseEquiv_symm_C, tensorBaseEquiv_one_tmul]

private theorem coeffDeriv_X (d : Derivation R B B) (v : α × (ι →₀ ℕ)) :
    coeffDeriv (ι := ι) (α := α) d (X v) = 0 := by
  simp [coeffDeriv, tensorBaseEquiv_symm_X]

/-- **Total differentiation** on the relative polynomial jet algebra `RelJetAlgebra B ι α` along
a family of base derivations `δ : ι → Derivation R B B`: it applies `δ i` to coefficients in `B`
and shifts each field-jet coordinate `uᵃ_I` to `uᵃ_(I + eᵢ)`. -/
def totalDeriv (δ : ι → Derivation R B B) (i : ι) :
    Derivation R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α) :=
  coeffDeriv (δ i) +
    (MvPolynomial.mkDerivation B fun aI : α × (ι →₀ ℕ) ↦
      (X (aI.1, aI.2 + Finsupp.single i 1) : RelJetAlgebra B ι α)).restrictScalars R

/-- Total differentiation acts on base coefficients `C b` by `δ i`. -/
@[simp]
theorem totalDeriv_C (δ : ι → Derivation R B B) (i : ι) (b : B) :
    totalDeriv (α := α) δ i (C b) = C (δ i b) := by
  simp [totalDeriv, coeffDeriv_C]

/-- Total differentiation shifts field-jet variables `uᵃ_I ↦ uᵃ_(I + eᵢ)`. -/
@[simp]
theorem totalDeriv_X (δ : ι → Derivation R B B) (i : ι) (a : α) (I : ι →₀ ℕ) :
    totalDeriv δ i (X (a, I)) = X (a, I + Finsupp.single i 1) := by
  simp [totalDeriv, coeffDeriv_X]

/-- Total differentiation is uniquely determined among `R`-derivations by its action on base
coefficients and field-jet coordinates. -/
theorem totalDeriv_unique (δ : ι → Derivation R B B) (i : ι)
    (D : Derivation R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α))
    (hC : ∀ b, D (C b) = C (δ i b))
    (hX : ∀ a I, D (X (a, I)) = X (a, I + Finsupp.single i 1)) :
    D = totalDeriv δ i := by
  refine Derivation.ext fun p ↦ ?_
  induction p using MvPolynomial.induction_on with
  | C b => rw [hC, totalDeriv_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rcases v with ⟨a, I⟩
    simp only [Derivation.leibniz, smul_eq_mul, hp, hX, totalDeriv_X]

/-- Commuting base derivations induce commuting total derivatives on `RelJetAlgebra B ι α`. -/
theorem totalDeriv_comm {δ : ι → Derivation R B B} {i j : ι}
    (hδ : ∀ b, δ i (δ j b) = δ j (δ i b)) (p : RelJetAlgebra B ι α) :
    totalDeriv δ i (totalDeriv δ j p) = totalDeriv δ j (totalDeriv δ i p) := by
  induction p using MvPolynomial.induction_on with
  | C b => simp [hδ]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    rcases v with ⟨a, I⟩
    simp only [Derivation.leibniz, smul_eq_mul, map_add, totalDeriv_X, hp, add_right_comm I]
    ring

open Classical in
/-- **Variational commutator identity**: vertical partial differentiation `∂/∂uᵃ_I` and total
differentiation `Dᵢ` satisfy `[∂/∂uᵃ_I, Dᵢ] = ∂/∂uᵃ_(I - eᵢ)` (or `0` when `I i = 0`). -/
theorem pderiv_totalDeriv (δ : ι → Derivation R B B) (i : ι) (a : α) (I : ι →₀ ℕ)
    (p : RelJetAlgebra B ι α) :
    MvPolynomial.pderiv (a, I) (totalDeriv δ i p) =
      totalDeriv δ i (MvPolynomial.pderiv (a, I) p) +
        if 1 ≤ I i then MvPolynomial.pderiv (a, I - Finsupp.single i 1) p else 0 := by
  classical
  have hshift (b : α) (J : ι →₀ ℕ) :
      ((b, J + Finsupp.single i 1) = (a, I)) ↔
        (1 ≤ I i ∧ (b, J) = (a, I - Finsupp.single i 1)) := by
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      refine ⟨?_, rfl, (add_tsub_cancel_right J (Finsupp.single i 1)).symm⟩
      simp
    · rintro ⟨hI, rfl, rfl⟩
      exact ⟨rfl, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hI)⟩
  induction p using MvPolynomial.induction_on with
  | C c =>
    split_ifs <;> simp
  | add p q hp hq =>
    split_ifs at hp hq ⊢
    · simp only [map_add, hp, hq]; ac_rfl
    · simp only [map_add, hp, hq, add_zero]
  | mul_X p v hp =>
    rcases v with ⟨b, J⟩
    have hX1 : MvPolynomial.pderiv (a, I) (X (b, J + Finsupp.single i 1) : RelJetAlgebra B ι α) =
        if 1 ≤ I i then
          MvPolynomial.pderiv (a, I - Finsupp.single i 1) (X (b, J) : RelJetAlgebra B ι α)
        else 0 := by
      simp only [MvPolynomial.pderiv_X, Pi.single_apply]
      by_cases hI : 1 ≤ I i
      · simp only [hI, ite_true]
        by_cases hEq : (b, J + Finsupp.single i 1) = (a, I)
        · have hEq' : (b, J) = (a, I - Finsupp.single i 1) := ((hshift b J).mp hEq).2
          simp [hEq, hEq']
        · have hNe' : (b, J) ≠ (a, I - Finsupp.single i 1) := fun h ↦
            hEq ((hshift b J).mpr ⟨hI, h⟩)
          simp [hEq, hNe']
      · simp only [hI, ite_false]
        have hNe : (b, J + Finsupp.single i 1) ≠ (a, I) := fun h ↦ hI ((hshift b J).mp h).1
        simp [hNe]
    have hD_pderiv_X :
        totalDeriv δ i (MvPolynomial.pderiv (a, I) (X (b, J) : RelJetAlgebra B ι α)) = 0 := by
      simp only [MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    split_ifs at hp hX1 ⊢ with hI
    · simp only [Derivation.leibniz, smul_eq_mul, map_add, totalDeriv_X, hp, hX1, hD_pderiv_X]
      ring
    · simp only [add_zero, Derivation.leibniz, smul_eq_mul, map_add, totalDeriv_X, hp, hX1,
        hD_pderiv_X]
      ring

end TotalDeriv

section Stage

variable (B ι α : Type*) [CommSemiring B]

/-- The finite-order relative jet subalgebra of order at most `r`, allowing arbitrary base
coefficients in `B` and field-jet coordinates `uᵃ_I` with `I.degree ≤ r`. -/
def stage (r : ℕ) : Subalgebra B (RelJetAlgebra B ι α) :=
  MvPolynomial.supported B {aI | aI.2.degree ≤ r}

variable {B ι α}

/-- `stage B ι α r` is the subalgebra of polynomials supported on coordinates of order at most `r`.
-/
theorem stage_eq_supported (r : ℕ) :
    stage B ι α r = MvPolynomial.supported B {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r} := by
  rfl

/-- Membership in `stage B ι α r` is equivalent to every occurring variable having order `≤ r`. -/
theorem mem_stage_iff {r : ℕ} {p : RelJetAlgebra B ι α} :
    p ∈ stage B ι α r ↔ ∀ a I, (a, I) ∈ p.vars → I.degree ≤ r := by
  rw [stage, MvPolynomial.mem_supported]
  constructor
  · intro h a I haI
    exact h haI
  · intro h ⟨a, I⟩ haI
    exact h a I haI

/-- Increasing the jet-order bound enlarges the stage subalgebra. -/
theorem stage_mono : Monotone (stage B ι α) := by
  intro r s hrs
  exact MvPolynomial.supported_mono fun _ h ↦ h.trans hrs

/-- A field-jet variable `uᵃ_I` lies in `stage B ι α r` whenever `I.degree ≤ r`. -/
theorem X_mem_stage {r : ℕ} {a : α} {I : ι →₀ ℕ} (hI : I.degree ≤ r) :
    (X (a, I) : RelJetAlgebra B ι α) ∈ stage B ι α r :=
  Algebra.subset_adjoin ⟨(a, I), hI, rfl⟩

/-- Over a nontrivial coefficient ring, `uᵃ_I ∈ stage B ι α r` if and only if `I.degree ≤ r`. -/
theorem X_mem_stage_iff [Nontrivial B] {r : ℕ} {a : α} {I : ι →₀ ℕ} :
    (X (a, I) : RelJetAlgebra B ι α) ∈ stage B ι α r ↔ I.degree ≤ r := by
  rw [mem_stage_iff, MvPolynomial.vars_X]
  simp

/-- Every relative jet polynomial belongs to some finite stage. -/
theorem exists_mem_stage (p : RelJetAlgebra B ι α) : ∃ r, p ∈ stage B ι α r := by
  induction p using MvPolynomial.induction_on with
  | C b => exact ⟨0, (stage B ι α 0).algebraMap_mem b⟩
  | add p q hp hq =>
    obtain ⟨r, hr⟩ := hp
    obtain ⟨s, hs⟩ := hq
    exact ⟨max r s, add_mem (stage_mono (le_max_left r s) hr)
      (stage_mono (le_max_right r s) hs)⟩
  | mul_X p v hp =>
    obtain ⟨r, hr⟩ := hp
    rcases v with ⟨a, I⟩
    exact ⟨max r I.degree, mul_mem (stage_mono (le_max_left _ _) hr)
      (X_mem_stage (le_max_right _ _))⟩

/-- Total differentiation raises the jet-order stage by at most one. -/
theorem totalDeriv_mem_stage {R : Type*} [CommSemiring R] [Algebra R B]
    (δ : ι → Derivation R B B) (i : ι) {r : ℕ} {p : RelJetAlgebra B ι α}
    (hp : p ∈ stage B ι α r) : totalDeriv δ i p ∈ stage B ι α (r + 1) := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨a, I⟩, hI, rfl⟩ := hx
    rw [totalDeriv_X]
    exact X_mem_stage (by simpa using Nat.add_le_add_right hI 1)
  | algebraMap b =>
    rw [MvPolynomial.algebraMap_eq, totalDeriv_C]
    exact (stage B ι α (r + 1)).algebraMap_mem (δ i b)
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (stage_mono (Nat.le_succ r) hx) ihy)
      (mul_mem (stage_mono (Nat.le_succ r) hy) ihx)

/-- Vertical partial differentiation preserves every finite stage. -/
theorem pderiv_mem_stage (a : α) (I : ι →₀ ℕ) {r : ℕ} {p : RelJetAlgebra B ι α}
    (hp : p ∈ stage B ι α r) : MvPolynomial.pderiv (a, I) p ∈ stage B ι α r := by
  classical
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨b, J⟩, _, rfl⟩ := hx
    simp only [MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | algebraMap b => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem hx ihy) (mul_mem hy ihx)

end Stage

section PolynomialBase

variable (R ι α : Type*) [CommSemiring R]

/-- **Comparison with `PolynomialJet`**: identifying base-and-field jet polynomials over `R`
with relative jet polynomials over `B = MvPolynomial ι R`. -/
def polyJetEquivRel : PolynomialJet R ι α ≃ₐ[R] RelJetAlgebra (MvPolynomial ι R) ι α :=
  (MvPolynomial.renameEquiv R (Equiv.sumComm ι (α × (ι →₀ ℕ)))).trans
    (MvPolynomial.sumAlgEquiv R (α × (ι →₀ ℕ)) ι)

variable {R ι α}

/-- Under `polyJetEquivRel`, a base coordinate `xⱼ` becomes the coefficient `C (X j)`. -/
@[simp]
theorem polyJetEquivRel_X_base (j : ι) :
    polyJetEquivRel R ι α (X (Sum.inl j)) = C (X j) := by
  simp [polyJetEquivRel]

/-- Under `polyJetEquivRel`, a field-jet coordinate `uᵃ_I` becomes `X (a, I)`. -/
@[simp]
theorem polyJetEquivRel_X_field (a : α) (I : ι →₀ ℕ) :
    polyJetEquivRel R ι α (X (Sum.inr (a, I))) = X (a, I) := by
  simp [polyJetEquivRel]

/-- Under `polyJetEquivRel`, a scalar polynomial `C r` becomes `C (C r)`. -/
@[simp]
theorem polyJetEquivRel_C (r : R) :
    polyJetEquivRel R ι α (C r) = C (C r) := by
  simp [polyJetEquivRel]

/-- The inverse comparison sends a base polynomial coefficient `C b` to `rename Sum.inl b`. -/
@[simp]
theorem polyJetEquivRel_symm_C (b : MvPolynomial ι R) :
    (polyJetEquivRel R ι α).symm (C b) = MvPolynomial.rename Sum.inl b := by
  apply (polyJetEquivRel R ι α).injective
  rw [AlgEquiv.apply_symm_apply]
  induction b using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]

/-- The inverse comparison sends a field-jet coordinate `X (a, I)` to `X (Sum.inr (a, I))`. -/
@[simp]
theorem polyJetEquivRel_symm_X (a : α) (I : ι →₀ ℕ) :
    (polyJetEquivRel R ι α).symm (X (a, I)) = X (Sum.inr (a, I)) := by
  apply (polyJetEquivRel R ι α).injective
  rw [AlgEquiv.apply_symm_apply, polyJetEquivRel_X_field]

/-- `polyJetEquivRel` intertwines `PolynomialJet.totalDeriv` with relative `totalDeriv pderiv`. -/
theorem polyJetEquivRel_totalDeriv (i : ι) (p : PolynomialJet R ι α) :
    polyJetEquivRel R ι α (PolynomialJet.totalDeriv i p) =
      totalDeriv (fun k ↦ MvPolynomial.pderiv (R := R) k) i (polyJetEquivRel R ι α p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    rcases v with j | ⟨a, I⟩
    · simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        PolynomialJet.totalDeriv_X_base, polyJetEquivRel_X_base, totalDeriv_C,
        MvPolynomial.pderiv_X, Pi.single_apply, hp]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    · simp [Derivation.leibniz, hp]

/-- `polyJetEquivRel` identifies the finite stages of `PolynomialJet` and `RelJetAlgebra`. -/
theorem polyJetEquivRel_mem_stage_iff (r : ℕ) (p : PolynomialJet R ι α) :
    p ∈ PolynomialJet.stage R ι α r ↔
      polyJetEquivRel R ι α p ∈ stage (MvPolynomial ι R) ι α r := by
  classical
  constructor
  · intro hp
    rw [PolynomialJet.mem_stage_iff] at hp
    rw [p.as_sum, map_sum]
    refine sum_mem fun s hs ↦ ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod, map_mul, map_prod]
    refine mul_mem ?_ (prod_mem fun v hv ↦ ?_)
    · rw [polyJetEquivRel_C]
      exact (stage (MvPolynomial ι R) ι α r).algebraMap_mem (C (p.coeff s))
    · rw [map_pow]
      refine pow_mem ?_ _
      rcases v with j | ⟨a, I⟩
      · rw [polyJetEquivRel_X_base]
        exact (stage (MvPolynomial ι R) ι α r).algebraMap_mem (X j)
      · rw [polyJetEquivRel_X_field]
        exact X_mem_stage (hp a I ((MvPolynomial.mem_vars_iff_mem_support _).mpr ⟨s, hs, hv⟩))
  · intro hp
    have hback : ∀ q ∈ stage (MvPolynomial ι R) ι α r,
        (polyJetEquivRel R ι α).symm q ∈ PolynomialJet.stage R ι α r := by
      intro q hq
      induction hq using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨⟨a, I⟩, hI, rfl⟩ := hx
        rw [polyJetEquivRel_symm_X]
        exact PolynomialJet.X_field_mem_stage r a I hI
      | algebraMap b =>
        rw [MvPolynomial.algebraMap_eq, polyJetEquivRel_symm_C]
        induction b using MvPolynomial.induction_on with
        | C c =>
          rw [MvPolynomial.rename_C]
          exact (PolynomialJet.stage R ι α r).algebraMap_mem c
        | add p q hp hq =>
          rw [map_add]
          exact add_mem hp hq
        | mul_X p j hp =>
          rw [map_mul, MvPolynomial.rename_X]
          exact mul_mem hp (PolynomialJet.X_base_mem_stage r j)
      | add x y _ _ hx hy =>
        rw [map_add]
        exact add_mem hx hy
      | mul x y _ _ hx hy =>
        rw [map_mul]
        exact mul_mem hx hy
    simpa using hback _ hp

end PolynomialBase

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

/-- On zero-forms, `totalDerivForm δ i` acts by `totalDeriv δ i`. -/
@[simp]
theorem totalDerivForm_algebraMap (δ : ι → Derivation R B B) (i : ι) (p : RelJetAlgebra B ι α) :
    totalDerivForm δ i (algebraMap (RelJetAlgebra B ι α) (VertForms B ι α) p) =
      algebraMap (RelJetAlgebra B ι α) (VertForms B ι α) (totalDeriv δ i p) :=
  Derivation.deRhamLieDeriv_algebraMap _ _ p

/-- On vertical generator one-forms `duᵃ_I`, `totalDerivForm δ i` shifts `I ↦ I + eᵢ`. -/
@[simp]
theorem totalDerivForm_ι_D_X (δ : ι → Derivation R B B) (i : ι) (a : α) (I : ι →₀ ℕ) :
    totalDerivForm δ i
        (ExteriorAlgebra.ι (RelJetAlgebra B ι α)
          (KaehlerDifferential.D B (RelJetAlgebra B ι α) (X (a, I)))) =
      ExteriorAlgebra.ι (RelJetAlgebra B ι α)
        (KaehlerDifferential.D B (RelJetAlgebra B ι α) (X (a, I + Finsupp.single i 1))) := by
  simp [totalDerivForm]

/-- `totalDerivForm δ i` satisfies the degree-zero Leibniz rule on wedge products. -/
theorem totalDerivForm_mul (δ : ι → Derivation R B B) (i : ι) (ω η : VertForms B ι α) :
    totalDerivForm δ i (ω * η) = totalDerivForm δ i ω * η + ω * totalDerivForm δ i η :=
  Derivation.deRhamLieDeriv_mul _ _ ω η

/-- `totalDerivForm δ i` annihilates `1`. -/
@[simp]
theorem totalDerivForm_one (δ : ι → Derivation R B B) (i : ι) :
    totalDerivForm δ i (1 : VertForms B ι α) = 0 :=
  Derivation.deRhamLieDeriv_one _ _

/-- `totalDerivForm δ i` commutes with the grade involution on vertical forms. -/
theorem totalDerivForm_involute (δ : ι → Derivation R B B) (i : ι) (ω : VertForms B ι α) :
    totalDerivForm δ i
        (CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _)) ω) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _))
        (totalDerivForm δ i ω) :=
  Derivation.deRhamLieDeriv_involute _ _ ω

/-- `totalDerivForm δ i` preserves vertical exterior degree. -/
theorem totalDerivForm_mem_exteriorPower (δ : ι → Derivation R B B) (i : ι) {q : ℕ}
    {ω : VertForms B ι α} (hω : ω ∈ ⋀[RelJetAlgebra B ι α]^q (Ω[RelJetAlgebra B ι α⁄B])) :
    totalDerivForm δ i ω ∈ ⋀[RelJetAlgebra B ι α]^q (Ω[RelJetAlgebra B ι α⁄B]) :=
  Derivation.deRhamLieDeriv_mem_exteriorPower _ _ hω

/-- **Commutation of `d_alg` and `Dᵢ`**: the algebraic vertical exterior derivative commutes with
total differentiation on all vertical forms. -/
theorem dAlg_totalDerivForm (δ : ι → Derivation R B B) (i : ι) (ω : VertForms B ι α) :
    dAlg B ι α (totalDerivForm δ i ω) = totalDerivForm δ i (dAlg B ι α ω) :=
  Derivation.extDeriv_deRhamLieDeriv (totalDeriv δ i) (fun b ↦ by simp) ω

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

/-- A zero-form in `stage B ι α r` lies in `vertStage B ι α r`. -/
theorem algebraMap_mem_vertStage {r : ℕ} {p : RelJetAlgebra B ι α} (hp : p ∈ stage B ι α r) :
    algebraMap (RelJetAlgebra B ι α) (VertForms B ι α) p ∈ vertStage B ι α r :=
  KaehlerDeRham.algebraMap_mem_supportedForms hp

/-- A vertical generator one-form `duᵃ_I` lies in `vertStage B ι α r` whenever `I.degree ≤ r`. -/
theorem ι_D_X_mem_vertStage {r : ℕ} {a : α} {I : ι →₀ ℕ} (hI : I.degree ≤ r) :
    ExteriorAlgebra.ι (RelJetAlgebra B ι α)
      (KaehlerDifferential.D B (RelJetAlgebra B ι α) (X (a, I))) ∈ vertStage B ι α r :=
  KaehlerDeRham.ι_D_X_mem_supportedForms hI

/-- The grade involution preserves every finite vertical stage `vertStage B ι α r`. -/
theorem involute_mem_vertStage {r : ℕ} {ω : VertForms B ι α} (hω : ω ∈ vertStage B ι α r) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _)) ω ∈
      vertStage B ι α r :=
  KaehlerDeRham.involute_mem_supportedForms hω

/-- Every vertical form belongs to some finite vertical stage. -/
theorem exists_mem_vertStage (ω : VertForms B ι α) : ∃ r, ω ∈ vertStage B ι α r := by
  obtain ⟨s, hs⟩ := KaehlerDeRham.exists_mem_supportedForms_finset ω
  refine ⟨s.sup (fun aI ↦ aI.2.degree), ?_⟩
  exact KaehlerDeRham.supportedForms_mono
    (fun aI haI ↦ Finset.le_sup (f := fun x : α × (ι →₀ ℕ) ↦ x.2.degree) haI) hs

/-- `dAlg` preserves every finite vertical stage `vertStage B ι α r`. -/
theorem dAlg_mem_vertStage {r : ℕ} {ω : VertForms B ι α} (hω : ω ∈ vertStage B ι α r) :
    dAlg B ι α ω ∈ vertStage B ι α r :=
  KaehlerDeRham.extDeriv_mem_supportedForms hω

/-- `totalDerivForm δ i` raises the vertical stage by at most one. -/
theorem totalDerivForm_mem_vertStage (δ : ι → Derivation R B B) (i : ι) {r : ℕ}
    {ω : VertForms B ι α} (hω : ω ∈ vertStage B ι α r) :
    totalDerivForm δ i ω ∈ vertStage B ι α (r + 1) :=
  KaehlerDeRham.deRhamLieDeriv_mem_supportedForms (fun b ↦ by simp)
    (fun _ h ↦ le_trans h (Nat.le_succ r)) (fun _ hp ↦ totalDeriv_mem_stage δ i hp) hω

end VerticalComplex

section UnsignedDoubleComplex

variable (R B ι α : Type*) [CommRing R] [CommRing B] [Algebra R B]

/-- The vertical differential `d_alg ⊗ id` on `VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)`. -/
def dAlgTensor :
    Module.End R (VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :=
  ((dAlg B ι α).restrictScalars R).rTensor (ExteriorAlgebra R (ι →₀ R))

variable {R B ι α}

/-- Action of `dAlgTensor` on a pure tensor `α ⊗ₜ β`. -/
@[simp]
theorem dAlgTensor_tmul (ω : VertForms B ι α) (β : ExteriorAlgebra R (ι →₀ R)) :
    dAlgTensor R B ι α (ω ⊗ₜ[R] β) = dAlg B ι α ω ⊗ₜ[R] β := by
  simp [dAlgTensor]

/-- `dAlgTensor` squares to zero. -/
@[simp]
theorem dAlgTensor_dAlgTensor (x : VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :
    dAlgTensor R B ι α (dAlgTensor R B ι α x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul ω β => simp [KaehlerDeRham.extDeriv_extDeriv]
  | add x y hx hy => simp [hx, hy]

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

/-- **Commutation in the unsigned double-differential complex**: `d_alg` and `D_H⁰` commute with
no sign. -/
theorem dAlgTensor_horizDerivUnsigned [Fintype ι] (δ : ι → Derivation R B B)
    (x : VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :
    dAlgTensor R B ι α (horizDerivUnsigned δ x) =
      horizDerivUnsigned δ (dAlgTensor R B ι α x) := by
  induction x using TensorProduct.inductionOn with
  | tmul ω β =>
    simp only [horizDerivUnsigned_tmul, dAlgTensor_tmul, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [dAlg_totalDerivForm]
  | add x y hx hy => simp [hx, hy]

/-- **Nilpotency of the unsigned horizontal differential**: `(D_H⁰)² = 0` whenever the base
derivations commute, over any commutative ring `R` (including in characteristic two). -/
theorem horizDerivUnsigned_horizDerivUnsigned [Fintype ι] {δ : ι → Derivation R B B}
    (hδ : ∀ i j b, δ i (δ j b) = δ j (δ i b))
    (x : VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :
    horizDerivUnsigned δ (horizDerivUnsigned δ x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul ω β =>
    simp only [horizDerivUnsigned_tmul, map_sum]
    refine Finset.sum_sum_eq_zero_of_diag Finset.univ
      (f := fun i j ↦ totalDerivForm δ j (totalDerivForm δ i ω) ⊗ₜ[R]
        (ExteriorAlgebra.ι R (Finsupp.single j (1 : R)) *
          (ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) * β)))
      (fun i _ ↦ by rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, TensorProduct.tmul_zero])
      (fun i _ j _ _ ↦ ?_)
    rw [totalDerivForm_comm (hδ j i), ← TensorProduct.tmul_add, ← mul_assoc, ← mul_assoc,
      ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul, TensorProduct.tmul_zero]
  | add x y hx hy => simp [hx, hy]

end UnsignedDoubleComplex

end

end RelJetAlgebra
end TauCeti
