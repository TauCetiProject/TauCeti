/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Variational.PolynomialJet.Filtration
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Contact Forms and the Splitting `d = d_H + d_V` on Polynomial Jets

This file develops differential forms on the polynomial jet algebra `TauCeti.PolynomialJet R ι α`
over an arbitrary commutative ring `R`, introduces the coordinate one-forms `baseDx μ` and
`du a I` together with the contact one-forms
`θᵃ_I = duᵃ_I - ∑ μ, uᵃ_(I+e_μ) • dx^μ`, and constructs the canonical `R`-algebra isomorphism
`TauCeti.PolynomialJet.contactEquiv` identifying `RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α`
with `TauCeti.PolynomialJet.JetForms R ι α`.

## Main definitions

* `TauCeti.PolynomialJet.JetForms R ι α`: the exterior algebra of Kähler differentials
  `ExteriorAlgebra (PolynomialJet R ι α) (Ω[PolynomialJet R ι α⁄R])`.
* `TauCeti.PolynomialJet.d R ι α`: the total exterior derivative on `JetForms R ι α`.
* `TauCeti.PolynomialJet.baseDx R ι α μ`: the base coordinate one-form `dx^μ`.
* `TauCeti.PolynomialJet.du R ι α a I`: the field-jet coordinate one-form `duᵃ_I`.
* `TauCeti.PolynomialJet.contactForm R ι α a I`: the contact one-form
  `duᵃ_I - ∑ μ, uᵃ_(I+e_μ) • dx^μ`.
* `TauCeti.PolynomialJet.jetFormStage R ι α r`: the finite-order subalgebra of jet forms using
  field coordinates and differentials of order at most `r` (with unrestricted base polynomial
  dependence).
* `TauCeti.PolynomialJet.contactEquiv R ι α`: the canonical `R`-algebra equivalence
  `RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α ≃ₐ[R] JetForms R ι α` sending `dx μ ↦ baseDx μ`
  and `theta a I ↦ contactForm a I`.

## Main results

* `TauCeti.PolynomialJet.d_contactForm`:
  `d (contactForm a I) = ∑ μ, baseDx μ * contactForm a (I + e_μ)`.
* `TauCeti.PolynomialJet.d_contactEquiv`: the splitting `d = d_H + d_V` under `contactEquiv`,
  `d (contactEquiv ω) = contactEquiv (dH (fun i ↦ MvPolynomial.pderiv i) ω + dV ω)`, over any
  commutative ring `R`.
* `TauCeti.PolynomialJet.contactEquiv_mem_jetFormStage` and
  `TauCeti.PolynomialJet.contactEquiv_symm_mem_stageForm`: cofinality of the finite-order stage
  filtrations, with exact order shift `+ 1` in each direction.

## References

* I. M. Anderson, *The Variational Bicomplex*, Utah State University technical report (1989),
  Chapter 1.
* R. E. Borcherds, *Quantum Field Theory* (lecture notes), p. 49.
-/

open MvPolynomial
open scoped ExteriorAlgebra TensorProduct

namespace TauCeti

namespace PolynomialJet

noncomputable section

public section

section Forms

variable (R ι α : Type*) [CommRing R]

/-- The algebra of polynomial differential forms on `PolynomialJet R ι α` over `R`. -/
abbrev JetForms :=
  ExteriorAlgebra (PolynomialJet R ι α) (Ω[PolynomialJet R ι α⁄R])

/-- The total exterior derivative on `JetForms R ι α`. -/
abbrev d : JetForms R ι α →ₗ[R] JetForms R ι α :=
  MvPolynomialDeRham.d R (ι ⊕ (α × (ι →₀ ℕ)))

/-- The base coordinate one-form `dx^μ` in `JetForms R ι α`. -/
def baseDx (μ : ι) : JetForms R ι α :=
  ExteriorAlgebra.ι (PolynomialJet R ι α)
    (KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inl μ)))

/-- The field-jet coordinate one-form `duᵃ_I` in `JetForms R ι α`. -/
def du (a : α) (I : ι →₀ ℕ) : JetForms R ι α :=
  ExteriorAlgebra.ι (PolynomialJet R ι α)
    (KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inr (a, I))))

/-- The contact one-form `θᵃ_I = duᵃ_I - ∑ μ, uᵃ_(I+e_μ) • dx^μ` in `JetForms R ι α`. -/
def contactForm [Fintype ι] (a : α) (I : ι →₀ ℕ) : JetForms R ι α :=
  du R ι α a I -
    ∑ μ : ι, (X (Sum.inr (a, I + Finsupp.single μ 1)) : PolynomialJet R ι α) • baseDx R ι α μ

/-- The finite-order subalgebra of jet forms supported on base coordinates and field-jet
coordinates of order at most `r`. -/
def jetFormStage (r : ℕ) : Subalgebra R (JetForms R ι α) :=
  MvPolynomialDeRham.supportedForms R
    {v : ι ⊕ (α × (ι →₀ ℕ)) | Sum.elim (fun _ ↦ True) (fun aI ↦ aI.2.degree ≤ r) v}

variable {R ι α}

/-- `d` annihilates `baseDx μ`. -/
@[simp]
theorem d_baseDx (μ : ι) : d R ι α (baseDx R ι α μ) = 0 :=
  MvPolynomialDeRham.d_ι_D_X (Sum.inl μ)

/-- `d` annihilates `du a I`. -/
@[simp]
theorem d_du (a : α) (I : ι →₀ ℕ) : d R ι α (du R ι α a I) = 0 :=
  MvPolynomialDeRham.d_ι_D_X (Sum.inr (a, I))

/-- `d` sends the base coordinate zero-form `x_μ` to `baseDx μ`. -/
theorem d_algebraMap_X_base (μ : ι) :
    d R ι α (algebraMap (PolynomialJet R ι α) (JetForms R ι α) (X (Sum.inl μ))) =
      baseDx R ι α μ :=
  MvPolynomialDeRham.d_algebraMap (X (Sum.inl μ))

/-- `d` sends the field-jet coordinate zero-form `uᵃ_I` to `du a I`. -/
theorem d_algebraMap_X_field (a : α) (I : ι →₀ ℕ) :
    d R ι α (algebraMap (PolynomialJet R ι α) (JetForms R ι α) (X (Sum.inr (a, I)))) =
      du R ι α a I :=
  MvPolynomialDeRham.d_algebraMap (X (Sum.inr (a, I)))

/-- A double sum over a finite set vanishes in any additive group when diagonal terms vanish and
symmetric pairs sum to zero (characteristic-free). -/
private theorem sum_sum_eq_zero_of_antisymm {M : Type*} [AddCommGroup M] (s : Finset ι)
    (f : ι → ι → M) (hdiag : ∀ i, f i i = 0) (hsym : ∀ i j, f i j + f j i = 0) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, hdiag, zero_add, Finset.sum_add_distrib, ih, add_zero]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ hsym a i

/-- **Exterior derivative of a contact one-form**:
`d (contactForm a I) = ∑ μ, baseDx μ * contactForm a (I + e_μ)`, valid over any commutative
ring `R` (including characteristic two). -/
theorem d_contactForm [Fintype ι] (a : α) (I : ι →₀ ℕ) :
    d R ι α (contactForm R ι α a I) =
      ∑ μ : ι, baseDx R ι α μ * contactForm R ι α a (I + Finsupp.single μ 1) := by
  have h1 : d R ι α (contactForm R ι α a I) =
      ∑ μ : ι, baseDx R ι α μ * du R ι α a (I + Finsupp.single μ 1) := by
    rw [contactForm, map_sub, d_du, zero_sub, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [Algebra.smul_def, MvPolynomialDeRham.d_mul, d_algebraMap_X_field, d_baseDx, mul_zero,
      add_zero]
    have hswap : du R ι α a (I + Finsupp.single μ 1) * baseDx R ι α μ +
        baseDx R ι α μ * du R ι α a (I + Finsupp.single μ 1) = 0 :=
      ExteriorAlgebra.ι_add_mul_swap _ _
    exact eq_neg_of_add_eq_zero_right hswap |>.symm
  have h2 : ∑ μ : ι, baseDx R ι α μ * contactForm R ι α a (I + Finsupp.single μ 1) =
      ∑ μ : ι, baseDx R ι α μ * du R ι α a (I + Finsupp.single μ 1) := by
    have hzero :
        ∑ μ : ι, ∑ ν : ι,
          (X (Sum.inr (a, I + Finsupp.single μ 1 + Finsupp.single ν 1)) : PolynomialJet R ι α) •
            (baseDx R ι α μ * baseDx R ι α ν) = 0 := by
      refine sum_sum_eq_zero_of_antisymm Finset.univ _ (fun μ ↦ ?_) (fun μ ν ↦ ?_)
      · rw [baseDx, ExteriorAlgebra.ι_sq_zero, smul_zero]
      · rw [add_assoc I (Finsupp.single ν 1), add_comm (Finsupp.single ν 1),
          ← add_assoc I, ← smul_add, baseDx, baseDx, ExteriorAlgebra.ι_add_mul_swap, smul_zero]
    simp only [contactForm, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_smul_comm]
    rw [hzero, sub_zero]
  rw [h1, h2]

/-- Increasing the jet-order bound enlarges `jetFormStage`. -/
theorem jetFormStage_mono : Monotone (jetFormStage R ι α) := by
  intro r s hrs
  refine MvPolynomialDeRham.supportedForms_mono ?_
  rintro (j | ⟨a, I⟩) h
  · trivial
  · exact h.trans hrs

/-- Every zero-form in `stage R ι α r` belongs to `jetFormStage R ι α r`. -/
theorem algebraMap_mem_jetFormStage {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) :
    algebraMap (PolynomialJet R ι α) (JetForms R ι α) p ∈ jetFormStage R ι α r := by
  refine MvPolynomialDeRham.algebraMap_mem_supportedForms ?_
  rw [MvPolynomial.mem_supported]
  rintro (j | ⟨a, I⟩) hv
  · trivial
  · exact (mem_stage_iff p r).mp hp a I hv

/-- Base coordinate one-forms `baseDx μ` belong to every finite stage `jetFormStage R ι α r`. -/
theorem baseDx_mem_jetFormStage (r : ℕ) (μ : ι) :
    baseDx R ι α μ ∈ jetFormStage R ι α r :=
  MvPolynomialDeRham.ι_D_X_mem_supportedForms (s := _) (i := Sum.inl μ) trivial

/-- Field-jet coordinate one-forms `du a I` with `I.degree ≤ r` belong to `jetFormStage R ι α r`.
-/
theorem du_mem_jetFormStage {r : ℕ} {a : α} {I : ι →₀ ℕ} (hI : I.degree ≤ r) :
    du R ι α a I ∈ jetFormStage R ι α r :=
  MvPolynomialDeRham.ι_D_X_mem_supportedForms (s := _) (i := Sum.inr (a, I)) hI

/-- A contact one-form `θᵃ_I` with `I.degree ≤ r` belongs to the next stage
`jetFormStage R ι α (r + 1)`. -/
theorem contactForm_mem_jetFormStage [Fintype ι] {r : ℕ} {a : α} {I : ι →₀ ℕ} (hI : I.degree ≤ r) :
    contactForm R ι α a I ∈ jetFormStage R ι α (r + 1) := by
  rw [contactForm]
  refine sub_mem (du_mem_jetFormStage (hI.trans (Nat.le_succ r))) (sum_mem fun μ _ ↦ ?_)
  rw [Algebra.smul_def]
  refine mul_mem (algebraMap_mem_jetFormStage ?_) (baseDx_mem_jetFormStage (r + 1) μ)
  exact X_field_mem_stage (r + 1) a (I + Finsupp.single μ 1)
    (by simpa using Nat.add_le_add_right hI 1)

/-- Every polynomial jet form lies in some finite stage `jetFormStage R ι α r`. -/
theorem exists_mem_jetFormStage (η : JetForms R ι α) : ∃ r, η ∈ jetFormStage R ι α r := by
  obtain ⟨s, hs⟩ := MvPolynomialDeRham.exists_mem_supportedForms_finset η
  refine ⟨s.sup (Sum.elim (fun _ ↦ 0) (fun aI ↦ aI.2.degree)), ?_⟩
  refine MvPolynomialDeRham.supportedForms_mono ?_ hs
  rintro (j | ⟨a, I⟩) hv
  · trivial
  · exact Finset.le_sup (f := Sum.elim (fun _ ↦ 0) (fun aI : α × (ι →₀ ℕ) ↦ aI.2.degree)) hv

/-- The total exterior derivative `d` preserves every finite stage `jetFormStage R ι α r`. -/
theorem d_mem_jetFormStage {r : ℕ} {η : JetForms R ι α} (hη : η ∈ jetFormStage R ι α r) :
    d R ι α η ∈ jetFormStage R ι α r :=
  MvPolynomialDeRham.d_mem_supportedForms hη

end Forms

section ContactSplitting

/-- Auxiliary exterior-algebra equivalence induced by a linear equivalence on the underlying
module. -/
private def exteriorMapEquiv {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    ExteriorAlgebra A M ≃ₐ[A] ExteriorAlgebra A N :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap) (ExteriorAlgebra.map e.symm.toLinearMap)
    (by ext m; simp) (by ext m; simp)

private theorem exteriorMapEquiv_ι {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (m : M) :
    exteriorMapEquiv e (ExteriorAlgebra.ι A m) = ExteriorAlgebra.ι A (e m) :=
  ExteriorAlgebra.map_apply_ι e.toLinearMap m

private theorem exteriorMapEquiv_involute {A M N : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (x : ExteriorAlgebra A M) :
    exteriorMapEquiv e (CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm A N)) (exteriorMapEquiv e x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap a =>
    rw [AlgHom.commutes, AlgEquiv.commutes, AlgHom.commutes]
  | ι m =>
    simp [exteriorMapEquiv]
  | mul x y hx hy =>
    simp only [map_mul, hx, hy]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- Base-change identification `S ⊗[R] ExteriorAlgebra R (σ →₀ R) ≃ₐ[S] ExteriorAlgebra S (σ →₀ S)`.
-/
private def exteriorFinsuppBaseChange (R S σ : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    S ⊗[R] ExteriorAlgebra R (σ →₀ R) ≃ₐ[S] ExteriorAlgebra S (σ →₀ S) :=
  (ExteriorAlgebra.baseChangeEquiv R (σ →₀ R) S).trans
    (exteriorMapEquiv (by classical exact TensorProduct.finsuppScalarRight R S S σ))

private theorem exteriorFinsuppBaseChange_tmul_one {R S σ : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (s : S) :
    exteriorFinsuppBaseChange R S σ (s ⊗ₜ[R] (1 : ExteriorAlgebra R (σ →₀ R))) =
      algebraMap S (ExteriorAlgebra S (σ →₀ S)) s := by
  have h : s ⊗ₜ[R] (1 : ExteriorAlgebra R (σ →₀ R)) =
      algebraMap S (S ⊗[R] ExteriorAlgebra R (σ →₀ R)) s := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h, AlgEquiv.commutes]

private theorem exteriorFinsuppBaseChange_one_tmul_ι_single {R S σ : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (i : σ) :
    exteriorFinsuppBaseChange R S σ
        ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ι R (Finsupp.single i (1 : R))) =
      ExteriorAlgebra.ι S (Finsupp.single i (1 : S)) := by
  classical
  rw [exteriorFinsuppBaseChange, AlgEquiv.trans_apply, ExteriorAlgebra.baseChangeEquiv_apply,
    exteriorMapEquiv_ι]
  congr 1
  refine Finsupp.ext fun j ↦ ?_
  simp only [TensorProduct.finsuppScalarRight_apply, LinearMap.lTensor_tmul, Finsupp.lapply_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Finsupp.single_eq_of_ne (Ne.symm hij)]

/-- Functorial transport `ExteriorAlgebra S₁ (σ →₀ S₁) ≃ₐ[R] ExteriorAlgebra S₂ (σ →₀ S₂)` along an
`R`-algebra equivalence `e : S₁ ≃ₐ[R] S₂`. -/
private def exteriorFinsuppChangeRing {R S₁ S₂ : Type*} (σ : Type*) [CommRing R] [CommRing S₁]
    [CommRing S₂] [Algebra R S₁] [Algebra R S₂] (e : S₁ ≃ₐ[R] S₂) :
    ExteriorAlgebra S₁ (σ →₀ S₁) ≃ₐ[R] ExteriorAlgebra S₂ (σ →₀ S₂) :=
  ((exteriorFinsuppBaseChange R S₁ σ).symm.restrictScalars R).trans
    ((Algebra.TensorProduct.congr e
        (AlgEquiv.refl (R := R) (A₁ := ExteriorAlgebra R (σ →₀ R)))).trans
      ((exteriorFinsuppBaseChange R S₂ σ).restrictScalars R))

private theorem exteriorFinsuppChangeRing_algebraMap {R S₁ S₂ σ : Type*} [CommRing R] [CommRing S₁]
    [CommRing S₂] [Algebra R S₁] [Algebra R S₂] (e : S₁ ≃ₐ[R] S₂) (s : S₁) :
    exteriorFinsuppChangeRing σ e (algebraMap S₁ (ExteriorAlgebra S₁ (σ →₀ S₁)) s) =
      algebraMap S₂ (ExteriorAlgebra S₂ (σ →₀ S₂)) (e s) := by
  rw [← exteriorFinsuppBaseChange_tmul_one (R := R) (σ := σ), exteriorFinsuppChangeRing,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
    AlgEquiv.coe_refl, id_eq, exteriorFinsuppBaseChange_tmul_one]

private theorem exteriorFinsuppChangeRing_ι_single {R S₁ S₂ σ : Type*} [CommRing R] [CommRing S₁]
    [CommRing S₂] [Algebra R S₁] [Algebra R S₂] (e : S₁ ≃ₐ[R] S₂) (i : σ) :
    exteriorFinsuppChangeRing σ e (ExteriorAlgebra.ι S₁ (Finsupp.single i (1 : S₁))) =
      ExteriorAlgebra.ι S₂ (Finsupp.single i (1 : S₂)) := by
  rw [← exteriorFinsuppBaseChange_one_tmul_ι_single (R := R), exteriorFinsuppChangeRing,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, map_one,
    AlgEquiv.coe_refl, id_eq, exteriorFinsuppBaseChange_one_tmul_ι_single]

private theorem exteriorFinsuppChangeRing_involute {R S₁ S₂ σ : Type*} [CommRing R] [CommRing S₁]
    [CommRing S₂] [Algebra R S₁] [Algebra R S₂] (e : S₁ ≃ₐ[R] S₂)
    (x : ExteriorAlgebra S₁ (σ →₀ S₁)) :
    exteriorFinsuppChangeRing σ e
        (CliffordAlgebra.involute (Q := (0 : QuadraticForm S₁ (σ →₀ S₁))) x) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm S₂ (σ →₀ S₂)))
        (exteriorFinsuppChangeRing σ e x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap s =>
    rw [AlgHom.commutes, exteriorFinsuppChangeRing_algebraMap, AlgHom.commutes]
  | ι v =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]
    | single i s =>
      have hsingle : ExteriorAlgebra.ι S₁ (Finsupp.single i s) =
          algebraMap S₁ (ExteriorAlgebra S₁ (σ →₀ S₁)) s *
            ExteriorAlgebra.ι S₁ (Finsupp.single i (1 : S₁)) := by
        rw [← Algebra.smul_def, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsingle, map_mul, AlgHom.commutes, CliffordAlgebra.involute_ι, map_mul, map_neg,
        exteriorFinsuppChangeRing_algebraMap, exteriorFinsuppChangeRing_ι_single, map_mul,
        exteriorFinsuppChangeRing_algebraMap, exteriorFinsuppChangeRing_ι_single, map_mul,
        AlgHom.commutes, CliffordAlgebra.involute_ι]
  | mul x y hx hy =>
    simp only [map_mul, hx, hy]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- Forward contact shear on `(ι ⊕ (α × (ι →₀ ℕ))) →₀ PolynomialJet R ι α`, mapping
`e_(inl μ) ↦ e_(inl μ)` and `e_(inr (a, I)) ↦ e_(inr (a, I)) - ∑ μ, uᵃ_(I+e_μ) • e_(inl μ)`. -/
private def shearFwd (R ι α : Type*) [CommRing R] [Fintype ι] :
    ((ι ⊕ (α × (ι →₀ ℕ))) →₀ PolynomialJet R ι α) →ₗ[PolynomialJet R ι α]
      ((ι ⊕ (α × (ι →₀ ℕ))) →₀ PolynomialJet R ι α) :=
  Finsupp.lsum (PolynomialJet R ι α) fun v ↦
    match v with
    | Sum.inl μ => Finsupp.lsingle (Sum.inl μ)
    | Sum.inr (a, I) =>
      Finsupp.lsingle (Sum.inr (a, I)) -
        ∑ μ : ι, (X (Sum.inr (a, I + Finsupp.single μ 1)) : PolynomialJet R ι α) •
          Finsupp.lsingle (Sum.inl μ)

/-- Inverse contact shear on `(ι ⊕ (α × (ι →₀ ℕ))) →₀ PolynomialJet R ι α`, mapping
`e_(inl μ) ↦ e_(inl μ)` and `e_(inr (a, I)) ↦ e_(inr (a, I)) + ∑ μ, uᵃ_(I+e_μ) • e_(inl μ)`. -/
private def shearInv (R ι α : Type*) [CommRing R] [Fintype ι] :
    ((ι ⊕ (α × (ι →₀ ℕ))) →₀ PolynomialJet R ι α) →ₗ[PolynomialJet R ι α]
      ((ι ⊕ (α × (ι →₀ ℕ))) →₀ PolynomialJet R ι α) :=
  Finsupp.lsum (PolynomialJet R ι α) fun v ↦
    match v with
    | Sum.inl μ => Finsupp.lsingle (Sum.inl μ)
    | Sum.inr (a, I) =>
      Finsupp.lsingle (Sum.inr (a, I)) +
        ∑ μ : ι, (X (Sum.inr (a, I + Finsupp.single μ 1)) : PolynomialJet R ι α) •
          Finsupp.lsingle (Sum.inl μ)

private theorem shearFwd_single_inl {R ι α : Type*} [CommRing R] [Fintype ι] (μ : ι)
    (p : PolynomialJet R ι α) :
    shearFwd R ι α (Finsupp.single (Sum.inl μ) p) = Finsupp.single (Sum.inl μ) p := by
  simp [shearFwd]

private theorem shearFwd_single_inr {R ι α : Type*} [CommRing R] [Fintype ι] (a : α)
    (I : ι →₀ ℕ) (p : PolynomialJet R ι α) :
    shearFwd R ι α (Finsupp.single (Sum.inr (a, I)) p) =
      Finsupp.single (Sum.inr (a, I)) p -
        ∑ μ : ι, (X (Sum.inr (a, I + Finsupp.single μ 1)) : PolynomialJet R ι α) •
          Finsupp.single (Sum.inl μ) p := by
  simp [shearFwd]

private theorem shearInv_single_inl {R ι α : Type*} [CommRing R] [Fintype ι] (μ : ι)
    (p : PolynomialJet R ι α) :
    shearInv R ι α (Finsupp.single (Sum.inl μ) p) = Finsupp.single (Sum.inl μ) p := by
  simp [shearInv]

private theorem shearInv_single_inr {R ι α : Type*} [CommRing R] [Fintype ι] (a : α)
    (I : ι →₀ ℕ) (p : PolynomialJet R ι α) :
    shearInv R ι α (Finsupp.single (Sum.inr (a, I)) p) =
      Finsupp.single (Sum.inr (a, I)) p +
        ∑ μ : ι, (X (Sum.inr (a, I + Finsupp.single μ 1)) : PolynomialJet R ι α) •
          Finsupp.single (Sum.inl μ) p := by
  simp [shearInv]

/-- The contact-basis shear automorphism on `(ι ⊕ (α × (ι →₀ ℕ))) →₀ PolynomialJet R ι α`. -/
private def shearFinsupp (R ι α : Type*) [CommRing R] [Fintype ι] :
    ((ι ⊕ (α × (ι →₀ ℕ))) →₀ PolynomialJet R ι α) ≃ₗ[PolynomialJet R ι α]
      ((ι ⊕ (α × (ι →₀ ℕ))) →₀ PolynomialJet R ι α) :=
  LinearEquiv.ofLinearMap (shearFwd R ι α) (shearInv R ι α)
    (by
      apply Finsupp.lhom_ext'
      rintro (μ | ⟨a, I⟩)
      · apply LinearMap.ext
        intro p
        simp [shearFwd_single_inl, shearInv_single_inl]
      · apply LinearMap.ext
        intro p
        simp [shearFwd_single_inr, shearInv_single_inr, shearFwd_single_inl])
    (by
      apply Finsupp.lhom_ext'
      rintro (μ | ⟨a, I⟩)
      · apply LinearMap.ext
        intro p
        simp [shearFwd_single_inl, shearInv_single_inl]
      · apply LinearMap.ext
        intro p
        simp [shearFwd_single_inr, shearInv_single_inr, shearInv_single_inl])

/-- Identifying the generator module of `Bicomplex (MvPolynomial ι R) ι α` with
`(ι ⊕ (α × (ι →₀ ℕ))) →₀ RelJetAlgebra (MvPolynomial ι R) ι α`. -/
private def bicomplexModuleEquiv (R ι α : Type*) [CommRing R] :
    ((ι →₀ RelJetAlgebra (MvPolynomial ι R) ι α) ×
        Ω[RelJetAlgebra (MvPolynomial ι R) ι α⁄MvPolynomial ι R]) ≃ₗ[
      RelJetAlgebra (MvPolynomial ι R) ι α]
      ((ι ⊕ (α × (ι →₀ ℕ))) →₀ RelJetAlgebra (MvPolynomial ι R) ι α) :=
  (LinearEquiv.prodCongr
      (LinearEquiv.refl (RelJetAlgebra (MvPolynomial ι R) ι α) _)
      (KaehlerDifferential.mvPolynomialBasis (MvPolynomial ι R) (α × (ι →₀ ℕ))).repr).trans
    (Finsupp.sumFinsuppLEquivProdFinsupp (RelJetAlgebra (MvPolynomial ι R) ι α)).symm

variable (R ι α : Type*) [CommRing R] [Fintype ι]

/-- **The contact splitting isomorphism**: canonical `R`-algebra equivalence identifying the
relative polynomial variational bicomplex `RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α` with
the polynomial jet de Rham algebra `JetForms R ι α`, sending `dx μ ↦ baseDx μ` and
`theta a I ↦ contactForm a I`. -/
def contactEquiv :
    RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α ≃ₐ[R] JetForms R ι α :=
  let toJet :=
    (shearFinsupp R ι α).trans
      (KaehlerDifferential.mvPolynomialBasis R (ι ⊕ (α × (ι →₀ ℕ)))).repr.symm
  ((exteriorMapEquiv (bicomplexModuleEquiv R ι α)).restrictScalars R).trans
    ((exteriorFinsuppChangeRing (ι ⊕ (α × (ι →₀ ℕ)))
        (RelJetAlgebra.polyJetEquivRel R ι α).symm).trans
      ((exteriorMapEquiv toJet).restrictScalars R))

variable {R ι α}

/-- On zero-forms, `contactEquiv` acts by `(polyJetEquivRel R ι α).symm`. -/
@[simp]
theorem contactEquiv_algebraMap (p : RelJetAlgebra (MvPolynomial ι R) ι α) :
    contactEquiv R ι α
        (algebraMap (RelJetAlgebra (MvPolynomial ι R) ι α)
          (RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α) p) =
      algebraMap (PolynomialJet R ι α) (JetForms R ι α)
        ((RelJetAlgebra.polyJetEquivRel R ι α).symm p) := by
  rw [contactEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.commutes, exteriorFinsuppChangeRing_algebraMap,
    AlgEquiv.commutes]

/-- On zero-forms transported via `polyJetEquivRel`, `contactEquiv` is the identity on
`PolynomialJet R ι α`. -/
theorem contactEquiv_algebraMap_polyJetEquivRel (q : PolynomialJet R ι α) :
    contactEquiv R ι α
        (algebraMap (RelJetAlgebra (MvPolynomial ι R) ι α)
          (RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α)
          (RelJetAlgebra.polyJetEquivRel R ι α q)) =
      algebraMap (PolynomialJet R ι α) (JetForms R ι α) q := by
  rw [contactEquiv_algebraMap, AlgEquiv.symm_apply_apply]

/-- `contactEquiv` sends the horizontal generator `dx μ` to `baseDx μ`. -/
@[simp]
theorem contactEquiv_dx (μ : ι) :
    contactEquiv R ι α (RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ) =
      baseDx R ι α μ := by
  rw [RelJetAlgebra.Bicomplex.dx_eq_ι, contactEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.restrictScalars_apply]
  have hmod : bicomplexModuleEquiv R ι α
      (Finsupp.single μ (1 : RelJetAlgebra (MvPolynomial ι R) ι α), 0) =
      Finsupp.single (Sum.inl μ) (1 : RelJetAlgebra (MvPolynomial ι R) ι α) := by
    classical
    refine Finsupp.ext fun v ↦ ?_
    rcases v with ν | aI
    · rw [bicomplexModuleEquiv, LinearEquiv.trans_apply,
        Finsupp.sumFinsuppLEquivProdFinsupp_symm_inl]
      simp [Finsupp.single_apply]
    · rw [bicomplexModuleEquiv, LinearEquiv.trans_apply,
        Finsupp.sumFinsuppLEquivProdFinsupp_symm_inr]
      simp
  rw [exteriorMapEquiv_ι, hmod, exteriorFinsuppChangeRing_ι_single, exteriorMapEquiv_ι,
    LinearEquiv.trans_apply, shearFinsupp, LinearEquiv.coe_ofLinearMap, shearFwd_single_inl,
    KaehlerDifferential.mvPolynomialBasis_repr_symm_single, one_smul]
  rfl

/-- `contactEquiv` sends the contact generator `theta a I` to `contactForm a I`. -/
@[simp]
theorem contactEquiv_theta (a : α) (I : ι →₀ ℕ) :
    contactEquiv R ι α (RelJetAlgebra.Bicomplex.theta (MvPolynomial ι R) ι α a I) =
      contactForm R ι α a I := by
  rw [RelJetAlgebra.Bicomplex.theta_eq_ι, contactEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.restrictScalars_apply]
  have hmod : bicomplexModuleEquiv R ι α
      (0, KaehlerDifferential.D (MvPolynomial ι R) (RelJetAlgebra (MvPolynomial ι R) ι α)
        (X (a, I))) =
      Finsupp.single (Sum.inr (a, I)) (1 : RelJetAlgebra (MvPolynomial ι R) ι α) := by
    classical
    refine Finsupp.ext fun v ↦ ?_
    rcases v with ν | bJ
    · rw [bicomplexModuleEquiv, LinearEquiv.trans_apply,
        Finsupp.sumFinsuppLEquivProdFinsupp_symm_inl]
      simp
    · rw [bicomplexModuleEquiv, LinearEquiv.trans_apply,
        Finsupp.sumFinsuppLEquivProdFinsupp_symm_inr]
      simp [KaehlerDifferential.mvPolynomialBasis_repr_D_X, Finsupp.single_apply]
  rw [exteriorMapEquiv_ι, hmod, exteriorFinsuppChangeRing_ι_single, exteriorMapEquiv_ι,
    LinearEquiv.trans_apply, shearFinsupp, LinearEquiv.coe_ofLinearMap, shearFwd_single_inr,
    map_sub, map_sum, KaehlerDifferential.mvPolynomialBasis_repr_symm_single, one_smul, map_sub,
    map_sum]
  rw [contactForm]
  congr 1
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [map_smul, KaehlerDifferential.mvPolynomialBasis_repr_symm_single, one_smul, map_smul]
  rfl

/-- `contactEquiv` sends scalar multiples `p • ω` to
`((polyJetEquivRel R ι α).symm p) • contactEquiv ω`. -/
theorem contactEquiv_smul (p : RelJetAlgebra (MvPolynomial ι R) ι α)
    (ω : RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α) :
    contactEquiv R ι α (p • ω) =
      ((RelJetAlgebra.polyJetEquivRel R ι α).symm p) • contactEquiv R ι α ω := by
  rw [Algebra.smul_def, map_mul, contactEquiv_algebraMap, ← Algebra.smul_def]

/-- `(contactEquiv R ι α).symm` acts on zero-forms by `polyJetEquivRel R ι α`. -/
@[simp]
theorem contactEquiv_symm_algebraMap (q : PolynomialJet R ι α) :
    (contactEquiv R ι α).symm (algebraMap (PolynomialJet R ι α) (JetForms R ι α) q) =
      algebraMap (RelJetAlgebra (MvPolynomial ι R) ι α)
        (RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α)
        (RelJetAlgebra.polyJetEquivRel R ι α q) := by
  apply (contactEquiv R ι α).injective
  rw [AlgEquiv.apply_symm_apply, contactEquiv_algebraMap_polyJetEquivRel]

/-- `(contactEquiv R ι α).symm` sends `baseDx μ` back to `dx μ`. -/
@[simp]
theorem contactEquiv_symm_baseDx (μ : ι) :
    (contactEquiv R ι α).symm (baseDx R ι α μ) =
      RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ := by
  apply (contactEquiv R ι α).injective
  rw [AlgEquiv.apply_symm_apply, contactEquiv_dx]

/-- `(contactEquiv R ι α).symm` sends `contactForm a I` back to `theta a I`. -/
@[simp]
theorem contactEquiv_symm_contactForm (a : α) (I : ι →₀ ℕ) :
    (contactEquiv R ι α).symm (contactForm R ι α a I) =
      RelJetAlgebra.Bicomplex.theta (MvPolynomial ι R) ι α a I := by
  apply (contactEquiv R ι α).injective
  rw [AlgEquiv.apply_symm_apply, contactEquiv_theta]

/-- `(contactEquiv R ι α).symm` splits `du a I` into its vertical contact part `θᵃ_I` plus its
horizontal part `∑ μ, uᵃ_(I+e_μ) • dx^μ`. -/
@[simp]
theorem contactEquiv_symm_du (a : α) (I : ι →₀ ℕ) :
    (contactEquiv R ι α).symm (du R ι α a I) =
      RelJetAlgebra.Bicomplex.theta (MvPolynomial ι R) ι α a I +
        ∑ μ : ι, (X (a, I + Finsupp.single μ 1) : RelJetAlgebra (MvPolynomial ι R) ι α) •
          RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ := by
  apply (contactEquiv R ι α).injective
  rw [AlgEquiv.apply_symm_apply, map_add, contactEquiv_theta, map_sum, contactForm]
  have hsum :
      ∑ μ : ι, contactEquiv R ι α
        ((X (a, I + Finsupp.single μ 1) : RelJetAlgebra (MvPolynomial ι R) ι α) •
          RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ) =
      ∑ μ : ι, (X (Sum.inr (a, I + Finsupp.single μ 1)) : PolynomialJet R ι α) •
        baseDx R ι α μ := by
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [contactEquiv_smul, RelJetAlgebra.polyJetEquivRel_symm_X, contactEquiv_dx]
  rw [hsum, sub_add_cancel]

/-- `contactEquiv` commutes with the grade involution on exterior algebras. -/
theorem contactEquiv_involute (ω : RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α) :
    contactEquiv R ι α
        (CliffordAlgebra.involute
          (Q := (0 : QuadraticForm (RelJetAlgebra (MvPolynomial ι R) ι α) _)) ω) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm (PolynomialJet R ι α) _))
        (contactEquiv R ι α ω) := by
  simp only [contactEquiv, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    exteriorMapEquiv_involute, exteriorFinsuppChangeRing_involute]

private theorem d_contactEquiv_add_step
    {x y : RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α}
    (hx : d R ι α (contactEquiv R ι α x) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i) x +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α x))
    (hy : d R ι α (contactEquiv R ι α y) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i) y +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α y)) :
    d R ι α (contactEquiv R ι α (x + y)) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i) (x + y) +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α (x + y)) := by
  simp only [map_add, hx, hy]
  abel

private theorem d_contactEquiv_mul_step
    {x y : RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α}
    (hx : d R ι α (contactEquiv R ι α x) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i) x +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α x))
    (hy : d R ι α (contactEquiv R ι α y) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i) y +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α y)) :
    d R ι α (contactEquiv R ι α (x * y)) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i) (x * y) +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α (x * y)) := by
  rw [map_mul, MvPolynomialDeRham.d_mul, hx, hy, ← contactEquiv_involute,
    ← map_mul (contactEquiv R ι α), ← map_mul (contactEquiv R ι α),
    ← map_add (contactEquiv R ι α), RelJetAlgebra.Bicomplex.dH_mul,
    RelJetAlgebra.Bicomplex.dV_mul]
  congr 1
  rw [add_mul, mul_add]
  abel

private theorem d_contactEquiv_algebraMap (p : RelJetAlgebra (MvPolynomial ι R) ι α) :
    d R ι α (contactEquiv R ι α
        (algebraMap (RelJetAlgebra (MvPolynomial ι R) ι α)
          (RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α) p)) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i)
            (algebraMap (RelJetAlgebra (MvPolynomial ι R) ι α)
              (RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α) p) +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α
            (algebraMap (RelJetAlgebra (MvPolynomial ι R) ι α)
              (RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α) p)) := by
  obtain ⟨q, rfl⟩ := (RelJetAlgebra.polyJetEquivRel R ι α).surjective p
  induction q using MvPolynomial.induction_on with
  | C r =>
    rw [contactEquiv_algebraMap_polyJetEquivRel, MvPolynomialDeRham.d_algebraMap,
      MvPolynomial.derivation_C, map_zero, RelJetAlgebra.polyJetEquivRel_C,
      RelJetAlgebra.Bicomplex.dH_algebraMap, RelJetAlgebra.Bicomplex.dV_algebraMap,
      MvPolynomial.derivation_C, map_zero, map_zero, add_zero]
    have h0 :
        ∑ μ : ι,
          RelJetAlgebra.totalDeriv (fun i ↦ MvPolynomial.pderiv i) μ
              (C (C r : MvPolynomial ι R) : RelJetAlgebra (MvPolynomial ι R) ι α) •
            RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ = 0 := by
      refine Finset.sum_eq_zero fun μ _ ↦ ?_
      rw [RelJetAlgebra.totalDeriv_C, MvPolynomial.pderiv_C, map_zero, zero_smul]
    rw [h0, map_zero]
  | add q₁ q₂ h₁ h₂ =>
    simp only [map_add, h₁, h₂]
    abel
  | mul_X q v hq =>
    rw [map_mul, map_mul]
    refine d_contactEquiv_mul_step hq ?_
    rcases v with μ | ⟨a, I⟩
    · rw [contactEquiv_algebraMap_polyJetEquivRel, d_algebraMap_X_base,
        RelJetAlgebra.polyJetEquivRel_X_base, RelJetAlgebra.Bicomplex.dH_algebraMap,
        RelJetAlgebra.Bicomplex.dV_algebraMap, MvPolynomial.derivation_C, map_zero, map_zero,
        add_zero, map_sum, Finset.sum_eq_single μ]
      · rw [RelJetAlgebra.totalDeriv_C, MvPolynomial.pderiv_X_self, map_one, one_smul,
          contactEquiv_dx]
      · intro ν _ hν
        rw [RelJetAlgebra.totalDeriv_C, MvPolynomial.pderiv_X_of_ne (Ne.symm hν), map_zero,
          zero_smul, map_zero]
      · intro hμ
        exact (hμ (Finset.mem_univ μ)).elim
    · rw [contactEquiv_algebraMap_polyJetEquivRel, d_algebraMap_X_field,
        RelJetAlgebra.polyJetEquivRel_X_field, RelJetAlgebra.Bicomplex.dH_algebraMap,
        RelJetAlgebra.Bicomplex.dV_algebraMap_X, map_add, contactEquiv_theta, map_sum,
        contactForm]
      have hsum :
          ∑ μ : ι, contactEquiv R ι α
            (RelJetAlgebra.totalDeriv (fun i ↦ MvPolynomial.pderiv i) μ
                (X (a, I) : RelJetAlgebra (MvPolynomial ι R) ι α) •
              RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ) =
          ∑ μ : ι, (X (Sum.inr (a, I + Finsupp.single μ 1)) : PolynomialJet R ι α) •
            baseDx R ι α μ := by
        refine Finset.sum_congr rfl fun μ _ ↦ ?_
        rw [RelJetAlgebra.totalDeriv_X, contactEquiv_smul,
          RelJetAlgebra.polyJetEquivRel_symm_X, contactEquiv_dx]
      rw [hsum, add_sub_cancel]

private theorem d_contactEquiv_dx (μ : ι) :
    d R ι α (contactEquiv R ι α (RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ)) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i)
            (RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ) +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α
            (RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ)) := by
  rw [contactEquiv_dx, d_baseDx, RelJetAlgebra.Bicomplex.dH_dx, RelJetAlgebra.Bicomplex.dV_dx,
    add_zero, map_zero]

private theorem d_contactEquiv_theta (a : α) (I : ι →₀ ℕ) :
    d R ι α (contactEquiv R ι α (RelJetAlgebra.Bicomplex.theta (MvPolynomial ι R) ι α a I)) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i)
            (RelJetAlgebra.Bicomplex.theta (MvPolynomial ι R) ι α a I) +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α
            (RelJetAlgebra.Bicomplex.theta (MvPolynomial ι R) ι α a I)) := by
  rw [contactEquiv_theta, d_contactForm, RelJetAlgebra.Bicomplex.dH_theta,
    RelJetAlgebra.Bicomplex.dV_theta, add_zero, map_sum]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [map_mul, contactEquiv_dx, contactEquiv_theta]

private theorem d_contactEquiv_ι_fst (v : ι →₀ RelJetAlgebra (MvPolynomial ι R) ι α) :
    d R ι α (contactEquiv R ι α (ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α)
        (v, (0 : Ω[RelJetAlgebra (MvPolynomial ι R) ι α⁄MvPolynomial ι R])))) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i)
            (ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (v, 0)) +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α
            (ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (v, 0))) := by
  induction v using Finsupp.induction_linear with
  | zero =>
    rw [show ((0 : ι →₀ RelJetAlgebra (MvPolynomial ι R) ι α),
        (0 : Ω[RelJetAlgebra (MvPolynomial ι R) ι α⁄MvPolynomial ι R])) = 0 from rfl,
      map_zero, map_zero, map_zero, map_zero, map_zero, add_zero, map_zero]
  | add v₁ v₂ hv₁ hv₂ =>
    have hadd :
        ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α)
            (v₁ + v₂, (0 : Ω[RelJetAlgebra (MvPolynomial ι R) ι α⁄MvPolynomial ι R])) =
          ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (v₁, 0) +
            ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (v₂, 0) := by
      rw [← map_add]
      congr 1
    rw [hadd]
    exact d_contactEquiv_add_step hv₁ hv₂
  | single μ p =>
    have hsingle :
        ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α)
            (Finsupp.single μ p,
              (0 : Ω[RelJetAlgebra (MvPolynomial ι R) ι α⁄MvPolynomial ι R])) =
          algebraMap (RelJetAlgebra (MvPolynomial ι R) ι α)
            (RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α) p *
            RelJetAlgebra.Bicomplex.dx (MvPolynomial ι R) ι α μ := by
      rw [← Algebra.smul_def, RelJetAlgebra.Bicomplex.dx_eq_ι,
        ← map_smul (ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α))]
      congr 1
      rw [Prod.smul_mk, Finsupp.smul_single, smul_eq_mul, mul_one]
      congr 1
    rw [hsingle]
    exact d_contactEquiv_mul_step (d_contactEquiv_algebraMap p) (d_contactEquiv_dx μ)

private theorem d_contactEquiv_ι_snd
    (η : Ω[RelJetAlgebra (MvPolynomial ι R) ι α⁄MvPolynomial ι R]) :
    d R ι α (contactEquiv R ι α (ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α)
        ((0 : ι →₀ RelJetAlgebra (MvPolynomial ι R) ι α), η))) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i)
            (ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (0, η)) +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α
            (ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (0, η))) := by
  let b := KaehlerDifferential.mvPolynomialBasis (MvPolynomial ι R) (α × (ι →₀ ℕ))
  obtain ⟨w, rfl⟩ := b.repr.symm.surjective η
  induction w using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, show ((0 : ι →₀ RelJetAlgebra (MvPolynomial ι R) ι α),
        (0 : Ω[RelJetAlgebra (MvPolynomial ι R) ι α⁄MvPolynomial ι R])) = 0 from rfl,
      map_zero, map_zero, map_zero, map_zero, map_zero, add_zero, map_zero]
  | add w₁ w₂ hw₁ hw₂ =>
    have hadd :
        ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α)
            ((0 : ι →₀ RelJetAlgebra (MvPolynomial ι R) ι α), b.repr.symm (w₁ + w₂)) =
          ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (0, b.repr.symm w₁) +
            ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (0, b.repr.symm w₂) := by
      rw [← map_add]
      congr 1
      exact Prod.ext (add_zero _).symm (map_add _ _ _)
    rw [hadd]
    exact d_contactEquiv_add_step hw₁ hw₂
  | single aI p =>
    rcases aI with ⟨a, I⟩
    have hsingle :
        ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α)
            ((0 : ι →₀ RelJetAlgebra (MvPolynomial ι R) ι α),
              b.repr.symm (Finsupp.single (a, I) p)) =
          algebraMap (RelJetAlgebra (MvPolynomial ι R) ι α)
            (RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α) p *
            RelJetAlgebra.Bicomplex.theta (MvPolynomial ι R) ι α a I := by
      rw [← Algebra.smul_def, RelJetAlgebra.Bicomplex.theta_eq_ι,
        ← map_smul (ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α))]
      congr 1
      refine Prod.ext (smul_zero p).symm ?_
      dsimp only [Prod.smul_snd]
      rw [b.repr_symm_single, KaehlerDifferential.mvPolynomialBasis_apply]
    rw [hsingle]
    exact d_contactEquiv_mul_step (d_contactEquiv_algebraMap p) (d_contactEquiv_theta a I)

/-- **The splitting `d = d_H + d_V`**: under the contact isomorphism `contactEquiv`, the total
exterior derivative on `JetForms R ι α` splits as the sum of the horizontal and vertical
differentials of the polynomial variational bicomplex, over any commutative ring `R`. -/
theorem d_contactEquiv (ω : RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α) :
    d R ι α (contactEquiv R ι α ω) =
      contactEquiv R ι α
        (RelJetAlgebra.Bicomplex.dH (fun i ↦ MvPolynomial.pderiv i) ω +
          RelJetAlgebra.Bicomplex.dV (MvPolynomial ι R) ι α ω) := by
  induction ω using CliffordAlgebra.induction with
  | algebraMap p => exact d_contactEquiv_algebraMap p
  | ι m =>
    rcases m with ⟨v, η⟩
    have hsplit :
        ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (v, η) =
          ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (v, 0) +
            ExteriorAlgebra.ι (RelJetAlgebra (MvPolynomial ι R) ι α) (0, η) := by
      rw [← map_add]
      congr 1
      exact Prod.ext (add_zero v).symm (zero_add η).symm
    rw [hsplit]
    exact d_contactEquiv_add_step (d_contactEquiv_ι_fst v) (d_contactEquiv_ι_snd η)
  | mul x y hx hy => exact d_contactEquiv_mul_step hx hy
  | add x y hx hy => exact d_contactEquiv_add_step hx hy

/-- **Cofinality (forward)**: `contactEquiv` maps the finite bicomplex stage `stageForm r` into
the shifted coordinate jet-form stage `jetFormStage (r + 1)`. -/
theorem contactEquiv_mem_jetFormStage {r : ℕ}
    {ω : RelJetAlgebra.Bicomplex (MvPolynomial ι R) ι α}
    (hω : ω ∈ RelJetAlgebra.Bicomplex.stageForm (MvPolynomial ι R) ι α r) :
    contactEquiv R ι α ω ∈ jetFormStage R ι α (r + 1) := by
  rw [RelJetAlgebra.Bicomplex.stageForm_eq_adjoin] at hω
  induction hω using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨η, hη, rfl⟩ | ⟨μ, rfl⟩
    · rw [RelJetAlgebra.vertStage_eq_supportedForms,
        MvPolynomialDeRham.supportedForms_eq_adjoin] at hη
      induction hη using Algebra.adjoin_induction with
      | mem y hy =>
        rcases hy with ⟨p, hp, rfl⟩ | ⟨⟨a, I⟩, hI, rfl⟩
        · rw [RelJetAlgebra.Bicomplex.includeVert_algebraMap, contactEquiv_algebraMap]
          refine algebraMap_mem_jetFormStage (stage_mono (Nat.le_succ r) ?_)
          rw [RelJetAlgebra.polyJetEquivRel_mem_stage_iff, AlgEquiv.apply_symm_apply]
          simpa [RelJetAlgebra.stage_eq_supported] using hp
        · rw [RelJetAlgebra.Bicomplex.includeVert_ι_D_X, contactEquiv_theta]
          exact contactForm_mem_jetFormStage hI
      | algebraMap b =>
        rw [IsScalarTower.algebraMap_apply (MvPolynomial ι R)
            (RelJetAlgebra (MvPolynomial ι R) ι α),
          RelJetAlgebra.Bicomplex.includeVert_algebraMap, contactEquiv_algebraMap]
        refine algebraMap_mem_jetFormStage ?_
        rw [RelJetAlgebra.polyJetEquivRel_mem_stage_iff, AlgEquiv.apply_symm_apply]
        exact (RelJetAlgebra.stage (MvPolynomial ι R) ι α (r + 1)).algebraMap_mem b
      | add y₁ y₂ _ _ hy₁ hy₂ =>
        rw [map_add, map_add]
        exact add_mem hy₁ hy₂
      | mul y₁ y₂ _ _ hy₁ hy₂ =>
        rw [map_mul, map_mul]
        exact mul_mem hy₁ hy₂
    · rw [contactEquiv_dx]
      exact baseDx_mem_jetFormStage (r + 1) μ
  | algebraMap b =>
    rw [IsScalarTower.algebraMap_apply (MvPolynomial ι R)
        (RelJetAlgebra (MvPolynomial ι R) ι α),
      contactEquiv_algebraMap]
    refine algebraMap_mem_jetFormStage ?_
    rw [RelJetAlgebra.polyJetEquivRel_mem_stage_iff, AlgEquiv.apply_symm_apply]
    exact (RelJetAlgebra.stage (MvPolynomial ι R) ι α (r + 1)).algebraMap_mem b
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

/-- **Cofinality (backward)**: `(contactEquiv R ι α).symm` maps the finite coordinate jet-form
stage `jetFormStage r` into the shifted bicomplex stage `stageForm (r + 1)`. -/
theorem contactEquiv_symm_mem_stageForm {r : ℕ} {η : JetForms R ι α}
    (hη : η ∈ jetFormStage R ι α r) :
    (contactEquiv R ι α).symm η ∈
      RelJetAlgebra.Bicomplex.stageForm (MvPolynomial ι R) ι α (r + 1) := by
  change η ∈ MvPolynomialDeRham.supportedForms R _ at hη
  rw [MvPolynomialDeRham.supportedForms_eq_adjoin] at hη
  induction hη using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨p, hp, rfl⟩ | ⟨v, hv, rfl⟩
    · rw [contactEquiv_symm_algebraMap]
      refine RelJetAlgebra.Bicomplex.algebraMap_mem_stageForm
        (RelJetAlgebra.stage_mono (Nat.le_succ r) ?_)
      rw [← RelJetAlgebra.polyJetEquivRel_mem_stage_iff, mem_stage_iff]
      intro a I haI
      exact (MvPolynomial.mem_supported.mp hp) haI
    · rcases v with μ | ⟨a, I⟩
      · change (contactEquiv R ι α).symm (baseDx R ι α μ) ∈ _
        rw [contactEquiv_symm_baseDx]
        exact RelJetAlgebra.Bicomplex.dx_mem_stageForm (r + 1) μ
      · change (contactEquiv R ι α).symm (du R ι α a I) ∈ _
        rw [contactEquiv_symm_du]
        refine add_mem
          (RelJetAlgebra.Bicomplex.theta_mem_stageForm (hv.trans (Nat.le_succ r)))
          (sum_mem fun μ _ ↦ ?_)
        rw [Algebra.smul_def]
        refine mul_mem (RelJetAlgebra.Bicomplex.algebraMap_mem_stageForm ?_)
          (RelJetAlgebra.Bicomplex.dx_mem_stageForm (r + 1) μ)
        exact RelJetAlgebra.X_mem_stage (by simpa using Nat.add_le_add_right hv 1)
  | algebraMap c =>
    rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply R (MvPolynomial ι R)]
    exact (RelJetAlgebra.Bicomplex.stageForm (MvPolynomial ι R) ι α (r + 1)).algebraMap_mem
      (algebraMap R (MvPolynomial ι R) c)
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

end ContactSplitting

end

end

end PolynomialJet

end TauCeti
