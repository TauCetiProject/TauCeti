/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import TauCeti.Geometry.Variational.PolynomialJet.Defs
public import TauCeti.Geometry.Variational.PolynomialJet.Relative.Basic
import TauCeti.RingTheory.Derivation.Basic

/-!
# Comparison between absolute and relative polynomial jet algebras

Over a base polynomial ring `B = MvPolynomial ι R`, `TauCeti.RelJetAlgebra.polyJetEquivRel`
identifies the absolute polynomial jet algebra `TauCeti.PolynomialJet R ι α` with the relative
polynomial jet algebra `TauCeti.RelJetAlgebra (MvPolynomial ι R) ι α`. This equivalence
intertwines total differentiation with `totalDeriv MvPolynomial.pderiv` and restricts to
finite-order stage isomorphisms `TauCeti.RelJetAlgebra.polyJetStageEquiv` compatible with stage
inclusions.

## Main definitions

* `TauCeti.RelJetAlgebra.polyJetEquivRel`: `R`-algebra isomorphism
  `PolynomialJet R ι α ≃ₐ[R] RelJetAlgebra (MvPolynomial ι R) ι α`.
* `TauCeti.RelJetAlgebra.polyJetStageEquiv`: finite-stage restriction
  `PolynomialJet.stage R ι α r ≃ₐ[R] (stage (MvPolynomial ι R) ι α r).restrictScalars R`.

## Main results

* `TauCeti.RelJetAlgebra.polyJetEquivRel_totalDeriv`,
  `TauCeti.RelJetAlgebra.polyJetEquivRel_pderiv_field`: compatibility with total derivatives and
  field partial derivatives.
* `TauCeti.RelJetAlgebra.map_stage_polyJetEquivRel_symm`,
  `TauCeti.RelJetAlgebra.polyJetEquivRel_mem_stage_iff`,
  `TauCeti.RelJetAlgebra.polyJetStageEquiv_inclusion`: compatibility with finite-order stages and
  their transition inclusions.
-/

public section

open MvPolynomial

namespace TauCeti.RelJetAlgebra

noncomputable section

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

/-- Restricting `(polyJetEquivRel R ι α).symm` to the base polynomial ring `MvPolynomial ι R`
yields `MvPolynomial.rename Sum.inl`. -/
theorem polyJetEquivRel_symm_comp_algebraMap :
    ((polyJetEquivRel R ι α).symm.toAlgHom).comp
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) (RelJetAlgebra (MvPolynomial ι R) ι α)) =
      MvPolynomial.rename Sum.inl := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [AlgEquiv.symm_apply_eq]

/-- The inverse comparison sends a base polynomial coefficient `C b` to `rename Sum.inl b`. -/
@[simp]
theorem polyJetEquivRel_symm_C (b : MvPolynomial ι R) :
    (polyJetEquivRel R ι α).symm (C b) = MvPolynomial.rename Sum.inl b := by
  simpa [MvPolynomial.algebraMap_eq] using
    AlgHom.congr_fun (polyJetEquivRel_symm_comp_algebraMap (R := R) (ι := ι) (α := α)) b

/-- The inverse comparison sends a field-jet coordinate `X (a, I)` to `X (Sum.inr (a, I))`. -/
@[simp]
theorem polyJetEquivRel_symm_X (a : α) (I : ι →₀ ℕ) :
    (polyJetEquivRel R ι α).symm (X (a, I)) = X (Sum.inr (a, I)) := by
  apply (polyJetEquivRel R ι α).injective
  rw [AlgEquiv.apply_symm_apply, polyJetEquivRel_X_field]

/-- `polyJetEquivRel` intertwines `PolynomialJet.totalDeriv` with relative `totalDeriv pderiv`. -/
@[simp]
theorem polyJetEquivRel_totalDeriv (i : ι) (p : PolynomialJet R ι α) :
    polyJetEquivRel R ι α (PolynomialJet.totalDeriv i p) =
      totalDeriv (fun k ↦ MvPolynomial.pderiv (R := R) k) i (polyJetEquivRel R ι α p) := by
  classical
  have h :
      (totalDeriv (α := α) (fun k ↦ MvPolynomial.pderiv (R := R) k) i).conjAlgEquiv
          (polyJetEquivRel R ι α).symm =
        PolynomialJet.totalDeriv i := by
    apply PolynomialJet.totalDeriv_unique
    · intro j
      simp only [Derivation.conjAlgEquiv_apply, AlgEquiv.symm_symm, polyJetEquivRel_X_base,
        totalDeriv_C, MvPolynomial.pderiv_X, Pi.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    · intro a I
      simp
  exact Derivation.algEquiv_apply_of_conjAlgEquiv_symm_eq h p

/-- `polyJetEquivRel` intertwines field partial derivatives with relative field partials. -/
@[simp]
theorem polyJetEquivRel_pderiv_field (a : α) (I : ι →₀ ℕ) (p : PolynomialJet R ι α) :
    polyJetEquivRel R ι α (MvPolynomial.pderiv (Sum.inr (a, I)) p) =
      MvPolynomial.pderiv (a, I) (polyJetEquivRel R ι α p) := by
  classical
  have h :
      ((MvPolynomial.pderiv (R := MvPolynomial ι R) (a, I)).restrictScalars R).conjAlgEquiv
          (polyJetEquivRel R ι α).symm =
        MvPolynomial.pderiv (R := R) (Sum.inr (a, I)) := by
    apply MvPolynomial.derivation_ext
    rintro (j | ⟨b, J⟩)
    · simp
    · simp only [Derivation.conjAlgEquiv_apply, AlgEquiv.symm_symm, polyJetEquivRel_X_field,
        Derivation.coe_restrictScalars, MvPolynomial.pderiv_X, Pi.single_apply, Sum.inr.injEq]
      split_ifs <;> simp
  exact Derivation.algEquiv_apply_of_conjAlgEquiv_symm_eq h p

/-- `polyJetEquivRel` identifies the finite stages of `PolynomialJet` and `RelJetAlgebra`. -/
@[simp]
theorem polyJetEquivRel_mem_stage_iff (r : ℕ) (p : PolynomialJet R ι α) :
    polyJetEquivRel R ι α p ∈ stage (MvPolynomial ι R) ι α r ↔
      p ∈ PolynomialJet.stage R ι α r := by
  constructor
  · -- Induct on `q ∈ stage ...` as a `(MvPolynomial ι R)`-subalgebra.
    intro hp
    have hq : ∀ q ∈ stage (MvPolynomial ι R) ι α r,
        (polyJetEquivRel R ι α).symm q ∈ PolynomialJet.stage R ι α r := by
      intro q hq
      rw [stage_eq_supported, MvPolynomial.supported_eq_adjoin_X] at hq
      induction hq using Algebra.adjoin_induction with
      | mem x hx =>
        rcases hx with ⟨⟨a, I⟩, hI, rfl⟩
        simpa using PolynomialJet.X_field_mem_stage r a I hI
      | algebraMap b =>
        rw [MvPolynomial.algebraMap_eq, polyJetEquivRel_symm_C]
        exact PolynomialJet.rename_inl_mem_stage r b
      | add _ _ _ _ h₁ h₂ =>
        rw [map_add]
        exact add_mem h₁ h₂
      | mul _ _ _ _ h₁ h₂ =>
        rw [map_mul]
        exact mul_mem h₁ h₂
    simpa using hq _ hp
  · -- Induct on `p ∈ PolynomialJet.stage R ι α r` as an `R`-subalgebra.
    intro hp
    rw [PolynomialJet.stage_eq_supported, MvPolynomial.supported_eq_adjoin_X] at hp
    induction hp using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨j | ⟨a, I⟩, hmem, rfl⟩
      · rw [polyJetEquivRel_X_base, ← MvPolynomial.algebraMap_eq]
        exact Subalgebra.algebraMap_mem _ _
      · simpa using X_mem_stage hmem
    | algebraMap c =>
      rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply R (MvPolynomial ι R)]
      exact Subalgebra.algebraMap_mem _ _
    | add _ _ _ _ h₁ h₂ =>
      rw [map_add]
      exact add_mem h₁ h₂
    | mul _ _ _ _ h₁ h₂ =>
      rw [map_mul]
      exact mul_mem h₁ h₂

/-- Mapping a relative finite stage along `(polyJetEquivRel R ι α).symm` yields the corresponding
`PolynomialJet` stage. -/
theorem map_stage_polyJetEquivRel_symm (r : ℕ) :
    ((stage (MvPolynomial ι R) ι α r).restrictScalars R).map
        (polyJetEquivRel R ι α).symm.toAlgHom =
      PolynomialJet.stage R ι α r := by
  ext p
  simp [Subalgebra.mem_map, (polyJetEquivRel R ι α).symm_apply_eq]

/-- Restricting `polyJetEquivRel` to finite stages gives an `R`-algebra isomorphism between
`PolynomialJet.stage R ι α r` and `(stage (MvPolynomial ι R) ι α r).restrictScalars R`. -/
def polyJetStageEquiv (R ι α : Type*) [CommSemiring R] (r : ℕ) :
    PolynomialJet.stage R ι α r ≃ₐ[R] (stage (MvPolynomial ι R) ι α r).restrictScalars R :=
  ((AlgEquiv.subalgebraMap (polyJetEquivRel R ι α).symm
      ((stage (MvPolynomial ι R) ι α r).restrictScalars R)).trans
    (Subalgebra.equivOfEq _ _ (map_stage_polyJetEquivRel_symm r))).symm

@[simp]
theorem coe_polyJetStageEquiv_symm (r : ℕ)
    (q : (stage (MvPolynomial ι R) ι α r).restrictScalars R) :
    ((polyJetStageEquiv R ι α r).symm q : PolynomialJet R ι α) =
      (polyJetEquivRel R ι α).symm q := by
  simp [polyJetStageEquiv]

@[simp]
theorem coe_polyJetStageEquiv (r : ℕ) (p : PolynomialJet.stage R ι α r) :
    (polyJetStageEquiv R ι α r p : RelJetAlgebra (MvPolynomial ι R) ι α) =
      polyJetEquivRel R ι α p := by
  have h : (polyJetEquivRel R ι α).symm (polyJetStageEquiv R ι α r p) = p := by
    have hsub := congrArg Subtype.val
      (((polyJetEquivRel R ι α).symm.subalgebraMap
        ((stage (MvPolynomial ι R) ι α r).restrictScalars R)).apply_symm_apply
        ((Subalgebra.equivOfEq _ _ (map_stage_polyJetEquivRel_symm r)).symm p))
    simpa [polyJetStageEquiv, -AlgEquiv.apply_symm_apply] using hsub
  exact (polyJetEquivRel R ι α).symm_apply_eq.mp h

/-- Increasing the jet-order bound enlarges the scalar-restricted relative stage subalgebra. -/
theorem restrictScalars_stage_mono {r s : ℕ} (hrs : r ≤ s) :
    (stage (MvPolynomial ι R) ι α r).restrictScalars R ≤
      (stage (MvPolynomial ι R) ι α s).restrictScalars R :=
  fun _ h ↦ (Subalgebra.mem_restrictScalars R).mpr
    (stage_mono hrs ((Subalgebra.mem_restrictScalars R).mp h))

/-- `polyJetStageEquiv` intertwines the stage transition inclusions. -/
theorem polyJetStageEquiv_inclusion {r s : ℕ} (hrs : r ≤ s) (p : PolynomialJet.stage R ι α r) :
    polyJetStageEquiv R ι α s (Subalgebra.inclusion (PolynomialJet.stage_mono hrs) p) =
      Subalgebra.inclusion (R := R) (restrictScalars_stage_mono hrs)
        (polyJetStageEquiv R ι α r p) := by
  apply Subtype.ext
  simp

end PolynomialBase

end

end TauCeti.RelJetAlgebra
