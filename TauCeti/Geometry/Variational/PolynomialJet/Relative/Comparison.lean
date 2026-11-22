/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import TauCeti.Geometry.Variational.PolynomialJet.Defs
public import TauCeti.Geometry.Variational.PolynomialJet.Relative.Basic
import Mathlib.RingTheory.Adjoin.Basic
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

* `TauCeti.RelJetAlgebra.polyJetEquivRel_totalDeriv`: compatibility with total derivatives.
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

/-- The inverse comparison sends a base polynomial coefficient `C b` to `rename Sum.inl b`. -/
@[simp]
theorem polyJetEquivRel_symm_C (b : MvPolynomial ι R) :
    (polyJetEquivRel R ι α).symm (C b) = MvPolynomial.rename Sum.inl b := by
  apply (polyJetEquivRel R ι α).injective
  rw [AlgEquiv.apply_symm_apply, polyJetEquivRel, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
  have h := AlgHom.congr_fun
    (MvPolynomial.sumAlgEquiv_comp_rename_inr R (α × (ι →₀ ℕ)) ι) b
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
    IsScalarTower.coe_toAlgHom', MvPolynomial.algebraMap_eq] at h
  exact h.symm

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
  have hp := DFunLike.congr_fun h p
  simpa [Derivation.conjAlgEquiv_apply] using congrArg (polyJetEquivRel R ι α) hp.symm

/-- Mapping a relative finite stage along `(polyJetEquivRel R ι α).symm` yields the corresponding
`PolynomialJet` stage. -/
theorem map_stage_polyJetEquivRel_symm (r : ℕ) :
    ((stage (MvPolynomial ι R) ι α r).restrictScalars R).map
        (polyJetEquivRel R ι α).symm.toAlgHom =
      PolynomialJet.stage R ι α r := by
  have hcoeff :
      (IsScalarTower.toAlgHom R (MvPolynomial ι R)
          (RelJetAlgebra (MvPolynomial ι R) ι α)).range.map
          (polyJetEquivRel R ι α).symm.toAlgHom =
        Algebra.adjoin R (X '' Set.range (Sum.inl : ι → ι ⊕ (α × (ι →₀ ℕ)))) := by
    rw [← AlgHom.range_comp]
    have hcomp :
        ((polyJetEquivRel R ι α).symm.toAlgHom).comp
            (IsScalarTower.toAlgHom R (MvPolynomial ι R)
              (RelJetAlgebra (MvPolynomial ι R) ι α)) =
          MvPolynomial.rename Sum.inl := by
      ext j
      simp [MvPolynomial.algebraMap_eq]
    rw [hcomp, ← Algebra.map_top, ← MvPolynomial.adjoin_range_X (R := R) (σ := ι),
      AlgHom.map_adjoin, ← Set.range_comp, ← Set.range_comp]
    congr 2
    ext j
    simp
  have hfield :
      Algebra.adjoin R
          ((polyJetEquivRel R ι α).symm.toAlgHom ''
            (X '' {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r})) =
        Algebra.adjoin R (X '' (Sum.inr '' {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r})) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    exact Set.image_congr fun ⟨a, I⟩ _ ↦ polyJetEquivRel_symm_X a I
  calc
    ((stage (MvPolynomial ι R) ι α r).restrictScalars R).map
          (polyJetEquivRel R ι α).symm.toAlgHom
        = (IsScalarTower.toAlgHom R (MvPolynomial ι R)
              (RelJetAlgebra (MvPolynomial ι R) ι α)).range.map
              (polyJetEquivRel R ι α).symm.toAlgHom ⊔
            Algebra.adjoin R
              ((polyJetEquivRel R ι α).symm.toAlgHom ''
                (X '' {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r})) := by
          rw [stage, MvPolynomial.supported_eq_adjoin_X,
            Algebra.Subalgebra.restrictScalars_adjoin, Algebra.map_sup, AlgHom.map_adjoin]
    _ = Algebra.adjoin R (X '' Set.range (Sum.inl : ι → ι ⊕ (α × (ι →₀ ℕ)))) ⊔
          Algebra.adjoin R (X '' (Sum.inr '' {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r})) := by
          rw [hcoeff, hfield]
    _ = PolynomialJet.stage R ι α r := by
          rw [← Algebra.adjoin_union, ← Set.image_union, PolynomialJet.stage,
            MvPolynomial.supported_eq_adjoin_X]
          congr 2
          ext (j | ⟨a, I⟩) <;> simp

/-- `polyJetEquivRel` identifies the finite stages of `PolynomialJet` and `RelJetAlgebra`. -/
theorem polyJetEquivRel_mem_stage_iff (r : ℕ) (p : PolynomialJet R ι α) :
    polyJetEquivRel R ι α p ∈ stage (MvPolynomial ι R) ι α r ↔
      p ∈ PolynomialJet.stage R ι α r := by
  have himg :
      (polyJetEquivRel R ι α).symm ''
          (stage (MvPolynomial ι R) ι α r : Set (RelJetAlgebra (MvPolynomial ι R) ι α)) =
        polyJetEquivRel R ι α ⁻¹'
          (stage (MvPolynomial ι R) ι α r : Set (RelJetAlgebra (MvPolynomial ι R) ι α)) :=
    (polyJetEquivRel R ι α).symm.toEquiv.image_eq_preimage_symm _
  rw [← map_stage_polyJetEquivRel_symm (R := R) (ι := ι) (α := α) r]
  nth_rw 2 [← SetLike.mem_coe]
  rw [Subalgebra.coe_map, Subalgebra.coe_restrictScalars, AlgEquiv.coe_toAlgHom, himg]
  rfl

/-- Restricting `polyJetEquivRel` to finite stages gives an `R`-algebra isomorphism between
`PolynomialJet.stage R ι α r` and `(stage (MvPolynomial ι R) ι α r).restrictScalars R`. -/
def polyJetStageEquiv (R ι α : Type*) [CommSemiring R] (r : ℕ) :
    PolynomialJet.stage R ι α r ≃ₐ[R] (stage (MvPolynomial ι R) ι α r).restrictScalars R :=
  ((AlgEquiv.subalgebraMap (polyJetEquivRel R ι α).symm
      ((stage (MvPolynomial ι R) ι α r).restrictScalars R)).trans
    (Subalgebra.equivOfEq _ _ (map_stage_polyJetEquivRel_symm r))).symm

@[simp]
theorem coe_polyJetStageEquiv (r : ℕ) (p : PolynomialJet.stage R ι α r) :
    (polyJetStageEquiv R ι α r p : RelJetAlgebra (MvPolynomial ι R) ι α) =
      polyJetEquivRel R ι α p := by
  apply (polyJetEquivRel R ι α).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact congrArg Subtype.val ((polyJetStageEquiv R ι α r).symm_apply_apply p)

@[simp]
theorem coe_polyJetStageEquiv_symm (r : ℕ)
    (q : (stage (MvPolynomial ι R) ι α r).restrictScalars R) :
    ((polyJetStageEquiv R ι α r).symm q : PolynomialJet R ι α) =
      (polyJetEquivRel R ι α).symm q := by
  rfl

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
