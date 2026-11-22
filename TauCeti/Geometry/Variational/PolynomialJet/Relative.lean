/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.Geometry.Variational.PolynomialJet.Defs
import Mathlib.RingTheory.Adjoin.Basic
import TauCeti.Algebra.MvPolynomial.Derivation.Basic
import TauCeti.Algebra.MvPolynomial.Derivation.Coeff
import TauCeti.RingTheory.Derivation.Basic

/-!
# Relative polynomial jet algebras, total derivatives, and finite stages

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

The subalgebra `TauCeti.RelJetAlgebra.stage B ι α r` consists of relative jet polynomials in
variables `uᵃ_I` of order `I.degree ≤ r`. Every polynomial belongs to a finite stage, and
`totalDeriv δ i` restricts to an `R`-linear map `stageDeriv δ i r` from `stage B ι α r` to
`stage B ι α (r + 1)` obeying the raised-stage Leibniz and commutation laws. When
`B = MvPolynomial ι R`, `polyJetEquivRel` identifies `PolynomialJet R ι α` with
`RelJetAlgebra (MvPolynomial ι R) ι α`, intertwining total derivatives and finite stages.

## Main definitions

* `TauCeti.RelJetAlgebra`: `MvPolynomial (α × (ι →₀ ℕ)) B`.
* `TauCeti.RelJetAlgebra.totalDeriv`, `TauCeti.RelJetAlgebra.stageDeriv`:
  total differentiation along `δ i` and its linear restriction between consecutive finite stages.
* `TauCeti.RelJetAlgebra.stage`: finite-order subalgebra of jet order at most `r`.
* `TauCeti.RelJetAlgebra.polyJetEquivRel`, `TauCeti.RelJetAlgebra.polyJetStageEquiv`:
  `R`-algebra isomorphisms `PolynomialJet R ι α ≃ₐ[R] RelJetAlgebra (MvPolynomial ι R) ι α` and
  their restrictions to finite stages.

## Main results

* `TauCeti.RelJetAlgebra.pderiv_totalDeriv`: commutator of vertical partial differentiation and
  total differentiation.
* `TauCeti.RelJetAlgebra.stageDeriv_mul`, `TauCeti.RelJetAlgebra.stageDeriv_comm`:
  finite-stage Leibniz and commutation rules for `stageDeriv`.
* `TauCeti.RelJetAlgebra.polyJetEquivRel_totalDeriv` and
  `TauCeti.RelJetAlgebra.polyJetEquivRel_mem_stage_iff`: compatibility with `PolynomialJet`.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, for relative jet algebras and
  total-derivative commutators.
-/

public section

open MvPolynomial

namespace TauCeti

/-- Polynomial expressions in symmetric field-jet coordinates `α × (ι →₀ ℕ)` with coefficients in
an arbitrary base commutative semiring `B`. -/
abbrev RelJetAlgebra (B ι α : Type*) [CommSemiring B] :=
  MvPolynomial (α × (ι →₀ ℕ)) B

namespace RelJetAlgebra

noncomputable section

section TotalDeriv

variable {R B ι α : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]

/-- **Total differentiation** on the relative polynomial jet algebra `RelJetAlgebra B ι α` along
a family of base derivations `δ : ι → Derivation R B B`: it applies `δ i` to coefficients in `B`
and shifts each field-jet coordinate `uᵃ_I` to `uᵃ_(I + eᵢ)`. -/
def totalDeriv (δ : ι → Derivation R B B) (i : ι) :
    Derivation R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α) :=
  (δ i).coeffDeriv +
    (MvPolynomial.mkDerivation B fun aI : α × (ι →₀ ℕ) ↦
      (X (aI.1, aI.2 + Finsupp.single i 1) : RelJetAlgebra B ι α)).restrictScalars R

/-- Total differentiation acts on base coefficients `C b` by `δ i`. -/
@[simp]
theorem totalDeriv_C (δ : ι → Derivation R B B) (i : ι) (b : B) :
    totalDeriv (α := α) δ i (C b) = C (δ i b) := by
  simp [totalDeriv]

/-- Total differentiation shifts field-jet variables `uᵃ_I ↦ uᵃ_(I + eᵢ)`. -/
@[simp]
theorem totalDeriv_X (δ : ι → Derivation R B B) (i : ι) (a : α) (I : ι →₀ ℕ) :
    totalDeriv δ i (X (a, I)) = X (a, I + Finsupp.single i 1) := by
  simp [totalDeriv]

/-- Total differentiation is uniquely determined among `R`-derivations by its action on base
coefficients and field-jet coordinates. -/
theorem totalDeriv_unique (δ : ι → Derivation R B B) (i : ι)
    (D : Derivation R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α))
    (hC : ∀ b, D (C b) = C (δ i b))
    (hX : ∀ a I, D (X (a, I)) = X (a, I + Finsupp.single i 1)) :
    D = totalDeriv δ i :=
  TauCeti.MvPolynomial.derivation_ext' (fun b ↦ by simp [hC]) (fun ⟨a, I⟩ ↦ by simp [hX])

/-- Commuting base derivations induce commuting total derivatives on `RelJetAlgebra B ι α`. -/
theorem totalDeriv_comm {δ : ι → Derivation R B B} {i j : ι}
    (hδ : ∀ b, δ i (δ j b) = δ j (δ i b)) (p : RelJetAlgebra B ι α) :
    totalDeriv δ i (totalDeriv δ j p) = totalDeriv δ j (totalDeriv δ i p) := by
  simpa using (totalDeriv δ i).apply_apply_eq_add_of_C_of_X (totalDeriv δ j) 0
    (fun b ↦ by simp [hδ]) (fun ⟨a, I⟩ ↦ by simp [add_right_comm I]) p

open Classical in
private theorem pderiv_X_add_single (i : ι) (a b : α) (I J : ι →₀ ℕ) :
    MvPolynomial.pderiv (a, I) (X (b, J + Finsupp.single i 1) : RelJetAlgebra B ι α) =
      if 1 ≤ I i then
        MvPolynomial.pderiv (a, I - Finsupp.single i 1) (X (b, J) : RelJetAlgebra B ι α)
      else 0 := by
  have hshift :
      ((b, J + Finsupp.single i 1) = (a, I)) ↔
        (1 ≤ I i ∧ (b, J) = (a, I - Finsupp.single i 1)) := by
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨by simp, rfl, (add_tsub_cancel_right J (Finsupp.single i 1)).symm⟩
    · rintro ⟨hI, rfl, rfl⟩
      exact ⟨rfl, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hI)⟩
  simp only [MvPolynomial.pderiv_X, Pi.single_apply]
  by_cases hI : 1 ≤ I i
  · simp only [hI, ite_true]
    by_cases hEq : (b, J + Finsupp.single i 1) = (a, I)
    · simp [hEq, (hshift.mp hEq).2]
    · have hNe' : (b, J) ≠ (a, I - Finsupp.single i 1) := fun h ↦ hEq (hshift.mpr ⟨hI, h⟩)
      simp [hEq, hNe']
  · simp only [hI, ite_false]
    have hNe : (b, J + Finsupp.single i 1) ≠ (a, I) := fun h ↦ hI (hshift.mp h).1
    simp [hNe]

open Classical in
/-- **Variational commutator identity**: vertical partial differentiation `∂/∂uᵃ_I` and total
differentiation `Dᵢ` satisfy `[∂/∂uᵃ_I, Dᵢ] = ∂/∂uᵃ_(I - eᵢ)` (or `0` when `I i = 0`). -/
theorem pderiv_totalDeriv (δ : ι → Derivation R B B) (i : ι) (a : α) (I : ι →₀ ℕ)
    (p : RelJetAlgebra B ι α) :
    MvPolynomial.pderiv (a, I) (totalDeriv δ i p) =
      totalDeriv δ i (MvPolynomial.pderiv (a, I) p) +
        if 1 ≤ I i then MvPolynomial.pderiv (a, I - Finsupp.single i 1) p else 0 := by
  have hX (E : Derivation R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α))
      (hE : ∀ b J, E (X (b, J)) =
        if 1 ≤ I i then MvPolynomial.pderiv (a, I - Finsupp.single i 1) (X (b, J)) else 0)
      (v : α × (ι →₀ ℕ)) :
      MvPolynomial.pderiv (a, I) (totalDeriv δ i (X v)) =
        totalDeriv δ i (MvPolynomial.pderiv (a, I) (X v)) + E (X v) := by
    rcases v with ⟨b, J⟩
    have h0 : totalDeriv δ i (MvPolynomial.pderiv (a, I) (X (b, J) : RelJetAlgebra B ι α)) =
        0 := by
      simp only [MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    simp only [totalDeriv_X, h0, zero_add, hE]
    exact pderiv_X_add_single i a b I J
  by_cases hI : 1 ≤ I i
  · simpa [hI] using ((MvPolynomial.pderiv (a, I)).restrictScalars R).apply_apply_eq_add_of_C_of_X
      (totalDeriv δ i) ((MvPolynomial.pderiv (a, I - Finsupp.single i 1)).restrictScalars R)
      (fun b ↦ by simp) (hX _ fun b J ↦ by simp [hI]) p
  · simpa [hI] using ((MvPolynomial.pderiv (a, I)).restrictScalars R).apply_apply_eq_add_of_C_of_X
      (totalDeriv δ i) 0
      (fun b ↦ by simp) (hX _ fun b J ↦ by simp [hI]) p

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
@[simp]
theorem X_mem_stage_iff [Nontrivial B] {r : ℕ} {a : α} {I : ι →₀ ℕ} :
    (X (a, I) : RelJetAlgebra B ι α) ∈ stage B ι α r ↔ I.degree ≤ r := by
  simp [stage]

/-- Every relative jet polynomial belongs to some finite stage. -/
theorem exists_mem_stage (p : RelJetAlgebra B ι α) : ∃ r, p ∈ stage B ι α r :=
  ⟨p.vars.sup (fun v ↦ v.2.degree),
    MvPolynomial.supported_mono
      (fun _ hv ↦ Finset.le_sup (f := fun v : α × (ι →₀ ℕ) ↦ v.2.degree) hv)
      p.mem_supported_vars⟩

/-- Total differentiation raises the jet-order stage by at most one. -/
theorem totalDeriv_mem_stage {R : Type*} [CommSemiring R] [Algebra R B]
    (δ : ι → Derivation R B B) (i : ι) {r : ℕ} {p : RelJetAlgebra B ι α}
    (hp : p ∈ stage B ι α r) : totalDeriv δ i p ∈ stage B ι α (r + 1) := by
  refine (totalDeriv δ i).map_mem_supported
    (s := {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r})
    (t := {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r + 1})
    (fun _ h ↦ h.trans (Nat.le_succ r))
    (fun b ↦ by
      rw [totalDeriv_C, ← MvPolynomial.algebraMap_eq]
      exact Subalgebra.algebraMap_mem _ _)
    (fun ⟨a, I⟩ hI ↦ by
      rw [totalDeriv_X]
      exact X_mem_stage (by simpa using Nat.add_le_add_right hI 1))
    hp

/-- Total differentiation as an `R`-linear map between consecutive finite stages. -/
def stageDeriv {R : Type*} [CommSemiring R] [Algebra R B] (δ : ι → Derivation R B B)
    (i : ι) (r : ℕ) : stage B ι α r →ₗ[R] stage B ι α (r + 1) :=
  (totalDeriv δ i).toLinearMap.restrict
    (p := (stage B ι α r).toSubmodule.restrictScalars R)
    (q := (stage B ι α (r + 1)).toSubmodule.restrictScalars R)
    fun _ hp ↦ totalDeriv_mem_stage δ i hp

@[simp]
theorem coe_stageDeriv {R : Type*} [CommSemiring R] [Algebra R B] (δ : ι → Derivation R B B)
    (i : ι) (r : ℕ) (p : stage B ι α r) :
    (stageDeriv δ i r p : RelJetAlgebra B ι α) = totalDeriv δ i p := by
  rfl

/-- Finite-stage total differentiation commutes with stage inclusions. -/
@[simp]
theorem stageDeriv_inclusion {R : Type*} [CommSemiring R] [Algebra R B]
    (δ : ι → Derivation R B B) (i : ι) {r s : ℕ} (hrs : r ≤ s) (p : stage B ι α r) :
    stageDeriv δ i s (Subalgebra.inclusion (stage_mono hrs) p) =
      Subalgebra.inclusion (stage_mono (Nat.add_le_add_right hrs 1)) (stageDeriv δ i r p) := by
  apply Subtype.ext
  simp

/-- The finite-stage Leibniz rule for `RelJetAlgebra.stageDeriv` uses the inclusion into the
raised stage. -/
theorem stageDeriv_mul {R : Type*} [CommSemiring R] [Algebra R B]
    (δ : ι → Derivation R B B) (i : ι) (r : ℕ) (p q : stage B ι α r) :
    stageDeriv δ i r (p * q) =
      Subalgebra.inclusion (stage_mono (Nat.le_succ r)) p * stageDeriv δ i r q +
        Subalgebra.inclusion (stage_mono (Nat.le_succ r)) q * stageDeriv δ i r p := by
  apply Subtype.ext
  simp [Derivation.leibniz]

/-- Commuting base derivations yield commuting `stageDeriv` maps from stage `r` to stage
`r + 2`. -/
theorem stageDeriv_comm {R : Type*} [CommSemiring R] [Algebra R B]
    {δ : ι → Derivation R B B} {i j : ι} (hδ : ∀ b, δ i (δ j b) = δ j (δ i b)) (r : ℕ)
    (p : stage B ι α r) :
    stageDeriv δ i (r + 1) (stageDeriv δ j r p) =
      stageDeriv δ j (r + 1) (stageDeriv δ i r p) := by
  apply Subtype.ext
  simp [totalDeriv_comm hδ]

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
theorem polyJetEquivRel_symm_map_stage (r : ℕ) :
    ((stage (MvPolynomial ι R) ι α r).restrictScalars R).map
        (polyJetEquivRel R ι α).symm.toAlgHom =
      PolynomialJet.stage R ι α r := by
  rw [stage_eq_supported, MvPolynomial.supported, Algebra.Subalgebra.restrictScalars_adjoin,
    Algebra.map_sup, AlgHom.map_adjoin, PolynomialJet.stage_eq_supported, MvPolynomial.supported]
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
      (polyJetEquivRel R ι α).symm.toAlgHom ''
          (X '' {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r}) =
        X '' (Sum.inr '' {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r}) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun ⟨a, I⟩ _ ↦ polyJetEquivRel_symm_X a I
  rw [hcoeff, hfield, ← Algebra.adjoin_union, ← Set.image_union]
  congr 2
  ext (j | ⟨a, I⟩) <;> simp

/-- `polyJetEquivRel` identifies the finite stages of `PolynomialJet` and `RelJetAlgebra`. -/
theorem polyJetEquivRel_mem_stage_iff (r : ℕ) (p : PolynomialJet R ι α) :
    polyJetEquivRel R ι α p ∈ stage (MvPolynomial ι R) ι α r ↔
      p ∈ PolynomialJet.stage R ι α r := by
  rw [← polyJetEquivRel_symm_map_stage (R := R) (ι := ι) (α := α) r, Subalgebra.mem_map]
  constructor
  · rintro hp
    exact ⟨polyJetEquivRel R ι α p, hp, by simp⟩
  · rintro ⟨q, hq, hqp⟩
    have hq' : polyJetEquivRel R ι α p = q := by
      rw [← hqp, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    rwa [hq']

/-- Restricting `polyJetEquivRel` to finite stages gives an `R`-algebra isomorphism between
`PolynomialJet.stage R ι α r` and `(stage (MvPolynomial ι R) ι α r).restrictScalars R`. -/
def polyJetStageEquiv (R ι α : Type*) [CommSemiring R] (r : ℕ) :
    PolynomialJet.stage R ι α r ≃ₐ[R] (stage (MvPolynomial ι R) ι α r).restrictScalars R :=
  ((AlgEquiv.subalgebraMap (polyJetEquivRel R ι α).symm
      ((stage (MvPolynomial ι R) ι α r).restrictScalars R)).trans
    (Subalgebra.equivOfEq _ _ (polyJetEquivRel_symm_map_stage r))).symm

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

/-- `polyJetStageEquiv` intertwines the stage transition inclusions. -/
theorem polyJetStageEquiv_inclusion {r s : ℕ} (hrs : r ≤ s) (p : PolynomialJet.stage R ι α r) :
    polyJetStageEquiv R ι α s (Subalgebra.inclusion (PolynomialJet.stage_mono hrs) p) =
      Subalgebra.inclusion (R := R)
          (show (stage (MvPolynomial ι R) ι α r).restrictScalars R ≤
              (stage (MvPolynomial ι R) ι α s).restrictScalars R from stage_mono hrs)
          (polyJetStageEquiv R ι α r p) := by
  apply Subtype.ext
  simp

end PolynomialBase

end

end RelJetAlgebra
end TauCeti
