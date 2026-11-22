/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Finsupp.Weight
import TauCeti.Algebra.MvPolynomial.Derivation.Basic
import TauCeti.Algebra.MvPolynomial.Derivation.Coeff
import TauCeti.Algebra.MvPolynomial.Supported
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
`stage B ι α (r + 1)` obeying the unconditional raised-stage Leibniz rule and compatibility with
stage inclusions; whenever the corresponding base derivations `δ i` and `δ j` commute,
`stageDeriv δ i` and `stageDeriv δ j` also commute from stage `r` to stage `r + 2`.

## Main definitions

* `TauCeti.RelJetAlgebra`: `MvPolynomial (α × (ι →₀ ℕ)) B`.
* `TauCeti.RelJetAlgebra.totalDeriv`, `TauCeti.RelJetAlgebra.stageDeriv`:
  total differentiation along `δ i` and its linear restriction between consecutive finite stages.
* `TauCeti.RelJetAlgebra.stage`: finite-order subalgebra of jet order at most `r`.

## Main results

* `TauCeti.RelJetAlgebra.pderiv_totalDeriv`: commutator of vertical partial differentiation and
  total differentiation.
* `TauCeti.RelJetAlgebra.stageDeriv_inclusion`, `TauCeti.RelJetAlgebra.stageDeriv_mul`:
  unconditional stage-inclusion compatibility and finite-stage Leibniz rule for `stageDeriv`.
* `TauCeti.RelJetAlgebra.stageDeriv_comm`: directional commutation of `stageDeriv` for commuting
  base derivations `δ i` and `δ j`.

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
  (δ i).mapCoeffsMvPolynomial +
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
  simpa using Derivation.apply_apply_eq_add_of_adjoin_eq_top
    (D₁ := totalDeriv δ i) (D₂ := totalDeriv δ j) (E := 0)
    (TauCeti.MvPolynomial.adjoin_range_C_union_range_X R B (α × (ι →₀ ℕ)))
    (by
      rintro _ (⟨b, rfl⟩ | ⟨⟨a, I⟩, rfl⟩)
      · simp [hδ]
      · simp [add_right_comm I]) p

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
  have hgen (E : Derivation R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α))
      (hC : ∀ b : B, E (C b) = 0)
      (hX : ∀ b J, E (X (b, J)) =
        if 1 ≤ I i then MvPolynomial.pderiv (a, I - Finsupp.single i 1) (X (b, J)) else 0)
      (x : RelJetAlgebra B ι α)
      (hx : x ∈ Set.range (C : B → RelJetAlgebra B ι α) ∪ Set.range X) :
      ((MvPolynomial.pderiv (a, I)).restrictScalars R) (totalDeriv δ i x) =
        totalDeriv δ i (((MvPolynomial.pderiv (a, I)).restrictScalars R) x) + E x := by
    rcases hx with ⟨b, rfl⟩ | ⟨⟨b, J⟩, rfl⟩
    · simp [hC]
    · have h0 : totalDeriv δ i (MvPolynomial.pderiv (a, I) (X (b, J) : RelJetAlgebra B ι α)) =
          0 := by
        simp only [MvPolynomial.pderiv_X, Pi.single_apply]
        split_ifs <;> simp
      simp only [Derivation.coe_restrictScalars, totalDeriv_X, h0, zero_add, hX]
      exact pderiv_X_add_single i a b I J
  by_cases hI : 1 ≤ I i
  · simpa [hI] using Derivation.apply_apply_eq_add_of_adjoin_eq_top
      (D₁ := (MvPolynomial.pderiv (a, I)).restrictScalars R) (D₂ := totalDeriv δ i)
      (E := (MvPolynomial.pderiv (a, I - Finsupp.single i 1)).restrictScalars R)
      (TauCeti.MvPolynomial.adjoin_range_C_union_range_X R B (α × (ι →₀ ℕ)))
      (hgen (E := (MvPolynomial.pderiv (a, I - Finsupp.single i 1)).restrictScalars R)
        (fun _ ↦ by simp) fun b J ↦ by simp [hI]) p
  · simpa [hI] using Derivation.apply_apply_eq_add_of_adjoin_eq_top
      (D₁ := (MvPolynomial.pderiv (a, I)).restrictScalars R) (D₂ := totalDeriv δ i) (E := 0)
      (TauCeti.MvPolynomial.adjoin_range_C_union_range_X R B (α × (ι →₀ ℕ)))
      (hgen (E := 0) (fun _ ↦ by simp) fun b J ↦ by simp [hI]) p

end TotalDeriv

section Stage

variable (B ι α : Type*) [CommSemiring B]

/-- The finite-order relative jet subalgebra of order at most `r`, allowing arbitrary base
coefficients in `B` and field-jet coordinates `uᵃ_I` with `I.degree ≤ r`. -/
@[expose] def stage (r : ℕ) : Subalgebra B (RelJetAlgebra B ι α) :=
  MvPolynomial.supported B {aI | aI.2.degree ≤ r}

variable {B ι α}

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

end

end RelJetAlgebra
end TauCeti
