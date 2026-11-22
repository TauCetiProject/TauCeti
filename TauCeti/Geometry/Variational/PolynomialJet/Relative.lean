/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Derivation
public import TauCeti.Geometry.Variational.PolynomialJet.Defs
public import TauCeti.RingTheory.Kaehler.DeRham.Polynomial
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.RingTheory.Derivation.Basic

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
whenever `δ i` and `δ j` commute. Over a finite base index type `[Fintype ι]`, tensoring with the
constant-coefficient horizontal exterior algebra `ExteriorAlgebra R (ι →₀ R)` yields the unsigned
double-differential complex with differentials `dAlgTensor` and `horizDerivUnsigned`, over any
commutative ring `R` (without characteristic restrictions). Here `dAlgTensor` squares to zero and
commutes with `horizDerivUnsigned` for arbitrary base derivations `δ`, while `horizDerivUnsigned`
squares to zero whenever the base derivations `δ i` and `δ j` commute.

## Main definitions

* `TauCeti.RelJetAlgebra`: `MvPolynomial (α × (ι →₀ ℕ)) B`.
* `TauCeti.RelJetAlgebra.totalDeriv`, `TauCeti.RelJetAlgebra.stageDeriv`:
  total differentiation along `∂ i` and its linear restriction between consecutive finite stages.
* `TauCeti.RelJetAlgebra.stage`: finite-order subalgebra of jet order at most `r`.
* `TauCeti.RelJetAlgebra.polyJetEquivRel`: `R`-algebra isomorphism
  `PolynomialJet R ι α ≃ₐ[R] RelJetAlgebra (MvPolynomial ι R) ι α`.
* `TauCeti.RelJetAlgebra.VertForms`, `TauCeti.RelJetAlgebra.dAlg`,
  `TauCeti.RelJetAlgebra.totalDerivForm`, `TauCeti.RelJetAlgebra.vertStage`,
  `TauCeti.RelJetAlgebra.vertStageDAlg`, `TauCeti.RelJetAlgebra.vertStageTotalDerivForm`: the
  relative vertical de Rham complex, its total-derivative Lie actions, and their finite-stage linear
  restrictions.
* `TauCeti.RelJetAlgebra.dAlgTensor` and `TauCeti.RelJetAlgebra.horizDerivUnsigned`: the vertical
  and (for `[Fintype ι]`) unsigned horizontal differentials on
  `VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)`.

## Main results

* `TauCeti.RelJetAlgebra.pderiv_totalDeriv`: commutator of vertical partial differentiation and
  total differentiation.
* `TauCeti.RelJetAlgebra.polyJetEquivRel_totalDeriv` and
  `TauCeti.RelJetAlgebra.polyJetEquivRel_mem_stage_iff`: compatibility with `PolynomialJet`.
* `TauCeti.RelJetAlgebra.dAlg_totalDerivForm`: `d_alg` commutes with `totalDerivForm ∂ i`.
* `TauCeti.RelJetAlgebra.algebraMap_mem_vertStage_iff` and
  `TauCeti.RelJetAlgebra.ι_D_X_mem_vertStage_iff`: membership characterizations for vertical
  zero-forms and coordinate one-forms in `vertStage`.
* `TauCeti.RelJetAlgebra.dAlgTensor_dAlgTensor` and
  `TauCeti.RelJetAlgebra.dAlgTensor_horizDerivUnsigned`: `dAlgTensor² = 0` and commutation of
  `dAlgTensor` with `horizDerivUnsigned` (for `[Fintype ι]` and arbitrary `δ`).
* `TauCeti.RelJetAlgebra.horizDerivUnsigned_horizDerivUnsigned`: `(D_H⁰)² = 0` when `[Fintype ι]`
  and the base derivations commute.

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

/-- **Total differentiation** on the relative polynomial jet algebra `RelJetAlgebra B ι α` along
a family of base derivations `δ : ι → Derivation R B B`: it applies `δ i` to coefficients in `B`
and shifts each field-jet coordinate `uᵃ_I` to `uᵃ_(I + eᵢ)`. -/
def totalDeriv (δ : ι → Derivation R B B) (i : ι) :
    Derivation R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α) :=
  MvPolynomial.coeffDeriv (δ i) +
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
  MvPolynomial.derivation_ext' (fun b ↦ by simp [hC]) (fun ⟨a, I⟩ ↦ by simp [hX])

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
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    split_ifs <;> simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    by_cases hI : 1 ≤ I i <;> simp [hI]
    ac_rfl
  | mul_X p v hp =>
    rcases v with ⟨b, J⟩
    have hD_pderiv_X :
        totalDeriv δ i (MvPolynomial.pderiv (a, I) (X (b, J) : RelJetAlgebra B ι α)) = 0 := by
      simp only [MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    have hite (x y : RelJetAlgebra B ι α) :
        (if 1 ≤ I i then x + y else 0) =
          (if 1 ≤ I i then x else 0) + (if 1 ≤ I i then y else 0) := by
      split_ifs <;> simp
    have hmul_ite (x y : RelJetAlgebra B ι α) :
        (if 1 ≤ I i then x * y else 0) = x * (if 1 ≤ I i then y else 0) := by
      split_ifs <;> simp
    simp only [Derivation.leibniz, smul_eq_mul, map_add, totalDeriv_X, hp, pderiv_X_add_single,
      hD_pderiv_X, hite, hmul_ite]
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
  refine MvPolynomial.derivation_mem_supported (totalDeriv δ i)
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

/-- Vertical partial differentiation preserves every finite stage. -/
theorem pderiv_mem_stage (a : α) (I : ι →₀ ℕ) {r : ℕ} {p : RelJetAlgebra B ι α}
    (hp : p ∈ stage B ι α r) : MvPolynomial.pderiv (a, I) p ∈ stage B ι α r :=
  MvPolynomial.pderiv_mem_supported (a, I) hp

/-- Total differentiation as an `R`-linear map between consecutive finite stages. -/
def stageDeriv {R : Type*} [CommSemiring R] [Algebra R B] (δ : ι → Derivation R B B)
    (i : ι) (r : ℕ) : stage B ι α r →ₗ[R] stage B ι α (r + 1) where
  toFun p := ⟨totalDeriv δ i p, totalDeriv_mem_stage δ i p.property⟩
  map_add' p q :=
    Subtype.ext (map_add (totalDeriv δ i) (p : RelJetAlgebra B ι α) (q : RelJetAlgebra B ι α))
  map_smul' c p := Subtype.ext ((totalDeriv δ i).toLinearMap.map_smul c (p : RelJetAlgebra B ι α))

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

/-- `polyJetEquivRel` identifies the finite stages of `PolynomialJet` and `RelJetAlgebra`. -/
theorem polyJetEquivRel_mem_stage_iff (r : ℕ) (p : PolynomialJet R ι α) :
    polyJetEquivRel R ι α p ∈ stage (MvPolynomial ι R) ι α r ↔
      p ∈ PolynomialJet.stage R ι α r := by
  have hmap :
      ((stage (MvPolynomial ι R) ι α r).restrictScalars R).map
          (polyJetEquivRel R ι α).symm.toAlgHom =
        PolynomialJet.stage R ι α r := by
    rw [stage, MvPolynomial.supported, Algebra.Subalgebra.restrictScalars_adjoin,
      Algebra.map_sup, AlgHom.map_adjoin, PolynomialJet.stage, MvPolynomial.supported]
    have hcoeff :
        (IsScalarTower.toAlgHom R (MvPolynomial ι R)
            (RelJetAlgebra (MvPolynomial ι R) ι α)).range.map
            (polyJetEquivRel R ι α).symm.toAlgHom =
          Algebra.adjoin R (X '' Set.range (Sum.inl : ι → ι ⊕ (α × (ι →₀ ℕ)))) := by
      rw [← Algebra.map_top, ← MvPolynomial.adjoin_range_X (R := R) (σ := ι), AlgHom.map_adjoin,
        AlgHom.map_adjoin, ← Set.image_comp]
      congr 1
      ext q
      simp only [Set.mem_image, Set.mem_range, Function.comp_apply, AlgEquiv.coe_toAlgHom,
        IsScalarTower.coe_toAlgHom', MvPolynomial.algebraMap_eq, polyJetEquivRel_symm_C]
      constructor
      · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
        exact ⟨Sum.inl j, ⟨j, rfl⟩, (MvPolynomial.rename_X Sum.inl j).symm⟩
      · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
        exact ⟨X j, ⟨j, rfl⟩, MvPolynomial.rename_X Sum.inl j⟩
    have hfield :
        (polyJetEquivRel R ι α).symm.toAlgHom ''
            (X '' {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r}) =
          X '' (Sum.inr '' {aI : α × (ι →₀ ℕ) | aI.2.degree ≤ r}) := by
      ext q
      simp only [Set.mem_image]
      constructor
      · rintro ⟨_, ⟨⟨a, I⟩, hI, rfl⟩, rfl⟩
        exact ⟨Sum.inr (a, I), ⟨(a, I), hI, rfl⟩, (polyJetEquivRel_symm_X a I).symm⟩
      · rintro ⟨_, ⟨⟨a, I⟩, hI, rfl⟩, rfl⟩
        exact ⟨X (a, I), ⟨(a, I), hI, rfl⟩, polyJetEquivRel_symm_X a I⟩
    rw [hcoeff, hfield, ← Algebra.adjoin_union, ← Set.image_union]
    congr 2
    ext v
    rcases v with j | ⟨a, I⟩ <;> simp
  rw [← hmap, Subalgebra.mem_map]
  constructor
  · intro hp
    exact ⟨polyJetEquivRel R ι α p, hp, by simp⟩
  · rintro ⟨q, hq, hqp⟩
    have hq' : polyJetEquivRel R ι α p = q := by
      rw [← hqp]
      simp
    rwa [hq']

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

/-- A vertical zero-form lies in `vertStage B ι α r` if and only if its polynomial lies in
`stage B ι α r`. -/
theorem algebraMap_mem_vertStage_iff {r : ℕ} {p : RelJetAlgebra B ι α} :
    algebraMap (RelJetAlgebra B ι α) (VertForms B ι α) p ∈ vertStage B ι α r ↔
      p ∈ stage B ι α r :=
  KaehlerDeRham.algebraMap_mem_supportedForms_iff

/-- Over a nontrivial base ring, a vertical generator one-form `duᵃ_I` lies in `vertStage B ι α r`
if and only if `I.degree ≤ r`. -/
@[simp]
theorem ι_D_X_mem_vertStage_iff [Nontrivial B] {r : ℕ} {a : α} {I : ι →₀ ℕ} :
    ExteriorAlgebra.ι (RelJetAlgebra B ι α)
        (KaehlerDifferential.D B (RelJetAlgebra B ι α) (X (a, I))) ∈ vertStage B ι α r ↔
      I.degree ≤ r :=
  KaehlerDeRham.ι_D_X_mem_supportedForms_iff

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
    (fun _ h ↦ le_trans h (Nat.le_succ r)) (fun _ hp ↦ totalDeriv_mem_stage δ i hp) hω

variable (B ι α) in
/-- The algebraic vertical exterior derivative restricted to a finite vertical stage. -/
def vertStageDAlg (r : ℕ) : vertStage B ι α r →ₗ[B] vertStage B ι α r where
  toFun ω := ⟨dAlg B ι α ω, KaehlerDeRham.extDeriv_mem_supportedForms ω.property⟩
  map_add' ω η := Subtype.ext (map_add (dAlg B ι α) (ω : VertForms B ι α) (η : VertForms B ι α))
  map_smul' b ω := Subtype.ext ((dAlg B ι α).map_smul b (ω : VertForms B ι α))

@[simp]
theorem coe_vertStageDAlg (r : ℕ) (ω : vertStage B ι α r) :
    (vertStageDAlg B ι α r ω : VertForms B ι α) = dAlg B ι α ω := by
  rfl

/-- Finite-stage vertical exterior differentiation commutes with stage inclusions. -/
@[simp]
theorem vertStageDAlg_inclusion {r s : ℕ} (h : vertStage B ι α r ≤ vertStage B ι α s)
    (ω : vertStage B ι α r) :
    vertStageDAlg B ι α s (Subalgebra.inclusion h ω) =
      Subalgebra.inclusion h (vertStageDAlg B ι α r ω) := by
  apply Subtype.ext
  simp

/-- Total differentiation on vertical forms as an `R`-linear map between consecutive finite
vertical stages. -/
def vertStageTotalDerivForm (δ : ι → Derivation R B B) (i : ι) (r : ℕ) :
    vertStage B ι α r →ₗ[R] vertStage B ι α (r + 1) where
  toFun ω := ⟨totalDerivForm δ i ω, totalDerivForm_mem_vertStage δ i ω.property⟩
  map_add' ω η :=
    Subtype.ext (map_add (totalDerivForm δ i) (ω : VertForms B ι α) (η : VertForms B ι α))
  map_smul' c ω := Subtype.ext ((totalDerivForm δ i).map_smul c (ω : VertForms B ι α))

@[simp]
theorem coe_vertStageTotalDerivForm (δ : ι → Derivation R B B) (i : ι) (r : ℕ)
    (ω : vertStage B ι α r) :
    (vertStageTotalDerivForm δ i r ω : VertForms B ι α) = totalDerivForm δ i ω := by
  rfl

/-- Finite-stage vertical total differentiation commutes with stage inclusions. -/
@[simp]
theorem vertStageTotalDerivForm_inclusion (δ : ι → Derivation R B B) (i : ι) {r s : ℕ}
    (hrs : r ≤ s) (ω : vertStage B ι α r) :
    vertStageTotalDerivForm δ i s
        (Subalgebra.inclusion
          (by
            rw [vertStage_eq_supportedForms, vertStage_eq_supportedForms]
            exact KaehlerDeRham.supportedForms_mono fun _ h ↦ h.trans hrs) ω) =
      Subalgebra.inclusion
        (by
          rw [vertStage_eq_supportedForms, vertStage_eq_supportedForms]
          exact KaehlerDeRham.supportedForms_mono
            fun _ h ↦ h.trans (Nat.add_le_add_right hrs 1))
        (vertStageTotalDerivForm δ i r ω) := by
  apply Subtype.ext
  simp

end VerticalComplex

section UnsignedDoubleComplex

variable (R B ι α : Type*) [CommRing R] [CommRing B] [Algebra R B]

/-- The vertical differential `d_alg ⊗ id` on `VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)`. -/
def dAlgTensor :
    Module.End R (VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :=
  ((dAlg B ι α).restrictScalars R).rTensor (ExteriorAlgebra R (ι →₀ R))

variable {R B ι α}

/-- `dAlgTensor` squares to zero. -/
@[simp]
theorem dAlgTensor_dAlgTensor (x : VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :
    dAlgTensor R B ι α (dAlgTensor R B ι α x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul ω β =>
    simp [dAlgTensor, dAlg, KaehlerDeRham.extDeriv_extDeriv]
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
  simp only [dAlgTensor, horizDerivUnsigned, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.rTensor_map, LinearMap.map_rTensor]
  congr 2
  ext ω
  exact dAlg_totalDerivForm δ i ω

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
      rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, TensorProduct.tmul_zero]
    have hswap (i j : ι) :
        totalDerivForm δ j (totalDerivForm δ i ω) ⊗ₜ[R]
            (ExteriorAlgebra.ι R (Finsupp.single j (1 : R)) *
              (ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) * β)) +
          totalDerivForm δ i (totalDerivForm δ j ω) ⊗ₜ[R]
            (ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) *
              (ExteriorAlgebra.ι R (Finsupp.single j (1 : R)) * β)) = 0 := by
      rw [totalDerivForm_comm (hδ j i), ← TensorProduct.tmul_add, ← mul_assoc, ← mul_assoc,
        ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul, TensorProduct.tmul_zero]
    simp only [horizDerivUnsigned_tmul, map_sum]
    exact Finset.sum_sum_eq_zero_of_diag Finset.univ
      (fun i _ ↦ hdiag i) (fun i _ j _ _ ↦ hswap i j)
  | add x y hx hy => simp [hx, hy]

end UnsignedDoubleComplex

end

end RelJetAlgebra
end TauCeti
