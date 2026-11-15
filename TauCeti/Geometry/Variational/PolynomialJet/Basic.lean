/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic.Ring

/-!
# Polynomial jets and total derivatives

`TauCeti.PolynomialJet R ι α` is the polynomial algebra on base coordinates indexed by `ι`
and field coordinates indexed by a field label `α` and a symmetric multi-index `ι →₀ ℕ`.
The multi-index records multiplicities, so mixed derivatives have a single coordinate.
Base coordinates are included: total differentiation differentiates position-dependent
polynomial coefficients as well as field coordinates.

`PolynomialJet.totalDeriv i` sends `xⱼ` to the Kronecker delta and `uᵃ_I` to
`uᵃ_(I+eᵢ)`. These derivations commute. The subalgebra `PolynomialJet.stage R ι α r`
contains precisely the expressions using field jets through order `r`, with unrestricted
polynomial dependence on the base coordinates. Every expression belongs to a stage, and a
total derivative raises its stage by at most one. The maps `PolynomialJet.stageDeriv` commute
with stage inclusions and satisfy the raised-stage Leibniz and commutation laws. In general a
total derivative does not preserve its input stage.

The evaluation theorem characterizes algebra maps that intertwine total differentiation
with derivations on a target algebra. This is the algebraic chain rule for evaluating jet
expressions, and permits differential substitutions as well as field evaluations. No smooth
jet bundle, differential forms, or convergence of infinite series is asserted here.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, §A, for symmetric jet
  coordinates and total derivatives.

The construction uses Mathlib's `MvPolynomial.mkDerivation`, its generator extensionality,
and `MvPolynomial.supported` for the finite-order subalgebras.
-/

public section

namespace TauCeti

/-- Polynomial expressions in base coordinates and symmetric field-jet coordinates.
The coefficient ring consists of constants; polynomial base dependence is represented by
the `Sum.inl` variables. -/
abbrev PolynomialJet (R ι α : Type*) [CommSemiring R] :=
  MvPolynomial (ι ⊕ (α × (ι →₀ ℕ))) R

namespace PolynomialJet

open MvPolynomial

noncomputable section

variable {R ι α : Type*} [CommSemiring R]

/-- Total differentiation in a base direction, including differentiation of base coordinates. -/
def totalDeriv (i : ι) :
    Derivation R (PolynomialJet R ι α) (PolynomialJet R ι α) := by
  classical
  exact mkDerivation R (Sum.elim (fun j ↦ if i = j then 1 else 0)
    (fun aI ↦ X (Sum.inr (aI.1, aI.2 + Finsupp.single i 1))))

open Classical in
@[simp]
theorem totalDeriv_X_base (i j : ι) :
    totalDeriv (R := R) (α := α) i (X (Sum.inl j)) = if i = j then 1 else 0 := by
  classical
  simp [totalDeriv]

@[simp]
theorem totalDeriv_X_field (i : ι) (a : α) (I : ι →₀ ℕ) :
    totalDeriv (R := R) i (X (Sum.inr (a, I))) =
      X (Sum.inr (a, I + Finsupp.single i 1)) := by
  simp [totalDeriv]

open Classical in
/-- The total derivative is determined by its actions on base and field coordinates. -/
theorem totalDeriv_unique (i : ι)
    (D : Derivation R (PolynomialJet R ι α) (PolynomialJet R ι α))
    (hx : ∀ j, D (X (Sum.inl j)) = if i = j then 1 else 0)
    (hu : ∀ a I, D (X (Sum.inr (a, I))) = X (Sum.inr (a, I + Finsupp.single i 1))) :
    D = totalDeriv i := by
  classical
  apply MvPolynomial.derivation_ext
  rintro (j | ⟨a, I⟩) <;> simp [hx, hu]

variable (R ι α)

/-- The finite-order polynomial jet algebra, embedded in the algebra on all jet variables.
Base-coordinate degree is unrestricted. -/
def stage (r : ℕ) : Subalgebra R (PolynomialJet R ι α) :=
  supported R {v | Sum.elim (fun _ ↦ True) (fun aI ↦ aI.2.degree ≤ r) v}

variable {R ι α}

/-- Membership in a finite stage means that every field variable occurring has bounded order. -/
theorem mem_stage_iff (p : PolynomialJet R ι α) (r : ℕ) :
    p ∈ stage R ι α r ↔ ∀ a I, Sum.inr (a, I) ∈ p.vars → I.degree ≤ r := by
  rw [stage, mem_supported]
  constructor
  · intro h a I hI
    exact h hI
  · intro h v hv
    rcases v with j | ⟨a, I⟩
    · trivial
    · exact h a I hv

/-- Increasing the jet-order budget gives the canonical inclusion of stage algebras. -/
theorem stage_mono : Monotone (stage R ι α) := by
  intro r s hrs
  apply supported_mono
  rintro (j | ⟨a, I⟩) h
  · trivial
  · exact h.trans hrs

@[simp]
theorem X_base_mem_stage (r : ℕ) (j : ι) :
    (X (Sum.inl j) : PolynomialJet R ι α) ∈ stage R ι α r := by
  exact Algebra.subset_adjoin ⟨Sum.inl j, trivial, rfl⟩

theorem X_field_mem_stage (r : ℕ) (a : α) (I : ι →₀ ℕ) (hI : I.degree ≤ r) :
    (X (Sum.inr (a, I)) : PolynomialJet R ι α) ∈ stage R ι α r := by
  exact Algebra.subset_adjoin ⟨Sum.inr (a, I), hI, rfl⟩

@[simp]
theorem X_field_mem_stage_iff [Nontrivial R] (r : ℕ) (a : α) (I : ι →₀ ℕ) :
    (X (Sum.inr (a, I)) : PolynomialJet R ι α) ∈ stage R ι α r ↔ I.degree ≤ r := by
  simp [stage]

/-- Every polynomial expression uses only finitely many jet orders. -/
theorem exists_mem_stage (p : PolynomialJet R ι α) : ∃ r, p ∈ stage R ι α r := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0, (stage R ι α 0).algebraMap_mem c⟩
  | add p q hp hq =>
    obtain ⟨r, hr⟩ := hp
    obtain ⟨s, hs⟩ := hq
    exact ⟨max r s, add_mem (stage_mono (le_max_left r s) hr)
      (stage_mono (le_max_right r s) hs)⟩
  | mul_X p v hp =>
    obtain ⟨r, hr⟩ := hp
    rcases v with j | ⟨a, I⟩
    · exact ⟨r, mul_mem hr (X_base_mem_stage r j)⟩
    · exact ⟨max r I.degree, mul_mem (stage_mono (le_max_left _ _) hr)
        (X_field_mem_stage _ a I (le_max_right _ _))⟩

/-- A total derivative raises field-jet order by at most one. -/
theorem totalDeriv_mem_stage (i : ι) {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) : totalDeriv i p ∈ stage R ι α (r + 1) := by
  classical
  induction hp using Algebra.adjoin_induction with
  | mem v hv =>
    obtain ⟨j | ⟨a, I⟩, hj, rfl⟩ := hv
    · simp only [totalDeriv_X_base]
      split <;> simp
    · rw [totalDeriv_X_field]
      exact X_field_mem_stage _ _ _ (by simpa using Nat.add_le_add_right hj 1)
  | algebraMap c => simp
  | add p q _ _ hp hq => simpa using add_mem hp hq
  | mul p q hp hq hDp hDq =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (stage_mono (Nat.le_succ r) hp) hDq)
      (mul_mem (stage_mono (Nat.le_succ r) hq) hDp)

/-- Total differentiation as a linear map between consecutive finite stages. -/
def stageDeriv (i : ι) (r : ℕ) : stage R ι α r →ₗ[R] stage R ι α (r + 1) where
  toFun p := ⟨totalDeriv i p, totalDeriv_mem_stage i p.property⟩
  map_add' p q :=
    Subtype.ext (map_add (totalDeriv i) (p : PolynomialJet R ι α) (q : PolynomialJet R ι α))
  map_smul' c p := Subtype.ext ((totalDeriv i).toLinearMap.map_smul c (p : PolynomialJet R ι α))

@[simp]
theorem coe_stageDeriv (i : ι) (r : ℕ) (p : stage R ι α r) :
    (stageDeriv i r p : PolynomialJet R ι α) = totalDeriv i p := by
  rfl

/-- Finite-stage differentiation commutes with the transition inclusions. -/
@[simp]
theorem stageDeriv_inclusion (i : ι) {r s : ℕ} (hrs : r ≤ s)
    (p : stage R ι α r) :
    stageDeriv i s (Subalgebra.inclusion (stage_mono hrs) p) =
      Subalgebra.inclusion (stage_mono (Nat.add_le_add_right hrs 1)) (stageDeriv i r p) := by
  apply Subtype.ext
  simp

/-- The finite-stage Leibniz rule uses the inclusion into the raised stage. -/
theorem stageDeriv_mul (i : ι) (r : ℕ) (p q : stage R ι α r) :
    stageDeriv i r (p * q) =
      Subalgebra.inclusion (stage_mono (Nat.le_succ r)) p * stageDeriv i r q +
        Subalgebra.inclusion (stage_mono (Nat.le_succ r)) q * stageDeriv i r p := by
  apply Subtype.ext
  simp [Derivation.leibniz]

/-- At the top-order generator the order increase is real; a finite stage is not closed
under total differentiation. -/
theorem totalDeriv_X_field_not_mem_stage [Nontrivial R] (i : ι) (a : α) (I : ι →₀ ℕ) :
    totalDeriv (R := R) i (X (Sum.inr (a, I))) ∉ stage R ι α I.degree := by
  simp

/-- Symmetry of multi-indices makes all total derivatives commute. -/
theorem totalDeriv_comm (i j : ι) (p : PolynomialJet R ι α) :
    totalDeriv i (totalDeriv j p) = totalDeriv j (totalDeriv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    have hv : totalDeriv (R := R) i (totalDeriv j (X v)) =
        totalDeriv j (totalDeriv i (X v)) := by
      rcases v with k | ⟨a, I⟩
      · simp [apply_ite]
      · simp [add_right_comm I]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp, hv]
    ring

/-- Commuting total derivatives give the same map from stage `r` to stage `r + 2`. -/
theorem stageDeriv_comm (i j : ι) (r : ℕ) (p : stage R ι α r) :
    stageDeriv i (r + 1) (stageDeriv j r p) =
      stageDeriv j (r + 1) (stageDeriv i r p) := by
  apply Subtype.ext
  simp [totalDeriv_comm]

section Evaluation

variable {A : Type*} [CommSemiring A] [Algebra R A]

open Classical in
/-- Evaluating jet expressions commutes with differentiation whenever the assigned
coordinates satisfy the base and prolongation equations. -/
theorem _root_.Derivation.aeval_polynomialJet (D : Derivation R A A) (i : ι) (x : ι → A)
    (u : α → (ι →₀ ℕ) → A)
    (hx : ∀ j, D (x j) = if i = j then 1 else 0)
    (hu : ∀ a I, D (u a I) = u a (I + Finsupp.single i 1))
    (p : PolynomialJet R ι α) :
    D (aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) p) =
      aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) (totalDeriv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    rcases v with j | ⟨a, I⟩ <;>
      simp [Derivation.leibniz, hp, hx, hu, apply_ite]

open Classical in
/-- An evaluation intertwines differentiation on every expression if and only if it does
so on base coordinates and field jets. -/
theorem _root_.Derivation.aeval_polynomialJet_iff (D : Derivation R A A) (i : ι) (x : ι → A)
    (u : α → (ι →₀ ℕ) → A) :
    (∀ p : PolynomialJet R ι α,
      D (aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) p) =
        aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) (totalDeriv i p)) ↔
      (∀ j, D (x j) = if i = j then 1 else 0) ∧
        (∀ a I, D (u a I) = u a (I + Finsupp.single i 1)) := by
  classical
  constructor
  · intro h
    exact ⟨fun j ↦ by simpa [apply_ite] using h (X (Sum.inl j)),
      fun a I ↦ by simpa using h (X (Sum.inr (a, I)))⟩
  · rintro ⟨hx, hu⟩ p
    exact D.aeval_polynomialJet i x u hx hu p

end Evaluation

end

end PolynomialJet
end TauCeti
