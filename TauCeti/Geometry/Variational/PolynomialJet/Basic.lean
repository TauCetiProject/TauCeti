/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Variational.PolynomialJet.Defs
import TauCeti.Geometry.Variational.PolynomialJet.Relative

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

The core definitions live in `TauCeti.Geometry.Variational.PolynomialJet.Defs`; stage finiteness,
stage-growth, and total-derivative commutation are derived from the relative jet algebra via
`TauCeti.RelJetAlgebra.polyJetEquivRel`.
-/

public section

namespace TauCeti

namespace PolynomialJet

open MvPolynomial

noncomputable section

variable {R ι α : Type*} [CommSemiring R]

/-- Every polynomial expression uses only finitely many jet orders. -/
theorem exists_mem_stage (p : PolynomialJet R ι α) : ∃ r, p ∈ stage R ι α r := by
  obtain ⟨r, hr⟩ := RelJetAlgebra.exists_mem_stage (RelJetAlgebra.polyJetEquivRel R ι α p)
  exact ⟨r, (RelJetAlgebra.polyJetEquivRel_mem_stage_iff r p).mp hr⟩

/-- A total derivative raises field-jet order by at most one. -/
theorem totalDeriv_mem_stage (i : ι) {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) : totalDeriv i p ∈ stage R ι α (r + 1) := by
  rw [← RelJetAlgebra.polyJetEquivRel_mem_stage_iff, RelJetAlgebra.polyJetEquivRel_totalDeriv]
  exact RelJetAlgebra.totalDeriv_mem_stage _ i
    ((RelJetAlgebra.polyJetEquivRel_mem_stage_iff r p).mpr hp)

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
  apply (RelJetAlgebra.polyJetEquivRel R ι α).injective
  simp only [RelJetAlgebra.polyJetEquivRel_totalDeriv]
  exact RelJetAlgebra.totalDeriv_comm (MvPolynomial.pderiv_comm i j) _

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
