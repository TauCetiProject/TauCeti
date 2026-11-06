/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# Polynomial jets and total derivatives

`TauCeti.PolynomialJet R ι α` has base variables indexed by `ι` and field-jet
variables indexed by a field component in `α` and an unordered multiset of base
indices. Thus mixed derivatives are symmetric by construction. Coefficients in
`R` are constant; explicit polynomial dependence on the base is allowed.

The total derivative sends `xᵛ` to the Kronecker delta and `uᵃ_I` to
`uᵃ_(μ ::ₘ I)`. These derivations commute. The subalgebra `stage R ι α r`
contains just the variables of jet order at most `r`. Total differentiation maps
stage `r` to stage `r + 1`, and every polynomial lies in some stage. Stages are
subalgebras of the same ambient algebra, so their transition maps are inclusions;
no fixed stage is asserted to be closed under total differentiation.

`aeval_totalDeriv` is the algebraic evaluation rule into an algebra with a
specified derivation. This is a polynomial model, not a construction of smooth
jets or an identification of polynomial and smooth functions.

## References

* Ian M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, for symmetric
  jet coordinates and total derivatives.

The construction uses Mathlib's `MvPolynomial.mkDerivation` and its generator
computation rule.
-/

public section

noncomputable section

namespace TauCeti

/-- Polynomial base coordinates and symmetric field-jet coordinates. -/
abbrev PolynomialJet (R ι α : Type*) [CommSemiring R] :=
  MvPolynomial (ι ⊕ (α × Multiset ι)) R

namespace PolynomialJet

variable {R ι α : Type*} [CommSemiring R]

/-- The order of a coordinate: base coordinates have order zero. -/
def coordinateOrder : ι ⊕ (α × Multiset ι) → ℕ
  | .inl _ => 0
  | .inr (_, I) => I.card

/-- The polynomial algebra of jets of order at most `r`, with all base coordinates. -/
def stage (R ι α : Type*) [CommSemiring R] (r : ℕ) : Subalgebra R (PolynomialJet R ι α) :=
  MvPolynomial.supported R {v | coordinateOrder v ≤ r}

/-- Stage membership is precisely a bound on the orders of the variables occurring. -/
theorem mem_stage_iff (p : PolynomialJet R ι α) (r : ℕ) :
    p ∈ stage R ι α r ↔ ∀ v ∈ p.vars, coordinateOrder v ≤ r := by
  simp [stage, MvPolynomial.mem_supported, Set.subset_def]

/-- A field-jet generator belongs to precisely the stages that allow its order. -/
@[simp]
theorem field_mem_stage_iff [Nontrivial R] (a : α) (I : Multiset ι) (r : ℕ) :
    (MvPolynomial.X (.inr (a, I)) : PolynomialJet R ι α) ∈ stage R ι α r ↔ I.card ≤ r := by
  simp [stage, coordinateOrder]

/-- Base coordinates belong to every stage. -/
@[simp]
theorem base_mem_stage (ν : ι) (r : ℕ) :
    (MvPolynomial.X (.inl ν) : PolynomialJet R ι α) ∈ stage R ι α r := by
  apply Algebra.subset_adjoin
  exact ⟨.inl ν, Nat.zero_le r, rfl⟩

/-- Increasing the jet budget gives an inclusion of polynomial algebras. -/
theorem stage_mono {r s : ℕ} (h : r ≤ s) : stage R ι α r ≤ stage R ι α s :=
  MvPolynomial.supported_mono fun _ hv => hv.trans h

/-- Every polynomial depends on jets of bounded order. -/
theorem exists_mem_stage (p : PolynomialJet R ι α) : ∃ r, p ∈ stage R ι α r := by
  classical
  exact ⟨p.vars.sup coordinateOrder, (mem_stage_iff p _).2
    (fun v hv => Finset.le_sup (f := coordinateOrder) hv)⟩

open Classical in
/-- The value of the total derivative on each coordinate. -/
def coordinateDerivative (μ : ι) : ι ⊕ (α × Multiset ι) → PolynomialJet R ι α :=
  fun v => match v with
  | .inl ν => if μ = ν then 1 else 0
  | .inr (a, I) => MvPolynomial.X (.inr (a, μ ::ₘ I))

/-- Total differentiation, including explicit polynomial base dependence. -/
def totalDeriv (μ : ι) : Derivation R (PolynomialJet R ι α) (PolynomialJet R ι α) :=
  MvPolynomial.mkDerivation R (coordinateDerivative μ)

/-- Total differentiation of a coordinate is its prescribed coordinate derivative. -/
theorem totalDeriv_X (μ : ι) (v : ι ⊕ (α × Multiset ι)) :
    totalDeriv (R := R) μ (MvPolynomial.X v) = coordinateDerivative μ v :=
  MvPolynomial.mkDerivation_X R _ v

/-- Base coordinate derivatives are the Kronecker delta. -/
@[simp]
theorem totalDeriv_base [DecidableEq ι] (μ ν : ι) :
    totalDeriv (R := R) (α := α) μ (MvPolynomial.X (.inl ν)) =
      if μ = ν then 1 else 0 := by
  classical
  simp [totalDeriv_X, coordinateDerivative]

/-- Differentiating a field jet appends an unordered base index. -/
@[simp]
theorem totalDeriv_field (μ : ι) (a : α) (I : Multiset ι) :
    totalDeriv (R := R) μ (MvPolynomial.X (.inr (a, I))) =
      MvPolynomial.X (.inr (a, μ ::ₘ I)) := by
  simp [totalDeriv_X, coordinateDerivative]

/-- Total derivatives commute, including on mixed symmetric jet coordinates. -/
theorem totalDeriv_commute (μ ν : ι) :
    Function.Commute (totalDeriv (R := R) (α := α) μ) (totalDeriv ν) := by
  classical
  intro p
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    have hv : totalDeriv (R := R) μ (totalDeriv ν (MvPolynomial.X v)) =
        totalDeriv ν (totalDeriv μ (MvPolynomial.X v)) := by
      cases v with
      | inl κ => simp only [totalDeriv_base]; split_ifs <;> simp
      | inr v => rcases v with ⟨a, I⟩; simp [Multiset.cons_swap]
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp]
    rw [hv]
    ring

/-- A coordinate derivative uses jets of at most one higher order. -/
theorem coordinateDerivative_mem_stage (μ : ι) {r : ℕ}
    (v : ι ⊕ (α × Multiset ι)) (hv : coordinateOrder v ≤ r) :
    coordinateDerivative (R := R) μ v ∈ stage R ι α (r + 1) := by
  classical
  cases v with
  | inl ν =>
    simp only [coordinateDerivative]
    split_ifs <;> simp
  | inr v =>
    rcases v with ⟨a, I⟩
    apply Algebra.subset_adjoin
    exact ⟨.inr (a, μ ::ₘ I), by simpa [coordinateOrder] using hv, rfl⟩

/-- Total differentiation raises the finite jet budget by at most one. -/
theorem totalDeriv_mem_stage (μ : ι) {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) : totalDeriv μ p ∈ stage R ι α (r + 1) := by
  induction hp using Algebra.adjoin_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    simpa only [totalDeriv_X] using coordinateDerivative_mem_stage (R := R) μ w hw
  | algebraMap c => simp
  | add p q hp hq ihp ihq => simpa using add_mem ihp ihq
  | mul p q hp hq ihp ihq =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (stage_mono (Nat.le_succ r) hp) ihq)
      (mul_mem (stage_mono (Nat.le_succ r) hq) ihp)

/-- The order estimate is sharp on each field-jet generator: its derivative is not
in the stage of its original order. In particular, finite stages are not closed under
all total derivatives when a base direction and field component are present. -/
theorem totalDeriv_field_notMem_stage [Nontrivial R] (μ : ι) (a : α) (I : Multiset ι) :
    totalDeriv (R := R) μ (MvPolynomial.X (.inr (a, I))) ∉ stage R ι α I.card := by
  simp

/-- Repeated total differentiation raises the stage by at most the number of derivatives. -/
theorem iterate_totalDeriv_mem_stage (μ : ι) (k : ℕ) {r : ℕ}
    {p : PolynomialJet R ι α} (hp : p ∈ stage R ι α r) :
    (totalDeriv μ)^[k] p ∈ stage R ι α (r + k) := by
  induction k with
  | zero => simpa using hp
  | succ k ih => simpa [Function.iterate_succ_apply', Nat.add_assoc] using
      totalDeriv_mem_stage μ ih

/-- A mixed string of total derivatives raises the stage by at most its length. -/
theorem foldr_totalDeriv_mem_stage (directions : List ι) {r : ℕ}
    {p : PolynomialJet R ι α} (hp : p ∈ stage R ι α r) :
    directions.foldr (fun μ q => totalDeriv μ q) p ∈ stage R ι α (r + directions.length) := by
  induction directions with
  | nil => simpa using hp
  | cons μ directions ih =>
    simpa [Nat.add_assoc] using totalDeriv_mem_stage μ ih

/-- Evaluation intertwines total differentiation with a derivation whenever it does so
on coordinates. This is the algebraic chain rule for field-jet evaluations. -/
theorem aeval_totalDeriv {A : Type*} [CommSemiring A] [Algebra R A]
    (f : ι ⊕ (α × Multiset ι) → A) (d : Derivation R A A) (μ : ι)
    (hf : ∀ v, d (f v) = MvPolynomial.aeval f (coordinateDerivative (R := R) μ v))
    (p : PolynomialJet R ι α) :
    MvPolynomial.aeval f (totalDeriv μ p) = d (MvPolynomial.aeval f p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [Derivation.leibniz, smul_eq_mul, totalDeriv_X, hp, hf]

-- A base-dependent polynomial exhibits both terms of the total derivative.
example (μ : ι) (a : α) :
    totalDeriv (R := R) μ
        (MvPolynomial.X (.inl μ) * MvPolynomial.X (.inr (a, (0 : Multiset ι))) ^ 2) =
      MvPolynomial.X (.inr (a, (0 : Multiset ι))) ^ 2 +
        2 * MvPolynomial.X (.inl μ) * MvPolynomial.X (.inr (a, (0 : Multiset ι))) *
          MvPolynomial.X (.inr (a, {μ})) := by
  classical
  simp [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]
  ring

end PolynomialJet

end TauCeti
