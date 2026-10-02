/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree

/-!
# The PBW representation of a Lie algebra on a polynomial algebra

Let `L` be a Lie algebra over a commutative ring `R`, free with a basis `b` indexed by a linearly
ordered type `ι`, and let `S = R[zᵢ | i ∈ ι]` be the polynomial algebra on the same index set.
This file constructs the representation of `L` on `S` that proves the linear-independence half
of the Poincaré--Birkhoff--Witt theorem: a Lie algebra homomorphism

`b.pbwPolynomialRep : L →ₗ⁅R⁆ Module.End R S`

such that

* `bᵢ` acts on a monomial `z^σ` all of whose variables are at least `i` by multiplication by
  `zᵢ`;
* every `x : L` acts on a polynomial of total degree at most `d` as multiplication by the linear
  form `zₓ = ∑ᵢ (b.repr x i) zᵢ`, up to an error of total degree at most `d`.

Given a word `x₁ ⋯ xₙ` in `L`, the induced action of `U(L)` therefore sends `1` to `zₓ₁ ⋯ zₓₙ`
up to lower-degree terms, and sends an ordered monomial `bᵢ₁ ⋯ bᵢₙ` (`i₁ ≤ ⋯ ≤ iₙ`) to the monomial
`zᵢ₁ ⋯ zᵢₙ` exactly. This is what separates the graded pieces of the PBW filtration from each
other.

## The construction

The action of `bₗ` on a monomial `z^σ` is defined by induction on the degree of `σ`. If every
variable of `σ` is at least `l`, it is multiplication by `zₗ`. Otherwise `σ = τ + eμ` where `μ` is
the least variable of `σ` and `μ < l`, and the value is forced by the commutator relation that the
representation must satisfy:

`bₗ · z^σ = zμ zₗ z^τ + bμ · (bₗ · z^τ - zₗ z^τ) + ⁅bₗ, bμ⁆ · z^τ`,

where all actions on the right are on polynomials of degree less than that of `σ`. The induction
is carried out by iterating a single step on bilinear maps `L → S → S`; the iterates agree on
polynomials of degree at most `n` from the `n`-th one onwards, and their limit is the action.
Verifying that the result is a Lie algebra homomorphism is again an induction on degree, whose
only nontrivial case uses the Jacobi identity.

## Main definitions and results

* `Module.Basis.pbwPolynomialRep`: the representation.
* `Module.Basis.pbwPolynomialRep_basis_monomial_of_le`: the action of `bₗ` on a monomial in
  variables at least `l` is multiplication by `zₗ`.
* `Module.Basis.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree`: up to terms of total degree at
  most `d`, the action on a polynomial of total degree at most `d` is multiplication by the
  corresponding linear form.
* `Module.Basis.pbwPolynomialRep_mem_restrictTotalDegree`: the action raises total degree by at
  most one.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4,
  Lemma A, whose proof this file follows.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

open MvPolynomial

universe u v w

namespace Module.Basis

variable {R : Type u} {L : Type v} {ι : Type w} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LinearOrder ι] (b : Basis ι R L)

local notation "S" => MvPolynomial ι R

local notation "S≤" => MvPolynomial.restrictTotalDegree ι R

attribute [local instance 100] LieRing.ofAssociativeRing

namespace PBWPolynomialRep

/-! ### Monomial bookkeeping -/

omit [LinearOrder ι] in
private theorem X_mul_monomial (i : ι) (σ : ι →₀ ℕ) :
    (X i : S) * monomial σ 1 = monomial (σ + Finsupp.single i 1) 1 := by
  rw [monomial_add_single, pow_one, mul_comm]

omit [LinearOrder ι] in
/-- A bilinear map out of `L × S` sends `L × S≤ d` into a submodule as soon as it does so on basis
vectors and monomials of degree at most `d`. -/
private theorem apply_mem_of_basis {M : Type*} [AddCommGroup M] [Module R M]
    (Φ : L →ₗ[R] S →ₗ[R] M) (N : Submodule R M) (d : ℕ)
    (h : ∀ (l : ι) (σ : ι →₀ ℕ), σ.degree ≤ d → Φ (b l) (monomial σ 1) ∈ N) (x : L) {p : S}
    (hp : p ∈ S≤ d) : Φ x p ∈ N := by
  have hle : Submodule.map₂ Φ (Submodule.span R (Set.range b))
      (Submodule.span R ((monomial · 1) '' {σ : ι →₀ ℕ | σ.degree ≤ d})) ≤ N := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨σ, hσ, rfl⟩, rfl⟩
    exact h l σ hσ
  rw [b.span_eq, ← restrictTotalDegree_eq_span] at hle
  exact Submodule.map₂_le.1 hle x Submodule.mem_top p hp

/-- A monomial in which some variable is less than `l` splits off its least variable `μ < l`. -/
private theorem exists_eq_add_single {l : ι} {σ : ι →₀ ℕ} (h : ¬ ∀ i ∈ σ.support, l ≤ i) :
    ∃ (μ : ι) (τ : ι →₀ ℕ), μ < l ∧ (∀ i ∈ τ.support, μ ≤ i) ∧ σ = τ + Finsupp.single μ 1 := by
  push Not at h
  obtain ⟨i, hi, hil⟩ := h
  have hne : σ.support.Nonempty := ⟨i, hi⟩
  set μ := σ.support.min' hne
  have hμ : μ ∈ σ.support := σ.support.min'_mem hne
  refine ⟨μ, σ - Finsupp.single μ 1, (σ.support.min'_le i hi).trans_lt hil, fun j hj ↦ ?_, ?_⟩
  · refine σ.support.min'_le j (Finsupp.mem_support_iff.2 fun hσj ↦ ?_)
    exact Finsupp.mem_support_iff.1 hj (by simp [hσj])
  · refine (tsub_add_cancel_of_le ?_).symm
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hμ)

/-- If `μ` is at most every variable of `τ` and at most `l`, it is at most every variable of
`τ + eₗ`. -/
private theorem le_of_mem_support_add_single {μ l : ι} {τ : ι →₀ ℕ}
    (hμτ : ∀ i ∈ τ.support, μ ≤ i) (hμl : μ ≤ l) {i : ι}
    (hi : i ∈ (τ + Finsupp.single l 1).support) : μ ≤ i := by
  rcases Finset.mem_union.1 (Finsupp.support_add hi) with hi | hi
  · exact hμτ i hi
  · rwa [Finset.mem_singleton.1 (Finsupp.support_single_subset hi)]

/-! ### The inductive step -/

/-- The linear form `x ↦ zₓ`, sending `bᵢ` to the variable `zᵢ`. -/
private noncomputable def gen : L →ₗ[R] S :=
  b.constr R X

omit [LinearOrder ι] in
private theorem gen_basis (i : ι) : gen b (b i) = X i :=
  b.constr_basis R X i

/-- Multiplication by the linear form `zₓ`. -/
private noncomputable def naive : L →ₗ[R] S →ₗ[R] S :=
  (LinearMap.mul R S).comp (gen b)

omit [LinearOrder ι] in
private theorem naive_apply (x : L) (p : S) : naive b x p = gen b x * p :=
  rfl

omit [LinearOrder ι] in
private theorem naive_mem {d : ℕ} (x : L) {p : S} (hp : p ∈ S≤ d) : naive b x p ∈ S≤ (d + 1) :=
  apply_mem_of_basis b (naive b) _ d (fun l σ hσ ↦ by
    rw [naive_apply, gen_basis, X_mul_monomial]
    exact monomial_mem_restrictTotalDegree (by simpa using hσ) 1) x hp

/-- One step of the inductive construction: from an action `g`, valid in degrees below that of
`σ`, define the action of `bₗ` on `z^σ`. -/
private noncomputable def step (g : L →ₗ[R] S →ₗ[R] S) : L →ₗ[R] S →ₗ[R] S :=
  b.constr R fun l ↦ (basisMonomials ι R).constr R fun σ ↦
    if h : ∀ i ∈ σ.support, l ≤ i then X l * monomial σ 1
    else
      let μ := σ.support.min' (by
        push Not at h
        obtain ⟨i, hi, -⟩ := h
        exact ⟨i, hi⟩)
      let τ := σ - Finsupp.single μ 1
      X μ * X l * monomial τ 1 + g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) +
        g ⁅b l, b μ⁆ (monomial τ 1)

private theorem step_of_le (g : L →ₗ[R] S →ₗ[R] S) {l : ι} {σ : ι →₀ ℕ}
    (h : ∀ i ∈ σ.support, l ≤ i) : step b g (b l) (monomial σ 1) = X l * monomial σ 1 := by
  have hσ : (monomial σ 1 : S) = basisMonomials ι R σ := by simp
  rw [step, Basis.constr_basis, hσ, Basis.constr_basis, dite_eq_left_of_eq_true (eq_true h), hσ]

private theorem step_of_lt (g : L →ₗ[R] S →ₗ[R] S) {l μ : ι} {τ : ι →₀ ℕ} (hμl : μ < l)
    (hμτ : ∀ i ∈ τ.support, μ ≤ i) :
    step b g (b l) (monomial (τ + Finsupp.single μ 1) 1) =
      X μ * X l * monomial τ 1 + g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) +
        g ⁅b l, b μ⁆ (monomial τ 1) := by
  have hμ : μ ∈ (τ + Finsupp.single μ 1).support := by simp
  have h : ¬ ∀ i ∈ (τ + Finsupp.single μ 1).support, l ≤ i :=
    fun h ↦ (h μ hμ).not_gt hμl
  have hσ : (monomial (τ + Finsupp.single μ 1) 1 : S) =
      basisMonomials ι R (τ + Finsupp.single μ 1) := by simp
  rw [step, Basis.constr_basis, hσ, Basis.constr_basis,
    dite_eq_right_of_eq_false (eq_false h)]
  have hmin : (τ + Finsupp.single μ 1).support.min' ⟨μ, hμ⟩ = μ :=
    le_antisymm (Finset.min'_le _ _ hμ)
      (Finset.le_min' _ _ _ fun i hi ↦ le_of_mem_support_add_single hμτ le_rfl hi)
  simp only [hmin, add_tsub_cancel_right]

/-- The degree estimate `g x p - zₓ p ∈ S≤ d` for `p ∈ S≤ d`, in every degree. -/
private def DegreeBound (g : L →ₗ[R] S →ₗ[R] S) : Prop :=
  ∀ (d : ℕ) (x : L) (p : S), p ∈ (S≤ d) → g x p - gen b x * p ∈ S≤ d

omit [LinearOrder ι] in
private theorem DegreeBound.mem {g : L →ₗ[R] S →ₗ[R] S} (hg : DegreeBound b g) {d : ℕ} (x : L)
    {p : S} (hp : p ∈ S≤ d) : g x p ∈ S≤ (d + 1) := by
  have := Submodule.add_mem _ (restrictTotalDegree_mono ι R (Nat.le_succ d) (hg d x p hp))
    (naive_mem b x hp)
  rwa [naive_apply, sub_add_cancel] at this

private theorem degreeBound_step {g : L →ₗ[R] S →ₗ[R] S} (hg : DegreeBound b g) :
    DegreeBound b (step b g) := by
  intro d x p hp
  refine apply_mem_of_basis b (step b g - naive b) _ d (fun l σ hσ ↦ ?_) x hp
  rw [LinearMap.sub_apply, LinearMap.sub_apply, naive_apply, gen_basis]
  by_cases h : ∀ i ∈ σ.support, l ≤ i
  · rw [step_of_le b g h, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨μ, τ, hμl, hμτ, rfl⟩ := exists_eq_add_single h
  have hτ : τ.degree + 1 ≤ d := by simpa using hσ
  have hX : X μ * X l * monomial τ 1 + g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) +
        g ⁅b l, b μ⁆ (monomial τ 1) - X l * (X μ * monomial τ 1) =
      g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) + g ⁅b l, b μ⁆ (monomial τ 1) := by
    ring
  rw [step_of_lt b g hμl hμτ, ← X_mul_monomial, hX]
  have hτmem : (monomial τ 1 : S) ∈ S≤ τ.degree := monomial_mem_restrictTotalDegree le_rfl 1
  refine restrictTotalDegree_mono ι R hτ
    (Submodule.add_mem _ (DegreeBound.mem b hg _ ?_) (DegreeBound.mem b hg _ hτmem))
  have := hg _ (b l) _ hτmem
  rwa [gen_basis] at this

/-- `step` only looks one degree down: actions agreeing in degree at most `d` give the same next
step in degree at most `d + 1`. -/
private theorem step_congr {g g' : L →ₗ[R] S →ₗ[R] S} (hg : DegreeBound b g) {d : ℕ}
    (hgg' : ∀ (x : L) (p : S), p ∈ (S≤ d) → g x p = g' x p) (x : L) {p : S}
    (hp : p ∈ S≤ (d + 1)) : step b g x p = step b g' x p := by
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.sub_apply, ← Submodule.mem_bot R]
  refine apply_mem_of_basis b (step b g - step b g') ⊥ (d + 1) (fun l σ hσ ↦ ?_) x hp
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.mem_bot, sub_eq_zero]
  by_cases h : ∀ i ∈ σ.support, l ≤ i
  · rw [step_of_le b g h, step_of_le b g' h]
  obtain ⟨μ, τ, hμl, hμτ, rfl⟩ := exists_eq_add_single h
  have hτmem : (monomial τ 1 : S) ∈ S≤ d :=
    monomial_mem_restrictTotalDegree (by simpa using hσ) 1
  have hq : g (b l) (monomial τ 1) - X l * monomial τ 1 ∈ S≤ d := by
    have := hg d (b l) _ hτmem
    rwa [gen_basis] at this
  rw [step_of_lt b g hμl hμτ, step_of_lt b g' hμl hμτ, hgg' _ _ hq, hgg' _ _ hτmem,
    hgg' _ _ hτmem]

/-- The iterates of `step`, starting from multiplication by the linear form. -/
private noncomputable def approx : ℕ → L →ₗ[R] S →ₗ[R] S
  | 0 => naive b
  | n + 1 => step b (approx n)

private theorem degreeBound_approx (n : ℕ) : DegreeBound b (approx b n) := by
  induction n with
  | zero =>
      intro d x p _
      rw [approx, naive_apply, sub_self]
      exact Submodule.zero_mem _
  | succ n ih => exact degreeBound_step b ih

private theorem approx_succ_eq (n : ℕ) (x : L) {p : S} (hp : p ∈ S≤ n) :
    approx b (n + 1) x p = approx b n x p := by
  induction n generalizing x p with
  | zero =>
      rw [← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.sub_apply, ← Submodule.mem_bot R]
      refine apply_mem_of_basis b (approx b 1 - approx b 0) ⊥ 0 (fun l σ hσ ↦ ?_) x hp
      rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.mem_bot, sub_eq_zero]
      have hσ : σ = 0 := (Finsupp.degree_eq_zero_iff σ).1 (Nat.le_zero.1 hσ)
      subst hσ
      rw [approx, approx, step_of_le b _ (by simp), naive_apply, gen_basis]
  | succ n ih => exact step_congr b (degreeBound_approx b (n + 1)) ih x hp

private theorem approx_add_eq (n k : ℕ) (x : L) {p : S} (hp : p ∈ S≤ n) :
    approx b (n + k) x p = approx b n x p := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [← add_assoc,
        approx_succ_eq b _ x (restrictTotalDegree_mono ι R (Nat.le_add_right n k) hp), ih]

/-! ### The limit action -/

/-- The limit of the iterates: on monomials of degree `n`, the `n`-th iterate. -/
private noncomputable def act : L →ₗ[R] S →ₗ[R] S :=
  b.constr R fun l ↦ (basisMonomials ι R).constr R fun σ ↦ approx b σ.degree (b l) (monomial σ 1)

private theorem act_eq_approx {d n : ℕ} (hdn : d ≤ n) (x : L) {p : S} (hp : p ∈ S≤ d) :
    act b x p = approx b n x p := by
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.sub_apply, ← Submodule.mem_bot R]
  refine apply_mem_of_basis b (act b - approx b n) ⊥ d (fun l σ hσ ↦ ?_) x hp
  have hσb : (monomial σ 1 : S) = basisMonomials ι R σ := by simp
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.mem_bot, sub_eq_zero, act,
    Basis.constr_basis, hσb, Basis.constr_basis, ← hσb]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (hσ.trans hdn)
  exact (approx_add_eq b _ k _ (monomial_mem_restrictTotalDegree le_rfl 1)).symm

private theorem act_sub_mem {d : ℕ} (x : L) {p : S} (hp : p ∈ S≤ d) :
    act b x p - gen b x * p ∈ S≤ d := by
  rw [act_eq_approx b le_rfl x hp]
  exact degreeBound_approx b d d x p hp

private theorem degreeBound_act : DegreeBound b (act b) :=
  fun _ x _ hp ↦ act_sub_mem b x hp

private theorem act_of_le {l : ι} {σ : ι →₀ ℕ} (h : ∀ i ∈ σ.support, l ≤ i) :
    act b (b l) (monomial σ 1) = X l * monomial σ 1 := by
  rw [act_eq_approx b (Nat.le_succ _) _ (monomial_mem_restrictTotalDegree le_rfl 1), approx,
    step_of_le b _ h]

private theorem act_of_lt {l μ : ι} {τ : ι →₀ ℕ} (hμl : μ < l) (hμτ : ∀ i ∈ τ.support, μ ≤ i) :
    act b (b l) (monomial (τ + Finsupp.single μ 1) 1) =
      X μ * X l * monomial τ 1 + act b (b μ) (act b (b l) (monomial τ 1) - X l * monomial τ 1) +
        act b ⁅b l, b μ⁆ (monomial τ 1) := by
  have hτmem : (monomial τ 1 : S) ∈ S≤ τ.degree := monomial_mem_restrictTotalDegree le_rfl 1
  have hq : approx b τ.degree (b l) (monomial τ 1) - X l * monomial τ 1 ∈ S≤ τ.degree := by
    have := degreeBound_approx b τ.degree τ.degree (b l) _ hτmem
    rwa [gen_basis] at this
  rw [act_eq_approx b le_rfl _
      (monomial_mem_restrictTotalDegree (s := τ + Finsupp.single μ 1) le_rfl 1), map_add,
    Finsupp.degree_single, approx, step_of_lt b _ hμl hμτ, act_eq_approx b le_rfl _ hτmem,
    act_eq_approx b le_rfl _ hτmem, act_eq_approx b le_rfl _ hq]

/-- The defining case of the commutator relation: `μ < l` and `μ` is at most every variable
of `τ`. -/
private theorem act_comm_of_lt {l μ : ι} {τ : ι →₀ ℕ} (hμl : μ < l)
    (hμτ : ∀ i ∈ τ.support, μ ≤ i) :
    act b (b l) (act b (b μ) (monomial τ 1)) =
      act b (b μ) (act b (b l) (monomial τ 1)) + act b ⁅b l, b μ⁆ (monomial τ 1) := by
  have hμ : act b (b μ) (X l * monomial τ 1) = X μ * X l * monomial τ 1 := by
    rw [X_mul_monomial, act_of_le b fun i hi ↦ le_of_mem_support_add_single hμτ hμl.le hi,
      mul_assoc, X_mul_monomial l τ]
  rw [act_of_le b hμτ, X_mul_monomial, act_of_lt b hμl hμτ, map_sub, hμ]
  abel

/-! ### The commutator relation -/

/-- The commutator relation for the action, in total degree at most `d`. -/
private def CommRel (d : ℕ) : Prop :=
  ∀ (x y : L) (p : S), p ∈ (S≤ d) → act b x (act b y p) = act b y (act b x p) + act b ⁅x, y⁆ p

/-- The defect `x ↦ y ↦ [act x, act y] - act ⁅x, y⁆`, as a bilinear map. -/
private noncomputable def defect : L →ₗ[R] L →ₗ[R] Module.End R S :=
  LinearMap.mk₂ R (fun x y ↦ act b x * act b y - act b y * act b x - act b ⁅x, y⁆)
    (fun x₁ x₂ y ↦ by simp only [map_add, add_lie, add_mul, mul_add]; abel)
    (fun c x y ↦ by
      simp only [map_smul, smul_lie, smul_mul_assoc, mul_smul_comm, smul_sub])
    (fun x y₁ y₂ ↦ by simp only [map_add, lie_add, add_mul, mul_add]; abel)
    (fun c x y ↦ by
      simp only [map_smul, lie_smul, smul_mul_assoc, mul_smul_comm, smul_sub])

private theorem commRel_of_basis {d : ℕ}
    (h : ∀ (l m : ι) (τ : ι →₀ ℕ), τ.degree ≤ d →
      act b (b l) (act b (b m) (monomial τ 1)) =
        act b (b m) (act b (b l) (monomial τ 1)) + act b ⁅b l, b m⁆ (monomial τ 1)) :
    CommRel b d := by
  have key : ∀ (l : ι) (y : L) (p : S), p ∈ (S≤ d) → defect b (b l) y p = 0 := by
    intro l y p hp
    rw [← Submodule.mem_bot R]
    refine apply_mem_of_basis b (defect b (b l)) ⊥ d
      (fun m τ hτ ↦ ?_) y hp
    simp [defect, h l m τ hτ]
  intro x y p hp
  have hx : ((defect b).flip y).flip p = 0 := b.ext fun l ↦ by simpa using key l y p hp
  have := LinearMap.congr_fun hx x
  simp only [defect, LinearMap.flip_apply, LinearMap.mk₂_apply, LinearMap.zero_apply,
    LinearMap.sub_apply, Module.End.mul_apply] at this
  rw [← sub_eq_zero, ← this]
  abel

/-- The expansion of `bₗ bₘ z^τ` when the least variable `ν` of `τ` is less than both `l` and `m`,
assuming the commutator relation one degree down. -/
private theorem act_act_eq_of_lt {l m ν : ι} {Ψ : ι →₀ ℕ} (hνl : ν < l) (hνm : ν < m)
    (hνΨ : ∀ i ∈ Ψ.support, ν ≤ i) (ih : CommRel b Ψ.degree) :
    act b (b l) (act b (b m) (monomial (Ψ + Finsupp.single ν 1) 1)) =
      act b (b ν) (act b (b l) (act b (b m) (monomial Ψ 1))) +
        act b ⁅b l, b ν⁆ (act b (b m) (monomial Ψ 1)) +
        act b ⁅b m, b ν⁆ (act b (b l) (monomial Ψ 1)) +
        act b ⁅b l, ⁅b m, b ν⁆⁆ (monomial Ψ 1) := by
  have hΨ : (monomial Ψ 1 : S) ∈ S≤ Ψ.degree := monomial_mem_restrictTotalDegree le_rfl 1
  -- `bₘ z^Ψ` is the monomial `zₘ z^Ψ` up to an error `w` of degree at most that of `Ψ`.
  set w := act b (b m) (monomial Ψ 1) - monomial (Ψ + Finsupp.single m 1) 1 with hw
  have hwmem : w ∈ S≤ Ψ.degree := by
    have := act_sub_mem b (b m) hΨ
    rwa [gen_basis, X_mul_monomial] at this
  have hνΨm : ∀ i ∈ (Ψ + Finsupp.single m 1).support, ν ≤ i :=
    fun i hi ↦ le_of_mem_support_add_single hνΨ hνm.le hi
  have hsplit : act b (b m) (monomial Ψ 1) = monomial (Ψ + Finsupp.single m 1) 1 + w := by
    rw [hw, add_sub_cancel]
  -- The commutator relation for `bₗ` and `bν` on `bₘ z^Ψ`.
  have hlν : act b (b l) (act b (b ν) (act b (b m) (monomial Ψ 1))) =
      act b (b ν) (act b (b l) (act b (b m) (monomial Ψ 1))) +
        act b ⁅b l, b ν⁆ (act b (b m) (monomial Ψ 1)) := by
    rw [hsplit]
    simp only [map_add]
    rw [act_comm_of_lt b hνl hνΨm, ih _ _ _ hwmem]
    abel
  rw [← X_mul_monomial, ← act_of_le b hνΨ, ih (b m) (b ν) _ hΨ, map_add, hlν,
    ih (b l) ⁅b m, b ν⁆ _ hΨ]
  abel

/-- The commutator relation in total degree at most `d`, by strong induction on `d`. -/
private theorem commRel (d : ℕ) : CommRel b d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  refine commRel_of_basis b fun l m τ hτ ↦ ?_
  -- the hard case: the least variable `ν` of `τ` is less than both `l` and `m`
  have hard : ∀ {l m : ι}, (¬ ∀ i ∈ τ.support, m ≤ i) → m < l →
      act b (b l) (act b (b m) (monomial τ 1)) =
        act b (b m) (act b (b l) (monomial τ 1)) + act b ⁅b l, b m⁆ (monomial τ 1) := by
    intro l m hm hml
    obtain ⟨ν, Ψ, hνm, hνΨ, rfl⟩ := exists_eq_add_single hm
    have hΨ : Ψ.degree < d := by simp at hτ; omega
    have hνl := hνm.trans hml
    have ihΨ := ih _ hΨ
    have hΨmem : (monomial Ψ 1 : S) ∈ S≤ Ψ.degree := monomial_mem_restrictTotalDegree le_rfl 1
    -- Expand both `bₗ bₘ z^τ` and `bₘ bₗ z^τ`; the cross terms `⁅bₗ, bν⁆ bₘ z^Ψ` and
    -- `⁅bₘ, bν⁆ bₗ z^Ψ` cancel. Writing `z^τ = bν z^Ψ`, the commutator relation one degree down
    -- turns the right-hand side into `bν ⁅bₗ, bₘ⁆ z^Ψ + ⁅⁅bₗ, bₘ⁆, bν⁆ z^Ψ`, and the Jacobi
    -- identity matches the remaining double brackets.
    rw [act_act_eq_of_lt b hνl hνm hνΨ ihΨ, act_act_eq_of_lt b hνm hνl hνΨ ihΨ,
      ← X_mul_monomial, ← act_of_le b hνΨ, ihΨ ⁅b l, b m⁆ (b ν) _ hΨmem,
      ihΨ (b l) (b m) _ hΨmem, map_add, leibniz_lie (b l) (b m) (b ν), map_add,
      LinearMap.add_apply]
    abel
  rcases lt_trichotomy m l with hml | rfl | hlm
  · by_cases hm : ∀ i ∈ τ.support, m ≤ i
    · exact act_comm_of_lt b hml hm
    · exact hard hm hml
  · rw [lie_self, map_zero, LinearMap.zero_apply, add_zero]
  · by_cases hl : ∀ i ∈ τ.support, l ≤ i
    · rw [act_comm_of_lt b hlm hl, ← lie_skew, map_neg, LinearMap.neg_apply]
      abel
    · rw [hard hl hlm, ← lie_skew, map_neg, LinearMap.neg_apply]
      abel

end PBWPolynomialRep

open PBWPolynomialRep

/-- **The PBW representation.** For a Lie algebra `L` with a basis `b` indexed by a linearly
ordered type `ι`, the representation of `L` on the polynomial algebra `R[zᵢ | i ∈ ι]` in which
`bₗ` acts on a monomial in variables at least `l` by multiplication by `zₗ`
(`Module.Basis.pbwPolynomialRep_basis_monomial_of_le`), and every element acts as multiplication
by its linear form up to lower-degree terms
(`Module.Basis.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree`). -/
noncomputable def pbwPolynomialRep : L →ₗ⁅R⁆ Module.End R (MvPolynomial ι R) where
  toLinearMap := act b
  map_lie' {x y} := by
    refine LinearMap.ext fun p ↦ ?_
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LieRing.of_associative_ring_bracket,
      LinearMap.sub_apply, Module.End.mul_apply,
      commRel b p.totalDegree x y p ((mem_restrictTotalDegree ι _ p).2 le_rfl)]
    abel

/-- A basis vector `bₗ` acts on a monomial all of whose variables are at least `l` as
multiplication by the variable `zₗ`. -/
theorem pbwPolynomialRep_basis_monomial_of_le {l : ι} {σ : ι →₀ ℕ}
    (h : ∀ i ∈ σ.support, l ≤ i) :
    b.pbwPolynomialRep (b l) (monomial σ 1) = X l * monomial σ 1 :=
  act_of_le b h

/-- On polynomials of total degree at most `d`, the action of `x` is multiplication by the linear
form `zₓ = b.constr R X x`, up to an error of total degree at most `d`. -/
theorem pbwPolynomialRep_sub_mul_mem_restrictTotalDegree {d : ℕ} (x : L) {p : MvPolynomial ι R}
    (hp : p ∈ restrictTotalDegree ι R d) :
    b.pbwPolynomialRep x p - b.constr R X x * p ∈ restrictTotalDegree ι R d :=
  act_sub_mem b x hp

/-- The action raises total degree by at most one. -/
theorem pbwPolynomialRep_mem_restrictTotalDegree {d : ℕ} (x : L) {p : MvPolynomial ι R}
    (hp : p ∈ restrictTotalDegree ι R d) :
    b.pbwPolynomialRep x p ∈ restrictTotalDegree ι R (d + 1) :=
  DegreeBound.mem b (degreeBound_act b) x hp

end Module.Basis
