/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import TauCeti.Geometry.Variational.PolynomialJet.Basic
public import TauCeti.RingTheory.Derivation.Coordinates
import Mathlib.RingTheory.Derivation.Lie
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.Data.Finsupp.Multiset

/-!
# The Euler operator on polynomial jets and the first variation formula

For a field component `a`, the Euler operator of polynomial jet expressions is

`E_a(L) = ∑_I (-D)_I (∂L/∂uᵃ_I)`,

where `I` runs over symmetric multi-indices, `D_I = ∏ᵢ Dᵢ ^ I i` is the iterated total
derivative (`PolynomialJet.iteratedTotalDeriv`, the monomial `TauCeti.multiIndexDeriv` in the
commuting total derivatives) and `(-D)_I = (-1)^|I| D_I`. Only finitely many partial derivatives
of `L` are nonzero, so the sum is finite (`PolynomialJet.euler_eq_sum`). From here on the base
dimension is finite: the base coordinates are indexed by a `Fintype`.

A characteristic `Q = (Qᵃ)ₐ` defines the prolonged evolutionary derivation
`pr Q = ∑_(a,I) (D_I Qᵃ) ∂/∂uᵃ_I` (`PolynomialJet.evolutionaryDeriv`), which commutes with every
total derivative. Top-degree horizontal forms `L dⁿx` are modelled by jet expressions `L`, and
the image of the horizontal differential in top degree by the total divergences
`∑ᵢ Dᵢ Θⁱ` (`PolynomialJet.totalDivergence`).

## Main results

* `PolynomialJet.euler_totalDeriv`: the Euler operator annihilates total derivatives,
  `E_a(Dᵢ f) = 0`; hence it annihilates total divergences (`euler_totalDivergence`).
* `PolynomialJet.mul_iteratedTotalDeriv_sub_mem_range_totalDivergence`: integration by parts,
  `g · D_I h ≡ (-1)^|I| (D_I g) · h` modulo total divergences.
* `PolynomialJet.exists_evolutionaryDeriv_eq_finsum_mul_euler_add_totalDivergence`: the first
  variation formula `pr Q (L) = ∑ₐ Qᵃ E_a(L) + ∑ᵢ Dᵢ Θⁱ` for some boundary family `Θ`.
* `PolynomialJet.euler_mem_stage`: the Euler expression of an order-`r` expression has order at
  most `2r`.
* `PolynomialJet.euler_of_mem_stage_zero`: for an expression of jet order zero, such as a
  potential `V(x, u)`, the Euler expression is the partial derivative `∂L/∂uᵃ`.

These are identities of polynomial jet expressions over an arbitrary commutative ring: no smooth
jet bundle, integral, or fundamental lemma of the calculus of variations is involved.

## References

* P. J. Olver, *Applications of Lie Groups to Differential Equations*, 2nd ed. (1993), §4.1 (the
  Euler operator, integration by parts and the vanishing of Euler expressions of total
  divergences) and §5.1 (evolutionary vector fields).
* I. M. Anderson, *The Variational Bicomplex* (1989), Chapters 1 and 2.
-/

public section

namespace TauCeti

namespace PolynomialJet

open MvPolynomial

noncomputable section

variable {R ι α : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Partial differentiation preserves every finite stage. -/
theorem pderiv_mem_stage (v : ι ⊕ (α × (ι →₀ ℕ))) {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) : pderiv v p ∈ stage R ι α r := by
  rw [mem_stage_iff] at hp ⊢
  exact fun a I hI ↦ hp a I (vars_pderiv_subset v p hI)

variable (R ι α) in
/-- The total divergence `(Θⁱ)ᵢ ↦ ∑ᵢ Dᵢ Θⁱ` of a finitely supported family of jet
expressions. -/
def totalDivergence : (ι →₀ PolynomialJet R ι α) →ₗ[R] PolynomialJet R ι α :=
  Finsupp.lsum R fun i ↦ (totalDeriv i).toLinearMap

theorem totalDivergence_apply (Θ : ι →₀ PolynomialJet R ι α) :
    totalDivergence R ι α Θ = Θ.sum fun i p ↦ totalDeriv i p := by
  simp [totalDivergence, Finsupp.lsum_apply]

@[simp]
theorem totalDivergence_single (i : ι) (p : PolynomialJet R ι α) :
    totalDivergence R ι α (Finsupp.single i p) = totalDeriv i p := by
  simp [totalDivergence_apply]

theorem totalDeriv_mem_range_totalDivergence (i : ι) (p : PolynomialJet R ι α) :
    totalDeriv i p ∈ LinearMap.range (totalDivergence R ι α) :=
  ⟨Finsupp.single i p, totalDivergence_single i p⟩

end CommSemiring

section CommRing

variable [CommRing R]

/-- Total derivatives commute as linear endomorphisms. -/
theorem commute_totalDeriv (i j : ι) :
    Commute (totalDeriv (R := R) (α := α) i : Module.End R (PolynomialJet R ι α))
      (totalDeriv (R := R) (α := α) j : Module.End R (PolynomialJet R ι α)) :=
  LinearMap.ext fun p ↦ totalDeriv_comm i j p

/-- Differentiating a total derivative in a field coordinate: the partial derivative in `uᵃ_I`
of `Dᵢ f` is `Dᵢ (∂f/∂uᵃ_I)`, plus `∂f/∂uᵃ_(I-eᵢ)` when `I` involves the direction `i`. -/
theorem pderiv_totalDeriv (i : ι) (a : α) (I : ι →₀ ℕ) (f : PolynomialJet R ι α) :
    pderiv (Sum.inr (a, I)) (totalDeriv i f) =
      totalDeriv i (pderiv (Sum.inr (a, I)) f) +
        if I i = 0 then 0 else pderiv (Sum.inr (a, I - Finsupp.single i 1)) f := by
  classical
  -- the commutator of the two derivations is a derivation, determined on the generators
  have h : ⁅(pderiv (Sum.inr (a, I)) : Derivation R (PolynomialJet R ι α) _), totalDeriv i⁆ =
      if I i = 0 then (0 : Derivation R (PolynomialJet R ι α) (PolynomialJet R ι α))
        else pderiv (Sum.inr (a, I - Finsupp.single i 1)) := by
    apply MvPolynomial.derivation_ext
    rintro (j | ⟨b, J⟩)
    · split <;> simp [Derivation.commutator_apply, pderiv_X, apply_ite]
    · rcases eq_or_ne (I i) 0 with hI | hI
      · -- `uᵇ_(J+eᵢ)` is never `uᵃ_I`, since `I` does not involve `i`
        have hJ : J + Finsupp.single i 1 ≠ I := fun h ↦ by simp [← h] at hI
        simp [Derivation.commutator_apply, pderiv_X, Pi.single_apply, apply_ite, hI, hJ]
      · obtain ⟨I, rfl⟩ : ∃ I', I = I' + Finsupp.single i 1 :=
          ⟨_, (Finsupp.sub_add_single_one_cancel hI).symm⟩
        by_cases hb : b = a <;> by_cases hJ : J = I <;>
          simp [Derivation.commutator_apply, pderiv_X, Pi.single_apply, apply_ite, hb, hJ]
  have := congr($h f)
  rw [Derivation.commutator_apply] at this
  rw [← sub_eq_iff_eq_add', this]
  split <;> simp

private theorem injective_field (a : α) :
    Function.Injective fun I : ι →₀ ℕ ↦ (Sum.inr (a, I) : ι ⊕ (α × (ι →₀ ℕ))) :=
  fun I J h ↦ by simpa using h

variable [Fintype ι]

/-- The iterated total derivative `D_I = ∏ᵢ Dᵢ ^ I i` for a multi-index `I`: the monomial
`TauCeti.multiIndexDeriv` in the commuting total derivatives. -/
def iteratedTotalDeriv (I : ι →₀ ℕ) : Module.End R (PolynomialJet R ι α) :=
  multiIndexDeriv (fun i ↦ totalDeriv i) commute_totalDeriv I

theorem iteratedTotalDeriv_def (I : ι →₀ ℕ) :
    iteratedTotalDeriv (R := R) (α := α) I =
      multiIndexDeriv (fun i ↦ totalDeriv i) commute_totalDeriv ⇑I := (rfl)

@[simp]
theorem iteratedTotalDeriv_zero :
    iteratedTotalDeriv (R := R) (α := α) (0 : ι →₀ ℕ) = 1 := by
  simp [iteratedTotalDeriv]

/-- Iterated total derivatives compose by adding their multi-indices: `D_{I+J} = D_I ∘ D_J`. -/
theorem iteratedTotalDeriv_add (I J : ι →₀ ℕ) :
    iteratedTotalDeriv (R := R) (α := α) (I + J) =
      iteratedTotalDeriv I * iteratedTotalDeriv J := by
  simp [iteratedTotalDeriv, multiIndexDeriv_add]

@[simp]
theorem iteratedTotalDeriv_single (i : ι) (k : ℕ) :
    iteratedTotalDeriv (R := R) (α := α) (Finsupp.single i k) =
      (totalDeriv (R := R) (α := α) i : Module.End R (PolynomialJet R ι α)) ^ k := by
  classical
  simp [iteratedTotalDeriv, Finsupp.single_eq_pi_single]

theorem iteratedTotalDeriv_add_single_one (I : ι →₀ ℕ) (i : ι) (p : PolynomialJet R ι α) :
    iteratedTotalDeriv (I + Finsupp.single i 1) p = totalDeriv i (iteratedTotalDeriv I p) := by
  classical
  simp [iteratedTotalDeriv, Finsupp.single_eq_pi_single, multiIndexDeriv_add_single']

/-- Total derivatives commute with iterated total derivatives. -/
theorem totalDeriv_iteratedTotalDeriv_comm (i : ι) (I : ι →₀ ℕ) (p : PolynomialJet R ι α) :
    totalDeriv i (iteratedTotalDeriv I p) = iteratedTotalDeriv I (totalDeriv i p) := by
  classical
  have h := (multiIndexDeriv_add_single' (fun i ↦ totalDeriv (R := R) (α := α) i)
    commute_totalDeriv I i).symm.trans
      (multiIndexDeriv_add_single _ commute_totalDeriv I i)
  exact LinearMap.congr_fun h p

@[simp]
theorem iteratedTotalDeriv_X_field (I : ι →₀ ℕ) (a : α) (J : ι →₀ ℕ) :
    iteratedTotalDeriv (R := R) I (X (Sum.inr (a, J))) = X (Sum.inr (a, J + I)) := by
  induction I using Finsupp.induction_add_single_one with
  | zero => simp
  | add_single_one i I ih => simp [iteratedTotalDeriv_add_single_one, ih, add_assoc]

open Classical in
@[simp]
theorem iteratedTotalDeriv_X_base (I : ι →₀ ℕ) (j : ι) :
    iteratedTotalDeriv (R := R) (α := α) I (X (Sum.inl j)) =
      if I = 0 then X (Sum.inl j) else if I = Finsupp.single j 1 then 1 else 0 := by
  induction I using Finsupp.induction_add_single_one with
  | zero => simp
  | add_single_one i I ih =>
    rw [iteratedTotalDeriv_add_single_one, ih]
    rcases eq_or_ne I 0 with rfl | hI
    · simp [totalDeriv_X_base, Finsupp.single_left_inj one_ne_zero, eq_comm]
    · -- `I + eᵢ` has degree at least `2`, so it is not the unit multi-index `eⱼ`
      have hj : I + Finsupp.single i 1 ≠ Finsupp.single j 1 := fun h ↦
        hI (by simpa [Finsupp.degree_eq_zero_iff] using congr(Finsupp.degree $h))
      split_ifs <;> simp_all

open Classical in
@[simp]
theorem iteratedTotalDeriv_C (I : ι →₀ ℕ) (c : R) :
    iteratedTotalDeriv (α := α) I (C c) = if I = 0 then C c else 0 := by
  induction I using Finsupp.induction_add_single_one with
  | zero => simp
  | add_single_one i I ih =>
    rw [iteratedTotalDeriv_add_single_one, ih]
    split <;> simp

open Classical in
@[simp]
theorem iteratedTotalDeriv_one (I : ι →₀ ℕ) :
    iteratedTotalDeriv (R := R) (α := α) I 1 = if I = 0 then 1 else 0 := by
  simpa using iteratedTotalDeriv_C (α := α) I (1 : R)

/-- An iterated total derivative `D_I` raises field-jet order by at most `|I|`. -/
theorem iteratedTotalDeriv_mem_stage (I : ι →₀ ℕ) {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) : iteratedTotalDeriv I p ∈ stage R ι α (r + I.degree) := by
  induction I using Finsupp.induction_add_single_one with
  | zero => simpa using hp
  | add_single_one i I ih =>
    rw [iteratedTotalDeriv_add_single_one, map_add, Finsupp.degree_single, ← add_assoc]
    exact totalDeriv_mem_stage i ih

/-- The prolonged evolutionary derivation `pr Q` with characteristic `Q`: it annihilates the
base coordinates and sends `uᵃ_I` to `D_I Qᵃ`. -/
def evolutionaryDeriv (Q : α → PolynomialJet R ι α) :
    Derivation R (PolynomialJet R ι α) (PolynomialJet R ι α) :=
  mkDerivation R (Sum.elim 0 fun aI ↦ iteratedTotalDeriv aI.2 (Q aI.1))

@[simp]
theorem evolutionaryDeriv_X_base (Q : α → PolynomialJet R ι α) (j : ι) :
    evolutionaryDeriv Q (X (Sum.inl j)) = 0 := by
  simp [evolutionaryDeriv]

@[simp]
theorem evolutionaryDeriv_X_field (Q : α → PolynomialJet R ι α) (a : α) (I : ι →₀ ℕ) :
    evolutionaryDeriv Q (X (Sum.inr (a, I))) = iteratedTotalDeriv I (Q a) := by
  simp [evolutionaryDeriv]

/-- A derivation that annihilates the base coordinates and sends each `uᵃ_I` to `D_I Qᵃ` is the
prolonged evolutionary derivation `pr Q`. -/
theorem evolutionaryDeriv_unique (Q : α → PolynomialJet R ι α)
    (D : Derivation R (PolynomialJet R ι α) (PolynomialJet R ι α))
    (hx : ∀ j, D (X (Sum.inl j)) = 0)
    (hu : ∀ a I, D (X (Sum.inr (a, I))) = iteratedTotalDeriv I (Q a)) :
    D = evolutionaryDeriv Q := by
  apply MvPolynomial.derivation_ext
  rintro (j | ⟨a, I⟩) <;> simp [hx, hu]

/-- Prolonged evolutionary derivations commute with total derivatives. -/
theorem evolutionaryDeriv_totalDeriv_comm (Q : α → PolynomialJet R ι α) (i : ι)
    (p : PolynomialJet R ι α) :
    evolutionaryDeriv Q (totalDeriv i p) = totalDeriv i (evolutionaryDeriv Q p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    have hv : evolutionaryDeriv Q (totalDeriv i (X v)) =
        totalDeriv i (evolutionaryDeriv Q (X v)) := by
      rcases v with j | ⟨a, I⟩
      · simp only [totalDeriv_X_base, evolutionaryDeriv_X_base, map_zero]
        split <;> simp
      · simp [iteratedTotalDeriv_add_single_one]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp, hv]
    ring

/-- The prolonged evolutionary derivation is `pr Q = ∑_(a,I) (D_I Qᵃ) ∂/∂uᵃ_I`. -/
theorem evolutionaryDeriv_apply (Q : α → PolynomialJet R ι α) (p : PolynomialJet R ι α) :
    evolutionaryDeriv Q p =
      ∑ᶠ aI : α × (ι →₀ ℕ), pderiv (Sum.inr aI) p * iteratedTotalDeriv aI.2 (Q aI.1) := by
  classical
  have hfin : ∀ q : PolynomialJet R ι α, Function.HasFiniteSupport fun aI : α × (ι →₀ ℕ) ↦
      pderiv (Sum.inr aI) q * iteratedTotalDeriv aI.2 (Q aI.1) := fun q ↦
    hasFiniteSupport_pderiv Sum.inr_injective q
      (fun aI x ↦ x * iteratedTotalDeriv aI.2 (Q aI.1)) (by simp)
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, hp, hq, ← finsum_add_distrib (hfin p) (hfin q)]
    simp [add_mul]
  | mul_X p v hp =>
    -- on a single variable the sum has at most one nonzero term
    have hv : ∑ᶠ aI : α × (ι →₀ ℕ), pderiv (Sum.inr aI) (X v) *
        iteratedTotalDeriv aI.2 (Q aI.1) = evolutionaryDeriv Q (X v) := by
      rcases v with j | ⟨a, I⟩
      · simp [pderiv_X]
      · rw [finsum_eq_single _ (a, I) fun aI h ↦ by
          rw [pderiv_X_of_ne (Sum.inr_injective.ne h).symm, zero_mul]]
        simp
    simp only [Derivation.leibniz, smul_eq_mul, add_mul, mul_assoc]
    rw [finsum_add_distrib, ← mul_finsum' _ _ (hfin (X v)), ← mul_finsum' _ _ (hfin p), hv, hp]
    · exact (hfin (X v)).subset fun aI h ↦ by simpa [mul_assoc] using right_ne_zero_of_mul h
    · exact (hfin p).subset fun aI h ↦ by simpa [mul_assoc] using right_ne_zero_of_mul h

private theorem hasFiniteSupport_euler (a : α) (f : PolynomialJet R ι α) :
    Function.HasFiniteSupport fun I ↦
      (-1 : R) ^ I.degree • iteratedTotalDeriv I (pderiv (Sum.inr (a, I)) f) :=
  hasFiniteSupport_pderiv (injective_field a) f
    (fun I x ↦ (-1 : R) ^ I.degree • iteratedTotalDeriv I x) (by simp)

/-- The Euler operator `E_a(f) = ∑_I (-D)_I (∂f/∂uᵃ_I)` of the field component `a`. -/
def euler (a : α) : PolynomialJet R ι α →ₗ[R] PolynomialJet R ι α where
  toFun f := ∑ᶠ I, (-1 : R) ^ I.degree • iteratedTotalDeriv I (pderiv (Sum.inr (a, I)) f)
  map_add' f g := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib (hasFiniteSupport_euler a f) (hasFiniteSupport_euler a g)
  map_smul' c f := by
    rw [RingHom.id_apply, smul_finsum' c (hasFiniteSupport_euler a f)]
    refine finsum_congr fun I ↦ ?_
    rw [Derivation.map_smul, LinearMap.map_smul, smul_comm]

theorem euler_apply (a : α) (f : PolynomialJet R ι α) :
    euler a f =
      ∑ᶠ I, (-1 : R) ^ I.degree • iteratedTotalDeriv I (pderiv (Sum.inr (a, I)) f) :=
  (rfl)

/-- The Euler operator is the finite sum over any set of multi-indices outside which the
partial derivatives vanish. -/
theorem euler_eq_sum (a : α) (f : PolynomialJet R ι α) (s : Finset (ι →₀ ℕ))
    (hs : ∀ I ∉ s, pderiv (Sum.inr (a, I)) f = 0) :
    euler a f =
      ∑ I ∈ s, (-1 : R) ^ I.degree • iteratedTotalDeriv I (pderiv (Sum.inr (a, I)) f) := by
  refine finsum_eq_sum_of_support_subset _ fun I hI ↦ ?_
  by_contra h
  exact hI (by simp [hs I h])

@[simp]
theorem euler_C (a : α) (c : R) : euler (ι := ι) a (C c) = 0 := by
  simp [euler_apply]

@[simp]
theorem euler_X_base (a : α) (j : ι) : euler (R := R) a (X (Sum.inl j)) = 0 := by
  simp [euler_apply]

open Classical in
@[simp]
theorem euler_X_field (a b : α) (J : ι →₀ ℕ) :
    euler (R := R) a (X (Sum.inr (b, J))) = if a = b ∧ J = 0 then 1 else 0 := by
  rw [euler_eq_sum a _ {J} fun I hI ↦ pderiv_X_of_ne fun h ↦ by
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact hI (Finset.mem_singleton.2 h.2.symm)]
  by_cases hab : a = b
  · subst hab
    by_cases hJ : J = 0 <;> simp [hJ]
  · simp [hab, Ne.symm hab]

/-- **The Euler operator annihilates total derivatives**: `E_a(Dᵢ f) = 0`. -/
@[simp]
theorem euler_totalDeriv (a : α) (i : ι) (f : PolynomialJet R ι α) :
    euler a (totalDeriv i f) = 0 := by
  classical
  -- `T` collects the multi-indices of the component `a` occurring in `f`
  set T : Finset (ι →₀ ℕ) := f.vars.preimage _ (injective_field a).injOn
  have hT : ∀ I ∉ T, pderiv (Sum.inr (a, I)) f = 0 := fun I hI ↦
    pderiv_eq_zero_of_notMem_vars (by simpa [T] using hI)
  -- the correction terms `∂f/∂uᵃ_(I-eᵢ)` live on the shifted index set `T + eᵢ`
  have hshift : ∀ I ∉ T.image (· + Finsupp.single i 1),
      (if I i = 0 then 0 else pderiv (Sum.inr (a, I - Finsupp.single i 1)) f) = 0 := by
    intro I hI
    split_ifs with h
    · rfl
    · exact hT _ fun hmem ↦ hI (Finset.mem_image.2 ⟨_, hmem, Finsupp.sub_add_single_one_cancel h⟩)
  rw [euler_eq_sum a _ (T ∪ T.image (· + Finsupp.single i 1)) fun I hI ↦ by
    rw [Finset.mem_union, not_or] at hI
    rw [pderiv_totalDeriv, hT I hI.1, hshift I hI.2, map_zero, add_zero]]
  simp only [pderiv_totalDeriv, map_add, smul_add, Finset.sum_add_distrib]
  -- after shifting the correction sum back to `T`, the two sums cancel termwise
  rw [← Finset.sum_subset Finset.subset_union_left fun I _ hI ↦ by simp [hT I hI],
    ← Finset.sum_subset Finset.subset_union_right fun I _ hI ↦ by simp [hshift I hI],
    Finset.sum_image fun _ _ _ _ h ↦ add_right_cancel h, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun I _ ↦ ?_
  simp [iteratedTotalDeriv_add_single_one, totalDeriv_iteratedTotalDeriv_comm, pow_succ]

/-- The Euler operator annihilates total divergences. -/
@[simp]
theorem euler_totalDivergence (a : α) (Θ : ι →₀ PolynomialJet R ι α) :
    euler a (totalDivergence R ι α Θ) = 0 := by
  simp [totalDivergence_apply, Finsupp.sum]

/-- **Integration by parts** modulo total divergences:
`g · D_I h ≡ (-1)^|I| (D_I g) · h`. -/
theorem mul_iteratedTotalDeriv_sub_mem_range_totalDivergence (I : ι →₀ ℕ)
    (g h : PolynomialJet R ι α) :
    g * iteratedTotalDeriv I h - (-1 : R) ^ I.degree • (iteratedTotalDeriv I g * h) ∈
      LinearMap.range (totalDivergence R ι α) := by
  induction I using Finsupp.induction_add_single_one generalizing g with
  | zero => simp
  | add_single_one i I ih =>
    -- `g · Dᵢ(D_I h) = Dᵢ(g · D_I h) - (Dᵢ g) · D_I h`, and the last term is handled by `ih`
    have key : g * iteratedTotalDeriv (I + Finsupp.single i 1) h -
        (-1 : R) ^ (I + Finsupp.single i 1).degree •
          (iteratedTotalDeriv (I + Finsupp.single i 1) g * h) =
        totalDeriv i (g * iteratedTotalDeriv I h) -
          (totalDeriv i g * iteratedTotalDeriv I h -
            (-1 : R) ^ I.degree • (iteratedTotalDeriv I (totalDeriv i g) * h)) := by
      simp only [iteratedTotalDeriv_add_single_one, Derivation.leibniz, smul_eq_mul, map_add,
        Finsupp.degree_single, pow_succ, totalDeriv_iteratedTotalDeriv_comm, mul_neg_one,
        neg_smul]
      ring
    rw [key]
    exact sub_mem (totalDeriv_mem_range_totalDivergence i _) (ih _)

/-- **The first variation formula**: for every characteristic `Q` there is a boundary family
`Θ` with `pr Q (L) = ∑ₐ Qᵃ E_a(L) + ∑ᵢ Dᵢ Θⁱ`. -/
theorem exists_evolutionaryDeriv_eq_finsum_mul_euler_add_totalDivergence
    (Q : α → PolynomialJet R ι α) (L : PolynomialJet R ι α) :
    ∃ Θ : ι →₀ PolynomialJet R ι α,
      evolutionaryDeriv Q L = ∑ᶠ a, Q a * euler a L + totalDivergence R ι α Θ := by
  have hfin₁ := hasFiniteSupport_pderiv Sum.inr_injective L
    (fun aI x ↦ x * iteratedTotalDeriv aI.2 (Q aI.1)) (by simp)
  have hfin₂ := hasFiniteSupport_pderiv Sum.inr_injective L
    (fun aI x ↦ Q aI.1 * ((-1 : R) ^ aI.2.degree • iteratedTotalDeriv aI.2 x)) (by simp)
  have hE : ∑ᶠ a, Q a * euler a L = ∑ᶠ aI : α × (ι →₀ ℕ),
      Q aI.1 * ((-1 : R) ^ aI.2.degree • iteratedTotalDeriv aI.2 (pderiv (Sum.inr aI) L)) := by
    rw [finsum_curry _ hfin₂]
    exact finsum_congr fun a ↦ mul_finsum' _ _ (hasFiniteSupport_euler a L)
  suffices evolutionaryDeriv Q L - ∑ᶠ a, Q a * euler a L ∈
      LinearMap.range (totalDivergence R ι α) by
    obtain ⟨Θ, hΘ⟩ := this
    exact ⟨Θ, by rw [hΘ, add_sub_cancel]⟩
  -- integrate each term `(∂L/∂uᵃ_I) · D_I Qᵃ` by parts
  rw [evolutionaryDeriv_apply, hE, ← finsum_sub_distrib hfin₁ hfin₂]
  refine finsum_induction _ (zero_mem _) (fun _ _ ↦ add_mem) fun aI ↦ ?_
  rw [mul_smul_comm, mul_comm (Q aI.1)]
  exact mul_iteratedTotalDeriv_sub_mem_range_totalDivergence _ _ _

/-- The Euler expression of an expression of field-jet order at most `r` has order at most
`2 r`. -/
theorem euler_mem_stage (a : α) {r : ℕ} {f : PolynomialJet R ι α}
    (hf : f ∈ stage R ι α r) : euler a f ∈ stage R ι α (2 * r) := by
  classical
  set T : Finset (ι →₀ ℕ) := f.vars.preimage _ (injective_field a).injOn
  rw [euler_eq_sum a f T fun I hI ↦ pderiv_eq_zero_of_notMem_vars (by simpa [T] using hI)]
  refine Subalgebra.sum_mem _ fun I hI ↦ Subalgebra.smul_mem _ ?_ _
  have hI : I.degree ≤ r := (mem_stage_iff f r).1 hf a I (by simpa [T] using hI)
  exact stage_mono (by omega) (iteratedTotalDeriv_mem_stage I (pderiv_mem_stage _ hf))

/-- For an expression of jet order zero, such as a potential `V(x, u)`, the Euler expression is
the partial derivative in the undifferentiated field coordinate: `E_a(L) = ∂L/∂uᵃ`. -/
theorem euler_of_mem_stage_zero (a : α) {L : PolynomialJet R ι α}
    (hL : L ∈ stage R ι α 0) : euler a L = pderiv (Sum.inr (a, 0)) L := by
  rw [euler_eq_sum a L {0} fun I hI ↦ pderiv_eq_zero_of_notMem_vars fun h ↦ hI <| by
    simpa [Finsupp.degree_eq_zero_iff] using (mem_stage_iff L 0).1 hL a I h]
  simp

end CommRing

end

end PolynomialJet

end TauCeti
