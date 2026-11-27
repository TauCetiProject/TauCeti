/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.GroupTheory.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
import Mathlib.Algebra.QuadraticDiscriminant
import TauCeti.Algebra.Group.Action.Pow
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Perron
import TauCeti.LinearAlgebra.RootSystem.Weyl.Chamber
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# A regular eigenvector of the bipartite Coxeter element

Let `b` be a base of a finite irreducible reduced crystallographic root system, and colour its
Dynkin diagram, which is a tree, by `Bool`. The bipartite Coxeter element `c` is the product of
the simple reflections of colour `true`, followed by those of colour `false`. Over a
field `K` containing `ℝ` and algebraically closed, such as `ℂ`, this file proves Steinberg's
theorem that `c` has a **regular eigenvector**, lying on no reflecting hyperplane, whose
eigenvalue is a primitive root of unity of order exactly the order `h` of `c`
(`RootPairing.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot`).

This is the geometric input of the uniform identification of the eigenvalues of a Coxeter element
with `ζ ^ (dᵢ - 1)` for the invariant degrees `dᵢ`: at a regular eigenvector, the invariant
degrees compute the characteristic polynomial.

## The argument

The Cartan matrix `C` of `b` is indecomposable and of finite type, so it has a left eigenvector
`y` with strictly positive real entries, for an eigenvalue `κ` with `0 < κ < 2` (when `b` has at
least two simple roots). Write `u₀` and `u₁` for the parts `∑ yᵢ αᵢ` of colour `true` and
`false`. Since simple roots of equal colour are orthogonal, the product of the reflections of one
colour negates the part of that colour and adds `λ = 2 - κ` times it to the other part. Hence `c`
preserves the real plane spanned by `u₀` and `u₁`, acting there by a matrix of trace `λ² - 2` and
determinant `1`. As `0 < λ < 2` its eigenvalues `μ` and `μ⁻¹` are not real, and the eigenvector
`(1 + μ) u₀ + λ u₁` is regular: every coroot takes real values on `u₀` and `u₁` whose sum, the
value on `u₀ + u₁`, is nonzero because `u₀ + u₁ = ∑ yᵢ αᵢ` is strictly positive on every simple
coroot. Finally if `μ ^ l = 1` then `c ^ l` fixes both eigenvectors, hence fixes `u₀ + u₁`, so
`c ^ l = 1` because the Weyl group acts freely on such vectors. With a single simple root `α`,
the element `c` is the reflection in `α` and `α` is a regular eigenvector for `-1`.

## Main results

* `RootPairing.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot`: the
  bipartite Coxeter element has a regular eigenvector whose eigenvalue is a primitive root of
  unity of order equal to the order of the element.

## References

* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§3.16–3.19.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §6, no. 2.
-/

public section

open Finset TauCeti

namespace RootPairing

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) (b : P.Base)

variable [P.IsCrystallographic]

/-- The value of a coroot on a real combination of the simple roots is real. -/
private theorem coroot'_sum_algebraMap_smul_root [Algebra ℝ K] (a : b.support → ℝ) (j : ι) :
    P.coroot' j (∑ i : b.support, algebraMap ℝ K (a i) • P.root i) =
      algebraMap ℝ K (∑ i : b.support, a i * P.pairingIn ℤ i j) := by
  simp only [map_sum, map_smul, root_coroot'_eq_pairing, smul_eq_mul, map_mul, map_intCast,
    ← P.algebraMap_pairingIn ℤ, algebraMap_int_eq, eq_intCast]

variable [CharZero K] [Finite ι] [P.IsReduced]

/-! ### The Coxeter plane -/

section Plane

variable [Algebra ℝ K]

omit [P.IsCrystallographic] [CharZero K] [Finite ι] [P.IsReduced] in
/-- The part `∑ yᵢ αᵢ` of colour `x` of a real combination of the simple roots. -/
noncomputable def colorPart (c : b.support → Bool) (y : b.support → ℝ) (x : Bool) : M :=
  ∑ i : b.support, algebraMap ℝ K (if c i = x then y i else 0) • P.root i

omit [P.IsCrystallographic] [CharZero K] [Finite ι] [P.IsReduced] in
/-- Unfolding lemma for `colorPart`. -/
theorem colorPart_def (c : b.support → Bool) (y : b.support → ℝ) (x : Bool) :
    colorPart P b c y x =
      ∑ i : b.support, algebraMap ℝ K (if c i = x then y i else 0) • P.root i :=
  (rfl)

omit [P.IsCrystallographic] [CharZero K] [Finite ι] [P.IsReduced] in
/-- The `i`-th simple-root coordinate of a colour part `colorPart P b c y x`. -/
@[simp]
theorem toWeightBasis_repr_colorPart [P.IsRootSystem] (c : b.support → Bool)
    (y : b.support → ℝ) (x : Bool) (i : b.support) :
    b.toWeightBasis.repr (colorPart P b c y x) i = algebraMap ℝ K (if c i = x then y i else 0) := by
  classical
  rw [colorPart, map_sum, Finset.sum_apply', Finset.sum_eq_single i
    (fun j _ hij ↦ by split_ifs <;> simp [b.toWeightBasis_repr_root, hij]) (by simp)]
  split_ifs <;> simp [b.toWeightBasis_repr_root, Algebra.smul_def]

variable {b} {c : (coxeterMatrixOfBase P b).graph.Coloring Bool} {y : b.support → ℝ} {κ : ℝ}

omit [P.IsCrystallographic] [CharZero K] [Finite ι] [P.IsReduced] in
/-- The two colour parts add up to the whole combination. -/
private theorem colorPart_add (c : b.support → Bool) (y : b.support → ℝ) :
    colorPart P b c y true + colorPart P b c y false =
      ∑ i : b.support, algebraMap ℝ K (y i) • P.root i := by
  rw [colorPart, colorPart, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  cases c i <;> simp

omit [CharZero K] [Finite ι] [P.IsReduced] in
/-- The value of a coroot on a colour part. -/
private theorem coroot'_colorPart_eq (c : b.support → Bool) (y : b.support → ℝ) (z : Bool)
    (i : ι) :
    P.coroot' i (colorPart P b c y z) =
      algebraMap ℝ K (∑ k : b.support, (if c k = z then y k else 0) * P.pairingIn ℤ k i) := by
  rw [colorPart, coroot'_sum_algebraMap_smul_root]

omit [CharZero K] [Finite ι] [P.IsReduced] in
/-- The value of a simple coroot on the sum of the two colour parts of a left eigenvector of the
Cartan matrix. -/
theorem coroot'_colorPart_add
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j) (j : b.support) :
    P.coroot' j (colorPart P b c y true + colorPart P b c y false) =
      algebraMap ℝ K (κ * y j) := by
  rw [colorPart_add, coroot'_sum_algebraMap_smul_root, hy]

omit [P.IsReduced] in
/-- The value of a simple coroot of colour `x` on the colour part of colour `z`. -/
private theorem coroot'_colorPart
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j) {x : Bool}
    {j : b.support} (hj : c j = x) (z : Bool) :
    P.coroot' j (colorPart P b c y z) = algebraMap ℝ K ((if z = x then 2 else κ - 2) * y j) := by
  classical
  rw [colorPart, coroot'_sum_algebraMap_smul_root]
  congr 1
  -- On its own colour class the sum sees only the diagonal entry `2`.
  have hsame (z : Bool) (hz : c j = z) :
      ∑ i : b.support, (if c i = z then y i else 0) * P.pairingIn ℤ i j = 2 * y j := by
    rw [sum_eq_single j (fun i _ hij ↦ ?_) (by simp), ite_eq_left hz, P.pairingIn_same]
    · push_cast
      ring
    · split_ifs with hi
      · rw [pairingIn_eq_zero_of_color_eq P b c hij (hi.trans hz.symm)]
        simp
      · simp
  split_ifs with hzx
  · exact hsame z (hj.trans hzx.symm)
  · have htotal : ∑ i : b.support, (if c i = z then y i else 0) * P.pairingIn ℤ i j +
        ∑ i : b.support, (if c i = !z then y i else 0) * P.pairingIn ℤ i j = κ * y j := by
      rw [← hy j, ← sum_add_distrib]
      refine sum_congr rfl fun i _ ↦ ?_
      cases c i <;> cases z <;> simp
    rw [hsame (!z) (by cases z <;> cases x <;> simp_all)] at htotal
    linarith

/-- The product of the simple reflections of colour `x` negates the colour part of colour `x`,
and adds `2 - κ` times it to the colour part of the other colour. -/
theorem colorClassProd_smul_colorPart
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j) (x z : Bool) :
    (weylCoxeterSystem P b).colorClassProd c x • colorPart P b c y z =
      colorPart P b c y z - algebraMap ℝ K (if z = x then 2 else κ - 2) • colorPart P b c y x := by
  rw [colorClassProd_smul]
  congr 1
  conv_rhs => rw [colorPart, smul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [smul_smul]
  by_cases hj : c j = x
  · simp only [hj, ↓reduceIte, coroot'_colorPart P hy hj, map_mul]
  · simp only [hj, ↓reduceIte, map_zero, mul_zero]

/-- The bipartite Coxeter element maps the colour part `u₀` of colour `true` to
`(λ ^ 2 - 1) u₀ + λ u₁`, where `λ = 2 - κ` and `u₁` is the colour part of colour `false`. -/
private theorem bipartiteCoxeterElement_smul_colorPart_true
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j) :
    (weylCoxeterSystem P b).bipartiteCoxeterElement c • colorPart P b c y true =
      (algebraMap ℝ K (2 - κ) ^ 2 - 1) • colorPart P b c y true +
        algebraMap ℝ K (2 - κ) • colorPart P b c y false := by
  rw [CoxeterSystem.bipartiteCoxeterElement_def, mul_smul,
    P.colorClassProd_smul_colorPart hy false true, smul_sub, smul_comm,
    P.colorClassProd_smul_colorPart hy true true, P.colorClassProd_smul_colorPart hy true false]
  simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte, map_sub, map_ofNat]
  module

/-- The bipartite Coxeter element maps the colour part `u₁` of colour `false` to `-u₁ - λ u₀`,
where `λ = 2 - κ` and `u₀` is the colour part of colour `true`. -/
private theorem bipartiteCoxeterElement_smul_colorPart_false
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j) :
    (weylCoxeterSystem P b).bipartiteCoxeterElement c • colorPart P b c y false =
      -colorPart P b c y false - algebraMap ℝ K (2 - κ) • colorPart P b c y true := by
  rw [CoxeterSystem.bipartiteCoxeterElement_def, mul_smul,
    P.colorClassProd_smul_colorPart hy false false, smul_sub, smul_comm,
    P.colorClassProd_smul_colorPart hy true false]
  simp only [Bool.false_eq_true, ↓reduceIte, map_sub, map_ofNat]
  module

/-- For a root `μ` of `X ^ 2 + (2 - λ ^ 2) X + 1`, the bipartite Coxeter element scales the
colour-part combination `(1 + μ) u₀ + λ u₁` by `μ` (making it an eigenvector when nonzero). -/
theorem bipartiteCoxeterElement_smul_one_add_smul_colorPart_add_smul
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j) {μ : K}
    (hμ : μ ^ 2 + (2 - algebraMap ℝ K (2 - κ) ^ 2) * μ + 1 = 0) :
    (weylCoxeterSystem P b).bipartiteCoxeterElement c •
        ((1 + μ) • colorPart P b c y true + algebraMap ℝ K (2 - κ) • colorPart P b c y false) =
      μ • ((1 + μ) • colorPart P b c y true +
        algebraMap ℝ K (2 - κ) • colorPart P b c y false) := by
  rw [smul_add, smul_comm _ (1 + μ), smul_comm _ (algebraMap ℝ K (2 - κ)),
    bipartiteCoxeterElement_smul_colorPart_true P hy,
    bipartiteCoxeterElement_smul_colorPart_false P hy]
  linear_combination (norm := module) (-1 : K) • hμ • colorPart P b c y true

omit [P.IsCrystallographic] [Finite ι] [P.IsReduced] in
/-- For `0 < κ < 2`, the polynomial `X ^ 2 + (2 - (2 - κ) ^ 2) X + 1` has no real root, its
discriminant being negative. -/
private theorem ne_algebraMap_of_quadratic (hκ : 0 < κ) (hκ2 : κ < 2) {μ : K}
    (hμ : μ ^ 2 + (2 - algebraMap ℝ K (2 - κ) ^ 2) * μ + 1 = 0) (r : ℝ) :
    μ ≠ algebraMap ℝ K r := by
  rintro rfl
  have h : r ^ 2 + (2 - (2 - κ) ^ 2) * r + 1 = 0 :=
    (algebraMap ℝ K).injective (by simpa [map_ofNat] using hμ)
  nlinarith [sq_nonneg (2 * r + 2 - (2 - κ) ^ 2),
    mul_pos (mul_pos (pow_pos (sub_pos.2 hκ2) 2) hκ) (by linarith : (0 : ℝ) < 4 - κ)]

omit [P.IsCrystallographic] [Finite ι] [P.IsReduced] in
/-- The value `(1 + μ) p + λ q` of a coroot on the combination `(1 + μ) u₀ + λ u₁`, where `p` and
`q` are the real values on `u₀` and `u₁`, is nonzero as soon as `p + q` is: otherwise `μ` would
be real. -/
private theorem one_add_mul_add_mul_ne_zero (hκ : 0 < κ) (hκ2 : κ < 2) {μ : K}
    (hμ : μ ^ 2 + (2 - algebraMap ℝ K (2 - κ) ^ 2) * μ + 1 = 0) {p q : ℝ} (hpq : p + q ≠ 0) :
    (1 + μ) * algebraMap ℝ K p + algebraMap ℝ K (2 - κ) * algebraMap ℝ K q ≠ 0 := by
  intro h
  by_cases hp : p = 0
  · subst hp
    rw [map_zero, mul_zero, zero_add, ← map_mul, map_eq_zero] at h
    rcases mul_eq_zero.1 h with h' | h'
    · linarith
    · exact hpq (by simp [h'])
  · refine ne_algebraMap_of_quadratic hκ hκ2 hμ (-(p + (2 - κ) * q) / p) ?_
    rw [map_div₀, map_neg, map_add, map_mul, eq_div_iff ((map_ne_zero _).2 hp)]
    linear_combination h

omit [CharZero K] [Finite ι] [P.IsReduced] in
/-- The sum `u₀ + u₁ = ∑ yᵢ αᵢ` of the two colour parts of a positive left eigenvector of the
Cartan matrix, for a positive eigenvalue, takes a positive real value on every simple coroot. -/
private theorem exists_pos_coroot'_colorPart_add
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j)
    (hy0 : ∀ i, 0 < y i) (hκ : 0 < κ) :
    ∀ j ∈ b.support, ∃ t : ℝ, 0 < t ∧
      P.coroot' j (colorPart P b c y true + colorPart P b c y false) = algebraMap ℝ K t :=
  fun j hj ↦ ⟨κ * y ⟨j, hj⟩, mul_pos hκ (hy0 _), P.coroot'_colorPart_add hy ⟨j, hj⟩⟩

/-- For `0 < κ < 2` and a root `ν` of `X ^ 2 + (2 - λ ^ 2) X + 1`, where `λ = 2 - κ`, the weight
`(1 + ν) u₀ + λ u₁` is regular (every coroot is nonzero on it). -/
theorem isRegularWeight_one_add_smul_colorPart_add_smul
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j)
    (hy0 : ∀ i, 0 < y i) (hκ : 0 < κ) (hκ2 : κ < 2) {ν : K}
    (hν : ν ^ 2 + (2 - algebraMap ℝ K (2 - κ) ^ 2) * ν + 1 = 0) :
    P.IsRegularWeight
      ((1 + ν) • colorPart P b c y true + algebraMap ℝ K (2 - κ) • colorPart P b c y false) := by
  refine (P.isRegularWeight_iff _).2 fun i ↦ ?_
  -- The values `p` and `q` of the coroot on `u₀` and `u₁` are real, and `p + q ≠ 0`.
  obtain ⟨t, ht, hxt⟩ :=
    exists_ne_zero_coroot'_eq P b (algebraMap ℝ K) (exists_pos_coroot'_colorPart_add P hy hy0 hκ) i
  rw [map_add, coroot'_colorPart_eq, coroot'_colorPart_eq, ← map_add] at hxt
  have hpq := (algebraMap ℝ K).injective hxt
  rw [map_add, map_smul, map_smul, coroot'_colorPart_eq, coroot'_colorPart_eq, smul_eq_mul,
    smul_eq_mul]
  exact one_add_mul_add_mul_ne_zero hκ hκ2 hν (by rw [hpq]; exact ht)

omit [P.IsCrystallographic] [Finite ι] [P.IsReduced] in
/-- For `0 < κ < 2`, the two roots `μ` and `μ⁻¹` of `X ^ 2 + (2 - (2 - κ) ^ 2) X + 1` are
distinct, since its only candidates for a double root, `±1`, are real. -/
private theorem ne_inv_of_quadratic (hκ : 0 < κ) (hκ2 : κ < 2) {μ : K}
    (hμ : μ ^ 2 + (2 - algebraMap ℝ K (2 - κ) ^ 2) * μ + 1 = 0) : μ ≠ μ⁻¹ := by
  intro h
  have h1 : (μ - 1) * (μ + 1) = 0 := by
    have := mul_inv_cancel₀ fun h0 : μ = 0 ↦ by simp [h0] at hμ
    rw [← h] at this
    linear_combination this
  rcases mul_eq_zero.1 h1 with h1 | h1
  · exact ne_algebraMap_of_quadratic hκ hκ2 hμ 1 (by rw [map_one]; linear_combination h1)
  · exact ne_algebraMap_of_quadratic hκ hκ2 hμ (-1)
      (by rw [map_neg, map_one]; linear_combination h1)

/-- If `μ ^ l = 1` for the eigenvalue `μ` of the bipartite Coxeter element `c` on the Coxeter
plane, then `c ^ l = 1`: the power fixes both eigenvectors `(1 + μ) u₀ + λ u₁` and
`(1 + μ⁻¹) u₀ + λ u₁`, hence `u₀` and `u₁`, hence `u₀ + u₁`, on which the Weyl group acts freely. -/
private theorem pow_eq_one_of_pow_eq_one
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j)
    (hy0 : ∀ i, 0 < y i) (hκ : 0 < κ) (hκ2 : κ < 2) {μ : K}
    (hμ : μ ^ 2 + (2 - algebraMap ℝ K (2 - κ) ^ 2) * μ + 1 = 0) {l : ℕ} (hl : μ ^ l = 1) :
    (weylCoxeterSystem P b).bipartiteCoxeterElement c ^ l = 1 := by
  set g := (weylCoxeterSystem P b).bipartiteCoxeterElement c
  set L := algebraMap ℝ K (2 - κ)
  set u₀ := colorPart P b c y true
  set u₁ := colorPart P b c y false
  have hμ' : μ⁻¹ ^ 2 + (2 - L ^ 2) * μ⁻¹ + 1 = 0 := by
    have hμ0 : μ ≠ 0 := fun h0 ↦ by simp [h0] at hμ
    field_simp
    linear_combination hμ
  have h1 : g ^ l • ((1 + μ) • u₀ + L • u₁) = (1 + μ) • u₀ + L • u₁ := by
    rw [pow_smul_eq_of_smul_eq
      (P.bipartiteCoxeterElement_smul_one_add_smul_colorPart_add_smul hy hμ), hl, one_smul]
  have h2 : g ^ l • ((1 + μ⁻¹) • u₀ + L • u₁) = (1 + μ⁻¹) • u₀ + L • u₁ := by
    rw [pow_smul_eq_of_smul_eq
      (P.bipartiteCoxeterElement_smul_one_add_smul_colorPart_add_smul hy hμ'), inv_pow, hl,
      inv_one, one_smul]
  -- The difference of the two eigenvectors is a nonzero multiple of `u₀`.
  have hg₀ : g ^ l • u₀ = u₀ := by
    have h3 : g ^ l • ((μ - μ⁻¹) • u₀) = (μ - μ⁻¹) • u₀ := by
      have : (μ - μ⁻¹) • u₀ = ((1 + μ) • u₀ + L • u₁) - ((1 + μ⁻¹) • u₀ + L • u₁) := by module
      rw [this, smul_sub, h1, h2]
    rw [smul_comm] at h3
    exact smul_right_injective M (sub_ne_zero.2 (ne_inv_of_quadratic hκ hκ2 hμ)) h3
  have hg₁ : g ^ l • u₁ = u₁ := by
    have h4 : g ^ l • (L • u₁) = L • u₁ := by
      have : L • u₁ = ((1 + μ) • u₀ + L • u₁) - (1 + μ) • u₀ := by module
      rw [this, smul_sub, h1, smul_comm, hg₀]
    rw [smul_comm] at h4
    exact smul_right_injective M ((map_ne_zero _).2 (sub_ne_zero.2 hκ2.ne')) h4
  exact P.eq_one_of_isRegularWeight_of_smul_eq b
    (isRegularWeight_of_forall_exists_pos_coroot'_eq P b _ (algebraMap ℝ K).injective
      (exists_pos_coroot'_colorPart_add P hy hy0 hκ))
    (by rw [smul_add, hg₀, hg₁])

/-- For `0 < κ < 2` and a root `μ` of `X ^ 2 + (2 - (2 - κ) ^ 2) X + 1`, the eigenvalue `μ` is a
primitive root of unity of order equal to the order of the bipartite Coxeter element. -/
theorem isPrimitiveRoot_bipartiteCoxeterElement_of_quadratic [Nonempty ι]
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j)
    (hy0 : ∀ i, 0 < y i) (hκ : 0 < κ) (hκ2 : κ < 2) {μ : K}
    (hμ : μ ^ 2 + (2 - algebraMap ℝ K (2 - κ) ^ 2) * μ + 1 = 0) :
    IsPrimitiveRoot μ (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c)) :=
  isPrimitiveRoot_orderOf_of_smul_eq
    (P.isRegularWeight_one_add_smul_colorPart_add_smul hy hy0 hκ hκ2 hμ).ne_zero
    (P.bipartiteCoxeterElement_smul_one_add_smul_colorPart_add_smul hy hμ)
    fun _ hl ↦ pow_eq_one_of_pow_eq_one P hy hy0 hκ hκ2 hμ hl

end Plane

omit [P.IsCrystallographic] [Finite ι] [P.IsReduced] in
/-- Over an algebraically closed field of characteristic zero, `X ^ 2 + (2 - L ^ 2) X + 1` has a
root. -/
private theorem exists_quadratic_root [IsAlgClosed K] (L : K) :
    ∃ μ : K, μ ^ 2 + (2 - L ^ 2) * μ + 1 = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (discrim (1 : K) (2 - L ^ 2) 1)
  obtain ⟨μ, hμ⟩ := exists_quadratic_eq_zero one_ne_zero ⟨s, hs⟩
  exact ⟨μ, by linear_combination hμ⟩

variable [Algebra ℝ K]

omit [Finite ι] [P.IsReduced] [Algebra ℝ K] in
/-- When `b.support` is subsingleton, the constant vector `1` satisfies the rank-1 left
eigenvector identity `∑ i, 1 * P.pairingIn ℤ i j = 2 * 1`. -/
theorem sum_pairingIn_eq_two_of_subsingleton [Subsingleton b.support] (j : b.support) :
    ∑ i : b.support, (1 : ℝ) * P.pairingIn ℤ i j = 2 * 1 := by
  rw [sum_eq_single j (fun i _ hij ↦ absurd (Subsingleton.elim i j) hij) (by simp),
    P.pairingIn_same]
  push_cast
  ring

omit [CharZero K] [Finite ι] [P.IsReduced] [Algebra ℝ K] in
/-- Unfolds a left eigenvector equation `Matrix.vecMul y (b.cartanMatrix.map Int.cast) = κ • y`
into the componentwise pairing sum identity `∑ i, y i * P.pairingIn ℤ i j = κ * y j`. -/
theorem sum_mul_pairingIn_eq_of_vecMul_eq_smul {y : b.support → ℝ} {κ : ℝ}
    (hyC : Matrix.vecMul y (b.cartanMatrix.map (Int.cast : ℤ → ℝ)) = κ • y) (j : b.support) :
    ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j := by
  simpa [Matrix.vecMul, dotProduct, Base.cartanMatrixIn_def] using congrFun hyC j

/-- With a single simple root `α`, the bipartite Coxeter element is the reflection in `α`, and `α`
is a regular eigenvector for `-1`. -/
private theorem exists_isRegularWeight_smul_eq_of_subsingleton
    [Nonempty ι] [Subsingleton b.support] (c : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    ∃ (x : M) (μ : K), P.IsRegularWeight x ∧
      (weylCoxeterSystem P b).bipartiteCoxeterElement c • x = μ • x ∧
      IsPrimitiveRoot μ (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c)) := by
  have hy := P.sum_pairingIn_eq_two_of_subsingleton b
  have hx := exists_pos_coroot'_colorPart_add P (c := c) hy (fun _ ↦ one_pos) two_pos
  set x := colorPart P b c (fun _ ↦ 1) true + colorPart P b c (fun _ ↦ 1) false with hxdef
  have hgx : (weylCoxeterSystem P b).bipartiteCoxeterElement c • x = (-1 : K) • x := by
    rw [hxdef, smul_add, bipartiteCoxeterElement_smul_colorPart_true P hy,
      bipartiteCoxeterElement_smul_colorPart_false P hy]
    simp only [sub_self, map_zero]
    module
  have hreg : P.IsRegularWeight x :=
    isRegularWeight_of_forall_exists_pos_coroot'_eq P b _ (algebraMap ℝ K).injective hx
  exact ⟨x, -1, hreg, hgx, isPrimitiveRoot_orderOf_of_smul_eq hreg.ne_zero hgx fun l hl ↦
    P.eq_one_of_isRegularWeight_of_smul_eq b hreg
      (by rw [pow_smul_eq_of_smul_eq hgx, hl, one_smul])⟩

/-- **Steinberg's regular eigenvector of the bipartite Coxeter element.** Let `b` be a base of a
finite irreducible reduced crystallographic root system over a field `K` which contains `ℝ` and is
algebraically closed, such as `ℂ`. For every colouring of its Dynkin diagram by `Bool`, the
bipartite Coxeter element `c` has a regular eigenvector, one on which no coroot vanishes, whose
eigenvalue is a primitive root of unity of order exactly the order of `c`. -/
theorem exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot
    [IsAlgClosed K] [Nonempty ι] [P.IsIrreducible]
    (c : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    ∃ (x : M) (μ : K), P.IsRegularWeight x ∧
      (weylCoxeterSystem P b).bipartiteCoxeterElement c • x = μ • x ∧
      IsPrimitiveRoot μ (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c)) := by
  rcases subsingleton_or_nontrivial b.support with hs | hs
  · exact exists_isRegularWeight_smul_eq_of_subsingleton P b c
  -- At least two simple roots: the Perron eigenvector of the Cartan matrix spans the plane.
  obtain ⟨κ, hκ, hκ2, y, hy0, hyC⟩ :=
    (isFiniteType_cartanMatrix b).exists_pos_vecMul_eq_smul b.cartanMatrix_isIndecomposable
  have hy := P.sum_mul_pairingIn_eq_of_vecMul_eq_smul b hyC
  obtain ⟨μ, hμ⟩ := exists_quadratic_root (algebraMap ℝ K (2 - κ))
  exact ⟨_, μ, P.isRegularWeight_one_add_smul_colorPart_add_smul hy hy0 hκ hκ2 hμ,
    P.bipartiteCoxeterElement_smul_one_add_smul_colorPart_add_smul hy hμ,
    P.isPrimitiveRoot_bipartiteCoxeterElement_of_quadratic hy hy0 hκ hκ2 hμ⟩

end RootPairing
