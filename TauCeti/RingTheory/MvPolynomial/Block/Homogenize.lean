/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Algebra.MvPolynomial.Monomial
public import TauCeti.Data.Finsupp.Weight

/-!
# Block homogenization of multivariate polynomials

Let the affine variables `Y_j`, `j : S`, be distributed into finitely many blocks by a map
`b : S → B`, and fix a degree `d h` for every block `h : B`. For an exponent `e : S →₀ ℕ`
write `t_h(e) = ∑_{b j = h} e_j` (that is, `e.mapDomain b h`) for its degree in block `h`.
Adjoining one homogenizing variable `X_h` to every block, the block homogenization of a monomial
`c Y^e` with `t_h(e) ≤ d h` for all `h` is `c X^(d - t(e)) Y^e`, a polynomial in the variables
`B ⊕ S` that is homogeneous of degree `d h` in block `h` (whose variables are `X_h` and the `Y_j`
with `b j = h`). Monomials exceeding some block bound are discarded, so
`MvPolynomial.blockHomogenize b d` is additive without any degree hypothesis.

For a polynomial `f` whose monomials all satisfy the block bounds, setting every homogenizing
variable to `1` recovers `f`, and block homogenization is a bijection on supports preserving
coefficients. Conversely, a polynomial homogeneous of degree `d h` in every block is the block
homogenization of its dehomogenization. With one block and one affine variable this is
Mathlib's `Polynomial.homogenize`.

Block homogenization turns the affine auxiliary polynomials of the subspace theorem into the
multihomogeneous polynomials to which the product theorem and the index estimates apply.

## Main definitions

* `MvPolynomial.blockHomogenizeExponent b d e`: the exponent `(d - t(e)) ⊕ e` on `B ⊕ S`.
* `MvPolynomial.blockHomogenize b d f`: the block homogenization of `f`.

## Main results

* `MvPolynomial.coeff_sumElim_blockHomogenize`: the coefficient of `X^a Y^e` in the block
  homogenization is the coefficient of `Y^e` in `f` if `a h + t_h(e) = d h` for all `h`, and
  zero otherwise.
* `MvPolynomial.support_blockHomogenize`: for `f` satisfying the block bounds,
  `blockHomogenizeExponent b d` maps the support of `f` onto that of its block homogenization.
* `MvPolynomial.eval₂_blockHomogenize_of_eq_one`, `MvPolynomial.aeval_blockHomogenize_one_X`:
  dehomogenizing recovers `f`.
* `MvPolynomial.isWeightedHomogeneous_blockHomogenize`: the block homogenization is homogeneous of
  degree `d h` in block `h`.
* `MvPolynomial.blockHomogenize_aeval_one_X`: a polynomial homogeneous of degree `d h` in every
  block is the block homogenization of its dehomogenization.
* `MvPolynomial.rename_blockHomogenize_unique`: comparison with `Polynomial.homogenize`.

## References

* J.-H. Evertse, *An explicit version of Faltings' Product Theorem and an improvement of Roth's
  lemma*, Acta Arith. 73 (1995), §1.
-/

public section

namespace MvPolynomial

open Finsupp

variable {R B S : Type*} [CommSemiring R] [Fintype B] (b : S → B) (d : B → ℕ)

/-- The exponent of the block homogenization of the monomial `Y^e`: the homogenizing variable of
block `h` gets exponent `d h - t_h(e)`, where `t_h(e) = e.mapDomain b h` is the degree of `e` in
block `h`, and the affine variables keep the exponents `e`. -/
noncomputable def blockHomogenizeExponent (e : S →₀ ℕ) : B ⊕ S →₀ ℕ :=
  (equivFunOnFinite.symm fun h ↦ d h - e.mapDomain b h).sumElim e

@[simp]
theorem blockHomogenizeExponent_inl (e : S →₀ ℕ) (h : B) :
    blockHomogenizeExponent b d e (.inl h) = d h - e.mapDomain b h := by
  simp [blockHomogenizeExponent]

@[simp]
theorem blockHomogenizeExponent_inr (e : S →₀ ℕ) (j : S) :
    blockHomogenizeExponent b d e (.inr j) = e j := by
  simp [blockHomogenizeExponent]

/-- An exponent is recovered from the exponent of its block homogenization. -/
theorem blockHomogenizeExponent_injective :
    Function.Injective (blockHomogenizeExponent b d) := fun e e' he ↦ by
  ext j
  simpa using DFunLike.congr_fun he (.inr j)

/-- The exponent of the block homogenization of `Y^e` is `X^a Y^e` exactly when `a` is the
complementary degree `d h - t_h(e)` in every block `h`. -/
theorem blockHomogenizeExponent_eq_sumElim_iff {e : S →₀ ℕ} {a : B →₀ ℕ} :
    blockHomogenizeExponent b d e = a.sumElim e ↔ ∀ h, d h - e.mapDomain b h = a h := by
  refine ⟨fun he h ↦ by simpa using DFunLike.congr_fun he (.inl h), fun he ↦ ?_⟩
  ext (h | j) <;> simp [he]

/-- The block homogenization of `f` with respect to the block map `b : S → B` and the block
degrees `d`: every monomial `c Y^e` of `f` with `t_h(e) ≤ d h` for all blocks `h` is replaced by
`c X^(d - t(e)) Y^e`, and the other monomials are discarded. Here `t_h(e) = e.mapDomain b h` is the
degree of `e` in block `h`, and the variable `.inl h` is the homogenizing variable of block `h`. -/
noncomputable def blockHomogenize (f : MvPolynomial S R) : MvPolynomial (B ⊕ S) R :=
  f.coeff.sum fun e c ↦
    if ∀ h, e.mapDomain b h ≤ d h then monomial (blockHomogenizeExponent b d e) c else 0

/-- The coefficient of `X^a Y^e` in the block homogenization of `f` is the coefficient of `Y^e`
in `f` when `a h + t_h(e) = d h` for every block `h`, and zero otherwise. -/
theorem coeff_sumElim_blockHomogenize (f : MvPolynomial S R) (a : B →₀ ℕ) (e : S →₀ ℕ) :
    (blockHomogenize b d f).coeff (a.sumElim e) =
      if ∀ h, a h + e.mapDomain b h = d h then f.coeff e else 0 := by
  classical
  have hne {e' : S →₀ ℕ} (he' : e' ≠ e) : blockHomogenizeExponent b d e' ≠ a.sumElim e :=
    fun h ↦ he' <| by ext j; simpa using DFunLike.congr_fun h (.inr j)
  rw [blockHomogenize, sum_def, coeff_sum, Finset.sum_eq_single e]
  · by_cases H : ∀ h, a h + e.mapDomain b h = d h
    · have hle : ∀ h, e.mapDomain b h ≤ d h := fun h ↦ H h ▸ le_add_self
      have hA : blockHomogenizeExponent b d e = a.sumElim e :=
        (blockHomogenizeExponent_eq_sumElim_iff b d).2 fun h ↦ by have := H h; omega
      simp [hle, hA, H]
    · rw [ite_eq_right H]
      split_ifs with hle
      · rw [coeff_monomial, ite_eq_right]
        intro hA
        refine H fun h ↦ ?_
        have := (blockHomogenizeExponent_eq_sumElim_iff b d).1 hA h
        have := hle h
        omega
      · simp
  · intro e' _ he'
    split_ifs
    · rw [coeff_monomial, ite_eq_right (hne he')]
    · simp
  · intro he
    rw [notMem_support_iff.mp he]
    split_ifs <;> simp

/-- At a monomial within the block bounds, block homogenization preserves the coefficient. -/
theorem coeff_blockHomogenizeExponent_blockHomogenize (f : MvPolynomial S R) {e : S →₀ ℕ}
    (he : ∀ h, e.mapDomain b h ≤ d h) :
    (blockHomogenize b d f).coeff (blockHomogenizeExponent b d e) = f.coeff e := by
  rw [blockHomogenizeExponent, coeff_sumElim_blockHomogenize, ite_eq_left]
  intro h
  have := he h
  simp only [coe_equivFunOnFinite_symm]
  omega

@[simp]
theorem blockHomogenize_zero : blockHomogenize b d (0 : MvPolynomial S R) = 0 := by
  simp [blockHomogenize]

@[simp]
theorem blockHomogenize_add (f g : MvPolynomial S R) :
    blockHomogenize b d (f + g) = blockHomogenize b d f + blockHomogenize b d g := by
  ext u
  obtain ⟨a, e, rfl⟩ : ∃ a e, u = Finsupp.sumElim a e :=
    ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sumElim_blockHomogenize]
  split_ifs <;> simp

@[simp]
theorem blockHomogenize_smul {T : Type*} [SMulZeroClass T R] (c : T) (f : MvPolynomial S R) :
    blockHomogenize b d (c • f) = c • blockHomogenize b d f := by
  ext u
  obtain ⟨a, e, rfl⟩ : ∃ a e, u = Finsupp.sumElim a e :=
    ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
  simp only [coeff_smul, coeff_sumElim_blockHomogenize]
  split_ifs <;> simp

theorem blockHomogenize_finsetSum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial S R) :
    blockHomogenize b d (∑ i ∈ s, f i) = ∑ i ∈ s, blockHomogenize b d (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => simp [Finset.sum_cons, ih]

theorem blockHomogenize_map {T : Type*} [CommSemiring T] (φ : R →+* T) (f : MvPolynomial S R) :
    blockHomogenize b d (map φ f) = map φ (blockHomogenize b d f) := by
  ext u
  obtain ⟨a, e, rfl⟩ : ∃ a e, u = Finsupp.sumElim a e :=
    ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
  simp only [coeff_map, coeff_sumElim_blockHomogenize]
  split_ifs <;> simp

@[simp]
theorem blockHomogenize_monomial (e : S →₀ ℕ) (c : R) :
    blockHomogenize b d (monomial e c) =
      if ∀ h, e.mapDomain b h ≤ d h then monomial (blockHomogenizeExponent b d e) c else 0 :=
  sum_monomial_eq (by simp)

@[simp]
theorem blockHomogenize_C (c : R) :
    blockHomogenize b d (C c : MvPolynomial S R) = C c * ∏ h, X (.inl h) ^ d h := by
  rw [C_apply, blockHomogenize_monomial, ite_eq_left (by simp), monomial_eq,
    blockHomogenizeExponent, prod_sumElim]
  simp [Finsupp.prod_fintype]

@[simp]
theorem blockHomogenize_one :
    blockHomogenize b d (1 : MvPolynomial S R) = ∏ h, X (.inl h) ^ d h := by
  simpa using blockHomogenize_C b d (1 : R)

/-- With all block degrees zero, block homogenization keeps only the constant term. -/
@[simp]
theorem blockHomogenize_degree_zero (f : MvPolynomial S R) :
    blockHomogenize b 0 f = C (f.coeff 0) := by
  classical
  ext u
  obtain ⟨a, e, rfl⟩ : ∃ a e, u = Finsupp.sumElim a e :=
    ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
  rw [coeff_sumElim_blockHomogenize, coeff_C]
  have h₀ : 0 = a.sumElim e ↔ a = 0 ∧ e = 0 := by
    refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨ha, he⟩ ↦ by simp [ha, he]⟩
    · simpa using congrArg (comapDomain Sum.inl · Sum.inl_injective.injOn) h.symm
    · simpa using congrArg (comapDomain Sum.inr · Sum.inr_injective.injOn) h.symm
  have h₁ : (∀ h, a h + e.mapDomain b h = (0 : B → ℕ) h) ↔ a = 0 ∧ e = 0 := by
    refine ⟨fun H ↦ ⟨?_, ?_⟩, fun ⟨ha, he⟩ h ↦ by simp [ha, he]⟩
    · ext h
      exact (Nat.add_eq_zero_iff.1 (H h)).1
    · have hmap : e.mapDomain b = 0 := by
        ext h
        exact (Nat.add_eq_zero_iff.1 (H h)).2
      rw [← degree_eq_zero_iff, ← degree_mapDomain b, hmap]
      simp
  by_cases H : a = 0 ∧ e = 0
  · rw [ite_eq_left (h₁.2 H), ite_eq_left (h₀.2 H), H.2]
  · rw [ite_eq_right (mt h₁.1 H), ite_eq_right (mt h₀.1 H)]

/-- If `f` satisfies the block bounds, then evaluating its block homogenization with every
homogenizing variable set to `1` gives the value of `f`. -/
theorem eval₂_blockHomogenize_of_eq_one {T : Type*} [CommSemiring T] (φ : R →+* T)
    (x : B ⊕ S → T) (hx : ∀ h, x (.inl h) = 1) {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    eval₂ φ x (blockHomogenize b d f) = eval₂ φ (x ∘ Sum.inr) f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [blockHomogenize_finsetSum, eval₂_sum, eval₂_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [blockHomogenize_monomial, ite_eq_left (hf e he), blockHomogenizeExponent,
    eval₂_monomial_sumElim_of_eq_one φ x hx]

/-- If `f` satisfies the block bounds, then setting every homogenizing variable of its block
homogenization to `1` recovers `f`. -/
theorem aeval_blockHomogenize_one_X {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    aeval (Sum.elim (fun _ ↦ 1) X) (blockHomogenize b d f) = f := by
  rw [aeval_def, eval₂_blockHomogenize_of_eq_one b d _ _ (fun _ ↦ rfl) hf, Sum.elim_comp_inr,
    ← aeval_def, aeval_X_left_apply]

/-- For a polynomial within the block bounds, `blockHomogenizeExponent b d` maps its support
bijectively onto the support of its block homogenization. -/
theorem support_blockHomogenize {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    (blockHomogenize b d f).support =
      f.support.map ⟨_, blockHomogenizeExponent_injective b d⟩ := by
  ext u
  obtain ⟨a, e, rfl⟩ : ∃ a e, u = Finsupp.sumElim a e :=
    ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
  simp only [mem_support_iff, coeff_sumElim_blockHomogenize, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro hc
    split_ifs at hc with H
    · refine ⟨e, hc, (blockHomogenizeExponent_eq_sumElim_iff b d).2 fun h ↦ ?_⟩
      have := H h
      omega
    · exact (hc rfl).elim
  · rintro ⟨e', he', hA⟩
    obtain rfl : e' = e := by ext j; simpa using DFunLike.congr_fun hA (.inr j)
    rw [ite_eq_left fun h ↦ ?_]
    · exact he'
    have := (blockHomogenizeExponent_eq_sumElim_iff b d).1 hA h
    have := hf e' (mem_support_iff.mpr he') h
    omega

section Weight

variable [DecidableEq B]

/-- The block homogenization is homogeneous of degree `d h` in block `h`, whose variables are
the homogenizing variable `.inl h` and the affine variables `.inr j` with `b j = h`. -/
theorem isWeightedHomogeneous_blockHomogenize (f : MvPolynomial S R) (h : B) :
    (blockHomogenize b d f).IsWeightedHomogeneous
      (fun v ↦ if Sum.elim id b v = h then 1 else 0) (d h) := by
  intro u hu
  obtain ⟨a, e, rfl⟩ : ∃ a e, u = Finsupp.sumElim a e :=
    ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
  rw [coeff_sumElim_blockHomogenize] at hu
  split_ifs at hu with H
  · rw [weight_ite_sumElim_eq_add_mapDomain_apply, H h]
  · exact (hu rfl).elim

/-- A polynomial in the variables `B ⊕ S` that is homogeneous of degree `d h` in every block `h`
is the block homogenization of its dehomogenization, obtained by setting every homogenizing
variable to `1`. -/
theorem blockHomogenize_aeval_one_X {F : MvPolynomial (B ⊕ S) R}
    (hF : ∀ h, F.IsWeightedHomogeneous (fun v ↦ if Sum.elim id b v = h then 1 else 0) (d h)) :
    blockHomogenize b d (aeval (Sum.elim (fun _ ↦ 1) X) F) = F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, blockHomogenize_finsetSum]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  obtain ⟨a, e, rfl⟩ : ∃ a e, u = Finsupp.sumElim a e :=
    ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
  have H (h : B) : a h + e.mapDomain b h = d h := by
    rw [← weight_ite_sumElim_eq_add_mapDomain_apply]
    exact hF h (mem_support_iff.mp hu)
  rw [aeval_def, eval₂_monomial_sumElim_of_eq_one _ _ (fun _ ↦ rfl), Sum.elim_comp_inr,
    ← aeval_def, aeval_X_left_apply, blockHomogenize_monomial,
    ite_eq_left fun h ↦ H h ▸ le_add_self,
    (blockHomogenizeExponent_eq_sumElim_iff b d (a := a)).2 fun h ↦ by have := H h; omega]

end Weight

/-- With one block and one affine variable, block homogenization is `Polynomial.homogenize`:
the affine variable becomes the variable `0` and the homogenizing variable the variable `1`. -/
theorem rename_blockHomogenize_unique [Unique B] [Unique S] (p : Polynomial R) :
    rename (Sum.elim (fun _ ↦ 1) fun _ ↦ 0)
        (blockHomogenize b d ((uniqueAlgEquiv R S).symm p)) =
      p.homogenize (d default) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, blockHomogenize_add, Polynomial.homogenize_add, hp, hq]
  | monomial k c =>
    have hsymm : (uniqueAlgEquiv R S).symm (Polynomial.monomial k c) =
        monomial (single default k) c := by
      simpa using uniqueAlgEquiv_symm_monomial (σ := S) (R := R) (d := single default k) (r := c)
    have hb : b default = default := Unique.eq_default _
    have hmap (h : B) : (single (default : S) k).mapDomain b h = k := by
      rw [Unique.eq_default h]
      simp [hb]
    rw [hsymm, blockHomogenize_monomial]
    by_cases hk : k ≤ d default
    · have hA : (blockHomogenizeExponent b d (single default k)).mapDomain
          (Sum.elim (fun _ ↦ (1 : Fin 2)) fun _ ↦ 0) =
            fun₀ | 0 => k | 1 => d default - k := by
        have : blockHomogenizeExponent b d (single default k) =
            single (.inl default) (d default - k) + single (.inr default) k := by
          ext (h | j)
          · rw [blockHomogenizeExponent_inl, hmap, Unique.eq_default h]
            simp
          · rw [Unique.eq_default j]
            simp
        rw [this, mapDomain_add, mapDomain_single, mapDomain_single]
        ext i
        fin_cases i <;> simp
      rw [ite_eq_left fun h ↦ (hmap h).trans_le (Unique.eq_default h ▸ hk), rename_monomial, hA,
        Polynomial.homogenize_monomial hk]
    · rw [ite_eq_right fun H ↦ hk ((hmap default).symm.trans_le (H default)), map_zero,
        Polynomial.homogenize_monomial_of_lt (not_le.mp hk)]

/-- In one block of degree `1`, the product of two affine variables exceeds the block bound and is
discarded, although each exponent is at most `1`. -/
example : blockHomogenize (fun _ : Fin 2 ↦ ()) (fun _ ↦ 1) (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) =
    0 := by
  rw [X, X, monomial_mul_monomial, blockHomogenize_monomial, ite_eq_right]
  intro h
  simpa [mapDomain_add] using h ()

/-- In two blocks of degree `1`, the product of one affine variable from each block is already
block homogeneous. -/
example : blockHomogenize id (fun _ ↦ 1) (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) =
    X (.inr 0) * X (.inr 1) := by
  have hA : blockHomogenizeExponent id (fun _ : Fin 2 ↦ 1) (single 0 1 + single 1 1) =
      single (.inr 0) 1 + single (.inr 1) 1 := by
    ext (h | j)
    · fin_cases h <;> simp
    · fin_cases j <;> simp
  rw [X, X, monomial_mul_monomial, blockHomogenize_monomial,
    ite_eq_left (fun h ↦ by fin_cases h <;> simp), hA, X, X, monomial_mul_monomial]

end MvPolynomial
