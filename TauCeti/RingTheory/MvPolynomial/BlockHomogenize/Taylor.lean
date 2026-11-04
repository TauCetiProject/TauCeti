/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.Data.Finsupp.Sum
public import TauCeti.RingTheory.MvPolynomial.BlockHomogenize.Basic
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor

/-!
# Taylor expansions and Hasse jets of block homogenizations

Let `b : S → B` assign each affine variable `j : S` to one of finitely many blocks `h : B` of
prescribed degree `d h`. When `f : MvPolynomial S R` has block degrees
`t_h(e) = e.mapDomain b h ≤ d h` on its support, expanding `f` around an affine center `a : S → R`
in Hasse derivatives and homogenizing term by term yields
`H_d(f) = ∑_γ (∂^γ f)(a) (∏_h X_h^(d_h - t_h(γ))) ∏_j (Y_j - a_j X_{b(j)})^(γ_j)`.
Indeed, each summand has degree `d h` in block `h` and dehomogenizes at `X_h = 1` to the
corresponding Taylor term `(∂^γ f)(a) ∏_j (Y_j - a_j)^(γ_j)` of `f`, so uniqueness of block
homogenization (`MvPolynomial.blockHomogenize_aeval_one_X`) identifies the two polynomials
without expanding multinomial coefficients.

Translating to the chart center `(1, a)` sends `X_h` to `X_h + 1` and `Y_j` to `Y_j + a_j`, which
cancels the constants in `Y_j - a_j X_{b(j)}` identically. Extracting the coefficient of
`X^κ Y^β` then expresses every homogeneous Hasse jet `(∂^(κ ⊕ β) H_d(f))(1, a)` in terms of the
affine jets `(∂^γ f)(a)` with `β ≤ γ` and `t_h(γ - β) ≤ κ h` (in particular, only orders with
`t_h(γ) ≤ κ h + t_h(β)` can contribute; note that positive affine orders `γ > β` do contribute when
`κ ≠ 0`, correcting a misprint in Evertse's displayed formula for `κ` of degree `1`). When
`κ = 0`, only `γ = β` survives, recovering `(∂^(0 ⊕ β) H_d(f))(1, a) = (∂^β f)(a)`; in fact,
dehomogenizing `∂^(0 ⊕ β) H_d(f)` at `X_h = 1` recovers `∂^β f` over any commutative semiring.

## Main definitions

* `MvPolynomial.blockExponents b d`: for finite `S`, the finite set of multi-indices `γ : S →₀ ℕ`
  satisfying `γ.mapDomain b h ≤ d h` in every block `h`.

## Main results

* `MvPolynomial.eval_one_blockHomogenize`,
  `MvPolynomial.eval₂_hasseDeriv_zero_sumElim_blockHomogenize_of_eq_one`,
  `MvPolynomial.aeval_hasseDeriv_zero_sumElim_blockHomogenize_one_X`,
  `MvPolynomial.eval_one_hasseDeriv_zero_sumElim_blockHomogenize`: pure affine Hasse derivatives
  `∂^(0 ⊕ β)` commute with dehomogenization on `d`-bounded polynomials over any commutative
  semiring.
* `MvPolynomial.blockHomogenize_eq_sum_support_taylor`,
  `MvPolynomial.blockHomogenize_eq_sum_blockExponents`: the centered Taylor expansion of
  `blockHomogenize b d f` around `a`.
* `MvPolynomial.eval_one_hasseDeriv_sumElim_blockHomogenize`,
  `MvPolynomial.eval_one_hasseDeriv_sumElim_blockHomogenize_eq_sum_blockExponents`: the explicit
  formula for `(∂^(κ ⊕ β) H_d(f))(1, a)` in terms of affine Hasse jets at `a`.
* `MvPolynomial.eval_one_hasseDeriv_sumElim_blockHomogenize_eq_zero`: `(∂^(κ ⊕ β) H_d(f))(1, a)`
  vanishes as soon as `(∂^γ f)(a) = 0` for all `γ ≥ β` with `t_h(γ) ≤ κ h + t_h(β)`.

## References

* J.-H. Evertse, *An explicit version of Faltings' Product Theorem and an improvement of Roth's
  lemma*, Acta Arith. 73 (1995), §1, pp. 221–222.
-/

public section

namespace MvPolynomial

open Finsupp

section CommSemiring

variable {R B S : Type*} [CommSemiring R] (b : S → B) (d : B → ℕ)

/-- If every monomial of `f` has degree at most `d h` in block `h`, then every monomial `m` of
`∂^γ f` satisfies `t_h(m) + t_h(γ) ≤ d h`. -/
theorem mapDomain_add_le_of_mem_support_hasseDeriv {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) {γ m : S →₀ ℕ}
    (hm : m ∈ (hasseDeriv γ f).support) (h : B) :
    m.mapDomain b h + γ.mapDomain b h ≤ d h := by
  rw [mem_support_iff, hasseDeriv_coeff] at hm
  have hmem : m + γ ∈ f.support := mem_support_iff.2 (right_ne_zero_of_mul hm)
  simpa only [mapDomain_add, Finsupp.add_apply] using hf (m + γ) hmem h

/-- A Hasse derivative of a `d`-bounded polynomial remains `d`-bounded. -/
theorem mapDomain_le_of_mem_support_hasseDeriv {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) (γ : S →₀ ℕ)
    {m : S →₀ ℕ} (hm : m ∈ (hasseDeriv γ f).support) (h : B) :
    m.mapDomain b h ≤ d h :=
  le_self_add.trans (mapDomain_add_le_of_mem_support_hasseDeriv b d hf hm h)

/-- A nonzero Hasse derivative `∂^γ f` of a `d`-bounded polynomial has block degrees
`t_h(γ) ≤ d h`. -/
theorem mapDomain_le_of_hasseDeriv_ne_zero {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) {γ : S →₀ ℕ}
    (hγ : hasseDeriv γ f ≠ 0) (h : B) :
    γ.mapDomain b h ≤ d h := by
  obtain ⟨m, hm⟩ := support_nonempty.2 hγ
  exact le_add_self.trans (mapDomain_add_le_of_mem_support_hasseDeriv b d hf hm h)

/-- If `γ` exceeds the block degree bound `d h` in some block `h`, then `∂^γ f = 0` for every
`d`-bounded polynomial `f`. -/
theorem hasseDeriv_eq_zero_of_lt_mapDomain {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) {γ : S →₀ ℕ} {h : B}
    (hγ : d h < γ.mapDomain b h) :
    hasseDeriv γ f = 0 :=
  by_contra fun hne ↦ (mapDomain_le_of_hasseDeriv_ne_zero b d hf hne h).not_gt hγ

/-- Every exponent occurring in the Taylor shift of a `d`-bounded polynomial satisfies the same
block degree bounds `t_h(γ) ≤ d h`. -/
theorem mapDomain_le_of_mem_support_taylor (a : S → R) {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) {γ : S →₀ ℕ}
    (hγ : γ ∈ (taylor a f).support) (h : B) :
    γ.mapDomain b h ≤ d h := by
  rw [mem_support_iff, coeff_taylor] at hγ
  exact mapDomain_le_of_hasseDeriv_ne_zero b d hf (fun hz ↦ hγ (by simp [hz])) h

section BlockExponents

variable [Finite S]

open Classical in
/-- For a finite variable type `S`, the finite set of multi-indices `γ : S →₀ ℕ` whose degree
`t_h(γ) = γ.mapDomain b h` in every block `h` is at most `d h`. -/
noncomputable def blockExponents : Finset (S →₀ ℕ) :=
  {γ ∈ Finset.Iic (equivFunOnFinite.symm (d ∘ b)) | ∀ h, γ.mapDomain b h ≤ d h}

@[simp]
theorem mem_blockExponents {γ : S →₀ ℕ} :
    γ ∈ blockExponents b d ↔ ∀ h, γ.mapDomain b h ≤ d h := by
  classical
  simp only [blockExponents, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
  intro h j
  have hj : γ j ≤ γ.mapDomain b (b j) := by
    have hle : single j (γ j) ≤ γ := Finsupp.single_le_iff.2 le_rfl
    simpa using Finsupp.mapDomain_mono (f := b) hle (b j)
  simpa using hj.trans (h (b j))

theorem zero_mem_blockExponents : (0 : S →₀ ℕ) ∈ blockExponents b d := by
  simp

theorem blockExponents_nonempty : (blockExponents b d).Nonempty :=
  ⟨0, zero_mem_blockExponents b d⟩

theorem blockExponents_mono {d₁ d₂ : B → ℕ} (hd : d₁ ≤ d₂) :
    blockExponents b d₁ ⊆ blockExponents b d₂ := fun _ hγ ↦
  (mem_blockExponents b d₂).2 fun h ↦ ((mem_blockExponents b d₁).1 hγ h).trans (hd h)

/-- A polynomial in finitely many variables is `d`-bounded if and only if its support lies in
`blockExponents b d`. -/
theorem support_subset_blockExponents_iff {f : MvPolynomial S R} :
    f.support ⊆ blockExponents b d ↔ ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h := by
  simp [Finset.subset_iff]

end BlockExponents

section ZeroSumElim

variable [Fintype B]

/-- At the chart point `(1, a)`, `blockHomogenize b d f` evaluates to `f(a)` for any `d`-bounded
polynomial `f`. -/
theorem eval_one_blockHomogenize (a : S → R) {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    eval (Sum.elim (fun _ ↦ 1) a) (blockHomogenize b d f) = eval a f := by
  simpa only [eval, coe_eval₂Hom, Sum.elim_comp_inr] using
    eval₂_blockHomogenize_of_eq_one b d (RingHom.id R) (Sum.elim (fun _ ↦ 1) a) (fun _ ↦ rfl) hf

/-- Evaluating a pure affine Hasse derivative `∂^(0 ⊕ β)` of the block homogenization of a
`d`-bounded polynomial `f` at any point whose homogenizing `.inl` coordinates are `1` evaluates
`∂^β f` at the `.inr` coordinates. -/
theorem eval₂_hasseDeriv_zero_sumElim_blockHomogenize_of_eq_one {T : Type*} [CommSemiring T]
    (φ : R →+* T) (x : B ⊕ S → T) (hx : ∀ h, x (.inl h) = 1) (β : S →₀ ℕ)
    {f : MvPolynomial S R} (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    eval₂ φ x (hasseDeriv ((0 : B →₀ ℕ).sumElim β) (blockHomogenize b d f)) =
      eval₂ φ (x ∘ Sum.inr) (hasseDeriv β f) := by
  classical
  have hsub (e : S →₀ ℕ) :
      blockHomogenizeExponent b d e - (0 : B →₀ ℕ).sumElim β =
        (equivFunOnFinite.symm fun h ↦ d h - e.mapDomain b h).sumElim (e - β) := by
    ext (h | j) <;> simp
  have hprod (e : S →₀ ℕ) :
      (((0 : B →₀ ℕ).sumElim β).prod fun v k ↦ (blockHomogenizeExponent b d e v).choose k) =
        β.prod fun j k ↦ (e j).choose k := by
    rw [Finsupp.prod_sumElim]
    simp [Function.comp_def]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [blockHomogenize_finsetSum, map_sum, map_sum, eval₂_sum, eval₂_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [blockHomogenize_monomial, ite_eq_left (hf e he), hasseDeriv_monomial, hasseDeriv_monomial,
    hsub, hprod, eval₂_monomial_sumElim_of_eq_one φ x hx]

/-- Dehomogenizing `∂^(0 ⊕ β) (blockHomogenize b d f)` by setting every homogenizing variable to
`1` recovers `∂^β f` for any `d`-bounded polynomial `f`. -/
theorem aeval_hasseDeriv_zero_sumElim_blockHomogenize_one_X (β : S →₀ ℕ)
    {f : MvPolynomial S R} (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    aeval (Sum.elim (fun _ ↦ 1) X)
        (hasseDeriv ((0 : B →₀ ℕ).sumElim β) (blockHomogenize b d f)) =
      hasseDeriv β f := by
  rw [aeval_def, eval₂_hasseDeriv_zero_sumElim_blockHomogenize_of_eq_one b d _ _ (fun _ ↦ rfl) β hf,
    Sum.elim_comp_inr, ← aeval_def, aeval_X_left_apply]

/-- At the chart point `(1, a)`, the pure affine Hasse jet `∂^(0 ⊕ β)` of `blockHomogenize b d f`
equals `(∂^β f)(a)` for any `d`-bounded polynomial `f`. -/
theorem eval_one_hasseDeriv_zero_sumElim_blockHomogenize (a : S → R) (β : S →₀ ℕ)
    {f : MvPolynomial S R} (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    eval (Sum.elim (fun _ ↦ 1) a)
        (hasseDeriv ((0 : B →₀ ℕ).sumElim β) (blockHomogenize b d f)) =
      eval a (hasseDeriv β f) := by
  simpa only [eval, coe_eval₂Hom, Sum.elim_comp_inr] using
    eval₂_hasseDeriv_zero_sumElim_blockHomogenize_of_eq_one b d (RingHom.id R)
      (Sum.elim (fun _ ↦ 1) a) (fun _ ↦ rfl) β hf

end ZeroSumElim

end CommSemiring

section CommRing

variable {R B S : Type*} [CommRing R] (b : S → B) (d : B → ℕ)

/-- Every polynomial `f` equals its finite Hasse Taylor expansion around `a`:
`f = ∑_{γ ∈ supp(taylor a f)} C((∂^γ f)(a)) ∏_j (X_j - C(a_j))^(γ_j)`. -/
private theorem eq_sum_support_taylor_hasseDeriv (a : S → R) (f : MvPolynomial S R) :
    f = ∑ γ ∈ (taylor a f).support,
      C (eval a (hasseDeriv γ f)) * γ.prod fun j k ↦ (X j - C (a j)) ^ k := by
  conv_lhs => rw [← taylor_zero f, ← neg_add_cancel a, ← taylor_taylor, (taylor a f).as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [coeff_taylor, taylor_apply, aeval_monomial, algebraMap_eq]
  congr 1
  simp only [Finsupp.prod, Pi.neg_apply, map_neg, sub_eq_add_neg]

/-- **Taylor expansion of a block homogenization** around an affine center `a : S → R`
(Evertse 1995, §1, pp. 221–222): for `d`-bounded `f`,
`H_d(f) = ∑_γ C((∂^γ f)(a)) (∏_h X_h^(d_h - t_h(γ))) ∏_j (Y_j - a_j X_{b(j)})^(γ_j)`,
summed over the support of `taylor a f` (so no finiteness assumption on `S` is needed). -/
theorem blockHomogenize_eq_sum_support_taylor [Fintype B] (a : S → R) {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    blockHomogenize b d f =
      ∑ γ ∈ (taylor a f).support,
        C (eval a (hasseDeriv γ f)) *
          (∏ h, X (.inl h) ^ (d h - γ.mapDomain b h)) *
          γ.prod fun j k ↦ (X (.inr j) - C (a j) * X (.inl (b j))) ^ k := by
  classical
  set G : MvPolynomial (B ⊕ S) R :=
    ∑ γ ∈ (taylor a f).support,
      C (eval a (hasseDeriv γ f)) *
        (∏ h, X (.inl h) ^ (d h - γ.mapDomain b h)) *
        γ.prod fun j k ↦ (X (.inr j) - C (a j) * X (.inl (b j))) ^ k
  -- Every summand of `G` has weight `d h` in block `h`, and dehomogenizes at `X_h = 1` to the
  -- corresponding Taylor summand of `f`.
  have hG (h : B) : G.IsWeightedHomogeneous
      (fun v ↦ if Sum.elim id b v = h then 1 else 0) (d h) := by
    set w : B ⊕ S → ℕ := fun v ↦ if Sum.elim id b v = h then 1 else 0
    refine IsWeightedHomogeneous.sum _ _ (d h) fun γ hγ ↦ ?_
    have hγd : γ.mapDomain b h ≤ d h := mapDomain_le_of_mem_support_taylor b d a hf hγ h
    have hleft : (∏ h' : B, (X (.inl h') : MvPolynomial (B ⊕ S) R) ^ (d h' - γ.mapDomain b h'))
        |>.IsWeightedHomogeneous w (d h - γ.mapDomain b h) := by
      have hp := IsWeightedHomogeneous.prod Finset.univ
        (fun h' : B ↦ (X (.inl h') : MvPolynomial (B ⊕ S) R) ^ (d h' - γ.mapDomain b h'))
        (fun h' : B ↦ (d h' - γ.mapDomain b h') • w (.inl h'))
        fun h' _ ↦ (isWeightedHomogeneous_X R w (.inl h')).pow _
      convert hp
      rw [Fintype.sum_eq_single h fun h' hh' ↦ by simp [w, hh']]
      simp [w]
    have hright : (γ.prod fun j k ↦ (X (.inr j) - C (a j) * X (.inl (b j)) :
          MvPolynomial (B ⊕ S) R) ^ k).IsWeightedHomogeneous w (γ.mapDomain b h) := by
      rw [Finsupp.prod]
      have hp := IsWeightedHomogeneous.prod (w := w) γ.support
        (fun j ↦ (X (.inr j) - C (a j) * X (.inl (b j)) : MvPolynomial (B ⊕ S) R) ^ γ j)
        (fun j ↦ γ j • w (.inr j)) fun j _ ↦ ?_
      · convert hp
        rw [← Finsupp.weight_ite_eq_mapDomain_apply b γ h, Finsupp.weight_apply, Finsupp.sum]
        rfl
      · refine ((isWeightedHomogeneous_X R w (.inr j)).sub ?_).pow (γ j)
        have hw : w (.inl (b j)) = w (.inr j) := by
          by_cases hbj : b j = h <;> simp [w, hbj]
        exact hw ▸ (isWeightedHomogeneous_X R w (.inl (b j))).C_mul (a j)
    rw [mul_assoc, ← Nat.sub_add_cancel hγd]
    exact (hleft.mul hright).C_mul (eval a (hasseDeriv γ f))
  have haeval : aeval (Sum.elim (fun _ ↦ 1) X) G = f := by
    rw [map_sum]
    conv_rhs => rw [eq_sum_support_taylor_hasseDeriv a f]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    simp [Finsupp.prod, map_prod]
  rw [← haeval, blockHomogenize_aeval_one_X b d hG]

/-- **Taylor expansion of a block homogenization** over `blockExponents b d` for finite `S`
(Evertse 1995, §1, pp. 221–222):
`H_d(f) = ∑_{γ ∈ Γ_d} C((∂^γ f)(a)) (∏_h X_h^(d_h - t_h(γ))) ∏_j (Y_j - a_j X_{b(j)})^(γ_j)`. -/
theorem blockHomogenize_eq_sum_blockExponents [Fintype B] [Fintype S] (a : S → R)
    {f : MvPolynomial S R} (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    blockHomogenize b d f =
      ∑ γ ∈ blockExponents b d,
        C (eval a (hasseDeriv γ f)) *
          (∏ h, X (.inl h) ^ (d h - γ.mapDomain b h)) *
          ∏ j, (X (.inr j) - C (a j) * X (.inl (b j))) ^ γ j := by
  rw [blockHomogenize_eq_sum_support_taylor b d a hf]
  have hsub : (taylor a f).support ⊆ blockExponents b d := fun γ hγ ↦
    (mem_blockExponents b d).2 (mapDomain_le_of_mem_support_taylor b d a hf hγ)
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun γ _ ↦ ?_
    rw [Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
  · intro γ _ hγ
    rw [notMem_support_iff, coeff_taylor] at hγ
    simp [hγ]

open Classical in
/-- Multiplying a polynomial in the `.inl` variables by a monomial `c X^u Y^β'` contributes to
`[X^κ Y^β]` only when `β' = β` and `u ≤ κ`, where it selects the coefficient `[X^(κ - u)]`. -/
private theorem coeff_rename_inl_mul_monomial_sumElim (P : MvPolynomial B R) (u κ : B →₀ ℕ)
    (β' β : S →₀ ℕ) (c : R) :
    (rename Sum.inl P * monomial (u.sumElim β') c).coeff (κ.sumElim β) =
      if β' = β ∧ u ≤ κ then P.coeff (κ - u) * c else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial μ r =>
    have hmap : μ.mapDomain (Sum.inl : B → B ⊕ S) = μ.sumElim (0 : S →₀ ℕ) := by
      simp [sumElim_eq_add]
    have hsum : (μ.sumElim (0 : S →₀ ℕ)) + u.sumElim β' = (μ + u).sumElim β' := by
      ext (h | j) <;> simp
    rw [rename_monomial, hmap, monomial_mul_monomial, hsum, coeff_monomial, coeff_monomial]
    simp only [sumElim_inj]
    by_cases hβ : β' = β
    · subst hβ
      by_cases hu : u ≤ κ
      · by_cases hμ : μ + u = κ
        · subst hμ
          simp
        · have hμ' : μ ≠ κ - u := fun h ↦ hμ (h ▸ tsub_add_cancel_of_le hu)
          simp [hu, hμ, hμ']
      · have hμ : μ + u ≠ κ := fun h ↦ hu (h ▸ le_add_left le_rfl)
        simp [hu, hμ]
    · simp [hβ]
  | add p q hp hq =>
    simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> ring

/-- The coefficient of `X^μ` in `∏_h (X_h + 1)^(m_h)` is `∏_h (m_h choose μ_h)`. -/
private theorem coeff_prod_X_add_one_pow [Fintype B] (m : B → ℕ) (μ : B →₀ ℕ) :
    (∏ h : B, (X h + 1 : MvPolynomial B R) ^ m h).coeff μ =
      ∏ h : B, ((m h).choose (μ h) : R) := by
  have heq : (∏ h : B, (X h + 1 : MvPolynomial B R) ^ m h) =
      taylor (fun _ ↦ 1) (monomial (equivFunOnFinite.symm m) (1 : R)) := by
    rw [taylor_apply, aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
    simp
  rw [heq, coeff_taylor, eval_const_hasseDeriv_monomial]
  simp

open Classical in
/-- Binomial expansion of `∏_{j ∈ supp(γ)} (Y_j - a_j X_{b(j)})^(γ_j)` over the sub-exponents
`β ≤ γ`: each `β` contributes the monomial `X^(t(γ - β)) Y^β`. -/
private theorem finsuppProd_X_inr_sub_C_mul_X_inl_pow (a : S → R) (γ : S →₀ ℕ) :
    (γ.prod fun j k ↦ (X (.inr j) - C (a j) * X (.inl (b j)) : MvPolynomial (B ⊕ S) R) ^ k) =
      ∑ β ∈ Finset.Iic γ,
        monomial (((γ - β).mapDomain b).sumElim β)
          (γ.prod fun j k ↦ (k.choose (β j) : R) * (-a j) ^ (k - β j)) := by
  classical
  induction γ using Finsupp.induction with
  | zero =>
    have h0 : Finset.Iic (0 : S →₀ ℕ) = {0} := by
      ext x
      simp
    simp [h0]
  | single_add j k s hj hk ih =>
    have hsupp : (single j k + s).support = insert j s.support := by
      ext i
      rcases eq_or_ne i j with rfl | hij
      · simp [Finsupp.mem_support_iff, Finsupp.notMem_support_iff.1 hj, hk]
      · simp [Finsupp.mem_support_iff, hij]
    have hprod_lhs :
        ((single j k + s).prod fun i n ↦
          (X (.inr i) - C (a i) * X (.inl (b i)) : MvPolynomial (B ⊕ S) R) ^ n) =
        (X (.inr j) - C (a j) * X (.inl (b j))) ^ k *
          s.prod fun i n ↦ (X (.inr i) - C (a i) * X (.inl (b i))) ^ n := by
      rw [Finsupp.prod, Finsupp.prod, hsupp, Finset.prod_insert hj]
      congr 1
      · simp [Finsupp.notMem_support_iff.1 hj]
      · refine Finset.prod_congr rfl fun i hi ↦ ?_
        have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
        simp [hij.symm]
    have hfactor :
        (X (.inr j) - C (a j) * X (.inl (b j)) : MvPolynomial (B ⊕ S) R) ^ k =
          ∑ m ∈ Finset.range (k + 1),
            monomial ((single (b j) (k - m)).sumElim (single j m))
              ((k.choose m : R) * (-a j) ^ (k - m)) := by
      have hterm : (X (.inr j) - C (a j) * X (.inl (b j)) : MvPolynomial (B ⊕ S) R) =
          monomial ((0 : B →₀ ℕ).sumElim (single j 1)) 1 +
            monomial ((single (b j) 1).sumElim (0 : S →₀ ℕ)) (-a j) := by
        rw [X, X, C_mul_monomial, mul_one, sub_eq_add_neg, ← map_neg (monomial _)]
        congr 1 <;> refine congrArg (monomial · _) ?_ <;>
          (ext (h | i) <;> simp [Finsupp.single_apply])
      rw [hterm, add_pow]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [monomial_pow, monomial_pow, one_pow, monomial_mul_monomial, one_mul, ← C_eq_natCast,
        mul_comm _ (C _), C_mul_monomial]
      refine congrArg (monomial · _) ?_
      ext (h | i) <;> simp [Finsupp.single_apply]
    rw [hprod_lhs, hfactor, ih, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_bij (fun p : ℕ × (S →₀ ℕ) ↦ fun _ ↦ single j p.1 + p.2) ?_ ?_ ?_ ?_
    · rintro ⟨m, β'⟩ hp
      rw [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff, Finset.mem_Iic] at hp
      exact Finset.mem_Iic.2 (add_le_add (single_le_single.2 hp.1) hp.2)
    · rintro ⟨m₁, β₁⟩ hp₁ ⟨m₂, β₂⟩ hp₂ heq
      rw [Finset.mem_product, Finset.mem_Iic] at hp₁ hp₂
      have hsj : s j = 0 := Finsupp.notMem_support_iff.1 hj
      have hβ₁j : β₁ j = 0 := Nat.eq_zero_of_le_zero ((hp₁.2 j).trans_eq hsj)
      have hβ₂j : β₂ j = 0 := Nat.eq_zero_of_le_zero ((hp₂.2 j).trans_eq hsj)
      have hm : m₁ = m₂ := by
        simpa [hβ₁j, hβ₂j] using DFunLike.congr_fun heq j
      subst hm
      exact Prod.ext rfl (add_left_cancel heq)
    · intro β hβ
      rw [Finset.mem_Iic] at hβ
      have hsj : s j = 0 := Finsupp.notMem_support_iff.1 hj
      refine ⟨(β j, β - single j (β j)), ?_, ?_⟩
      · rw [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff, Finset.mem_Iic]
        refine ⟨by simpa [hsj] using hβ j, fun i ↦ ?_⟩
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simpa [hij.symm] using hβ i
      · ext i
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp
    · rintro ⟨m, β'⟩ hp
      rw [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff, Finset.mem_Iic] at hp
      have hsj : s j = 0 := Finsupp.notMem_support_iff.1 hj
      have hβ'j : β' j = 0 := Nat.eq_zero_of_le_zero ((hp.2 j).trans_eq hsj)
      rw [monomial_mul_monomial]
      congr 1
      · have htsub : (single j k + s) - (single j m + β') = single j (k - m) + (s - β') := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp [hsj, hβ'j]
          · simp [hij.symm]
        rw [htsub, mapDomain_add, mapDomain_single]
        ext (h | i); simp
      · rw [Finsupp.prod, Finsupp.prod, hsupp, Finset.prod_insert hj]
        congr 1
        · simp [hsj, hβ'j]
        · refine Finset.prod_congr rfl fun i hi ↦ ?_
          have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
          simp [hij.symm]

open Classical in
/-- **Homogeneous Hasse jets of a block homogenization** at the chart point `(1, a)`
(Evertse 1995, §1, pp. 221–222): for `d`-bounded `f`, `(∂^(κ ⊕ β) H_d(f))(1, a)` is a linear
combination of the affine jets `(∂^γ f)(a)` with `β ≤ γ` and `t_h(γ - β) ≤ κ h` for all blocks
`h`. Summing over `(taylor a f).support` avoids any finiteness assumption on `S`. -/
theorem eval_one_hasseDeriv_sumElim_blockHomogenize [Fintype B] (a : S → R) (κ : B →₀ ℕ)
    (β : S →₀ ℕ) {f : MvPolynomial S R} (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    eval (Sum.elim (fun _ ↦ 1) a) (hasseDeriv (κ.sumElim β) (blockHomogenize b d f)) =
      ∑ γ ∈ (taylor a f).support with β ≤ γ ∧ ∀ h, (γ - β).mapDomain b h ≤ κ h,
        eval a (hasseDeriv γ f) *
          (γ.prod fun j k ↦ (k.choose (β j) : R) * (-a j) ^ (k - β j)) *
          ∏ h, ((d h - γ.mapDomain b h).choose (κ h - (γ - β).mapDomain b h) : R) := by
  classical
  rw [← coeff_taylor, blockHomogenize_eq_sum_support_taylor b d a hf, map_sum, coeff_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  have hshift (j : S) :
      taylor (Sum.elim (fun _ : B ↦ (1 : R)) a) (X (.inr j) - C (a j) * X (.inl (b j))) =
        X (.inr j) - C (a j) * X (.inl (b j)) := by
    simp only [map_sub, map_mul, taylor_X, taylor_C, Sum.elim_inl, Sum.elim_inr, C_1]
    ring
  have hinl :
      taylor (Sum.elim (fun _ : B ↦ (1 : R)) a)
          (∏ h : B, (X (.inl h) : MvPolynomial (B ⊕ S) R) ^ (d h - γ.mapDomain b h)) =
        rename Sum.inl (∏ h : B, (X h + 1 : MvPolynomial B R) ^ (d h - γ.mapDomain b h)) := by
    simp [map_prod]
  have hinr :
      taylor (Sum.elim (fun _ : B ↦ (1 : R)) a)
          (γ.prod fun j k ↦ (X (.inr j) - C (a j) * X (.inl (b j)) : MvPolynomial (B ⊕ S) R) ^ k) =
        γ.prod fun j k ↦ (X (.inr j) - C (a j) * X (.inl (b j))) ^ k := by
    simp only [Finsupp.prod, map_prod, map_pow, hshift]
  rw [map_mul, map_mul, taylor_C, hinl, hinr, mul_assoc, coeff_C_mul,
    finsuppProd_X_inr_sub_C_mul_X_inl_pow, Finset.mul_sum, coeff_sum]
  by_cases hcond : β ≤ γ ∧ ∀ h, (γ - β).mapDomain b h ≤ κ h
  · rw [ite_eq_left hcond]
    obtain ⟨hβγ, hκ⟩ := hcond
    have hκ' : (γ - β).mapDomain b ≤ κ := hκ
    rw [Finset.sum_eq_single β]
    · rw [coeff_rename_inl_mul_monomial_sumElim, ite_eq_left ⟨rfl, hκ'⟩,
        coeff_prod_X_add_one_pow]
      simp only [tsub_apply]
      ring
    · intro β' _ hβ'
      rw [coeff_rename_inl_mul_monomial_sumElim, ite_eq_right (fun h ↦ hβ' h.1)]
    · intro hβmem
      exact absurd (Finset.mem_Iic.2 hβγ) hβmem
  · rw [ite_eq_right hcond, Finset.sum_eq_zero]
    · exact mul_zero _
    · intro β' hβ'
      rw [coeff_rename_inl_mul_monomial_sumElim, ite_eq_right]
      rintro ⟨rfl, hle⟩
      exact hcond ⟨Finset.mem_Iic.1 hβ', hle⟩

open Classical in
/-- **Homogeneous Hasse jets of a block homogenization** over `blockExponents b d` for finite `S`
(Evertse 1995, §1, pp. 221–222):
`D^(κ ⊕ β) H_d(f)(1, a)` equals the sum over `γ ∈ Γ_d` with `β ≤ γ` and `t(γ - β) ≤ κ` of
`D^γ f(a) ∏_j (γ_j choose β_j) (-a_j)^(γ_j - β_j) ∏_h (d_h - t_h(γ) choose κ_h - t_h(γ - β))`. -/
theorem eval_one_hasseDeriv_sumElim_blockHomogenize_eq_sum_blockExponents [Fintype B] [Fintype S]
    (a : S → R) (κ : B →₀ ℕ) (β : S →₀ ℕ) {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    eval (Sum.elim (fun _ ↦ 1) a) (hasseDeriv (κ.sumElim β) (blockHomogenize b d f)) =
      ∑ γ ∈ blockExponents b d with β ≤ γ ∧ ∀ h, (γ - β).mapDomain b h ≤ κ h,
        eval a (hasseDeriv γ f) *
          (∏ j, ((γ j).choose (β j) : R) * (-a j) ^ (γ j - β j)) *
          ∏ h, ((d h - γ.mapDomain b h).choose (κ h - (γ - β).mapDomain b h) : R) := by
  classical
  rw [eval_one_hasseDeriv_sumElim_blockHomogenize b d a κ β hf]
  have hcongr :
      ∑ γ ∈ (taylor a f).support with β ≤ γ ∧ ∀ h, (γ - β).mapDomain b h ≤ κ h,
        eval a (hasseDeriv γ f) *
          (γ.prod fun j k ↦ (k.choose (β j) : R) * (-a j) ^ (k - β j)) *
          ∏ h, ((d h - γ.mapDomain b h).choose (κ h - (γ - β).mapDomain b h) : R) =
      ∑ γ ∈ (taylor a f).support with β ≤ γ ∧ ∀ h, (γ - β).mapDomain b h ≤ κ h,
        eval a (hasseDeriv γ f) *
          (∏ j, ((γ j).choose (β j) : R) * (-a j) ^ (γ j - β j)) *
          ∏ h, ((d h - γ.mapDomain b h).choose (κ h - (γ - β).mapDomain b h) : R) := by
    refine Finset.sum_congr rfl fun γ hγ ↦ ?_
    have hβγ : β ≤ γ := (Finset.mem_filter.1 hγ).2.1
    congr 2
    rw [Finsupp.prod, Finset.prod_subset (Finset.subset_univ γ.support)]
    intro j _ hj
    have hγj : γ j = 0 := Finsupp.notMem_support_iff.1 hj
    have hβj : β j = 0 := Nat.eq_zero_of_le_zero ((hβγ j).trans_eq hγj)
    simp [hγj, hβj]
  rw [hcongr]
  have hsub :
      {γ ∈ (taylor a f).support | β ≤ γ ∧ ∀ h, (γ - β).mapDomain b h ≤ κ h} ⊆
        {γ ∈ blockExponents b d | β ≤ γ ∧ ∀ h, (γ - β).mapDomain b h ≤ κ h} := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ ⊢
    exact ⟨(mem_blockExponents b d).2 (mapDomain_le_of_mem_support_taylor b d a hf hγ.1), hγ.2⟩
  refine Finset.sum_subset hsub fun γ hγ₁ hγ₂ ↦ ?_
  rw [Finset.mem_filter] at hγ₁ hγ₂
  have hnot : γ ∉ (taylor a f).support := fun hm ↦ hγ₂ ⟨hm, hγ₁.2⟩
  rw [notMem_support_iff, coeff_taylor] at hnot
  simp [hnot]

/-- If every affine jet `(∂^γ f)(a)` with `β ≤ γ` and `t_h(γ) ≤ κ h + t_h(β)` vanishes, then the
homogeneous jet `(∂^(κ ⊕ β) H_d(f))(1, a)` vanishes as well. -/
theorem eval_one_hasseDeriv_sumElim_blockHomogenize_eq_zero [Fintype B] (a : S → R) (κ : B →₀ ℕ)
    (β : S →₀ ℕ) {f : MvPolynomial S R} (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h)
    (hvan : ∀ γ : S →₀ ℕ, β ≤ γ → (∀ h, γ.mapDomain b h ≤ κ h + β.mapDomain b h) →
      eval a (hasseDeriv γ f) = 0) :
    eval (Sum.elim (fun _ ↦ 1) a) (hasseDeriv (κ.sumElim β) (blockHomogenize b d f)) = 0 := by
  classical
  rw [eval_one_hasseDeriv_sumElim_blockHomogenize b d a κ β hf]
  refine Finset.sum_eq_zero fun γ hγ ↦ ?_
  obtain ⟨_, hβγ, hκ⟩ := Finset.mem_filter.1 hγ
  have hγle (h : B) : γ.mapDomain b h ≤ κ h + β.mapDomain b h := by
    have hsplit : γ = (γ - β) + β := (tsub_add_cancel_of_le hβγ).symm
    calc
      γ.mapDomain b h = (γ - β).mapDomain b h + β.mapDomain b h := by
        conv_lhs => rw [hsplit]
        simp [mapDomain_add]
      _ ≤ κ h + β.mapDomain b h := Nat.add_le_add_right (hκ h) _
  simp [hvan γ hβγ hγle]

end CommRing

/-! ### Examples -/

/-- Over `ℚ`, in one block of degree `2`, `f(y) = y^2 - y` homogenizes to `F = Y^2 - X_0 Y`.
At `(1, 1)` we have `(∂F / ∂X_0)(1, 1) = -1` while `f(1) = 0`: the `γ = 1` affine jet
`f'(1) = 1` contributes to `D^(1 ⊕ 0) F(1, 1)` through the factor `-a = -1`. -/
example :
    let f : MvPolynomial Unit ℚ := X () ^ 2 - X ()
    let F := blockHomogenize (fun _ : Unit ↦ ()) (fun _ ↦ 2) f
    eval (fun _ ↦ 1) f = 0 ∧
      eval (Sum.elim (fun _ ↦ 1) (fun _ ↦ 1))
        (hasseDeriv ((single () 1).sumElim 0) F) = -1 := by
  classical
  dsimp only
  refine ⟨by simp, ?_⟩
  have hf : ∀ e ∈ (X () ^ 2 - X () : MvPolynomial Unit ℚ).support,
      ∀ h : Unit, e.mapDomain (fun _ : Unit ↦ ()) h ≤ 2 := by
    intro e he h
    rw [mem_support_iff] at he
    by_contra! hlt
    have he2 : single () 2 ≠ e := fun h2 ↦ by simp [← h2] at hlt
    have he1 : single () 1 ≠ e := fun h1 ↦ by simp [← h1] at hlt
    apply he
    rw [X_pow_eq_monomial, X, sub_eq_add_neg, ← map_neg (monomial _),
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial, coeff_monomial,
      ite_eq_right he2, ite_eq_right he1, add_zero]
  rw [eval_one_hasseDeriv_sumElim_blockHomogenize_eq_sum_blockExponents _ _ _ _ _ hf]
  have hmap (γ : Unit →₀ ℕ) : γ.mapDomain (fun _ : Unit ↦ ()) () = γ () := by
    have heq : (fun _ : Unit ↦ ()) = id := Subsingleton.elim _ _
    simp [heq]
  have hset :
      {γ ∈ blockExponents (fun _ : Unit ↦ ()) (fun _ ↦ 2) |
        (0 : Unit →₀ ℕ) ≤ γ ∧ ∀ h : Unit, (γ - 0).mapDomain (fun _ ↦ ()) h ≤ single () 1 h} =
      {0, single () 1} := by
    ext γ
    simp only [Finset.mem_filter, mem_blockExponents, zero_le, tsub_zero, true_and,
      Finset.mem_insert, Finset.mem_singleton, Unique.forall_iff, hmap, single_eq_same]
    constructor
    · rintro ⟨_, h1⟩
      have heq : γ = single () (γ ()) := Finsupp.ext fun u ↦ by simp [Unique.eq_default u]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h1'
      · left; rw [heq]; simp [h0]
      · right; rw [heq]; simp [h1']
    · rintro (rfl | rfl) <;> simp
  have hne : (0 : Unit →₀ ℕ) ≠ single () 1 := fun h ↦ by
    simpa using DFunLike.congr_fun h ()
  rw [hset, Finset.sum_pair hne]
  have hd0 : eval (fun _ : Unit ↦ (1 : ℚ))
      (hasseDeriv 0 (X () ^ 2 - X () : MvPolynomial Unit ℚ)) = 0 := by
    simp
  have hd1 : eval (fun _ : Unit ↦ (1 : ℚ))
      (hasseDeriv (single () 1) (X () ^ 2 - X () : MvPolynomial Unit ℚ)) = 1 := by
    rw [X_pow_eq_monomial, X, map_sub, hasseDeriv_monomial, hasseDeriv_monomial, ← single_tsub]
    simp [eval_monomial]
    norm_num
  rw [hd0, hd1]
  simp

/-- The `d`-boundedness hypothesis in `eval_one_hasseDeriv_zero_sumElim_blockHomogenize` cannot be
dropped: in one block of degree `1`, `f(y) = y^2 + 1` has `(∂^2 f)(0) = 1`, whereas
`blockHomogenize` discards `y^2` to give `X_0`, whose `∂^(0 ⊕ 2)` at `(1, 0)` vanishes. -/
example :
    let f : MvPolynomial Unit ℚ := X () ^ 2 + 1
    eval (fun _ ↦ 0) (hasseDeriv (single () 2) f) = 1 ∧
      eval (Sum.elim (fun _ ↦ 1) (fun _ ↦ 0))
        (hasseDeriv ((0 : Unit →₀ ℕ).sumElim (single () 2))
          (blockHomogenize (fun _ : Unit ↦ ()) (fun _ ↦ 1) f)) = 0 := by
  have hbh : blockHomogenize (fun _ : Unit ↦ ()) (fun _ ↦ 1)
      (X () ^ 2 + 1 : MvPolynomial Unit ℚ) = X (.inl ()) := by
    rw [blockHomogenize_add, X_pow_eq_monomial, blockHomogenize_monomial, ite_eq_right, zero_add,
      blockHomogenize_one, Finset.univ_unique, Finset.prod_singleton, pow_one]
    intro h
    simpa using h ()
  refine ⟨?_, ?_⟩
  · simp [X_pow_eq_monomial, hasseDeriv_monomial]
  · rw [hbh, X, hasseDeriv_monomial]
    simp

/-- Over `ZMod 2`, `f(y) = y^2 - 1` has second Hasse derivative `1` at `1` (both before and after
block homogenization of degree `2`), whereas its second iterated partial derivative vanishes. -/
example :
    let f : MvPolynomial Unit (ZMod 2) := X () ^ 2 - 1
    eval (fun _ ↦ 1) (hasseDeriv (single () 2) f) = 1 ∧
      eval (Sum.elim (fun _ ↦ 1) (fun _ ↦ 1))
        (hasseDeriv ((0 : Unit →₀ ℕ).sumElim (single () 2))
          (blockHomogenize (fun _ : Unit ↦ ()) (fun _ ↦ 2) f)) = 1 ∧
      eval (fun _ ↦ 1) ((pderiv ())^[2] f) = 0 := by
  have hf : ∀ e ∈ (X () ^ 2 - 1 : MvPolynomial Unit (ZMod 2)).support,
      ∀ h : Unit, e.mapDomain (fun _ : Unit ↦ ()) h ≤ 2 := by
    intro e he h
    rw [mem_support_iff] at he
    by_contra! hlt
    have he2 : single () 2 ≠ e := fun h2 ↦ by simp [← h2] at hlt
    have he0 : (0 : Unit →₀ ℕ) ≠ e := fun h0 ↦ by simp [← h0] at hlt
    apply he
    rw [X_pow_eq_monomial, ← C_1, ← monomial_zero', sub_eq_add_neg, ← map_neg (monomial _),
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial, coeff_monomial,
      ite_eq_right he2, ite_eq_right he0, add_zero]
  have hd2 : eval (fun _ : Unit ↦ (1 : ZMod 2))
      (hasseDeriv (single () 2) (X () ^ 2 - 1 : MvPolynomial Unit (ZMod 2))) = 1 := by
    simp [X_pow_eq_monomial, hasseDeriv_monomial]
  refine ⟨hd2, ?_, ?_⟩
  · rw [eval_one_hasseDeriv_zero_sumElim_blockHomogenize _ _ _ _ hf, hd2]
  · rw [← factorial_smul_hasseDeriv_single () 2, Nat.factorial_two, map_nsmul, hd2]
    decide

end MvPolynomial
