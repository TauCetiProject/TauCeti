/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.BlockHomogenize.Taylor
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# Weighted indices of block homogenizations

Let `b : S → B` distribute the affine variables `S` into finitely many blocks `B` of prescribed
degrees `d : B → ℕ`. On the affine variables `S`, the pulled-back degree vector `d ∘ b` assigns
weight `d (b j)` to `j : S`; on the block-homogenized variables `B ⊕ S`, the degree vector
`Sum.elim d (d ∘ b)` assigns weight `d h` both to the homogenizing variable `.inl h` and to every
affine variable `.inr j` with `b j = h`.

When `f : MvPolynomial S R` has block degrees `e.mapDomain b h ≤ d h` on its support:
* Over any commutative semiring, pure affine Hasse derivatives `∂^(0 ⊕ β)` commute with
  dehomogenization at `X_h = 1` (`MvPolynomial.eval_one_hasseDeriv_zero_sumElim_blockHomogenize`),
  so the homogeneous weighted index of `blockHomogenize b d f` at `(1, a)` is at most the affine
  weighted index of `f` at `a` (`MvPolynomial.weightedIndex_blockHomogenize_le`).
* Over any commutative ring, `(∂^(κ ⊕ β) H_d(f))(1, a)` is a linear combination of the affine jets
  `(∂^γ f)(a)` with `β ≤ γ` and `γ.mapDomain b h ≤ κ h + β.mapDomain b h`
  (`MvPolynomial.eval_one_hasseDeriv_sumElim_blockHomogenize`). Since the reciprocal block weight
  functional `fun h ↦ (d h : ℝ≥0∞)⁻¹` on `B →₀ ℕ` is monotone, all homogeneous jets at `(1, a)` of
  block weight `< T` vanish if and only if all affine jets at `a` of block weight `< T` vanish for
  every `T : ℝ≥0∞` (`MvPolynomial.forall_eval_one_hasseDeriv_sumElim_blockHomogenize_eq_zero_iff`),
  and the homogeneous and affine weighted indices coincide
  (`MvPolynomial.weightedIndex_blockHomogenize`). Neither result requires positive block degrees or
  finitely many affine variables, and both cover `f = 0`, where both indices equal `⊤`.
* Dually, dehomogenizing any polynomial `F : MvPolynomial (B ⊕ S) R` that is homogeneous of degree
  `d h` in every block `h` yields a `d`-bounded affine polynomial with the same weighted index
  (`MvPolynomial.weightedIndex_aeval_one_X`).

## Main results

* `MvPolynomial.mapDomain_le_of_mem_support_aeval_one_X`: dehomogenizing a block-homogeneous
  polynomial of degrees `d` yields a `d`-bounded affine polynomial.
* `MvPolynomial.hasseDeriv_sumElim_blockHomogenize_eq_zero_of_lt`: if `d h < κ h + t_h(β)` in some
  block `h`, then `∂^(κ ⊕ β) (blockHomogenize b d f) = 0`.
* `MvPolynomial.weightedIndex_blockHomogenize_le`: over a commutative semiring, block homogenization
  does not increase `weightedIndex` on `d`-bounded polynomials.
* `MvPolynomial.weightedIndex_blockHomogenize`, `MvPolynomial.weightedIndex_aeval_one_X`: over a
  commutative ring, block homogenization and dehomogenization preserve `weightedIndex`.
* `MvPolynomial.forall_eval_one_hasseDeriv_sumElim_blockHomogenize_eq_zero_iff`: equivalence of
  homogeneous jet vanishing at `(1, a)` and affine jet vanishing at `a` below any threshold
  `T : ℝ≥0∞`.
* `MvPolynomial.ofReal_le_weightedIndex_comp_of_eval_hasseDeriv_eq_zero`,
  `MvPolynomial.ofReal_le_weightedIndex_blockHomogenize_of_eval_hasseDeriv_eq_zero`,
  `MvPolynomial.le_sum_mapDomain_div_of_le_weightedIndex_comp`: real-valued index bounds in terms of
  the block ratios `∑ h, t_h(γ) / d h`.

## References

* J.-H. Evertse, *An explicit version of Faltings' Product Theorem and an improvement of Roth's
  lemma*, Acta Arith. 73 (1995), §1, pp. 221–222.
-/

public section

namespace MvPolynomial

open Finsupp
open scoped ENNReal

section CommSemiring

private theorem le_weightedIndex_of_forall {σ R : Type*} [CommSemiring R] {r : σ → ℕ}
    {a : σ → R} {P : MvPolynomial σ R} {t : ℝ≥0∞}
    (h : ∀ u : σ →₀ ℕ, eval a (hasseDeriv u P) ≠ 0 →
      t ≤ u.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹)) :
    t ≤ weightedIndex r a P := by
  rw [weightedIndex_def]
  refine le_iInf₂ fun u hu ↦ (h u hu).trans_eq ?_
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, div_eq_mul_inv]

variable {R B S : Type*} [CommSemiring R] (b : S → B) (d : B → ℕ)

/-- Dehomogenizing a polynomial `F : MvPolynomial (B ⊕ S) R` that is homogeneous of degree `d h` in
every block `h` produces an affine polynomial whose monomials satisfy `t_h(e) ≤ d h`. -/
theorem mapDomain_le_of_mem_support_aeval_one_X [DecidableEq B] {F : MvPolynomial (B ⊕ S) R}
    (hF : ∀ h, F.IsWeightedHomogeneous (fun v ↦ if Sum.elim id b v = h then 1 else 0) (d h))
    {e : S →₀ ℕ} (he : e ∈ (aeval (Sum.elim (fun _ ↦ 1) (X : S → MvPolynomial S R)) F).support)
    (h : B) :
    e.mapDomain b h ≤ d h := by
  classical
  rw [mem_support_iff] at he
  have hex : ∃ u ∈ F.support,
      (aeval (Sum.elim (fun _ : B ↦ (1 : MvPolynomial S R)) X)
        (monomial u (F.coeff u))).coeff e ≠ 0 := by
    by_contra! hall
    apply he
    conv_lhs => rw [F.as_sum]
    rw [map_sum, coeff_sum]
    exact Finset.sum_eq_zero hall
  obtain ⟨u, hu, hne⟩ := hex
  obtain ⟨κ, e', rfl⟩ : ∃ (κ : B →₀ ℕ) (e' : S →₀ ℕ), u = κ.sumElim e' :=
    ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
  rw [aeval_def, eval₂_monomial_sumElim_of_eq_one _ _ (fun _ ↦ rfl), Sum.elim_comp_inr,
    ← aeval_def, aeval_X_left_apply, coeff_monomial] at hne
  have he' : e' = e := by_contra fun h' ↦ hne (ite_eq_right h')
  subst e'
  have hdeg : κ h + e.mapDomain b h = d h := by
    rw [← Finsupp.weight_ite_sumElim_eq_add_mapDomain_apply]
    exact hF h (mem_support_iff.1 hu)
  exact hdeg ▸ le_add_self

section Fintype

variable [Fintype B]

/-- Since `blockHomogenize b d f` has degree `d h` in block `h`, any Hasse derivative `∂^(κ ⊕ β)`
whose order `κ h + t_h(β)` in block `h` exceeds `d h` vanishes identically. -/
theorem hasseDeriv_sumElim_blockHomogenize_eq_zero_of_lt (f : MvPolynomial S R)
    {κ : B →₀ ℕ} {β : S →₀ ℕ} {h : B} (hlt : d h < κ h + β.mapDomain b h) :
    hasseDeriv (κ.sumElim β) (blockHomogenize b d f) = 0 := by
  classical
  by_contra hne
  obtain ⟨m, hm⟩ := support_nonempty.2 hne
  rw [mem_support_iff, hasseDeriv_coeff] at hm
  have hdeg := isWeightedHomogeneous_blockHomogenize b d f h (right_ne_zero_of_mul hm)
  rw [map_add, Finsupp.weight_ite_sumElim_eq_add_mapDomain_apply] at hdeg
  exact (le_add_self.trans_eq hdeg).not_gt hlt

/-- Over any commutative semiring, the homogeneous `weightedIndex` of `blockHomogenize b d f` at
`(1, a)` is at most the affine `weightedIndex` of `f` at `a` whenever `f` is `d`-bounded. -/
theorem weightedIndex_blockHomogenize_le (a : S → R) {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    weightedIndex (Sum.elim d (d ∘ b)) (Sum.elim (fun _ ↦ 1) a) (blockHomogenize b d f) ≤
      weightedIndex (d ∘ b) a f := by
  refine le_weightedIndex_of_forall fun β hβ ↦ ?_
  have hjet : eval (Sum.elim (fun _ ↦ 1) a)
      (hasseDeriv ((0 : B →₀ ℕ).sumElim β) (blockHomogenize b d f)) ≠ 0 := by
    rwa [eval_one_hasseDeriv_zero_sumElim_blockHomogenize b d a β hf]
  have hw : (fun v ↦ ((Sum.elim d (d ∘ b) v : ℕ) : ℝ≥0∞)⁻¹) =
      Sum.elim (fun h ↦ (d h : ℝ≥0∞)⁻¹) (fun j ↦ (((d ∘ b) j : ℕ) : ℝ≥0∞)⁻¹) := by
    ext (_ | _) <;> rfl
  refine (weightedIndex_le hjet).trans_eq ?_
  rw [hw, Finsupp.weight_sumElim, map_zero, zero_add]

/-- A nonzero affine jet `∂^γ f (a)` of a `d`-bounded polynomial at a point where the block-weighted
index is at least `ENNReal.ofReal t` satisfies `t_h(γ) ≤ d h` for every block `h` and
`t ≤ ∑ h, t_h(γ) / d h` in `ℝ`. -/
theorem le_sum_mapDomain_div_of_le_weightedIndex_comp {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) {a : S → R} {t : ℝ}
    (ht : ENNReal.ofReal t ≤ weightedIndex (d ∘ b) a f) {γ : S →₀ ℕ}
    (hγ : eval a (hasseDeriv γ f) ≠ 0) :
    (∀ h, γ.mapDomain b h ≤ d h) ∧ t ≤ ∑ h, (γ.mapDomain b h : ℝ) / d h := by
  have hγd : ∀ h, γ.mapDomain b h ≤ d h :=
    mapDomain_le_of_hasseDeriv_ne_zero b d hf (fun hz ↦ hγ (by simp [hz]))
  refine ⟨hγd, ?_⟩
  have hw : γ.weight (fun j ↦ (((d ∘ b) j : ℕ) : ℝ≥0∞)⁻¹) =
      ENNReal.ofReal (∑ h, (γ.mapDomain b h : ℝ) / d h) := by
    have hcomp : (fun j ↦ (((d ∘ b) j : ℕ) : ℝ≥0∞)⁻¹) = (fun h ↦ (d h : ℝ≥0∞)⁻¹) ∘ b := rfl
    rw [hcomp, ← Finsupp.weight_mapDomain, Finsupp.weight_inv_natCast_eq_ofReal_sum_div hγd]
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun h _ ↦ by positivity)).1
    (ht.trans ((weightedIndex_le hγ).trans_eq hw))

/-- For a `d`-bounded polynomial `f`, the affine block-weighted index `weightedIndex (d ∘ b) a f` is
at least `ENNReal.ofReal t` once `(∂^γ f)(a) = 0` for every `γ` with `t_h(γ) ≤ d h` and real block
weight `∑ h, t_h(γ) / d h < t`. -/
theorem ofReal_le_weightedIndex_comp_of_eval_hasseDeriv_eq_zero {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) {a : S → R} {t : ℝ}
    (hvan : ∀ γ : S →₀ ℕ, (∀ h, γ.mapDomain b h ≤ d h) →
      ∑ h, (γ.mapDomain b h : ℝ) / d h < t → eval a (hasseDeriv γ f) = 0) :
    ENNReal.ofReal t ≤ weightedIndex (d ∘ b) a f := by
  refine le_weightedIndex_of_forall fun γ hγ ↦ le_of_not_gt fun hlt ↦ hγ ?_
  by_cases hγd : ∀ h, γ.mapDomain b h ≤ d h
  · have hcomp : (fun j ↦ (((d ∘ b) j : ℕ) : ℝ≥0∞)⁻¹) = (fun h ↦ (d h : ℝ≥0∞)⁻¹) ∘ b := rfl
    rw [hcomp, ← Finsupp.weight_mapDomain, Finsupp.weight_inv_natCast_eq_ofReal_sum_div hγd] at hlt
    exact hvan γ hγd (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
  · push Not at hγd
    obtain ⟨h, hh⟩ := hγd
    rw [hasseDeriv_eq_zero_of_lt_mapDomain b d hf hh, map_zero]

end Fintype

end CommSemiring

section CommRing

variable {R B S : Type*} [CommRing R] (b : S → B) (d : B → ℕ)

section Fintype

variable [Fintype B]

/-- **Equality of homogeneous and affine weighted indices** (Evertse 1995, §1, p. 222): for any
`d`-bounded polynomial `f : MvPolynomial S R` and any affine center `a : S → R`, the homogeneous
`weightedIndex` of `blockHomogenize b d f` at `(1, a)` with weights `Sum.elim d (d ∘ b)` equals the
affine `weightedIndex` of `f` at `a` with weights `d ∘ b`. Zero block degrees and `f = 0` (where
both indices equal `⊤`) are allowed, and `S` need not be finite. -/
theorem weightedIndex_blockHomogenize (a : S → R) {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    weightedIndex (Sum.elim d (d ∘ b)) (Sum.elim (fun _ ↦ 1) a) (blockHomogenize b d f) =
      weightedIndex (d ∘ b) a f := by
  refine (weightedIndex_blockHomogenize_le b d a hf).antisymm ?_
  refine le_weightedIndex_of_forall fun u hu ↦ ?_
  obtain ⟨κ, β, rfl⟩ : ∃ (κ : B →₀ ℕ) (β : S →₀ ℕ), u = κ.sumElim β :=
    ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
  obtain ⟨γ, _, hγle, hγne⟩ : ∃ γ : S →₀ ℕ, β ≤ γ ∧
      (∀ h, γ.mapDomain b h ≤ κ h + β.mapDomain b h) ∧ eval a (hasseDeriv γ f) ≠ 0 := by
    by_contra! hvan
    exact hu (eval_one_hasseDeriv_sumElim_blockHomogenize_eq_zero b d a κ β hf hvan)
  have hle : γ.mapDomain b ≤ κ + β.mapDomain b := hγle
  have hγw : γ.weight (fun j ↦ (((d ∘ b) j : ℕ) : ℝ≥0∞)⁻¹) =
      (γ.mapDomain b).weight (fun h ↦ (d h : ℝ≥0∞)⁻¹) :=
    (Finsupp.weight_mapDomain (fun h ↦ (d h : ℝ≥0∞)⁻¹) b γ).symm
  have huw : (κ.sumElim β).weight (fun v ↦ ((Sum.elim d (d ∘ b) v : ℕ) : ℝ≥0∞)⁻¹) =
      (κ + β.mapDomain b).weight (fun h ↦ (d h : ℝ≥0∞)⁻¹) := by
    have hcomp : (fun v ↦ ((Sum.elim d (d ∘ b) v : ℕ) : ℝ≥0∞)⁻¹) =
        (fun h ↦ (d h : ℝ≥0∞)⁻¹) ∘ Sum.elim id b := by
      ext (_ | _) <;> rfl
    rw [hcomp, ← Finsupp.weight_mapDomain, Finsupp.mapDomain_sumElim, Finsupp.mapDomain_id]
  exact (weightedIndex_le hγne).trans <| by
    rw [hγw, huw]
    exact Finsupp.weight_mono (fun h ↦ (d h : ℝ≥0∞)⁻¹) hle

/-- **Equivalence of homogeneous and affine jet vanishing** (Evertse 1995, §1, p. 222): for any
`d`-bounded polynomial `f` and any threshold `T : ℝ≥0∞`, all homogeneous Hasse jets
`(∂^(κ ⊕ β) H_d(f))(1, a)` of block weight `∑ h, (κ h + t_h(β)) / d h < T` vanish if and only if all
affine Hasse jets `(∂^γ f)(a)` of block weight `∑ h, t_h(γ) / d h < T` vanish. -/
theorem forall_eval_one_hasseDeriv_sumElim_blockHomogenize_eq_zero_iff (a : S → R)
    {f : MvPolynomial S R} (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) (T : ℝ≥0∞) :
    (∀ (κ : B →₀ ℕ) (β : S →₀ ℕ),
      ∑ h, ((κ h + β.mapDomain b h : ℕ) : ℝ≥0∞) / d h < T →
        eval (Sum.elim (fun _ ↦ 1) a)
          (hasseDeriv (κ.sumElim β) (blockHomogenize b d f)) = 0) ↔
    (∀ γ : S →₀ ℕ,
      ∑ h, (γ.mapDomain b h : ℝ≥0∞) / d h < T →
        eval a (hasseDeriv γ f) = 0) := by
  have hsum_eq (κ : B →₀ ℕ) (β : S →₀ ℕ) :
      (∑ v ∈ (κ.sumElim β).support,
          ((κ.sumElim β) v : ℝ≥0∞) / ((Sum.elim d (d ∘ b) v : ℕ) : ℝ≥0∞)) =
        ∑ h, ((κ h + β.mapDomain b h : ℕ) : ℝ≥0∞) / d h := by
    rw [← Finsupp.weight_inv_natCast_sumElim_eq_sum_div b d κ β,
      Finsupp.weight_apply, Finsupp.sum]
    simp only [nsmul_eq_mul, div_eq_mul_inv]
  have hlhs : T ≤ weightedIndex (Sum.elim d (d ∘ b)) (Sum.elim (fun _ ↦ 1) a)
        (blockHomogenize b d f) ↔
      ∀ (κ : B →₀ ℕ) (β : S →₀ ℕ),
        ∑ h, ((κ h + β.mapDomain b h : ℕ) : ℝ≥0∞) / d h < T →
          eval (Sum.elim (fun _ ↦ 1) a)
            (hasseDeriv (κ.sumElim β) (blockHomogenize b d f)) = 0 := by
    rw [le_weightedIndex_iff]
    constructor
    · intro H κ β hlt
      exact H (κ.sumElim β) ((hsum_eq κ β).trans_lt hlt)
    · intro H u hlt
      obtain ⟨κ, β, rfl⟩ : ∃ (κ : B →₀ ℕ) (β : S →₀ ℕ), u = κ.sumElim β :=
        ⟨_, _, (comapDomain_sumElim_comapDomain u).symm⟩
      exact H κ β ((hsum_eq κ β).symm.trans_lt hlt)
  have hrhs : T ≤ weightedIndex (d ∘ b) a f ↔
      ∀ γ : S →₀ ℕ,
        ∑ h, (γ.mapDomain b h : ℝ≥0∞) / d h < T → eval a (hasseDeriv γ f) = 0 := by
    rw [le_weightedIndex_iff]
    refine forall_congr' fun γ ↦ imp_congr_left ?_
    rw [← Finsupp.weight_inv_natCast_comp_eq_sum_mapDomain_div b d γ,
      Finsupp.weight_apply, Finsupp.sum]
    simp only [Function.comp_apply, nsmul_eq_mul, div_eq_mul_inv]
  rw [← hlhs, ← hrhs, weightedIndex_blockHomogenize b d a hf]

/-- For a `d`-bounded polynomial `f`, the homogeneous `weightedIndex` of `blockHomogenize b d f` at
`(1, a)` is at least `ENNReal.ofReal t` once `(∂^γ f)(a) = 0` for every `γ` with `t_h(γ) ≤ d h` and
real block weight `∑ h, t_h(γ) / d h < t`. -/
theorem ofReal_le_weightedIndex_blockHomogenize_of_eval_hasseDeriv_eq_zero
    {f : MvPolynomial S R} (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) {a : S → R} {t : ℝ}
    (hvan : ∀ γ : S →₀ ℕ, (∀ h, γ.mapDomain b h ≤ d h) →
      ∑ h, (γ.mapDomain b h : ℝ) / d h < t → eval a (hasseDeriv γ f) = 0) :
    ENNReal.ofReal t ≤
      weightedIndex (Sum.elim d (d ∘ b)) (Sum.elim (fun _ ↦ 1) a) (blockHomogenize b d f) := by
  rw [weightedIndex_blockHomogenize b d a hf]
  exact ofReal_le_weightedIndex_comp_of_eval_hasseDeriv_eq_zero b d hf hvan

end Fintype

/-- Dehomogenizing a polynomial `F : MvPolynomial (B ⊕ S) R` that is homogeneous of degree `d h` in
every block `h` preserves its weighted index between `(1, a)` and `a`. -/
theorem weightedIndex_aeval_one_X [Finite B] [DecidableEq B] (a : S → R)
    {F : MvPolynomial (B ⊕ S) R}
    (hF : ∀ h, F.IsWeightedHomogeneous (fun v ↦ if Sum.elim id b v = h then 1 else 0) (d h)) :
    weightedIndex (d ∘ b) a (aeval (Sum.elim (fun _ ↦ 1) X) F) =
      weightedIndex (Sum.elim d (d ∘ b)) (Sum.elim (fun _ ↦ 1) a) F := by
  have := Fintype.ofFinite B
  have hf : ∀ e ∈ (aeval (Sum.elim (fun _ ↦ 1) (X : S → MvPolynomial S R)) F).support,
      ∀ h, e.mapDomain b h ≤ d h :=
    fun _ he h ↦ mapDomain_le_of_mem_support_aeval_one_X b d hF he h
  rw [← weightedIndex_blockHomogenize b d a hf, blockHomogenize_aeval_one_X b d hF]

end CommRing

/-! ### Examples -/

/-- Over `ℚ`, in one block of degree `2`, `f(y) = y^2 - y` vanishes to order `1` at `a = 1`, so
both `f` and its block homogenization `F = Y^2 - X_0 Y` have weighted index `1 / 2`, while at the
threshold weight `1 / 2` itself the pure affine jet `∂^(0 ⊕ 1) F(1, 1) = 1` does not vanish. -/
example :
    let b : Unit → Unit := fun _ ↦ ()
    let d : Unit → ℕ := fun _ ↦ 2
    let f : MvPolynomial Unit ℚ := X () ^ 2 - X ()
    let F := blockHomogenize b d f
    weightedIndex (Sum.elim d (d ∘ b)) (Sum.elim (fun _ ↦ 1) (fun _ ↦ 1)) F = 1 / 2 ∧
      weightedIndex (d ∘ b) (fun _ ↦ 1) f = 1 / 2 ∧
      eval (Sum.elim (fun _ ↦ 1) (fun _ ↦ 1))
        (hasseDeriv ((0 : Unit →₀ ℕ).sumElim (single () 1)) F) = 1 := by
  dsimp only
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
  have hfac : (X () ^ 2 - X () : MvPolynomial Unit ℚ) = X () * (X () - C 1) ^ 1 := by
    simp only [C_1]
    ring
  have hind : weightedIndex (fun _ : Unit ↦ 2) (fun _ ↦ 1)
      (X () ^ 2 - X () : MvPolynomial Unit ℚ) = 1 / 2 := by
    rw [hfac, weightedIndex_mul, (weightedIndex_eq_zero_iff _ _ (X ())).2 (by simp), zero_add,
      weightedIndex_X_sub_C_pow]
    norm_num
  refine ⟨?_, hind, ?_⟩
  · rw [weightedIndex_blockHomogenize _ _ _ hf]
    exact hind
  · rw [eval_one_hasseDeriv_zero_sumElim_blockHomogenize _ _ _ _ hf,
      X_pow_eq_monomial, X, map_sub, hasseDeriv_monomial, hasseDeriv_monomial, ← single_tsub]
    simp [eval_monomial]
    norm_num

/-- At `f = 0`, both the homogeneous and affine weighted indices equal `⊤`. -/
example (b : Unit → Unit) (d : Unit → ℕ) (a : Unit → ℚ) :
    weightedIndex (Sum.elim d (d ∘ b)) (Sum.elim (fun _ ↦ 1) a)
        (blockHomogenize b d (0 : MvPolynomial Unit ℚ)) = ⊤ ∧
      weightedIndex (d ∘ b) a (0 : MvPolynomial Unit ℚ) = ⊤ := by
  simp

/-- Without `d`-boundedness, `weightedIndex_blockHomogenize` can fail: in one block of degree `1`,
`f(y) = y^2` at `a = 0` has affine weighted index `2`, whereas `blockHomogenize` discards `y^2` to
`0` and has homogeneous weighted index `⊤`. -/
example :
    let b : Unit → Unit := fun _ ↦ ()
    let d : Unit → ℕ := fun _ ↦ 1
    let f : MvPolynomial Unit ℚ := X () ^ 2
    weightedIndex (d ∘ b) (fun _ ↦ 0) f = 2 ∧
      weightedIndex (Sum.elim d (d ∘ b)) (Sum.elim (fun _ ↦ 1) (fun _ ↦ 0))
        (blockHomogenize b d f) = ⊤ := by
  dsimp only
  have hbh : blockHomogenize (fun _ : Unit ↦ ()) (fun _ ↦ 1) (X () ^ 2 : MvPolynomial Unit ℚ) =
      0 := by
    rw [X_pow_eq_monomial, blockHomogenize_monomial, ite_eq_right]
    intro h
    simpa using h ()
  refine ⟨?_, by simp [hbh]⟩
  have hpow : (X () ^ 2 : MvPolynomial Unit ℚ) = (X () - C 0) ^ 2 := by simp
  rw [hpow, weightedIndex_X_sub_C_pow]
  norm_num

end MvPolynomial
