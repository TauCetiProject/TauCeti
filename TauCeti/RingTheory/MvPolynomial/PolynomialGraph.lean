/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.MvPolynomial.Kronecker
import Mathlib.Data.ZMod.Basic

/-!
# Base-`B` Kronecker polynomial graphs

For a commutative semiring `k` and natural numbers `m` and `B`, the base-`B` Kronecker
substitution
`polynomialGraph k m B : MvPolynomial (Fin m) k →+* Polynomial k`
sends each variable `X i` (`i : Fin m`) to `T ^ (B ^ i)` and acts as `Polynomial.C` on constants.
Geometrically, when `k` is a commutative ring, its spectrum is the polynomial graph morphism
`𝔸¹_k → 𝔸^m_k`, `t ↦ (t, t ^ B, t ^ (B ^ 2), …, t ^ (B ^ (m - 1)))`.

Over a finite field `𝔽_q`, a hypersurface `V(h) ⊆ 𝔸^m` can contain every `𝔽_q`-rational line
through the origin even when `h ≠ 0` (for instance `X₀² X₁ - X₀ X₁²` over `𝔽_2` vanishes on all
three `𝔽_2`-lines through `0`). Replacing lines by high-degree Kronecker graphs avoids any
prescribed nonzero polynomial without extending the base field: when `B` exceeds every coordinate
of every exponent vector in the support of `h`, base-`B` digit uniqueness makes the weight
`d ↦ ∑ i, d i * B ^ i` injective on the support box `{d | ∀ i, d i < B}`
(`Finsupp.injOn_weight_pow`), so every coefficient of `h` survives in `polynomialGraph k m B h`
without cancellation. When `0 < m`, `X 0 ↦ T` also makes `polynomialGraph k m B` surjective, so the
corresponding morphism `Spec k[T] → Spec k[X₀, …, X_{m - 1}]` is a closed immersion.

## Main definitions

* `TauCeti.polynomialGraph`: the base-`B` Kronecker substitution
  `MvPolynomial (Fin m) k →+* Polynomial k` sending `X i` to `Polynomial.X ^ (B ^ (i : ℕ))`.

## Main results

* `TauCeti.polynomialGraph_coeff`: if every coordinate of every exponent in `h.support` is `< B`,
  then for every `e : Fin m →₀ ℕ` with all `e i < B`, the coefficient of
  `T ^ (∑ i, e i * B ^ i)` in `polynomialGraph k m B h` equals `h.coeff e`.
* `TauCeti.injOn_polynomialGraph`, `TauCeti.polynomialGraph_eq_zero_iff`,
  `TauCeti.polynomialGraph_ne_zero`: `polynomialGraph k m B` is injective (hence kernel-free) on
  polynomials whose support lies in the box `{d | ∀ i, d i < B}`.
* `TauCeti.natDegree_polynomialGraph_lt`: for `1 ≤ B`, if every exponent coordinate in `h.support`
  is `< B`, then `(polynomialGraph k m B h).natDegree < B ^ m`.
* `TauCeti.constantCoeff_comp_polynomialGraph`, `TauCeti.coeff_zero_polynomialGraph`: for `1 ≤ B`,
  `polynomialGraph k m B` commutes with `constantCoeff` (algebraic preservation of the origin);
  this fails at `B = 0` for `2 ≤ m` over a nontrivial semiring
  (`TauCeti.constantCoeff_comp_polynomialGraph_zero_right_ne`).
* `TauCeti.polynomialGraph_toMvPolynomial`, `TauCeti.polynomialGraph_surjective`,
  `TauCeti.surjective_polynomialGraph_iff`: `polynomialGraph k m B` maps `p.toMvPolynomial i` to
  `Polynomial.aeval (X ^ (B ^ i)) p`, so for `0 < m` it is surjective (and over a nontrivial
  semiring it is surjective if and only if `0 < m`, failing at `m = 0` by
  `TauCeti.not_surjective_polynomialGraph_zero`).
* `TauCeti.exists_polynomialGraph_ne_zero`: for any nonzero `h : MvPolynomial (Fin m) k`, there
  exists `B ≥ 2` exceeding all exponent coordinates in `h.support` with
  `polynomialGraph k m B h ≠ 0`.
* `TauCeti.not_injective_polynomialGraph`: for `2 ≤ m` over a nontrivial semiring,
  `polynomialGraph k m B` is not injective.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  proof of Theorem 3.3.7 and Exercise 3.5(a), for the base-`B` Kronecker substitution
  `xᵢ ↦ t ^ (d ^ (i - 1))`.
* M. Kisin and R. Zhou, *Independence of `ℓ` for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945v2, proofs of Corollary 5.2.7 (pp. 52–53) and Proposition 5.3.5
  (p. 54), for the motivating same-field curve-selection step (carried out there via Poonen's
  Bertini theorem rather than Kronecker graphs).
-/

public section

noncomputable section

namespace TauCeti

section CommSemiring

variable {k S : Type*} [CommSemiring k] [CommSemiring S]

/-- The **Kronecker substitution** `k[X_0, …, X_{m-1}] →+* k[T]` sending `X_i` to `T ^ (B ^ i)`
and acting as `Polynomial.C` on coefficients. Variables are indexed from `0`, so `X_0 ↦ T`
whenever `0 < m`. -/
def polynomialGraph (k : Type*) [CommSemiring k] (m B : ℕ) :
    MvPolynomial (Fin m) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C fun i ↦ Polynomial.X ^ (B ^ (i : ℕ))

/-- Explicit unfolding of `polynomialGraph` as `MvPolynomial.eval₂Hom`. -/
lemma polynomialGraph_def (k : Type*) [CommSemiring k] (m B : ℕ) :
    polynomialGraph k m B =
      MvPolynomial.eval₂Hom Polynomial.C fun (i : Fin m) ↦ Polynomial.X ^ (B ^ (i : ℕ)) :=
  (rfl)

/-- `polynomialGraph` acts as `Polynomial.C` on constant polynomials. -/
@[simp]
theorem polynomialGraph_C (m B : ℕ) (a : k) :
    polynomialGraph k m B (MvPolynomial.C a) = Polynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ a

/-- `polynomialGraph` sends the `i`-th variable `X i` to `T ^ (B ^ i)`. -/
@[simp]
theorem polynomialGraph_X (m B : ℕ) (i : Fin m) :
    polynomialGraph k m B (MvPolynomial.X i) = Polynomial.X ^ (B ^ (i : ℕ)) :=
  MvPolynomial.eval₂Hom_X' _ _ i

/-- Precomposing `polynomialGraph` with `MvPolynomial.C` recovers `Polynomial.C`. -/
@[simp]
theorem polynomialGraph_comp_C (m B : ℕ) :
    (polynomialGraph k m B).comp MvPolynomial.C = Polynomial.C :=
  RingHom.ext (polynomialGraph_C m B)

/-- `polynomialGraph k m B` is the ring homomorphism underlying the `k`-algebra Kronecker
substitution `MvPolynomial.aeval (fun i ↦ X ^ (B ^ i))`. -/
@[simp]
theorem coe_aeval_X_pow_eq_polynomialGraph (m B : ℕ) :
    (MvPolynomial.aeval (R := k) (fun i : Fin m ↦
      (Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))) :
      MvPolynomial (Fin m) k →+* Polynomial k) =
      polynomialGraph k m B := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_) <;> simp

/-- Applying `polynomialGraph k m B` agrees with `MvPolynomial.aeval (fun i ↦ X ^ (B ^ i))`. -/
theorem polynomialGraph_apply_eq_aeval (m B : ℕ) (f : MvPolynomial (Fin m) k) :
    polynomialGraph k m B f =
      MvPolynomial.aeval (fun i : Fin m ↦ (Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))) f := by
  rw [← coe_aeval_X_pow_eq_polynomialGraph, RingHom.coe_coe]

/-- `polynomialGraph` sends the monomial `a X ^ d` to `a T ^ (∑ i, d i * B ^ i)`. -/
@[simp]
theorem polynomialGraph_monomial (m B : ℕ) (d : Fin m →₀ ℕ) (a : k) :
    polynomialGraph k m B (MvPolynomial.monomial d a) =
      Polynomial.monomial (Finsupp.weight (fun i : Fin m ↦ B ^ (i : ℕ)) d) a := by
  rw [polynomialGraph_apply_eq_aeval, MvPolynomial.aeval_X_pow_left_monomial]

/-- Evaluating `polynomialGraph k m B f` at `t` in a `k`-algebra `S` evaluates `f` on the power
tuple `i ↦ t ^ (B ^ i)`. -/
@[simp]
theorem aeval_polynomialGraph [Algebra k S] (m B : ℕ) (t : S) (f : MvPolynomial (Fin m) k) :
    Polynomial.aeval t (polynomialGraph k m B f) =
      MvPolynomial.aeval (fun i : Fin m ↦ t ^ (B ^ (i : ℕ))) f := by
  simp [polynomialGraph_apply_eq_aeval, MvPolynomial.comp_aeval_apply]

/-- Evaluating `polynomialGraph k m B f` at `t : k` evaluates `f` at `i ↦ t ^ (B ^ i)`. -/
@[simp]
theorem eval_polynomialGraph (m B : ℕ) (t : k) (f : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B f).eval t = MvPolynomial.eval (fun i : Fin m ↦ t ^ (B ^ (i : ℕ))) f := by
  rw [← Polynomial.coe_aeval_eq_eval, ← MvPolynomial.aeval_eq_eval]
  exact aeval_polynomialGraph m B t f

/-- For `1 ≤ B`, every exponent `B ^ i` is positive, so `polynomialGraph k m B` commutes with
taking constant coefficients (the algebraic counterpart of sending the origin of `𝔸¹` to the
origin of `𝔸^m`). -/
@[simp]
theorem constantCoeff_comp_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) :
    (Polynomial.constantCoeff (R := k)).comp (polynomialGraph k m B) =
      MvPolynomial.constantCoeff := by
  refine MvPolynomial.ringHom_ext (fun a ↦ by simp) (fun i ↦ ?_)
  simp [(pow_ne_zero (i : ℕ) (Nat.one_le_iff_ne_zero.mp hB)).symm]

/-- Typeclass form of `constantCoeff_comp_polynomialGraph` when `[NeZero B]` is in scope. -/
@[simp]
theorem constantCoeff_comp_polynomialGraph_of_neZero (m B : ℕ) [NeZero B] :
    (Polynomial.constantCoeff (R := k)).comp (polynomialGraph k m B) =
      MvPolynomial.constantCoeff :=
  constantCoeff_comp_polynomialGraph (Nat.one_le_iff_ne_zero.mpr (NeZero.ne B))

/-- For `1 ≤ B`, the zeroth coefficient of `polynomialGraph k m B f` is `f.constantCoeff`. -/
@[simp]
theorem coeff_zero_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) (f : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B f).coeff 0 = f.constantCoeff := by
  rw [← Polynomial.constantCoeff_apply]
  simpa using DFunLike.congr_fun (constantCoeff_comp_polynomialGraph (k := k) hB) f

/-- Typeclass form of `coeff_zero_polynomialGraph` when `[NeZero B]` is in scope. -/
@[simp]
theorem coeff_zero_polynomialGraph_of_neZero (m B : ℕ) [NeZero B] (f : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B f).coeff 0 = f.constantCoeff :=
  coeff_zero_polynomialGraph (Nat.one_le_iff_ne_zero.mpr (NeZero.ne B)) f

/-- For `1 ≤ B`, the constant coefficient of `polynomialGraph k m B f` is the constant coefficient
of `f`. -/
theorem constantCoeff_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) (f : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B f).constantCoeff = f.constantCoeff := by
  rw [Polynomial.constantCoeff_apply, coeff_zero_polynomialGraph hB]

/-- For `1 ≤ B`, evaluating `polynomialGraph k m B f` at `0` recovers `f.constantCoeff`. -/
theorem eval_zero_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) (f : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B f).eval 0 = f.constantCoeff := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_zero_polynomialGraph hB]

/-- At `B = 0` and `2 ≤ m` over a nontrivial semiring, `polynomialGraph k m 0` sends `X 1` to
`T ^ (0 ^ 1) = 1` and therefore does not commute with `constantCoeff`. -/
theorem constantCoeff_comp_polynomialGraph_zero_right_ne {m : ℕ} (hm : 2 ≤ m) [Nontrivial k] :
    (Polynomial.constantCoeff (R := k)).comp (polynomialGraph k m 0) ≠
      MvPolynomial.constantCoeff := by
  intro h
  have h1 := DFunLike.congr_fun h (MvPolynomial.X ⟨1, hm⟩)
  simp at h1

/-- `polynomialGraph` is natural with respect to semiring homomorphisms on coefficients. -/
theorem mapRingHom_comp_polynomialGraph (φ : k →+* S) (m B : ℕ) :
    (Polynomial.mapRingHom φ).comp (polynomialGraph k m B) =
      (polynomialGraph S m B).comp (MvPolynomial.map φ) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_) <;> simp

/-- Mapping coefficients along `φ : k →+* S` commutes with `polynomialGraph`. -/
@[simp]
theorem polynomialGraph_map (φ : k →+* S) (m B : ℕ) (f : MvPolynomial (Fin m) k) :
    polynomialGraph S m B (MvPolynomial.map φ f) =
      Polynomial.map φ (polynomialGraph k m B f) := by
  simpa using (DFunLike.congr_fun (mapRingHom_comp_polynomialGraph φ m B) f).symm

/-- In zero variables (`m = 0`), `polynomialGraph k 0 B` factors through `constantCoeff`. -/
theorem polynomialGraph_zero (B : ℕ) :
    polynomialGraph k 0 B = Polynomial.C.comp MvPolynomial.constantCoeff :=
  MvPolynomial.ringHom_ext (fun a ↦ by simp) fun i ↦ Fin.elim0 i

/-- In zero variables (`m = 0`), `polynomialGraph k 0 B f` is the constant polynomial
`C (f.constantCoeff)`. -/
@[simp]
theorem polynomialGraph_zero_apply (B : ℕ) (f : MvPolynomial (Fin 0) k) :
    polynomialGraph k 0 B f = Polynomial.C f.constantCoeff := by
  simpa using DFunLike.congr_fun (polynomialGraph_zero (k := k) B) f

/-- Over a nontrivial semiring, `polynomialGraph k 0 B` has image inside the constant polynomials
and is therefore not surjective (`Polynomial.X` is not in its range). -/
theorem not_surjective_polynomialGraph_zero [Nontrivial k] (B : ℕ) :
    ¬ Function.Surjective (polynomialGraph k 0 B) := by
  intro hsurj
  obtain ⟨f, hf⟩ := hsurj Polynomial.X
  have h1 := congrArg (fun p ↦ p.coeff 1) hf
  simp at h1

/-- In one variable (`m = 1`), `polynomialGraph k 1 B` agrees with Mathlib's canonical isomorphism
`MvPolynomial.uniqueAlgEquiv k (Fin 1)` for every base `B`. -/
theorem polynomialGraph_one_eq_uniqueAlgEquiv (B : ℕ) :
    polynomialGraph k 1 B =
      (MvPolynomial.uniqueAlgEquiv k (Fin 1) : MvPolynomial (Fin 1) k →+* Polynomial k) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · simp
  · rw [Fin.eq_zero i]
    simp [MvPolynomial.uniqueAlgEquiv_apply]

/-- In one variable (`m = 1`), `polynomialGraph k 1 B` is bijective for every base `B`. -/
theorem polynomialGraph_one_bijective (B : ℕ) :
    Function.Bijective (polynomialGraph k 1 B) := by
  rw [polynomialGraph_one_eq_uniqueAlgEquiv]
  simpa using (MvPolynomial.uniqueAlgEquiv k (Fin 1)).bijective

/-! ### Bounded-base injectivity and survival of coefficients -/

/-- **Coefficients survive bounded Kronecker substitution.** If every coordinate `d i` of every
monomial in the support of `h` is `< B`, then for every exponent vector `e` with all `e i < B`, the
coefficient of `T ^ (∑ i, e i * B ^ i)` in `polynomialGraph k m B h` equals `h.coeff e`. -/
theorem polynomialGraph_coeff {k : Type*} [CommSemiring k] {m B : ℕ} (h : MvPolynomial (Fin m) k)
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) (e : Fin m →₀ ℕ) (he : ∀ i, e i < B) :
    (polynomialGraph k m B h).coeff (Finsupp.weight (fun i : Fin m ↦ B ^ (i : ℕ)) e) =
      h.coeff e := by
  rw [polynomialGraph_apply_eq_aeval]
  exact MvPolynomial.coeff_aeval_X_pow_weight (Finsupp.injOn_weight_pow m B)
    (fun d hd ↦ hh d hd) he

/-- `polynomialGraph k m B` is injective on the set of polynomials whose support lies in the box
`{d : Fin m →₀ ℕ | ∀ i, d i < B}`. -/
theorem injOn_polynomialGraph (k : Type*) [CommSemiring k] (m B : ℕ) :
    Set.InjOn (polynomialGraph k m B)
      {h : MvPolynomial (Fin m) k | ∀ d ∈ h.support, ∀ i, d i < B} := by
  intro f hf g hg hfg
  rw [polynomialGraph_apply_eq_aeval, polynomialGraph_apply_eq_aeval] at hfg
  exact MvPolynomial.injOn_aeval_X_pow (Finsupp.injOn_weight_pow m B)
    ((MvPolynomial.mem_restrictSupport_iff (R := k)).mpr hf)
    ((MvPolynomial.mem_restrictSupport_iff (R := k)).mpr hg) hfg

/-- For a polynomial `h` whose support has all exponent coordinates `< B`,
`polynomialGraph k m B h = 0` if and only if `h = 0`. -/
theorem polynomialGraph_eq_zero_iff {m B : ℕ} {h : MvPolynomial (Fin m) k}
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) :
    polynomialGraph k m B h = 0 ↔ h = 0 :=
  ⟨fun h0 ↦ injOn_polynomialGraph k m B hh (by simp) (by rwa [map_zero]),
    fun h0 ↦ by simp [h0]⟩

/-- A nonzero polynomial whose support has all exponent coordinates `< B` has nonzero image under
`polynomialGraph k m B`. -/
theorem polynomialGraph_ne_zero {m B : ℕ} {h : MvPolynomial (Fin m) k} (hh0 : h ≠ 0)
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) :
    polynomialGraph k m B h ≠ 0 :=
  mt (polynomialGraph_eq_zero_iff hh).mp hh0

/-- The support of `polynomialGraph k m B h` is contained in the image of `h.support` under the
base-`B` weight `d ↦ ∑ i, d i * B ^ i`. -/
theorem support_polynomialGraph_subset (m B : ℕ) (h : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B h).support ⊆
      h.support.image (Finsupp.weight fun i : Fin m ↦ B ^ (i : ℕ)) := by
  rw [polynomialGraph_apply_eq_aeval]
  exact MvPolynomial.support_aeval_X_pow_subset _ h

/-- For `1 ≤ B`, if every exponent coordinate in the support of `h` is `< B`, then
`(polynomialGraph k m B h).natDegree < B ^ m`. -/
theorem natDegree_polynomialGraph_lt {m B : ℕ} (hB : 1 ≤ B) {h : MvPolynomial (Fin m) k}
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) :
    (polynomialGraph k m B h).natDegree < B ^ m := by
  rcases eq_or_ne (polynomialGraph k m B h) 0 with h0 | h0
  · simp [h0, Nat.pow_pos (Nat.zero_lt_of_lt hB)]
  · obtain ⟨d, hd, hdeg⟩ := Finset.mem_image.mp
      (support_polynomialGraph_subset m B h (Polynomial.natDegree_mem_support_of_ne_zero h0))
    exact hdeg ▸ Finsupp.weight_pow_lt (hh d hd)

/-! ### Surjectivity, noninjectivity, and existence of an avoiding base -/

/-- Composing `polynomialGraph k m B` with the `i`-th coordinate embedding
`Polynomial.toMvPolynomial i` evaluates univariate polynomials at `X ^ (B ^ i)`. -/
theorem polynomialGraph_comp_toMvPolynomial (m B : ℕ) (i : Fin m) :
    (polynomialGraph k m B).comp
      (Polynomial.toMvPolynomial (R := k) i : Polynomial k →+* MvPolynomial (Fin m) k) =
      (Polynomial.aeval (R := k) ((Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))) :
        Polynomial k →+* Polynomial k) := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_ <;> simp

/-- Applying `polynomialGraph k m B` to `p.toMvPolynomial i` evaluates `p` at `X ^ (B ^ i)`. -/
@[simp]
theorem polynomialGraph_toMvPolynomial (m B : ℕ) (i : Fin m) (p : Polynomial k) :
    polynomialGraph k m B (p.toMvPolynomial i) =
      Polynomial.aeval ((Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))) p := by
  rw [polynomialGraph_apply_eq_aeval, MvPolynomial.aeval_toMvPolynomial]

/-- For `0 < m`, `polynomialGraph k m B` is surjective for every base `B` (including `B = 0` and
`B = 1`), since `X ⟨0, hm⟩` maps to `Polynomial.X`. -/
theorem polynomialGraph_surjective {m : ℕ} (hm : 0 < m) (B : ℕ) :
    Function.Surjective (polynomialGraph k m B) :=
  fun p ↦ ⟨p.toMvPolynomial ⟨0, hm⟩, by simp⟩

/-- Over a nontrivial commutative semiring, `polynomialGraph k m B` is surjective if and only if
`0 < m`. -/
@[simp]
theorem surjective_polynomialGraph_iff [Nontrivial k] (m B : ℕ) :
    Function.Surjective (polynomialGraph k m B) ↔ 0 < m :=
  ⟨fun h ↦ Nat.pos_of_ne_zero fun hm ↦ not_surjective_polynomialGraph_zero B (hm ▸ h),
    fun hm ↦ polynomialGraph_surjective hm B⟩

/-- For any nonzero polynomial `h : MvPolynomial (Fin m) k`, there exists a base `B ≥ 2` exceeding
every coordinate of every exponent in `h.support` such that `polynomialGraph k m B h ≠ 0`. -/
theorem exists_polynomialGraph_ne_zero {m : ℕ} {h : MvPolynomial (Fin m) k} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph k m B h ≠ 0 := by
  have hsupp : ∀ d ∈ h.support, ∀ i, d i < max 2 (h.totalDegree + 1) := fun d hd i ↦
    (Nat.lt_succ_of_le ((Finsupp.le_degree i d).trans
      (MvPolynomial.le_totalDegree hd))).trans_le (le_max_right _ _)
  exact ⟨max 2 (h.totalDegree + 1), le_max_left _ _, hsupp, polynomialGraph_ne_zero hh hsupp⟩

/-- In `m ≥ 2` variables over a nontrivial commutative semiring, `polynomialGraph k m B` is never
injective (`X 1` and `X 0 ^ B` are distinct yet both map to `T ^ B`). -/
theorem not_injective_polynomialGraph {m : ℕ} (hm : 2 ≤ m) [Nontrivial k] (B : ℕ) :
    ¬ Function.Injective (polynomialGraph k m B) := fun hinj ↦
  MvPolynomial.X_ne_X_pow (i := (⟨1, hm⟩ : Fin m)) (j := ⟨0, by omega⟩)
    (by simp [Fin.ext_iff]) B (hinj (by simp))

end CommSemiring

/-! ### Examples -/

section Examples

/-- Over `𝔽_2`, the homogeneous cubic `X₀² X₁ - X₀ X₁²` vanishes on every `𝔽_2`-rational line
`t ↦ (a₀ t, a₁ t)` through the origin, yet survives under `polynomialGraph (ZMod 2) 2 3` as
`T ^ 5 - T ^ 7 ≠ 0`. -/
example :
    let h : MvPolynomial (Fin 2) (ZMod 2) :=
      MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 - MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
    (∀ a : Fin 2 → ZMod 2,
      MvPolynomial.aeval (fun i ↦ Polynomial.C (a i) * Polynomial.X) h = 0) ∧
    polynomialGraph (ZMod 2) 2 3 h ≠ 0 := by
  dsimp only
  refine ⟨fun a ↦ ?_, ?_⟩
  · have ha : ∀ x : ZMod 2, x ^ 2 = x := by decide
    simp [mul_pow, ← Polynomial.C_pow, ha (a 0), ha (a 1)]
    ring
  · intro h0
    have hc := congrArg (fun p ↦ p.coeff 5) h0
    simp [← pow_mul, ← pow_add] at hc

/-- At `B = 2`, the exponent condition `d i < B` is sharp: `X₁ - X₀²` vanishes under
`polynomialGraph ℤ 2 2` (monomial collision `T² - T² = 0`) while surviving at `B = 3`. -/
example :
    let h : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2
    polynomialGraph ℤ 2 2 h = 0 ∧ polynomialGraph ℤ 2 3 h ≠ 0 := by
  refine ⟨by simp, fun h0 ↦ ?_⟩
  have hc := congrArg (fun p ↦ p.coeff 3) h0
  simp at hc

end Examples

end TauCeti
