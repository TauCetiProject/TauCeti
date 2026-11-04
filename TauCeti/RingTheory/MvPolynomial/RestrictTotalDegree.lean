/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.Weight
public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Order.Interval.Set.SuccPred
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import TauCeti.LinearAlgebra.Basis.Pi

/-!
# The submodules of polynomials of bounded total degree

Mathlib's `MvPolynomial.restrictTotalDegree σ R m` is the submodule of polynomials of total degree
at most `m`. This file records that these submodules increase with `m`, that a monomial of degree
at most `m` lies in the `m`-th one, and that the `m`-th one is spanned by those monomials, so that
a linear statement about polynomials of bounded degree reduces to monomials. These monomials form
a basis whose coordinates are the coefficients, giving finite coordinates on tuples of
bounded-degree polynomials; evaluating such tuples is faithful over an infinite integral domain,
by Mathlib's `MvPolynomial.funext`. Raising the degree bound leaves the evaluation unchanged and
zero-pads the coordinates. The homogeneous polynomials of degree `d` have the analogous
coordinates, from `TauCeti.homogeneousMonomialBasis`, and evaluation, and their inclusion among
the polynomials of total degree at most `d` again zero-pads the coordinates. As a spanning family,
the monomials may be replaced by products `∏ᵢ Sₖᵢ(Xᵢ)` of the members of a polynomial sequence
`S` in the separate variables, for instance the integer-valued binomial polynomials.

## Main results

* `MvPolynomial.restrictTotalDegree_mono`: the submodules increase with the degree bound.
* `MvPolynomial.monomial_mem_restrictTotalDegree`: a monomial of degree at most `m` has total
  degree at most `m`.
* `MvPolynomial.restrictTotalDegree_eq_span`: the monomials of degree at most `m` span the
  polynomials of total degree at most `m`.
* `MvPolynomial.basisRestrictTotalDegree`: the monomial basis of the polynomials of total degree
  at most `m`, whose coordinates are the coefficients.
* `MvPolynomial.boundedCoefficientEquiv`: monomial coefficients as finite coordinates on tuples of
  bounded-degree polynomials.
* `MvPolynomial.tupleEvaluation`, `MvPolynomial.tupleEvaluation_injective`: evaluation of tuples
  of polynomials from a submodule as vector-valued functions is linear, and injective over an
  infinite integral domain, for instance for the polynomials of bounded total degree.
* `MvPolynomial.boundedCoefficientEquiv_inclusion_comp_eq_extendByZero`: including a submodule of
  polynomials supported on a set of exponents of degree at most `e` among the polynomials of total
  degree at most `e` extends the coefficients by zero.
* `MvPolynomial.boundedCoefficientEquiv_inclusion_comp`: raising the degree bound extends the
  finite coefficient coordinates by zero.
* `MvPolynomial.boundedCoefficientEquiv_inclusion_comp_homogeneous`: including homogeneous
  polynomials in a bounded-degree space extends their coordinates by zero.
* `MvPolynomial.aeval_mem_restrictTotalDegree`: substituting linear forms for the variables does
  not raise the total degree.
* `MvPolynomial.span_prod_aeval_X_le`: products of a triangular family of one-variable polynomials
  in the separate variables lie in the span of the products of the original family.
* `Polynomial.Sequence.span_prod_aeval_X_eq_restrictTotalDegree`: the products `∏ᵢ Sₖᵢ(Xᵢ)` of
  a polynomial sequence with unit leading coefficients span the polynomials of bounded degree.
* `Module.Basis.apply_mem_of_monomial_degree_le`: a bilinear map takes values in a submodule on
  bounded-degree polynomials if it does so on basis vectors and bounded-degree monomials.
* `Module.Basis.constr_X_mul_mem_restrictTotalDegree`: multiplication by a linear form raises
  total degree by at most one.
-/

public section

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

variable (σ R) in
/-- The polynomials of total degree at most `m` increase with `m`. -/
theorem restrictTotalDegree_mono : Monotone (restrictTotalDegree σ R) :=
  fun _ _ h p hp ↦
    (mem_restrictTotalDegree σ _ p).2 (((mem_restrictTotalDegree σ _ p).1 hp).trans h)

/-- A polynomial of total degree at most `d` has zero coefficients at exponents of degree
above `d`. -/
theorem coeff_eq_zero_of_mem_restrictTotalDegree {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictTotalDegree σ R d) {a : σ →₀ ℕ} (ha : d < a.degree) :
    p.coeff a = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  rw [← Finsupp.degree_apply]
  exact ((mem_restrictTotalDegree σ d p).mp hp).trans_lt ha

/-- A monomial whose exponent has degree at most `m` has total degree at most `m`. -/
theorem monomial_mem_restrictTotalDegree {s : σ →₀ ℕ} {m : ℕ} (h : s.degree ≤ m) (r : R) :
    monomial s r ∈ restrictTotalDegree σ R m :=
  (mem_restrictTotalDegree σ m _).2 <| (totalDegree_monomial_le s r).trans <| by
    simpa [Finsupp.sum, Finsupp.degree_apply] using h

variable (σ R) in
/-- The polynomials of total degree at most `m` are those supported on exponents of degree at
most `m`. -/
theorem restrictTotalDegree_eq_restrictSupport (m : ℕ) :
    restrictTotalDegree σ R m = restrictSupport R {s : σ →₀ ℕ | s.degree ≤ m} := by
  have hs : {s : σ →₀ ℕ | (s.sum fun _ e ↦ e) ≤ m} = {s | s.degree ≤ m} := by
    ext s
    simp [Finsupp.sum, Finsupp.degree_apply]
  rw [restrictTotalDegree, hs]

variable (σ R) in
/-- The polynomials of total degree at most `m` are spanned by the monomials of degree at most
`m`. -/
theorem restrictTotalDegree_eq_span (m : ℕ) :
    restrictTotalDegree σ R m =
      Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ m}) := by
  rw [restrictTotalDegree_eq_restrictSupport, restrictSupport_eq_span]

variable (σ R) in
/-- The monomial basis of the polynomials of total degree at most `m`, indexed by exponents of
degree at most `m`. -/
noncomputable def basisRestrictTotalDegree (m : ℕ) :
    Module.Basis {s : σ →₀ ℕ // s.degree ≤ m} R (restrictTotalDegree σ R m) :=
  (basisRestrictSupport R {s : σ →₀ ℕ | s.degree ≤ m}).map
    (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R m).symm)

/-- The coordinate of a bounded-degree polynomial in the monomial basis is its coefficient. -/
@[simp]
theorem basisRestrictTotalDegree_repr_apply (m : ℕ) (p : restrictTotalDegree σ R m)
    (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m).repr p s = (p : MvPolynomial σ R).coeff s := (rfl)

/-- A monomial basis vector of the bounded-degree polynomials is the corresponding monomial. -/
@[simp]
theorem coe_basisRestrictTotalDegree (m : ℕ) (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m s : MvPolynomial σ R) = monomial s.1 1 := by
  classical
  have h : basisRestrictTotalDegree σ R m s =
      ⟨monomial s.1 1, monomial_mem_restrictTotalDegree s.2 1⟩ := by
    refine (basisRestrictTotalDegree σ R m).repr.injective (Finsupp.ext fun t ↦ ?_)
    simp [Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]
  rw [h]

section Coordinates

variable {J : Type*}

variable (σ R J) in
/-- Monomial coefficients identify `J`-indexed tuples of polynomials of total degree at most `d`
with functions on the pairs of an index and an exponent of degree at most `d`. For finitely many
variables and indices this index type is finite, so these are finite coordinates. -/
noncomputable def boundedCoefficientEquiv [Finite σ] (d : ℕ) :
    (J → restrictTotalDegree σ R d) ≃ₗ[R] (J × {s : σ →₀ ℕ // s.degree ≤ d} → R) :=
  (basisRestrictTotalDegree σ R d).piEquivFun J

/-- A finite coefficient coordinate is the corresponding monomial coefficient of an entry. -/
@[simp] theorem boundedCoefficientEquiv_apply [Finite σ] {d : ℕ}
    (v : J → restrictTotalDegree σ R d) (i : J × {s : σ →₀ ℕ // s.degree ≤ d}) :
    boundedCoefficientEquiv σ R J d v i = (v i.1 : MvPolynomial σ R).coeff i.2 := by
  simp [boundedCoefficientEquiv]

/-- The tuple with prescribed finite coefficient coordinates has those monomial coefficients. -/
@[simp] theorem coeff_boundedCoefficientEquiv_symm_apply [Finite σ] {d : ℕ}
    (a : J × {s : σ →₀ ℕ // s.degree ≤ d} → R) (j : J) (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    (((boundedCoefficientEquiv σ R J d).symm a j : restrictTotalDegree σ R d) :
      MvPolynomial σ R).coeff s = a (j, s) :=
  (basisRestrictTotalDegree σ R d).repr_piEquivFun_symm_apply a j s

variable (J) in
/-- Evaluation of a tuple of polynomials from a submodule `S` as a vector-valued function on
points. It is linear in the tuple. -/
noncomputable def tupleEvaluation (S : Submodule R (MvPolynomial σ R)) :
    (J → S) →ₗ[R] (σ → R) → J → R where
  toFun v x j := eval x (v j : MvPolynomial σ R)
  map_add' v w := by
    funext x j
    simp
  map_smul' a v := by
    funext x j
    simp

/-- Coordinate evaluation of a tuple of polynomials from a submodule. -/
@[simp] theorem tupleEvaluation_apply {S : Submodule R (MvPolynomial σ R)} (v : J → S)
    (x : σ → R) (j : J) :
    tupleEvaluation J S v x j = eval x (v j : MvPolynomial σ R) := (rfl)

/-- Over an infinite integral domain, tuples of polynomials from a submodule are determined by
the functions they define: the evaluation map is faithful. -/
theorem tupleEvaluation_injective {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    (S : Submodule R (MvPolynomial σ R)) : Function.Injective (tupleEvaluation J S) :=
  fun _ _ h =>
    _root_.funext fun j => Subtype.ext <| MvPolynomial.funext fun x => congrFun (congrFun h x) j

/-- Including a tuple of polynomials into a larger submodule does not change the function it
defines. -/
@[simp] theorem tupleEvaluation_inclusion_comp {S T : Submodule R (MvPolynomial σ R)}
    (h : S ≤ T) (v : J → S) :
    tupleEvaluation J T (Submodule.inclusion h ∘ v) = tupleEvaluation J S v := (rfl)

/-- Let `p` be a submodule of the polynomials of total degree at most `e` whose members have zero
coefficients at the exponents outside `Q`, all exponents in `Q` having degree at most `e`.
Including a tuple from `p` among the polynomials of total degree at most `e` extends its
coefficients at the exponents in `Q` by zero. -/
theorem boundedCoefficientEquiv_inclusion_comp_eq_extendByZero [Finite σ]
    {p : Submodule R (MvPolynomial σ R)} {e : ℕ} (hp : p ≤ restrictTotalDegree σ R e)
    {Q : (σ →₀ ℕ) → Prop} (hQ : ∀ s, Q s → s.degree ≤ e)
    (h0 : ∀ x ∈ p, ∀ s, ¬Q s → x.coeff s = 0) (v : J → p) :
    boundedCoefficientEquiv σ R J e (Submodule.inclusion hp ∘ v) =
      Function.ExtendByZero.linearMap R R
        (Prod.map (id : J → J) (Subtype.impEmbedding Q (fun s => s.degree ≤ e) hQ))
        (fun i : J × Subtype Q => (v i.1 : MvPolynomial σ R).coeff i.2) := by
  have hinj : Function.Injective
      (Prod.map (id : J → J) (Subtype.impEmbedding Q (fun s => s.degree ≤ e) hQ)) :=
    Function.injective_id.prodMap (Subtype.impEmbedding _ _ _).injective
  ext ⟨j, s, hs'⟩
  rw [Function.ExtendByZero.linearMap_apply]
  by_cases hs : Q s
  · -- The index `(j, ⟨s, hs'⟩)` is the image of `(j, ⟨s, hs⟩)` by definition.
    rw [show ((j, ⟨s, hs'⟩) : J × {s : σ →₀ ℕ // s.degree ≤ e}) =
      Prod.map id (Subtype.impEmbedding Q _ hQ) (j, ⟨s, hs⟩) from rfl, hinj.extend_apply]
    simp
  · rw [Function.extend_apply' _ _ _ ?_, Pi.zero_apply, boundedCoefficientEquiv_apply,
      Function.comp_apply, Submodule.coe_inclusion]
    · exact h0 _ (v j).2 s hs
    · rintro ⟨⟨j', s', hs''⟩, he⟩
      exact hs (by cases he; exact hs'')

/-- Raising the degree bound from `d` to `d'` zero-pads the finite coefficient coordinates: they
are extended by zero along the inclusion of index types, so the new coordinates at exponents of
degree above `d` vanish. -/
theorem boundedCoefficientEquiv_inclusion_comp [Finite σ] {d d' : ℕ} (h : d ≤ d')
    (v : J → restrictTotalDegree σ R d) :
    boundedCoefficientEquiv σ R J d' (Submodule.inclusion (restrictTotalDegree_mono σ R h) ∘ v) =
      Function.ExtendByZero.linearMap R R (Prod.map (id : J → J)
          (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ d) (fun s => s.degree ≤ d')
            fun _ hs => hs.trans h))
        (boundedCoefficientEquiv σ R J d v) := by
  rw [boundedCoefficientEquiv_inclusion_comp_eq_extendByZero _ (Q := fun s => s.degree ≤ d)
    (fun _ hs => hs.trans h)
    (fun _ hx _ hs => coeff_eq_zero_of_mem_restrictTotalDegree hx (not_le.1 hs)) v]
  congr 1
  ext i
  exact (boundedCoefficientEquiv_apply v i).symm

/-! ### Homogeneous coordinates

The homogeneous polynomials of degree `d` lie among those of total degree at most `d`. Their
monomial coordinates `(homogeneousMonomialBasis d).piEquivFun J` are indexed by the exponents of
degree exactly `d`, their evaluation is `tupleEvaluation`, and including them in a bounded-degree
space extends these coordinates by zero. -/

variable (σ R) in
/-- A homogeneous polynomial of degree `d` has total degree at most every `e ≥ d`. -/
theorem homogeneousSubmodule_le_restrictTotalDegree {d e : ℕ} (h : d ≤ e) :
    homogeneousSubmodule σ R d ≤ restrictTotalDegree σ R e := fun p hp =>
  (mem_restrictTotalDegree σ e p).2 <|
    ((mem_homogeneousSubmodule d p).1 hp).totalDegree_le.trans h

/-- Including homogeneous polynomials of degree `d` in the polynomials of total degree at most
`e ≥ d` extends their coefficient coordinates by zero along the inclusion of exponents of degree
`d` among those of degree at most `e`. -/
theorem boundedCoefficientEquiv_inclusion_comp_homogeneous [Finite σ] {d e : ℕ} (h : d ≤ e)
    (v : J → homogeneousSubmodule σ R d) :
    boundedCoefficientEquiv σ R J e
        (Submodule.inclusion (homogeneousSubmodule_le_restrictTotalDegree σ R h) ∘ v) =
      Function.ExtendByZero.linearMap R R (Prod.map (id : J → J)
          (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree = d) (fun s => s.degree ≤ e)
            fun _ hs => hs.le.trans h))
        ((TauCeti.homogeneousMonomialBasis d).piEquivFun J v) := by
  rw [boundedCoefficientEquiv_inclusion_comp_eq_extendByZero _ (Q := fun s => s.degree = d)
    (fun _ hs => hs.le.trans h)
    (fun x hx _ hs => ((mem_homogeneousSubmodule d x).1 hx).coeff_eq_zero hs) v]
  congr 1
  ext i
  simp

end Coordinates

/-- Substituting polynomials of total degree at most one, for instance linear forms, for the
variables does not raise the total degree. -/
theorem aeval_mem_restrictTotalDegree {τ : Type*} {f : σ → MvPolynomial τ R}
    (hf : ∀ i, (f i).totalDegree ≤ 1) {m : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictTotalDegree σ R m) : aeval f p ∈ restrictTotalDegree τ R m := by
  rw [restrictTotalDegree_eq_span] at hp
  induction hp using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨s, hs, rfl⟩ := h
    rw [mem_restrictTotalDegree, aeval_monomial, map_one, one_mul, Finsupp.prod]
    calc (∏ i ∈ s.support, f i ^ s i).totalDegree
        ≤ ∑ i ∈ s.support, (f i ^ s i).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum fun i _ ↦
          (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))
      _ ≤ m := hs
  | zero => simp
  | add p q _ _ hp hq => simpa using add_mem hp hq
  | smul a p _ hp => simpa using Submodule.smul_mem _ a hp

open Polynomial in
/-- If each `q k` with `k ≤ m` is a combination of the `p j` with `j ≤ k`, then the products
`∏ᵢ q_{τ i}(Xᵢ)` with `τ.degree ≤ m` lie in the span of the products `∏ᵢ p_{τ i}(Xᵢ)` with
`τ.degree ≤ m`. -/
theorem span_prod_aeval_X_le {σ R : Type*} [Fintype σ] [CommSemiring R] {p q : ℕ → R[X]} {m : ℕ}
    (h : ∀ k ≤ m, q k ∈ Submodule.span R (p '' Set.Iic k)) :
    Submodule.span R ((fun τ : σ →₀ ℕ ↦ ∏ i, Polynomial.aeval (X (R := R) i) (q (τ i))) ''
        {τ | τ.degree ≤ m}) ≤
      Submodule.span R ((fun τ : σ →₀ ℕ ↦ ∏ i, Polynomial.aeval (X (R := R) i) (p (τ i))) ''
        {τ | τ.degree ≤ m}) := by
  classical
  rw [Submodule.span_le]
  rintro _ ⟨τ, hτ, rfl⟩
  -- Each factor lies in the span of the `p j (Xᵢ)` with `j ≤ τ i`.
  have hmem (i : σ) : Polynomial.aeval (X (R := R) i) (q (τ i)) ∈
      Submodule.span R ((Polynomial.aeval (X (R := R) i)).toLinearMap '' (p '' Set.Iic (τ i))) := by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem (h _ ((Finsupp.le_degree i τ).trans hτ))
  have hprod : ∏ i, Polynomial.aeval (X (R := R) i) (q (τ i)) ∈ ∏ i,
      Submodule.span R ((Polynomial.aeval (X (R := R) i)).toLinearMap '' (p '' Set.Iic (τ i))) := by
    induction (Finset.univ : Finset σ) using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      exact Submodule.one_le.1 le_rfl
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact Submodule.mul_mem_mul (hmem i) ih
  rw [Submodule.prod_span] at hprod
  refine Submodule.span_mono ?_ hprod
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).1 hx
  simp only [Finset.mem_univ, forall_const, Set.image_image] at hg
  choose j hj hgj using fun i ↦ @hg i
  refine ⟨Finsupp.equivFunOnFinite.symm j, ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Finsupp.coe_equivFunOnFinite_symm]
    exact (Finset.sum_le_sum fun i _ ↦ Set.mem_Iic.1 (hj i)).trans
      ((Finsupp.degree_eq_sum τ).symm.le.trans hτ)
  · simp [← hgj]

end MvPolynomial

namespace Polynomial.Sequence

open Submodule

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- **Change of basis to products of a polynomial sequence.** If the leading coefficients of
`S₀, …, Sₘ` are units, then the products `∏ᵢ S_{τ i}(Xᵢ)` over the exponents `τ` of degree at
most `m` span the polynomials of total degree at most `m`, exactly as the monomials `X^τ` do. -/
theorem span_prod_aeval_X_eq_restrictTotalDegree (S : Sequence R) {m : ℕ}
    (hS : ∀ k ≤ m, IsUnit (S k).leadingCoeff) :
    span R ((fun τ : σ →₀ ℕ ↦ ∏ i, aeval (MvPolynomial.X (R := R) i) (S (τ i))) ''
        {τ | τ.degree ≤ m}) = MvPolynomial.restrictTotalDegree σ R m := by
  classical
  have hmon : MvPolynomial.restrictTotalDegree σ R m =
      span R ((fun τ : σ →₀ ℕ ↦ ∏ i, aeval (MvPolynomial.X (R := R) i) ((X : R[X]) ^ (τ i))) ''
        {τ | τ.degree ≤ m}) := by
    rw [MvPolynomial.restrictTotalDegree_eq_span]
    congr! with τ
    simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  rw [hmon]
  refine le_antisymm (MvPolynomial.span_prod_aeval_X_le fun k _ ↦ ?_)
    (MvPolynomial.span_prod_aeval_X_le fun k hk ↦ ?_)
  · have : S k ∈ degreeLE R k := mem_degreeLE.2 (S.degree_eq k).le
    rwa [degreeLE_eq_span_X_pow, Finset.coe_image, Finset.coe_range,
      Set.Iio_add_one_eq_Iic] at this
  · rw [S.span_degreeLE fun i hi ↦ hS i (hi.trans hk), mem_degreeLE]
    exact degree_X_pow_le k

end Polynomial.Sequence

namespace Module.Basis

open MvPolynomial

section Bilinear

variable {σ κ R L M : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]
  [AddCommMonoid M] [Module R M]

/-- A bilinear map out of a module and a polynomial algebra takes values in a submodule on
polynomials of total degree at most `d` if it does so on basis vectors and monomials of degree at
most `d`. -/
theorem apply_mem_of_monomial_degree_le (b : Basis κ R L)
    (Φ : L →ₗ[R] MvPolynomial σ R →ₗ[R] M) (N : Submodule R M) (d : ℕ)
    (h : ∀ (l : κ) (s : σ →₀ ℕ), s.degree ≤ d → Φ (b l) (monomial s 1) ∈ N)
    (x : L) {p : MvPolynomial σ R} (hp : p ∈ restrictTotalDegree σ R d) : Φ x p ∈ N := by
  have hle : Submodule.map₂ Φ (Submodule.span R (Set.range b))
      (Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ d})) ≤ N := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩
    exact h l s hs
  rw [b.span_eq, ← restrictTotalDegree_eq_span] at hle
  exact Submodule.map₂_le.1 hle x Submodule.mem_top p hp

end Bilinear

variable {ι R L : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]

/-- Multiplying by the linear form attached to `x` in the basis `b` raises total degree by at
most one. -/
theorem constr_X_mul_mem_restrictTotalDegree (b : Basis ι R L) {d : ℕ} (x : L)
    {p : MvPolynomial ι R} (hp : p ∈ restrictTotalDegree ι R d) :
    b.constr R X x * p ∈ restrictTotalDegree ι R (d + 1) := by
  refine b.apply_mem_of_monomial_degree_le
    ((LinearMap.mul R _).comp (b.constr R X)) _ d (fun l σ hσ ↦ ?_) x hp
  have hm : (monomial (Finsupp.single l 1 + σ) 1 : MvPolynomial ι R) ∈
      restrictTotalDegree ι R (d + 1) :=
    monomial_mem_restrictTotalDegree (by simpa [Nat.one_add] using hσ) 1
  simpa [monomial_single_add] using hm

end Module.Basis
