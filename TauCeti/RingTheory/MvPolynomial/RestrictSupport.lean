/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomials with restricted support

Mathlib's `MvPolynomial.basisRestrictSupport R s` is the basis of `MvPolynomial.restrictSupport R s`
indexed by `s`. This file records its coordinates (the coefficients) and its basis vectors (the
monomials with coefficient `1`), and from them the basic theory of these finite polynomial spaces:
coefficient extensionality, the rank, change of coefficients along a ring map, and the comparison
with the native degree spaces.

## Main results

* `MvPolynomial.eq_of_mem_restrictSupport_of_coeff_eq`: two polynomials supported on `s` with
  the same coefficients on `s` are equal.
* `MvPolynomial.finrank_restrictSupport`, `MvPolynomial.finrank_restrictSupport_finset`: the
  rank of `restrictSupport R T` over a ring with the strong rank condition is the number of
  exponents in `T`.
* `MvPolynomial.mapRestrictSupport`: changing coefficients along `f : R →+* S`, as an
  `f`-semilinear map `restrictSupport R s → restrictSupport S s` carrying the monomial basis to the
  monomial basis.
* `MvPolynomial.mem_restrictSupport_iff_degreeOf_le`: the degree box `{μ | ∀ i, μ i ≤ d i}`
  supports exactly the polynomials with `degreeOf i ≤ d i`. Mathlib's `restrictDegree σ R m` is by
  definition the box of the constant bound `m`. The total-degree ball is
  `MvPolynomial.restrictTotalDegree_eq_restrictSupport`
  (`TauCeti/RingTheory/MvPolynomial/RestrictTotalDegree.lean`).
* `MvPolynomial.degreeOf_lt_of_mem_restrictSupport`: a support restriction bounding the exponent
  of one variable bounds `degreeOf`. Conversely, `MvPolynomial.mem_restrictSupport_of_degreeOf_lt`
  gives a support restriction from a strict partial-degree bound.
* `MvPolynomial.uniqueAlgEquiv_mem_degreeLT_iff`, `MvPolynomial.map_restrictSupport_uniqueAlgEquiv`:
  in one variable, the box `{μ | μ default < N}` corresponds to `Polynomial.degreeLT R N` under
  `MvPolynomial.uniqueAlgEquiv`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {s : Set (σ →₀ ℕ)}

/-- The coordinates of a polynomial in `basisRestrictSupport` are its coefficients. -/
@[simp]
theorem basisRestrictSupport_repr_apply (p : restrictSupport R s) (c : s) :
    (basisRestrictSupport R s).repr p c = (p : MvPolynomial σ R).coeff c :=
  -- `basisRestrictSupport` is defined through `AddMonoidAlgebra.supportedEquivFinsupp`, which
  -- reads off coefficients.
  rfl

/-- The basis vectors of `basisRestrictSupport` are the monomials with coefficient `1`. -/
@[simp]
theorem basisRestrictSupport_apply_coe (c : s) :
    (basisRestrictSupport R s c : MvPolynomial σ R) = monomial (c : σ →₀ ℕ) 1 := by
  classical
  have hc : monomial (c : σ →₀ ℕ) (1 : R) ∈ restrictSupport R s := by simp
  suffices basisRestrictSupport R s c = ⟨_, hc⟩ from congrArg Subtype.val this
  refine (basisRestrictSupport R s).repr.injective (Finsupp.ext fun d ↦ ?_)
  simp [Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]

/-- Two polynomials supported on `s` whose coefficients agree on `s` are equal. -/
theorem eq_of_mem_restrictSupport_of_coeff_eq {p q : MvPolynomial σ R}
    (hp : p ∈ restrictSupport R s) (hq : q ∈ restrictSupport R s)
    (h : ∀ μ ∈ s, p.coeff μ = q.coeff μ) : p = q := by
  ext μ
  by_cases hμ : μ ∈ s
  · exact h μ hμ
  · have h0 {r : MvPolynomial σ R} (hr : r ∈ restrictSupport R s) : r.coeff μ = 0 := by
      by_contra hc
      exact hμ (hr (mem_support_iff.2 hc))
    rw [h0 hp, h0 hq]

/-- Elements of `restrictSupport R s` are determined by their coefficients on `s`. -/
theorem restrictSupport_ext {p q : restrictSupport R s}
    (h : ∀ μ ∈ s, (p : MvPolynomial σ R).coeff μ = (q : MvPolynomial σ R).coeff μ) : p = q :=
  Subtype.ext <| eq_of_mem_restrictSupport_of_coeff_eq p.2 q.2 h

variable (R s) in
/-- The rank of `restrictSupport R s` is the number of exponents in `s` (`0` if `s` is infinite).
-/
theorem finrank_restrictSupport [StrongRankCondition R] :
    Module.finrank R (restrictSupport R s) = Nat.card s :=
  Module.finrank_eq_nat_card_basis (basisRestrictSupport R s)

variable (R) in
/-- The rank of the polynomials supported on a finite set `T` of exponents is `#T`. -/
@[simp]
theorem finrank_restrictSupport_finset [StrongRankCondition R] (T : Finset (σ →₀ ℕ)) :
    Module.finrank R (restrictSupport R (T : Set (σ →₀ ℕ))) = T.card := by
  rw [finrank_restrictSupport, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- Changing coefficients along a ring map preserves a support restriction. -/
theorem map_mem_restrictSupport {S : Type*} [CommSemiring S] (f : R →+* S)
    {p : MvPolynomial σ R} (hp : p ∈ restrictSupport R s) : map f p ∈ restrictSupport S s :=
  (mem_restrictSupport_iff S).2 ((Finset.coe_subset.2 (support_map_subset f p)).trans hp)

variable (s) in
/-- Changing the coefficients of the polynomials supported on `s` along a ring map
`f : R →+* S`, as an `f`-semilinear map. -/
noncomputable def mapRestrictSupport {S : Type*} [CommSemiring S] (f : R →+* S) :
    restrictSupport R s →ₛₗ[f] restrictSupport S s where
  toFun p := ⟨map f p, map_mem_restrictSupport f p.2⟩
  map_add' p q := Subtype.ext (map_add (map f) (p : MvPolynomial σ R) q)
  map_smul' a p := Subtype.ext <| by simp [smul_eq_C_mul]

@[simp]
theorem coe_mapRestrictSupport_apply {S : Type*} [CommSemiring S] (f : R →+* S)
    (p : restrictSupport R s) : (mapRestrictSupport s f p : MvPolynomial σ S) = map f p :=
  (rfl)

/-- Changing coefficients sends the monomial basis to the monomial basis. -/
@[simp]
theorem mapRestrictSupport_basisRestrictSupport {S : Type*} [CommSemiring S] (f : R →+* S)
    (c : s) : mapRestrictSupport s f (basisRestrictSupport R s c) = basisRestrictSupport S s c :=
  Subtype.ext <| by simp

/-- The degree box `{μ | ∀ i, μ i ≤ d i}` supports exactly the polynomials of partial degrees
`degreeOf i ≤ d i`. -/
theorem mem_restrictSupport_iff_degreeOf_le {d : σ → ℕ} {p : MvPolynomial σ R} :
    p ∈ restrictSupport R {μ | ∀ i, μ i ≤ d i} ↔ ∀ i, p.degreeOf i ≤ d i := by
  simp only [mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq,
    degreeOf_le_iff]
  exact ⟨fun h i μ hμ ↦ h μ hμ i, fun h μ hμ i ↦ h i μ hμ⟩

/-- If every exponent in `s` has `i`-th entry below `B > 0`, then so does the `i`-th partial degree
of every polynomial supported on `s`. -/
theorem degreeOf_lt_of_mem_restrictSupport {p : MvPolynomial σ R} (hp : p ∈ restrictSupport R s)
    {i : σ} {B : ℕ} (hB : 0 < B) (hs : ∀ μ ∈ s, μ i < B) : p.degreeOf i < B :=
  (degreeOf_lt_iff hB).2 fun μ hμ ↦ hs μ (hp hμ)

/-- In one variable, the polynomials supported on the box `{μ | μ default < N}` are those whose
image under `uniqueAlgEquiv` has degree below `N`. -/
theorem uniqueAlgEquiv_mem_degreeLT_iff [Unique σ] {N : ℕ} {p : MvPolynomial σ R} :
    uniqueAlgEquiv R σ p ∈ Polynomial.degreeLT R N ↔
      p ∈ restrictSupport R {μ : σ →₀ ℕ | μ default < N} := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero, mem_restrictSupport_iff]
  simp only [coeff_uniqueAlgEquiv]
  refine ⟨fun h μ hμ ↦ ?_, fun h m hm ↦ ?_⟩
  · by_contra hN
    have hμ0 := h (μ default) (not_lt.1 hN)
    rw [← Finsupp.unique_single μ] at hμ0
    exact mem_support_iff.1 hμ hμ0
  · by_contra hc
    have := h (mem_support_iff.2 hc)
    simp only [Set.mem_ofPred_eq, Finsupp.single_eq_same] at this
    omega

/-- In one variable, the box `{μ | μ default < N}` corresponds to `Polynomial.degreeLT R N` under
`uniqueAlgEquiv`. -/
theorem map_restrictSupport_uniqueAlgEquiv [Unique σ] (N : ℕ) :
    (restrictSupport R {μ : σ →₀ ℕ | μ default < N}).map (uniqueAlgEquiv R σ).toLinearMap =
      Polynomial.degreeLT R N := by
  ext q
  rw [Submodule.mem_map_equiv, ← uniqueAlgEquiv_mem_degreeLT_iff]
  exact iff_of_eq (congrArg (· ∈ _) ((uniqueAlgEquiv R σ).apply_symm_apply q))

/-- A polynomial of `n`-degree below `d` is supported on the exponents `μ` with `μ n < d`. -/
theorem mem_restrictSupport_of_degreeOf_lt {n : σ} {d : ℕ} {F : MvPolynomial σ R}
    (hF : F.degreeOf n < d) : F ∈ restrictSupport R {μ : σ →₀ ℕ | μ n < d} :=
  (mem_restrictSupport_iff (R := R)).mpr fun μ hμ ↦
    (degreeOf_lt_iff ((Nat.zero_le _).trans_lt hF)).mp hF μ hμ

/-! ### Examples -/

/-- Mathlib's `restrictDegree σ R m` is by definition the degree box of the constant bound `m`, so
it consists of the polynomials all of whose partial degrees are at most `m`. -/
example {m : ℕ} {p : MvPolynomial σ R} : p ∈ restrictDegree σ R m ↔ ∀ i, p.degreeOf i ≤ m :=
  mem_restrictSupport_iff_degreeOf_le

end MvPolynomial
