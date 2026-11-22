/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Multiset.Sort
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Data.Finsupp.Multiset
public import TauCeti.Data.Multiset.Sort
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import TauCeti.RingTheory.GradedAlgebra.PositivePart
public import TauCeti.RingTheory.GradedAlgebra.Supercommutativity

/-!
# Free graded-commutative algebras

The free graded-commutative algebra `ΛV = Sym(V_even) ⊗ Λ(V_odd)` on a graded vector space `V`
is the underlying algebra of a Sullivan algebra in rational homotopy theory. This file presents it
by homogeneous generators: an internally `ℤ`-graded `K`-algebra `A` is free graded-commutative on
`x : ι → A`, with `x i` of degree `deg i : ℕ` and `ι` linearly ordered, when the generators
commute up to the Koszul sign `x i * x j = (-1) ^ (deg i * deg j) • (x j * x i)` and the standard
monomials `x_{i₁}^{f i₁} ⋯ x_{i_k}^{f i_k}`, `i₁ < ⋯ < i_k`, over the exponent vectors `f` (finitely
supported, with `f i ≤ 1` when `deg i` is odd) form a basis of `A`.

The main result is the universal property: when `2` is invertible in `K`, an algebra map out of
`ΛV` may send the generators to any elements of a graded-commutative algebra in the same degrees,
and is determined by these images. The hypothesis on `2` is needed: over `𝔽₂`, where every Koszul
sign is `1`, the polynomial ring `𝔽₂[e]` with `e` in degree `1` satisfies the definition on the
generators `e` and `e²`, of degrees `1` and `2`, while no algebra map out of it sends `e` to `u`
and `e²` to `v` in the graded-commutative algebra `𝔽₂[u, v]/(u²)`, `|u| = 1`, `|v| = 2`.

## Main definitions

* `TauCeti.standardMonomial x f`: the ordered product of the `x i` with multiplicities `f i`.
* `TauCeti.ExponentVector deg`: the exponent vectors of the standard monomials.
* `TauCeti.IsFreeGradedCommutative 𝒜 x deg`: `A` is free graded-commutative on the `x i`.
* `TauCeti.IsFreeGradedCommutative.basis`: the basis of standard monomials.
* `TauCeti.IsFreeGradedCommutative.lift`: the algebra map out of `A` sending `x i` to `b i`, for
  any `b i` which commute up to the Koszul sign.
* `TauCeti.IsFreeGradedCommutative.indecomposablesBasis`: when `2` is invertible and every
  generator has positive degree, the basis of the indecomposables `A⁺ ⧸ A⁺ · A⁺` given by the
  classes of the generators, so that the indecomposables of `ΛV` are `V`.

## Main results

* `TauCeti.mul_standardMonomial`: a generator times a standard monomial is the Koszul sign times a
  standard monomial; `TauCeti.mul_standardMonomial_eq_zero`: it is zero when the generator
  squares to zero and already occurs.
* `TauCeti.standardMonomial_mem`: standard monomials in homogeneous elements are homogeneous.
* `TauCeti.IsFreeGradedCommutative.span_standardMonomial_eq`: `Aᵖ` is spanned by the standard
  monomials of degree `p`; hence `Aᵖ = 0` for `p < 0`
  (`TauCeti.IsFreeGradedCommutative.eq_bot_of_neg`) and `A⁰ = K` when every generator has
  positive degree (`TauCeti.IsFreeGradedCommutative.eq_span_one_of_pos`).
* `TauCeti.IsFreeGradedCommutative.algHom_ext`: algebra maps out of `A` agreeing on the
  generators are equal.
* `TauCeti.IsFreeGradedCommutative.existsUnique_algHom`: the universal property of `ΛV` with
  respect to graded-commutative algebras.
* `TauCeti.IsFreeGradedCommutative.mem_positivePart`: a generator of positive degree lies in the
  positive part `A⁺`.
* `MvPolynomial.isFreeGradedCommutative_X`: a polynomial ring is free graded-commutative on its
  variables placed in even degrees.

## References

* Y. Félix, S. Halperin, J.-C. Thomas, *Rational homotopy theory*, Graduate Texts in Mathematics
  205, Springer, 2001, §3.
* K. Hess, *Rational homotopy theory: a brief introduction*, in *Interactions between homotopy
  theory and algebra*, Contemp. Math. 436, 2007, §1, before Definition 1.10.
* J. W. Morgan, *The algebraic topology of smooth algebraic varieties*, Publ. Math. IHÉS 48
  (1978), the note after Definition 5.2, for the indecomposables of `ΛV`.
-/

public section

namespace TauCeti

open Finsupp

section Monomial

variable {ι : Type*} [LinearOrder ι] {R : Type*}

/-- The standard monomial `x_{i₁}^{f i₁} ⋯ x_{i_k}^{f i_k}` of an exponent vector `f`, the
indices `i₁ < ⋯ < i_k` of its support taken in increasing order: the product of the `x i` over
the elements of the multiset `f.toMultiset`, sorted increasingly. -/
noncomputable def standardMonomial [Monoid R] (x : ι → R) (f : ι →₀ ℕ) : R :=
  ((Multiset.sort f.toMultiset).map x).prod

section Monoid

variable [Monoid R] (x : ι → R)

/-- A standard monomial is the product of the `x i` over the sorted multiset of its exponent
vector. -/
theorem standardMonomial_def (f : ι →₀ ℕ) :
    standardMonomial x f = ((Multiset.sort f.toMultiset).map x).prod :=
  (rfl)

@[simp]
theorem standardMonomial_zero : standardMonomial x 0 = 1 := by
  simp [standardMonomial]

@[simp]
theorem standardMonomial_single (i : ι) (n : ℕ) : standardMonomial x (single i n) = x i ^ n := by
  rw [standardMonomial_def, toMultiset_single, Multiset.nsmul_singleton, ← Multiset.coe_replicate,
    ((Multiset.eq_sort_iff _).2 ⟨List.pairwise_replicate.2 (Or.inr le_rfl), rfl⟩).symm]
  simp

/-- A monoid homomorphism maps standard monomials in the `x i` to standard monomials in their
images. -/
theorem map_standardMonomial {S F : Type*} [Monoid S] [FunLike F R S] [MonoidHomClass F R S]
    (φ : F) (f : ι →₀ ℕ) : φ (standardMonomial x f) = standardMonomial (φ ∘ x) f := by
  simp [standardMonomial, map_list_prod]

/-- A standard monomial in homogeneous elements `x i` of degrees `deg i` is homogeneous, of
degree the weight `∑ᵢ f i • deg i` of its exponent vector. -/
theorem standardMonomial_mem {x : ι → R} {M σ : Type*} [AddCommMonoid M] [SetLike σ R]
    {𝒜 : M → σ} [SetLike.GradedMonoid 𝒜] {deg : ι → M} (hx : ∀ i, x i ∈ 𝒜 (deg i)) (f : ι →₀ ℕ) :
    standardMonomial x f ∈ 𝒜 (weight deg f) := by
  have hw : ((Multiset.sort f.toMultiset).map deg).sum = weight deg f := by
    rw [Multiset.sum_map_sort, toMultiset_map, sum_toMultiset,
      sum_mapDomain_index (h := fun a n => n • a) (fun _ => zero_smul ..) fun _ _ _ => add_smul ..,
      weight_apply]
  rw [standardMonomial, ← hw]
  exact SetLike.list_prod_map_mem_graded _ deg x fun i _ => hx i

end Monoid

/-- In a commutative monoid a standard monomial is the product of the powers `x i ^ f i`. -/
theorem standardMonomial_eq_prod [CommMonoid R] (x : ι → R) (f : ι →₀ ℕ) :
    standardMonomial x f = f.prod fun i n => x i ^ n := by
  rw [standardMonomial, Multiset.prod_map_sort, toMultiset_map, prod_toMultiset,
    prod_mapDomain_index pow_zero pow_add]

section Ring

variable [Ring R] {deg : ι → ℕ} {y : ι → R}

private theorem mul_list_prod_map
    (hy : ∀ i j, y i * y j = ((deg i : ℤ) * deg j).negOnePow • (y j * y i))
    (i : ι) {l : List ι} (hl : l.Pairwise (· ≤ ·)) :
    y i * (l.map y).prod = (((l.filter (· < i)).map fun j => (deg j : ℤ)).sum * deg i).negOnePow •
      ((l.orderedInsert (· ≤ ·) i).map y).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hia : i ≤ a
    · have : l.filter (· < i) = [] := List.filter_eq_nil_iff.2 fun b hb => by
        simpa using hia.trans (hl.1 b hb)
      simp [hia, this, not_lt.2 hia]
    · have hai : a < i := not_le.1 hia
      simp only [List.map_cons, List.prod_cons, List.orderedInsert_cons, hia, ite_false,
        List.filter_cons, hai, decide_true, ite_true, List.sum_cons]
      rw [← mul_assoc, hy, smul_mul_assoc, mul_assoc, ih hl.2, mul_smul_comm, smul_smul,
        ← Int.negOnePow_add]
      congr 2
      ring

/-- Multiplying a standard monomial on the left by a generator `y i` reorders, with the Koszul
sign of moving `y i` past the factors `y j`, `j < i`, into the standard monomial of
`f + single i 1`. -/
theorem mul_standardMonomial
    (hy : ∀ i j, y i * y j = ((deg i : ℤ) * deg j).negOnePow • (y j * y i)) (i : ι) (f : ι →₀ ℕ) :
    y i * standardMonomial y f =
      (((f.toMultiset.filter (· < i)).map fun j => (deg j : ℤ)).sum * deg i).negOnePow •
        standardMonomial y (f + single i 1) := by
  rw [standardMonomial, mul_list_prod_map hy i (Multiset.pairwise_sort _ _), standardMonomial,
    toMultiset_add_single_one, Multiset.sort_cons_eq_orderedInsert, Multiset.sum_map_filter_sort]

/-- A generator whose square vanishes annihilates every standard monomial in which it occurs. -/
theorem mul_standardMonomial_eq_zero
    (hy : ∀ i j, y i * y j = ((deg i : ℤ) * deg j).negOnePow • (y j * y i)) {i : ι}
    (hi : y i * y i = 0) {f : ι →₀ ℕ} (hf : f i ≠ 0) : y i * standardMonomial y f = 0 := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + single i 1 :=
    ⟨f - single i 1, (tsub_add_cancel_of_le (single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hf))).symm⟩
  rw [(smul_eq_iff_eq_inv_smul _).1 (mul_standardMonomial hy i g).symm, mul_smul_comm,
    ← mul_assoc, hi, zero_mul, smul_zero]

end Ring

end Monomial

/-- The exponent vectors of standard monomials in generators of degrees `deg`: finitely supported
exponents, with every generator of odd degree occurring at most once. -/
abbrev ExponentVector {ι : Type*} (deg : ι → ℕ) : Type _ :=
  {f : ι →₀ ℕ // ∀ i, Odd (deg i) → f i ≤ 1}

section FreeGradedCommutative

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
  {ι : Type*} [LinearOrder ι]

variable (𝒜 : ℤ → Submodule K A) in
/-- `A` is the free graded-commutative algebra `ΛV` on the homogeneous generators `x i` of
degrees `deg i`: each `x i` lies in `𝒜 (deg i)`, the generators commute up to the Koszul sign,
and the standard monomials of the exponent vectors form a basis of `A`. -/
structure IsFreeGradedCommutative (x : ι → A) (deg : ι → ℕ) : Prop where
  /-- Each generator is homogeneous of its degree. -/
  mem : ∀ i, x i ∈ 𝒜 (deg i)
  /-- The generators commute up to the Koszul sign. -/
  mul_comm : ∀ i j, x i * x j = ((deg i : ℤ) * deg j).negOnePow • (x j * x i)
  /-- The standard monomials are linearly independent. -/
  linearIndependent : LinearIndependent K fun f : ExponentVector deg => standardMonomial x f.val
  /-- The standard monomials span. -/
  span_eq_top :
    Submodule.span K (Set.range fun f : ExponentVector deg => standardMonomial x f.val) = ⊤

namespace IsFreeGradedCommutative

variable {𝒜 : ℤ → Submodule K A} {x : ι → A} {deg : ι → ℕ}

/-- The basis of standard monomials of a free graded-commutative algebra. -/
noncomputable def basis (hx : IsFreeGradedCommutative 𝒜 x deg) :
    Module.Basis (ExponentVector deg) K A :=
  .mk hx.linearIndependent hx.span_eq_top.ge

@[simp]
theorem basis_apply (hx : IsFreeGradedCommutative 𝒜 x deg) (f : ExponentVector deg) :
    hx.basis f = standardMonomial x f.val :=
  Module.Basis.mk_apply ..

/-- The generators generate a free graded-commutative algebra as an algebra. -/
theorem adjoin_range_eq_top (hx : IsFreeGradedCommutative 𝒜 x deg) :
    Algebra.adjoin K (Set.range x) = ⊤ := by
  refine Algebra.eq_top_iff.2 fun a => ?_
  refine (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin K (Set.range x)))).2 ?_
    (hx.span_eq_top.ge Submodule.mem_top)
  rintro _ ⟨f, rfl⟩
  exact Subalgebra.list_prod_mem _ fun a ha => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
    exact Algebra.subset_adjoin ⟨i, rfl⟩

/-- Two algebra maps out of a free graded-commutative algebra agree once they agree on the
generators. -/
theorem algHom_ext (hx : IsFreeGradedCommutative 𝒜 x deg) {B : Type*} [Semiring B]
    [Algebra K B] {φ ψ : A →ₐ[K] B} (h : ∀ i, φ (x i) = ψ (x i)) : φ = ψ :=
  AlgHom.ext_of_adjoin_eq_top hx.adjoin_range_eq_top <| by
    rintro _ ⟨i, rfl⟩
    exact h i

/-- A generator of positive degree lies in the positive part. -/
theorem mem_positivePart (hx : IsFreeGradedCommutative 𝒜 x deg) {i : ι} (hi : 0 < deg i) :
    x i ∈ positivePart 𝒜 :=
  mem_positivePart_of_mem (by exact_mod_cast hi) (hx.mem i)

section Degree

variable [GradedAlgebra 𝒜]

/-- The homogeneous component `𝒜 p` of a free graded-commutative algebra is spanned by the
standard monomials of degree `p`. -/
theorem span_standardMonomial_eq (hx : IsFreeGradedCommutative 𝒜 x deg) (p : ℤ) :
    Submodule.span K ((fun f : ExponentVector deg => standardMonomial x f.val) ''
      {f | weight (fun i => (deg i : ℤ)) f.val = p}) = 𝒜 p := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun a ha => ?_
  · rintro _ ⟨f, rfl, rfl⟩
    exact standardMonomial_mem hx.mem f.val
  · have ha' : a ∈ (Submodule.span K (Set.range fun f : ExponentVector deg =>
        standardMonomial x f.val)).map (GradedAlgebra.proj 𝒜 p) :=
      ⟨a, hx.span_eq_top.ge Submodule.mem_top, by
        rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha]⟩
    rw [← Submodule.span_image] at ha'
    refine Submodule.span_le.2 ?_ ha'
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    have hf := standardMonomial_mem hx.mem f.val
    rw [GradedAlgebra.proj_apply]
    by_cases hfp : weight (fun i => (deg i : ℤ)) f.val = p
    · rw [DirectSum.decompose_of_mem_same 𝒜 (hfp ▸ hf)]
      exact Submodule.subset_span ⟨f, hfp, rfl⟩
    · rw [DirectSum.decompose_of_mem_ne 𝒜 hf hfp]
      exact zero_mem _

/-- A free graded-commutative algebra on generators of nonnegative degrees vanishes in negative
degrees. -/
theorem eq_bot_of_neg (hx : IsFreeGradedCommutative 𝒜 x deg) {p : ℤ} (hp : p < 0) : 𝒜 p = ⊥ := by
  rw [← hx.span_standardMonomial_eq p, Submodule.span_eq_bot]
  rintro _ ⟨f, hf, rfl⟩
  refine absurd hf (ne_of_gt (hp.trans_le ?_))
  rw [weight_apply]
  exact Finsupp.sum_nonneg fun i _ => nsmul_nonneg (Int.natCast_nonneg _) _

/-- A free graded-commutative algebra on generators of positive degrees is spanned by `1` in
degree `0`, so there it is the image of the ground ring `K`. -/
theorem eq_span_one_of_pos (hx : IsFreeGradedCommutative 𝒜 x deg) (hdeg : ∀ i, 0 < deg i) :
    𝒜 0 = Submodule.span K {1} := by
  rw [← hx.span_standardMonomial_eq 0]
  congr 1
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨⟨0, fun _ _ => zero_le_one⟩, by simp, by simp⟩, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  by_cases h : f.val = 0
  · simp [h]
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h
  have := le_weight_of_ne_zero (w := fun i => (deg i : ℤ)) (fun _ => Int.natCast_nonneg _) hi
  simp only [Set.mem_ofPred_eq] at hf
  have := hdeg i
  omega

end Degree

end IsFreeGradedCommutative

end FreeGradedCommutative

namespace IsFreeGradedCommutative

variable {K : Type*} [CommRing K] [Invertible (2 : K)] {A : Type*} [Ring A] [Algebra K A]
  {ι : Type*} [LinearOrder ι] {𝒜 : ℤ → Submodule K A} {x : ι → A} {deg : ι → ℕ}

/-- When `2` is invertible in `K`, a generator of odd degree of a free graded-commutative algebra
squares to zero. -/
theorem mul_self_eq_zero (hx : IsFreeGradedCommutative 𝒜 x deg) {i : ι} (hi : Odd (deg i)) :
    x i * x i = 0 :=
  mul_self_eq_zero_of_negOnePow_odd (K := K) hi.natCast (hx.mul_comm i i)

variable {B : Type*} [Ring B] [Algebra K B] {b : ι → B}

private theorem constr_generator_mul (hx : IsFreeGradedCommutative 𝒜 x deg)
    (hb : ∀ i j, b i * b j = ((deg i : ℤ) * deg j).negOnePow • (b j * b i)) (i : ι) (a : A) :
    hx.basis.constr K (fun f => standardMonomial b f.val) (x i * a) =
      b i * hx.basis.constr K (fun f => standardMonomial b f.val) a := by
  set L := hx.basis.constr K fun f => standardMonomial b f.val
  suffices h : L ∘ₗ LinearMap.mulLeft K (x i) = LinearMap.mulLeft K (b i) ∘ₗ L from
    LinearMap.congr_fun h a
  refine hx.basis.ext fun f => ?_
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, L, Module.Basis.constr_basis]
  rw [basis_apply]
  by_cases h : Odd (deg i) ∧ f.val i ≠ 0
  · rw [mul_standardMonomial_eq_zero hx.mul_comm (hx.mul_self_eq_zero h.1) h.2,
      mul_standardMonomial_eq_zero hb
        (mul_self_eq_zero_of_negOnePow_odd (K := K) h.1.natCast (hb i i)) h.2, map_zero]
  · have hg : ∀ j, Odd (deg j) → f.val j + single i 1 j ≤ 1 := fun j hj => by
      rcases eq_or_ne j i with rfl | hji
      · simpa using not_and_not_right.1 h hj
      · simpa [single_apply, hji.symm] using f.property j hj
    rw [mul_standardMonomial hx.mul_comm, mul_standardMonomial hb,
      ← basis_apply hx ⟨f.val + single i 1, hg⟩]
    simp only [Units.smul_def, map_zsmul, Module.Basis.constr_basis]

omit [Invertible (2 : K)] in
private theorem constr_one (hx : IsFreeGradedCommutative 𝒜 x deg) (b : ι → B) :
    hx.basis.constr K (fun f => standardMonomial b f.val) 1 = 1 := by
  rw [← standardMonomial_zero x, ← basis_apply hx ⟨0, fun _ _ => zero_le_one⟩,
    Module.Basis.constr_basis, standardMonomial_zero]

private theorem constr_x (hx : IsFreeGradedCommutative 𝒜 x deg)
    (hb : ∀ i j, b i * b j = ((deg i : ℤ) * deg j).negOnePow • (b j * b i)) (i : ι) :
    hx.basis.constr K (fun f => standardMonomial b f.val) (x i) = b i := by
  rw [← mul_one (x i), constr_generator_mul hx hb, constr_one, mul_one]

/-- The linear map sending each standard monomial in the `x i` to the same standard monomial in
the `b i` is multiplicative: the set of `w` with `L (w * a) = L w * L a` for all `a` is a
subalgebra containing the generators. -/
private theorem constr_mul (hx : IsFreeGradedCommutative 𝒜 x deg)
    (hb : ∀ i j, b i * b j = ((deg i : ℤ) * deg j).negOnePow • (b j * b i)) (a a' : A) :
    hx.basis.constr K (fun f => standardMonomial b f.val) (a * a') =
      hx.basis.constr K (fun f => standardMonomial b f.val) a *
        hx.basis.constr K (fun f => standardMonomial b f.val) a' := by
  set L := hx.basis.constr K fun f => standardMonomial b f.val
  suffices h : ∀ w ∈ Algebra.adjoin K (Set.range x), ∀ a, L (w * a) = L w * L a from
    h a (hx.adjoin_range_eq_top ▸ Algebra.mem_top) a'
  intro w hw
  induction hw using Algebra.adjoin_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    intro a
    rw [constr_generator_mul hx hb, constr_x hx hb]
  | algebraMap r =>
    intro a
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, map_smul, constr_one,
      smul_one_mul]
  | add w w' _ _ hw hw' =>
    intro a
    rw [add_mul, map_add, hw, hw', map_add, add_mul]
  | mul w w' _ _ hw hw' =>
    intro a
    rw [mul_assoc, hw, hw', hw, mul_assoc]

/-- The algebra map out of a free graded-commutative algebra sending each generator `x i` to
`b i`, for elements `b i` of any `K`-algebra which commute up to the Koszul sign of the degrees
of the generators. When `2` is invertible in `K` no further relation is needed: the `b i` of odd
degree square to zero automatically. -/
noncomputable def lift (hx : IsFreeGradedCommutative 𝒜 x deg) (b : ι → B)
    (hb : ∀ i j, b i * b j = ((deg i : ℤ) * deg j).negOnePow • (b j * b i)) : A →ₐ[K] B :=
  .ofLinearMap (hx.basis.constr K fun f => standardMonomial b f.val) (constr_one hx b)
    (constr_mul hx hb)

/-- `lift` sends each generator `x i` to `b i`. -/
@[simp]
theorem lift_x (hx : IsFreeGradedCommutative 𝒜 x deg) (b : ι → B)
    (hb : ∀ i j, b i * b j = ((deg i : ℤ) * deg j).negOnePow • (b j * b i)) (i : ι) :
    hx.lift b hb (x i) = b i := by
  rw [lift, AlgHom.ofLinearMap_apply, constr_x hx hb]

/-- `lift` sends the family of generators `x` to the family `b`. -/
@[simp]
theorem lift_comp_x (hx : IsFreeGradedCommutative 𝒜 x deg) (b : ι → B)
    (hb : ∀ i j, b i * b j = ((deg i : ℤ) * deg j).negOnePow • (b j * b i)) :
    hx.lift b hb ∘ x = b :=
  funext (hx.lift_x b hb)

/-- `lift` sends each standard monomial in the `x i` to the same standard monomial in the
`b i`. -/
@[simp]
theorem lift_standardMonomial (hx : IsFreeGradedCommutative 𝒜 x deg) (b : ι → B)
    (hb : ∀ i j, b i * b j = ((deg i : ℤ) * deg j).negOnePow • (b j * b i)) (f : ι →₀ ℕ) :
    hx.lift b hb (standardMonomial x f) = standardMonomial b f := by
  rw [map_standardMonomial, lift_comp_x]

/-- The universal property of the free graded-commutative algebra `ΛV`: when `2` is invertible in
`K`, for a graded-commutative algebra `(B, ℬ)` and elements `b i ∈ ℬ (deg i)` there is a unique
algebra map `ΛV → B` sending each generator `x i` to `b i`. -/
theorem existsUnique_algHom (hx : IsFreeGradedCommutative 𝒜 x deg) (ℬ : ℤ → Submodule K B)
    (hB : ∀ {p q : ℤ} {a b : B}, a ∈ ℬ p → b ∈ ℬ q → a * b = (p * q).negOnePow • (b * a))
    (b : ι → B) (hb : ∀ i, b i ∈ ℬ (deg i)) : ∃! φ : A →ₐ[K] B, ∀ i, φ (x i) = b i :=
  ⟨hx.lift b fun i j => hB (hb i) (hb j), hx.lift_x b _, fun φ hφ =>
    hx.algHom_ext fun i => by rw [hφ, lift_x]⟩

section Indecomposables

open TrivSqZeroExt

variable [GradedAlgebra 𝒜]

omit [GradedAlgebra 𝒜] in
/-- The algebra map from a free graded-commutative algebra to the trivial square-zero extension
`K ⊕ (ι →₀ K)` sending each generator `x i` to the basis vector `single i 1`. It reads off the
coefficients of the generators modulo decomposables. -/
private noncomputable def toTrivSqZeroExt (hx : IsFreeGradedCommutative 𝒜 x deg) :
    A →ₐ[K] TrivSqZeroExt K (ι →₀ K) :=
  hx.lift (fun i => inr (single i 1)) fun _ _ => by simp

omit [GradedAlgebra 𝒜] in
private theorem toTrivSqZeroExt_x (hx : IsFreeGradedCommutative 𝒜 x deg) (i : ι) :
    hx.toTrivSqZeroExt (x i) = inr (single i 1) :=
  hx.lift_x ..

/-- The constant term of `toTrivSqZeroExt` vanishes on the positive part. -/
private theorem fst_toTrivSqZeroExt_eq_zero (hx : IsFreeGradedCommutative 𝒜 x deg)
    {a : A} (ha : a ∈ positivePart 𝒜) : (hx.toTrivSqZeroExt a).fst = 0 := by
  let ε : A →ₐ[K] K := (fstHom K K (ι →₀ K)).comp hx.toTrivSqZeroExt
  have hε : ε ∘ x = 0 := funext fun i => by simp [ε, toTrivSqZeroExt_x]
  refine positivePart_le_iff (P := LinearMap.ker ε.toLinearMap).2 (fun p hp => ?_) ha
  rw [← hx.span_standardMonomial_eq p, Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, f.val i ≠ 0 := by
    by_contra! h
    rw [Set.mem_ofPred_eq, show f.val = 0 from Finsupp.ext h, map_zero] at hf
    omega
  simp only [SetLike.mem_coe, LinearMap.mem_ker, AlgHom.toLinearMap_apply,
    map_standardMonomial, hε, standardMonomial_eq_prod]
  exact Finset.prod_eq_zero (mem_support_iff.2 hi) (by simp [hi])

/-- Modulo its constant term, every element of a free graded-commutative algebra on generators
of positive degree has positive degree and is a combination of generators modulo decomposables. -/
private theorem sub_mem_positivePart_and_mem_span_sup (hx : IsFreeGradedCommutative 𝒜 x deg)
    (hdeg : ∀ i, 0 < deg i) (a : A) :
    a - algebraMap K A (hx.toTrivSqZeroExt a).fst ∈ positivePart 𝒜 ∧
      a - algebraMap K A (hx.toTrivSqZeroExt a).fst ∈
        Submodule.span K (Set.range x) ⊔ positivePart 𝒜 * positivePart 𝒜 := by
  suffices h : ∀ w ∈ Algebra.adjoin K (Set.range x),
      w - algebraMap K A (hx.toTrivSqZeroExt w).fst ∈ positivePart 𝒜 ∧
        w - algebraMap K A (hx.toTrivSqZeroExt w).fst ∈
          Submodule.span K (Set.range x) ⊔ positivePart 𝒜 * positivePart 𝒜 from
    h a (hx.adjoin_range_eq_top ▸ Algebra.mem_top)
  intro w hw
  induction hw using Algebra.adjoin_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only [toTrivSqZeroExt_x, fst_inr, map_zero, sub_zero]
    exact ⟨hx.mem_positivePart (hdeg i),
      Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)⟩
  | algebraMap r => simp [algebraMap_eq_inl]
  | add w w' _ _ hw hw' =>
    simp only [map_add, fst_add]
    rw [add_sub_add_comm]
    exact ⟨add_mem hw.1 hw'.1, add_mem hw.2 hw'.2⟩
  | mul w w' _ _ hw hw' =>
    set u := w - algebraMap K A (hx.toTrivSqZeroExt w).fst
    set v := w' - algebraMap K A (hx.toTrivSqZeroExt w').fst
    have key : w * w' - algebraMap K A (hx.toTrivSqZeroExt (w * w')).fst =
        u * v + (hx.toTrivSqZeroExt w').fst • u + (hx.toTrivSqZeroExt w).fst • v := by
      simp only [u, v, map_mul, fst_mul, Algebra.smul_def, mul_sub, sub_mul,
        Algebra.commutes (hx.toTrivSqZeroExt w').fst w]
      rw [Algebra.commutes (hx.toTrivSqZeroExt w').fst]
      abel
    rw [key]
    exact ⟨add_mem (add_mem (mul_mem_positivePart_of_left (fun _ => hx.eq_bot_of_neg) hw.1 v)
        (Submodule.smul_mem _ _ hw.1)) (Submodule.smul_mem _ _ hw'.1),
      add_mem (add_mem (Submodule.mem_sup_right (Submodule.mul_mem_mul hw.1 hw'.1))
        (Submodule.smul_mem _ _ hw.2)) (Submodule.smul_mem _ _ hw'.2)⟩

/-- The classes of the generators in the indecomposables are linearly independent: the
coefficient of `x i` modulo decomposables is read off by `toTrivSqZeroExt`. -/
private theorem linearIndependent_mk_x (hx : IsFreeGradedCommutative 𝒜 x deg)
    (hdeg : ∀ i, 0 < deg i) :
    LinearIndependent K fun i => Indecomposables.mk 𝒜 ⟨x i, hx.mem_positivePart (hdeg i)⟩ := by
  let L : A →ₗ[K] ι →₀ K := sndHom K (ι →₀ K) ∘ₗ hx.toTrivSqZeroExt.toLinearMap
  refine LinearIndependent.of_comp (Submodule.liftQ _ (L ∘ₗ (positivePart 𝒜).subtype)
    fun a ha => ?_) ?_
  · rw [LinearMap.mem_ker]
    refine Submodule.mul_induction_on (C := fun a => L a = 0) ha (fun b hb c hc => ?_)
      fun b c hb hc => ?_
    · simp [L, fst_toTrivSqZeroExt_eq_zero hx hb, fst_toTrivSqZeroExt_eq_zero hx hc]
    · simp [hb, hc]
  · convert (Finsupp.basisSingleOne : Module.Basis ι K (ι →₀ K)).linearIndependent
    ext1 i
    simp [L, Indecomposables.mk_apply, toTrivSqZeroExt_x]

/-- The classes of the generators span the indecomposables. -/
private theorem top_le_span_mk_x (hx : IsFreeGradedCommutative 𝒜 x deg)
    (hdeg : ∀ i, 0 < deg i) :
    ⊤ ≤ Submodule.span K
      (Set.range fun i => Indecomposables.mk 𝒜 ⟨x i, hx.mem_positivePart (hdeg i)⟩) := by
  have hspan : Submodule.span K (Set.range x) ≤ positivePart 𝒜 :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun i => hx.mem_positivePart (hdeg i))
  -- The class of a combination of generators is the combination of their classes.
  have key : ∀ s (hs : s ∈ Submodule.span K (Set.range x)),
      Indecomposables.mk 𝒜 ⟨s, hspan hs⟩ ∈ Submodule.span K
        (Set.range fun i => Indecomposables.mk 𝒜 ⟨x i, hx.mem_positivePart (hdeg i)⟩) := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨i, rfl⟩ := hs
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
      rw [show (⟨0, hspan (zero_mem _)⟩ : positivePart 𝒜) = 0 from rfl, map_zero]
      exact zero_mem _
    | add s t hs ht hs' ht' =>
      rw [show (⟨s + t, hspan (add_mem hs ht)⟩ : positivePart 𝒜) =
        ⟨s, hspan hs⟩ + ⟨t, hspan ht⟩ from rfl, map_add]
      exact add_mem hs' ht'
    | smul c s hs hs' =>
      rw [show (⟨c • s, hspan (Submodule.smul_mem _ c hs)⟩ : positivePart 𝒜) =
        c • ⟨s, hspan hs⟩ from rfl, map_smul]
      exact Submodule.smul_mem _ c hs'
  -- An element of positive degree is a combination of generators modulo decomposables.
  rintro q -
  obtain ⟨⟨a, ha⟩, rfl⟩ := Indecomposables.mk_surjective q
  have h := (hx.sub_mem_positivePart_and_mem_span_sup hdeg a).2
  rw [fst_toTrivSqZeroExt_eq_zero hx ha, map_zero, sub_zero] at h
  obtain ⟨s, hs, m, hm, rfl⟩ := Submodule.mem_sup.1 h
  convert key s hs using 1
  rw [Indecomposables.mk_eq_mk_iff]
  simpa using hm

/-- **The indecomposables of `ΛV` are `V`**: when `2` is invertible in `K`, the classes of the
generators of a free graded-commutative algebra on generators of positive degree form a basis of
its indecomposables `A⁺ ⧸ A⁺ · A⁺`. The hypothesis on `2` is needed: over `𝔽₂` the polynomial ring
`𝔽₂[e]`, `|e| = 1`, is free graded-commutative on `e` and `e²`, and the class of `e²` is zero. -/
noncomputable def indecomposablesBasis (hx : IsFreeGradedCommutative 𝒜 x deg)
    (hdeg : ∀ i, 0 < deg i) : Module.Basis ι K (Indecomposables 𝒜) :=
  .mk (hx.linearIndependent_mk_x hdeg) (hx.top_le_span_mk_x hdeg)

@[simp]
theorem indecomposablesBasis_apply (hx : IsFreeGradedCommutative 𝒜 x deg)
    (hdeg : ∀ i, 0 < deg i) (i : ι) :
    hx.indecomposablesBasis hdeg i = Indecomposables.mk 𝒜 ⟨x i, hx.mem_positivePart (hdeg i)⟩ :=
  Module.Basis.mk_apply ..

end Indecomposables

end IsFreeGradedCommutative

end TauCeti

namespace MvPolynomial

open TauCeti Finsupp

variable {K : Type*} [CommRing K] {σ : Type*} [LinearOrder σ]

/-- A polynomial ring is the free graded-commutative algebra on its variables placed in even
degrees, graded by the weighted degree. -/
theorem isFreeGradedCommutative_X {deg : σ → ℕ} (hdeg : ∀ i, Even (deg i)) :
    IsFreeGradedCommutative (weightedHomogeneousSubmodule K fun i => (deg i : ℤ)) X deg := by
  have hsm : (fun f : ExponentVector deg => standardMonomial (X : σ → MvPolynomial σ K) f.val) =
      basisMonomials σ K ∘ Subtype.val := by
    ext1 f
    simp [standardMonomial_eq_prod, coe_basisMonomials, monomial_eq]
  have hsurj : Function.Surjective (Subtype.val : ExponentVector deg → σ →₀ ℕ) := fun f =>
    ⟨⟨f, fun i hi => absurd (hdeg i) (Nat.not_even_iff_odd.2 hi)⟩, rfl⟩
  refine ⟨fun i => (mem_weightedHomogeneousSubmodule ..).2 (isWeightedHomogeneous_X ..),
    fun i j => ?_, ?_, ?_⟩
  · rw [Int.negOnePow_even _ (((Int.even_natCast _).2 (hdeg i)).mul_right _), one_smul, mul_comm]
  · rw [hsm]
    exact (basisMonomials σ K).linearIndependent.comp _ Subtype.val_injective
  · rw [hsm, Set.range_comp, hsurj.range_eq, Set.image_univ, (basisMonomials σ K).span_eq]

end MvPolynomial
