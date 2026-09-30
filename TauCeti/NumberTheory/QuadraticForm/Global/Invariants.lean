/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative

/-!
# Systems of local invariants of global quadratic forms

A regular quadratic form of rank `n` over a number field `K` has the following invariants:

* its rank `n`;
* its plain discriminant `d ∈ Kˣ/(Kˣ)²`, one global square class;
* at each finite place `v`, its Hasse sign `s_v = ∏_{i<j} (a_i, a_j)_v ∈ {±1}`;
* at each real place `w`, its positive index `p_w`.

This file defines the carrier `GlobalFormInvariants K` of such data, with no reference to a form,
and the predicate `GlobalFormInvariants.IsAdmissible` cutting out the systems that can arise from
a form. Admissibility consists of the exact conditions:

1. `1 ≤ n`;
2. at every real place `p_w ≤ n`, and the image of `d` in `ℝˣ/(ℝˣ)²` is the class of
   `(-1)^(n - p_w)`;
3. `s_v = 1` at all but finitely many finite places;
4. in rank one `s_v = 1`, and in rank two `s_v = 1` wherever the image of `d` in `K_v` is the
   class of `-1`;
5. the product of all `s_v` and of the real Hasse signs `(-1)^((n - p_w)(n - p_w - 1)/2)` is `1`.

The global discriminant is part of the carrier, and only its images are read at the places: the
local discriminants of a system are not independent data. Condition 4 records the two local
triples `(n, d_v, s_v)` over a nonarchimedean local field that no regular form realizes: a form
of rank one has trivial Hasse sign, and a binary form of discriminant `-1` is a hyperbolic plane,
whose Hasse sign is also trivial. Neither exception follows from the others, as the rank-one and
rank-two families below show: with Hasse sign `-1` at exactly two finite places they have finite
support and total product one, and are still not admissible.

## Main definitions

* `TauCeti.NumberField.QuadraticForm.GlobalFormInvariants`: rank, global discriminant, finite
  Hasse signs and real positive indices.
* `GlobalFormInvariants.discrAtFinitePlace`, `GlobalFormInvariants.discrAtRealPlace`: the images
  of the global discriminant in the completions.
* `GlobalFormInvariants.realNegativeIndex`, `GlobalFormInvariants.realHasse`: the negative index
  `n - p_w` and the Hasse sign `(-1)^((n - p_w)(n - p_w - 1)/2)` at a real place.
* `GlobalFormInvariants.hasseProduct`: the product of all finite and real Hasse signs.
* `GlobalFormInvariants.IsAdmissible`: the admissibility conditions above.

## Main results

* `GlobalFormInvariants.hasseProduct_eq_prod_of_mulSupport_subset`: the Hasse product may be
  computed over any finite set of finite places containing the support of the Hasse signs.
* `GlobalFormInvariants.hasseProduct_eq_neg_one_pow_card`: with Hasse sign `-1` exactly on a
  finite set `T` of finite places and trivial real Hasse signs, the Hasse product is `(-1)^#T`.
* `GlobalFormInvariants.isAdmissible_positiveDefinite_iff_even_card`: in rank at least three, the
  positive-definite system of trivial discriminant with Hasse sign `-1` exactly on `T` is
  admissible exactly when `#T` is even.
* `GlobalFormInvariants.isAdmissible_rankOne_iff_eq_empty`,
  `GlobalFormInvariants.isAdmissible_rankTwo_iff_eq_empty`: the corresponding systems in rank one,
  and in rank two with discriminant `-1`, are admissible only for `T = ∅`, although for every even
  `T` their Hasse product is one.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:20–23 for the local
  realization exceptions and 72:1 for existence with prescribed local invariants.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, §3.3, Theorem 9, the same
  conditions over `ℚ`.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField.QuadraticForm

variable (K : Type*) [Field K]

/-- **A system of local invariants of a quadratic form over a number field `K`**: a rank `n`, a
global plain discriminant `d ∈ Kˣ/(Kˣ)²`, a Hasse sign `s_v ∈ {±1}` at every finite place `v`,
and a positive index `p_w` at every real place `w`. No condition relates the data; the systems
arising from regular forms of positive rank are those satisfying `IsAdmissible`. -/
@[ext]
structure GlobalFormInvariants where
  /-- The rank `n`. -/
  rank : ℕ
  /-- The global plain discriminant `d ∈ Kˣ/(Kˣ)²`. -/
  discr : SquareClassGroup K
  /-- The Hasse sign `s_v ∈ {±1}` at a finite place `v`. -/
  finiteHasse : HeightOneSpectrum (𝓞 K) → ℤˣ
  /-- The positive index `p_w` at a real place `w`. -/
  realPositiveIndex : {w : InfinitePlace K // w.IsReal} → ℕ

namespace GlobalFormInvariants

variable {K} (I : GlobalFormInvariants K)

section FinitePlace

variable [NumberField K]

/-- The discriminant of a system at a finite place `v`: the image of the global discriminant in
`K_vˣ/(K_vˣ)²`. -/
def discrAtFinitePlace (v : HeightOneSpectrum (𝓞 K)) : SquareClassGroup (v.adicCompletion K) :=
  (algebraMap K (v.adicCompletion K)).squareClassMap I.discr

/-- Unfolds `discrAtFinitePlace`. -/
theorem discrAtFinitePlace_def (v : HeightOneSpectrum (𝓞 K)) :
    I.discrAtFinitePlace v = (algebraMap K (v.adicCompletion K)).squareClassMap I.discr :=
  (rfl)

end FinitePlace

/-- The discriminant of a system at a real place `w`: the image of the global discriminant in
`ℝˣ/(ℝˣ)²` under the real embedding of `w`. -/
def discrAtRealPlace (w : {w : InfinitePlace K // w.IsReal}) : SquareClassGroup ℝ :=
  (embedding_of_isReal w.2).squareClassMap I.discr

/-- Unfolds `discrAtRealPlace`. -/
theorem discrAtRealPlace_def (w : {w : InfinitePlace K // w.IsReal}) :
    I.discrAtRealPlace w = (embedding_of_isReal w.2).squareClassMap I.discr :=
  (rfl)

/-- The negative index `n - p_w` of a system at a real place `w`. -/
def realNegativeIndex (w : {w : InfinitePlace K // w.IsReal}) : ℕ :=
  I.rank - I.realPositiveIndex w

/-- Unfolds `realNegativeIndex`. -/
theorem realNegativeIndex_def (w : {w : InfinitePlace K // w.IsReal}) :
    I.realNegativeIndex w = I.rank - I.realPositiveIndex w :=
  (rfl)

/-- The Hasse sign of a system at a real place `w`: `(-1)^(q(q-1)/2)` for the negative index
`q = n - p_w`, the Hasse sign of the real diagonal form `p_w⟨1⟩ ⊥ q⟨-1⟩`. -/
def realHasse (w : {w : InfinitePlace K // w.IsReal}) : ℤˣ :=
  (-1) ^ (I.realNegativeIndex w).choose 2

/-- Unfolds `realHasse`. -/
theorem realHasse_def (w : {w : InfinitePlace K // w.IsReal}) :
    I.realHasse w = (-1) ^ (I.realNegativeIndex w).choose 2 :=
  (rfl)

variable [NumberField K]

open scoped Classical in
/-- **The Hasse product** of a system: the product of its Hasse signs over all finite places and
all real places. The finite factor is a `finprod`; it is the product of the Hasse signs when they
have finite support, which is part of admissibility. -/
def hasseProduct : ℤˣ :=
  (∏ᶠ v, I.finiteHasse v) * ∏ w, I.realHasse w

open scoped Classical in
/-- Unfolds `hasseProduct`. -/
theorem hasseProduct_def : I.hasseProduct = (∏ᶠ v, I.finiteHasse v) * ∏ w, I.realHasse w :=
  (rfl)

open scoped Classical in
/-- **The Hasse product is independent of the chosen finite support**: it is the product of the
finite Hasse signs over any finite set of finite places outside which they are trivial, times the
real Hasse signs. -/
theorem hasseProduct_eq_prod_of_mulSupport_subset {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : Function.mulSupport I.finiteHasse ⊆ S) :
    I.hasseProduct = (∏ v ∈ S, I.finiteHasse v) * ∏ w, I.realHasse w := by
  rw [hasseProduct_def, finprod_eq_prod_of_mulSupport_subset _ hS]

/-- **Admissibility of a system of local invariants.** A system `(n, d, s, p)` is admissible when
`1 ≤ n`; at every real place `p_w ≤ n` and the image of `d` is the class of `(-1)^(n - p_w)`; the
finite Hasse signs are trivial at almost every place; in rank one every `s_v` is trivial, and in
rank two `s_v` is trivial wherever the image of `d` in `K_v` is the class of `-1`; and the product
of all finite and real Hasse signs is one. These are the systems realized by regular forms of
positive rank. -/
structure IsAdmissible : Prop where
  /-- The rank is positive. -/
  one_le_rank : 1 ≤ I.rank
  /-- At a real place the positive index is at most the rank. -/
  realPositiveIndex_le_rank (w : {w : InfinitePlace K // w.IsReal}) : I.realPositiveIndex w ≤ I.rank
  /-- At a real place the discriminant is the class of `(-1)^(n - p_w)`. -/
  discrAtRealPlace_eq (w : {w : InfinitePlace K // w.IsReal}) :
    I.discrAtRealPlace w = I.realNegativeIndex w • squareClass (-1 : ℝˣ)
  /-- The finite Hasse signs are trivial at almost every finite place. -/
  hasFiniteMulSupport_finiteHasse : Function.HasFiniteMulSupport I.finiteHasse
  /-- In rank one every finite Hasse sign is trivial. -/
  finiteHasse_eq_one_of_rank_eq_one (hn : I.rank = 1) (v : HeightOneSpectrum (𝓞 K)) :
    I.finiteHasse v = 1
  /-- In rank two the finite Hasse sign is trivial where the discriminant is the class of `-1`. -/
  finiteHasse_eq_one_of_rank_eq_two (hn : I.rank = 2) (v : HeightOneSpectrum (𝓞 K))
    (hd : I.discrAtFinitePlace v = squareClass (-1)) : I.finiteHasse v = 1
  /-- The product of all finite and real Hasse signs is one. -/
  hasseProduct_eq_one : I.hasseProduct = 1

namespace IsAdmissible

variable {I}

/-- At a real place of an admissible system, the positive and negative indices add up to the
rank. -/
theorem realPositiveIndex_add_realNegativeIndex_eq_rank (hI : I.IsAdmissible)
    (w : {w : InfinitePlace K // w.IsReal}) :
    I.realPositiveIndex w + I.realNegativeIndex w = I.rank := by
  rw [realNegativeIndex_def]
  have := hI.realPositiveIndex_le_rank w
  omega

open scoped Classical in
/-- For an admissible system, the product of its finite Hasse signs over any finite set of finite
places outside which they are trivial, times its real Hasse signs, is one. -/
theorem prod_finiteHasse_mul_prod_realHasse_eq_one (hI : I.IsAdmissible)
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : Function.mulSupport I.finiteHasse ⊆ S) :
    (∏ v ∈ S, I.finiteHasse v) * ∏ w, I.realHasse w = 1 := by
  rw [← hasseProduct_eq_prod_of_mulSupport_subset I hS]
  exact hI.hasseProduct_eq_one

end IsAdmissible

/-! ### Hasse signs `-1` on a finite set of places -/

section Examples

variable (T : Finset (HeightOneSpectrum (𝓞 K)))

/-- The Hasse product of a system with Hasse sign `-1` exactly at the finite places of `T` and
trivial real Hasse signs is `(-1)^#T`. -/
theorem hasseProduct_eq_neg_one_pow_card
    (hs : I.finiteHasse = (T : Set (HeightOneSpectrum (𝓞 K))).mulIndicator fun _ ↦ -1)
    (hr : ∀ w, I.realHasse w = 1) :
    I.hasseProduct = (-1) ^ T.card := by
  rw [hasseProduct_def, hs, ← finprod_mem_def, finprod_mem_coe_finset, Finset.prod_const,
    Finset.prod_eq_one fun w _ ↦ hr w, mul_one]

omit [NumberField K] in
/-- A system with Hasse sign `-1` exactly at the finite places of `T` has all finite Hasse signs
trivial exactly when `T` is empty. -/
theorem forall_finiteHasse_eq_one_iff_eq_empty
    (hs : I.finiteHasse = (T : Set (HeightOneSpectrum (𝓞 K))).mulIndicator fun _ ↦ -1) :
    (∀ v, I.finiteHasse v = 1) ↔ T = ∅ := by
  refine ⟨fun h ↦ Finset.eq_empty_of_forall_notMem fun v hv ↦ ?_, fun hT v ↦ ?_⟩
  · have hv' := h v
    rw [hs, Set.mulIndicator_of_mem (Finset.mem_coe.2 hv)] at hv'
    exact absurd hv' (by decide)
  · rw [hs, hT, Finset.coe_empty, Set.mulIndicator_empty]

/-- **The positive-definite systems of trivial discriminant.** In rank `n ≥ 3`, the system with
trivial global discriminant, positive index `n` at every real place and Hasse sign `-1` exactly at
the finite places of `T` is admissible exactly when `T` has even cardinality. -/
theorem isAdmissible_positiveDefinite_iff_even_card {n : ℕ} (hn : 3 ≤ n) :
    (⟨n, 0, (T : Set _).mulIndicator fun _ ↦ -1, fun _ ↦ n⟩ :
      GlobalFormInvariants K).IsAdmissible ↔ Even T.card := by
  have hprod := hasseProduct_eq_neg_one_pow_card
    (⟨n, 0, (T : Set _).mulIndicator fun _ ↦ -1, fun _ ↦ n⟩ : GlobalFormInvariants K) T rfl
    fun w ↦ by simp [realHasse_def, realNegativeIndex_def]
  refine ⟨fun hI ↦ ?_, fun hT ↦ ⟨by dsimp only; omega, fun _ ↦ le_rfl, fun w ↦ ?_,
    T.finite_toSet.subset Set.mulSupport_mulIndicator_subset,
    fun h ↦ by dsimp only at h; omega, fun h ↦ by dsimp only at h; omega, ?_⟩⟩
  · rw [← neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1), ← hprod]
    exact hI.hasseProduct_eq_one
  · simp [discrAtRealPlace_def, realNegativeIndex_def]
  · rw [hprod, hT.neg_one_pow]

/-- **The rank-one exception.** The rank-one system with trivial discriminant, positive index `1`
at every real place and Hasse sign `-1` exactly at the finite places of `T` is admissible only for
`T = ∅`, although its Hasse signs have finite support and, for `#T` even, product one
(`hasseProduct_eq_neg_one_pow_card`). -/
theorem isAdmissible_rankOne_iff_eq_empty :
    (⟨1, 0, (T : Set _).mulIndicator fun _ ↦ -1, fun _ ↦ 1⟩ :
      GlobalFormInvariants K).IsAdmissible ↔ T = ∅ := by
  have hprod := hasseProduct_eq_neg_one_pow_card
    (⟨1, 0, (T : Set _).mulIndicator fun _ ↦ -1, fun _ ↦ 1⟩ : GlobalFormInvariants K) T rfl
    fun w ↦ by simp [realHasse_def, realNegativeIndex_def]
  refine ⟨fun hI ↦ ?_, fun hT ↦ ?_⟩
  · exact (forall_finiteHasse_eq_one_iff_eq_empty _ T rfl).1
      (hI.finiteHasse_eq_one_of_rank_eq_one rfl)
  · subst hT
    refine ⟨le_rfl, fun _ ↦ le_rfl, fun w ↦ ?_,
      (∅ : Finset (HeightOneSpectrum (𝓞 K))).finite_toSet.subset
        Set.mulSupport_mulIndicator_subset,
      fun _ v ↦ by simp, fun h ↦ by dsimp only at h; omega, by rw [hprod]; simp⟩
    simp [discrAtRealPlace_def, realNegativeIndex_def]

/-- **The rank-two exception.** The rank-two system with discriminant the class of `-1`, positive
index `1` at every real place and Hasse sign `-1` exactly at the finite places of `T` is admissible
only for `T = ∅`, although its Hasse signs have finite support and, for `#T` even, product one
(`hasseProduct_eq_neg_one_pow_card`). -/
theorem isAdmissible_rankTwo_iff_eq_empty :
    (⟨2, squareClass (-1), (T : Set _).mulIndicator fun _ ↦ -1, fun _ ↦ 1⟩ :
      GlobalFormInvariants K).IsAdmissible ↔ T = ∅ := by
  have hprod := hasseProduct_eq_neg_one_pow_card
    (⟨2, squareClass (-1), (T : Set _).mulIndicator fun _ ↦ -1, fun _ ↦ 1⟩ :
      GlobalFormInvariants K) T rfl
    fun w ↦ by simp [realHasse_def, realNegativeIndex_def]
  -- The image of `-1` in every completion is `-1`.
  have hdisc (v : HeightOneSpectrum (𝓞 K)) :
      (⟨2, squareClass (-1), (T : Set _).mulIndicator fun _ ↦ -1, fun _ ↦ 1⟩ :
        GlobalFormInvariants K).discrAtFinitePlace v = squareClass (-1) := by
    simp [discrAtFinitePlace_def]
  refine ⟨fun hI ↦ ?_, fun hT ↦ ?_⟩
  · exact (forall_finiteHasse_eq_one_iff_eq_empty _ T rfl).1
      fun v ↦ hI.finiteHasse_eq_one_of_rank_eq_two rfl v (hdisc v)
  · subst hT
    refine ⟨by dsimp only; omega, fun _ ↦ by dsimp only; omega, fun w ↦ ?_,
      (∅ : Finset (HeightOneSpectrum (𝓞 K))).finite_toSet.subset
        Set.mulSupport_mulIndicator_subset,
      fun h ↦ by dsimp only at h; omega, fun _ v _ ↦ by simp, by rw [hprod]; simp⟩
    simp [discrAtRealPlace_def, realNegativeIndex_def, one_nsmul]

end Examples

end GlobalFormInvariants

end TauCeti.NumberField.QuadraticForm
