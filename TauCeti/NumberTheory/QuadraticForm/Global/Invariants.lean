/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Discriminant
public import TauCeti.NumberTheory.QuadraticForm.Global.RealHasse

/-!
# Systems of local invariants of quadratic forms over a number field

A regular quadratic form of positive rank over a number field `K` determines

* its rank `n`;
* its global discriminant `d ∈ Kˣ/(Kˣ)²`;
* a Hasse sign `s_v ∈ {±1}` at every finite place `v`;
* its positive index `p_w` at every real place `w`.

This file defines the carrier `GlobalFormInvariants K` of such data, and the predicate
`GlobalFormInvariants.IsAdmissible` cutting out the systems that can occur. By the
Hasse–Minkowski theorem and the existence theorem for forms with prescribed local behaviour, these
are exactly the invariant systems of regular global forms (O'Meara 66:5 and 72:1).

The discriminant is stored once, globally; the local discriminants are its images
`GlobalFormInvariants.finiteDiscr` and `GlobalFormInvariants.realDiscr` under the place maps. The
local data at a finite place `v` are the triple `(n, finiteDiscr v, finiteHasse v)`, and at a real
place `w` they are `(n, realDiscr w, p_w)` with negative index `n - p_w`. The archimedean Hasse sign
at `w` is `(-1)^((n - p_w)(n - p_w - 1)/2)`, the value of `∏_{i<j} (aᵢ, aⱼ)_w` for a diagonalization
`⟨a₁, …, aₙ⟩` (`realHasse_eq_prod_hilbertSymbol`).

Admissibility consists of the conditions

1. `1 ≤ n`;
2. `p_w ≤ n` and `d` has sign `(-1)^(n - p_w)` at every real place `w`;
3. `s_v = 1` at all but finitely many finite places;
4. the two small-rank local realization constraints: in rank one every `s_v` is `1`, and in rank
   two `s_v = 1` wherever `d` is the class of `-1` at `v`;
5. the product of all finite Hasse signs and all real Hasse signs is `1`.

Finite support and the product formula alone do not suffice: a rank-one form has trivial Hasse
invariant at every place, and a binary form of discriminant `-1` is a hyperbolic plane, whose
Hasse invariant is trivial. The product is a `finprod`; `hasseProduct_eq_prod_mul_prod` computes
it over any finite set of places outside which the finite signs are `1`, so condition 5 does not
depend on a chosen support.

## Main definitions

* `TauCeti.NumberField.QuadraticForm.GlobalFormInvariants`: rank, global discriminant, finite
  Hasse signs, and real positive indices.
* `GlobalFormInvariants.hasseProduct`: the product of all finite and real Hasse signs.
* `GlobalFormInvariants.IsAdmissible`: the admissibility conditions above.

## Main results

* `GlobalFormInvariants.exists_finset_prod_mul_prod_eq_one_iff`: the product condition may be
  checked on any finite support.
* `GlobalFormInvariants.IsAdmissible.of_nondegenerate`: for a system whose rank, discriminant and
  real indices are those of a regular global form, the archimedean conditions hold automatically.
* `GlobalFormInvariants.realHasse_eq_prod_hilbertSymbol`: the real Hasse sign of such a system is
  the product of the real Hilbert symbols of a diagonalization.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:20–23, 66:5–6, 71:18
  and 72:1.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, AMS (2005), Chapter VI.
-/

public section
noncomputable section

open Finset IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap

namespace TauCeti.NumberField.QuadraticForm

variable (K : Type*) [Field K]

/-- A **system of local invariants** of a quadratic form over a number field `K`: a rank, one
global discriminant class, a Hasse sign at every finite place, and a positive index at every real
place. Whether the system comes from a form is `GlobalFormInvariants.IsAdmissible`. -/
@[ext]
structure GlobalFormInvariants where
  /-- The rank `n`. -/
  rank : ℕ
  /-- The global discriminant `d ∈ Kˣ/(Kˣ)²`. -/
  discr : SquareClassGroup K
  /-- The Hasse sign `s_v ∈ {±1}` at a finite place `v`. -/
  finiteHasse : HeightOneSpectrum (𝓞 K) → ℤˣ
  /-- The positive index `p_w` at a real place `w`. -/
  realPositiveIndex : {w : InfinitePlace K // w.IsReal} → ℕ

namespace GlobalFormInvariants

variable {K} (I : GlobalFormInvariants K)

/-- The discriminant at a real place `w`: the image of the global discriminant in the square
classes of `ℝ`, that is, its sign at `w`. -/
def realDiscr (w : {w : InfinitePlace K // w.IsReal}) : SquareClassGroup ℝ :=
  (embedding_of_isReal w.2).squareClassMap I.discr

/-- The negative index `n - p_w` at a real place `w`. -/
def realNegativeIndex (w : {w : InfinitePlace K // w.IsReal}) : ℕ :=
  I.rank - I.realPositiveIndex w

/-- The Hasse sign at a real place `w`: `(-1)^(q(q-1)/2)` for the negative index `q = n - p_w`,
the value of `∏_{i<j} (aᵢ, aⱼ)_w` on a real diagonal form `⟨a₁, …, aₙ⟩` with `q` negative
coefficients. -/
def realHasse (w : {w : InfinitePlace K // w.IsReal}) : ℤˣ :=
  (-1) ^ (I.realNegativeIndex w).choose 2

/-- The product of the Hasse signs over all finite and real places, as a `finprod` over each.
The finite factor is the product over any finite set outside which the finite Hasse signs are `1`
(`hasseProduct_eq_prod_mul_prod`). -/
def hasseProduct : ℤˣ :=
  (∏ᶠ v, I.finiteHasse v) * ∏ᶠ w, I.realHasse w

theorem realDiscr_def (w : {w : InfinitePlace K // w.IsReal}) :
    I.realDiscr w = (embedding_of_isReal w.2).squareClassMap I.discr := (rfl)

theorem realNegativeIndex_def (w : {w : InfinitePlace K // w.IsReal}) :
    I.realNegativeIndex w = I.rank - I.realPositiveIndex w := (rfl)

theorem realHasse_def (w : {w : InfinitePlace K // w.IsReal}) :
    I.realHasse w = (-1) ^ (I.realNegativeIndex w).choose 2 := (rfl)

theorem hasseProduct_def : I.hasseProduct = (∏ᶠ v, I.finiteHasse v) * ∏ᶠ w, I.realHasse w :=
  (rfl)

/-- When the positive index at `w` is at most the rank, the positive and negative indices add
to the rank. -/
theorem realPositiveIndex_add_realNegativeIndex {w : {w : InfinitePlace K // w.IsReal}}
    (hw : I.realPositiveIndex w ≤ I.rank) :
    I.realPositiveIndex w + I.realNegativeIndex w = I.rank :=
  Nat.add_sub_cancel' hw

/-- **Independence of the support.** Over any finite set of places outside which the finite
Hasse signs are `1`, the product of the Hasse signs is the finite product over that set times the
real Hasse signs. -/
theorem hasseProduct_eq_prod_mul_prod (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, I.finiteHasse v = 1) :
    I.hasseProduct = (∏ v ∈ S, I.finiteHasse v) * ∏ᶠ w, I.realHasse w := by
  rw [hasseProduct, finprod_eq_prod_of_mulSupport_subset]
  intro v hv
  by_contra hvS
  exact hv (hS v hvS)

/-- The product condition holds on some finite support exactly when the finite Hasse signs have
finite support and the product of all Hasse signs is `1`. In particular, it holds on one finite
support if and only if it holds on every one. -/
theorem exists_finset_prod_mul_prod_eq_one_iff :
    (∃ S : Finset (HeightOneSpectrum (𝓞 K)), (∀ v ∉ S, I.finiteHasse v = 1) ∧
        (∏ v ∈ S, I.finiteHasse v) * ∏ᶠ w, I.realHasse w = 1) ↔
      (Function.mulSupport I.finiteHasse).Finite ∧ I.hasseProduct = 1 := by
  constructor
  · rintro ⟨S, hS, hprod⟩
    refine ⟨S.finite_toSet.subset fun v hv => ?_, by rwa [I.hasseProduct_eq_prod_mul_prod S hS]⟩
    by_contra hvS
    exact hv (hS v hvS)
  · rintro ⟨hfin, hprod⟩
    have hS : ∀ v ∉ hfin.toFinset, I.finiteHasse v = 1 := fun v hv => by simpa using hv
    exact ⟨hfin.toFinset, hS, by rwa [← I.hasseProduct_eq_prod_mul_prod _ hS]⟩

section Form

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Q : _root_.QuadraticForm K V}

/-- If a system has the rank and the positive index at `w` of a regular form, it has the negative
index of that form at `w`. -/
theorem realNegativeIndex_eq_of_nondegenerate (hQ : Q.Nondegenerate)
    (hrank : I.rank = Module.finrank K V) {w : {w : InfinitePlace K // w.IsReal}}
    (hw : I.realPositiveIndex w = Q.realPositiveIndex w) :
    I.realNegativeIndex w = Q.realNegativeIndex w := by
  have := _root_.QuadraticForm.realPositiveIndex_add_realNegativeIndex_eq_finrank hQ w
  rw [realNegativeIndex, hrank, hw]
  omega

/-- If a system has the rank and the positive index at `w` of a regular form diagonalized as
`⟨a₁, …, aₙ⟩` by global units, its real Hasse sign at `w` is `∏_{i<j} (aᵢ, aⱼ)_w`. -/
theorem realHasse_eq_prod_hilbertSymbol {ι : Type*} [Fintype ι] [LinearOrder ι] {a : ι → Kˣ}
    (hQ : Q.Nondegenerate) (ha : Q.Equivalent (weightedSumSquares K fun i ↦ (a i : K)))
    (hrank : I.rank = Module.finrank K V) {w : {w : InfinitePlace K // w.IsReal}}
    (hw : I.realPositiveIndex w = Q.realPositiveIndex w) :
    I.realHasse w = ∏ ij ∈ univ.filter (fun ij : ι × ι => ij.1 < ij.2),
      hilbertSymbol (unitAtRealPlace w (a ij.1)) (unitAtRealPlace w (a ij.2)) := by
  rw [prod_hilbertSymbol_unitAtRealPlace_of_equiv_weightedSumSquares ha w, realHasse,
    I.realNegativeIndex_eq_of_nondegenerate hQ hrank hw]

end Form

section NumberField

variable [NumberField K]

/-- The discriminant at a finite place `v`: the image of the global discriminant in the square
classes of the completion `K_v`. -/
def finiteDiscr (v : HeightOneSpectrum (𝓞 K)) : SquareClassGroup (v.adicCompletion K) :=
  (algebraMap K (v.adicCompletion K)).squareClassMap I.discr

theorem finiteDiscr_def (v : HeightOneSpectrum (𝓞 K)) :
    I.finiteDiscr v = (algebraMap K (v.adicCompletion K)).squareClassMap I.discr := (rfl)

/-- **Admissibility** of a system of local invariants: the conditions satisfied by the invariants
of every regular global form of positive rank, and by the Hasse–Minkowski and existence theorems
only by those. The two small-rank conditions are the local realization constraints: in rank one
every Hasse sign is `1`, and in rank two the Hasse sign is `1` wherever the discriminant is the
class of `-1`. -/
structure IsAdmissible : Prop where
  /-- The rank is positive. -/
  one_le_rank : 1 ≤ I.rank
  /-- At every real place the positive index is at most the rank. -/
  realPositiveIndex_le_rank (w : {w : InfinitePlace K // w.IsReal}) :
    I.realPositiveIndex w ≤ I.rank
  /-- At every real place the discriminant has sign `(-1)^(n - p_w)`. -/
  realDiscr_eq (w : {w : InfinitePlace K // w.IsReal}) :
    I.realDiscr w = I.realNegativeIndex w • squareClass (-1 : ℝˣ)
  /-- The finite Hasse signs are `1` at all but finitely many places. -/
  finite_mulSupport_finiteHasse : (Function.mulSupport I.finiteHasse).Finite
  /-- In rank one every finite Hasse sign is `1`. -/
  finiteHasse_eq_one_of_rank_eq_one : I.rank = 1 → ∀ v, I.finiteHasse v = 1
  /-- In rank two the finite Hasse sign is `1` wherever the discriminant is the class of `-1`. -/
  finiteHasse_eq_one_of_rank_eq_two_of_finiteDiscr_eq_neg_one :
    I.rank = 2 → ∀ v, I.finiteDiscr v = squareClass (-1) → I.finiteHasse v = 1
  /-- The product of all finite and real Hasse signs is `1`. -/
  hasseProduct_eq_one : I.hasseProduct = 1

namespace IsAdmissible

variable {I}

/-- For an admissible system, the product of the finite Hasse signs over any finite set outside
which they are `1`, times the real Hasse signs, is `1`. -/
theorem prod_mul_prod_eq_one (h : I.IsAdmissible) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, I.finiteHasse v = 1) :
    (∏ v ∈ S, I.finiteHasse v) * ∏ᶠ w, I.realHasse w = 1 := by
  rw [← I.hasseProduct_eq_prod_mul_prod S hS, h.hasseProduct_eq_one]

/-- For an admissible system, the discriminant is positive at a real place exactly when the
negative index there is even. -/
theorem realDiscr_eq_zero_iff (h : I.IsAdmissible) (w : {w : InfinitePlace K // w.IsReal}) :
    I.realDiscr w = 0 ↔ Even (I.realNegativeIndex w) := by
  rw [h.realDiscr_eq, nsmul_squareClass_neg_one_eq_zero_iff_even]

end IsAdmissible

/-- The system of rank `n ≥ 1` with trivial discriminant, trivial finite Hasse signs and positive
index `n` at every real place is admissible. These are the invariants of the sum of `n` squares. -/
theorem isAdmissible_mk_zero_one {n : ℕ} (hn : 1 ≤ n) :
    (⟨n, 0, 1, fun _ ↦ n⟩ : GlobalFormInvariants K).IsAdmissible where
  one_le_rank := hn
  realPositiveIndex_le_rank _ := le_rfl
  realDiscr_eq _ := by simp [realDiscr, realNegativeIndex]
  finite_mulSupport_finiteHasse := by simp
  finiteHasse_eq_one_of_rank_eq_one _ _ := rfl
  finiteHasse_eq_one_of_rank_eq_two_of_finiteDiscr_eq_neg_one _ _ _ := rfl
  hasseProduct_eq_one := by simp [hasseProduct, realHasse, realNegativeIndex]

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Q : _root_.QuadraticForm K V}

/-- **The archimedean conditions are automatic for a global form.** A system whose rank,
discriminant and real positive indices are those of a regular form over `K` is admissible as
soon as it has positive rank and satisfies the conditions at the finite places and the product
condition. -/
theorem IsAdmissible.of_nondegenerate (hQ : Q.Nondegenerate)
    (hrank : I.rank = Module.finrank K V)
    (hdiscr : letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
      I.discr = RegularFormClass.discr (formClass Q hQ))
    (hindex : ∀ w, I.realPositiveIndex w = Q.realPositiveIndex w)
    (one_le_rank : 1 ≤ I.rank)
    (finite_mulSupport_finiteHasse : (Function.mulSupport I.finiteHasse).Finite)
    (finiteHasse_eq_one_of_rank_eq_one : I.rank = 1 → ∀ v, I.finiteHasse v = 1)
    (finiteHasse_eq_one_of_rank_eq_two_of_finiteDiscr_eq_neg_one :
      I.rank = 2 → ∀ v, I.finiteDiscr v = squareClass (-1) → I.finiteHasse v = 1)
    (hasseProduct_eq_one : I.hasseProduct = 1) :
    I.IsAdmissible where
  one_le_rank := one_le_rank
  realPositiveIndex_le_rank w := by
    have := _root_.QuadraticForm.realPositiveIndex_add_realNegativeIndex_eq_finrank hQ w
    rw [hrank, hindex]
    omega
  realDiscr_eq w := by
    rw [realDiscr, hdiscr, I.realNegativeIndex_eq_of_nondegenerate hQ hrank (hindex w),
      _root_.QuadraticForm.squareClassMap_discr_formClass_eq_realNegativeIndex_nsmul]
  finite_mulSupport_finiteHasse := finite_mulSupport_finiteHasse
  finiteHasse_eq_one_of_rank_eq_one := finiteHasse_eq_one_of_rank_eq_one
  finiteHasse_eq_one_of_rank_eq_two_of_finiteDiscr_eq_neg_one :=
    finiteHasse_eq_one_of_rank_eq_two_of_finiteDiscr_eq_neg_one
  hasseProduct_eq_one := hasseProduct_eq_one

end NumberField

end GlobalFormInvariants

end TauCeti.NumberField.QuadraticForm
