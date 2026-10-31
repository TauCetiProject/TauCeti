/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.RingTheory.GradedAlgebra.Cotangent

/-!
# Connected graded algebras that are regular at the vertex

Let `A` be an `ℕ`-graded algebra over a field `k` which is *connected*: its degree-zero part
consists of the scalars. Write `A₊` for the irrelevant ideal, the vertex of `Spec A`. If the local
ring `A_{A₊}` is regular of dimension `n`, then `A` is a polynomial algebra over `k` on `n`
homogeneous elements of positive degree.

The proof lifts `n` generators of the maximal ideal of `A_{A₊}` to `A`. Since every element
outside `A₊` has a nonzero constant term, the lifts span the `k`-vector space `A₊ ⧸ A₊²`. This
space is spanned by the classes of homogeneous elements, so at most
`n` homogeneous elements of positive degree span it, and by the graded Nakayama lemma
(`TauCeti.GradedAlgebra.surjective_aeval_of_irrelevant_le`) they generate `A` as a `k`-algebra.
Thus `A` is a quotient of a polynomial ring in at most `n` variables, while `A` has Krull
dimension at least `n`, the dimension of its localization. So exactly `n` generators were
needed, and the evaluation map is an isomorphism
(`TauCeti.GradedAlgebra.bijective_aeval_of_irrelevant_le`).

No Noetherian hypothesis on `A` is needed: finite generation is a consequence.

For the invariants of a finite linear group this gives the last step of the homological proof of
the Chevalley–Shephard–Todd theorem: once the invariant ring is known to be regular at its
vertex, it is a polynomial algebra on homogeneous basic invariants.

## Main results

* `TauCeti.GradedAlgebra.exists_sub_algebraMap_mem_irrelevant`: in a connected graded algebra
  every element is a scalar plus an element of the irrelevant ideal.
* `TauCeti.GradedAlgebra.exists_bijective_aeval_of_isRegularLocalRing`: a connected graded algebra
  over a field whose localization at the irrelevant ideal is a regular local ring of dimension
  `n` is a polynomial algebra on `n` homogeneous elements of positive degree.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), § 18.
* W. Bruns, J. Herzog, *Cohen–Macaulay Rings*, Cambridge University Press (1993), Sections 1.5
  and 2.2.
-/

public section

open DirectSum IsLocalRing Submodule

namespace TauCeti.GradedAlgebra

/-- In a connected graded algebra, whose degree-zero part consists of the scalars, every element
is a scalar plus an element of the irrelevant ideal. -/
theorem exists_sub_algebraMap_mem_irrelevant {R A : Type*} [CommSemiring R] [CommRing A]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra R A)) (a : A) :
    ∃ c : R, a - algebraMap R A c ∈ HomogeneousIdeal.irrelevant 𝒜 := by
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (h𝒜 _ (decompose 𝒜 a 0).2)
  refine ⟨c, ?_⟩
  rw [HomogeneousIdeal.mem_irrelevant_iff, map_sub, hc, GradedRing.proj_apply,
    GradedRing.proj_apply, decompose_of_mem_same 𝒜 (decompose 𝒜 a 0).2, sub_self]

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  [GradedAlgebra 𝒜]

/-- If `u * x` lies in the ideal spanned by elements `aᵢ ∈ A₊`, where `x ∈ A₊` and `u ∉ A₊`,
then `x` is a `k`-linear combination of the `aᵢ` modulo `A₊²`: write `u` and the coefficients
as scalars plus elements of `A₊`, and note that the constant term of `u` is nonzero. -/
private theorem mem_span_sup_of_mul_mem (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A)) {n : ℕ}
    {a : Fin n → A} (ha : ∀ i, a i ∈ HomogeneousIdeal.irrelevant 𝒜) {u x : A}
    (hu : u ∉ HomogeneousIdeal.irrelevant 𝒜) (hx : x ∈ HomogeneousIdeal.irrelevant 𝒜)
    (hux : u * x ∈ Ideal.span (Set.range a)) :
    x ∈ span k (Set.range a) ⊔
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ 2).restrictScalars k := by
  set m := (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  obtain ⟨r, hr⟩ := (mem_span_range_iff_exists_fun A).1 hux
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_irrelevant 𝒜 h𝒜 u
  choose d hd using fun i ↦ exists_sub_algebraMap_mem_irrelevant 𝒜 h𝒜 (r i)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hu (by simpa using hc)
  have hsq {y z : A} (hy : y ∈ m) (hz : z ∈ m) : y * z ∈ m ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hy hz
  -- `c x = ∑ dᵢ aᵢ + (∑ (rᵢ - dᵢ) aᵢ - (u - c) x)`, and the bracket lies in `A₊²`.
  have hx' : x = c⁻¹ • ∑ i, d i • a i +
      c⁻¹ • (∑ i, (r i - algebraMap k A (d i)) * a i - (u - algebraMap k A c) * x) := by
    rw [← smul_add, eq_inv_smul_iff₀ hc0]
    simp only [smul_eq_mul, Algebra.smul_def, sub_mul, Finset.sum_sub_distrib] at hr ⊢
    rw [hr]
    ring
  rw [hx']
  refine add_mem_sup (smul_mem _ _ (sum_mem fun i _ ↦ smul_mem _ _ (subset_span ⟨i, rfl⟩)))
    (smul_mem _ _ (sub_mem (sum_mem fun i _ ↦ hsq (hd i) (ha i)) (hsq hc hx)))

/-- If the localization of a connected graded algebra at the irrelevant ideal `A₊` is a regular
local ring of dimension `n`, then there are `n` elements of `A₊` spanning `A₊` modulo `A₊²` over
`k`. -/
private theorem exists_irrelevant_le_span_sup (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    [IsRegularLocalRing (Localization.AtPrime P)] {n : ℕ}
    (hn : ringKrullDim (Localization.AtPrime P) = n) :
    ∃ a : Fin n → A, (HomogeneousIdeal.irrelevant 𝒜).toIdeal.restrictScalars k ≤
      span k (Set.range a) ⊔ ((HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ 2).restrictScalars k := by
  subst hP
  set m := (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  -- Generators of the maximal ideal of `A_{A₊}`, written as fractions `aᵢ / uᵢ`.
  obtain ⟨s, hs, hspan⟩ := (IsNoetherian.noetherian (maximalIdeal (Localization.AtPrime m))
    ).exists_span_finset_card_eq_spanFinrank
  have hcard : s.card = n := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime m)
    rw [hn] at this
    exact hs.trans (by exact_mod_cast this)
  let e := s.equivFinOfCardEq hcard
  choose a u hau using fun i ↦
    IsLocalization.exists_mk'_eq m.primeCompl ((e.symm i : s) : Localization.AtPrime m)
  have hmax : maximalIdeal (Localization.AtPrime m) ≤
      (Ideal.span (Set.range a)).map (algebraMap A (Localization.AtPrime m)) := by
    rw [← hspan, span_le]
    intro y hy
    rw [show y = (e.symm (e ⟨y, hy⟩) : _) by simp, ← hau, SetLike.mem_coe,
      IsLocalization.mk'_mem_iff]
    exact Ideal.mem_map_of_mem _ (subset_span ⟨_, rfl⟩)
  have ha (i : Fin n) : a i ∈ m := by
    have hy : (e.symm i : Localization.AtPrime m) ∈ maximalIdeal _ :=
      hspan ▸ subset_span (e.symm i).2
    rwa [← hau, IsLocalization.mk'_mem_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m] at hy
  refine ⟨a, fun x hx ↦ ?_⟩
  have hx' : algebraMap A (Localization.AtPrime m) x ∈ maximalIdeal _ :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m x).2 hx
  obtain ⟨w, hw, hwx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff m.primeCompl _ _ x).1 (hmax hx')
  exact mem_span_sup_of_mul_mem 𝒜 h𝒜 ha hw hx hwx

/-- If `n` elements span `A₊` modulo `A₊²` over `k`, then so do at most `n` homogeneous elements
of positive degree, which therefore span the ideal `A₊` modulo `A₊²`. -/
private theorem exists_homogeneous_irrelevant_le_span_sup {n : ℕ} (a : Fin n → A)
    (ha : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.restrictScalars k ≤
      span k (Set.range a) ⊔ ((HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ 2).restrictScalars k) :
    ∃ t ≤ n, ∃ f : Fin t → A, (∀ i, ∃ d, 0 < d ∧ f i ∈ 𝒜 d) ∧
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
        Ideal.span (Set.range f) ⊔ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ 2 := by
  classical
  set m := (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  set N := (m ^ 2).restrictScalars k
  set H : Set A := {x | ∃ d, 0 < d ∧ x ∈ 𝒜 d}
  -- Work in the `k`-vector space `A ⧸ A₊²`.
  have hHm : span k H ≤ m.restrictScalars k :=
    span_le.2 fun x ⟨d, hd, hx⟩ ↦ HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hx
  have hmH : m.restrictScalars k ≤ span k H := by
    intro x hx
    rw [← sum_support_decompose 𝒜 x]
    refine sum_mem fun d hd ↦ subset_span ⟨d, Nat.pos_of_ne_zero ?_, (decompose 𝒜 x d).2⟩
    rintro rfl
    exact DFinsupp.mem_support_iff.1 hd (Subtype.ext hx)
  obtain ⟨b, hbH, hbspan, hbli⟩ := exists_linearIndependent k (N.mkQ '' H)
  have hle : span k b ≤ span k (Set.range (N.mkQ ∘ a)) := by
    rw [hbspan, span_image, Set.range_comp, span_image, ← sup_eq_left.2 (show
      (N.map N.mkQ) ≤ (span k (Set.range a)).map N.mkQ by simp), ← Submodule.map_sup]
    exact map_mono (hHm.trans ha)
  have hb : b.Finite := by
    have : Finite (Set.range (N.mkQ ∘ a)) := Set.finite_range _
    have hbsub : Set.range ((↑) : b → A ⧸ N) ≤ span k (Set.range (N.mkQ ∘ a)) := by
      rw [Subtype.range_coe]
      exact fun y hy ↦ hle (subset_span hy)
    exact Set.finite_coe_iff.1 (hbli.finite_of_le_span_finite _ _ hbsub)
  have hbcard : Nat.card b ≤ n := by
    have := FiniteDimensional.span_of_finite k (Set.finite_range (N.mkQ ∘ a))
    rw [Nat.card_coe_set_eq, ← finrank_span_set_eq_ncard hbli]
    exact (finrank_mono hle).trans (finrank_range_le_card _) |>.trans (by simp)
  have := hb.to_subtype
  let e := Finite.equivFin b
  choose f hfH hf using fun i ↦ hbH (e.symm i).2
  refine ⟨Nat.card b, hbcard, f, hfH, fun x hx ↦ ?_⟩
  -- The class of `x` is a combination of the classes of the `fᵢ`.
  have hxb : N.mkQ x ∈ span k b := by
    rw [hbspan, span_image]
    exact mem_map_of_mem (hmH hx)
  have hbf : span k b ≤ (span k (Set.range f)).map N.mkQ := by
    rw [← span_image, span_le]
    intro y hy
    refine subset_span ⟨f (e ⟨y, hy⟩), ⟨_, rfl⟩, ?_⟩
    have := hf (e ⟨y, hy⟩)
    rwa [e.symm_apply_apply] at this
  obtain ⟨z, hz, hzx⟩ := hbf hxb
  have hxz : x - z ∈ m ^ 2 := by
    simpa [N, sub_eq_zero, Submodule.Quotient.eq] using hzx.symm
  rw [show x = z + (x - z) by abel]
  exact add_mem_sup ((span_le_restrictScalars k A _) hz) hxz

/-- **A connected graded algebra regular at its vertex is a polynomial algebra.** Let `A` be an
`ℕ`-graded algebra over a field `k` whose degree-zero part consists of the scalars. If its
localization at the irrelevant ideal `A₊` is a regular local ring of dimension `n`, then there are
`n` homogeneous elements of positive degree `f₁, …, fₙ` such that `k[X₁, …, Xₙ] → A`,
`Xᵢ ↦ fᵢ`, is an isomorphism.

The prime `P` is any prime equal to `A₊`, so that the statement applies to an ideal presented in
another form. -/
theorem exists_bijective_aeval_of_isRegularLocalRing (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    [IsRegularLocalRing (Localization.AtPrime P)] {n : ℕ}
    (hn : ringKrullDim (Localization.AtPrime P) = n) :
    ∃ f : Fin n → A, (∀ i, ∃ d, 0 < d ∧ f i ∈ 𝒜 d) ∧
      Function.Bijective (MvPolynomial.aeval (R := k) f) := by
  obtain ⟨a, ha⟩ := exists_irrelevant_le_span_sup 𝒜 h𝒜 P hP hn
  obtain ⟨t, htn, f, hf, hm⟩ := exists_homogeneous_irrelevant_le_span_sup 𝒜 a ha
  -- By the graded Nakayama lemma, the `fᵢ` generate `A`.
  have hsurj := surjective_aeval_of_irrelevant_le 𝒜 h𝒜 hf hm
  -- Compare Krull dimensions: `n ≤ dim A ≤ t ≤ n`.
  have hnA : (n : WithBot ℕ∞) ≤ ringKrullDim A := by
    rw [← hn, IsLocalization.AtPrime.ringKrullDim_eq_height P]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  have hAt : ringKrullDim A ≤ t := by
    simpa using ringKrullDim_le_of_surjective _ hsurj
  obtain rfl : t = n := le_antisymm htn (by exact_mod_cast hnA.trans hAt)
  exact ⟨f, hf, bijective_aeval_of_irrelevant_le 𝒜 h𝒜 hf hm (by simpa using hnA)⟩

end TauCeti.GradedAlgebra
