/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# Normalising rational presentations with a pseudouniformiser power

Let `A` be a commutative ring with separately continuous multiplication, `A⁺` an open subring of
`A`, and `ϖ` a pseudouniformiser of `A` (a topologically nilpotent unit). Every rational subset
`R(T₀/s₀)` of `Spa(A, A⁺)` whose numerators generate the unit ideal of `A` admits a normalised
presentation
```text
R(T₀/s₀) = R((insert (ϖ ^ N) T) / s)
```
with `0 < N`, `insert (ϖ ^ N) T ⊆ A⁺`, and `s ∈ A⁺`.

Two facts enter:
1. Because `ϖ` is a topologically nilpotent unit and `A⁺` is open, multiplying every numerator and
   the denominator by a single power `ϖ ^ k` moves them into `A⁺` without changing either the
   rational subset (`rationalSubset_image_mul_right`) or the fact that the numerators generate the
   unit ideal.
2. Writing `1 = ∑ t ∈ T, c_t * t` and choosing `N ≥ 1` large enough that `ϖ ^ N ∈ A⁺` and every
   `c_t * ϖ ^ N ∈ A⁺`, any point `v ∈ R(T/s)` satisfies `v(c_t * ϖ ^ N) ≤ 1` and `v(t) ≤ v(s)`,
   hence `v(ϖ ^ N) ≤ v(s)` by the ultrametric sum bound. Adjoining `ϖ ^ N` to `T` therefore leaves
   `R(T/s)` unchanged (`rationalSubset_insert_of_forall_vle`).

For a Tate ring `A`, every open ideal is the unit ideal (`IsTateRing.isOpen_iff_eq_top`), so every
member of `spaRationalFamily A⁺` has such a presentation. Including a unit `ϖ ^ N` explicitly among
the numerators is what ensures that pulling back numerators along a multiplicative map such as the
sharp map `B♭ → B` still generates the unit ideal; keeping all defining elements inside `A⁺` is the
starting point for integral models of rational localisations.

## Main results

* `TauCeti.ValuationSpectrum.exists_rationalSubset_eq_insert_pseudoUniformizer_pow`: every
  rational subset whose numerators span `⊤` can be presented inside `A⁺` with `ϖ ^ N` (`0 < N`)
  among its numerators.
* `TauCeti.ValuationSpectrum.exists_mem_spaRationalFamily_eq_insert_pseudoUniformizer_pow`: the
  corresponding statement for any `U ∈ spaRationalFamily A⁺` over a Tate ring `A`.

## References

* P. Scholze, *Perfectoid spaces*, proof of Theorem 6.3 and Lemma 6.4.
* P. Scholze, *Étale cohomology of diamonds*, proof of Theorem 3.12.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Proposition 3.1.7.
-/

public section

namespace TauCeti.ValuationSpectrum

open Filter Topology TauCeti.Huber

section General

variable {A : Type*} [CommRing A]

open scoped Classical in
/-- Multiplying a finite generating set on the right by a unit does not change the ideal it
spans. -/
private theorem span_image_mul_right (T : Finset A) {u : A} (hu : IsUnit u) :
    Ideal.span ((T.image fun t ↦ t * u : Finset A) : Set A) = Ideal.span (T : Set A) := by
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · intro _ hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact SetLike.mem_coe.mpr
      (Ideal.mul_mem_right u _ (Ideal.subset_span (Finset.mem_coe.mpr ht)))
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    intro t ht
    have hmem : t * u ∈ Ideal.span ((T.image fun t ↦ t * u : Finset A) : Set A) :=
      Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp ht)))
    exact SetLike.mem_coe.mpr
      (by simpa only [mul_assoc, hv, mul_one] using Ideal.mul_mem_right v _ hmem)

variable [TopologicalSpace A] [SeparatelyContinuousMul A]

open scoped Classical in
/-- **Normalised integral presentation of a rational subset with a pseudouniformiser power.** If
`A⁺` is an open subring, `ϖ` is a pseudouniformiser of `A`, and `T₀` generates the unit ideal of
`A`, then `R(T₀/s₀)` can be rewritten as `R((insert (ϖ ^ N) T) / s)` with `0 < N`, all numerators
(including `ϖ ^ N`) in `A⁺`, and `s ∈ A⁺`. -/
theorem exists_rationalSubset_eq_insert_pseudoUniformizer_pow {Aplus : Subring A}
    (hopen : IsOpen (Aplus : Set A)) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {T₀ : Finset A} (hspan : Ideal.span (T₀ : Set A) = ⊤) (s₀ : A) :
    ∃ (T : Finset A) (s : A) (N : ℕ),
      0 < N ∧
      ((insert (ϖ ^ N) T : Finset A) : Set A) ⊆ Aplus ∧
      s ∈ Aplus ∧
      rationalSubset Aplus (insert (ϖ ^ N) T) s = rationalSubset Aplus T₀ s₀ := by
  have hnil := hϖ.isTopologicallyNilpotent
  -- First scale `T₀` and `s₀` into the open subring `Aplus` by a single unit power `ϖ ^ k`.
  have hk_ev : ∀ᶠ k : ℕ in atTop, s₀ * ϖ ^ k ∈ Aplus ∧ ∀ t ∈ T₀, t * ϖ ^ k ∈ Aplus :=
    (eventually_mul_pow_mem_of_isTopologicallyNilpotent hnil hopen s₀).and <|
      (Filter.eventually_all_finset T₀).mpr fun t _ ↦
        eventually_mul_pow_mem_of_isTopologicallyNilpotent hnil hopen t
  obtain ⟨k, hs₁, hT₁_mem⟩ := hk_ev.exists
  let T : Finset A := T₀.image fun t ↦ t * ϖ ^ k
  let s : A := s₀ * ϖ ^ k
  have huk : IsUnit (ϖ ^ k) := hϖ.isUnit.pow k
  have hT_sub : (T : Set A) ⊆ Aplus := by
    intro _ hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact hT₁_mem t ht
  have hspanT : Ideal.span (T : Set A) = ⊤ :=
    (span_image_mul_right T₀ huk).trans hspan
  -- Write `1 = ∑ t ∈ T, c t * t` and absorb `1` and the finite family `c t` into `Aplus`.
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp
    (hspanT.symm ▸ Submodule.mem_top : (1 : A) ∈ Ideal.span (T : Set A))
  have hϖ_ev : ∀ᶠ N : ℕ in atTop, ϖ ^ N ∈ Aplus := by
    simpa only [one_mul] using eventually_mul_pow_mem_of_isTopologicallyNilpotent hnil hopen 1
  have hN_ev : ∀ᶠ N : ℕ in atTop,
      0 < N ∧ ϖ ^ N ∈ Aplus ∧ ∀ t ∈ T, c t * ϖ ^ N ∈ Aplus :=
    (Filter.eventually_gt_atTop 0).and <|
      hϖ_ev.and <|
        (Filter.eventually_all_finset T).mpr fun t _ ↦
          eventually_mul_pow_mem_of_isTopologicallyNilpotent hnil hopen (c t)
  obtain ⟨N, hN_pos, hϖN, hcN⟩ := hN_ev.exists
  refine ⟨T, s, N, hN_pos, ?_, hs₁, ?_⟩
  · rw [Finset.coe_insert, Set.insert_subset_iff]
    exact ⟨hϖN, hT_sub⟩
  · -- On `R(T/s)`, `ϖ ^ N = ∑ t ∈ T, (c t * ϖ ^ N) * t` is dominated by `s`.
    have hdom : ∀ v ∈ rationalSubset Aplus T s, v.toValuativeRel.vle (ϖ ^ N) s := by
      intro v hv
      obtain ⟨hv_spa, hvT, -⟩ := (mem_rationalSubset_iff Aplus T s v).mp hv
      rw [← valuation_le_iff]
      have hsum : ϖ ^ N = ∑ t ∈ T, (c t * ϖ ^ N) * t := by
        calc ϖ ^ N = (1 : A) * ϖ ^ N := (one_mul _).symm
          _ = (∑ t ∈ T, c t • t) * ϖ ^ N := by rw [hc]
          _ = ∑ t ∈ T, (c t * ϖ ^ N) * t := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun t _ ↦ ?_
            rw [smul_eq_mul]
            ring
      rw [hsum]
      refine v.valuation.map_sum_le fun t ht ↦ ?_
      rw [map_mul]
      simpa only [one_mul] using mul_le_mul'
        (valuation_le_one_of_mem_spa hv_spa (hcN t ht))
        ((valuation_le_iff v t s).mpr (hvT t ht))
    rw [rationalSubset_insert_of_forall_vle Aplus T s (ϖ ^ N) hdom]
    exact rationalSubset_image_mul_right Aplus T₀ s₀ (ϖ ^ k) huk

end General

section Tate

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

open scoped Classical in
/-- Over a Tate ring, every `U ∈ spaRationalFamily A⁺` (for an open subring `A⁺` and a chosen
pseudouniformiser `ϖ`) admits a presentation `U = Subtype.val ⁻¹' R((insert (ϖ ^ N) T) / s)` with
`0 < N`, `insert (ϖ ^ N) T ⊆ A⁺`, and `s ∈ A⁺`. -/
theorem exists_mem_spaRationalFamily_eq_insert_pseudoUniformizer_pow {Aplus : Subring A}
    (hopen : IsOpen (Aplus : Set A)) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {U : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus) :
    ∃ (T : Finset A) (s : A) (N : ℕ),
      0 < N ∧
      ((insert (ϖ ^ N) T : Finset A) : Set A) ⊆ Aplus ∧
      s ∈ Aplus ∧
      U = Subtype.val ⁻¹' rationalSubset Aplus (insert (ϖ ^ N) T) s := by
  obtain ⟨T₀, s₀, hT₀, rfl⟩ := mem_spaRationalFamily_iff.mp hU
  obtain ⟨T, s, N, hN, hsub, hs, heq⟩ :=
    exists_rationalSubset_eq_insert_pseudoUniformizer_pow hopen hϖ
      ((IsTateRing.isOpen_iff_eq_top (Ideal.span (T₀ : Set A))).mp hT₀) s₀
  exact ⟨T, s, N, hN, hsub, hs, congrArg (Subtype.val ⁻¹' ·) heq.symm⟩

end Tate

end TauCeti.ValuationSpectrum
