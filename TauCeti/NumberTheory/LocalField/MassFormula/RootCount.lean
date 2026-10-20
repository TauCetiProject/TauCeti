/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein
import TauCeti.NumberTheory.LocalField.Topology

/-!
# Root counts of Eisenstein polynomials in the counted extensions

A monic polynomial of degree `n` over a field `K` is its coefficient vector `a : Fin n → K`,
through `TauCeti.Polynomial.monicOfCoeff`. For an intermediate field `L`, the root count
`L.rootCount a` is the number of roots of that polynomial in `L`, counted with multiplicity.

For a nonarchimedean local field `K`, this file proves the identity that Serre's mass formula
integrates over the Eisenstein region of coefficient space. For almost every Eisenstein
coefficient vector `a`, the root counts of `a` in the totally ramified extensions of degree `n`
inside the separable closure add up to `n`:
`∑' L : totallyRamifiedOfDegree K n, L.rootCount a = n`.

The proof has two halves.

* `TauCeti.tsum_card_aroots_of_isEisensteinAt`: the identity holds for every separable
  Eisenstein polynomial `f` of degree `n`. Such an `f` has `n` distinct roots in the separable
  closure. Each root `x` generates a member `K⟮x⟯` of the family. For a member `L`, a root lies
  in `L` exactly when it generates `L`, because both fields have degree `n`.
* `TauCeti.ae_separable_monicOfCoeff_of_isEisensteinAt`: almost every Eisenstein polynomial is
  separable, for every left-invariant measure on `Fin n → K` that is finite on compact sets. An
  Eisenstein polynomial is irreducible, so it is separable as soon as its derivative is nonzero.
  For `2 ≤ n`, the derivative has constant term `a 1`, and the hyperplane `a 1 = 0` is null by
  `MeasureTheory.Measure.measure_hyperplane`. In equal characteristic this is where the
  inseparable Eisenstein polynomials, which have no roots in the separable closure, are
  discarded.

`TauCeti.ae_tsum_rootCount_of_isEisensteinAt` combines the two.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §2, eq. (3) and
  Lemma 1.
-/

public section
noncomputable section

open ValuativeRel Polynomial MeasureTheory TauCeti.Polynomial
open scoped IntermediateField ENNReal

namespace TauCeti

section RootCount

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The root count of a coefficient vector `a : Fin n → K` in an intermediate field `L` of `E / K`:
the number of roots in `L`, counted with multiplicity, of the monic polynomial
`X ^ n + ∑ i, a i * X ^ i` whose lower coefficients are `a`. -/
def _root_.IntermediateField.rootCount (L : IntermediateField K E) {n : ℕ} (a : Fin n → K) : ℕ :=
  ((monicOfCoeff a).aroots L).card

/-- The root count is the cardinality of the root multiset of `monicOfCoeff a` in `L`. -/
theorem _root_.IntermediateField.rootCount_def (L : IntermediateField K E) {n : ℕ}
    (a : Fin n → K) : L.rootCount a = ((monicOfCoeff a).aroots L).card := by
  rw [IntermediateField.rootCount]

end RootCount

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The root counts of a separable Eisenstein polynomial add up to its degree.** If `f` is an
Eisenstein polynomial of degree `n` over `𝒪[K]` that is separable over `K`, then summing the
number of roots of `f` in `L` over the totally ramified extensions `L` of degree `n` inside the
separable closure gives `n`. Each of the `n` roots generates exactly one such `L`. -/
theorem tsum_card_aroots_of_isEisensteinAt {n : ℕ} {f : 𝒪[K][X]} (hf : f.IsEisensteinAt 𝓂[K])
    (hdeg : f.natDegree = n) (hsep : (f.map (algebraMap 𝒪[K] K)).Separable) :
    ∑' L : totallyRamifiedOfDegree K n,
      (((f.map (algebraMap 𝒪[K] K)).aroots L.1).card : ℝ≥0∞) = n := by
  classical
  set g := f.map (algebraMap 𝒪[K] K) with hg
  have hg0 : g ≠ 0 := hsep.ne_zero
  -- The roots of `g` in the separable closure: `n` of them, all distinct.
  set R := (g.aroots (SeparableClosure K)).toFinset
  have hR : R.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep.map),
      ← (IsSepClosed.splits_codomain g hsep).natDegree_eq_card_roots, natDegree_map, hg,
      natDegree_map_eq_of_injective (IsFractionRing.injective 𝒪[K] K), hdeg]
  have hroot {x : SeparableClosure K} (hx : x ∈ R) : aeval x g = 0 :=
    (mem_aroots.mp (Multiset.mem_toFinset.mp hx)).2
  -- The roots of `g` in `L` are the roots in the separable closure that lie in `L`.
  have hcard (L : IntermediateField K (SeparableClosure K)) :
      (g.aroots L).card = (R.filter (· ∈ L)).card := by
    have h := filter_roots_map_range_eq_map_roots
      (algebraMap L (SeparableClosure K)).injective (g.map (algebraMap K L))
    rw [map_map, ← IsScalarTower.algebraMap_eq] at h
    rw [← Multiset.card_map (algebraMap L (SeparableClosure K)), aroots_def, ← h,
      ← Multiset.toFinset_card_of_nodup ((nodup_roots hsep.map).filter _), Multiset.toFinset_filter]
    refine congrArg Finset.card (Finset.filter_congr fun x _ ↦ ?_)
    simp only [RingHom.mem_range, IntermediateField.algebraMap_apply]
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  -- A root lies in a counted extension exactly when it generates it, by comparing degrees.
  have hgen (L : totallyRamifiedOfDegree K n) {x : SeparableClosure K} (hx : x ∈ R) :
      x ∈ L.1 ↔ K⟮x⟯ = L.1 := by
    refine ⟨fun hxL ↦ ?_, fun h ↦ h ▸ IntermediateField.mem_adjoin_simple_self K x⟩
    have hL := mem_totallyRamifiedOfDegree_iff.mp L.2
    have := hL.2.finite
    exact IntermediateField.eq_of_le_of_finrank_eq
      (IntermediateField.adjoin_simple_le_iff.mpr hxL)
      ((mem_totallyRamifiedOfDegree_iff.mp
        (adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hf hdeg (hroot hx))).1.trans hL.1.symm)
  -- Each root generates exactly one counted extension.
  have hone {x : SeparableClosure K} (hx : x ∈ R) :
      ∑' L : totallyRamifiedOfDegree K n, (if K⟮x⟯ = L.1 then 1 else 0 : ℝ≥0∞) = 1 := by
    let L₀ : totallyRamifiedOfDegree K n :=
      ⟨K⟮x⟯, adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hf hdeg (hroot hx)⟩
    rw [tsum_eq_single L₀ fun L hL ↦ ite_eq_right_iff.2 fun h ↦ (hL (Subtype.ext h.symm)).elim]
    simp [L₀]
  calc ∑' L : totallyRamifiedOfDegree K n, ((g.aroots L.1).card : ℝ≥0∞)
      = ∑' L : totallyRamifiedOfDegree K n,
          ∑ x ∈ R, (if K⟮x⟯ = L.1 then 1 else 0 : ℝ≥0∞) := by
        refine tsum_congr fun L ↦ ?_
        rw [hcard, Finset.filter_congr fun x hx ↦ hgen L hx, Finset.card_filter]
        simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ = ∑ x ∈ R, ∑' L : totallyRamifiedOfDegree K n,
          (if K⟮x⟯ = L.1 then 1 else 0 : ℝ≥0∞) :=
        Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable
    _ = n := by rw [Finset.sum_congr rfl fun x hx ↦ hone hx, Finset.sum_const, hR, nsmul_one]

/-- **Almost every Eisenstein polynomial is separable.** For every left-invariant measure on the
coefficient space `Fin n → K` that is finite on compact sets, almost every coefficient vector
`a` whose monic polynomial is Eisenstein over `𝒪[K]` gives a separable polynomial. -/
theorem ae_separable_monicOfCoeff_of_isEisensteinAt {n : ℕ} [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] :
    ∀ᵐ a ∂μ, (∃ f : 𝒪[K][X], f.map (algebraMap 𝒪[K] K) = monicOfCoeff a ∧
      f.IsEisensteinAt 𝓂[K]) → (monicOfCoeff a).Separable := by
  -- Away from a null set, the coefficient of `X` is nonzero once the degree is positive.
  have hcoeff : ∀ᵐ a ∂μ, 0 < n → (monicOfCoeff a).coeff 1 ≠ 0 := by
    rcases lt_or_ge 1 n with h | h
    · filter_upwards [compl_mem_ae_iff.2 (Measure.measure_hyperplane μ (⟨1, h⟩ : Fin n) 0)]
        with a ha _
      rwa [show (1 : ℕ) = ((⟨1, h⟩ : Fin n) : ℕ) from rfl, coeff_monicOfCoeff]
    · refine .of_forall fun a hn ↦ ?_
      obtain rfl : n = 1 := le_antisymm h hn
      have h1 := (monic_monicOfCoeff a).coeff_natDegree
      rw [natDegree_monicOfCoeff] at h1
      exact h1 ▸ one_ne_zero
  filter_upwards [hcoeff] with a ha
  rintro ⟨f, hfa, hf⟩
  have hinj := IsFractionRing.injective 𝒪[K] K
  have hdeg : f.natDegree = n := by
    rw [← natDegree_monicOfCoeff a, ← hfa, natDegree_map_eq_of_injective hinj]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(Monic.natDegree_eq_zero (monic_monicOfCoeff a)).mp (natDegree_monicOfCoeff a)]
    exact separable_one
  -- An Eisenstein polynomial is irreducible over `K`, so a nonzero derivative suffices.
  have hmonic : f.Monic := by
    rw [Monic, ← hinj.eq_iff, ← leadingCoeff_map_of_injective hinj, hfa, map_one]
    exact monic_monicOfCoeff a
  have hirr : Irreducible (monicOfCoeff a) := hfa ▸
    hmonic.irreducible_iff_irreducible_map_fraction_map.mp
      (hf.irreducible (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).isPrime hmonic.isPrimitive
        (hdeg ▸ hn))
  refine (separable_iff_derivative_ne_zero hirr).2 fun h ↦ ha hn ?_
  simpa [coeff_derivative] using congrArg (coeff · 0) h

/-- **The root counts of almost every Eisenstein polynomial add up to its degree.** For every
left-invariant measure on the coefficient space `Fin n → K` that is finite on compact sets,
almost every coefficient vector `a` whose monic polynomial is Eisenstein over `𝒪[K]` has root
counts summing to `n` over the totally ramified extensions of degree `n` inside the separable
closure. -/
theorem ae_tsum_rootCount_of_isEisensteinAt {n : ℕ} [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] :
    ∀ᵐ a ∂μ, (∃ f : 𝒪[K][X], f.map (algebraMap 𝒪[K] K) = monicOfCoeff a ∧
      f.IsEisensteinAt 𝓂[K]) →
      ∑' L : totallyRamifiedOfDegree K n, (L.1.rootCount a : ℝ≥0∞) = n := by
  filter_upwards [ae_separable_monicOfCoeff_of_isEisensteinAt μ] with a ha hfa
  obtain ⟨f, hfa', hf⟩ := hfa
  have hdeg : f.natDegree = n := by
    rw [← natDegree_monicOfCoeff a, ← hfa',
      natDegree_map_eq_of_injective (IsFractionRing.injective 𝒪[K] K)]
  simp_rw [IntermediateField.rootCount_def, ← hfa']
  exact tsum_card_aroots_of_isEisensteinAt hf hdeg (hfa' ▸ ha ⟨f, hfa', hf⟩)

end TauCeti
