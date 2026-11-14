/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Probability.FreeProbability.Cumulant.Series
public import TauCeti.Probability.FreeProbability.Distribution.Free
public import TauCeti.Probability.FreeProbability.FreeProduct.Reduced
public import TauCeti.Probability.FreeProbability.Law.Basic
public import TauCeti.Probability.FreeProbability.WeakClosure
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Topology.ContinuousMap.Units

/-!
# Free realizations and realization-independence of scalar laws

This file connects `PositiveLinearMap.law` with free independence, formal moment and cumulant
series, and the reduced C⋆- and von Neumann free products:
* topological support and real-spectrum interval bounds for `PositiveLinearMap.law`, preservation of
  laws under state-preserving unital `⋆`-homomorphisms, and agreement of formal moment, free
  cumulant, and R-series of selfadjoint elements with those integrated against `φ.law a`;
* realization-independence of polynomial and finite-sum laws of freely independent selfadjoint
  families with matching individual laws;
* `TauCeti.FreeLawRealization`, realizing any family `μ : ι → Measure ℝ` of compactly supported
  probability measures by freely independent selfadjoint generators in a reduced C⋆-free product and
  in the generated concrete von Neumann algebra on the vacuum GNS Hilbert space.

## Main definitions and results

* `PositiveLinearMap.support_law_subset_spectrum`, `PositiveLinearMap.law_starAlgHom`,
  `PositiveLinearMap.map_ofReal_rSeries_integral_law`.
* `TauCeti.IsFreelyIndependentElements.law_lift_eq_of_forall_law_eq`,
  `TauCeti.IsFreelyIndependentElements.law_sum_eq_of_forall_law_eq`.
* `TauCeti.FreeLawRealization.algebra`, `TauCeti.FreeLawRealization.generator`,
  `TauCeti.FreeLawRealization.vonNeumannAlgebra`, `TauCeti.FreeLawRealization.vonNeumannGenerator`,
  `TauCeti.FreeLawRealization.isFreelyIndependent_vonNeumannAlgebra_adjoin_vonNeumannGenerator`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §§1.5, 3.2.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University
  Press (2006), Lectures 5, 7, and 12.
-/

public section

noncomputable section

open Finset MeasureTheory PowerSeries
open scoped ComplexOrder ENNReal InnerProductSpace

/-! ### Support, homomorphisms, spectrum bounds, and formal series of scalar laws -/

namespace PositiveLinearMap

section Basic

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)

/-- The topological support of the law of `a` is contained in its real spectrum. -/
theorem support_law_subset_spectrum (a : A) : (φ.law a).support ⊆ spectrum ℝ a :=
  Measure.support_subset_of_isClosed (spectrum.isClosed a) (φ.law_compl_spectrum a)

/-- The law of any element in a unital C⋆-algebra has compact topological support. -/
theorem isCompact_support_law (a : A) : IsCompact (φ.law a).support :=
  (ContinuousFunctionalCalculus.isCompact_spectrum a).of_isClosed_subset
    Measure.isClosed_support (φ.support_law_subset_spectrum a)

/-- The law of a real scalar `algebraMap ℝ A c` is `(φ 1).re` times the Dirac mass at `c`. -/
theorem law_algebraMap (c : ℝ) :
    φ.law (algebraMap ℝ A c) = ENNReal.ofReal (φ 1).re • Measure.dirac c := by
  have h1 : 0 ≤ φ 1 := φ.map_nonneg zero_le_one
  have h1re : ((φ 1).re : ℂ) = φ 1 := by
    rw [Complex.ext_iff]
    exact ⟨rfl, (Complex.nonneg_iff.mp h1).2⟩
  have hfin : IsFiniteMeasure (ENNReal.ofReal (φ 1).re • Measure.dirac c) := ⟨by simp⟩
  refine (eq_law_iff.mpr fun f _ => ?_).symm
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (Complex.nonneg_iff.mp h1).1,
    cfc_algebraMap c f, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul,
    smul_eq_mul, smul_eq_mul, Complex.ofReal_mul, h1re, mul_comm]

/-- For a state (`φ 1 = 1`), the law of `algebraMap ℝ A c` is the Dirac mass at `c`. -/
theorem law_algebraMap_of_apply_one (hφ : φ 1 = 1) (c : ℝ) :
    φ.law (algebraMap ℝ A c) = Measure.dirac c := by
  simpa [hφ] using φ.law_algebraMap c

/-- The law of `0` is `(φ 1).re` times the Dirac mass at `0`. -/
@[simp]
theorem law_zero : φ.law (0 : A) = ENNReal.ofReal (φ 1).re • Measure.dirac 0 := by
  simpa using φ.law_algebraMap 0

/-- For a state (`φ 1 = 1`), the law of `0` is the Dirac mass at `0`. -/
theorem law_zero_of_apply_one (hφ : φ 1 = 1) : φ.law (0 : A) = Measure.dirac 0 := by
  simp [hφ]

/-- For a state (`φ 1 = 1`), the law of `1` is the Dirac mass at `1`. -/
theorem law_one_of_apply_one (hφ : φ 1 = 1) : φ.law (1 : A) = Measure.dirac 1 := by
  simpa using φ.law_algebraMap_of_apply_one hφ 1

/-- Negating an element reflects its law, including the non-selfadjoint case where both are `0`. -/
@[simp]
theorem law_neg (a : A) : φ.law (-a) = (φ.law a).neg := by
  by_cases ha : IsSelfAdjoint a
  · have h := φ.law_smul_add_algebraMap ha (-1) 0
    simpa [Measure.neg_def] using h
  · have hna : ¬IsSelfAdjoint (-a) := fun h => ha (by simpa using h.neg)
    simp [law_of_not_isSelfAdjoint, ha, hna, Measure.neg_def]

/-- A unital `⋆`-algebra homomorphism intertwining two positive functionals preserves the law of
every selfadjoint element. Neither injectivity of `f` nor normalization is required. -/
theorem law_starAlgHom {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (ψ : B →ₚ[ℂ] ℂ) (f : A →⋆ₐ[ℂ] B) {a : A} (ha : IsSelfAdjoint a)
    (hf : ∀ x, ψ (f x) = φ x) : ψ.law (f a) = φ.law a :=
  (law_eq_law_iff_forall_apply_pow ψ φ (ha.map f) ha).mpr fun n => by
    rw [← map_pow, hf]

/-- If two selfadjoint elements have real spectra in `[m₁, M₁]` and `[m₂, M₂]`, then the real
spectrum of their sum lies in `[m₁ + m₂, M₁ + M₂]`. -/
theorem spectrum_add_subset_Icc {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {m₁ M₁ m₂ M₂ : ℝ} (haI : spectrum ℝ a ⊆ Set.Icc m₁ M₁)
    (hbI : spectrum ℝ b ⊆ Set.Icc m₂ M₂) :
    spectrum ℝ (a + b) ⊆ Set.Icc (m₁ + m₂) (M₁ + M₂) := by
  have hle₁ : algebraMap ℝ A m₁ ≤ a :=
    (algebraMap_le_iff_le_spectrum ha).mpr fun x hx => (haI hx).1
  have hge₁ : a ≤ algebraMap ℝ A M₁ :=
    (le_algebraMap_iff_spectrum_le ha).mpr fun x hx => (haI hx).2
  have hle₂ : algebraMap ℝ A m₂ ≤ b :=
    (algebraMap_le_iff_le_spectrum hb).mpr fun x hx => (hbI hx).1
  have hge₂ : b ≤ algebraMap ℝ A M₂ :=
    (le_algebraMap_iff_spectrum_le hb).mpr fun x hx => (hbI hx).2
  have hlow : algebraMap ℝ A (m₁ + m₂) ≤ a + b := by
    rw [map_add]
    exact add_le_add hle₁ hle₂
  have hhigh : a + b ≤ algebraMap ℝ A (M₁ + M₂) := by
    rw [map_add]
    exact add_le_add hge₁ hge₂
  exact fun x hx => ⟨(algebraMap_le_iff_le_spectrum (ha.add hb)).mp hlow x hx,
    (le_algebraMap_iff_spectrum_le (ha.add hb)).mp hhigh x hx⟩

/-- If selfadjoint elements `a i` (`i ∈ s`) have real spectra in `[m i, M i]`, then the real
spectrum of `∑ i ∈ s, a i` lies in `[∑ i ∈ s, m i, ∑ i ∈ s, M i]`, including `s = ∅`. -/
theorem spectrum_sum_subset_Icc {ι : Type*} (s : Finset ι) {a : ι → A} {m M : ι → ℝ}
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i))
    (hI : ∀ i ∈ s, spectrum ℝ (a i) ⊆ Set.Icc (m i) (M i)) :
    spectrum ℝ (∑ i ∈ s, a i) ⊆ Set.Icc (∑ i ∈ s, m i) (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [sum_empty, Set.Icc_self]
      by_cases hA : Nontrivial A
      · simp
      · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
        simp
  | @insert i s hi ih =>
      have hsa_sum : IsSelfAdjoint (∑ j ∈ s, a j) :=
        isSelfAdjoint_sum s fun j hj => ha j (mem_insert_of_mem hj)
      rw [sum_insert hi, sum_insert hi, sum_insert hi]
      exact spectrum_add_subset_Icc (ha i (mem_insert_self i s)) hsa_sum
        (hI i (mem_insert_self i s))
        (ih (fun j hj => ha j (mem_insert_of_mem hj))
          (fun j hj => hI j (mem_insert_of_mem hj)))

/-- Interval bounds on the real spectra of selfadjoint `a` and `b` bound the support of the law
of `a + b`. -/
theorem support_law_add_subset_Icc {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {m₁ M₁ m₂ M₂ : ℝ} (haI : spectrum ℝ a ⊆ Set.Icc m₁ M₁)
    (hbI : spectrum ℝ b ⊆ Set.Icc m₂ M₂) :
    (φ.law (a + b)).support ⊆ Set.Icc (m₁ + m₂) (M₁ + M₂) :=
  (φ.support_law_subset_spectrum (a + b)).trans (spectrum_add_subset_Icc ha hb haI hbI)

/-- Interval bounds on the real spectra of selfadjoint `a i` (`i ∈ s`) bound the support of the
law of `∑ i ∈ s, a i`. -/
theorem support_law_sum_subset_Icc {ι : Type*} (s : Finset ι) {a : ι → A} {m M : ι → ℝ}
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i))
    (hI : ∀ i ∈ s, spectrum ℝ (a i) ⊆ Set.Icc (m i) (M i)) :
    (φ.law (∑ i ∈ s, a i)).support ⊆ Set.Icc (∑ i ∈ s, m i) (∑ i ∈ s, M i) :=
  (φ.support_law_subset_spectrum _).trans (spectrum_sum_subset_Icc s ha hI)

/-! #### Formal series and free cumulants of a scalar law -/

/-- Ring homomorphisms commute with noncrossing partition cumulants. -/
private theorem map_partitionCumulant {R S M α : Type*} [CommRing R] [CommRing S] [Monoid M]
    [LinearOrder α] {s : Finset α} (g : R →+* S) (ψ : M → R) (x : α → M)
    (π : TauCeti.NoncrossingPartition s) :
    g (TauCeti.partitionCumulant ψ x π) = TauCeti.partitionCumulant (g ∘ ψ) x π := by
  refine congrFun (TauCeti.eq_partitionCumulant_of_forall_sum_Iic (g ∘ ψ) x
    (fun σ => g (TauCeti.partitionCumulant ψ x σ)) fun σ => ?_) π
  rw [← map_sum, TauCeti.sum_Iic_partitionCumulant, TauCeti.partitionMoment_def,
    TauCeti.partitionMoment_def, map_prod]
  rfl

/-- Mapping the real moment series of `φ.law a` into `ℂ` recovers the moment series of `a`. -/
theorem map_ofReal_momentSeries_integral_law {a : A} (ha : IsSelfAdjoint a) :
    PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
        (TauCeti.momentSeries (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a) id) =
      TauCeti.momentSeries φ a := by
  ext n
  simpa [TauCeti.coeff_momentSeries, Pi.pow_def] using φ.ofReal_integral_pow_law ha n

/-- Mapping the real free cumulant series of `φ.law a` into `ℂ` gives the free cumulant series of
`a`. -/
theorem map_ofReal_freeCumulantSeries_integral_law {a : A} (ha : IsSelfAdjoint a) :
    PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
        (TauCeti.freeCumulantSeries (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a) id) =
      TauCeti.freeCumulantSeries φ a := by
  have hm : TauCeti.momentSeries
      (Complex.ofRealHom ∘ fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a) (id : ℝ → ℝ) =
      TauCeti.momentSeries φ a := by
    ext n
    simpa [TauCeti.coeff_momentSeries, Pi.pow_def] using φ.ofReal_integral_pow_law ha n
  rw [← TauCeti.freeCumulantSeries_congr _ _ hm]
  ext n
  simpa [TauCeti.coeff_freeCumulantSeries, TauCeti.freeCumulant_def] using
    map_partitionCumulant Complex.ofRealHom
      (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a) (fun _ : Fin n => (id : ℝ → ℝ)) ⊤

/-- For selfadjoint `a`, the real free cumulants of `id` under `φ.law a` match the complex free
cumulants of `a` under `φ`. -/
theorem ofReal_freeCumulant_integral_law {a : A} (ha : IsSelfAdjoint a) {α : Type*}
    [LinearOrder α] (s : Finset α) :
    ((TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a)
        (fun _ : α => (id : ℝ → ℝ)) s : ℝ) : ℂ) =
      TauCeti.freeCumulant φ (fun _ : α => a) s := by
  rw [TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries,
    TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries,
    ← φ.map_ofReal_freeCumulantSeries_integral_law ha, coeff_map, Complex.ofRealHom_eq_coe]

/-- Mapping the real formal R-series of `φ.law a` into `ℂ` gives the formal R-series of `a`. -/
theorem map_ofReal_rSeries_integral_law {a : A} (ha : IsSelfAdjoint a) :
    PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
        (TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a) id) =
      TauCeti.rSeries φ a := by
  ext n
  simpa [TauCeti.coeff_rSeries] using
    φ.ofReal_freeCumulant_integral_law ha (univ : Finset (Fin (n + 1)))

end Basic

end PositiveLinearMap

/-! ### Uniqueness of polynomial and sum laws of freely independent selfadjoint families -/

namespace TauCeti

section Uniqueness

variable {A B ι : Type*}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace IsFreelyIndependentElements

/-- Freely independent families of selfadjoint elements in possibly different C⋆-probability
spaces with matching individual laws have the same joint noncommutative distribution. -/
theorem jointDistribution_eq_of_forall_law_eq {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {a : ι → A} {b : ι → B}
    (ha : IsFreelyIndependentElements φ.toLinearMap a)
    (hb : IsFreelyIndependentElements ψ.toLinearMap b)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hasa : ∀ i, IsSelfAdjoint (a i)) (hbsa : ∀ i, IsSelfAdjoint (b i))
    (hlaw : ∀ i, φ.law (a i) = ψ.law (b i)) :
    jointDistribution φ.toLinearMap a = jointDistribution ψ.toLinearMap b :=
  ha.jointDistribution_eq_of_forall_pow hb hφ hψ fun i n =>
    (PositiveLinearMap.law_eq_law_iff_forall_apply_pow φ ψ (hasa i) (hbsa i)).mp (hlaw i) n

/-- Any noncommutative polynomial `P` whose evaluations on two freely independent selfadjoint
families with matching individual laws are selfadjoint has the same scalar law in both spaces. -/
theorem law_lift_eq_of_forall_law_eq {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {a : ι → A} {b : ι → B}
    (ha : IsFreelyIndependentElements φ.toLinearMap a)
    (hb : IsFreelyIndependentElements ψ.toLinearMap b)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hasa : ∀ i, IsSelfAdjoint (a i)) (hbsa : ∀ i, IsSelfAdjoint (b i))
    (hlaw : ∀ i, φ.law (a i) = ψ.law (b i))
    (P : FreeAlgebra ℂ ι)
    (hPa : IsSelfAdjoint (FreeAlgebra.lift ℂ a P))
    (hPb : IsSelfAdjoint (FreeAlgebra.lift ℂ b P)) :
    φ.law (FreeAlgebra.lift ℂ a P) = ψ.law (FreeAlgebra.lift ℂ b P) := by
  have hjd := ha.jointDistribution_eq_of_forall_law_eq hb hφ hψ hasa hbsa hlaw
  refine (PositiveLinearMap.law_eq_law_iff_forall_apply_pow φ ψ hPa hPb).mpr fun n => ?_
  have hpow := LinearMap.congr_fun hjd (P ^ n)
  simpa only [jointDistribution_apply, map_pow, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, PositiveLinearMap.coe_toLinearMap] using hpow

/-- Finite sums of freely independent selfadjoint elements depend in law only on the individual
laws of the summands. Only the summands indexed by `s` need be selfadjoint or match in law. -/
theorem law_sum_eq_of_forall_law_eq {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {a : ι → A} {b : ι → B}
    (ha : IsFreelyIndependentElements φ.toLinearMap a)
    (hb : IsFreelyIndependentElements ψ.toLinearMap b)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1) (s : Finset ι)
    (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) (hbsa : ∀ i ∈ s, IsSelfAdjoint (b i))
    (hlaw : ∀ i ∈ s, φ.law (a i) = ψ.law (b i)) :
    φ.law (∑ i ∈ s, a i) = ψ.law (∑ i ∈ s, b i) := by
  let a' : s → A := fun i => a i.1
  let b' : s → B := fun i => b i.1
  have ha' : IsFreelyIndependentElements φ.toLinearMap a' := ha.comp Subtype.val_injective
  have hb' : IsFreelyIndependentElements ψ.toLinearMap b' := hb.comp Subtype.val_injective
  let P : FreeAlgebra ℂ s := ∑ i : s, FreeAlgebra.ι ℂ i
  have hPa : FreeAlgebra.lift ℂ a' P = ∑ i ∈ s, a i := by
    simp [P, a', Finset.univ_eq_attach, Finset.sum_attach]
  have hPb : FreeAlgebra.lift ℂ b' P = ∑ i ∈ s, b i := by
    simp [P, b', Finset.univ_eq_attach, Finset.sum_attach]
  rw [← hPa, ← hPb]
  exact ha'.law_lift_eq_of_forall_law_eq hb' hφ hψ
    (fun i => hasa i.1 i.2) (fun i => hbsa i.1 i.2) (fun i => hlaw i.1 i.2) P
    (hPa.symm ▸ isSelfAdjoint_sum s hasa) (hPb.symm ▸ isSelfAdjoint_sum s hbsa)

/-- Binary sums of distinct freely independent selfadjoint elements depend in law only on the two
individual laws. -/
theorem law_add_eq_of_law_eq {κ : Type*} {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {a : ι → A} {b : κ → B}
    (ha : IsFreelyIndependentElements φ.toLinearMap a)
    (hb : IsFreelyIndependentElements ψ.toLinearMap b)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    {i₁ i₂ : ι} {k₁ k₂ : κ} (hi : i₁ ≠ i₂) (hk : k₁ ≠ k₂)
    (ha₁ : IsSelfAdjoint (a i₁)) (ha₂ : IsSelfAdjoint (a i₂))
    (hb₁ : IsSelfAdjoint (b k₁)) (hb₂ : IsSelfAdjoint (b k₂))
    (h₁ : φ.law (a i₁) = ψ.law (b k₁)) (h₂ : φ.law (a i₂) = ψ.law (b k₂)) :
    φ.law (a i₁ + a i₂) = ψ.law (b k₁ + b k₂) := by
  let ea : Bool → ι := fun t => cond t i₁ i₂
  let eb : Bool → κ := fun t => cond t k₁ k₂
  have hea : Function.Injective ea := by
    rintro (_ | _) (_ | _) h <;> simp [ea] at h <;> tauto
  have heb : Function.Injective eb := by
    rintro (_ | _) (_ | _) h <;> simp [eb] at h <;> tauto
  have hsum := (ha.comp hea).law_sum_eq_of_forall_law_eq (hb.comp heb) hφ hψ
    ({true, false} : Finset Bool)
    (by rintro (_ | _) _ <;> assumption)
    (by rintro (_ | _) _ <;> assumption)
    (by rintro (_ | _) _ <;> assumption)
  simpa [ea, eb] using hsum

end IsFreelyIndependentElements

namespace IsFreelyIndependent

/-- Finite sums of selfadjoint elements chosen from freely independent subalgebras depend in law
only on the individual laws of the summands. -/
theorem law_sum_eq_of_forall_law_eq {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {SA : ι → Subalgebra ℂ A} {SB : ι → Subalgebra ℂ B}
    (hA : IsFreelyIndependent φ.toLinearMap SA)
    (hB : IsFreelyIndependent ψ.toLinearMap SB)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1) (s : Finset ι) {a : ι → A} {b : ι → B}
    (haS : ∀ i ∈ s, a i ∈ SA i) (hbS : ∀ i ∈ s, b i ∈ SB i)
    (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) (hbsa : ∀ i ∈ s, IsSelfAdjoint (b i))
    (hlaw : ∀ i ∈ s, φ.law (a i) = ψ.law (b i)) :
    φ.law (∑ i ∈ s, a i) = ψ.law (∑ i ∈ s, b i) := by
  have ha' : IsFreelyIndependentElements φ.toLinearMap (fun i : s => a i.1) :=
    isFreelyIndependentElements_iff.mpr <| (hA.comp Subtype.val_injective).mono fun i =>
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (haS i.1 i.2))
  have hb' : IsFreelyIndependentElements ψ.toLinearMap (fun i : s => b i.1) :=
    isFreelyIndependentElements_iff.mpr <| (hB.comp Subtype.val_injective).mono fun i =>
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (hbS i.1 i.2))
  simpa only [Finset.univ_eq_attach, Finset.sum_attach] using
    ha'.law_sum_eq_of_forall_law_eq hb' hφ hψ univ
      (fun i _ => hasa i.1 i.2) (fun i _ => hbsa i.1 i.2) (fun i _ => hlaw i.1 i.2)

end IsFreelyIndependent

end Uniqueness

/-! ### Canonical C⋆- and von Neumann realizations of compactly supported laws -/

namespace FreeLawRealization

/-- Restricting a probability measure on `ℝ` to its topological support yields a probability
measure. -/
private instance instIsProbabilityMeasureComapSupport (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ν.comap ((↑) : ν.support → ℝ)) :=
  (MeasurableEmbedding.subtype_coe
    (Measure.isClosed_support (μ := ν)).measurableSet).isProbabilityMeasure_comap
      (by simpa using Measure.support_mem_ae (μ := ν))

section Factor

variable {ι : Type*} (μ : ι → Measure ℝ)

/-- The selfadjoint coordinate function `x ↦ x` in `C((μ i).support, ℂ)`. -/
private def factorCoordinate (i : ι) : C((μ i).support, ℂ) :=
  (ContinuousMap.restrict (μ i).support (ContinuousMap.id ℝ)).realToRCLike ℂ

private theorem isSelfAdjoint_factorCoordinate (i : ι) :
    IsSelfAdjoint (factorCoordinate μ i) :=
  ContinuousMap.isSelfAdjoint_realToRCLike ℂ

private theorem spectrum_factorCoordinate_subset_support (i : ι) :
    spectrum ℝ (factorCoordinate μ i) ⊆ (μ i).support := by
  intro r hr
  rw [ContinuousMap.spectrum_eq_preimage_range] at hr
  rcases hr with ⟨x, hx⟩
  have hrx : x.1 = r := Complex.ofReal_injective hx
  exact hrx ▸ x.2

variable [∀ i, IsProbabilityMeasure (μ i)] [∀ i, CompactSpace (μ i).support]

/-- The positive functional on `C((μ i).support, ℂ)` given by integration against `μ i`. -/
def factorPositiveLinearMap (i : ι) : C((μ i).support, ℂ) →ₚ[ℂ] ℂ :=
  ContinuousMap.integralPositiveLinearMap ((μ i).comap ((↑) : (μ i).support → ℝ))

/-- The star-positive functional on `C((μ i).support, ℂ)` given by integration against `μ i`. -/
def factorFunctional (i : ι) : StarPositiveFunctional C((μ i).support, ℂ) :=
  StarPositiveFunctional.ofPositiveLinearMap (factorPositiveLinearMap μ i)

/-- The factor functional of a probability measure `μ i` is normalized (`φ 1 = 1`). -/
theorem factorFunctional_one (i : ι) : factorFunctional μ i 1 = 1 := by
  rw [factorFunctional, StarPositiveFunctional.ofPositiveLinearMap_apply, factorPositiveLinearMap,
    ContinuousMap.integralPositiveLinearMap_one]
  simp

private theorem law_factorCoordinate (i : ι) :
    (factorPositiveLinearMap μ i).law (factorCoordinate μ i) = μ i :=
  PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id
    (Measure.measure_compl_support (μ := μ i))

end Factor

section ReducedBridge

variable {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, CStarAlgebra (A i)]
  (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1)

private instance : IsTopologicalRing
    (ReducedFreeProduct.HilbertSpace φ hφ →L[ℂ] ReducedFreeProduct.HilbertSpace φ hφ) :=
  NonUnitalSeminormedRing.toIsTopologicalRing
    (α := ReducedFreeProduct.HilbertSpace φ hφ →L[ℂ] ReducedFreeProduct.HilbertSpace φ hφ)

private instance : ContinuousStar
    (ReducedFreeProduct.HilbertSpace φ hφ →L[ℂ] ReducedFreeProduct.HilbertSpace φ hφ) :=
  ⟨(ContinuousLinearMap.adjoint :
    (ReducedFreeProduct.HilbertSpace φ hφ →L[ℂ] ReducedFreeProduct.HilbertSpace φ hφ) ≃ₗᵢ⋆[ℂ]
      (ReducedFreeProduct.HilbertSpace φ hφ →L[ℂ]
        ReducedFreeProduct.HilbertSpace φ hφ)).continuous⟩

/-- Opaque Hilbert-space wrapper around `ReducedFreeProduct.HilbertSpace φ hφ` so downstream
operator subalgebras treat the carrier as an atomic Hilbert space. -/
def bridgeHilbertSpace : Type _ :=
  ReducedFreeProduct.HilbertSpace φ hφ

instance : NormedAddCommGroup (bridgeHilbertSpace φ hφ) :=
  inferInstanceAs (NormedAddCommGroup (ReducedFreeProduct.HilbertSpace φ hφ))

instance : InnerProductSpace ℂ (bridgeHilbertSpace φ hφ) :=
  inferInstanceAs (InnerProductSpace ℂ (ReducedFreeProduct.HilbertSpace φ hφ))

instance : CompleteSpace (bridgeHilbertSpace φ hφ) :=
  inferInstanceAs (CompleteSpace (ReducedFreeProduct.HilbertSpace φ hφ))

private def bridgeVacuum : bridgeHilbertSpace φ hφ :=
  ReducedFreeProduct.vacuum φ hφ

private theorem norm_bridgeVacuum : ‖bridgeVacuum φ hφ‖ = 1 :=
  ReducedFreeProduct.norm_vacuum φ hφ

private def bridgeVectorState :
    (bridgeHilbertSpace φ hφ →L[ℂ] bridgeHilbertSpace φ hφ) →ₚ[ℂ] ℂ :=
  ContinuousLinearMap.innerPositiveLinearMap ℂ (bridgeVacuum φ hφ)

private theorem bridgeVectorState_apply
    (T : bridgeHilbertSpace φ hφ →L[ℂ] bridgeHilbertSpace φ hφ) :
    bridgeVectorState φ hφ T = ⟪bridgeVacuum φ hφ, T (bridgeVacuum φ hφ)⟫_ℂ :=
  ContinuousLinearMap.innerPositiveLinearMap_apply (bridgeVacuum φ hφ) T

private def bridgeAlgebra :
    StarSubalgebra ℂ (bridgeHilbertSpace φ hφ →L[ℂ] bridgeHilbertSpace φ hφ) :=
  ReducedFreeProduct.algebra φ hφ

private instance isClosed_bridgeAlgebra :
    IsClosed (bridgeAlgebra φ hφ :
      Set (bridgeHilbertSpace φ hφ →L[ℂ] bridgeHilbertSpace φ hφ)) :=
  ReducedFreeProduct.isClosed_algebra φ hφ

private def bridgeState : bridgeAlgebra φ hφ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((bridgeVectorState φ hφ).toLinearMap.comp (bridgeAlgebra φ hφ).subtype.toLinearMap)
    fun _ hT => (bridgeVectorState φ hφ).map_nonneg hT

private theorem bridgeState_apply (T : bridgeAlgebra φ hφ) :
    bridgeState φ hφ T =
      ⟪bridgeVacuum φ hφ,
        (T : bridgeHilbertSpace φ hφ →L[ℂ] bridgeHilbertSpace φ hφ) (bridgeVacuum φ hφ)⟫_ℂ := by
  rw [bridgeState, PositiveLinearMap.mk₀]
  exact bridgeVectorState_apply φ hφ T

private def bridgeFactor (i : ι) : A i →⋆ₐ[ℂ] bridgeAlgebra φ hφ where
  toFun x := ReducedFreeProduct.factor φ hφ i x
  map_one' := Subtype.ext <| congrArg Subtype.val <| map_one (ReducedFreeProduct.factor φ hφ i)
  map_mul' x y := Subtype.ext <| congrArg Subtype.val <|
    map_mul (ReducedFreeProduct.factor φ hφ i) x y
  map_zero' := Subtype.ext <| congrArg Subtype.val <| map_zero (ReducedFreeProduct.factor φ hφ i)
  map_add' x y := Subtype.ext <| congrArg Subtype.val <|
    map_add (ReducedFreeProduct.factor φ hφ i) x y
  commutes' c := Subtype.ext <| congrArg Subtype.val <|
    AlgHomClass.commutes (ReducedFreeProduct.factor φ hφ i) c
  map_star' x := Subtype.ext <| congrArg Subtype.val <|
    map_star (ReducedFreeProduct.factor φ hφ i) x

private theorem bridgeState_eq (T : ReducedFreeProduct.algebra φ hφ) :
    bridgeState φ hφ T = ReducedFreeProduct.state φ hφ T :=
  (bridgeState_apply φ hφ T).trans (ReducedFreeProduct.state_apply φ hφ T).symm

private theorem bridgeState_factor (i : ι) (x : A i) :
    bridgeState φ hφ (bridgeFactor φ hφ i x) = φ i x :=
  (bridgeState_eq φ hφ (ReducedFreeProduct.factor φ hφ i x)).trans
    (ReducedFreeProduct.state_factor φ hφ i x)

private theorem isFreelyIndependent_bridgeFactor :
    IsFreelyIndependent (bridgeState φ hφ).toLinearMap
      (fun i => (bridgeFactor φ hφ i).toAlgHom.range) := by
  let e : ReducedFreeProduct.algebra φ hφ →ₐ[ℂ] bridgeAlgebra φ hφ :=
    { toFun := fun x => x
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hfree := (ReducedFreeProduct.isFreelyIndependent_factor φ hφ).map e
    (φ' := (bridgeState φ hφ).toLinearMap)
    (LinearMap.ext fun x => bridgeState_eq φ hφ x)
  exact hfree.mono fun i _ ⟨x, hx⟩ => ⟨ReducedFreeProduct.factor φ hφ i x, ⟨x, rfl⟩, hx⟩

end ReducedBridge

section Product

variable {ι : Type*} [DecidableEq ι] (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, CompactSpace (μ i).support]

/-- The completed GNS Hilbert space of the reduced free product realizing `μ`. -/
abbrev HilbertSpace : Type _ :=
  bridgeHilbertSpace (factorFunctional μ) (factorFunctional_one μ)

/-- The unit cyclic vacuum vector in `HilbertSpace μ`. -/
def vacuum : HilbertSpace μ :=
  bridgeVacuum (factorFunctional μ) (factorFunctional_one μ)

@[simp]
theorem norm_vacuum : ‖vacuum μ‖ = 1 :=
  norm_bridgeVacuum (factorFunctional μ) (factorFunctional_one μ)

/-- The vacuum vector state on all bounded operators on `HilbertSpace μ`. -/
def vectorState : (HilbertSpace μ →L[ℂ] HilbertSpace μ) →ₚ[ℂ] ℂ :=
  ContinuousLinearMap.innerPositiveLinearMap ℂ (vacuum μ)

theorem vectorState_apply (T : HilbertSpace μ →L[ℂ] HilbertSpace μ) :
    vectorState μ T = ⟪vacuum μ, T (vacuum μ)⟫_ℂ :=
  ContinuousLinearMap.innerPositiveLinearMap_apply (vacuum μ) T

@[simp]
theorem vectorState_one : vectorState μ 1 = 1 := by
  rw [vectorState, ContinuousLinearMap.innerPositiveLinearMap_one, norm_vacuum]
  simp

/-- The vacuum vector state is continuous for the weak operator topology. -/
theorem continuous_wot_vectorState :
    Continuous fun T : HilbertSpace μ →WOT[ℂ] HilbertSpace μ => vectorState μ T.toCLM := by
  simp_rw [vectorState_apply]
  exact ContinuousLinearMapWOT.continuous_dual_apply (vacuum μ) (innerSL ℂ (vacuum μ))

/-- The canonical reduced C⋆-free product algebra realizing `μ`. -/
def algebra : StarSubalgebra ℂ (HilbertSpace μ →L[ℂ] HilbertSpace μ) :=
  bridgeAlgebra (factorFunctional μ) (factorFunctional_one μ)

instance isClosed_algebra :
    IsClosed (algebra μ : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ)) :=
  isClosed_bridgeAlgebra (factorFunctional μ) (factorFunctional_one μ)

/-- The vacuum state on the canonical C⋆-free product algebra realizing `μ`. -/
def state : algebra μ →ₚ[ℂ] ℂ :=
  bridgeState (factorFunctional μ) (factorFunctional_one μ)

theorem state_apply (T : algebra μ) :
    state μ T = ⟪vacuum μ, (T : HilbertSpace μ →L[ℂ] HilbertSpace μ) (vacuum μ)⟫_ℂ :=
  bridgeState_apply (factorFunctional μ) (factorFunctional_one μ) T

@[simp]
theorem state_one : state μ 1 = 1 := by
  rw [state_apply, OneMemClass.coe_one, ← vectorState_apply, vectorState_one]

/-- The `i`-th canonical factor `⋆`-homomorphism from `C((μ i).support, ℂ)` into `algebra μ`. -/
def factor (i : ι) : C((μ i).support, ℂ) →⋆ₐ[ℂ] algebra μ :=
  bridgeFactor (factorFunctional μ) (factorFunctional_one μ) i

@[simp]
theorem state_factor (i : ι) (x : C((μ i).support, ℂ)) :
    state μ (factor μ i x) = factorPositiveLinearMap μ i x :=
  (bridgeState_factor (factorFunctional μ) (factorFunctional_one μ) i x).trans
    (StarPositiveFunctional.ofPositiveLinearMap_apply _ _)

/-- The `i`-th canonical selfadjoint generator in `algebra μ` realizing `μ i`. -/
def generator (i : ι) : algebra μ :=
  factor μ i (factorCoordinate μ i)

theorem isSelfAdjoint_generator (i : ι) : IsSelfAdjoint (generator μ i) :=
  (isSelfAdjoint_factorCoordinate μ i).map (factor μ i)

/-- The `i`-th canonical generator in the C⋆-free product realization has law `μ i`. -/
@[simp]
theorem law_generator (i : ι) : (state μ).law (generator μ i) = μ i := by
  have hpres : (state μ).law (generator μ i) =
      (factorPositiveLinearMap μ i).law (factorCoordinate μ i) :=
    PositiveLinearMap.law_starAlgHom (factorPositiveLinearMap μ i) (state μ)
      (factor μ i) (isSelfAdjoint_factorCoordinate μ i) (state_factor μ i)
  exact hpres.trans (law_factorCoordinate μ i)

/-- The real spectrum of the `i`-th canonical generator is contained in `(μ i).support`. -/
theorem spectrum_generator_subset_support (i : ι) :
    spectrum ℝ (generator μ i) ⊆ (μ i).support :=
  (AlgHom.spectrum_apply_subset ((factor μ i).toAlgHom.restrictScalars ℝ)
    (factorCoordinate μ i)).trans (spectrum_factorCoordinate_subset_support μ i)

/-- The canonical generators in `algebra μ` are freely independent for `state μ`. -/
theorem isFreelyIndependentElements_generator :
    IsFreelyIndependentElements (state μ).toLinearMap (generator μ) :=
  isFreelyIndependentElements_iff.mpr <|
    (isFreelyIndependent_bridgeFactor (factorFunctional μ) (factorFunctional_one μ)).mono fun i =>
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨factorCoordinate μ i, rfl⟩)

/-! #### Concrete von Neumann algebra realization -/

/-- The concrete von Neumann algebra on `HilbertSpace μ` generated by the reduced C⋆-free
product. -/
def vonNeumannAlgebra : VonNeumannAlgebra (HilbertSpace μ) :=
  VonNeumannAlgebra.adjoin (algebra μ : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ))

/-- The canonical `⋆`-algebra inclusion from the reduced C⋆-free product `algebra μ` into
`vonNeumannAlgebra μ`. -/
def toVonNeumannAlgebra : algebra μ →⋆ₐ[ℂ] vonNeumannAlgebra μ where
  toFun x := ⟨x.1, VonNeumannAlgebra.subset_adjoin _ x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem coe_toVonNeumannAlgebra (T : algebra μ) :
    ((toVonNeumannAlgebra μ T : vonNeumannAlgebra μ) :
      HilbertSpace μ →L[ℂ] HilbertSpace μ) = T := by
  rfl

/-- The vacuum vector state restricted to `vonNeumannAlgebra μ`. -/
def vonNeumannState : vonNeumannAlgebra μ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((vectorState μ).toLinearMap.comp (vonNeumannAlgebra μ).toStarSubalgebra.subtype.toLinearMap)
    fun _ hT => (vectorState μ).map_nonneg hT

theorem vonNeumannState_apply (T : vonNeumannAlgebra μ) :
    vonNeumannState μ T = vectorState μ (T : HilbertSpace μ →L[ℂ] HilbertSpace μ) := by
  rw [vonNeumannState, PositiveLinearMap.mk₀]
  rfl

@[simp]
theorem vonNeumannState_one : vonNeumannState μ 1 = 1 := by
  rw [vonNeumannState_apply, OneMemClass.coe_one, vectorState_one]

@[simp]
theorem vonNeumannState_toVonNeumannAlgebra (T : algebra μ) :
    vonNeumannState μ (toVonNeumannAlgebra μ T) = state μ T := by
  rw [vonNeumannState_apply, coe_toVonNeumannAlgebra, vectorState_apply, state_apply]

/-- The `i`-th canonical selfadjoint element inside `vonNeumannAlgebra μ` realizing `μ i`. -/
def vonNeumannGenerator (i : ι) : vonNeumannAlgebra μ :=
  toVonNeumannAlgebra μ (generator μ i)

theorem isSelfAdjoint_vonNeumannGenerator (i : ι) :
    IsSelfAdjoint (vonNeumannGenerator μ i) :=
  (isSelfAdjoint_generator μ i).map (toVonNeumannAlgebra μ)

@[simp]
theorem law_vonNeumannGenerator (i : ι) :
    (vonNeumannState μ).law (vonNeumannGenerator μ i) = μ i := by
  have h := PositiveLinearMap.law_starAlgHom (state μ) (vonNeumannState μ)
    (toVonNeumannAlgebra μ) (isSelfAdjoint_generator μ i)
    (vonNeumannState_toVonNeumannAlgebra μ)
  exact h.trans (law_generator μ i)

theorem spectrum_vonNeumannGenerator_subset_support (i : ι) :
    spectrum ℝ (vonNeumannGenerator μ i) ⊆ (μ i).support :=
  (AlgHom.spectrum_apply_subset ((toVonNeumannAlgebra μ).toAlgHom.restrictScalars ℝ)
    (generator μ i)).trans (spectrum_generator_subset_support μ i)

/-- The canonical generators inside `vonNeumannAlgebra μ` are freely independent for
`vonNeumannState μ`. -/
theorem isFreelyIndependentElements_vonNeumannGenerator :
    IsFreelyIndependentElements (vonNeumannState μ).toLinearMap (vonNeumannGenerator μ) :=
  (isFreelyIndependentElements_generator μ).map (toVonNeumannAlgebra μ).toAlgHom
    (by
      ext x
      exact vonNeumannState_toVonNeumannAlgebra μ x)

/-- The concrete von Neumann subalgebras generated by `vonNeumannGenerator μ i` on `HilbertSpace μ`
are freely independent for the weak-operator continuous vacuum vector state. -/
theorem isFreelyIndependent_vonNeumannAlgebra_adjoin_vonNeumannGenerator :
    IsFreelyIndependent (vectorState μ).toLinearMap
      (fun i => (VonNeumannAlgebra.adjoin
        {(vonNeumannGenerator μ i : HilbertSpace μ →L[ℂ] HilbertSpace μ)}).toSubalgebra) := by
  refine (isFreelyIndependent_vonNeumannAlgebra_adjoin_singleton_iff_of_isSelfAdjoint
    (T := fun i => (vonNeumannGenerator μ i : HilbertSpace μ →L[ℂ] HilbertSpace μ))
    (vectorState_one μ) (vacuum μ)
    (fun T => by rw [PositiveLinearMap.coe_toLinearMap, vectorState_apply])
    (fun i => (isSelfAdjoint_generator μ i).map (algebra μ).subtype)).mpr ?_
  exact (isFreelyIndependentElements_generator μ).map (algebra μ).subtype.toAlgHom
    (by
      ext x
      simp [vectorState_apply, state_apply])

end Product

end FreeLawRealization

end TauCeti
