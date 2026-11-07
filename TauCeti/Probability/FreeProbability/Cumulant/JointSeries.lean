/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Free
public import TauCeti.Probability.FreeProbability.Cumulant.Series
public import TauCeti.Probability.FreeProbability.Distribution.Basic
public import TauCeti.RingTheory.WordSeries.PowerSeries

/-!
# Joint moment and R-series

Joint moments and free cumulants are coefficients of series in noncommuting letters.
`jointMomentSeries` includes the empty-word moment, whereas `jointRSeries` has zero
constant coefficient and places the cumulant of order `n` in degree `n`.
In one variable the latter is therefore `z R(z)`, not the shifted scalar R-series.

The joint R-series determines a normalized joint distribution. Freeness of families
of generators is equivalent to vanishing of its coefficients on words mixing the
specified families. These are formal identities, without positivity or convergence
assumptions; the alphabet need not be finite.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*,
  Lectures 11 and 16.
-/

public section

noncomputable section

open Finset

namespace TauCeti

variable {R A B ι κ : Type*}

section Moment

variable [Monoid A]

/-- The joint moment series: the coefficient of a word is its ordered moment,
including the empty-word moment `φ 1`. -/
def jointMomentSeries (φ : A → R) (a : ι → A) : WordSeries ι R :=
  WordSeries.mk fun w => φ (w.toList.map a).prod

@[simp]
theorem coeff_jointMomentSeries (φ : A → R) (a : ι → A) (w : FreeMonoid ι) :
    WordSeries.coeff w (jointMomentSeries φ a) = φ (w.toList.map a).prod := by
  rw [jointMomentSeries, WordSeries.coeff_mk]

@[simp]
theorem constantCoeff_jointMomentSeries [Semiring R] (φ : A → R) (a : ι → A) :
    WordSeries.constantCoeff (jointMomentSeries φ a) = φ 1 := by
  simp [WordSeries.constantCoeff_apply]

/-- On a one-letter alphabet the joint moment series is the ordinary moment series. -/
theorem jointMomentSeries_unique [Semiring R] [Unique ι] (φ : A → R) (a : ι → A) :
    jointMomentSeries φ a = WordSeries.powerSeriesEquiv (momentSeries φ (a default)) := by
  ext w
  simp only [coeff_jointMomentSeries, WordSeries.coeff_powerSeriesEquiv, coeff_momentSeries]
  have h : w.toList.map a = List.replicate w.toList.length (a default) :=
    List.eq_replicate_iff.mpr ⟨by simp, by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact congrArg a (Subsingleton.elim i default)⟩
  rw [h, List.prod_replicate]

end Moment

section Cumulant

variable [CommRing R] [Monoid A]

/-- The joint R-series, with zero constant coefficient and the order-`n` free
cumulant as the coefficient of each word of length `n ≥ 1`. -/
def jointRSeries (φ : A → R) (a : ι → A) : WordSeries ι R :=
  WordSeries.mk fun w => if w.toList.length = 0 then 0 else
    freeCumulant φ (a ∘ w.toList.get) univ

/-- Coefficients at nonempty words are free cumulants in the displayed word order. -/
@[simp]
theorem coeff_jointRSeries (φ : A → R) (a : ι → A) (w : FreeMonoid ι)
    (hw : w.toList.length ≠ 0) :
    WordSeries.coeff w (jointRSeries φ a) = freeCumulant φ (a ∘ w.toList.get) univ := by
  simp only [jointRSeries, WordSeries.coeff_mk, ite_eq_right hw]

@[simp]
theorem constantCoeff_jointRSeries (φ : A → R) (a : ι → A) :
    WordSeries.constantCoeff (jointRSeries φ a) = 0 := by
  simp [WordSeries.constantCoeff_apply, jointRSeries]

/-- A finite tuple gives the coefficient of its corresponding word. The zero-degree
case is separated from the cumulant convention at the empty set. -/
theorem coeff_jointRSeries_ofFn (φ : A → R) (a : ι → A) {n : ℕ} (w : Fin n → ι)
    (hn : n ≠ 0) :
    WordSeries.coeff (FreeMonoid.ofList (List.ofFn w)) (jointRSeries φ a) =
      freeCumulant φ (a ∘ w) univ := by
  rw [coeff_jointRSeries φ a _ (by simpa using hn)]
  -- The length of List.ofFn is propositionally, not definitionally, the tuple length.
  -- Transport positions through the order isomorphism rather than unfolding cumulants.
  have h := freeCumulant_comp_of_strictMonoOn (s := univ) φ
    ((Fin.castOrderIso (List.length_ofFn (f := w))).strictMono.strictMonoOn _) (a ∘ w)
  rw [image_univ_of_surjective (Fin.castOrderIso (List.length_ofFn (f := w))).surjective] at h
  simpa [Function.comp_def, List.get_ofFn, Fin.castOrderIso_apply, Fin.cast] using h

/-- The one-variable joint R-series is `z R(z)`, not the shifted scalar R-series. -/
theorem jointRSeries_unique [Unique ι] (φ : A → R) (a : ι → A) :
    jointRSeries φ a = WordSeries.powerSeriesEquiv (PowerSeries.X * rSeries φ (a default)) := by
  ext w
  rw [WordSeries.coeff_powerSeriesEquiv]
  by_cases hw : w.toList.length = 0
  · simp only [jointRSeries, WordSeries.coeff_mk, hw, ↓reduceIte,
      PowerSeries.coeff_zero_X_mul]
  · rw [coeff_jointRSeries φ a w hw,
      freeCumulant_congr φ (a := a ∘ w.toList.get) (b := fun _ => a default)
        (fun i _ => congrArg a (Subsingleton.elim _ _)),
      freeCumulant_const_eq_coeff_freeCumulantSeries φ (a default) univ,
      card_univ, Fintype.card_fin]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hw
    rw [hn, PowerSeries.coeff_succ_X_mul, coeff_succ_freeCumulantSeries]

/-- Equal joint moments give equal joint R-series, even without normalization. -/
theorem jointRSeries_congr [Monoid B] {φ : A → R} {ψ : B → R}
    {a : ι → A} {b : ι → B} (h : jointMomentSeries φ a = jointMomentSeries ψ b) :
    jointRSeries φ a = jointRSeries ψ b := by
  ext w
  by_cases hw : w.toList.length = 0
  · simp only [jointRSeries, WordSeries.coeff_mk, hw, ↓reduceIte]
  · rw [coeff_jointRSeries φ a w hw, coeff_jointRSeries ψ b w hw]
    simp only [freeCumulant_eq_sum_mu_mul_partitionMoment, partitionMoment_def]
    refine sum_congr rfl fun π _ => congrArg (_ * ·) ?_
    refine prod_congr rfl fun C _ => ?_
    have hc := congrArg (WordSeries.coeff
      (FreeMonoid.ofList (C.sort.map w.toList.get))) h
    simpa only [coeff_jointMomentSeries, FreeMonoid.toList_ofList, List.map_map] using hc

/-- The joint R-series determines all word moments once the empty-word moment is fixed. -/
theorem jointMomentSeries_eq_of_jointRSeries_eq [Monoid B] {φ : A → R} {ψ : B → R}
    {a : ι → A} {b : ι → B} (h1 : φ 1 = ψ 1)
    (h : jointRSeries φ a = jointRSeries ψ b) :
    jointMomentSeries φ a = jointMomentSeries ψ b := by
  ext w
  rw [coeff_jointMomentSeries, coeff_jointMomentSeries]
  by_cases hw : w.toList.length = 0
  · simpa only [List.length_eq_zero_iff.mp hw, List.map_nil, List.prod_nil] using h1
  · have hc {C : Finset (Fin w.toList.length)} (hC : C.Nonempty) :
        freeCumulant φ (a ∘ w.toList.get) C = freeCumulant ψ (b ∘ w.toList.get) C := by
      rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ _ C,
        freeCumulant_eq_freeCumulant_comp_orderEmbOfFin ψ _ C]
      have he := congrArg (WordSeries.coeff
        (FreeMonoid.ofList (List.ofFn (w.toList.get ∘ C.orderEmbOfFin rfl)))) h
      simpa only [coeff_jointRSeries_ofFn _ _ _ hC.card_pos.ne', Function.comp_assoc] using he
    -- List.ofFn lists the positions in their original order, including repetitions of letters.
    rw [← List.ofFn_get w.toList, List.map_ofFn, List.map_ofFn,
      apply_prod_ofFn_eq_sum_prod_freeCumulant φ hw,
      apply_prod_ofFn_eq_sum_prod_freeCumulant ψ hw]
    exact sum_congr rfl fun π _ => prod_congr rfl fun C hC =>
      hc (π.1.nonempty_of_mem_parts hC)

end Cumulant

section Distribution

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B}

/-- Joint moment series and joint algebraic distributions encode the same word moments. -/
theorem jointMomentSeries_eq_iff_jointDistribution_eq :
    jointMomentSeries φ a = jointMomentSeries ψ b ↔
      jointDistribution φ a = jointDistribution ψ b := by
  rw [jointDistribution_eq_iff]
  exact ⟨fun h w => by
    simpa only [coeff_jointMomentSeries, FreeMonoid.toList_ofList] using
      congrArg (WordSeries.coeff (FreeMonoid.ofList w)) h,
    fun h => WordSeries.ext fun w => by simpa only [coeff_jointMomentSeries] using h w.toList⟩

end Distribution

section Algebra

variable [CommRing R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B}

/-- The joint R-series is a complete invariant of algebraic distributions with the
same empty-word moment; in particular, this applies to normalized functionals. -/
theorem jointRSeries_eq_iff_jointDistribution_eq (h1 : φ 1 = ψ 1) :
    jointRSeries φ a = jointRSeries ψ b ↔ jointDistribution φ a = jointDistribution ψ b :=
  ⟨fun h => jointMomentSeries_eq_iff_jointDistribution_eq.mp
      (jointMomentSeries_eq_of_jointRSeries_eq h1 h),
    fun h => jointRSeries_congr (jointMomentSeries_eq_iff_jointDistribution_eq.mpr h)⟩

/-- Subalgebras generated by specified groups of letters are free exactly when the
joint R-series has no coefficient mixing those groups. No injectivity of the
label map `g` or of the family `a` is required. -/
theorem isFreelyIndependent_adjoin_iff_coeff_jointRSeries_eq_zero (hφ : φ 1 = 1)
    (a : ι → A) (g : ι → κ) :
    (IsFreelyIndependent φ fun i => Algebra.adjoin R (a '' {j | g j = i})) ↔
      ∀ (w : FreeMonoid ι) (k k' : Fin w.toList.length),
        g (w.toList.get k) ≠ g (w.toList.get k') →
          WordSeries.coeff w (jointRSeries φ a) = 0 := by
  rw [isFreelyIndependent_adjoin_iff_freeCumulant_eq_zero hφ]
  constructor
  · intro h w k k' hkk'
    have hw : w.toList.length ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt k.isLt)
    rw [coeff_jointRSeries φ a w hw]
    exact h _ (a ∘ w.toList.get) (g ∘ w.toList.get)
      (fun q => ⟨w.toList.get q, rfl, rfl⟩) k k' hkk'
  · intro h n c ℓ hc k k' hkk'
    choose v hgv hav using hc
    have hn : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt k.isLt)
    have he := h (FreeMonoid.ofList (List.ofFn v))
      ((Fin.castOrderIso (List.length_ofFn (f := v))).symm k)
      ((Fin.castOrderIso (List.length_ofFn (f := v))).symm k')
    have hg : g (v k) ≠ g (v k') := by
      rw [hgv k, hgv k']
      exact hkk'
    have hz := he (by simpa [List.get_ofFn, Fin.castOrderIso, Fin.cast] using hg)
    rw [coeff_jointRSeries_ofFn φ a v hn] at hz
    have ha : a ∘ v = c := funext hav
    rwa [ha] at hz

end Algebra

end TauCeti
