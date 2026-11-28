/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Multiplicative indicators on finite adeles

A multiplicative indicator keeps the components on a set of places and replaces all other
components by one. The set need not be finite: replacing components by one preserves the
restricted product condition. Applied to a diagonal idele, this gives a principal component on a
chosen set of primes without introducing any new denominators elsewhere.

Applied to `0` on the complement of a set `S` of places, it gives the idempotent
`IsDedekindDomain.FiniteAdeleRing.indicatorOne S`, with component `1` at the places of `S` and `0`
elsewhere. Multiplying by it keeps the components on `S` and kills the others, so it cuts objects
over the finite adeles (for instance invertible matrices, through `IsIdempotentElem.cutGL`) into
their parts at the places of `S` and away from `S`.
-/

public noncomputable section

namespace IsDedekindDomain.FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

open scoped FiniteAdeleRing

/-- Keep the components of a finite adele in `S` and replace the rest by one. -/
def mulIndicator (S : Set (HeightOneSpectrum R)) : 𝔸ᶠ[R, K] →* 𝔸ᶠ[R, K] := by
  classical
  let f (a : 𝔸ᶠ[R, K]) : 𝔸ᶠ[R, K] := ⟨fun v ↦ if v ∈ S then a v else 1, by
    filter_upwards [a.cofinite_mem_adicCompletionIntegers] with v hv
    by_cases h : v ∈ S <;> simp [h, hv]⟩
  exact {
    toFun := f
    map_one' := ext K fun v ↦ by
      -- Evaluate the dependent tuple at `v` before simplifying the indicator.
      change (if v ∈ S then (1 : 𝔸ᶠ[R, K]) v else 1) = (1 : 𝔸ᶠ[R, K]) v
      simp
    map_mul' := fun a b ↦ ext K fun v ↦ by
      -- The two sides are coordinatewise products by definition of the restricted product.
      change (if v ∈ S then (a * b) v else 1) =
        (if v ∈ S then a v else 1) * (if v ∈ S then b v else 1)
      by_cases h : v ∈ S <;> simp [h] }

open Classical in
/-- The coordinate of a multiplicative indicator is the original coordinate on `S`, and one
elsewhere. -/
theorem mulIndicator_apply (S : Set (HeightOneSpectrum R)) (a : 𝔸ᶠ[R, K])
    (v : HeightOneSpectrum R) : mulIndicator S a v = if v ∈ S then a v else 1 := (rfl)

/-- On the selected places the multiplicative indicator keeps the original component. -/
@[simp] theorem mulIndicator_apply_of_mem {S : Set (HeightOneSpectrum R)} (a : 𝔸ᶠ[R, K])
    {v : HeightOneSpectrum R} (hv : v ∈ S) : mulIndicator S a v = a v := by
  classical
  rw [mulIndicator_apply, ite_eq_left hv]

/-- Off the selected places the multiplicative indicator has component one. -/
@[simp] theorem mulIndicator_apply_of_notMem {S : Set (HeightOneSpectrum R)} (a : 𝔸ᶠ[R, K])
    {v : HeightOneSpectrum R} (hv : v ∉ S) : mulIndicator S a v = 1 := by
  classical
  rw [mulIndicator_apply, ite_eq_right hv]

/-- The indicator is integral exactly when the selected components are integral. -/
theorem mulIndicator_mem_integralAdeles {S : Set (HeightOneSpectrum R)}
    {a : 𝔸ᶠ[R, K]} : mulIndicator S a ∈ integralAdeles R K ↔
      ∀ v ∈ S, a v ∈ v.adicCompletionIntegers K := by
  rw [mem_integralAdeles]
  refine ⟨fun h v hv ↦ by simpa [hv] using h v, fun h v ↦ ?_⟩
  by_cases hv : v ∈ S
  · simpa [hv] using h v hv
  · simp [hv]

/-- The **indicator of a set `S` of places**: the finite adele with component `1` at the places of
`S` and `0` elsewhere. It is the multiplicative indicator of the complement of `S` applied to `0`.
-/
def indicatorOne (S : Set (HeightOneSpectrum R)) : 𝔸ᶠ[R, K] :=
  mulIndicator Sᶜ 0

open Classical in
/-- The component of the indicator of `S` is `1` on `S` and `0` elsewhere. -/
theorem indicatorOne_apply (S : Set (HeightOneSpectrum R)) (v : HeightOneSpectrum R) :
    indicatorOne (K := K) S v = if v ∈ S then 1 else 0 := by
  by_cases hv : v ∈ S
  · rw [indicatorOne, mulIndicator_apply_of_notMem _ (Set.notMem_compl_iff.2 hv), ite_eq_left hv]
  · rw [indicatorOne, mulIndicator_apply_of_mem _ (Set.mem_compl hv), ite_eq_right hv,
      zero_apply]

/-- The indicator of `S` has component `1` at the places of `S`. -/
@[simp]
theorem indicatorOne_apply_of_mem {S : Set (HeightOneSpectrum R)} {v : HeightOneSpectrum R}
    (hv : v ∈ S) : indicatorOne (K := K) S v = 1 := by
  classical
  rw [indicatorOne_apply, ite_eq_left hv]

/-- The indicator of `S` has component `0` away from `S`. -/
@[simp]
theorem indicatorOne_apply_of_notMem {S : Set (HeightOneSpectrum R)} {v : HeightOneSpectrum R}
    (hv : v ∉ S) : indicatorOne (K := K) S v = 0 := by
  classical
  rw [indicatorOne_apply, ite_eq_right hv]

/-- The indicator of the empty set of places is `0`. -/
@[simp]
theorem indicatorOne_empty : indicatorOne (K := K) (∅ : Set (HeightOneSpectrum R)) = 0 :=
  ext K fun _ ↦ indicatorOne_apply_of_notMem (Set.notMem_empty _)

/-- The indicator of the set of all finite places is `1`. -/
@[simp]
theorem indicatorOne_univ : indicatorOne (K := K) (Set.univ : Set (HeightOneSpectrum R)) = 1 :=
  ext K fun _ ↦ indicatorOne_apply_of_mem (Set.mem_univ _)

/-- The indicator of `S` times the indicator of `T` is the indicator of `S ∩ T`. -/
@[simp]
theorem indicatorOne_mul_indicatorOne (S T : Set (HeightOneSpectrum R)) :
    indicatorOne (K := K) S * indicatorOne T = indicatorOne (S ∩ T) := by
  classical
  refine ext K fun v ↦ ?_
  simpa [indicatorOne_apply, Set.indicator_apply] using
    (congrFun (Set.inter_indicator_one (M₀ := v.adicCompletion K) (s := S) (t := T)) v).symm

/-- The indicator of a set of places is idempotent. -/
@[simp]
theorem isIdempotentElem_indicatorOne (S : Set (HeightOneSpectrum R)) :
    IsIdempotentElem (indicatorOne (K := K) S) := by
  rw [IsIdempotentElem, indicatorOne_mul_indicatorOne, Set.inter_self]

/-- `1` minus the indicator of `S` is the indicator of the complement of `S`. -/
@[simp]
theorem one_sub_indicatorOne (S : Set (HeightOneSpectrum R)) :
    1 - indicatorOne (K := K) S = indicatorOne Sᶜ := by
  classical
  refine ext K fun v ↦ ?_
  simpa [indicatorOne_apply, Set.indicator_apply] using
    (congrFun (Set.indicator_compl S (1 : HeightOneSpectrum R → v.adicCompletion K)) v).symm

/-- The indicator of a set of places is an integral finite adele. It takes priority over the
place-by-place unfolding `IsDedekindDomain.FiniteAdeleRing.mem_integralAdeles` as a `simp` lemma.
-/
@[simp high]
theorem indicatorOne_mem_integralAdeles (S : Set (HeightOneSpectrum R)) :
    indicatorOne (K := K) S ∈ integralAdeles R K :=
  mulIndicator_mem_integralAdeles.2 fun _ _ ↦ zero_mem _

/-- **Membership splits along a set of places.** A vector of a module over the finite adeles lies
in a submodule over the integral finite adeles if and only if its part `e_S • y` at the places of
`S` and its part `e_{Sᶜ} • y` away from `S` do. -/
theorem mem_iff_indicatorOne_smul_mem_and_indicatorOne_compl_smul_mem
    {M : Type*} [AddCommGroup M] [Module (FiniteAdeleRing R K) M]
    (S : Set (HeightOneSpectrum R)) {L : Submodule (integralAdeles R K) M} {y : M} :
    y ∈ L ↔ indicatorOne (K := K) S • y ∈ L ∧ indicatorOne (K := K) Sᶜ • y ∈ L := by
  have hsmul (T : Set (HeightOneSpectrum R)) (hy : y ∈ L) : indicatorOne (K := K) T • y ∈ L := by
    have := L.smul_mem (⟨_, indicatorOne_mem_integralAdeles T⟩ : integralAdeles R K) hy
    rwa [Subalgebra.smul_def] at this
  have hsum : indicatorOne (K := K) S • y + indicatorOne (K := K) Sᶜ • y = y := by
    rw [← one_sub_indicatorOne, ← add_smul, add_sub_cancel, one_smul]
  exact ⟨fun hy ↦ ⟨hsmul S hy, hsmul Sᶜ hy⟩, fun h ↦ hsum ▸ L.add_mem h.1 h.2⟩

end IsDedekindDomain.FiniteAdeleRing
