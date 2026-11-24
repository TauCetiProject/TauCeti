/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.ApproxProd
public import TauCeti.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.NumberField.PlacesOver.Relative

/-!
# The approximation product over a Galois extension

Let `K` be a number field, `x : ι → K` a point and `L v i` linear forms with coefficients in an
extension `F` of `K` at finite sets `Sinf` and `Sfin` of places of `K`, each measured by an
absolute value `w v` of `F`. The Subspace Theorem with such algebraic coefficients reduces to the
theorem with coefficients in the field of the points by passing to a finite Galois extension `E`
of `K` containing `F`. At each place `W` of `E` above `v` one puts a system of forms on `E` whose
values at the points of `K` are those of `L v`, conjugated by an automorphism of `E / K` that
carries an extension `w' v` of `w v` to the absolute value `W` induces over `v`.

Such a system reproduces the approximation product exactly, up to the power `[E : K]`
(`NumberField.approxProd_placesAbove`). At every place of `E` above `v` the point has the same
local factor as at `v`, read through the local-degree root at a finite place, and the local
degrees above `v`, respectively the multiplicities, add up to `[E : K]`, respectively
`mult v · [E : K]`. The relative height also changes by the power `[E : K]`
(`NumberField.mulHeight_algebraMap`), so the inequality of the Subspace Theorem over `K` is
equivalent to the same inequality over `E`
(`NumberField.approxProd_placesAbove_le_mulHeight_rpow_iff`).
Neither statement needs a Galois hypothesis.

When `E / K` is Galois, `NumberField.conjPair` chooses the conjugating automorphisms as a
function of the absolute value of `E` alone.

The places of `E` above `Sinf` and `Sfin` are `NumberField.InfinitePlace.placesAbove E Sinf` and
`NumberField.FinitePlace.placesAbove E Sfin`.

## Main results

* `NumberField.approxProd_placesAbove`: a system of forms on `E` whose values at every place
  above `v` match those of `L v` under `w v` has as approximation product the `[E : K]`-th power
  of the original one.
* `NumberField.approxProd_placesAbove_le_mulHeight_rpow_iff`: the inequality of the Subspace
  Theorem holds for such a system over `E` exactly when it holds for `L` over `K`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Theorem 7.2.2 and Remark 7.2.3.
-/

public section

open AbsoluteValue Module

namespace NumberField

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/-! ### The approximation product over the places above -/

variable {ι F : Type*} [Field F]

/-- **The approximation product over an extension.** Let `L'` be a system of forms on `E` whose
values at a point `x : ι → K` reproduce, at every place `W` of `E` above a place `v ∈ Sinf ∪ Sfin`,
the values of the forms `L v` under `w v`: exactly at an infinite place, and after taking the
local-degree root at a finite place. Then the approximation product of `x` with respect to `L'`
over the places of `E` above `Sinf` and `Sfin` is the `[E : K]`-th power of its approximation
product with respect to `L`. -/
theorem approxProd_placesAbove [Fintype ι] [Algebra K F] {Sinf : Finset (InfinitePlace K)}
    {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {L' : AbsoluteValue E ℝ → ι → Dual E (ι → E)} {x : ι → K}
    (hInf : ∀ v ∈ Sinf, ∀ W : InfinitePlace E, W.LiesOver v → ∀ i,
      W (L' W.val i fun j ↦ algebraMap K E (x j)) = w v.val (L v.val i fun j ↦ algebraMap K F
          (x j)))
    (hFin : ∀ v ∈ Sfin, ∀ W : FinitePlace E, W.LiesOver v → ∀ i,
      W.relativeAbsValue K (L' W.val i fun j ↦ algebraMap K E (x j)) =
        w v.val (L v.val i fun j ↦ algebraMap K F (x j))) :
    approxProd (InfinitePlace.placesAbove E Sinf) (FinitePlace.placesAbove E Sfin) id L'
        (algebraMap K E ∘ x) = approxProd Sinf Sfin w L x ^ finrank K E := by
  simp only [approxProd_def, id, Algebra.algebraMap_self, RingHom.id_apply, Function.comp_apply,
    mul_pow]
  congr 1
  · refine InfinitePlace.prod_placesAbove_pow_mult Sinf _ _ fun v hv W hW ↦ ?_
    simp only [InfinitePlace.coe_apply]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← InfinitePlace.coe_apply, hInf v hv W hW i]
    congr 1
    exact iSup_congr fun j ↦ AbsoluteValue.LiesOver.apply_algebraMap v.val (x j)
  · refine FinitePlace.prod_placesAbove Sfin _ _ fun v hv W hW ↦ ?_
    have hd : W.localDegree K ≠ 0 := (FinitePlace.localDegree_pos W).ne'
    simp only [FinitePlace.coe_apply]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [div_pow, Real.iSup_pow_of_ne_zero (fun _ ↦ apply_nonneg _ _) hd, ← FinitePlace.coe_apply,
      ← FinitePlace.relativeAbsValue_pow_localDegree (K := K), hFin v hv W hW i]
    congr 1
    refine iSup_congr fun j ↦ ?_
    rw [← FinitePlace.coe_apply, FinitePlace.apply_algebraMap W v, FinitePlace.coe_apply]

/-- **The inequality of the Subspace Theorem over an extension.** Under the hypotheses of
`NumberField.approxProd_placesAbove`, a point `x : ι → K` satisfies `approxProd ≤ mulHeight ^ r`
for `L'` over the places of `E` above `Sinf` and `Sfin` exactly when it satisfies it for `L` over
`K`: both sides are raised to the power `[E : K]` (`NumberField.mulHeight_algebraMap`). -/
theorem approxProd_placesAbove_le_mulHeight_rpow_iff [Fintype ι] [Algebra K F]
    {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {L' : AbsoluteValue E ℝ → ι → Dual E (ι → E)} {x : ι → K}
    (hInf : ∀ v ∈ Sinf, ∀ W : InfinitePlace E, W.LiesOver v → ∀ i,
      W (L' W.val i fun j ↦ algebraMap K E (x j)) = w v.val (L v.val i fun j ↦ algebraMap K F
          (x j)))
    (hFin : ∀ v ∈ Sfin, ∀ W : FinitePlace E, W.LiesOver v → ∀ i,
      W.relativeAbsValue K (L' W.val i fun j ↦ algebraMap K E (x j)) =
        w v.val (L v.val i fun j ↦ algebraMap K F (x j))) (r : ℝ) :
    approxProd (InfinitePlace.placesAbove E Sinf) (FinitePlace.placesAbove E Sfin) id L'
        (algebraMap K E ∘ x) ≤ Height.mulHeight (algebraMap K E ∘ x) ^ r ↔
      approxProd Sinf Sfin w L x ≤ Height.mulHeight x ^ r := by
  have h₀ := (Height.mulHeight_pos x).le
  rw [approxProd_placesAbove hInf hFin, mulHeight_algebraMap, ← Real.rpow_pow_comm h₀]
  exact pow_le_pow_iff_left₀ (approxProd_nonneg x) (Real.rpow_nonneg h₀ r) finrank_pos.ne'

/-- The hypotheses of `NumberField.approxProd_placesAbove` hold for the coordinate forms at every
place, each place of `K` measuring itself: the approximation product of the coordinate forms over
the places of `E` above `Sinf` and `Sfin` is its `[E : K]`-th power over `K`. -/
example [Fintype ι] (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (x : ι → K) :
    approxProd (InfinitePlace.placesAbove E Sinf) (FinitePlace.placesAbove E Sfin) id
        (fun _ i ↦ LinearMap.proj i) (algebraMap K E ∘ x) =
      approxProd Sinf Sfin id (fun _ i ↦ LinearMap.proj i) x ^ finrank K E := by
  refine approxProd_placesAbove (fun v _ W _ i ↦ ?_) fun v _ W _ i ↦ ?_
  · simp only [LinearMap.proj_apply, Algebra.algebraMap_self, RingHom.id_apply, id]
    exact AbsoluteValue.LiesOver.apply_algebraMap v.val (x i)
  · simp only [LinearMap.proj_apply, Algebra.algebraMap_self, RingHom.id_apply, id]
    exact FinitePlace.relativeAbsValue_algebraMap W v (x i)

end NumberField
