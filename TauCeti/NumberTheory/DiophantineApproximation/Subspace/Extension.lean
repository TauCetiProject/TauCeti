/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.ApproxProd
public import TauCeti.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Mult
public import TauCeti.NumberTheory.NumberField.PlacesOver.Galois
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

The conjugating automorphisms are chosen as a function of the absolute value of `E` alone
(`NumberField.conjPair`), together with the place of `K` below it, which is recovered by
restricting to `K` (`NumberField.conjPair_infinitePlace`, `NumberField.conjPair_finitePlace`).
Their existence is the transitivity of the Galois action on the absolute values above a place.

The places of `E` above `Sinf` and `Sfin` are `NumberField.InfinitePlace.placesAbove E Sinf` and
`NumberField.FinitePlace.placesAbove E Sfin`.

## Main definitions

* `NumberField.conjPair w' u`: a place `v` of `K` below the absolute value `u` of `E` and an
  automorphism of `E / K` carrying `w' v` to `u`, or to the local-degree root of `u`.

## Main results

* `NumberField.approxProd_placesAbove`: a system of forms on `E` whose values at every place
  above `v` match those of `L v` under `w v` has as approximation product the `[E : K]`-th power
  of the original one.
* `NumberField.approxProd_placesAbove_le_mulHeight_rpow_iff`: the inequality of the Subspace
  Theorem holds for such a system over `E` exactly when it holds for `L` over `K`.
* `NumberField.conjPair_infinitePlace`, `NumberField.conjPair_finitePlace`: at a place of `E`
  above `v`, `conjPair` returns `v` and an automorphism carrying `w' v` to that place.

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
      W (L' W.1 i fun j ↦ algebraMap K E (x j)) = w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)))
    (hFin : ∀ v ∈ Sfin, ∀ W : FinitePlace E, W.LiesOver v → ∀ i,
      W.relativeAbsValue K (L' W.1 i fun j ↦ algebraMap K E (x j)) =
        w v.1 (L v.1 i fun j ↦ algebraMap K F (x j))) :
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
    exact iSup_congr fun j ↦ AbsoluteValue.LiesOver.apply_algebraMap v.1 (x j)
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
      W (L' W.1 i fun j ↦ algebraMap K E (x j)) = w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)))
    (hFin : ∀ v ∈ Sfin, ∀ W : FinitePlace E, W.LiesOver v → ∀ i,
      W.relativeAbsValue K (L' W.1 i fun j ↦ algebraMap K E (x j)) =
        w v.1 (L v.1 i fun j ↦ algebraMap K F (x j))) (r : ℝ) :
    approxProd (InfinitePlace.placesAbove E Sinf) (FinitePlace.placesAbove E Sfin) id L'
        (algebraMap K E ∘ x) ≤ Height.mulHeight (algebraMap K E ∘ x) ^ r ↔
      approxProd Sinf Sfin w L x ≤ Height.mulHeight x ^ r := by
  have h₀ := (Height.mulHeight_pos x).le
  have hpow : (Height.mulHeight x ^ finrank K E) ^ r = (Height.mulHeight x ^ r) ^ finrank K E := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h₀, ← Real.rpow_mul h₀,
      mul_comm]
  rw [approxProd_placesAbove hInf hFin, mulHeight_algebraMap, hpow]
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
    exact AbsoluteValue.LiesOver.apply_algebraMap v.1 (x i)
  · simp only [LinearMap.proj_apply, Algebra.algebraMap_self, RingHom.id_apply, id]
    exact FinitePlace.relativeAbsValue_algebraMap W v (x i)

/-! ### Conjugating automorphisms -/


variable [IsGalois K E]

open Classical in
/-- For an absolute value `u` of `E`, a place `v` of `K` below it together with an automorphism
`σ` of `E / K` carrying `w' v` to the absolute value that `u` induces over `v`: `u` itself when
`u` is an infinite place of `E`, and the local-degree root of `u` when `u` is a finite place.
When `u` is a place of `E` above a place `v` at which `w' v` lies over `v`, the pair has first
component `v` (`NumberField.conjPair_infinitePlace`, `NumberField.conjPair_finitePlace`); when no
such pair exists, `(u.under K, 1)` is returned. -/
noncomputable def conjPair (w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (u : AbsoluteValue E ℝ) :
    AbsoluteValue K ℝ × (E ≃ₐ[K] E) :=
  if h : ∃ p : AbsoluteValue K ℝ × (E ≃ₐ[K] E),
      (∃ (W : InfinitePlace E) (v : InfinitePlace K), W.1 = u ∧ v.1 = p.1 ∧ W.LiesOver v ∧
        p.2 • w' v.1 = W.1) ∨
      (∃ (W : FinitePlace E) (v : FinitePlace K), W.1 = u ∧ v.1 = p.1 ∧ W.LiesOver v ∧
        p.2 • w' v.1 = W.relativeAbsValue K)
  then h.choose else (u.under K, 1)

section conjPair

variable {w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ}

/-- The defining property of `conjPair` at an absolute value for which some pair exists. -/
private theorem conjPair_spec {u : AbsoluteValue E ℝ}
    (h : ∃ p : AbsoluteValue K ℝ × (E ≃ₐ[K] E),
      (∃ (W : InfinitePlace E) (v : InfinitePlace K), W.1 = u ∧ v.1 = p.1 ∧ W.LiesOver v ∧
        p.2 • w' v.1 = W.1) ∨
      (∃ (W : FinitePlace E) (v : FinitePlace K), W.1 = u ∧ v.1 = p.1 ∧ W.LiesOver v ∧
        p.2 • w' v.1 = W.relativeAbsValue K)) :
    (∃ (W : InfinitePlace E) (v : InfinitePlace K), W.1 = u ∧ v.1 = (conjPair w' u).1 ∧
        W.LiesOver v ∧ (conjPair w' u).2 • w' v.1 = W.1) ∨
      (∃ (W : FinitePlace E) (v : FinitePlace K), W.1 = u ∧ v.1 = (conjPair w' u).1 ∧
        W.LiesOver v ∧ (conjPair w' u).2 • w' v.1 = W.relativeAbsValue K) := by
  unfold conjPair
  split_ifs
  exact h.choose_spec

/-- At an infinite place `W` of `E` above `v`, with `w' v` lying over `v`, the place of `K` chosen
by `conjPair` is `v`, and its automorphism carries `w' v` to `W`. -/
theorem conjPair_infinitePlace (W : InfinitePlace E) (v : InfinitePlace K) [W.LiesOver v]
    (hw : (w' v.1).LiesOver v.1) :
    (conjPair w' W.1).1 = v.1 ∧ (conjPair w' W.1).2 • w' v.1 = W.1 := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_liesOver_infinitePlace v (w' v.1) W.1
  rcases conjPair_spec (w' := w') ⟨(v.1, σ), .inl ⟨W, v, rfl, rfl, inferInstance, hσ⟩⟩ with
    ⟨W₀, v₀, hW, hv, hWv, hσ₀⟩ | ⟨W₀, v₀, hW, -, -, -⟩
  · obtain rfl : W₀ = W := Subtype.ext hW
    obtain rfl : v₀ = v :=
      (InfinitePlace.LiesOver.comap_eq W₀ v₀).symm.trans (InfinitePlace.LiesOver.comap_eq W₀ v)
    exact ⟨hv.symm, hσ₀⟩
  · exact absurd hW (FinitePlace.val_ne_infinitePlace_val W₀ W)

/-- At a finite place `W` of `E` above `v`, with `w' v` lying over `v`, the place of `K` chosen by
`conjPair` is `v`, and its automorphism carries `w' v` to the local-degree root of `W`. -/
theorem conjPair_finitePlace (W : FinitePlace E) (v : FinitePlace K) [W.LiesOver v]
    (hw : (w' v.1).LiesOver v.1) :
    (conjPair w' W.1).1 = v.1 ∧ (conjPair w' W.1).2 • w' v.1 = W.relativeAbsValue K := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_liesOver_finitePlace v (w' v.1) (W.relativeAbsValue K)
  rcases conjPair_spec (w' := w') ⟨(v.1, σ), .inr ⟨W, v, rfl, rfl, inferInstance, hσ⟩⟩ with
    ⟨W₀, v₀, hW, -, -, -⟩ | ⟨W₀, v₀, hW, hv, hWv, hσ₀⟩
  · exact absurd hW.symm (FinitePlace.val_ne_infinitePlace_val W W₀)
  · obtain rfl : W₀ = W := Subtype.ext hW
    obtain rfl : v₀ = v := FinitePlace.eq_of_liesOver (w := W₀)
    exact ⟨hv.symm, hσ₀⟩

end conjPair

end NumberField
