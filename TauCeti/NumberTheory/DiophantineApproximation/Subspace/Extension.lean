/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.CompRingHom
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.ApproxProd
public import TauCeti.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.NumberField.PlacesOver.Galois
public import TauCeti.NumberTheory.NumberField.PlacesOver.Relative

import TauCeti.LinearAlgebra.Submodule.CoordinateRestriction

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

A finite set of proper subspaces of `ι → E` containing the solutions over `E` restricts to at
most as many proper subspaces of `ι → K` containing the solutions over `K`
(`NumberField.exists_finset_submodule_of_approxProd_le_of_placesAbove`), so the Subspace Theorem
for such a system over `E` gives it for `L` over `K`.

When `E / K` is Galois, `NumberField.conjPair` chooses the conjugating automorphisms as a
function of the absolute value of `E` alone, and the conjugate system
`NumberField.conjSystem w' L` is such a system. Extension of the coefficients from `F` to `E` and
conjugation are one coefficient transport, `Module.Dual.compRingHom` along `σ ∘ algebraMap F E`,
and it preserves linear independence.

The places of `E` above `Sinf` and `Sfin` are `NumberField.InfinitePlace.placesAbove E Sinf` and
`NumberField.FinitePlace.placesAbove E Sfin`.

## Main definitions

* `NumberField.conjSystem w' L`: the conjugate system of forms on `E`.

## Main results

* `NumberField.approxProd_placesAbove`: a system of forms on `E` whose values at every place
  above `v` match those of `L v` under `w v` has as approximation product the `[E : K]`-th power
  of the original one.
* `NumberField.approxProd_placesAbove_le_mulHeight_rpow_iff`: the inequality of the Subspace
  Theorem holds for such a system over `E` exactly when it holds for `L` over `K`.
* `NumberField.exists_finset_submodule_of_approxProd_le_of_placesAbove`: a cover of the solutions
  over `E` by proper subspaces descends to a cover of the solutions over `K`.
* `NumberField.approxProd_conjSystem`: the conjugate system reproduces the approximation product,
  up to the power `[E : K]`.
* `NumberField.linearIndependent_conjSystem_infinitePlace`,
  `NumberField.linearIndependent_conjSystem_finitePlace`: at the places above `v` the conjugate
  system is linearly independent exactly when `L v` is.

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

/-- **Descent of a subspace cover from the extension.** Under the hypotheses of
`NumberField.approxProd_placesAbove`, a finite set `T` of proper subspaces of `ι → E` containing
the image of every nonzero `x : ι → K` with `approxProd ≤ mulHeight ^ r` for `L'` over the places
of `E` above `Sinf` and `Sfin` gives at most as many proper subspaces of `ι → K` containing every
nonzero `x` with `approxProd ≤ mulHeight ^ r` for `L` over `K`: the restrictions of the members of
`T` to the points of `K`. -/
theorem exists_finset_submodule_of_approxProd_le_of_placesAbove [Fintype ι] [Algebra K F]
    {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {L' : AbsoluteValue E ℝ → ι → Dual E (ι → E)} {r : ℝ}
    (hInf : ∀ x : ι → K, ∀ v ∈ Sinf, ∀ W : InfinitePlace E, W.LiesOver v → ∀ i,
      W (L' W.val i fun j ↦ algebraMap K E (x j)) = w v.val (L v.val i fun j ↦ algebraMap K F
          (x j)))
    (hFin : ∀ x : ι → K, ∀ v ∈ Sfin, ∀ W : FinitePlace E, W.LiesOver v → ∀ i,
      W.relativeAbsValue K (L' W.val i fun j ↦ algebraMap K E (x j)) =
        w v.val (L v.val i fun j ↦ algebraMap K F (x j)))
    (T : Finset (Submodule E (ι → E))) (hT : ∀ W ∈ T, W ≠ ⊤)
    (hTx : ∀ x : ι → K, x ≠ 0 →
      approxProd (InfinitePlace.placesAbove E Sinf) (FinitePlace.placesAbove E Sfin) id L'
          (algebraMap K E ∘ x) ≤ Height.mulHeight (algebraMap K E ∘ x) ^ r →
        ∃ W ∈ T, algebraMap K E ∘ x ∈ W) :
    ∃ T₀ : Finset (Submodule K (ι → K)), T₀.card ≤ T.card ∧ (∀ U ∈ T₀, U ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 → approxProd Sinf Sfin w L x ≤ Height.mulHeight x ^ r →
        ∃ U ∈ T₀, x ∈ U := by
  obtain ⟨T₀, hcard, hT₀, hmem⟩ :=
    T.exists_finset_submodule_card_le_and_piAlgebraMap_mem_iff (R := K) hT
  refine ⟨T₀, hcard, hT₀, fun x hx hle ↦ (hmem x).mp ?_⟩
  exact hTx x hx ((approxProd_placesAbove_le_mulHeight_rpow_iff (hInf x) (hFin x) r).mpr hle)

/-! ### The conjugate system -/

section conjSystem

variable [IsGalois K E] [Algebra F E] [Finite ι]

/-- The **conjugate system**: at an absolute value `u` of `E`, with `(v, σ) = conjPair w' u`, the
forms `L v` with their coefficients extended from `F` to `E` and then conjugated by `σ`. At the
places of `E` above a place `v` of `K` over which `w v` and its extension `w' v` lie, it measures
the points of `K` as `w v` measures `L v` (`NumberField.apply_conjSystem_infinitePlace`,
`NumberField.relativeAbsValue_conjSystem_finitePlace`), and it is linearly independent when `L v`
is (`NumberField.linearIndependent_conjSystem_infinitePlace`,
`NumberField.linearIndependent_conjSystem_finitePlace`). -/
noncomputable def conjSystem (w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (u : AbsoluteValue E ℝ) (i : ι) :
    Dual E (ι → E) :=
  (L (conjPair w' u).1 i).compRingHom (((conjPair w' u).2 : E →+* E).comp (algebraMap F E))

variable {w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}

/-- The defining formula of the conjugate system. -/
theorem conjSystem_def (u : AbsoluteValue E ℝ) (i : ι) :
    conjSystem w' L u i =
      (L (conjPair w' u).1 i).compRingHom (((conjPair w' u).2 : E →+* E).comp (algebraMap F E)) :=
  (rfl)

/-- On a point with coordinates in `K`, a form of the conjugate system takes the value of the
original form, conjugated by the automorphism that `conjPair` chooses. -/
theorem conjSystem_apply_algebraMap [Algebra K F] [IsScalarTower K F E]
    (u : AbsoluteValue E ℝ) (i : ι) (x : ι → K) :
    conjSystem w' L u i (fun j ↦ algebraMap K E (x j)) =
      (conjPair w' u).2 (algebraMap F E (L (conjPair w' u).1 i fun j ↦ algebraMap K F (x j))) := by
  rw [conjSystem_def]
  refine (L (conjPair w' u).1 i).compRingHom_apply_algebraMap_comp_of_commutes _ (fun a ↦ ?_) x
  simp [← IsScalarTower.algebraMap_apply]

/-- If `conjPair` chooses the place `v` below `u` and an automorphism carrying `w' v` to `u'`,
then `u'` measures the conjugate system at `u` on the points of `K` as `w v` measures the forms
`L v`, provided `w' v` lies over `w v`. -/
private theorem apply_conjSystem_of_conjPair [Algebra K F] [IsScalarTower K F E]
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {u u' : AbsoluteValue E ℝ} {v : AbsoluteValue K ℝ}
    [(w' v).LiesOver (w v)] (h₁ : (conjPair w' u).1 = v) (h₂ : (conjPair w' u).2 • w' v = u')
    (i : ι) (x : ι → K) :
    u' (conjSystem w' L u i fun j ↦ algebraMap K E (x j)) =
      w v (L v i fun j ↦ algebraMap K F (x j)) := by
  subst h₁ h₂
  simp [AbsoluteValue.smul_apply, conjSystem_apply_algebraMap, AlgEquiv.smul_def,
    AbsoluteValue.LiesOver.apply_algebraMap (w (conjPair w' u).1)]

/-- At an infinite place `W` of `E` above `v`, with `w v` lying over `v` and `w' v` over `w v`,
the conjugate system measures the points of `K` as `w v` measures the forms `L v`. -/
theorem apply_conjSystem_infinitePlace [Algebra K F] [IsScalarTower K F E]
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} (W : InfinitePlace E) (v : InfinitePlace K)
    [W.LiesOver v] [(w v.val).LiesOver v.val] [(w' v.val).LiesOver (w v.val)] (i : ι)
    (x : ι → K) :
    W (conjSystem w' L W.val i fun j ↦ algebraMap K E (x j)) =
      w v.val (L v.val i fun j ↦ algebraMap K F (x j)) := by
  obtain ⟨h₁, h₂⟩ := conjPair_infinitePlace (w' := w') W v (.trans v.val (w v.val) (w' v.val))
  exact apply_conjSystem_of_conjPair h₁ h₂ i x

/-- At a finite place `W` of `E` above `v`, with `w v` lying over `v` and `w' v` over `w v`,
the local-degree root of `W` measures the conjugate system on the points of `K` as `w v`
measures the forms `L v`. -/
theorem relativeAbsValue_conjSystem_finitePlace [Algebra K F] [IsScalarTower K F E]
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} (W : FinitePlace E) (v : FinitePlace K)
    [W.LiesOver v] [(w v.val).LiesOver v.val] [(w' v.val).LiesOver (w v.val)] (i : ι)
    (x : ι → K) :
    W.relativeAbsValue K (conjSystem w' L W.val i fun j ↦ algebraMap K E (x j)) =
      w v.val (L v.val i fun j ↦ algebraMap K F (x j)) := by
  obtain ⟨h₁, h₂⟩ := conjPair_finitePlace (w' := w') W v (.trans v.val (w v.val) (w' v.val))
  exact apply_conjSystem_of_conjPair h₁ h₂ i x

/-- The conjugate system at `u` is linearly independent exactly when the forms `L v` are, for
the place `v` that `conjPair` chooses below `u`. -/
theorem linearIndependent_conjSystem_iff (u : AbsoluteValue E ℝ) :
    LinearIndependent E (conjSystem w' L u) ↔ LinearIndependent F (L (conjPair w' u).1) :=
  Module.Dual.linearIndependent_compRingHom_iff

/-- At an infinite place of `E` above `v`, with `w' v` lying over `v`, the conjugate system is
linearly independent exactly when the forms `L v` are. -/
theorem linearIndependent_conjSystem_infinitePlace (W : InfinitePlace E) (v : InfinitePlace K)
    [W.LiesOver v] [(w' v.val).LiesOver v.val] :
    LinearIndependent E (conjSystem w' L W.val) ↔ LinearIndependent F (L v.val) := by
  rw [linearIndependent_conjSystem_iff, (conjPair_infinitePlace W v inferInstance).1]

/-- At a finite place of `E` above `v`, with `w' v` lying over `v`, the conjugate system is
linearly independent exactly when the forms `L v` are. -/
theorem linearIndependent_conjSystem_finitePlace (W : FinitePlace E) (v : FinitePlace K)
    [W.LiesOver v] [(w' v.val).LiesOver v.val] :
    LinearIndependent E (conjSystem w' L W.val) ↔ LinearIndependent F (L v.val) := by
  rw [linearIndependent_conjSystem_iff, (conjPair_finitePlace W v inferInstance).1]

/-- **The approximation product of the conjugate system.** Let `E / K` be a finite Galois
extension containing `F`, and at each place `v` in `Sinf` and `Sfin` let `w v` lie over `v` and
`w' v` over `w v`. Then for every `x : ι → K` the approximation product of `x` with respect to the
conjugate system over the places of `E` above `Sinf` and `Sfin`, each place measured by itself,
is the `[E : K]`-th power of its approximation product with respect to `L`. -/
theorem approxProd_conjSystem [Fintype ι] [Algebra K F] [IsScalarTower K F E]
    {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hwInf : ∀ v ∈ Sinf, (w v.val).LiesOver v.val) (hwFin : ∀ v ∈ Sfin, (w v.val).LiesOver v.val)
    (hw'Inf : ∀ v ∈ Sinf, (w' v.val).LiesOver (w v.val))
    (hw'Fin : ∀ v ∈ Sfin, (w' v.val).LiesOver (w v.val)) (x : ι → K) :
    approxProd (InfinitePlace.placesAbove E Sinf) (FinitePlace.placesAbove E Sfin) id
        (conjSystem w' L) (algebraMap K E ∘ x) =
      approxProd Sinf Sfin w L x ^ finrank K E := by
  refine approxProd_placesAbove (fun v hv W _ i ↦ ?_) fun v hv W _ i ↦ ?_
  · have := hwInf v hv
    have := hw'Inf v hv
    exact apply_conjSystem_infinitePlace W v i x
  · have := hwFin v hv
    have := hw'Fin v hv
    exact relativeAbsValue_conjSystem_finitePlace W v i x

end conjSystem

end NumberField
