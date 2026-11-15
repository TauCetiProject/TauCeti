/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Analysis.InnerProductSpace.Polar.Deformation
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.NegativeSubspace
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Polar factors of negative blocks along a composite

On `E × F` with the split indefinite form `Q(u, v) = -‖u‖² + ‖v‖²`, a *negative frame* is an
operator `L : E →L[ℝ] E × F` whose nonzero values lie strictly inside the negative cone
`‖v‖ < ‖u‖`. Its negative block `fst ∘ L` is then injective, hence invertible when `E` is
finite-dimensional, and its polar factor is a linear isometry of `E`. The change of Morse
coordinates compares negative discs through these polar factors.

The polar factor is not multiplicative along composites. Let `A` map the negative cone into itself
and let `L` be a negative frame. The negative block of `A ∘ L` is
`fst ∘ A ∘ L = A_uu (fst ∘ L) + A_us (snd ∘ L)`, which involves the block `A_us` of `A` from `F` to
`E`, so the polar factor of `fst ∘ A ∘ L` is in general not the composite of the polar factors of
`A_uu = fst ∘ A ∘ inl` and of `fst ∘ L`. This file shows that the two are joined by a canonical
homotopy of linear isometries, continuous in `A` and `L`
(`ContinuousLinearMap.exists_homotopy_polarFactor_fst_comp_comp_of_norm_snd_lt`). It is the
composite of two homotopies, each the polar factor of a path of invertible operators.

* The polar deformations `U P^(1-s)` of `A_uu` and of `fst ∘ L`
  (`ContinuousLinearMap.polarDeformation`) join the product of the two negative blocks to the
  product of their polar factors. That product is an isometry, so it is its own polar factor
  (`ContinuousLinearMap.polarFactor_eq_self_of_forall_norm_eq`, in
  `TauCeti.Analysis.InnerProductSpace.Polar.Bounded`).
* The straight-line contraction `L_t = (fst ∘ L, t • snd ∘ L)` of the frame `L`
  (`ContinuousLinearMap.negativeContraction`) stays negative, so `A ∘ L_t` does too, and the
  negative blocks `fst ∘ A ∘ L_t` stay invertible. At `t = 0` this negative block is the product
  `A_uu (fst ∘ L)`, at `t = 1` it is `fst ∘ A ∘ L`.

The same path of frames shows that the signs of the determinants multiply
(`ContinuousLinearMap.sign_det_fst_comp_comp_of_norm_snd_lt`); the homotopy here refines that
statement from the components of the orthogonal group to an explicit path, continuous over any
parameter space. For three Morse charts with transitions `A₀₁` and `A₁₂`, it joins `h₀₁ h₁₂` to
`h₀₂`, where `h_ij` is the polar factor of the negative block of `A_ij` and `A₀₂ = A₀₁ A₁₂`.

Normalized Morse charts take values in `ℝⁿ` with `f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, and
their negative blocks are `ι† A ι` for the zero extension `ι : ℝᵏ → ℝⁿ` onto the first `k`
coordinates. Splitting the coordinates of `ℝⁿ` into the first `k` and the remaining ones
(`EuclideanSpace.sumComplEquivProd`) carries the homotopy to these coordinates
(`TauCeti.exists_homotopy_polarFactor_adjoint_piLpExtendByZero_comp_comp`).

## Main results

* `ContinuousLinearMap.exists_homotopy_polarFactor_fst_comp_comp_of_norm_snd_lt`: for families
  `A x` preserving the negative cone and negative frames `L x`, continuous in `x`, a homotopy of
  linear isometries from the composite of the polar factors of `fst ∘ A x ∘ inl` and of
  `fst ∘ L x` to the polar factor of `fst ∘ A x ∘ L x`, continuous in `x`.
* `TauCeti.exists_homotopy_polarFactor_adjoint_piLpExtendByZero_comp_comp`: the same homotopy for
  the Euclidean negative blocks `ι† D₁ ι`, `ι† D₂ ι` and `ι† D₁ D₂ ι` of operators of `ℝⁿ`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Lemma 3.6.
-/

public section

open Set unitInterval

namespace ContinuousLinearMap

section NegativeFrame

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] {X : Type*} [TopologicalSpace X]

/-- Along the straight-line contraction of a negative frame `L`, the negative blocks of `A ∘ L_t`
stay invertible when `A` maps the negative cone into itself. -/
private theorem isUnit_fst_comp_comp_negativeContraction {A : E × F →L[ℝ] E × F}
    {L : E →L[ℝ] E × F} (hA : ∀ z : E × F, ‖z.2‖ < ‖z.1‖ → ‖(A z).2‖ < ‖(A z).1‖)
    (hL : ∀ u, u ≠ 0 → ‖(L u).2‖ < ‖(L u).1‖) (t : I) :
    IsUnit ((fst ℝ E F).comp (A.comp (L.negativeContraction t))) :=
  isInvertible_iff_isUnit.1 <|
    (A.comp (L.negativeContraction t)).isInvertible_fst_comp_of_norm_snd_lt fun _ hu ↦
      hA _ (L.norm_snd_negativeContraction_lt hL (abs_le.2 ⟨by linarith [t.2.1], t.2.2⟩) hu)

/-- The polar factors of the composites of the polar deformations of two continuous families of
invertible operators depend continuously on the time and the parameter. -/
private theorem continuous_polarFactor_polarDeformation_comp {a l : X → E →L[ℝ] E}
    (hac : Continuous a) (hlc : Continuous l) (hau : ∀ x, IsUnit (a x))
    (hlu : ∀ x, IsUnit (l x)) :
    Continuous fun q : I × X ↦
      ((a q.2).polarDeformation q.1 ∘L (l q.2).polarDeformation q.1).polarFactor := by
  have hd {b : X → E →L[ℝ] E} (hbc : Continuous b) (hbu : ∀ x, IsUnit (b x)) :
      Continuous fun q : I × X ↦ (b q.2).polarDeformation q.1 :=
    continuousOn_polarDeformation.comp_continuous
      ((hbc.comp continuous_snd).prodMk (continuous_subtype_val.comp continuous_fst)) fun q ↦
        ⟨isStrictlyPositive_modulus_of_isInvertible (isInvertible_iff_isUnit.2 (hbu q.2)),
          mem_univ _⟩
  refine continuousOn_polarFactor_isUnit.comp_continuous ((hd hac hau).clm_comp (hd hlc hlu))
    fun q ↦ ?_
  rw [← mul_def]
  exact ((a q.2).isUnit_polarDeformation (hau q.2) _).mul
    ((l q.2).isUnit_polarDeformation (hlu q.2) _)

/-- The polar factors of the negative blocks of `A x ∘ (L x)_t`, along the straight-line
contractions of negative frames `L x`, depend continuously on the time and the parameter. -/
private theorem continuous_polarFactor_fst_comp_comp_negativeContraction
    {A : X → E × F →L[ℝ] E × F} {L : X → E →L[ℝ] E × F} (hAc : Continuous A)
    (hLc : Continuous L) (hA : ∀ x (z : E × F), ‖z.2‖ < ‖z.1‖ → ‖(A x z).2‖ < ‖(A x z).1‖)
    (hL : ∀ x u, u ≠ 0 → ‖(L x u).2‖ < ‖(L x u).1‖) :
    Continuous fun q : I × X ↦
      ((fst ℝ E F).comp ((A q.2).comp ((L q.2).negativeContraction q.1))).polarFactor := by
  have heq : (fun q : I × X ↦ (L q.2).negativeContraction q.1) = fun q ↦
      (inl ℝ E F).comp ((fst ℝ E F).comp (L q.2)) +
        (q.1 : ℝ) • (inr ℝ E F).comp ((snd ℝ E F).comp (L q.2)) := by
    funext q
    ext u <;> simp
  have hcon : Continuous fun q : I × X ↦
      (fst ℝ E F).comp ((A q.2).comp ((L q.2).negativeContraction q.1)) := by
    refine (compL ℝ E (E × F) E (fst ℝ E F)).continuous.comp
      ((hAc.comp continuous_snd).clm_comp ?_)
    rw [heq]
    fun_prop
  exact continuousOn_polarFactor_isUnit.comp_continuous hcon fun q ↦
    isUnit_fst_comp_comp_negativeContraction (hA q.2) (hL q.2) q.1

/-- **The polar factors of negative blocks compose up to a homotopy of isometries, continuously
in parameters.** Let `A x` map the negative cone `‖v‖ < ‖u‖` of `E × F` into itself and let
`L x : E →L[ℝ] E × F` be a frame whose nonzero values lie in that cone, both continuous in `x`.
The polar factor of the negative block `fst ∘ A x ∘ L x` of the composite need not be the composite
of the polar factors of `fst ∘ A x ∘ inl` and of `fst ∘ L x`, but the two are joined by a homotopy
`H` through linear isometries of `E`, continuous in the parameter `x` as well as in time. -/
theorem exists_homotopy_polarFactor_fst_comp_comp_of_norm_snd_lt {A : X → E × F →L[ℝ] E × F}
    {L : X → E →L[ℝ] E × F} (hAc : Continuous A) (hLc : Continuous L)
    (hA : ∀ x (z : E × F), ‖z.2‖ < ‖z.1‖ → ‖(A x z).2‖ < ‖(A x z).1‖)
    (hL : ∀ x u, u ≠ 0 → ‖(L x u).2‖ < ‖(L x u).1‖) :
    ∃ H : C(I × X, E →L[ℝ] E),
      (∀ x, H (0, x) = ((fst ℝ E F).comp ((A x).comp (inl ℝ E F))).polarFactor ∘L
        ((fst ℝ E F).comp (L x)).polarFactor) ∧
      (∀ x, H (1, x) = ((fst ℝ E F).comp ((A x).comp (L x))).polarFactor) ∧
      ∀ p v, ‖H p v‖ = ‖v‖ := by
  -- The negative blocks `a x = fst ∘ A x ∘ inl` and `l x = fst ∘ L x` are invertible.
  set a : X → E →L[ℝ] E := fun x ↦ (fst ℝ E F).comp ((A x).comp (inl ℝ E F))
  set l : X → E →L[ℝ] E := fun x ↦ (fst ℝ E F).comp (L x)
  have hfst := (compL ℝ E (E × F) E (fst ℝ E F)).continuous
  have hac : Continuous a :=
    hfst.comp ((compL ℝ E (E × F) (E × F)).flip (inl ℝ E F) |>.continuous.comp hAc)
  have hlc : Continuous l := hfst.comp hLc
  have hau (x : X) : IsUnit (a x) := isInvertible_iff_isUnit.1 <|
    isInvertible_fst_comp_of_norm_snd_lt _ fun u hu ↦ hA x _ (by simpa using norm_pos_iff.2 hu)
  have hlu (x : X) : IsUnit (l x) :=
    isInvertible_iff_isUnit.1 <| isInvertible_fst_comp_of_norm_snd_lt _ (hL x)
  have hisom {T : E →L[ℝ] E} (hT : IsUnit T) (v : E) : ‖T.polarFactor v‖ = ‖v‖ :=
    T.norm_polarFactor_apply_of_injective (isUnit_iff_bijective.1 hT).injective v
  have hΦ := continuous_polarFactor_polarDeformation_comp hac hlc hau hlu
  have hΨ := continuous_polarFactor_fst_comp_comp_negativeContraction hAc hLc hA hL
  -- The homotopies are taken through operators of norm-preserving values.
  let P : C(X, E →L[ℝ] E) → Prop := fun g ↦ ∀ x v, ‖g x v‖ = ‖v‖
  let gm : C(X, E →L[ℝ] E) := ⟨fun x ↦ (a x ∘L l x).polarFactor,
    hΦ.comp ((continuous_const (y := (0 : I))).prodMk continuous_id) |>.congr fun x ↦ by simp⟩
  let g₀ : C(X, E →L[ℝ] E) := ⟨fun x ↦ (a x).polarFactor ∘L (l x).polarFactor,
    (continuousOn_polarFactor_isUnit.comp_continuous hac hau).clm_comp
      (continuousOn_polarFactor_isUnit.comp_continuous hlc hlu)⟩
  let g₁ : C(X, E →L[ℝ] E) := ⟨fun x ↦ ((fst ℝ E F).comp ((A x).comp (L x))).polarFactor,
    hΨ.comp ((continuous_const (y := (1 : I))).prodMk continuous_id) |>.congr fun x ↦ by simp⟩
  -- The polar deformations of `a x` and `l x` join `(a x ∘ l x).polarFactor` to `g₀`.
  let F₁ : ContinuousMap.HomotopyWith gm g₀ P :=
    { toFun := fun q ↦ ((a q.2).polarDeformation q.1 ∘L (l q.2).polarDeformation q.1).polarFactor
      continuous_toFun := hΦ
      map_zero_left := fun x ↦ by simp [gm]
      map_one_left := fun x ↦ by
        simp only [Icc.coe_one, polarDeformation_one, g₀, ContinuousMap.coe_mk]
        exact polarFactor_eq_self_of_forall_norm_eq fun v ↦ by
          rw [comp_apply, hisom (hau x), hisom (hlu x)]
      prop' := fun t x v ↦ hisom (by
        rw [← mul_def]
        exact ((a x).isUnit_polarDeformation (hau x) _).mul
          ((l x).isUnit_polarDeformation (hlu x) _)) v }
  -- The contraction of the frame `L x` joins `(a x ∘ l x).polarFactor` to `g₁`.
  let F₂ : ContinuousMap.HomotopyWith gm g₁ P :=
    { toFun := fun q ↦
        ((fst ℝ E F).comp ((A q.2).comp ((L q.2).negativeContraction q.1))).polarFactor
      continuous_toFun := hΨ
      map_zero_left := fun x ↦ by
        simp only [Icc.coe_zero, negativeContraction_zero, gm, ContinuousMap.coe_mk, a, l,
          ContinuousLinearMap.comp_assoc]
      map_one_left := fun x ↦ by simp [g₁]
      prop' := fun t x v ↦ hisom (isUnit_fst_comp_comp_negativeContraction (hA x) (hL x) t) v }
  let G := F₁.symm.trans F₂
  exact ⟨G.toContinuousMap, G.apply_zero, G.apply_one, fun p v ↦ G.prop p.1 p.2 v⟩

end NegativeFrame

end ContinuousLinearMap

namespace TauCeti

open ContinuousLinearMap LinearIsometry

variable {n k : ℕ}

/-- In Euclidean coordinates, the negative block `ι† D ι` of an operator `D` of `ℝⁿ`, for the zero
extension `ι : ℝᵏ → ℝⁿ` onto the first `k` coordinates, is the negative block of `D` read in the
coordinates split into the first `k` and the remaining ones, conjugated by the reindexing
`ℝᵏ ≃ ℝ^{j < k}`. -/
private theorem adjoint_piLpExtendByZero_comp_comp_eq (hk : k ≤ n)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    adjoint (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L D ∘L
        (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap =
      ((EuclideanSpace.finCastLEEquiv ℝ hk).symm :
          EuclideanSpace ℝ {j : Fin n // j.val < k} →L[ℝ] EuclideanSpace ℝ (Fin k)) ∘L
        ((fst ℝ _ _).comp (((EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k) :
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ {j : Fin n // j.val < k} ×
              EuclideanSpace ℝ {j : Fin n // ¬j.val < k}) ∘L D ∘L
          ((EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k).symm :
            EuclideanSpace ℝ {j : Fin n // j.val < k} ×
              EuclideanSpace ℝ {j : Fin n // ¬j.val < k} →L[ℝ] EuclideanSpace ℝ (Fin n)) ∘L
          inl ℝ _ _)) ∘L
        ((EuclideanSpace.finCastLEEquiv ℝ hk).symm.symm :
          EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ {j : Fin n // j.val < k}) := by
  ext1 w
  simp only [comp_apply, EuclideanSpace.adjoint_piLpExtendByZero_castLEEmb_apply,
    LinearIsometryEquiv.symm_symm, ContinuousLinearEquiv.coe_coe, coe_fst',
    LinearIsometry.coe_toContinuousLinearMap]
  rw [← EuclideanSpace.finCastLEEquiv_symm_fst_sumComplEquivProd hk,
    ← EuclideanSpace.sumComplEquivProd_symm_finCastLEEquiv hk w]
  simp

/-- **The polar factors of Euclidean negative blocks compose up to a homotopy of isometries,
continuously in parameters.** Let `q(y) = -Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²` on `ℝⁿ` and let
`ι : ℝᵏ → ℝⁿ` be the zero extension onto the first `k` coordinates. Let `D₁ x` carry vectors with
`q < 0` to vectors with `q < 0`, and let `q (D₂ x (ι w)) < 0` for `w ≠ 0`, both continuously in
`x`; for instance `D₁ x` and `D₂ x` preserve `q`, as the derivatives at the centre of transitions
between Morse charts do. Then the composite of the polar factors of the negative blocks
`ι† D₁ x ι` and `ι† D₂ x ι` is joined to the polar factor of the negative block of `D₁ x ∘ D₂ x`
by a homotopy `H` through linear isometries of `ℝᵏ`, continuous in the parameter `x`. -/
theorem exists_homotopy_polarFactor_adjoint_piLpExtendByZero_comp_comp (hk : k ≤ n)
    {X : Type*} [TopologicalSpace X]
    {D₁ D₂ : X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hD₁c : Continuous D₁) (hD₂c : Continuous D₂)
    (hD₁ : ∀ x y, ∑ j, (if j.val < k then -1 else 1) * y j ^ 2 < 0 →
      ∑ j, (if j.val < k then -1 else 1) * D₁ x y j ^ 2 < 0)
    (hD₂ : ∀ x w, w ≠ 0 → ∑ j, (if j.val < k then -1 else 1) *
      D₂ x (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w) j ^ 2 < 0) :
    ∃ H : C(I × X, EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)),
      (∀ x, H (0, x) =
        (adjoint (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L D₁ x ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor ∘L
        (adjoint (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L D₂ x ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor) ∧
      (∀ x, H (1, x) =
        (adjoint (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
          (D₁ x ∘L D₂ x) ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor) ∧
      ∀ p v, ‖H p v‖ = ‖v‖ := by
  set S := EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k
  set e := EuclideanSpace.finCastLEEquiv ℝ hk
  -- In the split coordinates `q` is `-‖u‖² + ‖v‖²`, so `q < 0` is the negative cone.
  have hq (y : EuclideanSpace ℝ (Fin n)) :
      ∑ j, (if j.val < k then -1 else 1) * y j ^ 2 < 0 ↔ ‖(S y).2‖ < ‖(S y).1‖ := by
    rw [EuclideanSpace.sum_ite_neg_one_mul_sq_eq, neg_add_lt_iff_lt_add, add_zero]
    exact pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero
  set A : X → (EuclideanSpace ℝ {j : Fin n // j.val < k} ×
      EuclideanSpace ℝ {j : Fin n // ¬j.val < k}) →L[ℝ] (EuclideanSpace ℝ {j : Fin n // j.val < k} ×
        EuclideanSpace ℝ {j : Fin n // ¬j.val < k}) :=
    fun x ↦ (S : EuclideanSpace ℝ (Fin n) →L[ℝ] _) ∘L D₁ x ∘L (S.symm : _ →L[ℝ] _)
  set L : X → EuclideanSpace ℝ {j : Fin n // j.val < k} →L[ℝ]
      (EuclideanSpace ℝ {j : Fin n // j.val < k} × EuclideanSpace ℝ {j : Fin n // ¬j.val < k}) :=
    fun x ↦ (S : EuclideanSpace ℝ (Fin n) →L[ℝ] _) ∘L D₂ x ∘L
      (S.symm : EuclideanSpace ℝ {j : Fin n // j.val < k} ×
        EuclideanSpace ℝ {j : Fin n // ¬j.val < k} →L[ℝ] _) ∘L inl ℝ _ _
  have hA (x : X) (z) (hz : ‖z.2‖ < ‖z.1‖) : ‖(A x z).2‖ < ‖(A x z).1‖ := by
    have h := (hq (S.symm z)).2 (by rwa [ContinuousLinearEquiv.apply_symm_apply])
    simpa [A] using (hq _).1 (hD₁ x _ h)
  have hL (x : X) (u) (hu : u ≠ 0) : ‖(L x u).2‖ < ‖(L x u).1‖ := by
    have hw : e.symm u ≠ 0 := by simpa using hu
    have h := (hq _).1 (hD₂ x _ hw)
    rwa [← EuclideanSpace.sumComplEquivProd_symm_finCastLEEquiv hk,
      LinearIsometryEquiv.apply_symm_apply] at h
  obtain ⟨H, h0, h1, hH⟩ := exists_homotopy_polarFactor_fst_comp_comp_of_norm_snd_lt
    (A := A) (L := L) (continuous_const.clm_comp (hD₁c.clm_comp continuous_const))
    (continuous_const.clm_comp (hD₂c.clm_comp continuous_const)) hA hL
  -- Conjugating by the reindexing `e : ℝᵏ ≃ ℝ^{j < k}` gives the homotopy in `ℝᵏ`.
  refine ⟨⟨fun p ↦ (e.symm : EuclideanSpace ℝ {j : Fin n // j.val < k} →L[ℝ] _) ∘L H p ∘L
      (e.symm.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] _),
    by fun_prop⟩, fun x ↦ ?_,
    fun x ↦ ?_, fun p v ↦ ?_⟩
  · simp only [ContinuousMap.coe_mk, h0, adjoint_piLpExtendByZero_comp_comp_eq hk,
      polarFactor_conj]
    ext1 w
    simp [A, L, S, e, ContinuousLinearMap.comp_assoc]
  · simp only [ContinuousMap.coe_mk, h1, adjoint_piLpExtendByZero_comp_comp_eq hk,
      polarFactor_conj]
    congr 3
    ext1 w
    simp [A, L, S]
  · simp [hH]

end TauCeti
