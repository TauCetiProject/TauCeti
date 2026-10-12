/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

/-!
# Totally isotropic subspaces and the Witt index

A subspace `W` of a quadratic space `(V, Q)` is *totally isotropic*
(`QuadraticMap.IsTotallyIsotropic`) when `Q` vanishes on every vector of `W`. Over a field in
which `2` is invertible, every maximal totally isotropic subspace of a regular finite-dimensional
quadratic space has dimension equal to the Witt index of `Q` (Lam I.4.4). The Witt index,
defined by `TauCeti.RegularFormClass.wittIndex` as the number of hyperbolic planes in the Witt
decomposition `Q ≅ m × ℍ ⊥ Q_a`, is therefore intrinsic to the quadratic space: it is the common
dimension of its maximal totally isotropic subspaces, and the largest dimension of a totally
isotropic subspace.

## Main results

* `QuadraticForm.finrank_eq_wittIndex_of_maximal`: **Lam I.4.4**, a maximal totally isotropic
  subspace of a regular space has dimension the Witt index.
* `QuadraticMap.IsTotallyIsotropic.finrank_le_wittIndex`: every totally isotropic subspace of a
  regular space has dimension at most the Witt index.
* `QuadraticMap.IsTotallyIsotropic.exists_le_finrank_eq_wittIndex`: every totally isotropic
  subspace of a regular space lies in one whose dimension is the Witt index.
* `QuadraticForm.maximal_isTotallyIsotropic_iff`: a totally isotropic subspace of a regular space
  is maximal exactly when its dimension is the Witt index.

## Implementation notes

The comparison goes by induction on the dimension. A nonzero vector `w` of a maximal totally
isotropic subspace `W` has an isotropic partner `f` with `polar Q w f = 1`. The span of `w` and
`f` is a hyperbolic plane, its orthogonal complement `U` has Witt index one less, and `W ∩ U` is a
maximal totally isotropic subspace of `U` of dimension one less.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §4.
-/

public section

open Module

namespace TauCeti

open _root_.QuadraticMap

universe u v

variable {K : Type u} [Field K]

/-! ### Splitting a hyperbolic pair off a totally isotropic subspace

Throughout, `w ∈ W` lies in a totally isotropic subspace `W` and `f` satisfies `polar Q w f = 1`.
Write `U` for the orthogonal complement of the span of `w` and `f`. Then `W` is the direct sum of
the line through `w` and `W ∩ U`, and `W ∩ U` is maximal in `U` when `W` is maximal in `V`. -/

section HyperbolicPair

variable {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {W : Submodule K V} {w f : V}

private theorem mem_orthogonal_span_pair_iff_polar {v : V} :
    v ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {w, f}) ↔
      polar Q w v = 0 ∧ polar Q f v = 0 := by
  simp only [LinearMap.BilinForm.mem_orthogonal_span_pair_iff, polarBilin_apply_apply]

/-- Subtracting `polar Q f v • w` moves `v ∈ W` into `U`. -/
private theorem sub_polar_smul_mem_orthogonal_span_pair (hTI : Q.IsTotallyIsotropic W)
    (hwW : w ∈ W) (hwf : polar Q w f = 1) {v : V} (hv : v ∈ W) :
    v - polar Q f v • w ∈
      LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {w, f}) := by
  rw [mem_orthogonal_span_pair_iff_polar, polar_sub_right, polar_smul_right, polar_sub_right,
    polar_smul_right, polar_self, hTI.apply_eq_zero hwW, hTI.polar_eq_zero hwW hv,
    polar_comm Q f w, hwf]
  simp

/-- The vectors of `W` orthogonal to `w` and `f` form, inside `U`, a subspace of dimension one
less than `W`. -/
private theorem finrank_comap_orthogonal_span_pair_add_one [FiniteDimensional K V]
    (hTI : Q.IsTotallyIsotropic W) (hwW : w ∈ W) (hwf : polar Q w f = 1) :
    finrank K (W.comap
      (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {w, f})).subtype) + 1 =
      finrank K W := by
  set U := LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {w, f})
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hwf
  have hsup : (K ∙ w) ⊔ (U ⊓ W) = W := by
    refine le_antisymm (sup_le ((Submodule.span_singleton_le_iff_mem w W).mpr hwW) inf_le_right)
      fun v hv ↦ ?_
    rw [← add_sub_cancel (polar Q f v • w) v]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
      ⟨sub_polar_smul_mem_orthogonal_span_pair hTI hwW hwf hv, W.sub_mem hv (W.smul_mem _ hwW)⟩
  have hinf : (K ∙ w) ⊓ (U ⊓ W) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hy, hyU, -⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hc : c = 0 := by
      simpa [polar_smul_right, polar_comm Q f w, hwf] using
        (mem_orthogonal_span_pair_iff_polar.mp hyU).2
    rw [hc, zero_smul]
    exact Submodule.zero_mem _
  have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ w) (U ⊓ W)
  rw [hsup, hinf, finrank_bot, add_zero, finrank_span_singleton hw0,
    ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq] at h
  rw [h, add_comm]

/-- If `W` is maximal totally isotropic in `V`, then the vectors of `W` orthogonal to `w` and `f`
form a maximal totally isotropic subspace of `U`. -/
private theorem maximal_comap_orthogonal_span_pair (hW : Maximal Q.IsTotallyIsotropic W)
    (hwW : w ∈ W) (hwf : polar Q w f = 1) :
    Maximal (Q.restrict
      (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {w, f}))).IsTotallyIsotropic
      (W.comap
        (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {w, f})).subtype) := by
  set U := LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {w, f})
  have hTI := hW.prop
  refine ⟨hTI.restrict U, fun T hT hle t ht ↦ ?_⟩
  -- Adjoining the line through `w` to a totally isotropic `T ⊆ U` keeps it totally isotropic.
  have hT' : Q.IsTotallyIsotropic ((K ∙ w) ⊔ T.map U.subtype) := by
    refine isTotallyIsotropic_iff.mpr fun v hv ↦ ?_
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hz
    rw [QuadraticMap.map_add Q, Q.map_smul, hTI.apply_eq_zero hwW,
      (isTotallyIsotropic_restrict_iff.mp hT).apply_eq_zero (Submodule.mem_map_of_mem hs),
      polar_smul_left, Submodule.subtype_apply, (mem_orthogonal_span_pair_iff_polar.mp s.2).1]
    simp
  have hWle : W ≤ (K ∙ w) ⊔ T.map U.subtype := by
    intro v hv
    rw [← add_sub_cancel (polar Q f v • w) v]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
      ⟨⟨_, sub_polar_smul_mem_orthogonal_span_pair hTI hwW hwf hv⟩, hle ?_, rfl⟩
    exact W.sub_mem hv (W.smul_mem _ hwW)
  exact hW.2 hT' hWle (Submodule.mem_sup_right ⟨t, ht, rfl⟩)

end HyperbolicPair

/-- **Lam I.4.4**, by induction on the dimension `n` of the space. -/
private theorem finrank_eq_wittIndex_of_maximal_aux [Invertible (2 : K)] (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : QuadraticForm K V) (hQ : Q.Nondegenerate), finrank K V = n →
      ∀ {W : Submodule K V}, Maximal Q.IsTotallyIsotropic W →
        finrank K W = RegularFormClass.wittIndex (formClass Q hQ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ Q hQ hn W hW
  by_cases hbot : W = ⊥
  · subst hbot
    rw [finrank_bot, eq_comm, RegularFormClass.wittIndex_eq_zero_iff,
      QuadraticForm.anisotropic_formClass]
    exact maximal_isTotallyIsotropic_bot_iff.mp hW
  -- Split off the hyperbolic plane spanned by a nonzero `w ∈ W` and an isotropic partner `f`;
  -- both the dimension of `W` and the Witt index drop by one on the orthogonal complement `U`.
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hwQ : Q w = 0 := hW.prop.apply_eq_zero hwW
  obtain ⟨f, hfQ, hwf⟩ :=
    exists_isotropic_polar_eq_one_of_radical_eq_bot hQ.radical_eq_bot hw0 hwQ
  set U := LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {w, f})
  have hequiv := Q.equivalent_hyperbolicPlane_prod_restrict_orthogonal hwQ hfQ hwf
  have hU := hQ.nondegenerate_restrict_orthogonal_span_pair hwQ hfQ hwf
  have hindex : RegularFormClass.wittIndex (formClass Q hQ) =
      RegularFormClass.wittIndex (formClass (Q.restrict U) hU) + 1 := by
    have hclass : formClass Q hQ = 1 • hyperbolicClass K + formClass (Q.restrict U) hU := by
      rw [one_nsmul, ← formClass_hyperbolicPlane, ← formClass_prod, formClass_eq_iff]
      exact hequiv
    rw [hclass, RegularFormClass.wittIndex_nsmul_hyperbolicClass_add, add_comm]
  have hdim : finrank K V = finrank K U + 2 := by
    obtain ⟨e⟩ := hequiv
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_fin_fun, add_comm]
  rw [← finrank_comap_orthogonal_span_pair_add_one hW.prop hwW hwf, hindex,
    ih (finrank K U) (by omega) (Q.restrict U) hU rfl
      (maximal_comap_orthogonal_span_pair hW hwW hwf)]

end TauCeti

namespace QuadraticForm

open TauCeti

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **Lam I.4.4.** Every maximal totally isotropic subspace of a regular finite-dimensional
quadratic space has dimension the Witt index of the form. -/
theorem finrank_eq_wittIndex_of_maximal (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {W : Submodule K V} (hW : Maximal Q.IsTotallyIsotropic W) :
    finrank K W = RegularFormClass.wittIndex (formClass Q hQ) :=
  finrank_eq_wittIndex_of_maximal_aux _ Q hQ rfl hW

end QuadraticForm

namespace QuadraticMap

open TauCeti

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {W : Submodule K V}

/-- Every totally isotropic subspace of a regular finite-dimensional quadratic space lies in a
totally isotropic subspace whose dimension is the Witt index. -/
theorem IsTotallyIsotropic.exists_le_finrank_eq_wittIndex (hQ : Q.Nondegenerate)
    (hW : Q.IsTotallyIsotropic W) :
    ∃ W' : Submodule K V, W ≤ W' ∧ Q.IsTotallyIsotropic W' ∧
      finrank K W' = RegularFormClass.wittIndex (formClass Q hQ) := by
  obtain ⟨W', hle, hW'⟩ := exists_maximal_ge_of_wellFoundedGT _ W hW
  exact ⟨W', hle, hW'.prop, QuadraticForm.finrank_eq_wittIndex_of_maximal Q hQ hW'⟩

/-- Every totally isotropic subspace of a regular finite-dimensional quadratic space has
dimension at most the Witt index. -/
theorem IsTotallyIsotropic.finrank_le_wittIndex (hQ : Q.Nondegenerate)
    (hW : Q.IsTotallyIsotropic W) :
    finrank K W ≤ RegularFormClass.wittIndex (formClass Q hQ) := by
  obtain ⟨W', hle, -, hW'⟩ := hW.exists_le_finrank_eq_wittIndex hQ
  exact hW' ▸ Submodule.finrank_mono hle

end QuadraticMap

namespace QuadraticForm

open TauCeti

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A totally isotropic subspace of a regular finite-dimensional quadratic space is maximal
exactly when its dimension is the Witt index: the maximal totally isotropic subspaces are those
of largest dimension. -/
theorem maximal_isTotallyIsotropic_iff (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {W : Submodule K V} :
    Maximal Q.IsTotallyIsotropic W ↔
      Q.IsTotallyIsotropic W ∧ finrank K W = RegularFormClass.wittIndex (formClass Q hQ) := by
  refine ⟨fun hW ↦ ⟨hW.prop, finrank_eq_wittIndex_of_maximal Q hQ hW⟩,
    fun ⟨hW, hfin⟩ ↦ ⟨hW, fun U hU hle ↦ ?_⟩⟩
  rw [Submodule.eq_of_le_of_finrank_le hle (hfin ▸ hU.finrank_le_wittIndex hQ)]

end QuadraticForm
