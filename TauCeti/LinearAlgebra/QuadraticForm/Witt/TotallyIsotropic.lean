/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.zero_isRepresentedBy_of_hyperbolicPlane_prod` and
  `TauCeti.zero_baseChange_isRepresentedBy_of_hyperbolicPlane_prod`: cancelling a hyperbolic plane
  from a totally isotropic embedding (before and after scalar extension).

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

/-- Subtracting `polar Q f v • w` moves `v ∈ W` into `U`. -/
private theorem sub_polar_smul_mem_orthogonal_span_pair (hTI : Q.IsTotallyIsotropic W)
    (hwW : w ∈ W) (hwf : polar Q w f = 1) {v : V} (hv : v ∈ W) :
    v - polar Q f v • w ∈
      LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {w, f}) := by
  simp [LinearMap.BilinForm.orthogonal, polar_sub_right, polar_smul_right, polar_self,
    hTI.apply_eq_zero hwW, hTI.polar_eq_zero hwW hv, polar_comm Q f w, hwf]

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
      obtain ⟨-, hfc⟩ : polar Q w (c • w) = 0 ∧ polar Q f (c • w) = 0 := by
        simpa [U, LinearMap.BilinForm.orthogonal] using hyU
      simpa [polar_smul_right, polar_comm Q f w, hwf] using hfc
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
    obtain ⟨hws, -⟩ : polar Q w s = 0 ∧ polar Q f s = 0 := by
      simpa [U, LinearMap.BilinForm.orthogonal] using s.2
    rw [QuadraticMap.map_add Q, Q.map_smul, hTI.apply_eq_zero hwW,
      (isTotallyIsotropic_restrict_iff.mp hT).apply_eq_zero (Submodule.mem_map_of_mem hs),
      polar_smul_left, Submodule.subtype_apply, hws]
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

namespace TauCeti

open _root_.QuadraticMap Module

universe u

section HyperbolicCancellation

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- Cancelling a hyperbolic plane from an embedding of a zero form into `H ⊥ Q` reduces the
dimension of the represented zero space by at least one. No nondegeneracy or finiteness hypothesis
is needed on `Q`. -/
theorem zero_isRepresentedBy_of_hyperbolicPlane_prod
    {U' U M : Type*} [AddCommGroup U'] [Module K U'] [FiniteDimensional K U']
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup M] [Module K M]
    {Q : QuadraticForm K M}
    (h : (0 : QuadraticForm K U).IsRepresentedBy ((hyperbolicPlane K).prod Q))
    (hk : finrank K U' + 1 ≤ finrank K U) :
    (0 : QuadraticForm K U').IsRepresentedBy Q := by
  obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff _ _).mp h
  let f₁ : U →ₗ[K] Fin 2 → K := (LinearMap.fst K (Fin 2 → K) M).comp f
  let f₂ : U →ₗ[K] M := (LinearMap.snd K (Fin 2 → K) M).comp f
  let phiPos : U →ₗ[K] K :=
    (LinearMap.proj (R := K) (φ := fun _ : Fin 2 ↦ K) 0 + LinearMap.proj 1).comp f₁
  let phiNeg : U →ₗ[K] K :=
    (LinearMap.proj (R := K) (φ := fun _ : Fin 2 ↦ K) 0 - LinearMap.proj 1).comp f₁
  have hQ_eq (u : U) : phiPos u * phiNeg u + Q (f₂ u) = 0 := by
    have h0 := hfQ u
    simp only [QuadraticMap.prod_apply, zero_apply, hyperbolicPlane_apply] at h0
    dsimp only [phiPos, phiNeg, f₁, f₂, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    rw [← h0]
    ring
  have hker_disj :
      LinearMap.ker phiPos ⊓ LinearMap.ker f₂ = ⊥ ∨
        LinearMap.ker phiNeg ⊓ LinearMap.ker f₂ = ⊥ := by
    by_contra hnot
    push Not at hnot
    obtain ⟨u, ⟨huPos, hu2⟩, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnot.1
    obtain ⟨v, ⟨hvNeg, hv2⟩, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnot.2
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at huPos hu2 hvNeg hv2
    have huPos' : f₁ u 0 + f₁ u 1 = 0 := huPos
    have hvNeg' : f₁ v 0 - f₁ v 1 = 0 := hvNeg
    have hf₁u : f₁ u 0 ≠ 0 := by
      intro h0
      have h1 : f₁ u 1 = 0 := by linear_combination huPos' - h0
      have hfu : f u = 0 := Prod.ext (funext fun i ↦ by fin_cases i <;> assumption) hu2
      exact hu0 (hf (hfu.trans (map_zero f).symm))
    have hf₁v : f₁ v 0 ≠ 0 := by
      intro h0
      have h1 : f₁ v 1 = 0 := by linear_combination -hvNeg' + h0
      have hfv : f v = 0 := Prod.ext (funext fun i ↦ by fin_cases i <;> assumption) hv2
      exact hv0 (hf (hfv.trans (map_zero f).symm))
    have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
    have hmul : phiPos (u + v) * phiNeg (u + v) = 0 := by
      have h0 := hQ_eq (u + v)
      have hf₂uv : f₂ (u + v) = 0 := by rw [map_add, hu2, hv2, add_zero]
      rwa [hf₂uv, Q.map_zero, add_zero] at h0
    have hadd : phiPos (u + v) = 2 * f₁ v 0 := by
      rw [map_add, huPos, zero_add]
      change f₁ v 0 + f₁ v 1 = 2 * f₁ v 0
      linear_combination -hvNeg'
    have hsub : phiNeg (u + v) = 2 * f₁ u 0 := by
      rw [map_add, hvNeg, add_zero]
      change f₁ u 0 - f₁ u 1 = 2 * f₁ u 0
      linear_combination -huPos'
    rw [hadd, hsub] at hmul
    exact mul_ne_zero (mul_ne_zero h2 hf₁v) (mul_ne_zero h2 hf₁u) hmul
  have of_ker :
      ∀ φ : U →ₗ[K] K, LinearMap.ker φ ⊓ LinearMap.ker f₂ = ⊥ →
        (∀ u ∈ LinearMap.ker φ, Q (f₂ u) = 0) →
        (0 : QuadraticForm K U').IsRepresentedBy Q := by
    intro φ hdisj hvanish
    have hker_dim : finrank K U' ≤ finrank K (LinearMap.ker φ) := by
      have hsum := LinearMap.finrank_range_add_finrank_ker φ
      have hrange : finrank K (LinearMap.range φ) ≤ 1 := by
        simpa using Submodule.finrank_le (LinearMap.range φ)
      omega
    have hker_Q : (0 : QuadraticForm K (LinearMap.ker φ)).IsRepresentedBy Q :=
      (isRepresentedBy_iff _ _).mpr
        ⟨f₂.comp (LinearMap.ker φ).subtype,
          fun x y hxy ↦ by
            apply Subtype.ext
            rw [← sub_eq_zero]
            have hmem : (x : U) - y ∈ LinearMap.ker φ ⊓ LinearMap.ker f₂ :=
              ⟨Submodule.sub_mem _ x.2 y.2, by
                simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
                exact hxy⟩
            rwa [hdisj, Submodule.mem_bot] at hmem,
          fun x ↦ hvanish x.1 x.2⟩
    exact (zero_isRepresentedBy_zero_of_finrank_le hker_dim).trans hker_Q
  rcases hker_disj with h | h
  · exact of_ker phiPos h fun u hu ↦ by
      have h0 := hQ_eq u
      rw [LinearMap.mem_ker.mp hu, zero_mul, zero_add] at h0
      exact h0
  · exact of_ker phiNeg h fun u hu ↦ by
      have h0 := hQ_eq u
      rw [LinearMap.mem_ker.mp hu, mul_zero, zero_add] at h0
      exact h0

/-- After scalar extension to a field `A`, cancelling a hyperbolic plane from an embedding of a
zero form into `H ⊥ Q` reduces the dimension of the represented zero space by at least one. Neither
nondegeneracy nor finiteness is needed on `Q`. -/
theorem zero_baseChange_isRepresentedBy_of_hyperbolicPlane_prod
    {A : Type*} [Field A] [Algebra K A]
    {U' U M : Type*} [AddCommGroup U'] [Module K U'] [FiniteDimensional K U']
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup M] [Module K M]
    {Q : QuadraticForm K M}
    (h : ((0 : QuadraticForm K U).baseChange A).IsRepresentedBy
      (QuadraticForm.baseChange A ((hyperbolicPlane K).prod Q)))
    (hk : finrank K U' + 1 ≤ finrank K U) :
    ((0 : QuadraticForm K U').baseChange A).IsRepresentedBy (Q.baseChange A) := by
  let _ : Invertible (2 : A) :=
    (Invertible.map (algebraMap K A) 2).copy 2 (map_ofNat _ _).symm
  have hH : (QuadraticForm.baseChange A ((hyperbolicPlane K).prod Q)).Equivalent
      ((hyperbolicPlane A).prod (Q.baseChange A)) :=
    Equivalent.trans ⟨QuadraticForm.baseChangeProd (A := A) (hyperbolicPlane K) Q⟩
      (baseChange_hyperbolicPlane_equivalent.prod (.refl _))
  have h' : ((0 : QuadraticForm K U).baseChange A).IsRepresentedBy
      ((hyperbolicPlane A).prod (Q.baseChange A)) :=
    h.trans hH.isRepresentedBy
  simp only [QuadraticForm.baseChange_zero] at h' ⊢
  exact zero_isRepresentedBy_of_hyperbolicPlane_prod h'
    (by simpa [Module.finrank_baseChange] using hk)

end HyperbolicCancellation

end TauCeti
