/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy

/-!
# Unique continuation and isolated point preimages of J-holomorphic curves

Let `E` be a finite-dimensional real normed space, `J : E → E →L[ℝ] E` a field of
endomorphisms, and `u : ℂ → E` a map of class `C¹` on an open set `Ω ⊆ ℂ` solving the
Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` on `Ω` in the coordinate `z = s + i t`. This file
shows that the preimages of points under `u` behave like the zeros of a holomorphic function
(McDuff–Salamon, Lemma 2.4.1, the part about point preimages). For the preimage of a point `x₀`
only the identity `J(x₀)² = -1` at that point and a Lipschitz bound for `J` near that point are
used (for instance, `J` of class `C¹` near `x₀`), and the theorems assume nothing more about `J`:

* **unique continuation**: if `Ω` is connected and `u` equals `x₀` near one point of `Ω`, or agrees
  with `x₀` to infinite order there, then `u ≡ x₀` on `Ω`
  (`TauCeti.eqOn_const_of_cauchyRiemann_of_eventually_eq`,
  `TauCeti.eqOn_const_of_cauchyRiemann_of_forall_isBigO`);
* **isolated preimages**: otherwise the preimage `u⁻¹(x₀)` is a discrete subset of `Ω`
  (`TauCeti.setOf_ne_mem_codiscreteWithin_of_cauchyRiemann`), so it meets every compact subset of
  `Ω` in finitely many points (`TauCeti.finite_inter_preimage_singleton_of_cauchyRiemann`);
* **local multiplicity**: each point `z₀` of `u⁻¹(x₀)` has a finite positive order `m`, with
  `‖u z - x₀‖ ≍ ‖z - z₀‖ ^ m` near `z₀`
  (`TauCeti.exists_isTheta_pow_of_cauchyRiemann`).

The proof freezes the complex structure at the value `x₀ = u z₀`. Since `J(x₀)² = -1`, a real-linear
isomorphism `Ψ : ℂⁿ → E` turns `J(x₀)` into multiplication by `i`
(`ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`), and
`η = Ψ⁻¹ (u - x₀)` satisfies

`∂ₛη + i ∂ₜη = Ψ⁻¹ (J(x₀) (J(u) - J(x₀)) ∂ₛu)`.

As `J` is Lipschitz near `x₀`, the right-hand side is bounded by a multiple of `‖∂ₛu‖ ‖η‖`, so
it equals `-C η` for a rank-one coefficient `C` which is measurable and locally bounded.
Carleman's similarity principle for the constant structure `i`, in its form for this differential
inequality (`TauCeti.hasSimilarityFactorizationAt_of_norm_le`), then factors `η` near each of its
zeros, and the zero structure of such factorizations
(`TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`) gives the results above. No
variable-structure similarity principle is needed for point preimages: the term
`(J(u) - J(x₀)) ∂ₛu` vanishes to first order in `u - x₀`. The corresponding statement for the
critical points of `u`, where the differentiated equation has a genuinely varying structure, is
not proved here.

## Main results

* `TauCeti.eqOn_const_of_cauchyRiemann_of_eventually_eq`: a solution equal to `x₀` near one point
  of a connected domain equals `x₀` on the domain.
* `TauCeti.eqOn_const_of_cauchyRiemann_of_forall_isBigO`: a solution agreeing with `x₀` to
  infinite order at one point of a connected domain equals `x₀` on the domain.
* `TauCeti.setOf_ne_mem_codiscreteWithin_of_cauchyRiemann`: a solution not identically equal to
  `x₀` on a connected domain takes the value `x₀` on a discrete set.
* `TauCeti.finite_inter_preimage_singleton_of_cauchyRiemann`: such a solution takes the value `x₀`
  at finitely many points of each compact subset of the domain.
* `TauCeti.exists_isTheta_pow_of_cauchyRiemann`: at each such point it has a positive order of
  contact with `x₀`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Lemma 2.4.1 and its proof via the similarity principle, Theorem 2.3.5.
-/

public section

open Asymptotics Complex Filter MeasureTheory Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {J : E → E →L[ℝ] E} {u : ℂ → E} {Ω : Set ℂ} {x₀ : E} {z₀ : ℂ}

section Frozen

variable {n : ℕ} {Ψ : EuclideanSpace ℂ (Fin n) ≃L[ℝ] E}

omit [FiniteDimensional ℝ E] in
/-- **The frozen equation at one point.** If `D` satisfies `D i = J(y) D 1`, then in the frame
`Ψ` the operator `∂ₛ + i ∂ₜ` with the frozen structure `J(x₀)` sees only the difference
`J(y) - J(x₀)`: `Ψ⁻¹ D 1 + i Ψ⁻¹ D i = Ψ⁻¹ (J(x₀) (J(y) - J(x₀)) D 1)`. -/
private theorem symm_apply_one_add_I_smul_symm_apply_I
    (hΨ : J x₀ ∘L (Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E) =
      (Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E) ∘L (I • ContinuousLinearMap.id ℝ _))
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E) {y : E} {D : ℂ →L[ℝ] E}
    (hD : D I = J y (D 1)) :
    Ψ.symm (D 1) + I • Ψ.symm (D I) = Ψ.symm (J x₀ ((J y - J x₀) (D 1))) := by
  have hJ₀' : J x₀ (J x₀ (D 1)) = -D 1 := congr($hJ₀ (D 1))
  rw [hD, ← Ψ.symm_apply_eq_I_smul_symm_of_comp_eq hΨ, sub_apply, map_sub, map_sub, hJ₀', map_neg]
  abel

omit [FiniteDimensional ℝ E] in
/-- **The size of the frozen error term.** If `‖J(y) - J(x₀)‖ ≤ K ‖y - x₀‖`, the error term of
the frozen equation is bounded by a multiple of `‖v‖ ‖Ψ⁻¹ (y - x₀)‖`. -/
private theorem norm_symm_apply_le {K : ℝ≥0} {y : E} (hy : ‖J y - J x₀‖ ≤ K * ‖y - x₀‖)
    (v : E) :
    ‖Ψ.symm (J x₀ ((J y - J x₀) v))‖ ≤
      ‖(Ψ.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n))‖ * ‖J x₀‖ * K *
        ‖(Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E)‖ * ‖v‖ * ‖Ψ.symm (y - x₀)‖ := by
  have hyx : ‖y - x₀‖ ≤ ‖(Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E)‖ * ‖Ψ.symm (y - x₀)‖ := by
    simpa using (Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E).le_opNorm (Ψ.symm (y - x₀))
  calc ‖Ψ.symm (J x₀ ((J y - J x₀) v))‖
      ≤ ‖(Ψ.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n))‖ * (‖J x₀‖ * (‖J y - J x₀‖ * ‖v‖)) := by
        refine ((Ψ.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n)).le_opNorm _).trans ?_
        gcongr
        exact ((J x₀).le_opNorm _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
    _ ≤ ‖(Ψ.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n))‖ * (‖J x₀‖ *
          (K * (‖(Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E)‖ * ‖Ψ.symm (y - x₀)‖) * ‖v‖)) := by
        gcongr
        exact hy.trans (by gcongr)
    _ = _ := by ring

end Frozen

omit [FiniteDimensional ℝ E] in
/-- **Localization near a point preimage.** If `J` is Lipschitz near `x₀ = u z₀`, then on some
disc about `z₀` inside `Ω` the difference `J(u) - J(x₀)` is bounded by a multiple of
`u - x₀`. -/
private theorem exists_ball_norm_sub_le (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω) (hz₀ : z₀ ∈ Ω) (hu₀ : u z₀ = x₀) :
    ∃ K : ℝ≥0, ∃ r > 0, ball z₀ r ⊆ Ω ∧
      ∀ z ∈ ball z₀ r, ‖J (u z) - J x₀‖ ≤ K * ‖u z - x₀‖ := by
  obtain ⟨K, t, ht, hK⟩ := hJ
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.1 (inter_mem (hΩ.mem_nhds hz₀)
    ((hu.continuousAt (hΩ.mem_nhds hz₀)).preimage_mem_nhds (hu₀ ▸ ht)))
  refine ⟨K, r, hr, fun z hz ↦ (hrB hz).1, fun z hz ↦ ?_⟩
  simpa only [dist_eq_norm] using
    lipschitzOnWith_iff_dist_le_mul.1 hK _ (hrB hz).2 _ (mem_of_mem_nhds ht)

omit [FiniteDimensional ℝ E] in
/-- **The frozen equation.** Let `Ψ : ℂⁿ → E` turn the structure `J(x₀)` at the value
`x₀ = u z₀` into multiplication by `i`. Then `η = Ψ⁻¹ (u - x₀)` solves a linear Cauchy–Riemann
equation `∂ₛη + i ∂ₜη + C η = 0` near `z₀` for a measurable, locally bounded coefficient `C`, so it
has a similarity factorization at `z₀`. -/
private theorem hasSimilarityFactorizationAt_symm_sub {n : ℕ}
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t) (Ψ : EuclideanSpace ℂ (Fin n) ≃L[ℝ] E)
    (hΨ : J x₀ ∘L (Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E) =
      (Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E) ∘L (I • ContinuousLinearMap.id ℝ _))
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E) (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u Ω) (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hz₀ : z₀ ∈ Ω) (hu₀ : u z₀ = x₀) :
    HasSimilarityFactorizationAt (fun z ↦ Ψ.symm (u z - x₀)) z₀ := by
  obtain ⟨K, r, hr, hBΩ, hJd⟩ := exists_ball_norm_sub_le hJ hΩ hu.continuousOn hz₀ hu₀
  have hDu : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  -- The error term of the frozen equation is bounded by `M ‖η‖`, with `M` a multiple of `‖∂ₛu‖`.
  refine hasSimilarityFactorizationAt_of_norm_le (η := fun z ↦ Ψ.symm (u z - x₀)) (M := fun w ↦
      ‖(Ψ.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n))‖ * ‖J x₀‖ * K *
        ‖(Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E)‖ * ‖fderiv ℝ u w 1‖) isOpen_ball
    ((Ψ.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n)).contDiff.comp_contDiffOn
      ((hu.sub contDiffOn_const).mono hBΩ)) (fun z hz ↦ ?_) (fun z hz ↦ ?_) (mem_ball_self hr)
  · -- `M` is continuous, hence locally bounded.
    have hz' : ContinuousAt (fun w ↦ ‖(Ψ.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n))‖ * ‖J x₀‖ *
        K * ‖(Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] E)‖ * ‖fderiv ℝ u w 1‖) z :=
      continuousAt_const.mul (((hDu.clm_apply continuousOn_const).continuousAt
        (hΩ.mem_nhds (hBΩ hz))).norm)
    exact ⟨_, (hz'.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h ↦ h.le⟩
  · have hDη : fderiv ℝ (fun z ↦ Ψ.symm (u z - x₀)) z =
        (Ψ.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n)) ∘L fderiv ℝ u z :=
      ((Ψ.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n)).hasFDerivAt.comp z
        (((hu.differentiableOn one_ne_zero z (hBΩ hz)).differentiableAt
          (hΩ.mem_nhds (hBΩ hz))).hasFDerivAt.sub_const x₀)).fderiv
    rw [hDη, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, symm_apply_one_add_I_smul_symm_apply_I hΨ hJ₀
      (hCR z (hBΩ hz))]
    exact norm_symm_apply_le (hJd z hz) _

/-- A frame `Ψ` turning `J(x₀)` into `i` makes `η = Ψ⁻¹ (u - x₀)` continuous on `Ω`, with a
similarity factorization at each of its zeros in `Ω`. -/
private theorem exists_hasSimilarityFactorizationAt
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E) (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) :
    ∃ (n : ℕ) (Ψ : EuclideanSpace ℂ (Fin n) ≃L[ℝ] E),
      ContinuousOn (fun z ↦ Ψ.symm (u z - x₀)) Ω ∧
      ∀ z ∈ Ω, Ψ.symm (u z - x₀) = 0 →
        HasSimilarityFactorizationAt (fun z ↦ Ψ.symm (u z - x₀)) z := by
  obtain ⟨n, Ψ, hΨ⟩ :=
    ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul _ hJ₀
  refine ⟨n, Ψ, Ψ.symm.continuous.comp_continuousOn (hu.continuousOn.sub continuousOn_const),
    fun z hz h0 ↦ hasSimilarityFactorizationAt_symm_sub hJ Ψ hΨ hJ₀ hΩ hu hCR hz ?_⟩
  simpa [sub_eq_zero] using h0

omit [FiniteDimensional ℝ E] in
/-- `Ψ⁻¹ (y - x₀)` vanishes exactly when `y = x₀`. -/
private theorem symm_sub_eq_zero_iff {n : ℕ} (Ψ : EuclideanSpace ℂ (Fin n) ≃L[ℝ] E) (y : E) :
    Ψ.symm (y - x₀) = 0 ↔ y = x₀ := by
  simp [sub_eq_zero]

/-- **Unique continuation for J-holomorphic curves.** A `C¹` solution of the Cauchy–Riemann
equation `∂ₜu = J(u) ∂ₛu` on a connected open set `Ω`, for a field `J` Lipschitz near `x₀` with
`J(x₀)² = -1`, that equals `x₀` near one point of `Ω` equals `x₀` on `Ω`. -/
theorem eqOn_const_of_cauchyRiemann_of_eventually_eq
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ᶠ z in 𝓝 z₀, u z = x₀) : EqOn u (fun _ ↦ x₀) Ω := by
  obtain ⟨n, Ψ, hc, hfac⟩ := exists_hasSimilarityFactorizationAt hJ hJ₀ hΩ hu hCR
  intro z hz
  exact (symm_sub_eq_zero_iff Ψ _).1
    (eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc hc hfac hz₀
      (h₀.mono fun w hw ↦ (symm_sub_eq_zero_iff Ψ _).2 hw) hz)

/-- **Unique continuation from infinite-order contact.** A `C¹` solution of the Cauchy–Riemann
equation `∂ₜu = J(u) ∂ₛu` on a connected open set `Ω`, for a field `J` Lipschitz near `x₀` with
`J(x₀)² = -1`, with `u z - x₀ = O(‖z - z₀‖ⁿ)` at a point `z₀ ∈ Ω` for every `n`, is constant
equal to `x₀` on `Ω`. -/
theorem eqOn_const_of_cauchyRiemann_of_forall_isBigO
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, (fun z ↦ u z - x₀) =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn u (fun _ ↦ x₀) Ω := by
  obtain ⟨n, Ψ, hc, hfac⟩ := exists_hasSimilarityFactorizationAt hJ hJ₀ hΩ hu hCR
  intro z hz
  exact (symm_sub_eq_zero_iff Ψ _).1 (eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO
    hΩ hΩc hc hfac hz₀ (fun k ↦ (Ψ.symm.isBigO_comp _ _).trans (h₀ k)) hz)

/-- **Isolated point preimages of J-holomorphic curves.** A `C¹` solution of the Cauchy–Riemann
equation `∂ₜu = J(u) ∂ₛu` on a connected open set `Ω`, for a field `J` Lipschitz near `x₀` with
`J(x₀)² = -1`, that is not identically equal to `x₀` on `Ω` takes the value `x₀` on a discrete
subset of `Ω`. -/
theorem setOf_ne_mem_codiscreteWithin_of_cauchyRiemann
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (hne : ∃ z ∈ Ω, u z ≠ x₀) :
    {z | u z ≠ x₀} ∈ codiscreteWithin Ω := by
  obtain ⟨n, Ψ, hc, hfac⟩ := exists_hasSimilarityFactorizationAt hJ hJ₀ hΩ hu hCR
  have hset : {z | u z ≠ x₀} = {z | Ψ.symm (u z - x₀) ≠ 0} := by
    ext z
    simp only [mem_ofPred_eq, ne_eq, symm_sub_eq_zero_iff Ψ]
  obtain ⟨z, hz, hzne⟩ := hne
  rw [hset]
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc hc hfac
    ⟨z, hz, mt (symm_sub_eq_zero_iff Ψ _).1 hzne⟩

/-- **Finite point preimages on compact sets.** A `C¹` solution of the Cauchy–Riemann equation
`∂ₜu = J(u) ∂ₛu` on a connected open set `Ω`, for a field `J` Lipschitz near `x₀` with
`J(x₀)² = -1`, that is not identically equal to `x₀` on `Ω` takes the value `x₀` at finitely many
points of each compact subset of `Ω`. -/
theorem finite_inter_preimage_singleton_of_cauchyRiemann
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (hne : ∃ z ∈ Ω, u z ≠ x₀)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) : (K ∩ u ⁻¹' {x₀}).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin (codiscreteWithin_mono hKΩ
    (setOf_ne_mem_codiscreteWithin_of_cauchyRiemann hJ hJ₀ hΩ hΩc hu hCR hne))
  convert h using 1
  ext z
  simp

/-- **The order of a point preimage.** For a `C¹` solution of the Cauchy–Riemann equation
`∂ₜu = J(u) ∂ₛu` on a connected open set `Ω`, for a field `J` Lipschitz near `x₀` with
`J(x₀)² = -1`, that is not identically equal to `x₀` on `Ω`, each point `z₀ ∈ Ω` with `u z₀ = x₀`
has a positive order `m`: `‖u z - x₀‖ ≍ ‖z - z₀‖ ^ m` near `z₀`. -/
theorem exists_isTheta_pow_of_cauchyRiemann
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (hne : ∃ z ∈ Ω, u z ≠ x₀)
    (hz₀ : z₀ ∈ Ω) (hu₀ : u z₀ = x₀) :
    ∃ m : ℕ, 0 < m ∧ (fun z ↦ u z - x₀) =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m := by
  obtain ⟨n, Ψ, hc, hfac⟩ := exists_hasSimilarityFactorizationAt hJ hJ₀ hΩ hu hCR
  obtain ⟨z, hz, hzne⟩ := hne
  obtain ⟨m, hm, hθ, -⟩ := exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt hΩ hΩc hc
    hfac ⟨z, hz, mt (symm_sub_eq_zero_iff Ψ _).1 hzne⟩ hz₀ ((symm_sub_eq_zero_iff Ψ _).2 hu₀)
  exact ⟨m, hm, IsTheta.trans ⟨Ψ.symm.isBigO_comp_rev _ _, Ψ.symm.isBigO_comp _ _⟩ hθ⟩

end TauCeti
