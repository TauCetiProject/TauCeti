/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
public import TauCeti.LinearAlgebra.TotallyReal.Basic
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.RealBoundary.DifferentialInequality
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

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

**Totally real boundary values.** The same statements hold up to the boundary for a half-disc
with totally real boundary values: `u` of class `C¹` up to the real axis on the closed upper part
`Ω ∩ {0 ≤ im}` of an open set, solving `∂ₜu = J(u) ∂ₛu` off the axis, with
`u x ∈ x₀ + L` on `Ω ∩ ℝ` for a subspace `L` that is maximal totally real for `J(x₀)`. This is the
local model of a pseudoholomorphic strip or disc with boundary on a totally real submanifold, in
coordinates flattening the submanifold near `x₀`. Here the frame `Ψ` is chosen to carry also `ℝⁿ`
onto `L`
(`TauCeti.IsMaximalTotallyReal.exists_continuousLinearEquiv_pi_comp_eq_comp_I_smul_and_mem_iff`),
so that `η = Ψ⁻¹ (u - x₀)` is real on the axis, and the frozen equation becomes the differential
inequality `‖bar∂η‖ ≤ g ‖η‖` with `g` locally bounded up to the axis. The boundary similarity
principle in that form
(`TauCeti.Analysis.Complex.CauchyRiemann.RealBoundary.DifferentialInequality`), proved by
reflection across the axis, gives unique continuation, isolated preimages and positive orders up
to the boundary, also at the points `z₀` of the axis where `u z₀ = x₀`. The reflection needs a
conjugation-invariant domain, so `Ω` is first replaced by `{z | re z + i |im z| ∈ Ω}`, which has
the same closed upper part.

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
* `TauCeti.eqOn_const_of_cauchyRiemann_of_isMaximalTotallyReal_of_eqOn` and
  `TauCeti.eqOn_const_of_cauchyRiemann_of_isMaximalTotallyReal_of_forall_isBigO`: unique
  continuation up to a totally real boundary.
* `TauCeti.setOf_ne_mem_codiscreteWithin_of_cauchyRiemann_of_isMaximalTotallyReal` and
  `TauCeti.finite_inter_preimage_singleton_of_cauchyRiemann_of_isMaximalTotallyReal`: isolated, and
  locally finitely many, preimages up to a totally real boundary.
* `TauCeti.exists_isTheta_pow_of_cauchyRiemann_of_isMaximalTotallyReal`: positive orders of
  contact up to a totally real boundary.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Lemma 2.4.1 and its proof via the similarity principle, Theorem 2.3.5, and Section 2.3 for its
  boundary version with totally real boundary conditions.
-/

public section

open Asymptotics Complex Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {J : E → E →L[ℝ] E} {u : ℂ → E} {Ω : Set ℂ} {x₀ : E} {z₀ : ℂ}

section Frozen

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {Ψ : V ≃L[ℝ] E}

omit [FiniteDimensional ℝ E] in
/-- **The frozen equation at one point.** If `D` satisfies `D i = J(y) D 1`, then in the frame
`Ψ` the operator `∂ₛ + i ∂ₜ` with the frozen structure `J(x₀)` sees only the difference
`J(y) - J(x₀)`: `Ψ⁻¹ D 1 + i Ψ⁻¹ D i = Ψ⁻¹ (J(x₀) (J(y) - J(x₀)) D 1)`. -/
private theorem symm_apply_one_add_I_smul_symm_apply_I
    (hΨ : J x₀ ∘L (Ψ : V →L[ℝ] E) =
      (Ψ : V →L[ℝ] E) ∘L (I • ContinuousLinearMap.id ℝ V))
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
      ‖(Ψ.symm : E →L[ℝ] V)‖ * ‖J x₀‖ * K *
        ‖(Ψ : V →L[ℝ] E)‖ * ‖v‖ * ‖Ψ.symm (y - x₀)‖ := by
  have hyx : ‖y - x₀‖ ≤ ‖(Ψ : V →L[ℝ] E)‖ * ‖Ψ.symm (y - x₀)‖ := by
    simpa using (Ψ : V →L[ℝ] E).le_opNorm (Ψ.symm (y - x₀))
  calc ‖Ψ.symm (J x₀ ((J y - J x₀) v))‖
      ≤ ‖(Ψ.symm : E →L[ℝ] V)‖ * (‖J x₀‖ * (‖J y - J x₀‖ * ‖v‖)) := by
        refine ((Ψ.symm : E →L[ℝ] V).le_opNorm _).trans ?_
        gcongr
        exact ((J x₀).le_opNorm _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
    _ ≤ ‖(Ψ.symm : E →L[ℝ] V)‖ * (‖J x₀‖ *
          (K * (‖(Ψ : V →L[ℝ] E)‖ * ‖Ψ.symm (y - x₀)‖) * ‖v‖)) := by
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
private theorem symm_sub_eq_zero_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Ψ : V ≃L[ℝ] E) (y : E) :
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
  exact exists_isTheta_pow_of_continuousLinearEquiv_of_hasSimilarityFactorizationAt Ψ.symm hΩ hΩc
    hc hfac (hne.imp fun _ ↦ .imp_right sub_ne_zero.2) hz₀ (sub_eq_zero.2 hu₀)

/-! ### Totally real boundary values -/

section TotallyRealBoundary

variable {L : Submodule ℝ E}

omit [FiniteDimensional ℝ E] in
/-- Off the real axis, the conjugate Wirtinger derivative of `η = Ψ⁻¹ (u - x₀)` is
`½ (Ψ⁻¹ ∂ₛu + i Ψ⁻¹ ∂ₜu)`. -/
private theorem conjWirtingerDeriv_symm_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Ψ : V ≃L[ℝ] E) {z : ℂ} (hu : DifferentiableAt ℝ u z) :
    conjWirtingerDeriv (fun w ↦ Ψ.symm (u w - x₀)) z 1 =
      (2 : ℂ)⁻¹ • (Ψ.symm (fderiv ℝ u z 1) + I • Ψ.symm (fderiv ℝ u z I)) := by
  have hD : fderiv ℝ (fun w ↦ Ψ.symm (u w - x₀)) z = (Ψ.symm : E →L[ℝ] V) ∘L fderiv ℝ u z :=
    ((Ψ.symm : E →L[ℝ] V).hasFDerivAt.comp z (hu.hasFDerivAt.sub_const x₀)).fderiv
  rw [conjWirtingerDeriv_apply, hD]
  simp

omit [FiniteDimensional ℝ E] in
/-- Off the real axis, the conjugate Wirtinger derivative of `η = Ψ⁻¹ (u - x₀)` is bounded by
`‖Ψ⁻¹‖ ‖du‖`. -/
private theorem norm_conjWirtingerDeriv_symm_sub_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (Ψ : V ≃L[ℝ] E) {z : ℂ} (hu : DifferentiableAt ℝ u z) :
    ‖conjWirtingerDeriv (fun w ↦ Ψ.symm (u w - x₀)) z 1‖ ≤
      ‖(Ψ.symm : E →L[ℝ] V)‖ * ‖fderiv ℝ u z‖ := by
  have hv (v : ℂ) (hv : ‖v‖ = 1) :
      ‖Ψ.symm (fderiv ℝ u z v)‖ ≤ ‖(Ψ.symm : E →L[ℝ] V)‖ * ‖fderiv ℝ u z‖ :=
    ((Ψ.symm : E →L[ℝ] V).le_opNorm _).trans
      (by gcongr; simpa [hv] using (fderiv ℝ u z).le_opNorm v)
  rw [conjWirtingerDeriv_symm_sub Ψ hu, norm_smul, norm_inv, Complex.norm_two]
  calc (2 : ℝ)⁻¹ * ‖Ψ.symm (fderiv ℝ u z 1) + I • Ψ.symm (fderiv ℝ u z I)‖
      ≤ (2 : ℝ)⁻¹ * (‖Ψ.symm (fderiv ℝ u z 1)‖ + ‖Ψ.symm (fderiv ℝ u z I)‖) := by
        gcongr
        exact (norm_add_le _ _).trans (by rw [norm_smul, Complex.norm_I, one_mul])
    _ ≤ _ := by linarith [hv 1 norm_one, hv I Complex.norm_I]

omit [FiniteDimensional ℝ E] in
/-- A map `C¹` up to the real axis on `Ω ∩ {0 ≤ im}` is differentiable off the axis. -/
private theorem differentiableAt_of_mem_inter_setOf_lt_im (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u (Ω ∩ {z | 0 ≤ z.im})) {z : ℂ} (hz : z ∈ Ω ∩ {z | 0 < z.im}) :
    DifferentiableAt ℝ u z :=
  (hu.contDiffAt (mem_interior_iff_mem_nhds.1 ((interior_inter_setOf_im_nonneg hΩ).ge hz))
    ).differentiableAt_one

omit [FiniteDimensional ℝ E] in
/-- **Local bounds for the frozen coefficient.** Let `η = Ψ⁻¹ (u - x₀)` for a frame `Ψ` turning
`J(x₀)` into `i`, and `G` its conjugate Wirtinger derivative. Near each point of
`Ω ∩ {0 ≤ im}` the quotient `‖G‖ / ‖η‖` is bounded off the real axis: near a zero of `η` because
`J` is Lipschitz near `x₀`, elsewhere because `η` stays away from zero. -/
private theorem exists_eventually_norm_conjWirtingerDeriv_div_le {n : ℕ}
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t) (Ψ : (Fin n → ℂ) ≃L[ℝ] E)
    (hΨ : J x₀ ∘L (Ψ : (Fin n → ℂ) →L[ℝ] E) =
      (Ψ : (Fin n → ℂ) →L[ℝ] E) ∘L (I • ContinuousLinearMap.id ℝ (Fin n → ℂ)))
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E) (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) {z₁ : ℂ}
    (hz₁ : z₁ ∈ Ω ∩ {z | 0 ≤ z.im}) :
    ∃ M, 0 ≤ M ∧ ∀ᶠ w in 𝓝[Ω ∩ {z | 0 ≤ z.im}] z₁, w ∈ Ω ∩ {z | 0 < z.im} →
      ‖conjWirtingerDeriv (fun w ↦ Ψ.symm (u w - x₀)) w 1‖ / ‖Ψ.symm (u w - x₀)‖ ≤ M := by
  obtain ⟨B, hB0, hB⟩ := hu.exists_eventually_norm_fderiv_le
    (by rw [inter_comm]; exact (uniqueDiffOn_setOfPred_le_im 0).inter hΩ) le_rfl hz₁
  by_cases h₀ : u z₁ = x₀
  · -- near a zero of `η`: the frozen error term is a multiple of `‖∂ₛu‖ ‖η‖`
    obtain ⟨K, t, ht, hK⟩ := hJ
    have hut : ∀ᶠ w in 𝓝[Ω ∩ {z | 0 ≤ z.im}] z₁, u w ∈ t :=
      hu.continuousOn.continuousWithinAt hz₁ (h₀ ▸ ht)
    refine ⟨(2 : ℝ)⁻¹ * (‖(Ψ.symm : E →L[ℝ] (Fin n → ℂ))‖ * ‖J x₀‖ * K *
      ‖(Ψ : (Fin n → ℂ) →L[ℝ] E)‖ * B), by positivity, ?_⟩
    filter_upwards [hB, hut] with w hwB hwt hw
    obtain ⟨hwd, hwB⟩ := hwB ((interior_inter_setOf_im_nonneg hΩ).ge hw)
    have hJw : ‖J (u w) - J x₀‖ ≤ K * ‖u w - x₀‖ := by
      simpa only [dist_eq_norm] using
        lipschitzOnWith_iff_dist_le_mul.1 hK _ hwt _ (mem_of_mem_nhds ht)
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    rw [conjWirtingerDeriv_symm_sub Ψ hwd,
      symm_apply_one_add_I_smul_symm_apply_I hΨ hJ₀ (hCR w hw.1 hw.2), norm_smul, norm_inv,
      Complex.norm_two]
    calc (2 : ℝ)⁻¹ * ‖Ψ.symm (J x₀ ((J (u w) - J x₀) (fderiv ℝ u w 1)))‖
        ≤ (2 : ℝ)⁻¹ * (‖(Ψ.symm : E →L[ℝ] (Fin n → ℂ))‖ * ‖J x₀‖ * K *
          ‖(Ψ : (Fin n → ℂ) →L[ℝ] E)‖ * ‖fderiv ℝ u w 1‖ * ‖Ψ.symm (u w - x₀)‖) := by
          gcongr
          exact norm_symm_apply_le hJw _
      _ ≤ (2 : ℝ)⁻¹ * (‖(Ψ.symm : E →L[ℝ] (Fin n → ℂ))‖ * ‖J x₀‖ * K *
          ‖(Ψ : (Fin n → ℂ) →L[ℝ] E)‖ * B * ‖Ψ.symm (u w - x₀)‖) := by
          gcongr
          exact ((fderiv ℝ u w).le_opNorm 1).trans (by simpa using hwB)
      _ = _ := by ring
  · -- away from the zeros of `η`: `‖η‖` stays above half its value at `z₁`
    have hη₁ : 0 < ‖Ψ.symm (u z₁ - x₀)‖ := norm_pos_iff.2 (by simpa [sub_eq_zero] using h₀)
    have hη : ∀ᶠ w in 𝓝[Ω ∩ {z | 0 ≤ z.im}] z₁,
        ‖Ψ.symm (u z₁ - x₀)‖ / 2 < ‖Ψ.symm (u w - x₀)‖ :=
      ((Ψ.symm.continuous.comp_continuousOn (hu.continuousOn.sub continuousOn_const)).norm
        z₁ hz₁).eventually (lt_mem_nhds (half_lt_self hη₁))
    refine ⟨‖(Ψ.symm : E →L[ℝ] (Fin n → ℂ))‖ * B / (‖Ψ.symm (u z₁ - x₀)‖ / 2), by positivity,
      ?_⟩
    filter_upwards [hB, hη] with w hwB hwη hw
    obtain ⟨hwd, hwB⟩ := hwB ((interior_inter_setOf_im_nonneg hΩ).ge hw)
    exact div_le_div₀ (by positivity)
      ((norm_conjWirtingerDeriv_symm_sub_le Ψ hwd).trans (by gcongr)) (by positivity) hwη.le

/-- **The frozen equation up to a totally real boundary.** Let `u` be `C¹` up to the real axis on
`Ω ∩ {0 ≤ im}`, solving `∂ₜu = J(u) ∂ₛu` off the axis, with boundary values in `x₀ + L` for a
subspace `L` that is maximal totally real for `J(x₀)`. In a frame `Ψ : ℂⁿ → E` turning `J(x₀)`
into `i` and `ℝⁿ` into `L`, the map `η = Ψ⁻¹ (u - x₀)` is continuous up to the axis, real on it,
and its conjugate Wirtinger derivative `G` satisfies `‖G‖ ≤ g ‖η‖` almost everywhere on
`Ω ∩ {0 ≤ im}` for a function `g` locally bounded up to the axis. -/
private theorem exists_frame_realBoundary (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E)
    (hL : IsMaximalTotallyReal (J x₀ : E →ₗ[ℝ] E) L) (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → u x - x₀ ∈ L) :
    ∃ (n : ℕ) (Ψ : (Fin n → ℂ) ≃L[ℝ] E) (g : ℂ → ℝ),
      ContinuousOn (fun z ↦ Ψ.symm (u z - x₀)) (Ω ∩ {z | 0 ≤ z.im}) ∧
      (∀ x : ℝ, (x : ℂ) ∈ Ω → star (Ψ.symm (u x - x₀)) = Ψ.symm (u x - x₀)) ∧
      MemLpLoc 3 (Ω ∩ {z | 0 ≤ z.im}) g ∧
      HasWeakConjWirtingerDerivRealBoundaryOn ⟨Ω, hΩ⟩ (fun z ↦ Ψ.symm (u z - x₀))
        (fun z ↦ conjWirtingerDeriv (fun w ↦ Ψ.symm (u w - x₀)) z 1) ∧
      ∀ᵐ z ∂volume.restrict (Ω ∩ {z | 0 ≤ z.im}),
        ‖conjWirtingerDeriv (fun w ↦ Ψ.symm (u w - x₀)) z 1‖ ≤ g z * ‖Ψ.symm (u z - x₀)‖ := by
  obtain ⟨n, Ψ, hΨ, hmem⟩ := hL.exists_continuousLinearEquiv_pi_comp_eq_comp_I_smul_and_mem_iff hJ₀
  set S := Ω ∩ {z | 0 ≤ z.im}
  set S' := Ω ∩ {z | 0 < z.im}
  set η : ℂ → Fin n → ℂ := fun z ↦ Ψ.symm (u z - x₀) with hη_def
  set G : ℂ → Fin n → ℂ := fun z ↦ conjWirtingerDeriv η z 1 with hG_def
  have hS' : IsOpen S' := hΩ.inter (isOpen_lt continuous_const continuous_im)
  have hS'S : S' ⊆ S := fun w hw ↦ ⟨hw.1, hw.2.out.le⟩
  have hSm : MeasurableSet S := hΩ.measurableSet.inter (measurableSet_le measurable_const
    Complex.measurable_im)
  have hηC : ContDiffOn ℝ 1 η S :=
    (Ψ.symm : E →L[ℝ] (Fin n → ℂ)).contDiff.comp_contDiffOn (hu.sub contDiffOn_const)
  have hreal (x : ℝ) (hx : (x : ℂ) ∈ Ω) : star (η x) = η x :=
    (hmem (η x)).1 (by simpa [hη_def] using hbd x hx)
  -- off the axis, `G` is continuous, and vanishes where `η` does
  have hGeq {z : ℂ} (hz : z ∈ S') : G z = (2 : ℂ)⁻¹ • Ψ.symm (J x₀ ((J (u z) - J x₀)
      (fderiv ℝ u z 1))) := by
    rw [hG_def, hη_def]
    beta_reduce
    rw [conjWirtingerDeriv_symm_sub Ψ (differentiableAt_of_mem_inter_setOf_lt_im hΩ hu hz),
      symm_apply_one_add_I_smul_symm_apply_I hΨ hJ₀ (hCR z hz.1 hz.2)]
  have hGc : ContinuousOn G S' := by
    have hDc := (hu.mono hS'S).continuousOn_fderiv_of_isOpen hS' le_rfl
    refine ContinuousOn.congr (f := fun z ↦ (2 : ℂ)⁻¹ • ((Ψ.symm : E →L[ℝ] (Fin n → ℂ))
      (fderiv ℝ u z 1) + I • (Ψ.symm : E →L[ℝ] (Fin n → ℂ)) (fderiv ℝ u z I)))
      (by fun_prop) fun z hz ↦ ?_
    rw [hG_def, hη_def]
    exact conjWirtingerDeriv_symm_sub Ψ (differentiableAt_of_mem_inter_setOf_lt_im hΩ hu hz)
  set g : ℂ → ℝ := S'.indicator fun z ↦ ‖G z‖ / ‖η z‖ with hg_def
  refine ⟨n, Ψ, g, hηC.continuousOn, hreal, memLpLoc_indicator_of_forall_eventually_norm_le
      hS'.measurableSet hS'S
      (((hGc.aestronglyMeasurable hS'.measurableSet).norm.aemeasurable.div ((hηC.continuousOn.mono
        hS'S).aestronglyMeasurable hS'.measurableSet).norm.aemeasurable).aestronglyMeasurable)
      fun z₁ hz₁ ↦ (exists_eventually_norm_conjWirtingerDeriv_div_le hJ Ψ hΨ hJ₀ hΩ hu hCR
        hz₁).imp fun _ hM ↦ hM.2.mono fun _ hw hwS' ↦
          (Real.norm_of_nonneg (by positivity)).trans_le (hw hwS'),
    hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn (Ω := ⟨Ω, hΩ⟩) hηC
      (fun _ _ _ ↦ rfl) hreal, ?_⟩
  · -- off the axis, a null set, `‖G‖ = (‖G‖ / ‖η‖) ‖η‖`, both sides vanishing where `η` does
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae Complex.ae_im_ne_zero] with z hz hz0
    have hzS' : z ∈ S' := ⟨hz.1, lt_of_le_of_ne hz.2 (Ne.symm hz0)⟩
    rw [hg_def, indicator_of_mem hzS']
    by_cases hη0 : η z = 0
    · have hu0 : u z = x₀ := by simpa [hη_def, sub_eq_zero] using hη0
      have hG0 : G z = 0 := by
        rw [hGeq hzS', hu0, sub_self]
        simp
      rw [hG0, norm_zero, zero_div, zero_mul]
      exact (norm_eq_zero.2 hG0).le
    · rw [div_mul_cancel₀ _ (norm_ne_zero_iff.2 hη0)]

omit [FiniteDimensional ℝ E] in
/-- **A conjugation-invariant domain with the same upper part.** The equation and the boundary
condition pass from `Ω` to the conjugation-invariant open set `Ω'` with the same closed upper part
given by `TauCeti.exists_isOpen_mapsTo_conj_inter_setOf_im_nonneg_eq`. -/
private theorem exists_mapsTo_conj_realBoundary (hΩ : IsOpen Ω)
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → u x - x₀ ∈ L) :
    ∃ Ω' : Set ℂ, IsOpen Ω' ∧ MapsTo (starRingEnd ℂ) Ω' Ω' ∧
      Ω' ∩ {z | 0 ≤ z.im} = Ω ∩ {z | 0 ≤ z.im} ∧
      (∀ z ∈ Ω', 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) ∧
      ∀ x : ℝ, (x : ℂ) ∈ Ω' → u x - x₀ ∈ L := by
  obtain ⟨Ω', hΩ', hΩs, heq⟩ := exists_isOpen_mapsTo_conj_inter_setOf_im_nonneg_eq hΩ
  have hsub {z : ℂ} (hz : z ∈ Ω') (h : 0 ≤ z.im) : z ∈ Ω :=
    (heq.subset (show z ∈ Ω' ∩ {z | 0 ≤ z.im} from ⟨hz, h⟩)).1
  exact ⟨Ω', hΩ', hΩs, heq, fun z hz h ↦ hCR z (hsub hz h.le) h,
    fun x hx ↦ hbd x (hsub hx (by simp))⟩

/-- **Unique continuation up to a totally real boundary.** Let `Ω` be an open set
with `Ω ∩ {0 ≤ im}` connected, and `u` a map of class `C¹` up to the real axis on
`Ω ∩ {0 ≤ im}` solving the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` off the axis, for a field `J`
Lipschitz near `x₀` with `J(x₀)² = -1`, with boundary values `u x ∈ x₀ + L` on `Ω ∩ ℝ` for a
subspace `L` maximal totally real for `J(x₀)`. If `u` equals `x₀` on a nonempty open subset of
`Ω ∩ {0 ≤ im}`, it equals `x₀` on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_const_of_cauchyRiemann_of_isMaximalTotallyReal_of_eqOn
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E)
    (hL : IsMaximalTotallyReal (J x₀ : E →ₗ[ℝ] E) L) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hu : ContDiffOn ℝ 1 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → u x - x₀ ∈ L) {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUΩ : U ⊆ Ω ∩ {z | 0 ≤ z.im}) (h₀ : EqOn u (fun _ ↦ x₀) U) :
    EqOn u (fun _ ↦ x₀) (Ω ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨Ω', hΩ', hΩs, heq, hCR', hbd'⟩ := exists_mapsTo_conj_realBoundary hΩ hCR hbd
  rw [← heq] at hΩc hu hUΩ ⊢
  obtain ⟨n, Ψ, g, hc, hr, hg, hw, hle⟩ := exists_frame_realBoundary hJ hJ₀ hL hΩ' hu hCR' hbd'
  intro z hz
  exact (symm_sub_eq_zero_iff Ψ _).1
    (eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le_of_eqOn_zero (Ω := ⟨Ω', hΩ'⟩)
      (by norm_num) hΩs hΩc hg hc hr hw hle hU hUne hUΩ
      (fun w hw ↦ (symm_sub_eq_zero_iff Ψ _).2 (h₀ hw)) hz)

/-- **Unique continuation from infinite-order contact, up to a totally real boundary.** Let `Ω`
be an open set with `Ω ∩ {0 ≤ im}` connected, and `u` a map of class `C¹` up
to the real axis on `Ω ∩ {0 ≤ im}` solving the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` off the
axis, for a field `J` Lipschitz near `x₀` with `J(x₀)² = -1`, with boundary values `u x ∈ x₀ + L`
on `Ω ∩ ℝ` for a subspace `L` maximal totally real for `J(x₀)`. If `u z - x₀ = O(‖z - z₀‖ⁿ)`
within `{0 ≤ im}` for every `n`, at a point `z₀ ∈ Ω ∩ {0 ≤ im}` possibly on the axis, then `u`
equals `x₀` on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_const_of_cauchyRiemann_of_isMaximalTotallyReal_of_forall_isBigO
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E)
    (hL : IsMaximalTotallyReal (J x₀ : E →ₗ[ℝ] E) L) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hu : ContDiffOn ℝ 1 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → u x - x₀ ∈ L) (hz₀ : z₀ ∈ Ω ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, (fun z ↦ u z - x₀) =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn u (fun _ ↦ x₀) (Ω ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨Ω', hΩ', hΩs, heq, hCR', hbd'⟩ := exists_mapsTo_conj_realBoundary hΩ hCR hbd
  rw [← heq] at hΩc hu hz₀ ⊢
  obtain ⟨n, Ψ, g, hc, hr, hg, hw, hle⟩ := exists_frame_realBoundary hJ hJ₀ hL hΩ' hu hCR' hbd'
  intro z hz
  exact (symm_sub_eq_zero_iff Ψ _).1
    (eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le_of_forall_isBigO
      (Ω := ⟨Ω', hΩ'⟩) (by norm_num) hΩs hΩc hg hc hr hw hle hz₀
      (fun k ↦ (Ψ.symm.isBigO_comp _ _).trans (h₀ k)) hz)

/-- **Isolated boundary point preimages.** Let `Ω` be an open set with
`Ω ∩ {0 ≤ im}` connected, and `u` a map of class `C¹` up to the real axis on `Ω ∩ {0 ≤ im}` solving
the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` off the axis, for a field `J` Lipschitz near `x₀` with
`J(x₀)² = -1`, with boundary values `u x ∈ x₀ + L` on `Ω ∩ ℝ` for a subspace `L` maximal totally
real for `J(x₀)`. If `u` is not identically `x₀` on `Ω ∩ {0 ≤ im}`, it takes the value `x₀` on a
discrete subset of `Ω ∩ {0 ≤ im}`, also near the real axis. -/
theorem setOf_ne_mem_codiscreteWithin_of_cauchyRiemann_of_isMaximalTotallyReal
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E)
    (hL : IsMaximalTotallyReal (J x₀ : E →ₗ[ℝ] E) L) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hu : ContDiffOn ℝ 1 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → u x - x₀ ∈ L) (hne : ∃ z ∈ Ω ∩ {z | 0 ≤ z.im}, u z ≠ x₀) :
    {z | u z ≠ x₀} ∈ codiscreteWithin (Ω ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨Ω', hΩ', hΩs, heq, hCR', hbd'⟩ := exists_mapsTo_conj_realBoundary hΩ hCR hbd
  rw [← heq] at hΩc hu hne ⊢
  obtain ⟨n, Ψ, g, hc, hr, hg, hw, hle⟩ := exists_frame_realBoundary hJ hJ₀ hL hΩ' hu hCR' hbd'
  have hset : {z | u z ≠ x₀} = {z | Ψ.symm (u z - x₀) ≠ 0} := by
    ext z
    simp only [mem_ofPred_eq, ne_eq, symm_sub_eq_zero_iff Ψ]
  obtain ⟨z, hz, hzne⟩ := hne
  rw [hset]
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le
    (Ω := ⟨Ω', hΩ'⟩) (by norm_num) hΩs hΩc hg hc hr hw hle
    ⟨z, hz, mt (symm_sub_eq_zero_iff Ψ _).1 hzne⟩

/-- **Finite boundary point preimages on compact sets.** Let `Ω` be an open set
with `Ω ∩ {0 ≤ im}` connected, and `u` a map of class `C¹` up to the real axis on
`Ω ∩ {0 ≤ im}` solving the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` off the axis, for a field `J`
Lipschitz near `x₀` with `J(x₀)² = -1`, with boundary values `u x ∈ x₀ + L` on `Ω ∩ ℝ` for a
subspace `L` maximal totally real for `J(x₀)`. If `u` is not identically `x₀` on
`Ω ∩ {0 ≤ im}`, it takes the value `x₀` at finitely many points of each compact subset of
`Ω ∩ {0 ≤ im}`, which may meet the real axis. -/
theorem finite_inter_preimage_singleton_of_cauchyRiemann_of_isMaximalTotallyReal
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E)
    (hL : IsMaximalTotallyReal (J x₀ : E →ₗ[ℝ] E) L) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hu : ContDiffOn ℝ 1 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → u x - x₀ ∈ L) (hne : ∃ z ∈ Ω ∩ {z | 0 ≤ z.im}, u z ≠ x₀)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω ∩ {z | 0 ≤ z.im}) :
    (K ∩ u ⁻¹' {x₀}).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin (codiscreteWithin_mono hKΩ
    (setOf_ne_mem_codiscreteWithin_of_cauchyRiemann_of_isMaximalTotallyReal hJ hJ₀ hL hΩ hΩc hu
      hCR hbd hne))
  convert h using 1
  ext z
  simp

/-- **The order of a boundary point preimage.** Let `Ω` be an open set with
`Ω ∩ {0 ≤ im}` connected, and `u` a map of class `C¹` up to the real axis on `Ω ∩ {0 ≤ im}` solving
the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` off the axis, for a field `J` Lipschitz near `x₀` with
`J(x₀)² = -1`, with boundary values `u x ∈ x₀ + L` on `Ω ∩ ℝ` for a subspace `L` maximal totally
real for `J(x₀)`, and not identically `x₀` on `Ω ∩ {0 ≤ im}`. Each point `z₀ ∈ Ω ∩ {0 ≤ im}` with
`u z₀ = x₀`, possibly on the axis, has a positive order `m`: `‖u z - x₀‖ ≍ ‖z - z₀‖ ^ m` for `z`
near `z₀` in `{0 ≤ im}`. -/
theorem exists_isTheta_pow_of_cauchyRiemann_of_isMaximalTotallyReal
    (hJ : ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K J t)
    (hJ₀ : J x₀ ∘L J x₀ = -ContinuousLinearMap.id ℝ E)
    (hL : IsMaximalTotallyReal (J x₀ : E →ₗ[ℝ] E) L) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hu : ContDiffOn ℝ 1 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → u x - x₀ ∈ L) (hne : ∃ z ∈ Ω ∩ {z | 0 ≤ z.im}, u z ≠ x₀)
    (hz₀ : z₀ ∈ Ω ∩ {z | 0 ≤ z.im}) (hu₀ : u z₀ = x₀) :
    ∃ m : ℕ, 0 < m ∧
      (fun z ↦ u z - x₀) =Θ[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ m := by
  obtain ⟨Ω', hΩ', hΩs, heq, hCR', hbd'⟩ := exists_mapsTo_conj_realBoundary hΩ hCR hbd
  rw [← heq] at hΩc hu hne hz₀
  obtain ⟨n, Ψ, g, hc, hr, hg, hw, hle⟩ := exists_frame_realBoundary hJ hJ₀ hL hΩ' hu hCR' hbd'
  obtain ⟨m, hm, hθ, -⟩ :=
    exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le
      (Ω := ⟨Ω', hΩ'⟩) (by norm_num) hΩs hΩc hg hc hr hw hle
      (hne.imp fun _ ↦ .imp_right fun h ↦ mt (symm_sub_eq_zero_iff Ψ _).1 h) hz₀
      ((symm_sub_eq_zero_iff Ψ _).2 hu₀)
  exact ⟨m, hm, ⟨by simpa using (Ψ.isBigO_comp _ _).trans hθ.1,
    by simpa using hθ.2.trans (Ψ.isBigO_comp_rev _ _)⟩⟩

end TotallyRealBoundary

end TauCeti
