/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.HoferZehnder
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Hamiltonian
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Codisc

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The `π₁`-sensitive capacity of the cotangent bundle of a torus is infinite

Let `p > 0` and let `Tⁿ = ι → AddCircle p` be the torus, `n ≥ 1`, with its cotangent bundle `T*Tⁿ`,
the canonical symplectic form `ω` and the actions `I_j = ξ(e_j)` of a covector `ξ`
(`TauCeti.CotangentBundle.torusActions`). In the action–angle coordinates
`κ(θ, I) = ∑ j, I_j dθ_j`, a Hamiltonian `H = h(I)` that depends on the actions alone moves each
point linearly on its invariant torus of constant action, with the frequencies `∇h(I)`
(`TauCeti.CotangentBundle.isMIntegralCurve_actionAngleCover_add_smul`). A periodic orbit of
nonzero frequency therefore winds around the torus and is not contractible in `T*Tⁿ`; the
contractible periodic orbits are constant
(`TauCeti.CotangentBundle.eq_of_isMIntegralCurve_hamiltonianVectorField_comp_torusActions`).

So the fast periodic orbits contractible in any set `W` are no obstruction for functions of the
actions. A smooth nonnegative function of the actions, compactly supported in an open set `B` of
actions, attaining its maximum on an open set and vanishing somewhere on `B`, is admissible for
the `π₁`-sensitive Hofer–Zehnder capacity `c°_HZ(U; W)` of the shell `U = I⁻¹(B)` in every `W`
(`TauCeti.CotangentBundle.isContractibleHZAdmissible_comp_torusActions`). Bump functions of the
actions of arbitrary height are of this form, so

`c°_HZ(U; W) = ∞`

whenever `U` contains a shell `I⁻¹(B)` over a nonempty open `B`
(`TauCeti.CotangentBundle.contractibleHZCapacity_eq_top_of_preimage_torusActions_subset`), in
particular whenever `U` is a neighbourhood of an invariant torus `I⁻¹(I₀)`
(`contractibleHZCapacity_eq_top_of_preimage_torusActions_singleton_subset_interior` in
`TauCeti.CotangentBundle`).
The unit codisc bundle `D*Tⁿ` of any continuous Riemannian metric on the torus is a
neighbourhood of the zero section, so its capacity `c°_HZ(D*Tⁿ)` is infinite
(`TauCeti.CotangentBundle.contractibleHZCapacity_codiscBundle_eq_top`). For the flat metric this
reflects that a flat torus has no contractible closed geodesics, and so `S*Tⁿ` no contractible
closed characteristics.

Finiteness of `c°_HZ` is the hypothesis under which the Hofer–Zehnder–Struwe argument produces
contractible closed characteristics on almost every level
(`IsNondegenerate.hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top` in
`TauCeti.SmoothTwoForm`), so this argument says nothing about hypersurfaces in the cotangent
bundle of a torus. The dimension hypothesis is needed: for `n = 0` the cotangent bundle is a point,
and every admissible function, which vanishes on a nonempty open set, is zero.

## Main results

* `TauCeti.CotangentBundle.isContractibleHZAdmissible_comp_torusActions`: admissible functions of
  the actions.
* `TauCeti.CotangentBundle.contractibleHZCapacity_eq_top_of_preimage_torusActions_subset`:
  `c°_HZ(U; W) = ∞` when `U` contains the shell over a nonempty open set of actions.
* `TauCeti.CotangentBundle.contractibleHZCapacity_codiscBundle_eq_top`: `c°_HZ(D*Tⁿ; W) = ∞`.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Sections 3.1 and 4.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.1 and Proposition 6.3.
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Functions of the actions are admissible.** Let `h` be a smooth nonnegative compactly
supported function on the actions, with support inside an open set `B`, vanishing somewhere on `B`
and attaining its maximum on a nonempty open set. Then `H = h(I)` is admissible for the
`π₁`-sensitive Hofer–Zehnder capacity of the shell `I⁻¹(B)` of `T*Tⁿ`, with contractibility tested
in any set `W`: its contractible periodic orbits are constant. -/
theorem isContractibleHZAdmissible_comp_torusActions {h : (ι → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h)
    (hh₀ : ∀ I, 0 ≤ h I) (hhc : HasCompactSupport h) {B : Set (ι → ℝ)} (hB : IsOpen B)
    (hhB : tsupport h ⊆ B) (hBh : (B \ tsupport h).Nonempty)
    (hmax : ∃ O : Set (ι → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ I ∈ O, IsMaxOn h univ I)
    (W : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))) :
    (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)).IsContractibleHZAdmissible W (torusActions p ⁻¹' B)
        (h ∘ torusActions p) := by
  have hcont := (contMDiff_torusActions (ι := ι) p).continuous
  have hsupp : tsupport (h ∘ torusActions p) ⊆ torusActions p ⁻¹' tsupport h :=
    tsupport_comp_subset_preimage h hcont
  obtain ⟨O, hO, ⟨I₁, hI₁⟩, hOmax⟩ := hmax
  obtain ⟨I₂, hI₂⟩ := hBh
  refine
    { contMDiff := hh.contMDiff.comp (contMDiff_torusActions p)
      isCompact_tsupport :=
        ((isProperMap_torusActions p).isCompact_preimage hhc).of_isClosed_subset
          (isClosed_tsupport _) hsupp
      tsupport_subset_interior := by
        rw [(hB.preimage hcont).interior_eq]
        exact hsupp.trans (preimage_mono hhB)
      tsupport_subset_interior_manifold := by
        rw [ModelWithCorners.interior_eq_univ]
        exact subset_univ _
      nonneg := fun z ↦ hh₀ _
      exists_isOpen_eqOn_zero := ⟨torusActions p ⁻¹' (B \ tsupport h),
        (hB.sdiff (isClosed_tsupport h)).preimage hcont, ⟨actionAngleCover p (0, I₂), by simpa⟩,
        preimage_mono sdiff_subset, fun z hz ↦ image_eq_zero_of_notMem_tsupport (f := h) hz.2⟩
      exists_isOpen_isMaxOn := ⟨torusActions p ⁻¹' O, hO.preimage hcont,
        ⟨actionAngleCover p (0, I₁), by simpa⟩, fun z hz w _ ↦ hOmax _ hz (mem_univ _)⟩
      eq_of_isMIntegralCurve := fun T γ hT _ hγ hper ⟨g, hg, hgγ⟩ t ↦
        eq_of_isMIntegralCurve_hamiltonianVectorField_comp_torusActions p (hh.of_le (by simp)) hγ
          hT hper ⟨(⟨Subtype.val, continuous_subtypeVal⟩ : C(W, _)).comp g, hg.comp_right _,
            hgγ⟩ t }

/-- **The capacity of a shell of the cotangent bundle of a torus is infinite.** If `U ⊆ T*Tⁿ`
contains all covectors whose actions lie in a nonempty open set `B`, and the torus has positive
dimension, then `c°_HZ(U; W) = ∞` for every set `W`: bump functions of the actions supported in
`B` are admissible, whatever their height. -/
theorem contractibleHZCapacity_eq_top_of_preimage_torusActions_subset [Nonempty ι]
    {B : Set (ι → ℝ)} (hB : IsOpen B) (hBne : B.Nonempty)
    {W U : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))}
    (hU : torusActions p ⁻¹' B ⊆ U) :
    (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)).contractibleHZCapacity W U = ⊤ := by
  obtain ⟨I₀, hI₀⟩ := hBne
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hB I₀ hI₀
  -- The bump `φ` is `1` on the ball of radius `R / 4` and vanishes outside that of radius `R / 2`.
  let φ : ContDiffBump I₀ := ⟨R / 4, R / 2, by positivity, by linarith⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun N ↦ ?_
  have hN : (0 : ℝ) ≤ N := N.property
  let h : (ι → ℝ) → ℝ := fun I ↦ N * φ I
  have hφB : tsupport h ⊆ B := (tsupport_smul_subset_right (fun _ ↦ (N : ℝ)) φ).trans <| by
    rw [ContDiffBump.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by simp only [φ]; linarith)).trans hball
  obtain ⟨v, hv⟩ := exists_norm_eq (ι → ℝ) (show 0 ≤ 3 * R / 4 by positivity)
  have hBh : (B \ tsupport h).Nonempty := by
    refine ⟨I₀ + v, hball ?_, fun hmem ↦ ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hv]
      linarith
    · have := (tsupport_smul_subset_right (fun _ ↦ (N : ℝ)) φ) hmem
      rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
        hv] at this
      simp only [φ] at this
      linarith
  have hmax (I : ι → ℝ) (hI : I ∈ Metric.ball I₀ (R / 4)) : IsMaxOn h univ I :=
    isMaxOn_iff.2 fun J _ ↦ by
      simp only [h, φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hI), mul_one]
      exact mul_le_of_le_one_right hN φ.le_one
  have hF := isContractibleHZAdmissible_comp_torusActions p
    (contDiff_const.mul φ.contDiff) (fun I ↦ mul_nonneg hN φ.nonneg)
    (φ.hasCompactSupport.mul_left) hB hφB hBh
    ⟨_, Metric.isOpen_ball, ⟨I₀, Metric.mem_ball_self (by positivity)⟩, hmax⟩ W
  have hsup : ⨆ z, (h ∘ torusActions p) z = N := by
    have h₀ : (h ∘ torusActions p) (actionAngleCover p (0, I₀)) = N := by
      simp [h, φ.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))]
    have hle (z) : (h ∘ torusActions p) z ≤ N := by
      rw [← h₀, comp_apply, comp_apply, torusActions_actionAngleCover]
      exact isMaxOn_iff.1 (hmax I₀ (Metric.mem_ball_self (by positivity))) _ (mem_univ _)
    refine le_antisymm (ciSup_le hle) ?_
    calc (N : ℝ) = (h ∘ torusActions p) (actionAngleCover p (0, I₀)) := h₀.symm
      _ ≤ _ := le_ciSup (f := h ∘ torusActions p) ⟨N, by rintro _ ⟨z, rfl⟩; exact hle z⟩ _
  have := (hF.mono subset_rfl hU).ofReal_iSup_le_contractibleHZCapacity
  rwa [hsup, ENNReal.ofReal_coe_nnreal] at this

/-- **The capacity of a neighbourhood of an invariant torus is infinite.** If `U ⊆ T*Tⁿ` is a
neighbourhood of the invariant torus of the actions `I₀`, and the torus has positive dimension,
then `c°_HZ(U; W) = ∞` for every set `W`. -/
theorem contractibleHZCapacity_eq_top_of_preimage_torusActions_singleton_subset_interior
    [Nonempty ι] {I₀ : ι → ℝ}
    {W U : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))}
    (hU : torusActions p ⁻¹' {I₀} ⊆ interior U) :
    (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)).contractibleHZCapacity W U = ⊤ := by
  -- The action map is closed, so a neighbourhood of the fibre over `I₀` contains a shell.
  have hmem : interior U ∈ Filter.comap (torusActions p) (𝓝 I₀) := by
    rw [(isProperMap_torusActions p).isClosedMap.comap_nhds_eq
      (isProperMap_torusActions p).continuous]
    exact isOpen_interior.mem_nhdsSet.2 hU
  obtain ⟨t, ht, htU⟩ := Filter.mem_comap.1 hmem
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
  exact contractibleHZCapacity_eq_top_of_preimage_torusActions_subset p Metric.isOpen_ball
    ⟨I₀, Metric.mem_ball_self hε⟩ ((preimage_mono hεt).trans (htU.trans interior_subset))

omit [DecidableEq ι] in
/-- **The capacity of the codisc bundle of a torus is infinite.** For every continuous Riemannian
metric on a torus of positive dimension, the unit codisc bundle `D*Tⁿ`, a neighbourhood of the
zero section, has `c°_HZ(D*Tⁿ; W) = ∞` for every set `W`; in particular `c°_HZ(D*Tⁿ) = ∞`. -/
theorem contractibleHZCapacity_codiscBundle_eq_top [Nonempty ι]
    [RiemannianBundle fun x : ι → AddCircle p ↦
      TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x]
    [IsContMDiffRiemannianBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) 0 (ι → ℝ)
      fun x : ι → AddCircle p ↦ TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x]
    (W : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))) :
    (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)).contractibleHZCapacity
      W (codiscBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) = ⊤ := by
  classical
  refine contractibleHZCapacity_eq_top_of_preimage_torusActions_singleton_subset_interior p
    (I₀ := 0)
    (Subset.trans ?_ (interior_maximal (fun z hz ↦ mem_codiscBundle.2 (le_of_lt hz))
      (isOpen_lt continuous_norm_snd continuous_const)))
  intro z hz
  obtain ⟨⟨θ, I⟩, rfl⟩ := surjective_actionAngleCover p z
  rw [mem_preimage, torusActions_actionAngleCover, mem_singleton_iff] at hz
  subst hz
  -- Over the zero actions the covector `κ(θ, 0)` vanishes.
  have h0 : ‖(actionAngleCover p (θ, 0)).snd‖ ≤ 0 :=
    ContinuousLinearMap.opNorm_le_bound _ le_rfl fun v ↦ by
      -- The evaluation lemma is stated for the coercion of `(ι → ℝ) →L[ℝ] ℝ`, which agrees with
      -- that of the covectors of the Riemannian metric up to unfolding the tangent space.
      have hv : (actionAngleCover p (θ, 0)).snd v = 0 :=
        (actionAngleCover_snd_apply p (θ, 0) v).trans (by simp)
      rw [hv, norm_zero, zero_mul]
  exact h0.trans_lt one_pos

end CotangentBundle

end TauCeti
