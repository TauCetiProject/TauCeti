/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.MinimalCoupling
public import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Changing the connection in the minimal coupling form

Let `ω` be a two-form on a normed space `E`, let `σ` be a constant skew-symmetric bilinear form
on a normed space `V`, and let `d + A₀` and `d + A₁` be two connections on the trivial bundle
`E × V → E`. This file shows that the germ of the minimal coupling form
`ω_A = π^* ω + dλ_A` (`TauCeti.minimalCouplingForm`) along the zero section does not depend on
the connection.

The minimal coupling primitive `λ_A` is affine in `A`, so the primitives of the two connections
differ by a term quadratic in the fibre coordinate: at `(z, w)`, on a vector `(v, n)`,

`(λ_{A₁} - λ_{A₀})(v, n) = σ(w, (A₁ - A₀)_z(v) w) / 2`

(`TauCeti.minimalCouplingPrimitive_sub_minimalCouplingPrimitive_apply`). Every primitive vanishes
along the zero section, and the difference also has zero derivative there
(`TauCeti.hasFDerivAt_minimalCouplingPrimitive_sub_minimalCouplingPrimitive_zero`). The minimal
coupling forms differ by the exterior derivative of this difference,
`ω_{A₁} - ω_{A₀} = d(λ_{A₁} - λ_{A₀})`
(`TauCeti.minimalCouplingForm_sub_minimalCouplingForm`), and along the zero section both are
`ω + σ` on the whole tangent space of `E × V`
(`TauCeti.minimalCouplingForm_zero_eq_minimalCouplingForm_zero`).

These are the hypotheses of Moser's argument relative to a compact set
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`).
Hence, in finite dimensions, for a smooth closed two-form `ω`, a skew-symmetric nondegenerate `σ`,
two smooth connection forms `A₀`, `A₁` and a compact set `K ⊆ E` on which `ω` is nondegenerate,
some diffeomorphism `Φ` of `E × V` fixes every point `(z, 0)` with `z ∈ K` to first order, moves
only the points of a compact set, and pulls `ω_{A₁}` back to `ω_{A₀}` on a neighbourhood of
`K × {0}` (`TauCeti.exists_diffeomorph_fix_eventually_minimalCouplingForm_eq`). Neither connection
needs to preserve `σ`. In a single trivialization this is the statement that the minimal coupling
model of a symplectic vector bundle near its zero section does not depend, up to such a
diffeomorphism, on the connection; a change of symplectic trivialization is accounted for by the
gauge covariance of the minimal coupling form
(`TauCeti.compContinuousLinearMap_minimalCouplingForm_gaugeAction`).

## Main results

* `TauCeti.minimalCouplingPrimitive_sub_minimalCouplingPrimitive_apply`: the primitives of two
  connections differ by `σ(w, (A₁ - A₀)_z(v) w) / 2`.
* `TauCeti.hasFDerivAt_minimalCouplingPrimitive_sub_minimalCouplingPrimitive_zero`: this
  difference has zero derivative along the zero section.
* `TauCeti.minimalCouplingForm_sub_minimalCouplingForm`: `ω_{A₁} - ω_{A₀} = d(λ_{A₁} - λ_{A₀})`.
* `TauCeti.minimalCouplingForm_zero_eq_minimalCouplingForm_zero`: along the zero section the
  minimal coupling form does not depend on the connection.
* `TauCeti.exists_diffeomorph_fix_eventually_minimalCouplingForm_eq`: the minimal coupling forms
  of two connections are related near the zero section over a compact set by a diffeomorphism
  fixing it to first order.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 3.4 (the symplectic neighbourhood theorem and the minimal coupling form).
* V. Guillemin, E. Lerman and S. Sternberg, *Symplectic fibrations and multiplicity diagrams*,
  Cambridge University Press, 1996, Section 1.4 (minimal coupling).
* J. Moser, *On the volume elements on a manifold*, Trans. Amer. Math. Soc. 120 (1965), 286–294.
-/

public section

noncomputable section

open ContinuousAlternatingMap
open Filter Set
open scoped Manifold Topology

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {σ : V →L[ℝ] V →L[ℝ] ℝ} {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ}
  {A A₀ A₁ : E → E →L[ℝ] V →L[ℝ] V} {z : E}

/-! ### The difference of two minimal coupling primitives -/

/-- **The primitives of two connections differ by a quadratic term.** At `(z, w)`, on a vector
`(v, n)`, the minimal coupling primitives of `d + A₁` and `d + A₀` differ by
`σ(w, (A₁ - A₀)_z(v) w) / 2`. -/
theorem minimalCouplingPrimitive_sub_minimalCouplingPrimitive_apply (p : E × V)
    (u : Fin 1 → E × V) :
    (minimalCouplingPrimitive σ A₁ p - minimalCouplingPrimitive σ A₀ p) u =
      σ p.2 ((A₁ p.1 - A₀ p.1) (u 0).1 p.2) / 2 := by
  simp only [ContinuousAlternatingMap.sub_apply, minimalCouplingPrimitive_apply, _root_.sub_apply,
    map_add, map_sub]
  ring

/-- The difference of two minimal coupling primitives, written as the one-form
`(v, n) ↦ σ(w, (A₁ - A₀)_z(v) w) / 2` at `(z, w)`, a product of the two factors
`w ↦ σ(w, ·)` and `(z, w) ↦ (v, n) ↦ (A₁ - A₀)_z(v) w`, both of which vanish along the zero
section. -/
private theorem minimalCouplingPrimitive_sub_minimalCouplingPrimitive_eq :
    (fun p ↦ minimalCouplingPrimitive σ A₁ p - minimalCouplingPrimitive σ A₀ p) = fun p : E × V ↦
      ofSubsingletonLIE (0 : Fin 1) ((2⁻¹ : ℝ) • (σ p.2).comp
        (((ContinuousLinearMap.apply ℝ V p.2).comp (A₁ p.1 - A₀ p.1)).comp
          (ContinuousLinearMap.fst ℝ E V))) := by
  funext p
  ext u
  rw [minimalCouplingPrimitive_sub_minimalCouplingPrimitive_apply]
  simp [ofSubsingletonLIE, div_eq_inv_mul]

/-- **The difference of two minimal coupling primitives has zero first jet along the zero
section.** If `A₀` and `A₁` are differentiable at `z`, then
`λ_{A₁} - λ_{A₀}` has derivative zero at `(z, 0)`: it is quadratic in the fibre coordinate. -/
theorem hasFDerivAt_minimalCouplingPrimitive_sub_minimalCouplingPrimitive_zero
    (hA₀ : DifferentiableAt ℝ A₀ z) (hA₁ : DifferentiableAt ℝ A₁ z) :
    HasFDerivAt (fun p ↦ minimalCouplingPrimitive σ A₁ p - minimalCouplingPrimitive σ A₀ p)
      (0 : E × V →L[ℝ] (E × V) [⋀^Fin 1]→L[ℝ] ℝ) (z, (0 : V)) := by
  rw [minimalCouplingPrimitive_sub_minimalCouplingPrimitive_eq]
  -- The two factors `σ(w, ·)` and `(v, n) ↦ (A₁ - A₀)_z(v) w` vanish at `(z, 0)`.
  have hc : HasFDerivAt (fun p : E × V ↦ σ p.2) (σ.comp (ContinuousLinearMap.snd ℝ E V))
      (z, (0 : V)) := σ.hasFDerivAt.comp _ hasFDerivAt_snd
  have hd : DifferentiableAt ℝ (fun p : E × V ↦ ((ContinuousLinearMap.apply ℝ V p.2).comp
      (A₁ p.1 - A₀ p.1)).comp (ContinuousLinearMap.fst ℝ E V)) (z, (0 : V)) := by
    fun_prop
  have hcd := ((hc.clm_comp hd.hasFDerivAt).const_smul (2⁻¹ : ℝ))
  refine ((ofSubsingletonLIE (0 : Fin 1) : ((E × V) →L[ℝ] ℝ) ≃ₗᵢ[ℝ]
    (E × V) [⋀^Fin 1]→L[ℝ] ℝ).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
      (z, (0 : V)) hcd).congr_fderiv ?_
  simp

/-! ### The difference of two minimal coupling forms -/

/-- **The minimal coupling forms of two connections differ by an exact form**,
`ω_{A₁} - ω_{A₀} = d(λ_{A₁} - λ_{A₀})`, at every point over which `A₀` and `A₁` are
differentiable. -/
theorem minimalCouplingForm_sub_minimalCouplingForm {p : E × V}
    (hA₀ : DifferentiableAt ℝ A₀ p.1) (hA₁ : DifferentiableAt ℝ A₁ p.1) :
    minimalCouplingForm σ ω A₁ p - minimalCouplingForm σ ω A₀ p =
      extDeriv (fun q ↦ minimalCouplingPrimitive σ A₁ q - minimalCouplingPrimitive σ A₀ q) p := by
  obtain ⟨z, w⟩ := p
  rw [← Pi.sub_def, extDeriv_sub (differentiableAt_minimalCouplingPrimitive hA₁ w)
    (differentiableAt_minimalCouplingPrimitive hA₀ w)]
  ext u
  simp only [ContinuousAlternatingMap.sub_apply, minimalCouplingForm_apply]
  ring

/-- **Along the zero section the minimal coupling form does not depend on the connection.** For
skew-symmetric `σ` and connection forms differentiable at `z`, the minimal coupling forms of
`d + A₀` and `d + A₁` agree at `(z, 0)` on the whole tangent space of `E × V`: both are `ω + σ`. -/
theorem minimalCouplingForm_zero_eq_minimalCouplingForm_zero (hσ : ∀ u u', σ u u' = -σ u' u)
    (hA₀ : DifferentiableAt ℝ A₀ z) (hA₁ : DifferentiableAt ℝ A₁ z) :
    minimalCouplingForm σ ω A₁ (z, 0) = minimalCouplingForm σ ω A₀ (z, 0) := by
  ext u
  have hu : u = ![u 0, u 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hu, minimalCouplingForm_apply_pair_zero hσ hA₁, minimalCouplingForm_apply_pair_zero hσ hA₀]

/-! ### Independence of the germ from the connection -/

section Moser

/-- The minimal coupling form of a smooth two-form and a smooth connection form, as a smooth
two-form on the model space `E × V`. -/
private def minimalCouplingSmoothForm (σ : V →L[ℝ] V →L[ℝ] ℝ) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    SmoothTwoForm 𝓘(ℝ, E × V) (E × V) :=
  ⟨minimalCouplingForm σ ω A, (isSmoothForm_modelSpace_iff.mpr (contDiff_minimalCouplingForm hω
    (hA.of_le (by rw [ENat.coe_top_add_one])))).mem_smoothBundleForms⟩

private theorem minimalCouplingSmoothForm_val (σ : V →L[ℝ] V →L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    (minimalCouplingSmoothForm σ hω hA).val = minimalCouplingForm σ ω A :=
  (rfl)

/-- The difference of the minimal coupling primitives of two smooth connection forms, as a smooth
one-form on the model space `E × V`. -/
private def minimalCouplingPrimitiveSubSmoothForm (σ : V →L[ℝ] V →L[ℝ] ℝ)
    (hA₀ : ContDiff ℝ (⊤ : ℕ∞) A₀)
    (hA₁ : ContDiff ℝ (⊤ : ℕ∞) A₁) : SmoothForm 𝓘(ℝ, E × V) (E × V) ℝ 1 :=
  ⟨fun p ↦ minimalCouplingPrimitive σ A₁ p - minimalCouplingPrimitive σ A₀ p,
    (isSmoothForm_modelSpace_iff.mpr ((contDiff_minimalCouplingPrimitive hA₁).sub
      (contDiff_minimalCouplingPrimitive hA₀))).mem_smoothBundleForms⟩

private theorem minimalCouplingPrimitiveSubSmoothForm_val (σ : V →L[ℝ] V →L[ℝ] ℝ)
    (hA₀ : ContDiff ℝ (⊤ : ℕ∞) A₀)
    (hA₁ : ContDiff ℝ (⊤ : ℕ∞) A₁) :
    (minimalCouplingPrimitiveSubSmoothForm σ hA₀ hA₁).val =
      fun p ↦ minimalCouplingPrimitive σ A₁ p - minimalCouplingPrimitive σ A₀ p :=
  (rfl)

/-- The minimal coupling form of a closed two-form is closed. -/
private theorem isClosed_minimalCouplingSmoothForm (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hdω : ∀ z, extDeriv ω z = 0) (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    (minimalCouplingSmoothForm σ hω hA).IsClosed := by
  rw [SmoothForm.isClosed_def]
  funext ⟨z, w⟩
  rw [mextDeriv_eq_extDeriv, minimalCouplingSmoothForm_val σ]
  exact extDeriv_minimalCouplingForm_eq_zero (hω.differentiable (by simp) z) (hdω z)
    (hA.contDiffAt.of_le (by simp))

/-- Along the zero section, over a point where `ω` is nondegenerate, the minimal coupling form of
a nondegenerate skew-symmetric `σ` is nondegenerate. -/
private theorem nondegenerate_bilinFormAt_minimalCouplingSmoothForm_zero
    (hσ : ∀ u u', σ u u' = -σ u' u) (hσn : ∀ u, (∀ u', σ u u' = 0) → u = 0)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hωz : ∀ v, (∀ v', ω z ![v, v'] = 0) → v = 0) :
    ((minimalCouplingSmoothForm σ hω hA).bilinFormAt (z, 0)).Nondegenerate := by
  refine ((SmoothForm.isAlt_bilinFormAt _ _).isRefl.nondegenerate_iff_separatingLeft).2 ?_
  rintro ⟨v, n⟩ h
  obtain ⟨rfl, hv⟩ := (forall_minimalCouplingForm_apply_zero_eq_zero_iff hσ hσn
    (hA.differentiable (by simp) z) v n).1
      fun x ↦ ((SmoothForm.bilinFormAt_apply _ _ _ x).trans
        (SmoothBundleForm.eval₂_apply _ _ _ x)).symm.trans (h x)
  rw [hωz v hv]
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]

/-- **The germ of the minimal coupling form along the zero section does not depend on the
connection.** In finite dimensions, let `ω` be a smooth closed two-form on `E`, let `σ` be a
skew-symmetric nondegenerate bilinear form on `V`, let `A₀`, `A₁` be smooth connection forms on
the trivial bundle `E × V`, and let `K ⊆ E` be a compact set on which `ω` is nondegenerate. Then
some diffeomorphism `Φ` of `E × V` fixes every point `(z, 0)` with `z ∈ K`, with identity
derivative there, moves only the points of a compact set, and pulls the minimal coupling form of
`A₁` back to that of `A₀` on a neighbourhood of `K × {0}`. -/
theorem exists_diffeomorph_fix_eventually_minimalCouplingForm_eq
    (hσ : ∀ u u', σ u u' = -σ u' u) (hσn : ∀ u, (∀ u', σ u u' = 0) → u = 0)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (hdω : ∀ z, extDeriv ω z = 0) (hA₀ : ContDiff ℝ (⊤ : ℕ∞) A₀)
    (hA₁ : ContDiff ℝ (⊤ : ℕ∞) A₁) {K : Set E} (hK : IsCompact K)
    (hωK : ∀ z ∈ K, ∀ v, (∀ v', ω z ![v, v'] = 0) → v = 0) :
    ∃ Φ : (E × V) ≃ₘ^(⊤ : ℕ∞)⟮𝓘(ℝ, E × V), 𝓘(ℝ, E × V)⟯ (E × V),
      (∀ z ∈ K, Φ (z, 0) = (z, 0)) ∧ (∃ C, IsCompact C ∧ ∀ p ∉ C, Φ p = p) ∧
      (∀ᶠ p in 𝓝ˢ (K ×ˢ {0}),
        (minimalCouplingForm σ ω A₁ (Φ p)).compContinuousLinearMap (fderiv ℝ Φ p) =
          minimalCouplingForm σ ω A₀ p) ∧
      ∀ z ∈ K, fderiv ℝ Φ (z, 0) = ContinuousLinearMap.id ℝ (E × V) := by
  set σ₀ := minimalCouplingSmoothForm σ hω hA₀
  set σ₁ := minimalCouplingSmoothForm σ hω hA₁
  set β := minimalCouplingPrimitiveSubSmoothForm σ hA₀ hA₁
  have hd₀ (z : E) : DifferentiableAt ℝ A₀ z := hA₀.differentiable (by simp) z
  have hd₁ (z : E) : DifferentiableAt ℝ A₁ z := hA₁.differentiable (by simp) z
  -- `ω_{A₁} - ω_{A₀}` is the exterior derivative of `β`.
  have hβ : mextDeriv β.val = (σ₁ - σ₀).val := by
    funext p
    rw [mextDeriv_eq_extDeriv, minimalCouplingPrimitiveSubSmoothForm_val σ,
      AddSubgroupClass.coe_sub, Pi.sub_apply, minimalCouplingSmoothForm_val σ,
      minimalCouplingSmoothForm_val σ]
    exact (minimalCouplingForm_sub_minimalCouplingForm (hd₀ _) (hd₁ _)).symm
  -- Along `K × {0}` the primitive vanishes, and the path of forms is `ω + σ`, nondegenerate.
  have hβK : ∀ p ∈ K ×ˢ ({0} : Set V), β.val p = 0 := by
    rintro ⟨z, w⟩ ⟨-, hw⟩
    obtain rfl : w = 0 := hw
    rw [minimalCouplingPrimitiveSubSmoothForm_val σ]
    exact sub_eq_zero_of_eq <|
      (minimalCouplingPrimitive_zero σ A₁ z).trans (minimalCouplingPrimitive_zero σ A₀ z).symm
  have hnd : ∀ p ∈ K ×ˢ ({0} : Set V), ∀ s ∈ Icc (0 : ℝ) 1,
      ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt p).Nondegenerate := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩ s -
    obtain rfl : w = 0 := hw
    rw [SmoothTwoForm.bilinFormAt_add_smul_sub_of_eq
      (minimalCouplingForm_zero_eq_minimalCouplingForm_zero hσ (hd₀ z) (hd₁ z)) s]
    exact nondegenerate_bilinFormAt_minimalCouplingSmoothForm_zero hσ hσn hω hA₀ (hωK z hz)
  obtain ⟨Φ, hΦK, hΦC, hΦ, hΦ1⟩ :=
    SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub
      (isClosed_minimalCouplingSmoothForm hω hdω hA₀) hβ
      (hK.prod isCompact_singleton) hβK hnd
  refine ⟨Φ, fun z hz ↦ hΦK _ ⟨hz, mem_singleton _⟩, hΦC, ?_, fun z hz ↦ ?_⟩
  · filter_upwards [hΦ] with p hp
    ext u
    -- On the model space, `mfderiv` is `fderiv` read through the identity `fromTangentSpace`.
    rw [SmoothForm.coe_mpullback] at hp
    have h := (TauCeti.mpullback_apply (I := 𝓘(ℝ, E × V)) (I' := 𝓘(ℝ, E × V)) Φ σ₁.val p
      u).symm.trans congr($hp u)
    rw [mfderiv_eq_fderiv] at h
    rw [compContinuousLinearMap_apply]
    exact h
  · have h := hΦ1 _ ⟨hz, mem_singleton _⟩ (by
      rw [RoughForm.inChartAt_modelSpace, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id,
        minimalCouplingPrimitiveSubSmoothForm_val σ]
      exact hasFDerivAt_minimalCouplingPrimitive_sub_minimalCouplingPrimitive_zero (hd₀ z) (hd₁ z))
    rw [mfderiv_eq_fderiv] at h
    exact ContinuousLinearMap.ext fun v ↦ congr($h v)

end Moser

end TauCeti
