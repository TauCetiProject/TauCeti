/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport

/-!
# Naturality of Fredholm determinant lines and of their orientations

A commuting square `S ∘ e₁ = e₂ ∘ T` of operators, with isomorphisms `e₁` of the sources and `e₂`
of the targets, induces an isomorphism of determinant lines `det T ≃ det S`
(`LinearMap.detLineCongr`). This file shows that these isomorphisms are compatible with the
structure through which the determinant lines of Fredholm operators are compared and oriented:
stabilizations, kernel charts, coherent families and orientation transport. Orientations of
determinant lines can therefore be moved between conjugate families of operators, for instance
between the expressions of a family of operators in two trivializations of a bundle, or along a
rescaling of the target.

* **Stabilizations and kernel charts.** A commuting square `Ψ`, `e₂` between stabilized operators
  `D₁.coprod D₂` and `D₁'.coprod D₂'` which is `e₁` on `E × 0` and induces `eΛ` on the
  stabilizing spaces intertwines the normalized stabilization isomorphisms
  (`ContinuousLinearMap.detLineStabilizationEquiv_congr`) and, for kernel coordinates matched by
  an isomorphism `eG`, the kernel charts (`ContinuousLinearMap.detLineChartEquiv_detLineCongr`).
* **Changes of kernel chart.** Changing the kernel coordinate `q` of a chart to `q₁` multiplies it
  by the determinant of `q₁ ∘ kerSection q`
  (`ContinuousLinearMap.detLineChartEquiv_apply_eq_det_smul`). Changing the stabilizer `D₂` to
  `D₂ + (D₁.coprod D₂) ∘ L`, with `L` valued in the kernel of `q`, multiplies it by the
  determinant of `1 + snd ∘ L`
  (`ContinuousLinearMap.detLineChartEquiv_apply_eq_det_smul_of_comp_eq`). Over `ℝ`, when the
  stabilizer and the coordinate move continuously with a parameter, both determinants are close
  to `1`, so the chart with moving data is a positive multiple of the chart with the data frozen
  (`ContinuousLinearMap.eventually_detLineChartEquiv_eq_smul`).
* **Coherence and transport.** Let `S x ∘ e₁ x = e₂ x ∘ T x` for families of isomorphisms which
  are continuous in the operator norm. The transport along these squares of a family coherent for
  `T` is coherent for `S` (`TauCeti.IsDetLineCoherentWithinAt.detLineCongr`,
  `TauCeti.IsDetLineCoherentOn.detLineCongr`): read on `T x`, a fixed kernel chart of `S x` has the
  moving stabilizer `(e₂ x)⁻¹ ∘ D₂` and coordinate `q ∘ (e₁ x × 1)`. Hence orientation transport
  along `S` is orientation transport along `T`, conjugated by the transports along the squares at
  the two ends (`TauCeti.detLineOrientationTransport_map_detLineCongr`).
* **Isomorphisms of the target.** For a Fredholm operator `T₀` and a path `A` of isomorphisms of
  its target, orientation transport along `t ↦ A t ∘ T₀` is the isomorphism of determinant lines
  induced by `A b ∘ (A a)⁻¹`, whatever the path (`TauCeti.detLineOrientationTransport_comp_left`).
  For example, the positive block rescaling `(f, η) ↦ (2 f, η / √2)` of the target, joined to the
  identity through positive block rescalings, carries the orientations of the determinant line of
  `(-d^*, √2 d⁺)` to those of `(-2 d^*, d⁺)` by the isomorphism of determinant lines it induces.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

section Congr

variable {𝕜 E Λ F E' Λ' F' : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F]
  [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [AddCommGroup Λ'] [Module 𝕜 Λ'] [TopologicalSpace Λ'] [AddCommGroup F'] [Module 𝕜 F']
  [TopologicalSpace F'] [ContinuousAdd F']
  {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {D₁' : E' →L[𝕜] F'} {D₂' : Λ' →L[𝕜] F'}
  {e₁ : E ≃ₗ[𝕜] E'} {e₂ : F ≃ₗ[𝕜] F'} {eΛ : Λ ≃ₗ[𝕜] Λ'} {Ψ : (E × Λ) ≃ₗ[𝕜] (E' × Λ')}

/-- A commuting square of stabilized operators which is `e₁` on `E × 0` restricts to a commuting
square of the original operators. -/
theorem comp_eq_of_coprod_comp_eq
    (hΨ : (D₁'.coprod D₂' : E' × Λ' →ₗ[𝕜] F') ∘ₗ Ψ.toLinearMap =
      e₂.toLinearMap ∘ₗ (D₁.coprod D₂ : E × Λ →ₗ[𝕜] F))
    (hΨ₁ : ∀ x, Ψ (x, 0) = (e₁ x, 0)) :
    (D₁' : E' →ₗ[𝕜] F') ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ (D₁ : E →ₗ[𝕜] F) := by
  refine LinearMap.ext fun x ↦ ?_
  simpa [hΨ₁] using LinearMap.congr_fun hΨ (x, 0)

/-- In a commuting square of stabilized operators, the target stabilization is onto when the
source stabilization is. -/
theorem surjective_coprod_of_coprod_comp_eq
    (hΨ : (D₁'.coprod D₂' : E' × Λ' →ₗ[𝕜] F') ∘ₗ Ψ.toLinearMap =
      e₂.toLinearMap ∘ₗ (D₁.coprod D₂ : E × Λ →ₗ[𝕜] F))
    (h : Function.Surjective (D₁.coprod D₂)) : Function.Surjective (D₁'.coprod D₂') := by
  intro y
  obtain ⟨x, hx⟩ := h (e₂.symm y)
  refine ⟨Ψ x, ?_⟩
  have := LinearMap.congr_fun hΨ x
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, coe_coe] at this
  rw [this, hx, LinearEquiv.apply_symm_apply]

variable [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 D₁'.ker]
  [FiniteDimensional 𝕜 Λ']

/-- **Naturality of the normalized stabilization isomorphism.** Let `Ψ : E × Λ ≃ E' × Λ'` and
`e₂ : F ≃ F'` form a commuting square of the stabilized operators `D₁.coprod D₂` and
`D₁'.coprod D₂'`, with `Ψ (x, 0) = (e₁ x, 0)` and with parameter component `eΛ`. Then the
normalized stabilization isomorphisms intertwine the isomorphism induced by the restriction of
`Ψ` to the stabilized kernels and by `eΛ` with the transport `LinearMap.detLineCongr` of the
determinant lines along the square formed by `e₁` and `e₂`. -/
theorem detLineStabilizationEquiv_congr
    (hΨ : (D₁'.coprod D₂' : E' × Λ' →ₗ[𝕜] F') ∘ₗ Ψ.toLinearMap =
      e₂.toLinearMap ∘ₗ (D₁.coprod D₂ : E × Λ →ₗ[𝕜] F))
    (hΨ₁ : ∀ x, Ψ (x, 0) = (e₁ x, 0)) (hΨ₂ : ∀ y, (Ψ y).2 = eΛ y.2)
    (h : Function.Surjective (D₁.coprod D₂))
    (t : TauCeti.detLine 𝕜 (D₁.coprod D₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) :
    detLineStabilizationEquiv D₁' D₂' (surjective_coprod_of_coprod_comp_eq hΨ h)
        (TensorProduct.congr (Ψ.ofSubmodules _ _
          ((D₁.coprod D₂ : E × Λ →ₗ[𝕜] F).map_ker_eq_ker_of_comp_eq Ψ.surjective e₂.injective
            hΨ)).detLineCongr eΛ.detLineCongr.symm.dualMap t) =
      (D₁ : E →ₗ[𝕜] F).detLineCongr e₁ e₂ (comp_eq_of_coprod_comp_eq hΨ hΨ₁)
        (detLineStabilizationEquiv D₁ D₂ h t) := by
  have hD := comp_eq_of_coprod_comp_eq hΨ hΨ₁
  set eD := Submodule.Quotient.equiv _ _ e₂ ((D₁ : E →ₗ[𝕜] F).map_range_eq_range_of_comp_eq
    e₁.surjective hD)
  have hcoker : finrank 𝕜 (F' ⧸ D₁'.range) = finrank 𝕜 (F ⧸ D₁.range) := eD.finrank_eq.symm
  have hsign : (-1 : 𝕜) ^ (finrank 𝕜 (F' ⧸ D₁'.range) * finrank 𝕜 Λ') =
      (-1) ^ (finrank 𝕜 (F ⧸ D₁.range) * finrank 𝕜 Λ) := by
    rw [hcoker, eΛ.finrank_eq]
  rw [detLineStabilizationEquiv_apply, detLineStabilizationEquiv_apply, map_smul, hsign]
  congr 1
  rw [detLineCoprodEquiv_def, detLineCoprodEquiv_def]
  have h' := surjective_coprod_of_coprod_comp_eq hΨ h
  refine (TauCeti.detLineFourTermEquiv_congr (kerCoprodHom_injective D₁ D₂)
    (exact_kerCoprodHom_parameterProj D₁ D₂) (exact_parameterProj_parameterToCoker D₁ D₂)
    ((parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).2 h)
    (kerCoprodHom_injective D₁' D₂') (exact_kerCoprodHom_parameterProj D₁' D₂')
    (exact_parameterProj_parameterToCoker D₁' D₂')
    ((parameterToCoker_surjective_iff_coprod_surjective D₁' D₂').2 h')
    (e₁.ofSubmodules _ _ ((D₁ : E →ₗ[𝕜] F).map_ker_eq_ker_of_comp_eq e₁.surjective
      e₂.injective hD)) _ eΛ eD ?_ ?_ ?_ t).trans ?_
  · exact LinearMap.ext fun x ↦ Subtype.ext (by simp [hΨ₁])
  · exact LinearMap.ext fun y ↦ by simp [hΨ₂]
  · refine LinearMap.ext fun l ↦ ?_
    have hl := LinearMap.congr_fun hΨ (0, l)
    have h2 := hΨ₂ (0, l)
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, coe_coe,
      coprod_apply, map_zero, zero_add] at hl h2
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      parameterToCoker_apply, eD, Submodule.Quotient.equiv_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, Submodule.Quotient.eq, ← h2, ← hl]
    exact ⟨-(Ψ (0, l)).1, by simp⟩
  · -- `LinearMap.detLineCongr` is the tensor product of the transports of kernel and cokernel.
    refine congrFun (congrArg DFunLike.coe (LinearEquiv.toLinearMap_injective
      (TensorProduct.ext' fun x φ ↦ ?_))) _
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, TensorProduct.congr_tmul,
      LinearMap.detLineCongr_tmul]
    rfl

end Congr

section ChartCongr

variable {𝕜 E Λ F G E' Λ' F' G' : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [AddCommGroup Λ'] [Module 𝕜 Λ'] [TopologicalSpace Λ'] [AddCommGroup F'] [Module 𝕜 F']
  [TopologicalSpace F'] [ContinuousAdd F'] [AddCommGroup G'] [Module 𝕜 G'] [TopologicalSpace G']
  [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 Λ'] [FiniteDimensional 𝕜 G']
  {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {D₁' : E' →L[𝕜] F'} {D₂' : Λ' →L[𝕜] F'}
  {q : E × Λ →L[𝕜] G} {q' : E' × Λ' →L[𝕜] G'}
  {e₁ : E ≃ₗ[𝕜] E'} {e₂ : F ≃ₗ[𝕜] F'} {eΛ : Λ ≃ₗ[𝕜] Λ'} {Ψ : (E × Λ) ≃ₗ[𝕜] (E' × Λ')}

/-- **Naturality of kernel charts.** In the setting of
`ContinuousLinearMap.detLineStabilizationEquiv_congr`, let `(D₂, q)` and `(D₂', q')` be kernel
charts of `D₁` and `D₁'`, and let `eG : G ≃ G'` match the kernel coordinates along `Ψ` on the
stabilized kernel. Then the two charts intertwine the transport of determinant lines along the
square formed by `e₁` and `e₂` with the isomorphism `det G ⊗ (det Λ)^* ≃ det G' ⊗ (det Λ')^*`
induced by `eG` and `eΛ`. -/
theorem detLineChartEquiv_detLineCongr
    (hΨ : (D₁'.coprod D₂' : E' × Λ' →ₗ[𝕜] F') ∘ₗ Ψ.toLinearMap =
      e₂.toLinearMap ∘ₗ (D₁.coprod D₂ : E × Λ →ₗ[𝕜] F))
    (hΨ₁ : ∀ x, Ψ (x, 0) = (e₁ x, 0)) (hΨ₂ : ∀ y, (Ψ y).2 = eΛ y.2) (eG : G ≃ₗ[𝕜] G')
    (hq : ∀ y ∈ (D₁.coprod D₂).ker, q' (Ψ y) = eG (q y))
    (hinv : ((D₁.coprod D₂).prod q).IsInvertible)
    (hinv' : ((D₁'.coprod D₂').prod q').IsInvertible) (y : (D₁ : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv D₁' D₂' q' hinv'
        ((D₁ : E →ₗ[𝕜] F).detLineCongr e₁ e₂ (comp_eq_of_coprod_comp_eq hΨ hΨ₁) y) =
      TensorProduct.congr eG.detLineCongr eΛ.detLineCongr.symm.dualMap
        (detLineChartEquiv D₁ D₂ q hinv y) := by
  have := finiteDimensional_ker_of_isInvertible_prod_coprod hinv
  have := finiteDimensional_ker_of_isInvertible_prod_coprod hinv'
  have hs := surjective_of_isInvertible_prod hinv
  obtain ⟨t, rfl⟩ := (detLineStabilizationEquiv D₁ D₂ hs).surjective y
  rw [← detLineStabilizationEquiv_congr hΨ hΨ₁ hΨ₂ hs t,
    detLineChartEquiv_detLineStabilizationEquiv, detLineChartEquiv_detLineStabilizationEquiv]
  induction t using TensorProduct.inductionOn with
  | tmul a φ =>
    rw [TensorProduct.congr_tmul, LinearEquiv.rTensor_tmul, LinearEquiv.rTensor_tmul,
      TensorProduct.congr_tmul]
    congr 1
    rw [← LinearEquiv.trans_apply, ← LinearEquiv.trans_apply, ← LinearEquiv.detLineCongr_trans,
      ← LinearEquiv.detLineCongr_trans]
    -- Both composites read a stabilized kernel vector `k` as `q' (Ψ k) = eG (q k)`.
    refine congrArg (fun e ↦ LinearEquiv.detLineCongr e a) (LinearEquiv.ext fun k ↦ ?_)
    simp [hq k k.2]
  | add a b ha hb => rw [LinearEquiv.map_add, LinearEquiv.map_add, ha, hb, LinearEquiv.map_add,
      LinearEquiv.map_add]

/-- **Changing the kernel coordinate.** Two kernel charts of `T` with the same stabilizer `D₂`
differ by the determinant of the change of coordinate `q' ∘ kerSection q` of `G`. -/
theorem detLineChartEquiv_apply_eq_det_smul (h : ((D₁.coprod D₂).prod q).IsInvertible)
    {q₁ : E × Λ →L[𝕜] G} (h₁ : ((D₁.coprod D₂).prod q₁).IsInvertible)
    (y : (D₁ : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv D₁ D₂ q₁ h₁ y =
      (q₁ ∘L (D₁.coprod D₂).kerSection q).det • detLineChartEquiv D₁ D₂ q h y := by
  set eG : G ≃ₗ[𝕜] G := ((D₁.coprod D₂).kerEquivOfProd q h).toLinearEquiv.trans
    ((D₁.coprod D₂).kerEquivOfProd q₁ h₁).toLinearEquiv.symm with heG
  have hdet : LinearMap.det (eG : G →ₗ[𝕜] G) = (q₁ ∘L (D₁.coprod D₂).kerSection q).det := by
    congr 1
    exact LinearMap.ext fun g ↦ by simp [heG]
  have := detLineChartEquiv_detLineCongr (D₁' := D₁) (D₂' := D₂) (e₁ := LinearEquiv.refl 𝕜 E)
    (e₂ := LinearEquiv.refl 𝕜 F) (eΛ := LinearEquiv.refl 𝕜 Λ) (Ψ := LinearEquiv.refl 𝕜 (E × Λ))
    (LinearMap.ext fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) eG
    (fun z hz ↦ by simp [heG, kerSection_apply_of_mem_ker h hz]) h h₁ y
  rwa [LinearMap.detLineCongr_refl, LinearEquiv.refl_apply,
    LinearEquiv.tensorCongr_detLineCongr_apply_eq_det_smul, hdet, LinearEquiv.refl_toLinearMap,
    LinearMap.det_id, inv_one, mul_one] at this

variable [ContinuousAdd Λ] in
/-- **Changing the stabilizer.** Let `D₂' = D₂ + (D₁.coprod D₂) ∘ L` for a map `L : Λ → E × Λ`
with values in the kernel of the coordinate `q`. Then the kernel charts `(D₂', q)` and `(D₂, q)` of
`D₁` differ by the determinant of the induced change `1 + snd ∘ L` of the stabilizing space. -/
theorem detLineChartEquiv_apply_eq_det_smul_of_comp_eq {D₂' : Λ →L[𝕜] F} {L : Λ →L[𝕜] E × Λ}
    (hL : ∀ l, D₁.coprod D₂ (L l) = D₂' l - D₂ l) (hqL : ∀ l, q (L l) = 0)
    (h : ((D₁.coprod D₂).prod q).IsInvertible) (h' : ((D₁.coprod D₂').prod q).IsInvertible)
    (y : (D₁ : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv D₁ D₂' q h' y =
      (ContinuousLinearMap.id 𝕜 Λ + snd 𝕜 E Λ ∘L L).det • detLineChartEquiv D₁ D₂ q h y := by
  set Φ := ContinuousLinearMap.id 𝕜 Λ + snd 𝕜 E Λ ∘L L with hΦ_def
  -- `Ψ (u, l) = (u, l) + L l` carries the kernel of `(D₁.coprod D₂', q)` into that of
  -- `(D₁.coprod D₂, q)`, so `Φ` is injective.
  have hΨL (z : E × Λ) : (D₁.coprod D₂ (z + L z.2), q (z + L z.2)) =
      (D₁.coprod D₂' z, q z) := by
    refine Prod.ext ?_ ?_
    · simp only [map_add, hL, coprod_apply]
      abel
    · simp [hqL]
  have hΦ : LinearMap.det (Φ : Λ →ₗ[𝕜] Λ) ≠ 0 := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot']
    intro l hl
    have hl' : l + (L l).2 = 0 := by simpa [hΦ_def] using hl
    have hz : ((D₁.coprod D₂').prod q) (-(L l).1, l) = 0 := by
      have h0 : (-(L l).1, l) + L (-(L l).1, l).2 = 0 := Prod.ext (neg_add_cancel _) hl'
      rw [prod_apply, ← hΨL, h0, map_zero, map_zero, Prod.mk_zero_zero]
    obtain ⟨e, he⟩ := h'
    rw [← he, ContinuousLinearEquiv.coe_coe, e.map_eq_zero_iff] at hz
    exact congrArg Prod.snd hz
  set eΛ : Λ ≃ₗ[𝕜] Λ := (Φ : Λ →ₗ[𝕜] Λ).equivOfDetNeZero hΦ with heΛ
  set Ψ : (E × Λ) ≃ₗ[𝕜] (E × Λ) := (LinearEquiv.prodComm 𝕜 E Λ).trans
    ((eΛ.skewProd (LinearEquiv.refl 𝕜 E) (fst 𝕜 E Λ ∘L L : Λ →L[𝕜] E)).trans
      (LinearEquiv.prodComm 𝕜 Λ E)) with hΨ_def
  have hΨ (z : E × Λ) : Ψ z = z + L z.2 := by
    ext <;> simp [hΨ_def, heΛ, hΦ_def]
  have := detLineChartEquiv_detLineCongr (D₁' := D₁) (D₂' := D₂) (q' := q)
    (e₁ := LinearEquiv.refl 𝕜 E) (e₂ := LinearEquiv.refl 𝕜 F) (eΛ := eΛ) (Ψ := Ψ)
    (LinearMap.ext fun z ↦ by simpa [hΨ] using congrArg Prod.fst (hΨL z))
    (fun u ↦ by simp [hΨ]) (fun z ↦ by simp [hΨ, heΛ, hΦ_def]) (LinearEquiv.refl 𝕜 G)
    (fun z _ ↦ by simp [hΨ, hqL]) h' h y
  rw [LinearMap.detLineCongr_refl, LinearEquiv.refl_apply,
    LinearEquiv.tensorCongr_detLineCongr_apply_eq_det_smul, LinearEquiv.refl_toLinearMap,
    LinearMap.det_id, one_mul] at this
  have hdet : LinearMap.det (eΛ : Λ →ₗ[𝕜] Λ) = Φ.det := by simp [heΛ]
  rw [hdet] at this
  exact (inv_smul_eq_iff₀ (hdet ▸ hΦ)).mp this.symm

end ChartCongr

section Conjugate

variable {𝕜 E Λ F G E' F' : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E'] [AddCommGroup F']
  [Module 𝕜 F'] [TopologicalSpace F'] [ContinuousAdd F'] [FiniteDimensional 𝕜 Λ]
  [FiniteDimensional 𝕜 G] {T : E →L[𝕜] F} {S : E' →L[𝕜] F'} {e₁ : E ≃L[𝕜] E'} {e₂ : F ≃L[𝕜] F'}
  {D₂ : Λ →L[𝕜] F'} {q : E' × Λ →L[𝕜] G}

omit [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G] in
/-- A kernel chart `(D₂, q)` of `S`, for `S ∘ e₁ = e₂ ∘ T`, is valid when the kernel chart
`(e₂⁻¹ ∘ D₂, q ∘ (e₁ × 1))` of `T` is. -/
theorem isInvertible_prod_coprod_of_comp_eq
    (h : (S : E' →ₗ[𝕜] F') ∘ₗ e₁.toLinearEquiv.toLinearMap =
      e₂.toLinearEquiv.toLinearMap ∘ₗ (T : E →ₗ[𝕜] F))
    (hT : ((T.coprod ((e₂.symm : F' →L[𝕜] F) ∘L D₂)).prod
      (q ∘L ((e₁ : E →L[𝕜] E') ∘L fst 𝕜 E Λ).prod (snd 𝕜 E Λ))).IsInvertible) :
    ((S.coprod D₂).prod q).IsInvertible := by
  have hS (u : E') : S u = e₂ (T (e₁.symm u)) := by
    simpa using LinearMap.congr_fun h (e₁.symm u)
  have : (S.coprod D₂).prod q =
      ((e₂.prodCongr (ContinuousLinearEquiv.refl 𝕜 G) : F × G →L[𝕜] F' × G) ∘L
        (T.coprod ((e₂.symm : F' →L[𝕜] F) ∘L D₂)).prod
          (q ∘L ((e₁ : E →L[𝕜] E') ∘L fst 𝕜 E Λ).prod (snd 𝕜 E Λ))) ∘L
      ((e₁.prodCongr (ContinuousLinearEquiv.refl 𝕜 Λ)).symm : E' × Λ →L[𝕜] E × Λ) := by
    ext z <;> simp [hS]
  rw [this, isInvertible_comp_equiv, isInvertible_equiv_comp]
  exact hT

/-- **Conjugate kernel charts.** For `S ∘ e₁ = e₂ ∘ T`, the kernel chart `(D₂, q)` of `S` reads
the transport of `y ∈ det T` along the square as the kernel chart `(e₂⁻¹ ∘ D₂, q ∘ (e₁ × 1))` of
`T` reads `y`. -/
theorem detLineChartEquiv_detLineCongr_of_comp_eq
    (h : (S : E' →ₗ[𝕜] F') ∘ₗ e₁.toLinearEquiv.toLinearMap =
      e₂.toLinearEquiv.toLinearMap ∘ₗ (T : E →ₗ[𝕜] F))
    (hT : ((T.coprod ((e₂.symm : F' →L[𝕜] F) ∘L D₂)).prod
      (q ∘L ((e₁ : E →L[𝕜] E') ∘L fst 𝕜 E Λ).prod (snd 𝕜 E Λ))).IsInvertible)
    (y : (T : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv S D₂ q (isInvertible_prod_coprod_of_comp_eq h hT)
        ((T : E →ₗ[𝕜] F).detLineCongr e₁.toLinearEquiv e₂.toLinearEquiv h y) =
      detLineChartEquiv T ((e₂.symm : F' →L[𝕜] F) ∘L D₂)
        (q ∘L ((e₁ : E →L[𝕜] E') ∘L fst 𝕜 E Λ).prod (snd 𝕜 E Λ)) hT y := by
  have hS (u : E) : S (e₁ u) = e₂ (T u) := by simpa using LinearMap.congr_fun h u
  have := detLineChartEquiv_detLineCongr (e₁ := e₁.toLinearEquiv) (e₂ := e₂.toLinearEquiv)
    (Ψ := e₁.toLinearEquiv.prodCongr (LinearEquiv.refl 𝕜 Λ)) (eΛ := LinearEquiv.refl 𝕜 Λ)
    (LinearMap.ext fun z ↦ by simp [hS])
    (fun _ ↦ rfl) (fun _ ↦ rfl) (LinearEquiv.refl 𝕜 G) (fun z _ ↦ by simp) hT
    (isInvertible_prod_coprod_of_comp_eq h hT) y
  rw [LinearEquiv.tensorCongr_detLineCongr_apply_eq_det_smul] at this
  simpa using this

end Conjugate

end ContinuousLinearMap


namespace ContinuousLinearMap

section Moving

open Filter Topology

variable {E F Λ G X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace X]
  {T : X → E →L[ℝ] F} {D₂ : X → Λ →L[ℝ] F} {q : X → E × Λ →L[ℝ] G} {s : Set X} {x₀ : X}

/-- **Kernel charts with moving data.** Let `T` be a family of operators and `(D₂ x, q x)` a
kernel chart whose stabilizer and coordinate depend on the parameter, all continuous within `s`
at `x₀`. Near `x₀` the chart with the moving data reads the determinant line of `T x` as a
positive multiple of the chart with the data frozen at `x₀`. -/
theorem eventually_detLineChartEquiv_eq_smul (hT : ContinuousWithinAt T s x₀)
    (hD₂ : ContinuousWithinAt D₂ s x₀) (hq : ContinuousWithinAt q s x₀)
    (h₀ : (((T x₀).coprod (D₂ x₀)).prod (q x₀)).IsInvertible) :
    ∀ᶠ x in 𝓝[s] x₀, ∃ (h : (((T x).coprod (D₂ x)).prod (q x)).IsInvertible)
      (h' : (((T x).coprod (D₂ x₀)).prod (q x₀)).IsInvertible) (c : ℝ), 0 < c ∧
      ∀ y, detLineChartEquiv (T x) (D₂ x) (q x) h y =
        c • detLineChartEquiv (T x) (D₂ x₀) (q x₀) h' y := by
  have : CompleteSpace Λ := FiniteDimensional.completeSpace ℝ Λ
  have hA : ContinuousWithinAt (fun x ↦ (T x).coprod (D₂ x)) s x₀ :=
    hT.continuousLinearMapCoprod hD₂
  have hA₀ : ContinuousWithinAt (fun x ↦ (T x).coprod (D₂ x₀)) s x₀ :=
    hT.continuousLinearMapCoprod continuousWithinAt_const
  have hprod {B : X → E × Λ →L[ℝ] F} {r : X → E × Λ →L[ℝ] G} (hB : ContinuousWithinAt B s x₀)
      (hr : ContinuousWithinAt r s x₀) (hBr : ((B x₀).prod (r x₀)).IsInvertible) :
      ∀ᶠ x in 𝓝[s] x₀, ((B x).prod (r x)).IsInvertible :=
    ((prodL ℝ).continuous.continuousAt.comp_continuousWithinAt (hB.prodMk hr)).tendsto.eventually
      hBr.eventually_nhds
  -- The three pairs of the comparison are invertible near `x₀`.
  have ev₀ := hprod hA₀ continuousWithinAt_const h₀
  have ev₁ := hprod hA continuousWithinAt_const h₀
  have ev₂ := hprod hA hq h₀
  -- Moving the stabilizer from `D₂ x₀` to `D₂ x` is the cutoff change `D₂ x = D₂ x₀ + A₀ ∘ L x`,
  -- where `L x` is normalized by `q x₀`; it acts on the stabilizer by `Φ x = 1 + snd ∘ L x`.
  set L : X → Λ →L[ℝ] E × Λ :=
    fun x ↦ (q x₀).kerSection ((T x).coprod (D₂ x₀)) ∘L (D₂ x - D₂ x₀) with hL_def
  set Φ : X → Λ →L[ℝ] Λ := fun x ↦ ContinuousLinearMap.id ℝ Λ + snd ℝ E Λ ∘L L x with hΦ_def
  have hL : ContinuousWithinAt L s x₀ :=
    ((contDiffAt_kerSection (n := 0)
      (isInvertible_prod_comm.mp h₀)).continuousAt.comp_continuousWithinAt
        (f := fun x ↦ (q x₀, (T x).coprod (D₂ x₀))) (continuousWithinAt_const.prodMk hA₀)).clm_comp
      (hD₂.sub continuousWithinAt_const)
  have hΦ : ContinuousWithinAt (fun x ↦ (Φ x).det) s x₀ :=
    continuous_det.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_const.add (continuousWithinAt_const.clm_comp hL))
  have hΦ₀ : (Φ x₀).det = 1 := by
    simp [hΦ_def, hL_def, ContinuousLinearMap.det, LinearMap.det_id]
  -- Moving the coordinate from `q x₀` to `q x` acts on `G` by `K x = q x ∘ kerSection`.
  set K : X → G →L[ℝ] G := fun x ↦ q x ∘L ((T x).coprod (D₂ x)).kerSection (q x₀)
  have hK : ContinuousWithinAt (fun x ↦ (K x).det) s x₀ :=
    continuous_det.continuousAt.comp_continuousWithinAt (hq.clm_comp
      ((contDiffAt_kerSection (n := 0) h₀).continuousAt.comp_continuousWithinAt
        (f := fun x ↦ ((T x).coprod (D₂ x), q x₀)) (hA.prodMk continuousWithinAt_const)))
  have hK₀ : (K x₀).det = 1 := by
    have : K x₀ = ContinuousLinearMap.id ℝ G :=
      ContinuousLinearMap.ext fun g ↦ apply_kerSection_right h₀ g
    rw [this, ContinuousLinearMap.det, coe_id, LinearMap.det_id]
  have evΦ := hΦ.tendsto.eventually (lt_mem_nhds (hΦ₀ ▸ one_pos : (0 : ℝ) < (Φ x₀).det))
  have evK := hK.tendsto.eventually (lt_mem_nhds (hK₀ ▸ one_pos : (0 : ℝ) < (K x₀).det))
  filter_upwards [ev₀, ev₁, ev₂, evΦ, evK] with x h0x h1x h2x hΦx hKx
  refine ⟨h2x, h0x, (K x).det * (Φ x).det, mul_pos hKx hΦx, fun y ↦ ?_⟩
  rw [detLineChartEquiv_apply_eq_det_smul h1x h2x,
    detLineChartEquiv_apply_eq_det_smul_of_comp_eq (L := L x)
      (fun l ↦ apply_kerSection_right (isInvertible_prod_comm.mp h0x) _)
      (fun l ↦ apply_kerSection _) h0x h1x, smul_smul]

end Moving

end ContinuousLinearMap

namespace TauCeti

open Filter Set Topology ContinuousLinearMap

section Coherent

variable {E F E' F' X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F'] [TopologicalSpace X]
  {T : X → E →L[ℝ] F} {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X} {x₀ : X}

variable {S : X → E' →L[ℝ] F'} {e₁ : X → E ≃L[ℝ] E'} {e₂ : X → F ≃L[ℝ] F'}

/-- **Naturality of coherence.** Let `S x ∘ e₁ x = e₂ x ∘ T x` for families of isomorphisms `e₁`
of the sources and `e₂` of the targets, continuous within `s` at `x₀`. If `v` is coherent for `T`
within `s` at `x₀`, then its transport along the squares, `LinearMap.detLineCongr`, is coherent
for `S`. -/
theorem IsDetLineCoherentWithinAt.detLineCongr (hv : IsDetLineCoherentWithinAt T v s x₀)
    (hT : ContinuousWithinAt T s x₀) (hF : IsFredholm (T x₀))
    (he₁ : ContinuousWithinAt (fun x ↦ (e₁ x : E →L[ℝ] E')) s x₀)
    (he₂ : ContinuousWithinAt (fun x ↦ (e₂ x : F →L[ℝ] F')) s x₀)
    (h : ∀ x, (S x : E' →ₗ[ℝ] F') ∘ₗ (e₁ x).toLinearEquiv.toLinearMap =
      (e₂ x).toLinearEquiv.toLinearMap ∘ₗ (T x : E →ₗ[ℝ] F)) :
    IsDetLineCoherentWithinAt S (fun x ↦ (T x : E →ₗ[ℝ] F).detLineCongr (e₁ x).toLinearEquiv
      (e₂ x).toLinearEquiv (h x) (v x)) s x₀ := by
  have hS_eq (x : X) : S x = (e₂ x : F →L[ℝ] F') ∘L T x ∘L ((e₁ x).symm : E' →L[ℝ] E) := by
    ext u
    simpa using LinearMap.congr_fun (h x) ((e₁ x).symm u)
  have he₁' : ContinuousWithinAt (fun x ↦ ((e₁ x).symm : E' →L[ℝ] E)) s x₀ := by
    simpa only [Function.comp_def, inverse_equiv] using
      (contDiffAt_map_inverse (n := 0) (e₁ x₀)).continuousAt.comp_continuousWithinAt
        (f := fun x ↦ (e₁ x : E →L[ℝ] E')) he₁
  have he₂' : ContinuousWithinAt (fun x ↦ ((e₂ x).symm : F' →L[ℝ] F)) s x₀ := by
    simpa only [Function.comp_def, inverse_equiv] using
      (contDiffAt_map_inverse (n := 0) (e₂ x₀)).continuousAt.comp_continuousWithinAt
        (f := fun x ↦ (e₂ x : F →L[ℝ] F')) he₂
  have hS : ContinuousWithinAt S s x₀ := by
    simpa only [← hS_eq] using he₂.clm_comp (hT.clm_comp he₁')
  have hFS : IsFredholm (S x₀) :=
    (isFredholm_iff_of_comp_eq (e₁ x₀) (e₂ x₀) (by rw [hS_eq]; ext; simp)).1 hF
  -- A kernel chart `(S₀, q₀)` of `T x₀`, transported to a kernel chart `(Dₛ, qₛ)` of `S x₀`.
  -- Read on `T x`, this chart of `S x` has the moving data `(D₂ x, q x)`.
  obtain ⟨S₀, hS₀, G, hG, q₀, U, -, hxU, hinv⟩ := hF.exists_isOpen_kernelChart
  set Dₛ : S₀ →L[ℝ] F' := (e₂ x₀ : F →L[ℝ] F') ∘L S₀.subtypeL with hDₛ_def
  set qₛ : E' × S₀ →L[ℝ] G :=
    q₀ ∘L (((e₁ x₀).symm : E' →L[ℝ] E) ∘L fst ℝ E' S₀).prod (snd ℝ E' S₀) with hqₛ_def
  set D₂ : X → S₀ →L[ℝ] F := fun x ↦ ((e₂ x).symm : F' →L[ℝ] F) ∘L Dₛ with hD₂_def
  set q : X → E × S₀ →L[ℝ] G :=
    fun x ↦ qₛ ∘L ((e₁ x : E →L[ℝ] E') ∘L fst ℝ E S₀).prod (snd ℝ E S₀) with hq_def
  have hD₂ : ContinuousWithinAt D₂ s x₀ := he₂'.clm_comp continuousWithinAt_const
  have hq : ContinuousWithinAt q s x₀ := continuousWithinAt_const.clm_comp
    ((prodL ℝ).continuous.continuousAt.comp_continuousWithinAt
      (f := fun x ↦ ((e₁ x : E →L[ℝ] E') ∘L fst ℝ E S₀, snd ℝ E S₀))
      ((he₁.clm_comp continuousWithinAt_const).prodMk continuousWithinAt_const))
  have h₀ : (((T x₀).coprod (D₂ x₀)).prod (q x₀)).IsInvertible := by
    have hD₂₀ : D₂ x₀ = S₀.subtypeL := by ext; simp [hD₂_def, hDₛ_def]
    have hq₀ : q x₀ = q₀ := by ext <;> simp [hq_def, hqₛ_def]
    rw [hD₂₀, hq₀]
    exact hinv _ hxU
  refine isDetLineCoherentWithinAt_of_eventually_sameRay hS hFS
    ((LinearEquiv.map_ne_zero_iff _).2 hv.ne_zero) (isInvertible_prod_coprod_of_comp_eq (h x₀) h₀)
    ?_
  filter_upwards [hv.eventually_sameRay hT h₀, eventually_detLineChartEquiv_eq_smul hT hD₂ hq h₀]
    with x hev₁ hev₂
  obtain ⟨h₁, hsr⟩ := hev₁
  obtain ⟨hx, h', c, hc, hcx⟩ := hev₂
  refine ⟨isInvertible_prod_coprod_of_comp_eq (h x) hx, ?_⟩
  have key := hsr.pos_smul_left hc
  rw [← hcx] at key
  rwa [detLineChartEquiv_detLineCongr_of_comp_eq (h x) hx,
    detLineChartEquiv_detLineCongr_of_comp_eq (h x₀) h₀]

/-- **Naturality of continuous orientations.** Transporting a family coherent on `s` along
squares `S x ∘ e₁ x = e₂ x ∘ T x` of families of isomorphisms continuous on `s` gives a family
coherent on `s`. -/
theorem IsDetLineCoherentOn.detLineCongr (hv : IsDetLineCoherentOn T v s) (hT : ContinuousOn T s)
    (hF : ∀ x ∈ s, IsFredholm (T x)) (he₁ : ContinuousOn (fun x ↦ (e₁ x : E →L[ℝ] E')) s)
    (he₂ : ContinuousOn (fun x ↦ (e₂ x : F →L[ℝ] F')) s)
    (h : ∀ x, (S x : E' →ₗ[ℝ] F') ∘ₗ (e₁ x).toLinearEquiv.toLinearMap =
      (e₂ x).toLinearEquiv.toLinearMap ∘ₗ (T x : E →ₗ[ℝ] F)) :
    IsDetLineCoherentOn S (fun x ↦ (T x : E →ₗ[ℝ] F).detLineCongr (e₁ x).toLinearEquiv
      (e₂ x).toLinearEquiv (h x) (v x)) s :=
  isDetLineCoherentOn_iff.2 fun x hx ↦ (isDetLineCoherentOn_iff.1 hv x hx).detLineCongr (hT x hx)
    (hF x hx) (he₁ x hx) (he₂ x hx) h

end Coherent

section Transport

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  {T : ℝ → E →L[ℝ] F} {S : ℝ → E' →L[ℝ] F'} {e₁ : ℝ → E ≃L[ℝ] E'} {e₂ : ℝ → F ≃L[ℝ] F'}
  {a b : ℝ}

/-- **Naturality of orientation transport.** Let `S t ∘ e₁ t = e₂ t ∘ T t` along paths of
isomorphisms `e₁` of the sources and `e₂` of the targets, continuous between `a` and `b`. Then
transporting an orientation along `S` from `a` to `b` is transporting it along `T`, conjugated by
the transports of determinant lines along the squares at `a` and at `b`. -/
theorem detLineOrientationTransport_map_detLineCongr (hT : ContinuousOn T (uIcc a b))
    (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) (hS : ContinuousOn S (uIcc a b))
    (hFS : ∀ t ∈ uIcc a b, IsFredholm (S t))
    (he₁ : ContinuousOn (fun t ↦ (e₁ t : E →L[ℝ] E')) (uIcc a b))
    (he₂ : ContinuousOn (fun t ↦ (e₂ t : F →L[ℝ] F')) (uIcc a b))
    (h : ∀ t, (S t : E' →ₗ[ℝ] F') ∘ₗ (e₁ t).toLinearEquiv.toLinearMap =
      (e₂ t).toLinearEquiv.toLinearMap ∘ₗ (T t : E →ₗ[ℝ] F))
    (o : Module.Ray ℝ (T a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hS hFS (Module.Ray.map ((T a : E →ₗ[ℝ] F).detLineCongr
        (e₁ a).toLinearEquiv (e₂ a).toLinearEquiv (h a)) o) =
      Module.Ray.map ((T b : E →ₗ[ℝ] F).detLineCongr (e₁ b).toLinearEquiv (e₂ b).toLinearEquiv
        (h b)) (detLineOrientationTransport a b hT hF o) := by
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc hv₀
  rw [Module.Ray.map_apply, detLineOrientationTransport_rayOfNeZero hT hF hv,
    Module.Ray.map_apply]
  exact detLineOrientationTransport_rayOfNeZero hS hFS (hv.detLineCongr hT hF he₁ he₂ h)

/-- **Transport along a path of target isomorphisms.** For a Fredholm operator `T₀` and a path
`A` of isomorphisms of its target, transporting an orientation along `t ↦ A t ∘ T₀` from `a` to
`b` is the transport of determinant lines along `A b ∘ (A a)⁻¹`: both are read off from `T₀`
through the transports along the squares `(A t ∘ T₀) ∘ 1 = A t ∘ T₀`. -/
theorem detLineOrientationTransport_comp_left {T₀ : E →L[ℝ] F} (hT₀ : IsFredholm T₀)
    {A : ℝ → F ≃L[ℝ] F'} (hA : ContinuousOn (fun t ↦ (A t : F →L[ℝ] F')) (uIcc a b))
    (o : Module.Ray ℝ (T₀ : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun t ↦ (A t : F →L[ℝ] F') ∘L T₀) a b
        (hA.clm_comp continuousOn_const) (fun t _ ↦ hT₀.equiv_comp (A t))
        (Module.Ray.map ((T₀ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
          (A a).toLinearEquiv (LinearMap.ext fun _ ↦ rfl)) o) =
      Module.Ray.map ((T₀ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E) (A b).toLinearEquiv
        (LinearMap.ext fun _ ↦ rfl)) o := by
  have := detLineOrientationTransport_map_detLineCongr (T := fun _ ↦ T₀)
    (S := fun t ↦ (A t : F →L[ℝ] F') ∘L T₀) (e₁ := fun _ ↦ ContinuousLinearEquiv.refl ℝ E)
    (e₂ := A) continuousOn_const (fun _ _ ↦ hT₀) (hA.clm_comp continuousOn_const)
    (fun t _ ↦ hT₀.equiv_comp (A t)) continuousOn_const hA (fun _ ↦ LinearMap.ext fun _ ↦ rfl) o
  rwa [detLineOrientationTransport_const hT₀, id] at this

end Transport

end TauCeti
