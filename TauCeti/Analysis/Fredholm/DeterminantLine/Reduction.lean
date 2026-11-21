/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
public import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Fredholm.ClosedRange

/-!
# Finite-dimensional reductions of Fredholm determinant lines

Let `T : E →L[ℝ] F` be an operator between real Banach spaces and `A : V →L[ℝ] W` a linear map of
finite-dimensional spaces with isomorphic kernels and cokernels,
`eK : ker T ≃ ker A` and `eC : coker T ≃ coker A`. The pair identifies the determinant lines,
`ρ = LinearMap.detLineCongrKerCoker eK eC : det T ≃ det A`. For instance, the operator
`ζ ↦ ζ' - S ζ` on loops has the kernel and cokernel of `1 - P`, `P` its return map. This file
shows that `ρ` is compatible with the kernel charts through which the determinant lines of a
family of Fredholm operators are compared, as soon as it comes from a *reduction*: a map
`r : E →L[ℝ] V` onto `V`, a stabilization `σ : W →L[ℝ] F` and an automorphism `M` of `W` with

* `eK k = r k` on the kernel of `T`;
* `eC [σ w] = [M w]` on the cokernel classes of the stabilizing directions;
* `A (r e) + M w = 0` whenever `T e + σ w = 0`.

Under these conditions, `T` has the kernel chart with stabilizer `σ` and coordinate `(e, w) ↦ r e`
(`ContinuousLinearMap.isInvertible_prod_coprod_comp_fst`), and every linear map `A` of
finite-dimensional spaces has the kernel chart with stabilizer the identity of `W` and coordinate
`(v, w) ↦ v` (`ContinuousLinearMap.isInvertible_prod_coprod_id_fst`). Both charts take values in
the line `det V ⊗ (det W)^*`, and the first reads `v ∈ det T` as `det M` times the reading of
`ρ v` in the second
(`ContinuousLinearMap.detLineChartEquiv_eq_det_smul_detLineChartEquiv_detLineCongrKerCoker`). The
proof compares the exact sequences `0 → ker T → ker (T.coprod σ) → W → coker T → 0` and
`0 → ker A → ker (A.coprod 1) → W → coker A → 0` through `eK`, the identification of the stabilized
kernels by their coordinates in `V`, `M` and `eC`, and uses the naturality of the isomorphism
`det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*` of a four-term exact sequence
(`TauCeti.detLineFourTermEquiv_congr`). The Koszul signs of the two normalized stabilizations
agree because the cokernels have the same dimension.

Consequently reductions transport coherent families: if, for families `T x`, `A x`, `M x`
continuous at `x₀` with `M x₀` invertible, the conditions hold for every `x`, then
`x ↦ ρₓ⁻¹ (u x)` is coherent for `T` within `s` at `x₀` whenever `u` is coherent for `A`
(`TauCeti.IsDetLineCoherentWithinAt.detLineCongrKerCoker_symm`). The operator `T x₀` is then
Fredholm, since its kernel and cokernel are those of `A x₀`, and the factor `det (M x)` keeps the
sign of `det (M x₀)` near `x₀`, so it does not change the orientations.

## Main results

* `ContinuousLinearMap.isInvertible_prod_coprod_comp_fst`: a reduction gives a kernel chart of
  `T`.
* `ContinuousLinearMap.detLineChartEquiv_eq_det_smul_detLineChartEquiv_detLineCongrKerCoker`: the
  kernel charts of `T` and `A` are related by `ρ` and the factor `det M`.
* `TauCeti.IsDetLineCoherentWithinAt.detLineCongrKerCoker_symm`: reductions continuous in a
  parameter carry coherent families for `A` to coherent families for `T`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open Module TensorProduct

open LinearMap (ker range)

namespace ContinuousLinearMap

variable {E F V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-! ### The kernel charts of a reduction -/

/-- The pair `(v, w) ↦ (A v + w, v)` is invertible, so every linear map `A` of finite-dimensional
spaces has the kernel chart stabilizing by the identity of its target, with coordinate the first
factor. -/
theorem isInvertible_prod_coprod_id_fst (A : V →L[ℝ] W) :
    ((A.coprod (ContinuousLinearMap.id ℝ W)).prod (fst ℝ V W)).IsInvertible := by
  refine isInvertible_iff_bijective.2 ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨(y.2, y.1 - A y.2), ?_⟩⟩
  · simp only [prod_apply, coprod_apply, id_apply, coe_fst', Prod.mk.injEq] at hxy
    obtain ⟨h₁, h₂⟩ := hxy
    rw [h₂, add_right_inj] at h₁
    exact Prod.ext h₂ h₁
  · simp

/-- The kernel coordinate of the chart `(id, fst)` of `A` reads a pair `(v, w)` of the stabilized
kernel as `v`; its kernel section sends `v` to `(v, -A v)`. -/
@[simp]
theorem kerSection_coprod_id_fst_apply (A : V →L[ℝ] W) (v : V) :
    (A.coprod (ContinuousLinearMap.id ℝ W)).kerSection (fst ℝ V W) v = (v, -A v) := by
  have h := isInvertible_prod_coprod_id_fst A
  refine h.injective ?_
  rw [prod_apply_kerSection h]
  simp

variable {T : E →L[ℝ] F} {A : V →L[ℝ] W} {r : E →L[ℝ] V} {σ : W →L[ℝ] F} {M : W →L[ℝ] W}
  {eK : ker (T : E →ₗ[ℝ] F) ≃ₗ[ℝ] ker (A : V →ₗ[ℝ] W)}
  {eC : (F ⧸ range (T : E →ₗ[ℝ] F)) ≃ₗ[ℝ] (W ⧸ range (A : V →ₗ[ℝ] W))}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- The pair `(e, w) ↦ (T e + σ w, r e)` of a reduction is injective. -/
private theorem injective_prod_coprod_comp_fst (hM : Function.Injective M)
    (hK : ∀ e w, T e + σ w = 0 → A (r e) + M w = 0) (heK : ∀ k, (eK k : V) = r k) :
    Function.Injective ((T.coprod σ).prod (r ∘L fst ℝ E W)) := by
  refine (injective_iff_map_eq_zero _).2 fun ⟨e, w⟩ h ↦ ?_
  simp only [prod_apply, coprod_apply, comp_apply, coe_fst', Prod.mk_eq_zero] at h
  -- `M w = -A (r e) = 0`, so `w = 0`; then `e` lies in the kernel of `T` and `eK e = r e = 0`.
  have hw : w = 0 := hM (by simpa [h.2] using hK e w h.1)
  subst hw
  have he : e ∈ ker (T : E →ₗ[ℝ] F) := by simpa using h.1
  have h0 : eK ⟨e, he⟩ = 0 := Subtype.ext (by rw [heK]; exact h.2)
  simpa using congrArg Subtype.val ((map_eq_zero_iff eK eK.injective).1 h0)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- Every point of `V` is the coordinate `r e` of a pair `(e, w)` with `T e + σ w = 0`. -/
private theorem exists_coprod_eq_zero_and_eq (hr : Function.Surjective r)
    (hM : Function.Surjective M) (hK : ∀ e w, T e + σ w = 0 → A (r e) + M w = 0)
    (heK : ∀ k, (eK k : V) = r k)
    (heC : ∀ w, eC (Submodule.Quotient.mk (σ w)) = Submodule.Quotient.mk (M w)) (v : V) :
    ∃ e w, T e + σ w = 0 ∧ r e = v := by
  obtain ⟨e₀, rfl⟩ := hr v
  obtain ⟨w, hw⟩ := hM (-A (r e₀))
  -- `T e₀ + σ w` has cokernel class `eC⁻¹ [M w] = eC⁻¹ [-A (r e₀)] = 0`, so it is some `T e₁`.
  have hcl : eC (Submodule.Quotient.mk (T e₀ + σ w)) = 0 := by
    rw [Submodule.Quotient.mk_add, map_add, heC, hw, Submodule.Quotient.mk_neg]
    have h₁ : (Submodule.Quotient.mk (T e₀) : F ⧸ range (T : E →ₗ[ℝ] F)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨e₀, rfl⟩
    have h₂ : (Submodule.Quotient.mk (A (r e₀)) : W ⧸ range (A : V →ₗ[ℝ] W)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨r e₀, rfl⟩
    rw [h₁, h₂, map_zero, neg_zero, add_zero]
  obtain ⟨e₁, he₁⟩ := (Submodule.Quotient.mk_eq_zero _).1
    ((map_eq_zero_iff eC eC.injective).1 hcl)
  -- `(e₀ - e₁, w)` lies in the stabilized kernel, so `r e₁` lies in the kernel of `A`, and is
  -- `r k` for some `k` in the kernel of `T`.
  have hz : T (e₀ - e₁) + σ w = 0 := by
    rw [map_sub, sub_add_eq_add_sub, sub_eq_zero]
    exact he₁.symm
  have hrk : r e₁ ∈ ker (A : V →ₗ[ℝ] W) := by
    have := hK _ _ hz
    rw [map_sub, map_sub, hw] at this
    simpa [sub_eq_add_neg] using this
  obtain ⟨k, hk⟩ := eK.surjective ⟨r e₁, hrk⟩
  refine ⟨e₀ - e₁ + k, w, ?_, ?_⟩
  · rw [map_add, add_right_comm, hz, zero_add]
    exact k.property
  · rw [map_add, map_sub, ← heK, hk, sub_add_cancel]

variable [CompleteSpace E] [CompleteSpace F]

/-- **The kernel chart of a reduction.** Let `r : E →L[ℝ] V` be onto, `σ : W →L[ℝ] F` and
`M : W →L[ℝ] W` bijective, with isomorphisms `eK : ker T ≃ ker A` restricting `r` and
`eC : coker T ≃ coker A` sending the class of `σ w` to that of `M w`, and suppose
`A (r e) + M w = 0` whenever `T e + σ w = 0`. Then `(e, w) ↦ (T e + σ w, r e)` is invertible: `σ`
stabilizes `T`, with kernel coordinate `r`. -/
theorem isInvertible_prod_coprod_comp_fst (hr : Function.Surjective r)
    (hM : Function.Bijective M) (hK : ∀ e w, T e + σ w = 0 → A (r e) + M w = 0)
    (heK : ∀ k, (eK k : V) = r k)
    (heC : ∀ w, eC (Submodule.Quotient.mk (σ w)) = Submodule.Quotient.mk (M w)) :
    ((T.coprod σ).prod (r ∘L fst ℝ E W)).IsInvertible := by
  refine isInvertible_iff_bijective.2 ⟨injective_prod_coprod_comp_fst hM.1 hK heK, ?_⟩
  rintro ⟨f, v⟩
  -- The class of `f` is that of some `σ w₁`, so `f = T e₂ + σ w₁`; correct the coordinate
  -- `r e₂` by a pair `(e₃, w₃)` of the stabilized kernel with `r e₃ = v - r e₂`.
  obtain ⟨w₀, hw₀⟩ := Submodule.Quotient.mk_surjective _ (eC (Submodule.Quotient.mk f))
  obtain ⟨w₁, rfl⟩ := hM.2 w₀
  rw [← heC, eC.injective.eq_iff, eq_comm, Submodule.Quotient.eq] at hw₀
  obtain ⟨e₂, he₂⟩ := hw₀
  obtain ⟨e₃, w₃, h₃, hr₃⟩ := exists_coprod_eq_zero_and_eq hr hM.2 hK heK heC (v - r e₂)
  refine ⟨(e₂ + e₃, w₁ + w₃), Prod.ext ?_ ?_⟩
  · have he₂' : T e₂ = f - σ w₁ := he₂
    simp only [prod_apply, coprod_apply, map_add]
    rw [he₂', add_add_add_comm, h₃, add_zero, sub_add_cancel]
  · simp [hr₃]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The stabilized kernels of `T` and `A` are identified by their coordinates in `V`; the
identification is `(e, w) ↦ (r e, M w)`. -/
private theorem exists_kerEquiv (hK : ∀ e w, T e + σ w = 0 → A (r e) + M w = 0)
    (h : ((T.coprod σ).prod (r ∘L fst ℝ E W)).IsInvertible) :
    ∃ Φ : (T.coprod σ).ker ≃ₗ[ℝ] (A.coprod (ContinuousLinearMap.id ℝ W)).ker,
      (∀ x, (Φ x : V × W) = (r (x : E × W).1, M (x : E × W).2)) ∧
        Φ.trans (kerEquivOfProd _ _ (isInvertible_prod_coprod_id_fst A)).toLinearEquiv.symm =
          (kerEquivOfProd _ _ h).toLinearEquiv.symm := by
  refine ⟨(kerEquivOfProd _ _ h).toLinearEquiv.symm.trans
    (kerEquivOfProd _ _ (isInvertible_prod_coprod_id_fst A)).toLinearEquiv, fun x ↦ ?_,
    by ext x; simp⟩
  have hx := hK (x : E × W).1 (x : E × W).2 (by simpa using x.property)
  have h₁ : (kerEquivOfProd _ _ h).toLinearEquiv.symm x = r (x : E × W).1 :=
    kerEquivOfProd_symm_apply h x
  rw [LinearEquiv.trans_apply, h₁, ContinuousLinearEquiv.coe_toLinearEquiv,
    coe_kerEquivOfProd_apply, kerSection_coprod_id_fst_apply, eq_neg_of_add_eq_zero_right hx]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The kernel sequences of a reduction.** The exact sequences
`0 → ker T → ker (T.coprod σ) → W → coker T → 0` and
`0 → ker A → ker (A.coprod 1) → W → coker A → 0` are isomorphic through `eK`, the
identification `Φ` of the stabilized kernels, `M` and `eC`, so their four-term isomorphisms
`ContinuousLinearMap.detLineCoprodEquiv` correspond. -/
private theorem detLineCongrKerCoker_detLineCoprodEquiv {Mₑ : W ≃ₗ[ℝ] W}
    (hMₑ : (Mₑ : W →ₗ[ℝ] W) = M) (heK : ∀ k, (eK k : V) = r k)
    (heC : ∀ w, eC (Submodule.Quotient.mk (σ w)) = Submodule.Quotient.mk (M w))
    {Φ : (T.coprod σ).ker ≃ₗ[ℝ] (A.coprod (ContinuousLinearMap.id ℝ W)).ker}
    (hΦ : ∀ x, (Φ x : V × W) = (r (x : E × W).1, M (x : E × W).2))
    [FiniteDimensional ℝ (T : E →ₗ[ℝ] F).ker] (hsT : Function.Surjective (T.coprod σ))
    (hsA : Function.Surjective (A.coprod (ContinuousLinearMap.id ℝ W)))
    (t : TauCeti.detLine ℝ (T.coprod σ).ker ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ W)) :
    LinearMap.detLineCongrKerCoker eK eC (detLineCoprodEquiv T σ hsT t) =
      detLineCoprodEquiv A (ContinuousLinearMap.id ℝ W) hsA
        (TensorProduct.congr Φ.detLineCongr Mₑ.detLineCongr.symm.dualMap t) := by
  have hsq₁ : (kerCoprodHom A (ContinuousLinearMap.id ℝ W) : _ →ₗ[ℝ] _) ∘ₗ eK.toLinearMap =
      Φ.toLinearMap ∘ₗ (kerCoprodHom T σ : _ →ₗ[ℝ] _) := by
    refine LinearMap.ext fun k ↦ Subtype.ext ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, coe_coe,
      kerCoprodHom_apply, hΦ, heK, map_zero]
  have hsq₂ : (parameterProj A (ContinuousLinearMap.id ℝ W) : _ →ₗ[ℝ] _) ∘ₗ Φ.toLinearMap =
      Mₑ.toLinearMap ∘ₗ (parameterProj T σ : _ →ₗ[ℝ] _) := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, coe_coe,
      parameterProj_apply, hΦ]
    exact (LinearMap.congr_fun hMₑ _).symm
  have hsq₃ : parameterToCoker A (ContinuousLinearMap.id ℝ W) ∘ₗ Mₑ.toLinearMap =
      eC.toLinearMap ∘ₗ parameterToCoker T σ := by
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      parameterToCoker_apply, Submodule.mkQ_apply, heC, ContinuousLinearMap.id_apply]
    rw [show Mₑ w = M w from LinearMap.congr_fun hMₑ w]
  rw [LinearMap.detLineCongrKerCoker_def, detLineCoprodEquiv_def, detLineCoprodEquiv_def]
  exact (TauCeti.detLineFourTermEquiv_congr (kerCoprodHom_injective T σ)
    (exact_kerCoprodHom_parameterProj T σ) (exact_parameterProj_parameterToCoker T σ)
    ((parameterToCoker_surjective_iff_coprod_surjective T σ).2 hsT)
    (kerCoprodHom_injective A (ContinuousLinearMap.id ℝ W))
    (exact_kerCoprodHom_parameterProj A (ContinuousLinearMap.id ℝ W))
    (exact_parameterProj_parameterToCoker A (ContinuousLinearMap.id ℝ W))
    ((parameterToCoker_surjective_iff_coprod_surjective A (ContinuousLinearMap.id ℝ W)).2 hsA)
    eK Φ Mₑ eC hsq₁ hsq₂ hsq₃ t).symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- The normalized stabilization isomorphisms of `T` and `A` correspond as well: their Koszul signs
agree, since `eC` identifies the cokernels. -/
private theorem detLineCongrKerCoker_detLineStabilizationEquiv {Mₑ : W ≃ₗ[ℝ] W}
    (hMₑ : (Mₑ : W →ₗ[ℝ] W) = M) (heK : ∀ k, (eK k : V) = r k)
    (heC : ∀ w, eC (Submodule.Quotient.mk (σ w)) = Submodule.Quotient.mk (M w))
    {Φ : (T.coprod σ).ker ≃ₗ[ℝ] (A.coprod (ContinuousLinearMap.id ℝ W)).ker}
    (hΦ : ∀ x, (Φ x : V × W) = (r (x : E × W).1, M (x : E × W).2))
    [FiniteDimensional ℝ (T : E →ₗ[ℝ] F).ker] (hsT : Function.Surjective (T.coprod σ))
    (hsA : Function.Surjective (A.coprod (ContinuousLinearMap.id ℝ W)))
    (t : TauCeti.detLine ℝ (T.coprod σ).ker ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ W)) :
    LinearMap.detLineCongrKerCoker eK eC (detLineStabilizationEquiv T σ hsT t) =
      detLineStabilizationEquiv A (ContinuousLinearMap.id ℝ W) hsA
        (TensorProduct.congr Φ.detLineCongr Mₑ.detLineCongr.symm.dualMap t) := by
  have hsign : (-1 : ℝ) ^ (finrank ℝ (F ⧸ range (T : E →ₗ[ℝ] F)) * finrank ℝ W) =
      (-1) ^ (finrank ℝ (W ⧸ range (A : V →ₗ[ℝ] W)) * finrank ℝ W) := by
    rw [eC.finrank_eq]
  rw [detLineStabilizationEquiv_apply, detLineStabilizationEquiv_apply, LinearEquiv.map_smul,
    hsign, detLineCongrKerCoker_detLineCoprodEquiv hMₑ heK heC hΦ]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The kernel charts of a reduction.** In the situation of
`ContinuousLinearMap.isInvertible_prod_coprod_comp_fst`, the kernel chart of `T` with stabilizer
`σ` and coordinate `(e, w) ↦ r e` reads `v ∈ det T` as `det M` times the reading of
`ρ v = LinearMap.detLineCongrKerCoker eK eC v ∈ det A` in the kernel chart of `A` with stabilizer
the identity of `W` and coordinate `(v, w) ↦ v`. Both charts take values in `det V ⊗ (det W)^*`. -/
theorem detLineChartEquiv_eq_det_smul_detLineChartEquiv_detLineCongrKerCoker
    (hM : Function.Bijective M) (hK : ∀ e w, T e + σ w = 0 → A (r e) + M w = 0)
    (heK : ∀ k, (eK k : V) = r k)
    (heC : ∀ w, eC (Submodule.Quotient.mk (σ w)) = Submodule.Quotient.mk (M w))
    (h : ((T.coprod σ).prod (r ∘L fst ℝ E W)).IsInvertible) (v : (T : E →ₗ[ℝ] F).detLine) :
    detLineChartEquiv T σ (r ∘L fst ℝ E W) h v =
      LinearMap.det (M : W →ₗ[ℝ] W) •
        detLineChartEquiv A (ContinuousLinearMap.id ℝ W) (fst ℝ V W)
          (isInvertible_prod_coprod_id_fst A) (LinearMap.detLineCongrKerCoker eK eC v) := by
  have := finiteDimensional_ker_of_isInvertible_prod_coprod h
  obtain ⟨Mₑ, hMₑ⟩ : ∃ Mₑ : W ≃ₗ[ℝ] W, (Mₑ : W →ₗ[ℝ] W) = M :=
    ⟨LinearEquiv.ofBijective (M : W →ₗ[ℝ] W) hM, rfl⟩
  obtain ⟨Φ, hΦ, hkΦ⟩ := exists_kerEquiv hK h
  obtain ⟨t, rfl⟩ :=
    (detLineStabilizationEquiv T σ (surjective_of_isInvertible_prod h)).surjective v
  -- Reading after `Φ` in the coordinates of `A` is reading in those of `T`; the dual factor is
  -- rescaled by `det M⁻¹`.
  rw [detLineCongrKerCoker_detLineStabilizationEquiv hMₑ heK heC hΦ _
      (surjective_of_isInvertible_prod (isInvertible_prod_coprod_id_fst A)),
    detLineChartEquiv_detLineStabilizationEquiv, detLineChartEquiv_detLineStabilizationEquiv,
    ← LinearEquiv.trans_apply, LinearEquiv.congr_trans_rTensor, ← LinearEquiv.detLineCongr_trans,
    hkΦ, ← LinearEquiv.lTensor_trans_rTensor, LinearEquiv.trans_apply,
    LinearEquiv.lTensor_detLineCongr_symm_dualMap_apply, LinearEquiv.map_smul, smul_smul, ← hMₑ,
    LinearEquiv.det_mul_det_symm, one_smul]

end ContinuousLinearMap

namespace TauCeti

open Filter Topology ContinuousLinearMap

variable {E F V W X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [TopologicalSpace X]
  {T : X → E →L[ℝ] F} {A : X → V →L[ℝ] W} {r : E →L[ℝ] V} {σ : W →L[ℝ] F} {M : X → W →L[ℝ] W}
  {eK : ∀ x, ker (T x : E →ₗ[ℝ] F) ≃ₗ[ℝ] ker (A x : V →ₗ[ℝ] W)}
  {eC : ∀ x, (F ⧸ range (T x : E →ₗ[ℝ] F)) ≃ₗ[ℝ] (W ⧸ range (A x : V →ₗ[ℝ] W))}
  {u : ∀ x, (A x : V →ₗ[ℝ] W).detLine} {s : Set X} {x₀ : X}

/-- **Reductions transport coherent families.** Let `T x : E →L[ℝ] F` and `A x : V →L[ℝ] W` be
families continuous within `s` at `x₀`, with `V`, `W` finite-dimensional, and let
`eK x : ker (T x) ≃ ker (A x)` and `eC x : coker (T x) ≃ coker (A x)` come from a reduction
(`ContinuousLinearMap.isInvertible_prod_coprod_comp_fst`): a fixed map `r : E →L[ℝ] V` onto `V`
restricting to `eK x`, a fixed stabilization `σ : W →L[ℝ] F` and a family `M x` of endomorphisms
of `W`, continuous within `s` at `x₀` and invertible at `x₀`, with `eC x [σ w] = [M x w]` and
`A x (r e) + M x w = 0` whenever `T x e + σ w = 0`. If `u` is coherent for `A` within `s` at
`x₀`, then its transport `x ↦ (LinearMap.detLineCongrKerCoker (eK x) (eC x))⁻¹ (u x)` is coherent
for `T` within `s` at `x₀`. -/
theorem IsDetLineCoherentWithinAt.detLineCongrKerCoker_symm
    (hu : IsDetLineCoherentWithinAt A u s x₀) (hT : ContinuousWithinAt T s x₀)
    (hA : ContinuousWithinAt A s x₀) (hM : ContinuousWithinAt M s x₀)
    (hM₀ : Function.Bijective (M x₀)) (hr : Function.Surjective r)
    (hK : ∀ x e w, T x e + σ w = 0 → A x (r e) + M x w = 0)
    (heK : ∀ x k, (eK x k : V) = r k)
    (heC : ∀ x w, eC x (Submodule.Quotient.mk (σ w)) = Submodule.Quotient.mk (M x w)) :
    IsDetLineCoherentWithinAt T
      (fun x ↦ (LinearMap.detLineCongrKerCoker (eK x) (eC x)).symm (u x)) s x₀ := by
  -- Near `x₀`, `det (M x)` has the sign of `det (M x₀) ≠ 0`, so `M x` is invertible.
  have hd₀ : LinearMap.det (M x₀ : W →ₗ[ℝ] W) ≠ 0 :=
    (LinearEquiv.isUnit_det' (LinearEquiv.ofBijective (M x₀ : W →ₗ[ℝ] W) hM₀)).ne_zero
  have hdet : ∀ᶠ x in 𝓝[s] x₀,
      0 < LinearMap.det (M x : W →ₗ[ℝ] W) * LinearMap.det (M x₀ : W →ₗ[ℝ] W) :=
    (continuous_det.continuousAt.comp_continuousWithinAt hM).eventually
      ((isOpen_lt continuous_const (continuous_id.mul continuous_const)).mem_nhds
        (mul_self_pos.2 hd₀))
  have hbij {x : X} (hx : 0 < LinearMap.det (M x : W →ₗ[ℝ] W) *
      LinearMap.det (M x₀ : W →ₗ[ℝ] W)) : Function.Bijective (M x) := by
    have hunit : IsUnit (M x : W →ₗ[ℝ] W) := (LinearMap.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul hx.ne'))
    exact (Module.End.isUnit_iff _).1 hunit
  have h₀ := isInvertible_prod_coprod_comp_fst hr hM₀ (hK x₀) (heK x₀) (heC x₀)
  -- `T x₀` is Fredholm, its kernel and cokernel being those of the linear map `A x₀` of
  -- finite-dimensional spaces.
  have hF : IsFredholm (T x₀) := (isFredholm_iff_finite_ker_coker (T x₀)).2
    ⟨(eK x₀).symm.finiteDimensional, (eC x₀).symm.finiteDimensional⟩
  refine isDetLineCoherentWithinAt_of_eventually_sameRay hT hF
    ((LinearEquiv.map_ne_zero_iff _).2 hu.ne_zero) h₀ ?_
  filter_upwards [hu.eventually_sameRay hA (isInvertible_prod_coprod_id_fst (A x₀)), hdet]
    with x hux hx
  obtain ⟨_, hsr⟩ := hux
  refine ⟨isInvertible_prod_coprod_comp_fst hr (hbij hx) (hK x) (heK x) (heC x), ?_⟩
  rw [detLineChartEquiv_eq_det_smul_detLineChartEquiv_detLineCongrKerCoker (hbij hx) (hK x)
      (heK x) (heC x), detLineChartEquiv_eq_det_smul_detLineChartEquiv_detLineCongrKerCoker hM₀
      (hK x₀) (heK x₀) (heC x₀), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  -- Rescaling two readings on the same ray by `det (M x)` and `det (M x₀)`, of the same sign.
  have hpos : 0 < LinearMap.det (M x : W →ₗ[ℝ] W) / LinearMap.det (M x₀ : W →ₗ[ℝ] W) := by
    have := div_pos hx (mul_self_pos.2 hd₀)
    rwa [mul_div_mul_right _ _ hd₀] at this
  rw [← div_mul_cancel₀ (LinearMap.det (M x : W →ₗ[ℝ] W)) hd₀, mul_comm, mul_smul]
  exact (hsr.pos_smul_left hpos).smul _

end TauCeti
