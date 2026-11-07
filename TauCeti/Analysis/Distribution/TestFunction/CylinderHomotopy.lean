/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.CylinderHomotopy
public import TauCeti.Analysis.Convex.SegmentUIcc
public import TauCeti.Analysis.Distribution.Mass.Normal

/-!
# The product of a current with an oriented interval

Let `Ω ⊆ E` be an open subset of a real normed space and let `W ⊆ E × ℝ` be an open set whose
part over the unit interval lies over `Ω`: if `(x, t) ∈ W` and `t ∈ [0, 1]`, then `x ∈ Ω`. The
main example is `W = Ω × ℝ`. The cylinder homotopy operator `TauCeti.cylinderHomotopy`

`(h ω)(x)(v₁, …, vₖ) = ∫₀¹ ω(x, t)(∂ₜ, v₁, …, vₖ) dt`

sends test `(k + 1)`-forms on `W` to test `k`-forms on `Ω`, continuously for the LF topologies
(`TestFunction.cylinderHomotopyCLM`). So for a `k`-current `T` on `Ω` (a continuous linear
functional on test `k`-forms), the composite `T ∘ h` is a `(k + 1)`-current on `W`: the product
`[[0, 1]] × T` of `T` with the unit interval, with the interval factor first: by Fubini, when `T`
integrates over an oriented `k`-dimensional piece `S`, the current `T ∘ h` integrates over
`[0, 1] × S` with the orientation `∂ₜ ∧ (orientation of S)` (this comparison is not formalized
here).

More generally, for real numbers `a` and `b` such that the part of `W` over the interval
`[[a, b]] = uIcc a b` lies over `Ω`, the operator `h_{a,b}` of
`TestFunction.intervalCylinderHomotopyCLM` integrates over the oriented interval from `a` to `b`:

`(h_{a,b} ω)(x)(v₁, …, vₖ) = ∫ t in a..b, ω(x, t)(∂ₜ, v₁, …, vₖ)`,

and `[[a, b]] × T = T ∘ h_{a,b}`. The orientation is that of the interval integral: exchanging `a`
and `b` changes the sign of the product, and `[[a, a]] × T = 0`. For `a = 0` and `b = 1` this is
`[[0, 1]] × T`.

Write `ιₜ : x ↦ (x, t)` for the slice at time `t`, so that `ιₜ^*` is the pullback
`TestFunction.pullbackCLM` and `{t} × T = T ∘ ιₜ^*` is the pushforward of `T` along `ιₜ`. The
cylinder homotopy identity `h_{a,b} (d ω) = ι_b^* ω - ι_a^* ω - d (h_{a,b} ω)` on test forms gives
the **boundary formula**

`∂ ([[a, b]] × T) = {b} × T - {a} × T - [[a, b]] × ∂ T`,

where `∂ T = T ∘ d`; in degree zero the last term is absent. For the operator-norm mass of
`Distribution.mass`, with the sup norm on `E × ℝ`, this gives `M([[a, b]] × T) ≤ |b - a| M(T)` and
`M(∂ ([[a, b]] × T)) ≤ 2 M(T) + |b - a| M(∂ T)`, with the corresponding local mass bound. So the
product with an interval preserves locally finite mass, local normality and normality. These are
the product and homotopy formulas used to build homotopies between pushforwards of currents and to
estimate their masses.

## Main declarations

* `TestFunction.cylinderHomotopyCLM`: the cylinder homotopy operator on test forms, as a
  continuous linear map.
* `TauCeti.isCompact_inter_preimage_prodMk_left`: the slices `ιₜ` are proper from `Ω` to `W` at
  the times over which `W` lies over `Ω`, so the pushforwards `{t} × T` are defined.
* `TestFunction.pullbackCLM_prodMk_left_apply`: at such times, `ιₜ^* ω` is `ω (·, t)` restricted
  to `E`.
* `TestFunction.tsupport_cylinderHomotopyCLM_subset`,
  `TestFunction.norm_cylinderHomotopyCLM_apply_le`: its support and pointwise bound.
* `TestFunction.cylinderHomotopyCLM_comp_extDerivCLM`: `h ∘ d = ι₁^* - ι₀^* - d ∘ h`, and
  `TestFunction.cylinderHomotopyCLM_comp_extDerivCLM_finZero` in degree zero.
* `TestFunction.intervalCylinderHomotopyCLM`: the operator `h_{a,b}` over an oriented interval,
  with its values `TestFunction.intervalCylinderHomotopyCLM_apply`, endpoint cancellation
  `TestFunction.intervalCylinderHomotopyCLM_self`, orientation reversal
  `TestFunction.intervalCylinderHomotopyCLM_symm` and the unit interval case
  `TestFunction.intervalCylinderHomotopyCLM_zero_one`.
* `TestFunction.intervalCylinderHomotopyCLM_comp_extDerivCLM`: `h_{a,b} ∘ d = ι_b^* - ι_a^* -
  d ∘ h_{a,b}`, and `TestFunction.intervalCylinderHomotopyCLM_comp_extDerivCLM_finZero`.
* `ContinuousLinearMap.comp_intervalCylinderHomotopyCLM_comp_extDerivCLM`: the boundary formula
  `∂ ([[a, b]] × T) = {b} × T - {a} × T - [[a, b]] × ∂ T`, and its degree zero version; the
  unit-interval versions are `ContinuousLinearMap.comp_cylinderHomotopyCLM_comp_extDerivCLM` and
  `ContinuousLinearMap.comp_cylinderHomotopyCLM_comp_extDerivCLM_finZero`.
* `Distribution.mass_comp_pullbackCLM_prodMk_left_le`: `M({t} × T) ≤ M(T)`.
* `Distribution.localMass_comp_intervalCylinderHomotopyCLM_le`,
  `Distribution.mass_comp_intervalCylinderHomotopyCLM_le`: `M([[a, b]] × T) ≤ |b - a| M(T)`, and
  `Distribution.mass_comp_cylinderHomotopyCLM_le` on the unit interval.
* `Distribution.mass_comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_le`:
  `M(∂ ([[a, b]] × T)) ≤ 2 M(T) + |b - a| M(∂ T)`, with the degree zero bound
  `Distribution.mass_comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_finZero_le` and the unit
  interval case `Distribution.mass_comp_cylinderHomotopyCLM_comp_extDerivCLM_le`.
* `Distribution.HasLocallyFiniteMass.comp_intervalCylinderHomotopyCLM`,
  `Distribution.IsLocallyNormal.comp_intervalCylinderHomotopyCLM`,
  `Distribution.IsNormal.comp_intervalCylinderHomotopyCLM`: preservation of locally finite mass,
  local normality and normality.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.8 (the product `[[0, 1]] × T` and the homotopy
  formula).
-/

public section

noncomputable section

open Set TopologicalSpace TauCeti
open scoped Distributions ENNReal BoundedContinuousFunction

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {Ω : Opens X} {W : Opens (X × ℝ)}

/-- The projection to `X` of the part of a compact set in `X × [0, 1]` is compact. -/
private theorem isCompact_fst_image_inter {K : Set (X × ℝ)} (hK : IsCompact K) :
    IsCompact (Prod.fst '' (K ∩ univ ×ˢ Icc 0 1)) :=
  (hK.inter_right (isClosed_univ.prod isClosed_Icc)).image continuous_fst

/-- The projection to `X` of the part of a subset of `W` in `X × [0, 1]` lies in `Ω`. -/
private theorem fst_image_inter_subset (hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω)
    {K : Set (X × ℝ)} (hKW : K ⊆ W) : Prod.fst '' (K ∩ univ ×ˢ Icc 0 1) ⊆ Ω := by
  rintro _ ⟨p, ⟨hpK, -, hp⟩, rfl⟩
  exact hW p (hKW hpK) hp

/-- **The slices are proper.** If the part of `W` over a set `S` of times lies over `Ω`, then
for `t ∈ S` the slice `x ↦ (x, t)` is proper from `Ω` to `W`. -/
theorem isCompact_inter_preimage_prodMk_left [T2Space X] {S : Set ℝ}
    (hW : ∀ p ∈ W, p.2 ∈ S → p.1 ∈ Ω) {t : ℝ} (ht : t ∈ S)
    (K : Set (X × ℝ)) (hK : IsCompact K) (hKW : K ⊆ W) :
    IsCompact ((Ω : Set X) ∩ (fun x ↦ (x, t)) ⁻¹' K) := by
  rw [inter_eq_right.2 fun x hx ↦ hW (x, t) (hKW hx) ht]
  exact (hK.image continuous_fst).of_isClosed_subset
    (hK.isClosed.preimage (continuous_id.prodMk continuous_const)) fun x hx ↦ ⟨_, hx, rfl⟩

end TauCeti

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {W : Opens (E × ℝ)} {k : ℕ}

variable [CompleteSpace F]

/-- The cylinder homotopy operator on tests supported in a compact `K ⊆ E × ℝ`, whose images are
supported in the projection of `K ∩ (E × [0, 1])`. -/
private def cylinderHomotopySupportedInCLM (K : Compacts (E × ℝ)) :
    𝓓_{K}(E × ℝ, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ]
      𝓓_{⟨Prod.fst '' ((K : Set (E × ℝ)) ∩ univ ×ˢ Icc 0 1),
        isCompact_fst_image_inter K.isCompact⟩}(E, E [⋀^Fin k]→L[ℝ] F) :=
  letI P : 𝓓_{K}(E × ℝ, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →ₗ[ℝ]
      𝓓_{⟨Prod.fst '' ((K : Set (E × ℝ)) ∩ univ ×ˢ Icc 0 1),
        isCompact_fst_image_inter K.isCompact⟩}(E, E [⋀^Fin k]→L[ℝ] F) :=
    { toFun ω := ⟨cylinderHomotopy ω, contDiff_cylinderHomotopy ω.contDiff,
        fun x hx ↦ Function.notMem_support.1 fun h ↦ hx <|
          image_mono (inter_subset_inter_left _ ω.support_subset)
            (support_cylinderHomotopy_subset _ h)⟩
      map_add' ω η := ContDiffMapSupportedIn.ext fun x ↦
        cylinderHomotopy_add_apply ω.continuous.continuousOn η.continuous.continuousOn
      map_smul' c ω := ContDiffMapSupportedIn.ext fun x ↦
        congrFun (cylinderHomotopy_smul c ω) x }
  { toLinearMap := P
    cont := by
      -- Each seminorm of the image is bounded by the seminorm of the same order of the source.
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      refine ⟨{i}, 1, fun ω ↦ ((P ω).seminorm_le_iff ℝ (by positivity) i).2 fun _ x _ ↦ ?_⟩
      refine norm_iteratedFDeriv_cylinderHomotopy_le ω.contDiff ω.hasCompactSupport
        (mod_cast le_top) fun t _ ↦ ?_
      exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans_eq
        (by simp) }

/-- The **cylinder homotopy operator** on test forms: the continuous linear map sending a test
`(k + 1)`-form `ω` on `W` to the test `k`-form `x ↦ ∫₀¹ ω(x, t)(∂ₜ, ·) dt` on `Ω`, see
`TauCeti.cylinderHomotopy`. Here the part of `W` over `[0, 1]` is assumed to lie over `Ω`.
Precomposing a `k`-current `T` on `Ω` with it gives the product current `[[0, 1]] × T` on `W`. -/
def cylinderHomotopyCLM (hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω) :
    𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
  letI T (ω : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)) : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
    haveI hC := isCompact_fst_image_inter ω.hasCompactSupport
    haveI hsupp := tsupport_cylinderHomotopy_subset ω.hasCompactSupport
    ⟨cylinderHomotopy ω, contDiff_cylinderHomotopy ω.contDiff,
      hC.of_isClosed_subset (isClosed_tsupport _) hsupp,
      hsupp.trans (fst_image_inter_subset hW ω.tsupport_subset)⟩
  TestFunction.limitCLM ℝ T
    (fun K hK ↦ ofSupportedInCLM ℝ (fst_image_inter_subset hW hK) ∘L
      cylinderHomotopySupportedInCLM K)
    (fun _ _ _ ↦ rfl)

variable {hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω}

/-- The cylinder homotopy operator on test forms is the pointwise cylinder homotopy operator. -/
@[simp]
theorem coe_cylinderHomotopyCLM (ω : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)) :
    ⇑(cylinderHomotopyCLM hW ω) = cylinderHomotopy ω :=
  (rfl)

/-- The cylinder homotopy operator on test forms is `x ↦ ∫₀¹ ω(x, t)(∂ₜ, ·) dt`. -/
theorem cylinderHomotopyCLM_apply (ω : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)) (x : E) :
    cylinderHomotopyCLM hW ω x =
      ∫ t in (0 : ℝ)..1, ((ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  rw [coe_cylinderHomotopyCLM, cylinderHomotopy_apply]

/-- The cylinder homotopy operator is supported over the part of the support of the form that lies
in `E × [0, 1]`. -/
theorem tsupport_cylinderHomotopyCLM_subset (ω : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)) :
    tsupport (cylinderHomotopyCLM hW ω) ⊆ Prod.fst '' (tsupport ω ∩ univ ×ˢ Icc 0 1) :=
  tsupport_cylinderHomotopy_subset ω.hasCompactSupport

/-- The cylinder homotopy operator of a test form is pointwise bounded by any bound for the form
along `{x} × [0, 1]`, for the sup norm on `E × ℝ`. -/
theorem norm_cylinderHomotopyCLM_apply_le (ω : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)) {x : E}
    {B : ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖ω (x, t)‖ ≤ B) : ‖cylinderHomotopyCLM hW ω x‖ ≤ B :=
  norm_cylinderHomotopy_le h

omit [CompleteSpace F] in
/-- If the part of `W` over a set `S` of times lies over `Ω`, then at a time `t ∈ S` the pullback
along the slice `x ↦ (x, t)` is `ω (x, t)` restricted to `E`, at every point of `E`. -/
theorem pullbackCLM_prodMk_left_apply {S : Set ℝ} (hW : ∀ p ∈ W, p.2 ∈ S → p.1 ∈ Ω)
    {m : ℕ} {t : ℝ} (ht : t ∈ S)
    {hp : ∀ K : Set (E × ℝ), IsCompact K → K ⊆ W →
      IsCompact ((Ω : Set E) ∩ (fun x ↦ (x, t)) ⁻¹' K)}
    (ω : 𝓓(W, (E × ℝ) [⋀^Fin m]→L[ℝ] F)) (x : E) :
    pullbackCLM (fun x ↦ (x, t)) (contDiffOn_id.prodMk contDiffOn_const) hp ω x =
      (ω (x, t)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  by_cases hx : x ∈ Ω
  · rw [pullbackCLM_apply_of_mem _ hx, (hasFDerivAt_prodMk_left x t).fderiv]
  · have hxt : (x, t) ∉ tsupport ω := fun h ↦ hx (hW _ (ω.tsupport_subset h) ht)
    rw [pullbackCLM_apply_of_notMem _ hx, image_eq_zero_of_notMem_tsupport hxt]
    ext v
    simp

/-- **The homotopy formula on test forms**: `h ∘ d = ι₁^* - ι₀^* - d ∘ h` on test
`(k + 1)`-forms, where `ιₜ^*` is the pullback along the slice `x ↦ (x, t)`. -/
theorem cylinderHomotopyCLM_comp_extDerivCLM :
    (cylinderHomotopyCLM hW ∘L extDerivCLM : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM (fun x ↦ (x, (1 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW ⟨zero_le_one, le_rfl⟩) -
        pullbackCLM (fun x ↦ (x, (0 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW ⟨le_rfl, zero_le_one⟩) -
        extDerivCLM ∘L cylinderHomotopyCLM hW := by
  ext ω x : 2
  have h := extDeriv_cylinderHomotopy_add_cylinderHomotopy_extDeriv
    (ω.contDiff.of_le (by simp)) x
  simp only [ContinuousLinearMap.comp_apply, sub_apply, coe_cylinderHomotopyCLM,
    coe_extDerivCLM]
  rw [pullbackCLM_prodMk_left_apply hW ⟨zero_le_one, le_rfl⟩,
    pullbackCLM_prodMk_left_apply hW ⟨le_rfl, zero_le_one⟩, ← h]
  abel

/-- **The homotopy formula on test `0`-forms**: `h ∘ d = ι₁^* - ι₀^*`, where `ιₜ^*` is the
pullback along the slice `x ↦ (x, t)`. -/
theorem cylinderHomotopyCLM_comp_extDerivCLM_finZero :
    (cylinderHomotopyCLM hW ∘L extDerivCLM : 𝓓(W, (E × ℝ) [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM (fun x ↦ (x, (1 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW ⟨zero_le_one, le_rfl⟩) -
        pullbackCLM (fun x ↦ (x, (0 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW ⟨le_rfl, zero_le_one⟩) := by
  ext ω x : 2
  simp only [ContinuousLinearMap.comp_apply, sub_apply, coe_cylinderHomotopyCLM,
    coe_extDerivCLM]
  rw [pullbackCLM_prodMk_left_apply hW ⟨zero_le_one, le_rfl⟩,
    pullbackCLM_prodMk_left_apply hW ⟨le_rfl, zero_le_one⟩]
  exact cylinderHomotopy_extDeriv_eq_sub (ω.contDiff.of_le (by simp)) x

/-! ### The product with an oriented interval

For real numbers `a` and `b`, the operator `h_{a,b}` contracts a test form with `∂ₜ` and integrates
over the oriented interval from `a` to `b`. For `a ≠ b` it is the unit-interval operator `h` applied
after the pullback along the affine diffeomorphism `(x, t) ↦ (x, (b - a) t + a)`; for `a = b` it is
zero. Its values are pinned by `TestFunction.intervalCylinderHomotopyCLM_apply`. -/

section Interval

variable {a b : ℝ}

/-- The affine reparametrization `(x, t) ↦ (x, (b - a) * t + a)` of the time line, as a
homeomorphism of `E × ℝ` when `a ≠ b`. -/
private def reparam (a b : ℝ) (hab : a ≠ b) : E × ℝ ≃ₜ E × ℝ :=
  (Homeomorph.refl E).prodCongr
    ((Homeomorph.mulLeft₀ (b - a) (sub_ne_zero.2 hab.symm)).trans (Homeomorph.addRight a))

omit [NormedSpace ℝ E] [CompleteSpace F] in
private theorem reparam_apply (hab : a ≠ b) (p : E × ℝ) :
    reparam a b hab p = (p.1, (b - a) * p.2 + a) :=
  (rfl)

omit [CompleteSpace F] in
private theorem contDiff_reparam (hab : a ≠ b) :
    ContDiff ℝ (⊤ : ℕ∞) (reparam (E := E) a b hab) := by
  simp_rw [funext (reparam_apply hab)]
  exact contDiff_fst.prodMk ((contDiff_const.mul contDiff_snd).add contDiff_const)

omit [CompleteSpace F] in
/-- The derivative of the reparametrization is `(v, s) ↦ (v, (b - a) s)`. -/
private theorem fderiv_reparam (hab : a ≠ b) (p : E × ℝ) :
    fderiv ℝ (reparam a b hab) p =
      (ContinuousLinearMap.fst ℝ E ℝ).prod ((b - a) • ContinuousLinearMap.snd ℝ E ℝ) := by
  simp_rw [funext (reparam_apply hab)]
  exact (hasFDerivAt_fst.prodMk ((hasFDerivAt_snd.const_mul (b - a)).add_const a)).fderiv

/-- The preimage of `W` under the reparametrization. -/
private def reparamPreimage (hab : a ≠ b) (W : Opens (E × ℝ)) : Opens (E × ℝ) :=
  ⟨reparam a b hab ⁻¹' W, W.isOpen.preimage (reparam a b hab).continuous⟩

omit [NormedSpace ℝ E] [CompleteSpace F] in
private theorem coe_reparamPreimage (hab : a ≠ b) :
    (reparamPreimage hab W : Set (E × ℝ)) = reparam a b hab ⁻¹' W :=
  (rfl)

omit [NormedSpace ℝ E] [CompleteSpace F] in
private theorem reparamPreimage_spec (hab : a ≠ b) (hW : ∀ p ∈ W, p.2 ∈ uIcc a b → p.1 ∈ Ω) :
    ∀ p ∈ reparamPreimage hab W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω := fun p hp ht ↦ by
  rw [SetLike.mem_coe.symm, coe_reparamPreimage, mem_preimage] at hp
  simpa [reparam_apply] using hW _ hp (by simpa [reparam_apply] using sub_mul_add_mem_uIcc ht)

omit [NormedSpace ℝ E] [CompleteSpace F] in
private theorem isCompact_inter_preimage_reparam (hab : a ≠ b) (K : Set (E × ℝ))
    (hK : IsCompact K) (hKW : K ⊆ W) :
    IsCompact ((reparamPreimage hab W : Set (E × ℝ)) ∩ reparam a b hab ⁻¹' K) := by
  rw [coe_reparamPreimage, inter_eq_right.2 (preimage_mono hKW)]
  exact (reparam a b hab).isCompact_preimage.2 hK

omit [CompleteSpace F] in
/-- Contracting a pulled back form with `∂ₜ` and restricting to `E` gives `b - a` times the
contraction of the form. -/
private theorem curryLeft_compContinuousLinearMap_reparam (hab : a ≠ b) {m : ℕ}
    (α : (E × ℝ) [⋀^Fin (m + 1)]→L[ℝ] F) (p : E × ℝ) :
    ((α.compContinuousLinearMap (fderiv ℝ (reparam a b hab) p)).curryLeft
        (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) =
      (b - a) • (α.curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  ext v
  -- `Matrix.vecCons` is `Fin.cons`, so this is linearity in the first argument.
  simpa [fderiv_reparam, Function.comp_def, Matrix.vecCons] using
    α.toMultilinearMap.cons_smul (fun i ↦ (v i, 0)) (b - a) (0, 1)

omit [CompleteSpace F] in
/-- The pullback along the reparametrization is given by the pullback formula at every point of
`E × ℝ`, including points off the preimage of `W`, where both sides vanish. -/
private theorem pullbackCLM_reparam_apply (hab : a ≠ b) {m : ℕ}
    (ω : 𝓓(W, (E × ℝ) [⋀^Fin m]→L[ℝ] F)) (p : E × ℝ) :
    pullbackCLM (reparam a b hab) (contDiff_reparam hab).contDiffOn
        (isCompact_inter_preimage_reparam hab) ω p =
      (ω (reparam a b hab p)).compContinuousLinearMap (fderiv ℝ (reparam a b hab) p) := by
  by_cases hp : p ∈ reparamPreimage hab W
  · exact pullbackCLM_apply_of_mem _ hp
  · have hp' : reparam a b hab p ∉ tsupport ω := fun h ↦ hp <| by
      rw [SetLike.mem_coe.symm, coe_reparamPreimage, mem_preimage]
      exact ω.tsupport_subset h
    rw [pullbackCLM_apply_of_notMem _ hp, image_eq_zero_of_notMem_tsupport hp']
    ext v
    simp

variable {hW : ∀ p ∈ W, p.2 ∈ uIcc a b → p.1 ∈ Ω}

omit [CompleteSpace F] in
/-- Pulling back along the reparametrization and then along the slice at time `t ∈ [0, 1]` is
pulling back along the slice at the reparametrized time `(b - a) * t + a`. -/
private theorem pullbackCLM_prodMk_left_comp_pullbackCLM_reparam (hab : a ≠ b) {m : ℕ} {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : (b - a) * t + a = s)
    {hp : ∀ K : Set (E × ℝ), IsCompact K → K ⊆ W →
      IsCompact ((Ω : Set E) ∩ (fun x ↦ (x, s)) ⁻¹' K)} :
    (pullbackCLM (fun x ↦ (x, t)) (contDiffOn_id.prodMk contDiffOn_const)
        (isCompact_inter_preimage_prodMk_left (reparamPreimage_spec hab hW) ht) ∘L
      pullbackCLM (reparam a b hab) (contDiff_reparam hab).contDiffOn
        (isCompact_inter_preimage_reparam hab) :
        𝓓(W, (E × ℝ) [⋀^Fin m]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM (fun x ↦ (x, s)) (contDiffOn_id.prodMk contDiffOn_const) hp := by
  ext ω x : 2
  rw [ContinuousLinearMap.comp_apply,
    pullbackCLM_prodMk_left_apply (reparamPreimage_spec hab hW) ht,
    pullbackCLM_prodMk_left_apply hW (hs ▸ sub_mul_add_mem_uIcc ht), pullbackCLM_reparam_apply,
    reparam_apply, hs]
  ext v
  simp [fderiv_reparam, Function.comp_def]

/-- The **cylinder homotopy operator over an oriented interval** on test forms: the continuous
linear map sending a test `(k + 1)`-form `ω` on `W` to the test `k`-form
`x ↦ ∫ t in a..b, ω(x, t)(∂ₜ, ·)` on `Ω`, see `TestFunction.intervalCylinderHomotopyCLM_apply`.
Here the part of `W` over the interval `[[a, b]]` is assumed to lie over `Ω`. The integral is
oriented: the operator changes sign when `a` and `b` are exchanged and vanishes when `a = b`.
Precomposing a `k`-current `T` on `Ω` with it gives the product current `[[a, b]] × T` on `W`. -/
def intervalCylinderHomotopyCLM (a b : ℝ) (hW : ∀ p ∈ W, p.2 ∈ uIcc a b → p.1 ∈ Ω) :
    𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
  if hab : a = b then 0 else
    cylinderHomotopyCLM (reparamPreimage_spec hab hW) ∘L
      pullbackCLM (reparam a b hab) (contDiff_reparam hab).contDiffOn
        (isCompact_inter_preimage_reparam hab)

private theorem intervalCylinderHomotopyCLM_of_ne (hab : a ≠ b) :
    (intervalCylinderHomotopyCLM a b hW : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      cylinderHomotopyCLM (reparamPreimage_spec hab hW) ∘L
        pullbackCLM (reparam a b hab) (contDiff_reparam hab).contDiffOn
          (isCompact_inter_preimage_reparam hab) := by
  simp only [intervalCylinderHomotopyCLM, hab, ↓reduceDIte]

/-- The operator over the interval from `a` to `b` is `b - a` times the unit-interval operator of
the reparametrized form `(x, t) ↦ ω (x, (b - a) * t + a)`. -/
theorem coe_intervalCylinderHomotopyCLM (ω : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)) :
    ⇑(intervalCylinderHomotopyCLM a b hW ω) =
      (b - a) • cylinderHomotopy fun p : E × ℝ ↦ ω (p.1, (b - a) * p.2 + a) := by
  by_cases hab : a = b
  · subst hab
    simp [intervalCylinderHomotopyCLM]
  funext x
  rw [intervalCylinderHomotopyCLM_of_ne hab, ContinuousLinearMap.comp_apply,
    coe_cylinderHomotopyCLM, Pi.smul_apply, cylinderHomotopy_apply, cylinderHomotopy_apply,
    ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [pullbackCLM_reparam_apply, curryLeft_compContinuousLinearMap_reparam, reparam_apply]

/-- The operator over an oriented interval is `x ↦ ∫ t in a..b, ω(x, t)(∂ₜ, ·)`. -/
@[simp]
theorem intervalCylinderHomotopyCLM_apply (ω : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)) (x : E) :
    intervalCylinderHomotopyCLM a b hW ω x =
      ∫ t in a..b, ((ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  rw [coe_intervalCylinderHomotopyCLM, Pi.smul_apply, cylinderHomotopy_apply]
  simpa using intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1)
    (fun t ↦ ((ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ)) (b - a) a

/-- **Endpoint cancellation**: the operator over a degenerate interval vanishes. -/
@[simp]
theorem intervalCylinderHomotopyCLM_self (hW : ∀ p ∈ W, p.2 ∈ uIcc a a → p.1 ∈ Ω) :
    (intervalCylinderHomotopyCLM a a hW : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) = 0 := by
  simp only [intervalCylinderHomotopyCLM, ↓reduceDIte]

/-- **Orientation reversal**: exchanging the endpoints changes the sign of the operator. -/
theorem intervalCylinderHomotopyCLM_symm (hW' : ∀ p ∈ W, p.2 ∈ uIcc b a → p.1 ∈ Ω) :
    (intervalCylinderHomotopyCLM b a hW' : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      -intervalCylinderHomotopyCLM a b fun p hp ht ↦ hW' p hp (uIcc_comm a b ▸ ht) := by
  ext ω x : 2
  simp [intervalIntegral.integral_symm a b]

/-- Over the unit interval, the operator is the cylinder homotopy operator. -/
theorem intervalCylinderHomotopyCLM_zero_one (hW' : ∀ p ∈ W, p.2 ∈ uIcc (0 : ℝ) 1 → p.1 ∈ Ω)
    (hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω) :
    (intervalCylinderHomotopyCLM 0 1 hW' : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      cylinderHomotopyCLM hW := by
  ext ω x : 2
  rw [intervalCylinderHomotopyCLM_apply, cylinderHomotopyCLM_apply]

/-- The operator over an oriented interval is supported over the part of the support of the form
that lies over the interval. -/
theorem tsupport_intervalCylinderHomotopyCLM_subset (ω : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)) :
    tsupport (intervalCylinderHomotopyCLM a b hW ω) ⊆
      Prod.fst '' (tsupport ω ∩ univ ×ˢ uIcc a b) := by
  by_cases hab : a = b
  · subst hab
    simp
  rw [intervalCylinderHomotopyCLM_of_ne hab, ContinuousLinearMap.comp_apply]
  refine (tsupport_cylinderHomotopyCLM_subset _).trans ?_
  rintro _ ⟨p, ⟨hp, -, ht⟩, rfl⟩
  have hp' := (tsupport_pullbackCLM_subset ω hp).2
  rw [mem_preimage, reparam_apply] at hp'
  exact ⟨_, ⟨hp', mem_univ _, sub_mul_add_mem_uIcc ht⟩, rfl⟩

/-- The operator over an oriented interval is pointwise bounded by `|b - a|` times any bound for
the form along `{x} × [[a, b]]`, for the sup norm on `E × ℝ`. -/
theorem norm_intervalCylinderHomotopyCLM_apply_le (ω : 𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F))
    {x : E} {B : ℝ} (h : ∀ t ∈ uIcc a b, ‖ω (x, t)‖ ≤ B) :
    ‖intervalCylinderHomotopyCLM a b hW ω x‖ ≤ |b - a| * B := by
  rw [coe_intervalCylinderHomotopyCLM, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  gcongr
  exact norm_cylinderHomotopy_le fun t ht ↦ h _ (sub_mul_add_mem_uIcc ht)

omit [CompleteSpace F] in
/-- The slice at time `1` of the reparametrized form is the slice at time `b`. -/
private theorem pullbackCLM_prodMk_one_comp_pullbackCLM_reparam (hab : a ≠ b) {m : ℕ} :
    (pullbackCLM (fun x ↦ (x, (1 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
        (isCompact_inter_preimage_prodMk_left (reparamPreimage_spec hab hW)
          ⟨zero_le_one, le_rfl⟩) ∘L
      pullbackCLM (reparam a b hab) (contDiff_reparam hab).contDiffOn
        (isCompact_inter_preimage_reparam hab) :
        𝓓(W, (E × ℝ) [⋀^Fin m]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM (fun x ↦ (x, b)) (contDiffOn_id.prodMk contDiffOn_const)
        (isCompact_inter_preimage_prodMk_left hW right_mem_uIcc) :=
  pullbackCLM_prodMk_left_comp_pullbackCLM_reparam (hW := hW) hab ⟨zero_le_one, le_rfl⟩ (by ring)

omit [CompleteSpace F] in
/-- The slice at time `0` of the reparametrized form is the slice at time `a`. -/
private theorem pullbackCLM_prodMk_zero_comp_pullbackCLM_reparam (hab : a ≠ b) {m : ℕ} :
    (pullbackCLM (fun x ↦ (x, (0 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
        (isCompact_inter_preimage_prodMk_left (reparamPreimage_spec hab hW)
          ⟨le_rfl, zero_le_one⟩) ∘L
      pullbackCLM (reparam a b hab) (contDiff_reparam hab).contDiffOn
        (isCompact_inter_preimage_reparam hab) :
        𝓓(W, (E × ℝ) [⋀^Fin m]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM (fun x ↦ (x, a)) (contDiffOn_id.prodMk contDiffOn_const)
        (isCompact_inter_preimage_prodMk_left hW left_mem_uIcc) :=
  pullbackCLM_prodMk_left_comp_pullbackCLM_reparam (hW := hW) hab ⟨le_rfl, zero_le_one⟩ (by ring)

/-- **Naturality of `d`**: for `a ≠ b`, `h_{a,b} ∘ d` is the unit-interval `h ∘ d` applied after
the pullback along the reparametrization. -/
private theorem intervalCylinderHomotopyCLM_comp_extDerivCLM_of_ne (hab : a ≠ b) :
    (intervalCylinderHomotopyCLM a b hW ∘L extDerivCLM :
        𝓓(W, (E × ℝ) [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) =
      (cylinderHomotopyCLM (reparamPreimage_spec hab hW) ∘L extDerivCLM) ∘L
        pullbackCLM (reparam a b hab) (contDiff_reparam hab).contDiffOn
          (isCompact_inter_preimage_reparam hab) := by
  rw [intervalCylinderHomotopyCLM_of_ne hab, ContinuousLinearMap.comp_assoc,
    pullbackCLM_comp_extDerivCLM, ContinuousLinearMap.comp_assoc]

/-- **The homotopy formula over an oriented interval** on test forms:
`h_{a,b} ∘ d = ι_b^* - ι_a^* - d ∘ h_{a,b}` on test `(k + 1)`-forms, where `ιₜ^*` is the pullback
along the slice `x ↦ (x, t)`. -/
theorem intervalCylinderHomotopyCLM_comp_extDerivCLM :
    (intervalCylinderHomotopyCLM a b hW ∘L extDerivCLM :
        𝓓(W, (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM (fun x ↦ (x, b)) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW right_mem_uIcc) -
        pullbackCLM (fun x ↦ (x, a)) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW left_mem_uIcc) -
        extDerivCLM ∘L intervalCylinderHomotopyCLM a b hW := by
  by_cases hab : a = b
  · subst hab
    simp
  rw [intervalCylinderHomotopyCLM_comp_extDerivCLM_of_ne hab, cylinderHomotopyCLM_comp_extDerivCLM,
    intervalCylinderHomotopyCLM_of_ne hab]
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc,
    pullbackCLM_prodMk_one_comp_pullbackCLM_reparam (hW := hW) hab,
    pullbackCLM_prodMk_zero_comp_pullbackCLM_reparam (hW := hW) hab]

/-- **The homotopy formula over an oriented interval on test `0`-forms**:
`h_{a,b} ∘ d = ι_b^* - ι_a^*`, where `ιₜ^*` is the pullback along the slice `x ↦ (x, t)`. -/
theorem intervalCylinderHomotopyCLM_comp_extDerivCLM_finZero :
    (intervalCylinderHomotopyCLM a b hW ∘L extDerivCLM :
        𝓓(W, (E × ℝ) [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM (fun x ↦ (x, b)) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW right_mem_uIcc) -
        pullbackCLM (fun x ↦ (x, a)) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW left_mem_uIcc) := by
  by_cases hab : a = b
  · subst hab
    simp
  rw [intervalCylinderHomotopyCLM_comp_extDerivCLM_of_ne hab,
    cylinderHomotopyCLM_comp_extDerivCLM_finZero]
  simp only [ContinuousLinearMap.sub_comp,
    pullbackCLM_prodMk_one_comp_pullbackCLM_reparam (hW := hW) hab,
    pullbackCLM_prodMk_zero_comp_pullbackCLM_reparam (hW := hW) hab]

end Interval

end TestFunction

namespace ContinuousLinearMap

open TestFunction

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  {Ω : Opens E} {W : Opens (E × ℝ)} {k : ℕ} {hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω}

/-- **The boundary of a product with the unit interval**: for a `(k + 1)`-current `T` on `Ω`,
`∂ ([[0, 1]] × T) = {1} × T - {0} × T - [[0, 1]] × ∂ T`, where `[[0, 1]] × T = T ∘ h`,
`{t} × T = T ∘ ιₜ^*` and `∂ T = T ∘ d`. -/
theorem comp_cylinderHomotopyCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L cylinderHomotopyCLM hW) ∘L extDerivCLM =
      T ∘L pullbackCLM (fun x ↦ (x, (1 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW ⟨zero_le_one, le_rfl⟩) -
        T ∘L pullbackCLM (fun x ↦ (x, (0 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW ⟨le_rfl, zero_le_one⟩) -
        (T ∘L extDerivCLM) ∘L cylinderHomotopyCLM hW := by
  rw [comp_assoc, cylinderHomotopyCLM_comp_extDerivCLM, comp_sub, comp_sub, comp_assoc]

/-- **The boundary of a product with the unit interval in degree zero**: for a `0`-current `T` on
`Ω`, `∂ ([[0, 1]] × T) = {1} × T - {0} × T`, where `[[0, 1]] × T = T ∘ h` and
`{t} × T = T ∘ ιₜ^*`. -/
theorem comp_cylinderHomotopyCLM_comp_extDerivCLM_finZero
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L cylinderHomotopyCLM hW) ∘L extDerivCLM =
      T ∘L pullbackCLM (fun x ↦ (x, (1 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW ⟨zero_le_one, le_rfl⟩) -
        T ∘L pullbackCLM (fun x ↦ (x, (0 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW ⟨le_rfl, zero_le_one⟩) := by
  rw [comp_assoc, cylinderHomotopyCLM_comp_extDerivCLM_finZero, comp_sub]

section Interval

variable {a b : ℝ} {hW : ∀ p ∈ W, p.2 ∈ uIcc a b → p.1 ∈ Ω}

/-- **The boundary of a product with an oriented interval**: for a `(k + 1)`-current `T` on `Ω`,
`∂ ([[a, b]] × T) = {b} × T - {a} × T - [[a, b]] × ∂ T`, where `[[a, b]] × T = T ∘ h_{a,b}`,
`{t} × T = T ∘ ιₜ^*` and `∂ T = T ∘ d`. -/
theorem comp_intervalCylinderHomotopyCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L intervalCylinderHomotopyCLM a b hW) ∘L extDerivCLM =
      T ∘L pullbackCLM (fun x ↦ (x, b)) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW right_mem_uIcc) -
        T ∘L pullbackCLM (fun x ↦ (x, a)) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW left_mem_uIcc) -
        (T ∘L extDerivCLM) ∘L intervalCylinderHomotopyCLM a b hW := by
  rw [comp_assoc, intervalCylinderHomotopyCLM_comp_extDerivCLM, comp_sub, comp_sub, comp_assoc]

/-- **The boundary of a product with an oriented interval in degree zero**: for a `0`-current `T`
on `Ω`, `∂ ([[a, b]] × T) = {b} × T - {a} × T`, where `[[a, b]] × T = T ∘ h_{a,b}` and
`{t} × T = T ∘ ιₜ^*`. -/
theorem comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_finZero
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L intervalCylinderHomotopyCLM a b hW) ∘L extDerivCLM =
      T ∘L pullbackCLM (fun x ↦ (x, b)) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW right_mem_uIcc) -
        T ∘L pullbackCLM (fun x ↦ (x, a)) (contDiffOn_id.prodMk contDiffOn_const)
          (isCompact_inter_preimage_prodMk_left hW left_mem_uIcc) := by
  rw [comp_assoc, intervalCylinderHomotopyCLM_comp_extDerivCLM_finZero, comp_sub]

end Interval

end ContinuousLinearMap

namespace Distribution

open TestFunction

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {W : Opens (E × ℝ)} {k : ℕ}

omit [CompleteSpace F] in
/-- **The mass of a slice**: `M({t} × T) ≤ M(T)` for a `k`-current `T` on `Ω`, where
`{t} × T = T ∘ ιₜ^*` is the pushforward along the slice `ιₜ : x ↦ (x, t)`, for the sup norm
on `E × ℝ`. -/
theorem mass_comp_pullbackCLM_prodMk_left_le {𝓕 : Type*}
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) {t : ℝ} {hp : ∀ K : Set (E × ℝ), IsCompact K → K ⊆ W →
      IsCompact ((Ω : Set E) ∩ (fun x ↦ (x, t)) ⁻¹' K)} :
    mass (T ∘ pullbackCLM (fun x ↦ (x, t)) (contDiffOn_id.prodMk contDiffOn_const) hp) ≤
      mass T := by
  refine (mass_comp_pullbackCLM_le T (L := 1) fun x _ ↦ ?_).trans_eq (by simp)
  rw [(hasFDerivAt_prodMk_left x t).fderiv, NNReal.coe_one]
  exact ContinuousLinearMap.norm_inl_le_one ℝ E ℝ

section Interval

variable {a b : ℝ} {hW : ∀ p ∈ W, p.2 ∈ uIcc a b → p.1 ∈ Ω}

/-- **The local mass of a product with an oriented interval**: on a set `U ⊆ E × ℝ`, the local
mass of `[[a, b]] × T = T ∘ h_{a,b}` is at most `|b - a|` times the local mass of `T` on the
projection to `E` of the part of `U` over `[[a, b]]`, for the sup norm on `E × ℝ`. -/
theorem localMass_comp_intervalCylinderHomotopyCLM_le {𝓕 : Type*}
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) (U : Set (E × ℝ)) :
    localMass (T ∘ intervalCylinderHomotopyCLM a b hW) U ≤
      ‖b - a‖ₑ * localMass T (Prod.fst '' (U ∩ univ ×ˢ uIcc a b)) := by
  refine localMass_le_iff.2 fun ω hωU hω ↦ ?_
  rw [mul_comm]
  refine enorm_apply_le_localMass_mul_of_forall_enorm_le T
    ((tsupport_intervalCylinderHomotopyCLM_subset ω).trans
      (image_mono (inter_subset_inter_left _ hωU))) fun x ↦ ?_
  rw [← ofReal_norm, Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal ((norm_intervalCylinderHomotopyCLM_apply_le ω
    fun t _ ↦ hω _).trans_eq (mul_one _))

/-- **The mass of a product with an oriented interval**: `M([[a, b]] × T) ≤ |b - a| M(T)` for a
`k`-current `T` on `Ω`, where `[[a, b]] × T = T ∘ h_{a,b}`, for the sup norm on `E × ℝ`. -/
theorem mass_comp_intervalCylinderHomotopyCLM_le {𝓕 : Type*}
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) : mass (T ∘ intervalCylinderHomotopyCLM a b hW) ≤ ‖b - a‖ₑ * mass T :=
  calc mass (T ∘ intervalCylinderHomotopyCLM a b hW)
      = localMass (T ∘ intervalCylinderHomotopyCLM a b hW) univ := localMass_univ.symm
    _ ≤ ‖b - a‖ₑ * localMass T (Prod.fst '' (univ ∩ univ ×ˢ uIcc a b)) :=
        localMass_comp_intervalCylinderHomotopyCLM_le T univ
    _ ≤ ‖b - a‖ₑ * mass T := by gcongr; exact localMass_le_mass

/-- **The mass of the boundary of a product with an oriented interval**:
`M(∂ ([[a, b]] × T)) ≤ 2 M(T) + |b - a| M(∂ T)` for a `(k + 1)`-current `T` on `Ω`, where
`[[a, b]] × T = T ∘ h_{a,b}` and `∂ T = T ∘ d`, for the sup norm on `E × ℝ`. -/
theorem mass_comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_le
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) :
    mass ((T ∘L intervalCylinderHomotopyCLM a b hW) ∘L extDerivCLM) ≤
      2 * mass T + ‖b - a‖ₑ * mass (T ∘L extDerivCLM) := by
  rw [ContinuousLinearMap.comp_intervalCylinderHomotopyCLM_comp_extDerivCLM,
    FunLike.coe_sub, FunLike.coe_sub, two_mul]
  refine (mass_sub_le ..).trans (add_le_add ((mass_sub_le ..).trans (add_le_add ?_ ?_)) ?_) <;>
    rw [ContinuousLinearMap.coe_comp]
  · exact mass_comp_pullbackCLM_prodMk_left_le T
  · exact mass_comp_pullbackCLM_prodMk_left_le T
  · exact mass_comp_intervalCylinderHomotopyCLM_le _

/-- **The mass of the boundary of a product with an oriented interval in degree zero**:
`M(∂ ([[a, b]] × T)) ≤ 2 M(T)` for a `0`-current `T` on `Ω`, where `[[a, b]] × T = T ∘ h_{a,b}`,
for the sup norm on `E × ℝ`. -/
theorem mass_comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_finZero_le
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V) :
    mass ((T ∘L intervalCylinderHomotopyCLM a b hW) ∘L extDerivCLM) ≤ 2 * mass T := by
  rw [ContinuousLinearMap.comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_finZero,
    FunLike.coe_sub, two_mul]
  refine (mass_sub_le ..).trans (add_le_add ?_ ?_) <;> rw [ContinuousLinearMap.coe_comp] <;>
    exact mass_comp_pullbackCLM_prodMk_left_le T

omit [NormedSpace ℝ V] in
/-- **Products with an oriented interval preserve locally finite mass.** If a map `T` on test
`k`-forms on `Ω` has locally finite mass, so does `[[a, b]] × T = T ∘ h_{a,b}` on `W`. For the
quantitative local mass bound see `Distribution.localMass_comp_intervalCylinderHomotopyCLM_le`. -/
theorem HasLocallyFiniteMass.comp_intervalCylinderHomotopyCLM
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) → V} (hT : HasLocallyFiniteMass T) :
    HasLocallyFiniteMass (T ∘ intervalCylinderHomotopyCLM a b hW) := by
  rw [hasLocallyFiniteMass_def] at hT ⊢
  intro K hK hKW
  obtain ⟨C, hC, hTC⟩ := hT _ ((hK.inter_right (isClosed_univ.prod isClosed_uIcc)).image
    continuous_fst) (by rintro _ ⟨p, ⟨hpK, -, hp⟩, rfl⟩; exact hW p (hKW hpK) hp)
  refine ⟨C * |b - a|, by positivity, fun ω hω ↦ ?_⟩
  have hb : ‖(intervalCylinderHomotopyCLM a b hW ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ ≤
      |b - a| * ‖(ω : E × ℝ →ᵇ (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)‖ :=
    (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦
      norm_intervalCylinderHomotopyCLM_apply_le ω fun t _ ↦
        BoundedContinuousFunction.norm_coe_le_norm
          (ω : E × ℝ →ᵇ (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) (x, t)
  calc ‖(T ∘ intervalCylinderHomotopyCLM a b hW) ω‖
      ≤ C * ‖(intervalCylinderHomotopyCLM a b hW ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ :=
        hTC _ ((tsupport_intervalCylinderHomotopyCLM_subset ω).trans
          (image_mono (inter_subset_inter_left _ hω)))
    _ ≤ C * (|b - a| * ‖(ω : E × ℝ →ᵇ (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)‖) := by gcongr
    _ = C * |b - a| * ‖(ω : E × ℝ →ᵇ (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)‖ := (mul_assoc ..).symm

/-- **Products with an oriented interval preserve local normality**: if `T` is a locally normal
`k`-current on `Ω`, then `[[a, b]] × T = T ∘ h_{a,b}` is a locally normal `(k + 1)`-current on
`W`. -/
theorem IsLocallyNormal.comp_intervalCylinderHomotopyCLM
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V} (hT : IsLocallyNormal T) :
    IsLocallyNormal (T ∘L intervalCylinderHomotopyCLM a b hW) := by
  rw [isLocallyNormal_succ_iff, ContinuousLinearMap.coe_comp]
  refine ⟨hT.hasLocallyFiniteMass.comp_intervalCylinderHomotopyCLM, ?_⟩
  cases k with
  | zero =>
    rw [ContinuousLinearMap.comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_finZero,
      FunLike.coe_sub, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
    have hT := isLocallyNormal_finZero_iff.1 hT
    exact hT.comp_pullbackCLM.sub hT.comp_pullbackCLM
  | succ k =>
    have hT := isLocallyNormal_succ_iff.1 hT
    rw [ContinuousLinearMap.comp_intervalCylinderHomotopyCLM_comp_extDerivCLM, FunLike.coe_sub,
      FunLike.coe_sub, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.coe_comp]
    exact (hT.1.comp_pullbackCLM.sub hT.1.comp_pullbackCLM).sub
      hT.2.comp_intervalCylinderHomotopyCLM

/-- **Products with an oriented interval preserve normality**: if `T` is a normal `k`-current on
`Ω`, then `[[a, b]] × T = T ∘ h_{a,b}` is a normal `(k + 1)`-current on `W`. -/
theorem IsNormal.comp_intervalCylinderHomotopyCLM
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V} (hT : IsNormal T) :
    IsNormal (T ∘L intervalCylinderHomotopyCLM a b hW) := by
  rw [isNormal_succ_iff, ContinuousLinearMap.coe_comp]
  refine ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top enorm_ne_top hT.mass_ne_top)
    (mass_comp_intervalCylinderHomotopyCLM_le T), ?_⟩
  cases k with
  | zero =>
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (isNormal_finZero_iff.1 hT))
      (mass_comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_finZero_le T)
  | succ k =>
    have hT := isNormal_succ_iff.1 hT
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT.1,
      ENNReal.mul_ne_top enorm_ne_top hT.2⟩)
      (mass_comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_le T)

end Interval

section UnitInterval

variable {hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
private theorem forall_mem_uIcc_zero_one (hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω) :
    ∀ p ∈ W, p.2 ∈ uIcc (0 : ℝ) 1 → p.1 ∈ Ω := by
  rwa [uIcc_of_le zero_le_one]

/-- **The mass of a product with the unit interval**: `M([[0, 1]] × T) ≤ M(T)` for a `k`-current
`T` on `Ω`, where `[[0, 1]] × T = T ∘ h`, for the sup norm on `E × ℝ`. -/
theorem mass_comp_cylinderHomotopyCLM_le {𝓕 : Type*} [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] (T : 𝓕) :
    mass (T ∘ cylinderHomotopyCLM hW) ≤ mass T := by
  simpa [← intervalCylinderHomotopyCLM_zero_one (forall_mem_uIcc_zero_one hW) hW] using
    mass_comp_intervalCylinderHomotopyCLM_le (hW := forall_mem_uIcc_zero_one hW) T

/-- **The mass of the boundary of a product with the unit interval**:
`M(∂ ([[0, 1]] × T)) ≤ 2 M(T) + M(∂ T)` for a `(k + 1)`-current `T` on `Ω`, where
`[[0, 1]] × T = T ∘ h` and `∂ T = T ∘ d`, for the sup norm on `E × ℝ`. -/
theorem mass_comp_cylinderHomotopyCLM_comp_extDerivCLM_le
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) :
    mass ((T ∘L cylinderHomotopyCLM hW) ∘L extDerivCLM) ≤
      2 * mass T + mass (T ∘L extDerivCLM) := by
  simpa [← intervalCylinderHomotopyCLM_zero_one (forall_mem_uIcc_zero_one hW) hW] using
    mass_comp_intervalCylinderHomotopyCLM_comp_extDerivCLM_le
      (hW := forall_mem_uIcc_zero_one hW) T

end UnitInterval

end Distribution
