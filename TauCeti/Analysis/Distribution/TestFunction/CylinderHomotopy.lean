/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.CylinderHomotopy
public import TauCeti.Analysis.Distribution.TestFunction.Pullback
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# The product of a current with the unit interval

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

Write `ιₜ : x ↦ (x, t)` for the slice at time `t`, so that `ιₜ^*` is the pullback
`TestFunction.pullbackCLM` and `{t} × T = T ∘ ιₜ^*` is the pushforward of `T` along `ιₜ`. The
cylinder homotopy identity `h (d ω) = ι₁^* ω - ι₀^* ω - d (h ω)` on test forms gives the
**boundary formula**

`∂ ([[0, 1]] × T) = {1} × T - {0} × T - [[0, 1]] × ∂ T`,

where `∂ T = T ∘ d`; in degree zero the last term is absent. For the operator-norm mass of
`Distribution.mass`, with the sup norm on `E × ℝ`, this gives `M([[0, 1]] × T) ≤ M(T)` and
`M(∂ ([[0, 1]] × T)) ≤ 2 M(T) + M(∂ T)`. These are the product and homotopy formulas used to
build homotopies between pushforwards of currents and to estimate their masses.

## Main declarations

* `TopologicalSpace.Opens.cylinder`: the open cylinder `Ω × ℝ`, and `TestFunction.timeCutoff`, a
  test function of time equal to one near `[0, 1]`, used to cut forms on it off in time.
* `TestFunction.cylinderHomotopyCLM`: the cylinder homotopy operator on test forms, as a
  continuous linear map.
* `TauCeti.isCompact_inter_preimage_prodMk_left`: the slices `ι₀` and `ι₁` are proper from `Ω`
  to `W`, so the pushforwards `{t} × T` are defined.
* `TestFunction.pullbackCLM_prodMk_left_apply`: for `t ∈ [0, 1]`, `ιₜ^* ω` is `ω (·, t)` restricted
  to `E`.
* `TestFunction.tsupport_cylinderHomotopyCLM_subset`,
  `TestFunction.norm_cylinderHomotopyCLM_apply_le`: its support and pointwise bound.
* `TestFunction.cylinderHomotopyCLM_comp_extDerivCLM`: `h ∘ d = ι₁^* - ι₀^* - d ∘ h`, and
  `TestFunction.cylinderHomotopyCLM_comp_extDerivCLM_finZero` in degree zero.
* `ContinuousLinearMap.comp_cylinderHomotopyCLM_comp_extDerivCLM`: the boundary formula
  `∂ ([[0, 1]] × T) = {1} × T - {0} × T - [[0, 1]] × ∂ T`, and
  `ContinuousLinearMap.comp_cylinderHomotopyCLM_comp_extDerivCLM_finZero` in degree zero.
* `Distribution.mass_comp_cylinderHomotopyCLM_le`: `M([[0, 1]] × T) ≤ M(T)`.
* `Distribution.mass_comp_pullbackCLM_prodMk_left_le`: `M({t} × T) ≤ M(T)` for `t ∈ [0, 1]`.
* `Distribution.mass_comp_cylinderHomotopyCLM_comp_extDerivCLM_le`:
  `M(∂ ([[0, 1]] × T)) ≤ 2 M(T) + M(∂ T)`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.8 (the product `[[0, 1]] × T` and the homotopy
  formula).
-/

public section

noncomputable section

open Set TopologicalSpace TauCeti
open scoped Distributions ENNReal BoundedContinuousFunction Topology

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

/-- **The slices are proper.** If the part of `W` over `[0, 1]` lies over `Ω`, then for
`t ∈ [0, 1]` the slice `x ↦ (x, t)` is proper from `Ω` to `W`. -/
theorem isCompact_inter_preimage_prodMk_left [T2Space X]
    (hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (K : Set (X × ℝ)) (hK : IsCompact K) (hKW : K ⊆ W) :
    IsCompact ((Ω : Set X) ∩ (fun x ↦ (x, t)) ⁻¹' K) := by
  rw [inter_eq_right.2 fun x hx ↦ hW (x, t) (hKW hx) ht]
  exact (hK.image continuous_fst).of_isClosed_subset
    (hK.isClosed.preimage (continuous_id.prodMk continuous_const)) fun x hx ↦ ⟨_, hx, rfl⟩

end TauCeti

namespace TopologicalSpace.Opens

variable {X : Type*} [TopologicalSpace X] {Ω : Opens X}

/-- The open **cylinder** `Ω × ℝ` over an open set `Ω`, the main domain of the cylinder homotopy
operator `TestFunction.cylinderHomotopyCLM`. -/
def cylinder (Ω : Opens X) : Opens (X × ℝ) :=
  ⟨(Ω : Set X) ×ˢ univ, Ω.isOpen.prod isOpen_univ⟩

@[simp]
theorem mem_cylinder {p : X × ℝ} : p ∈ Ω.cylinder ↔ p.1 ∈ Ω := by
  simp [cylinder, ← SetLike.mem_coe]

/-- The product of `Ω` with the whole line lies in the cylinder over `Ω`; this is the form in
which `TestFunction.prodSMulCLM` takes a product domain. -/
theorem prod_top_subset_cylinder : (Ω : Set X) ×ˢ ((⊤ : Opens ℝ) : Set ℝ) ⊆ Ω.cylinder :=
  fun _ hp ↦ mem_cylinder.2 hp.1

end TopologicalSpace.Opens

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {W : Opens (E × ℝ)} {k : ℕ}

/-- A test function of time equal to one on a neighbourhood of `[0, 1]`. Multiplying a form on a
cylinder by it cuts the form off in time without changing it near times in `[0, 1]`. -/
def timeCutoff : 𝓓((⊤ : Opens ℝ), ℝ) :=
  (exists_eventually_eq_one (Ω := ⊤) (n := ⊤) isCompact_Icc
    (subset_univ (Icc (0 : ℝ) 1))).choose

/-- The time cutoff is equal to one on a neighbourhood of `[0, 1]`. -/
theorem timeCutoff_eventually_eq_one : ∀ᶠ t in 𝓝ˢ (Icc (0 : ℝ) 1), timeCutoff t = 1 :=
  (exists_eventually_eq_one (Ω := ⊤) (n := ⊤) isCompact_Icc
    (subset_univ (Icc (0 : ℝ) 1))).choose_spec.1

/-- The time cutoff is equal to one on `[0, 1]`. -/
theorem timeCutoff_eq_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : timeCutoff t = 1 :=
  timeCutoff_eventually_eq_one.self_of_nhdsSet t ht

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
/-- At a time `t ∈ [0, 1]`, the pullback along the slice `x ↦ (x, t)` is `ω (x, t)` restricted to
`E`, at every point of `E`. -/
theorem pullbackCLM_prodMk_left_apply (hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω)
    {m : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
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

end ContinuousLinearMap

namespace Distribution

open TestFunction

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {W : Opens (E × ℝ)} {k : ℕ} {hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω}

/-- **The mass of a product with the unit interval**: `M([[0, 1]] × T) ≤ M(T)` for a `k`-current
`T` on `Ω`, where `[[0, 1]] × T = T ∘ h`, for the sup norm on `E × ℝ`. -/
theorem mass_comp_cylinderHomotopyCLM_le {𝓕 : Type*} [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] (T : 𝓕) :
    mass (T ∘ cylinderHomotopyCLM hW) ≤ mass T := by
  refine mass_le_iff.2 fun ω hω ↦ ?_
  have hb : ‖(cylinderHomotopyCLM hW ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ ≤ 1 :=
    (BoundedContinuousFunction.norm_le zero_le_one).2 fun x ↦
      norm_cylinderHomotopyCLM_apply_le (hW := hW) ω fun t _ ↦ hω _
  calc ‖T (cylinderHomotopyCLM hW ω)‖ₑ
      ≤ mass T * ‖(cylinderHomotopyCLM hW ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ :=
        enorm_apply_le_mass_mul T _
    _ ≤ mass T * 1 := by
        gcongr
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hb
    _ = mass T := mul_one _

omit [CompleteSpace F] in
/-- **The mass of a slice**: `M({t} × T) ≤ M(T)` for a `k`-current `T` on `Ω` and `t ∈ [0, 1]`,
where `{t} × T = T ∘ ιₜ^*` is the pushforward along the slice `ιₜ : x ↦ (x, t)`, for the sup norm
on `E × ℝ`. -/
theorem mass_comp_pullbackCLM_prodMk_left_le {𝓕 : Type*}
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    mass (T ∘ pullbackCLM (fun x ↦ (x, t)) (contDiffOn_id.prodMk contDiffOn_const)
      (isCompact_inter_preimage_prodMk_left hW ht)) ≤ mass T := by
  refine (mass_comp_pullbackCLM_le T (L := 1) fun x _ ↦ ?_).trans_eq (by simp)
  rw [(hasFDerivAt_prodMk_left x t).fderiv, NNReal.coe_one]
  exact ContinuousLinearMap.norm_inl_le_one ℝ E ℝ

/-- **The mass of the boundary of a product with the unit interval**:
`M(∂ ([[0, 1]] × T)) ≤ 2 M(T) + M(∂ T)` for a `(k + 1)`-current `T` on `Ω`, where
`[[0, 1]] × T = T ∘ h` and `∂ T = T ∘ d`, for the sup norm on `E × ℝ`. -/
theorem mass_comp_cylinderHomotopyCLM_comp_extDerivCLM_le
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) :
    mass ((T ∘L cylinderHomotopyCLM hW) ∘L extDerivCLM) ≤
      2 * mass T + mass (T ∘L extDerivCLM) := by
  rw [ContinuousLinearMap.comp_cylinderHomotopyCLM_comp_extDerivCLM,
    FunLike.coe_sub, FunLike.coe_sub, two_mul]
  refine (mass_sub_le ..).trans (add_le_add ((mass_sub_le ..).trans (add_le_add ?_ ?_)) ?_) <;>
    rw [ContinuousLinearMap.coe_comp]
  · exact mass_comp_pullbackCLM_prodMk_left_le (hW := hW) T ⟨zero_le_one, le_rfl⟩
  · exact mass_comp_pullbackCLM_prodMk_left_le (hW := hW) T ⟨le_rfl, zero_le_one⟩
  · exact mass_comp_cylinderHomotopyCLM_le _

end Distribution
