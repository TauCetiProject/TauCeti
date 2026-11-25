/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Localization
public import TauCeti.Analysis.Holder.OpenSet.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Multiplication of `C^{k,α}(Ω)` by smooth cutoffs

Let `Ω` be an open set of a real normed space `E`, and let `χ : E → ℝ` be a `C^{k+1}` function
whose iterated derivatives through order `k + 1` are bounded by `N`, and whose support stays at
distance `δ > 0` from the complement of `Ω`: the `δ`-thickening of `tsupport χ` lies in `Ω`. For
`α ≤ 1`, multiplication by `χ` is a bounded linear map from `C^{k,α}(Ω, F)` to the whole-space
Hölder space `C^{k,α}(E, F)`, of operator norm at most `2^k N (k + 8 + 2 δ^(-α))`
(`TauCeti.CkHolderSpaceOn.cutoffSMulL`); its composition with restriction is a bounded operator on
`C^{k,α}(Ω, F)` (`TauCeti.CkHolderSpaceOn.cutoffSMulOnL`).

No convexity of `Ω` is needed, unlike for products of two elements of `C^{k,α}(Ω)`
(`ContinuousLinearMap.compCkHolderOn₂`) or for the cutoff of local data on a convex set
(`TauCeti.CkHolderSpace.cutoff`). The lower derivative fields of an element of `C^{k,α}(Ω)` need
not be Hölder on `Ω` (across a slit they jump), but they are Lipschitz on every ball of radius
`δ` centred in `tsupport χ`, since such a ball lies in `Ω` and is convex. So the Leibniz rule gives
a Hölder bound for the `k`-th derivative of `χ f` between points at distance less than `δ`, and
at larger distances the supremum bound suffices
(`TauCeti.holderWith_iteratedFDeriv_cutoff_smul_of_thickening_subset`). The
distance `δ` exists whenever `tsupport χ` is a compact subset of `Ω`
(`IsCompact.exists_thickening_subset_open`), the case of the functions of a partition of unity
subordinate to a finite atlas.

## Main declarations

* `TauCeti.CkHolderSpaceOn.cutoffSMulL`: multiplication by `χ`, from `C^{k,α}(Ω, F)` to
  `C^{k,α}(E, F)`, with `TauCeti.CkHolderSpaceOn.norm_cutoffSMulL_le`.
* `TauCeti.CkHolderSpaceOn.cutoffSMulOnL`: multiplication by `χ` as an operator on
  `C^{k,α}(Ω, F)`, with `TauCeti.CkHolderSpaceOn.norm_cutoffSMulOnL_le`.
-/

public section

noncomputable section

open Set Metric
open scoped NNReal Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace CkHolderSpaceOn

variable {k : ℕ} {α : ℝ≥0} {Ω : TopologicalSpace.Opens E} {χ : E → ℝ} {N δ : ℝ≥0}

section cutoff

variable (hχ : ContDiff ℝ (k + 1) χ) (hδ : 0 < δ)
  (hχΩ : thickening δ (tsupport χ) ⊆ Ω) (hα : α ≤ 1)
  (hχb : ∀ i ≤ k + 1, ∀ x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ N)

omit [NormedSpace ℝ E] in
include hδ hχΩ in
private theorem tsupport_subset : tsupport χ ⊆ Ω :=
  (self_subset_thickening (by exact_mod_cast hδ) _).trans hχΩ

private theorem norm_iteratedFDeriv_extend_le_nnnorm (f : CkHolderSpaceOn k α Ω F) {i : ℕ}
    (hi : i ≤ k) (x : E) (hx : x ∈ Ω) :
    ‖_root_.iteratedFDeriv ℝ i f.extend x‖ ≤ ‖f‖₊ := by
  rw [coe_nnNorm]
  exact f.norm_iteratedFDeriv_extend_le hi ⟨x, hx⟩

include hχ hδ hχΩ hχb in
private theorem norm_iteratedFDeriv_smul_extend_le (f : CkHolderSpaceOn k α Ω F) {j : ℕ}
    (hj : j ≤ k) (x : E) :
    ‖_root_.iteratedFDeriv ℝ j (fun x ↦ χ x • f.extend x) x‖ ≤ (2 : ℝ) ^ j * N * ‖f‖₊ :=
  norm_iteratedFDeriv_cutoff_smul_le f.contDiffOn_extend (hχ.of_le (by simp)) Ω.isOpen
    (tsupport_subset hδ hχΩ) hj
    (fun _ hi x hx ↦ norm_iteratedFDeriv_extend_le_nnnorm f hi x hx)
    (fun i hi ↦ hχb i (by omega)) x

include hχ hδ hχΩ hα hχb in
private theorem holderWith_iteratedFDeriv_smul_extend (f : CkHolderSpaceOn k α Ω F) :
    HolderWith ((2 : ℝ≥0) ^ k * N * (‖f‖₊ + 6 * ‖f‖₊ + 2 * ‖f‖₊ * δ ^ (-(α : ℝ)))) α
      (_root_.iteratedFDeriv ℝ k (fun x ↦ χ x • f.extend x)) :=
  holderWith_iteratedFDeriv_cutoff_smul_of_thickening_subset f.contDiffOn_extend hχ Ω.isOpen hδ
    hχΩ hα
    (fun _ hi x hx ↦ norm_iteratedFDeriv_extend_le_nnnorm f hi x hx) hχb
    ((f.holderOnWith_iteratedFDeriv f.extend_apply).mono_const
      (by exact_mod_cast f.nnHolderNorm_iteratedFDeriv_le))

/-- The product of a cutoff with an element of `C^{k,α}(Ω)`, extended by zero, as an element of
the whole-space Hölder space `C^{k,α}(E)`. -/
private def cutoffSMul (f : CkHolderSpaceOn k α Ω F) : CkHolderSpace k α E F :=
  CkHolderSpace.ofContDiff (fun x ↦ χ x • f.extend x)
    (f.contDiffOn_extend.contDiff_smul_of_tsupport_subset Ω.isOpen
      (hχ.of_le (by simp) : ContDiff ℝ k χ).contDiffOn (tsupport_subset hδ hχΩ))
    (fun _ hj ↦ ⟨_, norm_iteratedFDeriv_smul_extend_le hχ hδ hχΩ hχb f hj⟩)
    ⟨_, holderWith_iteratedFDeriv_smul_extend hχ hδ hχΩ hα hχb f⟩

private theorem cutoffSMul_apply (f : CkHolderSpaceOn k α Ω F) (x : E) :
    cutoffSMul hχ hδ hχΩ hα hχb f x = χ x • f.extend x :=
  congrFun (CkHolderSpace.coe_ofContDiff _ _ _ _) x

include hδ hχΩ in
/-- Outside `Ω` the cutoff vanishes, and on `Ω` the extension by zero is the element itself. -/
private theorem smul_extend_eq (f : CkHolderSpaceOn k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) (x : E) : χ x • f.extend x = χ x • g x := by
  by_cases hx : x ∈ (Ω : Set E)
  · rw [f.extend_apply ⟨x, hx⟩, hg ⟨x, hx⟩]
  · have : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_subset hδ hχΩ h)
    simp [this]

private theorem norm_cutoffSMul_le (f : CkHolderSpaceOn k α Ω F) :
    ‖cutoffSMul hχ hδ hχΩ hα hχb f‖ ≤
      (2 : ℝ) ^ k * N * (k + 8 + 2 * (δ : ℝ) ^ (-(α : ℝ))) * ‖f‖ := by
  have hu : ⇑(cutoffSMul hχ hδ hχΩ hα hχb f) = fun x ↦ χ x • f.extend x :=
    funext (cutoffSMul_apply hχ hδ hχΩ hα hχb f)
  refine (CkHolderSpace.norm_le_of_norm_iteratedFDeriv_le_of_holderWith
    (M := (2 : ℝ) ^ k * N * ‖f‖) (fun i hi x ↦ ?_)
    (by rw [hu]; exact holderWith_iteratedFDeriv_smul_extend hχ hδ hχΩ hα hχb f)).trans ?_
  · rw [hu]
    exact (norm_iteratedFDeriv_smul_extend_le hχ hδ hχΩ hχb f hi x).trans (by
      gcongr
      · norm_num
      · exact (coe_nnNorm f).le)
  · refine le_of_eq ?_
    push_cast
    ring

/-- **Multiplication by a cutoff**, as a continuous linear map from `C^{k,α}(Ω)` to the
whole-space Hölder space `C^{k,α}(E)`: an element `f` is sent to `χ • f`, extended by zero
outside `Ω`. Here `χ` is `C^{k+1}` with derivatives through order `k + 1` bounded by `N`, the
`δ`-thickening of its support lies in `Ω`, and `α ≤ 1`. The operator norm is at most
`2^k N (k + 8 + 2 δ^(-α))` (`TauCeti.CkHolderSpaceOn.norm_cutoffSMulL_le`). -/
def cutoffSMulL : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpace k α E F :=
  LinearMap.mkContinuous
    { toFun := cutoffSMul hχ hδ hχΩ hα hχb
      map_add' f g := CkHolderSpace.ext fun x ↦ by
        simp only [cutoffSMul_apply, CkHolderSpace.coe_add, Pi.add_apply]
        rw [smul_extend_eq hδ hχΩ (f + g) (g := f.extend + g.extend) fun y ↦ by
          simp [coe_add, f.extend_apply, g.extend_apply], Pi.add_apply, smul_add]
      map_smul' c f := CkHolderSpace.ext fun x ↦ by
        simp only [cutoffSMul_apply, CkHolderSpace.coe_smul, Pi.smul_apply, RingHom.id_apply]
        rw [smul_extend_eq hδ hχΩ (c • f) (g := c • f.extend) fun y ↦ by
          simp [coe_smul, f.extend_apply], Pi.smul_apply, smul_comm] }
    ((2 : ℝ) ^ k * N * (k + 8 + 2 * (δ : ℝ) ^ (-(α : ℝ))))
    (norm_cutoffSMul_le hχ hδ hχΩ hα hχb)

/-- Multiplication by a cutoff is multiplication of the extension by zero. -/
@[simp]
theorem coe_cutoffSMulL (f : CkHolderSpaceOn k α Ω F) :
    ⇑(cutoffSMulL hχ hδ hχΩ hα hχb f) = fun x ↦ χ x • f.extend x :=
  funext (cutoffSMul_apply hχ hδ hχΩ hα hχb f)

/-- Multiplication by a cutoff is pointwise multiplication of the extension by zero. -/
@[simp]
theorem cutoffSMulL_apply (f : CkHolderSpaceOn k α Ω F) (x : E) :
    cutoffSMulL hχ hδ hχΩ hα hχb f x = χ x • f.extend x :=
  congrFun (coe_cutoffSMulL hχ hδ hχΩ hα hχb f) x

/-- On `Ω`, multiplication by a cutoff is pointwise multiplication. -/
theorem cutoffSMulL_apply_coe (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    cutoffSMulL hχ hδ hχΩ hα hχb f x = χ x • f x := by
  rw [cutoffSMulL_apply, f.extend_apply]

/-- The product with a cutoff vanishes outside the support of the cutoff. -/
theorem cutoffSMulL_apply_of_notMem {x : E} (hx : x ∉ tsupport χ)
    (f : CkHolderSpaceOn k α Ω F) : cutoffSMulL hχ hδ hχΩ hα hχb f x = 0 := by
  rw [cutoffSMulL_apply, image_eq_zero_of_notMem_tsupport hx, zero_smul]

/-- The topological support of a product with a cutoff lies in that of the cutoff. -/
theorem tsupport_cutoffSMulL_subset (f : CkHolderSpaceOn k α Ω F) :
    tsupport (cutoffSMulL hχ hδ hχΩ hα hχb f) ⊆ tsupport χ := by
  rw [coe_cutoffSMulL]
  exact tsupport_smul_subset_left _ _

/-- Multiplication by a cutoff has operator norm at most `2^k N (k + 8 + 2 δ^(-α))`. -/
theorem norm_cutoffSMulL_le :
    ‖cutoffSMulL (F := F) hχ hδ hχΩ hα hχb‖ ≤
      (2 : ℝ) ^ k * N * (k + 8 + 2 * (δ : ℝ) ^ (-(α : ℝ))) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- **Multiplication by a cutoff** as a bounded operator on `C^{k,α}(Ω)`: the product with `χ`,
restricted back to `Ω`. -/
def cutoffSMulOnL : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k α Ω F :=
  (CkHolderSpace.restrictOnL Ω).comp (cutoffSMulL hχ hδ hχΩ hα hχb)

/-- Multiplication by a cutoff on `C^{k,α}(Ω)` is pointwise multiplication. -/
@[simp]
theorem cutoffSMulOnL_apply (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    cutoffSMulOnL hχ hδ hχΩ hα hχb f x = χ x • f x := by
  rw [cutoffSMulOnL, ContinuousLinearMap.comp_apply, CkHolderSpace.restrictOnL_apply,
    cutoffSMulL_apply_coe]

/-- Multiplication by a cutoff on `C^{k,α}(Ω)` has operator norm at most
`2^k N (k + 8 + 2 δ^(-α))`. -/
theorem norm_cutoffSMulOnL_le :
    ‖cutoffSMulOnL (F := F) hχ hδ hχΩ hα hχb‖ ≤
      (2 : ℝ) ^ k * N * (k + 8 + 2 * (δ : ℝ) ^ (-(α : ℝ))) := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc
    _ ≤ 1 * ((2 : ℝ) ^ k * N * (k + 8 + 2 * (δ : ℝ) ^ (-(α : ℝ)))) := by
      gcongr
      · exact CkHolderSpace.norm_restrictOnL_le_one (E := E) (F := F) (k := k) (α := α) Ω
      · exact norm_cutoffSMulL_le hχ hδ hχΩ hα hχb
    _ = _ := one_mul _

end cutoff

end CkHolderSpaceOn

end TauCeti
