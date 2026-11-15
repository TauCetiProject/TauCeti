/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.VectorBundle.FiberScaling
public import TauCeti.Analysis.Calculus.DifferentialForm.Relative.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Relative.FirstJet
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# The relative Poincaré lemma on the total space of a vector bundle

Let `V → B` be a smooth real vector bundle. Fibre scaling
`H : V × [0, 1] → V`, `(v, t) ↦ t • v` (`TauCeti.vectorBundleFiberScaling`), is a smooth homotopy
from the retraction `ρ = 0 ∘ π` of `V` onto its zero section to the identity, and it fixes the
zero section at all times. Applying the homotopy operator of the cylinder `V × [0, 1]` to `H^* η`
gives the *relative Poincaré operator* `P` (`TauCeti.vectorBundlePoincareHomotopy`)

`β = P η = h (H^* η)`, `β(v)(w₁, …, wₖ) = ∫₀¹ η(t • v)(dH ∂ₜ, dH w₁, …, dH wₖ) dt`.

Since `H` is constant in time along the zero section, `dH ∂ₜ = 0` there, so `β` vanishes at
every point of the zero section as a full ambient tensor, for every form `η`
(`TauCeti.vectorBundlePoincareHomotopy_zeroSection`), even when `η` does not. For a `C¹` form `η`
of positive degree, the cochain-homotopy identity of the homotopy operator gives

`d (P η) + P (d η) = η - ρ^* η`

(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv`), so
`d β = η - ρ^* η` when `η` is closed (`TauCeti.mextDeriv_vectorBundlePoincareHomotopy`), and
`ρ^* η = π^* (i^* η)` only depends on the restriction `i^* η` of `η` to the zero section `i`
(`TauCeti.mpullback_zeroSection_comp_proj`). Hence `d β = η` as soon as `i^* η = 0`
(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy_of_mpullback_zeroSection_eq_zero`), although `η`
need not vanish as a full ambient tensor along the zero section. The operator preserves `C^r`
regularity over a `C^(r + 1)` bundle (`TauCeti.IsSmoothForm.vectorBundlePoincareHomotopy`) and is
additive on continuous forms (`TauCeti.vectorBundlePoincareHomotopy_add`). The identities above
need only a `C²` bundle.

In the preferred chart at a point of the total space, with a base coordinate and a fibre
coordinate, fibre scaling scales the fibre coordinate, so `P` is read there as the flat relative
Poincaré operator `TauCeti.fiberwisePoincareHomotopy` of the coordinate expression of `η`
(`TauCeti.inChartAt_vectorBundlePoincareHomotopy`). Hence at a point of the zero section at which
`η` vanishes as a full ambient tensor, `β` has *zero first jet*: it vanishes there and its
coordinate expression has derivative zero there
(`TauCeti.hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`). Vanishing of
`i^* η` alone does not suffice for this.

Everything transports along a diffeomorphism `Φ` from the total space onto a manifold `M`, such as
a tubular neighbourhood of an embedded submanifold
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`). With the zero-section inclusion
`i = Φ ∘ 0` and the retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹`, every closed `C^r` form `η` of positive
degree on `M`, with `r ≥ 1`, has a `C^r` form `β` with `d β = η - ρ^* η` that vanishes along
`i` as a full ambient tensor (`Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback`), and
`d β = η` when `i^* η = 0` (`Diffeomorph.exists_isSmoothForm_relative_primitive`). This needs `Φ`
and the bundle to be `C^(r + 1)`. At every point of the image of `i` at which `η` vanishes as a
full ambient tensor, `β` has zero first jet, since pullback along `Φ⁻¹` preserves zero first jets
(`TauCeti.RoughForm.hasFDerivWithinAt_inChartAt_mpullback`). This is the primitive used to compare
two symplectic forms relative to a submanifold. When the two forms agree as full ambient tensors
along the submanifold, the zero first jet of the primitive makes the Moser vector field vanish to
first order there.

The flat counterpart on an open set stable under scaling the normal coordinate is
`IsOpen.exists_contDiffOn_relative_primitive`. The base may have boundary or corners and the
coefficient space is any Banach space.

## Main declarations

* `TauCeti.vectorBundlePoincareHomotopy`: the relative Poincaré operator `β = h (H^* η)`.
* `TauCeti.vectorBundlePoincareHomotopy_zeroSection`: `β` vanishes along the zero section.
* `TauCeti.mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv`:
  `d (P η) + P (d η) = η - ρ^* η`.
* `TauCeti.mextDeriv_vectorBundlePoincareHomotopy`: `d β = η - ρ^* η` for closed `η`.
* `TauCeti.inChartAt_vectorBundlePoincareHomotopy`: in a bundle chart, `P` is the flat relative
  Poincaré operator of the coordinate expression.
* `TauCeti.hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`: `β` has zero
  first jet where `η` vanishes along the zero section.
* `Diffeomorph.exists_isSmoothForm_relative_primitive`: the relative Poincaré lemma on a tube, with
  zero first jet where `η` vanishes along the core.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §6.2 (the relative Poincaré lemma by fibre scaling).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {B FV : Type*} {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-! ### The relative Poincaré operator -/

/-- The **relative Poincaré operator** of a vector bundle: the homotopy operator of the cylinder
`V × [0, 1]` applied to the pullback of `η` by fibre scaling `H(v, t) = t • v`,

`β(v)(w₁, …, wₖ) = ∫₀¹ η(t • v)(dH ∂ₜ, dH (w₁, 0), …, dH (wₖ, 0)) dt`.

It vanishes along the zero section (`TauCeti.vectorBundlePoincareHomotopy_zeroSection`), and for a
closed `C¹` form `η`, `d β = η - ρ^* η` with `ρ` the retraction onto the zero section
(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy`). -/
def vectorBundlePoincareHomotopy
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) :
    RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F k :=
  homotopyOperator
    (mpullback ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
      (vectorBundleFiberScaling FV V) η)

/-- The relative Poincaré operator is the homotopy operator of the pullback by fibre scaling. -/
theorem vectorBundlePoincareHomotopy_def
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) :
    vectorBundlePoincareHomotopy η =
      homotopyOperator (mpullback ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
        (vectorBundleFiberScaling FV V) η) :=
  (rfl)

/-- The relative Poincaré operator of the zero form is zero. -/
@[simp]
theorem vectorBundlePoincareHomotopy_zero :
    vectorBundlePoincareHomotopy
      (0 : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) = 0 := by
  rw [vectorBundlePoincareHomotopy_def, mpullback_zero, homotopyOperator_zero]

/-- The relative Poincaré operator commutes with real scalar multiplication of forms. -/
@[simp]
theorem vectorBundlePoincareHomotopy_smul (c : ℝ)
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) :
    vectorBundlePoincareHomotopy (c • η) = c • vectorBundlePoincareHomotopy η := by
  rw [vectorBundlePoincareHomotopy_def, mpullback_smul, homotopyOperator_smul,
    vectorBundlePoincareHomotopy_def]

variable [VectorBundle ℝ FV V]

/-- **The relative Poincaré operator vanishes along the zero section**, as a full ambient tensor,
for every form `η`: fibre scaling kills the time direction there. -/
@[simp]
theorem vectorBundlePoincareHomotopy_zeroSection
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) (b : B) :
    vectorBundlePoincareHomotopy η (zeroSection FV V b) = 0 :=
  homotopyOperator_apply_eq_zero fun t _ ↦ by
    rw [mpullback_apply]
    exact (η _).map_coord_zero 0 (mfderiv_vectorBundleFiberScaling_zeroSection_time b t _)

/-- The relative Poincaré operator is additive on continuous forms, over a `C¹` vector bundle on a
`C¹` base. -/
theorem vectorBundlePoincareHomotopy_add [IsManifold IB 1 B] [ContMDiffVectorBundle 1 FV V IB]
    {η₁ η₂ : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (h₁ : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η₁) (h₂ : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η₂) :
    vectorBundlePoincareHomotopy (η₁ + η₂) =
      vectorBundlePoincareHomotopy η₁ + vectorBundlePoincareHomotopy η₂ := by
  rw [vectorBundlePoincareHomotopy_def, mpullback_add,
    homotopyOperator_add (h₁.mpullback contMDiff_vectorBundleFiberScaling)
      (h₂.mpullback contMDiff_vectorBundleFiberScaling)]
  rfl

/-- The relative Poincaré operator preserves `C^r` regularity of forms, over a `C^(r + 1)` vector
bundle on a `C^(r + 1)` base. -/
theorem IsSmoothForm.vectorBundlePoincareHomotopy {r : ℕ∞} [IsManifold IB 1 B]
    [ContMDiffVectorBundle 1 FV V IB] [IsManifold IB (r + 1) B]
    [ContMDiffVectorBundle (r + 1) FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) r η) :
    IsSmoothForm (IB.prod 𝓘(ℝ, FV)) r (vectorBundlePoincareHomotopy η) := by
  exact IsSmoothForm.homotopyOperator (hη.mpullback contMDiff_vectorBundleFiberScaling)

/-! ### The chart expression and the first jet along the zero section -/

section Chart

variable [IsManifold IB 1 B] [ContMDiffVectorBundle 1 FV V IB]

/-- **The relative Poincaré operator in a bundle chart.** In the preferred chart at any point of
the total space, whose coordinates are a base coordinate and a fibre coordinate, the relative
Poincaré operator of a vector bundle is the flat relative Poincaré operator
`TauCeti.fiberwisePoincareHomotopy` of the coordinate expression of the form: the chart turns fibre
scaling into scaling of the fibre coordinate. -/
theorem inChartAt_vectorBundlePoincareHomotopy
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) (v : TotalSpace FV V)
    {y : EB × FV} (hy : y ∈ (extChartAt (IB.prod 𝓘(ℝ, FV)) v).target) :
    (vectorBundlePoincareHomotopy η).inChartAt v y =
      fiberwisePoincareHomotopy (η.inChartAt v) y := by
  set c := extChartAt (IB.prod 𝓘(ℝ, FV)) v
  have hsu : UniqueDiffOn ℝ c.target := uniqueDiffOn_extChartAt_target v
  -- The chart target is a product with the whole fibre, so it is stable under fibre scaling.
  have hmaps : MapsTo fiberScaling (c.target ×ˢ Icc 0 1) c.target := fun z hz ↦ by
    have h := hz.1
    simp only [c, fiberScaling_apply, FiberBundle.extChartAt_target, mem_prod, mem_univ,
      and_true] at h ⊢
    exact h
  -- On the cylinder over the chart target, fibre scaling read through the cylinder chart is the
  -- chart inverse composed with flat fibre scaling.
  have hEq : EqOn (vectorBundleFiberScaling FV V ∘ cylinderChart (IB.prod 𝓘(ℝ, FV)) v)
      (c.symm ∘ fiberScaling) (c.target ×ˢ Icc 0 1) := by
    rintro ⟨z, τ⟩ ⟨hz, hτ⟩
    simp only [Function.comp_apply, cylinderChart_apply, vectorBundleFiberScaling_apply,
      projIcc_of_mem _ hτ, fiberScaling_apply]
    exact (FiberBundle.extChartAt_symm_smul_snd v hz τ).symm
  rw [vectorBundlePoincareHomotopy_def, inChartAt_homotopyOperator v subset_rfl hsu _ hy,
    fiberwisePoincareHomotopy_eq_cylinderHomotopy, cylinderHomotopy_apply]
  refine (cylinderHomotopy_apply _ y).trans (intervalIntegral.integral_congr fun t ht ↦ ?_)
  rw [uIcc_of_le zero_le_one] at ht
  have hyt : (y, t) ∈ c.target ×ˢ Icc (0 : ℝ) 1 := ⟨hy, ht⟩
  -- The pullback of `η` along fibre scaling, read on the cylinder over the chart target, is the
  -- flat pullback of the coordinate expression of `η` along flat fibre scaling.
  have hH : MDifferentiableAt ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
      (vectorBundleFiberScaling FV V) (cylinderChart (IB.prod 𝓘(ℝ, FV)) v (y, t)) :=
    (contMDiff_vectorBundleFiberScaling (n := 1) _).mdifferentiableAt one_ne_zero
  have hcyl : MDifferentiableWithinAt 𝓘(ℝ, (EB × FV) × ℝ) ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1))
      (cylinderChart (IB.prod 𝓘(ℝ, FV)) v) (c.target ×ˢ Icc 0 1) (y, t) :=
    (contMDiffOn_cylinderChart (n := 1) v subset_rfl _ hyt).mdifferentiableWithinAt one_ne_zero
  have hu := (hsu.prod uniqueDiffOn_Icc_zero_one) _ hyt
  have hS : HasFDerivWithinAt fiberScaling (fderiv ℝ fiberScaling (y, t)) (c.target ×ˢ Icc 0 1)
      (y, t) :=
    ((contDiff_fiberScaling (r := 1)).differentiable one_ne_zero _).hasFDerivAt.hasFDerivWithinAt
  have hkey : mpullbackWithin 𝓘(ℝ, (EB × FV) × ℝ) ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1))
      (cylinderChart (IB.prod 𝓘(ℝ, FV)) v) (c.target ×ˢ Icc 0 1)
      (mpullback ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
        (vectorBundleFiberScaling FV V) η) (y, t) =
      fiberScalingPullback (η.inChartAt v) (y, t) := by
    rw [← mpullbackWithin_univ, ← mpullbackWithin_comp_at hcyl hH.mdifferentiableWithinAt
      (mapsTo_univ _ _) hu.uniqueMDiffWithinAt, mpullbackWithin_congr hEq hyt,
      mpullbackWithin_comp_apply_of_hasFDerivWithinAt hS
        ((mdifferentiableWithinAt_extChartAt_symm (hmaps hyt)).mono
          (extChartAt_target_subset_range v)) hmaps hu, fiberScalingPullback_apply]
    congr 1
    ext w
    rw [mpullbackWithin_apply,
      mfderivWithin_extChartAt_symm_of_subset v subset_rfl (hmaps hyt) (hsu _ (hmaps hyt))]
    exact (RoughForm.inChartAt_apply η v _ w).symm
  rw [hkey]

/-- **The relative Poincaré primitive has zero first jet** at every point of the zero section at
which the form vanishes as a full ambient tensor: in the preferred chart there, the coordinate
expression of the primitive has derivative zero. Only continuity of the form is used. -/
theorem hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η) {b : B} (hb : η (zeroSection FV V b) = 0) :
    HasFDerivWithinAt ((vectorBundlePoincareHomotopy η).inChartAt (zeroSection FV V b))
      (0 : (EB × FV) →L[ℝ] (EB × FV) [⋀^Fin k]→L[ℝ] F) (range (IB.prod 𝓘(ℝ, FV)))
      (extChartAt (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V b) (zeroSection FV V b)) := by
  set p := zeroSection FV V b
  set c := extChartAt (IB.prod 𝓘(ℝ, FV)) p
  have hc : c p = (extChartAt IB b b, 0) := by
    have h := (trivializationAt FV V b).zeroSection ℝ (mem_baseSet_trivializationAt FV V b)
    simp only [c, FiberBundle.extChartAt, PartialEquiv.coe_trans, Function.comp_apply,
      PartialEquiv.prod_coe, PartialEquiv.refl_coe, id_eq]
    have h' : (trivializationAt FV V p.proj).toPartialEquiv p = (b, 0) := h
    rw [h']
    -- The base coordinate of `p` is that of `b`, both by definition.
    rfl
  have hp : (extChartAt IB b b, (0 : FV)) ∈ c.target := hc ▸ mem_extChartAt_target p
  -- The chart target is a product with the whole fibre, so it is stable under fibre scaling.
  have hscale : ∀ x ∈ c.target, ∀ t ∈ Icc (0 : ℝ) 1, (x.1, t • x.2) ∈ c.target := by
    intro x hx t _
    simp only [c, FiberBundle.extChartAt_target, mem_prod, mem_univ, and_true] at hx ⊢
    exact hx
  have hzero : η.inChartAt p (extChartAt IB b b, 0) = 0 := by
    rw [← hc, RoughForm.inChartAt_extChartAt_self, hb]
    -- The two zeros are the same alternating map; the tangent space is the model space.
    rfl
  have h := hasFDerivWithinAt_fiberwisePoincareHomotopy_zeroSection
    (hη.continuousOn_inChartAt p _ hp) hzero hscale
  rw [hc]
  exact (h.congr (fun z hz ↦ inChartAt_vectorBundlePoincareHomotopy η p hz)
    (inChartAt_vectorBundlePoincareHomotopy η p hp)).mono_of_mem_nhdsWithin
      (hc ▸ extChartAt_target_mem_nhdsWithin p)

end Chart

variable [CompleteSpace F]

/-- **The relative cochain-homotopy identity.** For a `C¹` form `η` of positive degree on the total
space of a `C²` vector bundle over a `C²` base, `d β + P (d η) = η - ρ^* η`, where `P` is the
relative Poincaré operator, `β = P η`, and `ρ = 0 ∘ π` is the retraction onto the zero section. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv
    [IsManifold IB 2 B] [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) :
    mextDeriv (vectorBundlePoincareHomotopy η) + vectorBundlePoincareHomotopy (mextDeriv η) =
      η - mpullback (IB.prod 𝓘(ℝ, FV)) (IB.prod 𝓘(ℝ, FV))
        (zeroSection FV V ∘ TotalSpace.proj) η := by
  have hH : ContMDiff ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV)) 2
      (vectorBundleFiberScaling FV V) :=
    contMDiff_vectorBundleFiberScaling
  have hι (s : Icc (0 : ℝ) 1) : MDifferentiable (IB.prod 𝓘(ℝ, FV))
      ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (fun v : TotalSpace FV V ↦ (v, s)) :=
    mdifferentiable_id.prodMk mdifferentiable_const
  have h₁ : vectorBundleFiberScaling FV V ∘ (fun v ↦ (v, 1)) = id :=
    funext fun v ↦ vectorBundleFiberScaling_one v
  have h₀ : vectorBundleFiberScaling FV V ∘ (fun v ↦ (v, 0)) =
      zeroSection FV V ∘ TotalSpace.proj :=
    funext fun v ↦ vectorBundleFiberScaling_zero v
  funext v
  rw [Pi.add_apply, vectorBundlePoincareHomotopy_def, vectorBundlePoincareHomotopy_def,
    mpullback_mextDeriv hH ((isSmoothBundleForm_def 1 _).mpr hη.contMDiff),
    mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv
      (hη.mpullback (hH.of_le (by norm_num))),
    ← mpullback_comp_at (hι 1 v) (hH.mdifferentiable two_ne_zero _),
    ← mpullback_comp_at (hι 0 v) (hH.mdifferentiable two_ne_zero _), h₁, h₀, mpullback_id,
    Pi.sub_apply]

/-- **The relative Poincaré identity.** For a closed `C¹` form `η` of positive degree on the total
space of a `C²` vector bundle over a `C²` base, `d β = η - ρ^* η`, where `β` is the relative
Poincaré operator of `η` and `ρ = 0 ∘ π` is the retraction onto the zero section. -/
theorem mextDeriv_vectorBundlePoincareHomotopy [IsManifold IB 2 B]
    [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) (hclosed : mextDeriv η = 0) :
    mextDeriv (vectorBundlePoincareHomotopy η) =
      η - mpullback (IB.prod 𝓘(ℝ, FV)) (IB.prod 𝓘(ℝ, FV))
        (zeroSection FV V ∘ TotalSpace.proj) η := by
  rw [← mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv hη,
    hclosed, vectorBundlePoincareHomotopy_zero, add_zero]

/-- **The relative Poincaré lemma on the total space of a vector bundle.** If a closed `C¹` form
`η` of positive degree, on the total space of a `C²` vector bundle over a `C²` base, restricts to
zero on the zero section, then the relative Poincaré operator is a primitive of `η`, which
vanishes along the zero section as a full ambient tensor. The form `η` itself need not vanish as
an ambient tensor there. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_of_mpullback_zeroSection_eq_zero
    [IsManifold IB 2 B] [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V) η = 0) :
    mextDeriv (vectorBundlePoincareHomotopy η) = η := by
  rw [mextDeriv_vectorBundlePoincareHomotopy hη hclosed, mpullback_zeroSection_comp_proj, hi,
    mpullback_zero, sub_zero]

/-! ### Transport to a tube -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : WithTop ℕ∞} [IsManifold IB n B] [ContMDiffVectorBundle n FV V IB]

/-- **The relative Poincaré lemma on a tube.** Let `Φ` be a `C^n` diffeomorphism from the total
space of a `C^n` vector bundle onto `M`, such as a tubular neighbourhood, with zero-section
inclusion `i = Φ ∘ 0` and retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto its image. Every closed `C^r`
form `η` of positive degree on `M`, with `1 ≤ r` and `r + 1 ≤ n`, has a `C^r` form `β` with
`d β = η - ρ^* η` that vanishes along `i` as a full ambient tensor. Moreover `β` has zero first
jet at every point of the image of `i` at which `η` vanishes as a full ambient tensor: its
coordinate expression in the preferred chart there has derivative zero. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧
      mextDeriv β = η - mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm) η ∧
      (∀ b, β (Φ (zeroSection FV V b)) = 0) ∧
      ∀ b, η (Φ (zeroSection FV V b)) = 0 →
        HasFDerivWithinAt (β.inChartAt (Φ (zeroSection FV V b)))
          (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (range I)
          (extChartAt I (Φ (zeroSection FV V b)) (Φ (zeroSection FV V b))) := by
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by rw [← one_add_one_eq_two]; gcongr) hn
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by norm_num) h2).ne'
  have : IsManifold IB ((r : WithTop ℕ∞) + 1) B := .of_le hn
  have : ContMDiffVectorBundle ((r : WithTop ℕ∞) + 1) FV V IB := .of_le hn
  have : IsManifold IB 2 B := .of_le h2
  have : ContMDiffVectorBundle 2 FV V IB := .of_le h2
  have hη₀ := hη.mpullback (Φ.contMDiff.of_le hn)
  have hβ₀ := hη₀.vectorBundlePoincareHomotopy
  refine ⟨mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm (vectorBundlePoincareHomotopy
    (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η)), hβ₀.mpullback (Φ.symm.contMDiff.of_le hn), ?_,
    fun b ↦ ?_, fun b hb ↦ ?_⟩
  · have hd := Φ.mdifferentiable hn0
    have hds := Φ.symm.mdifferentiable hn0
    have hZ := (contMDiff_zeroSection ℝ V (IB := IB) (F := FV) (n := 1)).mdifferentiable one_ne_zero
    have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
    rw [← mpullback_mextDeriv (Φ.symm.contMDiff.of_le h2)
        ((isSmoothBundleForm_def 1 _).mpr (hβ₀.of_le hr').contMDiff),
      mextDeriv_vectorBundlePoincareHomotopy (hη₀.of_le hr')
        (hη.of_le hr' |>.mextDeriv_mpullback_eq_zero hclosed (Φ.contMDiff.of_le h2)),
      mpullback_sub, mpullback_symm_mpullback hn0, ← mpullback_comp (hZ.comp hp) hd,
      ← mpullback_comp hds (hd.comp (hZ.comp hp))]
    -- Both retractions are `Φ ∘ 0 ∘ π ∘ Φ⁻¹`, associated differently.
    simp only [Function.comp_assoc]
  · exact mpullback_apply_eq_zero ((congrArg _ (Φ.symm_apply_apply _)).trans
      (vectorBundlePoincareHomotopy_zeroSection _ b))
  · -- The primitive has zero first jet at the zero vector over `b` on the total space, and
    -- pulling back along `Φ⁻¹` preserves this.
    have : IsManifold IB 1 B := .of_le (n := 2) one_le_two
    have : ContMDiffVectorBundle 1 FV V IB := .of_le (n := 2) one_le_two
    have hb' : Φ.symm (Φ (zeroSection FV V b)) = zeroSection FV V b := Φ.symm_apply_apply _
    have hzero : mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η (zeroSection FV V b) = 0 :=
      mpullback_apply_eq_zero hb
    refine RoughForm.hasFDerivWithinAt_inChartAt_mpullback
      ((Φ.symm.contMDiff.of_le (le_trans (by norm_num) h2)).contMDiffAt) ?_ ?_
    · rw [hb']
      exact vectorBundlePoincareHomotopy_zeroSection _ b
    · rw [hb']
      exact hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection
        (hη₀.of_le bot_le) hzero

/-- **The relative Poincaré lemma on a tube**, for forms restricting to zero on the core. Let `Φ`
be a `C^n` diffeomorphism from the total space of a `C^n` vector bundle onto `M`, such as a
tubular neighbourhood, with zero-section inclusion `i = Φ ∘ 0`. Every closed `C^r` form `η` of
positive degree on `M` with `i^* η = 0`, where `1 ≤ r` and `r + 1 ≤ n`, is the exterior
derivative of a `C^r` form `β` that vanishes along `i` as a full ambient tensor. Moreover `β` has
zero first jet at every point of the image of `i` at which `η` vanishes as a full ambient tensor:
its coordinate expression in the preferred chart there has derivative zero. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_relative_primitive
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧ mextDeriv β = η ∧
      (∀ b, β (Φ (zeroSection FV V b)) = 0) ∧
      ∀ b, η (Φ (zeroSection FV V b)) = 0 →
        HasFDerivWithinAt (β.inChartAt (Φ (zeroSection FV V b)))
          (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (range I)
          (extChartAt I (Φ (zeroSection FV V b)) (Φ (zeroSection FV V b))) := by
  obtain ⟨β, hβ, hdβ, hβ₀, hjet⟩ :=
    Φ.exists_isSmoothForm_mextDeriv_eq_sub_mpullback hr hn hη hclosed
  refine ⟨β, hβ, ?_, hβ₀, hjet⟩
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by simp) hn).ne'
  have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
  have hiΦ := (Φ.contMDiff.comp (contMDiff_zeroSection ℝ V (IB := IB) (F := FV))).mdifferentiable
    hn0
  rw [hdβ, ← Function.comp_assoc (Φ : TotalSpace FV V → M) (zeroSection FV V),
    mpullback_comp (hp.comp (Φ.symm.mdifferentiable hn0)) hiΦ, hi, mpullback_zero, sub_zero]

end TauCeti
