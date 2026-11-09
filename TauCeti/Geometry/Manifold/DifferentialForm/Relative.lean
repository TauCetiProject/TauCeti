/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# The relative Poincaré lemma on the total space of a vector bundle

Let `V → B` be a smooth real vector bundle. Fibre scaling
`H : V × [0, 1] → V`, `(v, t) ↦ t • v` (`TauCeti.vectorBundleFiberScaling`), is a smooth homotopy
from the retraction `r = 0 ∘ π` of `V` onto its zero section to the identity, and it fixes the
zero section at all times. Applying the homotopy operator of the cylinder `V × [0, 1]` to `H^* η`
gives the *relative Poincaré operator* (`TauCeti.vectorBundlePoincareHomotopy`)

`β = h (H^* η)`, `β(v)(w₁, …, wₖ) = ∫₀¹ η(t • v)(dH ∂ₜ, dH w₁, …, dH wₖ) dt`.

Since `H` is constant in time along the zero section, `dH ∂ₜ = 0` there, so `β` vanishes at
every point of the zero section as a full ambient tensor, for every form `η`
(`TauCeti.vectorBundlePoincareHomotopy_zeroSection`), even when `η` does not. For a closed `C¹`
form `η` of positive degree, the cochain-homotopy identity of the homotopy operator gives

`d β = η - r^* η`

(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy`), and `r^* η = π^* (i^* η)` only depends on the
restriction `i^* η` of `η` to the zero section `i`. Hence `d β = η` as soon as `i^* η = 0`
(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy_of_mpullback_zeroSection_eq_zero`), although `η`
need not vanish as a full ambient tensor along the zero section. The operator preserves `C^r`
regularity (`TauCeti.IsSmoothForm.vectorBundlePoincareHomotopy`).

Everything transports along a diffeomorphism `Φ` from the total space onto a manifold `M`, such as
a tubular neighbourhood of an embedded submanifold
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`). With the zero-section inclusion
`i = Φ ∘ 0` and the retraction `r = Φ ∘ 0 ∘ π ∘ Φ⁻¹`, every closed `C^r` form `η` of positive
degree on `M`, with `r ≥ 1`, has a `C^r` form `β` with `d β = η - r^* η` that vanishes along
`i` as a full ambient tensor (`Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback`), and
`d β = η` when `i^* η = 0` (`Diffeomorph.exists_isSmoothForm_relative_primitive`). This is the
primitive used to compare two symplectic forms relative to a submanifold.

The flat counterpart on a convex set stable under scaling the normal coordinate is
`Convex.exists_contDiffOn_relative_primitive`. The base may have boundary or corners and the
coefficient space is any Banach space.

## Main declarations

* `TauCeti.vectorBundleFiberScaling`: the fibre scaling homotopy `(v, t) ↦ t • v`.
* `TauCeti.vectorBundlePoincareHomotopy`: the relative Poincaré operator `β = h (H^* η)`.
* `TauCeti.vectorBundlePoincareHomotopy_zeroSection`: `β` vanishes along the zero section.
* `TauCeti.mextDeriv_vectorBundlePoincareHomotopy`: `d β = η - r^* η` for closed `η`.
* `Diffeomorph.exists_isSmoothForm_relative_primitive`: the relative Poincaré lemma on a tube.

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

/-! ### Fibre scaling -/

variable (FV V) in
/-- **Fibre scaling** `(v, t) ↦ t • v` on the total space of a vector bundle, a homotopy from the
retraction `v ↦ 0_(π v)` onto the zero section to the identity. This is the whole-bundle radial
contraction `TauCeti.IsTubularNeighborhood.radialContraction`, with the time last as in the
cylinder `V × [0, 1]` of `TauCeti.homotopyOperator`. -/
def vectorBundleFiberScaling (p : TotalSpace FV V × Icc (0 : ℝ) 1) : TotalSpace FV V :=
  ⟨p.1.proj, (p.2 : ℝ) • p.1.2⟩

/-- Fibre scaling multiplies the vector by the time and keeps its base point. -/
@[simp]
theorem vectorBundleFiberScaling_apply (v : TotalSpace FV V) (t : Icc (0 : ℝ) 1) :
    vectorBundleFiberScaling FV V (v, t) = ⟨v.proj, (t : ℝ) • v.2⟩ :=
  (rfl)

/-- At time one, fibre scaling is the identity. -/
theorem vectorBundleFiberScaling_one (v : TotalSpace FV V) :
    vectorBundleFiberScaling FV V (v, 1) = v := by
  simp

/-- At time zero, fibre scaling is the retraction onto the zero section. -/
theorem vectorBundleFiberScaling_zero (v : TotalSpace FV V) :
    vectorBundleFiberScaling FV V (v, 0) = zeroSection FV V v.proj := by
  simp [zeroSection]

/-- Fibre scaling fixes the zero section at all times. -/
theorem vectorBundleFiberScaling_zeroSection (b : B) (t : Icc (0 : ℝ) 1) :
    vectorBundleFiberScaling FV V (zeroSection FV V b, t) = zeroSection FV V b := by
  simp [zeroSection]

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
closed `C¹` form `η`, `d β = η - r^* η` with `r` the retraction onto the zero section
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

/-! ### Smoothness of fibre scaling and vanishing along the zero section -/

variable [VectorBundle ℝ FV V]

/-- Fibre scaling is smooth on the cylinder `V × [0, 1]`. Only the vector bundle structure is
used: the total space need not be a smooth manifold. -/
theorem contMDiff_vectorBundleFiberScaling {n : ℕ∞ω} :
    ContMDiff ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV)) n
      (vectorBundleFiberScaling FV V) :=
  (contMDiff_subtypeVal_Icc.comp contMDiff_snd).smul_totalSpace contMDiff_fst

/-- Along the zero section, fibre scaling has zero derivative in the time direction: it maps
`∂ₜ = (0, 1)` to `0`. -/
theorem mfderiv_vectorBundleFiberScaling_zeroSection_time (b : B) (t : Icc (0 : ℝ) 1)
    (τ : EuclideanSpace ℝ (Fin 1)) :
    mfderiv ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
      (vectorBundleFiberScaling FV V) (zeroSection FV V b, t) ((0 : EB × FV), τ) = 0 := by
  rw [mfderiv_prod_eq_add_apply (v := ((0 : EB × FV), τ))
    ((contMDiff_vectorBundleFiberScaling (n := 1) _).mdifferentiableAt one_ne_zero)]
  have hconst : (fun z : Icc (0 : ℝ) 1 ↦ vectorBundleFiberScaling FV V (zeroSection FV V b, z)) =
      fun _ ↦ zeroSection FV V b :=
    funext fun z ↦ vectorBundleFiberScaling_zeroSection b z
  rw [hconst, mfderiv_const]
  exact (add_zero _).trans (ContinuousLinearMap.map_zero _)

/-- **The relative Poincaré operator vanishes along the zero section**, as a full ambient tensor,
for every form `η`. -/
@[simp]
theorem vectorBundlePoincareHomotopy_zeroSection
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) (b : B) :
    vectorBundlePoincareHomotopy η (zeroSection FV V b) = 0 := by
  rw [vectorBundlePoincareHomotopy_def, homotopyOperator_apply]
  -- The integrand vanishes: its first argument is the image of `∂ₜ`, which is zero.
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : (EB × FV) [⋀^Fin k]→L[ℝ] F))
    fun t _ ↦ ?_).trans (intervalIntegral.integral_zero (E := (EB × FV) [⋀^Fin k]→L[ℝ] F))
  refine ContinuousAlternatingMap.ext fun w ↦ ?_
  -- `curryLeft_apply_apply` does not fire: the tangent spaces of the cylinder are the model
  -- spaces only by definition. So state the evaluation of the curried form on `∂ₜ` followed by
  -- the included vectors explicitly.
  change mpullback ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
      (vectorBundleFiberScaling FV V) η (zeroSection FV V b, projIcc 0 1 zero_le_one t)
      (Matrix.vecCons ((0 : EB × FV), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))
        fun i ↦ ((w i : EB × FV), (0 : EuclideanSpace ℝ (Fin 1)))) = 0
  rw [mpullback_apply]
  exact (η _).map_coord_zero 0 (mfderiv_vectorBundleFiberScaling_zeroSection_time b _ _)

/-- Pulling back along the retraction `0 ∘ π` onto the zero section factors through the
restriction to the zero section. -/
private theorem mpullback_zeroSection_comp_proj
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F k) :
    mpullback (IB.prod 𝓘(ℝ, FV)) (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V ∘ TotalSpace.proj) η =
      mpullback (IB.prod 𝓘(ℝ, FV)) IB (π FV V)
        (mpullback IB (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V) η) :=
  mpullback_comp ((Bundle.contMDiff_proj (F := FV) V).mdifferentiable one_ne_zero)
    ((contMDiff_zeroSection ℝ V).mdifferentiable one_ne_zero) η

variable [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ FV V IB]

/-- The relative Poincaré operator preserves `C^r` regularity of forms. -/
theorem IsSmoothForm.vectorBundlePoincareHomotopy {r : ℕ∞}
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) r η) :
    IsSmoothForm (IB.prod 𝓘(ℝ, FV)) r (vectorBundlePoincareHomotopy η) := by
  have : IsManifold (IB.prod 𝓘(ℝ, FV)) ((r : WithTop ℕ∞) + 1) (TotalSpace FV V) :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast (le_top : r + 1 ≤ ⊤))
  exact IsSmoothForm.homotopyOperator (hη.mpullback contMDiff_vectorBundleFiberScaling)

variable [CompleteSpace F]

/-- **The relative Poincaré identity.** For a closed `C¹` form `η` of positive degree on the total
space of a vector bundle, `d β = η - r^* η`, where `β` is the relative Poincaré operator of `η`
and `r = 0 ∘ π` is the retraction onto the zero section. -/
theorem mextDeriv_vectorBundlePoincareHomotopy
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) (hclosed : mextDeriv η = 0) :
    mextDeriv (vectorBundlePoincareHomotopy η) =
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
  rw [vectorBundlePoincareHomotopy_def,
    mextDeriv_homotopyOperator (hη.mpullback (hH.of_le (by norm_num)))
      (hη.mextDeriv_mpullback_eq_zero hclosed hH),
    ← mpullback_comp_at (hι 1 v) (hH.mdifferentiable two_ne_zero _),
    ← mpullback_comp_at (hι 0 v) (hH.mdifferentiable two_ne_zero _), h₁, h₀, mpullback_id,
    Pi.sub_apply]

/-- **The relative Poincaré lemma on the total space of a vector bundle.** If a closed `C¹` form
`η` of positive degree restricts to zero on the zero section, then the relative Poincaré operator
is a primitive of `η`, which vanishes along the zero section as a full ambient tensor. The form
`η` itself need not vanish as an ambient tensor there. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_of_mpullback_zeroSection_eq_zero
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V) η = 0) :
    mextDeriv (vectorBundlePoincareHomotopy η) = η := by
  rw [mextDeriv_vectorBundlePoincareHomotopy hη hclosed, mpullback_zeroSection_comp_proj, hi,
    mpullback_zero, sub_zero]

/-! ### Transport to a tube -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- **The relative Poincaré lemma on a tube.** Let `Φ` be a diffeomorphism from the total space of
a vector bundle onto `M`, such as a tubular neighbourhood, with zero-section inclusion
`i = Φ ∘ 0` and retraction `r = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto its image. Every closed `C^r` form `η` of
positive degree on `M`, with `1 ≤ r`, has a `C^r` form `β` with `d β = η - r^* η` that vanishes
along `i` as a full ambient tensor. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback
    (Φ : TotalSpace FV V ≃ₘ⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧
      mextDeriv β = η - mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm) η ∧
      ∀ b, β (Φ (zeroSection FV V b)) = 0 := by
  have hΦ : ContMDiff (IB.prod 𝓘(ℝ, FV)) I ((r : WithTop ℕ∞) + 1) Φ :=
    Φ.contMDiff.of_le (by exact_mod_cast (le_top : r + 1 ≤ ⊤))
  have hΦs : ContMDiff I (IB.prod 𝓘(ℝ, FV)) ((r : WithTop ℕ∞) + 1) Φ.symm :=
    Φ.symm.contMDiff.of_le (by exact_mod_cast (le_top : r + 1 ≤ ⊤))
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have hη₀ := hη.mpullback hΦ
  have hβ₀ := hη₀.vectorBundlePoincareHomotopy
  refine ⟨mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm (vectorBundlePoincareHomotopy
    (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η)), hβ₀.mpullback hΦs, ?_, fun b ↦ ?_⟩
  · have hΦs₂ : ContMDiff I (IB.prod 𝓘(ℝ, FV)) 2 Φ.symm := Φ.symm.contMDiff.of_le (by simp)
    have hd := Φ.mdifferentiable (by simp)
    have hds := Φ.symm.mdifferentiable (by simp)
    have hZ := (contMDiff_zeroSection ℝ V (IB := IB) (F := FV) (n := 1)).mdifferentiable one_ne_zero
    have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
    rw [← mpullback_mextDeriv hΦs₂ ((isSmoothBundleForm_def 1 _).mpr (hβ₀.of_le hr').contMDiff),
      mextDeriv_vectorBundlePoincareHomotopy (hη₀.of_le hr')
        (hη.of_le hr' |>.mextDeriv_mpullback_eq_zero hclosed (Φ.contMDiff.of_le (by simp))),
      show (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm : M → M) =
        (Φ ∘ (zeroSection FV V ∘ π FV V)) ∘ Φ.symm from rfl,
      mpullback_comp hds (hd.comp (hZ.comp hp)), mpullback_comp (hZ.comp hp) hd]
    funext x
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    simp only [mpullback_apply, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
    congr 1
    rw [← mpullback_apply, ← mpullback_apply, mpullback_symm_mpullback (by simp)]
  · exact mpullback_apply_eq_zero ((congrArg _ (Φ.symm_apply_apply _)).trans
      (vectorBundlePoincareHomotopy_zeroSection _ b))

/-- **The relative Poincaré lemma on a tube**, for forms restricting to zero on the core. Let `Φ`
be a diffeomorphism from the total space of a vector bundle onto `M`, such as a tubular
neighbourhood, with zero-section inclusion `i = Φ ∘ 0`. Every closed `C^r` form `η` of positive
degree on `M` with `i^* η = 0`, where `1 ≤ r`, is the exterior derivative of a `C^r` form `β`
that vanishes along `i` as a full ambient tensor. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_relative_primitive
    (Φ : TotalSpace FV V ≃ₘ⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧ mextDeriv β = η ∧
      ∀ b, β (Φ (zeroSection FV V b)) = 0 := by
  obtain ⟨β, hβ, hdβ, hβ₀⟩ := Φ.exists_isSmoothForm_mextDeriv_eq_sub_mpullback hr hη hclosed
  refine ⟨β, hβ, ?_, hβ₀⟩
  have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
  have hiΦ := (Φ.contMDiff.comp (contMDiff_zeroSection ℝ V (IB := IB) (F := FV))).mdifferentiable
    (by simp)
  rw [hdβ, show (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm : M → M) =
      (Φ ∘ zeroSection FV V) ∘ (π FV V ∘ Φ.symm) from rfl,
    mpullback_comp (hp.comp (Φ.symm.mdifferentiable (by simp))) hiΦ, hi, mpullback_zero,
    sub_zero]

end TauCeti
