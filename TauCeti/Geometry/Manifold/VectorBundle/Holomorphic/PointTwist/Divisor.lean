/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Functor
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.TransverseZero
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Untwist

/-!
# A smooth line bundle is the bundle of a divisor

Let `X` be a Riemann surface. For a finite list `D` of signed points `(xᵢ, sᵢ)` of `X`, the line
bundle `𝒪(D)` (`TauCeti.divisorCore`) is the trivial bundle `X × ℂ` twisted at each `xᵢ`, by `xᵢ`
when `sᵢ = true` and by `-xᵢ` when `sᵢ = false`; it is the line bundle of the divisor
`Σ ±xᵢ`, of degree `TauCeti.divisorDegree D = Σ ±1`. It is a holomorphic line bundle
(`TauCeti.divisorCore.isContMDiff`), and its underlying real bundle is smooth
(`TauCeti.divisorCore.contMDiffVectorBundle_real`).

This file shows that every complex line bundle `L` over a compact Riemann surface whose underlying
real bundle is smooth is smoothly isomorphic to some `𝒪(D)`, with `deg D = c₁(L)[X]`
(`TauCeti.exists_contMDiff_divisorCore_equiv`). The route is that of McDuff–Salamon, Theorem
C.1.10, step 5:

* `L` has a smooth section `σ` whose finitely many zeros `xᵢ` are transverse, each positive
  (`εᵢ = false`) or negative (`εᵢ = true`), with `c₁(L)[X] = Σ (if εᵢ then -1 else 1)`
  (`TauCeti.exists_contMDiffSection_complexEulerClass_eq_sum_sign`).
* Twisting at a zero `x` of sign `ε` by `-x` (positive) or `x` (negative) removes that zero
  without changing `σ` near the other zeros (`TauCeti.exists_untwist_section_of_finset`, built on
  `TauCeti.exists_untwist_section`), so their chart readings, hence their signs, are unchanged
  (`TauCeti.negPointTwistChartReading_eventuallyEq_of_pointTwistDiv`).
* After all zeros are removed the section vanishes nowhere, and a line bundle with a nowhere-zero
  smooth section is isomorphic to the trivial bundle (`TauCeti.fibreEquivOfNeZero`).
* Twisting back with the opposite signs, cancellation (`TauCeti.signedPointTwistCancelEquiv`) and
  functoriality (`TauCeti.signedPointTwistEquiv`) of point twists give `L ≅ 𝒪(Σ ±xᵢ)`
  (`TauCeti.exists_contMDiff_divisorCore_equiv_of_section`).

The isomorphisms are families of complex linear fibre isomorphisms whose total-space maps are
smooth for the real structures; by `TauCeti.bundleDiffeomorph` (after restricting scalars to `ℝ`)
they are diffeomorphisms of total spaces with smooth inverses.

## Main definitions

* `TauCeti.divisorCore`: the coordinate core of the line bundle `𝒪(D)` of a list of signed points.
* `TauCeti.divisorDegree`: the degree `Σ ±1` of a list of signed points.
* `TauCeti.fibreEquivOfNeZero`: the coordinate in the basis given by a nonzero vector of a fibre.
* `TauCeti.IsSignedTransverseZero`: a zero of a section which is positive or negative, in the
  sense of `TauCeti.exists_contMDiffSection_complexEulerClass_eq_sum_sign`.

## Main results

* `TauCeti.divisorCore.isContMDiff` and `TauCeti.divisorCore.contMDiffVectorBundle_real`: `𝒪(D)`
  is a holomorphic line bundle whose underlying real bundle is smooth.
* `TauCeti.contMDiff_fibreEquivOfNeZero`: a line bundle with a nowhere-zero smooth section is
  isomorphic to the trivial bundle.
* `TauCeti.exists_untwist_section_of_finset`: untwisting one of finitely many zeros.
* `TauCeti.exists_contMDiff_divisorCore_equiv_of_section`: a smooth section whose zeros are
  transverse, listed with their signs, gives `L ≅ 𝒪(D)`.
* `TauCeti.exists_contMDiff_divisorCore_equiv`: every smooth complex line bundle over a compact
  Riemann surface is isomorphic to `𝒪(D)` for a list `D` of distinct points with
  `deg D = c₁(L)[X]`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 1, Section 1
  (divisors and line bundles).
-/

public section

noncomputable section

open Bundle Set Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### The line bundle of a divisor -/

/-- The coordinate core of the line bundle `𝒪(D)` of a list `D` of signed points: the trivial
bundle for the empty list, and the point twist `𝒪(D)(x)` (`s = true`) or `𝒪(D)(-x)` (`s = false`)
for `(x, s) :: D`. The trivial bundle is indexed by `X × Bool`, like the point twists, with the
whole of `X` as every base set and identity coordinate changes. -/
def divisorCore : List (X × Bool) → VectorBundleCore ℂ X ℂ (X × Bool)
  | [] =>
    { baseSet := fun _ ↦ univ
      isOpen_baseSet := fun _ ↦ isOpen_univ
      indexAt := fun z ↦ (z, false)
      mem_baseSet_at := mem_univ
      coordChange := fun _ _ _ ↦ ContinuousLinearMap.id ℂ ℂ
      coordChange_self := fun _ _ _ _ ↦ rfl
      continuousOn_coordChange := fun _ _ ↦ continuousOn_const
      coordChange_comp := fun _ _ _ _ _ _ ↦ rfl }
  | (x, s) :: D => signedPointTwistCore ℂ (divisorCore D).Fiber x s

@[simp] theorem divisorCore_nil_localTriv_baseSet (i : X × Bool) :
    ((divisorCore []).localTriv i).baseSet = univ :=
  (rfl)

@[simp] theorem divisorCore_nil_coordChange (i j : X × Bool) (z : X) :
    (divisorCore []).coordChange i j z = ContinuousLinearMap.id ℂ ℂ :=
  (rfl)

theorem divisorCore_cons (x : X) (s : Bool) (D : List (X × Bool)) :
    divisorCore ((x, s) :: D) = signedPointTwistCore ℂ (divisorCore D).Fiber x s :=
  (rfl)

/-- The degree of a list of signed points: the number of points with sign `true` minus the number
with sign `false`. -/
def divisorDegree (D : List (X × Bool)) : ℤ :=
  (D.map fun p ↦ if p.2 then 1 else -1).sum

omit [TopologicalSpace X] [ChartedSpace ℂ X] in
@[simp] theorem divisorDegree_nil : divisorDegree ([] : List (X × Bool)) = 0 := (rfl)

omit [TopologicalSpace X] [ChartedSpace ℂ X] in
@[simp] theorem divisorDegree_cons (x : X) (s : Bool) (D : List (X × Bool)) :
    divisorDegree ((x, s) :: D) = (if s then 1 else -1) + divisorDegree D :=
  List.sum_cons

variable {n : ℕ∞ω} [IsManifold 𝓘(ℂ) n X]

/-- **The line bundle of a divisor is holomorphic.** The coordinate changes of `𝒪(D)` are `C^n`
over `𝓘(ℂ)`: those of the trivial bundle are constant, and point twists of `C^n` bundles are `C^n`
(`TauCeti.signedPointTwistCore.isContMDiff`). For `n = ∞` this is the holomorphic structure of
`𝒪(D)`. -/
instance divisorCore.isContMDiff (D : List (X × Bool)) : (divisorCore D).IsContMDiff 𝓘(ℂ) n := by
  induction D with
  | nil => exact ⟨fun _ _ ↦ contMDiffOn_const⟩
  | cons p D ih =>
    obtain ⟨x, s⟩ := p
    exact signedPointTwistCore.isContMDiff (E := (divisorCore D).Fiber) x s

/-- The fibres of `𝒪(D)` are real vector spaces, through the model fibre `ℂ`. -/
instance divisorCore.moduleRealFiber (D : List (X × Bool)) (z : X) :
    Module ℝ ((divisorCore D).Fiber z) :=
  inferInstanceAs (Module ℝ ℂ)

instance divisorCore.isScalarTowerRealFiber (D : List (X × Bool)) (z : X) :
    IsScalarTower ℝ ℂ ((divisorCore D).Fiber z) :=
  inferInstanceAs (IsScalarTower ℝ ℂ ℂ)

local instance instVectorBundleRealDivisorCore (D : List (X × Bool)) :
    VectorBundle ℝ ℂ (divisorCore D).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ ℂ _

/-- **The line bundle of a divisor is real smooth.** The underlying real bundle of `𝒪(D)` is a
`C^n` vector bundle over the real manifold underlying `X`: the trivial bundle has identity
coordinate changes, and point twists of real-`C^n` bundles are real `C^n`
(`TauCeti.signedPointTwistCore.contMDiffVectorBundle_real`). -/
instance divisorCore.contMDiffVectorBundle_real (D : List (X × Bool)) :
    ContMDiffVectorBundle n ℂ (divisorCore D).Fiber 𝓘(ℝ, ℂ) := by
  induction D with
  | nil =>
    refine ⟨fun e e' he he' ↦ ?_⟩
    -- The real coordinate changes are the complex ones, which are the identity.
    have hR (z : X) : (e.coordChangeL ℝ e' z : ℂ →L[ℝ] ℂ) =
        (e.coordChangeL ℂ e' z : ℂ →L[ℂ] ℂ).restrictScalars ℝ :=
      (Trivialization.restrictScalars_coordChangeL ℝ ℂ e e').symm
    simp_rw [hR]
    obtain ⟨i, rfl⟩ := he.out
    obtain ⟨j, rfl⟩ := he'.out
    refine (contMDiffOn_const (c := ContinuousLinearMap.id ℝ ℂ)).congr fun z hz ↦ ?_
    ext v
    rw [ContinuousLinearMap.coe_restrictScalars']
    exact (divisorCore []).localTriv_coordChange_eq i j hz v
  | cons p D ih =>
    obtain ⟨x, s⟩ := p
    exact signedPointTwistCore.contMDiffVectorBundle_real (E := (divisorCore D).Fiber) x s

/-! ### Sections without zeros -/

section Trivial

variable {L : X → Type} [∀ z, AddCommGroup (L z)] [∀ z, Module ℂ (L z)] [∀ z, Module ℝ (L z)]
  [∀ z, IsScalarTower ℝ ℂ (L z)] [∀ z, TopologicalSpace (L z)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealDivisor : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

/-- The isomorphism of the fibre of a complex line bundle at `z` with `ℂ` defined by a vector
`σ z ≠ 0`: it sends `v` to its coordinate in the basis `σ z`. Its inverse is `w ↦ w • σ z`
(`TauCeti.fibreEquivOfNeZero_symm_apply`). -/
def fibreEquivOfNeZero (σ : ∀ z, L z) (hσ : ∀ z, σ z ≠ 0) (z : X) : L z ≃L[ℂ] ℂ :=
  let t := (trivializationAt ℂ L z).continuousLinearEquivAt ℂ z
    (mem_baseSet_trivializationAt ℂ L z)
  t.trans (ContinuousLinearEquiv.unitsEquivAut ℂ
    (Units.mk0 (t (σ z)) ((map_ne_zero_iff t t.injective).2 (hσ z)))⁻¹)

omit [ChartedSpace ℂ X] [∀ z, Module ℝ (L z)] [∀ z, IsScalarTower ℝ ℂ (L z)] in
theorem fibreEquivOfNeZero_symm_apply (σ : ∀ z, L z) (hσ : ∀ z, σ z ≠ 0) (z : X) (w : ℂ) :
    (fibreEquivOfNeZero σ hσ z).symm w = w • σ z := by
  dsimp only [fibreEquivOfNeZero]
  rw [ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply_symm, inv_inv, Units.val_mk0, ← smul_eq_mul,
    map_smul, ContinuousLinearEquiv.symm_apply_apply]

variable [IsManifold 𝓘(ℂ) ∞ X] [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)]

/-- **A line bundle with a nowhere-zero section is trivial.** If `σ` is a real-smooth section of a
complex line bundle `L` without zeros, the fibre isomorphisms `fibreEquivOfNeZero σ` of `L` with
the trivial bundle `𝒪(0)` are smooth on total spaces. -/
theorem contMDiff_fibreEquivOfNeZero {σ : ∀ z, L z}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ fun z ↦ TotalSpace.mk' ℂ z (σ z))
    (hσ₀ : ∀ z, σ z ≠ 0) :
    ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      fun p : TotalSpace ℂ L ↦ TotalSpace.mk' ℂ (E := (divisorCore []).Fiber) p.proj
        (fibreEquivOfNeZero σ hσ₀ p.proj p.snd) := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ X := IsManifold.restrictScalars ℝ ‹_›
  -- The inverse `w ↦ w • σ z` is smooth: in a chart of `L` it is `w` times the reading of `σ`.
  have h : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      fun p : TotalSpace ℂ (divisorCore []).Fiber ↦ TotalSpace.mk' ℂ (E := L) p.proj
        ((show ℂ from p.snd) • σ p.proj) := by
    intro p
    rw [Bundle.contMDiffAt_totalSpace_iff]
    refine ⟨contMDiffAt_proj _, ?_⟩
    have hw := (Bundle.contMDiffAt_totalSpace_iff.mp
      (contMDiffAt_id (I := 𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) (x := p) (n := ∞))).2
    have hg := (((trivializationAt ℂ L p.proj).contMDiffAt_section_iff
      (mem_baseSet_trivializationAt ℂ L p.proj)).1 (hσ p.proj)).comp p (contMDiffAt_proj _)
    refine (((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).contMDiff.contMDiffAt.comp p
      hw).clm_apply hg).congr_of_eventuallyEq ?_
    filter_upwards [(FiberBundle.continuous_proj ℂ _).continuousAt.preimage_mem_nhds
      ((trivializationAt ℂ L p.proj).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ℂ L p.proj))] with q hq
    rw [Function.comp_apply, ContinuousLinearMap.lsmul_apply,
      (trivializationAt ℂ L p.proj).linear ℂ hq |>.map_smul]
    rfl
  refine (contMDiff_bundle_symm (E₁ := (divisorCore []).Fiber)
    (fun z ↦ ((fibreEquivOfNeZero σ hσ₀ z).restrictScalars' ℝ).symm) (h.congr fun q ↦
      congrArg (TotalSpace.mk' ℂ q.proj) ((congrFun (ContinuousLinearEquiv.coe_restrictScalars'_symm
        (R := ℝ) (fibreEquivOfNeZero σ hσ₀ q.proj)) q.snd).trans
          (fibreEquivOfNeZero_symm_apply σ hσ₀ q.proj q.snd)))).congr fun p ↦
    congrArg (TotalSpace.mk' ℂ p.proj) ?_
  exact (congrFun (ContinuousLinearEquiv.coe_restrictScalars' (R := ℝ)
    (fibreEquivOfNeZero σ hσ₀ p.proj)) p.snd).symm

end Trivial

/-! ### Untwisting the zeros one at a time -/

section Untwist

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {E : X → Type*} [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)]
  [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]

/-- Away from `x`, the chart reading at `y` of a section `τ` of the signed point twist `E(±x)` is
that of its image in `E` under `pointTwistDiv`: if this image is `σ` near `y`, the two readings
agree near the chart coordinate of `y`. -/
theorem negPointTwistChartReading_eventuallyEq_of_pointTwistDiv {x y : X} {s : Bool}
    (hyx : y ≠ x) {τ : ∀ z, (signedPointTwistCore F E x s).Fiber z} {σ : ∀ z, E z}
    (h : ∀ᶠ z in 𝓝 y, pointTwistDiv F E x z (τ z) = σ z) :
    negPointTwistChartReading F y τ =ᶠ[𝓝 (chartAt ℂ y y)] negPointTwistChartReading F y σ := by
  have hb : (signedPointTwistCore F E x s).baseSet (y, false) ∈ 𝓝 y :=
    ((signedPointTwistCore F E x s).isOpen_baseSet _).mem_nhds
      (mem_signedPointTwistCore_baseSet.2 ⟨mem_baseSet_trivializationAt F E y, by simpa using hyx⟩)
  filter_upwards [(chartAt ℂ y).tendsto_symm (mem_chart_source ℂ y) (h.and hb)] with w hw
  rw [negPointTwistChartReading_apply, negPointTwistChartReading_apply,
    signedPointTwistCore_trivializationAt_of_ne hyx, ← hw.1]
  exact (trivializationAt_pointTwistDiv hw.2 _).symm

end Untwist

section Assembly

variable {L : X → Type} [∀ z, AddCommGroup (L z)] [∀ z, Module ℂ (L z)] [∀ z, Module ℝ (L z)]
  [∀ z, IsScalarTower ℝ ℂ (L z)] [∀ z, TopologicalSpace (L z)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealDivisorAssembly {L : X → Type} [∀ z, AddCommGroup (L z)]
    [∀ z, Module ℂ (L z)] [∀ z, Module ℝ (L z)] [∀ z, IsScalarTower ℝ ℂ (L z)]
    [∀ z, TopologicalSpace (L z)] [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L]
    [VectorBundle ℂ ℂ L] : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

local instance instVectorBundleRealSignedPointTwistCoreDivisor (x : X) (s : Bool) :
    VectorBundle ℝ ℂ (signedPointTwistCore ℂ L x s).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ ℂ _

/-- A zero `x` of `σ` is *transverse of sign `s`* when the real derivative `D` of the chart reading
of `σ` at `x` is within `‖c‖` of `u ↦ u c` (`s = false`, a positive zero) or of `u ↦ conj u c`
(`s = true`, a negative zero), for some `c`. -/
def IsSignedTransverseZero (σ : ∀ z, L z) (x : X) (s : Bool) : Prop :=
  ∃ (D : ℂ →L[ℝ] ℂ) (c : ℂ), HasFDerivAt (negPointTwistChartReading ℂ x σ) D (chartAt ℂ x x) ∧
    ‖D - (if s then Complex.conjCLE.toContinuousLinearMap
      else ContinuousLinearMap.id ℝ ℂ).smulRight c‖ < ‖c‖

omit [∀ z, AddCommGroup (L z)] [∀ z, Module ℂ (L z)] [∀ z, Module ℝ (L z)]
  [∀ z, IsScalarTower ℝ ℂ (L z)] [VectorBundle ℂ ℂ L] in
/-- The sign of a transverse zero depends only on the section near the zero. -/
theorem IsSignedTransverseZero.congr {L' : X → Type} [∀ z, TopologicalSpace (L' z)]
    [TopologicalSpace (TotalSpace ℂ L')] [FiberBundle ℂ L']
    {σ : ∀ z, L z} {σ' : ∀ z, L' z} {x : X} {s : Bool} (h : IsSignedTransverseZero σ x s)
    (h' : negPointTwistChartReading ℂ x σ =ᶠ[𝓝 (chartAt ℂ x x)]
      negPointTwistChartReading ℂ x σ') :
    IsSignedTransverseZero σ' x s := by
  obtain ⟨D, c, hD, hDc⟩ := h
  exact ⟨D, c, hD.congr_of_eventuallyEq h'.symm, hDc⟩

variable [T2Space X] [IsManifold 𝓘(ℂ) ∞ X] [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)]

/-- **Untwisting one zero among finitely many.** Let `σ` be a smooth section of `L` whose zeros
are `x` and the points of a finite set `S ∌ x`, with `x` transverse of sign `s`. Then the signed
point twist `L(-x)` (`s = false`) or `L(x)` (`s = true`) has a smooth section `τ` whose zeros are
exactly the points of `S`, and which near every point of `S` is `σ`, read in `L` through
`pointTwistDiv`. -/
theorem exists_untwist_section_of_finset {x : X} {S : Finset X} (hxS : x ∉ S) {σ : ∀ z, L z}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ fun z ↦ TotalSpace.mk' ℂ z (σ z))
    (hZ : ∀ z, σ z = 0 ↔ z = x ∨ z ∈ S) {s : Bool} (hx : IsSignedTransverseZero σ x s) :
    ∃ τ : ∀ z, (signedPointTwistCore ℂ L x s).Fiber z,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ (fun z ↦ TotalSpace.mk' ℂ z (τ z)) ∧
        (∀ z, τ z = 0 ↔ z ∈ S) ∧ ∀ y ∈ S, ∀ᶠ z in 𝓝 y, pointTwistDiv ℂ L x z (τ z) = σ z := by
  -- Disjoint open neighbourhoods `U` of `x` and `W` of `S`; the untwisting happens inside `U`.
  obtain ⟨U, W, hU, hW, hxU, hSW, hUW⟩ := SeparatedNhds.of_singleton_finset hxS
  have hxU' : x ∈ U := hxU rfl
  have hUS : ∀ z ∈ U, z ∉ S := fun z hz hzS ↦ hUW.notMem_of_mem_left hz (hSW hzS)
  obtain ⟨D, c, hD, hDc⟩ := hx
  have hσx : σ x = 0 := (hZ x).2 (Or.inl rfl)
  obtain ⟨τ, hτ, hτU, hτσ⟩ := exists_untwist_section hσ (hU.mem_nhds hxU')
    (fun z hz h0 ↦ ((hZ z).1 h0).resolve_right (hUS z hz)) s (c := c) (by
      filter_upwards [hD.eventually_norm_sub_sub_apply_lt hDc] with w hw
      cases s <;>
      simpa only [negPointTwistChartReading_chartAt_self ℂ hσx, sub_zero,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul, ite_true, ite_false,
        Bool.false_eq_true] using hw)
  refine ⟨τ, hτ, fun z ↦ ?_, fun y hy ↦ ?_⟩
  · by_cases hz : z ∈ U
    · exact ⟨fun h ↦ (hτU z hz h).elim, fun h ↦ (hUS z hz h).elim⟩
    · have hzx : z ≠ x := fun h ↦ hz (h ▸ hxU')
      have h := pointTwistDiv_eq_zero_iff (F := ℂ) (E := L) (x := x) (z := z) (τ z)
      rw [hτσ z hz, hZ z] at h
      simp only [hzx, false_or] at h
      exact h.symm
  · filter_upwards [hW.mem_nhds (hSW hy)] with z hz
    exact hτσ z fun hzU ↦ hUW.notMem_of_mem_left hzU hz

/-- **A section with signed transverse zeros identifies a line bundle with `𝒪(D)`.** Let `σ` be a
smooth section of `L` whose zeros are the distinct points `xᵢ` of a list `l` of pairs `(xᵢ, εᵢ)`,
each transverse of sign `εᵢ`. Then `L` is isomorphic to `𝒪(Σ ±xᵢ)`, with `+xᵢ` at the positive
zeros (`εᵢ = false`) and `-xᵢ` at the negative ones, by complex linear fibre isomorphisms which are
smooth on total spaces. -/
theorem exists_contMDiff_divisorCore_equiv_of_section (l : List (X × Bool))
    (hl : (l.map Prod.fst).Nodup) {σ : ∀ z, L z}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ fun z ↦ TotalSpace.mk' ℂ z (σ z))
    (hZ : ∀ z, σ z = 0 ↔ z ∈ l.map Prod.fst) (hT : ∀ p ∈ l, IsSignedTransverseZero σ p.1 p.2) :
    ∃ e : ∀ z, L z ≃L[ℂ] (divisorCore (l.map fun p ↦ (p.1, !p.2))).Fiber z,
      ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ fun p : TotalSpace ℂ L ↦
        TotalSpace.mk' ℂ (E := (divisorCore (l.map fun p ↦ (p.1, !p.2))).Fiber) p.proj
          (e p.proj p.snd) := by
  induction l generalizing L with
  | nil =>
    -- No zeros: `σ` trivializes `L`.
    exact ⟨_, contMDiff_fibreEquivOfNeZero hσ fun z h ↦ by simpa using (hZ z).1 h⟩
  | cons p l ih =>
    classical
    obtain ⟨x, s⟩ := p
    rw [List.forall_mem_cons] at hT
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hl hZ ⊢
    -- Untwist the zero at `x` in `L(±x)`; the other zeros and their signs are unchanged.
    obtain ⟨τ, hτ, hτZ, hτσ⟩ := exists_untwist_section_of_finset
      (S := (l.map Prod.fst).toFinset) (by simpa using hl.1) hσ (by simpa using hZ) hT.1
    have hne : ∀ q ∈ l, q.1 ≠ x := fun q hq h ↦ hl.1 (h ▸ List.mem_map_of_mem hq)
    obtain ⟨e, he⟩ := ih hl.2 hτ (fun z ↦ by simpa using hτZ z) fun q hq ↦ (hT.2 q hq).congr
      (negPointTwistChartReading_eventuallyEq_of_pointTwistDiv (hne q hq)
        (hτσ q.1 (List.mem_toFinset.2 (List.mem_map_of_mem hq)))).symm
    -- `L ≅ L(±x)(∓x) ≅ 𝒪(D')(∓x)`, by cancellation and functoriality.
    refine ⟨fun z ↦ (signedPointTwistCancelEquiv ℂ L x s z).symm.trans
      (signedPointTwistEquiv ℂ ℂ x (!s) e z), ((contMDiff_signedPointTwistEquiv x (!s) he).comp
        (signedPointTwistCancelDiffeomorph ℂ L 𝓘(ℝ, ℂ) x s).symm.contMDiff).congr fun p ↦ ?_⟩
    rw [Function.comp_apply, signedPointTwistCancelDiffeomorph_symm_apply]
    rfl

open Classical in
/-- **Every smooth line bundle is the bundle of a divisor.** Let `L` be a complex line bundle with
fibre `ℂ` over a compact Riemann surface `X`, whose underlying real bundle is smooth. Then there is
a list `D` of signed points of `X`, with distinct points, and complex linear fibre isomorphisms
`L z ≃ 𝒪(D) z` which are smooth on total spaces, such that the degree of `D` is the Euler number
`c₁(L)[X]` of `L` with its complex orientation. -/
theorem exists_contMDiff_divisorCore_equiv [CompactSpace X] :
    ∃ (D : List (X × Bool)) (e : ∀ z, L z ≃L[ℂ] (divisorCore D).Fiber z),
      (D.map Prod.fst).Nodup ∧
      ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ (fun p : TotalSpace ℂ L ↦
        TotalSpace.mk' ℂ (E := (divisorCore D).Fiber) p.proj (e p.proj p.snd)) ∧
      ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
          (complexEulerClass ℂ L (r := 0) (Module.finrank_self ℂ))).down = divisorDegree D := by
  obtain ⟨σ, hZ, ε, hT, hc⟩ := exists_contMDiffSection_complexEulerClass_eq_sum_sign (L := L)
  -- The zeros of `σ`, each with its sign.
  set l := hZ.toFinset.toList.map fun z ↦ (z, ε z)
  have hl : l.map Prod.fst = hZ.toFinset.toList := by simp [l, Function.comp_def]
  obtain ⟨e, he⟩ := exists_contMDiff_divisorCore_equiv_of_section l
    (hl ▸ Finset.nodup_toList _) σ.contMDiff (fun z ↦ by simp [hl])
    fun p hp ↦ by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
      exact hT z (by simpa using hz)
  refine ⟨_, e, by simpa [l, Function.comp_def] using Finset.nodup_toList hZ.toFinset, he, ?_⟩
  rw [hc, divisorDegree, ← Finset.sum_map_toList]
  simp only [l, List.map_map, Function.comp_def]
  exact congrArg List.sum (List.map_congr_left fun z _ ↦ by cases ε z <;> rfl)

end Assembly

end TauCeti
