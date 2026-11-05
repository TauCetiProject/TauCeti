/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Covariant derivatives read in a local frame

Let `V → M` be a finite-rank smooth vector bundle and let `e` be a trivialization of `V` with
`b` a basis of the model fibre, so that `e.localFrame b` is a smooth frame of `V` over
`e.baseSet`. This file reads a covariant derivative on `V` in that frame.

Writing `σ = ∑ i, σⁱ • eᵢ` over `e.baseSet`, any covariant derivative `∇` satisfies

`∇ σ = ∑ i, dσⁱ ⊗ eᵢ + ∑ i, σⁱ • ∇ eᵢ`

on `e.baseSet`. The first summand is itself a covariant derivative over `e.baseSet`, the *flat*
one attached to the frame; it is `frameCovariantDerivative`, and it witnesses that covariant
derivatives always exist locally. The second summand is tensorial in `σ`, and is the Christoffel
form `christoffelForm` of `∇` in the frame: `∇` is the flat derivative plus `christoffelForm`.

For an arbitrary local frame, `IsLocalFrameOn.covariantDerivative_eq_sum` gives the same product
rule directly in its native coefficients.

Pairing `e` with a trivialization `eT` of the tangent bundle transports `christoffelForm` to a
model-space continuous bilinear map `bundleChristoffelMap`, which gives the coordinate formula
`dg + Γ(g, ·)` for differentiating a section of `V` along a coordinate tangent vector.
Specializing to the tangent bundle (`eT = e`) yields `christoffelMap` and the scalar Christoffel
symbols `christoffelSymbol`; they are `C^∞` on `e.baseSet` for a `C^∞` covariant derivative, and
they give the classical coordinate formula for `∇ σ` along a frame direction.

## Main definitions and results

* `TauCeti.Manifold.frameCovariantDerivative`: the flat covariant derivative attached to a local
  frame, and `TauCeti.Manifold.isCovariantDerivativeOn_frameCovariantDerivative`, the proof that
  it is a covariant derivative over the trivialization base set.
* `TauCeti.Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum`: the local frame
  formula for an arbitrary covariant derivative.
* `TauCeti.Manifold.covariantDerivative_eq_of_localFrame_eq`: two covariant derivatives which
  agree on the frame sections at a point agree at that point on every section differentiable
  there.
* `TauCeti.Manifold.christoffelForm`: the Christoffel form of a covariant derivative in a local
  frame, with `TauCeti.Manifold.christoffelForm_apply` computing it and
  `TauCeti.Manifold.covariantDerivative_eq_add_christoffelForm` expressing the covariant
  derivative as the flat one plus it.
* `TauCeti.Manifold.bundleChristoffelMap` and `TauCeti.Manifold.christoffelMap`: the Christoffel
  form transported to a continuous bilinear map on the model spaces (for a general vector bundle
  and for the tangent bundle), with `TauCeti.Manifold.bundleChristoffelMap_apply`,
  `TauCeti.Manifold.christoffelMap_apply`, `TauCeti.Manifold.contMDiffOn_bundleChristoffelMap`,
  and `TauCeti.Manifold.contMDiffOn_christoffelMap`.
* `TauCeti.Manifold.covariantDerivative_symm_eq_christoffelForm`,
  `TauCeti.Manifold.covariantDerivative_symm_apply_symm_bundle`, and
  `TauCeti.Manifold.covariantDerivative_symm_apply_symm`: a covariant derivative differentiates a
  section with constant coordinates in the trivialization by the Christoffel form / map.
* `TauCeti.Manifold.covariantDerivative_symm_comp_apply_symm_bundle` and
  `TauCeti.Manifold.covariantDerivative_symm_comp_apply_symm`: the covariant derivative of a
  section with coordinates `g` in the trivialization has coordinates `dg + Γ(g, ·)`.
* `TauCeti.Manifold.christoffelSymbol`: the scalar Christoffel symbols of a covariant derivative
  on the tangent bundle in a local frame, with
  `TauCeti.Manifold.covariantDerivative_localFrame_eq_sum_christoffelSymbol` expanding
  `∇_{eᵢ} eⱼ`, `TauCeti.Manifold.contMDiffOn_christoffelSymbol` their smoothness, and
  `TauCeti.Manifold.christoffelForm_localFrame_apply` identifying them with the frame components
  of the Christoffel form.
* `TauCeti.Manifold.covariantDerivative_apply_localFrame_eq_sum`: the classical coordinate
  formula `(∇_{eᵢ} σ)ᵏ = dσᵏ(eᵢ) + ∑ j, σʲ Γᵏᵢⱼ`.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Regularity of the Levi-Civita connection".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

public section

open Bundle FiberBundle Module Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace IsLocalFrameOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {ι : Type*} [Fintype ι] {s : ι → Π x, V x} {u : Set M} {x : M}

/-- A covariant derivative in a local frame differentiates the coefficients and the frame
sections by the product rule. Only differentiability of the coefficient functions at the point
is required. -/
theorem covariantDerivative_eq_sum {n : ℕ∞ω} (hs : IsLocalFrameOn I F n s u)
    (hn : 1 ≤ n) (hu : u ∈ 𝓝 x)
    {cov : (Π x, V x) → Π x, TangentSpace I x →L[𝕜] V x}
    (hcov : IsCovariantDerivativeOn F cov u) {σ : Π x, V x}
    (hcoeff : ∀ i, MDiffAt (fun y ↦ hs.coeff i y (σ y)) x) :
    cov σ x = ∑ i, (hs.coeff i x (σ x) • cov (s i) x +
      (mvfderiv I (fun y ↦ hs.coeff i y (σ y)) x).smulRight (s i x)) := by
  have hframe (i : ι) : MDiffAt (T% (s i)) x :=
    (((hs.contMDiffOn i).contMDiffAt hu).of_le hn).mdifferentiableAt one_ne_zero
  have hterm (i : ι) : MDiffAt (T% ((fun y ↦ hs.coeff i y (σ y)) • s i)) x :=
    (hcoeff i).smul_section (hframe i)
  have hsum : MDiffAt (T% (∑ i, (fun y ↦ hs.coeff i y (σ y)) • s i)) x := by
    simpa [Finset.sum_apply] using MDifferentiableAt.sum_section
      (t := fun i ↦ (fun y ↦ hs.coeff i y (σ y)) • s i)
      (s := (Finset.univ : Finset ι)) (fun i _ ↦ hterm i)
  have heq : ∀ᶠ y in 𝓝 x, σ y = (∑ i, (fun z ↦ hs.coeff i z (σ z)) • s i) y := by
    filter_upwards [hs.eventually_eq_sum_coeff_smul σ hu] with y hy
    simpa [Finset.sum_apply] using hy
  have hσ := hsum.congr_of_eventuallyEq (heq.mono fun y hy ↦ congrArg (TotalSpace.mk' F y) hy)
  rw [hcov.congr_of_eventuallyEq hσ hsum hu heq,
    TauCeti.Manifold.covariantDerivative_sum hcov (mem_of_mem_nhds hu) (fun i _ ↦ hterm i)]
  exact Finset.sum_congr rfl fun i _ ↦ hcov.leibniz (hframe i) (hcoeff i) (mem_of_mem_nhds hu)

end IsLocalFrameOn

namespace TauCeti.Manifold

section GeneralFibre

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {x : M} {σ : Π x : M, V x}
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}

variable [ContMDiffVectorBundle 1 F V I]
  {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 F)
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]

/-! ### The flat covariant derivative of a local frame -/

variable (I) in
/-- The flat covariant derivative attached to the local frame induced by a trivialization `e` of
`V` and a basis `b` of the model fibre: it differentiates the coefficient functions of a section
and keeps the frame fixed. It is a covariant derivative over `e.baseSet`, by
`isCovariantDerivativeOn_frameCovariantDerivative`; outside that set it carries a junk value. -/
def frameCovariantDerivative (b : Basis ι 𝕜 F)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (σ : Π x : M, V x) (x : M) : TangentSpace I x →L[𝕜] V x :=
  ∑ i, (mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x).smulRight
    (e.localFrame b i x)

/-- The flat covariant derivative of the frame, evaluated on a tangent vector. -/
theorem frameCovariantDerivative_apply (v : TangentSpace I x) :
    frameCovariantDerivative I b e σ x v =
      ∑ i, mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v •
        e.localFrame b i x := by
  simp [frameCovariantDerivative]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- The flat frame derivative satisfies the covariant-derivative axioms on the base set of the
trivialization defining the frame. -/
theorem isCovariantDerivativeOn_frameCovariantDerivative :
    IsCovariantDerivativeOn F (frameCovariantDerivative I b e) e.baseSet where
  add {σ σ'} {x} hσ hσ' hx := by
    have key (i : ι) :
        mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) (σ + σ')) x =
          mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x +
            mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ') x := by
      have hsplit : (LinearMap.piApply (e.localFrameCoeff I b i)) (σ + σ') =
          (LinearMap.piApply (e.localFrameCoeff I b i)) σ +
            (LinearMap.piApply (e.localFrameCoeff I b i)) σ' := by
        ext y; simp
      rw [hsplit, mvfderiv_add (mdifferentiableAt_localFrameCoeff b hx hσ i)
        (mdifferentiableAt_localFrameCoeff b hx hσ' i)]
    ext v
    simp only [frameCovariantDerivative_apply, add_apply, key, add_smul,
      Finset.sum_add_distrib]
  leibniz {σ g x} hσ hg hx := by
    have hcoeff (i : ι) : MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x :=
      mdifferentiableAt_localFrameCoeff b hx hσ i
    have key (i : ι) (v : TangentSpace I x) :
        mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) (g • σ)) x v =
          g x * mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v +
            mvfderiv I g x v * e.localFrameCoeff I b i x (σ x) := by
      have hsplit : (LinearMap.piApply (e.localFrameCoeff I b i)) (g • σ) =
          g * (LinearMap.piApply (e.localFrameCoeff I b i)) σ := by
        ext y; simp
      rw [hsplit, mvfderiv_mul hg (hcoeff i)]
      simp [-mvfderiv_apply_eq_mfderiv_apply, mul_comm]
    ext v
    simp only [frameCovariantDerivative_apply, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, key, add_smul, mul_smul, Finset.sum_add_distrib,
      ← Finset.smul_sum]
    rw [← e.eq_sum_localFrameCoeff_smul (s := σ) hx]

/-! ### The local frame formula -/

/-- The local frame formula: over the base set of a trivialization, a covariant derivative is the
flat derivative of the frame coefficients plus the coefficients times the covariant derivatives
of the frame sections. -/
theorem covariantDerivative_eq_frameCovariantDerivative_add_sum
    (hcov : IsCovariantDerivativeOn F cov e.baseSet) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = frameCovariantDerivative I b e σ x +
      ∑ i, e.localFrameCoeff I b i x (σ x) • cov (e.localFrame b i) x := by
  have h := (e.isLocalFrameOn_localFrame_baseSet I 1 b).covariantDerivative_eq_sum
    le_rfl (e.open_baseSet.mem_nhds hx) hcov (fun i ↦ mdifferentiableAt_localFrameCoeff b hx hσ i)
  rw [Finset.sum_add_distrib, add_comm] at h
  rw [frameCovariantDerivative]
  exact h

omit [Fintype ι] in
/-- Two covariant derivatives over the base set of a trivialization which agree on the frame
sections at a point agree there on every section differentiable at that point. -/
theorem covariantDerivative_eq_of_localFrame_eq [Finite ι]
    {cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    (hcov' : IsCovariantDerivativeOn F cov' e.baseSet) (hx : x ∈ e.baseSet)
    (hframe : ∀ i, cov (e.localFrame b i) x = cov' (e.localFrame b i) x)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = cov' σ x := by
  have : Fintype ι := Fintype.ofFinite ι
  rw [covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov hx hσ,
    covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov' hx hσ]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hframe i]

/-! ### The Christoffel form -/

/-- The Christoffel form of a covariant derivative in a local frame: the endomorphism-valued
one-form by which the covariant derivative differs from the flat derivative
`frameCovariantDerivative` of the frame. -/
def christoffelForm (hcov : IsCovariantDerivativeOn F cov e.baseSet) :
    Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  hcov.difference (isCovariantDerivativeOn_frameCovariantDerivative b)

/-- A covariant derivative is the flat derivative of its frame plus its Christoffel form. -/
theorem covariantDerivative_eq_add_christoffelForm
    (hcov : IsCovariantDerivativeOn F cov e.baseSet) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = frameCovariantDerivative I b e σ x + christoffelForm b hcov x (σ x) := by
  rw [christoffelForm, IsCovariantDerivativeOn.difference_apply _ _ hx hσ]
  abel

/-- The Christoffel form is the frame expansion of the covariant derivatives of the frame
sections. -/
theorem christoffelForm_apply (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    (hx : x ∈ e.baseSet) (v : V x) :
    christoffelForm b hcov x v = ∑ i, e.localFrameCoeff I b i x v • cov (e.localFrame b i) x := by
  have hext : MDiffAt (T% (extend F v)) x := mdifferentiableAt_extend I F v
  have hv : (extend F v) x = v := extend_apply_self F v
  have h := covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov hx hext
  rw [covariantDerivative_eq_add_christoffelForm b hcov hx hext, hv] at h
  exact add_right_injective _ h

/-- A covariant derivative differentiates the section with constant coordinates `v` in the
trivialization `e` by its Christoffel form: the flat derivative of such a section vanishes. -/
theorem covariantDerivative_symm_eq_christoffelForm
    (hcov : IsCovariantDerivativeOn F cov e.baseSet) (hx : x ∈ e.baseSet) (v : F) :
    cov (fun y ↦ e.symm y v) x = christoffelForm b hcov x (e.symm x v) := by
  have hσ : MDiffAt (T% (fun y ↦ e.symm y v)) x :=
    ((contMDiffOn_symm_baseSet v).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (e.open_baseSet.mem_nhds hx)
  rw [covariantDerivative_eq_add_christoffelForm b hcov hx hσ, add_eq_right]
  ext w
  rw [frameCovariantDerivative_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  -- The `i`-th coefficient of the section is the constant `b.repr v i` on `e.baseSet`.
  have hconst : (LinearMap.piApply (e.localFrameCoeff I b i)) (fun y ↦ e.symm y v) =ᶠ[𝓝 x]
      fun _ ↦ b.repr v i :=
    Filter.eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦
      (e.localFrameCoeff_eq_coeff (I := I) (b := b) (s := fun y ↦ e.symm y v) hy).trans
        (by simp [e.apply_mk_symm hy])
  have hzero :
      mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) fun y ↦ e.symm y v) x = 0 := by
    have h := ((hasMFDerivAt_const (I := I) (I' := 𝓘(𝕜, 𝕜)) (b.repr v i) x).congr_of_eventuallyEq
      hconst).mfderiv
    ext u
    simp only [mvfderiv, ContinuousLinearMap.comp_apply, h, zero_apply, map_zero]
  rw [hzero]
  simp

section BundleChristoffelMap

variable [IsManifold I 1 M]
  (eT : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas eT]

/-- The Christoffel form of a covariant derivative on `V`, transported through the bundle
trivialization `e` and a tangent-bundle trivialization `eT` to a continuous bilinear map
`F →L[𝕜] E →L[𝕜] F`. -/
def bundleChristoffelMap (hcov : IsCovariantDerivativeOn F cov e.baseSet) (x : M) :
    F →L[𝕜] E →L[𝕜] F :=
  ((e.continuousLinearMap (RingHom.id 𝕜) (eT.continuousLinearMap (RingHom.id 𝕜) e))
    ⟨x, christoffelForm b hcov x⟩).2

/-- The bundle Christoffel map is the Christoffel form read in the trivializations `e` and `eT`:
it acts on the coordinates of a fibre vector and of a tangent direction, returning the coordinates
of the value of the Christoffel form on them. -/
theorem bundleChristoffelMap_apply (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    (hx : x ∈ e.baseSet) (hxT : x ∈ eT.baseSet) (v : F) (u : E) :
    bundleChristoffelMap b eT hcov x v u =
      e.continuousLinearMapAt 𝕜 x
        (christoffelForm b hcov x (e.symmL 𝕜 x v) (eT.symmL 𝕜 x u)) := by
  have hxe : x ∈ (eT.continuousLinearMap (RingHom.id 𝕜) e).baseSet := ⟨hxT, hx⟩
  simp only [bundleChristoffelMap, Bundle.Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.comp_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := 𝕜) (eT.continuousLinearMap (RingHom.id 𝕜) e) hxe]
  simp only [Bundle.Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply]

/-- A covariant derivative on `V` differentiates the section with constant coordinates `v` in `e`,
along the tangent vector with coordinates `u` in `eT`, by `bundleChristoffelMap`. -/
theorem covariantDerivative_symm_apply_symm_bundle
    (hcov : IsCovariantDerivativeOn F cov e.baseSet) (hx : x ∈ e.baseSet) (hxT : x ∈ eT.baseSet)
    (v : F) (u : E) :
    cov (fun y ↦ e.symm y v) x (eT.symm x u) =
      e.symm x (bundleChristoffelMap b eT hcov x v u) := by
  rw [covariantDerivative_symm_eq_christoffelForm b hcov hx,
    bundleChristoffelMap_apply b eT hcov hx hxT]
  simp only [e.symmL_apply hx, eT.symmL_apply hxT,
    Bundle.Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e hx]
  exact (e.symm_apply_apply_mk hx _).symm

/-- **The coordinate formula for a covariant derivative on a vector bundle.** The covariant
derivative of the section with coordinates `g` in `e`, along the tangent vector with coordinates
`u` in `eT`, has coordinates `dg(u) + Γ(g, u)`, where `Γ = bundleChristoffelMap b eT hcov`. -/
theorem covariantDerivative_symm_comp_apply_symm_bundle
    (hcov : IsCovariantDerivativeOn F cov e.baseSet) (hx : x ∈ e.baseSet) (hxT : x ∈ eT.baseSet)
    {g : M → F} (hg : MDifferentiableAt I 𝓘(𝕜, F) g x) (u : E) :
    cov (fun y ↦ e.symm y (g y)) x (eT.symm x u) =
      e.symm x (mvfderiv I g x (eT.symm x u) + bundleChristoffelMap b eT hcov x (g x) u) := by
  have hread : ∀ᶠ y in 𝓝 x, (e ⟨y, e.symm y (g y)⟩).2 = g y :=
    Filter.eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ by rw [e.apply_mk_symm hy]
  have hσ : MDiffAt (T% (fun y ↦ e.symm y (g y))) x :=
    (e.mdifferentiableAt_section_iff I _ hx).2 (hg.congr_of_eventuallyEq hread)
  have hcoeff (i : ι) : mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i))
      (fun y ↦ e.symm y (g y))) x (eT.symm x u) = b.coord i (mvfderiv I g x (eT.symm x u)) := by
    have heq : (LinearMap.piApply (e.localFrameCoeff I b i)) (fun y ↦ e.symm y (g y)) =ᶠ[𝓝 x]
        ((b.coord i).toContinuousLinearMap ∘ g) := by
      filter_upwards [hread, e.open_baseSet.mem_nhds hx] with y hy hyb
      simp [e.localFrameCoeff_eq_coeff (I := I) (b := b) (s := fun y ↦ e.symm y (g y)) hyb, hy]
    rw [heq.mvfderiv_eq, mvfderiv_comp_apply_of_differentiableAt
      (b.coord i).toContinuousLinearMap.differentiableAt hg, ContinuousLinearMap.fderiv,
      LinearMap.coe_toContinuousLinearMap']
  have hframe : frameCovariantDerivative I b e (fun y ↦ e.symm y (g y)) x (eT.symm x u) =
      e.symm x (mvfderiv I g x (eT.symm x u)) := by
    rw [frameCovariantDerivative_apply]
    simp_rw [hcoeff, ← symmL_basis_eq_localFrame b hx, ← map_smul, ← map_sum]
    simp only [Basis.coord_apply, b.sum_repr, e.symmL_apply (R := 𝕜) hx]
  have hchris : christoffelForm b hcov x (e.symm x (g x)) (eT.symm x u) =
      e.symm x (bundleChristoffelMap b eT hcov x (g x) u) := by
    rw [bundleChristoffelMap_apply b eT hcov hx hxT, e.symmL_apply (R := 𝕜) hx,
      eT.symmL_apply (R := 𝕜) hxT,
      Bundle.Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e hx,
      e.symm_apply_apply_mk hx]
  rw [covariantDerivative_eq_add_christoffelForm b hcov hx hσ, add_apply, hframe, hchris,
    ← e.symmL_apply (R := 𝕜) hx, ← e.symmL_apply (R := 𝕜) hx, ← e.symmL_apply (R := 𝕜) hx,
    map_add]

/-- The bundle Christoffel map of a `C^n` covariant derivative is `C^n` on the intersection of the
base sets of `e` and `eT`. -/
theorem contMDiffOn_bundleChristoffelMap {n : ℕ∞ω}
    (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle n F V I]
    [ContMDiffVectorBundle (n + 1) F V I]
    [ContMDiffCovariantDerivativeOn F n cov e.baseSet] :
    CMDiff[e.baseSet ∩ eT.baseSet] n (bundleChristoffelMap b eT hcov) := by
  let O := e.baseSet ∩ eT.baseSet
  let eTV := eT.continuousLinearMap (RingHom.id 𝕜) e
  let eh := e.continuousLinearMap (RingHom.id 𝕜) eTV
  have hmaps : MapsTo (id : M → M) O (e.baseSet ∩ eTV.baseSet) := fun _ hy ↦ ⟨hy.1, hy.2, hy.1⟩
  have hframeEval (j : ι) :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) n
        (fun y ↦ TotalSpace.mk' (E →L[𝕜] F) (E := fun z ↦ TangentSpace I z →L[𝕜] V z) y
          (christoffelForm b hcov y (e.localFrame b j y))) O := by
    have hj : ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) n
        (fun y ↦ TotalSpace.mk' (E →L[𝕜] F) (E := fun z ↦ TangentSpace I z →L[𝕜] V z) y
          (cov (e.localFrame b j) y)) e.baseSet :=
      ContMDiffCovariantDerivativeOn.contMDiff (e.contMDiffOn_localFrame_baseSet (n + 1) b j)
    refine (hj.mono inter_subset_left).congr fun y hy ↦ ?_
    congr 1
    rw [christoffelForm_apply b hcov hy.1]
    classical
    simp [localFrameCoeff_localFrame b hy.1]
  have hsec : ContMDiffOn I (I.prod 𝓘(𝕜, F →L[𝕜] E →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] E →L[𝕜] F)
        (E := fun z ↦ V z →L[𝕜] TangentSpace I z →L[𝕜] V z) y
        (christoffelForm b hcov y)) O :=
    contMDiffOn_hom_of_localFrame (e' := eTV) b contMDiffOn_id hmaps hframeEval
  exact ((eh.contMDiffOn_iff fun _ hy ↦ eh.mem_source.mpr (hmaps hy)).1 hsec).2

end BundleChristoffelMap

end GeneralFibre

/-! ### Christoffel symbols on the tangent bundle -/

section TangentBundle

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {ι : Type*} (b : Basis ι 𝕜 E)
  {e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)} [MemTrivializationAtlas e]
  {x : M}
  {cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}

variable (I) in
/-- The Christoffel symbols of a covariant derivative on the tangent bundle, in the local frame
induced by a trivialization `e` and a basis `b` of the model space: `christoffelSymbol I b e cov
i j k x` is the `k`-th coefficient of `∇_{eᵢ} eⱼ` at `x`. Outside `e.baseSet` it carries a junk
value. -/
def christoffelSymbol (b : Basis ι 𝕜 E)
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x))
    (i j k : ι) (x : M) : 𝕜 :=
  e.localFrameCoeff I b k x (cov (e.localFrame b j) x (e.localFrame b i x))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- The defining formula for the Christoffel symbols. -/
@[simp]
theorem christoffelSymbol_apply (i j k : ι) :
    christoffelSymbol I b e cov i j k x =
      e.localFrameCoeff I b k x (cov (e.localFrame b j) x (e.localFrame b i x)) :=
  (rfl)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- The Christoffel symbols expand the covariant derivative of a frame section along a frame
direction back in the frame. -/
theorem covariantDerivative_localFrame_eq_sum_christoffelSymbol [Fintype ι] (hx : x ∈ e.baseSet)
    (i j : ι) :
    cov (e.localFrame b j) x (e.localFrame b i x) =
      ∑ k, christoffelSymbol I b e cov i j k x • e.localFrame b k x := by
  have hexp : extend E (cov (e.localFrame b j) x (e.localFrame b i x)) x =
      ∑ k, e.localFrameCoeff I b k x
          (extend E (cov (e.localFrame b j) x (e.localFrame b i x)) x) • e.localFrame b k x :=
    e.eq_sum_localFrameCoeff_smul hx
  rw [extend_apply_self] at hexp
  exact hexp

/-- The Christoffel form transported through the tangent-bundle trivialization to a
model-space-valued continuous bilinear map. -/
def christoffelMap [Fintype ι] (hcov : IsCovariantDerivativeOn E cov e.baseSet) (x : M) :
    E →L[𝕜] E →L[𝕜] E :=
  bundleChristoffelMap b e hcov x

/-- On the tangent bundle, `christoffelMap` is `bundleChristoffelMap` with `eT = e`. -/
theorem christoffelMap_eq_bundleChristoffelMap [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) :
    christoffelMap b hcov = bundleChristoffelMap b e hcov :=
  (rfl)

/-- The model-space Christoffel map is the Christoffel form read in the trivialization: it acts
on the coordinates of a fibre vector and of a tangent direction, and returns the coordinates of
the value of the Christoffel form on them. -/
theorem christoffelMap_apply [Fintype ι] (hcov : IsCovariantDerivativeOn E cov e.baseSet)
    (hx : x ∈ e.baseSet) (v w : E) :
    christoffelMap b hcov x v w =
      e.continuousLinearMapAt 𝕜 x
        (christoffelForm b hcov x (e.symmL 𝕜 x v) (e.symmL 𝕜 x w)) :=
  bundleChristoffelMap_apply b e hcov hx hx v w

/-- A covariant derivative on the tangent bundle differentiates the vector field with constant
coordinates `v` in the trivialization `e`, in the direction with coordinates `u`, by the Christoffel
map: the result has coordinates `christoffelMap b hcov x v u`. -/
theorem covariantDerivative_symm_apply_symm [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) (v u : E) :
    cov (fun y ↦ e.symm y v) x (e.symm x u) = e.symm x (christoffelMap b hcov x v u) :=
  covariantDerivative_symm_apply_symm_bundle b e hcov hx hx v u

/-- **The coordinate formula for a covariant derivative on the tangent bundle.**  The covariant
derivative of the vector field with coordinates `g` in the trivialization `e`, in the direction
with coordinates `u`, has coordinates `dg(u) + Γ(g, u)`, where `Γ` is the Christoffel map. -/
theorem covariantDerivative_symm_comp_apply_symm [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) {g : M → E}
    (hg : MDifferentiableAt I 𝓘(𝕜, E) g x) (u : E) :
    cov (fun y ↦ e.symm y (g y)) x (e.symm x u) =
      e.symm x (mvfderiv I g x (e.symm x u) + christoffelMap b hcov x (g x) u) :=
  covariantDerivative_symm_comp_apply_symm_bundle b e hcov hx hx hg u

/-- The Christoffel symbols of a `C^n` covariant derivative are `C^n` on the base set of the
trivialization defining the frame. -/
theorem contMDiffOn_christoffelSymbol {n : ℕ∞ω}
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I]
    [ContMDiffCovariantDerivativeOn E n cov e.baseSet] (i j k : ι) :
    CMDiff[e.baseSet] n (christoffelSymbol I b e cov i j k) := by
  have hj : CMDiff[e.baseSet] (n + 1) (T% (e.localFrame b j)) :=
    e.contMDiffOn_localFrame_baseSet (n + 1) b j
  have hi : CMDiff[e.baseSet] n (T% (e.localFrame b i)) :=
    e.contMDiffOn_localFrame_baseSet n b i
  have hcov : ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E)
        (E := fun y : M ↦ (TangentSpace I y →L[𝕜] TangentSpace I y)) y
        (cov (e.localFrame b j) y)) e.baseSet :=
    ContMDiffCovariantDerivativeOn.contMDiff hj
  have happ : CMDiff[e.baseSet] n
      (T% (fun y ↦ cov (e.localFrame b j) y (e.localFrame b i y))) :=
    ContMDiffOn.clm_bundle_apply hcov hi
  exact contMDiffOn_baseSet_localFrameCoeff b happ k

variable {σ : Π x : M, TangentSpace I x}

/-- The frame components of the Christoffel form are the Christoffel symbols. -/
theorem christoffelForm_localFrame_apply [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) (i j : ι) :
    christoffelForm b hcov x (e.localFrame b j x) (e.localFrame b i x) =
      ∑ k, christoffelSymbol I b e cov i j k x • e.localFrame b k x := by
  classical
  rw [christoffelForm_apply b hcov hx]
  have hcollapse : ∑ l, e.localFrameCoeff I b l x (e.localFrame b j x) • cov (e.localFrame b l) x
      = cov (e.localFrame b j) x := by
    simp [localFrameCoeff_localFrame b hx]
  rw [hcollapse]
  exact covariantDerivative_localFrame_eq_sum_christoffelSymbol b hx i j

/-- The basis coefficients of the model-space Christoffel map are the scalar Christoffel
symbols. -/
@[simp]
theorem christoffelMap_apply_basis [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) (i j : ι) :
    christoffelMap b hcov x (b j) (b i) =
      ∑ k, christoffelSymbol I b e cov i j k x • b k := by
  classical
  rw [christoffelMap_apply b hcov hx, symmL_basis_eq_localFrame b hx j,
    symmL_basis_eq_localFrame b hx i,
    christoffelForm_localFrame_apply b hcov hx i j]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by
    rw [map_smul, continuousLinearMapAt_localFrame b hx k]

/-- The scalar basis coefficients of the model-space Christoffel map are precisely the
Christoffel symbols. -/
theorem coord_christoffelMap_apply_basis [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) (i j k : ι) :
    b.coord k (christoffelMap b hcov x (b j) (b i)) =
      christoffelSymbol I b e cov i j k x := by
  classical
  rw [christoffelMap_apply_basis b hcov hx i j]
  simp [Basis.coord_apply, Finsupp.single_apply]

/-- The model-space Christoffel map of a `C^n` covariant derivative is `C^n` on the base set of
the trivialization defining its coordinates. -/
theorem contMDiffOn_christoffelMap [Fintype ι] {n : ℕ∞ω}
    (hcov : IsCovariantDerivativeOn E cov e.baseSet)
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I]
    [ContMDiffCovariantDerivativeOn E n cov e.baseSet] :
    CMDiff[e.baseSet] n (christoffelMap b hcov) :=
  Set.inter_self e.baseSet ▸ contMDiffOn_bundleChristoffelMap b e hcov

/-- The classical coordinate formula for a covariant derivative on the tangent bundle: along the
frame direction `eᵢ`, the `k`-th component of `∇ σ` is the derivative of the `k`-th coefficient of
`σ` plus the Christoffel contraction `∑ j, σʲ Γᵏᵢⱼ`. -/
theorem covariantDerivative_apply_localFrame_eq_sum [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) (i : ι) :
    cov σ x (e.localFrame b i x) =
      ∑ k, (mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b k)) σ) x (e.localFrame b i x) +
        ∑ j, e.localFrameCoeff I b j x (σ x) * christoffelSymbol I b e cov i j k x) •
          e.localFrame b k x := by
  have hΓ (j : ι) : cov (e.localFrame b j) x (e.localFrame b i x) =
      ∑ k, christoffelSymbol I b e cov i j k x • e.localFrame b k x :=
    covariantDerivative_localFrame_eq_sum_christoffelSymbol b hx i j
  rw [covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov hx hσ]
  simp only [add_apply, frameCovariantDerivative_apply, sum_apply, smul_apply, hΓ,
    Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_comm]

end TangentBundle

end TauCeti.Manifold
