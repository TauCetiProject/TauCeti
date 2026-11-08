/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorField.Regularity

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

Specializing to the tangent bundle and expanding `∇_{eᵢ} eⱼ` again in the frame gives the scalar
Christoffel symbols `christoffelSymbol`; they are `C^∞` on `e.baseSet` for a `C^∞` covariant
derivative, and they give the classical coordinate formula for `∇ σ` along a frame direction.

## Main definitions and results

* `TauCeti.Manifold.frameCovariantDerivative`: the flat covariant derivative attached to a local
  frame, and `TauCeti.Manifold.isCovariantDerivativeOn_frameCovariantDerivative`, the proof that
  it is a covariant derivative over the trivialization base set, and
  `TauCeti.Manifold.contMDiffCovariantDerivativeOn_frameCovariantDerivative`, its regularity
  there.
* `TauCeti.Manifold.frameCovariantDerivative_eq_symmL_comp`: the flat derivative of a section whose
  frame coefficients are the coordinates of a model-valued map, and
  `TauCeti.Manifold.frameCovariantDerivative_symmL_const`, its vanishing on constant coordinates.
* `TauCeti.Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum`: the local frame
  formula for an arbitrary covariant derivative.
* `TauCeti.Manifold.covariantDerivative_eq_of_localFrame_eq`: two covariant derivatives which
  agree on the frame sections at a point agree at that point on every section differentiable
  there.
* `TauCeti.Manifold.christoffelForm`: the Christoffel form of a covariant derivative in a local
  frame, with `TauCeti.Manifold.christoffelForm_apply` computing it and
  `TauCeti.Manifold.covariantDerivative_eq_add_christoffelForm` expressing the covariant
  derivative as the flat one plus it.
* `TauCeti.Manifold.covariantDerivative_symm_eq_christoffelForm` and
  `TauCeti.Manifold.covariantDerivative_symm_apply_symm`: a covariant derivative differentiates a
  section with constant coordinates in the trivialization by the Christoffel form, and on the
  tangent bundle by the Christoffel map.
* `TauCeti.Manifold.covariantDerivative_symm_comp_apply_symm`: on the tangent bundle, the
  covariant derivative of the vector field with coordinates `g` in the trivialization has
  coordinates `dg + Γ(g, ·)`.
* `TauCeti.Manifold.christoffelSymbol`: the scalar Christoffel symbols of a covariant derivative
  on the tangent bundle in a local frame, with
  `TauCeti.Manifold.covariantDerivative_localFrame_eq_sum_christoffelSymbol` expanding
  `∇_{eᵢ} eⱼ`, `TauCeti.Manifold.contMDiffOn_christoffelSymbol` their smoothness, and
  `TauCeti.Manifold.christoffelForm_localFrame_apply` identifying them with the frame components
  of the Christoffel form.
* `TauCeti.Manifold.christoffelMap`: the Christoffel form transported to a continuous bilinear map
  on the model space, with `TauCeti.Manifold.christoffelMap_apply` reading it back as the
  Christoffel form and `TauCeti.Manifold.contMDiffOn_christoffelMap` proving its smoothness.
* `TauCeti.Manifold.covariantDerivative_apply_localFrame_eq_sum`: the classical coordinate
  formula `(∇_{eᵢ} σ)ᵏ = dσᵏ(eᵢ) + ∑ j, σʲ Γᵏᵢⱼ`.

## References

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

omit [FiniteDimensional 𝕜 F] in
/-- If the coefficients of a section in the frame of `e` agree near `x` with the coordinates of a
model-valued map `g` that has derivative `A` at `x`, then its flat frame derivative at `x` is
`e.symmL x ∘ A`. -/
theorem frameCovariantDerivative_eq_symmL_comp {g : M → F}
    {A : TangentSpace I x →L[𝕜] F} (hg : HasMFDerivAt I 𝓘(𝕜, F) g x A)
    (hcoeff : ∀ i, (fun z ↦ e.localFrameCoeff I b i z (σ z)) =ᶠ[𝓝 x] fun z ↦ b.coord i (g z))
    (hx : x ∈ e.baseSet) :
    frameCovariantDerivative I b e σ x = (e.symmL 𝕜 x).comp A := by
  have : FiniteDimensional 𝕜 F := Module.Finite.of_basis b
  ext v
  rw [frameCovariantDerivative_apply]
  have hterm (i : ι) :
      mvfderiv I (LinearMap.piApply (e.localFrameCoeff I b i) σ) x v = b.coord i (A v) := by
    let k : F →L[𝕜] 𝕜 := LinearMap.toContinuousLinearMap (b.coord i)
    have hk : (fun z ↦ b.coord i (g z)) = ⇑k ∘ g := by
      rw [Function.comp_def]
      simp [k]
    have h := (((ContinuousLinearMap.hasMFDerivAt k).comp x hg).congr_of_eventuallyEq
      (hk ▸ hcoeff i)).mfderiv
    rw [mvfderiv_apply_eq_mfderiv_apply, LinearMap.piApply_apply, h]
    -- `tangentSpaceCast` and `fromTangentSpace` are the identity of the model space `𝕜` and
    -- `LinearMap.toContinuousLinearMap` has the same underlying function, so this is `rfl`.
    rfl
  simp only [hterm]
  have h1 : e.symmL 𝕜 x (A v) = e.symmL 𝕜 x (∑ i, b.coord i (A v) • b i) := by
    simp [Basis.sum_repr, Basis.coord_apply]
  rw [ContinuousLinearMap.comp_apply, h1, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, symmL_basis_eq_localFrame b hx i]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
/-- The section `z ↦ e.symmL z v` has constant coefficients in the frame of `e`, so its flat frame
derivative at a point of the base set vanishes. -/
@[simp]
theorem frameCovariantDerivative_symmL_const (hx : x ∈ e.baseSet) (v : F) :
    frameCovariantDerivative I b e (fun z ↦ e.symmL 𝕜 z v) x = 0 := by
  have hconst (i : ι) : mvfderiv I (LinearMap.piApply (e.localFrameCoeff I b i)
      (fun z ↦ e.symmL 𝕜 z v)) x = 0 := by
    have hc : HasMFDerivAt (M' := 𝕜) I 𝓘(𝕜, 𝕜) (fun _ : M ↦ b.coord i v) x
        (0 : TangentSpace I x →L[𝕜] 𝕜) := hasMFDerivAt_const _ _
    have h := (hc.congr_of_eventuallyEq (f₁ := fun z ↦ e.localFrameCoeff I b i z (e.symmL 𝕜 z v))
      (by
        filter_upwards [e.open_baseSet.mem_nhds hx] with z hz
        rw [e.localFrameCoeff_eq_coeff (b := b) (s := fun z ↦ e.symmL 𝕜 z v) hz,
          ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e hz,
          ← Basis.coord_apply]
        exact congrArg (b.coord i) (e.continuousLinearMapAt_symmL (R := 𝕜) hz v))).mfderiv
    ext w
    rw [mvfderiv_apply_eq_mfderiv_apply, LinearMap.piApply_apply, h]
    rfl
  ext w
  rw [frameCovariantDerivative_apply]
  simp only [hconst, zero_apply, zero_smul, Finset.sum_const_zero]

omit [FiniteDimensional 𝕜 F] in
/-- The flat frame derivative satisfies the covariant-derivative axioms on the base set of the
trivialization defining the frame. -/
theorem isCovariantDerivativeOn_frameCovariantDerivative :
    IsCovariantDerivativeOn F (frameCovariantDerivative I b e) e.baseSet where
  add {σ σ'} {x} hσ hσ' hx := by
    have : FiniteDimensional 𝕜 F := Module.Finite.of_basis b
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
    have : FiniteDimensional 𝕜 F := Module.Finite.of_basis b
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
      simp only [add_apply, smul_apply, smul_eq_mul, LinearMap.piApply_apply_apply]
      ring
    ext v
    simp only [frameCovariantDerivative_apply, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, key, add_smul, mul_smul, Finset.sum_add_distrib,
      ← Finset.smul_sum]
    rw [← e.eq_sum_localFrameCoeff_smul (s := σ) hx]

/-! ### The local frame formula -/

omit [FiniteDimensional 𝕜 F] in
/-- The local frame formula: over the base set of a trivialization, a covariant derivative is the
flat derivative of the frame coefficients plus the coefficients times the covariant derivatives
of the frame sections. -/
theorem covariantDerivative_eq_frameCovariantDerivative_add_sum
    (hcov : IsCovariantDerivativeOn F cov e.baseSet) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = frameCovariantDerivative I b e σ x +
      ∑ i, e.localFrameCoeff I b i x (σ x) • cov (e.localFrame b i) x := by
  have : FiniteDimensional 𝕜 F := Module.Finite.of_basis b
  have h := (e.isLocalFrameOn_localFrame_baseSet I 1 b).covariantDerivative_eq_sum
    le_rfl (e.open_baseSet.mem_nhds hx) hcov (fun i ↦ mdifferentiableAt_localFrameCoeff b hx hσ i)
  rw [Finset.sum_add_distrib, add_comm] at h
  rw [frameCovariantDerivative]
  exact h

omit [Fintype ι] [FiniteDimensional 𝕜 F] in
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
  -- The `i`-th coefficient of the section is the constant `b.coord i v` on `e.baseSet`.
  have hcoeff (i : ι) : (fun y ↦ e.localFrameCoeff I b i y (e.symm y v)) =ᶠ[𝓝 x]
      fun _ ↦ b.coord i v :=
    Filter.eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦
      (e.localFrameCoeff_eq_coeff (I := I) (b := b) (s := fun y ↦ e.symm y v) hy).trans
        (by simp [e.apply_mk_symm hy])
  have hconst : HasMFDerivAt (M' := F) I 𝓘(𝕜, F) (fun _ : M ↦ v) x
      (0 : TangentSpace I x →L[𝕜] F) := hasMFDerivAt_const _ _
  rw [frameCovariantDerivative_eq_symmL_comp b hconst hcoeff hx, ContinuousLinearMap.comp_zero]

/-! ### Regularity of the flat covariant derivative of a local frame -/

omit [FiniteDimensional 𝕜 F] in
/-- The flat covariant derivative of a local frame is `C^n` on the base set of the trivialization
defining the frame, on a `C^m` manifold and a `C^k` bundle with `n + 1 ≤ m` and `n + 1 ≤ k`: it
sends a section which is `C^(n + 1)` there to a `C^n` section of `Hom(TM, V)` there. -/
theorem contMDiffCovariantDerivativeOn_frameCovariantDerivative
    [FiniteDimensional 𝕜 E] {m k n : ℕ∞ω} [IsManifold I m M]
    [ContMDiffVectorBundle k F V I] (hm : n + 1 ≤ m) (hk : n + 1 ≤ k) :
    -- The class needs `IsManifold I 1 M` merely to be stated; it follows from `hm`.
    have : IsManifold I 1 M := .of_le (le_add_self.trans hm)
    ContMDiffCovariantDerivativeOn F n (frameCovariantDerivative I b e) e.baseSet := by
  have : IsManifold I 1 M := .of_le (le_add_self.trans hm)
  have : FiniteDimensional 𝕜 F := Module.Finite.of_basis b
  refine ⟨fun {σ} hσ ↦ ?_⟩
  have : IsManifold I (n + 1) M := .of_le hm
  have : ContMDiffVectorBundle (n + 1) F V I := .of_le hk
  have : ContMDiffVectorBundle n F V I := .of_le (le_self_add.trans hk)
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  -- Test the hom-bundle section on the local frame of the tangent bundle at each point.
  refine contMDiffOn_of_locally_contMDiffOn fun x _ ↦ ?_
  let eT := trivializationAt E (TangentSpace I : M → Type _) x
  let bT := Module.Basis.ofVectorSpace 𝕜 E
  have hu : IsOpen (e.baseSet ∩ eT.baseSet) := e.open_baseSet.inter eT.open_baseSet
  refine ⟨eT.baseSet, eT.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' x, ?_⟩
  refine contMDiffOn_hom_of_localFrame (b := bT) (e := eT) (e' := e) (f := id)
    (u := e.baseSet ∩ eT.baseSet) contMDiffOn_id
    (fun y hy ↦ ⟨hy.2, hy.1⟩) fun j ↦ ?_
  simp only [id, frameCovariantDerivative_apply]
  refine ContMDiffOn.sum_section fun i _ ↦ ContMDiffOn.smul_section ?_ ?_
  · exact ((contMDiffOn_baseSet_localFrameCoeff b hσ i).mono inter_subset_left
      ).contMDiffOn_mvfderiv_apply hu
      ((eT.contMDiffOn_localFrame_baseSet n bT j).mono inter_subset_right) le_rfl
  · exact ((e.contMDiffOn_localFrame_baseSet n b i).mono inter_subset_left)

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
theorem covariantDerivative_localFrame_eq_sum_christoffelSymbol [Fintype ι] (i j : ι) :
    cov (e.localFrame b j) x (e.localFrame b i x) =
      ∑ k, christoffelSymbol I b e cov i j k x • e.localFrame b k x := by
  by_cases hx : x ∈ e.baseSet
  swap
  · simp [Trivialization.localFrame_apply_of_notMem _ _ hx]
  have hexp : extend E (cov (e.localFrame b j) x (e.localFrame b i x)) x =
      ∑ k, e.localFrameCoeff I b k x
          (extend E (cov (e.localFrame b j) x (e.localFrame b i x)) x) • e.localFrame b k x :=
    e.eq_sum_localFrameCoeff_smul hx
  rw [extend_apply_self] at hexp
  exact hexp

variable (I) in
private def christoffelMapOfSymbols [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x))
    (x : M) : E →L[𝕜] E →L[𝕜] E :=
  ∑ j, ∑ i, ∑ k, christoffelSymbol I b e cov i j k x •
    (b.coord j).toContinuousLinearMap.smulRight
      ((b.coord i).toContinuousLinearMap.smulRight (b k))

private theorem christoffelMapOfSymbols_apply_basis [Fintype ι] (i j : ι) :
    christoffelMapOfSymbols I b e cov x (b j) (b i) =
      ∑ k, christoffelSymbol I b e cov i j k x • b k := by
  classical
  simp [christoffelMapOfSymbols, Basis.coord_apply, Finsupp.single_apply]

/-- The Christoffel form transported through the tangent-bundle trivialization to a
model-space-valued continuous bilinear map. -/
def christoffelMap [Fintype ι] (hcov : IsCovariantDerivativeOn E cov e.baseSet) (x : M) :
    E →L[𝕜] E →L[𝕜] E :=
  ((e.continuousLinearMap (RingHom.id 𝕜)
      (e.continuousLinearMap (RingHom.id 𝕜) e))
    ⟨x, christoffelForm b hcov x⟩).2

/-- The model-space Christoffel map is the Christoffel form read in the trivialization: it acts
on the coordinates of a fibre vector and of a tangent direction, and returns the coordinates of
the value of the Christoffel form on them. -/
theorem christoffelMap_apply [Fintype ι] (hcov : IsCovariantDerivativeOn E cov e.baseSet)
    (v w : E) :
    christoffelMap b hcov x v w =
      e.continuousLinearMapAt 𝕜 x
        (christoffelForm b hcov x (e.symmL 𝕜 x v) (e.symmL 𝕜 x w)) := by
  by_cases hx : x ∈ e.baseSet
  swap
  · simp [christoffelMap, Bundle.Trivialization.continuousLinearMap_apply,
      e.symmL_apply_of_notMem (R := 𝕜) hx, Bundle.Trivialization.linearMapAt_apply, hx]
  have hxe : x ∈ (e.continuousLinearMap (RingHom.id 𝕜) e).baseSet := by simp [hx]
  simp only [christoffelMap, Bundle.Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.comp_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := 𝕜) (e.continuousLinearMap (RingHom.id 𝕜) e) hxe]
  simp only [Bundle.Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.comp_apply]

/-- A covariant derivative on the tangent bundle differentiates the vector field with constant
coordinates `v` in the trivialization `e`, in the direction with coordinates `u`, by the Christoffel
map: the result has coordinates `christoffelMap b hcov x v u`. -/
theorem covariantDerivative_symm_apply_symm [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) (v u : E) :
    cov (fun y ↦ e.symm y v) x (e.symm x u) = e.symm x (christoffelMap b hcov x v u) := by
  rw [covariantDerivative_symm_eq_christoffelForm b hcov hx, christoffelMap_apply b hcov]
  simp only [e.symmL_apply hx, Bundle.Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e hx]
  exact (e.symm_apply_apply_mk hx _).symm

/-- **The coordinate formula for a covariant derivative on the tangent bundle.**  The covariant
derivative of the vector field with coordinates `g` in the trivialization `e`, in the direction
with coordinates `u`, has coordinates `dg(u) + Γ(g, u)`, where `Γ` is the Christoffel map. -/
theorem covariantDerivative_symm_comp_apply_symm [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) {g : M → E}
    (hg : MDifferentiableAt I 𝓘(𝕜, E) g x) (u : E) :
    cov (fun y ↦ e.symm y (g y)) x (e.symm x u) =
      e.symm x (mvfderiv I g x (e.symm x u) + christoffelMap b hcov x (g x) u) := by
  have hread : ∀ᶠ y in 𝓝 x, (e ⟨y, e.symm y (g y)⟩).2 = g y :=
    Filter.eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ by rw [e.apply_mk_symm hy]
  have hσ : MDiffAt (T% (fun y ↦ e.symm y (g y))) x :=
    (e.mdifferentiableAt_section_iff I _ hx).2 (hg.congr_of_eventuallyEq hread)
  rw [covariantDerivative_eq_add_christoffelForm b hcov hx hσ, add_apply,
    ← e.symmL_apply (R := 𝕜) hx (_ + _), map_add, christoffelMap_apply b hcov,
    e.symmL_continuousLinearMapAt (R := 𝕜) hx, e.symmL_apply (R := 𝕜) hx,
    e.symmL_apply (R := 𝕜) hx, e.symmL_apply (R := 𝕜) hx]
  congr 1
  have hcoeff (i : ι) : (fun y ↦ e.localFrameCoeff I b i y (e.symm y (g y))) =ᶠ[𝓝 x]
      fun y ↦ b.coord i (g y) := by
    filter_upwards [hread, e.open_baseSet.mem_nhds hx] with y hy hyb
    rw [e.localFrameCoeff_eq_coeff (I := I) (b := b) (s := fun y ↦ e.symm y (g y)) hyb, hy,
      Basis.coord_apply]
  rw [frameCovariantDerivative_eq_symmL_comp b hg.hasMFDerivAt hcoeff hx]
  exact e.symmL_apply (R := 𝕜) hx _

/-- The Christoffel symbols of a `C^n` covariant derivative are `C^n` on the base set of the
trivialization defining the frame. -/
theorem contMDiffOn_christoffelSymbol {n : ℕ∞ω}
    [ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I]
    [ContMDiffCovariantDerivativeOn E n cov e.baseSet] (i j k : ι) :
    CMDiff[e.baseSet] n (christoffelSymbol I b e cov i j k) := by
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    .of_le (show n ≤ n + 1 from le_self_add)
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
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (i j : ι) :
    christoffelForm b hcov x (e.localFrame b j x) (e.localFrame b i x) =
      ∑ k, christoffelSymbol I b e cov i j k x • e.localFrame b k x := by
  classical
  by_cases hx : x ∈ e.baseSet
  swap
  · simp [Trivialization.localFrame_apply_of_notMem _ _ hx]
  rw [christoffelForm_apply b hcov hx]
  have hcollapse : ∑ l, e.localFrameCoeff I b l x (e.localFrame b j x) • cov (e.localFrame b l) x
      = cov (e.localFrame b j) x := by
    simp [localFrameCoeff_localFrame b hx]
  rw [hcollapse]
  exact covariantDerivative_localFrame_eq_sum_christoffelSymbol b i j

/-- The basis coefficients of the model-space Christoffel map are the scalar Christoffel
symbols. -/
@[simp]
theorem christoffelMap_apply_basis [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) (i j : ι) :
    christoffelMap b hcov x (b j) (b i) =
      ∑ k, christoffelSymbol I b e cov i j k x • b k := by
  classical
  rw [christoffelMap_apply b hcov, symmL_basis_eq_localFrame b hx j,
    symmL_basis_eq_localFrame b hx i,
    christoffelForm_localFrame_apply b hcov i j]
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

private theorem christoffelMap_eq_of_mem [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) :
    christoffelMap b hcov x = christoffelMapOfSymbols I b e cov x := by
  -- Both sides are continuous linear maps, so they are determined by their underlying linear
  -- maps (`ContinuousLinearMap.coe_injective`), hence by their values on the basis `b`; the
  -- coercion is transparent on applications by `ContinuousLinearMap.coe_coe`.
  refine ContinuousLinearMap.coe_injective (b.ext fun j ↦ ?_)
  simp only [ContinuousLinearMap.coe_coe]
  refine ContinuousLinearMap.coe_injective (b.ext fun i ↦ ?_)
  simp only [ContinuousLinearMap.coe_coe]
  rw [christoffelMap_apply_basis b hcov hx i j, christoffelMapOfSymbols_apply_basis b i j]

/-- The model-space Christoffel map of a `C^n` covariant derivative is `C^n` on the base set of
the trivialization defining its coordinates. -/
theorem contMDiffOn_christoffelMap [Fintype ι] {n : ℕ∞ω}
    (hcov : IsCovariantDerivativeOn E cov e.baseSet)
    [ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I]
    [ContMDiffCovariantDerivativeOn E n cov e.baseSet] :
    CMDiff[e.baseSet] n (christoffelMap b hcov) := by
  classical
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    .of_le (show n ≤ n + 1 from le_self_add)
  have hsymbols : CMDiff[e.baseSet] n (christoffelMapOfSymbols I b e cov) := by
    unfold christoffelMapOfSymbols
    apply contMDiffOn_finsetSum
    intro j _
    apply contMDiffOn_finsetSum
    intro i _
    apply contMDiffOn_finsetSum
    intro k _
    exact (contMDiffOn_christoffelSymbol b i j k).smul contMDiffOn_const
  exact hsymbols.congr fun y hy ↦ christoffelMap_eq_of_mem b hcov hy

omit [FiniteDimensional 𝕜 E] in
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
    covariantDerivative_localFrame_eq_sum_christoffelSymbol b i j
  rw [covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov hx hσ]
  simp only [add_apply, frameCovariantDerivative_apply, sum_apply, smul_apply, hΓ,
    Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_comm]

end TangentBundle

end TauCeti.Manifold
