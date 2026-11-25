/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Regularity of covariant derivatives along vector fields

This file records the regularity of evaluating a smooth covariant derivative on a smooth vector
field.  It turns the hom-bundle-valued regularity supplied by
`CovariantDerivative.ContMDiffCovariantDerivative` into regularity of the resulting section.
That class asks for regularity of `∇σ` only for sections `σ` which are regular everywhere, and
`ContMDiffCovariantDerivativeOn` on a set `s` only for sections regular on all of `s`; on a
smooth real manifold, cutting off by bump functions shows that this gives the same regularity of
`∇σ` on every open subset where `σ` is regular, which is the form used to read a connection in a
local frame.

## Main results

* `CovariantDerivative.contMDiff_covariantDerivative`: the covariant derivative `∇σ` of a
  `C^(n + 1)` section is a `C^n` section of `Hom(TM, V)`.
* `ContMDiffCovariantDerivativeOn.contMDiff_univ`: the same for any operator which is `C^n` on the
  whole manifold in the sense of `ContMDiffCovariantDerivativeOn`.
* `CovariantDerivative.contMDiffAt_apply`: the pointwise version of the next result.
* `CovariantDerivative.contMDiff_apply`: applying a `C^n` covariant derivative
  to a `C^(n + 1)` section along a `C^n` vector field produces a `C^n` section.
* `CovariantDerivative.alongVectorField`: hence a smooth covariant derivative along a smooth vector
  field `X` is a linear operator `∇_X` on smooth sections.
* `CovariantDerivative.alongVectorField_smul`: the Leibniz rule for `∇_X`.
* `ContMDiffCovariantDerivativeOn.mono_of_isOpen_of_eventuallyEq`: on a smooth real manifold, an
  operator from sections to one-forms which is `C^n` on a set and local at the points of an open
  subset is `C^n` on that subset.
* `ContMDiffCovariantDerivativeOn.mono_of_isOpen`: on a smooth real manifold, a covariant
  derivative which is `C^n` on a set is `C^n` on each open subset where it is a covariant
  derivative.
* `CovariantDerivative.contMDiffCovariantDerivativeOn_of_isOpen`: a `C^n` covariant derivative
  is `C^n` on every open set.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω}

/-- The covariant derivative `∇σ` of a `C^(n + 1)` section for a `C^n` covariant derivative is a
`C^n` section of the bundle `Hom(TM, V)` of `V`-valued one-forms. -/
theorem contMDiff_covariantDerivative
    (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov n]
    {σ : Π x : M, V x} (hσ : CMDiff (n + 1) (T% σ)) :
    ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] F)) n
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] F) (E := fun y ↦ TangentSpace I y →L[𝕜] V y) x (cov σ x)) :=
  contMDiffOn_univ.mp (ContMDiffCovariantDerivative.contMDiff.contMDiff hσ.contMDiffOn)

/-- An operator which is `C^n` over the whole manifold, in the sense of Mathlib's
`ContMDiffCovariantDerivativeOn`, sends a `C^(n + 1)` section to a `C^n` section of the bundle
`Hom(TM, V)` of `V`-valued one-forms. The operator need not be a covariant derivative. -/
theorem _root_.ContMDiffCovariantDerivativeOn.contMDiff_univ
    {D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[𝕜] V x}
    (hD : ContMDiffCovariantDerivativeOn F n D Set.univ) {σ : Π x : M, V x}
    (hσ : CMDiff (n + 1) (T% σ)) :
    ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] F)) n
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] F) (E := fun y ↦ TangentSpace I y →L[𝕜] V y) x (D σ x)) :=
  contMDiffOn_univ.mp (hD.contMDiff hσ.contMDiffOn)

/-- Applying a `C^n` covariant derivative to a `C^(n + 1)` section along a vector field which is
`C^n` at `x` produces a section which is `C^n` at `x`. -/
theorem contMDiffAt_apply
    (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov n]
    {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M}
    (hX : CMDiffAt n (T% X) x) (hσ : CMDiff (n + 1) (T% σ)) :
    CMDiffAt n (T% (fun x ↦ cov σ x (X x))) x :=
  (cov.contMDiff_covariantDerivative hσ x).clm_bundle_apply hX

/-- Applying a `C^n` covariant derivative to a `C^(n + 1)` section along a `C^n` vector field
produces a `C^n` section. -/
theorem contMDiff_apply
    (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov n]
    {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    (hX : CMDiff n (T% X)) (hσ : CMDiff (n + 1) (T% σ)) :
    CMDiff n (T% (fun x ↦ cov σ x (X x))) :=
  fun x ↦ cov.contMDiffAt_apply (hX x) hσ

/-- The covariant derivative `∇_X` along a smooth vector field `X`, as a linear operator on the
smooth sections: it sends `σ` to `x ↦ ∇_{X x} σ`. -/
def alongVectorField (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; F, V⟯ →ₗ[𝕜] Cₛ^∞⟮I; F, V⟯ where
  toFun σ := ⟨fun x ↦ cov σ x (X x), cov.contMDiff_apply X.contMDiff (by simpa using σ.contMDiff)⟩
  map_add' σ τ := ContMDiffSection.ext fun x ↦ by
    simp [cov.isCovariantDerivativeOnUniv.add σ.mdifferentiableAt
      τ.mdifferentiableAt]
  map_smul' c σ := ContMDiffSection.ext fun x ↦ by
    simp [cov.isCovariantDerivativeOnUniv.smul_const c σ.mdifferentiableAt]

@[simp]
theorem alongVectorField_apply (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Cₛ^∞⟮I; F, V⟯) (x : M) : cov.alongVectorField X σ x = cov σ x (X x) :=
  (rfl)

/-- **The Leibniz rule for `∇_X`**: `∇_X (a σ) = a ∇_X σ + X(a) σ` for a smooth function `a`. -/
theorem alongVectorField_smul (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a : C^∞⟮I, M; 𝕜⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.alongVectorField X (a • σ) x =
      a x • cov.alongVectorField X σ x + mvfderiv I a x (X x) • σ x := by
  have hfun : ⇑(a • σ) = (⇑a : M → 𝕜) • ⇑σ := funext fun y ↦ ContMDiffSection.smul_apply a σ y
  rw [alongVectorField_apply, hfun, cov.isCovariantDerivativeOnUniv.leibniz σ.mdifferentiableAt
    (a.contMDiff.mdifferentiableAt (by simp))]
  simp

/-- Adding a `C^n` endomorphism-valued one-form preserves the regularity of a connection.
The model fibre need not have finite dimension. -/
theorem ContMDiffCovariantDerivative.addOneForm
    {cov : CovariantDerivative I F V} (hcov : ContMDiffCovariantDerivative cov n)
    {A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x}
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] E →L[𝕜] F)) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] E →L[𝕜] F)
        (E := fun y ↦ V y →L[𝕜] TangentSpace I y →L[𝕜] V y) x (A x))) :
    ContMDiffCovariantDerivative (cov.addOneForm A) n where
  contMDiff.contMDiff {σ} hσ := by
    have h := hA.contMDiffOn.clm_bundle_apply (hσ.of_le le_self_add)
    exact hcov.contMDiff.contMDiff hσ |>.add_section h

section Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **Locality of regularity.**  On a smooth real manifold, let `cov` send sections of `V` to
`V`-valued one-forms, and suppose that at each point of an open set `u` its value on a section
differentiable there depends only on the germ of the section. If `cov` is `C^n` on a set `s ⊇ u`,
then it is `C^n` on `u`: it sends sections which are `C^(n + 1)` on `u` to one-forms which are
`C^n` on `u`. -/
theorem _root_.ContMDiffCovariantDerivativeOn.mono_of_isOpen_of_eventuallyEq {n : ℕ∞ω}
    [ENat.LEInfty n] {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}
    {s u : Set M} (h : ContMDiffCovariantDerivativeOn F n cov s)
    (hloc : ∀ ⦃σ σ' : Π x : M, V x⦄ ⦃x : M⦄, x ∈ u → MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      (∀ᶠ y in 𝓝 x, σ y = σ' y) → cov σ x = cov σ' x)
    (hu : IsOpen u) (hus : u ⊆ s) :
    ContMDiffCovariantDerivativeOn F n cov u where
  contMDiff {σ} hσ y hy := by
    lift n to ℕ∞ using ENat.LEInfty.ne_top n
    -- Cut `σ` off by a bump function equal to one near `y` and supported in `u`.
    obtain ⟨ρ, -, hρ⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) y).mem_iff.mp (hu.mem_nhds hy)
    have hρσ : CMDiff (n + 1) (T% ((ρ : M → ℝ) • σ)) :=
      (ρ.contMDiff.of_le (mod_cast le_top)).contMDiffOn.smul_section_of_tsupport hu hρ hσ
    have hρσ' := (h.contMDiff hρσ.contMDiffOn y (hus hy)).contMDiffAt
      (Filter.mem_of_superset (hu.mem_nhds hy) hus)
    -- Near `y` the cut-off section agrees with `σ`, so `cov` agrees on them there.
    have heq : ∀ᶠ z in 𝓝 y, cov ((ρ : M → ℝ) • σ) z = cov σ z := by
      filter_upwards [hu.mem_nhds hy, ρ.eventuallyEq_one.eventually_nhds] with z hz hρz
      refine hloc hz ((hρσ z).mdifferentiableAt (by simp))
        (((hσ z hz).contMDiffAt (hu.mem_nhds hz)).mdifferentiableAt (by simp)) ?_
      filter_upwards [hρz] with w hw
      simp [hw]
    exact (hρσ'.congr_of_eventuallyEq (heq.mono fun z hz ↦ by simp only [hz])).contMDiffWithinAt

/-- **Locality of the regularity of a connection.**  On a smooth real manifold, if `cov` is `C^n`
on a set `s` and is a covariant derivative on an open subset `u ⊆ s`, then `cov` is also `C^n`
on `u`: it sends sections which are `C^(n + 1)` on `u` to covariant derivatives which are `C^n`
on `u`. -/
theorem _root_.ContMDiffCovariantDerivativeOn.mono_of_isOpen {n : ℕ∞ω} [ENat.LEInfty n]
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)} {s u : Set M}
    (h : ContMDiffCovariantDerivativeOn F n cov s) (hcov : IsCovariantDerivativeOn F cov u)
    (hu : IsOpen u) (hus : u ⊆ s) :
    ContMDiffCovariantDerivativeOn F n cov u :=
  h.mono_of_isOpen_of_eventuallyEq
    (fun _ _ _ hx hσ hσ' hσσ' ↦ hcov.congr_of_eventuallyEq hσ hσ' (hu.mem_nhds hx) hσσ') hu hus

/-- **Locality of the regularity of a connection.**  A `C^n` covariant derivative on a smooth
real manifold is `C^n` on every open set `u`: it sends sections which are `C^(n + 1)` on `u` to
covariant derivatives which are `C^n` on `u`. -/
theorem contMDiffCovariantDerivativeOn_of_isOpen {n : ℕ∞ω} [ENat.LEInfty n]
    (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov n] {u : Set M}
    (hu : IsOpen u) : ContMDiffCovariantDerivativeOn F n cov.toFun u :=
  ContMDiffCovariantDerivative.contMDiff.mono_of_isOpen cov.isCovariantDerivativeOn hu
    (Set.subset_univ u)

end Real

end CovariantDerivative
