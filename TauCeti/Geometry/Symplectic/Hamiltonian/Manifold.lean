/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Hamiltonian vector fields on symplectic manifolds

Let `σ` be a smooth two-form on a manifold `M`. A vector field `X` is a **Hamiltonian vector field**
of a function `f : M → ℝ` when `ι_X σ = df`, that is `σ(X x, v) = df_x(v)` for every tangent
vector `v` at every point `x` (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField`). This is the
sign convention of the vector-space API `TauCeti.SymplecticForm.hamiltonianVectorField`.

The Hamiltonian vector field of `f` is `X_f = (σ♭)⁻¹ df`, the inverse flat map
`TauCeti.SmoothTwoForm.flat` applied to the differential of `f`
(`TauCeti.SmoothTwoForm.hamiltonianVectorField`). On a finite-dimensional manifold every flat map
of a nondegenerate form is invertible, so `X_f` is then the unique Hamiltonian vector field of `f`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isHamiltonianVectorField_iff_eq`). Smoothness of the
inverse flat maps makes the Hamiltonian vector field of a `C^(n+1)` function a `C^n` vector field
(`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianVectorField`), which is the regularity
needed to integrate it to a Hamiltonian flow.

Since `σ` is alternating, `df(X) = σ(X, X) = 0` for a Hamiltonian vector field `X` of `f`: the
Hamiltonian is constant along the integral curves of `X`, which is conservation of energy
(`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.apply_eq_of_isMIntegralCurveOn`). For a constant
symplectic form on a vector space, the construction recovers the Hamiltonian vector field of the
linear theory (`TauCeti.SymplecticForm.hamiltonianVectorField_constSmooth`).

The **Poisson bracket** of two functions is `{f, g} = σ(X_f, X_g)`
(`TauCeti.SmoothTwoForm.poissonBracket`), which is `df(X_g)` for a nondegenerate form on a
finite-dimensional manifold. It is antisymmetric and agrees with the Poisson bracket of the linear
theory for a constant symplectic form (`TauCeti.SymplecticForm.poissonBracket_constSmooth`).

## Main declarations

* `TauCeti.SmoothTwoForm.IsHamiltonianVectorField`: the equation `ι_X σ = df`, also in the
  language of forms (`TauCeti.SmoothTwoForm.isHamiltonianVectorField_iff_interior_eq`).
* `TauCeti.SmoothTwoForm.hamiltonianVectorField`: the Hamiltonian vector field `(σ♭)⁻¹ df`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isHamiltonianVectorField_iff_eq`: existence and
  uniqueness of the Hamiltonian vector field.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianVectorField`: a `C^(n+1)`
  Hamiltonian has a `C^n` Hamiltonian vector field.
* `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.apply_eq_of_isMIntegralCurveOn`: conservation
  of energy along integral curves on open preconnected sets of times, with the global case
  `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.apply_eq_of_isMIntegralCurve`.
* `TauCeti.SymplecticForm.hamiltonianVectorField_constSmooth`: comparison with the vector-space
  construction.
* `TauCeti.SmoothTwoForm.poissonBracket`: the Poisson bracket `{f, g} = σ(X_f, X_g)`, with
  `TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_eq_mvfderiv`: `{f, g} = df(X_g)`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1 (Hamiltonian vector fields on symplectic manifolds).
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 1.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {f g : M → ℝ} {X : (x : M) → TangentSpace I x}

/-! ### Hamiltonian vector fields -/

/-- A vector field `X` is a **Hamiltonian vector field** of `f` for the two-form `σ` when
`ι_X σ = df`: `σ(X x, v) = df_x(v)` for every tangent vector `v` at every point `x`. -/
def IsHamiltonianVectorField (σ : SmoothTwoForm I M) (f : M → ℝ)
    (X : (x : M) → TangentSpace I x) : Prop :=
  ∀ x v, SmoothForm.eval₂ σ x (X x) v = mvfderiv I f x v

/-- The defining characterization of a Hamiltonian vector field. -/
theorem isHamiltonianVectorField_iff :
    σ.IsHamiltonianVectorField f X ↔ ∀ x v, SmoothForm.eval₂ σ x (X x) v = mvfderiv I f x v :=
  Iff.rfl

/-- A Hamiltonian vector field is one whose flat is the differential of the Hamiltonian. -/
theorem isHamiltonianVectorField_iff_flat :
    σ.IsHamiltonianVectorField f X ↔ ∀ x, σ.flat x (X x) = mvfderiv I f x := by
  simp only [isHamiltonianVectorField_iff, ContinuousLinearMap.ext_iff, flat_apply]

/-- A Hamiltonian vector field in the language of forms: the interior product `ι_X σ` is the
exterior derivative of the `0`-form of the Hamiltonian. -/
theorem isHamiltonianVectorField_iff_interior_eq :
    σ.IsHamiltonianVectorField f X ↔
      σ.1.interior X = mextDeriv (RoughForm.ofFunction I f) := by
  -- Both sides are one-forms of one vector, the images of `σ♭ X` and `df` respectively.
  simp only [isHamiltonianVectorField_iff_flat, funext_iff, interior_apply_eq_ofSubsingleton_flat,
    mextDeriv_ofFunction, EmbeddingLike.apply_eq_iff_eq]

namespace IsHamiltonianVectorField

/-- **A Hamiltonian is stationary along its Hamiltonian vector field**: `df(X) = σ(X, X) = 0`. -/
theorem mvfderiv_apply_self (hX : σ.IsHamiltonianVectorField f X) (x : M) :
    mvfderiv I f x (X x) = 0 := by
  rw [← hX x, ← SmoothForm.bilinFormAt_apply]
  exact SmoothForm.isAlt_bilinFormAt σ x (X x)

/-- **Conservation of energy.** A Hamiltonian, differentiable along an integral curve of its
Hamiltonian vector field on an open interval of times (or any open preconnected set of times), is
constant along that curve. -/
theorem apply_eq_of_isMIntegralCurveOn (hX : σ.IsHamiltonianVectorField f X) {γ : ℝ → M}
    {s : Set ℝ} (hs : IsOpen s) (hs' : IsPreconnected s) (hγ : IsMIntegralCurveOn γ X s)
    (hf : ∀ t ∈ s, MDifferentiableAt I 𝓘(ℝ) f (γ t)) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    f (γ t) = f (γ t₀) := by
  have hd (u : ℝ) (hu : u ∈ s) : HasDerivAt (f ∘ γ) 0 u := by
    simpa only [hX.mvfderiv_apply_self] using
      Manifold.hasDerivAt_comp_curve (hf u hu) ((hγ u hu).hasMFDerivAt (hs.mem_nhds hu))
  exact hs.is_const_of_deriv_eq_zero hs'
    (fun u hu ↦ (hd u hu).differentiableAt.differentiableWithinAt) (fun u hu ↦ (hd u hu).deriv)
    ht ht₀

/-- **Conservation of energy** along a global integral curve: a Hamiltonian, differentiable along
an integral curve of its Hamiltonian vector field, is constant along that curve. -/
theorem apply_eq_of_isMIntegralCurve (hX : σ.IsHamiltonianVectorField f X) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ X) (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) f (γ t)) (s t : ℝ) :
    f (γ t) = f (γ s) :=
  hX.apply_eq_of_isMIntegralCurveOn isOpen_univ isPreconnected_univ (hγ.isMIntegralCurveOn _)
    (fun t _ ↦ hf t) (Set.mem_univ s) (Set.mem_univ t)

end IsHamiltonianVectorField

/-- The **Hamiltonian vector field** `X_f = (σ♭)⁻¹ df` of a function `f`. It satisfies
`ι_{X_f} σ = df` when `σ` is nondegenerate and `M` is finite-dimensional
(`TauCeti.SmoothTwoForm.IsNondegenerate.isHamiltonianVectorField_hamiltonianVectorField`); the
inverse is `ContinuousLinearMap.inverse`, so the field vanishes at points where the flat map is
not invertible. -/
def hamiltonianVectorField (σ : SmoothTwoForm I M) (f : M → ℝ) (x : M) : TangentSpace I x :=
  (σ.flat x).inverse (mvfderiv I f x)

/-- The Hamiltonian vector field unfolds as the inverse flat map applied to `df`. -/
theorem hamiltonianVectorField_def (σ : SmoothTwoForm I M) (f : M → ℝ) (x : M) :
    σ.hamiltonianVectorField f x = (σ.flat x).inverse (mvfderiv I f x) :=
  (rfl)

/-- The Hamiltonian vector field of a constant function vanishes. -/
@[simp]
theorem hamiltonianVectorField_const (σ : SmoothTwoForm I M) (c : ℝ) :
    σ.hamiltonianVectorField (fun _ ↦ c) = 0 := by
  funext x
  simp [hamiltonianVectorField_def, mvfderiv_const]

/-- The Hamiltonian vector field is additive on differentiable functions. -/
theorem hamiltonianVectorField_add {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    σ.hamiltonianVectorField (f + g) x =
      σ.hamiltonianVectorField f x + σ.hamiltonianVectorField g x := by
  simp [hamiltonianVectorField_def, mvfderiv_add hf hg]

/-- The Hamiltonian vector field of `-f` is the opposite of that of `f`. -/
@[simp]
theorem hamiltonianVectorField_neg (x : M) :
    σ.hamiltonianVectorField (-f) x = -σ.hamiltonianVectorField f x := by
  simp [hamiltonianVectorField_def, mvfderiv_neg]

/-- The Hamiltonian vector field commutes with multiplication by a real constant. -/
theorem hamiltonianVectorField_const_smul (c : ℝ) {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    σ.hamiltonianVectorField (c • f) x = c • σ.hamiltonianVectorField f x := by
  have hd := mvfderiv_smul (a := fun _ : M ↦ c) mdifferentiableAt_const hf
  simp only [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] at hd
  -- `c • f` is, pointwise, the product of `f` with the constant function `c`.
  have hcf : c • f = (fun _ : M ↦ c) • f := rfl
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, hcf, hd, map_smul]

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
include h

/-- The flat of the Hamiltonian vector field is the differential of the Hamiltonian. -/
@[simp]
theorem flat_hamiltonianVectorField (f : M → ℝ) (x : M) :
    σ.flat x (σ.hamiltonianVectorField f x) = mvfderiv I f x :=
  (h.isInvertible_flat x).self_apply_inverse _

/-- **Contraction with the Hamiltonian vector field** is the differential of the Hamiltonian,
`σ(X_f, v) = df(v)`. -/
theorem eval₂_hamiltonianVectorField (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    SmoothForm.eval₂ σ x (σ.hamiltonianVectorField f x) v = mvfderiv I f x v := by
  rw [← flat_apply, h.flat_hamiltonianVectorField]

/-- The simp normal form of `eval₂_hamiltonianVectorField`, with `eval₂` unfolded:
`σ_x(X_f, v) = df_x(v)`. -/
@[simp]
theorem apply_hamiltonianVectorField (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    σ.1 x ![σ.hamiltonianVectorField f x, v] = mvfderiv I f x v := by
  rw [← SmoothForm.eval₂_apply, h.eval₂_hamiltonianVectorField]

/-- The Hamiltonian vector field of `f` is a Hamiltonian vector field of `f`. -/
theorem isHamiltonianVectorField_hamiltonianVectorField (f : M → ℝ) :
    σ.IsHamiltonianVectorField f (σ.hamiltonianVectorField f) :=
  h.eval₂_hamiltonianVectorField f

/-- **Existence and uniqueness of Hamiltonian vector fields.** For a nondegenerate two-form on a
finite-dimensional manifold, `X_f` is the only Hamiltonian vector field of `f`. -/
theorem isHamiltonianVectorField_iff_eq :
    σ.IsHamiltonianVectorField f X ↔ X = σ.hamiltonianVectorField f := by
  refine ⟨fun hX ↦ funext fun x ↦ (h.isInvertible_flat x).injective ?_, fun hX ↦ hX ▸
    h.isHamiltonianVectorField_hamiltonianVectorField f⟩
  rw [h.flat_hamiltonianVectorField, isHamiltonianVectorField_iff_flat.1 hX x]

/-- **Regularity of Hamiltonian vector fields.** For a nondegenerate two-form on a
finite-dimensional manifold, the Hamiltonian vector field of a `C^(n+1)` function is a `C^n`
vector field, for `n ≤ ∞`. -/
theorem contMDiff_hamiltonianVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (T% (σ.hamiltonianVectorField f)) :=
  ((σ.contMDiff_flat.clm_bundle_inverse h.isInvertible_flat).of_le hn).clm_bundle_apply
    hf.contMDiff_totalSpaceMk_mvfderiv

end IsNondegenerate

/-! ### The Poisson bracket -/

/-- The **Poisson bracket** `{f, g}(x) = σ(X_f x, X_g x)` of two functions. For a nondegenerate
form on a finite-dimensional manifold it is `{f, g} = df(X_g)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_eq_mvfderiv`). -/
def poissonBracket (σ : SmoothTwoForm I M) (f g : M → ℝ) (x : M) : ℝ :=
  SmoothForm.eval₂ σ x (σ.hamiltonianVectorField f x) (σ.hamiltonianVectorField g x)

/-- The Poisson bracket unfolds as `σ` evaluated on the two Hamiltonian vector fields. -/
theorem poissonBracket_def (σ : SmoothTwoForm I M) (f g : M → ℝ) (x : M) :
    σ.poissonBracket f g x =
      SmoothForm.eval₂ σ x (σ.hamiltonianVectorField f x) (σ.hamiltonianVectorField g x) :=
  (rfl)

/-- The Poisson bracket is antisymmetric. -/
theorem neg_poissonBracket (σ : SmoothTwoForm I M) (f g : M → ℝ) (x : M) :
    -σ.poissonBracket g f x = σ.poissonBracket f g x := by
  rw [poissonBracket_def, poissonBracket_def, SmoothForm.eval₂_swap σ x, neg_neg]

@[simp]
theorem poissonBracket_self (σ : SmoothTwoForm I M) (f : M → ℝ) (x : M) :
    σ.poissonBracket f f x = 0 :=
  SmoothForm.eval₂_self σ x _

@[simp]
theorem poissonBracket_const_left (σ : SmoothTwoForm I M) (c : ℝ) (g : M → ℝ) (x : M) :
    σ.poissonBracket (fun _ ↦ c) g x = 0 := by
  rw [poissonBracket_def, hamiltonianVectorField_const, ← SmoothForm.bilinFormAt_apply]
  simp

@[simp]
theorem poissonBracket_const_right (σ : SmoothTwoForm I M) (f : M → ℝ) (c : ℝ) (x : M) :
    σ.poissonBracket f (fun _ ↦ c) x = 0 := by
  rw [poissonBracket_def, hamiltonianVectorField_const, ← SmoothForm.bilinFormAt_apply,
    Pi.zero_apply, map_zero]

/-- The Poisson bracket is additive in its first argument on differentiable functions. -/
theorem poissonBracket_add_left {k : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    σ.poissonBracket (f + g) k x = σ.poissonBracket f k x + σ.poissonBracket g k x := by
  simp only [poissonBracket_def, hamiltonianVectorField_add hf hg,
    ← SmoothForm.bilinFormAt_apply, map_add, LinearMap.add_apply]

/-- The Poisson bracket is additive in its second argument on differentiable functions. -/
theorem poissonBracket_add_right {k : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    σ.poissonBracket k (f + g) x = σ.poissonBracket k f x + σ.poissonBracket k g x := by
  simp only [poissonBracket_def, hamiltonianVectorField_add hf hg,
    ← SmoothForm.bilinFormAt_apply, map_add]

/-- Negating the first argument negates the Poisson bracket. -/
@[simp]
theorem poissonBracket_neg_left (x : M) :
    σ.poissonBracket (-f) g x = -σ.poissonBracket f g x := by
  simp only [poissonBracket_def, hamiltonianVectorField_neg, ← SmoothForm.bilinFormAt_apply,
    map_neg, LinearMap.neg_apply]

/-- Negating the second argument negates the Poisson bracket. -/
@[simp]
theorem poissonBracket_neg_right (x : M) :
    σ.poissonBracket f (-g) x = -σ.poissonBracket f g x := by
  simp only [poissonBracket_def, hamiltonianVectorField_neg, ← SmoothForm.bilinFormAt_apply,
    map_neg]

/-- Multiplication of the first argument by a real constant scales the Poisson bracket. -/
theorem poissonBracket_const_smul_left (c : ℝ) {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    σ.poissonBracket (c • f) g x = c • σ.poissonBracket f g x := by
  simp only [poissonBracket_def, hamiltonianVectorField_const_smul c hf,
    ← SmoothForm.bilinFormAt_apply, map_smul, LinearMap.smul_apply]

/-- Multiplication of the second argument by a real constant scales the Poisson bracket. -/
theorem poissonBracket_const_smul_right (c : ℝ) {x : M}
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    σ.poissonBracket f (c • g) x = c • σ.poissonBracket f g x := by
  simp only [poissonBracket_def, hamiltonianVectorField_const_smul c hg,
    ← SmoothForm.bilinFormAt_apply, map_smul]

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
include h

/-- The Poisson bracket `{f, g}` is the derivative of `f` along the Hamiltonian vector field of
`g`. -/
theorem poissonBracket_eq_mvfderiv (f g : M → ℝ) (x : M) :
    σ.poissonBracket f g x = mvfderiv I f x (σ.hamiltonianVectorField g x) :=
  h.eval₂_hamiltonianVectorField f x _

/-- The Poisson bracket `{f, g}` is minus the derivative of `g` along the Hamiltonian vector
field of `f`. -/
theorem poissonBracket_eq_neg_mvfderiv (f g : M → ℝ) (x : M) :
    σ.poissonBracket f g x = -mvfderiv I g x (σ.hamiltonianVectorField f x) := by
  rw [← neg_poissonBracket, h.poissonBracket_eq_mvfderiv]

end IsNondegenerate

end SmoothTwoForm

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- For a constant symplectic form on a vector space, the Hamiltonian vector field of the
manifold theory is that of the linear theory. -/
theorem hamiltonianVectorField_constSmooth (omegaForm : SymplecticForm V) (f : V → ℝ) :
    omegaForm.constSmooth.hamiltonianVectorField f = omegaForm.hamiltonianVectorField f := by
  refine ((isNondegenerate_constSmooth omegaForm).isHamiltonianVectorField_iff_eq.1
    fun x v ↦ ?_).symm
  -- The tangent spaces of the model space are `V` itself, through the identity map
  -- `NormedSpace.fromTangentSpace`.
  refine (fromTangentSpace_constSmooth_apply omegaForm x _ v).trans ?_
  rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
  exact omegaForm.apply_hamiltonianVectorField f x _

/-- For a constant symplectic form on a vector space, the Poisson bracket of the manifold theory
is that of the linear theory. -/
theorem poissonBracket_constSmooth (omegaForm : SymplecticForm V) (f g : V → ℝ) :
    omegaForm.constSmooth.poissonBracket f g = omegaForm.poissonBracket f g := by
  funext x
  rw [SmoothTwoForm.poissonBracket_def, hamiltonianVectorField_constSmooth,
    hamiltonianVectorField_constSmooth, poissonBracket_def]
  -- The tangent spaces of the model space are `V` itself, through the identity map
  -- `NormedSpace.fromTangentSpace`.
  exact fromTangentSpace_constSmooth_apply omegaForm x _ _

end SymplecticForm

end TauCeti
