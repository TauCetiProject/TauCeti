/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Variation
public import TauCeti.Geometry.Manifold.VectorField.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Symplectic.Manifold.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Integral
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Symplectic.Manifold.Rescale

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
needed to integrate it to a Hamiltonian flow. Rescaling the form by `c ≠ 0` rescales the
Hamiltonian vector field by `c⁻¹`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_smul`), and post-composing the
Hamiltonian with a real function `φ` rescales it pointwise by `φ'`, `X_{φ ∘ f} = φ'(f) X_f`
(`TauCeti.SmoothTwoForm.hamiltonianVectorField_comp`). The value of `X_f` at `x` only depends on the
germ of `f` at `x` (`Filter.EventuallyEq.hamiltonianVectorField_eq`).

Since `σ` is alternating, `df(X) = σ(X, X) = 0` for a Hamiltonian vector field `X` of `f`: the
Hamiltonian is constant along the integral curves of `X`, which is conservation of energy
(`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.apply_eq_of_isMIntegralCurveOn`). The pairing
`σ(a - X_f, b) = -σ(b, a) - df(b)` is the integrand of the first variation of the action
functionals of Hamiltonian dynamics
(`TauCeti.SmoothTwoForm.IsNondegenerate.apply_sub_hamiltonianVectorField`). Along the chart
variations `TauCeti.Manifold.sinChartVariation` of a curve `γ`, it is the profile times the pairing
of `γ' - X_f` with a tangent vector of fixed chart coordinates
(`TauCeti.SmoothTwoForm.apply_mfderiv_sinChartVariation`). A nonzero value
`a - X_f` of the obstruction pairs positively with a tangent vector of short chart coordinates,
which supplies the test direction of the first variation arguments showing that the critical
points of these functionals solve Hamilton's equation
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_apply_and_eventually_add_smul_mem_target`).
The orbits of
`G + f ∘ F`, where `G` is supported in `{F < s}` and `f` is constant on `(-∞, s]`, either stay in
`{F < s}` as orbits of `G` or lie in a level of `F` as orbits of `f'(c) X_F`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_or_exists_of_isMIntegralCurve_add_comp`).
For a constant symplectic form on a vector space, the construction recovers the Hamiltonian vector
field of the linear theory (`TauCeti.SymplecticForm.hamiltonianVectorField_constSmooth`).

The **Poisson bracket** of two functions is `{f, g} = σ(X_f, X_g)`
(`TauCeti.SmoothTwoForm.poissonBracket`), which is `df(X_g)` for a nondegenerate form on a
finite-dimensional manifold. It is antisymmetric and agrees with the Poisson bracket of the linear
theory for a constant symplectic form (`TauCeti.SymplecticForm.poissonBracket_constSmooth`).

Hamiltonian vector fields pull back: if a smooth map `φ` carries a vector field `X` to a
Hamiltonian vector field of `g`, then `X` is a Hamiltonian vector field of `g ∘ φ` for the pulled
back form (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mpullback`). On a product `M × N` with
the product form, the product of Hamiltonian vector fields of `f` and `g` is a Hamiltonian vector
field of `(x, y) ↦ f x + g y` (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.prod`).

Both constructions are natural. Pointwise, if a linear map `D` from `T_x M` to `T_y M₂`
satisfies `σ₂_y(D u, D v) = σ_x(u, v)` and `dg_y ∘ D = df_x` for nondegenerate `σ` and `σ₂`, and
`X_g(y)` lies in the range of `D`, then `D` carries `X_f(x)` to `X_g(y)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.map_hamiltonianVectorField_of_eval₂`). This holds when
`D` is surjective, which is automatic when `M₂ = M` and `σ₂ = σ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.surjective_of_eval₂_map`). Hence a smooth map `φ` pulling
a nondegenerate form `σ₂` back to `σ`
carries the Hamiltonian vector field of `g ∘ φ` to that of `g`, wherever its differential is
surjective (`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp`), and so
`{g ∘ φ, k ∘ φ} = {g, k} ∘ φ` there (`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_comp`).
Surjectivity is only used to lift the Hamiltonian vector of `g`: wherever `X_g(φ x)` lies in the
range of `dφ_x`, the differential carries `X_{g ∘ φ}(x)` to it
(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp_of_mem_range`), and
`{f ∘ φ, g ∘ φ}(x) = {f, g}(φ x)` for every differentiable `f`
(`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_comp_of_mem_range`). For the inclusion of a
symplectic submanifold, this computes brackets with the restriction of an ambient function whose
Hamiltonian vector field is tangent to the submanifold.
Along a curve where `X_g` is tangent to `φ`, `φ` therefore maps integral curves of the
Hamiltonian vector field of `g ∘ φ` to integral curves of that of `g`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_comp_hamiltonianVectorField_of_mem_range`),
in particular along a curve where its differential is surjective
(`TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_comp_hamiltonianVectorField`).

Hamiltonian vector fields and Poisson brackets restrict to open submanifolds, for any form
(`TauCeti.SmoothTwoForm.hamiltonianVectorField_comp_subtype_val`,
`TauCeti.SmoothTwoForm.poissonBracket_comp_subtype_val`).

## Main declarations

* `TauCeti.SmoothTwoForm.IsHamiltonianVectorField`: the equation `ι_X σ = df`, also in the
  language of forms (`TauCeti.SmoothTwoForm.isHamiltonianVectorField_iff_interior_eq`).
* `TauCeti.SmoothTwoForm.hamiltonianVectorField`: the Hamiltonian vector field `(σ♭)⁻¹ df`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isHamiltonianVectorField_iff_eq`: existence and
  uniqueness of the Hamiltonian vector field.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianVectorField`: a `C^(n+1)`
  Hamiltonian has a `C^n` Hamiltonian vector field, with the version
  `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianVectorField_uncurry` for jointly
  `C^(n+1)` families of Hamiltonians, such as time-dependent ones.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_smul`: `X^{cσ}_f = c⁻¹ X^σ_f`.
* `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.apply_eq_of_isMIntegralCurveOn`: conservation
  of energy along integral curves on preconnected sets of times, with the global case
  `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.apply_eq_of_isMIntegralCurve`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_or_exists_of_isMIntegralCurve_add_comp`:
  the dichotomy for the integral curves of `X_{G + f ∘ F}`.
* `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mpullback`,
  `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.prod`: Hamiltonian vector fields under pullback
  along related fields and on products.
* `TauCeti.SymplecticForm.hamiltonianVectorField_constSmooth`: comparison with the vector-space
  construction.
* `TauCeti.SmoothTwoForm.poissonBracket`: the Poisson bracket `{f, g} = σ(X_f, X_g)`, with
  `TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_eq_mvfderiv`: `{f, g} = df(X_g)`, and
  `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_poissonBracket`: the Poisson bracket of
  `C^(n+1)` functions is `C^n`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.map_hamiltonianVectorField_of_eval₂`: a linear map `D`
  with `σ₂(D u, D v) = σ(u, v)` and `dg ∘ D = df` whose range contains `X_g(y)` carries `X_f(x)`
  to `X_g(y)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_comp_hamiltonianVectorField` and
  `TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_comp`: naturality of Hamiltonian vector
  fields, their integral curves and Poisson brackets under maps pulling one form back to the
  other.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp_of_mem_range`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_comp_hamiltonianVectorField_of_mem_range`
  and `TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_comp_of_mem_range`: the same
  naturality where the Hamiltonian vector field is tangent to the map.
* `TauCeti.SmoothTwoForm.hamiltonianVectorField_comp_subtype_val`,
  `TauCeti.SmoothTwoForm.poissonBracket_comp_subtype_val`: restriction to an open submanifold
  preserves Hamiltonian vector fields and Poisson brackets.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1 (Hamiltonian vector fields on symplectic manifolds).
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 1.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold Topology

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
  ∀ x v, SmoothBundleForm.eval₂ σ x (X x) v = mvfderiv I f x v

/-- The defining characterization of a Hamiltonian vector field. -/
theorem isHamiltonianVectorField_iff :
    σ.IsHamiltonianVectorField f X ↔ ∀ x v, SmoothBundleForm.eval₂ σ x (X x) v = mvfderiv I f x v :=
  Iff.rfl

/-- A Hamiltonian vector field is one whose flat is the differential of the Hamiltonian. -/
theorem isHamiltonianVectorField_iff_flat :
    σ.IsHamiltonianVectorField f X ↔ ∀ x, σ.flat x (X x) = mvfderiv I f x := by
  simp only [isHamiltonianVectorField_iff, ContinuousLinearMap.ext_iff, flat_apply]

/-- A Hamiltonian vector field in the language of forms: the interior product `ι_X σ` is the
exterior derivative of the `0`-form of the Hamiltonian. -/
theorem isHamiltonianVectorField_iff_interior_eq :
    σ.IsHamiltonianVectorField f X ↔
      RoughForm.interior X σ.1 = mextDeriv (RoughForm.ofFunction I f) := by
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
Hamiltonian vector field on an interval of times (or any preconnected set of times), is constant
along that curve. -/
theorem apply_eq_of_isMIntegralCurveOn (hX : σ.IsHamiltonianVectorField f X) {γ : ℝ → M}
    {s : Set ℝ} (hs' : IsPreconnected s) (hγ : IsMIntegralCurveOn γ X s)
    (hf : ∀ t ∈ s, MDifferentiableAt I 𝓘(ℝ) f (γ t)) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    f (γ t) = f (γ t₀) :=
  hγ.apply_eq_of_mvfderiv_apply_eq_zero hs' hf (fun u _ ↦ hX.mvfderiv_apply_self (γ u)) ht₀ ht

/-- **Conservation of energy** along a global integral curve: a Hamiltonian, differentiable along
an integral curve of its Hamiltonian vector field, is constant along that curve. -/
theorem apply_eq_of_isMIntegralCurve (hX : σ.IsHamiltonianVectorField f X) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ X) (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) f (γ t)) (s t : ℝ) :
    f (γ t) = f (γ s) :=
  hX.apply_eq_of_isMIntegralCurveOn isPreconnected_univ (hγ.isMIntegralCurveOn _)
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

/-- **The Hamiltonian vector field is local**: at `x` it depends only on the germ of the
Hamiltonian at `x`. -/
theorem _root_.Filter.EventuallyEq.hamiltonianVectorField_eq (σ : SmoothTwoForm I M) {x : M}
    (hfg : f =ᶠ[𝓝 x] g) : σ.hamiltonianVectorField f x = σ.hamiltonianVectorField g x := by
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, hfg.mvfderiv_eq]

/-- The Hamiltonian vector field of a constant function vanishes. -/
@[simp]
theorem hamiltonianVectorField_const (σ : SmoothTwoForm I M) (c : ℝ) :
    σ.hamiltonianVectorField (fun _ ↦ c) = 0 := by
  funext x
  simp [hamiltonianVectorField_def, mvfderiv_const]

/-- Adding a constant to a Hamiltonian does not change its Hamiltonian vector field. No
differentiability is needed: `f` and `f + c` are differentiable at the same points. -/
@[simp]
theorem hamiltonianVectorField_add_const (σ : SmoothTwoForm I M) (f : M → ℝ) (c : ℝ) :
    σ.hamiltonianVectorField (fun x ↦ f x + c) = σ.hamiltonianVectorField f := by
  funext x
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, mvfderiv_add_const]

/-- The Hamiltonian vector field vanishes at every point near which the Hamiltonian is constant,
for instance outside the topological support of the Hamiltonian. -/
theorem hamiltonianVectorField_eq_zero_of_eventuallyEq {x : M} {c : ℝ}
    (h : f =ᶠ[nhds x] fun _ ↦ c) : σ.hamiltonianVectorField f x = 0 := by
  rw [hamiltonianVectorField_def, h.mvfderiv_eq]
  simp [mvfderiv_const]

/-- The Hamiltonian vector field vanishes at every point where the Hamiltonian is not
differentiable, by the convention `mfderiv = 0` there. -/
theorem hamiltonianVectorField_eq_zero_of_not_mdifferentiableAt {x : M}
    (h : ¬MDifferentiableAt I 𝓘(ℝ) f x) : σ.hamiltonianVectorField f x = 0 := by
  simp [hamiltonianVectorField_def, mvfderiv, mfderiv_zero_of_not_mdifferentiableAt h]

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
@[simp]
theorem hamiltonianVectorField_const_smul (c : ℝ) (x : M) :
    σ.hamiltonianVectorField (c • f) x = c • σ.hamiltonianVectorField f x := by
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, mvfderiv_const_smul_field, map_smul]

/-- Adding a real multiple of a differentiable Hamiltonian changes its vector field affinely. -/
theorem hamiltonianVectorField_add_smul {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) (r : ℝ) :
    σ.hamiltonianVectorField (f + r • g) x =
      σ.hamiltonianVectorField f x + r • σ.hamiltonianVectorField g x := by
  rw [hamiltonianVectorField_add hf (hg.const_smul r), hamiltonianVectorField_const_smul]

/-- The Hamiltonian vector field is subtractive on differentiable functions. -/
theorem hamiltonianVectorField_sub {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    σ.hamiltonianVectorField (f - g) x =
      σ.hamiltonianVectorField f x - σ.hamiltonianVectorField g x := by
  simp [hamiltonianVectorField_def, mvfderiv_sub hf hg]

/-- The Hamiltonian vector field of a finite sum of functions differentiable at `x` is the sum of
their Hamiltonian vector fields at `x`. -/
theorem hamiltonianVectorField_fun_sum {ι : Type*} {s : Finset ι} {F : ι → M → ℝ} {x : M}
    (hF : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (F i) x) :
    σ.hamiltonianVectorField (fun y ↦ ∑ i ∈ s, F i y) x =
      ∑ i ∈ s, σ.hamiltonianVectorField (F i) x := by
  simp only [hamiltonianVectorField_def, mvfderiv_fun_sum hF, map_sum]

/-- At fixed `x`, the derivative in the real coefficient of `f + t • g`, read in the model
space of the tangent fiber, is the Hamiltonian vector of `g` at `x`. -/
theorem hasDerivAt_hamiltonianVectorField_add_smul {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x) (r : ℝ) :
    HasDerivAt (fun t : ℝ => (σ.hamiltonianVectorField (f + t • g) x : E))
      (σ.hamiltonianVectorField g x : E) r := by
  -- Work in the model explicitly: instance search does not put a norm on the fiber synonym.
  let w : E := σ.hamiltonianVectorField f x
  let v : E := σ.hamiltonianVectorField g x
  have hd : HasDerivAt (fun t : ℝ => w + t • v) v r := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id r).smul_const v).const_add w
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (hamiltonianVectorField_add_smul hf hg))

/-- **The chain rule for Hamiltonian vector fields.** Post-composing the Hamiltonian with a real
function `φ` differentiable at `f x` rescales the Hamiltonian vector field at `x` by `φ'(f x)`:
`X_{φ ∘ f}(x) = φ'(f x) X_f(x)`. -/
theorem hamiltonianVectorField_comp {φ : ℝ → ℝ} {x : M} (hφ : DifferentiableAt ℝ φ (f x))
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    σ.hamiltonianVectorField (φ ∘ f) x = deriv φ (f x) • σ.hamiltonianVectorField f x := by
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, mvfderiv_scalar_comp hf hφ,
    map_smul]

/-- Along the chart variation `TauCeti.Manifold.sinChartVariation` of a `C^n` curve `γ`, `n ≥ 1`,
for `C^n` data, the integrand `σ(∂_t w - X_{H_t}(w), ∂_s w)` of the first variation of an action
functional at `s = 0` is `φ t` times the pairing of `γ' - X_{H_t}` with the tangent vector of chart
coordinates `e` at `γ t`. -/
theorem apply_mfderiv_sinChartVariation [I.Boundaryless] {H : ℝ → M → ℝ}
    {γ : ℝ → M} {x₀ : M} {J : Set ℝ} {φ : ℝ → ℝ} {e : E} {n : ℕ∞} (hn : 1 ≤ n) (hJo : IsOpen J)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    (hT : ∀ t ∈ J, ∀ c : ℝ, |c| ≤ 1 →
      extChartAt I x₀ (γ t) + (c * φ t) • e ∈ (extChartAt I x₀).target)
    (hφ : ContDiff ℝ n φ) (hφJ : tsupport φ ⊆ J) (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) (t : ℝ) :
    σ.1 (Manifold.sinChartVariation I γ x₀ J φ e (0, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I (Manifold.sinChartVariation I γ x₀ J φ e) (0, t) (0, 1) -
            σ.hamiltonianVectorField (H t) (Manifold.sinChartVariation I γ x₀ J φ e (0, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I (Manifold.sinChartVariation I γ x₀ J φ e) (0, t) (1, 0)] =
      φ t * σ.1 (γ t) ![Manifold.curveVelocity I γ t - σ.hamiltonianVectorField (H t) (γ t),
        (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e] := by
  have : IsManifold I n M := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hw0 : ∀ t, Manifold.sinChartVariation I γ x₀ J φ e (0, t) = γ t :=
    Manifold.sinChartVariation_zero hJ
  have hwd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (Manifold.sinChartVariation I γ x₀ J φ e) (0, t) :=
    (Manifold.contMDiff_sinChartVariation hJo hJ hT hφ hφJ hγ (0, t)).mdifferentiableAt
      (zero_lt_one.trans_le hn1).ne'
  have hv : mfderiv 𝓘(ℝ, ℝ × ℝ) I (Manifold.sinChartVariation I γ x₀ J φ e) (0, t) (0, 1) =
      Manifold.curveVelocity I γ t := by
    rw [← Manifold.curveVelocity_eq_mfderiv_snd
      (f := fun a b ↦ Manifold.sinChartVariation I γ x₀ J φ e (a, b)) hwd, funext hw0]
  -- first the base point `w (0, t) = γ t` and the velocity `∂_t w (0, t) = γ'(t)`
  trans σ.1 (γ t) ![Manifold.curveVelocity I γ t - σ.hamiltonianVectorField (H t) (γ t),
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (Manifold.sinChartVariation I γ x₀ J φ e) (0, t) (1, 0)]
  · rw [hv, hw0 t]
  -- then the variation field
  by_cases htJ : t ∈ J
  · rw [Manifold.mfderiv_sinChartVariation_of_mem hJo hJ (hφ.of_le hn1) hφJ ((hγ t).of_le hn1)
        hwd htJ,
      ← SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_smul_right,
      SmoothBundleForm.eval₂_apply, smul_eq_mul]
  · have hφt : φ t = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ htJ (hφJ h')
    rw [Manifold.mfderiv_sinChartVariation_of_notMem hwd htJ, hφt, zero_mul]
    exact (σ.1 (γ t)).map_coord_zero 1 rfl

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
include h

/-- The flat of the Hamiltonian vector field is the differential of the Hamiltonian. -/
@[simp]
theorem flat_hamiltonianVectorField (f : M → ℝ) (x : M) :
    σ.flat x (σ.hamiltonianVectorField f x) = mvfderiv I f x :=
  (h.isInvertible_flat x).self_apply_inverse _

/-- **The zeros of a Hamiltonian vector field are the critical points of the Hamiltonian**:
`X_f(x) = 0` exactly when `df_x = 0`. -/
theorem hamiltonianVectorField_eq_zero_iff {x : M} :
    σ.hamiltonianVectorField f x = 0 ↔ mvfderiv I f x = 0 := by
  rw [← h.flat_hamiltonianVectorField f x]
  exact (map_eq_zero_iff _ (h.isInvertible_flat x).injective).symm

/-- **Contraction with the Hamiltonian vector field** is the differential of the Hamiltonian,
`σ(X_f, v) = df(v)`. -/
theorem eval₂_hamiltonianVectorField (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    SmoothBundleForm.eval₂ σ x (σ.hamiltonianVectorField f x) v = mvfderiv I f x v := by
  rw [← flat_apply, h.flat_hamiltonianVectorField]

/-- The simp normal form of `eval₂_hamiltonianVectorField`, with `eval₂` unfolded:
`σ_x(X_f, v) = df_x(v)`. -/
@[simp]
theorem apply_hamiltonianVectorField (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    σ.1 x ![σ.hamiltonianVectorField f x, v] = mvfderiv I f x v := by
  rw [← SmoothBundleForm.eval₂_apply, h.eval₂_hamiltonianVectorField]

/-- Pairing `a - X_f` with `b` under `σ`: `σ(a - X_f, b) = -σ(b, a) - df(b)`. This is the
integrand of the first variation of the action functional. -/
theorem apply_sub_hamiltonianVectorField (f : M → ℝ) (x : M) (a b : TangentSpace I x) :
    σ.1 x ![a - σ.hamiltonianVectorField f x, b] = -σ.1 x ![b, a] - mvfderiv I f x b := by
  rw [← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply, ← flat_apply, map_sub,
    sub_apply, flat_apply, flat_apply, h.eval₂_hamiltonianVectorField, SmoothBundleForm.eval₂_swap]

/-- For a jointly `C¹` time-dependent Hamiltonian `H` and a `C¹` map `w` of the plane, the
integrand `t ↦ σ(∂_t w - X_{H_t}(w), ∂_s w)` of the first variation of an action functional,
taken at `(s₀, t)`, is continuous. -/
theorem continuous_apply_sub_hamiltonianVectorField {H : ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (Function.uncurry H)) {w : ℝ × ℝ → M}
    (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w) (s₀ : ℝ) :
    Continuous fun t ↦ σ.1 (w (s₀, t))
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (s₀, t)),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)] :=
  ((((σ.isSmoothForm.of_le (by simp)).continuous_apply_mfderiv hw (1, 0) (0, 1)).comp
    (continuous_const.prodMk continuous_id)).neg.sub
    (Manifold.continuous_mvfderiv_apply_mfderiv hH hw s₀)).congr fun t ↦
    (h.apply_sub_hamiltonianVectorField (H t) (w (s₀, t)) _ _).symm

/-- Along the chart variation `TauCeti.Manifold.sinChartVariation` of a `C^n` curve `γ`, `n ≥ 1`,
for `C^n` data, the pairing of `γ' - X_{H_t}` with the tangent vectors of chart coordinates `e`,
weighted by the profile `φ`, is continuous. -/
theorem continuous_mul_apply_curveVelocity_sub [I.Boundaryless] {H : ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (Function.uncurry H)) {γ : ℝ → M} {x₀ : M}
    {J : Set ℝ} {φ : ℝ → ℝ} {e : E} {n : ℕ∞} (hn : 1 ≤ n) (hJo : IsOpen J)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    (hT : ∀ t ∈ J, ∀ c : ℝ, |c| ≤ 1 →
      extChartAt I x₀ (γ t) + (c * φ t) • e ∈ (extChartAt I x₀).target)
    (hφ : ContDiff ℝ n φ) (hφJ : tsupport φ ⊆ J) (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) :
    Continuous fun t ↦ φ t * σ.1 (γ t) ![Manifold.curveVelocity I γ t -
      σ.hamiltonianVectorField (H t) (γ t), (trivializationAt E (TangentSpace I) x₀).symmL ℝ
        (γ t) e] :=
  have : IsManifold I n M := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  (h.continuous_apply_sub_hamiltonianVectorField hH
    ((Manifold.contMDiff_sinChartVariation hJo hJ hT hφ hφJ hγ).of_le (by exact_mod_cast hn))
    0).congr fun t ↦ σ.apply_mfderiv_sinChartVariation hn hJo hJ hT hφ hφJ hγ t

omit [FiniteDimensional ℝ E] in
/-- **The test direction of a first variation argument.** For a nondegenerate `σ` on a manifold
without boundary and a nonzero tangent vector `v` at `x₀`, there is a chart vector `e` such that
`σ(v, ·)` is positive on the tangent vector at `x₀` of coordinates `e` in the tangent-bundle
trivialization at `x₀`, and, near `x₀`, the points displaced by `c • e` with `|c| ≤ 1` stay in the
target of the extended chart at `x₀`. -/
theorem exists_pos_apply_and_eventually_add_smul_mem_target [I.Boundaryless] {x₀ : M}
    {v : TangentSpace I x₀} (hv : v ≠ 0) :
    ∃ e : E, 0 < σ.1 x₀ ![v, (trivializationAt E (TangentSpace I) x₀).symmL ℝ x₀ e] ∧
      ∀ᶠ x in 𝓝 x₀, x ∈ (extChartAt I x₀).source ∧
        ∀ c : ℝ, |c| ≤ 1 → extChartAt I x₀ x + c • e ∈ (extChartAt I x₀).target := by
  -- a tangent vector `u` at `x₀` pairing positively with `v`
  obtain ⟨u, hu⟩ : ∃ u : TangentSpace I x₀, 0 < σ.1 x₀ ![v, u] := by
    obtain ⟨u, hu⟩ : ∃ u, SmoothBundleForm.eval₂ σ x₀ v u ≠ 0 := by
      by_contra hcon
      exact hv (SmoothTwoForm.isNondegenerate_iff_separatingLeft.mp h x₀ _
        fun u ↦ not_not.mp (not_exists.mp hcon u))
    rw [SmoothBundleForm.eval₂_apply] at hu
    refine ⟨σ.1 x₀ ![v, u] • u, ?_⟩
    rw [← SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_smul_right,
      SmoothBundleForm.eval₂_apply, smul_eq_mul]
    exact mul_self_pos.mpr hu
  -- a ball of radius `2ρ` around `ψ x₀` in the target of the extended chart `ψ` at `x₀`
  obtain ⟨ρ, hρ, hball⟩ :
      ∃ ρ > 0, Metric.ball (extChartAt I x₀ x₀) (2 * ρ) ⊆ (extChartAt I x₀).target := by
    obtain ⟨ε, hε, hb⟩ :=
      Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x₀) _ (mem_extChartAt_target x₀)
    exact ⟨ε / 2, by positivity, by rwa [mul_div_cancel₀ _ two_ne_zero]⟩
  -- the chart vector `e`, shorter than `ρ`, of the tangent vector `κ • u` at `x₀`
  set e₀ : E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀ u
  set κ : ℝ := ρ / (‖e₀‖ + 1)
  have hκ : 0 < κ := by positivity
  have he : ‖κ • e₀‖ < ρ := by
    rw [norm_smul, Real.norm_of_nonneg hκ.le, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg e₀]
  refine ⟨κ • e₀, ?_, ?_⟩
  · rw [map_smul, Bundle.Trivialization.symmL_continuousLinearMapAt _
      (FiberBundle.mem_baseSet_trivializationAt' x₀), ← SmoothBundleForm.eval₂_apply,
      SmoothBundleForm.eval₂_smul_right, SmoothBundleForm.eval₂_apply, smul_eq_mul]
    exact mul_pos hκ hu
  -- near `x₀`, the point `ψ x` lies within `ρ` of `ψ x₀`, and `c • e` is shorter than `ρ`
  filter_upwards [(isOpen_extChartAt_source (I := I) x₀).mem_nhds (mem_extChartAt_source x₀),
    (continuousAt_extChartAt (I := I) x₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)]
    with x hx hxρ
  refine ⟨hx, fun c hc ↦ hball (Metric.mem_ball.mpr ?_)⟩
  have hce : ‖c • κ • e₀‖ ≤ ‖κ • e₀‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  calc dist (extChartAt I x₀ x + c • κ • e₀) (extChartAt I x₀ x₀)
      ≤ dist (extChartAt I x₀ x) (extChartAt I x₀ x₀) + ‖c • κ • e₀‖ := by
        rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
        exact norm_add_le _ _
    _ < ρ + ρ := add_lt_add_of_lt_of_le hxρ (hce.trans he.le)
    _ = 2 * ρ := by ring

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

/-- **Joint regularity of Hamiltonian vector fields of a family.** For a nondegenerate two-form on
a finite-dimensional manifold and a family of Hamiltonians `H : N → M → ℝ` which is jointly
`C^(n+1)` on `N × M`, the Hamiltonian vector fields `(p, x) ↦ X_{H p}(x)` are jointly `C^n`, for
`n ≤ ∞`. For `N = ℝ` this is the regularity of the vector field of a time-dependent Hamiltonian,
which is what is needed to integrate it to a time-dependent Hamiltonian flow. -/
theorem contMDiff_hamiltonianVectorField_uncurry {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J 1 N] {n : WithTop ℕ∞} (hn : n ≤ ∞) {H : N → M → ℝ}
    (hH : ContMDiff (J.prod I) 𝓘(ℝ) (n + 1) (Function.uncurry H)) :
    ContMDiff (J.prod I) I.tangent n
      (fun q : N × M ↦ (⟨q.2, σ.hamiltonianVectorField (H q.1) q.2⟩ : TangentBundle I M)) :=
  (((σ.contMDiff_flat.clm_bundle_inverse h.isInvertible_flat).of_le hn).comp
    contMDiff_snd).clm_bundle_apply hH.contMDiff_totalSpaceMk_mvfderiv_uncurry

/-- The Hamiltonian vector field of a `C²` function is differentiable. -/
theorem mdifferentiable_hamiltonianVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    MDifferentiable I I.tangent (fun y ↦ (σ.hamiltonianVectorField f y : TangentBundle I M)) :=
  (h.contMDiff_hamiltonianVectorField (n := 1) (by simp) (by norm_num [hf])).mdifferentiable
    one_ne_zero

/-- **Hamiltonian vector fields of a rescaled form.** For a nondegenerate form `σ` and `c ≠ 0`,
`X^{cσ}_f = c⁻¹ X^σ_f`. -/
theorem hamiltonianVectorField_smul {c : ℝ} (hc : c ≠ 0) (f : M → ℝ) :
    (c • σ).hamiltonianVectorField f = c⁻¹ • σ.hamiltonianVectorField f := by
  refine ((h.smul c hc).isHamiltonianVectorField_iff_eq.1 (isHamiltonianVectorField_iff.2
    fun x v ↦ ?_)).symm
  rw [SmoothForm.eval₂_smul, Pi.smul_apply, SmoothBundleForm.eval₂_smul_left,
    h.eval₂_hamiltonianVectorField, smul_inv_smul₀ hc]

/-- Rescaling the form and the Hamiltonian by the same `c ≠ 0` leaves the Hamiltonian vector
field unchanged: `X^{cσ}_{cf} = X^σ_f`. -/
theorem hamiltonianVectorField_smul_smul {c : ℝ} (hc : c ≠ 0) (f : M → ℝ) :
    (c • σ).hamiltonianVectorField (c • f) = σ.hamiltonianVectorField f := by
  funext x
  rw [hamiltonianVectorField_const_smul, h.hamiltonianVectorField_smul hc, Pi.smul_apply,
    smul_inv_smul₀ hc]

end IsNondegenerate

/-- **Orbits of a Hamiltonian enlarged along the levels of `F`.** Let `G` be supported in
`{F < s}`, let `f` be constant on `(-∞, s]`, and let `γ` be an integral curve of the Hamiltonian
vector field of `G + f ∘ F`. Either `γ` stays in `{F < s}` and is an integral curve of `X_G`, or it
lies in a level `F⁻¹(c)` with `c ≥ s`, along which `X_G` vanishes, and is an integral curve of
`f'(c) X_F`. -/
theorem IsNondegenerate.isMIntegralCurve_or_exists_of_isMIntegralCurve_add_comp
    [FiniteDimensional ℝ E]
    (hσ : σ.IsNondegenerate) {F G : M → ℝ} {f : ℝ → ℝ} (hG : MDifferentiable I 𝓘(ℝ) G)
    (hF : MDifferentiable I 𝓘(ℝ) F) (hf : Differentiable ℝ f) {s : ℝ}
    (hGs : tsupport G ⊆ {x | F x < s}) (hfs : ∀ r ≤ s, f r = f s) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField (G + f ∘ F))) :
    ((∀ t, F (γ t) < s) ∧ IsMIntegralCurve γ (σ.hamiltonianVectorField G)) ∨
      ∃ c, s ≤ c ∧ (∀ t, F (γ t) = c) ∧ (∀ t, σ.hamiltonianVectorField G (γ t) = 0) ∧
        IsMIntegralCurve γ (deriv f c • σ.hamiltonianVectorField F) := by
  have hXH (x : M) : σ.hamiltonianVectorField (G + f ∘ F) x =
      σ.hamiltonianVectorField G x + deriv f (F x) • σ.hamiltonianVectorField F x := by
    rw [hamiltonianVectorField_add (hG x) ((hf _).comp_mdifferentiableAt (hF x)),
      hamiltonianVectorField_comp (hf _) (hF x)]
  -- `X_G` vanishes off the support of `G`, and `X_{f ∘ F}` vanishes on `{F < s}`.
  have hXG (x : M) (hx : x ∉ tsupport G) : σ.hamiltonianVectorField G x = 0 :=
    hamiltonianVectorField_eq_zero_of_eventuallyEq (c := 0)
      (notMem_tsupport_iff_eventuallyEq.1 hx)
  have hXf (x : M) (hx : F x < s) : deriv f (F x) • σ.hamiltonianVectorField F x = 0 := by
    rw [← hamiltonianVectorField_comp (hf _) (hF x)]
    refine hamiltonianVectorField_eq_zero_of_eventuallyEq (c := f s) ?_
    filter_upwards [(isOpen_lt hF.continuous continuous_const).mem_nhds hx] with y hy
    exact hfs _ (le_of_lt hy)
  by_cases hlt : ∀ t, F (γ t) < s
  · refine Or.inl ⟨hlt, fun t ↦ ?_⟩
    have h := hγ t
    rwa [hXH, hXf _ (hlt t), add_zero] at h
  push Not at hlt
  obtain ⟨t₀, ht₀⟩ := hlt
  -- Off the support of `G`, the field is `f'(F) X_F`, which is tangent to the levels of `F`. So
  -- the set of times at which `γ` lies in the level of `γ t₀`, which is off the support, is open.
  have hconst : ∀ t, F (γ t) = F (γ t₀) := by
    have hγc := hγ.continuous
    have hopen : IsOpen {t | F (γ t) = F (γ t₀)} := by
      refine isOpen_iff_mem_nhds.2 fun t ht ↦ ?_
      have hmem : γ t ∈ (tsupport G)ᶜ := fun h ↦ (hGs h).not_ge (ht.symm ▸ ht₀)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
        ((isClosed_tsupport G).isOpen_compl.preimage hγc) t hmem
      refine Filter.mem_of_superset (Metric.ball_mem_nhds t hε) fun u hu ↦ ?_
      have h := (hγ.isMIntegralCurveOn (Metric.ball t ε)).apply_eq_of_mvfderiv_apply_eq_zero
        (convex_ball t ε).isPreconnected (fun v _ ↦ hF _) (fun v hv ↦ ?_)
        (Metric.mem_ball_self hε) hu
      · exact h.trans ht
      rw [hXH, hXG _ (hball hv), zero_add, map_smul,
        (hσ.isHamiltonianVectorField_hamiltonianVectorField F).mvfderiv_apply_self, smul_zero]
    have hclosed : IsClosed {t | F (γ t) = F (γ t₀)} :=
      isClosed_eq (hF.continuous.comp hγc) continuous_const
    have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, rfl⟩
    exact fun t ↦ (Set.ext_iff.1 huniv t).2 trivial
  have hXG' (t : ℝ) : σ.hamiltonianVectorField G (γ t) = 0 :=
    hXG _ fun h ↦ (hGs h).not_ge ((hconst t).symm ▸ ht₀)
  refine Or.inr ⟨F (γ t₀), ht₀, hconst, hXG', fun t ↦ ?_⟩
  have h : σ.hamiltonianVectorField (G + f ∘ F) (γ t) =
      (deriv f (F (γ t₀)) • σ.hamiltonianVectorField F) (γ t) := by
    rw [hXH, hXG', zero_add, hconst, Pi.smul_apply]
  rw [← h]
  exact hγ t

/-! ### The Poisson bracket -/

/-- The **Poisson bracket** `{f, g}(x) = σ(X_f x, X_g x)` of two functions. For a nondegenerate
form on a finite-dimensional manifold it is `{f, g} = df(X_g)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_eq_mvfderiv`). -/
def poissonBracket (σ : SmoothTwoForm I M) (f g : M → ℝ) (x : M) : ℝ :=
  SmoothBundleForm.eval₂ σ x (σ.hamiltonianVectorField f x) (σ.hamiltonianVectorField g x)

/-- The Poisson bracket unfolds as `σ` evaluated on the two Hamiltonian vector fields. -/
theorem poissonBracket_def (σ : SmoothTwoForm I M) (f g : M → ℝ) (x : M) :
    σ.poissonBracket f g x =
      SmoothBundleForm.eval₂ σ x (σ.hamiltonianVectorField f x) (σ.hamiltonianVectorField g x) :=
  (rfl)

/-- The Poisson bracket is antisymmetric. -/
theorem neg_poissonBracket (σ : SmoothTwoForm I M) (f g : M → ℝ) (x : M) :
    -σ.poissonBracket g f x = σ.poissonBracket f g x := by
  rw [poissonBracket_def, poissonBracket_def, SmoothBundleForm.eval₂_swap σ x, neg_neg]

@[simp]
theorem poissonBracket_self (σ : SmoothTwoForm I M) (f : M → ℝ) (x : M) :
    σ.poissonBracket f f x = 0 :=
  SmoothBundleForm.eval₂_self σ x _

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

/-- Adding a constant to the first Hamiltonian does not change the Poisson bracket. -/
@[simp]
theorem poissonBracket_add_const_left (σ : SmoothTwoForm I M) (f : M → ℝ) (c : ℝ) (g : M → ℝ)
    (x : M) : σ.poissonBracket (fun y ↦ f y + c) g x = σ.poissonBracket f g x := by
  rw [poissonBracket_def, poissonBracket_def, hamiltonianVectorField_add_const]

/-- Adding a constant to the second Hamiltonian does not change the Poisson bracket. -/
@[simp]
theorem poissonBracket_add_const_right (σ : SmoothTwoForm I M) (f g : M → ℝ) (c : ℝ) (x : M) :
    σ.poissonBracket f (fun y ↦ g y + c) x = σ.poissonBracket f g x := by
  rw [poissonBracket_def, poissonBracket_def, hamiltonianVectorField_add_const]

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
theorem poissonBracket_const_smul_left (c : ℝ) (x : M) :
    σ.poissonBracket (c • f) g x = c • σ.poissonBracket f g x := by
  simp only [poissonBracket_def, hamiltonianVectorField_const_smul c x,
    ← SmoothForm.bilinFormAt_apply, map_smul, LinearMap.smul_apply]

/-- Multiplication of the second argument by a real constant scales the Poisson bracket. -/
theorem poissonBracket_const_smul_right (c : ℝ) (x : M) :
    σ.poissonBracket f (c • g) x = c • σ.poissonBracket f g x := by
  simp only [poissonBracket_def, hamiltonianVectorField_const_smul c x,
    ← SmoothForm.bilinFormAt_apply, map_smul]

/-- The Poisson bracket is subtractive in its first argument on differentiable functions. -/
theorem poissonBracket_sub_left {k : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    σ.poissonBracket (f - g) k x = σ.poissonBracket f k x - σ.poissonBracket g k x := by
  simp only [poissonBracket_def, hamiltonianVectorField_sub hf hg,
    ← SmoothForm.bilinFormAt_apply, map_sub, LinearMap.sub_apply]

/-- The Poisson bracket is subtractive in its second argument on differentiable functions. -/
theorem poissonBracket_sub_right {k : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    σ.poissonBracket k (f - g) x = σ.poissonBracket k f x - σ.poissonBracket k g x := by
  simp only [poissonBracket_def, hamiltonianVectorField_sub hf hg,
    ← SmoothForm.bilinFormAt_apply, map_sub]

/-- The Poisson bracket is additive in its first argument on finite sums of functions
differentiable at the point: `{∑ fᵢ, g} = ∑ {fᵢ, g}`. -/
theorem poissonBracket_fun_sum_left {ι : Type*} {s : Finset ι} {F : ι → M → ℝ} {x : M}
    (hF : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (F i) x) :
    σ.poissonBracket (fun y ↦ ∑ i ∈ s, F i y) g x = ∑ i ∈ s, σ.poissonBracket (F i) g x := by
  simp only [poissonBracket_def, hamiltonianVectorField_fun_sum hF,
    ← SmoothForm.bilinFormAt_apply, map_sum, LinearMap.sum_apply]

/-- The Poisson bracket is additive in its second argument on finite sums of functions
differentiable at the point: `{f, ∑ gᵢ} = ∑ {f, gᵢ}`. -/
theorem poissonBracket_fun_sum_right {ι : Type*} {s : Finset ι} {G : ι → M → ℝ} {x : M}
    (hG : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (G i) x) :
    σ.poissonBracket f (fun y ↦ ∑ i ∈ s, G i y) x = ∑ i ∈ s, σ.poissonBracket f (G i) x := by
  simp only [poissonBracket_def, hamiltonianVectorField_fun_sum hG,
    ← SmoothForm.bilinFormAt_apply, map_sum]

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

/-- **Regularity of the Poisson bracket.** For a nondegenerate two-form on a finite-dimensional
manifold, the Poisson bracket of two `C^(n+1)` functions is `C^n`, for `n ≤ ∞`. -/
theorem contMDiff_poissonBracket {n : WithTop ℕ∞} (hn : n ≤ ∞) {f g : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) (hg : ContMDiff I 𝓘(ℝ) (n + 1) g) :
    ContMDiff I 𝓘(ℝ) n (σ.poissonBracket f g) := by
  rw [funext (h.poissonBracket_eq_mvfderiv f g)]
  exact (hf.contMDiff_mvfderiv_apply le_rfl).comp (h.contMDiff_hamiltonianVectorField hn hg)

end IsNondegenerate

/-! ### Pullbacks and products -/

section PullbackProd

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  {σ₂ : SmoothTwoForm I₂ M₂} {g : M₂ → ℝ} {Y : (y : M₂) → TangentSpace I₂ y}

/-- **Hamiltonian vector fields pull back along related fields.** Let `Y` be a Hamiltonian vector
field of `g` for `σ₂` and let a smooth map `φ` carry a vector field `X` to `Y`, that is
`dφ (X x) = Y (φ x)`. Then `X` is a Hamiltonian vector field of `g ∘ φ` for the pullback `φ^* σ₂`.
No nondegeneracy is needed. -/
theorem IsHamiltonianVectorField.mpullback (hY : σ₂.IsHamiltonianVectorField g Y) {φ : M → M₂}
    (hφ : ContMDiff I I₂ ∞ φ) (hg : ∀ x, MDifferentiableAt I₂ 𝓘(ℝ) g (φ x))
    (hXY : ∀ x, mfderiv I I₂ φ x (X x) = Y (φ x)) :
    IsHamiltonianVectorField (SmoothForm.mpullback φ hφ σ₂) (g ∘ φ) X := fun x v ↦ by
  rw [SmoothForm.eval₂_mpullback, hXY, hY,
    mvfderiv_comp_apply x (hg x) ((hφ x).mdifferentiableAt (by simp))]

/-- **Hamiltonian vector fields of products.** If `X` is a Hamiltonian vector field of `f` for
`σ` on `M` and `Y` one of `g` for `σ₂` on `M₂`, then the product field `(X, Y)` is a Hamiltonian
vector field of `(x, y) ↦ f x + g y` for the product form `pr₁^* σ + pr₂^* σ₂` on `M × M₂`. -/
theorem IsHamiltonianVectorField.prod (hX : σ.IsHamiltonianVectorField f X)
    (hY : σ₂.IsHamiltonianVectorField g Y) (hf : MDifferentiable I 𝓘(ℝ) f)
    (hg : MDifferentiable I₂ 𝓘(ℝ) g) :
    (σ.prod σ₂).IsHamiltonianVectorField (fun p ↦ f p.1 + g p.2)
      (Manifold.prodVectorField X Y) := fun p v ↦ by
  have hf' : MDifferentiableAt (I.prod I₂) 𝓘(ℝ) (fun q : M × M₂ ↦ f q.1) p :=
    (hf p.1).comp p mdifferentiableAt_fst
  have hg' : MDifferentiableAt (I.prod I₂) 𝓘(ℝ) (fun q : M × M₂ ↦ g q.2) p :=
    (hg p.2).comp p mdifferentiableAt_snd
  rw [eval₂_prod, Manifold.tangentSpaceProdEquiv_prodVectorField, hX, hY,
    Manifold.tangentSpaceProdEquiv_apply, mvfderiv_fun_add hf' hg', add_apply]
  exact congrArg₂ (· + ·) (mvfderiv_comp_fst_apply f p v).symm
    (mvfderiv_comp_snd_apply g p v).symm

end PullbackProd

/-! ### Naturality under symplectic maps -/

section Naturality

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₂] {σ₂ : SmoothTwoForm I₂ M₂} {φ : M → M₂}
  {x : M}

namespace IsNondegenerate

/-- **Linear maps preserving nondegenerate forms carry Hamiltonian vectors.** Let `D` be a
linear map from the tangent space of `M` at `x` to the tangent space of `M₂` at `y` with
`σ₂_y(D u, D v) = σ_x(u, v)` and `dg_y ∘ D = df_x`. If `X_g(y)` lies in the range of `D`, then
`D` carries `X_f(x)` to `X_g(y)`. -/
theorem map_hamiltonianVectorField_of_eval₂ (hσ : σ.IsNondegenerate) (hσ₂ : σ₂.IsNondegenerate)
    {y : M₂} {D : TangentSpace I x →L[ℝ] TangentSpace I₂ y} {f : M → ℝ} {g : M₂ → ℝ}
    (hDg : σ₂.hamiltonianVectorField g y ∈ D.range)
    (hD : ∀ u v, SmoothBundleForm.eval₂ σ₂ y (D u) (D v) = SmoothBundleForm.eval₂ σ x u v)
    (hfg : ∀ u, mvfderiv I₂ g y (D u) = mvfderiv I f x u) :
    D (σ.hamiltonianVectorField f x) = σ₂.hamiltonianVectorField g y := by
  obtain ⟨v, hv⟩ := hDg
  rw [ContinuousLinearMap.coe_coe] at hv
  -- The tangent vector `v` lifting `X_g(y)` satisfies the Hamiltonian equation of `f`.
  have hvσ : σ.flat x v = mvfderiv I f x := ContinuousLinearMap.ext fun w ↦ by
    rw [flat_apply, ← hD, hv, hσ₂.eval₂_hamiltonianVectorField, hfg]
  rwa [← (hσ.isInvertible_flat x).injective (hvσ.trans (hσ.flat_hamiltonianVectorField _ x).symm)]

end IsNondegenerate

namespace IsNondegenerate

variable (hσ : σ.IsNondegenerate) (hσ₂ : σ₂.IsNondegenerate) (hφ : ContMDiff I I₂ ∞ φ)
  (hφσ : SmoothForm.mpullback φ hφ σ₂ = σ)
include hσ hσ₂ hφσ

/-- **Hamiltonian vector fields tangent to a map are natural.** Let a smooth map `φ` pull a
nondegenerate form `σ₂` back to a nondegenerate form `σ`. If the Hamiltonian vector of `g` at `φ x`
is tangent to `φ`, that is in the range of the differential of `φ` at `x`, then this differential
carries the Hamiltonian vector of `g ∘ φ` at `x` to it. For the inclusion of a symplectic
submanifold, this computes the Hamiltonian vector fields of the restrictions of the ambient
functions whose Hamiltonian vector fields are tangent to the submanifold. -/
theorem mfderiv_hamiltonianVectorField_comp_of_mem_range {g : M₂ → ℝ}
    (hg : MDifferentiableAt I₂ 𝓘(ℝ) g (φ x))
    (hgx : σ₂.hamiltonianVectorField g (φ x) ∈ (mfderiv I I₂ φ x).range) :
    mfderiv I I₂ φ x (σ.hamiltonianVectorField (g ∘ φ) x) = σ₂.hamiltonianVectorField g (φ x) :=
  hσ.map_hamiltonianVectorField_of_eval₂ hσ₂ hgx
    (fun u v ↦ by rw [← hφσ, SmoothForm.eval₂_mpullback φ hφ])
    fun u ↦ (mvfderiv_comp_apply x hg ((hφ x).mdifferentiableAt (by simp)) u).symm

/-- **Hamiltonian vector fields are natural.** Let a smooth map `φ` pull a nondegenerate form `σ₂`
back to a nondegenerate form `σ`. At a point where the differential of `φ` is surjective, it carries
the Hamiltonian vector field of `g ∘ φ` to the Hamiltonian vector field of `g`. -/
theorem mfderiv_hamiltonianVectorField_comp (hx : Function.Surjective (mfderiv I I₂ φ x))
    {g : M₂ → ℝ} (hg : MDifferentiableAt I₂ 𝓘(ℝ) g (φ x)) :
    mfderiv I I₂ φ x (σ.hamiltonianVectorField (g ∘ φ) x) = σ₂.hamiltonianVectorField g (φ x) :=
  hσ.mfderiv_hamiltonianVectorField_comp_of_mem_range hσ₂ hφ hφσ hg (hx _)

/-- **Poisson brackets with a Hamiltonian tangent to a map are natural.** Let a smooth map `φ` pull
a nondegenerate form `σ₂` back to a nondegenerate form `σ`. If the Hamiltonian vector of `k` at
`φ x` is in the range of the differential of `φ` at `x`, then the Poisson bracket of `g ∘ φ` and
`k ∘ φ` at `x` is the Poisson bracket of `g` and `k` at `φ x`. No condition is imposed on `g`
beyond differentiability. -/
theorem poissonBracket_comp_of_mem_range {g k : M₂ → ℝ}
    (hg : MDifferentiableAt I₂ 𝓘(ℝ) g (φ x)) (hk : MDifferentiableAt I₂ 𝓘(ℝ) k (φ x))
    (hkx : σ₂.hamiltonianVectorField k (φ x) ∈ (mfderiv I I₂ φ x).range) :
    σ.poissonBracket (g ∘ φ) (k ∘ φ) x = σ₂.poissonBracket g k (φ x) := by
  rw [hσ.poissonBracket_eq_mvfderiv, hσ₂.poissonBracket_eq_mvfderiv,
    mvfderiv_comp_apply x hg ((hφ x).mdifferentiableAt (by simp)),
    hσ.mfderiv_hamiltonianVectorField_comp_of_mem_range hσ₂ hφ hφσ hk hkx]

/-- **Poisson brackets are natural.** Let a smooth map `φ` pull a nondegenerate form `σ₂` back to a
nondegenerate form `σ`. At a point where the differential of `φ` is surjective, the Poisson
bracket of `g ∘ φ` and `k ∘ φ` is the Poisson bracket of `g` and `k` at the image point. -/
theorem poissonBracket_comp (hx : Function.Surjective (mfderiv I I₂ φ x)) {g k : M₂ → ℝ}
    (hg : MDifferentiableAt I₂ 𝓘(ℝ) g (φ x)) (hk : MDifferentiableAt I₂ 𝓘(ℝ) k (φ x)) :
    σ.poissonBracket (g ∘ φ) (k ∘ φ) x = σ₂.poissonBracket g k (φ x) :=
  hσ.poissonBracket_comp_of_mem_range hσ₂ hφ hφσ hg hk (hx _)

/-- **Hamiltonian integral curves tangent to a map are natural.** Let a smooth map `φ` pull a
nondegenerate form `σ₂` back to a nondegenerate form `σ`. If `γ` is an integral curve of the
Hamiltonian vector field of `g ∘ φ`, and at every point `φ (γ t)` the function `g` is
differentiable with Hamiltonian vector in the range of the differential of `φ` at `γ t`, then
`φ ∘ γ` is an integral curve of the Hamiltonian vector field of `g`. -/
theorem isMIntegralCurve_comp_hamiltonianVectorField_of_mem_range {g : M₂ → ℝ} {γ : ℝ → M}
    (hgγ : ∀ t, σ₂.hamiltonianVectorField g (φ (γ t)) ∈ (mfderiv I I₂ φ (γ t)).range)
    (hg : ∀ t, MDifferentiableAt I₂ 𝓘(ℝ) g (φ (γ t)))
    (hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField (g ∘ φ))) :
    IsMIntegralCurve (φ ∘ γ) (σ₂.hamiltonianVectorField g) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  exact hγ.map_of_mfderiv_eq (fun t _ ↦ (hφ (γ t)).mdifferentiableAt (by simp))
    fun t _ ↦ hσ.mfderiv_hamiltonianVectorField_comp_of_mem_range hσ₂ hφ hφσ (hg t) (hgγ t)

/-- **Hamiltonian integral curves are natural.** Let a smooth map `φ` pull a nondegenerate form
`σ₂` back to a nondegenerate form `σ`. If `γ` is an integral curve of the Hamiltonian vector field
of `g ∘ φ`, along which the differential of `φ` is surjective and `g` is differentiable at the
image points, then `φ ∘ γ` is an integral curve of the Hamiltonian vector field of `g`. -/
theorem isMIntegralCurve_comp_hamiltonianVectorField {g : M₂ → ℝ} {γ : ℝ → M}
    (hsurj : ∀ t, Function.Surjective (mfderiv I I₂ φ (γ t)))
    (hg : ∀ t, MDifferentiableAt I₂ 𝓘(ℝ) g (φ (γ t)))
    (hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField (g ∘ φ))) :
    IsMIntegralCurve (φ ∘ γ) (σ₂.hamiltonianVectorField g) :=
  hσ.isMIntegralCurve_comp_hamiltonianVectorField_of_mem_range hσ₂ hφ hφσ (fun t ↦ hsurj t _) hg hγ

end IsNondegenerate

end Naturality

/-! ### Restriction to open submanifolds -/

section Opens

/-- **Hamiltonian vector fields restrict to open submanifolds.** For an open set `U`, the
Hamiltonian vector field of the restriction of `f` to `U`, for the restriction of `σ` to `U`, is
the Hamiltonian vector field of `f`, read in the tangent space of `U`. No nondegeneracy or
differentiability is needed: both sides are computed from the same form and differential. -/
@[simp]
theorem hamiltonianVectorField_comp_subtype_val (σ : SmoothTwoForm I M)
    {U : TopologicalSpace.Opens M} (f : M → ℝ) (x : U) :
    SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ)
        (f ∘ Subtype.val) x =
      (Manifold.tangentSpaceOpenEquiv (I := I) x).symm (σ.hamiltonianVectorField f x) := by
  have hflat : SmoothTwoForm.flat
      (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ) x = σ.flat x := by
    ext v w
    rw [flat_apply, SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe, Manifold.tangentSpaceOpenEquiv_apply,
      Manifold.tangentSpaceOpenEquiv_apply]
    exact (flat_apply σ x v w).symm
  have hd : mvfderiv I (f ∘ Subtype.val) x = mvfderiv I f (x : M) := by
    ext v
    exact Manifold.mfderiv_comp_subtype_val_apply v
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, hflat, hd,
    Manifold.tangentSpaceOpenEquiv_symm_apply]
  -- The tangent spaces at `x` in `U` and at `(x : M)` in `M` are both the model space `E`.
  exact (rfl)

/-- **Poisson brackets restrict to open submanifolds.** For an open set `U`, the Poisson bracket
of the restrictions of `f` and `g` to `U`, for the restriction of `σ` to `U`, is the restriction of
their Poisson bracket. -/
@[simp]
theorem poissonBracket_comp_subtype_val (σ : SmoothTwoForm I M)
    {U : TopologicalSpace.Opens M} (f g : M → ℝ) (x : U) :
    SmoothTwoForm.poissonBracket
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ)
        (f ∘ Subtype.val) (g ∘ Subtype.val) x =
      σ.poissonBracket f g x := by
  rw [poissonBracket_def, poissonBracket_def, hamiltonianVectorField_comp_subtype_val,
    hamiltonianVectorField_comp_subtype_val, SmoothForm.eval₂_mpullback,
    Manifold.mfderiv_subtype_val]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

end Opens

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
  rw [TauCeti.mvfderiv_eq_fderiv_apply]
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
