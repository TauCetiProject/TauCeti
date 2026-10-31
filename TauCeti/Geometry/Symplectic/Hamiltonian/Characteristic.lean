/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Reparam
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import TauCeti.Geometry.Manifold.RegularValue.Scalar.Level

/-!
# Characteristic foliations of regular hypersurfaces

Let `σ` be a nondegenerate two-form on a manifold `M` modelled on a finite-dimensional space, and
let `S = f⁻¹(c)` be a regular level of a function `f : M → ℝ`, a hypersurface whose tangent space
at `x` is `ker df_x` (`TauCeti.range_mfderiv_coe_scalarRegularLevel`). The restriction of `σ` to
`T_x S` has a one-dimensional kernel `T_x S ∩ (T_x S)^σ`, the **characteristic line** of `S` at
`x`; these lines form the characteristic foliation of `S`. With the convention `ι_{X_f} σ = df`:

* the symplectic complement of `ker df_x` is the line spanned by the Hamiltonian vector `X_f(x)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.orthogonal_ker_mfderiv_eq_span_singleton`), and since
  `df(X_f) = 0` this is also the characteristic line
  (`TauCeti.SmoothTwoForm.IsNondegenerate.ker_mfderiv_inf_orthogonal_eq_span_singleton`);
* at a regular point `X_f(x) ≠ 0`, so the line is indeed a line;
* if `S` lies in a level `g⁻¹(c')` of a second function, then `ker dg = ker df` at the regular
  points of `g` on `S` (`TauCeti.ker_mfderiv_eq_of_forall_eq_imp`), and `X_g` is a nonzero
  multiple of `X_f` there
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_hamiltonianVectorField_eq_smul`).

A **closed characteristic** of `S` is a closed leaf of the characteristic foliation, an embedded
circle in `S` tangent to the characteristic lines. Traced by a nonconstant periodic orbit of the
Hamiltonian flow of a defining function `f`, it is traced by a periodic orbit of every other
defining function `g`, after a change of time and with a new period
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_homeomorph_isMIntegralCurve_comp`).
So closed characteristics correspond to periodic orbits of any defining Hamiltonian, up to
reparametrization; this is the form in which periodic orbits on a fixed energy level, such as
those produced by almost existence, are statements about the hypersurface alone.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.ker_mfderiv_inf_orthogonal_eq_span_singleton`: the
  characteristic line of a level is spanned by the Hamiltonian vector field.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_hamiltonianVectorField_eq_smul`: two defining
  functions of a regular hypersurface have proportional Hamiltonian vector fields along it.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_homeomorph_isMIntegralCurve_comp`:
  periodic orbits on the hypersurface do not depend on the defining function, up to
  reparametrization.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 1.1 (the characteristic line bundle of an energy surface and its closed
  characteristics).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 1.1 and Chapter 12 (closed characteristics).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
  {f g : M → ℝ} {c c' : ℝ} {x : M}

include hσ

/-! ### The characteristic line at a point -/

/-- **The symplectic complement of `ker df_x`** is the line spanned by the Hamiltonian vector
`X_f(x)`. This is the scalar case of `orthogonal_ker_mfderiv`, and needs no differentiability: at a
point where `f` is not differentiable both sides are `0`. -/
theorem orthogonal_ker_mfderiv_eq_span_singleton :
    (hσ.symplecticFormAt x).orthogonal (mfderiv I 𝓘(ℝ) f x).ker =
      ℝ ∙ σ.hamiltonianVectorField f x := by
  rw [← SymplecticForm.orthogonal_orthogonal (hσ.symplecticFormAt x) (ℝ ∙ _)]
  congr 1
  ext v
  simp only [SymplecticForm.mem_orthogonal_span_iff, mem_singleton_iff, forall_eq,
    symplecticFormAt_apply, hσ.eval₂_hamiltonianVectorField, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, mvfderiv_apply_eq_mfderiv_apply]
  -- The two zeros are those of `ℝ` and of its tangent space at `f x`, which is `ℝ`.
  rfl

/-- **The characteristic line of a level.** The kernel of `σ` restricted to `ker df_x` is the line
spanned by the Hamiltonian vector `X_f(x)`. At a regular point `x`, `ker df_x` is the tangent space
of the level of `f` through `x`, and `X_f(x) ≠ 0` (`hamiltonianVectorField_ne_zero`). -/
theorem ker_mfderiv_inf_orthogonal_eq_span_singleton :
    (mfderiv I 𝓘(ℝ) f x).ker ⊓ (hσ.symplecticFormAt x).orthogonal (mfderiv I 𝓘(ℝ) f x).ker =
      ℝ ∙ σ.hamiltonianVectorField f x := by
  rw [hσ.orthogonal_ker_mfderiv_eq_span_singleton, inf_eq_right,
    Submodule.span_singleton_le_iff_mem]
  exact (hσ.isHamiltonianVectorField_hamiltonianVectorField f).mvfderiv_apply_self x

/-- The Hamiltonian vector field does not vanish at a regular point of the Hamiltonian. -/
theorem hamiltonianVectorField_ne_zero (hx : IsRegularPoint I 𝓘(ℝ) f x) :
    σ.hamiltonianVectorField f x ≠ 0 := by
  intro h0
  refine isRegularPoint_iff_mvfderiv_ne_zero.1 hx ?_
  rw [← hσ.flat_hamiltonianVectorField, h0, map_zero]

/-! ### Two defining functions of one hypersurface -/

/-- **Two defining functions have proportional Hamiltonian vector fields.** If the regular level
`f⁻¹(c)` of a function `C¹` near the level lies in the level `g⁻¹(c')` of a second function, then
at each of its points `x` which is a regular point of `g`, `X_g(x)` is a nonzero multiple of
`X_f(x)`: both span the characteristic line. -/
theorem exists_hamiltonianVectorField_eq_smul [I.Boundaryless]
    (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) 1 f x) (hfc : IsRegularValue I 𝓘(ℝ) f c)
    (hfg : ∀ x, f x = c → g x = c') (hx : f x = c) (hgx : IsRegularPoint I 𝓘(ℝ) g x) :
    ∃ a : ℝ, a ≠ 0 ∧ σ.hamiltonianVectorField g x = a • σ.hamiltonianVectorField f x := by
  have hmem : σ.hamiltonianVectorField g x ∈ ℝ ∙ σ.hamiltonianVectorField f x := by
    rw [← hσ.orthogonal_ker_mfderiv_eq_span_singleton,
      ← ker_mfderiv_eq_of_forall_eq_imp hf hfc hfg hx hgx,
      hσ.orthogonal_ker_mfderiv_eq_span_singleton]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨a, ?_, ha.symm⟩
  rintro rfl
  exact hσ.hamiltonianVectorField_ne_zero hgx (by simp [← ha])

/-! ### Closed characteristics -/

/-- **Closed characteristics do not depend on the defining Hamiltonian.** Let the regular level
`S = f⁻¹(c)` of a `C¹` function lie in the level `g⁻¹(c')` of a second `C¹` function which is
regular along `S`, for instance as the same regular hypersurface. A periodic orbit `γ`, of nonzero
period, of the Hamiltonian vector field of `f` starting on `S` is, after a change of time by a
homeomorphism `ψ` of `ℝ` fixing `0`, a periodic orbit of nonzero period of the Hamiltonian vector
field of `g`. -/
theorem exists_homeomorph_isMIntegralCurve_comp [I.Boundaryless]
    (hf : ContMDiff I 𝓘(ℝ) 1 f) (hg : ContMDiff I 𝓘(ℝ) 1 g) (hfc : IsRegularValue I 𝓘(ℝ) f c)
    (hfg : ∀ x, f x = c → g x = c') (hgS : ∀ x, f x = c → IsRegularPoint I 𝓘(ℝ) g x) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField f)) (hγ₀ : f (γ 0) = c) {T : ℝ}
    (hT : T ≠ 0) (hper : Periodic γ T) :
    ∃ ψ : ℝ ≃ₜ ℝ, ψ 0 = 0 ∧ ∃ T', T' ≠ 0 ∧ Periodic (γ ∘ ψ) T' ∧
      IsMIntegralCurve (γ ∘ ψ) (σ.hamiltonianVectorField g) := by
  -- By conservation of energy the orbit stays on `S`.
  have hγS : ∀ t, f (γ t) = c := fun t ↦ by
    rw [(hσ.isHamiltonianVectorField_hamiltonianVectorField f).apply_eq_of_isMIntegralCurve hγ
        (fun t ↦ hf.mdifferentiableAt one_ne_zero) 0 t, hγ₀]
  have hcont : ∀ k : M → ℝ, ContMDiff I 𝓘(ℝ) 1 k → Continuous (T% (σ.hamiltonianVectorField k)) :=
    fun k hk ↦ (hσ.contMDiff_hamiltonianVectorField (n := 0) (by simp)
      (by simpa using hk)).continuous
  exact hγ.exists_homeomorph_isMIntegralCurve_comp hT hper
    (fun t ↦ (hcont f hf).continuousAt) (fun t ↦ (hcont g hg).continuousAt)
    (fun t ↦ hσ.hamiltonianVectorField_ne_zero (hfc.isRegularPoint (hγS t)))
    fun t ↦ hσ.exists_hamiltonianVectorField_eq_smul (fun x _ ↦ hf.contMDiffAt) hfc hfg
      (hγS t) (hgS _ (hγS t))

end IsNondegenerate

end SmoothTwoForm

end TauCeti
