/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# Hamiltonian dynamics on reduced spaces

Symplectic reduction produces a manifold `Z` with two smooth maps out of it, a map `i : Z → M`
into a manifold with a two-form `σ` and a map `p : Z → Q` onto a manifold with a two-form `η`,
such that

`p^* η = i^* σ`.

For Marsden–Weinstein–Meyer reduction, `Z = μ⁻¹(c)` is a regular level of a moment map, `i` its
inclusion, `p : Z → Z / G_c` the orbit projection and `η` the reduced symplectic form
(`TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`). This file shows that Hamiltonian
dynamics descends along such data. Let `f : M → ℝ` and `F : Q → ℝ` be related by `f ∘ i = F ∘ p`,
as a function invariant under the symmetry is related to the function it induces on the reduced
space.

* If a tangent vector `Y` of `Z` at `z` is carried by `di` to the value at `i z` of a Hamiltonian
  vector field `X` of `f`, then `dp Y` satisfies the Hamiltonian equation of `F` at `p z` on the
  image of `dp`: `η(dp Y, dp v) = dF(dp v)`
  (`TauCeti.SmoothTwoForm.eval₂_mfderiv_eq_mvfderiv_of_mpullback_eq`). Where `η` is
  nondegenerate and `dp` is surjective, `dp Y = X_F(p z)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_eq_hamiltonianVectorField_of_mpullback_eq`).
* Hence **the bracket of reduced functions is the reduction of the bracket**: if moreover
  `g ∘ i = G ∘ p` and `X_g(i z)` is tangent to `Z`, then `{F, G}(p z) = {f, g}(i z)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_eq_of_mpullback_eq`).
* Hence **Hamiltonian flows descend**: if a differentiable curve `γ` in `Z` is carried by `i` to
  an integral curve of `X`, then `p ∘ γ` is an integral curve of `X_F`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_comp_of_mpullback_eq`).

None of these statements needs `σ` to be closed, `p` to be a quotient map, or `i` to be an
immersion, and the first two are pointwise. For `Z = M` and `i = id` they recover the naturality of
Hamiltonian vector fields under a map pulling one form back to another
(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp`).

For a level of a moment map `μ`, whose tangent spaces are `ker dμ`, the tangency hypothesis is
**Noether's theorem**: a Hamiltonian vector field of `f` lies in `ker dμ_x` exactly when `df_x`
vanishes on all generated vector fields `ξ_M`
(`TauCeti.SmoothTwoForm.IsMomentMap.mem_ker_differential_iff_of_isHamiltonianVectorField`). So
for infinitesimally invariant Hamiltonians the Hamiltonian vector field of the reduced function is
the projection of a lift of the original one
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_mfderiv_eq_and_mfderiv_eq_hamiltonianVectorField`),
and the reduced bracket is the reduction of the bracket
(`TauCeti.SmoothTwoForm.IsMomentMap.poissonBracket_eq_of_mpullback_eq`).

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_eq_hamiltonianVectorField_of_mpullback_eq`:
  `dp Y = X_F(p z)` when `di Y = X_f(i z)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_eq_of_mpullback_eq`:
  `{F, G}(p z) = {f, g}(i z)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_comp_of_mpullback_eq`: integral curves
  of `X_f` through `Z` project to integral curves of `X_F`.
* `TauCeti.SmoothTwoForm.IsMomentMap.exists_mfderiv_eq_and_mfderiv_eq_hamiltonianVectorField`,
  `TauCeti.SmoothTwoForm.IsMomentMap.poissonBracket_eq_of_mpullback_eq`: the specialization to
  invariant Hamiltonians on a level of a moment map.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130 (reduction of Hamiltonian dynamics).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 24 (reduction for invariant Hamiltonians).
* J. Marsden, T. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer, 1999,
  Section 1.2 and Chapter 10 (Poisson reduction of brackets).
-/

public section

noncomputable section

open Function
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M E' H' Q E₀ H₀ Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace Z] [ChartedSpace H₀ Z] [IsManifold I₀ ∞ Z]
  {σ : SmoothTwoForm I M} {η : SmoothTwoForm J Q} {i : Z → M} {p : Z → Q}
  (hi : ContMDiff I₀ I ∞ i) (hp : ContMDiff I₀ J ∞ p)
  (hpi : SmoothForm.mpullback p hp η = SmoothForm.mpullback i hi σ)
  {f g : M → ℝ} {F G : Q → ℝ} {X : (x : M) → TangentSpace I x} {z : Z}

include hpi

/-- **The Hamiltonian equation descends.** Let `p^* η = i^* σ`, let `X` be a Hamiltonian vector
field of `f` for `σ`, and let `f ∘ i = F ∘ p`. If `di Y = X(i z)`, then `dp Y` satisfies the
Hamiltonian equation of `F` on the image of `dp`: `η(dp Y, dp v) = dF(dp v)`. No nondegeneracy is
needed. -/
theorem eval₂_mfderiv_eq_mvfderiv_of_mpullback_eq (hX : σ.IsHamiltonianVectorField f X)
    (hfF : f ∘ i = F ∘ p) (hf : MDifferentiableAt I 𝓘(ℝ) f (i z))
    (hF : MDifferentiableAt J 𝓘(ℝ) F (p z)) {Y : TangentSpace I₀ z}
    (hY : mfderiv I₀ I i z Y = X (i z)) (v : TangentSpace I₀ z) :
    SmoothBundleForm.eval₂ η (p z) (mfderiv I₀ J p z Y) (mfderiv I₀ J p z v) =
      mvfderiv J F (p z) (mfderiv I₀ J p z v) := by
  -- Both sides are `σ(X(i z), di v) = df(di v) = d(f ∘ i)(v) = d(F ∘ p)(v)`.
  rw [← SmoothForm.eval₂_mpullback p hp, hpi, SmoothForm.eval₂_mpullback, hY,
    isHamiltonianVectorField_iff.1 hX,
    ← mvfderiv_comp_apply z hf ((hi z).mdifferentiableAt (by simp)), hfF,
    mvfderiv_comp_apply z hF ((hp z).mdifferentiableAt (by simp))]

namespace IsNondegenerate

variable [FiniteDimensional ℝ E'] (hη : η.IsNondegenerate)
include hη

/-- **Hamiltonian vector fields descend.** Let `p^* η = i^* σ` with `η` nondegenerate, let `X` be
a Hamiltonian vector field of `f` for `σ`, and let `f ∘ i = F ∘ p`. At a point `z` where `dp` is
surjective, a tangent vector `Y` with `di Y = X(i z)` projects to the Hamiltonian vector field of
`F`: `dp Y = X_F(p z)`. -/
theorem mfderiv_eq_hamiltonianVectorField_of_mpullback_eq (hX : σ.IsHamiltonianVectorField f X)
    (hfF : f ∘ i = F ∘ p) (hf : MDifferentiableAt I 𝓘(ℝ) f (i z))
    (hF : MDifferentiableAt J 𝓘(ℝ) F (p z)) (hsurj : Surjective (mfderiv I₀ J p z))
    {Y : TangentSpace I₀ z} (hY : mfderiv I₀ I i z Y = X (i z)) :
    mfderiv I₀ J p z Y = η.hamiltonianVectorField F (p z) := by
  refine (hη.isInvertible_flat (p z)).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  obtain ⟨v, rfl⟩ := hsurj w
  rw [flat_apply, flat_apply, hη.eval₂_hamiltonianVectorField,
    eval₂_mfderiv_eq_mvfderiv_of_mpullback_eq hi hp hpi hX hfF hf hF hY]

/-- **The bracket of reduced functions is the reduction of the bracket.** Let `p^* η = i^* σ` with
`σ` and `η` nondegenerate, and let `f ∘ i = F ∘ p` and `g ∘ i = G ∘ p`. At a point `z` where `dp`
is surjective and the Hamiltonian vector field of `g` at `i z` is tangent to `Z`, that is, lies in
the image of `di`, the Poisson brackets agree: `{F, G}(p z) = {f, g}(i z)`. -/
theorem poissonBracket_eq_of_mpullback_eq [FiniteDimensional ℝ E] (hσ : σ.IsNondegenerate)
    (hfF : f ∘ i = F ∘ p) (hgG : g ∘ i = G ∘ p) (hf : MDifferentiableAt I 𝓘(ℝ) f (i z))
    (hF : MDifferentiableAt J 𝓘(ℝ) F (p z)) (hg : MDifferentiableAt I 𝓘(ℝ) g (i z))
    (hG : MDifferentiableAt J 𝓘(ℝ) G (p z)) (hsurj : Surjective (mfderiv I₀ J p z))
    (htan : σ.hamiltonianVectorField g (i z) ∈ LinearMap.range (mfderiv I₀ I i z).toLinearMap) :
    η.poissonBracket F G (p z) = σ.poissonBracket f g (i z) := by
  obtain ⟨Y, hY⟩ := htan
  -- `{F, G} = dF(X_G) = dF(dp Y) = d(F ∘ p)(Y) = d(f ∘ i)(Y) = df(X_g) = {f, g}`.
  rw [hη.poissonBracket_eq_mvfderiv, hσ.poissonBracket_eq_mvfderiv,
    ← hη.mfderiv_eq_hamiltonianVectorField_of_mpullback_eq hi hp hpi
      (hσ.isHamiltonianVectorField_hamiltonianVectorField g) hgG hg hG hsurj hY,
    ← mvfderiv_comp_apply z hF ((hp z).mdifferentiableAt (by simp)), ← hfF,
    mvfderiv_comp_apply z hf ((hi z).mdifferentiableAt (by simp))]
  exact congrArg _ hY

/-- **Hamiltonian flows descend.** Let `p^* η = i^* σ` with `η` nondegenerate, let `X` be a
Hamiltonian vector field of `f` for `σ`, and let `f ∘ i = F ∘ p`. If a differentiable curve `γ` in
`Z` is carried by `i` to an integral curve of `X`, and `dp` is surjective along `γ`, then `p ∘ γ`
is an integral curve of the Hamiltonian vector field of `F`. -/
theorem isMIntegralCurve_comp_of_mpullback_eq (hX : σ.IsHamiltonianVectorField f X)
    (hfF : f ∘ i = F ∘ p) {γ : ℝ → Z} (hγ : ∀ t, MDifferentiableAt 𝓘(ℝ) I₀ γ t)
    (hiγ : IsMIntegralCurve (i ∘ γ) X) (hsurj : ∀ t, Surjective (mfderiv I₀ J p (γ t)))
    (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) f (i (γ t)))
    (hF : ∀ t, MDifferentiableAt J 𝓘(ℝ) F (p (γ t))) :
    IsMIntegralCurve (p ∘ γ) (η.hamiltonianVectorField F) := fun t ↦ by
  set Y : TangentSpace I₀ (γ t) := mfderiv 𝓘(ℝ) I₀ γ t 1
  -- The velocity `Y` of `γ` is a lift of `X`, by uniqueness of the derivative of `i ∘ γ`.
  have hY : mfderiv I₀ I i (γ t) Y = X (i (γ t)) := by
    have h := (((hi (γ t)).mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (hγ t).hasMFDerivAt).mfderiv.symm.trans (hiγ t).mfderiv
    simpa using congr($h 1)
  have hpY := hη.mfderiv_eq_hamiltonianVectorField_of_mpullback_eq hi hp hpi hX hfF (hf t) (hF t)
    (hsurj t) hY
  -- The derivative of `p ∘ γ` is determined by its value `dp Y` at `1`.
  refine (((hp (γ t)).mdifferentiableAt (by simp)).hasMFDerivAt.comp t
    (hγ t).hasMFDerivAt).congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
  have h₁ : η.hamiltonianVectorField F (p (γ t)) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (η.hamiltonianVectorField F (p (γ t))) 1 := by
    simp
  -- Both sides are `dp Y` up to unfolding the composition and the type of tangent vectors at `t`.
  exact hpY.trans h₁

end IsNondegenerate

/-! ### Invariant Hamiltonians on a level of a moment map -/

namespace IsMomentMap

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] {a : InfinitesimalAction 𝔤 I M}
  {μ : M → Module.Dual ℝ 𝔤} (h : σ.IsMomentMap a μ)
  (hrange : LinearMap.range (mfderiv I₀ I i z).toLinearMap = LinearMap.ker (h.differential (i z)))
include h hrange

/-- **Invariant Hamiltonians on a level.** Let `i : Z → M` have tangent images the kernels of the
differential of a moment map `μ`, as the inclusion of a level of `μ` does, let `p^* η = i^* σ` with
`η` nondegenerate, and let `f ∘ i = F ∘ p`. If the derivative of `f` at `i z` vanishes along every
generated vector field `ξ_M`, then a Hamiltonian vector field `X` of `f` lifts to a tangent vector
`Y` of `Z` at `z`, and wherever `dp` is surjective every such lift projects to the Hamiltonian
vector field of `F`. -/
theorem exists_mfderiv_eq_and_mfderiv_eq_hamiltonianVectorField [FiniteDimensional ℝ E']
    (hη : η.IsNondegenerate) (hX : σ.IsHamiltonianVectorField f X) (hfF : f ∘ i = F ∘ p)
    (hf : MDifferentiableAt I 𝓘(ℝ) f (i z)) (hF : MDifferentiableAt J 𝓘(ℝ) F (p z))
    (hsurj : Surjective (mfderiv I₀ J p z)) (hinv : ∀ ξ, mvfderiv I f (i z) (a ξ (i z)) = 0) :
    ∃ Y : TangentSpace I₀ z, mfderiv I₀ I i z Y = X (i z) ∧
      mfderiv I₀ J p z Y = η.hamiltonianVectorField F (p z) := by
  obtain ⟨Y, hY⟩ : X (i z) ∈ LinearMap.range (mfderiv I₀ I i z).toLinearMap :=
    hrange ▸ (h.mem_ker_differential_iff_of_isHamiltonianVectorField hX (i z)).2 hinv
  exact ⟨Y, hY, hη.mfderiv_eq_hamiltonianVectorField_of_mpullback_eq hi hp hpi hX hfF hf hF hsurj
    hY⟩

/-- **Reduction of Poisson brackets on a level.** Let `i : Z → M` have tangent images the kernels
of the differential of a moment map `μ`, as the inclusion of a level of `μ` does, and let
`p^* η = i^* σ` with `σ` and `η` nondegenerate. Let `f ∘ i = F ∘ p` and `g ∘ i = G ∘ p`, where the
derivative of `g` at `i z` vanishes along every generated vector field `ξ_M`. At a point `z` where
`dp` is surjective, `{F, G}(p z) = {f, g}(i z)`. -/
theorem poissonBracket_eq_of_mpullback_eq [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (hσ : σ.IsNondegenerate) (hη : η.IsNondegenerate) (hfF : f ∘ i = F ∘ p)
    (hgG : g ∘ i = G ∘ p) (hf : MDifferentiableAt I 𝓘(ℝ) f (i z))
    (hF : MDifferentiableAt J 𝓘(ℝ) F (p z)) (hg : MDifferentiableAt I 𝓘(ℝ) g (i z))
    (hG : MDifferentiableAt J 𝓘(ℝ) G (p z)) (hsurj : Surjective (mfderiv I₀ J p z))
    (hinv : ∀ ξ, mvfderiv I g (i z) (a ξ (i z)) = 0) :
    η.poissonBracket F G (p z) = σ.poissonBracket f g (i z) :=
  hη.poissonBracket_eq_of_mpullback_eq hi hp hpi hσ hfF hgG hf hF hg hG hsurj <| hrange ▸
    (h.mem_ker_differential_iff_of_isHamiltonianVectorField
      (hσ.isHamiltonianVectorField_hamiltonianVectorField g) (i z)).2 hinv

end IsMomentMap

end SmoothTwoForm

end TauCeti
