/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian
public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The maximum principle for the Hermitian part of a family of two-forms

Let `V` be a finite-dimensional real inner product space with an orthogonal almost complex
structure `J`, and let `F` be a `C²` family of two-forms `F y ∈ ⋀² V` parametrized by a compact
boundaryless Riemannian manifold `M`. The Hermitian part of `F y` is the symmetric bilinear form
`B_y(v, w) = (F y (v, J w) + F y (w, J v)) / 2`
(`TauCeti.AlmostComplexStructure.hermitianForm`), with `B_y(v, v) = F y (v, J v)`. Its least
eigenvalue `λ(y)`, the least value of `B_y(v, v)` on the unit sphere, is continuous in `y` but not
differentiable where eigenvalues cross.

Hamilton's maximum principle for symmetric tensors bounds `λ` from below without differentiating
it. At a point `y` and a unit vector `v` attaining `λ(y)`, the smooth function `z ↦ B_z(v, v)` lies
above `λ` and touches it at `y`, so at a minimum of `λ` it has a local minimum and nonnegative
Laplacian (`TauCeti.Manifold.forall_le_apply_self_of_laplaceBeltrami_neg`). Hence, if
`Δ (z ↦ B_z(v, v)) < 0` at every such `(y, v)` with `λ(y) < -C`, then `B_y ≥ -C g` for every `y`
(`TauCeti.SeibergWitten.forall_le_hermitianForm_apply_self_of_laplaceBeltrami_neg`).

In dimension four, for the complex orientation, `λ = c - ‖F⁻‖ / √2` with `c = ⟪ω, F⟫ / 2` and
`F⁻ = (F - ⋆F) / 2` (`TauCeti.AlmostComplexStructure.isLeast_hermitianForm_apply_self`), and a lower
bound `B ≥ -C g` is the bound `‖F⁻‖ ≤ √2 (c + C)` on the anti-self-dual part. Combining the two
gives that bound from a differential inequality at the unit eigenvectors of `λ`
(`TauCeti.SeibergWitten.norm_smul_sub_hodgeStar_le_of_laplaceBeltrami_neg`).

Taubes's estimate for the anti-self-dual curvature of solutions of the large-parameter
Seiberg–Witten equations on a symplectic four-manifold has this shape, with `F` the real curvature
form `i F_a` of the connection on the twisting line, and there the lower bound `B ≥ -C g` turns
the formula for `c` into the refined bound `|F_a⁻| ≤ (r / (4 √2)) w₊ + O(1)`
(`TauCeti.SeibergWitten.norm_smul_sub_hodgeStar_le`). The results here only cover a family of
forms on one fixed inner product space `V` with a constant `J`, that is, the case of a global
unitary frame in which `J` is constant. A general symplectic four-manifold has no such frame, and
in a frame the Laplacian of the components of `F` differs from the rough Laplacian of the bundle
by connection terms; applying the estimate there needs the intrinsic version with the rough
Laplacian. For a field of symmetric endomorphisms of the tangent bundle, such as `B` read through
the metric, that version is
`TauCeti.Manifold.forall_le_inner_apply_self_of_inner_roughLaplacian_pos`. The differential
inequality at the eigenvectors of `λ`, which comes from the curvature, Dirac and Weitzenböck
equations, is a hypothesis.

## Main results

* `TauCeti.SeibergWitten.forall_le_hermitianForm_apply_self_of_laplaceBeltrami_neg`: the lower
  bound `B ≥ -C g` from the sign of `Δ (z ↦ B_z(v, v))` at the unit eigenvectors `v` of the least
  eigenvalue, in any dimension.
* `TauCeti.SeibergWitten.norm_smul_sub_hodgeStar_le_of_laplaceBeltrami_neg`: in dimension four,
  the resulting bound `‖F⁻‖ ≤ √2 (c + C)` on the anti-self-dual part.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 4.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Bundle Filter Metric Module exteriorPower
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti.SeibergWitten

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J : AlmostComplexStructure V} {F : M → ⋀[ℝ]^2 V}

/-- **Hamilton's maximum principle for the Hermitian part of a family of two-forms.** On a compact
boundaryless Riemannian manifold `M`, let `F` be a `C²` family of two-forms on `V` and `B_y` the
Hermitian part of `F y`. Suppose that for every point `y` and every unit vector `v` minimizing
`B_y(w, w)` over the unit vectors `w`, with `B_y(v, v) < -C`, the function `z ↦ B_z(v, v)` has
negative Laplace–Beltrami operator at `y`. Then `B_y ≥ -C g` for every `y`, which is the form
`∀ v, -C ‖v‖² ≤ B_y(v, v)` in which the anti-self-dual bounds of
`TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature` take it. -/
theorem forall_le_hermitianForm_apply_self_of_laplaceBeltrami_neg [CompactSpace M]
    (hF : ContMDiff I 𝓘(ℝ, ⋀[ℝ]^2 V) 2 F) {C : ℝ}
    (hΔ : ∀ y, ∀ v : V, ‖v‖ = 1 →
      (∀ w : V, ‖w‖ = 1 → J.hermitianForm (F y) v v ≤ J.hermitianForm (F y) w w) →
      J.hermitianForm (F y) v v < -C →
      laplaceBeltrami I (fun z ↦ J.hermitianForm (F z) v v) y < 0)
    (y : M) : ∀ v : V, -C * ‖v‖ ^ 2 ≤ J.hermitianForm (F y) v v := by
  -- `(z, w) ↦ B_z(w, w) = ⟪F z, w ∧ J w⟫` is jointly continuous.
  have hc : Continuous fun p : M × V ↦ J.hermitianForm (F p.1) p.2 p.2 := by
    have hι : Continuous fun w : V ↦ ιMulti ℝ 2 ![w, J w] :=
      (ιMulti ℝ 2 : V [⋀^Fin 2]→ₗ[ℝ] ⋀[ℝ]^2 V).toMultilinearMap.continuous_of_finiteDimensional.comp
        (by have := J.toLinearMap.continuous_of_finiteDimensional; fun_prop)
    simp only [AlmostComplexStructure.hermitianForm_apply_self]
    exact (hF.continuous.comp continuous_fst).inner (hι.comp continuous_snd)
  -- Each `z ↦ B_z(w, w) = ⟪ιMulti ℝ 2 ![w, J w], F z⟫` is `C²`.
  have hB : ∀ w, ContMDiff I 𝓘(ℝ) 2 fun z ↦ J.hermitianForm (F z) w w := fun w ↦ by
    have hBw : (fun z ↦ J.hermitianForm (F z) w w) =
        fun z ↦ innerSL ℝ (ιMulti ℝ 2 ![w, J w]) (F z) := by
      ext z
      simp [real_inner_comm]
    rw [hBw]
    exact (innerSL ℝ (ιMulti ℝ 2 ![w, J w])).contMDiff.comp hF
  exact forall_le_apply_self_of_laplaceBeltrami_neg (B := fun z ↦ J.hermitianForm (F z)) hc hB hΔ y

/-! ### Dimension four -/

section Four

variable {e : OrthonormalBasis (Fin 4) ℝ V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)
include h₀ h₂ he

/-- **The anti-self-dual bound from the maximum principle.** On a compact boundaryless Riemannian
manifold `M`, let `F` be a `C²` family of two-forms on an oriented four-dimensional `V` whose
orthogonal almost complex structure `J` induces the orientation. Write `c = ⟪ω, F⟫ / 2` and
`F⁻ = (F - ⋆F) / 2`, so that the least eigenvalue of the Hermitian part `B_y` of `F y` is
`c y - ‖F⁻ y‖ / √2`. Suppose that wherever this eigenvalue is below `-C`, every unit eigenvector `v`
of it gives `Δ (z ↦ B_z(v, v)) < 0` at `y`. Then `‖F⁻ y‖ ≤ √2 (c y + C)` for every `y`. -/
theorem norm_smul_sub_hodgeStar_le_of_laplaceBeltrami_neg [CompactSpace M]
    (hF : ContMDiff I 𝓘(ℝ, ⋀[ℝ]^2 V) 2 F) {C : ℝ}
    (hΔ : ∀ y, ∀ v : V, ‖v‖ = 1 →
      J.hermitianForm (F y) v v =
        ⟪J.kahlerForm, F y⟫ / 2 - ‖(2⁻¹ : ℝ) • (F y - o.hodgeStar hkl (F y))‖ / √2 →
      ⟪J.kahlerForm, F y⟫ / 2 - ‖(2⁻¹ : ℝ) • (F y - o.hodgeStar hkl (F y))‖ / √2 < -C →
      laplaceBeltrami I (fun z ↦ J.hermitianForm (F z) v v) y < 0)
    (y : M) :
    ‖(2⁻¹ : ℝ) • (F y - o.hodgeStar hkl (F y))‖ ≤ √2 * (⟪J.kahlerForm, F y⟫ / 2 + C) := by
  refine AlmostComplexStructure.norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm_apply_self
    h₀ h₂ hkl he (F y) (forall_le_hermitianForm_apply_self_of_laplaceBeltrami_neg hF
      (fun x v hv hmin hlt ↦ ?_) y)
  -- A minimizing unit vector attains the least eigenvalue `c x - ‖F⁻ x‖ / √2`.
  have hleast : IsLeast ((fun w ↦ J.hermitianForm (F x) w w) '' sphere 0 1)
      (J.hermitianForm (F x) v v) :=
    ⟨Set.mem_image_of_mem _ (mem_sphere_zero_iff_norm.2 hv), by
      rintro _ ⟨w, hw, rfl⟩
      exact hmin w (mem_sphere_zero_iff_norm.1 hw)⟩
  have heq := hleast.unique
    (AlmostComplexStructure.isLeast_hermitianForm_apply_self h₀ h₂ hkl he (F x))
  exact hΔ x v hv heq (heq ▸ hlt)

end Four

end TauCeti.SeibergWitten
