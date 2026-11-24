/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Analysis.Calculus.Conformal.Liouville
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Transitions between conformal charts

Let `φ` and `ψ` be partial diffeomorphisms from a manifold `M` into a real inner product space `F`.
Say that they are *conformally related* at a point `x` of both sources if the pulled-back inner
products agree up to a factor `ρ`:

`⟪Dψ(x) u, Dψ(x) v⟫ = ρ ⟪Dφ(x) u, Dφ(x) v⟫` for all tangent vectors `u`, `v` at `x`.

When `F` is nontrivial, such a factor is automatically positive
(`PartialDiffeomorph.pos_of_inner_mfderiv`).

This is the case for any two *conformal Euclidean charts* of a Riemannian metric `g`, that is,
charts in which `g` is a positive multiple of the pulled-back inner product of `F`, as produced
for a locally conformally flat metric by
`Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat.exists_partialDiffeomorph_ball`.

At such a point the transition `z ↦ ψ (φ⁻¹ z)` scales inner products by `ρ` at `φ x`
(`PartialDiffeomorph.inner_fderiv_comp_symm`), so it is conformal there
(`PartialDiffeomorph.conformalAt_comp_symm`). This holds in every dimension. In dimension at least
`3`, Liouville's theorem (`TauCeti.exists_eq_smul_linearIsometry_add_or_inversion_of_conformalAt`)
then makes the transition the restriction of a Möbius transformation: on a connected open subset
`W` of both sources on which `φ` and `ψ` are conformally related and `C³`, there are `r > 0`, a
linear isometry `A` of `F` and a vector `a` such that either `ψ = r • A φ + a` on `W`, or
`ψ = r • A (inversion b 1 φ) + a` on `W` for a point `b ∉ φ '' W`
(`PartialDiffeomorph.exists_eq_smul_linearIsometry_add_or_inversion_of_inner_mfderiv`). For the
conformal charts of a Riemannian metric, the conformal factors of the charts are automatically
positive (`Bundle.ContMDiffRiemannianMetric.pos_of_inner_eq_mul_inner_mfderiv`) and the
hypothesis is satisfied
(`Bundle.ContMDiffRiemannianMetric.exists_eq_smul_linearIsometry_add_or_inversion_of_inner_eq`).

This is the transition theorem for the conformal atlas of a locally conformally flat manifold of
dimension at least `3`: its conformal charts differ by Möbius transformations, which is what makes
the analytic continuation of a conformal chart along paths, and hence the developing map,
possible. In dimension `2` the transitions are only holomorphic or antiholomorphic.

## Main results

* `PartialDiffeomorph.inner_fderiv_comp_symm`: the transition between conformally related partial
  diffeomorphisms scales inner products by the relating factor.
* `PartialDiffeomorph.pos_of_inner_mfderiv`: the relating factor is positive when `F` is
  nontrivial.
* `PartialDiffeomorph.conformalAt_comp_symm`: such a transition is conformal.
* `PartialDiffeomorph.exists_eq_smul_linearIsometry_add_or_inversion_of_inner_mfderiv`: in
  dimension at least `3`, on a connected open set the transition is a similarity or a similarity
  composed with an inversion.
* `Bundle.ContMDiffRiemannianMetric.exists_eq_smul_linearIsometry_add_or_inversion_of_inner_eq`:
  the same for two conformal Euclidean charts of a Riemannian metric.
* `Bundle.ContMDiffRiemannianMetric.pos_of_inner_eq_mul_inner_mfderiv`: the conformal factor of a
  conformal Euclidean chart of a Riemannian metric is positive.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 10 (Theorem 10.4 and the developing map of a locally conformally flat manifold).
* R. Schoen and S.-T. Yau, *Conformally flat manifolds, Kleinian groups and scalar curvature*,
  Invent. Math. 92 (1988), 47–71.
-/

public section

open Bundle Set
open scoped ContDiff Manifold InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {n : WithTop ℕ∞}

namespace PartialDiffeomorph

/-- **Transitions between conformally related charts scale inner products.** If two partial
diffeomorphisms `φ`, `ψ` into a real inner product space `F` satisfy
`⟪Dψ(x) u, Dψ(x) v⟫ = ρ ⟪Dφ(x) u, Dφ(x) v⟫` at a point `x` of both sources, then the derivative
of the transition `z ↦ ψ (φ⁻¹ z)` at `φ x` multiplies inner products by `ρ`. -/
theorem inner_fderiv_comp_symm (φ ψ : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hn : n ≠ 0) {x : M}
    (hφ : x ∈ φ.source) (hψ : x ∈ ψ.source) {ρ : ℝ}
    (hρ : ∀ u v : TangentSpace I x,
      ⟪mfderiv I 𝓘(ℝ, F) ψ x u, mfderiv I 𝓘(ℝ, F) ψ x v⟫_ℝ =
        ρ * ⟪mfderiv I 𝓘(ℝ, F) φ x u, mfderiv I 𝓘(ℝ, F) φ x v⟫_ℝ) (u v : F) :
    ⟪fderiv ℝ (fun z ↦ ψ (φ.symm z)) (φ x) u, fderiv ℝ (fun z ↦ ψ (φ.symm z)) (φ x) v⟫_ℝ =
      ρ * ⟪u, v⟫_ℝ := by
  have hD (w : TangentSpace I x) :
      fderiv ℝ (fun z ↦ ψ (φ.symm z)) (φ x) (mfderiv I 𝓘(ℝ, F) φ x w) =
        mfderiv I 𝓘(ℝ, F) ψ x w := by
    rw [← φ.mfderiv_symm_trans_apply_mfderiv_apply ψ hn hφ hψ w, mfderiv_eq_fderiv, coe_trans]
    -- `mfderiv_eq_fderiv` states the identity through the identifications
    -- `NormedSpace.fromTangentSpace` of the tangent spaces of `F` with `F`, which are the identity.
    rfl
  obtain ⟨u', rfl⟩ := (φ.isInvertible_mfderiv hn hφ).surjective u
  obtain ⟨v', rfl⟩ := (φ.isInvertible_mfderiv hn hφ).surjective v
  rw [hD, hD]
  exact hρ u' v'

/-- **The factor relating two charts into a nontrivial space is positive.** If two partial
diffeomorphisms `φ`, `ψ` into a nontrivial real inner product space `F` satisfy
`⟪Dψ(x) u, Dψ(x) v⟫ = ρ ⟪Dφ(x) u, Dφ(x) v⟫` at a point `x` of the source of `ψ`, then `ρ > 0`. -/
theorem pos_of_inner_mfderiv [Nontrivial F] (φ ψ : PartialDiffeomorph I 𝓘(ℝ, F) M F n)
    (hn : n ≠ 0) {x : M} (hψ : x ∈ ψ.source) {ρ : ℝ}
    (hρ : ∀ u v : TangentSpace I x,
      ⟪mfderiv I 𝓘(ℝ, F) ψ x u, mfderiv I 𝓘(ℝ, F) ψ x v⟫_ℝ =
        ρ * ⟪mfderiv I 𝓘(ℝ, F) φ x u, mfderiv I 𝓘(ℝ, F) φ x v⟫_ℝ) :
    0 < ρ := by
  obtain ⟨w, hw⟩ := exists_ne (0 : F)
  obtain ⟨u, rfl⟩ := (ψ.isInvertible_mfderiv hn hψ).surjective w
  have hg : 0 < ⟪mfderiv I 𝓘(ℝ, F) ψ x u, mfderiv I 𝓘(ℝ, F) ψ x u⟫_ℝ := real_inner_self_pos.2 hw
  rw [hρ u u, real_inner_self_eq_norm_sq] at hg
  exact pos_of_mul_pos_left hg (sq_nonneg _)

/-- **Transitions between conformally related charts are conformal.** If two partial
diffeomorphisms `φ`, `ψ` into a real inner product space `F` satisfy
`⟪Dψ(x) u, Dψ(x) v⟫ = ρ ⟪Dφ(x) u, Dφ(x) v⟫` at a point `x` of both sources, then the transition
`z ↦ ψ (φ⁻¹ z)` is conformal at `φ x`. -/
theorem conformalAt_comp_symm (φ ψ : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hn : n ≠ 0) {x : M}
    (hφ : x ∈ φ.source) (hψ : x ∈ ψ.source) {ρ : ℝ}
    (hρ : ∀ u v : TangentSpace I x,
      ⟪mfderiv I 𝓘(ℝ, F) ψ x u, mfderiv I 𝓘(ℝ, F) ψ x v⟫_ℝ =
        ρ * ⟪mfderiv I 𝓘(ℝ, F) φ x u, mfderiv I 𝓘(ℝ, F) φ x v⟫_ℝ) :
    ConformalAt (fun z ↦ ψ (φ.symm z)) (φ x) := by
  cases subsingleton_or_nontrivial F
  · exact conformalAt_iff'.2 ⟨1, one_pos, fun u v ↦ by simp [Subsingleton.elim u 0]⟩
  · exact conformalAt_iff'.2
      ⟨ρ, φ.pos_of_inner_mfderiv ψ hn hψ hρ, φ.inner_fderiv_comp_symm ψ hn hφ hψ hρ⟩

/-- **Liouville's theorem for transitions between conformal charts.** Let `φ`, `ψ` be `C³`
partial diffeomorphisms from `M` into a real inner product space `F` of finite dimension at
least `3`, and let `W` be a connected open subset of both sources at each point `x` of which
`⟪Dψ(x) u, Dψ(x) v⟫ = ρ ⟪Dφ(x) u, Dφ(x) v⟫` for some `ρ`. Then `ψ` is a Möbius
transformation of `φ` on `W`: there are `r > 0`, a linear isometry `A` and a vector `a` such that
either `ψ x = r • A (φ x) + a` on `W`, or `ψ x = r • A (inversion b 1 (φ x)) + a` on `W` for
some point `b ∉ φ '' W`. -/
theorem exists_eq_smul_linearIsometry_add_or_inversion_of_inner_mfderiv [FiniteDimensional ℝ F]
    (φ ψ : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hF : 3 ≤ Module.finrank ℝ F) (hn : 3 ≤ n)
    {W : Set M} (hWo : IsOpen W) (hWc : IsConnected W) (hWφ : W ⊆ φ.source)
    (hWψ : W ⊆ ψ.source)
    (hρ : ∀ x ∈ W, ∃ ρ : ℝ, ∀ u v : TangentSpace I x,
      ⟪mfderiv I 𝓘(ℝ, F) ψ x u, mfderiv I 𝓘(ℝ, F) ψ x v⟫_ℝ =
        ρ * ⟪mfderiv I 𝓘(ℝ, F) φ x u, mfderiv I 𝓘(ℝ, F) φ x v⟫_ℝ) :
    ∃ (r : ℝ) (A : F →ₗᵢ[ℝ] F) (a : F), 0 < r ∧
      ((∀ x ∈ W, ψ x = r • A (φ x) + a) ∨
        ∃ b ∉ φ '' W, ∀ x ∈ W, ψ x = r • A (EuclideanGeometry.inversion b 1 (φ x)) + a) := by
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by norm_num) hn).ne'
  have hUo : IsOpen (φ '' W) := φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hWo hWφ
  have hUc : IsConnected (φ '' W) := hWc.image _ (φ.contMDiffOn.continuousOn.mono hWφ)
  -- On `φ '' W` the transition lands in `ψ.source` and is `C³`.
  have hUt : φ '' W ⊆ φ.target := image_subset_iff.2 fun x hx ↦ φ.map_source (hWφ hx)
  have hl : ∀ x ∈ W, φ.symm (φ x) = x := fun x hx ↦ φ.left_inv (hWφ hx)
  have hmaps : MapsTo φ.symm (φ '' W) ψ.source := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [hl x hx] using hWψ hx
  have hsmooth : ContDiffOn ℝ 3 (fun z ↦ ψ (φ.symm z)) (φ '' W) :=
    (contMDiffOn_iff_contDiffOn.1 (ψ.contMDiffOn.comp (φ.symm.contMDiffOn.mono hUt) hmaps)).of_le
      hn
  have hconf : ∀ z ∈ φ '' W, ConformalAt (fun z ↦ ψ (φ.symm z)) z := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ρ, hρx⟩ := hρ x hx
    exact φ.conformalAt_comp_symm ψ hn0 (hWφ hx) (hWψ hx) hρx
  obtain ⟨r, A, a, hr, h | ⟨b, hb, h⟩⟩ :=
    TauCeti.exists_eq_smul_linearIsometry_add_or_inversion_of_conformalAt hF rfl hsmooth hUo hUc
      hconf
  · refine ⟨r, A, a, hr, Or.inl fun x hx ↦ ?_⟩
    simpa only [hl x hx] using h (φ x) (mem_image_of_mem φ hx)
  · refine ⟨r, A, a, hr, Or.inr ⟨b, hb, fun x hx ↦ ?_⟩⟩
    simpa only [hl x hx] using h (φ x) (mem_image_of_mem φ hx)

end PartialDiffeomorph

namespace Bundle.ContMDiffRiemannianMetric

variable [IsManifold I 1 M] {k : ℕ∞ω}

/-- **The factor of a conformal chart is positive.** If a Riemannian metric `g` is a multiple
`g = c ⟪Dχ ·, Dχ ·⟫` of the pulled-back inner product along a partial diffeomorphism `χ` into a
nontrivial real inner product space at a point `x` of its source, then `c > 0`. -/
theorem pos_of_inner_eq_mul_inner_mfderiv [Nontrivial F]
    (g : ContMDiffRiemannianMetric I k E (fun x : M ↦ TangentSpace I x))
    (χ : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hn : n ≠ 0) {x : M} (hx : x ∈ χ.source) {c : ℝ}
    (hχ : ∀ u v : TangentSpace I x,
      g.inner x u v = c * ⟪mfderiv I 𝓘(ℝ, F) χ x u, mfderiv I 𝓘(ℝ, F) χ x v⟫_ℝ) :
    0 < c := by
  obtain ⟨w, hw⟩ := exists_ne (0 : F)
  obtain ⟨u, rfl⟩ := (χ.isInvertible_mfderiv hn hx).surjective w
  have hu : u ≠ 0 := by
    rintro rfl
    exact hw (map_zero _)
  have hg := g.pos x u hu
  rw [hχ u u, real_inner_self_eq_norm_sq] at hg
  exact pos_of_mul_pos_left hg (sq_nonneg _)

/-- **Liouville's theorem for the conformal charts of a Riemannian metric.** Let `g` be a
Riemannian metric on `M`, let `φ`, `ψ` be `C³` partial diffeomorphisms from `M` into a real
inner product space `F` of finite dimension at least `3`, and let `W` be a connected open subset
of both sources on which `g` is a multiple of the pulled-back inner product of `F` along each of
them: `g = c_φ ⟪Dφ ·, Dφ ·⟫` and `g = c_ψ ⟪Dψ ·, Dψ ·⟫` on `W`. Then there are `r > 0`, a linear
isometry `A` and a vector `a` such that either `ψ x = r • A (φ x) + a` on `W`, or
`ψ x = r • A (inversion b 1 (φ x)) + a` on `W` for some point `b ∉ φ '' W`. The factors `c_φ` and
`c_ψ` are automatically positive on `W` (`pos_of_inner_eq_mul_inner_mfderiv`). -/
theorem exists_eq_smul_linearIsometry_add_or_inversion_of_inner_eq [FiniteDimensional ℝ F]
    (g : ContMDiffRiemannianMetric I k E (fun x : M ↦ TangentSpace I x))
    (hF : 3 ≤ Module.finrank ℝ F) (hn : 3 ≤ n) {φ ψ : PartialDiffeomorph I 𝓘(ℝ, F) M F n}
    {W : Set M} (hWo : IsOpen W) (hWc : IsConnected W) (hWφ : W ⊆ φ.source)
    (hWψ : W ⊆ ψ.source) {cφ cψ : M → ℝ}
    (hφ : ∀ x ∈ W, ∀ u v : TangentSpace I x,
      g.inner x u v = cφ x * ⟪mfderiv I 𝓘(ℝ, F) φ x u, mfderiv I 𝓘(ℝ, F) φ x v⟫_ℝ)
    (hψ : ∀ x ∈ W, ∀ u v : TangentSpace I x,
      g.inner x u v = cψ x * ⟪mfderiv I 𝓘(ℝ, F) ψ x u, mfderiv I 𝓘(ℝ, F) ψ x v⟫_ℝ) :
    ∃ (r : ℝ) (A : F →ₗᵢ[ℝ] F) (a : F), 0 < r ∧
      ((∀ x ∈ W, ψ x = r • A (φ x) + a) ∨
        ∃ b ∉ φ '' W, ∀ x ∈ W, ψ x = r • A (EuclideanGeometry.inversion b 1 (φ x)) + a) := by
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by norm_num) hn).ne'
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  refine PartialDiffeomorph.exists_eq_smul_linearIsometry_add_or_inversion_of_inner_mfderiv φ ψ hF
    hn hWo hWc hWφ hWψ fun x hx ↦ ⟨cφ x / cψ x, fun u v ↦ ?_⟩
  rw [div_mul_eq_mul_div, ← hφ x hx, hψ x hx,
    mul_div_cancel_left₀ _ (g.pos_of_inner_eq_mul_inner_mfderiv ψ hn0 (hWψ hx) (hψ x hx)).ne']

end Bundle.ContMDiffRiemannianMetric
