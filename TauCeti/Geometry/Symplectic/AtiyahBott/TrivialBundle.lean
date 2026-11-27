/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Gauge.Curvature
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Nondegenerate

/-!
# The Atiyah–Bott moment map of the trivial bundle with a nonabelian structure group

Let `M` be a closed oriented surface and let `P = M × K` be the trivial principal bundle with
structure group a Lie group `K`, with Lie algebra `𝔨`. The connections on `P` are the operators
`d + A` for the `𝔨`-valued `1`-forms `A`, so the space of connections is the affine space
`Ω¹(M; 𝔨)`, and the Lie algebra of the gauge group `C^∞(M, K)` is `C^∞(M, 𝔨)`. This file develops
the Atiyah–Bott description of the infinitesimal gauge action on this affine space as a
Hamiltonian action. The case `K = U(1)` is
`TauCeti.Geometry.Symplectic.AtiyahBott.Circle.Basic`, whose form is the one of `𝔨 = ℝ` here.

The Lie algebra enters through two continuous bilinear maps on a normed space `𝔨`: its bracket
`β : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨`, `[a, b] = β a b`, and a bilinear form `B : 𝔨 →L[ℝ] 𝔨 →L[ℝ] ℝ`, as in
`TauCeti.bracketWedge`. Each statement assumes only the identities it uses: skew-symmetry of `β`,
the Leibniz form `[a, [b, c]] = [[a, b], c] + [b, [a, c]]` of the Jacobi identity, symmetry of
`B`, its `ad`-invariance `B([u, v], w) = B(u, [v, w])` and its nondegeneracy. The bracket of a
compact Lie algebra and an `Ad`-invariant inner product satisfy all of them. Wedge products of
`𝔨`-valued forms are paired wedges `SmoothForm.wedgeWith`, by `β` for `[a ∧ b]` and by `B` for
`B(a ∧ b)`.

* **Covariant derivatives and curvature.** These are developed in
  `TauCeti.Geometry.Manifold.DifferentialForm.Gauge.Curvature`: the covariant derivatives
  `d_A ξ = dξ + [A, ξ]` (`TauCeti.gaugeCovariantDeriv`) and `d_A b = db + [A ∧ b]`
  (`TauCeti.gaugeCovariantExtDeriv`), the curvature `F_A = dA + ½ [A ∧ A]`
  (`TauCeti.gaugeCurvature`), its expansion `F_(A + t b) = F_A + t d_A b + (t² / 2) [b ∧ b]`
  along a line of connections (`TauCeti.gaugeCurvature_add_smul`), and
  `d_A (d_A η) = [F_A, η]` (`TauCeti.gaugeCovariantExtDeriv_gaugeCovariantDeriv`).
* **The symplectic form.** `Ω(a, b) = ∫_M B(a ∧ b)` (`TauCeti.atiyahBottFormWith`) is a bilinear
  form on `Ω¹(M; 𝔨)`, alternating for a symmetric `B` (`TauCeti.atiyahBottFormWith_isAlt`) and
  weakly nondegenerate for a symmetric nondegenerate `B`
  (`TauCeti.atiyahBottFormWith_nondegenerate`): a nonzero `a` has a nonzero real component
  `B(a, z)`, which pairs nontrivially with some real `1`-form. It does not depend on the base
  connection. For `𝔨 = ℝ` with `B` the product it is the form `TauCeti.atiyahBottForm` of the
  circle bundle.
* **The moment map.** The infinitesimal generator of `ξ ∈ C^∞(M, 𝔨)` at the connection `A` is
  `ξ_A = -d_A ξ = [ξ, A] - dξ`: for a matrix group `K` this is the velocity at `t = 0` of the gauge
  transformations `g · A = g A g⁻¹ - (dg) g⁻¹` along `g = exp (t ξ)`
  (`TauCeti.hasDerivAt_mgaugeAction_gaugeExp_smul_apply`). The curvature pairing
  `⟨μ(A), ξ⟩ = ∫_M B(F_A, ξ)` (`TauCeti.atiyahBottMomentWith`) is a moment map for these
  generators. By Stokes' theorem on the closed surface and the invariance of `B`,
  `∫_M B(d_A b, ξ) = Ω(ξ_A, b)`
  (`TauCeti.atiyahBottFormWith_neg_gaugeCovariantDeriv`). Together with the expansion of the
  curvature this gives the exact expansion
  `⟨μ(A + t b), ξ⟩ = ⟨μ(A), ξ⟩ + t Ω(ξ_A, b) + (t² / 2) ∫_M B([b ∧ b], ξ)`
  (`TauCeti.atiyahBottMomentWith_add_smul`), hence the moment map equation `ι_(ξ_A) Ω = dμ_ξ`
  in directional form (`TauCeti.hasDerivAt_atiyahBottMomentWith_add_smul`). The quadratic term
  vanishes for an abelian `𝔨`, where `μ` is affine in `A`.
* **Equivariance.** The generators pair to the moment map of the pointwise bracket,
  `Ω(ξ_A, η_A) = ⟨μ(A), [ξ, η]⟩`
  (`TauCeti.atiyahBottFormWith_neg_gaugeCovariantDeriv_neg_gaugeCovariantDeriv`), from
  `d_A (d_A η) = [F_A, η]` and the invariance of `B`: the moment cocycle vanishes, so `μ` is
  infinitesimally equivariant.
* **The flat connections.** For a nondegenerate `B`, `μ(A) = 0` exactly when `F_A = 0`
  (`TauCeti.atiyahBottMomentWith_eq_zero_iff`): the zero level is the space of flat connections.

Everything is stated in directional form on the affine space `Ω¹(M; 𝔨)`, with no manifold
structure on the space of connections. The action of the elements of the gauge group, for `𝔨` a
normed algebra with its commutator, and the group-level invariance and equivariance statements are
in `TauCeti.Geometry.Symplectic.AtiyahBott.GaugeGroup`; nontrivial principal bundles are not
treated here.

## Main definitions

* `TauCeti.atiyahBottFormWith`: the Atiyah–Bott form `Ω(a, b) = ∫_M B(a ∧ b)`.
* `TauCeti.atiyahBottMomentWith`: the curvature moment map `⟨μ(A), ξ⟩ = ∫_M B(F_A, ξ)`.

## Main results

* `TauCeti.atiyahBottFormWith_nondegenerate`: `Ω` is weakly nondegenerate.
* `TauCeti.hasDerivAt_atiyahBottMomentWith_add_smul`: the moment map equation.
* `TauCeti.atiyahBottFormWith_neg_gaugeCovariantDeriv_neg_gaugeCovariantDeriv`: infinitesimal
  equivariance.
* `TauCeti.atiyahBottMomentWith_eq_zero_iff`: the zero level is the flat connections.

## References

* M. F. Atiyah and R. Bott, *The Yang–Mills equations over Riemann surfaces*, Philos. Trans.
  Roy. Soc. London Ser. A 308 (1983), 523–615 (the symplectic form on the space of connections
  and the curvature as its moment map).
* E. Meinrenken, *Symplectic geometry*, lecture notes (2000), Theorem 7.46 (the trivial bundle).
-/

public section

noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M 𝔨 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [NormedAddCommGroup 𝔨] [NormedSpace ℝ 𝔨]
  (β : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨)

/-! ### The Atiyah–Bott form -/

variable (B : 𝔨 →L[ℝ] 𝔨 →L[ℝ] ℝ) [FiniteDimensional ℝ E] [CompactSpace M]
  (o : Manifold.Orientation I M (Fin 2))

/-- The **Atiyah–Bott form** `Ω(a, b) = ∫_M B(a ∧ b)` on the tangent space `Ω¹(M; 𝔨)` of the
space of connections of the trivial bundle over the closed oriented surface `M`, where `B` is a
bilinear form on `𝔨`. It does not depend on the base connection. When `B` is symmetric and
nondegenerate it is symplectic, that is alternating (`TauCeti.atiyahBottFormWith_isAlt`) and
weakly nondegenerate (`TauCeti.atiyahBottFormWith_nondegenerate`). -/
def atiyahBottFormWith : LinearMap.BilinForm ℝ (SmoothForm I M 𝔨 1) :=
  (SmoothForm.wedgeWith B).compr₂ (SmoothForm.integralTopFormₗ o)

@[simp]
theorem atiyahBottFormWith_apply (a b : SmoothForm I M 𝔨 1) :
    atiyahBottFormWith B o a b = integralTopForm o (RoughForm.wedgeWith B a.val b.val) := by
  rw [atiyahBottFormWith, LinearMap.compr₂_apply, SmoothForm.integralTopFormₗ_apply,
    SmoothForm.coe_wedgeWith]

/-- The Atiyah–Bott form of a symmetric bilinear form `B` is antisymmetric. -/
theorem atiyahBottFormWith_swap (hB : ∀ u v, B u v = B v u) (a b : SmoothForm I M 𝔨 1) :
    atiyahBottFormWith B o b a = -atiyahBottFormWith B o a b := by
  rw [atiyahBottFormWith, LinearMap.compr₂_apply, LinearMap.compr₂_apply,
    SmoothForm.wedgeWith_comm_one_one B hB, map_neg]

/-- The Atiyah–Bott form of a symmetric bilinear form `B` is alternating. -/
theorem atiyahBottFormWith_isAlt (hB : ∀ u v, B u v = B v u) :
    (atiyahBottFormWith B o).IsAlt := fun a ↦ by
  have h := atiyahBottFormWith_swap B o hB a a
  linarith

/-! ### The curvature moment map -/

/-- The **curvature moment map** of the infinitesimal gauge action on the connections `d + A` of
the trivial bundle: the pairing `⟨μ(A), ξ⟩ = ∫_M B(F_A, ξ)` of the curvature
`F_A = dA + ½ [A ∧ A]` with an element `ξ` of the Lie algebra `C^∞(M, 𝔨)` of the gauge group. -/
def atiyahBottMomentWith (A : SmoothForm I M 𝔨 1) : SmoothForm I M 𝔨 0 →ₗ[ℝ] ℝ :=
  (SmoothForm.integralTopFormₗ o).comp (SmoothForm.wedgeWith B (gaugeCurvature β A))

@[simp]
theorem atiyahBottMomentWith_apply (A : SmoothForm I M 𝔨 1) (ξ : SmoothForm I M 𝔨 0) :
    atiyahBottMomentWith β B o A ξ =
      integralTopForm o (RoughForm.wedgeWith B (gaugeCurvature β A).val ξ.val) := by
  rw [atiyahBottMomentWith, LinearMap.comp_apply, SmoothForm.integralTopFormₗ_apply,
    SmoothForm.coe_wedgeWith]

/-! ### Nondegeneracy -/

variable [T2Space M]

/-- **The Atiyah–Bott form is weakly nondegenerate** when `B` is symmetric and nondegenerate:
if `Ω(a, b) = 0` for every `b`, then `a = 0`, and likewise in the second argument. -/
theorem atiyahBottFormWith_nondegenerate (hB : ∀ u v, B u v = B v u)
    (hB' : ∀ u, (∀ z, B u z = 0) → u = 0) : (atiyahBottFormWith B o).Nondegenerate := by
  have hleft : LinearMap.SeparatingLeft (atiyahBottFormWith B o) := fun a ha ↦ by
    by_contra hne
    obtain ⟨b, hb⟩ := SmoothForm.exists_integralTopForm_wedgeWith_ne_zero o
      (show 1 + 1 = 2 from rfl) hB' (isClosed_tsupport _).isCompact hne
    have h := ha b
    rw [atiyahBottFormWith_apply] at h
    exact hb (by rwa [SmoothForm.cast_refl, SmoothForm.coe_wedgeWith])
  refine ⟨hleft, fun b hb ↦ hleft b fun a ↦ ?_⟩
  rw [atiyahBottFormWith_swap B o hB, hb, neg_zero]

/-- **The zero level of the moment map is the flat connections**: for a nondegenerate `B`,
`μ(A) = 0` exactly when the curvature `F_A` vanishes. -/
theorem atiyahBottMomentWith_eq_zero_iff (hB' : ∀ u, (∀ z, B u z = 0) → u = 0)
    {A : SmoothForm I M 𝔨 1} : atiyahBottMomentWith β B o A = 0 ↔ gaugeCurvature β A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hne
    obtain ⟨ξ, hξ⟩ := SmoothForm.exists_integralTopForm_wedgeWith_ne_zero o
      (show 2 + 0 = 2 from rfl) hB' (isClosed_tsupport _).isCompact hne
    have hμ := LinearMap.congr_fun h ξ
    rw [atiyahBottMomentWith_apply, LinearMap.zero_apply] at hμ
    exact hξ (by rwa [SmoothForm.cast_refl, SmoothForm.coe_wedgeWith])
  · rw [atiyahBottMomentWith, h, map_zero, LinearMap.comp_zero]

/-! ### The moment map equation and equivariance -/

variable [BoundarylessManifold I M]

/-- **Integration by parts against the covariant derivative.** For an `ad`-invariant symmetric
bilinear form `B` and a skew-symmetric bracket, `∫_M B(d_A b, ξ) = Ω(ξ_A, b)` for the
infinitesimal generator `ξ_A = -d_A ξ` of the gauge action. -/
theorem atiyahBottFormWith_neg_gaugeCovariantDeriv (hB : ∀ u v, B u v = B v u)
    (hBβ : ∀ u v w, B (β u v) w = B u (β v w)) (hβ : ∀ a b, β a b = -β b a)
    (A b : SmoothForm I M 𝔨 1) (ξ : SmoothForm I M 𝔨 0) :
    atiyahBottFormWith B o (-gaugeCovariantDeriv β A ξ) b =
      SmoothForm.integralTopFormₗ o
        (SmoothForm.wedgeWith B (gaugeCovariantExtDeriv β A b) ξ) := by
  have hpt : SmoothForm.wedgeWith B (gaugeCovariantExtDeriv β A b) ξ =
      mextDerivₗ I 1 (SmoothForm.wedgeWith B b ξ) +
        SmoothForm.wedgeWith B (-gaugeCovariantDeriv β A ξ) b := by
    refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
    simp only [SmoothBundleForm.eval₂_apply, Submodule.coe_add, Pi.add_apply,
      ContinuousAlternatingMap.add_apply, mextDerivₗ_apply, SmoothForm.coe_wedgeWith,
      SmoothForm.mextDeriv_wedgeWith_apply_one_zero, RoughForm.wedgeWith_apply_zero_right,
      RoughForm.wedgeWith_apply_one_one, gaugeCovariantExtDeriv_val, Submodule.coe_neg,
      Pi.neg_apply, ContinuousAlternatingMap.neg_apply, LinearMap.neg_apply,
      gaugeCovariantDeriv_val, map_add, map_sub, map_neg, add_apply, sub_apply, hBβ,
      hβ (ξ.val x 0)]
    linear_combination hB (b.val x ![v]) (mextDeriv ξ.val x ![w]) -
      hB (b.val x ![w]) (mextDeriv ξ.val x ![v])
  have hS : SmoothForm.integralTopFormₗ o (mextDerivₗ I 1 (SmoothForm.wedgeWith B b ξ)) = 0 := by
    rw [SmoothForm.integralTopFormₗ_apply, mextDerivₗ_apply]
    exact integralTopForm_mextDeriv_eq_zero (n := 1) o
      ((SmoothForm.wedgeWith B b ξ).isSmoothForm.of_le (by simp)) (isClosed_tsupport _).isCompact
  rw [hpt, map_add, hS, zero_add, atiyahBottFormWith, LinearMap.compr₂_apply]

/-- **The moment map along a line of connections.** For an `ad`-invariant symmetric bilinear
form `B` and a skew-symmetric bracket,
`⟨μ(A + t b), ξ⟩ = ⟨μ(A), ξ⟩ + t Ω(ξ_A, b) + (t² / 2) ∫_M B([b ∧ b], ξ)`,
where `ξ_A = -d_A ξ` is the infinitesimal generator of the gauge action. -/
theorem atiyahBottMomentWith_add_smul (hB : ∀ u v, B u v = B v u)
    (hBβ : ∀ u v w, B (β u v) w = B u (β v w)) (hβ : ∀ a b, β a b = -β b a)
    (A b : SmoothForm I M 𝔨 1) (t : ℝ) (ξ : SmoothForm I M 𝔨 0) :
    atiyahBottMomentWith β B o (A + t • b) ξ =
      atiyahBottMomentWith β B o A ξ + t * atiyahBottFormWith B o (-gaugeCovariantDeriv β A ξ) b +
        t ^ 2 / 2 *
          SmoothForm.integralTopFormₗ o
            (SmoothForm.wedgeWith B (SmoothForm.wedgeWith β b b) ξ) := by
  simp only [atiyahBottFormWith_neg_gaugeCovariantDeriv β B o hB hBβ hβ, atiyahBottMomentWith,
    LinearMap.comp_apply, gaugeCurvature_add_smul β hβ, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]

/-- **The moment map equation** `ι_(ξ_A) Ω = dμ_ξ`, in directional form: along the line `A + t b`
through any connection `A`, the derivative of `⟨μ, ξ⟩` at `t = 0` is `Ω(ξ_A, b)`, where
`ξ_A = -d_A ξ` is the infinitesimal generator of the gauge action. -/
theorem hasDerivAt_atiyahBottMomentWith_add_smul (hB : ∀ u v, B u v = B v u)
    (hBβ : ∀ u v w, B (β u v) w = B u (β v w)) (hβ : ∀ a b, β a b = -β b a)
    (A b : SmoothForm I M 𝔨 1) (ξ : SmoothForm I M 𝔨 0) :
    HasDerivAt (fun t : ℝ ↦ atiyahBottMomentWith β B o (A + t • b) ξ)
      (atiyahBottFormWith B o (-gaugeCovariantDeriv β A ξ) b) 0 := by
  simp_rw [atiyahBottMomentWith_add_smul β B o hB hBβ hβ]
  set c₁ := atiyahBottFormWith B o (-gaugeCovariantDeriv β A ξ) b
  set c₂ := SmoothForm.integralTopFormₗ o (SmoothForm.wedgeWith B (SmoothForm.wedgeWith β b b) ξ)
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const c₁).const_add
    (atiyahBottMomentWith β B o A ξ)).add (((hasDerivAt_pow 2 (0 : ℝ)).div_const 2).mul_const c₂)
  convert h using 1
  · funext t
    simp only [Pi.add_apply, id, mul_comm t]
  · simp

/-- **Infinitesimal equivariance of the moment map.** For an `ad`-invariant symmetric bilinear
form `B` and a Lie bracket `β`, the Atiyah–Bott form pairs the infinitesimal generators
`ξ_A = -d_A ξ` and `η_A = -d_A η` to the moment map of the pointwise bracket:
`Ω(ξ_A, η_A) = ⟨μ(A), [ξ, η]⟩`, that is, the moment cocycle vanishes. -/
theorem atiyahBottFormWith_neg_gaugeCovariantDeriv_neg_gaugeCovariantDeriv
    (hB : ∀ u v, B u v = B v u) (hBβ : ∀ u v w, B (β u v) w = B u (β v w))
    (hβ : ∀ a b, β a b = -β b a) (hJ : ∀ a b c, β a (β b c) = β (β a b) c + β b (β a c))
    (A : SmoothForm I M 𝔨 1) (ξ η : SmoothForm I M 𝔨 0) :
    atiyahBottFormWith B o (-gaugeCovariantDeriv β A ξ) (-gaugeCovariantDeriv β A η) =
      atiyahBottMomentWith β B o A (SmoothForm.wedgeWith β ξ η) := by
  have hpt : -SmoothForm.wedgeWith B (SmoothForm.wedgeWith β (gaugeCurvature β A) η) ξ =
      SmoothForm.wedgeWith B (gaugeCurvature β A) (SmoothForm.wedgeWith β ξ η) :=
    SmoothBundleForm.ext_eval₂ fun x v w ↦ by
      simp only [SmoothBundleForm.eval₂_apply, Submodule.coe_neg, Pi.neg_apply,
        ContinuousAlternatingMap.neg_apply, SmoothForm.wedgeWith_apply_zero_right, hBβ,
        hβ (η.val x 0), map_neg, neg_neg]
      rw [SmoothForm.wedgeWith_apply_zero_right, SmoothForm.wedgeWith_apply_zero_right]
  rw [map_neg, atiyahBottFormWith_neg_gaugeCovariantDeriv β B o hB hBβ hβ,
    gaugeCovariantExtDeriv_gaugeCovariantDeriv β hβ hJ, ← map_neg, hpt, atiyahBottMomentWith,
    LinearMap.comp_apply]

end TauCeti
