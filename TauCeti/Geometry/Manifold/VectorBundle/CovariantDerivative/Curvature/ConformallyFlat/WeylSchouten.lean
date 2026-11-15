/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Chart
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.RadialContraction
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Isometry.ConformalCurvature
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Divergence
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Solvability

/-!
# The Weyl–Schouten theorem on smooth Riemannian manifolds

This file proves local solvability of the conformal flattening equation on smooth Riemannian
manifolds — including smooth dependence on the initial value and gradient — and deduces the
Weyl–Schouten characterization of locally conformally flat metrics in dimension at least three:

* In dimension `n ≥ 4`, a smooth Riemannian metric `g` on a boundaryless manifold is locally
  conformally flat if and only if its Weyl tensor vanishes everywhere.
* In dimension `n = 3` (where the Weyl tensor vanishes identically), `g` is locally conformally
  flat if and only if its Cotton tensor vanishes everywhere.

At an interior point `x₀` where the Weyl and Cotton tensors vanish on a neighbourhood, radial
contraction (`TauCeti.exists_diffeomorph_modelSpace_of_isInteriorPoint`) produces an open
neighbourhood `W` of `x₀` diffeomorphic to the whole model space `E` on which both tensors vanish.
Pushing the restricted metric `g|_W` forward to `E` makes the diffeomorphism `Φ : W → E` and the
inclusion `W → M` local Riemannian isometries. By naturality of the Weyl and Cotton tensors under
local Riemannian isometries (`TauCeti.IsLocalRiemannianIsometry`), the model-space smooth-family
existence theorem (`TauCeti.Manifold.exists_contMDiff_hessian_eq_family_model_space`) applies on
`E`, and its compactly supported solution family extends by zero outside `W` to a globally smooth,
compactly supported family on `M` solving `Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` near `x₀` with
prescribed value and gradient.

Combining the Weyl–Schouten theorem with `ConformallyFlat.Chart` characterizes conformally
Euclidean coordinate charts directly by the vanishing of the Weyl tensor (`n ≥ 4`) or Cotton tensor
(`n = 3`), and shows that every constant-curvature Riemannian manifold of dimension `n ≠ 2` is
locally conformally flat.

## Main results

In `TauCeti.Manifold`:

* `exists_contMDiff_hessian_eq_family_of_isInteriorPoint` and `exists_contMDiff_hessian_eq_family`:
  local smooth-family solvability of the conformal flattening equation on a manifold with arbitrary
  initial value and gradient where `W = 0` and `C = 0` nearby.
* `exists_eventually_hessian_eq_of_isInteriorPoint` and `exists_eventually_hessian_eq`: pointwise
  local solvability with prescribed value and gradient at `x₀`.

In `Bundle.ContMDiffRiemannianMetric`:

* `exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint` and
  `exists_eventually_curvatureTensor_rescale_exp_eq_zero`: local conformal flattening `e^(2φ) g`
  with prescribed `φ x₀` and `mgradient I φ x₀`.
* `isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero`: characterization of
  local conformal flatness in dimension `n ≥ 3` by `W = 0` and `C = 0`.
* `isLocallyConformallyFlat_iff_weylTensor_eq_zero`,
  `isLocallyConformallyFlat_iff_weylTensor_eq_zero_of_riemannianBundle_eq`, and
  `isLocallyConformallyFlat_of_weylTensor_eq_zero`: the Weyl–Schouten theorem for `n ≥ 4`.
* `isLocallyConformallyFlat_iff_cottonTensor_eq_zero`,
  `isLocallyConformallyFlat_iff_cottonTensor_eq_zero_of_riemannianBundle_eq`, and
  `isLocallyConformallyFlat_of_cottonTensor_eq_zero`: the Weyl–Schouten theorem for `n = 3`.
* `forall_exists_partialDiffeomorph_iff_weylTensor_eq_zero` and
  `forall_exists_partialDiffeomorph_iff_cottonTensor_eq_zero`: existence of conformally Euclidean
  charts characterized by `W = 0` (`n ≥ 4`) or `C = 0` (`n = 3`).
* `IsConstantCurvatureTensor.isLocallyConformallyFlat`: constant-curvature manifolds of dimension
  `n ≠ 2` (spheres, Euclidean spaces, hyperbolic manifolds) are locally conformally flat.

## References

* É. Cotton, *Sur les variétés à trois dimensions*, Ann. Fac. Sci. Toulouse (2) 1 (1899), 385–438,
  Chapter III, n° 18, p. 412.
* H. Weyl, *Reine Infinitesimalgeometrie*, Math. Z. 2 (1918), 384–411.
* J. A. Schouten, *Über die konforme Abbildung `n`-dimensionaler Mannigfaltigkeiten mit
  quadratischer Maßbestimmung auf eine Mannigfaltigkeit mit euklidischer Maßbestimmung*, Math. Z.
  11 (1921), 58–88.
* L. P. Eisenhart, *Riemannian Geometry*, Princeton Univ. Press (1926), §28.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2, p. 43.
-/

public section

open Bundle Filter Function Manifold Set TopologicalSpace
open scoped ContDiff InnerProductSpace Manifold Topology TauCeti

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

local notation "lc" => CovariantDerivative.leviCivitaConnection

/-- **Local smooth-family solvability of the conformal flattening equation at an interior point.**
If the Weyl and Cotton tensors vanish near an interior point `x₀ : M`, then around any initial
value `c₀ : ℝ` and initial gradient `ξ₀ : TangentSpace I x₀` there exist open neighbourhoods `V` of
`x₀` and `Q` of `(c₀, ξ₀)`, a compact set `K ⊆ M`, and a jointly smooth function
`φ : M × (ℝ × TangentSpace I x₀) → ℝ` vanishing outside `K` in the first variable such that for
every `p ∈ Q`, `φ (x₀, p) = p.1`, `mgradient I (fun x ↦ φ (x, p)) x₀ = p.2`, and `φ (·, p)` solves
`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` at every point of `V`. -/
theorem exists_contMDiff_hessian_eq_family_of_isInteriorPoint {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (lc I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (lc I M).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    ∃ (φ : M × (ℝ × TangentSpace I x₀) → ℝ)
      (V : Set M) (Q : Set (ℝ × TangentSpace I x₀)) (K : Set M),
      IsOpen V ∧ IsOpen Q ∧ IsCompact K ∧ x₀ ∈ V ∧ (c₀, ξ₀) ∈ Q ∧
      ContMDiff (I.prod (𝓘(ℝ).prod 𝓘(ℝ, TangentSpace I x₀))) 𝓘(ℝ) ∞ φ ∧
      (∀ x ∉ K, ∀ p, φ (x, p) = 0) ∧
      ∀ p ∈ Q, φ (x₀, p) = p.1 ∧
        mgradient I (fun x ↦ φ (x, p)) x₀ = p.2 ∧
        ∀ y ∈ V, ∀ u v : TangentSpace I y,
          hessian I (fun x ↦ φ (x, p)) y u v =
            (lc I M).conformalFlatteningForm y (mgradient I (fun x ↦ φ (x, p)) y) u v := by
  have : FiniteDimensional ℝ (TangentSpace I x₀) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x₀
  obtain ⟨U₀, hU₀WC, hU₀open, hx₀U₀⟩ := mem_nhds_iff.1 (hW.and hC)
  obtain ⟨W, hx₀W, Φ, hWU₀, -⟩ :=
    TauCeti.exists_diffeomorph_modelSpace_of_isInteriorPoint (le_rfl : ∞ ≤ ∞) hx₀
      (hU₀open.mem_nhds hx₀U₀)
  let x₀W : W := ⟨x₀, hx₀W⟩
  set z₀ : E := Φ x₀W
  -- Transport the restricted metric of `W` to `E` along `Φ.symm` so both `Φ` and `Subtype.val`
  -- are local Riemannian isometries.
  let gW := contMDiffRiemannianMetricOpen (I := I) (n := ∞) W
  let gE := gW.pullback Φ.symm (Φ.symm.contMDiff.of_le (by simp))
    fun z ↦ (Φ.symm.isInvertible_mfderiv (by simp) (x := z)).injective
  let _ : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) :=
    ⟨gE.inner, gE.contMDiff, fun _ _ _ ↦ rfl⟩
  -- `W` carries the scoped `instRiemannianBundleOpen W` instance rather than
  -- `⟨gW.toRiemannianMetric⟩`, so build `Ψsymm` directly from `inner_tangentSpace_open`.
  let Ψsymm : TauCeti.RiemannianIsometry 𝓘(ℝ, E) I E W :=
    { toDiffeomorph := Φ.symm
      inner_mfderiv' := fun z u v ↦ by
        rw [inner_tangentSpace_open W, ← contMDiffRiemannianMetricOpen_inner (n := ∞) W,
          gE.inner_riemannianBundle, gW.pullback_inner] }
  have hΨ : TauCeti.IsLocalRiemannianIsometry 𝓘(ℝ, E) I Φ.symm := Ψsymm.isLocalRiemannianIsometry
  have hcoe : (Ψsymm.symm : W → E) = Φ := by
    rw [TauCeti.RiemannianIsometry.coe_symm, ← Diffeomorph.coe_toEquiv]
    simp [Ψsymm]
  have hΦ : TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, E) Φ :=
    hcoe ▸ Ψsymm.symm.isLocalRiemannianIsometry
  have hι : TauCeti.IsLocalRiemannianIsometry I I (Subtype.val : W → M) :=
    TauCeti.IsLocalRiemannianIsometry.subtype_val W
  have hWE (z : E) : (lc 𝓘(ℝ, E) E).weylTensor z = 0 :=
    (hΨ.weylTensor_eq_zero_iff z).1
      ((hι.weylTensor_eq_zero_iff (Φ.symm z)).1 (hU₀WC (hWU₀ (Φ.symm z).2)).1)
  have hCE (z : E) : (lc 𝓘(ℝ, E) E).cottonTensor z = 0 :=
    (hΨ.cottonTensor_eq_zero_iff z).1
      ((hι.cottonTensor_eq_zero_iff (Φ.symm z)).1 (hU₀WC (hWU₀ (Φ.symm z).2)).2)
  -- Solve the conformal flattening equation in smooth families on the model space `E`.
  let L : TangentSpace I x₀ →L[ℝ] TangentSpace 𝓘(ℝ, E) z₀ :=
    (mfderiv I 𝓘(ℝ, E) Φ x₀W).comp
      (tangentSpaceOpenEquiv (I := I) x₀W).symm.toContinuousLinearMap
  have hL_inj : Injective L :=
    (hΦ.mfderiv_injective x₀W).comp (tangentSpaceOpenEquiv (I := I) x₀W).symm.injective
  obtain ⟨φE, VE, QE, KE, hVE, hQE, hKE, hz₀VE, hp₀QE, hφE, hφE_supp, hφE_sol⟩ :=
    exists_contMDiff_hessian_eq_family_model_space
      (Eventually.of_forall hWE) (Eventually.of_forall hCE) c₀ (L ξ₀)
  -- Pull the solution family back to `W` and extend by zero outside `W`.
  let KM : Set M := (Subtype.val ∘ Φ.symm) '' KE
  have hKM_cpt : IsCompact KM := hKE.image (continuous_subtype_val.comp Φ.symm.continuous)
  have hKMW : KM ⊆ (W : Set M) := by
    rintro _ ⟨z, -, rfl⟩
    exact (Φ.symm z).2
  let g : W × (ℝ × TangentSpace I x₀) → ℝ := fun q ↦ φE (Φ q.1, (q.2.1, L q.2.2))
  have hg_supp (w : W) (hw : (w : M) ∉ KM) (p : ℝ × TangentSpace I x₀) : g (w, p) = 0 :=
    hφE_supp (Φ w) (fun hz ↦ hw ⟨Φ w, hz, congrArg Subtype.val (Φ.symm_apply_apply w)⟩)
      (p.1, L p.2)
  have hg : ContMDiff (I.prod (𝓘(ℝ).prod 𝓘(ℝ, TangentSpace I x₀))) 𝓘(ℝ) ∞ g :=
    hφE.comp ((Φ.contMDiff.comp contMDiff_fst).prodMk
      ((contMDiff_fst.comp contMDiff_snd).prodMk
        (L.contDiff.contMDiff.comp (contMDiff_snd.comp contMDiff_snd))))
  let φ : M × (ℝ × TangentSpace I x₀) → ℝ := (Prod.map (Subtype.val : W → M) id).extend g 0
  have hφ : ContMDiff (I.prod (𝓘(ℝ).prod 𝓘(ℝ, TangentSpace I x₀))) 𝓘(ℝ) ∞ φ :=
    ContMDiff.extend_prodMap_subtypeVal_zero hKM_cpt.isClosed hKMW hg hg_supp
  have hφ_supp (x : M) (hxK : x ∉ KM) (p : ℝ × TangentSpace I x₀) : φ (x, p) = 0 := by
    by_cases hxW : x ∈ W
    · exact ((Subtype.val_injective.prodMap injective_id).extend_apply g 0 (⟨x, hxW⟩, p)).trans
        (hg_supp ⟨x, hxW⟩ hxK p)
    · exact extend_apply' _ _ _ fun ⟨q, hq⟩ ↦
        hxW ((show (q.1 : M) = x from congrArg Prod.fst hq) ▸ q.1.2)
  -- Transport initial data and the Hessian identity back from `E` to `VM ⊆ M`.
  let VM : Set M := Subtype.val '' (Φ.symm '' VE)
  have hVM : IsOpen VM :=
    W.isOpen.isOpenMap_subtype_val _ (Φ.symm.toHomeomorph.isOpenMap VE hVE)
  have hx₀VM : x₀ ∈ VM := ⟨x₀W, ⟨z₀, hz₀VE, Φ.symm_apply_apply x₀W⟩, rfl⟩
  let Q : Set (ℝ × TangentSpace I x₀) := Prod.map id L ⁻¹' QE
  have hQ : IsOpen Q := hQE.preimage (continuous_id.prodMap L.continuous)
  refine ⟨φ, VM, Q, KM, hVM, hQ, hKM_cpt, hx₀VM, hp₀QE, hφ, hφ_supp, fun p hp ↦ ?_⟩
  obtain ⟨hvalE, hgradE, hsolE⟩ := hφE_sol (p.1, L p.2) hp
  set φp : M → ℝ := fun x ↦ φ (x, p)
  set φEp : E → ℝ := fun z ↦ φE (z, (p.1, L p.2))
  have hφp : ContMDiff I 𝓘(ℝ) ∞ φp := hφ.comp (contMDiff_id.prodMk contMDiff_const)
  have hφEp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φEp := hφE.comp (contMDiff_id.prodMk contMDiff_const)
  have hcompW : φp ∘ (Subtype.val : W → M) = φEp ∘ Φ :=
    funext fun w ↦ (Subtype.val_injective.prodMap injective_id).extend_apply g 0 (w, p)
  refine ⟨((Subtype.val_injective.prodMap injective_id).extend_apply g 0 (x₀W, p)).trans hvalE,
    ?_, ?_⟩
  · apply hL_inj
    have hgradι : mfderiv I I (Subtype.val : W → M) x₀W (mgradient I (φp ∘ Subtype.val) x₀W) =
        mgradient I φp x₀ :=
      hι.mfderiv_mgradient_comp (x := x₀W) (hφp.contMDiffAt.mdifferentiableAt (by simp))
    have hgradW : (tangentSpaceOpenEquiv (I := I) x₀W).symm (mgradient I φp x₀) =
        mgradient I (φp ∘ Subtype.val) x₀W := by
      rw [← hgradι, mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply]
    conv_lhs =>
      simp only [L, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearEquiv.coe_coe]
    rw [hgradW, hcompW,
      hΦ.mfderiv_mgradient_comp (x := x₀W) (hφEp.contMDiffAt.mdifferentiableAt (by simp))]
    exact hgradE
  · rintro _ ⟨_, ⟨z, hzVE, rfl⟩, rfl⟩
    refine (hι.hessian_comp_eq_conformalFlatteningForm_iff (x := Φ.symm z)
      (hφp.contMDiffAt.of_le (by simp))).1 ?_
    rw [hcompW]
    refine (hΦ.hessian_comp_eq_conformalFlatteningForm_iff (x := Φ.symm z)
      (hφEp.contMDiffAt.of_le (by simp))).2 ?_
    exact hsolE (Φ (Φ.symm z)) (by simpa using hzVE)

/-- **Local smooth-family solvability of the conformal flattening equation on a boundaryless
manifold.** -/
theorem exists_contMDiff_hessian_eq_family [BoundarylessManifold I M] {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (lc I M).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    ∃ (φ : M × (ℝ × TangentSpace I x₀) → ℝ)
      (V : Set M) (Q : Set (ℝ × TangentSpace I x₀)) (K : Set M),
      IsOpen V ∧ IsOpen Q ∧ IsCompact K ∧ x₀ ∈ V ∧ (c₀, ξ₀) ∈ Q ∧
      ContMDiff (I.prod (𝓘(ℝ).prod 𝓘(ℝ, TangentSpace I x₀))) 𝓘(ℝ) ∞ φ ∧
      (∀ x ∉ K, ∀ p, φ (x, p) = 0) ∧
      ∀ p ∈ Q, φ (x₀, p) = p.1 ∧
        mgradient I (fun x ↦ φ (x, p)) x₀ = p.2 ∧
        ∀ y ∈ V, ∀ u v : TangentSpace I y,
          hessian I (fun x ↦ φ (x, p)) y u v =
            (lc I M).conformalFlatteningForm y (mgradient I (fun x ↦ φ (x, p)) y) u v :=
  exists_contMDiff_hessian_eq_family_of_isInteriorPoint BoundarylessManifold.isInteriorPoint
    hW hC c₀ ξ₀

/-- **Local solvability of the conformal flattening equation at an interior point.** Where the Weyl
and Cotton tensors vanish near an interior point `x₀`, there is a globally smooth function `φ` on
`M` with prescribed value `c` and gradient `ξ` at `x₀` solving the conformal flattening equation
near `x₀`. -/
theorem exists_eventually_hessian_eq_of_isInteriorPoint {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (lc I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (lc I M).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient I φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace I y,
        hessian I φ y u v = (lc I M).conformalFlatteningForm y (mgradient I φ y) u v := by
  obtain ⟨φ, V, Q, -, hV, -, -, hx₀V, hcξQ, hφ, -, hsol⟩ :=
    exists_contMDiff_hessian_eq_family_of_isInteriorPoint hx₀ hW hC c ξ
  obtain ⟨hval, hgrad, hhess⟩ := hsol (c, ξ) hcξQ
  exact ⟨fun x ↦ φ (x, (c, ξ)), hφ.comp (contMDiff_id.prodMk contMDiff_const), hval, hgrad,
    eventually_of_mem (hV.mem_nhds hx₀V) hhess⟩

/-- **Local solvability of the conformal flattening equation on a boundaryless manifold.** -/
theorem exists_eventually_hessian_eq [BoundarylessManifold I M] {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (lc I M).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient I φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace I y,
        hessian I φ y u v = (lc I M).conformalFlatteningForm y (mgradient I φ y) u v :=
  exists_eventually_hessian_eq_of_isInteriorPoint BoundarylessManifold.isInteriorPoint hW hC c ξ

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Where the Weyl and Cotton tensors vanish near an interior point `x` in dimension at least `3`,
a smooth Riemannian metric `g` admits a flat conformal rescaling `e^(2φ) g` near `x` with arbitrary
prescribed value `c` and gradient `ξ` of `φ` at `x`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x : M} (hx : I.IsInteriorPoint x)
    (hW : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace I x) :
    ∃ (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ), φ x = c ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I φ x = ξ) ∧
      ∀ᶠ y in 𝓝 x,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
              (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  obtain ⟨φ, hφ, hval, hgrad, hsol⟩ :=
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    exists_eventually_hessian_eq_of_isInteriorPoint hx hW hC c ξ
  refine ⟨φ, hφ, hval, hgrad, ?_⟩
  filter_upwards [hW, hsol] with y hyW hy
  exact (g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff
    (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ)) (fun _ ↦ Real.exp_pos _)
    (fun _ ↦ rfl) hn y).2 ⟨hyW, hy⟩

section Boundaryless

variable [BoundarylessManifold I M]

/-- On a boundaryless manifold of dimension at least `3`, vanishing Weyl and Cotton tensors near
`x` give a flat conformal rescaling `e^(2φ) g` near `x` with prescribed value and gradient of `φ`
at `x`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x : M}
    (hW : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace I x) :
    ∃ (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ), φ x = c ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I φ x = ξ) ∧
      ∀ᶠ y in 𝓝 x,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
              (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  g.exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint hW hC c ξ

/-- On a boundaryless smooth manifold of dimension at least `3`, a smooth Riemannian metric is
locally conformally flat if and only if both its Weyl tensor and its Cotton tensor vanish
everywhere. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) := by
  refine ⟨fun hg ↦ ⟨hg.weylTensor_eq_zero (by omega), hg.cottonTensor_eq_zero (by omega)⟩, ?_⟩
  rintro ⟨hW, hC⟩
  rw [g.isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨φ, hφ, -, -, hflat⟩ :=
    g.exists_eventually_curvatureTensor_rescale_exp_eq_zero hn
      (Eventually.of_forall hW) (Eventually.of_forall hC) 0 0
  exact ⟨fun y ↦ Real.exp (2 * φ y),
    Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ), fun _ ↦ Real.exp_pos _, hflat⟩

/-- **Weyl–Schouten theorem in dimension at least four.** On a boundaryless smooth manifold of
dimension `n ≥ 4`, a smooth Riemannian metric is locally conformally flat if and only if its Weyl
tensor vanishes everywhere. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) := by
  rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero (by omega)]
  refine and_iff_left_of_imp fun hW x ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  exact hcov.cottonTensor_eq_zero_of_eventually_weylTensor_eq_zero
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) (by omega) (by omega)
    (Eventually.of_forall hW)

/-- **Weyl–Schouten theorem in dimension at least four (installed metric form).** When `g` is
installed as the ambient `RiemannianBundle` on a boundaryless manifold of dimension `n ≥ 4`, `g` is
locally conformally flat if and only if its Weyl tensor vanishes everywhere. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_of_riemannianBundle_eq
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) (hg : RiemannianBundle.g = g.toRiemannianMetric) :
    g.IsLocallyConformallyFlat ↔
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0 := by
  obtain ⟨_⟩ := inst
  subst hg
  exact g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn

/-- **Converse Weyl–Schouten theorem in dimension at least four (installed metric form).** On a
boundaryless smooth manifold of dimension `n ≥ 4`, if `g` is installed as the ambient
`RiemannianBundle` and its Weyl tensor vanishes everywhere, then `g` is locally conformally flat.
`IsLocallyConformallyFlat.weylTensor_eq_zero` is the forward implication. -/
theorem isLocallyConformallyFlat_of_weylTensor_eq_zero
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) (hg : RiemannianBundle.g = g.toRiemannianMetric)
    (hW : ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_of_riemannianBundle_eq hn hg).2 hW

/-- **Weyl–Schouten theorem in dimension three.** On a boundaryless smooth `3`-manifold, a smooth
Riemannian metric is locally conformally flat if and only if its Cotton tensor vanishes
everywhere. -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) := by
  rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero hn.ge]
  refine and_iff_right ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro x
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  exact CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three
    (cov := CovariantDerivative.leviCivitaConnection I M) hcov x
    (by rw [TauCeti.finrank_tangentSpace, hn])

/-- **Weyl–Schouten theorem in dimension three (installed metric form).** When `g` is installed as
the ambient `RiemannianBundle` on a boundaryless `3`-manifold, `g` is locally conformally flat if
and only if its Cotton tensor vanishes everywhere. -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero_of_riemannianBundle_eq
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) (hg : RiemannianBundle.g = g.toRiemannianMetric) :
    g.IsLocallyConformallyFlat ↔
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0 := by
  obtain ⟨_⟩ := inst
  subst hg
  exact g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn

/-- **Converse Weyl–Schouten theorem in dimension three (installed metric form).** On a
boundaryless smooth `3`-manifold, if `g` is installed as the ambient `RiemannianBundle` and its
Cotton tensor vanishes everywhere, then `g` is locally conformally flat.
`IsLocallyConformallyFlat.cottonTensor_eq_zero` is the forward implication. -/
theorem isLocallyConformallyFlat_of_cottonTensor_eq_zero
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) (hg : RiemannianBundle.g = g.toRiemannianMetric)
    (hC : ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero_of_riemannianBundle_eq hn hg).2 hC

/-- On a boundaryless smooth manifold of dimension `n ≥ 4`, every point admits a conformally
Euclidean `PartialDiffeomorph` sending it to `0` if and only if the Weyl tensor of `g` vanishes
everywhere. -/
theorem forall_exists_partialDiffeomorph_iff_weylTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) :
    (∀ x : M, ∃ (φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞) (h : M → ℝ),
      x ∈ φ.source ∧ φ x = 0 ∧ ContMDiffOn I 𝓘(ℝ) ∞ h φ.source ∧
      (∀ y ∈ φ.source, 0 < h y) ∧
      ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
        g.inner y v w = h y *
          ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y v,
            mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y w⟫_ℝ) ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) :=
  g.isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph.symm.trans
    (g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn)

/-- On a boundaryless smooth `3`-manifold, every point admits a conformally Euclidean
`PartialDiffeomorph` sending it to `0` if and only if the Cotton tensor of `g` vanishes
everywhere. -/
theorem forall_exists_partialDiffeomorph_iff_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) :
    (∀ x : M, ∃ (φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞) (h : M → ℝ),
      x ∈ φ.source ∧ φ x = 0 ∧ ContMDiffOn I 𝓘(ℝ) ∞ h φ.source ∧
      (∀ y ∈ φ.source, 0 < h y) ∧
      ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
        g.inner y v w = h y *
          ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y v,
            mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y w⟫_ℝ) ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) :=
  g.isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph.symm.trans
    (g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn)

/-- **Spaces of constant sectional curvature are locally conformally flat.** On a boundaryless
smooth manifold of dimension `n ≠ 2`, every smooth Riemannian metric of constant curvature `κ`
(including round spheres, Euclidean spaces, and hyperbolic manifolds) is locally conformally flat.
-/
theorem IsConstantCurvatureTensor.isLocallyConformallyFlat
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {κ : ℝ}
    (hg : g.IsConstantCurvatureTensor κ) (hn : Module.finrank ℝ E ≠ 2) :
    g.IsLocallyConformallyFlat := by
  rcases le_or_gt (Module.finrank ℝ E) 1 with h1 | h1
  · refine g.isLocallyConformallyFlat_of_curvatureTensor_eq_zero fun x ↦ ?_
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact (CovariantDerivative.leviCivitaConnection I M).curvatureTensor_eq_zero_of_finrank_le_one
      x (by rwa [TauCeti.finrank_tangentSpace])
  · have hn3 : 3 ≤ Module.finrank ℝ E := by omega
    rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero hn3]
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    have hcurv := g.isConstantCurvatureTensor_iff κ |>.1 hg
    have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
    open CovariantDerivative in
    refine ⟨fun x ↦ (leviCivitaConnection I M)
        |>.weylTensor_eq_zero_of_curvatureTensor_eq_smul_inner_sub x κ
          (by rwa [TauCeti.finrank_tangentSpace]) (hcurv x),
      fun x ↦ IsMetricCompatible.cottonTensor_eq_zero_of_curvatureTensor_eq_smul_inner_sub
        (cov := leviCivitaConnection I M) hcov κ hcurv x⟩

end Boundaryless

end Bundle.ContMDiffRiemannianMetric
