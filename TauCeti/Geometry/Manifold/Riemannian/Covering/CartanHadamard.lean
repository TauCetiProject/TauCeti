/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import Mathlib.Analysis.Convex.Contractible
import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed.Basic
import TauCeti.AlgebraicTopology.UniversalCover.Covering
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Extension
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing
import TauCeti.Geometry.Manifold.Riemannian.Covering.Criterion
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Comparison
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Nonsingular
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Topology.Covering.Clopen
import TauCeti.Topology.Homotopy.Covering
import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv

/-!
# The Cartan–Hadamard theorem

Let `M` be a complete Riemannian manifold of nonpositive sectional curvature and `p ∈ M`. By the
Hopf–Rinow theorem the exponential map `exp_p` is defined on all of `T_p M`. Nonpositive curvature
makes its differential nondecreasing on lengths,
`|w| ≤ |d(exp_p)_v(w)|` (`norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos`), so
in particular `exp_p` is a local diffeomorphism. The flat space `T_p M` is complete, so the
covering criterion for length-nondecreasing local diffeomorphisms
(`TauCeti.Manifold.isCoveringMap_of_norm_le_norm_mfderiv`) makes `exp_p` a covering map. It is
surjective when `M` is connected, since `T_p M` is nonempty.

When `M` is moreover simply connected, a covering map from the connected space `T_p M` is
injective, so `exp_p` is a diffeomorphism `T_p M ≃ M`, and `M` is contractible. Any two points
`p, q` are then joined by a unique geodesic on `[0, 1]`: a geodesic `γ` from `p` is the radial
geodesic `t ↦ exp_p (t • v)` for its initial velocity `v`, and `exp_p v = q` determines `v`. Since
some geodesic from `p` to `q` is minimizing, this unique one is. Every segment of any geodesic is
then minimizing, after an affine reparametrization to `[0, 1]`.

Without simple connectivity, the covering `exp_p : T_p M → M` has simply connected, indeed
contractible, total space. So it is the universal covering: the universal cover of `M` based at `p`
is homeomorphic to the Euclidean space `T_p M` over `M`, and is contractible. Its higher homotopy
groups vanish, and the covering identifies them with those of `M`, so a connected `M` is
aspherical.

## Main results

* `TauCeti.Manifold.cartanHadamard_isCoveringMap`: **the Cartan–Hadamard theorem**, `exp_p` is a
  covering map.
* `TauCeti.Manifold.isLocalDiffeomorph_riemannianExp_of_sectionalCurvature_nonpos`: `exp_p` is
  a smooth local diffeomorphism on all of `T_p M`.
* `TauCeti.Manifold.cartanHadamard_surjective`: `exp_p` is surjective when `M` is connected.
* `TauCeti.Manifold.cartanHadamard_bijective`: `exp_p` is bijective when `M` is simply connected.
* `TauCeti.Manifold.cartanHadamardDiffeomorph`: for simply connected `M`, `exp_p` is a smooth
  diffeomorphism `T_p M ≃ M`.
* `TauCeti.Manifold.cartanHadamard_contractibleSpace`: a simply connected complete manifold of
  nonpositive sectional curvature is contractible.
* `TauCeti.Manifold.cartanHadamard_eqOn_riemannianExp_smul`: for simply connected `M`, every
  geodesic on `[0, 1]` from `p` to `q` is `t ↦ exp_p (t • v)` with `exp_p v = q`.
* `TauCeti.Manifold.cartanHadamard_exists_geodesic_unique`: for simply connected `M`, any two
  points are joined by a geodesic on `[0, 1]`, unique on `[0, 1]`.
* `TauCeti.Manifold.cartanHadamard_pathELength_eq_edist`,
  `TauCeti.Manifold.cartanHadamard_pathELength_eq_edist_of_le`: for simply connected `M`, that
  geodesic is minimizing, and so is every segment `[s, t]` of a geodesic lying in its parameter
  set.
* `TauCeti.Manifold.cartanHadamard_exists_homeomorph_universalCover` and
  `TauCeti.Manifold.cartanHadamardHomeomorphUniversalCover`: the universal cover based at `p` is
  homeomorphic to `T_p M`, by a homeomorphism under which the projection becomes `exp_p`.
* `TauCeti.Manifold.cartanHadamard_contractibleSpace_universalCover`: the universal cover is
  contractible.
* `TauCeti.Manifold.cartanHadamard_isAspherical`: a connected complete manifold of nonpositive
  sectional curvature is aspherical.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific, 2020,
  Theorem 6.2.6.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §3, Theorem 3.1.
-/

public section

open Bundle CovariantDerivative Function Manifold Set
open TauCeti (UniversalCover)
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]

/-- On a complete Riemannian manifold of nonpositive sectional curvature, the exponential map at
any point is a smooth local diffeomorphism on the whole tangent space. -/
theorem isLocalDiffeomorph_riemannianExp_of_sectionalCurvature_nonpos
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    IsLocalDiffeomorph 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) := by
  have hdom : expDomain I M p = univ := expDomain_eq_univ_of_completeSpace p
  exact fun v ↦ isLocalDiffeomorphAt_riemannianExp_of_sectionalCurvature_nonpos
    (hdom ▸ mem_univ v) fun t _ ↦ hK (riemannianExp I M p (t • v))

/-- **The Cartan–Hadamard theorem.** On a complete Riemannian manifold of nonpositive sectional
curvature, the exponential map at any point is a covering map from the tangent space. -/
theorem cartanHadamard_isCoveringMap
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    IsCoveringMap (riemannianExp I M p) := by
  have hdom : expDomain I M p = univ := expDomain_eq_univ_of_completeSpace p
  exact isCoveringMap_of_norm_le_norm_mfderiv
    (isLocalDiffeomorph_riemannianExp_of_sectionalCurvature_nonpos hK p) fun v w ↦
      norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos (hdom ▸ mem_univ v)
        (fun t _ ↦ hK (riemannianExp I M p (t • v))) w

/-- On a connected complete Riemannian manifold of nonpositive sectional curvature, the
exponential map at any point is surjective. -/
theorem cartanHadamard_surjective [PreconnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    Surjective (riemannianExp I M p) :=
  (cartanHadamard_isCoveringMap hK p).surjective

/-- On a simply connected complete Riemannian manifold of nonpositive sectional curvature, the
exponential map at any point is bijective. -/
theorem cartanHadamard_bijective [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    Bijective (riemannianExp I M p) :=
  ⟨(cartanHadamard_isCoveringMap hK p).injective, cartanHadamard_surjective hK p⟩

/-- **The Cartan–Hadamard theorem, simply connected form.** On a simply connected complete
Riemannian manifold of nonpositive sectional curvature, the exponential map at any point is a
smooth diffeomorphism from the tangent space onto the manifold. -/
def cartanHadamardDiffeomorph [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    TangentSpace I p ≃ₘ^∞⟮𝓘(ℝ, TangentSpace I p), I⟯ M :=
  (isLocalDiffeomorph_riemannianExp_of_sectionalCurvature_nonpos hK p).diffeomorphOfBijective
    (cartanHadamard_bijective hK p)

/-- The forward map of `cartanHadamardDiffeomorph` is the exponential map. -/
@[simp]
theorem coe_cartanHadamardDiffeomorph [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    ⇑(cartanHadamardDiffeomorph hK p) = riemannianExp I M p :=
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

/-- The exponential map at `p` undoes the inverse of `cartanHadamardDiffeomorph`. -/
@[simp]
theorem riemannianExp_cartanHadamardDiffeomorph_symm [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p q : M) :
    riemannianExp I M p ((cartanHadamardDiffeomorph hK p).symm q) = q := by
  rw [← coe_cartanHadamardDiffeomorph hK, Diffeomorph.apply_symm_apply]

/-- The inverse of `cartanHadamardDiffeomorph` undoes the exponential map at `p`. -/
@[simp]
theorem cartanHadamardDiffeomorph_symm_riemannianExp [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) (v : TangentSpace I p) :
    (cartanHadamardDiffeomorph hK p).symm (riemannianExp I M p v) = v := by
  rw [← coe_cartanHadamardDiffeomorph hK, Diffeomorph.symm_apply_apply]

/-- A simply connected complete Riemannian manifold of nonpositive sectional curvature is
contractible. -/
theorem cartanHadamard_contractibleSpace [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) :
    ContractibleSpace M := by
  obtain ⟨p⟩ : Nonempty M := inferInstance
  exact (cartanHadamardDiffeomorph hK p).toHomeomorph.symm.contractibleSpace

/-! ### Geodesics of a simply connected manifold -/

/-- **Geodesics of a Cartan–Hadamard manifold are radial.** On a simply connected complete
Riemannian manifold of nonpositive sectional curvature, every geodesic `γ` on `[0, 1]` from `p` to
`q` agrees on `[0, 1]` with `t ↦ exp_p (t • v)`, where `v` is the unique tangent vector at `p` with
`exp_p v = q`. -/
theorem cartanHadamard_eqOn_riemannianExp_smul [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) {γ : ℝ → M} {p q : M} (hγ : IsGeodesicCurveOn I γ (Icc 0 1)) (h0 : γ 0 = p)
    (h1 : γ 1 = q) :
    EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • (cartanHadamardDiffeomorph hK p).symm q))
      (Icc 0 1) := by
  subst h0 h1
  let v : TangentSpace I (γ 0) := curveVelocityWithin I γ (Icc 0 1) 0
  have hfrom : IsGeodesicCurveOnFrom I γ (Icc 0 1) (γ 0) v :=
    ⟨hγ, left_mem_Icc.2 zero_le_one, rfl⟩
  have heq := hfrom.eqOn_maximalGeodesic_of_isPreconnected isPreconnected_Icc
  have hexp : riemannianExp I M (γ 0) v = γ 1 := by
    rw [← one_smul ℝ v, riemannianExp_smul, heq (right_mem_Icc.2 zero_le_one)]
  have hv : (cartanHadamardDiffeomorph hK (γ 0)).symm (γ 1) = v := by
    rw [← hexp, cartanHadamardDiffeomorph_symm_riemannianExp]
  intro t ht
  simp only [hv, riemannianExp_smul, heq ht]

/-- **Unique geodesics on a Cartan–Hadamard manifold.** On a simply connected complete Riemannian
manifold of nonpositive sectional curvature, any two points `p` and `q` are joined by a geodesic
on `[0, 1]`, and any other geodesic on `[0, 1]` from `p` to `q` agrees with it on `[0, 1]`. -/
theorem cartanHadamard_exists_geodesic_unique [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p q : M) :
    ∃ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q ∧
      ∀ γ' : ℝ → M, IsGeodesicCurveOn I γ' (Icc 0 1) → γ' 0 = p → γ' 1 = q →
        EqOn γ' γ (Icc 0 1) := by
  set v := (cartanHadamardDiffeomorph hK p).symm q
  have hJ : geodesicInterval I M p v = univ := by
    rw [geodesicInterval_eq_preimage_expDomain, expDomain_eq_univ_of_completeSpace, preimage_univ]
  refine ⟨fun t ↦ riemannianExp I M p (t • v),
    isGeodesicCurveOn_riemannianExp_smul_Icc zero_lt_one (hJ ▸ mem_univ _) (hJ ▸ mem_univ _),
    by simp, ?_, fun γ' hγ' h0 h1 ↦ cartanHadamard_eqOn_riemannianExp_smul hK hγ' h0 h1⟩
  simp only [one_smul, v, riemannianExp_cartanHadamardDiffeomorph_symm]

/-- **The geodesic of a Cartan–Hadamard manifold is minimizing.** On a simply connected complete
Riemannian manifold of nonpositive sectional curvature, every geodesic on `[0, 1]` from `p` to `q`
has length the distance from `p` to `q`. -/
theorem cartanHadamard_pathELength_eq_edist [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) {γ : ℝ → M} {p q : M} (hγ : IsGeodesicCurveOn I γ (Icc 0 1)) (h0 : γ 0 = p)
    (h1 : γ 1 = q) :
    pathELength I γ 0 1 = edist p q := by
  -- Simple connectivity makes the Riemannian distance finite, so `M` is a metric space with the
  -- same extended distance and uniformity, where minimizing geodesics exist.
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  let : MetricSpace M := EMetricSpace.toMetricSpace fun x y ↦
    (IsRiemannianManifold.out (I := I) x y).symm ▸ riemannianEDist_ne_top I x y
  obtain ⟨γ₀, hγ₀, h00, h01, hlen, -⟩ :=
    exists_isGeodesicCurveOn_Icc_pathELength_eq_edist (I := I)
      (expDomain_eq_univ_of_completeSpace p) q
  rw [pathELength_congr ((cartanHadamard_eqOn_riemannianExp_smul hK hγ h0 h1).trans
    (cartanHadamard_eqOn_riemannianExp_smul hK hγ₀ h00 h01).symm), hlen]

/-- On a simply connected complete Riemannian manifold of nonpositive sectional curvature, every
segment `[s, t]` of a geodesic lying in its parameter set realizes the distance between its
endpoints. -/
theorem cartanHadamard_pathELength_eq_edist_of_le [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) {γ : ℝ → M} {u : Set ℝ} (hγ : IsGeodesicCurveOn I γ u) {s t : ℝ}
    (hsub : Icc s t ⊆ u) (hst : s ≤ t) :
    pathELength I γ s t = edist (γ s) (γ t) := by
  rcases hst.eq_or_lt with rfl | hlt
  · simp
  -- Reparametrize the segment `[s, t]` affinely to `[0, 1]`.
  set φ : ℝ → ℝ := fun r ↦ (t - s) * r + s
  have hφ0 : φ 0 = s := by simp [φ]
  have hφ1 : φ 1 = t := by simp [φ]
  have hmaps : MapsTo φ (Icc 0 1) (Icc s t) := fun r hr ↦ by
    simp only [φ, mem_Icc]
    constructor <;> nlinarith [hr.1, hr.2]
  have hγ' : IsGeodesicCurveOn I (γ ∘ φ) (Icc 0 1) :=
    hγ.comp_affine _ _ (uniqueDiffOn_Icc zero_lt_one) (hmaps.mono_right hsub)
  have hmono : MonotoneOn φ (Icc 0 1) := fun a _ b _ hab ↦ by
    simp only [φ]; nlinarith
  have hdiff : DifferentiableOn ℝ φ (Icc 0 1) := by fun_prop
  have hmd : MDiff[Icc (φ 0) (φ 1)] γ := by
    rw [hφ0, hφ1]
    exact (hγ.mono (uniqueDiffOn_Icc hlt) hsub).mdifferentiableOn
  have h := cartanHadamard_pathELength_eq_edist hK hγ' rfl rfl
  rwa [pathELength_comp_of_monotoneOn zero_le_one hmono hdiff hmd, comp_apply, comp_apply, hφ0,
    hφ1] at h

/-! ### The universal cover and asphericity -/

/-- **The universal cover of a Cartan–Hadamard manifold is Euclidean.** On a complete Riemannian
manifold of nonpositive sectional curvature, the universal cover based at `p` is
homeomorphic to the tangent space `T_p M`, by a homeomorphism sending `0` to the base point and
under which the projection of the universal cover becomes `exp_p`. -/
theorem cartanHadamard_exists_homeomorph_universalCover
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    ∃ h : TangentSpace I p ≃ₜ UniversalCover p,
      h 0 = UniversalCover.basepointLift p ∧ UniversalCover.proj ∘ h = riemannianExp I M p := by
  have : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  have : TauCeti.SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  exact (cartanHadamard_isCoveringMap hK p).exists_homeomorph_comp_eq_of_simplyConnectedSpace
    (TauCeti.UniversalCover.isCoveringMap p) (riemannianExp_zero p)
    (TauCeti.UniversalCover.proj_basepointLift p)

/-- A homeomorphism from `T_p M` onto the universal cover based at `p`, sending `0` to the base
point and under which the projection of the universal cover becomes `exp_p`
(`cartanHadamard_exists_homeomorph_universalCover`). -/
noncomputable def cartanHadamardHomeomorphUniversalCover
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    TangentSpace I p ≃ₜ UniversalCover p :=
  (cartanHadamard_exists_homeomorph_universalCover hK p).choose

/-- `cartanHadamardHomeomorphUniversalCover` sends `0` to the base point. -/
@[simp]
theorem cartanHadamardHomeomorphUniversalCover_zero
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    cartanHadamardHomeomorphUniversalCover hK p 0 = UniversalCover.basepointLift p :=
  (cartanHadamard_exists_homeomorph_universalCover hK p).choose_spec.1

/-- Under `cartanHadamardHomeomorphUniversalCover`, the projection of the universal cover is
`exp_p`. -/
@[simp]
theorem proj_cartanHadamardHomeomorphUniversalCover
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) (v : TangentSpace I p) :
    UniversalCover.proj (cartanHadamardHomeomorphUniversalCover hK p v) = riemannianExp I M p v :=
  congrFun (cartanHadamard_exists_homeomorph_universalCover hK p).choose_spec.2 v

/-- Under the inverse of `cartanHadamardHomeomorphUniversalCover`, `exp_p` becomes the projection
of the universal cover. -/
@[simp]
theorem riemannianExp_cartanHadamardHomeomorphUniversalCover_symm
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) (z : UniversalCover p) :
    riemannianExp I M p ((cartanHadamardHomeomorphUniversalCover hK p).symm z) =
      UniversalCover.proj z := by
  rw [← proj_cartanHadamardHomeomorphUniversalCover hK, Homeomorph.apply_symm_apply]

/-- The inverse of `cartanHadamardHomeomorphUniversalCover` sends the base point, the class of the
constant path at `p`, to `0`. -/
@[simp]
theorem cartanHadamardHomeomorphUniversalCover_symm_mk_refl
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    (cartanHadamardHomeomorphUniversalCover hK p).symm
      (UniversalCover.mk p (Path.Homotopic.Quotient.refl p)) = 0 := by
  rw [← UniversalCover.basepointLift_coe, ← cartanHadamardHomeomorphUniversalCover_zero hK p,
    Homeomorph.symm_apply_apply]

/-- The universal cover of a complete Riemannian manifold of nonpositive sectional curvature, at any
base point, is contractible. -/
theorem cartanHadamard_contractibleSpace_universalCover
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    ContractibleSpace (UniversalCover p) := by
  obtain ⟨h, -⟩ := cartanHadamard_exists_homeomorph_universalCover hK p
  exact h.symm.contractibleSpace

/-- **A Cartan–Hadamard manifold is aspherical.** A connected complete Riemannian manifold of
nonpositive sectional curvature is aspherical: it is path-connected, and its homotopy groups in
every dimension at least two vanish. -/
theorem cartanHadamard_isAspherical [PreconnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    TauCeti.IsAspherical M p :=
  (cartanHadamard_isCoveringMap hK p).isAspherical (cartanHadamard_surjective hK p)
    (riemannianExp_zero p) (TauCeti.IsAspherical.mk inferInstance fun _ ↦ inferInstance)

end TauCeti.Manifold
