/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Sublevel
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.ChainRule
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.RegularDomain.Basic

/-!
# The inward normal and the second fundamental form of a regular domain

Let `j : M → N` be a local Riemannian isometry from a Riemannian manifold with boundary `M` into a
Riemannian manifold `N`, and let `ρ : N → ℝ` be such that `ρ ∘ j` is a boundary defining function
of `M` near `q ∈ ∂M`. Then the boundary geometry of `M` at `q` is read off `ρ` in `N`:

* `dj(ν_in) = grad ρ / |grad ρ|` at `j q`
  (`TauCeti.IsBoundaryDefiningFunctionOn.mfderiv_inwardUnitNormal_of_comp`);
* `II_q(u, w) = -Hess^N ρ(dj dι u, dj dι w) / |grad^N ρ|`
  (`TauCeti.IsBoundaryDefiningFunctionOn.boundarySecondFundamentalForm_apply_of_comp`).

For the regular sublevel `D = {f ≤ a}` of a smooth function `f` on a boundaryless Riemannian
manifold `N`, with the pulled-back metric (`TauCeti.scalarRegularSublevelMetric`), the inclusion is
a local Riemannian isometry and `a - f` restricts to a global boundary defining function, so at a
point of the level `f⁻¹(a)`:

* `dj(ν_in) = -grad f / |grad f|`
  (`TauCeti.mfderiv_inwardUnitNormal_scalarRegularSublevel`);
* `II(u, w) = Hess^N f(dj dι u, dj dι w) / |grad^N f|`
  (`TauCeti.boundarySecondFundamentalForm_scalarRegularSublevel_apply`).

Writing a regular domain `D_ρ = {ρ ≥ 0}` as the sublevel `{-ρ ≤ 0}`, these are the formulas
`dj(ν_in) = grad ρ / |grad ρ|` and `II_{D_ρ} = -Hess^N ρ / |dρ|`.

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Section 3.1.
-/

public section

open Bundle Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

section Isometry

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 2 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {j : M → N} {ρ : N → ℝ} {U : Set M} {q : (𝓡∂ (n + 1)).boundary M}

omit [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)] in
/-- If `ρ ∘ j` is a boundary defining function near `q ∈ ∂M` for a local Riemannian isometry `j`,
the differential of `ρ ∘ j` at `q` has the length of the gradient of `ρ` at `j q`. -/
theorem IsLocalRiemannianIsometry.norm_mvfderiv_comp_eq_norm_mgradient
    (hj : IsLocalRiemannianIsometry (𝓡∂ (n + 1)) J j)
    (hρ : MDifferentiableAt J 𝓘(ℝ) ρ (j q)) :
    ‖mvfderiv (𝓡∂ (n + 1)) (ρ ∘ j) q‖ = ‖Manifold.mgradient J ρ (j q)‖ := by
  have : IsManifold (𝓡∂ (n + 1)) 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have : IsManifold J 1 N := IsManifold.of_le (n := 2) (by norm_num)
  rw [← Manifold.norm_mgradient_eq_norm_mvfderiv, hj.norm_mgradient_comp hρ]

omit [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)] in
/-- **The inward unit normal through a defining function in the ambient manifold.** If `j` is a
local Riemannian isometry and `ρ ∘ j` is a boundary defining function near `q ∈ ∂M`, then
`dj(ν_in) = grad ρ / |grad ρ|` at `j q`. -/
theorem IsBoundaryDefiningFunctionOn.mfderiv_inwardUnitNormal_of_comp
    (hρU : IsBoundaryDefiningFunctionOn n (ρ ∘ j) U)
    (hj : IsLocalRiemannianIsometry (𝓡∂ (n + 1)) J j) (hqU : (q : M) ∈ U)
    (hρ : MDifferentiableAt J 𝓘(ℝ) ρ (j q)) :
    mfderiv (𝓡∂ (n + 1)) J j q (inwardUnitNormal q) =
      ‖Manifold.mgradient J ρ (j q)‖⁻¹ • Manifold.mgradient J ρ (j q) := by
  have : IsManifold (𝓡∂ (n + 1)) 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have : IsManifold J 1 N := IsManifold.of_le (n := 2) (by norm_num)
  have hpos := hρU.norm_mvfderiv_pos hqU q.property
  rw [hj.norm_mvfderiv_comp_eq_norm_mgradient hρ] at hpos
  have h := congrArg (mfderiv (𝓡∂ (n + 1)) J j q)
    (hρU.mgradient_eq_norm_smul_inwardUnitNormal hqU)
  rw [hj.mfderiv_mgradient_comp hρ, map_smul, hj.norm_mvfderiv_comp_eq_norm_mgradient hρ] at h
  set c := ‖Manifold.mgradient J ρ (j q)‖
  rw [h, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

/-- **The second fundamental form through a defining function in the ambient manifold.** If `j` is
a local Riemannian isometry and `ρ ∘ j` is a boundary defining function near `q ∈ ∂M`, then
`II_q(u, w) = -Hess^N ρ(dj dι u, dj dι w) / |grad^N ρ|`, where `ι : ∂M → M` is the inclusion. -/
theorem IsBoundaryDefiningFunctionOn.boundarySecondFundamentalForm_apply_of_comp
    (hρU : IsBoundaryDefiningFunctionOn n (ρ ∘ j) U)
    (hj : IsLocalRiemannianIsometry (𝓡∂ (n + 1)) J j) (hqU : (q : M) ∈ U)
    (hρ : ContMDiffAt J 𝓘(ℝ) 2 ρ (j q)) (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundarySecondFundamentalForm q u w =
      -Manifold.hessian J ρ (j q)
          (mfderiv (𝓡∂ (n + 1)) J j q (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u))
          (mfderiv (𝓡∂ (n + 1)) J j q (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w)) /
        ‖Manifold.mgradient J ρ (j q)‖ := by
  rw [hρU.boundarySecondFundamentalForm_apply hqU, hj.hessian_comp hρ,
    hj.norm_mvfderiv_comp_eq_norm_mgradient (hρ.mdifferentiableAt (by norm_num))]

end Isometry

section Sublevel

variable {n : ℕ} {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace N]
  [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : N ↦ TangentSpace I y)]
  {f : N → ℝ} {a : ℝ}

omit [I.Boundaryless] [IsContMDiffRiemannianBundle I ∞ E (fun y : N ↦ TangentSpace I y)] in
/-- The gradient of `a - f` is minus the gradient of `f`. -/
private theorem mgradient_const_sub {x : N} (hfx : MDifferentiableAt I 𝓘(ℝ) f x) :
    Manifold.mgradient I (fun y ↦ a - f y) x = -Manifold.mgradient I f x := by
  apply ext_inner_right ℝ
  intro v
  rw [Manifold.inner_mgradient, inner_neg_left, Manifold.inner_mgradient,
    mvfderiv_fun_sub mdifferentiableAt_const hfx, mvfderiv_const, zero_sub,
    neg_apply]

omit [I.Boundaryless] in
/-- The Hessian of `a - f` is minus the Hessian of `f`. -/
private theorem hessian_const_sub {x : N} (hfx : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v w : TangentSpace I x) :
    Manifold.hessian I (fun y ↦ a - f y) x v w = -Manifold.hessian I f x v w := by
  have hd : deriv (fun t : ℝ ↦ a - t) = fun _ ↦ -1 := funext fun t ↦ by simp
  have h := Manifold.hessian_comp (h := fun t : ℝ ↦ a - t)
    (contDiffAt_const.sub contDiffAt_id) hfx v w
  rw [hd, deriv_const, zero_mul, zero_mul, add_zero, neg_one_mul] at h
  exact h

variable (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hreg : IsRegularValue I 𝓘(ℝ) f a)
  (hn : finrank ℝ E = n + 1)

/-- **The inward unit normal of a regular sublevel.** For the regular sublevel `D = {f ≤ a}` with
the pulled-back metric, the differential of the inclusion `j` maps the inward unit normal at a
point of the level `f⁻¹(a)` to `-grad f / |grad f|`. For a regular domain `{ρ ≥ 0} = {-ρ ≤ 0}`
this is `dj(ν_in) = grad ρ / |grad ρ|`. -/
theorem mfderiv_inwardUnitNormal_scalarRegularSublevel
    (q : letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
      (𝓡∂ (n + 1)).boundary {x | f x ≤ a}) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
    mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) q (inwardUnitNormal q) =
      -(‖Manifold.mgradient I f ((q : {x | f x ≤ a}) : N)‖⁻¹ •
        Manifold.mgradient I f ((q : {x | f x ≤ a}) : N)) := by
  let := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  have := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  let : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
  have hfx : MDifferentiableAt I 𝓘(ℝ) f ((q : {x | f x ≤ a}) : N) :=
    hf.mdifferentiableAt (by simp)
  have h := IsBoundaryDefiningFunctionOn.mfderiv_inwardUnitNormal_of_comp
    (ρ := fun y ↦ a - f y) (isBoundaryDefiningFunctionOn_scalarRegularSublevel hf hreg hn)
    (isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel hf hreg hn) (mem_univ _)
    (mdifferentiableAt_const.sub hfx)
  rw [h, mgradient_const_sub hfx, norm_neg, smul_neg]

/-- **The second fundamental form of a regular sublevel.** For the regular sublevel
`D = {f ≤ a}` with the pulled-back metric, at a point `q` of the level `f⁻¹(a)`,
`II_q(u, w) = Hess^N f(dj dι u, dj dι w) / |grad^N f|`, where `j : D → N` and `ι : ∂D → D` are the
inclusions. For a regular domain `{ρ ≥ 0} = {-ρ ≤ 0}` this is `II = -Hess^N ρ / |dρ|`. -/
theorem boundarySecondFundamentalForm_scalarRegularSublevel_apply
    (q : letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
      (𝓡∂ (n + 1)).boundary {x | f x ≤ a})
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric hf hreg hn).inner,
        (scalarRegularSublevelMetric hf hreg hn).contMDiff, fun _ _ _ ↦ rfl⟩
    boundarySecondFundamentalForm q u w =
      Manifold.hessian I f ((q : {x | f x ≤ a}) : N)
          (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) q
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
              (Subtype.val : (𝓡∂ (n + 1)).boundary {x | f x ≤ a} → {x | f x ≤ a}) q u))
          (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) q
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
              (Subtype.val : (𝓡∂ (n + 1)).boundary {x | f x ≤ a} → {x | f x ≤ a}) q w)) /
        ‖Manifold.mgradient I f ((q : {x | f x ≤ a}) : N)‖ := by
  let := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  have := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  let : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric hf hreg hn).inner,
      (scalarRegularSublevelMetric hf hreg hn).contMDiff, fun _ _ _ ↦ rfl⟩
  have hfx : ContMDiffAt I 𝓘(ℝ) 2 f ((q : {x | f x ≤ a}) : N) := (hf.of_le (by simp)) _
  rw [IsBoundaryDefiningFunctionOn.boundarySecondFundamentalForm_apply_of_comp
    (ρ := fun y ↦ a - f y) (isBoundaryDefiningFunctionOn_scalarRegularSublevel hf hreg hn)
    (isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel hf hreg hn) (mem_univ _)
    (contMDiffAt_const.sub hfx), hessian_const_sub hfx,
    mgradient_const_sub (hfx.mdifferentiableAt (by simp)), norm_neg, neg_neg]

end Sublevel

end TauCeti
