/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Geometry.Manifold.FiberBundle.Fiber
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Principal orbit maps onto regular fibres

For a point `p` of a smooth principal bundle, the right orbit map `g ↦ p·g` is a
diffeomorphism onto the fibre of the bundle projection. The target carries the independently
constructed regular-fibre atlas, with its subspace topology, rather than an atlas transported
from the group. Its inverse is division by `p`, computed in any principal trivialization.

The comparison is equivariant for right multiplication and changing `p` to `p·a`
precomposes it with left multiplication by `a`. Thus it identifies the smooth torsor
structure of each fibre, without choosing a global section. Only smooth multiplication
of the structure group is used; smooth inversion is not required.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §§10.2–10.3 (principal bundles and division).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience (1963),
  Chapter I, §5.
-/

public section

open Bundle MulOpposite
open scoped Manifold ContDiff

namespace TauCeti.PrincipalBundle

variable {n : ℕ∞ω} {B G : Type*} {P : B → Type*}
  {EB HB EG HG : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IB : ModelWithCorners ℝ EB HB} {IG : ModelWithCorners ℝ EG HG}
  [TopologicalSpace B] [ChartedSpace HB B] [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)] [FiberBundle G P]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [IsManifold IB n B] [ContMDiffMul IG n G]
  [ContMDiffFiberBundle n G P IB IG]
  [IB.Boundaryless] [IG.Boundaryless]
  [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EG]

local notation "T" => ManifoldTotalSpace G P
local notation "ι" => ManifoldTotalSpace.homeomorph G P
local notation "π₀" => fun x : T ↦ Bundle.TotalSpace.proj
  (Homeomorph.symm (ManifoldTotalSpace.homeomorph G P) x)
local notation "K" => 𝓘(ℝ, Fin (Module.finrank ℝ (EB × EG) - Module.finrank ℝ EB) → ℝ)

variable (hn : 1 ≤ n) {b : B}

variable (G IB IG) in
/-- The right orbit map through `p` is a diffeomorphism from the structure group onto the
actual regular fibre of the projection. The inverse sends `q` to the unique `g` with `p·g=q`. -/
noncomputable def orbitDiffeomorph (p : P b) :
    letI := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
    Diffeomorph IG K G {x : T // π₀ x = b} n := by
  letI := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
  haveI := ManifoldTotalSpace.isManifold_fiber G P IB IG hn b
  let e := trivializationAt G P b
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt G P b
  have he := ManifoldTotalSpace.isSmoothEmbedding_coe_fiber G P IB IG hn b
  exact {
    toFun g := ⟨ι ⟨b, op g • p⟩, by simp⟩
    invFun q := (e ⟨b, p⟩).2⁻¹ * (e ((ι).symm q.1)).2
    left_inv g := by simp [e.snd_apply_smul hb]
    right_inv q := by
      rcases q with ⟨q, hq⟩
      obtain ⟨⟨b', q⟩, rfl⟩ := (ι).surjective q
      simp only [Homeomorph.symm_apply_apply] at hq
      subst b'
      apply Subtype.ext
      simp only [Homeomorph.symm_apply_apply]
      rw [← division_eq_of_mem_baseSet hb, smul_division]
    contMDiff_toFun := he.contMDiff_iff_comp.2
      (ContMDiff.totalSpaceMk_smul contMDiff_const contMDiff_id)
    contMDiff_invFun := by
      rw [← contMDiffOn_univ]
      exact contMDiffOn_const.mul
        (ManifoldTotalSpace.contMDiffOn_trivialization_snd_comp e he.contMDiff.contMDiffOn
          fun q _ ↦ by simpa only [q.2] using hb)
  }

/-- The orbit diffeomorphism acts by the principal right action. -/
@[simp]
theorem orbitDiffeomorph_apply (p : P b) (g : G) :
    letI := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
    (orbitDiffeomorph G IB IG hn p g).1 = ι ⟨b, op g • p⟩ :=
  (rfl)

/-- The inverse orbit diffeomorphism is the principal division map. -/
@[simp]
theorem orbitDiffeomorph_symm_apply (p q : P b) :
    letI := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
    (orbitDiffeomorph G IB IG hn p).symm ⟨ι ⟨b, q⟩, by simp⟩ =
      division G p q := by
  apply (orbitDiffeomorph G IB IG hn p).injective
  simp only [Diffeomorph.coe_toEquiv, Diffeomorph.apply_symm_apply]
  apply Subtype.ext
  simp

/-- Multiplication in the group corresponds to the right action on the fibre. -/
theorem orbitDiffeomorph_mul (p : P b) (g h : G) :
    letI := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
    (orbitDiffeomorph G IB IG hn p (g * h)).1 =
      op h • (orbitDiffeomorph G IB IG hn p g).1 := by
  simp [op_mul, mul_smul]

/-- Changing the origin of the fibre from `p` to `p·a` is left multiplication by `a`
in group coordinates. -/
@[simp]
theorem orbitDiffeomorph_smul (p : P b) (a g : G) :
    letI := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
    orbitDiffeomorph G IB IG hn (op a • p) g =
      orbitDiffeomorph G IB IG hn p (a * g) := by
  apply Subtype.ext
  simp [op_mul, mul_smul]

/-- Applying the group coordinate of an arbitrary regular-fibre point recovers that point. -/
@[simp]
theorem op_orbitDiffeomorph_symm_smul (p : P b) (x : {x : T // π₀ x = b}) :
    letI := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
    ι ⟨b, op ((orbitDiffeomorph G IB IG hn p).symm x) • p⟩ = x.1 := by
  let := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
  exact congrArg Subtype.val ((orbitDiffeomorph G IB IG hn p).apply_symm_apply x)

/-- Changing the origin to `p·a` left-multiplies inverse orbit coordinates by `a⁻¹`. -/
@[simp]
theorem orbitDiffeomorph_smul_symm_apply (p : P b) (a : G)
    (x : {x : T // π₀ x = b}) :
    letI := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
    (orbitDiffeomorph G IB IG hn (op a • p)).symm x =
      a⁻¹ * (orbitDiffeomorph G IB IG hn p).symm x := by
  apply (orbitDiffeomorph G IB IG hn (op a • p)).injective
  simp

/-- The inverse orbit coordinates intertwine the right action with right multiplication. -/
theorem orbitDiffeomorph_symm_apply_smul (p : P b)
    (x : {x : T // π₀ x = b}) (h : G) :
    letI := ManifoldTotalSpace.fiberChartedSpace G P IB IG hn b
    (orbitDiffeomorph G IB IG hn p).symm
      ⟨op h • x.1, by simpa only [ManifoldTotalSpace.homeomorph_symm_smul] using x.2⟩ =
        (orbitDiffeomorph G IB IG hn p).symm x * h := by
  apply (orbitDiffeomorph G IB IG hn p).injective
  apply Subtype.ext
  simp only [Diffeomorph.coe_toEquiv, Diffeomorph.apply_symm_apply]
  rw [orbitDiffeomorph_mul]
  simp only [Diffeomorph.apply_symm_apply]

end TauCeti.PrincipalBundle
