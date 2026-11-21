/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Character
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
import TauCeti.Analysis.Normed.Group.Prod
import TauCeti.Analysis.Normed.Module.Prod
import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Symplectic.Darboux.EuclideanBasis
import TauCeti.Geometry.Symplectic.Manifold.EquivariantDarboux
import TauCeti.Geometry.Symplectic.Manifold.Invariants
import TauCeti.Geometry.Symplectic.WeightDecomposition

/-!
# The weight normal form of a Hamiltonian torus action at a fixed point

Let a compact commutative Lie group `G`, such as a torus, act smoothly on a finite-dimensional
symplectic manifold `(M, σ)` without boundary, preserving `σ`, with moment map
`μ : M → 𝔤*` (`d⟨μ, ξ⟩ = ι_{ξ_M} σ` for the fundamental vector fields `ξ_M`), and let `p` be a
fixed point of the action. This file proves that near `p` the action, the form and the moment map
are those of the linear weight model of `TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic`
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`). There are continuous characters
`χ₁, …, χₙ : G → S¹`, with real weights `αₖ ∈ 𝔤*` determined by `χₖ (exp ξ) = e^{i αₖ(ξ)}`, and a
smooth chart `z = (q, p)` of `M` at `p` with values in `ℂⁿ = ℝⁿ × ℝⁿ` and `z(p) = 0`, whose image
is a round ball `‖q‖² + ‖p‖² < r²`, such that

* the source of the chart is `G`-invariant and `g` acts by `zₖ ↦ χₖ(g) zₖ`;
* the chart pulls the standard form `Σ dqₖ ∧ dpₖ` back to `σ`;
* the chart sends the fundamental vector field `ξ_M` to the model one
  (`TauCeti.weightInfinitesimalAction`), the generator of the rotation by the angles `αₖ(ξ)`;
* the moment map is the model one up to its value at `p`:

  `μ = μ(p) - ½ Σₖ (qₖ² + pₖ²) αₖ`.

So near `p` the image of `μ` lies in `μ(p) - cone{αₖ}`, and the component `μ^ξ` is, in these
symplectic coordinates, the constant `μ^ξ(p)` plus the quadratic form
`-½ Σₖ αₖ(ξ) (qₖ² + pₖ²)`. This is the chart through
which the results on the model, such as `TauCeti.range_weightMomentMap`,
`TauCeti.weightRotation_apply_eq_self_iff`, `TauCeti.finrank_range_weightInfinitesimalAction` and
`TauCeti.morseIndex_weightMomentMap_apply`, are read on `M`. The weights are integral on the
period lattice: `αₖ(ξ) ∈ ℤ` whenever `exp (2π ξ) = 1`.

Without a moment map the same chart exists for any symplectic action of a compact commutative
group with a fixed point (`TauCeti.SmoothTwoForm.IsSymplectic.exists_weightRotation_darbouxChart`),
and its linear part is the weight decomposition of a symplectic representation in standard
coordinates (`TauCeti.SymplecticForm.exists_continuousLinearEquiv_weightRotation`).

The proof composes three linearizations. The equivariant Darboux theorem
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart`) gives a chart into
`T_p M` in which `G` acts through its isotropy representation and `σ` is constant. The isotropy
representation of the compact commutative group `G` on the symplectic space `(T_p M, σ_p)` splits
into rotations of complex lines in a Darboux basis
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq`), whose coordinates identify
`T_p M` symplectically with `ℂⁿ`. In the resulting chart the curve `t ↦ exp (t ξ) • x` is the
rotation by the angles `t αₖ(ξ)` (`ContinuousMonoidHom.apply_lieExp_eq_circleExp_lieWeight`), so
the chart carries `ξ_M` to the generator of that rotation. Both `μ^ξ` and the model component
`-½ Σₖ αₖ(ξ) (qₖ² + pₖ²)` then have Hamiltonian vector field `ξ_M`
(`TauCeti.stdSymplecticForm_weightInfinitesimalAction`), so their difference has zero derivative
on the connected ball and is the constant `μ^ξ(p)`.

## Main results

* `TauCeti.SymplecticForm.exists_continuousLinearEquiv_weightRotation`: a symplectic
  representation of a compact commutative group is, in linear symplectic coordinates `V ≃ ℂⁿ`,
  the rotation of the coordinates by characters.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_weightRotation_darbouxChart`: the equivariant Darboux
  theorem in these coordinates, on a round ball around a fixed point.
* `TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`: the weight normal form of a
  Hamiltonian action of a compact commutative Lie group at a fixed point.

## References

* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, Section 2 (the local form of the moment map at a fixed point).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 22 and 27 (equivariant Darboux and the weights at a fixed point).
* J. Hilgert, K.-H. Neeb and W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Math. 94 (1994), 129–180, Lemmas 2.1–2.2 (the quadratic weight formula).
-/

public section

noncomputable section

open Set Real
open scoped Manifold

namespace TauCeti

namespace SymplecticForm

/-- **The linear weight normal form.** A continuous representation `ρ` of a compact commutative
group `G` on a finite-dimensional symplectic space `(V, ω)` preserving `ω` is, in suitable linear
symplectic coordinates `L : V ≃ ℂⁿ`, the action of `n` continuous characters `χₖ : G → S¹` by
rotation of the coordinates: `L (ρ g v) = (χₖ(g) L(v)ₖ)ₖ`, and `L` carries `ω` to the standard
form. -/
theorem exists_continuousLinearEquiv_weightRotation {V G : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (ω : SymplecticForm V) (ρ : ContRepresentation ℝ G V)
    (hρ : Continuous ρ) (hω : ∀ g u v, ω (ρ g u) (ρ g v) = ω u v) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle)
      (L : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      (∀ u v, stdSymplecticForm (L u) (L v) = ω u v) ∧
      ∀ g v, L (ρ g v) = weightRotation (fun k ↦ Complex.arg (χ k g)) (L v) := by
  obtain ⟨n, b, χ, hb, hbχ⟩ := exists_isDarbouxBasis_forall_apply_eq ω ρ hρ hω
  refine ⟨n, χ, b.darbouxBasisContinuousLinearEquiv, fun u v ↦ ?_, fun g v ↦ ?_⟩
  · rw [Module.Basis.coe_darbouxBasisContinuousLinearEquiv]
    exact hb.isSymplectomorphism_darbouxBasisEquiv.apply u v
  have hcos (k : Fin n) : cos (Complex.arg (χ k g)) = (χ k g : ℂ).re := by
    rw [Complex.cos_arg (Circle.coe_ne_zero _), Circle.norm_coe, div_one]
  have hsin (k : Fin n) : sin (Complex.arg (χ k g)) = (χ k g : ℂ).im := by
    rw [Complex.sin_arg, Circle.norm_coe, div_one]
  -- Both sides are linear in `v`, and they agree on the Darboux basis.
  have key : b.darbouxBasisEquiv.toLinearMap ∘ₗ (ρ g).toLinearMap =
      (weightRotation fun k ↦ Complex.arg (χ k g)).toLinearMap ∘ₗ
        b.darbouxBasisEquiv.toLinearMap := by
    refine b.ext fun ⟨k, j⟩ ↦ ?_
    rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with rfl | rfl <;>
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
        (hbχ g k).1, (hbχ g k).2, map_add, map_smul, Module.Basis.darbouxBasisEquiv_apply_zero,
        Module.Basis.darbouxBasisEquiv_apply_one] <;>
      ext m <;> by_cases hm : m = k <;> simp [hm, hcos, hsin]
  rw [Module.Basis.coe_darbouxBasisContinuousLinearEquiv]
  exact LinearMap.congr_fun key v

end SymplecticForm

namespace SmoothTwoForm

open scoped ContDiff

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] {σ : SmoothTwoForm I' M}

section Darboux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [IsManifold I ∞ G] [CommGroup G]
  [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] [ContMDiffSMul I I' ∞ G M]

omit [I'.Boundaryless] [I.Boundaryless] in
/-- The isotropy representation `g ↦ d(g • ·)_p` at a fixed point `p` of a compact commutative
group preserving `σ` is, in linear symplectic coordinates `L : (T_p M, σ_p) ≃ ℂⁿ`, the rotation of
the coordinates by continuous characters. -/
private theorem IsNondegenerate.exists_continuousLinearEquiv_mfderiv_smul
    (hσ : σ.IsNondegenerate)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle)
      (L : E' ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      (∀ u v, stdSymplecticForm (L u) (L v) = hσ.symplecticFormAt p u v) ∧
      ∀ g v, L (mfderiv I' I' (fun y : M ↦ g • y) p v) =
        weightRotation (fun k ↦ Complex.arg (χ k g)) (L v) := by
  have hd : ∀ g ∈ MulAction.stabilizer G p, MDifferentiableAt I' I' (fun y : M ↦ g • y) p :=
    fun g _ ↦ (ContMDiffSMul.contMDiff_const_smul (I := I) (n := ∞) g).mdifferentiableAt
      (by simp)
  -- The tangent representation of the stabilizer `G` of `p`, read as a representation of `G`.
  let ρ : ContRepresentation ℝ G E' :=
    .ofMonoidHom ((tangentRepresentation hd).toMonoidHom.comp
      (MonoidHom.codRestrict (MonoidHom.id G) (MulAction.stabilizer G p)
        fun g ↦ MulAction.mem_stabilizer_iff.2 (hp g)))
  have hρ (g : G) : ρ g = mfderiv I' I' (fun y : M ↦ g • y) p := tangentRepresentation_apply hd _
  -- `σ_p`, as a symplectic form on the model space `E' = T_p M`.
  let ωₚ : SymplecticForm E' := hσ.symplecticFormAt p
  have hω (g : G) (u v : TangentSpace I' p) : ωₚ (ρ g u) (ρ g v) = ωₚ u v :=
    -- The invariance lemma is stated for actions by individually smooth maps.
    have : ContMDiffConstSMul I' ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := I)⟩
    hσ.symplecticFormAt_tangentRepresentation (fun g _ ↦ hG g) hd ⟨g, hp g⟩ u v
  obtain ⟨n, χ, L, hL, hLρ⟩ := SymplecticForm.exists_continuousLinearEquiv_weightRotation ωₚ ρ
    ((continuous_tangentRepresentation I hd).comp (continuous_id.subtype_mk _)) hω
  exact ⟨n, χ, L, hL, fun g v ↦ (congrArg L (DFunLike.congr_fun (hρ g) v)).symm.trans (hLρ g v)⟩

/-- **The equivariant Darboux theorem in weight coordinates.** Let a compact commutative group
`G`, a manifold without boundary, act smoothly on a finite-dimensional manifold `M` without
boundary, preserving a symplectic form `σ`, and let `p` be a fixed point. Then there are
continuous characters `χₖ : G → S¹`, `k < n`, and a smooth chart of `M` at `p` with values in
`ℂⁿ = ℝⁿ × ℝⁿ`, sending `p` to `0`, whose image is the ball `‖q‖² + ‖p‖² < r²`, such that its
source is `G`-invariant, `g` acts in it by the rotation `zₖ ↦ χₖ(g) zₖ`, and it pulls the standard
symplectic form back to `σ`. -/
theorem IsSymplectic.exists_weightRotation_darbouxChart (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle)
      (chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
        M (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞) (r : ℝ),
      p ∈ chart.source ∧ chart p = 0 ∧ 0 < r ∧
      chart.target = {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2} ∧
      (∀ g : G, ∀ x ∈ chart.source, g • x ∈ chart.source ∧
        chart (g • x) = weightRotation (fun k ↦ Complex.arg (χ k g)) (chart x)) ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I' x,
        σ.eval₂ x v w = stdSymplecticForm (mvfderiv I' chart x v) (mvfderiv I' chart x w) := by
  obtain ⟨n, χ, L, hL, hLd⟩ := hσ.isNondegenerate.exists_continuousLinearEquiv_mfderiv_smul
    (I := I) hG hp
  -- The equivariant Darboux chart at `p`, followed by these coordinates.
  obtain ⟨c₀, hpc₀, hc₀p, hc₀G, hc₀σ, -⟩ := hσ.exists_equivariant_darbouxChart (IG := I) hG hp
  let c₁ := c₀.trans (L.toPartialDiffeomorph (n := ∞))
  have hc₁ : (c₁ : M → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) = L ∘ c₀ := by
    rw [PartialDiffeomorph.coe_trans, ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
    simp only [Equiv.toPartialEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv]
  have hc₁s : c₁.source = c₀.source := by simp [c₁]
  have hc₁p : c₁ p = 0 := by rw [hc₁, Function.comp_apply, hc₀p, map_zero]
  -- Restrict `c₁` to the preimage of a round ball in its target.
  obtain ⟨r, hr, hBt⟩ := exists_setOf_norm_fst_sq_add_norm_snd_sq_lt_subset
    (c₁.open_target.mem_nhds (hc₁p ▸ c₁.map_source (hc₁s ▸ hpc₀)))
  set B := {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
    ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2} with hB
  have hBo : IsOpen B := isOpen_lt (by fun_prop) continuous_const
  have hso : IsOpen (c₁.source ∩ c₁ ⁻¹' B) :=
    c₁.contMDiffOn.continuousOn.isOpen_inter_preimage c₁.open_source hBo
  let chart := c₁.restrOpen _ hso
  have hchart : (chart : M → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) = L ∘ c₀ :=
    (PartialDiffeomorph.coe_restrOpen _ _).trans hc₁
  have hmem {x : M} : x ∈ chart.source ↔ x ∈ c₀.source ∧ L (c₀ x) ∈ B := by
    simp [chart, hc₁s, hc₁]
  refine ⟨n, χ, chart, r, hmem.2 ⟨hpc₀, by simp [hc₀p, hB, hr]⟩,
    by rw [hchart, Function.comp_apply, hc₀p, map_zero], hr, ?_, fun g x hx ↦ ?_,
    fun x hx v w ↦ ?_⟩
  · ext z
    simp only [chart, PartialDiffeomorph.restrOpen_target, mem_inter_iff, mem_preimage]
    refine ⟨fun ⟨hz, _, hzB⟩ ↦ ?_, fun hz ↦ ⟨hBt hz, c₁.map_target (hBt hz), ?_⟩⟩
    · rwa [c₁.right_inv hz] at hzB
    · rwa [c₁.right_inv (hBt hz)]
  · -- `G` acts in the chart by the rotations `zₖ ↦ χₖ(g) zₖ`, which preserve the ball.
    obtain ⟨hx₀, hxB⟩ := hmem.1 hx
    obtain ⟨hgx, hcgx⟩ := hc₀G g x hx₀
    have hrot : L (c₀ (g • x)) = weightRotation (fun k ↦ Complex.arg (χ k g)) (L (c₀ x)) := by
      rw [hcgx]
      exact hLd g _
    rw [hchart, Function.comp_apply, Function.comp_apply, hrot]
    refine ⟨hmem.2 ⟨hgx, ?_⟩, rfl⟩
    rw [hrot, hB, Set.mem_ofPred_eq, norm_fst_sq_add_norm_snd_sq_weightRotation]
    exact hxB
  · -- The chart is `L ∘ c₀`, and `L` carries `σ_p` to the standard form.
    have hdchart (u : TangentSpace I' x) : mvfderiv I' chart x u = L (mvfderiv I' c₀ x u) := by
      rw [hchart, mvfderiv_comp_apply x L.differentiableAt.mdifferentiableAt
        (c₀.mdifferentiableAt (by simp) (hmem.1 hx).1), mvfderiv_eq_fderiv_apply, L.fderiv,
        mvfderiv_apply_eq_mfderiv_apply]
      rw [ContinuousLinearEquiv.coe_coe]
    rw [hdchart, hdchart, hL, hc₀σ x (hmem.1 hx).1]

end Darboux

namespace IsMomentMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

omit [FiniteDimensional ℝ E'] [I'.Boundaryless] [IsManifold I' ∞ M] [IsTopologicalGroup G]
  [CompactSpace G] in
/-- Let `f : M → ℂ^ι` be differentiable at `x`, and let `g` act near `x` through `f` by the rotation
`zₖ ↦ χₖ(g) zₖ`, for characters `χₖ` with real weights `αₖ`, `χₖ (exp ξ) = e^{i αₖ(ξ)}`. Then `f`
sends the fundamental vector field `ξ_M` at `x` to the generator of the rotation by the angles
`αₖ(ξ)`: along `t ↦ exp (t ξ) • x`, the map `f` is the rotation by the angles `t αₖ(ξ)`. -/
private theorem mfderiv_fundamentalVectorField_eq_weightGenerator {ι : Type*} [Fintype ι]
    {f : M → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} {x : M}
    (hf : MDifferentiableAt I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x)
    {χ : ι → G →ₜ* Circle} {α : ι → StrongDual ℝ E}
    (hα : ∀ k (ξ : GroupLieAlgebra I G), χ k (mulInvariantExp (I := I) ξ) = Circle.exp (α k ξ))
    (hχ : ∀ g : G, f (g • x) = weightRotation (fun k ↦ Complex.arg (χ k g)) (f x))
    (ξ : GroupLieAlgebra I G) :
    mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x
      (fundamentalVectorField I' ξ x) = weightGenerator (fun k ↦ α k ξ) (f x) := by
  -- `exp (t ξ)` acts by the rotation by the angles `t αₖ(ξ)`. The Lie algebra is the model space
  -- `E` by definition, so `αₖ` is linear on it.
  have hcurve (t : ℝ) : f (mulInvariantExp (I := I) (t • ξ) • x) =
      weightRotation (t • fun k ↦ α k ξ) (f x) := by
    have hθ : (fun k ↦ Complex.arg (χ k (mulInvariantExp (I := I) (t • ξ)))) =
        fun k ↦ Complex.arg (Circle.exp ((t • fun k ↦ α k ξ) k)) := by
      funext k
      rw [hα]
      exact congrArg (fun a ↦ Complex.arg (Circle.exp a)) ((α k).map_smul t ξ)
    rw [hχ, hθ, weightRotation_arg_circleExp]
  have hx : mulInvariantExp (I := I) ((0 : ℝ) • ξ) • x = x := by
    rw [zero_smul, mulInvariantExp_zero, one_smul]
  -- Differentiate `t ↦ f (exp (t ξ) • x)` at `t = 0` in two ways.
  have hcomp := (hx ▸ hf).hasMFDerivAt.comp 0
    (isMIntegralCurve_mulInvariantExp_smul_smul (I := I) (I' := I') ξ x 0)
  have hmodel := hasDerivAt_weightRotation_smul (fun k ↦ α k ξ) (f x) 0
  rw [zero_smul, weightRotation_zero, ContinuousLinearMap.id_apply,
    show (fun s : ℝ ↦ weightRotation (s • fun k ↦ α k ξ) (f x)) =
      f ∘ fun s : ℝ ↦ mulInvariantExp (I := I) (s • ξ) • x from (funext hcurve).symm] at hmodel
  have hd := congrArg (fun T ↦ T (1 : ℝ))
    (hcomp.mfderiv.symm.trans hmodel.hasFDerivAt.hasMFDerivAt.mfderiv)
  beta_reduce at hd
  rw [hx] at hd
  have e₁ : ((mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (fundamentalVectorField I' ξ x))) (1 : ℝ) =
      mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x
        (fundamentalVectorField I' ξ x) := by
    simp
  have e₂ : ContinuousLinearMap.toSpanSingleton ℝ (weightGenerator (fun k ↦ α k ξ) (f x))
      (1 : ℝ) = weightGenerator (fun k ↦ α k ξ) (f x) := by
    simp
  exact e₁.symm.trans (hd.trans e₂)

omit [I'.Boundaryless] [I.Boundaryless] [T2Space G] [IsTopologicalGroup G] [CompactSpace G] in
/-- Let `f : M → ℂ^ι` be a chart at `x` pulling the standard form back to `σ`, which sends `ξ_M`
at `x` to the generator of the rotation by the angles `αₖ(ξ)`. Then the component `μ^ξ` of a
moment map and the model component `-½ Σₖ αₖ(ξ) (qₖ² + pₖ²)` read through `f` have the same
differential at `x`: both are contractions of `σ` with `ξ_M`. -/
private theorem mfderiv_sub_weightMomentMap_eq_zero
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {ι : Type*} [Fintype ι]
    {f : M → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} {x : M}
    (hf : MDifferentiableAt I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x)
    (hform : ∀ v w : TangentSpace I' x,
      σ.eval₂ x v w = stdSymplecticForm (mvfderiv I' f x v) (mvfderiv I' f x w))
    {α : ι → StrongDual ℝ E} (ξ : GroupLieAlgebra I G)
    (hgen : mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x
      (fundamentalVectorField I' ξ x) = weightGenerator (fun k ↦ α k ξ) (f x)) :
    MDifferentiableAt I' 𝓘(ℝ) ((fun y ↦ μ y ξ) - fun y ↦ weightMomentMap α (f y) ξ) x ∧
      mfderiv I' 𝓘(ℝ) ((fun y ↦ μ y ξ) - fun y ↦ weightMomentMap α (f y) ξ) x = 0 := by
  -- The model component is `f` followed by the evaluation at `ξ`, viewed in the model space `E`
  -- of the Lie algebra, of the model moment map.
  have hd := (ContinuousLinearMap.apply ℝ ℝ (show E from ξ)).hasFDerivAt.comp (f x)
    (hasFDerivAt_weightMomentMap α (f x)).differentiableAt.hasFDerivAt
  have hWc : (fun y ↦ weightMomentMap α (f y) ξ) =
      (⇑(ContinuousLinearMap.apply ℝ ℝ (show E from ξ)) ∘ weightMomentMap α) ∘ f := (rfl)
  have hWd := hWc ▸ hd.differentiableAt.comp_mdifferentiableAt hf
  refine ⟨(hμ.mdifferentiableAt ξ x).sub hWd, ContinuousLinearMap.ext fun v ↦ ?_⟩
  have hμv : mvfderiv I' (fun y ↦ μ y ξ) x v =
      fderiv ℝ (weightMomentMap α) (f x) (mvfderiv I' f x v) ξ := by
    rw [← hμ.eval₂_apply, InfinitesimalAction.fundamental_apply, hform,
      mvfderiv_apply_eq_mfderiv_apply f x (fundamentalVectorField I' ξ x), hgen]
    have h := stdSymplecticForm_weightInfinitesimalAction α (f x) (mvfderiv I' f x v)
      (show E from ξ)
    rw [weightInfinitesimalAction_apply] at h
    exact h
  have hWv : mvfderiv I' (fun y ↦ weightMomentMap α (f y) ξ) x v =
      fderiv ℝ (weightMomentMap α) (f x) (mvfderiv I' f x v) ξ := by
    rw [hWc, mvfderiv_comp_apply x hd.differentiableAt.mdifferentiableAt hf,
      mvfderiv_eq_fderiv_apply, hd.fderiv]
    -- The tangent spaces of a normed space are the space itself, so `mvfderiv` and `mfderiv`
    -- of `f` agree, and the evaluation map unfolds.
    rfl
  have h := DFunLike.congr_fun (mvfderiv_sub (hμ.mdifferentiableAt ξ x) hWd) v
  rw [sub_apply, hμv, hWv, sub_self] at h
  rw [← mvfderiv_apply_eq_mfderiv_apply]
  exact h

/-- **The weight normal form at a fixed point.** Let a compact commutative Lie group `G`, with Lie
algebra `𝔤 = E`, act smoothly on a finite-dimensional symplectic manifold `(M, σ)` without
boundary, preserving `σ`, with moment map `μ`, and let `p` be a fixed point. Then there are
continuous characters `χₖ : G → S¹`, `k < n`, with real weights `αₖ ∈ 𝔤*` determined by
`χₖ (exp ξ) = e^{i αₖ(ξ)}`, and a smooth chart of `M` at `p` with values in `ℂⁿ = ℝⁿ × ℝⁿ`,
sending `p` to `0`, whose image is the ball `‖q‖² + ‖p‖² < r²`, such that

* its source is `G`-invariant and `g` acts in it by the rotation `zₖ ↦ χₖ(g) zₖ`;
* it pulls the standard symplectic form back to `σ`;
* its differential sends the fundamental vector field `ξ_M` to the model one,
  `weightInfinitesimalAction α · ξ`, the generator of the rotation by the angles `αₖ(ξ)`;
* `μ = μ(p) - ½ Σₖ (qₖ² + pₖ²) αₖ` on its source.

The weights are integral on the period lattice: `αₖ(ξ) ∈ ℤ` whenever `exp (2π ξ) = 1`. -/
theorem exists_weightModelChart (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle) (α : Fin n → StrongDual ℝ E)
      (chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
        M (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞) (r : ℝ),
      (∀ k (ξ : GroupLieAlgebra I G), χ k (mulInvariantExp (I := I) ξ) = Circle.exp (α k ξ)) ∧
      (∀ k (ξ : GroupLieAlgebra I G), mulInvariantExp (I := I) ((2 * π) • ξ) = 1 →
        ∃ m : ℤ, α k ξ = m) ∧
      p ∈ chart.source ∧ chart p = 0 ∧ 0 < r ∧
      chart.target = {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2} ∧
      (∀ g : G, ∀ x ∈ chart.source, g • x ∈ chart.source ∧
        chart (g • x) = weightRotation (fun k ↦ Complex.arg (χ k g)) (chart x)) ∧
      (∀ x ∈ chart.source, ∀ v w : TangentSpace I' x,
        σ.eval₂ x v w = stdSymplecticForm (mvfderiv I' chart x v) (mvfderiv I' chart x w)) ∧
      (∀ x ∈ chart.source, ∀ ξ : GroupLieAlgebra I G,
        mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) chart x
          (fundamentalVectorField I' ξ x) = weightInfinitesimalAction α (chart x) ξ) ∧
      ∀ x ∈ chart.source, ∀ ξ, μ x ξ = μ p ξ + weightMomentMap α (chart x) ξ := by
  obtain ⟨n, χ, chart, r, hpchart, hchartp, hr, htarget, hequiv, hform⟩ :=
    hσ.exists_weightRotation_darbouxChart (I := I) hG hp
  -- The real weights `αₖ` of the characters, read on `𝔤` through the identification of `𝔤` with
  -- the left-invariant derivations.
  let ε := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  let α : Fin n → StrongDual ℝ E := fun k ↦
    LinearMap.toContinuousLinearMap (ContinuousMonoidHom.lieWeight (χ k) ∘ₗ ε.symm.toLinearMap)
  have hα (k : Fin n) (ξ : GroupLieAlgebra I G) :
      χ k (mulInvariantExp (I := I) ξ) = Circle.exp (α k ξ) := by
    have h := ContinuousMonoidHom.apply_lieExp_eq_circleExp_lieWeight (χ k) (ε.symm ξ)
    rwa [lieExp_eq_mulInvariantExp, LinearEquiv.apply_symm_apply] at h
  -- In the chart, `ξ_M` is the generator of the rotation by the angles `αₖ(ξ)`.
  have hgen (y : M) (hy : y ∈ chart.source) (ξ : GroupLieAlgebra I G) :=
    mfderiv_fundamentalVectorField_eq_weightGenerator (chart.mdifferentiableAt (by simp) hy) hα
      (fun g ↦ (hequiv g y hy).2) ξ
  refine ⟨n, χ, α, chart, r, hα, fun k ξ hξ ↦ ?_, hpchart, hchartp, hr, htarget, hequiv, hform,
    fun y hy ξ ↦ (hgen y hy ξ).trans (weightInfinitesimalAction_apply α (chart y) ξ).symm,
    fun x hx ξ ↦ ?_⟩
  · -- Integrality: `ε⁻¹ ξ` lies in the period lattice, where weights take integer values.
    exact (χ k).exists_lieWeight_apply_eq_intCast_of_mem_periodLattice (X := ε.symm ξ)
      (mem_periodLattice.2 (by rwa [← map_smul, lieExp_eq_mulInvariantExp,
        LinearEquiv.apply_symm_apply]))
  -- As the chart sends `ξ_M` to the model generator, `μ^ξ` minus the model component
  -- `-½ Σₖ αₖ(ξ) (qₖ² + pₖ²)` has zero differential on the source.
  set F : M → ℝ := (fun y ↦ μ y ξ) - fun y ↦ weightMomentMap α (chart y) ξ
  have hF {y : M} (hy : y ∈ chart.source) :
      MDifferentiableAt I' 𝓘(ℝ) F y ∧ mfderiv I' 𝓘(ℝ) F y = 0 :=
    mfderiv_sub_weightMomentMap_eq_zero hμ (chart.mdifferentiableAt (by simp) hy) (hform y hy) ξ
      (hgen y hy ξ)
  -- The source of the chart is connected, being the preimage of a ball, so `F` is constant there.
  have hsrc : IsPreconnected chart.source := by
    have hB := (convex_setOf_norm_fst_sq_add_norm_snd_sq_lt (E := EuclideanSpace ℝ (Fin n))
      (F := EuclideanSpace ℝ (Fin n)) (r ^ 2)).isPreconnected
    rw [← htarget] at hB
    rw [← chart.toPartialEquiv.symm_image_target_eq_source]
    exact hB.image _ chart.contMDiffOn_invFun.continuousOn
  have : PreconnectedSpace chart.source := isPreconnected_iff_preconnectedSpace.1 hsrc
  have hloc : IsLocallyConstant (chart.source.domRestrict F) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun z ↦
      (continuous_subtypeVal.tendsto z).eventually
        (MDifferentiableOn.eventuallyEq_const_of_mfderiv_eq_zero
          (fun y hy ↦ (hF hy).1.mdifferentiableWithinAt) chart.open_source
          (fun y hy ↦ (hF hy).2) z.property)
  have hFx := hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨p, hpchart⟩
  have h0 : (0 : StrongDual ℝ E) ξ = 0 := zero_apply _
  simp only [Set.domRestrict, F, Pi.sub_apply, hchartp, weightMomentMap_zero, h0,
    sub_zero] at hFx
  linarith

end IsMomentMap

end SmoothTwoForm

end TauCeti
