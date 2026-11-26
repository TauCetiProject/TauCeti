/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InvariantForm.RankOne
public import TauCeti.RepresentationTheory.SU2.LieGroup
import TauCeti.Geometry.Lie.Integration

/-!
# The rank-one homomorphisms `SU(2) → G` of the roots of a compact Lie group

Let `G` be a Lie group with a symmetric positive definite invariant form `B` on its Lie algebra
`𝔤`, for instance a compact Lie group with an averaged inner product, and let `t ⊆ 𝔤` be a
subspace, for instance the Lie algebra of a maximal torus. A root pair `x ≠ 0, y` of `t` with
nonzero root `α`, `⁅H, x⁆ = α(H) y` and `⁅H, y⁆ = -α(H) x` for `H ∈ t`, spans with `⁅x, y⁆ ∈ t` a
copy of `𝔰𝔲(2)` (`LinearMap.BilinForm.exists_injective_lieHom_soThree_of_lie_eq_smul`). Since the
Lie group `SU(2)` is simply connected, this Lie algebra homomorphism integrates
(`LieHom.integrate`) to the **rank-one homomorphism** of the root,

`φ_α : SU(2) → G`

(`LinearMap.BilinForm.exists_contMDiffMonoidMorphism_of_lie_eq_smul`, and
`TauCeti.IsRootPlane.exists_contMDiffMonoidMorphism` for a root plane). It is a smooth homomorphism
with injective differential, and its differential is calibrated by the coroot:

`dφ_α(diag(i, -i)) = α∨`,

where `α∨ ∈ t` has `α(α∨) = 2` and is `B`-orthogonal to `ker α`, so `α∨ = 2 α♯ / ‖α‖²` is the coroot
of `α` for the metric `B`. The differential sends the real root vectors `-iσ₁/2, -iσ₂/2` of
`𝔰𝔲(2)` to the same positive multiple of `y` and `x`. The root vectors are not canonical, since
every rotation of `x, y` in their plane is again a root pair, so the rank-one homomorphism is
stated as an existence statement.

Every smooth homomorphism `φ : SU(2) → G` sends the diagonal torus `diag(e^{is}, e^{-is})` to
the one-parameter subgroup of `v = dφ(diag(i, -i))`, which has period `2π`: `exp_G(2π v) = 1`
(`ContMDiffMonoidMorphism.lieExp_two_pi_smul_lieMap_torusGenerator`, in
`TauCeti.RepresentationTheory.SU2.LieGroup`). For the rank-one homomorphism of a root this says
that `α∨` lies in the period lattice `Λ_ℤ = (2π)⁻¹ ker(exp_G)`: **the coroot is an integral
cocharacter**. If `v ≠ 0`, then `φ` is not trivial, and its kernel lies in the center `{1, -1}` of
`SU(2)` (`ContMDiffMonoidMorphism.ker_le_center_of_lieMap_ne_zero`, also in
`TauCeti.RepresentationTheory.SU2.LieGroup`). This applies to every rank-one homomorphism, since
`α(α∨) = 2` forces `α∨ ≠ 0`.

## Main results

* `LinearMap.BilinForm.exists_contMDiffMonoidMorphism_of_lie_eq_smul`,
  `TauCeti.IsRootPlane.exists_contMDiffMonoidMorphism`: the rank-one homomorphism of a root, with
  its coroot calibration.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, GTM 98, Springer, 1985,
  Chapter V, § 2 (the subgroups `SU(2)` and `SO(3)` attached to the roots).
* B. Conrad and C. Landesman, *Compact Lie Groups*, Appendix R, Proposition R.2.1 and its proof
  (integrality of the coroot), and § 18 (the kernel of a rank-one homomorphism).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

open TauCeti

open LieAlgebra.Orthogonal

namespace LinearMap.BilinForm

-- Use the operator-norm topology under which `GL(2, ℂ)` is a Lie group, as in
-- `TauCeti.RepresentationTheory.SU2.LieGroup`.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal

open scoped Matrix.Norms.Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [SecondCountableTopology G]

/-- **The rank-one homomorphism of a root.** Let `B` be a symmetric positive definite invariant form
on the Lie algebra `𝔤` of a Lie group `G`, let `t ⊆ 𝔤` be a subspace, and let `x ≠ 0, y` be a root
pair of `t` with nonzero root `α`, `⁅H, x⁆ = α(H) y` and `⁅H, y⁆ = -α(H) x` for `H ∈ t`, with
`⁅x, y⁆ ∈ t`. Then there is a smooth homomorphism `φ : SU(2) → G` with injective differential whose
differential sends

* `diag(i, -i)` to the coroot `α∨` of `α`: an element of `t` with `α(α∨) = 2`, `B`-orthogonal to
  the kernel of `α`;
* the real root vectors `-iσ₁/2` and `-iσ₂/2` of `𝔰𝔲(2)` to the same positive multiple of `y` and
  `x`.

By `ContMDiffMonoidMorphism.map_torusExp` it sends `diag(e^{is}, e^{-is})` to `exp_G(s α∨)`, so
`exp_G(2π α∨) = 1`, and its kernel lies in `{1, -1}`. -/
theorem exists_contMDiffMonoidMorphism_of_lie_eq_smul (B : LinearMap.BilinForm ℝ
      (LeftInvariantDerivation I G))
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    {t : Submodule ℝ (LeftInvariantDerivation I G)} {α : Dual ℝ t} (hα : α ≠ 0)
    {x y : LeftInvariantDerivation I G} (hx0 : x ≠ 0)
    (hx : ∀ H : t, ⁅(H : LeftInvariantDerivation I G), x⁆ = α H • y)
    (hy : ∀ H : t, ⁅(H : LeftInvariantDerivation I G), y⁆ = -(α H • x)) (hxy : ⁅x, y⁆ ∈ t) :
    ∃ φ : ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) I ∞
        (GLSpecialUnitary (Fin 2) ℂ) G,
      Function.Injective (lieMap φ) ∧
      (∃ h : lieMap φ SU2.torusGenerator ∈ t, α ⟨_, h⟩ = 2 ∧
        ∀ H : t, α H = 0 → B H (lieMap φ SU2.torusGenerator) = 0) ∧
      ∃ c : ℝ, 0 < c ∧
        lieMap φ (SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 0 1))) = c • y ∧
        lieMap φ (SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 1 1))) = c • x := by
  -- The pair `y, x` is a root pair of the root `-α`, which is nonzero.
  have hy0 : y ≠ 0 := by
    rintro rfl
    refine hα (LinearMap.ext fun H ↦ ?_)
    have h := hy H
    rw [lie_zero, eq_comm, neg_eq_zero, smul_eq_zero] at h
    exact h.resolve_right hx0
  have hy' (H : t) : ⁅(H : LeftInvariantDerivation I G), y⁆ = (-α) H • x := by
    rw [hy, LinearMap.neg_apply, neg_smul]
  have hx' (H : t) : ⁅(H : LeftInvariantDerivation I G), x⁆ = -((-α) H • y) := by
    rw [hx, LinearMap.neg_apply, neg_smul, neg_neg]
  have hyx : ⁅y, x⁆ ∈ t := by
    rw [← lie_skew]
    exact t.neg_mem hxy
  obtain ⟨f, hf, ⟨c, hc, hf₀, hf₁⟩, hf₂, hα₂⟩ :=
    B.exists_injective_lieHom_soThree_of_lie_eq_smul hBs hBp hB (neg_ne_zero.mpr hα) hy0 hy' hx'
      hyx
  -- Transport `f` to the native Lie algebra of `SU(2)` and integrate it.
  let ψ := f.comp (suTwoLieEquivSoThree.toLieHom.comp SU2.nativeLieEquiv.toLieHom)
  have hψ (v : Fin 3 → ℝ) :
      ψ (SU2.nativeLieEquiv.symm (suTwoEquiv v)) = f (soThreeEquiv ℝ v) := by
    simp [ψ]
  have hcoroot : ψ SU2.torusGenerator = (-2 : ℝ) • f (soThreeEquiv ℝ (Pi.single 2 1)) := by
    simp [ψ]
  have hmem : ψ SU2.torusGenerator ∈ t := by
    rw [hcoroot]
    exact t.smul_mem _ hf₂
  refine ⟨ψ.integrate, ?_, ⟨?_, ?_, ?_⟩, c, hc, ?_, ?_⟩
  · rw [LieHom.lieMap_integrate]
    exact hf.comp ((suTwoLieEquivSoThree.injective).comp SU2.nativeLieEquiv.injective)
  · rwa [LieHom.lieMap_integrate]
  · have hsmul : (⟨_, hmem⟩ : t) = (-2 : ℝ) • ⟨_, hf₂⟩ := Subtype.ext (by simp [hcoroot])
    simp only [LieHom.lieMap_integrate]
    rw [hsmul, map_smul, ← neg_neg (α ⟨_, hf₂⟩), ← LinearMap.neg_apply, hα₂]
    norm_num
  · intro H hH
    -- `f ê₂ = ⁅f ê₀, f ê₁⁆ = c² ⁅y, x⁆`, which `B` pairs with `H ∈ t` to `-α(H) c² B(x, x)`.
    have hbr : f (soThreeEquiv ℝ (Pi.single 2 1)) = (c * c) • ⁅y, x⁆ := by
      rw [← lie_soThreeEquiv_single_zero_one, LieHom.map_lie, hf₀, hf₁, smul_lie, lie_smul,
        smul_smul]
    have hB' := hB.apply_lie_eq_mul_of_lie_eq_smul hy' H
    rw [LieHom.lieMap_integrate, hcoroot, hbr, map_smul, map_smul, hB', LinearMap.neg_apply, hH]
    simp
  · rw [LieHom.lieMap_integrate, hψ, hf₀]
  · rw [LieHom.lieMap_integrate, hψ, hf₁]

end LinearMap.BilinForm

namespace TauCeti.IsRootPlane

-- Use the operator-norm topology under which `GL(2, ℂ)` is a Lie group, as in
-- `TauCeti.RepresentationTheory.SU2.LieGroup`.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal

open scoped Matrix.Norms.Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [SecondCountableTopology G]
  {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)}
  {t : Submodule ℝ (LeftInvariantDerivation I G)} {α : Dual ℝ t}
  {V : Submodule ℝ (LeftInvariantDerivation I G)} {J : Module.End ℝ V}

/-- **The rank-one homomorphism of a root plane.** For a symmetric positive definite invariant form
`B` on the Lie algebra of a Lie group `G` and a subspace `t`, a root plane `V` of `t` with nonzero
root `α` and rotation `J`, and `v ≠ 0` in `V` with `⁅v, J v⁆ ∈ t`, there is a smooth homomorphism
`φ : SU(2) → G` with injective differential whose differential sends `diag(i, -i)` to the coroot
`α∨ ∈ t`, with `α(α∨) = 2` and `α∨` orthogonal to `ker α`, and the real root vectors `-iσ₁/2` and
`-iσ₂/2` to the same positive multiple of `J v` and `v`. -/
theorem exists_contMDiffMonoidMorphism (h : IsRootPlane B t α V J) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hα : α ≠ 0) {v : V} (hv : v ≠ 0)
    (hvt : ⁅(v : LeftInvariantDerivation I G), (J v : LeftInvariantDerivation I G)⁆ ∈ t) :
    ∃ φ : ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) I ∞
        (GLSpecialUnitary (Fin 2) ℂ) G,
      Function.Injective (lieMap φ) ∧
      (∃ h : lieMap φ SU2.torusGenerator ∈ t, α ⟨_, h⟩ = 2 ∧
        ∀ H : t, α H = 0 → B H (lieMap φ SU2.torusGenerator) = 0) ∧
      ∃ c : ℝ, 0 < c ∧
        lieMap φ (SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 0 1))) =
          c • (J v : LeftInvariantDerivation I G) ∧
        lieMap φ (SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 1 1))) =
          c • (v : LeftInvariantDerivation I G) :=
  B.exists_contMDiffMonoidMorphism_of_lie_eq_smul hBs hBp hB hα (fun h' ↦ hv (Subtype.ext h'))
    (fun H ↦ h.lie_apply H v) (fun H ↦ by
      rw [h.lie_apply, h.apply_apply, Submodule.coe_neg, smul_neg]) hvt

end TauCeti.IsRootPlane
