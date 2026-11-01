/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Exact

import TauCeti.Topology.FiberBundle.Separation

/-!
# The moment map of a cotangent-lifted action

Let a Lie group `G` act smoothly on a manifold `Q`. Its cotangent lift
`g • (q, p) = (g • q, p ∘ (dg_q)⁻¹)` is a smooth action on the cotangent bundle `T*Q`
(`TauCeti.CotangentBundle.instContMDiffSMul`) preserving the Liouville form `λ`
(`TauCeti.CotangentBundle.mpullback_smul_liouvilleForm`). The moment map determined by `λ`
(`TauCeti.SmoothForm.momentMap`) is the pairing of a covector with the fundamental vector field at
its base point,

`⟨μ(q, p), ξ⟩ = p(ξ_Q q)`

(`TauCeti.CotangentBundle.liouvilleForm_momentMap_apply`), since the bundle projection carries the
fundamental vector field of the lifted action to that of the action on `Q`. Therefore `μ` is a
coadjoint-equivariant moment map of the cotangent-lifted action for the canonical symplectic form
`ω = -dλ` (`TauCeti.CotangentBundle.isEquivariantMomentMap_liouvilleForm_momentMap`). It vanishes
on the zero section.

This is the manifold counterpart of the moment map `⟨μ(q, p), A⟩ = p(A q)` of the linear
cotangent-lifted action of `GL(V)` on `V × V*` (`TauCeti.cotangentMomentMap`).

## Main results

* `TauCeti.CotangentBundle.liouvilleForm_momentMap_apply`: `⟨μ(q, p), ξ⟩ = p(ξ_Q q)`.
* `TauCeti.CotangentBundle.isEquivariantMomentMap_liouvilleForm_momentMap`: `μ` is a
  group-level moment map of the cotangent-lifted action for the canonical symplectic form.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 12.1 (momentum maps of cotangent lifts).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 22.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
  [IsManifold I ∞ Q]
  {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  [LieGroup IG ∞ G] [MulAction G Q] [ContMDiffConstSMul I ∞ G Q] [ContMDiffSMul IG I ∞ G Q]

/-- **The cotangent moment map.** The moment map determined by the Liouville form for the
cotangent-lifted action evaluates `ξ` at a covector `p` over `q` as `p(ξ_Q q)`, the pairing of `p`
with the fundamental vector field of the action on `Q`. -/
theorem liouvilleForm_momentMap_apply (z : CotangentBundle I Q) (ξ : GroupLieAlgebra IG G) :
    (liouvilleForm I Q).momentMap IG G z ξ = z.2 (fundamentalVectorField I ξ z.proj) := by
  rw [SmoothForm.momentMap_apply, liouvilleForm_apply, Matrix.cons_val_zero,
    fundamentalVectorField_apply, fundamentalVectorField_apply]
  -- The projection carries the orbit map of `z` to the orbit map of its base point.
  have hproj : (π (E →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace I x →L[ℝ] ℝ) ∘ fun g : G ↦ g • z) =
      fun g : G ↦ g • z.proj :=
    funext fun g ↦ proj_smul g z
  have h := mfderiv_comp_apply_of_eq (1 : G)
    ((contMDiff_proj (fun x : Q ↦ TangentSpace I x →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero)
    ((ContMDiffSMul.contMDiff_smul_const (I := IG) (I' := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (n := 1)
      z).mdifferentiableAt one_ne_zero)
    (one_smul G z) ξ
  rw [hproj] at h
  exact congrArg z.2 h.symm

/-- The cotangent moment map vanishes on the zero section. -/
@[simp]
theorem liouvilleForm_momentMap_zeroSection (x : Q) :
    (liouvilleForm I Q).momentMap IG G
        (zeroSection (E →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace I x →L[ℝ] ℝ) x) = 0 := by
  ext ξ
  rw [liouvilleForm_momentMap_apply, zeroSection_snd, LinearMap.zero_apply]
  -- The zero covector evaluates every tangent vector to zero.
  rfl

/-- Over `ℝ`, `minSmoothness ℝ 3 = 3`, so a smooth Lie group is a `C^{minSmoothness ℝ 3}` Lie
group, the regularity at which group-level moment maps are stated. -/
local instance lieGroupMinSmoothness : LieGroup IG (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞) (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)

/-- **The moment map of a cotangent-lifted action.** For a smooth action of a Lie group `G` on
`Q`, the map `(q, p) ↦ (ξ ↦ p(ξ_Q q))` is a coadjoint-equivariant moment map of the
cotangent-lifted action of `G` on `T*Q` for the canonical symplectic form `ω = -dλ`. -/
theorem isEquivariantMomentMap_liouvilleForm_momentMap [FiniteDimensional ℝ E] [I.Boundaryless]
    [T2Space Q] [CompleteSpace EG] [T2Space G] [BoundarylessManifold IG G] :
    (symplecticForm I Q).IsEquivariantMomentMap ((liouvilleForm I Q).momentMap IG G) := by
  rw [symplecticForm_eq_neg_mextDerivₗ]
  exact SmoothForm.isEquivariantMomentMap_momentMap fun g ↦ mpullback_smul_liouvilleForm (I := I) g

end TauCeti.CotangentBundle
