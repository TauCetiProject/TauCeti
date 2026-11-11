/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Instances.Comap

/-!
# Lie groups covered by local diffeomorphisms

Let `π : G →* G'` be a surjective group homomorphism out of a `C^n` Lie group `G` which is a `C^n`
local diffeomorphism onto a `C^n` manifold `G'`. Then `G'` is a `C^n` Lie group. Near a pair of
points of `G'`, multiplication is the image under `π` of the product of two local inverses of `π`,
which are `C^n`; inversion on `G'` is the descent of inversion on `G`. This covers quotients of Lie
groups by discrete normal subgroups, such as tori `E ⧸ L` and circles `AddCircle p`.

The charts of a Lie group can also be pulled back along a locally homeomorphic homomorphism
from a topological group, giving the source a Lie-group structure over the same model.

This file also proves that the integer power maps of a `C^n` Lie group are `C^n`.

## Main results

* `IsLocalDiffeomorph.lieGroup`, `IsLocalDiffeomorph.lieAddGroup`: the image of a Lie group under
  a surjective homomorphism which is a local diffeomorphism is a Lie group.
* `IsLocalHomeomorph.lieGroup_chartedSpaceComap`,
  `IsLocalHomeomorph.lieAddGroup_chartedSpaceComap`: Lie-group structures for pulled-back charts.
* `TauCeti.contMDiff_zpow`, `TauCeti.contMDiff_zsmul`: integer powers, and integer multiples, in
  a Lie group are `C^n`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 4.40 and Theorem 7.7.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I n G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [IsManifold I' n G'] [Group G']

/-- If a surjective group homomorphism `π : G →* G'` out of a `C^n` Lie group is a `C^n` local
diffeomorphism, then `G'` is a `C^n` Lie group. -/
@[to_additive /-- If a surjective additive group homomorphism `π : G →+ G'` out of a `C^n` additive
Lie group is a `C^n` local diffeomorphism, then `G'` is a `C^n` additive Lie group. -/]
theorem IsLocalDiffeomorph.lieGroup (π : G →* G') (hπ : IsLocalDiffeomorph I I' n π)
    (hsurj : Function.Surjective π) : LieGroup I' n G' where
  contMDiff_mul := by
    -- Near a pair of points, multiplication is the image under `π` of the product of two local
    -- inverses of `π`.
    rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    have ha := hπ a
    have hb := hπ b
    have h₀ : ContMDiffAt (I'.prod I') I n
        (fun z : G' × G' ↦ ha.localInverse z.1 * hb.localInverse z.2) (π a, π b) :=
      (ha.contMDiffAt_localInverse.comp_of_eq contMDiffAt_fst rfl).mul
        (hb.contMDiffAt_localInverse.comp_of_eq contMDiffAt_snd rfl)
    refine (hπ.contMDiff.contMDiffAt.comp _ h₀).congr_of_eventuallyEq ?_
    filter_upwards [ha.localInverse_eventuallyEq_right.prodMk_nhds
      hb.localInverse_eventuallyEq_right] with z hz
    simp only [Function.comp_apply, id, map_mul] at hz ⊢
    rw [hz.1, hz.2]
  contMDiff_inv := by
    -- Inversion is the descent of inversion on `G`.
    have h : (fun x : G' ↦ x⁻¹) ∘ π = π ∘ fun x : G ↦ x⁻¹ := funext fun x ↦ (map_inv π x).symm
    rw [← hπ.contMDiff_comp_iff hsurj le_rfl, h]
    exact hπ.contMDiff.comp (contMDiff_inv I n)

section Comap

variable {A B : Type*} [TopologicalSpace A] [Group A] [IsTopologicalGroup A]
  [TopologicalSpace B] [Group B] [ChartedSpace H B] [LieGroup I n B]
  {p : A → B}

/-- Charts pulled back through a locally homeomorphic homomorphism from a topological group
form a Lie-group structure over the target's model. -/
@[to_additive /-- Charts pulled back through a locally homeomorphic additive homomorphism from a
topological additive group form an additive Lie-group structure over the target's model. -/]
theorem IsLocalHomeomorph.lieGroup_chartedSpaceComap (hp : IsLocalHomeomorph p)
    (hmul : ∀ x y, p (x * y) = p x * p y) :
    let _ : ChartedSpace H A := hp.chartedSpaceComap
    LieGroup I n A := by
  let _ : ChartedSpace H A := hp.chartedSpaceComap
  let _ : IsManifold I n A := hp.isManifold_chartedSpaceComap
  have hinv (x : A) : p x⁻¹ = (p x)⁻¹ := by
    simpa only [MonoidHom.mk'_apply] using map_inv (MonoidHom.mk' p hmul) x
  exact
    { contMDiff_mul := by
        apply hp.contMDiff_chartedSpaceComap_iff.mpr
        refine ⟨continuous_mul, ?_⟩
        simpa only [Function.comp_def, hmul, Pi.mul_def] using
          ((hp.contMDiff_chartedSpaceComap (I := I) (n := n)).comp contMDiff_fst).mul
            ((hp.contMDiff_chartedSpaceComap (I := I) (n := n)).comp contMDiff_snd)
      contMDiff_inv := by
        apply hp.contMDiff_chartedSpaceComap_iff.mpr
        refine ⟨continuous_inv, ?_⟩
        simpa only [Function.comp_def, hinv] using
          (hp.contMDiff_chartedSpaceComap (I := I) (n := n)).inv }

end Comap

namespace TauCeti

/-- In a `C^n` Lie group, every integer power map is `C^n`. -/
@[to_additive /-- In a `C^n` additive Lie group, multiplication by every integer is `C^n`. -/]
theorem contMDiff_zpow : ∀ k : ℤ, ContMDiff I I n fun a : G ↦ a ^ k
  | (k : ℕ) => by simpa using contMDiff_pow k
  | .negSucc k => by simpa using (contMDiff_pow (k + 1)).inv

end TauCeti
