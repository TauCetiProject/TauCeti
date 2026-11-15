/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus.Conjugacy
public import TauCeti.Geometry.Lie.Subgroup.Weyl.Group
import Mathlib.RepresentationTheory.Stabilizer
import TauCeti.Geometry.Lie.Adjoint.Representation.Basic

/-!
# Adjoint orbits through the Lie algebra of a maximal torus

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱 ⊆ 𝔤`. Every adjoint
orbit of `G` on `𝔤` meets `𝔱` (`TauCeti.Lie.IsMaximalTorus.exists_Ad_mem_lieSubalgebraOfSubgroup`).
This file shows that it meets `𝔱` in exactly one orbit of the normalizer `N(T)`, so in exactly one
orbit of the Weyl group `N(T) / T` acting on `𝔱` by the adjoint representation.

The argument is the Lie algebra analogue of the one for conjugacy classes in
`TauCeti.Geometry.Lie.Subgroup.Weyl.ConjugacyClasses`. Let `X, Y ∈ 𝔱` with `Ad_g X = Y`. The
torus `T` fixes `Y`, since it is commutative and `Y ∈ 𝔱`, and the conjugate torus `g T g⁻¹` fixes
`Ad_g X = Y` for the same reason. Both are connected, so they lie in the identity component
`Z_G(Y)⁰` of the closed stabilizer `Z_G(Y) = {h | Ad_h Y = Y}`, and they are maximal tori of `G`
there. Maximal tori lying in a closed subgroup are conjugate by an element of its identity component
(`TauCeti.Lie.IsMaximalTorus.exists_mem_connectedComponentIn_map_conj_eq_of_le`), so some
`c ∈ Z_G(Y)⁰` conjugates `g T g⁻¹` to `T`. Then `c g` normalizes `T` and still sends `X` to
`Ad_c Y = Y`. Neither `G` nor the stabilizer `Z_G(Y)` needs to be connected: the conjugating element
`c` is found in the identity component regardless.

## Main results

* `TauCeti.Lie.IsMaximalTorus.exists_mem_connectedComponentIn_mul_mem_normalizer`: if `Ad_g X = Y`
  for `X, Y ∈ 𝔱`, then `c g ∈ N(T)` for some `c` in the identity component of the stabilizer of
  `Y`, and `Ad_(c g) X = Y`.
* `TauCeti.Lie.IsMaximalTorus.exists_mem_normalizer_Ad_eq`: elements of `𝔱` in one adjoint orbit
  are in one orbit of `N(T)`.
* `TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_apply_eq`: they are in one orbit of
  the Weyl group.
* `TauCeti.Lie.IsMaximalTorus.range_Ad_inter_lieSubalgebraOfSubgroup`: the adjoint orbit of `X ∈ 𝔱`
  meets `𝔱` exactly in the `N(T)`-orbit of `X`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, Proposition (2.5).
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Springer Universitext (2000),
  Theorem 3.7.13 and Corollary 3.7.14.
-/

public section

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [T2Space G] [CompactSpace G]

include I

/-- The stabilizer `{h | Ad_h Y = Y}` of an element of the Lie algebra under the adjoint
representation. -/
private abbrev adStabilizer (Y : LeftInvariantDerivation I G) : Subgroup G :=
  Representation.stabilizer (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation Y

omit [CompactSpace G] in
private theorem coe_adStabilizer (Y : LeftInvariantDerivation I G) :
    (adStabilizer I Y : Set G) = {h | Ad (I := I) h Y = Y} := by
  ext h
  simp [ContRepresentation.toMonoidHom_apply]

omit [CompactSpace G] in
private theorem isClosed_adStabilizer (Y : LeftInvariantDerivation I G) :
    IsClosed (adStabilizer I Y : Set G) := by
  rw [coe_adStabilizer]
  have hcont : Continuous fun h : G ↦ Ad (I := I) h Y :=
    (contMDiff_Ad_apply (I := I) (G := G)).continuous.comp
      (continuous_id.prodMk continuous_const)
  exact isClosed_eq hcont continuous_const

/-- **Adjoint conjugacy in the Lie algebra of a maximal torus is realized in its normalizer.** Let
`T` be a maximal torus of a compact Lie group and let `X, Y` lie in its Lie algebra `𝔱`. If
`Ad_g X = Y`, then `c g` normalizes `T` for some `c` in the identity component of the stabilizer
`Z_G(Y) = {h | Ad_h Y = Y}`, and `Ad_(c g) X = Y`. -/
theorem IsMaximalTorus.exists_mem_connectedComponentIn_mul_mem_normalizer {T : Subgroup G}
    (hT : IsMaximalTorus T) {X Y : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) T) (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) T)
    {g : G} (hg : Ad (I := I) g X = Y) :
    ∃ c ∈ connectedComponentIn {h : G | Ad (I := I) h Y = Y} 1,
      c * g ∈ Subgroup.normalizer (T : Set G) ∧ Ad (I := I) (c * g) X = Y := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have hTc : T ≤ Subgroup.centralizer (T : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hT.isTorus.isMulCommutative
  -- `T` fixes `Y`, and `g T g⁻¹` fixes `Ad_g X = Y`, because `T` fixes every element of `𝔱`.
  have hTK : T ≤ adStabilizer I Y := fun t ht ↦ by
    rw [← SetLike.mem_coe, coe_adStabilizer]
    exact Ad_apply_eq_self_of_mem_centralizer (hTc ht) hY
  have hSK : T.map (MulAut.conj g).toMonoidHom ≤ adStabilizer I Y := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← SetLike.mem_coe, coe_adStabilizer, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Ad_mul, Ad_mul, Ad_inv, LieEquiv.trans_apply, LieEquiv.trans_apply, ← hg,
      LieEquiv.symm_apply_apply, Ad_apply_eq_self_of_mem_centralizer (hTc ht) hX]
  obtain ⟨c, hc, hmap⟩ := (hT.map_conj g).exists_mem_connectedComponentIn_map_conj_eq_of_le I
    (isClosed_adStabilizer I Y) hT hSK hTK
  rw [coe_adStabilizer] at hc
  have hcY : Ad (I := I) c Y = Y := connectedComponentIn_subset _ _ hc
  refine ⟨c, hc, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, map_mul]
    exact (Subgroup.map_map _ _ _).symm.trans hmap
  · rw [Ad_mul, LieEquiv.trans_apply, hg, hcY]

/-- **Elements of `𝔱` in one adjoint orbit are in one orbit of the normalizer.** For a maximal
torus `T` of a compact Lie group, two elements of its Lie algebra that are conjugate under the
adjoint action of `G` are conjugate under the adjoint action of the normalizer of `T`. -/
theorem IsMaximalTorus.exists_mem_normalizer_Ad_eq {T : Subgroup G} (hT : IsMaximalTorus T)
    {X Y : LeftInvariantDerivation I G} (hX : X ∈ lieSubalgebraOfSubgroup (I := I) T)
    (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) T) {g : G} (hg : Ad (I := I) g X = Y) :
    ∃ n ∈ Subgroup.normalizer (T : Set G), Ad (I := I) n X = Y := by
  obtain ⟨c, -, hn, hcg⟩ := hT.exists_mem_connectedComponentIn_mul_mem_normalizer I hX hY hg
  exact ⟨c * g, hn, hcg⟩

/-- **Elements of `𝔱` in one adjoint orbit are Weyl-related.** For a maximal torus `T` of a
compact Lie group, two elements of its Lie algebra that are conjugate under the adjoint action of
`G` are related by the adjoint action of an element of the Weyl group `N(T) / T`. -/
theorem IsMaximalTorus.exists_weylAdjointRepresentation_apply_eq {T : Subgroup G}
    [IsMulCommutative T] (hT : IsMaximalTorus T)
    (X Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {g : G} (hg : Ad (I := I) g X = Y) :
    ∃ w : T.normalizerQuotient, T.weylAdjointRepresentation (I := I) w X = Y := by
  obtain ⟨n, hn, hnX⟩ := hT.exists_mem_normalizer_Ad_eq I X.2 Y.2 hg
  refine ⟨((⟨n, hn⟩ : Subgroup.normalizer (T : Set G)) : T.normalizerQuotient), Subtype.ext ?_⟩
  rw [Subgroup.coe_weylAdjointRepresentation_mk_apply, hnX]

/-- **The adjoint orbit of an element of `𝔱` meets `𝔱` in its normalizer orbit.** For a maximal
torus `T` of a compact Lie group and `X` in its Lie algebra `𝔱`, the elements of `𝔱` of the form
`Ad_g X` are exactly the `Ad_n X` with `n` in the normalizer of `T`. -/
theorem IsMaximalTorus.range_Ad_inter_lieSubalgebraOfSubgroup {T : Subgroup G}
    (hT : IsMaximalTorus T) {X : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) T) :
    Set.range (fun g : G ↦ Ad (I := I) g X) ∩ lieSubalgebraOfSubgroup (I := I) T =
      Set.range fun n : Subgroup.normalizer (T : Set G) ↦ Ad (I := I) (n : G) X := by
  ext Y
  constructor
  · rintro ⟨⟨g, hg⟩, hY⟩
    obtain ⟨n, hn, hnX⟩ := hT.exists_mem_normalizer_Ad_eq I hX hY hg
    exact ⟨⟨n, hn⟩, hnX⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨n, rfl⟩, Ad_mem_lieSubalgebraOfSubgroup n.2 hX⟩

end TauCeti.Lie
