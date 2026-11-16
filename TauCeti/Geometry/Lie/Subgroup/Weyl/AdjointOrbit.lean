/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.Geometry.Lie.Subgroup.Torus.Conjugacy
public import TauCeti.Geometry.Lie.Subgroup.Weyl.Group
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# Adjoint orbits meet the Lie algebra of a maximal torus in Weyl orbits

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱 ⊆ 𝔤`. Every adjoint
orbit of `G` meets `𝔱` (`TauCeti.Lie.IsMaximalTorus.exists_Ad_mem_lieSubalgebraOfSubgroup`). This
file proves that it meets `𝔱` in exactly one orbit of the Weyl group `W = N(T) / T`: two elements
`X, Y ∈ 𝔱` with `Ad_g X = Y` are related by the adjoint action of an element of the normalizer
`N(T)`.

The argument is the Lie algebra form of the one for conjugacy classes in
`TauCeti.Geometry.Lie.Subgroup.Weyl.ConjugacyClasses`. Let `Z_G(Y) = {h ∈ G | Ad_h Y = Y}` be the
stabilizer of `Y` in the adjoint representation; it is the centralizer of the one-parameter
subgroup `t ↦ exp (t Y)`, hence a closed subgroup. Both `T` and `g T g⁻¹` lie in the identity
component `Z_G(Y)⁰`: they are connected, and they fix `Y = Ad_g X` because `T` is commutative and
`X, Y ∈ 𝔱`. Both are maximal tori of `G`, so they are conjugate by some `c ∈ Z_G(Y)⁰`, and then
`c g ∈ N(T)` with `Ad_(c g) X = Ad_c Y = Y`. Neither `G` nor the full centralizer `Z_G(Y)` needs
to be connected, and the conjugating element `c` is found in the identity component of `Z_G(Y)`.

## Main results

* `TauCeti.Lie.isClosed_stabilizer_continuousAdjointRepresentation`: the adjoint stabilizer
  `Z_G(Y)` of `Y ∈ 𝔤` is closed; it is the centralizer of the one-parameter subgroup of `Y`
  (`TauCeti.Lie.stabilizer_continuousAdjointRepresentation_eq_centralizer`).
* `TauCeti.Lie.IsMaximalTorus.exists_mem_connectedComponentIn_stabilizer_mul_mem_normalizer`: if
  `Ad_g X = Y` with `X, Y ∈ 𝔱`, then `c g ∈ N(T)` for some `c ∈ Z_G(Y)⁰`.
* `TauCeti.Lie.IsMaximalTorus.exists_mem_normalizer_Ad_eq`: elements of `𝔱` in one adjoint orbit
  are in one orbit of `N(T)`.
* `TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_iff`: two elements of `𝔱` lie in
  one adjoint orbit of `G` exactly when they lie in one orbit of the Weyl group.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### The adjoint stabilizer -/

/-- An element lies in the adjoint stabilizer `Z_G(Y)` of `Y` exactly when it fixes `Y`. -/
theorem mem_stabilizer_continuousAdjointRepresentation_iff {Y : LeftInvariantDerivation I G}
    {g : G} :
    g ∈ (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y ↔
      Ad (I := I) g Y = Y := by
  rw [Representation.mem_stabilizer, ContRepresentation.toRepresentation_apply,
    continuousAdjointRepresentation_apply]

/-- **The adjoint stabilizer of `Y` is the centralizer of its one-parameter subgroup.** -/
theorem stabilizer_continuousAdjointRepresentation_eq_centralizer
    (Y : LeftInvariantDerivation I G) :
    (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y =
      Subgroup.centralizer (Set.range fun t : ℝ ↦ lieExp (I := I) (t • Y)) := by
  ext g
  rw [mem_stabilizer_continuousAdjointRepresentation_iff, Subgroup.mem_centralizer_iff,
    Set.forall_mem_range]
  refine ⟨fun h t ↦ ?_, fun h ↦ Ad_apply_eq_self_of_forall_commute fun t ↦ (h t).symm⟩
  rw [eq_comm, ← mul_inv_eq_iff_eq_mul, conj_lieExp, map_smul, h]

/-- **The adjoint stabilizer `Z_G(Y)` is a closed subgroup.** -/
theorem isClosed_stabilizer_continuousAdjointRepresentation (Y : LeftInvariantDerivation I G) :
    IsClosed ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y :
      Set G) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  rw [stabilizer_continuousAdjointRepresentation_eq_centralizer]
  exact Set.isClosed_centralizer _

/-- A commutative subgroup fixes every element of its Lie algebra, so it lies in the adjoint
stabilizer of each of them. -/
theorem le_stabilizer_continuousAdjointRepresentation {K : Subgroup G} [IsMulCommutative K]
    {Y : LeftInvariantDerivation I G} (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) K) :
    K ≤ (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y :=
  fun _ hg ↦ mem_stabilizer_continuousAdjointRepresentation_iff.mpr
    (Ad_apply_eq_self_of_mem_lieSubalgebraOfSubgroup hg hY)

/-! ### Weyl orbits in the Lie algebra of a maximal torus -/

section Compact

variable [CompactSpace G]

/-- **Adjoint conjugacy in a torus Lie algebra is realized in the normalizer.** If `Ad_g X = Y`
for `X, Y` in the Lie algebra of a maximal torus `T` of a compact Lie group, then `c g` normalizes
`T` for some `c` in the identity component of the adjoint stabilizer `Z_G(Y)`; in particular
`Ad_(c g) X = Y`. -/
theorem IsMaximalTorus.exists_mem_connectedComponentIn_stabilizer_mul_mem_normalizer
    {T : Subgroup G} (hT : IsMaximalTorus T) {X Y : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) T) (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) T)
    {g : G} (hg : Ad (I := I) g X = Y) :
    ∃ c ∈ connectedComponentIn
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y :
          Set G) 1,
      c * g ∈ Subgroup.normalizer (T : Set G) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : IsMulCommutative T := hT.isTorus.isMulCommutative
  set K := (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y
  -- `T` fixes `Y ∈ Lie(T)`, and `g T g⁻¹` fixes `Ad_g X = Y` because `T` fixes `X ∈ Lie(T)`.
  have hTK : T ≤ K := le_stabilizer_continuousAdjointRepresentation hY
  have hSK : T.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_stabilizer_continuousAdjointRepresentation_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, ← hg]
    simp only [Ad_mul, Ad_inv, LieEquiv.trans_apply, LieEquiv.symm_apply_apply,
      Ad_apply_eq_self_of_mem_lieSubalgebraOfSubgroup ht hX]
  obtain ⟨c, hc, hmap⟩ := (hT.map_conj g).exists_mem_connectedComponentIn_map_conj_eq_of_le I
    (isClosed_stabilizer_continuousAdjointRepresentation Y) hT hSK hTK
  refine ⟨c, hc, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, map_mul]
  exact (Subgroup.map_map _ _ _).symm.trans hmap

/-- **Elements of a torus Lie algebra in one adjoint orbit are in one orbit of the normalizer.**
If `Ad_g X = Y` for `X, Y` in the Lie algebra of a maximal torus `T` of a compact Lie group, then
`Ad_n X = Y` for some `n` normalizing `T`. -/
theorem IsMaximalTorus.exists_mem_normalizer_Ad_eq {T : Subgroup G} (hT : IsMaximalTorus T)
    {X Y : LeftInvariantDerivation I G} (hX : X ∈ lieSubalgebraOfSubgroup (I := I) T)
    (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) T) {g : G} (hg : Ad (I := I) g X = Y) :
    ∃ n ∈ Subgroup.normalizer (T : Set G), Ad (I := I) n X = Y := by
  obtain ⟨c, hc, hn⟩ :=
    hT.exists_mem_connectedComponentIn_stabilizer_mul_mem_normalizer hX hY hg
  refine ⟨c * g, hn, ?_⟩
  rw [Ad_mul, LieEquiv.trans_apply, hg]
  exact mem_stabilizer_continuousAdjointRepresentation_iff.mp (connectedComponentIn_subset _ _ hc)

/-- **An adjoint orbit meets the Lie algebra of a maximal torus in one Weyl orbit.** Two elements
of the Lie algebra of a maximal torus `T` of a compact Lie group lie in one adjoint orbit exactly
when they are related by the Weyl group `N(T) / T`, acting through
`Subgroup.weylAdjointRepresentation`. -/
theorem IsMaximalTorus.exists_weylAdjointRepresentation_eq_iff {T : Subgroup G}
    [IsMulCommutative T] (hT : IsMaximalTorus T)
    (X Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    (∃ w : T.normalizerQuotient, T.weylAdjointRepresentation (I := I) w X = Y) ↔
      ∃ g : G, Ad (I := I) g X = Y := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨n, (T.coe_weylAdjointRepresentation_mk_apply n X).symm⟩
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn, hnX⟩ := hT.exists_mem_normalizer_Ad_eq X.2 Y.2 hg
    refine ⟨((⟨n, hn⟩ : Subgroup.normalizer (T : Set G)) : T.normalizerQuotient), ?_⟩
    exact Subtype.ext ((T.coe_weylAdjointRepresentation_mk_apply ⟨n, hn⟩ X).trans hnX)

end Compact

end TauCeti.Lie
