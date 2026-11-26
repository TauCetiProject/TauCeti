/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Stabilizer
public import TauCeti.Geometry.Lie.Subgroup.Torus.Conjugacy
public import TauCeti.Geometry.Lie.Subgroup.Weyl.Group
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
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
subgroup `t ↦ exp (t Y)`, hence a closed subgroup
(`TauCeti.Lie.isClosed_stabilizer_continuousAdjointRepresentation`). Both `T` and `g T g⁻¹` lie
in the identity component `Z_G(Y)⁰`: they are connected, and they fix `Y = Ad_g X` because `T`
is commutative and `X, Y ∈ 𝔱`. Both are maximal tori of `G`, so they are conjugate by some
`c ∈ Z_G(Y)⁰`, and then `c g ∈ N(T)` with `Ad_(c g) X = Ad_c Y = Y`. Neither `G` nor the full
centralizer `Z_G(Y)` needs to be connected, and the conjugating element `c` is found in the
identity component of `Z_G(Y)`.

The same arguments run inside the adjoint stabilizer `Z_G(X)` of an element `X ∈ 𝔱`, a closed
subgroup containing `T`. An element `Y` with `⁅X, Y⁆ = 0` generates a torus fixing `X`; a maximal
torus of `Z_G(X)` containing it is conjugate in `Z_G(X)` to `T`, so `Ad_c Y ∈ 𝔱` for some
`c ∈ Z_G(X)`. And a conjugacy in `𝔱` by an element of `Z_G(X)` is realized in `N(T) ∩ Z_G(X)`.
These describe the critical points of the heights `⟨·, X⟩` on coadjoint orbits.

## Main results

* `TauCeti.Lie.IsMaximalTorus.exists_mem_connectedComponentIn_stabilizer_mul_mem_normalizer`: if
  `Ad_g X = Y` with `X, Y ∈ 𝔱`, then `c g ∈ N(T)` for some `c ∈ Z_G(Y)⁰`.
* `TauCeti.Lie.IsMaximalTorus.exists_mem_normalizer_Ad_eq`: elements of `𝔱` in one adjoint orbit
  are in one orbit of `N(T)`.
* `TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_iff`: two elements of `𝔱` lie in
  one adjoint orbit of `G` exactly when they lie in one orbit of the Weyl group.
* `TauCeti.Lie.IsMaximalTorus.range_Ad_inter_lieSubalgebraOfSubgroup`: the adjoint orbit of
  `X ∈ 𝔱` meets `𝔱` exactly in the `N(T)`-orbit of `X`.
* `TauCeti.Lie.IsMaximalTorus.exists_mem_stabilizer_Ad_mem_lieSubalgebraOfSubgroup`: if
  `⁅X, Y⁆ = 0` with `X ∈ 𝔱`, then `Ad_c Y ∈ 𝔱` for some `c ∈ Z_G(X)`.
* `TauCeti.Lie.IsMaximalTorus.exists_mem_stabilizer_mem_normalizer_Ad_eq`: if `Ad_k Y = Y'` with
  `X, Y, Y' ∈ 𝔱` and `k ∈ Z_G(X)`, then `Ad_n Y = Y'` for some `n ∈ Z_G(X) ∩ N(T)`.

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
  let _ : IsMulCommutative T := hT.isTorus.isMulCommutative
  -- `T` fixes `Y ∈ Lie(T)`, and `g T g⁻¹` fixes `Ad_g X = Y` because `T` fixes `X ∈ Lie(T)`.
  have hSK : T.map (MulAut.conj g).toMonoidHom ≤
      (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y := by
    rw [← hg, ← continuousAdjointRepresentation_apply, ← ContRepresentation.toRepresentation_apply,
      Representation.stabilizer_conj]
    exact Subgroup.map_mono (le_stabilizer_continuousAdjointRepresentation hX)
  exact hT.exists_mem_connectedComponentIn_mul_mem_normalizer_of_le I
    (isClosed_stabilizer_continuousAdjointRepresentation Y)
    (le_stabilizer_continuousAdjointRepresentation hY) hSK

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
    obtain ⟨n, hn, hnX⟩ := hT.exists_mem_normalizer_Ad_eq hX hY hg
    exact ⟨⟨n, hn⟩, hnX⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨n, rfl⟩, Ad_mem_lieSubalgebraOfSubgroup n.property hX⟩

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
    obtain ⟨n, hn, hnX⟩ := hT.exists_mem_normalizer_Ad_eq X.property Y.property hg
    refine ⟨((⟨n, hn⟩ : Subgroup.normalizer (T : Set G)) : T.normalizerQuotient), ?_⟩
    exact Subtype.ext ((T.coe_weylAdjointRepresentation_mk_apply ⟨n, hn⟩ X).trans hnX)

/-! ### Conjugacy under the stabilizer of an element of `𝔱` -/

/-- **Elements commuting with `X ∈ 𝔱` are conjugate into `𝔱` under the stabilizer of `X`.** Let
`T` be a maximal torus of a compact Lie group and `X` in its Lie algebra `𝔱`. If `⁅X, Y⁆ = 0`,
then `Ad_c Y ∈ 𝔱` for some `c` in the adjoint stabilizer `Z_G(X)`. For `X = 0` this is the
statement that every adjoint orbit meets `𝔱`. -/
theorem IsMaximalTorus.exists_mem_stabilizer_Ad_mem_lieSubalgebraOfSubgroup {T : Subgroup G}
    (hT : IsMaximalTorus T) {X Y : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) T) (hXY : ⁅X, Y⁆ = 0) :
    ∃ c ∈ (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer X,
      Ad (I := I) c Y ∈ lieSubalgebraOfSubgroup (I := I) T := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : IsMulCommutative T := hT.isTorus.isMulCommutative
  set K := (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer X
  have hK : IsClosed (K : Set G) := isClosed_stabilizer_continuousAdjointRepresentation X
  have hTK : T ≤ K := le_stabilizer_continuousAdjointRepresentation hX
  -- The closure `S` of the one-parameter subgroup of `Y` is a torus fixing `X`, whose Lie algebra
  -- contains `Y`.
  set S := closedOneParameterSubgroup (leftInvariantDerivationEquivGroupLieAlgebra (I := I)
    (G := G) BoundarylessManifold.isInteriorPoint Y)
  have hexp (t : ℝ) : lieExp (I := I) (t • Y) ∈ S := by
    rw [lieExp_eq_mulInvariantExp, map_smul]
    exact mulInvariantExp_smul_mem_closedOneParameterSubgroup _ t
  have hYX : ⁅Y, X⁆ = 0 := by rw [← lie_skew, hXY, neg_zero]
  have hSK : S ≤ K := (closedOneParameterSubgroup_le hK).2 fun t ↦ by
    rw [← map_smul, ← lieExp_eq_mulInvariantExp]
    exact mem_stabilizer_continuousAdjointRepresentation_iff.2
      (Ad_lieExp_smul_apply_eq_self_of_lie_eq_zero hYX t)
  -- Cartan's theorem makes `K` a compact Lie group. A maximal torus of `K` containing `S` is
  -- conjugate in `K` to `T`, so the conjugating element carries `S` into `T`.
  let L := (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  obtain ⟨d⟩ := nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    (I := I) (K := K) hK
  let _ : ChartedSpace L K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, L) ∞ K := d.lieGroup
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  obtain ⟨S', hS', hSS'⟩ :=
    ((isTorus_closedOneParameterSubgroup _).subgroupOf hSK).exists_isMaximalTorus_le 𝓘(ℝ, L)
  obtain ⟨c, hc⟩ := hS'.exists_map_conj_eq 𝓘(ℝ, L) (hT.subgroupOf hTK)
  have hle : S.map (MulAut.conj (c : G)).toMonoidHom ≤ T := by
    rintro _ ⟨s, hs, rfl⟩
    have hmem : MulAut.conj c ⟨s, hSK hs⟩ ∈ T.subgroupOf K :=
      hc ▸ ⟨_, hSS' (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
    exact hmem
  refine ⟨c, c.property, lieSubalgebraOfSubgroup_mono hle ?_⟩
  rw [lieSubalgebraOfSubgroup_map_conj]
  exact ⟨Y, mem_lieSubalgebraOfSubgroup_of_forall hexp, rfl⟩

/-- **Conjugacy in `𝔱` under the stabilizer of `X ∈ 𝔱` is realized in the normalizer.** Let `T` be
a maximal torus of a compact Lie group and `X`, `Y`, `Y'` elements of its Lie algebra `𝔱`. If
`Ad_k Y = Y'` for some `k` in the adjoint stabilizer `Z_G(X)`, then `Ad_n Y = Y'` for some `n` in
`Z_G(X)` normalizing `T`. For `X = 0` this is
`TauCeti.Lie.IsMaximalTorus.exists_mem_normalizer_Ad_eq`. -/
theorem IsMaximalTorus.exists_mem_stabilizer_mem_normalizer_Ad_eq {T : Subgroup G}
    (hT : IsMaximalTorus T) {X Y Y' : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) T) (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) T)
    (hY' : Y' ∈ lieSubalgebraOfSubgroup (I := I) T) {k : G}
    (hk : k ∈ (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer X)
    (hkY : Ad (I := I) k Y = Y') :
    ∃ n ∈ (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer X,
      n ∈ Subgroup.normalizer (T : Set G) ∧ Ad (I := I) n Y = Y' := by
  let _ : IsMulCommutative T := hT.isTorus.isMulCommutative
  set ρ := (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation
  -- `k T k⁻¹` fixes `Ad_k Z` for every `Z ∈ 𝔱`, in particular `Ad_k X = X` and `Ad_k Y = Y'`.
  have hconj {Z : LeftInvariantDerivation I G} (hZ : Z ∈ lieSubalgebraOfSubgroup (I := I) T) :
      T.map (MulAut.conj k).toMonoidHom ≤ ρ.stabilizer (Ad (I := I) k Z) := by
    rw [← continuousAdjointRepresentation_apply, ← ContRepresentation.toRepresentation_apply,
      Representation.stabilizer_conj]
    exact Subgroup.map_mono (le_stabilizer_continuousAdjointRepresentation hZ)
  have hkX : Ad (I := I) k X = X := mem_stabilizer_continuousAdjointRepresentation_iff.mp hk
  -- Both `T` and `k T k⁻¹` lie in the closed subgroup `Z_G(X) ∩ Z_G(Y')`.
  have hclosed : IsClosed ((ρ.stabilizer X ⊓ ρ.stabilizer Y' : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_stabilizer_continuousAdjointRepresentation X).inter
      (isClosed_stabilizer_continuousAdjointRepresentation Y')
  obtain ⟨c, hc, hn⟩ := hT.exists_mem_connectedComponentIn_mul_mem_normalizer_of_le I hclosed
    (le_inf (le_stabilizer_continuousAdjointRepresentation hX)
      (le_stabilizer_continuousAdjointRepresentation hY'))
    (le_inf (hkX ▸ hconj hX) (hkY ▸ hconj hY))
  have hc' := connectedComponentIn_subset _ _ hc
  refine ⟨c * k, mul_mem (Subgroup.mem_inf.mp hc').1 hk, hn, ?_⟩
  rw [Ad_mul, LieEquiv.trans_apply, hkY]
  exact mem_stabilizer_continuousAdjointRepresentation_iff.mp (Subgroup.mem_inf.mp hc').2

end Compact

end TauCeti.Lie
