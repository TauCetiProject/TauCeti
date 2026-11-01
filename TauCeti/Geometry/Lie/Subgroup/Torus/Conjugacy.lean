/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.Geometry.Lie.Adjoint.Representation.Basic

/-!
# Conjugacy of maximal tori

In a compact finite-dimensional real Lie group `G`, all maximal tori are conjugate, and every torus
is conjugate into any given maximal torus. So the dimension of a maximal torus, the rank of `G`,
does not depend on the torus. No connectedness of `G` is needed.

The proof is the classical maximization argument of Hunt, which needs no degree theory. Fix an
`Ad`-invariant inner product `B` on the Lie algebra `𝔤`. Given `X Y : 𝔤`, the function
`g ↦ B (Ad g X) Y` on the compact group `G` attains its maximum at some `g`, and differentiating
along one-parameter subgroups at the maximum, using that each `ad Z` is skew for `B`, gives
`⁅Ad g X, Y⁆ = 0` (`TauCeti.Lie.exists_lie_Ad_eq_zero`). Choose `Y` with `lieExp Y` a topological
generator of a maximal torus `T`. Then the one-parameter subgroup of `Ad g X` centralizes `T`, so
`Ad g X` lies in `Lie(T)`: every adjoint orbit in `𝔤` meets `Lie(T)`. Applying this to an `X` whose
exponential topologically generates another torus `S` conjugates `S` into `T`.

The conjugates of `T` therefore cover exactly the image of the exponential map
(`TauCeti.Lie.IsMaximalTorus.iUnion_map_conj_eq_range_lieExp`). For a compact connected `G` they
cover all of `G` as soon as `lieExp` is known to be surjective, which is a separate theorem.

## Main results

* `TauCeti.Lie.exists_lie_Ad_eq_zero`: for `X Y : 𝔤` in the Lie algebra of a compact Lie group,
  some adjoint translate of `X` brackets to zero with `Y`.
* `TauCeti.Lie.IsMaximalTorus.exists_Ad_mem_lieSubalgebraOfSubgroup`: every adjoint orbit meets the
  Lie algebra of a maximal torus.
* `TauCeti.Lie.IsMaximalTorus.iUnion_map_conj_eq_range_lieExp`: the conjugates of a maximal torus
  cover exactly the image of the exponential map.
* `TauCeti.Lie.IsMaximalTorus.exists_map_conj_le`: a torus is conjugate into any maximal torus.
* `TauCeti.Lie.IsMaximalTorus.exists_map_conj_eq`: **any two maximal tori are conjugate**.
* `TauCeti.Lie.IsMaximalTorus.finrank_lieSubalgebraOfSubgroup_eq`: any two maximal tori have the
  same dimension.

## References

* G. A. Hunt, *A theorem of Élie Cartan*, Proc. Amer. Math. Soc. **7** (1956), 307–308.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, § 1.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [CompactSpace G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **Hunt's lemma.** For `X` and `Y` in the Lie algebra of a compact Lie group, some adjoint
translate of `X` brackets to zero with `Y`. -/
theorem exists_lie_Ad_eq_zero (X Y : LeftInvariantDerivation I G) :
    ∃ g : G, ⁅Ad (I := I) g X, Y⁆ = 0 := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  obtain ⟨B, -, hpos, hAd⟩ := exists_isSymm_bilinForm_Ad_invariant (I := I) (G := G)
  have hinv := lieInvariant_of_forall_Ad_apply hAd
  -- Let `g` maximize `g ↦ B (Ad g X) Y` over the compact group.
  let φ := LinearMap.toContinuousLinearMap (B.flip Y)
  have hcont : Continuous fun g : G ↦ φ (Ad (I := I) g X) :=
    φ.continuous.comp ((contMDiff_Ad_apply (I := I) (G := G)).continuous.comp
      (continuous_id.prodMk continuous_const))
  obtain ⟨g, -, hg⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  refine ⟨g, ?_⟩
  set X' := Ad (I := I) g X with hX'
  set Z := ⁅X', Y⁆
  -- Along the one-parameter subgroup of `Z`, the value at `g` is still maximal.
  have hmax : IsLocalMax (fun s : ℝ ↦ φ (Ad (I := I) (lieExp (I := I) (s • Z)) X')) 0 := by
    refine Filter.Eventually.of_forall fun s ↦ ?_
    have := hg (Set.mem_univ (lieExp (I := I) (s • Z) * g))
    simpa [hX', Ad_mul] using this
  have hderiv := φ.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_Ad_lieExp_smul_apply_zero (I := I) Z X')
  have hzero : B ⁅Z, X'⁆ Y = 0 := by
    simpa [φ] using hmax.hasDerivAt_eq_zero hderiv
  -- By invariance the derivative at the maximum is `B Z Z`.
  have hnorm : B Z Z = 0 := by
    have h := hinv X' Z Y
    rw [← lie_skew, map_neg, LinearMap.neg_apply, hzero, neg_zero] at h
    exact neg_eq_zero.mp h.symm
  by_contra hne
  exact (hpos Z hne).ne' hnorm

/-- **Every adjoint orbit meets the Lie algebra of a maximal torus.** -/
theorem IsMaximalTorus.exists_Ad_mem_lieSubalgebraOfSubgroup {T : Subgroup G}
    (hT : IsMaximalTorus T) (X : LeftInvariantDerivation I G) :
    ∃ g : G, Ad (I := I) g X ∈ lieSubalgebraOfSubgroup (I := I) T := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- `T` is generated by an element `lieExp Y`, and a translate of `X` brackets to zero with `Y`.
  obtain ⟨t, ht, hgen⟩ := hT.isTorus.exists_closedZpowers_eq I
  rw [← SetLike.mem_coe, ← hT.isTorus.image_lieExp_lieSubalgebraOfSubgroup (I := I)] at ht
  obtain ⟨Y, -, rfl⟩ := ht
  obtain ⟨g, hg⟩ := exists_lie_Ad_eq_zero (I := I) X Y
  refine ⟨g, ?_⟩
  -- So its one-parameter subgroup commutes with the generator, and hence with all of `T`.
  rw [← hT.lieSubalgebraOfSubgroup_centralizer,
    mem_lieSubalgebraOfSubgroup (Set.isClosed_centralizer (T : Set G))]
  intro s
  have hle : T ≤ Subgroup.centralizer
      ({lieExp (I := I) (s • Ad (I := I) g X)} : Set G) := by
    rw [← hgen, closedZpowers_le (Set.isClosed_centralizer _),
      Subgroup.mem_centralizer_singleton_iff]
    exact (commute_lieExp_of_lie_eq_zero (by rw [smul_lie, hg, smul_zero])).symm.eq
  rw [Subgroup.mem_centralizer_iff]
  exact fun t ht ↦ Subgroup.mem_centralizer_singleton_iff.mp (hle ht)

/-- **The conjugates of a maximal torus cover exactly the image of the exponential map.** -/
theorem IsMaximalTorus.iUnion_map_conj_eq_range_lieExp {T : Subgroup G} (hT : IsMaximalTorus T) :
    ⋃ g : G, (T.map (MulAut.conj g).toMonoidHom : Set G) =
      Set.range (lieExp (I := I) (G := G)) := by
  ext x
  simp only [Set.mem_iUnion, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_range]
  constructor
  · rintro ⟨g, t, ht, rfl⟩
    rw [← SetLike.mem_coe, ← hT.isTorus.image_lieExp_lieSubalgebraOfSubgroup (I := I)] at ht
    obtain ⟨Y, -, rfl⟩ := ht
    exact ⟨Ad (I := I) g Y, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_lieExp]⟩
  · rintro ⟨X, rfl⟩
    obtain ⟨g, hg⟩ := hT.exists_Ad_mem_lieSubalgebraOfSubgroup (I := I) X
    refine ⟨g⁻¹, lieExp (I := I) (Ad (I := I) g X),
      lieExp_mem_of_mem_lieSubalgebraOfSubgroup hT.isTorus.isClosed hg, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← conj_lieExp]
    group

section Conjugacy

variable (I)
include I

/-- **A torus is conjugate into any maximal torus.** -/
theorem IsMaximalTorus.exists_map_conj_le {S T : Subgroup G} (hT : IsMaximalTorus T)
    (hS : IsTorus S) : ∃ g : G, S.map (MulAut.conj g).toMonoidHom ≤ T := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- `S` is generated by an element `lieExp X`, and `X` has an adjoint translate in `Lie(T)`.
  obtain ⟨s, hs, hgen⟩ := hS.exists_closedZpowers_eq I
  rw [← SetLike.mem_coe, ← hS.image_lieExp_lieSubalgebraOfSubgroup (I := I)] at hs
  obtain ⟨X, -, rfl⟩ := hs
  obtain ⟨g, hg⟩ := hT.exists_Ad_mem_lieSubalgebraOfSubgroup (I := I) X
  refine ⟨g, ?_⟩
  have hclosed : IsClosed (T.comap (MulAut.conj g).toMonoidHom : Set G) :=
    hT.isTorus.isClosed.preimage (IsTopologicalGroup.continuous_conj g)
  rw [Subgroup.map_le_iff_le_comap, ← hgen, closedZpowers_le hclosed, Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_lieExp]
  exact lieExp_mem_of_mem_lieSubalgebraOfSubgroup hT.isTorus.isClosed hg

/-- **Conjugacy of maximal tori.** Any two maximal tori of a compact Lie group are conjugate. -/
theorem IsMaximalTorus.exists_map_conj_eq {S T : Subgroup G} (hS : IsMaximalTorus S)
    (hT : IsMaximalTorus T) : ∃ g : G, S.map (MulAut.conj g).toMonoidHom = T := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  obtain ⟨g, hg⟩ := hT.exists_map_conj_le I hS.isTorus
  have hmax := hS.map_mulEquiv (MulAut.conj g) (IsTopologicalGroup.continuous_conj g)
    ((by fun_prop : Continuous fun x ↦ g⁻¹ * x * g).congr fun x ↦
      (MulAut.conj_symm_apply g x).symm)
  exact ⟨g, hmax.eq_of_le hT.isTorus hg⟩

end Conjugacy

/-- **Any two maximal tori of a compact Lie group have the same dimension**, so the rank of the
group is well defined. -/
theorem IsMaximalTorus.finrank_lieSubalgebraOfSubgroup_eq {S T : Subgroup G}
    (hS : IsMaximalTorus S) (hT : IsMaximalTorus T) :
    Module.finrank ℝ (lieSubalgebraOfSubgroup (I := I) S) =
      Module.finrank ℝ (lieSubalgebraOfSubgroup (I := I) T) := by
  obtain ⟨g, rfl⟩ := hS.exists_map_conj_eq I hT
  rw [lieSubalgebraOfSubgroup_map_conj hS.isTorus.isClosed]
  exact ((Ad (I := I) g).lieSubalgebraMap _).toLinearEquiv.finrank_eq

end TauCeti.Lie
