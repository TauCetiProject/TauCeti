/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Commutative
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Tori and maximal tori

A **torus** of a topological group `G` is a compact connected commutative subgroup, and a
**maximal torus** is a torus which is maximal under inclusion among the tori of `G`. For a
finite-dimensional real Lie group `G`:

* a torus is the exponential image of its Lie algebra, `T = lieExp '' Lie(T)`, since a closed
  connected commutative subgroup is (`image_lieExp_lieSubalgebraOfSubgroup_of_isConnected`);
* for a maximal torus `T` of a compact `G`, the centralizer of `T` has the same Lie algebra as `T`,
  and `Lie(T)` is a maximal abelian Lie subalgebra of `𝔤`: a derivation that brackets to zero with
  `Lie(T)` lies in `Lie(T)`.

## Main definitions

* `TauCeti.Lie.IsTorus`: a compact connected commutative subgroup.
* `TauCeti.Lie.IsMaximalTorus`: a torus which is maximal under inclusion among tori,
  `Maximal IsTorus T`.

## Main results

* `TauCeti.Lie.IsTorus.image_lieExp_lieSubalgebraOfSubgroup`: a torus is the exponential image of
  its Lie algebra (the case of `image_lieExp_lieSubalgebraOfSubgroup_of_isConnected`).
* `TauCeti.Lie.IsMaximalTorus.lieSubalgebraOfSubgroup_centralizer`: the centralizer of a maximal
  torus of a compact Lie group has the Lie algebra of the torus.
* `TauCeti.Lie.IsMaximalTorus.mem_lieSubalgebraOfSubgroup_of_forall_lie_eq_zero`: a derivation
  that brackets to zero with `Lie(T)` lies in `Lie(T)`.
* `TauCeti.Lie.IsMaximalTorus.eq_lieSubalgebraOfSubgroup_of_isLieAbelian`: `Lie(T)` is a maximal
  abelian Lie subalgebra of `𝔤`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map), Theorem (3.6), and Chapter IV, § 1 (Maximal Tori),
  Definition (1.1) and Theorem (1.5).
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori), Propositions 15.2
  and 15.8 and Theorem 15.2.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

section Definitions

variable {G : Type*} [TopologicalSpace G] [Group G]

/-- **A torus** of a topological group: a compact, connected, commutative subgroup. -/
structure IsTorus (T : Subgroup G) : Prop where
  isCompact : IsCompact (T : Set G)
  isConnected : IsConnected (T : Set G)
  isMulCommutative : IsMulCommutative T

/-- **A maximal torus**: a torus which is maximal under inclusion among the tori of `G`. -/
def IsMaximalTorus (T : Subgroup G) : Prop :=
  Maximal IsTorus T

@[simp]
theorem isMaximalTorus_iff {T : Subgroup G} : IsMaximalTorus T ↔ Maximal IsTorus T :=
  Iff.rfl

theorem IsMaximalTorus.isTorus {T : Subgroup G} (hT : IsMaximalTorus T) : IsTorus T :=
  Maximal.prop hT

/-- A torus containing a maximal torus is that maximal torus. -/
theorem IsMaximalTorus.eq_of_le {T T' : Subgroup G} (hT : IsMaximalTorus T) (hT' : IsTorus T')
    (h : T ≤ T') : T = T' :=
  Maximal.eq_of_le hT hT' h

theorem IsTorus.isClosed [T2Space G] {T : Subgroup G} (hT : IsTorus T) : IsClosed (T : Set G) :=
  hT.isCompact.isClosed

end Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **A torus is the exponential image of its Lie algebra.** -/
@[simp]
theorem IsTorus.image_lieExp_lieSubalgebraOfSubgroup {T : Subgroup G} (hT : IsTorus T) :
    lieExp (I := I) '' (lieSubalgebraOfSubgroup (I := I) T : Set (LeftInvariantDerivation I G)) =
      T :=
  have := hT.isMulCommutative
  image_lieExp_lieSubalgebraOfSubgroup_of_isConnected hT.isClosed hT.isConnected

variable [CompactSpace G]

/-- **The centralizer of a maximal torus has the Lie algebra of the torus.** -/
theorem IsMaximalTorus.lieSubalgebraOfSubgroup_centralizer {T : Subgroup G}
    (hT : IsMaximalTorus T) :
    lieSubalgebraOfSubgroup (I := I) (Subgroup.centralizer (T : Set G)) =
      lieSubalgebraOfSubgroup (I := I) T := by
  have := hT.isTorus.isMulCommutative
  refine le_antisymm (fun X hX => ?_)
    (lieSubalgebraOfSubgroup_mono (Subgroup.le_centralizer T))
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  rw [mem_lieSubalgebraOfSubgroup (Set.isClosed_centralizer (T : Set G))] at hX
  rw [mem_lieSubalgebraOfSubgroup hT.isTorus.isClosed]
  -- The one-parameter subgroup of `X` centralizes `T`, so together with `T` it generates a
  -- commutative subgroup whose closure is a torus containing `T`, hence equal to `T`.
  have hcomm : ∀ (t : T) (s : Multiplicative ℝ),
      Commute (T.subtype t) (oneParameterSubgroup (I := I) X s) := by
    intro t s
    obtain ⟨s, rfl⟩ := Multiplicative.ofAdd.surjective s
    rw [oneParameterSubgroup_apply]
    exact Subgroup.mem_centralizer_iff.mp (hX s) t t.2
  let φ : T × Multiplicative ℝ →* G :=
    T.subtype.noncommCoprod (oneParameterSubgroup (I := I) X).toMonoidHom hcomm
  have hφ : Continuous φ := by
    have hcont : Continuous fun p : T × Multiplicative ℝ =>
        (p.1 : G) * oneParameterSubgroup (I := I) X p.2 :=
      (continuous_subtype_val.comp continuous_fst).mul
        ((oneParameterSubgroup (I := I) X).continuous.comp continuous_snd)
    exact hcont.congr fun p => by
      rw [MonoidHom.noncommCoprod_apply, Subgroup.coe_subtype, ContinuousMonoidHom.coe_toMonoidHom,
        MonoidHom.coe_ofClass]
  have _ : ConnectedSpace T := isConnected_iff_connectedSpace.mp hT.isTorus.isConnected
  have _ : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  have _ : IsMulCommutative φ.range := by
    rw [MonoidHom.range_eq_map]
    infer_instance
  have hS : IsTorus φ.range.topologicalClosure :=
    { isCompact := φ.range.isClosed_topologicalClosure.isCompact
      isConnected := by
        rw [Subgroup.topologicalClosure_coe, MonoidHom.coe_range]
        exact (isConnected_range hφ).closure
      isMulCommutative := Subgroup.isMulCommutative_topologicalClosure _ }
  have hTS : T ≤ φ.range.topologicalClosure := fun t ht =>
    Subgroup.le_topologicalClosure _ ⟨(⟨t, ht⟩, 1), by simp [φ]⟩
  intro s
  have hs : lieExp (I := I) (s • X) ∈ φ.range.topologicalClosure :=
    Subgroup.le_topologicalClosure _
      ⟨(1, Multiplicative.ofAdd s), by simp [φ, oneParameterSubgroup_apply]⟩
  rwa [← hT.eq_of_le hS hTS] at hs

/-- **A derivation that brackets to zero with the Lie algebra of a maximal torus lies in it.** -/
theorem IsMaximalTorus.mem_lieSubalgebraOfSubgroup_of_forall_lie_eq_zero {T : Subgroup G}
    (hT : IsMaximalTorus T) {X : LeftInvariantDerivation I G}
    (h : ∀ Y ∈ lieSubalgebraOfSubgroup (I := I) T, ⁅X, Y⁆ = 0) :
    X ∈ lieSubalgebraOfSubgroup (I := I) T := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- The one-parameter subgroup of `X` commutes with the exponential image of `Lie(T)`, which is
  -- `T`; so `X` lies in the Lie algebra of the centralizer of `T`, which is `Lie(T)`.
  rw [← hT.lieSubalgebraOfSubgroup_centralizer,
    mem_lieSubalgebraOfSubgroup (Set.isClosed_centralizer (T : Set G))]
  intro s
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rw [← hT.isTorus.image_lieExp_lieSubalgebraOfSubgroup (I := I)] at ht
  obtain ⟨Y, hY, rfl⟩ := ht
  exact (commute_lieExp_of_lie_eq_zero (by rw [smul_lie, h Y hY, smul_zero])).symm

/-- **The Lie algebra of a maximal torus is a maximal abelian Lie subalgebra.** -/
theorem IsMaximalTorus.eq_lieSubalgebraOfSubgroup_of_isLieAbelian {T : Subgroup G}
    (hT : IsMaximalTorus T) {𝔞 : LieSubalgebra ℝ (LeftInvariantDerivation I G)} [IsLieAbelian 𝔞]
    (h𝔞 : lieSubalgebraOfSubgroup (I := I) T ≤ 𝔞) : 𝔞 = lieSubalgebraOfSubgroup (I := I) T :=
  le_antisymm
    (fun X hX => hT.mem_lieSubalgebraOfSubgroup_of_forall_lie_eq_zero fun Y hY => by
      have htriv := trivial_lie_zero 𝔞 𝔞 (⟨X, hX⟩ : 𝔞) ⟨Y, h𝔞 hY⟩
      simpa only [Subtype.ext_iff, LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using htriv)
    h𝔞

end TauCeti.Lie
