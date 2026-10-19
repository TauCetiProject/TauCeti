/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Commutative
public import Mathlib.Analysis.Complex.Circle
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import Mathlib.GroupTheory.NoncommCoprod
import TauCeti.Geometry.Lie.Exponential.CommutativeGroup
import TauCeti.Geometry.Lie.Subgroup.Embedded

/-!
# Tori and maximal tori

A **torus** of a topological group `G` is a compact connected commutative subgroup, and a
**maximal torus** is a torus which is maximal under inclusion among the tori of `G`. For a
finite-dimensional real Lie group `G`:

* a torus is the exponential image of its Lie algebra, `T = lieExp '' Lie(T)`, since a closed
  connected commutative subgroup is (`image_lieExp_lieSubalgebraOfSubgroup_of_isConnected`); so
  a torus is determined by its Lie algebra, and a torus whose Lie algebra is maximal among those
  of the tori containing a given torus is a maximal torus: every torus lies in a maximal torus;
* by the closed-subgroup theorem a torus is a compact connected commutative Lie group, hence a
  product `(Circle)^r` of circles with `r` the dimension of its Lie algebra;
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
* `TauCeti.Lie.IsTorus.le_of_lieSubalgebraOfSubgroup_le` and
  `TauCeti.Lie.IsTorus.eq_of_lieSubalgebraOfSubgroup_eq`: a torus lies in a closed subgroup whose
  Lie algebra contains its own; in particular a torus is determined by its Lie algebra.
* `TauCeti.Lie.IsTorus.nonempty_continuousMulEquiv_pi_circle`: a torus is isomorphic to
  `(Circle)^r` as a topological group, where `r` is the dimension of its Lie algebra.
* `TauCeti.Lie.IsTorus.exists_isMaximalTorus_le` and `TauCeti.Lie.exists_isMaximalTorus`: every
  torus is contained in a maximal torus; in particular maximal tori exist.
* `TauCeti.Lie.IsMaximalTorus.lieSubalgebraOfSubgroup_centralizer`: the centralizer of a maximal
  torus of a compact Lie group has the Lie algebra of the torus.
* `TauCeti.Lie.IsMaximalTorus.mem_lieSubalgebraOfSubgroup_of_forall_lie_eq_zero`: a derivation
  that brackets to zero with `Lie(T)` lies in `Lie(T)`.
* `TauCeti.Lie.IsMaximalTorus.eq_lieSubalgebraOfSubgroup_of_isLieAbelian`: `Lie(T)` is a maximal
  abelian Lie subalgebra of `𝔤`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map), Theorem (3.6), and Chapter IV, § 1 (Maximal Tori),
  Definition (1.1) with the remark following it, and Theorem (1.5).
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

/-- The trivial subgroup is a torus. -/
theorem isTorus_bot : IsTorus (⊥ : Subgroup G) where
  isCompact := by
    rw [Subgroup.coe_bot]
    exact isCompact_singleton
  isConnected := by
    rw [Subgroup.coe_bot]
    exact isConnected_singleton
  isMulCommutative := inferInstance

/-- A compact connected commutative group is a torus of itself. -/
theorem isTorus_top [CompactSpace G] [ConnectedSpace G] [IsMulCommutative G] :
    IsTorus (⊤ : Subgroup G) where
  isCompact := by
    rw [Subgroup.coe_top]
    exact isCompact_univ
  isConnected := by
    rw [Subgroup.coe_top]
    exact isConnected_univ
  isMulCommutative := inferInstance

/-- A compact connected commutative group is its own maximal torus. -/
theorem isMaximalTorus_top [CompactSpace G] [ConnectedSpace G] [IsMulCommutative G] :
    IsMaximalTorus (⊤ : Subgroup G) :=
  ⟨isTorus_top, fun _ _ _ => le_top⟩

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

/-- **A torus lies in a closed subgroup whose Lie algebra contains its own.** -/
theorem IsTorus.le_of_lieSubalgebraOfSubgroup_le {T K : Subgroup G} (hT : IsTorus T)
    (hK : IsClosed (K : Set G))
    (h : lieSubalgebraOfSubgroup (I := I) T ≤ lieSubalgebraOfSubgroup (I := I) K) : T ≤ K := by
  intro t ht
  rw [← SetLike.mem_coe, ← hT.image_lieExp_lieSubalgebraOfSubgroup (I := I)] at ht
  obtain ⟨X, hX, rfl⟩ := ht
  exact lieExp_mem_of_mem_lieSubalgebraOfSubgroup hK (h hX)

/-- **A torus is determined by its Lie algebra.** -/
theorem IsTorus.eq_of_lieSubalgebraOfSubgroup_eq {T T' : Subgroup G} (hT : IsTorus T)
    (hT' : IsTorus T')
    (h : lieSubalgebraOfSubgroup (I := I) T = lieSubalgebraOfSubgroup (I := I) T') : T = T' :=
  le_antisymm (hT.le_of_lieSubalgebraOfSubgroup_le hT'.isClosed h.le)
    (hT'.le_of_lieSubalgebraOfSubgroup_le hT.isClosed h.ge)

/-- **A torus is a product of circles**: a torus `T` whose Lie algebra has dimension `r` is
isomorphic to `(Circle)^r` as a topological group. Through the closed-subgroup theorem `T` is a
compact connected commutative Lie group modelled on its Lie algebra, so this is
`TauCeti.nonempty_continuousMulEquiv_pi_circle`. -/
theorem IsTorus.nonempty_continuousMulEquiv_pi_circle {T : Subgroup G} (hT : IsTorus T) :
    Nonempty (T ≃ₜ* (Fin (Module.finrank ℝ (lieSubalgebraOfSubgroup (I := I) T)) → Circle)) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  obtain ⟨d⟩ :=
    nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed (I := I) hT.isClosed
  let F := (lieSubalgebraOfSubgroup (I := I) T).toSubmodule
  let _ : ChartedSpace F T := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, F) ∞ T := d.lieGroup
  have _ : CompactSpace T := isCompact_iff_compactSpace.mp hT.isCompact
  have _ : ConnectedSpace T := isConnected_iff_connectedSpace.mp hT.isConnected
  have _ : IsMulCommutative T := hT.isMulCommutative
  exact TauCeti.nonempty_continuousMulEquiv_pi_circle 𝓘(ℝ, F)

section Existence

variable (I)
include I

/-- The Lie algebra is finite-dimensional, so its lattice of Lie subalgebras is well-founded; a
local instance for the existence argument below. -/
private noncomputable local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

/-- **Every torus is contained in a maximal torus.** No compactness of `G` is needed. -/
theorem IsTorus.exists_isMaximalTorus_le {T : Subgroup G} (hT : IsTorus T) :
    ∃ T', IsMaximalTorus T' ∧ T ≤ T' := by
  -- The lattice of Lie subalgebras of `𝔤` is well-founded, so some torus containing `T` has a
  -- maximal Lie algebra; a torus containing it has the same Lie algebra, hence is equal to it.
  obtain ⟨T', ⟨hT', hle⟩, hmax⟩ := exists_maximalFor_of_wellFoundedGT
    (fun T' : Subgroup G => IsTorus T' ∧ T ≤ T') (lieSubalgebraOfSubgroup (I := I)) ⟨T, hT, le_rfl⟩
  refine ⟨T', ⟨hT', fun T'' hT'' hle' => ?_⟩, hle⟩
  rw [hT'.eq_of_lieSubalgebraOfSubgroup_eq hT'' (le_antisymm (lieSubalgebraOfSubgroup_mono hle')
    (hmax ⟨hT'', hle.trans hle'⟩ (lieSubalgebraOfSubgroup_mono hle')))]

/-- **Maximal tori exist.** -/
theorem exists_isMaximalTorus : ∃ T : Subgroup G, IsMaximalTorus T :=
  ((isTorus_bot (G := G)).exists_isMaximalTorus_le I).imp fun _ h => h.1

end Existence

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
