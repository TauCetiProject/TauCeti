/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Degree
public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
import TauCeti.AlgebraicTopology.Singular.Contractible
import TauCeti.Topology.Homotopy.MappingPath.PathFibration

/-!
# Acyclic Eilenberg--Mac Lane spaces through the path fibration

Let `k` be a commutative ring. A Serre fibration whose fibres are `K(G, n)` spaces induces
isomorphisms on `k`-homology as soon as `K(G, n)` spaces have the `k`-homology of a point
(`TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber`). This is the case of
`TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber` where the fibres are
Eilenberg--Mac Lane spaces; in the language of the Serre spectral sequence, its second page is
concentrated on the bottom row, which is the homology of the base.

Applied to the based path fibration `p : P → X` of a `K(A, n + 1)` space `X`, whose total space
`P`, the paths ending at the base point, is contractible and whose fibres are homotopy equivalent
to the loop space of `X`, a `K(A, n)` space, this gives an induction on `n`: every `K(A, n)` space,
`n ≥ 1`, has the `k`-homology of a point as soon as every `K(A, 1)` space has
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne`).
No hypothesis of CW type is made on the spaces.

## Main results

* `TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber`: a Serre fibration whose
  fibres are `k`-acyclic `K(G, n)` spaces is a `k`-homology isomorphism.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne`:
  `K(A, n)` spaces are `k`-acyclic as soon as `K(A, 1)` spaces are.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

/-- **A Serre fibration with acyclic Eilenberg--Mac Lane fibres is a homology isomorphism.** A
Serre fibration whose fibres are `K(G, n)` spaces induces isomorphisms on `k`-homology, as soon as
`K(G, n)` spaces have no positive-degree `k`-homology. -/
theorem isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber {G : Type u} [Group G]
    {n : ℕ} [NeZero n] {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : TauCeti.TopCat.serreFibrations p)
    (hfib : ∀ b, ∃ y, IsEilenbergMacLaneSpace G n (p.fiber b) y)
    (hK : ∀ {X : Type u} [TopologicalSpace X] {x : X}, IsEilenbergMacLaneSpace G n X x →
      ∀ i, Subsingleton (((singularChains k).obj (_root_.TopCat.of X)).homology (i + 1)))
    (i : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).map p) :=
  TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber hp k i
    (fun b ↦ (hfib b).choose_spec.pathConnectedSpace) fun b q hq0 _ ↦ by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      rw [singularHomologyFunctor_obj_obj]
      exact ModuleCat.isZero_iff_subsingleton.2 (hK (hfib b).choose_spec q)

namespace IsEilenbergMacLaneSpace

/-- The induction on the degree, through the based path fibration. The degree is written `j + 1`
so that the induction does not have to carry a `NeZero` instance. -/
private theorem subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne_succ {A : Type u}
    [AddCommGroup A]
    (hA : ∀ {X : Type u} [TopologicalSpace X] {x : X},
      IsEilenbergMacLaneSpaceOne (Multiplicative A) X x →
        ∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1))) (j : ℕ) :
    ∀ {X : Type u} [TopologicalSpace X] {x : X},
      IsEilenbergMacLaneSpace (Multiplicative A) (j + 1) X x →
        ∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) := by
  induction j with
  | zero =>
    intro X _ x hX i
    exact hA (isEilenbergMacLaneSpace_one_iff.1 hX) i
  | succ j ih =>
    intro X _ x hX i
    have := hX.pathConnectedSpace
    -- The based path fibration `P → X`, sending a path ending at `x` to its starting point.
    let p : TopCat.of (MappingPathFiber (ContinuousMap.id X) x) ⟶ TopCat.of X :=
      TopCat.ofHom (MappingPathFiber.proj _ x)
    have hp : TauCeti.TopCat.serreFibrations p :=
      (MappingPathFiber.isHurewiczFibration_proj.{u} _ _).mem_serreFibrations
    -- Every fibre is homotopy equivalent to the loop space, a `K(A, j + 1)` space.
    have hfib (b : X) : ∃ y, IsEilenbergMacLaneSpace (Multiplicative A) (j + 1) (p.fiber b) y :=
      hX.exists_fiber_mappingPathFiberProj (ContinuousMap.id X) x b
    have := isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber k hp hfib ih (i + 1)
    -- The total space is contractible, so its positive-degree homology vanishes.
    rw [← subsingleton_singularChains_homology_iff_of_isIso k p (i + 1),
      ← singularHomologyFunctor_obj_obj]
    infer_instance

/-- **`K(A, n)` spaces are acyclic as soon as `K(A, 1)` spaces are.** If every `K(A, 1)` space
has no homology in positive degrees with coefficients in a commutative ring `k`, then neither has
any `K(A, n)` space, `n ≥ 1`. The induction goes through the based path fibration of a
`K(A, n + 1)` space, whose total space is contractible and whose fibres are `K(A, n)` spaces. -/
theorem subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne {A : Type u}
    [AddCommGroup A] (hA : ∀ {X : Type u} [TopologicalSpace X] {x : X},
      IsEilenbergMacLaneSpaceOne (Multiplicative A) X x →
        ∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)))
    {n : ℕ} [NeZero n] {X : Type u} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne_succ k hA j hX i

end IsEilenbergMacLaneSpace

end TauCeti
