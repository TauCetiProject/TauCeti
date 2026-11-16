/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
import TauCeti.AlgebraicTopology.Singular.Contractible
import TauCeti.Topology.Homotopy.MappingPath.PathFibration

/-!
# Eilenberg--Mac Lane spaces of uniquely divisible groups

Let `m` be an integer, `A` an abelian group on which multiplication by `m` is bijective, and `k` a
commutative semisimple ring in which `m = 0`, for instance `k = 𝔽₂` and `m = 2`. Then every
Eilenberg--Mac Lane space of type `K(A, n)`, for every `n ≥ 1`, has the `k`-homology of a point
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`). For
`m = 2`: every `K(A, n)` space of a uniquely two-divisible group has the mod-two homology of a
point (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`).
No hypothesis of CW type is made on the space.

The case `n = 1` is the computation of the group homology of `A`
(`TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul`). The
induction goes through the based path fibration `p : P → X` of a `K(A, n + 1)` space `X`, whose
total space `P`, the paths ending at the base point, is contractible. Its fibre over any point is
homotopy equivalent to the loop space of `X`, a `K(A, n)` space, so all fibres have the
`k`-homology of a point by induction. A Serre fibration whose fibres have the homology of a point
induces isomorphisms on homology
(`TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber`), so `X` has the homology of the
contractible space `P`. In the language of the Serre spectral sequence, its second page is
concentrated on the bottom row, which is the homology of the base. The same argument shows that
every Serre fibration with `K(A, n)` fibres is a homology isomorphism modulo `m`
(`TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber`).

This is the input on Eilenberg--Mac Lane spaces of Serre's theorem that the homotopy groups of a
simply connected space with the mod-two homology of a point are uniquely two-divisible.

## Main results

* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`: a `K(A, n)`
  space of a uniquely `m`-divisible abelian group is acyclic modulo `m`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`: a
  `K(A, n)` space of a uniquely two-divisible abelian group has the mod-two homology of a point.
* `TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber`: a Serre fibration whose
  fibres are `K(A, n)` spaces of a uniquely `m`-divisible abelian group is a homology isomorphism
  modulo `m`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace TauCeti

namespace IsEilenbergMacLaneSpace

variable (k : Type) [CommRing k] [IsSemisimpleRing k] {m : ℤ}

omit [IsSemisimpleRing k] in
/-- A Serre fibration whose fibres are `K(G, n)` spaces induces isomorphisms on `k`-homology, as
soon as `K(G, n)` spaces have no positive-degree `k`-homology. -/
private theorem isIso_singularHomologyMap_of_fiber {G : Type} [Group G] {n : ℕ} [NeZero n]
    {E B : _root_.TopCat.{0}} {p : E ⟶ B} (hp : TauCeti.TopCat.serreFibrations p)
    (hfib : ∀ b, ∃ y, IsEilenbergMacLaneSpace G n (p.fiber b) y)
    (hK : ∀ {X : Type} [TopologicalSpace X] {x : X}, IsEilenbergMacLaneSpace G n X x →
      ∀ i, Subsingleton (((singularChains k).obj (_root_.TopCat.of X)).homology (i + 1)))
    (i : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} k) i).obj (ModuleCat.of k k)).map p) :=
  TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber hp k i
    (fun b ↦ (hfib b).choose_spec.pathConnectedSpace) fun b q hq0 _ ↦ by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      rw [singularHomologyFunctor_obj_obj]
      exact ModuleCat.isZero_iff_subsingleton.2 (hK (hfib b).choose_spec q)

/-- The induction on the degree, through the based path fibration. The degree is written `j + 1`
so that the induction does not have to carry a `NeZero` instance. -/
private theorem subsingleton_singularHomology_of_bijective_zsmul_succ (hmk : (m : k) = 0)
    {A : Type} [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) (j : ℕ) :
    ∀ {X : Type} [TopologicalSpace X] {x : X},
      IsEilenbergMacLaneSpace (Multiplicative A) (j + 1) X x →
        ∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) := by
  induction j with
  | zero =>
    intro X _ x hX i
    exact IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul k hmk hA
      (isEilenbergMacLaneSpace_one_iff.1 hX) i
  | succ j ih =>
    intro X _ x hX i
    have := hX.pathConnectedSpace
    -- The based path fibration `P → X`, sending a path ending at `x` to its starting point.
    let p : TopCat.of (MappingPathFiber (ContinuousMap.id X) x) ⟶ TopCat.of X :=
      TopCat.ofHom (MappingPathFiber.proj _ x)
    have hp : TauCeti.TopCat.serreFibrations p :=
      (MappingPathFiber.isHurewiczFibration_proj.{0} _ _).mem_serreFibrations
    -- Every fibre is homotopy equivalent to the loop space, a `K(A, j + 1)` space.
    have hfib (b : X) : ∃ y, IsEilenbergMacLaneSpace (Multiplicative A) (j + 1) (p.fiber b) y :=
      hX.exists_fiber_mappingPathFiberProj (ContinuousMap.id X) x b
    have := isIso_singularHomologyMap_of_fiber k hp hfib ih (i + 1)
    -- The total space is contractible, so its positive-degree homology vanishes.
    rw [← subsingleton_singularChains_homology_iff_of_isIso k p (i + 1),
      ← singularHomologyFunctor_obj_obj]
    infer_instance

/-- **`K(A, n)` spaces of uniquely `m`-divisible groups are acyclic modulo `m`.** If
multiplication by the integer `m` is a bijection of the abelian group `A`, then every `K(A, n)`
space, for every `n ≥ 1`, has no homology in positive degrees with coefficients in a commutative
semisimple ring `k` in which `m = 0`. -/
theorem subsingleton_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    (i : ℕ) : Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact subsingleton_singularHomology_of_bijective_zsmul_succ k hmk hA j hX i

/-- **Mod-two acyclicity of `K(A, n)` spaces.** For a uniquely two-divisible abelian group `A`
and every `n ≥ 1`, every `K(A, n)` space has the mod-two homology of a point: `Hᵢ(X; 𝔽₂) = 0` for
all `i > 0`. -/
theorem subsingleton_singularHomology_of_isUniquelyTwoDivisible {A : Type} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) hX i

end IsEilenbergMacLaneSpace

/-- **A Serre fibration with `K(A, n)` fibres is a homology isomorphism modulo `m`.** If
multiplication by the integer `m` is a bijection of the abelian group `A`, then a Serre fibration
whose fibres are `K(A, n)` spaces, `n ≥ 1`, induces isomorphisms on homology with coefficients in
a commutative semisimple ring `k` in which `m = 0`. -/
theorem isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber (k : Type) [CommRing k]
    [IsSemisimpleRing k] {m : ℤ} (hmk : (m : k) = 0) {A : Type} [AddCommGroup A]
    (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {E B : _root_.TopCat.{0}}
    {p : E ⟶ B} (hp : TauCeti.TopCat.serreFibrations p)
    (hfib : ∀ b, ∃ y, IsEilenbergMacLaneSpace (Multiplicative A) n (p.fiber b) y) (i : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} k) i).obj (ModuleCat.of k k)).map p) :=
  IsEilenbergMacLaneSpace.isIso_singularHomologyMap_of_fiber k hp hfib
    (IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul k hmk hA) i

end TauCeti
