/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Exponent
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
import TauCeti.Algebra.Category.ModuleCat.Annihilated
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.Topology.Homotopy.MappingPath.Fiber
import TauCeti.Topology.Homotopy.MappingPath.PathFibration

/-!
# Eilenberg--Mac Lane spaces of groups killed by a power of `d`

Let `d` be a natural number and `A` an abelian group annihilated by some power of `d`. Then the
positive-degree integral homology of every Eilenberg--Mac Lane space of type `K(A, n)`, `n ≥ 1`, is
annihilated by some power of `d`, degree by degree
(`TauCeti.IsEilenbergMacLaneSpace.isKilledBySomePower_singularHomology`). No hypothesis of CW type
is made on the space, and none of finite generation on `A`.

This is Serre's axiom on the homology of Eilenberg--Mac Lane spaces for the class
`AddCommGrpCat.isKilledBySomePower d` of groups annihilated by some power of `d`, in every degree
`n`. It is the input on Eilenberg--Mac Lane spaces of Serre's Hurewicz theorem modulo that class,
which climbs the Whitehead tower through fibrations with fibres `K(πₙ, n - 1)`.

The case `n = 1` is the computation of the homology of `K(A, 1)`, killed by the exponent of `A`
(`TauCeti.isKilledBySomePower_classifyingSpace_singularHomology`). The induction goes through the
based path fibration `p : P → X` of a `K(A, n + 1)` space `X`, whose total space is contractible
and whose fibres are homotopy equivalent to the loop space `ΩX`, a `K(A, n)` space. Since the
class is not closed under infinite direct sums, the comparison theorem modulo a Serre class
(`TauCeti.TopCat.prop_singularHomology_of_contractibleSpace`) needs the homology of all fibres to
be annihilated by one fixed power of `d` in the degrees considered. That power is read off the
single space `ΩX`, in finitely many degrees, and transported to every fibre
(`TauCeti.exists_isKilledBy_singularHomology_of_homotopyEquiv`).

## Main results

* `TauCeti.IsEilenbergMacLaneSpace.isKilledBySomePower_singularHomology`: if `A` is annihilated by
  some power of `d`, so is `Hᵢ₊₁(K(A, n); ℤ)` for every `i`.
* `TauCeti.exists_isKilledBy_singularHomology_of_homotopyEquiv`: one power of `d` annihilates the
  homology, in finitely many positive degrees, of all spaces homotopy equivalent to a given one.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter I.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace TauCeti

/-- **One power of `d` for a family of homotopy equivalent spaces.** If the integral homology of a
space `F` in the degrees `1, …, k` is annihilated by powers of `d`, then a single power `d ^ M`
annihilates the homology in these degrees of every space `Y i` of a family of spaces homotopy
equivalent to `F`. This is the uniform bound on the fibres of a fibration that the comparison
theorem modulo the class of groups annihilated by some power of `d` needs. -/
theorem exists_isKilledBy_singularHomology_of_homotopyEquiv {ι : Type*} {Y : ι → Type}
    [∀ i, TopologicalSpace (Y i)] {F : Type} [TopologicalSpace F]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (Y i) F) {d k : ℕ}
    (hF : ∀ q, q ≠ 0 → q ≤ k → AddCommGrpCat.isKilledBySomePower d
      (AddCommGrpCat.of (((singularChains ℤ).obj (TopCat.of F)).homology q))) :
    ∃ M : ℕ, ∀ i q, q ≠ 0 → q ≤ k → ObjectProperty.isKilledBy (ModuleCat.{0} ℤ) (d ^ M)
      (((singularChains ℤ).obj (TopCat.of (Y i))).homology q) := by
  obtain ⟨M, hM⟩ := AddCommGrpCat.exists_forall_isTorsionBy_of_isKilledBySomePower
    (Set.finite_Ioc 0 k) fun q hq ↦ hF q hq.1.ne' hq.2
  refine ⟨M, fun i q hq0 hq ↦ ObjectProperty.prop_of_iso _
    ((e i).singularHomologyIso (ModuleCat.of ℤ ℤ) q).symm
    ((ModuleCat.prop_isKilledBy_iff _ _).2 fun y ↦ ?_)⟩
  rw [← natCast_zsmul, Nat.cast_pow]
  exact hM q ⟨Nat.pos_of_ne_zero hq0, hq⟩ (x := y)

namespace IsEilenbergMacLaneSpace

variable {d : ℕ} {A : Type} [AddCommGroup A]

/-- The induction on the degree, through the based path fibration. The degree is written `j + 1`
so that the induction does not have to carry a `NeZero` instance. -/
private theorem isKilledBySomePower_singularHomology_succ
    (hA : AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of A)) (j : ℕ) :
    ∀ {X : Type} [TopologicalSpace X] {x : X},
      IsEilenbergMacLaneSpace (Multiplicative A) (j + 1) X x → ∀ i,
        AddCommGrpCat.isKilledBySomePower d
          (AddCommGrpCat.of (((singularChains ℤ).obj (TopCat.of X)).homology (i + 1))) := by
  -- The Serre class of `ℤ`-modules annihilated by some power of `d`.
  let P := (AddCommGrpCat.isKilledBySomePower d).inverseImage
    (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat)
  induction j with
  | zero =>
    intro X _ x hX i
    -- A `K(A, 1)` space is weakly equivalent to the classifying space of `A`.
    obtain ⟨f, hf⟩ :=
      (isEilenbergMacLaneSpace_one_iff.1 hX).exists_isWeakHomotopyEquivalence_classifyingSpace
    exact P.prop_of_iso
      (@asIso _ _ _ _ _ (hf.isIso_singularHomologyMap (ModuleCat.of ℤ ℤ) (i + 1)))
      (isKilledBySomePower_classifyingSpace_singularHomology ℤ hA i)
  | succ j ih =>
    intro X _ x hX i
    have := hX.pathConnectedSpace
    -- The based path fibration `P → X`, sending a path ending at `x` to its starting point, has
    -- contractible total space and fibres homotopy equivalent to the loop space `ΩX`, a
    -- `K(A, j + 1)` space. So one power `d ^ M` annihilates the homology of all fibres in
    -- degrees `1, …, i + 1`.
    let p : TopCat.of (MappingPathFiber (ContinuousMap.id X) x) ⟶ TopCat.of X :=
      TopCat.ofHom (MappingPathFiber.proj _ x)
    obtain ⟨M, hM⟩ := exists_isKilledBy_singularHomology_of_homotopyEquiv
      (Y := fun b ↦ p.fiber b) (k := i + 1)
      (fun b ↦ MappingPathFiber.projFiberHomotopyEquivLoopSpace (ContinuousMap.id X) x b
        (PathConnectedSpace.somePath b x))
      fun q hq0 _ ↦ by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
        exact ih hX.loopSpace q
    exact TauCeti.TopCat.prop_singularHomology_of_contractibleSpace P
      (ObjectProperty.isKilledBy (ModuleCat.{0} ℤ) (d ^ M))
      (AddCommGrpCat.isKilledBy_pow_le_inverseImage_isKilledBySomePower d M)
      (MappingPathFiber.isHurewiczFibration_proj.{0} _ _).mem_serreFibrations
      (Nat.succ_ne_zero i)
      (fun b ↦ (hX.exists_fiber_mappingPathFiberProj (ContinuousMap.id X) x b).choose_spec
        |>.pathConnectedSpace) hM

/-- **Serre's `K(A, n)` axiom for the groups annihilated by a power of `d`.** If an abelian group
`A` is annihilated by some power of `d`, then for every `n ≥ 1` and every `i`, the integral
homology `Hᵢ₊₁(X; ℤ)` of every `K(A, n)` space `X` is annihilated by some power of `d`. -/
theorem isKilledBySomePower_singularHomology
    (hA : AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of A)) {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    (i : ℕ) :
    AddCommGrpCat.isKilledBySomePower d
      (AddCommGrpCat.of (((singularChains ℤ).obj (TopCat.of X)).homology (i + 1))) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact isKilledBySomePower_singularHomology_succ hA j hX i

end IsEilenbergMacLaneSpace

end TauCeti
