/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Acyclic
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ReducedHomology
public import TauCeti.AlgebraicTopology.Homotopy.ZModVanishing
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Contractible
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Mod-two vanishing for the contractible loops of a space

Serre's mod-two vanishing theorem says that the higher homotopy groups at a base point with
trivial fundamental group and mod-two acyclic ambient space are uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo`). This file
applies it to the component `Ω₀X` of the constant loop in the loop space of a pointed space
`(X, x)`, the space of contractible loops at `x`.

Since a path component has the homotopy groups of the ambient space in positive degrees
(`HomotopyGroup.subtypeValMulEquivOfPathComponentSubset`), applying the mod-two vanishing theorem
to the component of the constant loop and composing with the loop-space shift `πₖ₊₁(ΩX) ≅ πₖ₊₂(X)`
turns its conclusion into a statement about `X`. Suppose `π₂(X, x) = 0`, so that `Ω₀X` has
trivial fundamental group. If `Hᵢ(Ω₀X; 𝔽₂) = 0` for `i > 0`, then every homotopy group
`πₙ₊₃(X, x)` is uniquely two-divisible, hence `πₙ₊₃(X, x) ⊗ ℤ/2 = 0`. Contrapositively, a space
with `π₂(X) = 0` and `π_ℓ(X) ⊗ ℤ/2 ≠ 0` for some `ℓ ≥ 3` has contractible loops with nonzero
reduced mod-two homology. This is the topological step in Barraud–Damian–Humilière–Oancea's
proof of their Theorem 5.15, where it replaces an appeal to Hurewicz modulo the class of groups
`G` with `G ⊗ ℤ/2 = 0`, which is not a Serre class.

Both loop models are treated: the fixed-interval loops `Ω X x = Path x x`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_loopSpace`), and
the Moore loops `MooreLoopSpace X x`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace`),
whose constant loop is the loop `1` of length zero.

The same conclusion holds with the hypothesis on the double loop space `Ω²X`, the loop space of
`Ω₀X` at the constant loop, as in the source's proof. If `π₂(X, x) = 0`, then `Ω²X` is path
connected, and if it moreover has the mod-two homology of a point, so does `Ω₀X`
(`TauCeti.isIso_singularHomologyMap_pathComponent_of_isIso_loopSpace`). So every `πₙ₊₃(X, x)` is
uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_doubleLoopSpace`).
Contrapositively, if `π₂(X, x) ≠ 0` or `πₙ₊₃(X, x) ⊗ ℤ/2 ≠ 0` for some `n`, the reduced mod-two
homology `H~_*(Ω²X; 𝔽₂)` does not vanish
(`TauCeti.exists_nontrivial_reducedSingularHomology_doubleLoopSpace`): when `π₂(X, x) ≠ 0` it is
nonzero in degree zero, since `Ω²X` is not path connected. In the source's proof, the map
`i_{Q*} : H_*(Q; i_Q^*𝓕 ⊗ 𝔽₂) → H_*(𝓛₀Q; 𝓕 ⊗ 𝔽₂)` for `𝓕 = C_*(Ω𝓛₀Q)` is identified with the
map `H_*(Ω²Q; 𝔽₂) → H_*(pt; 𝔽₂)`, whose kernel is `H~_*(Ω²Q; 𝔽₂)`; that identification is not
formalized here.

## Main results

* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_loopSpace`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace`:
  if `π₂(X, x) = 0` and the contractible loops at `x` have the mod-two homology of a point, the
  homotopy groups `πₙ₊₃(X, x)` are uniquely two-divisible.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_doubleLoopSpace`
  and its Moore form, with suffix `doubleMooreLoopSpace`: the same with the hypothesis on the
  double loop space.
* `TauCeti.exists_nontrivial_reducedSingularHomology_doubleLoopSpace`,
  `TauCeti.exists_nontrivial_reducedSingularHomology_doubleMooreLoopSpace`: if `π₂(X, x) ≠ 0` or
  some `πₙ₊₃(X, x) ⊗ ℤ/2 ≠ 0`, the double loop space has nonzero reduced mod-two homology.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Theorem 5.15.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy TensorProduct

namespace TauCeti

variable {X : Type} [TopologicalSpace X] (x : X)

/-- **Mod-two vanishing for the contractible loops.** If `π₂(X, x)` is trivial and the path
component of the constant loop in the loop space `Ω X x` has the mod-two homology of a point,
then every homotopy group `πₙ₊₃(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_loopSpace
    [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton
      (((singularChains (ZMod 2)).obj (TopCat.of (pathComponent (Path.refl x)))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  -- The fundamental group of the path component of `Path.refl x` is `π₂(X, x)`.
  let c₀ : pathComponent (Path.refl x) := ⟨Path.refl x, mem_pathComponent_self _⟩
  have : Subsingleton (π_ 1 (pathComponent (Path.refl x)) c₀) :=
    ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      (HomotopyGroup.pathLoopSpaceMulEquiv 0)).toEquiv.subsingleton_congr.2 ‹_›
  (isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo (y := c₀) (n := n)
    fun q hq _ ↦ by
      obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      exact ModuleCat.isZero_iff_subsingleton.2 (hX q')).of_addEquiv
    ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      (HomotopyGroup.pathLoopSpaceMulEquiv (n + 1))).toAdditive

/-- **Mod-two vanishing for the contractible Moore loops.** If `π₂(X, x)` is trivial and the path
component of the constant loop `1` in the Moore loop space has the mod-two homology of a point,
then every homotopy group `πₙ₊₃(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace
    [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of (pathComponent (1 : MooreLoopSpace X x)))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  -- The fundamental group of the path component of `1` is `π₂(X, x)`.
  let c₀ : pathComponent (1 : MooreLoopSpace X x) := ⟨1, mem_pathComponent_self _⟩
  have : Subsingleton (π_ 1 (pathComponent (1 : MooreLoopSpace X x)) c₀) :=
    ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      (MooreLoopSpace.homotopyGroupMulEquiv x 0)).toEquiv.subsingleton_congr.2 ‹_›
  (isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo (y := c₀) (n := n)
    fun q hq _ ↦ by
      obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      exact ModuleCat.isZero_iff_subsingleton.2 (hX q')).of_addEquiv
    ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      (MooreLoopSpace.homotopyGroupMulEquiv x (n + 1))).toAdditive

/-! ### The double loop space -/

/-- **Mod-two vanishing for the double loop space.** If `π₂(X, x)` is trivial and the double loop
space `Ω²X` has no mod-two homology in positive degrees, then every homotopy group `πₙ₊₃(X, x)` is
uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_doubleLoopSpace
    [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) := by
  have := (pathConnectedSpace_doubleLoopSpace_iff x).2 ‹_›
  -- `Ω²X` is the loop space of `Ω₀X`, which therefore has the mod-two homology of a point.
  refine isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_loopSpace x
    (fun i ↦ ?_) n
  have := isIso_singularHomologyMap_pathComponent_of_isIso_loopSpace (ZMod 2) (Path.refl x)
    (i + 1) fun q _ ↦ isIso_singularHomologyMap_isTerminalPUnit_from_of_subsingleton _ _ hX q
  exact (isIso_singularHomologyMap_isTerminalPUnit_from_succ_iff _ _ i).1 this

/-- **Nonvanishing of the reduced mod-two homology of the double loop space.** If `π₂(X, x)` is
nontrivial, or `πₙ₊₃(X, x) ⊗ ℤ/2` is nontrivial for some `n`, then the reduced mod-two homology
`H~ₖ(Ω²X; 𝔽₂)` is nonzero in some degree `k`. This is the topological input to Theorem 5.15 of
Barraud–Damian–Humilière–Oancea, where `H~_*(Ω²Q; 𝔽₂)` is the kernel of `i_{Q*}`. -/
theorem exists_nontrivial_reducedSingularHomology_doubleLoopSpace
    (h : Nontrivial (π_ 2 X x) ∨ ∃ n, Nontrivial (Additive (π_ (n + 3) X x) ⊗[ℤ] ZMod 2)) :
    ∃ k, Nontrivial ((reducedSingularHomologyFunctor (ModuleCat.of (ZMod 2) (ZMod 2)) k).obj
      (TopCat.of (Ω (Ω X x) (Path.refl x)))) := by
  by_contra! hX
  -- A nontrivial `π₂(X, x)` gives nonzero reduced homology in degree zero.
  have : Subsingleton (π_ 2 X x) := not_nontrivial_iff_subsingleton.1 fun _ ↦
    have ⟨_, hf⟩ := exists_injective_doubleLoopSpaceReducedHomology₀ (R := ZMod 2) x
    not_nontrivial_iff_subsingleton.2 (hX 0) hf.nontrivial
  obtain h | ⟨n, hn⟩ := h
  · exact not_nontrivial_iff_subsingleton.2 this h
  -- Otherwise every `πₙ₊₃(X, x)` is uniquely two-divisible, so `πₙ₊₃(X, x) ⊗ ℤ/2` vanishes.
  have hX' (i : ℕ) := hX (i + 1)
  simp only [reducedSingularHomologyFunctor_succ, singularHomologyFunctor_obj_obj] at hX'
  exact not_nontrivial_iff_subsingleton.2
    (isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_doubleLoopSpace x hX'
      n).subsingleton_tensorProduct_zmod_two hn

/-- **Mod-two vanishing for the double Moore loop space.** If `π₂(X, x)` is trivial and the
double Moore loop space has no mod-two homology in positive degrees, then every homotopy group
`πₙ₊₃(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_doubleMooreLoopSpace
    [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) := by
  have := MooreLoopSpace.pathConnectedSpace_double x
  -- It is the Moore loop space of the contractible Moore loops, which therefore have the mod-two
  -- homology of a point.
  refine isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace x
    (fun i ↦ ?_) n
  have := isIso_singularHomologyMap_pathComponent_of_isIso_mooreLoopSpace (ZMod 2)
    (1 : MooreLoopSpace X x) (i + 1) fun q _ ↦
      isIso_singularHomologyMap_isTerminalPUnit_from_of_subsingleton _ _ hX q
  exact (isIso_singularHomologyMap_isTerminalPUnit_from_succ_iff _ _ i).1 this

/-- **Nonvanishing of the reduced mod-two homology of the double Moore loop space.** If
`π₂(X, x)` is nontrivial, or `πₙ₊₃(X, x) ⊗ ℤ/2` is nontrivial for some `n`, then the reduced mod-two
homology of the double Moore loop space is nonzero in some degree. -/
theorem exists_nontrivial_reducedSingularHomology_doubleMooreLoopSpace
    (h : Nontrivial (π_ 2 X x) ∨ ∃ n, Nontrivial (Additive (π_ (n + 3) X x) ⊗[ℤ] ZMod 2)) :
    ∃ k, Nontrivial ((reducedSingularHomologyFunctor (ModuleCat.of (ZMod 2) (ZMod 2)) k).obj
      (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))) := by
  by_contra! hX
  -- A nontrivial `π₂(X, x)` gives nonzero reduced homology in degree zero.
  have : Subsingleton (π_ 2 X x) := not_nontrivial_iff_subsingleton.1 fun _ ↦
    have ⟨_, hf⟩ := MooreLoopSpace.exists_injective_doubleReducedHomology₀ (R := ZMod 2) x
    not_nontrivial_iff_subsingleton.2 (hX 0) hf.nontrivial
  obtain h | ⟨n, hn⟩ := h
  · exact not_nontrivial_iff_subsingleton.2 this h
  -- Otherwise every `πₙ₊₃(X, x)` is uniquely two-divisible, so `πₙ₊₃(X, x) ⊗ ℤ/2` vanishes.
  have hX' (i : ℕ) := hX (i + 1)
  simp only [reducedSingularHomologyFunctor_succ, singularHomologyFunctor_obj_obj] at hX'
  exact not_nontrivial_iff_subsingleton.2
    (isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_doubleMooreLoopSpace x
      hX' n).subsingleton_tensorProduct_zmod_two hn

end TauCeti
