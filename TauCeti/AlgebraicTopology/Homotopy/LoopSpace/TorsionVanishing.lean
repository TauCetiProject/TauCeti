/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ReducedHomology
public import TauCeti.AlgebraicTopology.Homotopy.TorsionVanishing
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Acyclic
import TauCeti.AlgebraicTopology.Singular.Coefficients.FlatBaseChange

/-!
# Torsion homotopy groups from the homology of loop spaces

Let `S` be a submonoid of `ℤ`, for instance the nonzero integers or the powers of an integer `d`.
Serre's theorem modulo `S`-torsion says that the homotopy groups of a simply connected space whose
reduced integral homology is `S`-torsion are `S`-torsion
(`TauCeti.isTorsion'_homotopyGroup_of_isTorsion'_singularHomology`), and its path-component form
(`TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology_pathComponent`) needs only
the path component of the base point to be simply connected. This file
applies it to the component `Ω₀X` of the constant loop in the loop space of a pointed space
`(X, x)`, and then to the double loop space `Ω²X`.

Suppose that `π₂(X, x)` is trivial, so that `Ω₀X` is simply connected and `Ω²X` is path connected.

* If `Ω₀X` has the homology of a point with coefficients in the localization `S⁻¹ℤ`, then every
  homotopy group `πₙ₊₃(X, x) ≅ πₙ₊₂(Ω₀X)` is `S`-torsion
  (`TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology_loopSpace`, and
  `TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace` for the Moore
  loops).
* If `Ω²X` has the homology of a point over `S⁻¹ℤ`, so does its delooping `Ω₀X`, through the path
  fibration `Ω²X → P → Ω₀X` with contractible total space
  (`TauCeti.isIso_singularHomologyMap_pathComponent_of_isIso_loopSpace`). By flat base change,
  the hypothesis says that the positive-degree integral homology of `Ω²X` is `S`-torsion
  (`TauCeti.isTorsion'_homotopyGroup_of_isTorsion'_singularHomology_doubleLoopSpace`).

Contrapositively, if `π₂(X, x)` is nontrivial, or if some `π_ℓ(X, x)`, `ℓ ≥ 3`, has an element
killed by no element of `S`, then the reduced integral homology `H~_*(Ω²X; ℤ)` has a class killed
by no element of `S`, provided `0 ∉ S`
(`TauCeti.exists_not_isTorsion'_reducedSingularHomology_doubleLoopSpace`). In degree zero this is
the copy of `ℤ` in `H~₀(Ω²X; ℤ)` indexed by a nontrivial element of `π₂(X, x)`
(`TauCeti.exists_injective_doubleLoopSpaceReducedHomology₀`). For the nonzero integers: if
`π₂(X, x) ≠ 0` or some `π_ℓ(X, x)`, `ℓ ≥ 3`, has an element of infinite order, then `H~_*(Ω²X; ℤ)`
is not a torsion group (`TauCeti.exists_not_isAddTorsion_reducedSingularHomology_doubleLoopSpace`).

This is the topological input of Barraud–Damian–Humilière–Oancea's proof of their Theorem 5.14
(Theorem B of the introduction): there the kernel of the map `i_{Q*}` induced by the constant loops
is identified with `H~_*(Ω²Q; ℤ)`, and the theorem needs it to contain a non-torsion class. With
`S` the powers of an integer `d`, it gives an elementwise analogue of the homotopy-to-homology
content of the second part of their Proposition 5.11. Here `d`-torsion is elementwise, each element
being annihilated by some power of `d`, while the source states that proposition for groups
annihilated by a single power of `d`, a stronger condition for groups that are not finitely
generated. Their proof applies the Hurewicz theorem modulo the class of torsion groups (their
Theorem 5.12) to `Ω₀Q` and the Leray–Serre spectral sequence of the path fibration over `Ω₀Q`; here
both steps are replaced by the vanishing theorems with localized coefficients.

The double loop space is the fixed-interval model `Ω (Ω X x) (Path.refl x)`.

## Main results

* `TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology_loopSpace`,
  `TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace`: if
  `π₂(X, x) = 0` and the contractible loops at `x` have the homology of a point over `S⁻¹ℤ`, the
  homotopy groups `πₙ₊₃(X, x)` are `S`-torsion.
* `TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology_doubleLoopSpace`: the same
  with the hypothesis on the double loop space.
* `TauCeti.isTorsion'_homotopyGroup_of_isTorsion'_singularHomology_doubleLoopSpace`: if
  `π₂(X, x) = 0` and the positive-degree integral homology of `Ω²X` is `S`-torsion, so are the
  homotopy groups `πₙ₊₃(X, x)`.
* `TauCeti.exists_not_isTorsion'_reducedSingularHomology_doubleLoopSpace`,
  `TauCeti.exists_not_isAddTorsion_reducedSingularHomology_doubleLoopSpace`: the contrapositive,
  stated on the reduced homology of `Ω²X`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11 and the proof of
  Theorem 5.14.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

namespace TauCeti

variable (S : Submonoid ℤ) {X : Type} [TopologicalSpace X] (x : X)

/-- **Torsion homotopy groups from the contractible loops.** Let `k` be a localization of `ℤ` at a
submonoid `S`. If `π₂(X, x)` is trivial and the path component of the constant loop in the loop
space `Ω X x` has the `k`-homology of a point, then every homotopy group `πₙ₊₃(X, x)` is
`S`-torsion. -/
theorem isTorsion'_homotopyGroup_of_subsingleton_singularHomology_loopSpace (k : Type) [CommRing k]
    [Algebra ℤ k] [IsLocalization S k] [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton
      (((singularChains k).obj (TopCat.of (pathComponent (Path.refl x)))).homology (i + 1)))
    (n : ℕ) : Module.IsTorsion' (Additive (π_ (n + 3) X x)) S :=
  -- The fundamental group of the loop space is `π₂(X, x)`.
  have : Subsingleton (FundamentalGroup (Ω X x) (Path.refl x)) :=
    HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv.toEquiv.subsingleton_congr.2 ‹_›
  (HomotopyGroup.pathLoopSpaceMulEquiv (n + 1)).toAdditive.isTorsion'_iff.1
    (isTorsion'_homotopyGroup_of_subsingleton_singularHomology_pathComponent S k (Path.refl x) hX
      n)

/-- **Torsion homotopy groups from the contractible Moore loops.** Let `k` be a localization of
`ℤ` at a submonoid `S`. If `π₂(X, x)` is trivial and the path component of the constant loop `1` in
the Moore loop space has the `k`-homology of a point, then every homotopy group `πₙ₊₃(X, x)` is
`S`-torsion. -/
theorem isTorsion'_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace (k : Type)
    [CommRing k] [Algebra ℤ k] [IsLocalization S k] [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton (((singularChains k).obj
      (TopCat.of (pathComponent (1 : MooreLoopSpace X x)))).homology (i + 1)))
    (n : ℕ) : Module.IsTorsion' (Additive (π_ (n + 3) X x)) S :=
  -- The fundamental group of the Moore loop space is `π₂(X, x)`.
  have : Subsingleton (FundamentalGroup (MooreLoopSpace X x) 1) :=
    (HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
      (MooreLoopSpace.homotopyGroupMulEquiv x 0)).toEquiv.subsingleton_congr.2 ‹_›
  (MooreLoopSpace.homotopyGroupMulEquiv x (n + 1)).toAdditive.isTorsion'_iff.1
    (isTorsion'_homotopyGroup_of_subsingleton_singularHomology_pathComponent S k
      (1 : MooreLoopSpace X x) hX n)

/-- **Torsion homotopy groups from the double loop space.** Let `k` be a localization of `ℤ` at a
submonoid `S`. If `π₂(X, x)` is trivial and the double loop space `Ω²X` has no `k`-homology in
positive degrees, then every homotopy group `πₙ₊₃(X, x)` is `S`-torsion. The double loop space is
then path connected, so it has the `k`-homology of a point, and so does its delooping `Ω₀X`. -/
theorem isTorsion'_homotopyGroup_of_subsingleton_singularHomology_doubleLoopSpace (k : Type)
    [CommRing k] [Algebra ℤ k] [IsLocalization S k] [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton (((singularChains k).obj
      (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology (i + 1)))
    (n : ℕ) : Module.IsTorsion' (Additive (π_ (n + 3) X x)) S := by
  have := (pathConnectedSpace_doubleLoopSpace_iff x).2 ‹_›
  let H (q : ℕ) := (singularHomologyFunctor (ModuleCat.{0} k) q).obj (ModuleCat.of k k)
  have hpt (i : ℕ) : IsZero ((H (i + 1)).obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ (i + 1) _ _ i.succ_ne_zero
  -- The path-connected space `Ω²X` without positive-degree homology has the homology of a point.
  have hΩ (q : ℕ) : IsIso ((H q).map (TopCat.isTerminalPUnit.from
      (TopCat.of (Ω (Ω X x) (Path.refl x))))) := by
    rcases q with _ | i
    · exact IsIso.of_isIso_fac_right (singularHomologyMap_singularHomology₀ε _ _)
    · exact (ModuleCat.isZero_iff_subsingleton.2 (hX i)).isIso (hpt i) _
  refine isTorsion'_homotopyGroup_of_subsingleton_singularHomology_loopSpace S x k (fun i ↦ ?_) n
  -- So does the path component `Ω₀X` of the constant loop, whose loop space is `Ω²X`.
  have := isIso_singularHomologyMap_pathComponent_of_isIso_loopSpace k (Path.refl x) (i + 1)
    fun q _ ↦ hΩ q
  exact (subsingleton_singularChains_homology_iff_of_isIso k
    (TopCat.isTerminalPUnit.from (TopCat.of (pathComponent (Path.refl x)))) (i + 1)).2
    (ModuleCat.isZero_iff_subsingleton.1 (hpt i))

/-- **Torsion homotopy groups from the integral homology of the double loop space.** Let `S` be a
submonoid of `ℤ`. If `π₂(X, x)` is trivial and every class of the positive-degree integral homology
of the double loop space `Ω²X` is killed by an element of `S`, then so is every element of every
homotopy group `πₙ₊₃(X, x)`. -/
theorem isTorsion'_homotopyGroup_of_isTorsion'_singularHomology_doubleLoopSpace
    [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Module.IsTorsion' (((singularChains ℤ).obj
      (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology (i + 1)) S)
    (n : ℕ) : Module.IsTorsion' (Additive (π_ (n + 3) X x)) S :=
  -- Instance search does not find this through the semiring structure of `ℤ` that `S` carries.
  haveI : IsLocalization S (Localization S) := Localization.isLocalization
  isTorsion'_homotopyGroup_of_subsingleton_singularHomology_doubleLoopSpace S x (Localization S)
    (fun i ↦ (isTorsion'_singularChains_int_homology_iff S _ _ (i + 1)).1 (hX i)) n

/-- **The reduced homology of the double loop space is not `S`-torsion.** Let `S` be a submonoid
of `ℤ` not containing `0`. If `π₂(X, x)` is nontrivial, or if some homotopy group `πₙ₊₃(X, x)` has
an element killed by no element of `S`, then some reduced integral homology group `H~ᵢ(Ω²X; ℤ)`
has a class killed by no element of `S`. -/
theorem exists_not_isTorsion'_reducedSingularHomology_doubleLoopSpace (hS : (0 : ℤ) ∉ S)
    (h : Nontrivial (π_ 2 X x) ∨ ∃ n, ¬ Module.IsTorsion' (Additive (π_ (n + 3) X x)) S) :
    ∃ i, ¬ Module.IsTorsion' ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) i).obj
      (TopCat.of (Ω (Ω X x) (Path.refl x)))) S := by
  -- If `π₂(X, x)` is nontrivial, `H~₀(Ω²X; ℤ)` contains a copy of `ℤ`, on which only `0` acts by
  -- zero.
  have h₀ (h2 : Nontrivial (π_ 2 X x)) : ¬ Module.IsTorsion'
      ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 0).obj
        (TopCat.of (Ω (Ω X x) (Path.refl x)))) S := fun hT ↦ by
    obtain ⟨f, hf⟩ := exists_injective_doubleLoopSpaceReducedHomology₀ (R := ℤ) x
    obtain ⟨⟨s, hs⟩, hs1⟩ := @hT (f 1)
    have hfs : f s = f 0 := by
      rw [map_zero, ← hs1, Submonoid.smul_def]
      simpa using map_zsmul f s 1
    exact hS (hf hfs ▸ hs)
  rcases h with h | ⟨n, hn⟩
  · exact ⟨0, h₀ h⟩
  · by_contra! hT
    have : Subsingleton (π_ 2 X x) := not_nontrivial_iff_subsingleton.1 fun h ↦ h₀ h (hT 0)
    -- In positive degrees reduced and ordinary homology agree.
    exact hn (isTorsion'_homotopyGroup_of_isTorsion'_singularHomology_doubleLoopSpace S x
      (fun i ↦ ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) i).app
        (TopCat.of (Ω (Ω X x) (Path.refl x)))).toLinearEquiv.toAddEquiv.isTorsion'_iff.1
        (hT (i + 1))) n)

/-- **The reduced homology of the double loop space is not torsion.** If `π₂(X, x)` is
nontrivial, or if some homotopy group `πₙ₊₃(X, x)` has an element of infinite order, then the
reduced integral homology of the double loop space `Ω²X` is not a torsion group in some
degree. -/
theorem exists_not_isAddTorsion_reducedSingularHomology_doubleLoopSpace
    (h : Nontrivial (π_ 2 X x) ∨ ∃ n, ∃ g : π_ (n + 3) X x, ¬ IsOfFinOrder g) :
    ∃ i, ¬ IsAddTorsion ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) i).obj
      (TopCat.of (Ω (Ω X x) (Path.refl x)))) := by
  simp_rw [isAddTorsion_iff_isTorsion_int]
  refine exists_not_isTorsion'_reducedSingularHomology_doubleLoopSpace (nonZeroDivisors ℤ) x
    zero_notMem_nonZeroDivisors (h.imp_right fun ⟨n, g, hg⟩ ↦ ⟨n, fun hT ↦ hg ?_⟩)
  exact isOfFinAddOrder_ofMul_iff.1
    (isAddTorsion_iff_isTorsion_int.2 hT (Additive.ofMul g))

end TauCeti
