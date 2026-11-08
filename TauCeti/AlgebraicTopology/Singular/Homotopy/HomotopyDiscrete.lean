/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.HomotopyGroup.TotallyDisconnected

/-!
# Homology of spaces with weakly contractible path components

Let `X` be a space all of whose positive-dimensional homotopy groups vanish, at every base point:
each path component of `X` is weakly contractible. Choosing a point in each path component gives a
map to `X` from the set of path components with the discrete topology, which is a weak homotopy
equivalence (`ContinuousMap.isWeakHomotopyEquivalence_of_totallyDisconnectedSpace`). The homology
of a discrete space vanishes in positive degrees, so the same holds for `X`, with coefficients in
any ring, for normalized cubical
(`TauCeti.isZero_homology_normalizedCubicalChainComplex_of_forall_subsingleton_homotopyGroup`) and
for singular homology
(`TauCeti.isZero_singularHomologyFunctor_of_forall_subsingleton_homotopyGroup`). On chains: every
cubical cycle of positive dimension of `X` is a boundary
(`TauCeti.NormalizedCubicalChain.exists_boundary_eq_of_forall_subsingleton_homotopyGroup`).

The basic example is the loop space of an aspherical space, whose path components are the
elements of the fundamental group.

## Main results

* `TauCeti.NormalizedCubicalChain.exists_boundary_eq_of_isZero_homology`: if the normalized
  cubical homology vanishes in dimension `n + 1`, every `(n + 1)`-cycle is a boundary.
* `TauCeti.isZero_homology_normalizedCubicalChainComplex_of_forall_subsingleton_homotopyGroup`,
  `TauCeti.isZero_singularHomologyFunctor_of_forall_subsingleton_homotopyGroup`: the positive-degree
  homology of a space with weakly contractible path components vanishes.
* `TauCeti.NormalizedCubicalChain.exists_boundary_eq_of_forall_subsingleton_homotopyGroup`: its
  cubical cycles of positive dimension are boundaries.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 4.21.
-/

public section

open AlgebraicTopology CategoryTheory Limits
open scoped Topology

universe u

namespace TauCeti

namespace NormalizedCubicalChain

variable {R : Type u} [Ring R]

/-- If the normalized cubical homology of `X` vanishes in dimension `n + 1`, every normalized
cubical `(n + 1)`-cycle of `X` is a boundary. -/
theorem exists_boundary_eq_of_isZero_homology {X : TopCat.{u}} {n : ℕ}
    (h : IsZero (((normalizedCubicalChainComplex R).obj X).homology (n + 1)))
    {c : NormalizedCubicalChain X R (n + 1)} (hc : NormalizedCubicalChain.boundary X R n c = 0) :
    ∃ c' : NormalizedCubicalChain X R (n + 2),
      NormalizedCubicalChain.boundary X R (n + 1) c' = c := by
  have hex := (((normalizedCubicalChainComplex R).obj X).exactAt_iff_isZero_homology (n + 1)).2 h
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨c', hc'⟩ := hex c ((normalizedCubicalChainComplex_obj_d_apply X n c).trans hc)
  exact ⟨c', (normalizedCubicalChainComplex_obj_d_apply X (n + 1) c').symm.trans hc'⟩

end NormalizedCubicalChain

variable {X : Type u} [TopologicalSpace X] (R : Type u) [Ring R]

/-- **A space with weakly contractible path components has no normalized cubical homology in
positive degrees.** If every positive-dimensional homotopy group of `X` vanishes, at every base
point, then `Hₘ(X; R) = 0` for `m ≠ 0`. The choice of a point in each path component is a weak
homotopy equivalence from the discrete space of path components. -/
theorem isZero_homology_normalizedCubicalChainComplex_of_forall_subsingleton_homotopyGroup
    (hX : ∀ (n : ℕ) (x : X), Subsingleton (π_ (n + 1) X x)) {m : ℕ} (hm : m ≠ 0) :
    IsZero (((normalizedCubicalChainComplex R).obj (TopCat.of X)).homology m) := by
  -- The path components of `X`, with the discrete topology, and a point in each of them.
  let D : TopCat.{u} := TopCat.discrete.obj (ZerothHomotopy X)
  let s : C(D, X) := ⟨fun q ↦ Quotient.out (s := pathSetoid X) q, continuous_of_discreteTopology⟩
  have hs : s.IsWeakHomotopyEquivalence :=
    s.isWeakHomotopyEquivalence_of_totallyDisconnectedSpace
      (fun y ↦ ⟨ZerothHomotopy.mk y, Quotient.exact (Quotient.out_eq (ZerothHomotopy.mk y))⟩)
      (fun a b h ↦ (Quotient.out_eq (s := pathSetoid X) a).symm.trans
        ((Quotient.sound h).trans (Quotient.out_eq b)))
      (fun n _ ↦ hX n _)
  have := hs.quasiIso_normalizedCubicalChainComplex_map R
  have hD : IsZero (((normalizedCubicalChainComplex R).obj D).homology m) :=
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{u} R)
      m (ModuleCat.of R R) D hm).of_iso (singularCubicalHomologyIso R D m).symm
  exact hD.of_iso (asIso (HomologicalComplex.homologyMap
    ((normalizedCubicalChainComplex R).map (TopCat.ofHom s)) m)).symm

/-- **A space with weakly contractible path components has no singular homology in positive
degrees.** If every positive-dimensional homotopy group of `X` vanishes, at every base point, then
`Hₘ(X; R) = 0` for `m ≠ 0`. -/
theorem isZero_singularHomologyFunctor_of_forall_subsingleton_homotopyGroup
    (hX : ∀ (n : ℕ) (x : X), Subsingleton (π_ (n + 1) X x)) {m : ℕ} (hm : m ≠ 0) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).obj
      (TopCat.of X)) :=
  (isZero_homology_normalizedCubicalChainComplex_of_forall_subsingleton_homotopyGroup R hX
    hm).of_iso (singularCubicalHomologyIso R (TopCat.of X) m)

variable {R} in
/-- **Cycles of a space with weakly contractible path components are boundaries.** If every
positive-dimensional homotopy group of `X` vanishes, at every base point, then every normalized
cubical cycle of `X` of positive dimension is a boundary. -/
theorem NormalizedCubicalChain.exists_boundary_eq_of_forall_subsingleton_homotopyGroup
    (hX : ∀ (n : ℕ) (x : X), Subsingleton (π_ (n + 1) X x)) {n : ℕ}
    {c : NormalizedCubicalChain (TopCat.of X) R (n + 1)}
    (hc : NormalizedCubicalChain.boundary (TopCat.of X) R n c = 0) :
    ∃ c' : NormalizedCubicalChain (TopCat.of X) R (n + 2),
      NormalizedCubicalChain.boundary (TopCat.of X) R (n + 1) c' = c :=
  exists_boundary_eq_of_isZero_homology
    (isZero_homology_normalizedCubicalChainComplex_of_forall_subsingleton_homotopyGroup R hX
      n.succ_ne_zero) hc

end TauCeti
