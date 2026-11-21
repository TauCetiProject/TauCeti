/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence
public import TauCeti.AlgebraicTopology.Singular.Fibration.TopCell

/-!
# Classes living over the fundamental class and the top column of the Serre spectral sequence

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex whose `n`-skeleton is all
of `B` and which has a single `n`-cell, with centre `b`, as for a closed `n`-manifold with a CW
structure having one top cell. Filtering `E` by the preimages `E_q = p⁻¹(Xᵠ)` of the skeleta gives
the Serre spectral sequence of `p`, whose abutment `Hₖ(E; R)` is filtered by the images
`F_q Hₖ(E) = im(Hₖ(E_q) → Hₖ(E))`. Since `E_n = E`, the top piece `F_n Hₖ(E)` is all of `Hₖ(E)`, so
`Hₖ(E)` projects onto the graded piece `F_n Hₖ(E) / F_{n-1} Hₖ(E)`, which is the object
`E^∞_{n,k-n}` of the column `n` of the limit page
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`). This projection is
`TauCeti.TopCat.toSerreTopColumnEInfty`, the case of the skeletal filtration of the projection
`TauCeti.toFilteredSpaceTopColumnEInfty` defined for any filtered space.

The main result is that a class `α ∈ Hₖ(E; R)` lives over the fundamental class at `b`
(`TauCeti.LivesOverFundamentalClass`) exactly when its image in `E^∞_{n,k-n}` is nonzero
(`TauCeti.TopCat.livesOverFundamentalClass_iff_toSerreTopColumnEInfty_ne_zero`). This is the
spectral-sequence reading of Proposition 2.6 of Barraud–Damian–Humilière–Oancea: a class lives over
the fundamental class of the base exactly when it is detected on the top column `E^∞_{n,*}`. Over
an absolute CW complex the spectral sequence converges strongly, and every late enough page of
`TauCeti.TopCat.serreSpectralSequence` is the same graded piece
(`TauCeti.TopCat.serreSpectralSequencePageXIsoGraded`).

The proof combines two facts. The filtration of the abutment is the image filtration
(`TauCeti.range_filteredSpaceAbutmentFiltrationι_comp_chainFiltrationAbutmentIso_hom`), so the
kernel of the projection is the image of `Hₖ(p⁻¹(Xⁿ⁻¹)) → Hₖ(E)`
(`TauCeti.toFilteredSpaceTopColumnEInfty_eq_zero_iff`); and a class lives over the
fundamental class exactly when it does not come from the part of `E` over the `(n - 1)`-skeleton
(`TauCeti.TopCat.livesOverFundamentalClass_iff_notMem_range`).

The spectral sequences are indexed as in `TauCeti.filteredSpaceSpectralSequence`: the classical
position `(n, k - n)` is `(a, b) = (1 - k - n, n - 1)`, so `E^∞_{n,k-n}` is the limit object at
`b = n - 1` in degree `a + b = -k`.

## Main definitions

* `TauCeti.TopCat.toSerreTopColumnEInfty`: the projection `Hₖ(E; R) ⟶ E^∞_{n,k-n}` onto the top
  column.

## Main results

* `TauCeti.TopCat.livesOverFundamentalClass_iff_toSerreTopColumnEInfty_ne_zero`: a class lives
  over the fundamental class at the centre of the top cell exactly when its image on the top
  column of the limit page is nonzero.
* `TauCeti.TopCat.toSerreTopColumnEInfty_eq_zero_iff`: the kernel of the projection is the image
  of the homology of the part of `E` over the `(n - 1)`-skeleton.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Proposition 2.6.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  (R : Type u) [Ring R] {n : ℕ}

variable (hC : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) = univ)
include hC

/-- Over a complex whose `n`-skeleton is all of `B`, the stage `n` of the skeletal filtration is
all of `E`. -/
private lemma preimageSkeleton_natCast_sub_one_add_one :
    preimageSkeleton C p ((n : ℤ) - 1 + 1) = univ := by
  rw [preimageSkeleton_def, show ((n : ℤ) - 1 + 1 + 1).toNat = n + 1 by lia, hC, preimage_univ]

variable (p) in
/-- **The projection onto the top column of the Serre spectral sequence.** Let `C ⊆ B` be a
relative CW complex whose `n`-skeleton is all of `B`. The homology `Hₖ(E; R)` is the top piece
`F_n Hₖ(E)` of the filtration of the abutment of the Serre spectral sequence of `p : E ⟶ B`, and
this is its projection onto the graded piece `F_n Hₖ(E) / F_{n-1} Hₖ(E)`, the object
`E^∞_{n,k-n}` of the limit page at the classical position `(n, k - n)`. It is the projection
`TauCeti.toFilteredSpaceTopColumnEInfty` of the skeletal filtration. -/
def toSerreTopColumnEInfty (k : ℕ) :
    ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R) ⟶
      (serreSpectralObject C p R).EInfty ((n : ℤ) - 1) (-k) :=
  toFilteredSpaceTopColumnEInfty (ModuleCat.of R R) (monotone_preimageSkeleton p)
    (preimageSkeleton_natCast_sub_one_add_one hC) k

/-- **The defining property of the projection onto the top column.** On the top piece
`F_n Hₖ(E)` of the filtration of the abutment, identified with `Hₖ(E; R)`, the projection is the
quotient map onto the cokernel of `F_{n-1} Hₖ(E) ⟶ F_n Hₖ(E)`, identified with `E^∞_{n,k-n}`. -/
@[reassoc]
theorem abutmentFiltrationι_comp_chainFiltrationAbutmentIso_hom_comp_toSerreTopColumnEInfty
    (k : ℕ) :
    (serreSpectralObject C p R).abutmentFiltrationι ((n : ℤ) - 1 + 1) (-k) ≫
        (chainFiltrationAbutmentIso (singularChains R) (monotone_preimageSkeleton _) k).hom ≫
          toSerreTopColumnEInfty p R hC k =
      cokernel.π ((serreSpectralObject C p R).abutmentFiltrationMap ((n : ℤ) - 1) (-k)) ≫
        ((serreSpectralObject C p R).EInftyIsoCokernel ((n : ℤ) - 1) (-k)).inv :=
  abutmentFiltrationι_comp_chainFiltrationAbutmentIso_hom_comp_chainFiltrationToTopColumnEInfty _ _
    (preimageSkeleton_natCast_sub_one_add_one hC) k

instance (k : ℕ) : Epi (toSerreTopColumnEInfty p R hC k) := by
  rw [toSerreTopColumnEInfty]
  infer_instance

/-- The projection onto the top column vanishes on a class `α ∈ Hₖ(E; R)` exactly when `α` comes
from the homology of the part of `E` over the `(n - 1)`-skeleton. -/
theorem toSerreTopColumnEInfty_eq_zero_iff {k : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R)) :
    (toSerreTopColumnEInfty p R hC k).hom α = 0 ↔
      α ∈ LinearMap.range (SSet.homologyMap (_root_.TopCat.toSSet.map
        (TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).map)
          (ModuleCat.of R R) k).hom := by
  have h := toFilteredSpaceTopColumnEInfty_eq_zero_iff (ModuleCat.of R R)
    (monotone_preimageSkeleton (C := C) p) (preimageSkeleton_natCast_sub_one_add_one hC) α
  rw [preimageSkeleton_natCast_sub_one] at h
  exact h

/-- **Classes living over the fundamental class are detected on the top column** of the Serre
spectral sequence: the spectral-sequence form of Proposition 2.6 of
Barraud–Damian–Humilière–Oancea. Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW
complex whose `n`-skeleton is all of `B` and which has a single `n`-cell, with centre `b`. A class
`α ∈ Hₖ(E; R)` lives over the fundamental class at `b` exactly when its image in the object
`E^∞_{n,k-n}` of the top column of the limit page is nonzero. -/
theorem livesOverFundamentalClass_iff_toSerreTopColumnEInfty_ne_zero (hp : serreFibrations p)
    [Unique (cell C n)] {k : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p (map n (default : cell C n) 0) α ↔
      (toSerreTopColumnEInfty p R hC k).hom α ≠ 0 := by
  rw [livesOverFundamentalClass_iff_notMem_range hp R hC α, Ne,
    toSerreTopColumnEInfty_eq_zero_iff R hC α]

end TopCat

end TauCeti
