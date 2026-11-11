/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence

/-!
# The first page of the Serre spectral sequence over a CW complex

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex. The first page of the
Serre spectral sequence `TauCeti.TopCat.serreSpectralSequence C p R` of `p` over `C` is the direct
sum, over the cells of `C`, of the homology of the fibres over their centres:

`E¹_{d,t} ≅ ⨁ⱼ H_t(p⁻¹(χⱼ(0)); R)`,

the sum running over the `d`-cells `j` of `C`, with characteristic maps `χⱼ`
(`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`). No finiteness or dimension assumption
is made on `C` or on the fibres.

In the cohomological indexing of `CochainComplex.spectralSequence` the first page is numbered `2`,
and the object at `(a, b)` is the relative homology `Hₙ(E_{b+1}, E_b; R)`, with `a + b = -n`, of
consecutive stages `E_i = p⁻¹(C^(i))` of the skeletal filtration
(`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso`). So the classical bidegree `(d, t)` is
`d = b + 1` and `t = n - d`. The pair `(E_d, E_{d-1})` is
`TauCeti.TopCat.preimageSkeletonPair p C d`, whose homology is the sum over the `d`-cells
(`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`).

## Main definitions

* `TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`: the first page of the Serre spectral
  sequence as a sum over the cells of the homology of the fibres.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  (hp : serreFibrations p) (R : Type u) [Ring R]

/-- The pair `(E_d, E_{d-1})` of consecutive stages of the skeletal filtration, as it appears on the
first page of `TauCeti.TopCat.serreSpectralSequence`, is `TauCeti.TopCat.preimageSkeletonPair`. -/
lemma ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (d : ℕ)
    (h : preimageSkeleton C p ((d : ℤ) - 1) ⊆ preimageSkeleton C p d) :
    TopPair.ofInclusion h = preimageSkeletonPair p C d := by
  have h₁ : preimageSkeleton C p ((d : ℤ) - 1) = p ⁻¹' skeletonLT C (d : ℕ∞) := by
    rw [preimageSkeleton_def, sub_add_cancel, Int.toNat_natCast]
  have h₂ : preimageSkeleton C p d = p ⁻¹' skeletonLT C ((d : ℕ∞) + 1) := by
    rw [preimageSkeleton_def, ← Nat.cast_add_one (R := ℤ), Int.toNat_natCast, Nat.cast_add_one]
  revert h
  rw [h₁, h₂]
  intro h
  rfl

include hp in
variable (C) in
/-- **The first page of the Serre spectral sequence over a relative CW complex.** For a Serre
fibration `p : E ⟶ B` and a relative CW complex `C ⊆ B`, the object of the first page (numbered `2`)
of `TauCeti.TopCat.serreSpectralSequence C p R` at `pq = (a, b)` is
`⨁ⱼ H_t(p⁻¹(χⱼ(0)); R)`, the sum running over the `d`-cells `j` of `C` and `χⱼ(0)` being the centre
of the cell `j`, where `d = b + 1` and `a + b = -(t + d)`. In the classical homological indexing
this is `E¹_{d,t} ≅ ⨁ⱼ H_t(Fⱼ; R)`. On the summand of `j` the inverse is induced by the pullback of
`p` along the characteristic map of `j`
(`TauCeti.TopCat.ι_serreSpectralSequenceFirstPageXIsoSigma_inv`). -/
def serreSpectralSequenceFirstPageXIsoSigma (pq : ℤ × ℤ) (d t : ℕ) (hd : pq.2 + 1 = d)
    (ht : pq.1 + pq.2 = -((t + d : ℕ) : ℤ)) :
    ((serreSpectralSequence C p R).page 2).X pq ≅
      ∐ fun j : cell C d ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) t).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map d j 0} : Set E)) :=
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) (monotone_preimageSkeleton p) pq
      ((d : ℤ) - 1) d (by lia) (by lia) (pq.1 + pq.2) rfl (t + d) ht ≪≫
    eqToIso (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) (t + d))
      (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair d _)) ≪≫
    preimageSkeletonPairSingularHomologyIsoSigma C hp R d t

@[reassoc (attr := simp)]
lemma ι_serreSpectralSequenceFirstPageXIsoSigma_inv (pq : ℤ × ℤ) (d t : ℕ) (hd : pq.2 + 1 = d)
    (ht : pq.1 + pq.2 = -((t + d : ℕ) : ℤ)) (j : cell C d) :
    Sigma.ι _ j ≫ (serreSpectralSequenceFirstPageXIsoSigma C hp R pq d t hd ht).inv =
      (cellDiskPullbackPairSingularHomologyIso hp R d t j).inv ≫
        (cellDiskPullbackPair p C d j).singularHomologyMap (cellDiskPullbackPairMap p C d j)
          (ModuleCat.of R R) (t + d) ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) (t + d))
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair d
            (monotone_preimageSkeleton p (by lia)))).symm ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
          (monotone_preimageSkeleton p) pq ((d : ℤ) - 1) d (by lia) (by lia) (pq.1 + pq.2) rfl
          (t + d) ht).inv := by
  simp [serreSpectralSequenceFirstPageXIsoSigma]

end TopCat

end TauCeti
