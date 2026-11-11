/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.SerreFibration
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Skeleton
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Relative
public import TauCeti.Topology.CWComplex.Classical.Subcomplex

/-!
# Homology of the skeletal filtration of a Serre fibration

Let `p : E → B` be a Serre fibration. A Serre fibration pulls `n`-connected pairs back to
`n`-connected pairs
(`TauCeti.TopCat.subsingleton_relHomotopyGroup_preimage_of_mem_serreFibrations`), and relative
singular homology vanishes below the connectivity of a pair
(`TauCeti.isZero_singularHomology_ofSubset_of_relHomotopyGroup`). Together:

* if `(B, A)` is `(n - 1)`-connected, then `Hₘ(E, p⁻¹(A); R) = 0` for every `m < n`
  (`TauCeti.TopCat.isZero_singularHomology_preimage_of_relHomotopyGroup`).

Over a relative CW complex `C ⊆ B` with skeleta `Xⁱ = skeletonLT C (i + 1)`, the pair
`(skeletonLT C k, Xⁱ)` is `i`-connected for every `k ≥ i + 1` (Hatcher, Corollary 4.12), and the
restriction of `p` over `skeletonLT C k` is again a Serre fibration. Hence the preimages
`Eᵢ = p⁻¹(Xⁱ)` satisfy

* `Hₘ(p⁻¹(skeletonLT C k), Eᵢ; R) = 0` for every `m ≤ i` and every `k ≥ i + 1`
  (`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT`). The case `k = i + 2` is
  `Hₘ(Eᵢ₊₁, Eᵢ; R) = 0`, and the case `k = ⊤` is `Hₘ(p⁻¹(C), Eᵢ; R) = 0`.

The filtration starts at `E₋₁ = p⁻¹(skeletonLT C 0) = p⁻¹(D)`. This is the vanishing that places
the first page `Hₚ₊q(Eₚ, Eₚ₋₁)` of the spectral sequence of the relative skeletal filtration
`E₋₁ ⊆ E₀ ⊆ E₁ ⊆ ⋯` in nonnegative fibre degrees `q ≥ 0`, so that the spectral sequence is a
first-quadrant one. For an absolute CW complex (`D = ∅`, so `E₋₁` is empty) it is the Serre
spectral sequence of `p` over `C`; for general `D` the initial stage `p⁻¹(D)` can have arbitrary
topology. No finiteness, dimension, or connectivity assumption is made on `C`, on `E`, or on the
fibres of `p`.

## Main results

* `TauCeti.TopCat.isZero_singularHomology_preimage_of_relHomotopyGroup`: the homology of a
  preimage pair vanishes below the connectivity of the pair in the base.
* `TauCeti.TopCat.isZero_singularHomology_preimage_of_homotopyRel`: if `S ⊆ B` deforms into
  `A ⊆ S` relative to `A`, then `(p⁻¹(S), p⁻¹(A))` has vanishing relative homology.
* `TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT`: the homology of a pair of stages
  of the skeletal filtration of a Serre fibration vanishes in degrees at most the lower stage.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.12, and Section 4.2, Theorem 4.41.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Section 5.1.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B}

/-- **Homology of a preimage pair vanishes below the connectivity of the base pair.** Let
`p : E ⟶ B` be a Serre fibration and `A ⊆ B`. If every point of `B` is joined by a path to a
point of `A`, and the relative homotopy set `π_{k+1}(B, A, a)` is trivial for every `k + 1 < n`
and every `a ∈ A`, then `Hₘ(E, p⁻¹(A); R) = 0` for every `m < n`. -/
theorem isZero_singularHomology_preimage_of_relHomotopyGroup (hp : serreFibrations p)
    {A : Set B} {n : ℕ} (h₀ : ∀ b : B, ∃ a ∈ A, Joined b a)
    (h : ∀ k : ℕ, k + 1 < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩))
    (R : Type u) [Ring R] {m : ℕ} (hm : m < n) :
    IsZero ((TopPair.ofSubset (p ⁻¹' A)).singularHomology (ModuleCat.of R R) m) :=
  isZero_singularHomology_ofSubset_of_relHomotopyGroup
    (exists_joined_preimage_of_mem_serreFibrations hp h₀)
    (fun k hk e ↦ subsingleton_relHomotopyGroup_preimage_of_mem_serreFibrations hp e
      (h k hk ⟨p e, e.2⟩)) R hm

/-- **A Serre fibration over a deformation has acyclic preimage pair.** Let `p : E ⟶ B` be a Serre
fibration and `A ⊆ S ⊆ B`. If the identity of `S` is homotopic, relative to `A`, to a map with
values in `A`, then `Hₘ(p⁻¹(S), p⁻¹(A); R) = 0` in every degree `m`. -/
theorem isZero_singularHomology_preimage_of_homotopyRel (hp : serreFibrations p) {A S : Set B}
    (hAS : A ⊆ S) {g : C(S, S)} (H : (ContinuousMap.id S).HomotopyRel g (Subtype.val ⁻¹' A))
    (hg : ∀ x, (g x : B) ∈ A) (R : Type u) [Ring R] (m : ℕ) :
    IsZero ((TopPair.ofInclusion (X := E) (preimage_mono (f := p) hAS)).singularHomology
      (ModuleCat.of R R) m) := by
  let A' : Set (_root_.TopCat.of S) := Subtype.val ⁻¹' A
  have h₀ (b : _root_.TopCat.of S) : ∃ a ∈ A', Joined b a :=
    ⟨g b, hg b, ⟨{ toFun t := H (t, b), source' := by simp, target' := by simp }⟩⟩
  have h (k : ℕ) (_ : k + 1 < m + 1) (a : A') :
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A', a⟩) := by
    refine RelHomotopyGroup.subsingleton_of_homotopyRel (g := g) ?_ fun x ↦ ?_
    · rw [TopPair.range_ofSubset_map]
      exact H
    · rw [TopPair.range_ofSubset_map]
      exact hg x
  have hz := isZero_singularHomology_preimage_of_relHomotopyGroup
    (mem_serreFibrations_restrictPreimage hp S) h₀ h R (Nat.lt_succ_self m)
  -- The preimage pair of the restriction of `p` over `S` is the pair `(p⁻¹(S), p⁻¹(A))`.
  exact hz.of_iso (asIso (TopPair.singularHomologyMap
    (TopPair.ofSubsetPreimageValIso (X := E) (preimage_mono (f := p) hAS)).hom
    (ModuleCat.of R R) m)).symm

variable [T2Space B] {C D : Set B} [RelCWComplex C D]

/-- **The skeletal filtration of a Serre fibration has vanishing low-degree homology.** Let
`p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta
`Xⁱ = skeletonLT C (i + 1)`. Then `Hₘ(p⁻¹(skeletonLT C k), p⁻¹(Xⁱ); R) = 0` for every `m ≤ i` and
every `k ≥ i + 1`; for `k = ⊤` the upper stage is `p⁻¹(C)`. -/
theorem isZero_singularHomology_preimage_skeletonLT (hp : serreFibrations p) (R : Type u)
    [Ring R] {i m : ℕ} {k : ℕ∞} (hk : (i + 1 : ℕ∞) ≤ k) (hm : m ≤ i) :
    IsZero ((TopPair.ofInclusion (X := E) (preimage_mono (f := p) (skeletonLT_mono (C := C)
      hk))).singularHomology (ModuleCat.of R R) m) := by
  set t : Set B := (skeletonLT C k : Set B)
  set s : Set B := (skeletonLT C (i + 1) : Set B)
  have hst : s ⊆ t := skeletonLT_mono hk
  -- The `i`-skeleton of the subcomplex `t` is `s`.
  have hts : (skeletonLT t (i + 1) : Set B) = s := coe_skeletonLT_skeletonLT hk
  -- The pair `(t, s)`, read as the pair of `t` and the preimage of `s` in `t`, is `i`-connected.
  let A : Set (_root_.TopCat.of t) := Subtype.val ⁻¹' s
  have h₀ (b : _root_.TopCat.of t) : ∃ a ∈ A, Joined b a := by
    obtain ⟨a, ha⟩ := exists_joined_skeletonLT hts hst b
    exact ⟨inclusion hst a, a.2, ha.symm⟩
  have h (j : ℕ) (hj : j + 1 < i + 1) (a : A) :
      Subsingleton (RelHomotopyGroup (Fin j) ⟨TopPair.ofSubset A, a⟩) := by
    have := subsingleton_relHomotopyGroup_skeletonLT (N := Fin j) (by simpa using hj) hts hst
      ⟨a.1.1, a.2⟩
    -- The pairs `(t, A)` and `(t, s)` are isomorphic, by a basepoint-preserving isomorphism.
    let e := TopPair.ofSubsetPreimageValIso hst
    let f : (⟨TopPair.ofSubset A, a⟩ : BasedTopPair) ⟶ ⟨TopPair.ofInclusion hst, ⟨a.1.1, a.2⟩⟩ :=
      ⟨e.hom, Subtype.ext (TopPair.ofSubsetPreimageValIso_hom_snd_apply a)⟩
    let g : (⟨TopPair.ofInclusion hst, ⟨a.1.1, a.2⟩⟩ : BasedTopPair) ⟶ ⟨TopPair.ofSubset A, a⟩ :=
      ⟨e.inv, Subtype.ext (TopPair.ofSubsetPreimageValIso_inv_snd_apply ⟨a.1.1, a.2⟩)⟩
    exact RelHomotopyGroup.subsingleton_of_comp_eq_id (f := f) (g := g)
      (BasedTopPair.hom_ext e.hom_inv_id)
  -- The restriction of `p` over `t` is a Serre fibration, so its preimage pair has vanishing
  -- homology below degree `i + 1`.
  have hz := isZero_singularHomology_preimage_of_relHomotopyGroup
    (mem_serreFibrations_restrictPreimage hp t) h₀ h R (Nat.lt_succ_of_le hm)
  -- That preimage pair is the pair `(p⁻¹(t), p⁻¹(s))`, up to the identification of the preimage
  -- of `A` in `p⁻¹(t)` with `p⁻¹(s)`.
  exact hz.of_iso (asIso (TopPair.singularHomologyMap
    (TopPair.ofSubsetPreimageValIso (X := E) (preimage_mono (f := p) hst)).hom
    (ModuleCat.of R R) m)).symm

end TopCat

end TauCeti
