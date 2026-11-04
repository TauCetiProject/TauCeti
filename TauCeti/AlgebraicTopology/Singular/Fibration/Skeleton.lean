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
`(Xⁱ⁺¹, Xⁱ)` is `i`-connected (Hatcher, Corollary 4.12), and the restriction of `p` over `Xⁱ⁺¹`
is again a Serre fibration. Hence the preimages `Eᵢ = p⁻¹(Xⁱ)` satisfy

* `Hₘ(Eᵢ₊₁, Eᵢ; R) = 0` for every `m ≤ i`
  (`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT`).

This is the vanishing that places the first page `Hₚ₊q(Eₚ, Eₚ₋₁)` of the spectral sequence of
the filtration `(Eᵢ)` in nonnegative fibre degrees `q ≥ 0`, so that the spectral sequence is a
first-quadrant one: the Serre spectral sequence of `p` over the CW complex `C`. No finiteness,
dimension, or connectivity assumption is made on `C`, on `E`, or on the fibres of `p`.

## Main results

* `TauCeti.TopCat.isZero_singularHomology_preimage_of_relHomotopyGroup`: the homology of a
  preimage pair vanishes below the connectivity of the pair in the base.
* `TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT`: the homology of consecutive stages
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

variable [T2Space B] {C D : Set B} [RelCWComplex C D]

/-- **The skeletal filtration of a Serre fibration has vanishing low-degree homology.** Let
`p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta
`Xⁱ = skeletonLT C (i + 1)`. Then `Hₘ(p⁻¹(Xⁱ⁺¹), p⁻¹(Xⁱ); R) = 0` for every `m ≤ i`. -/
theorem isZero_singularHomology_preimage_skeletonLT (hp : serreFibrations p) (R : Type u)
    [Ring R] {i m : ℕ} (hm : m ≤ i) :
    IsZero ((TopPair.ofInclusion (X := E) (preimage_mono (f := p) (skeletonLT_mono (C := C)
      (add_le_add_right (by norm_num) _ : (i + 1 : ℕ∞) ≤ i + 2)))).singularHomology
        (ModuleCat.of R R) m) := by
  have hi : (i + 1 : ℕ∞) ≤ i + 2 := add_le_add_right (by norm_num) _
  set t : Set B := (skeletonLT C (i + 2) : Set B)
  set s : Set B := (skeletonLT C (i + 1) : Set B)
  have hst : s ⊆ t := skeletonLT_mono hi
  -- The `i`-skeleton of the subcomplex `t` is `s`.
  have hts : (skeletonLT t (i + 1) : Set B) = s := coe_skeletonLT_skeletonLT hi
  -- The pair `(t, s)`, read as the pair of `t` and the preimage of `s` in `t`, is `i`-connected.
  let A : Set (_root_.TopCat.of t) := Subtype.val ⁻¹' s
  have h₀ (b : _root_.TopCat.of t) : ∃ a ∈ A, Joined b a := by
    obtain ⟨a, ha⟩ := exists_joined_skeletonLT hts hst b
    exact ⟨inclusion hst a, a.2, ha.symm⟩
  have h (k : ℕ) (hk : k + 1 < i + 1) (a : A) :
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩) := by
    have := subsingleton_relHomotopyGroup_skeletonLT (N := Fin k) (by simpa using hk) hts hst
      ⟨a.1.1, a.2⟩
    -- The pairs `(t, A)` and `(t, s)` have the same ambient space and the same subspace.
    let f : (⟨TopPair.ofSubset A, a⟩ : BasedTopPair) ⟶ ⟨TopPair.ofInclusion hst, ⟨a.1.1, a.2⟩⟩ :=
      ⟨TopPair.ofHom (𝟙 _) (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩, by fun_prop⟩), rfl⟩
    let g : (⟨TopPair.ofInclusion hst, ⟨a.1.1, a.2⟩⟩ : BasedTopPair) ⟶ ⟨TopPair.ofSubset A, a⟩ :=
      ⟨TopPair.ofHom (𝟙 _) (_root_.TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, hst x.2⟩, x.2⟩, by fun_prop⟩),
        rfl⟩
    have hfg : f ≫ g = 𝟙 _ := rfl
    refine Function.LeftInverse.injective (g := RelHomotopyGroup.map g)
      (f := RelHomotopyGroup.map f) (fun x ↦ ?_) |>.subsingleton
    rw [RelHomotopyGroup.map_map, hfg, RelHomotopyGroup.map_id, id]
  -- The restriction of `p` over `t` is a Serre fibration, so its preimage pair has vanishing
  -- homology below degree `i + 1`.
  have hz := isZero_singularHomology_preimage_of_relHomotopyGroup
    (mem_serreFibrations_restrictPreimage hp t) h₀ h R (Nat.lt_succ_of_le hm)
  -- That preimage pair is the pair `(p⁻¹(t), p⁻¹(s))`, up to the identification of the preimage
  -- of `A` in `p⁻¹(t)` with `p⁻¹(s)`.
  let φ : TopPair.ofSubset ((_root_.TopCat.ofHom (p.hom.restrictPreimage t)) ⁻¹' A) ⟶
      TopPair.ofInclusion (X := E) (preimage_mono (f := p) hst) :=
    TopPair.ofHom (𝟙 _) (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩, by fun_prop⟩)
  have : IsIso (TopPair.Hom.fst φ) := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso φ := TopPair.isIso_of_isIso_fst_of_surjective_snd _
    fun x ↦ ⟨⟨⟨x.1, hst x.2⟩, x.2⟩, rfl⟩
  exact hz.of_iso (asIso (TopPair.singularHomologyMap φ (ModuleCat.of R R) m)).symm

end TopCat

end TauCeti
