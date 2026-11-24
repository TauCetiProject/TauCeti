/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.ModuloTorsion
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ReducedHomology
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Acyclic
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Detection of non-torsion higher homotopy groups in loop space homology

For any submonoid `S : Submonoid ℤ`, this file applies Serre's Hurewicz theorem modulo `S`-torsion
(`TauCeti.forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology`) and loop-space
acyclicity transfer (`TauCeti.isIso_singularHomologyMap_of_isIso_loopSpace`) to detect
non-`S`-torsion higher homotopy groups in the reduced integral homology of single and double loop
spaces (fixed-interval `Ω²Q` and Moore `ΩᴹΩᴹQ`), without any connectedness hypothesis on `Q`. This
provides the homological content of the second part of Proposition 5.11 of
Barraud--Damian--Humilière--Oancea; the identification of `H~_*(Ω²Q)` with `ker i_{Q*}` is in
`TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ConstantLoopKernel`, the normalized cubical
comparison is in `TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Torsion.Cubical`, and the
vanishing/contrapositive forms are in
`TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Torsion.Vanishing`.

## Proof outline

* For a single loop space `Ω X x`, split on whether `π₁(X, x)` is trivial. If nontrivial,
  `H~₀(Ω X x; ℤ)` contains a copy of `ℤ`, forcing `0 ∈ S` if it is `S`-torsion. If trivial,
  restrict to `Y = pathComponent x` (simply connected with `Ω Y ≃ₜ Ω X x` path-connected),
  transfer acyclicity of `Ω Y` over `S⁻¹ℤ` to `Y`, and apply Hurewicz modulo `S`-torsion.
* For double loop spaces `Ω²Q` (and `ΩᴹΩᴹQ`), `m = 0` (`π₂`) uses degree-0 reduced homology, while
  `m = n + 1` applies the single-loop-space result to `Ω Q q` via `pathLoopSpaceMulEquiv`.

## Main results

* `TauCeti.isTorsion'_homotopyGroup_of_forall_isTorsion'_loopSpaceReducedHomology`,
  `TauCeti.MooreLoopSpace.isTorsion'_homotopyGroup_of_forall_isTorsion'_reducedHomology`:
  `S`-torsion of `H~_k(Ω X x; ℤ)` for `k ≤ m + 2` implies `S`-torsion of `π_{m + 2}(X, x)`.
* `TauCeti.isTorsion'_homotopyGroup_of_forall_isTorsion'_doubleLoopSpaceReducedHomology`,
  `TauCeti.exists_forall_smul_ne_zero_doubleLoopSpaceReducedHomology`,
  `TauCeti.exists_forall_pow_smul_ne_zero_doubleLoopSpaceReducedHomology`,
  `TauCeti.exists_not_isOfFinAddOrder_doubleLoopSpaceReducedHomology`: detection of non-`S`-torsion
  higher homotopy groups in `H~_*(Ω²Q; ℤ)`, with mirrors in `TauCeti.MooreLoopSpace` for
  `ΩᴹΩᴹQ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter III, Theorem 1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomotopyGroup
open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

/-! ### Private helpers -/

section Helpers

/-- Degree-zero torsion transfer for double loop spaces: if `π₂(Q, q)` injects `ℤ` into an
`S`-torsion reduced zeroth homology group `H₀` whenever it is nontrivial, then `π₂(Q, q)` is
`S`-torsion. -/
private lemma isTorsion'_pi2_of_isTorsion'_homology₀ {Q : Type} [TopologicalSpace Q]
    (q : Q) {S : Submonoid ℤ} {H₀ : Type*} [AddCommGroup H₀] [Module ℤ H₀]
    (hH₀ : Module.IsTorsion' H₀ S)
    (hinj : Nontrivial (π_ 2 Q q) → ∃ f : ℤ →ₗ[ℤ] H₀, Function.Injective f) :
    Module.IsTorsion' (Additive (π_ 2 Q q)) S := by
  by_cases h2 : Subsingleton (π_ 2 Q q)
  · exact fun a ↦ ⟨1, by rw [one_smul]; exact Subsingleton.elim a 0⟩
  · obtain ⟨f, hf⟩ := hinj (not_subsingleton_iff_nontrivial.1 h2)
    exact Module.isTorsion'_of_zero_mem
      (f.toAddMonoidHom.zero_mem_of_injective_of_isTorsion' hf hH₀)

/-- If a path-connected space `W` has `S`-torsion reduced integral homology up to degree `N`, then
the map to a point induces an isomorphism on `H_q(-; A)` for all `q ≤ N`, for every localization
`A` of `ℤ` at `S`. -/
private lemma isIso_singularHomologyMap_isTerminalPUnit_of_forall_isTorsion'_reducedHomology
    {W : Type} [TopologicalSpace W] [PathConnectedSpace W] (S : Submonoid ℤ)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] (N : ℕ)
    (hW : ∀ q ≤ N, Module.IsTorsion'
      ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) q).obj (TopCat.of W)) S)
    {q : ℕ} (hq : q ≤ N) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} A) q).obj (ModuleCat.of A A)).map
      (TopCat.isTerminalPUnit.from (TopCat.of W))) := by
  cases q with
  | zero =>
    -- In degree `0`, path-connectedness identifies `H₀(W; A)` with `A ≅ H₀(*; A)`.
    exact IsIso.of_isIso_fac_right (singularHomologyMap_singularHomology₀ε
      (ModuleCat.of A A) (TopCat.isTerminalPUnit.from (TopCat.of W)))
  | succ r =>
    -- In positive degrees, reduced and ordinary homology agree, so flat base change turns
    -- `S`-torsion in `H~_{r + 1}(W; ℤ)` into vanishing of `H_{r + 1}(W; A)`.
    have hsub : Subsingleton (((singularChains A).obj (TopCat.of W)).homology (r + 1)) :=
      (isTorsion'_singularChains_int_homology_iff S A (TopCat.of W) (r + 1)).1 <|
        ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) r).app
          (TopCat.of W)).symm.toLinearEquiv.toAddEquiv.isTorsion'_iff.2 (hW (r + 1) hq)
    exact (isIso_singularHomologyMap_isTerminalPUnit_from_succ_iff
      (ModuleCat.of A A) (TopCat.of W) r).2 hsub

end Helpers

/-! ### Single loop spaces -/

section SingleLoopSpace

variable {X : Type} [TopologicalSpace X]

/-- **Single loop-space torsion detection.** For any pointed space `(X, x)`, submonoid
`S : Submonoid ℤ`, and `m : ℕ`, if the reduced integral singular homology `H~_k(Ω X x; ℤ)` is
`S`-torsion for all `k ≤ m + 2`, then `π_{m + 2}(X, x)` is `S`-torsion. -/
theorem isTorsion'_homotopyGroup_of_forall_isTorsion'_loopSpaceReducedHomology
    (x : X) (S : Submonoid ℤ) (m : ℕ)
    (hH : ∀ k ≤ m + 2, Module.IsTorsion'
      ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj (TopCat.of (Ω X x))) S) :
    Module.IsTorsion' (Additive (π_ (m + 2) X x)) S := by
  have : IsLocalization S (Localization S) := Localization.isLocalization
  by_cases h1 : Subsingleton (π_ 1 X x)
  · -- When `π₁(X, x)` is trivial, restrict to the path component `Y = pathComponent x` (simply
    -- connected, with `Ω Y y₀ ≃ₜ Ω X x`), transfer `S⁻¹ℤ`-acyclicity from `Ω Y y₀` to `Y`, and
    -- apply Serre's Hurewicz theorem modulo `S`-torsion.
    let Y := pathComponent x
    let y₀ : Y := pathComponentSelf x
    have : Subsingleton (π_ 1 Y y₀) :=
      (HomotopyGroup.subtypeValMulEquivOfPathComponentSubset (N := Fin 1)
        subset_rfl rfl).toEquiv.subsingleton_congr.2 h1
    have : PathConnectedSpace (Ω Y y₀) :=
      (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 y₀).2 inferInstance
    let A := Localization S
    have hΩ : ∀ q ≤ m + 2, Module.IsTorsion'
        ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) q).obj (TopCat.of (Ω Y y₀))) S :=
      fun q hq ↦
        ((Path.subtypeValHomeomorph (a := y₀) (b := y₀)
          subset_rfl).toHomotopyEquiv.reducedSingularHomologyIso
          (ModuleCat.of ℤ ℤ) q).toLinearEquiv.toAddEquiv.isTorsion'_iff.2 (hH q hq)
    have hπY : Module.IsTorsion' (Additive (π_ (m + 2) Y y₀)) S :=
      (forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y₀ S A (m + 1)).2
        (fun j hj ↦ (isIso_singularHomologyMap_isTerminalPUnit_from_succ_iff
          (ModuleCat.of A A) (TopCat.of Y) (j + 1)).1
          (isIso_singularHomologyMap_of_isIso_loopSpace A y₀ (j + 2) fun q hq ↦
            isIso_singularHomologyMap_isTerminalPUnit_of_forall_isTorsion'_reducedHomology
              S A (m + 2) hΩ (by omega)))
        m (Nat.lt_succ_self m)
    exact (HomotopyGroup.subtypeValMulEquivOfPathComponentSubset (N := Fin (m + 2))
      subset_rfl rfl).toAdditive.isTorsion'_iff.1 hπY
  · -- When `π₁(X, x)` is nontrivial, `H~₀(Ω X x; ℤ)` contains a copy of `ℤ`, forcing `0 ∈ S`.
    have : Nontrivial (π_ 1 X x) := not_subsingleton_iff_nontrivial.1 h1
    obtain ⟨f, hf⟩ := exists_injective_loopSpaceReducedHomology₀ (R := ℤ) x
    exact Module.isTorsion'_of_zero_mem
      (f.toAddMonoidHom.zero_mem_of_injective_of_isTorsion' hf (hH 0 (Nat.zero_le _)))

namespace MooreLoopSpace

/-- **Single Moore loop-space torsion detection.** For any pointed space `(X, x)`, submonoid
`S : Submonoid ℤ`, and `m : ℕ`, if the reduced integral singular homology `H~_k(Ωᴹ X x; ℤ)` is
`S`-torsion for all `k ≤ m + 2`, then `π_{m + 2}(X, x)` is `S`-torsion. -/
theorem isTorsion'_homotopyGroup_of_forall_isTorsion'_reducedHomology
    (x : X) (S : Submonoid ℤ) (m : ℕ)
    (hH : ∀ k ≤ m + 2, Module.IsTorsion'
      ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (MooreLoopSpace X x))) S) :
    Module.IsTorsion' (Additive (π_ (m + 2) X x)) S :=
  isTorsion'_homotopyGroup_of_forall_isTorsion'_loopSpaceReducedHomology x S m fun k hk ↦
    ((homotopyEquivPath x).reducedSingularHomologyIso
      (ModuleCat.of ℤ ℤ) k).symm.toLinearEquiv.toAddEquiv.isTorsion'_iff.2 (hH k hk)

end MooreLoopSpace

end SingleLoopSpace

/-! ### Double loop spaces (fixed-interval) -/

section DoubleLoopSpace

variable {Q : Type} [TopologicalSpace Q]

/-- **Double loop-space torsion detection.** For any pointed space `(Q, q)`, submonoid
`S : Submonoid ℤ`, and `m : ℕ`, if `H~_k(Ω²Q; ℤ)` is `S`-torsion for all `k < m + 2`, then
`π_{m + 2}(Q, q)` is `S`-torsion. -/
theorem isTorsion'_homotopyGroup_of_forall_isTorsion'_doubleLoopSpaceReducedHomology
    (q : Q) (S : Submonoid ℤ) (m : ℕ)
    (hH : ∀ k < m + 2, Module.IsTorsion'
      ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (Ω (Ω Q q) (Path.refl q)))) S) :
    Module.IsTorsion' (Additive (π_ (m + 2) Q q)) S := by
  cases m with
  | zero =>
    exact isTorsion'_pi2_of_isTorsion'_homology₀ q (hH 0 (Nat.zero_lt_succ 1))
      fun _ ↦ exists_injective_doubleLoopSpaceReducedHomology₀ (R := ℤ) q
  | succ n =>
    exact (pathLoopSpaceMulEquiv (X := Q) (x := q) (n + 1)).symm.toAdditive.isTorsion'_iff.2
      (isTorsion'_homotopyGroup_of_forall_isTorsion'_loopSpaceReducedHomology (Path.refl q) S n
        fun k hk ↦ hH k (Nat.lt_succ_of_le hk))

/-- **Detection of non-`S`-torsion higher homotopy groups in `H~_*(Ω²Q; ℤ)`** (homological content
of Proposition 5.11 of Barraud--Damian--Humilière--Oancea). If `π_{m + 2}(Q, q)` is not
`S`-torsion, then there exist `k < m + 2` and a class in `H~_k(Ω²Q; ℤ)` not annihilated by any
element of `S`. -/
theorem exists_forall_smul_ne_zero_doubleLoopSpaceReducedHomology
    (q : Q) (S : Submonoid ℤ) (m : ℕ)
    (hπ : ¬ Module.IsTorsion' (Additive (π_ (m + 2) Q q)) S) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (Ω (Ω Q q) (Path.refl q))), ∀ s ∈ S, s • x ≠ 0 :=
  Module.exists_forall_smul_ne_zero_of_not_isTorsion'_of_imp
    (isTorsion'_homotopyGroup_of_forall_isTorsion'_doubleLoopSpaceReducedHomology q S m) hπ

/-- **Power-torsion detection in `H~_*(Ω²Q; ℤ)`.** If `π_{m + 2}(Q, q)` contains an element not
killed by any power `d ^ r`, then in some degree `k < m + 2` the reduced integral homology
`H~_k(Ω²Q; ℤ)` contains a class not killed by any power `d ^ r`. -/
theorem exists_forall_pow_smul_ne_zero_doubleLoopSpaceReducedHomology
    (q : Q) (d : ℤ) (m : ℕ)
    (hπ : ∃ a : Additive (π_ (m + 2) Q q), ∀ r : ℕ, (d ^ r) • a ≠ 0) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (Ω (Ω Q q) (Path.refl q))), ∀ r : ℕ, (d ^ r) • x ≠ 0 := by
  obtain ⟨k, hk, x, hx⟩ := exists_forall_smul_ne_zero_doubleLoopSpaceReducedHomology q
    (Submonoid.powers d) m (by simpa [Submodule.isTorsion'_powers_iff] using hπ)
  exact ⟨k, hk, x, fun r ↦ hx (d ^ r) ⟨r, rfl⟩⟩

/-- **Infinite-order class in `H~_*(Ω²Q; ℤ)`.** If `π_{m + 2}(Q, q)` is not a torsion group, then
in some degree `k < m + 2` the reduced integral homology `H~_k(Ω²Q; ℤ)` contains an element of
infinite additive order. -/
theorem exists_not_isOfFinAddOrder_doubleLoopSpaceReducedHomology
    (q : Q) (m : ℕ)
    (hπ : ¬ IsAddTorsion (Additive (π_ (m + 2) Q q))) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (Ω (Ω Q q) (Path.refl q))), ¬ IsOfFinAddOrder x := by
  obtain ⟨k, hk, x, hx⟩ := exists_forall_smul_ne_zero_doubleLoopSpaceReducedHomology q
    (nonZeroDivisors ℤ) m (isAddTorsion_iff_isTorsion_int.not.1 hπ)
  exact ⟨k, hk, x, not_isOfFinAddOrder_iff_forall_nonZeroDivisors.2 hx⟩

end DoubleLoopSpace

/-! ### Double Moore loop spaces -/

namespace MooreLoopSpace

variable {Q : Type} [TopologicalSpace Q]

/-- **Double Moore loop-space torsion detection.** For any pointed space `(Q, q)`, submonoid
`S : Submonoid ℤ`, and `m : ℕ`, if `H~_k(ΩᴹΩᴹQ; ℤ)` is `S`-torsion for all `k < m + 2`, then
`π_{m + 2}(Q, q)` is `S`-torsion. -/
theorem isTorsion'_homotopyGroup_of_forall_isTorsion'_doubleReducedHomology
    (q : Q) (S : Submonoid ℤ) (m : ℕ)
    (hH : ∀ k < m + 2, Module.IsTorsion'
      ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1))) S) :
    Module.IsTorsion' (Additive (π_ (m + 2) Q q)) S := by
  cases m with
  | zero =>
    exact isTorsion'_pi2_of_isTorsion'_homology₀ q (hH 0 (Nat.zero_lt_succ 1))
      fun _ ↦ exists_injective_doubleReducedHomology₀ (R := ℤ) q
  | succ n =>
    exact (homotopyGroupMulEquiv q (n + 1)).symm.toAdditive.isTorsion'_iff.2
      (isTorsion'_homotopyGroup_of_forall_isTorsion'_reducedHomology (1 : MooreLoopSpace Q q) S n
        fun k hk ↦ hH k (Nat.lt_succ_of_le hk))

/-- **Detection of non-`S`-torsion higher homotopy groups in `H~_*(ΩᴹΩᴹQ; ℤ)`.** If
`π_{m + 2}(Q, q)` is not `S`-torsion, then there exist `k < m + 2` and a class in
`H~_k(ΩᴹΩᴹQ; ℤ)` not annihilated by any element of `S`. -/
theorem exists_forall_smul_ne_zero_doubleReducedHomology
    (q : Q) (S : Submonoid ℤ) (m : ℕ)
    (hπ : ¬ Module.IsTorsion' (Additive (π_ (m + 2) Q q)) S) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)), ∀ s ∈ S, s • x ≠ 0 :=
  Module.exists_forall_smul_ne_zero_of_not_isTorsion'_of_imp
    (isTorsion'_homotopyGroup_of_forall_isTorsion'_doubleReducedHomology q S m) hπ

/-- **Power-torsion detection in `H~_*(ΩᴹΩᴹQ; ℤ)`.** If `π_{m + 2}(Q, q)` contains an element not
killed by any power `d ^ r`, then in some degree `k < m + 2` the reduced integral homology
`H~_k(ΩᴹΩᴹQ; ℤ)` contains a class not killed by any power `d ^ r`. -/
theorem exists_forall_pow_smul_ne_zero_doubleReducedHomology
    (q : Q) (d : ℤ) (m : ℕ)
    (hπ : ∃ a : Additive (π_ (m + 2) Q q), ∀ r : ℕ, (d ^ r) • a ≠ 0) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)), ∀ r : ℕ, (d ^ r) • x ≠ 0 := by
  obtain ⟨k, hk, x, hx⟩ := exists_forall_smul_ne_zero_doubleReducedHomology q
    (Submonoid.powers d) m (by simpa [Submodule.isTorsion'_powers_iff] using hπ)
  exact ⟨k, hk, x, fun r ↦ hx (d ^ r) ⟨r, rfl⟩⟩

/-- **Infinite-order class in `H~_*(ΩᴹΩᴹQ; ℤ)`.** If `π_{m + 2}(Q, q)` is not a torsion group,
then in some degree `k < m + 2` the reduced integral homology `H~_k(ΩᴹΩᴹQ; ℤ)` contains an element
of infinite additive order. -/
theorem exists_not_isOfFinAddOrder_doubleReducedHomology
    (q : Q) (m : ℕ)
    (hπ : ¬ IsAddTorsion (Additive (π_ (m + 2) Q q))) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)), ¬ IsOfFinAddOrder x := by
  obtain ⟨k, hk, x, hx⟩ := exists_forall_smul_ne_zero_doubleReducedHomology q
    (nonZeroDivisors ℤ) m (isAddTorsion_iff_isTorsion_int.not.1 hπ)
  exact ⟨k, hk, x, not_isOfFinAddOrder_iff_forall_nonZeroDivisors.2 hx⟩

end MooreLoopSpace

end TauCeti
