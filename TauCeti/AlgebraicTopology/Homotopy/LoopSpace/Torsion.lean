/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.ModuloTorsion
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ReducedHomology
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Acyclic
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Detection of non-torsion higher homotopy groups in loop space homology

For any submonoid `S : Submonoid ℤ`, this file applies Serre's Hurewicz theorem modulo `S`-torsion
(`TauCeti.forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology`) and loop-space
acyclicity transfer (`TauCeti.isZero_singularHomology_of_isIso_loopSpace`) to detect
non-`S`-torsion higher homotopy groups in the reduced integral homology of single and double loop
spaces (fixed-interval `Ω²Q`, Moore `ΩᴹΩᴹQ`, and normalized cubical homology when
`π₂(Q, q) = 0`), without any connectedness hypothesis on `Q`. This provides the homological content
of the second part of Proposition 5.11 of Barraud--Damian--Humilière--Oancea; the identification of
`H~_*(Ω²Q)` with `ker i_{Q*}` is in
`TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ConstantLoopKernel`.

## Proof outline

* For a single loop space `Ω X x`, split on whether `π₁(X, x)` is trivial. If nontrivial,
  `H~₀(Ω X x; ℤ)` contains a copy of `ℤ`, forcing `0 ∈ S` if it is `S`-torsion. If trivial,
  restrict to `Y = pathComponent x` (simply connected with `Ω Y ≃ₜ Ω X x` path-connected),
  transfer vanishing of `H_*(Ω Y; S⁻¹ℤ)` to `H_*(Y; S⁻¹ℤ)`, and apply Hurewicz modulo `S`-torsion.
* For double loop spaces `Ω²Q` (and `ΩᴹΩᴹQ`), `m = 0` (`π₂`) uses degree-0 reduced homology, while
  `m = n + 1` applies the single-loop-space result to `Ω Q q` via `pathLoopSpaceMulEquiv`.

## Main results

* `TauCeti.isTorsion'_homotopyGroup_of_forall_isTorsion'_loopSpaceReducedHomology`,
  `TauCeti.MooreLoopSpace.isTorsion'_homotopyGroup_of_forall_isTorsion'_reducedHomology`:
  `S`-torsion of `H~_k(Ω X x; ℤ)` for `k ≤ m + 2` implies `S`-torsion of `π_{m + 2}(X, x)`.
* `TauCeti.isTorsion'_homotopyGroup_of_forall_isTorsion'_doubleLoopSpaceReducedHomology`,
  `TauCeti.exists_forall_smul_ne_zero_doubleLoopSpaceReducedHomology`,
  `TauCeti.exists_forall_pow_smul_ne_zero_doubleLoopSpaceReducedHomology`,
  `TauCeti.exists_smul_ne_zero_doubleLoopSpaceReducedHomology`,
  `TauCeti.exists_not_isOfFinAddOrder_doubleLoopSpaceReducedHomology`: detection of non-`S`-torsion
  higher homotopy groups in `H~_*(Ω²Q; ℤ)`, with mirrors in `TauCeti.MooreLoopSpace` for
  `ΩᴹΩᴹQ` and normalized cubical homology.

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

/-- Extraction of a degree `< m + 2` carrying a class not annihilated by any scalar in `S`. -/
private lemma exists_forall_smul_ne_zero {F : ℕ → ModuleCat.{0} ℤ} {G : Type*}
    [AddCommGroup G] {S : Submonoid ℤ} {m : ℕ}
    (himp : (∀ k < m + 2, Module.IsTorsion' (F k) S) → Module.IsTorsion' G S)
    (hG : ¬ Module.IsTorsion' G S) :
    ∃ k < m + 2, ∃ x : F k, ∀ s ∈ S, s • x ≠ 0 := by
  obtain ⟨k, hk⟩ := Classical.not_forall.mp (mt himp hG)
  rw [not_imp, Module.not_isTorsion'_iff] at hk
  exact ⟨k, hk.1, hk.2⟩

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
      (Module.zero_mem_of_injective_of_isTorsion' f.toAddMonoidHom hf hH₀)

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
  · let Y := pathComponent x
    let y₀ : Y := pathComponentSelf x
    have : Subsingleton (π_ 1 Y y₀) := (Equiv.ofBijective _
      (HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
        (x := y₀) Set.Subset.rfl rfl)).subsingleton_congr.2 h1
    have : PathConnectedSpace (Ω Y y₀) :=
      (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 y₀).2 inferInstance
    let A := Localization S
    have hΩA : ∀ q, q ≤ m + 2 →
        IsIso (((singularHomologyFunctor (ModuleCat.{0} A) q).obj (ModuleCat.of A A)).map
          (TopCat.isTerminalPUnit.from (TopCat.of (Ω Y y₀)))) := by
      intro q hqm
      cases q with
      | zero =>
        exact IsIso.of_isIso_fac_right (singularHomologyMap_singularHomology₀ε
          (ModuleCat.of A A) (TopCat.isTerminalPUnit.from (TopCat.of (Ω Y y₀))))
      | succ r =>
        have hsub : Subsingleton (((singularChains A).obj (TopCat.of (Ω Y y₀))).homology
            (r + 1)) :=
          (isTorsion'_singularChains_int_homology_iff S A (TopCat.of (Ω Y y₀)) (r + 1)).1 <|
            (((Path.subtypeValHomeomorph (a := y₀) (b := y₀)
              subset_rfl).toHomotopyEquiv.singularHomologyIso
              (ModuleCat.of ℤ ℤ) (r + 1)).toLinearEquiv.toAddEquiv.isTorsion'_iff.2 <|
              ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) r).app
                (TopCat.of (Ω X x))).symm.toLinearEquiv.toAddEquiv.isTorsion'_iff.2
                  (hH (r + 1) hqm))
        exact (ModuleCat.isZero_iff_subsingleton.mpr hsub).isIso
          (isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of A A)
            (TopCat.of PUnit) r.succ_ne_zero) _
    have hπY : Module.IsTorsion' (Additive (π_ (m + 2) Y y₀)) S :=
      (forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y₀ S A (m + 1)).2
        (fun j hj ↦ ModuleCat.isZero_iff_subsingleton.mp <|
          isZero_singularHomology_of_isIso_loopSpace A y₀ (Nat.succ_ne_zero (j + 1))
            fun q hq ↦ hΩA q (by omega)) m (Nat.lt_succ_self m)
    exact (MulEquiv.ofBijective
      (HomotopyGroup.mapHom (N := Fin (m + 2)) (x := y₀) (y := x)
        ⟨Subtype.val, continuous_subtypeVal⟩ rfl)
      (HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
        Set.Subset.rfl rfl)).toAdditive.isTorsion'_iff.1 hπY
  · have : Nontrivial (π_ 1 X x) := not_subsingleton_iff_nontrivial.1 h1
    obtain ⟨f, hf⟩ := exists_injective_loopSpaceReducedHomology₀ (R := ℤ) x
    exact Module.isTorsion'_of_zero_mem
      (Module.zero_mem_of_injective_of_isTorsion' f.toAddMonoidHom hf (hH 0 (Nat.zero_le _)))

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
  exists_forall_smul_ne_zero
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

/-- **Non-`d`-torsion class in `H~_*(Ω²Q; ℤ)`.** If `π_{m + 2}(Q, q)` contains an element not
killed by any power of `d`, then in some degree `k < m + 2` the reduced integral homology
`H~_k(Ω²Q; ℤ)` contains a class `x` with `d • x ≠ 0`. -/
theorem exists_smul_ne_zero_doubleLoopSpaceReducedHomology
    (q : Q) (d : ℤ) (m : ℕ)
    (hπ : ∃ a : Additive (π_ (m + 2) Q q), ∀ r : ℕ, (d ^ r) • a ≠ 0) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (Ω (Ω Q q) (Path.refl q))), d • x ≠ 0 := by
  obtain ⟨k, hk, x, hx⟩ := exists_forall_pow_smul_ne_zero_doubleLoopSpaceReducedHomology q d m hπ
  exact ⟨k, hk, x, by simpa only [pow_one] using hx 1⟩

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
  exists_forall_smul_ne_zero
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

/-- **Non-`d`-torsion class in `H~_*(ΩᴹΩᴹQ; ℤ)`.** If `π_{m + 2}(Q, q)` contains an element not
killed by any power of `d`, then in some degree `k < m + 2` the reduced integral homology
`H~_k(ΩᴹΩᴹQ; ℤ)` contains a class `x` with `d • x ≠ 0`. -/
theorem exists_smul_ne_zero_doubleReducedHomology
    (q : Q) (d : ℤ) (m : ℕ)
    (hπ : ∃ a : Additive (π_ (m + 2) Q q), ∀ r : ℕ, (d ^ r) • a ≠ 0) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)), d • x ≠ 0 := by
  obtain ⟨k, hk, x, hx⟩ := exists_forall_pow_smul_ne_zero_doubleReducedHomology q d m hπ
  exact ⟨k, hk, x, by simpa only [pow_one] using hx 1⟩

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

/-- **Normalized cubical homology version when `π₂(Q, q)` vanishes.** When
`Subsingleton (π_ 2 Q q)`, `ΩᴹΩᴹQ` is path-connected so `H~₀(ΩᴹΩᴹQ; ℤ) = 0`, and any
non-`S`-torsion higher homotopy group `π_{m + 2}(Q, q)` produces a positive-degree normalized
cubical homology class (`1 ≤ k < m + 2`) not annihilated by any `s ∈ S`. -/
theorem exists_forall_smul_ne_zero_doubleCubicalHomology
    (q : Q) [Subsingleton (π_ 2 Q q)] (S : Submonoid ℤ) (m : ℕ)
    (hπ : ¬ Module.IsTorsion' (Additive (π_ (m + 2) Q q)) S) :
    ∃ k, 1 ≤ k ∧ k < m + 2 ∧
      ∃ x : ((normalizedCubicalChainComplex ℤ).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1))).homology k,
        ∀ s ∈ S, s • x ≠ 0 := by
  obtain ⟨k, hk, x, hx⟩ := exists_forall_smul_ne_zero_doubleReducedHomology q S m hπ
  have := pathConnectedSpace_double q
  cases k with
  | zero =>
    have := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_reducedSingularHomologyFunctor_zero (ModuleCat.of ℤ ℤ)
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)))
    exact (hx 1 S.one_mem (Subsingleton.elim _ _)).elim
  | succ r =>
    let e := ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) r).app
      (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1))).trans
      (singularCubicalHomologyIso ℤ (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)) (r + 1))
    exact ⟨r + 1, Nat.succ_le_succ (Nat.zero_le r), hk, e.hom.hom x, fun s hs h0 ↦
      hx s hs <| e.toLinearEquiv.toAddEquiv.injective
        (by rw [map_zsmul]; exact h0.trans (map_zero _).symm)⟩

end MooreLoopSpace

end TauCeti
