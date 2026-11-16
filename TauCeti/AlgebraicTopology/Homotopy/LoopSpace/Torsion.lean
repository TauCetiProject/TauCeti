/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.ModuloTorsion
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ReducedHomology
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
import TauCeti.AlgebraicTopology.Singular.Fibration.AcyclicFiber
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent
import TauCeti.Topology.Homotopy.Path
import TauCeti.Topology.PathComponent

/-!
# Detection of non-torsion higher homotopy groups in loop space homology

For any submonoid `S : Submonoid ℤ`, this file applies Serre's Hurewicz theorem modulo `S`-torsion
(`TauCeti.forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology`) and path-fibration
acyclicity transfer (`TauCeti.subsingleton_singularHomology_of_loopSpace`) to detect non-`S`-torsion
higher homotopy groups in the reduced integral homology of single and double loop spaces (fixed-
interval `Ω²Q`, Moore `ΩᴹΩᴹQ`, and normalized cubical homology when `π₂(Q, q) = 0`), without any
connectedness hypothesis on `Q`. This provides the homological content of the second part of
Proposition 5.11 of Barraud--Damian--Humilière--Oancea; the identification of `H~_*(Ω²Q)` with
`ker i_{Q*}` is not formalized here.

## Proof outline

* For a single loop space `Ω X x`, split on whether `π₁(X, x)` is trivial. If nontrivial,
  `H~₀(Ω X x; ℤ)` contains a copy of `ℤ`, forcing `0 ∈ S` if it is `S`-torsion. If trivial,
  restrict to `Y = pathComponent x` (simply connected with `Ω Y ≃ₜ Ω X x` path-connected),
  transfer vanishing of `H_*(Ω Y; S⁻¹ℤ)` to `H_*(Y; S⁻¹ℤ)`, and apply Hurewicz modulo `S`-torsion.
* For double loop spaces `Ω²Q` (and `ΩᴹΩᴹQ`), `m = 0` (`π₂`) uses degree-0 reduced homology, while
  `m = n + 1` applies the single-loop-space result to `Ω Q q` via `pathLoopSpaceMulEquiv`.

## Main results

* `TauCeti.loopSpaceReducedHomology₀Iso`, `TauCeti.exists_injective_loopSpaceReducedHomology₀`:
  `H~₀(Ω X x; R) ≅ ∐_{a ∈ π₁(X, x), a ≠ 1} R`, containing a copy of `R` when `π₁(X, x)` is
  nontrivial.
* `TauCeti.isTorsion'_homotopyGroup_of_forall_isTorsion'_loopSpaceReducedHomology`,
  `TauCeti.MooreLoopSpace.isTorsion'_homotopyGroup_of_forall_isTorsion'_reducedHomology`:
  `S`-torsion of `H~_k(Ω X x; ℤ)` for `k ≤ m + 2` implies `S`-torsion of `π_{m + 2}(X, x)`.
* `TauCeti.isTorsion'_homotopyGroup_of_forall_isTorsion'_doubleLoopSpaceReducedHomology`,
  `TauCeti.exists_not_isTorsion'_doubleLoopSpaceReducedHomology`,
  `TauCeti.exists_not_pow_smul_eq_zero_doubleLoopSpaceReducedHomology`,
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

/-! ### Reduced zeroth homology of a single loop space -/

section LoopSpaceDegreeZero

universe w v u

/-- **Reduced zeroth homology of a loop space.** `H~₀(Ω X x; R)` is the coproduct of copies of
`R` indexed by the nontrivial elements of `π₁(X, x)`. -/
def loopSpaceReducedHomology₀Iso {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Preadditive C] [CategoryWithHomology C] [HasKernels C] (R : C) {X : Type w}
    [TopologicalSpace X] (x : X) :
    (reducedSingularHomologyFunctor R 0).obj (TopCat.of (Ω X x)) ≅
      ∐ fun _ : {a : FundamentalGroup X x // a ≠ 1} ↦ R :=
  reducedSingularHomology₀IsoOfEquiv R (Y := TopCat.of (Ω X x)) (Path.refl x)
    zerothHomotopyLoopSpaceEquivFundamentalGroup
    (zerothHomotopyLoopSpaceEquivFundamentalGroup_mk (Path.refl x))

/-- If `π₁(X, x)` is nontrivial, the reduced zeroth homology `H~₀(Ω X x; R)` contains a copy
of `R`. -/
theorem exists_injective_loopSpaceReducedHomology₀ {R : Type u} [Ring R] {X : Type u}
    [TopologicalSpace X] (x : X) [Nontrivial (π_ 1 X x)] :
    ∃ f : R →ₗ[R]
        (reducedSingularHomologyFunctor (ModuleCat.of R R) 0).obj (TopCat.of (Ω X x)),
      Function.Injective f := by
  have : Nontrivial (FundamentalGroup X x) :=
    pi1MulEquivFundamentalGroup.toEquiv.nontrivial_congr.1 inferInstance
  have : Nonempty {a : FundamentalGroup X x // a ≠ 1} :=
    nonempty_subtype.2 (exists_ne (1 : FundamentalGroup X x))
  exact ModuleCat.exists_injective_of_iso_sigma (loopSpaceReducedHomology₀Iso _ x)

end LoopSpaceDegreeZero

/-! ### Private torsion and path-component helpers -/

section Helpers

/-- Transport `S`-torsion across an additive group equivalence. -/
private lemma isTorsion'_of_addEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {S : Submonoid ℤ} (e : M ≃+ N) (hN : Module.IsTorsion' N S) : Module.IsTorsion' M S :=
  fun m ↦ let ⟨s, hs⟩ := @hN (e m); ⟨s, e.injective (by
    rw [Submonoid.smul_def, map_zsmul, map_zero]; exact hs)⟩

/-- Transport `S`-torsion across a `ModuleCat ℤ` isomorphism. -/
private lemma isTorsion'_of_moduleCatIso {M N : ModuleCat.{0} ℤ} {S : Submonoid ℤ} (e : M ≅ N)
    (hN : Module.IsTorsion' N S) : Module.IsTorsion' M S :=
  isTorsion'_of_addEquiv e.toLinearEquiv.toAddEquiv hN

/-- If an `S`-torsion `ℤ`-module admits an injective `ℤ`-linear map from `ℤ`, then `0 ∈ S`. -/
private lemma zero_mem_of_injective_of_isTorsion' {M : ModuleCat.{0} ℤ} {S : Submonoid ℤ}
    (f : ℤ →ₗ[ℤ] M) (hf : Function.Injective f) (hM : Module.IsTorsion' M S) : (0 : ℤ) ∈ S := by
  obtain ⟨s, hs⟩ := @hM (f 1)
  have hs0 : (s : ℤ) = 0 := hf <| by
    have hmap : f (s : ℤ) = (s : ℤ) • f 1 := by
      simpa [zsmul_eq_mul] using map_zsmul f.toAddMonoidHom (s : ℤ) 1
    rw [hmap, ← Submonoid.smul_def, hs, map_zero]
  exact hs0 ▸ s.2

/-- When `0 ∈ S`, every additive commutative group is `S`-torsion. -/
private lemma isTorsion'_of_zero_mem {M : Type*} [AddCommGroup M] {S : Submonoid ℤ}
    (h0 : (0 : ℤ) ∈ S) : Module.IsTorsion' M S :=
  fun _ ↦ ⟨⟨0, h0⟩, by rw [Submonoid.smul_def, zero_smul]⟩

/-- Every loop based at `x` stays inside `pathComponent x`, giving a homeomorphism
`Ω (pathComponent x) ⟨x, _⟩ ≃ₜ Ω X x`. -/
private def loopSpacePathComponentHomeomorph {X : Type*} [TopologicalSpace X] (x : X) :
    Ω (pathComponent x) ⟨x, mem_pathComponent_self x⟩ ≃ₜ Ω X x where
  toFun p := p.map continuous_subtype_val
  invFun p :=
    ⟨⟨fun t ↦ ⟨p t, p.mem_pathComponent t⟩, continuous_induced_rng.2 p.continuous⟩,
      Subtype.ext p.source, Subtype.ext p.target⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  continuous_toFun := continuous_induced_rng.2
    ((ContinuousMap.continuous_postcomp ⟨Subtype.val, continuous_subtype_val⟩).comp
      continuous_induced_dom)
  continuous_invFun := continuous_induced_rng.2 <| ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_induced_rng.2 <| (continuous_eval (F := C(I, X))).comp
      ((continuous_induced_dom (f := Path.toContinuousMap).comp continuous_fst).prodMk
        continuous_snd))

/-- Contrapositive extraction of a degree `< m + 2` carrying a non-`S`-torsion homology class. -/
private lemma exists_not_isTorsion'_of_contrapositive {F : ℕ → ModuleCat.{0} ℤ} {G : Type*}
    [AddCommGroup G] {S : Submonoid ℤ} {m : ℕ}
    (himp : (∀ k < m + 2, Module.IsTorsion' (F k) S) → Module.IsTorsion' G S)
    (hG : ¬ Module.IsTorsion' G S) :
    ∃ k < m + 2, ∃ x : F k, ∀ s ∈ S, s • x ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hG (himp fun k hk x ↦ let ⟨s, hs, h0⟩ := hall k hk x; ⟨⟨s, hs⟩, h0⟩)

/-- An element of a `ℤ`-module has infinite additive order if no nonzero integer kills it. -/
private lemma not_isOfFinAddOrder_of_forall_nonZeroDivisors {M : ModuleCat.{0} ℤ} {x : M}
    (hx : ∀ s ∈ nonZeroDivisors ℤ, s • x ≠ 0) : ¬ IsOfFinAddOrder x := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  rintro ⟨n, hn, hnx⟩
  exact hx (n : ℤ) (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)))
    ((natCast_zsmul x n).trans hnx)

/-- Reinterpret an element not annihilated by any `d ^ r` as a witness against
`Submonoid.powers d`-torsion. -/
private lemma not_isTorsion'_powers_of_exists {M : Type*} [AddCommGroup M] {d : ℤ}
    (h : ∃ a : M, ∀ r : ℕ, (d ^ r) • a ≠ 0) : ¬ Module.IsTorsion' M (Submonoid.powers d) :=
  let ⟨a, ha⟩ := h
  fun ht ↦ let ⟨⟨_, r, rfl⟩, hs⟩ := @ht a; ha r (by rwa [Submonoid.smul_def] at hs)

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
  by_cases h1 : Subsingleton (π_ 1 X x)
  · let Y := pathComponent x
    let y₀ : Y := ⟨x, mem_pathComponent_self x⟩
    have : Subsingleton (π_ 1 Y y₀) := (Equiv.ofBijective _
      (HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
        (x := y₀) Set.Subset.rfl rfl)).subsingleton_congr.2 h1
    have : PathConnectedSpace (Ω Y y₀) :=
      (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 y₀).2 inferInstance
    let A := Localization S
    have hΩA : ∀ q, 1 ≤ q → q ≤ m + 2 →
        Subsingleton (((singularChains A).obj (TopCat.of (Ω Y y₀))).homology q) := by
      intro q hq1 hqm
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq1)
      exact ((TopCat.of (Ω Y y₀)).isTorsion'_singularHomology_int_iff_subsingleton S A (r + 1)).1 <|
        isTorsion'_of_moduleCatIso
          ((loopSpacePathComponentHomeomorph x).toHomotopyEquiv.singularHomologyIso
            (ModuleCat.of ℤ ℤ) (r + 1)) <|
        isTorsion'_of_moduleCatIso
          ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) r).app (TopCat.of (Ω X x))).symm
          (hH (r + 1) hqm)
    have hπY : Module.IsTorsion' (Additive (π_ (m + 2) Y y₀)) S :=
      (forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y₀ S A (m + 1)).2
        (fun j hj ↦ subsingleton_singularHomology_of_loopSpace y₀ A (j + 1)
          fun q hq1 hqj ↦ hΩA q hq1 (by omega)) m (Nat.lt_succ_self m)
    exact isTorsion'_of_addEquiv (MulEquiv.ofBijective
      (HomotopyGroup.mapHom (N := Fin (m + 2)) (x := y₀) (y := x)
        ⟨Subtype.val, continuous_subtype_val⟩ rfl)
      (HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
        Set.Subset.rfl rfl)).symm.toAdditive hπY
  · have : Nontrivial (π_ 1 X x) := not_subsingleton_iff_nontrivial.1 h1
    obtain ⟨f, hf⟩ := exists_injective_loopSpaceReducedHomology₀ (R := ℤ) x
    exact isTorsion'_of_zero_mem (zero_mem_of_injective_of_isTorsion' f hf (hH 0 (Nat.zero_le _)))

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
    isTorsion'_of_moduleCatIso
      ((homotopyEquivPath x).reducedSingularHomologyIso (ModuleCat.of ℤ ℤ) k).symm (hH k hk)

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
    by_cases h2 : Subsingleton (π_ 2 Q q)
    · exact fun a ↦ ⟨1, by rw [one_smul]; exact Subsingleton.elim a 0⟩
    · have : Nontrivial (π_ 2 Q q) := not_subsingleton_iff_nontrivial.1 h2
      obtain ⟨f, hf⟩ := exists_injective_doubleLoopSpaceReducedHomology₀ (R := ℤ) q
      exact isTorsion'_of_zero_mem
        (zero_mem_of_injective_of_isTorsion' f hf (hH 0 (Nat.zero_lt_succ 1)))
  | succ n =>
    exact isTorsion'_of_addEquiv (pathLoopSpaceMulEquiv (X := Q) (x := q) (n + 1)).symm.toAdditive
      (isTorsion'_homotopyGroup_of_forall_isTorsion'_loopSpaceReducedHomology (Path.refl q) S n
        fun k hk ↦ hH k (Nat.lt_succ_of_le hk))

/-- **Detection of non-`S`-torsion higher homotopy groups in `H~_*(Ω²Q; ℤ)`** (homological content
of Proposition 5.11 of Barraud--Damian--Humilière--Oancea). If `π_{m + 2}(Q, q)` is not
`S`-torsion, then there exist `k < m + 2` and a class in `H~_k(Ω²Q; ℤ)` not annihilated by any
element of `S`. -/
theorem exists_not_isTorsion'_doubleLoopSpaceReducedHomology
    (q : Q) (S : Submonoid ℤ) (m : ℕ)
    (hπ : ¬ Module.IsTorsion' (Additive (π_ (m + 2) Q q)) S) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (Ω (Ω Q q) (Path.refl q))), ∀ s ∈ S, s • x ≠ 0 :=
  exists_not_isTorsion'_of_contrapositive
    (isTorsion'_homotopyGroup_of_forall_isTorsion'_doubleLoopSpaceReducedHomology q S m) hπ

/-- **Power-torsion detection in `H~_*(Ω²Q; ℤ)`.** If `π_{m + 2}(Q, q)` contains an element not
killed by any power `d ^ r`, then in some degree `k < m + 2` the reduced integral homology
`H~_k(Ω²Q; ℤ)` contains a class not killed by any power `d ^ r`. -/
theorem exists_not_pow_smul_eq_zero_doubleLoopSpaceReducedHomology
    (q : Q) (d : ℤ) (m : ℕ)
    (hπ : ∃ a : Additive (π_ (m + 2) Q q), ∀ r : ℕ, (d ^ r) • a ≠ 0) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (Ω (Ω Q q) (Path.refl q))), ∀ r : ℕ, (d ^ r) • x ≠ 0 := by
  obtain ⟨k, hk, x, hx⟩ := exists_not_isTorsion'_doubleLoopSpaceReducedHomology q
    (Submonoid.powers d) m (not_isTorsion'_powers_of_exists hπ)
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
  obtain ⟨k, hk, x, hx⟩ := exists_not_pow_smul_eq_zero_doubleLoopSpaceReducedHomology q d m hπ
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
  obtain ⟨k, hk, x, hx⟩ := exists_not_isTorsion'_doubleLoopSpaceReducedHomology q
    (nonZeroDivisors ℤ) m (isAddTorsion_iff_isTorsion_int.not.1 hπ)
  exact ⟨k, hk, x, not_isOfFinAddOrder_of_forall_nonZeroDivisors hx⟩

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
    by_cases h2 : Subsingleton (π_ 2 Q q)
    · exact fun a ↦ ⟨1, by rw [one_smul]; exact Subsingleton.elim a 0⟩
    · have : Nontrivial (π_ 2 Q q) := not_subsingleton_iff_nontrivial.1 h2
      obtain ⟨f, hf⟩ := exists_injective_doubleReducedHomology₀ (R := ℤ) q
      exact isTorsion'_of_zero_mem
        (zero_mem_of_injective_of_isTorsion' f hf (hH 0 (Nat.zero_lt_succ 1)))
  | succ n =>
    exact isTorsion'_of_addEquiv (homotopyGroupMulEquiv q (n + 1)).symm.toAdditive
      (isTorsion'_homotopyGroup_of_forall_isTorsion'_reducedHomology (1 : MooreLoopSpace Q q) S n
        fun k hk ↦ hH k (Nat.lt_succ_of_le hk))

/-- **Detection of non-`S`-torsion higher homotopy groups in `H~_*(ΩᴹΩᴹQ; ℤ)`.** If
`π_{m + 2}(Q, q)` is not `S`-torsion, then there exist `k < m + 2` and a class in
`H~_k(ΩᴹΩᴹQ; ℤ)` not annihilated by any element of `S`. -/
theorem exists_not_isTorsion'_doubleReducedHomology
    (q : Q) (S : Submonoid ℤ) (m : ℕ)
    (hπ : ¬ Module.IsTorsion' (Additive (π_ (m + 2) Q q)) S) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)), ∀ s ∈ S, s • x ≠ 0 :=
  exists_not_isTorsion'_of_contrapositive
    (isTorsion'_homotopyGroup_of_forall_isTorsion'_doubleReducedHomology q S m) hπ

/-- **Power-torsion detection in `H~_*(ΩᴹΩᴹQ; ℤ)`.** If `π_{m + 2}(Q, q)` contains an element not
killed by any power `d ^ r`, then in some degree `k < m + 2` the reduced integral homology
`H~_k(ΩᴹΩᴹQ; ℤ)` contains a class not killed by any power `d ^ r`. -/
theorem exists_not_pow_smul_eq_zero_doubleReducedHomology
    (q : Q) (d : ℤ) (m : ℕ)
    (hπ : ∃ a : Additive (π_ (m + 2) Q q), ∀ r : ℕ, (d ^ r) • a ≠ 0) :
    ∃ k < m + 2,
      ∃ x : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) k).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)), ∀ r : ℕ, (d ^ r) • x ≠ 0 := by
  obtain ⟨k, hk, x, hx⟩ := exists_not_isTorsion'_doubleReducedHomology q
    (Submonoid.powers d) m (not_isTorsion'_powers_of_exists hπ)
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
  obtain ⟨k, hk, x, hx⟩ := exists_not_pow_smul_eq_zero_doubleReducedHomology q d m hπ
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
  obtain ⟨k, hk, x, hx⟩ := exists_not_isTorsion'_doubleReducedHomology q
    (nonZeroDivisors ℤ) m (isAddTorsion_iff_isTorsion_int.not.1 hπ)
  exact ⟨k, hk, x, not_isOfFinAddOrder_of_forall_nonZeroDivisors hx⟩

/-- **Normalized cubical homology version when `π₂(Q, q)` vanishes.** When
`Subsingleton (π_ 2 Q q)`, `ΩᴹΩᴹQ` is path-connected so `H~₀(ΩᴹΩᴹQ; ℤ) = 0`, and any
non-`S`-torsion higher homotopy group `π_{m + 2}(Q, q)` produces a positive-degree normalized
cubical homology class (`1 ≤ k < m + 2`) not annihilated by any `s ∈ S`. -/
theorem exists_not_isTorsion'_doubleCubicalHomology
    (q : Q) [Subsingleton (π_ 2 Q q)] (S : Submonoid ℤ) (m : ℕ)
    (hπ : ¬ Module.IsTorsion' (Additive (π_ (m + 2) Q q)) S) :
    ∃ k, 1 ≤ k ∧ k < m + 2 ∧
      ∃ x : ((normalizedCubicalChainComplex ℤ).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1))).homology k,
        ∀ s ∈ S, s • x ≠ 0 := by
  obtain ⟨k, hk, x, hx⟩ := exists_not_isTorsion'_doubleReducedHomology q S m hπ
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
