/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ModTwoVanishing
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.PowerTorsion

import TauCeti.Algebra.Module.ZMod.TensorProduct

/-!
# The alternatives of Proposition 5.11, and the kernel of the constant loops

Let `Q` be a space with a point `x`, and `d` an integer. The inclusion of path spaces
`P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` (`TauCeti.basedConstContractibleMoorePathsInclusion`) has, on
homology, the kernel `H~_*(Ω²Q)` (`TauCeti.kernelBasedConstContractibleMoorePathsInclusionIso`).
Barraud, Damian, Humilière and Oancea detect closed characteristics on cotangent bundles by
finding in this kernel a class that `d` does not kill, where `d` is the degree of a map to `Q`.
Their Proposition 5.11 finds one under each of three conditions on the homotopy groups of `Q`;
this file packages the three as one predicate, `TauCeti.HomotopyGroupsDetectDegree Q x d` (the
homotopy groups provide a kernel class detecting the degree `d`):

* `d ≠ 0` and `π₂(Q, x)` is nontrivial;
* `π₃(Q, x), …, π_{k+2}(Q, x)` vanish and some `a ∈ π_{k+3}(Q, x)` has `a ^ d ≠ 1`;
* some `π_{ℓ+3}(Q, x)` is annihilated by no power `d ^ m`, `m ≥ 1`.

Each alternative forces `d ≠ 0` (`TauCeti.HomotopyGroupsDetectDegree.ne_zero`). Under the predicate
the kernel of the inclusion contains a class `z` with `d • z ≠ 0`, by
`HomotopyGroupsDetectDegree.exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths`.
The three cases are
`TauCeti.exists_injective_singularHomology_basedConstContractibleMoorePaths_zero`
(a copy of `ℤ` in degree zero), the Hurewicz isomorphism
`TauCeti.basedConstContractibleMoorePathsHomologyAddEquiv` in degree `k + 1`, and
`TauCeti.exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths` (Serre's Hurewicz
theorem modulo the groups annihilated by a power of `d`).

Two special cases are the hypotheses of the source's Theorem A.

* For `d = ±1` the predicate says exactly that some `π_{j+2}(Q, x)` is nontrivial
  (`TauCeti.homotopyGroupsDetectDegree_iff_exists_nontrivial`), which for a path-connected `Q` is
  that `Q` is not aspherical (`TauCeti.homotopyGroupsDetectDegree_iff_not_isAspherical`).
* For `d ≠ 0`, a homotopy group `π_{ℓ+2}(Q, x)` that is not a torsion group gives the predicate
  (`TauCeti.HomotopyGroupsDetectDegree.of_not_isMulTorsion`).

The mod-two analogue, the input of the source's Theorems 5.15 and C, is
`TauCeti.exists_ne_zero_singularHomology_zmod_two_basedConstContractibleMoorePaths`: if `π₂(Q, x)`
is nontrivial or squaring is not surjective on some `π_{ℓ+3}(Q, x)`, the kernel of the inclusion on
mod-two homology is nonzero. The second alternative says that `π_{ℓ+3}(Q, x) ⊗ ℤ/2` is nonzero,
and mod-two vanishing for the double loop space applies.

The source identifies this kernel with the kernel of the map `i_{Q*}` induced by the constant loops
`Q → 𝓛₀Q` on DG Morse homology with coefficients in the chains on the based loops of `𝓛₀Q`, through
the fibration theorem; that identification is not formalized here.

## Main definitions

* `TauCeti.HomotopyGroupsDetectDegree`: the three alternatives of Proposition 5.11.

## Main results

* `HomotopyGroupsDetectDegree.exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths`
  in the namespace `TauCeti`: under the alternatives, the kernel of the inclusion of path spaces on
  integral homology has a class not killed by `d`.
* `TauCeti.homotopyGroupsDetectDegree_iff_not_isAspherical`: for `d = ±1` and path-connected `Q`
  the alternatives say that `Q` is not aspherical.
* `TauCeti.HomotopyGroupsDetectDegree.of_not_isMulTorsion`: a non-torsion higher homotopy group
  gives the alternatives for every `d ≠ 0`.
* `TauCeti.exists_ne_zero_singularHomology_zmod_two_basedConstContractibleMoorePaths`: the mod-two
  kernel is nonzero when `π₂` is nontrivial or squaring is not onto some higher homotopy group.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11 and Theorems 5.10 and
  5.15, with their consequences Theorems A and C.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy TensorProduct

universe u

namespace TauCeti

section Predicate

variable {Q : Type u} [TopologicalSpace Q] {x : Q} {d : ℤ}

variable (Q x d) in
/-- **The homotopy groups of `Q` at `x` detect the degree `d`**: the three alternatives of
Proposition 5.11 of Barraud–Damian–Humilière–Oancea. Either `d ≠ 0` and `π₂(Q, x)` is
nontrivial; or the groups `π₃(Q, x), …, π_{k+2}(Q, x)` vanish and `π_{k+3}(Q, x)` has an element
`a` with `a ^ d ≠ 1`; or some `π_{ℓ+3}(Q, x)` has, for every `m ≥ 1`, an element `a` with
`a ^ (d ^ m) ≠ 1`, that is, it is annihilated by no power of `d`. Under this condition the kernel
of the inclusion of the constant loops on path spaces, which is the reduced homology of the double
loop space, has a class not killed by `d`. -/
def HomotopyGroupsDetectDegree : Prop :=
  (d ≠ 0 ∧ Nontrivial (π_ 2 Q x)) ∨
    (∃ k : ℕ, (∀ j < k, Subsingleton (π_ (j + 3) Q x)) ∧ ∃ a : π_ (k + 3) Q x, a ^ d ≠ 1) ∨
    ∃ ℓ : ℕ, ∀ m : ℕ, 1 ≤ m → ∃ a : π_ (ℓ + 3) Q x, a ^ (d ^ m) ≠ 1

/-- The defining disjunction of `TauCeti.HomotopyGroupsDetectDegree`. -/
theorem homotopyGroupsDetectDegree_iff :
    HomotopyGroupsDetectDegree Q x d ↔
      (d ≠ 0 ∧ Nontrivial (π_ 2 Q x)) ∨
        (∃ k : ℕ, (∀ j < k, Subsingleton (π_ (j + 3) Q x)) ∧ ∃ a : π_ (k + 3) Q x, a ^ d ≠ 1) ∨
        ∃ ℓ : ℕ, ∀ m : ℕ, 1 ≤ m → ∃ a : π_ (ℓ + 3) Q x, a ^ (d ^ m) ≠ 1 :=
  Iff.rfl

namespace HomotopyGroupsDetectDegree

/-- A nontrivial `π₂(Q, x)` gives the alternatives for every `d ≠ 0`. -/
theorem of_nontrivial_two (hd : d ≠ 0) [Nontrivial (π_ 2 Q x)] :
    HomotopyGroupsDetectDegree Q x d :=
  Or.inl ⟨hd, ‹_›⟩

/-- An element `a` of the first possibly nontrivial group `π_{k+3}(Q, x)` above `π₂`, with
`a ^ d ≠ 1`, gives the alternatives. -/
theorem of_zpow_ne_one {k : ℕ} (hk : ∀ j < k, Subsingleton (π_ (j + 3) Q x))
    (a : π_ (k + 3) Q x) (ha : a ^ d ≠ 1) : HomotopyGroupsDetectDegree Q x d :=
  Or.inr (Or.inl ⟨k, hk, a, ha⟩)

/-- A group `π_{ℓ+3}(Q, x)` annihilated by no power `d ^ m`, `m ≥ 1`, gives the alternatives. -/
theorem of_forall_exists_zpow_pow_ne_one {ℓ : ℕ}
    (h : ∀ m : ℕ, 1 ≤ m → ∃ a : π_ (ℓ + 3) Q x, a ^ (d ^ m) ≠ 1) :
    HomotopyGroupsDetectDegree Q x d :=
  Or.inr (Or.inr ⟨ℓ, h⟩)

/-- Each alternative forces `d ≠ 0`. -/
theorem ne_zero (h : HomotopyGroupsDetectDegree Q x d) : d ≠ 0 := by
  rintro rfl
  rcases h with ⟨hd, -⟩ | ⟨k, -, a, ha⟩ | ⟨ℓ, hℓ⟩
  · exact hd rfl
  · exact ha (zpow_zero a)
  · obtain ⟨a, ha⟩ := hℓ 1 le_rfl
    exact ha (by rw [pow_one, zpow_zero])

/-- Under the alternatives some higher homotopy group `π_{j+2}(Q, x)` is nontrivial. -/
theorem exists_nontrivial (h : HomotopyGroupsDetectDegree Q x d) :
    ∃ j : ℕ, Nontrivial (π_ (j + 2) Q x) := by
  rcases h with ⟨-, h2⟩ | ⟨k, -, a, ha⟩ | ⟨ℓ, hℓ⟩
  · exact ⟨0, h2⟩
  · refine ⟨k + 1, nontrivial_of_ne a 1 fun h ↦ ha ?_⟩
    rw [h, one_zpow]
  · obtain ⟨a, ha⟩ := hℓ 1 le_rfl
    refine ⟨ℓ + 1, nontrivial_of_ne a 1 fun h ↦ ha ?_⟩
    rw [h, one_zpow]

/-- **A non-torsion higher homotopy group gives the alternatives.** If `d ≠ 0` and some
`π_{ℓ+2}(Q, x)` is not a torsion group, then the homotopy groups of `Q` detect `d`: either `ℓ = 0`
and `π₂(Q, x)` is nontrivial, or an element of infinite order of `π_{ℓ+2}(Q, x)` is killed by no
power of `d`. -/
theorem of_not_isMulTorsion (hd : d ≠ 0) {ℓ : ℕ} (h : ¬ IsMulTorsion (π_ (ℓ + 2) Q x)) :
    HomotopyGroupsDetectDegree Q x d := by
  obtain ⟨a, ha⟩ := (not_isMulTorsion_iff _).1 h
  -- An element of infinite order has no nonzero power equal to `1`.
  have hpow (n : ℤ) (hn : n ≠ 0) : a ^ n ≠ 1 := fun h ↦
    ha (isOfFinOrder_iff_zpow_eq_one.2 ⟨n, hn, h⟩)
  cases ℓ with
  | zero =>
    have : Nontrivial (π_ 2 Q x) :=
      nontrivial_of_ne a 1 fun h ↦ hpow 1 one_ne_zero (by rw [zpow_one, h])
    exact of_nontrivial_two hd
  | succ ℓ => exact of_forall_exists_zpow_pow_ne_one fun m _ ↦ ⟨a, hpow _ (pow_ne_zero m hd)⟩

end HomotopyGroupsDetectDegree

/-- **For `d = ±1` the alternatives say that a higher homotopy group is nontrivial.** If `d` is a
unit of `ℤ`, the homotopy groups of `Q` at `x` detect `d` exactly when some
`π_{j+2}(Q, x)` is nontrivial: the first such group has a nontrivial element `a`, and
`a ^ d ≠ 1`. -/
theorem homotopyGroupsDetectDegree_iff_exists_nontrivial (hd : IsUnit d) :
    HomotopyGroupsDetectDegree Q x d ↔ ∃ j : ℕ, Nontrivial (π_ (j + 2) Q x) := by
  refine ⟨HomotopyGroupsDetectDegree.exists_nontrivial, fun h ↦ ?_⟩
  classical
  -- Take the first nontrivial higher homotopy group.
  have hmin (m : ℕ) (hm : m < Nat.find h) : ¬ Nontrivial (π_ (m + 2) Q x) := Nat.find_min h hm
  cases hj : Nat.find h with
  | zero =>
    have := Nat.find_spec h
    rw [hj] at this
    exact .of_nontrivial_two hd.ne_zero
  | succ k =>
    have := Nat.find_spec h
    rw [hj] at this
    obtain ⟨a, ha⟩ := exists_ne (1 : π_ (k + 3) Q x)
    refine .of_zpow_ne_one (fun j hj' ↦ not_nontrivial_iff_subsingleton.1
      (hmin (j + 1) (by omega))) a ?_
    rcases Int.isUnit_iff.1 hd with rfl | rfl
    · rwa [zpow_one]
    · rwa [zpow_neg_one, ne_eq, inv_eq_one]

/-- **For `d = ±1` the alternatives say that `Q` is not aspherical** (the first case of Theorem A of
Barraud–Damian–Humilière–Oancea). For a path-connected `Q` and a unit `d` of `ℤ`, the homotopy
groups of `Q` at `x` detect `d` exactly when `Q` is not aspherical. -/
theorem homotopyGroupsDetectDegree_iff_not_isAspherical [PathConnectedSpace Q] (hd : IsUnit d) :
    HomotopyGroupsDetectDegree Q x d ↔ ¬ IsAspherical Q x := by
  simp only [homotopyGroupsDetectDegree_iff_exists_nontrivial hd, isAspherical_iff,
    not_and, not_forall, not_subsingleton_iff_nontrivial]
  exact ⟨fun h _ ↦ h, fun h ↦ h ‹_›⟩

end Predicate

section Kernel

variable {Q : Type} [TopologicalSpace Q] (x : Q) {d : ℤ}

/-- **Proposition 5.11 of Barraud–Damian–Humilière–Oancea, case `π₂(Q, x) ≠ 0`, not killed by
`d`.** If
`π₂(Q, x)` is nontrivial and `d ≠ 0`, the kernel of the map induced on `H₀(-; ℤ)` by the inclusion
`P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` has a class not killed by `d`. -/
theorem exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths_zero
    [Nontrivial (π_ 2 Q x)] (hd : d ≠ 0) :
    ∃ z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (BasedConstContractibleMoorePaths Q x)),
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))).hom z = 0 ∧
        d • z ≠ 0 := by
  obtain ⟨f, hf, hf0⟩ := exists_injective_singularHomology_basedConstContractibleMoorePaths_zero
    (R := ℤ) x
  refine ⟨f 1, hf0 1, fun h ↦ hd (hf ?_)⟩
  rw [map_zero, ← h, ← map_zsmul, smul_eq_mul, mul_one]

/-- **Proposition 5.11 of Barraud–Damian–Humilière–Oancea, case of a first nontrivial group
`π_{k+3}(Q, x)` above `π₂`, not killed by `d`.** If
`π_{j+2}(Q, x)` vanishes for `j ≤ k` and `a ∈ π_{k+3}(Q, x)` has `a ^ d ≠ 1`, the class of `a` in
`H_{k+1}(P_{⋆→Q} 𝓛₀Q; ℤ) ≅ π_{k+3}(Q, x)` lies in the kernel of the map induced by the inclusion
`P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` and is not killed by `d`. -/
theorem exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths_succ {k : ℕ}
    (hk : ∀ j ≤ k, Subsingleton (π_ (j + 2) Q x)) (a : π_ (k + 3) Q x) (ha : a ^ d ≠ 1) :
    ∃ z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (k + 1)).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (BasedConstContractibleMoorePaths Q x)),
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (k + 1)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))).hom z = 0 ∧
        d • z ≠ 0 := by
  let e := basedConstContractibleMoorePathsHomologyAddEquiv x k hk
  refine ⟨e (Additive.ofMul a), ?_, fun h ↦ ha ?_⟩
  · rw [singularHomologyMap_basedConstContractibleMoorePathsInclusion_succ_eq_zero]
    exact (LinearMap.congr_fun ModuleCat.hom_zero _).trans (LinearMap.zero_apply _)
  · -- `h` is stated on singular homology, `e` lands in the homology of the singular chains; the
    -- two carriers agree by definition (`TauCeti.singularHomologyFunctor_obj_obj`).
    have h' : e (d • Additive.ofMul a) = 0 := (map_zsmul e d _).trans h
    rwa [← ofMul_zpow, map_eq_zero_iff e e.injective, ofMul_eq_zero] at h'

namespace HomotopyGroupsDetectDegree

/-- **Proposition 5.11 of Barraud–Damian–Humilière–Oancea, on path spaces.** If the homotopy groups
of `Q` at `x` detect `d`, then the kernel of the map induced on integral homology by the
inclusion `P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` is not killed by `d`: in some degree `i` it has an
element `z` with `d • z ≠ 0`. -/
theorem exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths
    (h : HomotopyGroupsDetectDegree Q x d) :
    ∃ i, ∃ z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (BasedConstContractibleMoorePaths Q x)),
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))).hom z = 0 ∧
        d • z ≠ 0 := by
  obtain h2 | h2 := subsingleton_or_nontrivial (π_ 2 Q x)
  swap
  -- A nontrivial `π₂(Q, x)` gives the class in degree zero.
  · exact ⟨0, TauCeti.exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths_zero x
      h.ne_zero⟩
  -- Otherwise `Ω²Q` is path connected, and the second or third alternative holds.
  rcases h with ⟨-, h2'⟩ | ⟨k, hk, a, ha⟩ | ⟨ℓ, hℓ⟩
  · exact absurd h2' (not_nontrivial_iff_subsingleton.2 h2)
  · -- The first possibly nontrivial group above `π₂` is `π_{k+3}`, detected by Hurewicz.
    refine ⟨k + 1,
      TauCeti.exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths_succ x
        (fun j hj ↦ ?_) a ha⟩
    cases j with
    | zero => exact h2
    | succ j => exact hk j (by omega)
  · -- `π_{ℓ+3}` is annihilated by no power of `|d|`, so Hurewicz modulo that class applies.
    refine (TauCeti.exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths d.natAbs x
      (n := ℓ) fun hT ↦ ?_).imp fun i ⟨_, z, hz, hdz⟩ ↦ ⟨z, hz, fun h ↦ hdz ?_⟩
    · obtain ⟨n, hn⟩ := (AddCommGrpCat.prop_isKilledBySomePower_iff _ _).1 hT
      obtain ⟨a, ha⟩ := hℓ (n + 1) (Nat.le_add_left 1 n)
      -- `|d| ^ n` divides `d ^ (n + 1)`, so `d ^ (n + 1)` kills `π_{ℓ+3}` as well.
      obtain ⟨c, hc⟩ : ((d.natAbs : ℤ) ^ n) ∣ d ^ (n + 1) :=
        (pow_dvd_pow_of_dvd (Int.natAbs_dvd.2 dvd_rfl) n).trans (pow_dvd_pow d n.le_succ)
      refine ha (Additive.ofMul.injective ?_)
      simpa [ofMul_zpow, hc, mul_smul] using hn (c • Additive.ofMul a)
    · -- `d` and `|d|` kill the same elements.
      rcases Int.natAbs_eq d with hd | hd
      · rwa [← hd]
      · rw [hd] at h
        simpa using h

end HomotopyGroupsDetectDegree

/-- **The mod-two kernel of the inclusion of the constant loops is nonzero** (the topological input
to Theorem 5.15 of Barraud–Damian–Humilière–Oancea). If `π₂(Q, x)` is nontrivial, or squaring is
not surjective on some `π_{ℓ+3}(Q, x)`, then the kernel of the map induced on mod-two homology by
the inclusion `P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` is nonzero in some degree. -/
theorem exists_ne_zero_singularHomology_zmod_two_basedConstContractibleMoorePaths
    (h : Nontrivial (π_ 2 Q x) ∨
      ∃ ℓ : ℕ, ¬ Function.Surjective fun a : π_ (ℓ + 3) Q x ↦ a ^ 2) :
    ∃ i, ∃ z : ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) i).obj
        (ModuleCat.of (ZMod 2) (ZMod 2))).obj (TopCat.of (BasedConstContractibleMoorePaths Q x)),
      (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) i).obj
          (ModuleCat.of (ZMod 2) (ZMod 2))).map
          (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))).hom z = 0 ∧ z ≠ 0 := by
  -- Squaring not onto `π_{ℓ+3}` says that `π_{ℓ+3} ⊗ ℤ/2` is nonzero.
  have h' : Nontrivial (π_ 2 Q x) ∨ ∃ n, Nontrivial (Additive (π_ (n + 3) Q x) ⊗[ℤ] ZMod 2) :=
    h.imp_right fun ⟨ℓ, hℓ⟩ ↦ ⟨ℓ, not_subsingleton_iff_nontrivial.1 fun hs ↦ hℓ fun a ↦ by
      obtain ⟨b, hb⟩ := (subsingleton_tensorProduct_zmod_iff 2).1 hs (Additive.ofMul a)
      beta_reduce at hb ⊢
      exact ⟨b.toMul, by rw [← zpow_natCast, ← toMul_zsmul, hb, toMul_ofMul]⟩⟩
  obtain ⟨i, hi⟩ := exists_nontrivial_reducedSingularHomology_doubleLoopSpace x h'
  obtain ⟨w, hw⟩ := exists_ne (0 : (reducedSingularHomologyFunctor
    (ModuleCat.of (ZMod 2) (ZMod 2)) i).obj (TopCat.of (Ω (Ω Q x) (Path.refl x))))
  -- The kernel of the inclusion on `Hᵢ` contains `H~ᵢ(Ω²Q)`.
  obtain ⟨f, hf, hf0⟩ :=
    exists_injective_singularHomology_basedConstContractibleMoorePaths (R := ZMod 2) x i
  exact ⟨i, f w, hf0 w, (map_ne_zero_iff f hf).2 hw⟩

/-- **The mod-two kernel of the inclusion of the constant loops is nonzero** (the topological input
to Theorem C of Barraud–Damian–Humilière–Oancea). If squaring is not surjective on some higher
homotopy group `π_{ℓ+2}(Q, x)`, then the kernel of the map induced on mod-two homology by the
inclusion `P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` is nonzero in some degree. -/
theorem exists_ne_zero_singularHomology_zmod_two_basedConstContractibleMoorePaths_of_not_surjective
    {ℓ : ℕ} (h : ¬ Function.Surjective fun a : π_ (ℓ + 2) Q x ↦ a ^ 2) :
    ∃ i, ∃ z : ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) i).obj
        (ModuleCat.of (ZMod 2) (ZMod 2))).obj (TopCat.of (BasedConstContractibleMoorePaths Q x)),
      (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) i).obj
          (ModuleCat.of (ZMod 2) (ZMod 2))).map
          (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))).hom z = 0 ∧ z ≠ 0 := by
  refine exists_ne_zero_singularHomology_zmod_two_basedConstContractibleMoorePaths x ?_
  cases ℓ with
  | zero =>
    -- Squaring is onto a trivial group, so `π₂(Q, x)` is nontrivial.
    exact .inl (not_subsingleton_iff_nontrivial.1 fun _ ↦ h fun a ↦ ⟨a, Subsingleton.elim _ _⟩)
  | succ ℓ => exact .inr ⟨ℓ, h⟩

end Kernel

end TauCeti
