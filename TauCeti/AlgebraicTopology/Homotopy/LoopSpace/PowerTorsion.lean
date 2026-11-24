/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.PowerTorsion
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ConstantLoopKernel
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.SerreClass
import TauCeti.AlgebraicTopology.PathComponent

/-!
# Homotopy groups annihilated by a power of `d`, from the double loop space

Let `d` be a natural number and `(X, x)` a pointed space. This file proves the third case of
Proposition 5.11 of Barraud–Damian–Humilière–Oancea on the double loop space `Ω²X` and on the path
spaces of the constant loops: if some homotopy group `π_ℓ(X, x)`, `ℓ ≥ 3`, is annihilated by no
power `dᵐ`, then the reduced integral homology `H~_*(Ω²X; ℤ)` has a class not killed by `d`.

The source assumes `π₂(X, x) = 0`; the statements here do not. When `π₂(X, x)` is nontrivial, the
reduced zeroth homology `H~₀(Ω²X; ℤ)` contains a copy of `ℤ`
(`TauCeti.exists_injective_doubleLoopSpaceReducedHomology₀`), and a group annihilated by no power
of `d` forces `d ≠ 0`, so `d` does not kill that copy. When `π₂(X, x)` is trivial, the proof is
the source's, with its spectral-sequence step replaced by the comparison theorem modulo a Serre
class.

* If `d` kills `Hq(Ω²X; ℤ)` for `1 ≤ q ≤ k`, then some power of `d` kills `Hk(Ω₀X; ℤ)`, where
  `Ω₀X` is the path component of the constant loop in `Ω X x`
  (`TauCeti.exists_pow_smul_eq_zero_singularHomology_pathComponent_refl`).
* The space `Ω₀X` is simply connected, since its fundamental group is `π₂(X, x)`. By Serre's
  Hurewicz theorem modulo the groups annihilated by a power of `d`
  (`TauCeti.isKilledBySomePower_homotopyGroup_of_isKilledBySomePower_singularHomology`), its
  homotopy groups `πₙ₊₂(Ω₀X) ≅ πₙ₊₃(X, x)` are annihilated by powers of `d`
  (`TauCeti.isKilledBySomePower_homotopyGroup_of_smul_eq_zero_singularHomology_doubleLoopSpace`).

Here, as in the source, "annihilated by a power of `d`" is a property of the whole group,
`∃ m, dᵐ • G = 0`, not of each element separately. The elementwise analogue is
`TauCeti.exists_not_isTorsion'_reducedSingularHomology_doubleLoopSpace`; the two differ for
groups that are not finitely generated, such as `⨁ₘ ℤ/dᵐ`.

The source identifies the kernel of the map `i_{Q*}` induced by the constant loops, for the DG
local system of the path fibration of `𝓛₀Q`, with the kernel of the inclusion of path spaces
`P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` on homology, through the fibration theorem of DG Morse homology.
That identification is not formalized here. The kernel of the inclusion of path spaces is
`H~_*(Ω²Q)` (`TauCeti.kernelBasedConstContractibleMoorePathsInclusionIso`), and the third case is
proved for it (`TauCeti.exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths`).
The first two cases are in `TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ConstantLoopKernel`.

## Main results

* `TauCeti.isKilledBySomePower_homotopyGroup_of_smul_eq_zero_singularHomology_doubleLoopSpace`:
  if `π₂(X, x)` is trivial and `d` kills `Hq(Ω²X; ℤ)` for `1 ≤ q ≤ n + 2`, then `πₙ₊₃(X, x)` is
  annihilated by a power of `d`.
* `TauCeti.exists_smul_ne_zero_reducedSingularHomology_doubleLoopSpace`: if `πₙ₊₃(X, x)` is
  annihilated by no power of `d`, then `d` does not kill `H~ᵢ(Ω²X; ℤ)` for some `i ≤ n + 2`.
* `TauCeti.exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths`: **Proposition
  5.11, third case, on path spaces.** Under the same hypothesis, the kernel of the inclusion
  `P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` on integral homology has an element not killed by `d`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11 and its proof.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Theorem 1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

namespace TauCeti

variable {X : Type} [TopologicalSpace X] (x : X) (d : ℕ)

/-- **Homotopy groups annihilated by a power of `d`, from the double loop space.** If `π₂(X, x)` is
trivial and `d` kills the integral homology `Hq(Ω²X; ℤ)` of the double loop space for
`1 ≤ q ≤ n + 2`, then the homotopy group `πₙ₊₃(X, x)` is annihilated by some power of `d`. -/
theorem isKilledBySomePower_homotopyGroup_of_smul_eq_zero_singularHomology_doubleLoopSpace
    [Subsingleton (π_ 2 X x)] {n : ℕ}
    (hΩ : ∀ q, q ≠ 0 → q ≤ n + 2 → ∀ z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Ω (Ω X x) (Path.refl x))), (d : ℤ) • z = 0) :
    AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of (Additive (π_ (n + 3) X x))) := by
  -- The contractible loops `Ω₀X` are simply connected: their fundamental group is `π₂(X, x)`.
  let y : pathComponent (Path.refl x) := ⟨Path.refl x, mem_pathComponent_self _⟩
  have : Subsingleton (FundamentalGroup (Ω X x) (Path.refl x)) :=
    HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv.toEquiv.subsingleton_congr.2 ‹_›
  have : SimplyConnectedSpace (pathComponent (Path.refl x)) :=
    (simplyConnectedSpace_pathComponent_iff (Path.refl x)).2 ‹_›
  -- A power of `d` kills `Hᵢ(Ω₀X; ℤ)` for `1 ≤ i ≤ n + 2`, so it kills `πₙ₊₂(Ω₀X)` by Hurewicz.
  have hπ := isKilledBySomePower_homotopyGroup_of_isKilledBySomePower_singularHomology
    (d := d) (k := n + 2) (fun i hi0 hik ↦ (AddCommGrpCat.prop_isKilledBySomePower_iff _ _).2 <|
      exists_pow_smul_eq_zero_singularHomology_pathComponent_refl x ‹_› d hi0
        fun q hq hqi ↦ hΩ q hq (hqi.trans hik)) y le_rfl
  -- And `πₙ₊₂(Ω₀X) ≅ πₙ₊₂(Ω X x) ≅ πₙ₊₃(X, x)`.
  let e : π_ (n + 2) (pathComponent (Path.refl x)) y ≃* π_ (n + 3) X x :=
    (HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      (HomotopyGroup.pathLoopSpaceMulEquiv (n + 1))
  exact (AddCommGrpCat.isKilledBySomePower d).prop_of_iso e.toAdditive.toAddCommGrpIso hπ

/-- **The reduced homology of the double loop space is not killed by `d`.** If the homotopy group
`πₙ₊₃(X, x)` is annihilated by no power of `d`, then some reduced integral homology group
`H~ᵢ(Ω²X; ℤ)`, `i ≤ n + 2`, has a class not killed by `d`. No assumption on `π₂(X, x)` is
needed. -/
theorem exists_smul_ne_zero_reducedSingularHomology_doubleLoopSpace {n : ℕ}
    (h : ¬ AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of (Additive (π_ (n + 3) X x)))) :
    ∃ i ≤ n + 2, ∃ z : (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) i).obj
      (TopCat.of (Ω (Ω X x) (Path.refl x))), (d : ℤ) • z ≠ 0 := by
  by_contra! hT
  rcases subsingleton_or_nontrivial (π_ 2 X x) with h2 | h2
  · -- In positive degrees reduced and ordinary homology agree.
    refine h (isKilledBySomePower_homotopyGroup_of_smul_eq_zero_singularHomology_doubleLoopSpace
      x d fun q hq0 hq z ↦ ?_)
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    let e := ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) i).app
      (TopCat.of (Ω (Ω X x) (Path.refl x)))).toLinearEquiv
    simpa using congrArg e (hT (i + 1) hq (e.symm z))
  · -- `H~₀(Ω²X; ℤ)` contains a copy of `ℤ`, so `d = 0`, and then `d` kills every group.
    obtain ⟨f, hf⟩ := exists_injective_doubleLoopSpaceReducedHomology₀ (R := ℤ) x
    have hd : (d : ℤ) = 0 := hf <| by
      simpa [← map_zsmul] using hT 0 (Nat.zero_le _) (f 1)
    exact h ((AddCommGrpCat.prop_isKilledBySomePower_iff _ _).2 ⟨1, fun z ↦ by simp [hd]⟩)

/-- **Proposition 5.11 of Barraud–Damian–Humilière–Oancea, third case, on path spaces.** If the
homotopy group `πₙ₊₃(Q, x)` is annihilated by no power of `d`, then the kernel of the map induced
on integral homology by the inclusion `P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` is not killed by `d`: in some
degree `i ≤ n + 2` it has an element `z` with `d • z ≠ 0`. -/
theorem exists_smul_ne_zero_singularHomology_basedConstContractibleMoorePaths {Q : Type}
    [TopologicalSpace Q] (x : Q) {n : ℕ}
    (h : ¬ AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of (Additive (π_ (n + 3) Q x)))) :
    ∃ i ≤ n + 2, ∃ z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (BasedConstContractibleMoorePaths Q x)),
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))).hom z = 0 ∧
        (d : ℤ) • z ≠ 0 := by
  obtain ⟨i, hi, w, hw⟩ := exists_smul_ne_zero_reducedSingularHomology_doubleLoopSpace x d h
  -- The kernel of the inclusion on `Hᵢ` contains `H~ᵢ(Ω²Q)`.
  obtain ⟨f, hf, hf0⟩ :=
    exists_injective_singularHomology_basedConstContractibleMoorePaths (R := ℤ) x i
  refine ⟨i, hi, f w, hf0 w, fun hz ↦ hw (hf ?_)⟩
  rw [map_zsmul, hz, map_zero]

end TauCeti
