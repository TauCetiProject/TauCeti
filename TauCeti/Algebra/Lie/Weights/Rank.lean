/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Rank
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Base
import TauCeti.Algebra.Lie.AdjointAction.RootExponential
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.Subalgebra.Engel
import TauCeti.Algebra.Lie.Weights.Dimension

/-!
# The rank of a Lie algebra and the dimension of a Cartan subalgebra

Let `L` be a finite-dimensional Lie algebra over an infinite field, and let `H` be a Cartan
subalgebra whose action on `L` is triangularizable with linear weights. This file chooses an
element `h : H` on which no root vanishes and proves that its Engel subalgebra is exactly `H`.
Mathlib's lower bound on the dimension of each Engel subalgebra then gives

`LieAlgebra.rank K L ≤ Module.finrank K H`.

The construction has two ingredients. First, finitely many nonzero linear functionals cannot
cover a vector space over an infinite field, so there is an `h` outside every root hyperplane.
Second, the generalized Cartan weight spaces span `L`. The generalized zero eigenspace of `ad h`
therefore receives only the zero weight space: every nonzero weight is a root, and its value at `h`
is nonzero by construction. The zero root space is the Cartan subalgebra.

When the Killing form is non-degenerate and the characteristic is zero the two numbers are equal.
The coefficient of index `LieAlgebra.rank K L` of the characteristic polynomial of `ad x` is a
nonzero polynomial function of `x` that is invariant under inner automorphisms, and the conjugates
of `H` under inner automorphisms are Zariski dense
(`LieSubalgebra.polynomial_eq_zero_of_intCartan`). So this coefficient is nonzero at some element
of `H`, whereas for `h ∈ H` the characteristic polynomial of `ad h` is divisible by
`X ^ finrank K H`.

The equality turns quantities phrased through the rank into root-system data: the exponents
`(dim L ± rank L) / 2` in Kostant's description of the Clifford algebra of the Killing form are
exact divisions by the parity identity `dim L = rank L + 2 · #Δ⁺`.

## Main results

* `LieSubalgebra.exists_forall_root_apply_ne_zero`: some element of `H` is nonzero under every root.
* `LieSubalgebra.engel_eq_cartan_iff_forall_root_apply_ne_zero`: an element has Engel
  subalgebra `H` exactly when every root is nonzero on it.
* `LieSubalgebra.exists_engel_eq_cartan`: a Cartan subalgebra is the Engel subalgebra of one of its
  elements.
* `LieSubalgebra.rank_le_finrank_cartan`: the rank of `L` is at most the dimension of `H`.
* `LieSubalgebra.engel_eq_cartan_of_isRegular`: a regular element of `H` has Engel subalgebra `H`.
* `LieSubalgebra.engel_eq_map_of_isRegular`: if the image `e h` of `h ∈ H` under an automorphism
  `e` is regular, then its Engel subalgebra is `e H`.
* `LieSubalgebra.rank_eq_finrank_cartan`: for non-degenerate Killing form in characteristic zero,
  the rank of `L` is the dimension of every splitting Cartan subalgebra.
* `LieSubalgebra.finrank_eq_rank_add_two_mul_card_isPos`: the parity identity
  `dim L = rank L + 2 · #Δ⁺`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Springer GTM 9
  (1972), §15.1--15.3, and §23.1 for the density of the conjugates of a Cartan subalgebra.
* B. Kostant, *Clifford algebra analogue of the Hopf-Koszul-Samelson theorem, the ρ-decomposition
  C(g) = End V_ρ ⊗ C(P), and the g-module structure of ⋀g*, Adv. Math. 125 (1997).
-/

public section

namespace LieSubalgebra

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-- **A generic element of a Cartan subalgebra avoids every root hyperplane.** Since the root set
is finite and each root is a nonzero linear functional, finite hyperplane avoidance over the
infinite field `K` supplies one `h : H` on which every root is nonzero. -/
theorem exists_forall_root_apply_ne_zero [Infinite K] [LieModule.LinearWeights K H L] :
    ∃ h : H, ∀ α ∈ H.root, (α : H → K) h ≠ 0 := by
  let f : H.root → Module.Dual K H := fun α ↦ (α.1 : H →ₗ[K] K)
  obtain ⟨h, hh⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f fun α ↦ by
    simpa [f] using DFunLike.ne_iff.mp
      (Weight.coe_toLinear_ne_zero_iff.mpr (H.isNonZero_coe_root α))
  exact ⟨h, fun α hα ↦ hh ⟨α, hα⟩⟩

/-- An element of a Cartan subalgebra has Engel subalgebra equal to the Cartan subalgebra
if and only if no root vanishes on it. The Cartan action is assumed triangularizable. -/
theorem engel_eq_cartan_iff_forall_root_apply_ne_zero {h : H}
    [LieModule.IsTriangularizable K H L] :
    LieSubalgebra.engel K (h : L) = H ↔ ∀ α ∈ H.root, (α : H → K) h ≠ 0 := by
  let N : LieSubmodule K H L := genWeightSpaceOf L 0 h
  have hEngel : (LieSubalgebra.engel K (h : L)).toSubmodule = N.toSubmodule := by
    ext x
    rw [LieSubalgebra.mem_toSubmodule, LieSubmodule.mem_toSubmodule,
      LieSubalgebra.mem_engel_iff, LieModule.mem_genWeightSpaceOf]
    simp only [zero_smul, sub_zero, LieAlgebra.ad, LieSubalgebra.toEnd_eq]
  rw [← LieSubalgebra.toSubmodule_inj, hEngel, ← H.coe_toLieSubmodule,
    LieSubmodule.toSubmodule_inj, ← rootSpace_zero_eq K L H]
  constructor
  · intro hN χ hχ hχh
    have hle : genWeightSpace L χ ≤ rootSpace H 0 := by
      rw [← hN]
      simpa only [hχh] using genWeightSpace_le_genWeightSpaceOf L h χ
    have hdisj : Disjoint (genWeightSpace L χ) (rootSpace H 0) :=
      disjoint_genWeightSpace K H L (H.isNonZero_coe_root ⟨χ, hχ⟩)
    exact χ.genWeightSpace_ne_bot L (disjoint_self.mp (hdisj.mono_right hle))
  · intro hh
    refine le_antisymm ?_ (genWeightSpace_le_genWeightSpaceOf L h 0)
    rw [eq_iSup_inf_genWeightSpace K H L N]
    refine iSup_le fun χ ↦ ?_
    by_cases hχ : χ.IsZero
    · rw [hχ.eq]
      exact inf_le_right
    · have hχroot : χ ∈ H.root := by
        simpa [LieSubalgebra.root] using hχ
      have hχh : χ h ≠ 0 := hh χ hχroot
      have hdisj : Disjoint N (genWeightSpace L χ) :=
        (disjoint_genWeightSpaceOf K H L hχh.symm).mono_right
          (genWeightSpace_le_genWeightSpaceOf L h χ)
      simp [hdisj.eq_bot]

/-- **Every Cartan subalgebra is the Engel subalgebra of one of its elements** when its action has
linear weights and is triangularizable over an infinite field. -/
theorem exists_engel_eq_cartan [Infinite K] [LieModule.LinearWeights K H L]
    [LieModule.IsTriangularizable K H L] :
    ∃ h : H, LieSubalgebra.engel K (h : L) = H := by
  obtain ⟨h, hh⟩ := exists_forall_root_apply_ne_zero H
  exact ⟨h, (H.engel_eq_cartan_iff_forall_root_apply_ne_zero).mpr hh⟩

/-- **The rank is at most the dimension of a Cartan subalgebra.** Choose a root-regular Cartan
element whose Engel subalgebra is `H`, then apply Mathlib's Engel-subalgebra dimension bound
`LieAlgebra.rank_le_finrank_engel`. -/
theorem rank_le_finrank_cartan [Infinite K] [LieModule.LinearWeights K H L]
    [LieModule.IsTriangularizable K H L] :
    LieAlgebra.rank K L ≤ finrank K H := by
  obtain ⟨h, hh⟩ := exists_engel_eq_cartan H
  rw [← hh]
  exact LieAlgebra.rank_le_finrank_engel K (h : L)

/-- **A regular element of a Cartan subalgebra has Engel subalgebra equal to it.** If `h ∈ H` is
regular in `L`, in the sense of `LieAlgebra.IsRegular`, then the Engel subalgebra of `h` is `H`. -/
theorem engel_eq_cartan_of_isRegular [Infinite K] [LieModule.LinearWeights K H L]
    [LieModule.IsTriangularizable K H L] {h : H} (hh : LieAlgebra.IsRegular K (h : L)) :
    LieSubalgebra.engel K (h : L) = H := by
  refine (LieSubalgebra.toSubmodule_injective
    (Submodule.eq_of_le_of_finrank_le (H.le_engel_of_isNilpotent h) ?_)).symm
  exact ((LieAlgebra.isRegular_iff_finrank_engel_eq_rank K _).mp hh).trans_le
    (rank_le_finrank_cartan H)

/-- **Transport of Cartan subalgebras along regular elements.** If the image `e h` of an element
`h` of a Cartan subalgebra `H` under a Lie algebra automorphism `e` is regular, then its Engel
subalgebra is `e H`. -/
theorem engel_eq_map_of_isRegular [Infinite K] [LieModule.LinearWeights K H L]
    [LieModule.IsTriangularizable K H L] (e : L ≃ₗ⁅K⁆ L) {h : L} (hh : h ∈ H)
    (hx : LieAlgebra.IsRegular K (e h)) :
    LieSubalgebra.engel K (e h) = H.map e.toLieHom := by
  rw [LieAlgebra.isRegular_iff_finrank_engel_eq_rank, ← e.map_engel] at hx
  -- `h` is regular too: its Engel subalgebra is isomorphic to that of `e h`
  have hreg : LieAlgebra.IsRegular K ((⟨h, hh⟩ : H) : L) := by
    rw [LieAlgebra.isRegular_iff_finrank_engel_eq_rank, ← hx]
    exact (LieSubalgebra.equivMapOfInjective _ _ e.injective).toLinearEquiv.finrank_eq
  rw [← e.map_engel, engel_eq_cartan_of_isRegular H hreg]

/-- **The dimension of a splitting Cartan subalgebra is at most the rank**, for a Lie algebra with
non-degenerate Killing form over a field of characteristic zero. This is the converse of
`LieSubalgebra.rank_le_finrank_cartan`. -/
theorem finrank_cartan_le_rank [CharZero K] [IsKilling K L] [LieModule.IsTriangularizable K H L] :
    finrank K H ≤ LieAlgebra.rank K L := by
  classical
  let _ := TauCeti.ratLieAlgebra K L
  by_contra! hlt
  -- The rank coefficient of the characteristic polynomial would vanish on all conjugates of `H`.
  let b := finBasis K L
  refine polyCharpoly_coeff_rank_ne_zero K L b <|
    H.polynomial_eq_zero_of_intCartan b fun g hg h hh ↦ ?_
  have hH : finrank K H ≤ (ad K L h).charpoly.natTrailingDegree :=
    (Submodule.finrank_mono (LieSubalgebra.toSubmodule_le_toSubmodule _ _ |>.mpr
      (H.le_engel_of_isNilpotent ⟨h, hh⟩))).trans_eq (finrank_engel K h)
  have hconj : (ad K L (g • h)).charpoly = (ad K L h).charpoly := by
    rw [← TauCeti.intLieAlgebraLieEquiv_apply ⟨g, hg⟩, ← conj_ad_apply, LinearEquiv.charpoly_conj]
  rw [Module.Basis.equivFun_apply, LinearMap.polyCharpoly_coeff_eval]
  simp only [LieHom.coe_toLinearMap, hconj]
  exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hlt.trans_le hH)

/-- **The rank is the dimension of a splitting Cartan subalgebra.** For a Lie algebra with
non-degenerate Killing form over a field of characteristic zero, `LieAlgebra.rank K L`, which is
defined through the characteristic polynomial of a generic `ad x`, equals `finrank K H` for every
splitting Cartan subalgebra `H`. In particular all such `H` have the same dimension. -/
theorem rank_eq_finrank_cartan [CharZero K] [IsKilling K L] [LieModule.IsTriangularizable K H L] :
    LieAlgebra.rank K L = finrank K H :=
  (H.rank_le_finrank_cartan).antisymm H.finrank_cartan_le_rank

/-- **The parity identity `d = l + 2 · #Δ⁺` in terms of the rank.** It makes the divisions in the
exponents `(dim L ± rank L) / 2` exact. -/
theorem finrank_eq_rank_add_two_mul_card_isPos [CharZero K] [IsKilling K L]
    [LieModule.IsTriangularizable K H L] (b : (IsKilling.rootSystem H).Base)
    [DecidablePred b.IsPos] :
    finrank K L
      = LieAlgebra.rank K L + 2 * (Finset.univ.filter fun i : H.root ↦ b.IsPos i).card := by
  rw [H.rank_eq_finrank_cartan]
  exact TauCeti.finrank_eq_finrank_cartan_add_two_mul_card_isPos H b

end LieSubalgebra
