/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Finite kernels of maps of split-torus points

For an integral character map `φ`, the kernel of `TauCeti.torusPointMap φ` consists of the
points annihilating its image. If that image has finite index `c`, every coordinate of a kernel
point is a `c`-th root of unity. Consequently the kernel is finite over every integral domain,
without algebraic closure or a restriction on the characteristic. In particular this applies
to injective maps between character lattices of equal finite rank.

This supplies the torus part of finiteness of the kernel in comparisons of Chevalley groups
with different weight lattices. It concerns groups of points, not the order or reducedness of
the scheme-theoretic kernel: in characteristic two the squaring map has trivial kernel on
field-valued points although its group-scheme kernel is the nonreduced group `μ₂`.

The construction uses `TauCeti.torusCharacter_torusPointMap`, Mathlib's finite-index lattice
criterion `Submodule.finiteQuotientOfFreeOfRankEq`, and its finiteness of roots of unity.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28(c) and Corollary 5 to
  Theorem 4′ (comparison of weight lattices).
* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(b) (character cokernels and kernels
  of diagonalizable groups).
-/

public section

namespace TauCeti

variable {ι κ R : Type*} [Finite ι] [Fintype κ] [DecidableEq ι]
variable [CommRing R] (φ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ))

/-- Each coordinate of a kernel point is killed by the index of the character image. When
the index is zero this is the usual identity `s ^ 0 = 1`; the useful case is finite index. -/
theorem pow_index_eq_one_of_mem_ker_torusPointMap {s : κ → Rˣ}
    (hs : s ∈ (torusPointMap φ).ker) (j : κ) :
    s j ^ (LinearMap.range φ).toAddSubgroup.index = 1 := by
  classical
  obtain ⟨χ, hχ⟩ := (LinearMap.range φ).toAddSubgroup.nsmul_index_mem (Pi.single j 1)
  have h := (mem_ker_torusPointMap_iff φ s).mp hs χ
  rw [hχ, torusCharacter_nsmul, torusCharacter_single, zpow_one] at h
  exact h

/-- A finite character cokernel gives a finite kernel on points over an integral domain.
No separability or divisibility hypothesis on the units is needed. -/
theorem finite_ker_torusPointMap_of_finite_cokernel [IsDomain R]
    [Finite ((κ → ℤ) ⧸ LinearMap.range φ)] :
    Finite (torusPointMap (R := R) φ).ker := by
  let c := (LinearMap.range φ).toAddSubgroup.index
  have : Finite ((κ → ℤ) ⧸ (LinearMap.range φ).toAddSubgroup) :=
    ‹Finite ((κ → ℤ) ⧸ LinearMap.range φ)›
  have hc : c ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  let : NeZero c := ⟨hc⟩
  let f : (torusPointMap (R := R) φ).ker → (κ → rootsOfUnity c R) :=
    fun s j => ⟨s.val j, pow_index_eq_one_of_mem_ker_torusPointMap φ s.property j⟩
  exact Finite.of_injective f fun s t h => Subtype.ext <| funext fun j =>
    congrArg Subtype.val (congrFun h j)

/-- An injective character map between lattices of the same finite rank gives a finite
kernel on split-torus points over any integral domain. The map on points need not be
surjective over that domain. -/
theorem finite_ker_torusPointMap_of_injective [IsDomain R]
    (hφ : Function.Injective φ) (hrank : Nat.card ι = Nat.card κ) :
    Finite (torusPointMap (R := R) φ).ker := by
  let := Fintype.ofFinite ι
  have hr : Module.finrank ℤ (ι → ℤ) = Module.finrank ℤ (κ → ℤ) := by
    simpa only [Nat.card_eq_fintype_card, Module.finrank_pi, Module.finrank_self] using hrank
  have : Finite ((κ → ℤ) ⧸ LinearMap.range φ) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ ((LinearMap.finrank_range_of_inj hφ).trans hr)
  exact finite_ker_torusPointMap_of_finite_cokernel φ

end TauCeti
