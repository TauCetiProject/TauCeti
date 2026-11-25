/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanExists
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
import TauCeti.Algebra.Lie.Subalgebra.Engel

/-!
# A semisimple element lies in a Cartan subalgebra

Let `L` be a finite-dimensional Lie algebra over an infinite field. Mathlib proves that `L` has a
Cartan subalgebra, namely the Engel subalgebra of a regular element
(`LieAlgebra.exists_isCartanSubalgebra_engel`). This file proves that every element `x` with
semisimple adjoint action lies in some Cartan subalgebra
(`TauCeti.exists_isCartanSubalgebra_mem_of_isSemisimple_ad`).

The Cartan subalgebra is a Cartan subalgebra of the Engel subalgebra `engel K x`, viewed inside
`L`. This is the step that places the neutral element of an `sl₂` triple in a Cartan subalgebra.

Over an algebraically closed field of characteristic zero, when the Killing form of `L` is
nondegenerate, a Cartan subalgebra comes with a base of its root system
(`TauCeti.exists_isCartanSubalgebra_base`). This is the choice behind statements that mention
neither.

Mathlib's existence proof shows that the Engel subalgebra of an element that is regular in the
sense of `LieAlgebra.IsRegular` is a Cartan subalgebra, but records only the existence. This file
states it for every regular element (`LieAlgebra.IsRegular.isCartanSubalgebra_engel`), following
the same argument: the Engel subalgebra of a regular element has the minimal dimension
`LieAlgebra.rank K L`, so by Barnes's lemma `LieAlgebra.engel_isBot_of_isMin` it lies in the
Engel subalgebra of each of its elements, and is therefore nilpotent and self-normalizing.

## Main results

* `TauCeti.exists_isCartanSubalgebra_mem_of_isSemisimple_ad`: an element with semisimple adjoint
  action lies in a Cartan subalgebra.
* `TauCeti.exists_isCartanSubalgebra_base`: a Lie algebra with nondegenerate Killing form has a
  Cartan subalgebra whose root system has a base.
* `LieAlgebra.IsRegular.isCartanSubalgebra_engel_of_finrank_le_card` and
  `LieAlgebra.IsRegular.isCartanSubalgebra_engel`: the Engel subalgebra of a regular element is a
  Cartan subalgebra.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Springer GTM 9
  (1972), §15.
* D. W. Barnes, *On Cartan subalgebras of Lie algebras*, Math. Z. **101** (1967), 350–355.
-/

public section

open LieAlgebra LieSubalgebra Module

namespace TauCeti

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- **A semisimple element lies in a Cartan subalgebra.** In a finite-dimensional Lie algebra over
an infinite field, an element whose adjoint action is semisimple lies in some Cartan
subalgebra. -/
theorem exists_isCartanSubalgebra_mem_of_isSemisimple_ad [Infinite K] [FiniteDimensional K L]
    {x : L} (hx : (ad K L x).IsSemisimple) :
    ∃ H : LieSubalgebra K L, H.IsCartanSubalgebra ∧ x ∈ H := by
  -- take a Cartan subalgebra `C` of `E = engel K x`; it contains `x`, which is central in `E`, and
  -- an element normalizing `C` in `L` lies in `E`, so `C` is self-normalizing in `L`
  let E := engel K x
  obtain ⟨y, hy⟩ := exists_isCartanSubalgebra_engel K E
  let C : LieSubalgebra K E := engel K y
  have hinj : Function.Injective E.incl := Subtype.val_injective
  have hC : C.IsCartanSubalgebra := hy
  have hmemC {w : E} : (w : L) ∈ C.map E.incl ↔ w ∈ C := by
    refine ⟨fun h ↦ ?_, fun h ↦ (C.mem_map E.incl _).mpr ⟨w, h, rfl⟩⟩
    obtain ⟨w', hw', hw⟩ := (C.mem_map E.incl _).mp h
    rwa [← hinj hw]
  -- `x` is central in its Engel subalgebra, because the generalized kernel of `ad x` is its kernel
  have hxE : x ∈ E := self_mem_engel K x
  have hcentral (w : E) : ⁅(⟨x, hxE⟩ : E), w⁆ = 0 :=
    Subtype.ext ((mem_engel_iff_lie_eq_zero hx.isFinitelySemisimple).1 w.property)
  have hxC : (⟨x, hxE⟩ : E) ∈ C := by
    rw [← hC.self_normalizing, mem_normalizer_iff]
    intro w _
    simp [hcentral w]
  refine ⟨C.map E.incl, ⟨?_, ?_⟩, hmemC.mpr hxC⟩
  · exact (LieSubalgebra.equivMapOfInjective E.incl C hinj).nilpotent_iff_equiv_nilpotent.mp
      hC.nilpotent
  · refine le_antisymm (fun z hz ↦ ?_) (le_normalizer _)
    -- a normalizing element lies in `E`: `⁅x, z⁆ ∈ E`, so a power of `ad x` kills `z`
    have hxz : ⁅x, z⁆ ∈ C.map E.incl :=
      (mem_normalizer_iff' (C.map E.incl) z).mp hz x (hmemC.mpr hxC)
    have hzE : z ∈ E := by
      obtain ⟨w, -, hw⟩ := (C.mem_map E.incl _).mp hxz
      obtain ⟨n, hn⟩ := (mem_engel_iff K x w).mp w.property
      refine (mem_engel_iff K x z).mpr ⟨n + 1, ?_⟩
      rw [pow_succ, mul_apply_eq_comp, ad_apply, ← hw]
      simpa using hn
    -- and it normalizes `C` inside `E`
    refine (hmemC (w := ⟨z, hzE⟩)).mpr ?_
    rw [← hC.self_normalizing, mem_normalizer_iff]
    intro w hw
    refine hmemC.mp ?_
    rw [LieSubalgebra.coe_bracket]
    exact (mem_normalizer_iff (C.map E.incl) z).mp hz w (hmemC.mpr hw)

variable (K L) in
/-- **A Cartan subalgebra with a base of its root system.** A finite-dimensional Lie algebra with
nondegenerate Killing form over an algebraically closed field of characteristic zero has a Cartan
subalgebra, and the root system of a Cartan subalgebra has a base. -/
theorem exists_isCartanSubalgebra_base [CharZero K] [IsAlgClosed K] [FiniteDimensional K L]
    [IsKilling K L] :
    ∃ (H : LieSubalgebra K L) (_ : H.IsCartanSubalgebra),
      Nonempty (IsKilling.rootSystem H).Base := by
  obtain ⟨x₀, hx₀⟩ := exists_isCartanSubalgebra_engel K L
  have _i : (engel K x₀).IsCartanSubalgebra := hx₀
  exact ⟨_, _i, (IsKilling.rootSystem _).nonempty_base⟩

end TauCeti

namespace LieAlgebra

open Cardinal

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] {x : L}

/-- **The Engel subalgebra of a regular element is a Cartan subalgebra**, over a field with at
least `finrank K L` elements: if `x` is regular in Mathlib's sense, then `engel K x` is a Cartan
subalgebra of `L`. -/
theorem IsRegular.isCartanSubalgebra_engel_of_finrank_le_card (hx : IsRegular K x)
    (hLK : finrank K L ≤ #K) : (engel K x).IsCartanSubalgebra := by
  refine ⟨isNilpotent_of_forall_le_engel _ fun y hy ↦ ?_, normalizer_engel _ _⟩
  -- `engel K x` is minimal among the Engel subalgebras of its elements, hence the least of them
  let Ex : {engel K z | z ∈ engel K x} := ⟨engel K x, x, self_mem_engel _ _, rfl⟩
  suffices IsBot Ex from this ⟨engel K y, y, hy, rfl⟩
  refine engel_isBot_of_isMin hLK (engel K x) Ex le_rfl ?_
  rintro ⟨_, y, _, rfl⟩ hyx
  -- an Engel subalgebra inside `engel K x` has dimension at least `rank K L`, so it is equal
  suffices finrank K (engel K x) ≤ finrank K (engel K y) from
    (LieSubalgebra.toSubmodule_injective (Submodule.eq_of_le_of_finrank_le hyx this)).ge
  rw [(isRegular_iff_finrank_engel_eq_rank K x).mp hx]
  exact rank_le_finrank_engel K y

/-- **The Engel subalgebra of a regular element is a Cartan subalgebra**, over an infinite
field. -/
theorem IsRegular.isCartanSubalgebra_engel [Infinite K] (hx : IsRegular K x) :
    (engel K x).IsCartanSubalgebra :=
  hx.isCartanSubalgebra_engel_of_finrank_le_card <|
    natCast_le_aleph0.trans <| Cardinal.infinite_iff.mp ‹Infinite K›

end LieAlgebra
