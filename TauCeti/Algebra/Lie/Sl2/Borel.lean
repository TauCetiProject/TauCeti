/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
public import TauCeti.Algebra.Lie.Weights.Borel
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Sl2.Spectrum
import TauCeti.LinearAlgebra.Eigenspace.Semisimple
import TauCeti.LinearAlgebra.RootSystem.IntegralCoweight

/-!
# Every nilpotent element lies in a Borel nilradical

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over an algebraically
closed field `K` of characteristic zero. This file proves that every `ad`-nilpotent element `e` of
`L` lies in the positive nilradical `n⁺` of some splitting Cartan subalgebra `H` and some base `b`
of its root system (`TauCeti.exists_mem_positiveNilradical_of_isNilpotent_ad`). In other words,
every nilpotent element lies in the nilradical `n⁺` of some Borel subalgebra `𝔟 = H ⊕ n⁺`.

The proof goes through the `sl₂` triple `(h, e, f)` of the Jacobson–Morozov theorem.

* The neutral element `h` acts diagonalizably on `L`, so `ad h` is semisimple and `h` lies in a
  Cartan subalgebra `H` (`TauCeti.exists_isCartanSubalgebra_mem_of_isSemisimple_ad`).
* Every root of `H` takes an integer value at `h`, since it is an eigenvalue of `ad h`
  (`IsSl2Triple.exists_int_weight_apply`), so some base `b` makes `h` dominant
  (`RootPairing.exists_base_forall_exists_nat_root'_apply`).
* The nilpositive element `e` is an eigenvector of `ad h` with eigenvalue `2`. An eigenvector of a
  dominant element with positive eigenvalue lies in `n⁺`
  (`TauCeti.mem_positiveNilradical_of_mem_genWeightSpaceOf`), so `e ∈ n⁺`
  (`IsSl2Triple.exists_base_mem_positiveNilradical`).

The second and third steps work over any field of characteristic zero, for a splitting Cartan
subalgebra that happens to contain `h`; algebraic closure is used only to know that every Cartan
subalgebra splits.

## Main results

* `IsSl2Triple.exists_int_weight_apply`: the weights of a nilpotent subalgebra containing the
  neutral element `h` on a finite-dimensional module take integer values at `h`; in particular so
  do the roots of a Cartan subalgebra containing `h`.
* `IsSl2Triple.exists_base_mem_positiveNilradical`: such a Cartan subalgebra has a base making `h`
  dominant, and the nilpositive element lies in the positive nilradical of that base.
* `TauCeti.exists_mem_positiveNilradical_of_isNilpotent_ad`: over an algebraically closed field,
  every `ad`-nilpotent element lies in the positive nilradical of some Cartan subalgebra and base.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.2 and §3.5.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 7–9, Chapter VIII, §11.
-/

public section

open LieAlgebra LieModule LieAlgebra.IsKilling Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

namespace IsSl2Triple

/-- **The weights take integer values at a neutral element.** If the neutral element `h` of an
`sl₂` triple lies in a nilpotent subalgebra `H`, then every weight of `H` on a finite-dimensional
`L`-module takes an integer value at `h`: that value is an eigenvalue of `h`. -/
theorem exists_int_weight_apply {H : LieSubalgebra K L} [LieRing.IsNilpotent H] {M : Type*}
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
    {h : H} {e f : L} (t : IsSl2Triple (h : L) e f) (α : Weight K H M) : ∃ z : ℤ, α h = z := by
  obtain ⟨y, hy, hy0⟩ := α.exists_ne_zero
  obtain ⟨k, hk⟩ := (mem_genWeightSpaceOf M (α h) h y).mp
    (genWeightSpace_le_genWeightSpaceOf M h α hy)
  refine TauCeti.exists_int_of_hasEigenvalue (M := M) t
    (Module.End.hasEigenvalue_of_hasGenEigenvalue (k := k) ?_)
  rw [Module.End.hasGenEigenvalue_iff, Submodule.ne_bot_iff]
  exact ⟨y, Module.End.mem_genEigenspace_nat.mpr hk, hy0⟩

variable [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- **A base making the neutral element dominant.** If the neutral element `h` of an `sl₂` triple
`(h, e, f)` lies in a splitting Cartan subalgebra `H`, then some base `b` of the root system of
`H` makes `h` dominant, and the nilpositive element `e` lies in the positive nilradical of `b`. -/
theorem exists_base_mem_positiveNilradical {h : H} {e f : L} (t : IsSl2Triple (h : L) e f) :
    ∃ b : (rootSystem H).Base, (∀ i ∈ b.support, ∃ n : ℕ, (i : Weight K H L) h = n) ∧
      e ∈ TauCeti.positiveNilradical H b := by
  obtain ⟨b, hb⟩ := (rootSystem H).exists_base_forall_exists_nat_root'_apply h
    fun i ↦ t.exists_int_weight_apply (i : Weight K H L)
  refine ⟨b, hb, TauCeti.mem_positiveNilradical_of_mem_genWeightSpaceOf hb two_ne_zero ?_⟩
  rw [mem_genWeightSpaceOf]
  exact ⟨1, by simp [t.lie_h_e_nsmul, two_smul]⟩

end IsSl2Triple

namespace TauCeti

variable [FiniteDimensional K L] [IsKilling K L]

/-- **Every nilpotent element lies in a Borel nilradical.** In a finite-dimensional Lie algebra
with nondegenerate Killing form over an algebraically closed field of characteristic zero, every
`ad`-nilpotent element lies in the positive nilradical of some Cartan subalgebra `H` and some base
of its root system. -/
theorem exists_mem_positiveNilradical_of_isNilpotent_ad [IsAlgClosed K] {e : L}
    (he : IsNilpotent (ad K L e)) :
    ∃ (H : LieSubalgebra K L) (_ : H.IsCartanSubalgebra) (b : (rootSystem H).Base),
      e ∈ positiveNilradical H b := by
  rcases eq_or_ne e 0 with rfl | he0
  · obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel K L
    exact ⟨LieSubalgebra.engel K x, hx, (rootSystem _).nonempty_base.some, zero_mem _⟩
  obtain ⟨h, f, t⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
  obtain ⟨H, hH, hhH⟩ := exists_isCartanSubalgebra_mem_of_isSemisimple_ad
    (isSemisimple_of_iSup_eigenspace_eq_top (iSup_eigenspace_toEnd_eq_top (K := K) (M := L) t))
  obtain ⟨b, -, hb⟩ :=
    IsSl2Triple.exists_base_mem_positiveNilradical (H := H) (h := ⟨h, hhH⟩) t
  exact ⟨H, hH, b, hb⟩

end TauCeti
