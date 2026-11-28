/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.RingTheory.TrivSqZeroExt
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.RingTheory.LocalRing.Socle

/-!
# Socles of square-zero extensions of fields

In the square-zero extension of a field by a nonzero vector space, the socle of the regular
module is the square-zero ideal. If the dimension of that ideal is at least two, the ring fails
to be self-injective because no single nonzero socle element generates the socle.

## References

* M. Auslander, I. Reiten and S. O. Smalø, *Representation Theory of Artin Algebras*,
  Proposition II.4.1, for the socle of an indecomposable injective module of finite length.
-/

public section

open IsLocalRing

namespace TrivSqZeroExt

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
  [IsCentralScalar k V]

/-- A trivial square-zero extension of a field by a vector space of dimension at least two,
possibly infinite, is not self-injective. -/
theorem not_moduleInjective_self_of_one_lt_rank (h : 1 < Module.rank k V) :
    ¬ Module.Injective (TrivSqZeroExt k V) (TrivSqZeroExt k V) := by
  intro hinj
  have : Nontrivial V := rank_pos_iff_nontrivial.mp (zero_lt_one.trans h)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hspan : k ∙ v ≠ ⊤ := fun e ↦ by
    have hle : Module.rank k (k ∙ v) ≤ 1 := (rank_span_le {v}).trans (by simp)
    rw [e, rank_top] at hle
    exact (not_le.mpr h) hle
  obtain ⟨w, hw⟩ := SetLike.exists_notMem_of_ne_top _ hspan
  -- Self-injectivity would put every socle element in the principal ideal of `inr v`.
  have hv' : (inr v : TrivSqZeroExt k V) ≠ 0 :=
    by simpa only [inr_zero] using (inr_injective (R := k)).ne hv
  have hw' : (inr w : TrivSqZeroExt k V) ∈
      Submodule.torsionBySet (TrivSqZeroExt k V) (TrivSqZeroExt k V)
        (maximalIdeal (TrivSqZeroExt k V)) :=
    mem_torsionBySet_maximalIdeal_iff_fst_eq_zero.mpr (fst_inr k w)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp
    (TauCeti.IsLocalRing.mem_span_singleton_of_mem_torsionBySet hv' hw')
  refine hw (Submodule.mem_span_singleton.mpr ⟨r.fst, ?_⟩)
  simpa [snd_mul] using congrArg snd hr

end TrivSqZeroExt
