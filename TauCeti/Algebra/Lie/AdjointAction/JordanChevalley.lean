/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
public import Mathlib.Algebra.Central.End
import TauCeti.Algebra.Lie.AdjointAction.Basic

/-!
# Ad-nilpotent endomorphisms

The adjoint action of an associative algebra does not see its centre, so the adjoint action of a
scalar plus a nilpotent element is nilpotent
(`TauCeti.LieAlgebra.isNilpotent_ad_of_isNilpotent_sub_algebraMap`, over any commutative ring).
For the endomorphisms of a finite-dimensional vector space over a perfect field this is the only
way `ad f` can be nilpotent: the semisimple part `s` of the Jordan–Chevalley decomposition
`f = n + s` has a semisimple adjoint action, which is also nilpotent since it is `ad f - ad n`.
Hence `ad s = 0`, so `s` is central, hence a scalar.

This is the general linear instance of the fact that, in a reductive Lie algebra, ad-nilpotence
alone allows an arbitrary central component. The trace-zero version, where the central component
is forced to vanish when the matrix size is nonzero in the field, is in
`TauCeti.Algebra.Lie.GeneralLinear.AdNilpotent`.

The perfectness hypothesis cannot be dropped: if `K` has characteristic `p` and `a ∈ K` is not a
`p`-th power, the companion matrix `f` of `X ^ p - a` satisfies `ad f ^ p = ad (f ^ p) = 0`, but
`(f - c) ^ p = (a - c ^ p) • 1 ≠ 0` for every `c : K`.

## Main statements

* `TauCeti.LieAlgebra.isNilpotent_ad_iff_exists_isNilpotent_sub_algebraMap`: over a perfect field,
  an endomorphism of a finite-dimensional space is ad-nilpotent exactly when it is a scalar plus a
  nilpotent endomorphism.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §4.2.
-/

public section

namespace TauCeti.LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

open Module

/-- **Ad-nilpotent endomorphisms.** Over a perfect field, the adjoint action of an endomorphism `f`
of a finite-dimensional vector space is nilpotent exactly when `f` is a scalar plus a nilpotent
endomorphism. -/
theorem isNilpotent_ad_iff_exists_isNilpotent_sub_algebraMap [PerfectField K]
    [FiniteDimensional K V] {f : End K V} :
    IsNilpotent (LieAlgebra.ad K (End K V) f) ↔
      ∃ c : K, IsNilpotent (f - algebraMap K (End K V) c) := by
  refine ⟨fun hf ↦ ?_, fun ⟨c, hc⟩ ↦ isNilpotent_ad_of_isNilpotent_sub_algebraMap hc⟩
  obtain ⟨n, hn, s, -, hn_nil, hs_ss, rfl⟩ := f.exists_isNilpotent_isSemisimple
  -- The adjoint action of the semisimple part is semisimple and nilpotent, hence zero.
  have hcomm : Commute (LieAlgebra.ad K (End K V) (n + s)) (LieAlgebra.ad K (End K V) n) :=
    LieAlgebra.commute_ad_of_commute (Algebra.commute_of_mem_adjoin_self hn)
  have hs : LieAlgebra.ad K (End K V) s = 0 := by
    refine End.eq_zero_of_isNilpotent_isSemisimple ?_
      (LieAlgebra.ad_isSemisimple_of_isSemisimple hs_ss)
    simpa using hcomm.isNilpotent_sub hf (LieAlgebra.ad_nilpotent_of_nilpotent hn_nil)
  -- So the semisimple part is central, and the centre of `End K V` is the scalars.
  rw [ad_eq_zero_iff_mem_center, Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at hs
  obtain ⟨c, rfl⟩ := hs
  exact ⟨c, by simpa using hn_nil⟩

end TauCeti.LieAlgebra
