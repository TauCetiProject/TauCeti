/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Homology.Boundaries
public import TauCeti.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Complexes of projective modules over a principal ideal domain

Let `K` be a homological complex of modules over a principal ideal ring `k` without zero divisors,
of any shape.  Every submodule of a projective `k`-module is free
(`Submodule.free_of_projective_of_isPrincipalIdealRing`).  So when the term `Kᵢ` is projective,
its cycles `Zᵢ` are free, hence projective.  When the term `Kⱼ` after `Kᵢ` is projective, the
boundaries `Bⱼ ⊆ Kⱼ` are projective, so the short exact sequence `0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Bⱼ ⟶ 0` splits
and the cycles split off `Kᵢ`.

These are the hypotheses of the universal coefficient sequence
(`TauCeti.ChainComplex.exact_extToHomology_kronecker`) and of the splitting of complexes
(`HomologicalComplex.exists_homotopyEquiv_d_eq_zero`), so both apply to every complex of free
abelian groups, for instance to singular chains with integer coefficients.  Over a field the
cycles split off for the simpler reason that all modules are semisimple
(`TauCeti.Algebra.Homology.Semisimple`).

## Main results

* `HomologicalComplex.free_cycles_of_isPrincipalIdealRing`: the cycles of a projective term are
  free.
* `HomologicalComplex.isSplitMono_iCycles_of_isPrincipalIdealRing`: the cycles split off a term
  when the next term is projective.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, where the same splitting
  gives the Künneth and universal coefficient theorems for complexes of free abelian groups.
-/

public section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex

variable {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
  {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{v} k) c) (i : ι)

/-- The source of a monomorphism into a projective module over a principal ideal ring without zero
divisors is free: it is isomorphic to the range, a submodule. -/
private lemma free_of_mono {A B : ModuleCat.{v} k} (f : A ⟶ B) [Mono f] [Module.Projective k B] :
    Module.Free k A :=
  have := (LinearMap.range f.hom).free_of_projective_of_isPrincipalIdealRing
  .of_equiv (LinearEquiv.ofInjective f.hom ((ModuleCat.mono_iff_injective f).mp ‹_›)).symm

/-- Over a principal ideal ring without zero divisors, the cycles of a projective term of a
complex of modules are free. -/
instance free_cycles_of_isPrincipalIdealRing [Module.Projective k (K.X i)] :
    Module.Free k (K.cycles i) :=
  free_of_mono (K.iCycles i)

/-- Over a principal ideal ring without zero divisors, the inclusion of the cycles into a term of a
complex of modules is a split monomorphism when the next term is projective: the differential maps
the term onto the boundaries, which are projective as a submodule of the next term. -/
instance isSplitMono_iCycles_of_isPrincipalIdealRing [Module.Projective k (K.X (c.next i))] :
    IsSplitMono (K.iCycles i) := by
  by_cases h : c.Rel i (c.next i)
  · -- the boundaries `Bⱼ ⊆ Zⱼ ⊆ Kⱼ` of the next term `Kⱼ` are free
    have := free_of_mono (kernel.ι (K.homologyπ (c.next i)) ≫ K.iCycles (c.next i))
    have := K.epi_toBoundaries h
    -- `0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Bⱼ ⟶ 0` is short exact with projective quotient, hence split
    have hS : (ShortComplex.mk _ _ (K.iCycles_toBoundaries i (c.next i))).ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (K.toBoundariesIsCokernel h) }
    exact .mk' ⟨hS.splittingOfProjective.r, hS.splittingOfProjective.f_r⟩
  · -- with no differential out of `Kᵢ`, all of `Kᵢ` is cycles
    have := K.isIso_iCycles i (c.next i) rfl (K.shape _ _ h)
    infer_instance

end HomologicalComplex
