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
import TauCeti.Algebra.Homology.Split

/-!
# Complexes of projective modules over a principal ideal domain

Let `K` be a homological complex of modules over a principal ideal ring `k` without zero divisors,
of any shape.  Every module injecting into a projective `k`-module is free
(`Module.Free.of_injective_of_projective_of_isPrincipalIdealRing`).  So when the term `Kᵢ` is
projective, its cycles `Zᵢ` are free, hence projective.  When the term `Kⱼ` after `Kᵢ` is
projective, the boundaries `Bⱼ ⊆ Kⱼ` are projective, so the short exact sequence
`0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Bⱼ ⟶ 0` splits and the cycles split off `Kᵢ`.

These are the hypotheses of the universal coefficient sequence
(`TauCeti.ChainComplex.exact_extToHomology_kronecker`), so it applies to every complex of free
abelian groups, for instance to singular chains with integer coefficients.  The splitting of
complexes (`HomologicalComplex.exists_homotopyEquiv_d_eq_zero`) additionally needs the homology to
split off the cycles, which holds when the homology is projective
(`HomologicalComplex.isSplitEpi_homologyπ_of_projective`).  Over a field the cycles split off for
the simpler reason that all modules are semisimple (`TauCeti.Algebra.Homology.Semisimple`).

## Main results

* `HomologicalComplex.free_cycles_of_isPrincipalIdealRing`: the cycles of a projective term are
  free.
* `HomologicalComplex.isSplitMono_iCycles_of_isPrincipalIdealRing`: the cycles split off a term
  when the next term is projective.
* `HomologicalComplex.free_cokernel_iCycles_of_isPrincipalIdealRing`: the quotient of a term by
  its cycles is free when the next term is projective.
* `HomologicalComplex.free_homology_of_d_eq_zero` and
  `ChainComplex.free_homology_of_isZero_X_succ`: when the incoming differential into a projective
  term vanishes, its homology coincides with its cycles and is free, without any finiteness
  assumption on rank.

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

/-- Over a principal ideal ring without zero divisors, the cycles of a projective term of a
complex of modules are free. -/
instance free_cycles_of_isPrincipalIdealRing [Module.Projective k (K.X i)] :
    Module.Free k (K.cycles i) :=
  .of_injective_of_projective_of_isPrincipalIdealRing (K.iCycles i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- Over a principal ideal ring without zero divisors, the inclusion of the cycles into a term of a
complex of modules is a split monomorphism when the next term is projective: the differential maps
the term onto the boundaries, which are projective as a submodule of the next term. -/
instance isSplitMono_iCycles_of_isPrincipalIdealRing [Module.Projective k (K.X (c.next i))] :
    IsSplitMono (K.iCycles i) := by
  by_cases h : c.Rel i (c.next i)
  · -- the boundaries `Bⱼ ⊆ Zⱼ ⊆ Kⱼ` of the next term `Kⱼ` are free
    have := Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
      (kernel.ι (K.homologyπ (c.next i)) ≫ K.iCycles (c.next i)).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
    exact K.isSplitMono_iCycles_of_projective_kernel_homologyπ h
  · -- with no differential out of `Kᵢ`, all of `Kᵢ` is cycles
    have := K.isIso_iCycles i (c.next i) rfl (K.shape _ _ h)
    exact IsSplitMono.of_iso _

/-- Over a principal ideal ring without zero divisors, the quotient of a term of a complex of
modules by its cycles is free when the next term is projective: the differential embeds the
quotient into the next term. -/
instance free_cokernel_iCycles_of_isPrincipalIdealRing [Module.Projective k (K.X (c.next i))] :
    Module.Free k (cokernel (K.iCycles i) : ModuleCat.{v} k) :=
  .of_injective_of_projective_of_isPrincipalIdealRing
    (cokernel.desc (K.iCycles i) (K.d i (c.next i)) (K.iCycles_d _ _)).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- Over a principal ideal ring without zero divisors, if every differential into `K.X i` vanishes
and `K.X i` is projective, then `K.homology i` is free: with no incoming boundaries, `K.homologyπ i`
is an isomorphism from the free module of cycles `K.cycles i`. -/
theorem free_homology_of_d_eq_zero [Module.Projective k (K.X i)]
    (h : ∀ j, c.Rel j i → K.d j i = 0) : Module.Free k (K.homology i) := by
  have hd : K.d (c.prev i) i = 0 := by
    by_cases hrel : c.Rel (c.prev i) i
    · exact h _ hrel
    · exact K.shape _ _ hrel
  exact .of_equiv (K.isoHomologyπ (c.prev i) i rfl hd).toLinearEquiv

/-- Over a principal ideal ring without zero divisors, if every term with a differential into
`K.X i` is zero and `K.X i` is projective, then `K.homology i` is free. -/
theorem free_homology_of_isZero_X [Module.Projective k (K.X i)]
    (h : ∀ j, c.Rel j i → IsZero (K.X j)) : Module.Free k (K.homology i) :=
  K.free_homology_of_d_eq_zero i fun j hj ↦ (h j hj).eq_of_src _ _

end HomologicalComplex

namespace ChainComplex

variable {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
  {α : Type*} [AddRightCancelSemigroup α] [One α]
  (K : ChainComplex (ModuleCat.{v} k) α) (n : α)

/-- Over a principal ideal ring without zero divisors, if `K.d (n + 1) n = 0` and `K.X n` is
projective, then `K.homology n` is free. -/
theorem free_homology_of_d_eq_zero [Module.Projective k (K.X n)] (h : K.d (n + 1) n = 0) :
    Module.Free k (K.homology n) :=
  HomologicalComplex.free_homology_of_d_eq_zero K n fun _ hj ↦ hj ▸ h

/-- Over a principal ideal ring without zero divisors, if `K.X (n + 1)` is zero and `K.X n` is
projective, then `K.homology n` is free. -/
theorem free_homology_of_isZero_X_succ [Module.Projective k (K.X n)] (h : IsZero (K.X (n + 1))) :
    Module.Free k (K.homology n) :=
  K.free_homology_of_d_eq_zero n (h.eq_of_src _ _)

end ChainComplex
