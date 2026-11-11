/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.RingTheory.Flat.Extensions

/-!
# Flat cycles in an exact tail

In a bounded-above complex of flat modules, the cycles in degree `i` are flat if the complex
is exact in all degrees strictly greater than `i`. No exactness in degree `i` is required.
In particular every cycle module of a bounded-above acyclic flat complex is flat. If exactness
also holds in degree `i`, its opcycles (the quotient by incoming boundaries) are flat as well.

This is the dimension-shifting step used when cutting off flat resolutions: the acyclic
mapping cone of a quasi-isomorphism between bounded-above flat complexes has flat cycles.
The quotient terms at a cutoff can consequently be shown flat, and finitely presented flat
quotients are projective. The terms need not be finite, and the base ring need not be
Noetherian. Only the terms at or above the cycle degree (strictly above the opcycle degree)
need to be flat; nothing is assumed about the remaining terms.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma III.12.3.
* D. Mumford, *Abelian Varieties*, §5, the lemma on complexes of flat modules.
-/

public section

open CategoryTheory Limits

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- In a bounded-above complex flat in degrees `≥ i`, exactness strictly above `i` makes its
cycles in degree `i` flat. Exactness in degree `i` itself is not needed. -/
theorem flat_cycles_of_exactAt_of_isStrictlyLE (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (n i : ℤ) [K.IsStrictlyLE n] (hFlat : ∀ j, i ≤ j → Module.Flat R (K.X j))
    (hK : ∀ j, i < j → K.ExactAt j) : Module.Flat R (K.cycles i) := by
  have above (j : ℤ) (hj : n < j) : Module.Flat R (K.cycles j) := by
    have : Subsingleton (K.X j) := ModuleCat.subsingleton_of_isZero
      (K.isZero_of_isStrictlyLE n j hj)
    have : Subsingleton (K.cycles j) :=
      (ModuleCat.mono_iff_injective (K.iCycles j)).1 inferInstance |>.subsingleton
    infer_instance
  have step (j : ℤ) (hj : i ≤ j) [Module.Flat R (K.cycles (j + 1))] :
      Module.Flat R (K.cycles j) := by
    have := hFlat j hj
    have hS := K.cyclesShortComplex_shortExact j (j + 1) (by simp) (hK _ (by omega))
    rw [K.cyclesShortComplex_def] at hS
    exact Function.Exact.flat_left_of_injective_of_surjective
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
      hS.moduleCat_injective_f hS.moduleCat_surjective_g
  by_cases hi : n < i
  · exact above i hi
  -- Descend from the zero cycle module above the bound, one short exact cycle sequence at a time.
  have down (k : ℕ) (hk : i ≤ n + 1 - k) : Module.Flat R (K.cycles (n + 1 - k)) := by
    induction k with
    | zero =>
      have heq : n + 1 - (0 : ℕ) = n + 1 := by omega
      exact heq.symm ▸ above (n + 1) (by omega)
    | succ k ih =>
      have : Module.Flat R (K.cycles (n + 1 - k)) := ih (by omega)
      have heq : n + 1 - (k + 1 : ℕ) + 1 = n + 1 - k := by omega
      have : Module.Flat R (K.cycles (n + 1 - (k + 1 : ℕ) + 1)) := heq ▸ this
      exact step _ hk
  have heq : n + 1 - ((n + 1 - i).toNat : ℤ) = i := by omega
  exact heq ▸ down (n + 1 - i).toNat (by omega)

/-- In a bounded-above complex flat in degrees `> i` and exact in degrees `≥ i`, the quotient
in degree `i` by incoming boundaries is flat. This is the term introduced by canonical
truncation from below. -/
theorem flat_opcycles_of_exactAt_of_isStrictlyLE (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (n i : ℤ) [K.IsStrictlyLE n] (hFlat : ∀ j, i < j → Module.Flat R (K.X j))
    (hK : ∀ j, i ≤ j → K.ExactAt j) : Module.Flat R (K.opcycles i) := by
  have : Module.Flat R (K.cycles (i + 1)) :=
    K.flat_cycles_of_exactAt_of_isStrictlyLE n (i + 1)
      (fun j hj ↦ hFlat j (by omega)) (fun j hj ↦ hK j (by omega))
  -- Exactness in degree `i` identifies the kernel of the differential with incoming boundaries;
  -- corestricting the outgoing differential to cycles does not change its kernel.
  have hE := (K.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mp (hK i le_rfl)
  have hS := K.exact_toCycles (i + 1) (K.d (i - 1) i) (K.d_comp_d _ _ _) hE
  have : Epi (K.toCycles i (i + 1)) :=
    HomologicalComplex.epi_toCycles_of_exactAt (hK (i + 1) (by omega)) (by simp)
  -- Both `opcycles i` and `cycles (i + 1)` are cokernels of `d (i - 1) i`.
  let e : K.opcycles i ≅ K.cycles (i + 1) :=
    (K.opcyclesIsCokernel (i - 1) i (by simp)).coconePointUniqueUpToIso hS.gIsCokernel
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

end CochainComplex
