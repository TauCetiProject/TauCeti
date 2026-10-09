/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.FiniteLength
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Length

/-!
# Right minimal summands of module morphisms

A map with finite-length source restricts to a right minimal map on a direct summand,
and vanishes on the complementary summand. Right minimality means that every endomorphism
of the source fixing the map is invertible. This reduction removes redundant summands
from right almost split morphisms before forming their kernel sequences.

The proof uses Mathlib's Fitting decomposition
`LinearMap.eventually_isCompl_ker_pow_range_pow` and minimizes `Module.length` among
retracts through which the original map factors.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section V.1.
-/

public section

namespace ModuleCat

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A morphism with finite-length source is a right minimal morphism on a retract of
its source, extended by zero on the complementary summand. No finiteness condition on
the target or on the ring is required. -/
theorem exists_retract_right_minimal {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (hM : IsFiniteLength R M) :
    ∃ (P : ModuleCat.{v} R) (r : Retract P M),
      r.r ≫ r.i ≫ f = f ∧
        ∀ b : P ⟶ P, b ≫ r.i ≫ f = r.i ≫ f → IsIso b := by
  classical
  let D (P : ModuleCat.{v} R) := ∃ r : Retract P M, r.r ≫ r.i ≫ f = f
  -- Choose a factorizing summand of least length.
  obtain ⟨P, hP⟩ := exists_minimalFor_of_wellFoundedLT D (fun P ↦ Module.length R P)
    ⟨M, Retract.refl M, by simp⟩
  obtain ⟨r, hr⟩ := hP.prop
  have hlen : IsFiniteLength R P :=
    hM.of_injective ((mono_iff_injective r.i).mp inferInstance)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hlen
  refine ⟨P, r, hr, fun b hb ↦ ?_⟩
  let g := r.i ≫ f
  have hpow (n : ℕ) : ((End.of b) ^ n) ≫ g = g := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, End.mul_def, Category.assoc, ih, g, hb]
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    (LinearMap.eventually_isCompl_ker_pow_range_pow b.hom)
  let K := LinearMap.ker (b.hom ^ (n + 1))
  let I := LinearMap.range (b.hom ^ (n + 1))
  have hc : IsCompl K I := hn (n + 1) (Nat.le_succ n)
  -- The fixed-map identity kills the Fitting kernel, so projection onto the range
  -- gives another factorizing summand.
  let s : Retract (ModuleCat.of R I) P :=
    { i := ofHom I.subtype
      r := ofHom (I.projectionOnto K hc.symm)
      retract := by
        ext x
        exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hc.symm x) }
  have hkill : g.hom.comp K.subtype = 0 := by
    have hhom : (End.of b ^ (n + 1)).hom = b.hom ^ (n + 1) :=
      map_pow P.endRingEquiv (End.of b) (n + 1)
    have he : g.hom.comp (b.hom ^ (n + 1)) = g.hom := by
      simpa only [hom_comp, hhom] using congrArg Hom.hom (hpow (n + 1))
    ext x
    have hx : (b.hom ^ (n + 1)) x = 0 := x.property
    simpa [hx] using congrArg (fun l : P →ₗ[R] N ↦ l x) he.symm
  have hs : s.r ≫ s.i ≫ g = g := by
    apply hom_ext
    have he := congrArg (fun l : P →ₗ[R] P ↦ g.hom.comp l)
      (Submodule.subtype_comp_projectionOnto_add_eq_id hc.symm)
    simpa only [hom_comp, hom_ofHom, s, LinearMap.comp_add, ← LinearMap.comp_assoc,
      hkill, LinearMap.zero_comp, add_zero, LinearMap.comp_id] using he
  have hD : D (ModuleCat.of R I) := by
    refine ⟨s.trans r, ?_⟩
    simpa [Retract.trans, Category.assoc, g, hs] using hr
  have hI : I = ⊤ := by
    by_contra hI
    exact hP.not_lt hD (Submodule.length_lt hI)
  -- Minimal length forces that range to be the whole source.
  have hsur : Function.Surjective (b.hom ^ (n + 1)) := LinearMap.range_eq_top.mp hI
  have hu : IsUnit (b.hom ^ (n + 1)) := (Module.End.isUnit_iff _).mpr
    (IsNoetherian.bijective_of_surjective_endomorphism _ hsur)
  exact (isUnit_iff_isIso b).mp (((isUnit_pow_succ_iff (n := n)).mp hu).map P.endRingEquiv.symm)

end ModuleCat
