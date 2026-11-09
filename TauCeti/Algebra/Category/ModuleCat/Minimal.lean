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

/-- If an endomorphism fixes a map from a finite-length module, the map factors through
a retract onto the range of a positive power of that endomorphism. -/
theorem exists_retract_range_pow {P N : ModuleCat.{v} R} (g : P ⟶ N) (b : P ⟶ P)
    (hP : IsFiniteLength R P) (hb : b ≫ g = g) :
    ∃ (n : ℕ) (s : Retract (ModuleCat.of R (LinearMap.range (b.hom ^ (n + 1)))) P),
      s.r ≫ s.i ≫ g = g := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hP
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    (LinearMap.eventually_isCompl_ker_pow_range_pow b.hom)
  let K := LinearMap.ker (b.hom ^ (n + 1))
  let I := LinearMap.range (b.hom ^ (n + 1))
  have hc : IsCompl K I := hn (n + 1) n.le_succ
  -- The fixed-map identity kills the Fitting kernel, so projection onto the range
  -- gives another factorizing summand.
  have hfix (x : P) : g ((b.hom ^ (n + 1)) x) = g x := by
    have h : ⇑g.hom ∘ ⇑b.hom = ⇑g.hom := by rw [← LinearMap.coe_comp, ← hom_comp, hb]
    rw [pow_apply_eq_iterate]
    exact congrFun (Function.iterate_invariant h _) x
  refine ⟨n, ⟨ofHom I.subtype, ofHom (I.projectionOnto K hc.symm), by ext; simp⟩, ?_⟩
  ext x
  have hK : g (K.projection I hc x) = 0 := by
    rw [← hfix, LinearMap.mem_ker.mp (K.projection_apply_mem hc x), map_zero]
  conv_rhs => rw [← Submodule.projection_add_projection_eq_self hc.symm x]
  simp [hK]

/-- A morphism with finite-length source is a right minimal morphism on a retract of
its source, extended by zero on the complementary summand. No finiteness condition on
the target or on the ring is required. -/
theorem exists_retract_right_minimal {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (hM : IsFiniteLength R M) :
    ∃ (P : ModuleCat.{v} R) (r : Retract P M),
      r.r ≫ r.i ≫ f = f ∧
        ∀ b : P ⟶ P, b ≫ r.i ≫ f = r.i ≫ f → IsIso b := by
  let D (P : ModuleCat.{v} R) := ∃ r : Retract P M, r.r ≫ r.i ≫ f = f
  -- Choose a factorizing summand of least length.
  obtain ⟨P, hP⟩ := exists_minimalFor_of_wellFoundedLT D (fun P ↦ Module.length R P)
    ⟨M, Retract.refl M, by simp⟩
  obtain ⟨r, hr⟩ := hP.prop
  have hlen : IsFiniteLength R P :=
    hM.of_injective ((mono_iff_injective r.i).mp inferInstance)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hlen
  refine ⟨P, r, hr, fun b hb ↦ ?_⟩
  obtain ⟨n, s, hs⟩ := exists_retract_range_pow (r.i ≫ f) b hlen hb
  have hD : D (ModuleCat.of R (LinearMap.range (b.hom ^ (n + 1)))) :=
    ⟨s.trans r, by simpa [Retract.trans, hs] using hr⟩
  -- Minimal length forces that range to be the whole source.
  have hI : LinearMap.range (b.hom ^ (n + 1)) = ⊤ :=
    by_contra fun hI ↦ hP.not_lt hD (Submodule.length_lt hI)
  exact (ConcreteCategory.isIso_iff_bijective b).mpr
    (IsNoetherian.bijective_of_surjective_endomorphism b.hom
      (Module.End.surjective_of_iterate_surjective n.succ_ne_zero
        (LinearMap.range_eq_top.mp hI)))

end ModuleCat
