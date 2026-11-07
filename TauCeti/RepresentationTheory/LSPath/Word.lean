/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.OrbitStable
public import TauCeti.RepresentationTheory.LSPath.PartialInverse
import TauCeti.LinearAlgebra.RootSystem.Height
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Bounds on words of path root operators

Words act by successive raising or lowering operators, read from left to right. Their endpoint
changes by the sum of the indicated roots. If the velocities lie in a reflection-stable set,
they continue to do so after every defined word.

For a finite Weyl orbit there is a uniform natural-number bound on the length of every defined
raising word, and likewise every defined lowering word, starting at any duration-one path with
velocities in that orbit. A linear form taking value one on each simple root measures the length
exactly; its range on the convex hull of the finite orbit is bounded. The form exists by extending
the linearly independent simple roots to a basis, so the roots need not span the weight space.
This includes central shapes and empty root systems. No LS stability or crystal classification
is used, and no bound on arbitrary mixed raising/lowering words is asserted.

These bounds give termination of successive raising, as needed in the comparison of LS paths
with components generated from straight paths.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§4–5 (finite path components and root-operator distance).
-/

public section

namespace TauCeti.PLPath

open Module

variable {ι 𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- Successive lowering along a word, read from left to right. -/
noncomputable def lowerWord (F : ι → Dual 𝕜 V) (x : ι → V) (w : List ι)
    (π : PLPath 𝕜 V) : Option (PLPath 𝕜 V) :=
  w.foldlM (fun π i ↦ lower (F i) (x i) π) π

/-- Successive raising along a word, read from left to right. -/
noncomputable def raiseWord (F : ι → Dual 𝕜 V) (x : ι → V) (w : List ι)
    (π : PLPath 𝕜 V) : Option (PLPath 𝕜 V) :=
  w.foldlM (fun π i ↦ raise (F i) (x i) π) π

variable {F : ι → Dual 𝕜 V} {x : ι → V} {w : List ι} {π ρ : PLPath 𝕜 V}

@[simp]
theorem lowerWord_nil (π : PLPath 𝕜 V) : lowerWord F x [] π = some π := (rfl)

@[simp]
theorem raiseWord_nil (π : PLPath 𝕜 V) : raiseWord F x [] π = some π := (rfl)

theorem lowerWord_cons (i : ι) (w : List ι) (π : PLPath 𝕜 V) :
    lowerWord F x (i :: w) π = (lower (F i) (x i) π).bind (lowerWord F x w) := (rfl)

theorem raiseWord_cons (i : ι) (w : List ι) (π : PLPath 𝕜 V) :
    raiseWord F x (i :: w) π = (raise (F i) (x i) π).bind (raiseWord F x w) := (rfl)

@[simp]
theorem lowerWord_singleton (i : ι) (π : PLPath 𝕜 V) :
    lowerWord F x [i] π = lower (F i) (x i) π := by
  simp [lowerWord_cons]

@[simp]
theorem raiseWord_singleton (i : ι) (π : PLPath 𝕜 V) :
    raiseWord F x [i] π = raise (F i) (x i) π := by
  simp [raiseWord_cons]

/-- Concatenating words composes their partial lowering actions. -/
theorem lowerWord_append (v w : List ι) (π : PLPath 𝕜 V) :
    lowerWord F x (v ++ w) π = (lowerWord F x v π).bind (lowerWord F x w) := by
  induction v generalizing π with
  | nil => simp
  | cons i v ih => simp only [List.cons_append, lowerWord_cons, ih, Option.bind_assoc]

/-- Concatenating words composes their partial raising actions. -/
theorem raiseWord_append (v w : List ι) (π : PLPath 𝕜 V) :
    raiseWord F x (v ++ w) π = (raiseWord F x v π).bind (raiseWord F x w) := by
  induction v generalizing π with
  | nil => simp
  | cons i v ih => simp only [List.cons_append, raiseWord_cons, ih, Option.bind_assoc]

/-- Lowering along a word and raising along its reversal are partial inverses. -/
theorem lowerWord_eq_some_iff (hx : ∀ i, F i (x i) = 2) :
    lowerWord F x w π = some ρ ↔ raiseWord F x w.reverse ρ = some π := by
  induction w generalizing π ρ with
  | nil => simp [eq_comm]
  | cons i w ih =>
    simp only [lowerWord_cons, List.reverse_cons, raiseWord_append, raiseWord_singleton,
      Option.bind_eq_some_iff, ih, lower_eq_some_iff (hx i)]
    exact exists_congr fun _ ↦ and_comm

/-- Raising along a word and lowering along its reversal are partial inverses. -/
theorem raiseWord_eq_some_iff (hx : ∀ i, F i (x i) = 2) :
    raiseWord F x w π = some ρ ↔ lowerWord F x w.reverse ρ = some π := by
  simpa using (lowerWord_eq_some_iff hx (w := w.reverse) (π := ρ) (ρ := π)).symm

/-- A lowering word subtracts the sum of its roots from the endpoint. -/
theorem endpoint_of_lowerWord_eq_some (h : lowerWord F x w π = some ρ) :
    ρ.endpoint = π.endpoint - (w.map x).sum := by
  induction w generalizing π with
  | nil =>
    obtain rfl := Option.some.inj h
    simp
  | cons i w ih =>
    obtain ⟨σ, hσ, hρ⟩ := Option.bind_eq_some_iff.mp (lowerWord_cons i w π ▸ h)
    rw [ih hρ, endpoint_of_lower_eq_some hσ, List.map_cons, List.sum_cons]
    abel

/-- A raising word adds the sum of its roots to the endpoint. -/
theorem endpoint_of_raiseWord_eq_some (h : raiseWord F x w π = some ρ) :
    ρ.endpoint = π.endpoint + (w.map x).sum := by
  induction w generalizing π with
  | nil =>
    obtain rfl := Option.some.inj h
    simp
  | cons i w ih =>
    obtain ⟨σ, hσ, hρ⟩ := Option.bind_eq_some_iff.mp (raiseWord_cons i w π ▸ h)
    rw [ih hρ, endpoint_of_raise_eq_some hσ, List.map_cons, List.sum_cons, add_assoc]

/-- A defined lowering word preserves a reflection-stable set of velocities. -/
theorem hasDistinguished_of_lowerWord_eq_some {S : Set V} (hπ : HasDistinguished S π)
    (hS : ∀ i, Set.MapsTo (preReflection (x i) (F i)) S S)
    (h : lowerWord F x w π = some ρ) : HasDistinguished S ρ := by
  induction w generalizing π with
  | nil => simpa using Option.some.inj h ▸ hπ
  | cons i w ih =>
    obtain ⟨σ, hσ, hρ⟩ := Option.bind_eq_some_iff.mp (lowerWord_cons i w π ▸ h)
    exact ih (hasDistinguished_of_lower_eq_some hπ (hS i) hσ) hρ

/-- A defined raising word preserves a reflection-stable set of velocities. -/
theorem hasDistinguished_of_raiseWord_eq_some {S : Set V} (hπ : HasDistinguished S π)
    (hS : ∀ i, Set.MapsTo (preReflection (x i) (F i)) S S)
    (h : raiseWord F x w π = some ρ) : HasDistinguished S ρ := by
  induction w generalizing π with
  | nil => simpa using Option.some.inj h ▸ hπ
  | cons i w ih =>
    obtain ⟨σ, hσ, hρ⟩ := Option.bind_eq_some_iff.mp (raiseWord_cons i w π ▸ h)
    exact ih (hasDistinguished_of_raise_eq_some hπ (hS i) hσ) hρ

/-- A form equal to one on every root measures the length of a defined lowering word. -/
theorem apply_endpoint_of_lowerWord_eq_some {g : Dual 𝕜 V} (hg : ∀ i, g (x i) = 1)
    (h : lowerWord F x w π = some ρ) :
    g ρ.endpoint = g π.endpoint - (w.length : 𝕜) := by
  rw [endpoint_of_lowerWord_eq_some h, map_sub, map_list_sum, List.map_map]
  simp [Function.comp_def, hg]

/-- A form equal to one on every root measures the length of a defined raising word. -/
theorem apply_endpoint_of_raiseWord_eq_some {g : Dual 𝕜 V} (hg : ∀ i, g (x i) = 1)
    (h : raiseWord F x w π = some ρ) :
    g ρ.endpoint = g π.endpoint + (w.length : 𝕜) := by
  rw [endpoint_of_raiseWord_eq_some h, map_add, map_list_sum, List.map_map]
  simp [Function.comp_def, hg]

end TauCeti.PLPath

namespace RootPairing

open Module TauCeti TauCeti.PLPath

variable {ι 𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

section WeylOrbit

variable {N : Type*} [AddCommGroup N] [Module 𝕜 N]
  (P : RootPairing ι 𝕜 V N) (b : P.Base)

/-- There is a uniform bound for all defined pure raising and pure lowering words on
duration-one paths with velocities in a fixed finite Weyl orbit (that is, having a distinguished
presentation for the orbit). The bound is independent of the path and
its number of segments. The roots need not span, and the shape need not be dominant. -/
theorem exists_bound_path_word_length [Finite P.weylGroup] [Archimedean 𝕜] (lam : V) :
    ∃ n : ℕ, ∀ (π ρ : PLPath 𝕜 V) (w : List b.support),
      HasDistinguished (MulAction.orbit P.weylGroup lam) π →
      (lowerWord (fun i : b.support ↦ P.coroot' i) (fun i : b.support ↦ P.root i) w π = some ρ →
        w.length ≤ n) ∧
      (raiseWord (fun i : b.support ↦ P.coroot' i) (fun i : b.support ↦ P.root i) w π = some ρ →
        w.length ≤ n) := by
  obtain ⟨g, hg⟩ := b.exists_dual_eq_one_on_root
  have hS := fun i : b.support ↦ P.mapsTo_preReflection_orbit_weylGroup i lam
  -- The same bounds hold on the convex hull, hence at every endpoint under consideration.
  obtain ⟨L, hL⟩ := (Set.finite_range fun w : P.weylGroup ↦ g (w • lam)).bddBelow
  obtain ⟨U, hU⟩ := (Set.finite_range fun w : P.weylGroup ↦ g (w • lam)).bddAbove
  have hb {π : PLPath 𝕜 V} (hπ : HasDistinguished (MulAction.orbit P.weylGroup lam) π) :
      L ≤ g π.endpoint ∧ g π.endpoint ≤ U := by
    exact hπ.apply_endpoint_mem_Icc g fun _ ⟨w, hw⟩ ↦
      hw ▸ ⟨hL ⟨w, rfl⟩, hU ⟨w, rfl⟩⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (U - L)
  refine ⟨n, fun π ρ w hπ ↦ ?_⟩
  have hbound (hρ : HasDistinguished (MulAction.orbit P.weylGroup lam) ρ)
      (heq : g ρ.endpoint = g π.endpoint - (w.length : 𝕜) ∨
        g ρ.endpoint = g π.endpoint + (w.length : 𝕜)) : w.length ≤ n := by
    have hπb := hb hπ
    have hρb := hb hρ
    have : (w.length : 𝕜) ≤ n := by rcases heq with heq | heq <;> linarith
    exact_mod_cast this
  exact ⟨fun h ↦ hbound (hasDistinguished_of_lowerWord_eq_some hπ hS h)
      (Or.inl (apply_endpoint_of_lowerWord_eq_some hg h)),
    fun h ↦ hbound (hasDistinguished_of_raiseWord_eq_some hπ hS h)
      (Or.inr (apply_endpoint_of_raiseWord_eq_some hg h))⟩

end WeylOrbit

end RootPairing
