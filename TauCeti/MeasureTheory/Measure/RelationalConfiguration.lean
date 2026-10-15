/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Finite measures on relational configurations

A relational configuration is a Boolean value for every atom, and configurations carry the product
σ-algebra. A finite measure on configurations is therefore determined by its finite-dimensional
laws, the laws of the values at finite sets of atoms. Over the vertex set `ℕ`, every finite set of
atoms involves finitely many vertices, so a finite measure is already determined by its windows,
the restrictions along `Fin.val : Fin n → ℕ`.

## Main results

* `TauCeti.RelationalConfiguration.measure_ext_of_forall_finset` — a finite measure on
  configurations is determined by the laws of its values at finite sets of atoms;
* `TauCeti.RelationalConfiguration.map_restrict_eq_of_forall_finset` — the restriction of a
  finite measure along a vertex map is determined by the laws of the finite sets of atoms that are
  relabelled from the source;
* `TauCeti.RelationalConfiguration.measure_ext_of_map_restrict_val` — a finite measure on
  configurations over `ℕ` is determined by its windows.
-/

public section

open MeasureTheory

open _root_.FirstOrder (Language)

namespace TauCeti

namespace RelationalConfiguration

variable {L : Language} {V W : Type*}

/-- Reading off a finite set of atoms is measurable. -/
@[fun_prop]
theorem measurable_restrict_eval (J : Finset (Atom L V)) :
    Measurable fun c : RelationalConfiguration L V => J.restrict c.eval := by
  fun_prop

/-- **A finite measure on configurations is determined by its finite-dimensional laws**, the laws
of the values at finite sets of atoms. -/
theorem measure_ext_of_forall_finset {μ ν : Measure (RelationalConfiguration L V)}
    [IsFiniteMeasure μ]
    (h : ∀ J : Finset (Atom L V),
      μ.map (fun c => J.restrict c.eval) = ν.map (fun c => J.restrict c.eval)) : μ = ν := by
  have heval : Measurable fun c : RelationalConfiguration L V => c.eval :=
    measurable_pi_iff.2 measurable_eval
  -- The laws of the atom values are projective limits of the same family.
  have hcoord : μ.map (fun c => c.eval) = ν.map (fun c => c.eval) :=
    IsProjectiveLimit.unique (P := fun J => μ.map fun c => J.restrict c.eval)
      (fun J => by rw [Measure.map_map (Finset.measurable_restrict J) heval]; rfl)
      fun J => by rw [Measure.map_map (Finset.measurable_restrict J) heval]; exact (h J).symm
  have hmk : ∀ ρ : Measure (RelationalConfiguration L V), (ρ.map fun c => c.eval).map mk = ρ :=
    fun ρ => by
      have hid : (mk ∘ fun c : RelationalConfiguration L V => c.eval) = id :=
        funext fun c => ext fun a => eval_mk _ a
      rw [Measure.map_map measurable_mk heval, hid, Measure.map_id]
  rw [← hmk μ, hcoord, hmk]

/-- Two finite measures on configurations have the same restriction along a vertex map `f` as soon
as they give the same law to every finite set of atoms relabelled along `f`. -/
theorem map_restrict_eq_of_forall_finset {μ ν : Measure (RelationalConfiguration L W)}
    [IsFiniteMeasure μ] (f : V → W)
    (h : ∀ J : Finset (Atom L W), (∀ a ∈ J, ∃ b : Atom L V, b.map f = a) →
      μ.map (fun c => J.restrict c.eval) = ν.map (fun c => J.restrict c.eval)) :
    μ.map (restrict f) = ν.map (restrict f) := by
  classical
  refine measure_ext_of_forall_finset fun J => ?_
  -- Reading the atoms of `J` after restricting along `f` reads the atoms of `J.image (map f)`.
  have hread : (fun c : RelationalConfiguration L W => J.restrict (c.restrict f).eval) =
      (fun x j => x ⟨j.1.map f, Finset.mem_image_of_mem _ j.2⟩) ∘
        fun c => (J.image (Atom.map f)).restrict c.eval := by
    funext c
    ext j
    simp
  have hlaw : ∀ ρ : Measure (RelationalConfiguration L W),
      (ρ.map (restrict f)).map (fun d => J.restrict d.eval) =
        (ρ.map fun c => (J.image (Atom.map f)).restrict c.eval).map
          fun x j => x ⟨j.1.map f, Finset.mem_image_of_mem _ j.2⟩ := fun ρ => by
    rw [Measure.map_map (measurable_restrict_eval J) (measurable_restrict f),
      Measure.map_map (measurable_of_countable _) (measurable_restrict_eval _)]
    exact congrArg ρ.map hread
  refine (hlaw μ).trans ((congrArg (Measure.map _) (h _ fun a ha => ?_)).trans (hlaw ν).symm)
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 ha
  exact ⟨b, hb⟩

/-- **A finite measure on configurations over `ℕ` is determined by its windows**, the
restrictions along `Fin.val : Fin n → ℕ`: every finite set of atoms lies in some window, where
the configuration is recovered by extending its restriction. -/
theorem measure_ext_of_map_restrict_val {μ ν : Measure (RelationalConfiguration L ℕ)}
    [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (restrict (Fin.val : Fin n → ℕ)) = ν.map (restrict Fin.val)) : μ = ν := by
  refine measure_ext_of_forall_finset fun J => ?_
  obtain ⟨n, hn⟩ := Atom.exists_forall_map_val J
  -- The atoms of `J` are read off the extension of the window below `n`.
  have hread : (fun c : RelationalConfiguration L ℕ => J.restrict c.eval) =
      (fun d => J.restrict (d.extend Fin.val).eval) ∘ restrict (Fin.val : Fin n → ℕ) := by
    funext c
    ext a
    obtain ⟨b, hb⟩ := hn a a.2
    simp [← hb, Fin.val_injective]
  have hm : Measurable fun d : RelationalConfiguration L (Fin n) =>
      J.restrict (d.extend Fin.val).eval :=
    (measurable_restrict_eval J).comp (measurable_extend _)
  rw [hread, ← Measure.map_map hm (measurable_restrict _), h, Measure.map_map hm
    (measurable_restrict _)]

end RelationalConfiguration

end TauCeti
