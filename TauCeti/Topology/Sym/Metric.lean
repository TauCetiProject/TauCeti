/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import TauCeti.Topology.Sym.Basic
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Neighbourhoods in the symmetric power of a pseudometric space

For a pseudometric space `α`, two unordered `n`-tuples `s t : Sym α n` are `ε`-close when their
points can be paired off one-to-one with paired points at distance less than `ε`, that is, when
`Multiset.Rel (fun a b ↦ dist a b < ε) s t`. This file shows that these matchings describe the
quotient topology of `Sym α n`: the sets of tuples `ε`-matched to `s` form a basis of the
neighbourhoods of `s` (`Sym.nhds_basis_rel_dist_lt`). Consequently a family of tuples converges
to `s` exactly when, for every `ε > 0`, its members are eventually `ε`-matched to `s`
(`Sym.tendsto_nhds_iff_rel_dist_lt`).

This is the form in which convergence of zero divisors is proved: by counting zeros, with
multiplicity, in small discs around the points of the limit divisor. The two descriptions agree
because `Sym.ofFn` is an open quotient map, so the images of the balls of `Fin n → α` form a basis
of neighbourhoods, and an unordered tuple is in the image of the `ε`-ball about `f` exactly when it
is `ε`-matched to `ofFn f` (`Sym.rel_coe_ofFn_iff`).
-/

public section

open Filter Topology

namespace Sym

variable {α : Type*} [PseudoMetricSpace α] {n : ℕ}

/-- **Neighbourhoods by matchings.** The unordered tuples whose points can be paired off with
those of `s` at distances less than `ε` form, for `ε > 0`, a basis of the neighbourhoods of `s` in
`Sym α n`. -/
theorem nhds_basis_rel_dist_lt (s : Sym α n) :
    (𝓝 s).HasBasis (fun ε : ℝ ↦ 0 < ε)
      fun ε ↦ {t | Multiset.Rel (fun a b ↦ dist a b < ε) (s : Multiset α) t} := by
  obtain ⟨f, rfl⟩ := ofFn_surjective s
  rw [← isOpenQuotientMap_ofFn.map_nhds_eq f]
  refine (Metric.nhds_basis_ball.map ofFn).congr (fun _ ↦ Iff.rfl) fun ε hε ↦ ?_
  ext t
  simp only [Set.mem_image, Metric.mem_ball, Set.mem_ofPred_eq, rel_coe_ofFn_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, rfl, fun i ↦ by rw [dist_comm]; exact (dist_pi_lt_iff hε).1 hg i⟩
  · rintro ⟨g, rfl, hg⟩
    exact ⟨g, (dist_pi_lt_iff hε).2 fun i ↦ by rw [dist_comm]; exact hg i, rfl⟩

/-- **Convergence by matchings.** A family of unordered tuples tends to `s` exactly when, for
every `ε > 0`, its members are eventually matched to `s` with paired points at distance less than
`ε`. -/
theorem tendsto_nhds_iff_rel_dist_lt {ι : Type*} {l : Filter ι} {t : ι → Sym α n} {s : Sym α n} :
    Tendsto t l (𝓝 s) ↔
      ∀ ε > 0, ∀ᶠ i in l, Multiset.Rel (fun a b ↦ dist a b < ε) (s : Multiset α) (t i) :=
  (nhds_basis_rel_dist_lt s).tendsto_right_iff

end Sym
