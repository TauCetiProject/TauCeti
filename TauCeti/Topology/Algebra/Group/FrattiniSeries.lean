/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries

/-!
# The Frattini series of a topological group

The **Frattini series** `Φ_k = TauCeti.proPFrattiniSeries p G k` of a topological group is the
sequence of closed normal subgroups

```text
Φ₀ = G,   Φ_{k+1} = closure (Φ_kᵖ ⬝ [Φ_k, Φ_k]),
```

obtained by iterating the verbal form of the pro-`p` Frattini subgroup. One step of the recursion
is `TauCeti.proPFrattiniStep`, the verbal step `TauCeti.pVerbalStep` of a subgroup against itself;
its characteristic property `TauCeti.proPFrattiniStep_le_iff` characterizes containment in a closed
subgroup. The series is descending with closed normal terms, and continuous homomorphisms carry
`Φ_k` into `Φ_k`.

The Frattini series lies below the lower `p`-series `λ_k = TauCeti.pLowerCentralSeries p G k` of
`TauCeti.Topology.Algebra.Group.LowerCentralSeries`, term by term: the two steps differ only in
that the Frattini step takes commutators inside the subgroup while the lower `p`-series step takes
them against the whole group.

Nothing here assumes `p` prime or `G` profinite. For a profinite `G` and a prime `p` the step is
the honest pro-`p` Frattini subgroup, so `Φ_{k+1} = Φ(Φ_k)`; and in a topologically finitely
generated pro-`p` group the inclusion `Φ_k ≤ λ_k` reverses cofinally — every `Φ_k` contains some
`λ_j` — so there the two series are cofinal in one another. See
`TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Series`.

## Main definitions

* `TauCeti.proPFrattiniStep`: one step `H ↦ closure (Hᵖ ⬝ [H, H])` of the recursion.
* `TauCeti.proPFrattiniSeries`: the Frattini series `Φ_k`.

## Main results

* `TauCeti.proPFrattiniStep_le_iff`: a closed subgroup contains `proPFrattiniStep p H` exactly
  when it contains the `p`-th powers of `H` and the commutators `⁅H, H⁆`.
* `TauCeti.proPFrattiniSeries_le_pLowerCentralSeries`: `Φ_k ≤ λ_k`.
* `MonoidHom.map_proPFrattiniSeries_le`,
  `MonoidHom.map_proPFrattiniSeries_eq_of_surjective`,
  `ContinuousMulEquiv.map_proPFrattiniSeries_eq`: functoriality of the series.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8, Proposition 2.8.13.
* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, Section 1.2.
-/

public section

namespace TauCeti

open Subgroup
open scoped commutatorElement

/-! ### One step of the recursion -/

section Step

variable (p : ℕ) {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- One step of the **Frattini series**: `H ↦ closure (Hᵖ ⬝ [H, H])`, the verbal step
`TauCeti.pVerbalStep` of `H` against itself. For a prime `p` and a closed subgroup of a profinite
group it is the pro-`p` Frattini subgroup of `H`, viewed inside the ambient group
(`TauCeti.proPFrattiniStep_eq_map_proPFrattini`). Its characteristic property is
`TauCeti.proPFrattiniStep_le_iff`. -/
def proPFrattiniStep (H : Subgroup G) : Subgroup G := pVerbalStep p H H

/-- One step of the Frattini series is the verbal step of a subgroup against itself. -/
theorem proPFrattiniStep_eq_pVerbalStep (H : Subgroup G) :
    proPFrattiniStep p H = pVerbalStep p H H := by
  rw [proPFrattiniStep]

/-- The defining equation `proPFrattiniStep p H = closure (Hᵖ ⬝ [H, H])`, with topological
closure, expresses the next Frattini step in terms of powers and commutators. -/
theorem proPFrattiniStep_def (H : Subgroup G) :
    proPFrattiniStep p H =
      (Subgroup.closure ((· ^ p) '' (H : Set G)) ⊔ ⁅H, H⁆).topologicalClosure := by
  rw [proPFrattiniStep_eq_pVerbalStep, pVerbalStep_def]

variable {p}

/-- One step of the Frattini series is a closed subgroup. -/
theorem isClosed_proPFrattiniStep (H : Subgroup G) :
    IsClosed (proPFrattiniStep p H : Set G) := by
  rw [proPFrattiniStep_eq_pVerbalStep]
  exact isClosed_pVerbalStep H H

/-- The `p`-th power of an element of `H` lies in `proPFrattiniStep p H`. -/
theorem pow_mem_proPFrattiniStep {H : Subgroup G} {x : G} (hx : x ∈ H) :
    x ^ p ∈ proPFrattiniStep p H := by
  rw [proPFrattiniStep_eq_pVerbalStep]
  exact pow_mem_pVerbalStep hx

/-- The commutators `⁅H, H⁆` lie in `proPFrattiniStep p H`. -/
theorem commutator_le_proPFrattiniStep (H : Subgroup G) :
    ⁅H, H⁆ ≤ proPFrattiniStep p H := by
  rw [proPFrattiniStep_eq_pVerbalStep]
  exact commutator_le_pVerbalStep H H

/-- The commutator of two elements of `H` lies in `proPFrattiniStep p H`. -/
theorem commutator_mem_proPFrattiniStep {H : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    ⁅x, y⁆ ∈ proPFrattiniStep p H :=
  commutator_le_proPFrattiniStep H (commutator_mem_commutator hx hy)

/-- **The characteristic property of one step.** A closed subgroup contains
`proPFrattiniStep p H` exactly when it contains the `p`-th powers of the elements of `H` and the
commutators `⁅H, H⁆`. -/
theorem proPFrattiniStep_le_iff {H K : Subgroup G} (hK : IsClosed (K : Set G)) :
    proPFrattiniStep p H ≤ K ↔ (∀ x ∈ H, x ^ p ∈ K) ∧ ⁅H, H⁆ ≤ K := by
  rw [proPFrattiniStep_eq_pVerbalStep, pVerbalStep_le_iff hK]

/-- One step of the Frattini series is monotone in the subgroup. -/
theorem proPFrattiniStep_mono {H K : Subgroup G} (h : H ≤ K) :
    proPFrattiniStep p H ≤ proPFrattiniStep p K := by
  rw [proPFrattiniStep_eq_pVerbalStep, proPFrattiniStep_eq_pVerbalStep]
  exact pVerbalStep_mono h h

/-- One step of the Frattini series lies in the corresponding step of the lower `p`-series: the
two differ only in that the latter takes commutators against the whole group. -/
theorem proPFrattiniStep_le_pLowerCentralStep (H : Subgroup G) :
    proPFrattiniStep p H ≤ pLowerCentralStep p H := by
  rw [proPFrattiniStep_eq_pVerbalStep, pLowerCentralStep_eq_pVerbalStep]
  exact pVerbalStep_mono le_rfl le_top

/-- One step of the Frattini series of a normal subgroup is normal. -/
instance proPFrattiniStep_normal (H : Subgroup G) [H.Normal] :
    (proPFrattiniStep p H).Normal := by
  rw [proPFrattiniStep_eq_pVerbalStep]
  infer_instance

/-- One step of the Frattini series of a closed subgroup lies in that subgroup. -/
theorem proPFrattiniStep_le {H : Subgroup G} (hH : IsClosed (H : Set G)) :
    proPFrattiniStep p H ≤ H :=
  (proPFrattiniStep_le_iff hH).mpr ⟨fun _ hx ↦ H.pow_mem hx p, H.commutator_le_self⟩

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous homomorphism carries one step of the Frattini series of a subgroup into the
corresponding step for the image of that subgroup. -/
theorem _root_.MonoidHom.map_proPFrattiniStep_le (f : G →* H) (hf : Continuous f)
    (K : Subgroup G) : (proPFrattiniStep p K).map f ≤ proPFrattiniStep p (K.map f) := by
  rw [proPFrattiniStep_eq_pVerbalStep, proPFrattiniStep_eq_pVerbalStep]
  exact f.map_pVerbalStep_le hf K K

/-- A continuous closed map (for instance a continuous homomorphism from a compact group to a
Hausdorff group, by `Continuous.isClosedMap`) carries one step of the Frattini series of a
subgroup onto the corresponding step for its image. Unlike for the lower `p`-series, no
surjectivity is needed: the Frattini step of `K` refers to `K` alone. -/
theorem _root_.MonoidHom.map_proPFrattiniStep_eq_of_isClosedMap (f : G →* H) (hf : Continuous f)
    (hfc : IsClosedMap f) (K : Subgroup G) :
    (proPFrattiniStep p K).map f = proPFrattiniStep p (K.map f) := by
  rw [proPFrattiniStep_eq_pVerbalStep, proPFrattiniStep_eq_pVerbalStep,
    f.map_pVerbalStep_eq_of_isClosedMap hf hfc]

end Step

/-! ### The series -/

section Series

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The **Frattini series** of a topological group, 0-based like the lower `p`-series:
`Φ₀ = G` and `Φ_{k+1} = closure (Φ_kᵖ ⬝ [Φ_k, Φ_k])`. For a prime `p` and a profinite group it
is the iterated pro-`p` Frattini subgroup
(`TauCeti.proPFrattiniSeries_succ_eq_map_proPFrattini`), and it always lies below the lower
`p`-series (`TauCeti.proPFrattiniSeries_le_pLowerCentralSeries`); in a topologically finitely
generated pro-`p` group the two series are moreover cofinal in one another
(`TauCeti.IsProP.exists_pLowerCentralSeries_le_proPFrattiniSeries`). -/
def proPFrattiniSeries : ℕ → Subgroup G
  | 0 => ⊤
  | k + 1 => proPFrattiniStep p (proPFrattiniSeries k)

@[simp]
theorem proPFrattiniSeries_zero : proPFrattiniSeries p G 0 = ⊤ := by
  rw [proPFrattiniSeries]

@[simp]
theorem proPFrattiniSeries_succ (k : ℕ) :
    proPFrattiniSeries p G (k + 1) = proPFrattiniStep p (proPFrattiniSeries p G k) := by
  rw [proPFrattiniSeries]

variable {p G}

/-- Every term of the Frattini series is a normal subgroup. -/
instance proPFrattiniSeries_normal (k : ℕ) : (proPFrattiniSeries p G k).Normal := by
  induction k with
  | zero => rw [proPFrattiniSeries_zero]; infer_instance
  | succ k _ => rw [proPFrattiniSeries_succ]; infer_instance

/-- Every term of the Frattini series is closed. -/
theorem isClosed_proPFrattiniSeries (k : ℕ) :
    IsClosed (proPFrattiniSeries p G k : Set G) := by
  cases k with
  | zero => rw [proPFrattiniSeries_zero, coe_top]; exact isClosed_univ
  | succ k => rw [proPFrattiniSeries_succ]; exact isClosed_proPFrattiniStep _

/-- The Frattini series is descending. -/
theorem proPFrattiniSeries_succ_le (k : ℕ) :
    proPFrattiniSeries p G (k + 1) ≤ proPFrattiniSeries p G k := by
  rw [proPFrattiniSeries_succ]
  exact proPFrattiniStep_le (isClosed_proPFrattiniSeries k)

/-- The Frattini series is antitone. -/
theorem proPFrattiniSeries_antitone : Antitone (proPFrattiniSeries p G) :=
  antitone_nat_of_succ_le proPFrattiniSeries_succ_le

/-- The `p`-th power of an element of `Φ_k` lies in `Φ_{k+1}`. -/
theorem pow_mem_proPFrattiniSeries {k : ℕ} {x : G} (hx : x ∈ proPFrattiniSeries p G k) :
    x ^ p ∈ proPFrattiniSeries p G (k + 1) := by
  rw [proPFrattiniSeries_succ]
  exact pow_mem_proPFrattiniStep hx

/-- The commutators of `Φ_k` with itself lie in `Φ_{k+1}`. -/
theorem commutator_proPFrattiniSeries_le (k : ℕ) :
    ⁅proPFrattiniSeries p G k, proPFrattiniSeries p G k⁆ ≤ proPFrattiniSeries p G (k + 1) := by
  rw [proPFrattiniSeries_succ]
  exact commutator_le_proPFrattiniStep _

/-- **The Frattini series lies below the lower `p`-series**, term by term: the Frattini step takes
commutators inside the subgroup, the lower `p`-series step takes them against the whole group. -/
theorem proPFrattiniSeries_le_pLowerCentralSeries (k : ℕ) :
    proPFrattiniSeries p G k ≤ pLowerCentralSeries p G k := by
  induction k with
  | zero => rw [proPFrattiniSeries_zero, pLowerCentralSeries_zero]
  | succ k ih =>
    rw [proPFrattiniSeries_succ, pLowerCentralSeries_succ]
    exact (proPFrattiniStep_le_pLowerCentralStep _).trans (pLowerCentralStep_mono ih)

/-! ### Functoriality -/

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous homomorphism carries `Φ_k` into `Φ_k`. -/
theorem _root_.MonoidHom.map_proPFrattiniSeries_le (f : G →* H) (hf : Continuous f) (k : ℕ) :
    (proPFrattiniSeries p G k).map f ≤ proPFrattiniSeries p H k := by
  induction k with
  | zero => rw [proPFrattiniSeries_zero]; exact le_top
  | succ k ih =>
    rw [proPFrattiniSeries_succ, proPFrattiniSeries_succ]
    exact (f.map_proPFrattiniStep_le hf _).trans (proPFrattiniStep_mono ih)

/-- A continuous closed surjection (for instance a continuous surjection from a compact group onto
a Hausdorff group, by `Continuous.isClosedMap`) carries `Φ_k` onto `Φ_k`. -/
theorem _root_.MonoidHom.map_proPFrattiniSeries_eq_of_surjective (f : G →* H) (hf : Continuous f)
    (hfc : IsClosedMap f) (hsurj : Function.Surjective f) (k : ℕ) :
    (proPFrattiniSeries p G k).map f = proPFrattiniSeries p H k := by
  induction k with
  | zero =>
    rw [proPFrattiniSeries_zero, proPFrattiniSeries_zero]
    exact map_top_of_surjective f hsurj
  | succ k ih =>
    rw [proPFrattiniSeries_succ, proPFrattiniSeries_succ,
      f.map_proPFrattiniStep_eq_of_isClosedMap hf hfc, ih]

/-- A topological group isomorphism matches the Frattini series of its source and target term by
term. In particular, every term of the Frattini series is stable under continuous
automorphisms. -/
theorem _root_.ContinuousMulEquiv.map_proPFrattiniSeries_eq (e : G ≃ₜ* H) (k : ℕ) :
    (proPFrattiniSeries p G k).map e.toMulEquiv.toMonoidHom = proPFrattiniSeries p H k := by
  refine le_antisymm (MonoidHom.map_proPFrattiniSeries_le _ e.continuous k) fun x hx ↦ ?_
  have hsymm : e.symm x ∈ proPFrattiniSeries p G k :=
    e.symm.toMulEquiv.toMonoidHom.map_proPFrattiniSeries_le e.symm.continuous k
      (mem_map_of_mem _ hx)
  exact ⟨e.symm x, hsymm, e.apply_symm_apply x⟩

end Series

end TauCeti
