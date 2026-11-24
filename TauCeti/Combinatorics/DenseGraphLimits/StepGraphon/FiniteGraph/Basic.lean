/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.OfMatrix
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Average
public import TauCeti.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.UniformOn
import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Pullback
import TauCeti.Probability.Distributions.Uniform.Finite

/-!
# A finite graph as a graphon

`finiteGraphGraphon G` is the graphon `W_G` of a finite graph `G` on `Fin m`: the step graphon on
the `m` equal cells of `(I, volume)` taking the value `1` on the rectangle `cell i × cell j` when
`i ~ j` in `G`, and `0` otherwise.

Its defining property is **finite-graph compatibility**: the graphon homomorphism density of a
finite pattern `F` in `W_G` is the finite homomorphism density of `F` in `G`,

`t(F, W_G) = hom(F, G) / m ^ |V(F)|`,

which is `homDensity_finiteGraphGraphon`. That is what makes the graphon theory an extension of the
finite theory rather than a parallel one: every finite graph sits in the graphon world with its
densities unchanged, and the sampling and mixture results read a sampled finite graph back as a
point of the graphon space along this map.

## Why the definition goes through `ℕ`

`finiteGraphGraphon` has to be total in `m`, and there is no map `I → Fin 0`. The value is
therefore read off `G.map Fin.valEmbedding`, the transport of `G` to a graph on `ℕ` in which every
vertex outside `[0, m)` is isolated, evaluated at the `ℕ`-valued cell index `unitInterval.cellIdx`.
At `m = 0` that graph has no edges and `finiteGraphGraphon G` is the zero graphon — which is why
`homDensity_finiteGraphGraphon` carries `0 < m`: for a *nonempty* vertex type and a pattern with no
edges the graphon density is `1`, while there is no map `V → Fin 0`, so the finite density is
`0 / 0 ^ |V(F)| = 0 / 0 = 0`. (For an empty vertex type both sides are `1` even at `m = 0`.)

Symmetry of the value is then the symmetry of an adjacency relation, with no case analysis on `m`,
and measurability is a composition through the countable discrete space `ℕ × ℕ`.

## Main definitions

* `TauCeti.DenseGraphLimits.finiteGraphGraphon` — the graphon of a finite graph.
* `TauCeti.DenseGraphLimits.finiteGraphGraphonOnFin` — the same graph on the uniform finite
  carrier.

## Main results

* `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply` — the defining value, at the level of the
  `ℕ`-valued cell indices;
* `TauCeti.DenseGraphLimits.finiteGraphGraphon_eq_const_zero` — the value for the empty host;
* `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_fin`,
  `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_of_adj`,
  `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_of_not_adj`,
  `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_of_cellIdx_eq` — the value in terms of the
  adjacency of `G` itself, on `Fin m`;
* `TauCeti.DenseGraphLimits.finiteGraphGraphon_eq_comap` — the unit-interval graphon is the
  pullback of the uniform finite-carrier graphon;
* `TauCeti.DenseGraphLimits.exists_stepGraphon_eq_finiteGraphGraphon` — the graphon of a finite
  graph is a `stepGraphon` on the partition of the unit interval into its `m` cells, and
  `TauCeti.DenseGraphLimits.stepGraphonAvg_finiteGraphGraphon` — it is its own block average
  over those cells;
* `TauCeti.DenseGraphLimits.homDensity_eq_homDensityFin_of_apply_eq_ite` — finite-graph
  compatibility for a graphon that is the adjacency indicator of a graph on a nonempty finite
  carrier with its uniform measure; the carrier's σ-algebra need not be discrete, but the
  indicator must then be measurable for it;
* `TauCeti.DenseGraphLimits.homDensity_finiteGraphGraphonOnFin`,
  `TauCeti.DenseGraphLimits.homDensity_finiteGraphGraphon` — finite-graph compatibility, on the
  uniform finite carrier `Fin m` and on the unit interval.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.unitInterval

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {m : ℕ}

open scoped Classical in
/-- The **graphon of a finite graph** `G` on `Fin m`: the step graphon on the `m` equal cells of
`(I, volume)` whose value on `cell i × cell j` is `1` if `i ~ j` in `G` and `0` otherwise.

The adjacency is read off `G.map Fin.valEmbedding`, the transport of `G` to `ℕ`, so that the
definition is total in `m`; see the module docstring. Use `finiteGraphGraphon_apply_fin` and the
rectangle lemmas `finiteGraphGraphon_apply_of_adj`, `finiteGraphGraphon_apply_of_not_adj` to
evaluate in terms of the adjacency of `G` on `Fin m`. -/
def finiteGraphGraphon (G : SimpleGraph (Fin m)) : Graphon I (volume : Measure I) where
  toFun x y := if (G.map Fin.valEmbedding).Adj (cellIdx m x) (cellIdx m y) then 1 else 0
  symm' x y := by
    by_cases h : (G.map Fin.valEmbedding).Adj (cellIdx m x) (cellIdx m y)
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]
  meas' :=
    (measurable_of_countable fun q : ℕ × ℕ =>
        if (G.map Fin.valEmbedding).Adj q.1 q.2 then (1 : ℝ) else 0).comp
      ((measurable_cellIdx.comp measurable_fst).prodMk (measurable_cellIdx.comp measurable_snd))
  bdd' := ⟨1, fun x y => by split_ifs <;> simp⟩
  mem01' x y := by split_ifs <;> simp

variable {G : SimpleGraph (Fin m)} {x y : I} {i j : Fin m}

open scoped Classical in
/-- The defining value of `finiteGraphGraphon`, at the level of the `ℕ`-valued cell indices and the
transported graph `G.map Fin.valEmbedding`.

The lemmas below state the same value in terms of the adjacency of `G` on `Fin m`, which is the
form callers should use. -/
theorem finiteGraphGraphon_apply (G : SimpleGraph (Fin m)) (x y : I) :
    finiteGraphGraphon G x y =
      if (G.map Fin.valEmbedding).Adj (cellIdx m x) (cellIdx m y) then 1 else 0 := (rfl)

/-- The graphon of the unique graph on the empty vertex type is the constant-zero graphon. -/
@[simp]
theorem finiteGraphGraphon_eq_const_zero (G : SimpleGraph (Fin 0)) :
    finiteGraphGraphon G = Graphon.const volume 0 := by
  ext x y
  rw [finiteGraphGraphon_apply, Graphon.const_apply, ite_eq_right]
  · rfl
  · rw [SimpleGraph.map_adj]
    rintro ⟨i, _, _⟩
    exact Fin.elim0 i

private theorem map_valEmbedding_adj_iff (G : SimpleGraph (Fin m)) (i j : Fin m) :
    (G.map Fin.valEmbedding).Adj (i : ℕ) (j : ℕ) ↔ G.Adj i j := by
  simpa only [Fin.valEmbedding_apply] using
    (SimpleGraph.map_adj_apply (G := G) (f := Fin.valEmbedding) (a := i) (b := j))

/-- On a rectangle `cell i × cell j` spanned by an edge of `G`, the graphon takes the value `1`. -/
theorem finiteGraphGraphon_apply_of_adj (hij : G.Adj i j) (hx : cellIdx m x = i)
    (hy : cellIdx m y = j) : finiteGraphGraphon G x y = 1 := by
  rw [finiteGraphGraphon_apply, ite_eq_left]
  rw [hx, hy]
  exact (map_valEmbedding_adj_iff G i j).2 hij

/-- On a rectangle `cell i × cell j` spanned by a non-edge of `G`, the graphon takes the value
`0`. -/
theorem finiteGraphGraphon_apply_of_not_adj (hij : ¬ G.Adj i j) (hx : cellIdx m x = i)
    (hy : cellIdx m y = j) : finiteGraphGraphon G x y = 0 := by
  rw [finiteGraphGraphon_apply, ite_eq_right]
  rw [hx, hy]
  exact fun h => hij ((map_valEmbedding_adj_iff G i j).1 h)

/-- Evaluating the graphon of a finite graph on a rectangle of cells, in `if`-form. -/
theorem finiteGraphGraphon_apply_of_cellIdx_eq [DecidableRel G.Adj] (hx : cellIdx m x = i)
    (hy : cellIdx m y = j) : finiteGraphGraphon G x y = if G.Adj i j then 1 else 0 := by
  by_cases hij : G.Adj i j
  · rw [ite_eq_left hij, finiteGraphGraphon_apply_of_adj hij hx hy]
  · rw [ite_eq_right hij, finiteGraphGraphon_apply_of_not_adj hij hx hy]

/-- The value of `finiteGraphGraphon` at an arbitrary pair of points, in terms of the adjacency of
`G` between the cells containing them. -/
@[simp]
theorem finiteGraphGraphon_apply_fin (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hm : 0 < m) (x y : I) : finiteGraphGraphon G x y =
      if G.Adj ⟨cellIdx m x, cellIdx_lt hm x⟩ ⟨cellIdx m y, cellIdx_lt hm y⟩ then 1 else 0 :=
  finiteGraphGraphon_apply_of_cellIdx_eq rfl rfl

open scoped Classical in
/-- A graph on `Fin m` as a graphon on its uniform finite carrier. -/
def finiteGraphGraphonOnFin [NeZero m] (G : SimpleGraph (Fin m)) :
    Graphon (Fin m) (uniformOn Set.univ) :=
  Graphon.ofMatrix _ (fun i j => if G.Adj i j then 1 else 0) fun i j => by
    simp only [G.adj_comm]

open scoped Classical in
/-- The uniform finite-carrier graphon is the adjacency indicator of `G`. -/
@[simp]
theorem finiteGraphGraphonOnFin_apply [NeZero m] (G : SimpleGraph (Fin m)) (i j : Fin m) :
    finiteGraphGraphonOnFin G i j = if G.Adj i j then 1 else 0 := by
  simp [finiteGraphGraphonOnFin, apply_ite Subtype.val]

open scoped Classical in
/-- The graphon of a finite graph is the pullback of its uniform-carrier graphon along the cells of
the unit interval. -/
theorem finiteGraphGraphon_eq_comap [NeZero m] (G : SimpleGraph (Fin m)) :
    finiteGraphGraphon G =
      (finiteGraphGraphonOnFin G).comap (cellFin m) measurable_cellFin volume := by
  ext x y
  have hcell : ∀ z : I, cellFin m z = ⟨cellIdx m z, cellIdx_lt (NeZero.pos m) z⟩ := fun z =>
    Fin.ext (coe_cellFin z)
  rw [finiteGraphGraphon_apply_fin G (NeZero.pos m), Graphon.comap_apply,
    finiteGraphGraphonOnFin_apply, hcell, hcell]

/-- **A finite graph as a step graphon.** The graphon of a finite graph on `Fin m` is a step graphon
on the partition of the unit interval into its `m` cells, the fibres of `cellFin m`. -/
theorem exists_stepGraphon_eq_finiteGraphGraphon [NeZero m] (G : SimpleGraph (Fin m)) :
    ∃ (val : (Finpartition.ofFibers (cellFin m)).parts →
        (Finpartition.ofFibers (cellFin m)).parts → Set.Icc (0 : ℝ) 1)
      (hsymm : ∀ p q, val p q = val q p),
      stepGraphon (μ := volume) (Finpartition.ofFibers (cellFin m))
          (fun _ hp => Finpartition.measurableSet_of_mem_ofFibers measurable_cellFin hp) val
          hsymm =
        finiteGraphGraphon G := by
  rw [finiteGraphGraphon_eq_comap]
  exact exists_stepGraphon_ofFibers_eq_comap _ measurable_cellFin

/-- **The graphon of a finite graph is its own block average** over the `m` cells of the unit
interval: every cell has volume `1 / m`, so averaging over the cell rectangles returns the
adjacency indicator unchanged. -/
@[simp]
theorem stepGraphonAvg_finiteGraphGraphon [NeZero m] (G : SimpleGraph (Fin m)) :
    stepGraphonAvg (μ := volume) (Finpartition.ofFibers (cellFin m))
        (fun _ hp => Finpartition.measurableSet_of_mem_ofFibers measurable_cellFin hp)
        (finiteGraphGraphon G) =
      finiteGraphGraphon G := by
  rw [finiteGraphGraphon_eq_comap]
  refine stepGraphonAvg_ofFibers_comap _ measurable_cellFin fun x => ?_
  rw [preimage_cellFin_singleton, volume_preimage_cellIdx (cellFin m x).isLt]
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m)

variable {V : Type*} [Fintype V]

/-- **Finite-graph compatibility on a uniform finite carrier.** If the graphon `W` on a nonempty
finite carrier with its uniform measure is the adjacency indicator of a graph `G` on the carrier,
the graphon homomorphism density of `F` in `W` is the finite homomorphism density of `F` in `G`.

The carrier's σ-algebra need not be discrete. Since `W` is a graphon, `hW` can hold only if the
adjacency indicator of `G` is measurable for that σ-algebra on `Ω × Ω`; for a discrete carrier
such as `Fin m` this is automatic. -/
theorem homDensity_eq_homDensityFin_of_apply_eq_ite {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] (F : SimpleGraph V) [DecidableRel F.Adj] {G : SimpleGraph Ω}
    [DecidableRel G.Adj] {W : Graphon Ω (uniformOn Set.univ)}
    (hW : ∀ a b, W a b = if G.Adj a b then 1 else 0) :
    homDensity F W = homDensityFin F G := by
  classical
  -- pull `W` back along a bijection from `Fin (Fintype.card Ω)` so every subset is measurable
  have : NeZero (Fintype.card Ω) := ⟨Fintype.card_ne_zero⟩
  let e : Fin (Fintype.card Ω) ≃ Ω := (Fintype.equivFin Ω).symm
  have he : MeasurePreserving e (uniformOn Set.univ) (uniformOn Set.univ) :=
    e.measurePreserving_uniformOn_univ .of_discrete
  have hcomap : ∀ i j, W.comap e he.measurable (uniformOn Set.univ) i j =
      if (G.comap e).Adj i j then 1 else 0 := fun i j => by
    simpa only [Graphon.comap_apply, SimpleGraph.comap_adj] using hW (e i) (e j)
  calc homDensity F W
      = homDensity F (W.comap e he.measurable (uniformOn Set.univ)) :=
        (homDensity_comap F W he).symm
    _ = ∫ ψ : V → Fin (Fintype.card Ω), ((Finset.univ.filter fun ψ : V → Fin (Fintype.card Ω) =>
            ∀ a b, F.Adj a b → (G.comap e).Adj (ψ a) (ψ b)) :
          Set (V → Fin (Fintype.card Ω))).indicator 1 ψ ∂uniformOn Set.univ := by
        rw [homDensity_def, ← uniformOn_pi, Set.pi_univ]
        congr 1 with ψ
        rw [prod_edgeFactor_eq_ite_of_apply_eq_ite F hcomap, Finset.coe_filter, Set.indicator_apply]
        simp
    _ = homDensityFin F G := by
        rw [integral_indicator_one (Finset.measurableSet _), Finset.uniformOn_univ_real_finset,
          ← F.card_hom_eq_card_filter_adjPreserving (G.comap e),
          Nat.card_congr (SimpleGraph.Iso.refl.homCongr (SimpleGraph.Iso.comap e G)),
          homDensityFin_def, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- **Finite-graph compatibility on the uniform finite carrier `Fin m`.** The graphon
homomorphism density of `F` in the graphon of `G` on `Fin m` is the finite homomorphism density of
`F` in `G`. -/
@[simp]
theorem homDensity_finiteGraphGraphonOnFin [NeZero m] (F : SimpleGraph V) [DecidableRel F.Adj]
    (G : SimpleGraph (Fin m)) :
    homDensity F (finiteGraphGraphonOnFin G) = homDensityFin F G := by
  classical
  exact homDensity_eq_homDensityFin_of_apply_eq_ite F (finiteGraphGraphonOnFin_apply G)

/-- **Finite-graph compatibility.** The graphon homomorphism density of `F` in the graphon of a
finite graph `G` on `Fin m` is the finite homomorphism density of `F` in `G`:

`t(F, W_G) = hom(F, G) / m ^ |V(F)|`.

Positivity of `m` is needed when `V` is nonempty: at `m = 0` and a pattern with no edges the
left-hand side is `1`, while the right-hand side is `0 / 0 = 0`. -/
@[simp]
theorem homDensity_finiteGraphGraphon (F : SimpleGraph V) [DecidableRel F.Adj] (hm : 0 < m)
    (G : SimpleGraph (Fin m)) :
    homDensity F (finiteGraphGraphon G) = homDensityFin F G := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [finiteGraphGraphon_eq_comap, homDensity_comap F _ measurePreserving_cellFin,
    homDensity_finiteGraphGraphonOnFin]

end DenseGraphLimits

end TauCeti
