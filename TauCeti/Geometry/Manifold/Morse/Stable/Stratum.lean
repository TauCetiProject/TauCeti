/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Compactification
import TauCeti.Data.Fin.Basic

/-!
# The strata of the compactified spaces of trajectories

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f`, and `c i`, for `i` in a type `ι`, regular levels of `f`. The compactified space of
trajectories from `p` to `r` is the closure of their records on the levels `c`, the families of
their points on these levels (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryRecords`). Under the
Morse–Smale condition, for countably many regular levels strictly between `f r` and `f p`, its
points are records of broken trajectories
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`,
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryRecords_subset`): chains of
critical points `p = x 0, …, x k = r` with a trajectory from `x j` to `x (j + 1)` for each `j`.

This file sorts these records by their chain of critical points. The *stratum* of a chain
`x : Fin (k + 1) → M` (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryStratum`) consists of
the records of the broken trajectories through `x`. The records of broken trajectories are the
union of the strata of the chains of critical points from `p` to `r` with consecutive points
distinct (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords_eq_iUnion`), and:

* **Each stratum is the ordered product of the trajectory spaces of its steps.** Along a chain the
  values of `f` decrease, and every level strictly between `f r` and `f p` that is not a value of
  the chain lies strictly between `f (x (j + 1))` and `f (x j)` for exactly one step `j`. A record
  in the stratum of `x` is therefore the same as a family, indexed by the steps `j`, of records of
  trajectories from `x j` to `x (j + 1)` on the levels of step `j`
  (`TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseBrokenTrajectoryStratum`). When every
  step has a level, the stratum is homeomorphic to the product, over the steps, of the spaces of
  unparametrized trajectories from `x j` to `x (j + 1)`
  (`TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseBrokenTrajectoryStratum_orbitQuotient`).
  The stratum of the one-step chain `p, r` is the space of unbroken trajectories
  (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryStratum_eq_morseTrajectoryRecords`).
* **A record determines its chain.** If every step of a chain `x` has a level, a record in the
  stratum of `x` lies in the stratum of no other chain from `x 0` to `x k` with consecutive points
  distinct (`TauCeti.IsAdaptedPseudoGradient.sigma_mk_eq_of_mem_morseBrokenTrajectoryStratum`,
  `TauCeti.IsAdaptedPseudoGradient.disjoint_morseBrokenTrajectoryStratum`). The point of the record
  on a level of step `j` determines the trajectory from `x j` to `x (j + 1)`, whose limits are its
  ends. The record does not see a step without a level, hence the hypothesis.

The strata need no Morse–Smale hypothesis. When `f` is Morse and the Morse–Smale condition holds,
the Morse index drops strictly along each chain with consecutive points distinct, so the stratum
of such a chain from `p` to `r` with `k` steps is empty unless `k ≤ ind p - ind r`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.add_manifoldMorseIndex_le_of_chain`).

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseBrokenTrajectoryStratum`: the records of the broken trajectories through a chain.
* `morseBrokenTrajectoryRecords_eq_iUnion`: the records of broken trajectories are the union of the
  strata.
* `morseBrokenTrajectoryStratum_eq_morseTrajectoryRecords`: the stratum of a one-step chain is the
  space of unbroken trajectories.
* `antitone_apply_of_chain`, `strictAnti_apply_of_chain`: `f` decreases along a chain of critical
  points joined by trajectories, strictly when consecutive points are distinct.
* `value_le_of_mem_morseBrokenTrajectoryRecords`, `value_lt_of_mem_morseBrokenTrajectoryRecords`:
  `f` decreases from the start to the end of a broken trajectory, strictly when they are distinct.
* `exists_flow_eq_of_mem_Ioo`: the point of a record on a level of step `j` lies on the orbit of
  the component of step `j`.
* `mem_unstableSet_inter_stableSet_of_mem_morseBrokenTrajectoryStratum`: the point of a record on a
  level of step `j` lies on a trajectory from `x j` to `x (j + 1)`.
* `exists_homeomorph_morseBrokenTrajectoryStratum`: a stratum is the product of the spaces of
  records of the trajectories of its steps.
* `exists_homeomorph_morseBrokenTrajectoryStratum_orbitQuotient`: when every step has a level, it is
  the product of the spaces of unparametrized trajectories of its steps.
* `sigma_mk_eq_of_mem_morseBrokenTrajectoryStratum`, `disjoint_morseBrokenTrajectoryStratum`: a
  record determines its chain.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of broken trajectories).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the compactified spaces of flow lines and their strata of
  broken flow lines).
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- The stratum of a chain `x 0, …, x k` of points in the records of broken trajectories on the
levels `c`: the families `w` of points with `f (w i) = c i` that each lie on a component of a
broken trajectory through this chain, made of a point `z j` of a trajectory from `x j` to
`x (j + 1)` for each `j`. -/
def morseBrokenTrajectoryStratum {k : ℕ} (x : Fin (k + 1) → M) (c : ι → ℝ) : Set (ι → M) :=
  {w | ∃ z : Fin k → M,
    (∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) ∧
    ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i}

/-- Membership in the stratum of a chain. -/
@[simp]
theorem mem_morseBrokenTrajectoryStratum {k : ℕ} {x : Fin (k + 1) → M} {c : ι → ℝ}
    {w : ι → M} :
    w ∈ hX.morseBrokenTrajectoryStratum x c ↔ ∃ z : Fin k → M,
      (∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) ∧
      ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i :=
  Iff.rfl

/-- **The records of broken trajectories are the union of the strata** of the chains of critical
points from `p` to `r` with consecutive points distinct. -/
theorem morseBrokenTrajectoryRecords_eq_iUnion (p r : M) (c : ι → ℝ) :
    hX.morseBrokenTrajectoryRecords p r c =
      ⋃ (k : ℕ) (x : Fin (k + 1) → M) (_ : x 0 = p ∧ x (Fin.last k) = r ∧
        (∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) ∧ ∀ j : Fin k, x j.castSucc ≠ x j.succ),
        hX.morseBrokenTrajectoryStratum x c := by
  ext w
  simp only [mem_morseBrokenTrajectoryRecords, mem_iUnion, mem_morseBrokenTrajectoryStratum,
    exists_prop]
  constructor
  · rintro ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hw⟩
    exact ⟨k, x, ⟨hx0, hxk, hxc, hxne⟩, z, hz, hw⟩
  · rintro ⟨k, x, ⟨hx0, hxk, hxc, hxne⟩, z, hz, hw⟩
    exact ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hw⟩

/-- **The stratum of a one-step chain is the space of unbroken trajectories.** The broken
trajectories through the chain `p, r` are the trajectories from `p` to `r`. -/
theorem morseBrokenTrajectoryStratum_eq_morseTrajectoryRecords (p r : M) (c : ι → ℝ) :
    hX.morseBrokenTrajectoryStratum ![p, r] c = hX.morseTrajectoryRecords p r c := by
  ext w
  simp only [mem_morseBrokenTrajectoryStratum, mem_morseTrajectoryRecords, Fin.forall_fin_one,
    Fin.exists_fin_one]
  constructor
  · rintro ⟨z, hz, hw⟩
    exact ⟨z 0, hz, hw⟩
  · rintro ⟨y, hy, hw⟩
    exact ⟨![y], hy, hw⟩

/-- **`f` decreases along a chain joined by trajectories.** If each `x j` is joined to `x (j + 1)`
by a trajectory, then `f (x (j + 1)) ≤ f (x j)` for all `j`. -/
theorem antitone_apply_of_chain {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M}
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) :
    Antitone fun j ↦ f (x j) :=
  Fin.antitone_iff_succ_le.2 fun j ↦
    (hX.mem_Icc_of_mem_unstableSet_inter_stableSet (hz j)).1.trans
      (hX.mem_Icc_of_mem_unstableSet_inter_stableSet (hz j)).2

/-- **`f` decreases strictly along a chain of distinct points joined by trajectories.** If each
`x j` is joined to a different point `x (j + 1)` by a trajectory, then `f (x (j + 1)) < f (x j)`
for all `j`. -/
theorem strictAnti_apply_of_chain {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M}
    (hxne : ∀ j : Fin k, x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) :
    StrictAnti fun j ↦ f (x j) :=
  Fin.strictAnti_iff_succ_lt.2 fun j ↦
    (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet (hxne j) (hz j)).1.trans
      (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet (hxne j) (hz j)).2

/-- **The function decreases along a broken trajectory.** If there is a broken trajectory from `p`
to `r`, recorded on any levels, then `f r ≤ f p`. -/
theorem value_le_of_mem_morseBrokenTrajectoryRecords {p r : M} {c : ι → ℝ} {w : ι → M}
    (hw : w ∈ hX.morseBrokenTrajectoryRecords p r c) : f r ≤ f p := by
  obtain ⟨k, x, z, rfl, rfl, -, -, hz, -⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  exact hX.antitone_apply_of_chain hz (Fin.zero_le _)

/-- **The function decreases strictly along a broken trajectory between distinct points.** If there
is a broken trajectory from `p` to `r ≠ p`, recorded on any levels, then `f r < f p`. -/
theorem value_lt_of_mem_morseBrokenTrajectoryRecords {p r : M} {c : ι → ℝ} {w : ι → M}
    (hpr : p ≠ r) (hw : w ∈ hX.morseBrokenTrajectoryRecords p r c) : f r < f p := by
  obtain ⟨k, x, z, rfl, rfl, -, hne, hz, -⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  exact hX.strictAnti_apply_of_chain hne hz
    ((Fin.zero_le _).lt_of_ne fun h ↦ hpr (congrArg x h))

/-- The point of a record of a broken trajectory through `x`, made of the points `z j`, on a level
strictly between `f (x (j + 1))` and `f (x j)` lies on the orbit of `z j`. -/
theorem exists_flow_eq_of_mem_Ioo {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M}
    {c : ι → ℝ} {w : ι → M}
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
    (hw : ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i) {i : ι} {j : Fin k}
    (hij : c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))) : ∃ t, hX.flow t (z j) = w i := by
  obtain ⟨hwc, j', t, ht⟩ := hw i
  -- The point `w i` lies on the trajectory of step `j'`, whose values lie between the values at
  -- the ends of that step; only the step `j` has the value `c i` between them.
  have hj' := hX.mem_Icc_of_mem_unstableSet_inter_stableSet
    (hX.flow.isInvariant_unstableSet_inter_stableSet _ _ t (hz j'))
  rw [ht, hwc] at hj'
  obtain rfl : j = j' := (hX.antitone_apply_of_chain hz).eq_of_mem_Ioo_of_mem_Icc_fin hij hj'
  exact ⟨t, ht⟩

/-- **The points of a record on the levels of a step lie on a trajectory of that step.** The point
of a record in the stratum of `x` on a level strictly between `f (x (j + 1))` and `f (x j)` lies on
a trajectory from `x j` to `x (j + 1)`. -/
theorem mem_unstableSet_inter_stableSet_of_mem_morseBrokenTrajectoryStratum {k : ℕ}
    {x : Fin (k + 1) → M} {c : ι → ℝ} {w : ι → M} (hw : w ∈ hX.morseBrokenTrajectoryStratum x c)
    {i : ι} {j : Fin k} (hij : c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))) :
    w i ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ) := by
  obtain ⟨z, hz, hw⟩ := hw
  obtain ⟨t, ht⟩ := hX.exists_flow_eq_of_mem_Ioo hz hw hij
  exact ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet _ _ t (hz j)

/-- **A stratum is the product of the trajectory spaces of its steps.** Let `x 0, …, x k` be a
chain and `c i` levels strictly between `f (x k)` and `f (x 0)` that are not values of the chain.
Restricting a record to the levels of each step `j`, those strictly between `f (x (j + 1))` and
`f (x j)`, identifies the stratum of `x` with the product over `j` of the records of trajectories
from `x j` to `x (j + 1)` on the levels of step `j`. -/
theorem exists_homeomorph_morseBrokenTrajectoryStratum {k : ℕ} {x : Fin (k + 1) → M}
    {c : ι → ℝ} (hc : ∀ i, c i ∈ Ioo (f (x (Fin.last k))) (f (x 0)))
    (hcx : ∀ i j, c i ≠ f (x j)) :
    ∃ Φ : hX.morseBrokenTrajectoryStratum x c ≃ₜ
        ((j : Fin k) → hX.morseTrajectoryRecords (x j.castSucc) (x j.succ)
          fun i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} ↦ c i),
      ∀ w j i, (Φ w j).val i = w.val i := by
  -- Each level lies strictly between the values at the ends of some step `J i`.
  have hJ (i : ι) : ∃ j : Fin k, c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc)) :=
    (Fin.exists_succ_lt_lt_castSucc (g := fun j ↦ f (x j)) (fun j ↦ (hcx i j).symm) (hc i).2
      (hc i).1).imp fun _ h ↦ ⟨h.1, h.2⟩
  choose J hJ using hJ
  -- Restricting a record of the stratum to the levels of a step gives a record of that step.
  have hfwd (w : ι → M) (hw : w ∈ hX.morseBrokenTrajectoryStratum x c) (j : Fin k) :
      (fun i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} ↦ w i) ∈
        hX.morseTrajectoryRecords (x j.castSucc) (x j.succ)
          fun i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} ↦ c i := by
    obtain ⟨z, hz, hw⟩ := hw
    exact hX.mem_morseTrajectoryRecords.2
      ⟨z j, hz j, fun i ↦ ⟨(hw i).1, hX.exists_flow_eq_of_mem_Ioo hz hw i.property⟩⟩
  -- Conversely, records of the steps assemble into a record of the stratum.
  have hbwd (v : (j : Fin k) → hX.morseTrajectoryRecords (x j.castSucc) (x j.succ)
      fun i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} ↦ c i) :
      (fun i ↦ (v (J i)).val ⟨i, hJ i⟩) ∈ hX.morseBrokenTrajectoryStratum x c := by
    choose y hy hv using fun j ↦ hX.mem_morseTrajectoryRecords.1 (v j).property
    exact ⟨y, hy, fun i ↦ ⟨(hv (J i) ⟨i, hJ i⟩).1, J i, (hv (J i) ⟨i, hJ i⟩).2⟩⟩
  have hcont : Continuous fun (v : (j : Fin k) → hX.morseTrajectoryRecords (x j.castSucc)
      (x j.succ) fun i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} ↦ c i) i ↦
      (v (J i)).val ⟨i, hJ i⟩ :=
    continuous_pi fun i ↦ ((continuous_apply _).comp continuous_subtypeVal).comp
      (continuous_apply (J i))
  refine ⟨
    { toFun w j := ⟨fun i ↦ (w : ι → M) i, hfwd w.val w.property j⟩
      invFun v := ⟨fun i ↦ (v (J i)).val ⟨i, hJ i⟩, hbwd v⟩
      left_inv w := rfl
      right_inv v := funext fun j ↦ Subtype.ext (funext fun i ↦ ?_)
      continuous_toFun := continuous_pi fun j ↦
        (continuous_pi fun i ↦ (continuous_apply i.val).comp continuous_subtypeVal).subtype_mk _
      continuous_invFun := hcont.subtype_mk _ },
    fun w j i ↦ rfl⟩
  -- A level of step `j` is a level of no other step, since `f` decreases along the chain.
  obtain ⟨i, hi⟩ := i
  choose y hy _ using fun j ↦ hX.mem_morseTrajectoryRecords.1 (v j).property
  obtain rfl : J i = j :=
    (hX.antitone_apply_of_chain hy).eq_of_mem_Ioo_of_mem_Icc_fin (hJ i) (Ioo_subset_Icc_self hi)
  rfl

/-- **A stratum is the product of the spaces of unparametrized trajectories of its steps.** Let
`x 0, …, x k` be a chain and `c i` levels strictly between `f (x k)` and `f (x 0)` that are not
values of the chain, with at least one level strictly between `f (x (j + 1))` and `f (x j)` for
every step `j`. Then the stratum of `x` is homeomorphic to the product over `j` of the quotients of
`W^u(x j) ∩ W^s(x (j + 1))` by the orbits of the flow. -/
theorem exists_homeomorph_morseBrokenTrajectoryStratum_orbitQuotient {k : ℕ}
    {x : Fin (k + 1) → M} {c : ι → ℝ} (hc : ∀ i, c i ∈ Ioo (f (x (Fin.last k))) (f (x 0)))
    (hcx : ∀ i j, c i ≠ f (x j))
    (hlev : ∀ j : Fin k, ∃ i, c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))) :
    Nonempty (hX.morseBrokenTrajectoryStratum x c ≃ₜ
      ((j : Fin k) → Quotient (Flow.connectingOrbitSetoid hX.flow (x j.castSucc) (x j.succ)))) := by
  obtain ⟨Φ, -⟩ := hX.exists_homeomorph_morseBrokenTrajectoryStratum hc hcx
  refine ⟨Φ.trans (Homeomorph.piCongrRight fun j ↦ ?_)⟩
  haveI : Nonempty {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} :=
    (hlev j).elim fun i hi ↦ ⟨⟨i, hi⟩⟩
  -- A step with a level strictly between the values at its ends joins distinct points.
  have hne : x j.castSucc ≠ x j.succ := fun h ↦ by
    obtain ⟨i, hi⟩ := hlev j
    exact (hi.1.trans hi.2).ne (by rw [h])
  exact (hX.exists_homeomorph_morseTrajectoryRecords_orbitQuotient hne fun i ↦ i.property).some

/-- **A record determines its chain.** Let `x 0, …, x k` be a chain with a level strictly between
`f (x (j + 1))` and `f (x j)` for every step `j`, and `x' 0, …, x' k'` a chain with the same ends
and consecutive points distinct. If a record lies in the strata of both chains, the chains are
equal. -/
theorem sigma_mk_eq_of_mem_morseBrokenTrajectoryStratum {k k' : ℕ} {x : Fin (k + 1) → M}
    {x' : Fin (k' + 1) → M} {c : ι → ℝ} {w : ι → M} (hx0 : x 0 = x' 0)
    (hxk : x (Fin.last k) = x' (Fin.last k'))
    (hlev : ∀ j : Fin k, ∃ i, c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc)))
    (hxne' : ∀ j : Fin k', x' j.castSucc ≠ x' j.succ)
    (hw : w ∈ hX.morseBrokenTrajectoryStratum x c)
    (hw' : w ∈ hX.morseBrokenTrajectoryStratum x' c) :
    (⟨k, x⟩ : (n : ℕ) × (Fin (n + 1) → M)) = ⟨k', x'⟩ := by
  have hw₀ := hw
  obtain ⟨z', hz', hwz'⟩ := hw'
  -- The chain `x'` is injective, since `f` decreases strictly along it.
  have hinj : Function.Injective x' :=
    Function.Injective.of_comp (f := f) (hX.strictAnti_apply_of_chain hxne' hz').injective
  -- If `x j = x' m`, the step `j` of `x` is a step of `x'` starting at `m`.
  have hstep (j : Fin k) (m : Fin (k' + 1)) (hjm : x j.castSucc = x' m) :
      ∃ j' : Fin k', j'.castSucc = m ∧ x j.succ = x' j'.succ := by
    obtain ⟨i, hi⟩ := hlev j
    have hwi := hX.mem_unstableSet_inter_stableSet_of_mem_morseBrokenTrajectoryStratum hw₀ hi
    obtain ⟨-, j', t, ht⟩ := hwz' i
    have hwi' := ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet _ _ t (hz' j')
    -- The orbit of `w i` has one limit in backward time and one in forward time.
    have hu : x j.castSucc = x' j'.castSucc := by
      by_contra h
      exact disjoint_left.1 (Flow.disjoint_unstableSet h) hwi.1 hwi'.1
    have hs : x j.succ = x' j'.succ := by
      by_contra h
      exact disjoint_left.1 (Flow.disjoint_stableSet h) hwi.2 hwi'.2
    exact ⟨j', hinj (hu.symm.trans hjm), hs⟩
  -- By induction, the two chains agree as long as both are defined.
  have hagree (n : ℕ) (hn : n ≤ k) : ∃ hn' : n ≤ k', x ⟨n, by omega⟩ = x' ⟨n, by omega⟩ := by
    induction n with
    | zero => exact ⟨Nat.zero_le _, hx0⟩
    | succ n ih =>
      obtain ⟨hn', hxn⟩ := ih (by omega)
      obtain ⟨j', hj', hx⟩ := hstep ⟨n, by omega⟩ ⟨n, by omega⟩ hxn
      obtain rfl : (j' : ℕ) = n := congrArg Fin.val hj'
      exact ⟨j'.isLt, hx⟩
  -- At the end of `x`, the chain `x'` reaches its end too.
  obtain ⟨hk, hxk'⟩ := hagree k le_rfl
  obtain rfl : k = k' := congrArg Fin.val (hinj (hxk'.symm.trans hxk))
  congr
  funext j
  exact (hagree j (by omega)).2

/-- **Strata of different chains are disjoint.** Let `x 0, …, x k` be a chain with a level
strictly between `f (x (j + 1))` and `f (x j)` for every step `j`, and `x' 0, …, x' k'` a
different chain with the same ends and consecutive points distinct. Their strata are disjoint. -/
theorem disjoint_morseBrokenTrajectoryStratum {k k' : ℕ} {x : Fin (k + 1) → M}
    {x' : Fin (k' + 1) → M} {c : ι → ℝ} (hx0 : x 0 = x' 0)
    (hxk : x (Fin.last k) = x' (Fin.last k'))
    (hlev : ∀ j : Fin k, ∃ i, c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc)))
    (hxne' : ∀ j : Fin k', x' j.castSucc ≠ x' j.succ)
    (hne : (⟨k, x⟩ : (n : ℕ) × (Fin (n + 1) → M)) ≠ ⟨k', x'⟩) :
    Disjoint (hX.morseBrokenTrajectoryStratum x c) (hX.morseBrokenTrajectoryStratum x' c) :=
  disjoint_left.2 fun _ hw hw' ↦
    hne (hX.sigma_mk_eq_of_mem_morseBrokenTrajectoryStratum hx0 hxk hlev hxne' hw hw')

end IsAdaptedPseudoGradient

end TauCeti
