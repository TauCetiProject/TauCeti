/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Compactification
import TauCeti.Data.Fin.Basic
import TauCeti.Order.Fin.Antitone

/-!
# The strata of the compactified spaces of Morse trajectories

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient field
adapted to `f`. Trajectories and broken trajectories from `p` to `r` are recorded by their points
on levels `c i` strictly between `f r` and `f p`
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryRecords`,
`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`), and the compactified space of
trajectories from `p` to `r` is the closure of the records of unbroken ones.

This file sorts the broken trajectories by the critical points at which they break. For a chain of
critical points `x 0, …, x k`, the **stratum** of the chain
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryStratum`) consists of the records of the
broken trajectories with a component from `x j` to `x (j + 1)` for each `j < k`. The records of
broken trajectories from `p` to `r` are the union of the strata of the chains from `p` to `r`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords_eq_iUnion`), and the stratum of a
chain with one step is the space of unbroken trajectories
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryStratum_eq_morseTrajectoryRecords`).

The main result identifies each stratum with the ordered product of the trajectory spaces of the
steps of its chain. Suppose that no level is a critical value `f (x j)` and that all levels lie
between `f (x k)` and `f (x 0)`. Each level then lies strictly between `f (x (j + 1))` and
`f (x j)` for exactly one step `j`, and the component of a broken trajectory along the chain that
crosses this level is the one from `x j` to `x (j + 1)`. So restricting a record along the chain
to the levels of each step is a homeomorphism from the stratum onto the product over `j` of the
records of trajectories from `x j` to `x (j + 1)` on the levels of that step
(`TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseBrokenTrajectoryStratum`). If moreover
each step has a level, these records form the space of unparametrized trajectories of the step, so
the stratum is homeomorphic to the product of the spaces of unparametrized trajectories from
`x j` to `x (j + 1)`
(`TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseBrokenTrajectoryStratum_orbitQuotient`).
A chain with `k` steps describes the trajectories broken `k - 1` times.

No transversality is used: the identification holds for every adapted pseudo-gradient.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseBrokenTrajectoryStratum`: the records of the broken trajectories along a chain of critical
  points.
* `morseBrokenTrajectoryRecords_eq_iUnion`: the broken trajectories from `p` to `r` are the union
  of the strata of the chains from `p` to `r`.
* `morseBrokenTrajectoryStratum_eq_morseTrajectoryRecords`: the stratum of a chain with one step
  is the space of trajectories.
* `exists_homeomorph_morseBrokenTrajectoryStratum`: a stratum is the product of the records of
  the trajectories of the steps of its chain.
* `exists_homeomorph_morseBrokenTrajectoryStratum_orbitQuotient`: a stratum is the product of
  the spaces of unparametrized trajectories of the steps of its chain.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the compactified moduli spaces of broken flow lines and
  their strata).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of broken trajectories).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- The stratum of a chain of critical points `x 0, …, x k`: the families `w` of points with
`f (w i) = c i` that each lie on a component of one broken trajectory along the chain, that is,
with a point `z j` of a trajectory from `x j` to `x (j + 1)` for each `j`. -/
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

/-- **The broken trajectories are the union of the strata.** The records of broken trajectories
from `p` to `r` are the union of the strata of the chains of critical points from `p` to `r` with
distinct consecutive points. -/
theorem morseBrokenTrajectoryRecords_eq_iUnion (p r : M) (c : ι → ℝ) :
    hX.morseBrokenTrajectoryRecords p r c = ⋃ (k : ℕ) (x : Fin (k + 1) → M)
      (_ : x 0 = p ∧ x (Fin.last k) = r ∧ (∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) ∧
        ∀ j : Fin k, x j.castSucc ≠ x j.succ),
      hX.morseBrokenTrajectoryStratum x c := by
  ext w
  simp only [mem_morseBrokenTrajectoryRecords, mem_iUnion, mem_morseBrokenTrajectoryStratum,
    exists_prop]
  constructor
  · rintro ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hw⟩
    exact ⟨k, x, ⟨hx0, hxk, hxc, hxne⟩, z, hz, hw⟩
  · rintro ⟨k, x, ⟨hx0, hxk, hxc, hxne⟩, z, hz, hw⟩
    exact ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hw⟩

/-- **The top stratum.** The stratum of a chain `x 0, x 1` with one step is the space of
trajectories from `x 0` to `x 1`. -/
theorem morseBrokenTrajectoryStratum_eq_morseTrajectoryRecords (x : Fin 2 → M) (c : ι → ℝ) :
    hX.morseBrokenTrajectoryStratum x c = hX.morseTrajectoryRecords (x 0) (x 1) c := by
  ext w
  simp only [mem_morseBrokenTrajectoryStratum, mem_morseTrajectoryRecords, Fin.forall_fin_one,
    Fin.exists_fin_one, Fin.castSucc_zero, Fin.succ_zero_eq_one]
  constructor
  · rintro ⟨z, hz, hw⟩
    exact ⟨z 0, hz, hw⟩
  · rintro ⟨y, hy, hw⟩
    exact ⟨fun _ ↦ y, hy, hw⟩

/-- Along a trajectory from `a` to `b`, every value of `f` other than `f a` lies strictly between
`f b` and `f a`. If `a = b` the trajectory is the constant one at `a`. -/
private theorem mem_Ioo_of_apply_flow_ne {a b z : M}
    (hz : z ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) (t : ℝ)
    (hne : f (hX.flow t z) ≠ f a) : f (hX.flow t z) ∈ Ioo (f b) (f a) := by
  by_cases hab : a = b
  · subst hab
    rw [hX.eq_of_mem_unstableSet_inter_stableSet hz,
      hX.flow_apply_of_mfderiv_eq_zero (hX.mfderiv_eq_zero_of_mem_stableSet hz.2)] at hne
    exact (hne rfl).elim
  · exact hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hab
      (hX.flow.isInvariant_unstableSet_inter_stableSet a b t hz)

/-- `f` decreases weakly along a chain of critical points joined by trajectories. -/
private theorem antitone_apply_of_mem {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M}
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) :
    Antitone fun j ↦ f (x j) := by
  refine Fin.antitone_iff_succ_le.2 fun j ↦ ?_
  by_cases h : x j.castSucc = x j.succ
  · rw [h]
  · have h' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet h (hz j)
    exact (h'.1.trans h'.2).le

/-- In a record along a chain whose levels avoid the critical values of the chain, the point on a
level strictly between `f (x (j + 1))` and `f (x j)` lies on the component from `x j` to
`x (j + 1)`. -/
private theorem exists_flow_eq_of_mem_Ioo {k : ℕ} {x : Fin (k + 1) → M} {c : ι → ℝ}
    {w : ι → M} {z : Fin k → M}
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
    (hw : ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i) (hreg : ∀ i j, f (x j) ≠ c i)
    {i : ι} {j : Fin k} (hij : c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))) :
    ∃ t, hX.flow t (z j) = w i := by
  obtain ⟨hwi, j', t, ht⟩ := hw i
  have h' : c i ∈ Ioo (f (x j'.succ)) (f (x j'.castSucc)) := by
    rw [← hwi, ← ht]
    exact hX.mem_Ioo_of_apply_flow_ne (hz j') t (by rw [ht, hwi]; exact (hreg i _).symm)
  rw [Fin.eq_of_mem_Ioo_succ_castSucc (g := fun j ↦ f (x j)) (hX.antitone_apply_of_mem hz) hij h']
  exact ⟨t, ht⟩

/-- **A stratum is the product of the trajectory spaces of its steps.** Let `x 0, …, x k` be a
chain of critical points and `c i` levels between `f (x k)` and `f (x 0)` that avoid the values
`f (x j)`. Restricting a record along the chain to the levels between `f (x (j + 1))` and `f (x j)`,
for each step `j`, identifies the stratum of the chain with the product over `j` of the records of
trajectories from `x j` to `x (j + 1)` on these levels. -/
theorem exists_homeomorph_morseBrokenTrajectoryStratum {k : ℕ} {x : Fin (k + 1) → M}
    {c : ι → ℝ} (hreg : ∀ i j, f (x j) ≠ c i)
    (hc : ∀ i, c i ∈ Ioo (f (x (Fin.last k))) (f (x 0))) :
    ∃ Φ : hX.morseBrokenTrajectoryStratum x c ≃ₜ
        ∀ j : Fin k, ↥(hX.morseTrajectoryRecords (x j.castSucc) (x j.succ)
          fun i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} ↦ c i),
      ∀ w j (i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))}),
        (Φ w j : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} → M) i = (w : ι → M) i := by
  -- Each level lies strictly between the values at the two ends of some step `J i`.
  have hJ (i : ι) : ∃ j : Fin k, c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc)) :=
    Fin.exists_succ_lt_lt_castSucc (g := fun j ↦ f (x j)) (hreg i) (hc i).2 (hc i).1
  choose J hJ using hJ
  -- Restricted to the levels of one step, a record along the chain records a trajectory of that
  -- step.
  have hres (w : hX.morseBrokenTrajectoryStratum x c) (j : Fin k) :
      (fun i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} ↦ (w : ι → M) i.1) ∈
        hX.morseTrajectoryRecords (x j.castSucc) (x j.succ) fun i ↦ c i.1 := by
    obtain ⟨z, hz, hw⟩ := w.2
    exact hX.mem_morseTrajectoryRecords.2
      ⟨z j, hz j, fun i ↦ ⟨(hw i.1).1, hX.exists_flow_eq_of_mem_Ioo hz hw hreg i.2⟩⟩
  -- Conversely, records of trajectories of the steps assemble to a record along the chain, whose
  -- point on the level `c i` is taken from the record of the step `J i`.
  have hasm (v : ∀ j : Fin k, ↥(hX.morseTrajectoryRecords (x j.castSucc) (x j.succ)
      fun i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} ↦ c i)) :
      (fun i ↦ (v (J i)).1 ⟨i, hJ i⟩) ∈ hX.morseBrokenTrajectoryStratum x c := by
    choose y hy hv using fun j ↦ hX.mem_morseTrajectoryRecords.1 (v j).2
    exact hX.mem_morseBrokenTrajectoryStratum.2
      ⟨y, hy, fun i ↦ ⟨(hv (J i) ⟨i, hJ i⟩).1, J i, (hv (J i) ⟨i, hJ i⟩).2⟩⟩
  refine ⟨
    { toFun w j := ⟨_, hres w j⟩
      invFun v := ⟨_, hasm v⟩
      left_inv w := rfl
      right_inv v := funext fun j ↦ Subtype.ext (funext fun ⟨i, hi⟩ ↦ ?_)
      continuous_toFun := continuous_pi fun j ↦ (continuous_pi fun i ↦
        (continuous_apply i.1).comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_pi fun i ↦ (continuous_apply _).comp
        (continuous_subtype_val.comp (continuous_apply (J i)))).subtype_mk (hasm ·) },
    fun w j i ↦ rfl⟩
  -- The step `J i` of a level `c i` of the step `j` is `j`, since `f` decreases along the chain.
  have hanti : Antitone fun j ↦ f (x j) :=
    hX.antitone_apply_of_mem fun j ↦ (hX.mem_morseTrajectoryRecords.1 (v j).2).choose_spec.1
  have hJi : J i = j := Fin.eq_of_mem_Ioo_succ_castSucc (g := fun j ↦ f (x j)) hanti (hJ i) hi
  have key : ∀ (j' : Fin k) (_ : j' = j) (hi' : c i ∈ Ioo (f (x j'.succ)) (f (x j'.castSucc))),
      (v j').1 ⟨i, hi'⟩ = (v j).1 ⟨i, hi⟩ := by
    rintro _ rfl _
    rfl
  exact key _ hJi _

/-- **A stratum is the product of the spaces of unparametrized trajectories of its steps.** Let
`x 0, …, x k` be a chain of critical points and `c i` levels between `f (x k)` and `f (x 0)` that
avoid the values `f (x j)`, with at least one level between `f (x (j + 1))` and `f (x j)` for each
step `j`. Then the stratum of the chain is homeomorphic to the product over `j` of the quotients of
`W^u(x j) ∩ W^s(x (j + 1))` by the orbits of the flow. -/
theorem exists_homeomorph_morseBrokenTrajectoryStratum_orbitQuotient {k : ℕ}
    {x : Fin (k + 1) → M} {c : ι → ℝ} (hreg : ∀ i j, f (x j) ≠ c i)
    (hc : ∀ i, c i ∈ Ioo (f (x (Fin.last k))) (f (x 0)))
    (hstep : ∀ j : Fin k, ∃ i, c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))) :
    Nonempty (hX.morseBrokenTrajectoryStratum x c ≃ₜ
      ∀ j : Fin k, Quotient (Flow.connectingOrbitSetoid hX.flow (x j.castSucc) (x j.succ))) := by
  obtain ⟨Φ, -⟩ := hX.exists_homeomorph_morseBrokenTrajectoryStratum hreg hc
  have he (j : Fin k) : Nonempty (↥(hX.morseTrajectoryRecords (x j.castSucc) (x j.succ)
      fun i : {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} ↦ c i) ≃ₜ
        Quotient (Flow.connectingOrbitSetoid hX.flow (x j.castSucc) (x j.succ))) := by
    obtain ⟨i, hi⟩ := hstep j
    have : Nonempty {i // c i ∈ Ioo (f (x j.succ)) (f (x j.castSucc))} := ⟨⟨i, hi⟩⟩
    exact hX.exists_homeomorph_morseTrajectoryRecords_orbitQuotient
      (fun h ↦ (hi.1.trans hi.2).ne' (congrArg f h)) fun i ↦ i.2
  exact ⟨Φ.trans (Homeomorph.piCongrRight fun j ↦ (he j).some)⟩

end IsAdaptedPseudoGradient

end TauCeti
