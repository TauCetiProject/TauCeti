/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.HatDifferential
public import TauCeti.LowDimTopology.Heegaard.MapRegion
public import TauCeti.LowDimTopology.Heegaard.RelativeGrading
public import TauCeti.LowDimTopology.Heegaard.SpincAdmissibility
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The singly pointed diagram obtained by joining the basepoint regions

Let `(Σ, α, β, z₁, …, z_b)` be a balanced multipointed Heegaard diagram of a closed `3`-manifold
`Y`: `Σ` has genus `g`, there are `n = g + b - 1` curves of each kind, and each component of
`Σ - α` and of `Σ - β` contains exactly one basepoint. Attaching `b - 1` tubes to `Σ`, each
joining two of the regions containing basepoints, gives a surface of genus `n` with `n` curves of
each kind, a singly pointed Heegaard diagram of `Y_b = Y # (S¹ × S²) # ⋯ # (S¹ × S²)`, with
`b - 1` copies of `S¹ × S²`. This is the auxiliary diagram through which Ozsváth, Stipsicz and
Szabó compare the twisted complexes of a multipointed diagram with those of `Y_b`.

On the incidence data `TauCeti.HeegaardRegionSystem` the tubes only join regions: the curves,
their intersection points and the order of the points along them are unchanged, and the regions
containing basepoints become one region. This file builds that system
(`TauCeti.HeegaardRegionSystem.joinBasepoints`) from the relabelling of regions
`TauCeti.HeegaardRegionSystem.joinRegion`, which sends the regions containing basepoints to the
joined region `none` of `TauCeti.HeegaardRegionSystem.JoinedRegion` and every other region `r` to
`some r`. The joined region carries the single basepoint. Each tube lowers the Euler
characteristic by two, so when the basepoints lie in distinct regions the joined region has Euler
characteristic `∑ᵢ χ(R_{zᵢ}) - 2 (b - 1)` (`TauCeti.HeegaardRegionSystem.joinedEuler`), and when
moreover the original regions assemble a surface of genus `g` the joined ones assemble a surface
of genus `g + b - 1` (`TauCeti.HeegaardRegionSystem.sum_joinedEuler_sub_card_eq`).

The two systems have the same generators, and a domain `D` of the joined system is read on the
original one as `D ∘ joinRegion`, which takes one value on all the regions containing basepoints.
The lemmas of `TauCeti.LowDimTopology.Heegaard.MapRegion` apply to `joinBasepoints`, which is
`TauCeti.HeegaardRegionSystem.mapRegion` for this relabelling. The comparisons proved here are:

* **Periodic domains.** A periodic domain of the joined system avoids the joined region, so its
  pullback avoids every basepoint, and every periodic domain of the multipointed system arises
  in this way exactly once
  (`TauCeti.HeegaardRegionSystem.joinBasepointsPeriodicDomainsEquiv`). On a geometric diagram
  both groups are `H₂(Y_b; ℤ)` (this identification is not formalized here): besides the classes
  of `H₂(Y; ℤ)`, the multipointed periodic domains include the differences of the components of
  `Σ - α` and of `Σ - β` around a basepoint, which become the spheres of the `S¹ × S²` summands.
  The two systems are weakly admissible together
  (`TauCeti.HeegaardRegionSystem.weaklyAdmissible_joinBasepoints_iff`), and weakly admissible at a
  generator together (`TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_joinBasepoints_iff`).
* **Maslov indices.** When the basepoints lie in distinct regions, for the joined Euler
  characteristics a domain `D` has
  `μ(D) = μ(D ∘ joinRegion) - 2 (b - 1) n_z(D)`
  (`TauCeti.HeegaardRegionSystem.maslovIndex_joinBasepoints`), since the point measures are
  unchanged. As `D ∘ joinRegion` has multiplicity `n_z(D)` at each of the `b` basepoints, the
  grading quantity `μ(D) - 2 n_z(D)` of the joined diagram is the quantity
  `μ - 2 ∑ᵢ n_{zᵢ}` of the multipointed one
  (`TauCeti.HeegaardRegionSystem.maslovIndex_joinBasepoints_sub_two_mul_sum`). On domains
  avoiding the joined region the Euler characteristic of the joined region plays no role, so the
  periodic Maslov indices agree for every choice of it
  (`TauCeti.HeegaardRegionSystem.periodicMaslovIndices_joinBasepoints`).
* **Hat counts.** The domains counted by the hat differential avoid every basepoint, so they are
  the same for both systems
  (`TauCeti.HeegaardRegionSystem.hatDomains_joinBasepoints`), and the two hat differentials on the
  common chain group coincide (`TauCeti.HeegaardRegionSystem.hatDifferential_joinBasepoints`).
* **Relative gradings.** When the basepoints lie in distinct components of `Σ - α`, the domains of
  these components equalize the basepoint multiplicities of any domain, so generators are joined
  by a domain of the joined system exactly when they are joined by a domain of the multipointed
  one (`TauCeti.HeegaardRegionSystem.exists_isDomainBetween_joinBasepoints_iff`). The relative
  grading of the joined system is normalized whenever that of the multipointed system is
  (`maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_joinBasepoints`),
  and then the two relative gradings agree modulo the periodic Maslov indices
  (`TauCeti.HeegaardRegionSystem.coe_relativeGrading_joinBasepoints`).

## Main definitions

* `TauCeti.HeegaardRegionSystem.JoinedRegion`: the regions after joining those containing
  basepoints.
* `TauCeti.HeegaardRegionSystem.joinRegion`: the relabelling of regions.
* `TauCeti.HeegaardRegionSystem.joinBasepoints`: the singly pointed system with the joined region.
* `TauCeti.HeegaardRegionSystem.joinedEuler`: the Euler characteristics of the joined regions.
* `TauCeti.HeegaardRegionSystem.joinBasepointsPeriodicDomainsEquiv`: the periodic domains of the
  two systems.

## References

* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830), §10
  (the stable and twisted invariants of multipointed diagrams, and their comparison with
  `Y # (S¹ × S²) # ⋯ # (S¹ × S²)`).
* P. Ozsváth and Z. Szabó, *Holomorphic disks, link invariants and the multi-variable Alexander
  polynomial*, Algebr. Geom. Topol. **8** (2008),
  [arXiv:math/0512286](https://arxiv.org/abs/math/0512286), §3 (multipointed Heegaard diagrams).
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

open Function

/-! ### The joined regions -/

/-- The regions of `H` after the regions containing basepoints are joined into one: the joined
region `none`, and a region `some r` for every region `r` containing no basepoint. -/
abbrev JoinedRegion : Type v :=
  Option {r : Region // r ∉ Set.range H.basepoint}

open scoped Classical in
/-- The joined regions of finitely many regions are finitely many. -/
noncomputable instance [Fintype Region] : Fintype H.JoinedRegion :=
  inferInstanceAs (Fintype (Option _))

open scoped Classical in
/-- The relabelling of the regions of `H` that joins the regions containing basepoints: they go to
the joined region `none`, and every other region `r` goes to `some r`. -/
noncomputable def joinRegion (r : Region) : H.JoinedRegion :=
  if h : r ∈ Set.range H.basepoint then none else some ⟨r, h⟩

/-- A region containing a basepoint is sent to the joined region. -/
@[simp]
theorem joinRegion_basepoint (z : Basepoint) : H.joinRegion (H.basepoint z) = none := by
  simp [joinRegion]

/-- A region containing no basepoint is kept. -/
theorem joinRegion_of_notMem {r : Region} (h : r ∉ Set.range H.basepoint) :
    H.joinRegion r = some ⟨r, h⟩ := by
  simp [joinRegion, h]

/-- A region `s` containing no basepoint is sent to `some s`. -/
@[simp]
theorem joinRegion_coe (s : {r : Region // r ∉ Set.range H.basepoint}) :
    H.joinRegion s = some s :=
  H.joinRegion_of_notMem s.property

/-- A region is sent to the joined region exactly when it contains a basepoint. -/
@[simp]
theorem joinRegion_eq_none_iff {r : Region} : H.joinRegion r = none ↔ r ∈ Set.range H.basepoint :=
  ⟨fun h => by_contra fun h' => by simp [H.joinRegion_of_notMem h'] at h,
    fun ⟨z, hz⟩ => hz ▸ H.joinRegion_basepoint z⟩

/-- When there is a basepoint, every joined region comes from a region of `H`. -/
theorem joinRegion_surjective [Nonempty Basepoint] : Surjective H.joinRegion := by
  rintro (_ | s)
  · exact ⟨H.basepoint (Classical.arbitrary Basepoint), H.joinRegion_basepoint _⟩
  · exact ⟨s, H.joinRegion_coe s⟩

/-- A domain of `H` is the pullback of a domain of the joined regions exactly when it has the same
multiplicity at all the basepoints. -/
theorem exists_comp_joinRegion_eq_iff {D : Region → ℤ} :
    (∃ D' : H.JoinedRegion → ℤ, D' ∘ H.joinRegion = D) ↔
      ∀ z z', D (H.basepoint z) = D (H.basepoint z') := by
  constructor
  · rintro ⟨D', rfl⟩ z z'
    simp
  · intro hD
    classical
    -- the value on the joined region is the common value at the basepoints
    let c : ℤ := if h : Nonempty Basepoint then D (H.basepoint h.some) else 0
    refine ⟨fun r => r.elim c fun s => D s, funext fun r => ?_⟩
    by_cases hr : r ∈ Set.range H.basepoint
    · obtain ⟨z, rfl⟩ := hr
      simp [c, (⟨z⟩ : Nonempty Basepoint), hD _ z]
    · simp [H.joinRegion_of_notMem hr]

/-- A region is sent to the kept region `some s` exactly when it is `s`. -/
@[simp]
theorem joinRegion_eq_some_iff {r : Region} {s : {r : Region // r ∉ Set.range H.basepoint}} :
    H.joinRegion r = some s ↔ r = s := by
  by_cases hr : r ∈ Set.range H.basepoint
  · obtain ⟨z, rfl⟩ := hr
    simp only [joinRegion_basepoint, reduceCtorEq, false_iff]
    exact fun h => s.property (h ▸ ⟨z, rfl⟩)
  · rw [H.joinRegion_of_notMem hr, Option.some_inj, Subtype.ext_iff]

/-! ### Euler characteristics of the joined regions -/

section Sum

variable [Fintype Region]

/-- For Euler characteristics `χ'` of the joined regions agreeing with `χ` on the kept regions,
the Euler measures of a domain `D` of the joined regions and of its pullback differ only at the
joined region, by `χ'` of the joined region minus the Euler characteristics of the regions that
are joined. -/
private theorem sum_mul_sub_sum_mul_comp_joinRegion {χ : Region → ℤ} {χ' : H.JoinedRegion → ℤ}
    (hχ' : ∀ s, χ' (some s) = χ s) (D : H.JoinedRegion → ℤ) :
    ∑ r', (χ' r' : ℚ) * D r' - ∑ r, (χ r : ℚ) * D (H.joinRegion r) =
      ((χ' none : ℚ) - ∑ r with H.joinRegion r = none, (χ r : ℚ)) * D none := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ H.joinRegion, ← Finset.sum_sub_distrib,
    Fintype.sum_eq_single none]
  · rw [sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.1 hr).2]
  · rintro (_ | s) hs
    · exact absurd rfl hs
    · have : (Finset.univ.filter fun r => H.joinRegion r = some s) = {s.val} := by
        ext r
        simp [joinRegion_eq_some_iff]
      rw [this, Finset.sum_singleton, H.joinRegion_coe, hχ', sub_self]

/-- When the basepoints lie in distinct regions, the regions joined into one are the regions of the
basepoints, each counted once. -/
private theorem sum_joinRegion_eq_none [Fintype Basepoint] (hinj : Injective H.basepoint)
    (χ : Region → ℤ) :
    ∑ r with H.joinRegion r = none, (χ r : ℚ) = ∑ z, (χ (H.basepoint z) : ℚ) := by
  classical
  rw [show (Finset.univ.filter fun r => H.joinRegion r = none) = Finset.univ.image H.basepoint by
      ext r
      simp [joinRegion_eq_none_iff],
    Finset.sum_image fun _ _ _ _ h => hinj h]

end Sum

section Euler

variable [Fintype Basepoint]

/-- **The Euler characteristics of the joined regions.** A region containing no basepoint keeps
its Euler characteristic `χ`, and the joined region has Euler characteristic
`∑ᵢ χ(R_{zᵢ}) - 2 (b - 1)`. When the `b` basepoints lie in distinct regions, this is the Euler
characteristic of the tubed surface, since each of the `b - 1` tubes joining the `b` regions
containing basepoints lowers the Euler characteristic by two. -/
def joinedEuler (χ : Region → ℤ) : H.JoinedRegion → ℤ
  | none => ∑ z, χ (H.basepoint z) - 2 * (Fintype.card Basepoint - 1)
  | some r => χ r

/-- The joined region has Euler characteristic `∑ᵢ χ(R_{zᵢ}) - 2 (b - 1)`. -/
@[simp]
theorem joinedEuler_none (χ : Region → ℤ) :
    H.joinedEuler χ none = ∑ z, χ (H.basepoint z) - 2 * (Fintype.card Basepoint - 1) :=
  (rfl)

/-- A region containing no basepoint keeps its Euler characteristic. -/
@[simp]
theorem joinedEuler_some (χ : Region → ℤ) (s : {r : Region // r ∉ Set.range H.basepoint}) :
    H.joinedEuler χ (some s) = χ s :=
  (rfl)

/-- **The total Euler characteristic of the joined regions.** When the basepoints lie in
distinct regions, the sum of the joined Euler characteristics is that of the original ones minus
`2 (b - 1)`. -/
theorem sum_joinedEuler [Fintype Region] (hinj : Injective H.basepoint) (χ : Region → ℤ) :
    ∑ r, H.joinedEuler χ r = ∑ r, χ r - 2 * (Fintype.card Basepoint - 1) := by
  have h := H.sum_mul_sub_sum_mul_comp_joinRegion (joinedEuler_some H χ) 1
  rw [H.sum_joinRegion_eq_none hinj, joinedEuler_none] at h
  push_cast [Pi.one_apply, mul_one] at h
  have h' : ∑ r, (H.joinedEuler χ r : ℚ) = ∑ r, (χ r : ℚ) - 2 * (Fintype.card Basepoint - 1) := by
    linarith
  exact_mod_cast h'

/-- **The joined system has genus `g + b - 1`.** If the basepoints lie in distinct regions and the
regions of `H` assemble a closed surface of genus `g`, in the sense `∑ χ(R) - #(α ∩ β) = 2 - 2g`,
and `n = g + b - 1`, as for a balanced diagram with `b` basepoints, then the joined regions assemble
a closed surface of genus `n`. This is the normalization of a singly pointed diagram with `n` curves
of each kind, the hypothesis of `TauCeti.HeegaardRegionSystem.maslovIndex_one_eq_two`. -/
theorem sum_joinedEuler_sub_card_eq [Fintype Region] [Fintype Point]
    (hinj : Injective H.basepoint) {χ : Region → ℤ} {g : ℕ}
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (g : ℤ))
    (hn : n + 1 = g + Fintype.card Basepoint) :
    ∑ r, H.joinedEuler χ r - Fintype.card Point = 2 - 2 * (n : ℤ) := by
  rw [H.sum_joinedEuler hinj]
  have : (n : ℤ) + 1 = g + Fintype.card Basepoint := by exact_mod_cast hn
  linarith

end Euler

/-! ### The joined system -/

/-- **The singly pointed system of `Y_b`.** The regions of `H` containing basepoints are joined
into one region carrying a single basepoint, as by attaching tubes between them, and the curves
and intersection points are kept. For a balanced diagram of `Y` with `b` basepoints this is the
incidence data of a singly pointed diagram of `Y_b = Y # (S¹ × S²) # ⋯ # (S¹ × S²)`, with `b - 1`
copies of `S¹ × S²`.

This is an abbreviation for `TauCeti.HeegaardRegionSystem.mapRegion`, so the lemmas about
relabelled systems apply to it. -/
noncomputable abbrev joinBasepoints [Nonempty Basepoint] :
    HeegaardRegionSystem n Point H.JoinedRegion Unit :=
  H.mapRegion H.joinRegion_surjective fun _ => none

variable [Nonempty Basepoint]

/-- A domain of the joined system is periodic exactly when its pullback is a periodic domain of
`H`: avoiding the joined region means avoiding every basepoint. -/
theorem mem_periodicDomains_joinBasepoints_iff {P : H.JoinedRegion → ℤ} :
    P ∈ H.joinBasepoints.periodicDomains ↔ P ∘ H.joinRegion ∈ H.periodicDomains := by
  rw [mem_periodicDomains_mapRegion_iff, mem_periodicDomains_iff]
  simp

/-- A periodic domain of the joined system has multiplicity zero at the joined region. -/
theorem apply_none_eq_zero_of_mem_periodicDomains_joinBasepoints {P : H.JoinedRegion → ℤ}
    (hP : P ∈ H.joinBasepoints.periodicDomains) : P none = 0 :=
  (mem_periodicDomains_iff.1 hP).1 ()

/-- Every periodic domain of `H` is the pullback of a periodic domain of the joined system: it
avoids every basepoint, so it takes the single value `0` on the regions that are joined. -/
theorem exists_mem_periodicDomains_joinBasepoints_comp_eq {P : Region → ℤ}
    (hP : P ∈ H.periodicDomains) :
    ∃ P' ∈ H.joinBasepoints.periodicDomains, P' ∘ H.joinRegion = P := by
  obtain ⟨P', hP'⟩ := (H.exists_comp_joinRegion_eq_iff (D := P)).2 fun z z' => by
    rw [(mem_periodicDomains_iff.1 hP).1 z, (mem_periodicDomains_iff.1 hP).1 z']
  exact ⟨P', (H.mem_periodicDomains_joinBasepoints_iff).2 (hP' ▸ hP), hP'⟩

/-- The pullback of the periodic domains of the joined system along the relabelling. -/
private noncomputable def periodicDomainsComap :
    H.joinBasepoints.periodicDomains →+ H.periodicDomains where
  toFun P := ⟨P ∘ H.joinRegion, (H.mem_periodicDomains_joinBasepoints_iff).1 P.property⟩
  map_zero' := Subtype.ext (rfl)
  map_add' _ _ := Subtype.ext (rfl)

/-- **The periodic domains of the joined system** are those of `H`, by pulling back along the
relabelling `TauCeti.HeegaardRegionSystem.joinRegion`. -/
noncomputable def joinBasepointsPeriodicDomainsEquiv :
    H.joinBasepoints.periodicDomains ≃+ H.periodicDomains :=
  AddEquiv.ofBijective H.periodicDomainsComap
    ⟨fun P Q h => Subtype.ext <| H.joinRegion_surjective.injective_comp_right <|
        congrArg Subtype.val h,
      fun P => by
        obtain ⟨P', hP', hP'P⟩ := H.exists_mem_periodicDomains_joinBasepoints_comp_eq P.property
        exact ⟨⟨P', hP'⟩, Subtype.ext hP'P⟩⟩

/-- The periodic domain of `H` corresponding to a periodic domain of the joined system is its
pullback along the relabelling. -/
@[simp]
theorem coe_joinBasepointsPeriodicDomainsEquiv_apply (P : H.joinBasepoints.periodicDomains) :
    (H.joinBasepointsPeriodicDomainsEquiv P : Region → ℤ) =
      (P : H.JoinedRegion → ℤ) ∘ H.joinRegion :=
  (rfl)

/-- The joined system is weakly admissible exactly when `H` is: the pullback of a periodic domain
is nonnegative, or zero, exactly when the periodic domain is. -/
@[simp]
theorem weaklyAdmissible_joinBasepoints_iff :
    H.joinBasepoints.WeaklyAdmissible ↔ H.WeaklyAdmissible := by
  simp only [weaklyAdmissible_iff]
  refine ⟨fun h P hP hP0 => ?_, fun h P hP hP0 => ?_⟩
  · obtain ⟨P', hP', rfl⟩ := H.exists_mem_periodicDomains_joinBasepoints_comp_eq hP
    have := h P' hP' fun r' => by
      obtain ⟨r, rfl⟩ := H.joinRegion_surjective r'
      exact hP0 r
    simp [this]
  · have := h _ ((H.mem_periodicDomains_joinBasepoints_iff).1 hP) fun r => hP0 _
    exact H.joinRegion_surjective.injective_comp_right (by simpa using this)

/-- **Domains of the joined system.** When the basepoints lie in distinct components of `Σ - α`,
two generators are joined by a domain of the joined system exactly when they are joined by a
domain of `H`: adding multiples of the domains of the components of the basepoints gives a domain
with the same multiplicity at all the basepoints, which is a pullback. -/
theorem exists_isDomainBetween_joinBasepoints_iff [Finite Basepoint]
    (hz : ∀ z z', H.SameAlphaComponent (H.basepoint z) (H.basepoint z') → z = z')
    {x y : H.Generator} :
    (∃ D, H.joinBasepoints.IsDomainBetween x y D) ↔ ∃ D, H.IsDomainBetween x y D := by
  have := Fintype.ofFinite Basepoint
  refine ⟨fun ⟨D, hD⟩ => ⟨_, (isDomainBetween_mapRegion_iff _ _ _).1 hD⟩, fun ⟨D, hD⟩ => ?_⟩
  -- the combination of the component domains with the multiplicities of `D` at the basepoints
  set E := ∑ z, D (H.basepoint z) • H.alphaComponentDomain (H.basepoint z) with hE
  have hEz (z : Basepoint) : E (H.basepoint z) = D (H.basepoint z) :=
    H.sum_smul_alphaComponentDomain_basepoint_apply_basepoint (ι := id) hz D z
  have hEself : H.IsDomainBetween y y E := by
    refine (H.isDomainBetween_self_iff_sub_sum_smul_mem_periodicDomains hz).2 ?_
    simp only [hEz, ← hE, sub_self, zero_mem]
  obtain ⟨D', hD'⟩ := H.exists_comp_joinRegion_eq_iff (D := D + -E).2 fun z z' => by
    simp [hEz]
  exact ⟨D', (isDomainBetween_mapRegion_iff _ _ _).2 (hD' ▸ hD.add hEself.neg)⟩

/-! ### Maslov indices -/

section Maslov

variable [Fintype Region] [Fintype Point] [DecidableEq Region]

/-- **Maslov indices of domains avoiding the joined region.** For Euler characteristics `χ'` of
the joined regions that agree with `χ` on the regions containing no basepoint, a domain of the
joined system with multiplicity zero at the joined region has the Maslov index of its pullback.
The Euler characteristic of the joined region does not matter here. -/
theorem maslovIndex_joinBasepoints_of_apply_none_eq_zero {χ : Region → ℤ}
    {χ' : H.JoinedRegion → ℤ} (hχ' : ∀ s, χ' (some s) = χ s) (x y : H.Generator)
    {D : H.JoinedRegion → ℤ} (hD : D none = 0) :
    H.joinBasepoints.maslovIndex χ' x y D = H.maslovIndex χ x y (D ∘ H.joinRegion) := by
  rw [H.maslovIndex_mapRegion _ _ χ, H.sum_mul_sub_sum_mul_comp_joinRegion hχ', hD]
  simp

/-- **The Maslov index of a domain of the joined system.** When the basepoints lie in distinct
regions, for the joined Euler characteristics `TauCeti.HeegaardRegionSystem.joinedEuler`, a domain
`D` has Maslov index `μ(D ∘ joinRegion) - 2 (b - 1) n_z(D)`, where `n_z(D)` is its multiplicity at
the joined region: the point measures do not see the relabelling, and the Euler measures differ by
the `b - 1` tubes. -/
theorem maslovIndex_joinBasepoints [Fintype Basepoint] (hinj : Injective H.basepoint)
    (χ : Region → ℤ) (x y : H.Generator) (D : H.JoinedRegion → ℤ) :
    H.joinBasepoints.maslovIndex (H.joinedEuler χ) x y D =
      H.maslovIndex χ x y (D ∘ H.joinRegion) -
        2 * ((Fintype.card Basepoint : ℚ) - 1) * D none := by
  rw [H.maslovIndex_mapRegion _ _ χ,
    H.sum_mul_sub_sum_mul_comp_joinRegion (joinedEuler_some H χ), H.sum_joinRegion_eq_none hinj,
    joinedEuler_none]
  push_cast
  ring

/-- **The grading quantity of the joined system.** When the basepoints lie in distinct regions, for
the joined Euler characteristics, the quantity `μ(D) - 2 n_z(D)` of a domain `D` of the singly
pointed joined system is the quantity `μ - 2 ∑ᵢ n_{zᵢ}` of its pullback to the multipointed system,
which has multiplicity `n_z(D)` at each of the `b` basepoints. -/
theorem maslovIndex_joinBasepoints_sub_two_mul_sum [Fintype Basepoint]
    (hinj : Injective H.basepoint) (χ : Region → ℤ) (x y : H.Generator) (D : H.JoinedRegion → ℤ) :
    H.joinBasepoints.maslovIndex (H.joinedEuler χ) x y D -
        2 * ∑ z, (D (H.joinBasepoints.basepoint z) : ℚ) =
      H.maslovIndex χ x y (D ∘ H.joinRegion) -
        2 * ∑ z, ((D ∘ H.joinRegion) (H.basepoint z) : ℚ) := by
  rw [H.maslovIndex_joinBasepoints hinj]
  simp only [comp_apply, joinRegion_basepoint, Finset.sum_const, Finset.card_univ,
    Fintype.card_unit, one_smul, nsmul_eq_mul]
  ring

/-- **The periodic Maslov indices of the joined system** are those of `H`, for any Euler
characteristics of the joined regions agreeing with `χ` on the regions containing no basepoint:
periodic domains avoid the joined region. -/
theorem periodicMaslovIndices_joinBasepoints {χ : Region → ℤ} {χ' : H.JoinedRegion → ℤ}
    (hχ' : ∀ s, χ' (some s) = χ s) (x : H.Generator) :
    H.joinBasepoints.periodicMaslovIndices χ' x = H.periodicMaslovIndices χ x := by
  ext q
  simp only [mem_periodicMaslovIndices_iff]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨_, (H.mem_periodicDomains_joinBasepoints_iff).1 hP,
      (H.maslovIndex_joinBasepoints_of_apply_none_eq_zero hχ' x x
        (H.apply_none_eq_zero_of_mem_periodicDomains_joinBasepoints hP)).symm⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨P', hP', rfl⟩ := H.exists_mem_periodicDomains_joinBasepoints_comp_eq hP
    exact ⟨P', hP', H.maslovIndex_joinBasepoints_of_apply_none_eq_zero hχ' x x
      (H.apply_none_eq_zero_of_mem_periodicDomains_joinBasepoints hP')⟩

/-- **The relative grading of the joined system is normalized** when that of `H` is and the
basepoints lie in distinct regions: a domain `E` from a generator `x` to itself in the joined system
has `μ(E) - 2 n_z(E)` among its periodic Maslov indices at `x` as soon as every domain from a
generator to itself in `H` has `μ - 2 ∑ᵢ n_{zᵢ}` among the periodic Maslov indices of `H`. This is
the hypothesis `hself` of the relative grading lemmas of
`TauCeti.LowDimTopology.Heegaard.RelativeGrading`, for the joined system. -/
theorem maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_joinBasepoints [Fintype Basepoint]
    (hinj : Injective H.basepoint) {χ : Region → ℤ}
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x)
    (x : H.Generator) (E : H.JoinedRegion → ℤ) (hE : H.joinBasepoints.IsDomainBetween x x E) :
    H.joinBasepoints.maslovIndex (H.joinedEuler χ) x x E -
        2 * ∑ z, (E (H.joinBasepoints.basepoint z) : ℚ) ∈
      H.joinBasepoints.periodicMaslovIndices (H.joinedEuler χ) x := by
  rw [H.maslovIndex_joinBasepoints_sub_two_mul_sum hinj,
    H.periodicMaslovIndices_joinBasepoints (joinedEuler_some H χ)]
  exact hself x _ ((isDomainBetween_mapRegion_iff _ _ _).1 hE)

/-- The joined system is weakly admissible at a generator exactly when `H` is, for any Euler
characteristics of the joined regions agreeing with `χ` on the regions containing no basepoint. -/
theorem weaklyAdmissibleAt_joinBasepoints_iff {χ : Region → ℤ} {χ' : H.JoinedRegion → ℤ}
    (hχ' : ∀ s, χ' (some s) = χ s) (x : H.Generator) :
    H.joinBasepoints.WeaklyAdmissibleAt χ' x ↔ H.WeaklyAdmissibleAt χ x := by
  simp only [weaklyAdmissibleAt_def]
  refine ⟨fun h P hP hμ hP0 => ?_, fun h P hP hμ hP0 => ?_⟩
  · obtain ⟨P', hP', rfl⟩ := H.exists_mem_periodicDomains_joinBasepoints_comp_eq hP
    have h0 := H.apply_none_eq_zero_of_mem_periodicDomains_joinBasepoints hP'
    rw [← H.maslovIndex_joinBasepoints_of_apply_none_eq_zero hχ' x x h0] at hμ
    obtain ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩⟩ := h P' hP' hμ fun hP'0 => hP0 (by simp [hP'0])
    obtain ⟨s₁, rfl⟩ := H.joinRegion_surjective r₁
    obtain ⟨s₂, rfl⟩ := H.joinRegion_surjective r₂
    exact ⟨⟨s₁, h₁⟩, ⟨s₂, h₂⟩⟩
  · have hPH := (H.mem_periodicDomains_joinBasepoints_iff).1 hP
    rw [H.maslovIndex_joinBasepoints_of_apply_none_eq_zero hχ' x x
      (H.apply_none_eq_zero_of_mem_periodicDomains_joinBasepoints hP)] at hμ
    obtain ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩⟩ := h _ hPH hμ fun h0 =>
      hP0 (H.joinRegion_surjective.injective_comp_right (by simpa using h0))
    exact ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩

/-! ### The hat differential -/

/-- **The hat domains of the joined system** are the domains whose pullbacks are hat domains of
`H`, for any Euler characteristics of the joined regions agreeing with `χ` on the regions
containing no basepoint: a counted domain avoids the basepoints, hence the joined region. -/
theorem hatDomains_joinBasepoints {χ : Region → ℤ} {χ' : H.JoinedRegion → ℤ}
    (hχ' : ∀ s, χ' (some s) = χ s) (x y : H.Generator) :
    H.joinBasepoints.hatDomains χ' x y = (· ∘ H.joinRegion) ⁻¹' H.hatDomains χ x y := by
  ext D
  simp only [Set.mem_preimage, mem_hatDomains_iff, isDomainBetween_mapRegion_iff, comp_apply,
    joinRegion_basepoint, forall_const]
  refine and_congr_right fun _ => ⟨fun ⟨h0, hD, hμ⟩ => ⟨h0, fun r => hD _, ?_⟩,
    fun ⟨h0, hD, hμ⟩ => ⟨h0, fun r' => ?_, ?_⟩⟩
  · rwa [← H.maslovIndex_joinBasepoints_of_apply_none_eq_zero hχ' x y h0]
  · obtain ⟨r, rfl⟩ := H.joinRegion_surjective r'
    exact hD r
  · rwa [H.maslovIndex_joinBasepoints_of_apply_none_eq_zero hχ' x y h0]

/-- The hat coefficients of the joined system are those of `H`, for any Euler characteristics of
the joined regions agreeing with `χ` on the regions containing no basepoint. -/
theorem hatCoefficient_joinBasepoints {χ : Region → ℤ} {χ' : H.JoinedRegion → ℤ}
    (hχ' : ∀ s, χ' (some s) = χ s) (x y : H.Generator) :
    H.joinBasepoints.hatCoefficient χ' x y = H.hatCoefficient χ x y := by
  rw [hatCoefficient_def, hatCoefficient_def, H.hatDomains_joinBasepoints hχ',
    Set.ncard_preimage_of_injective_subset_range H.joinRegion_surjective.injective_comp_right]
  intro D hD
  exact H.exists_comp_joinRegion_eq_iff.2 fun z z' => by
    rw [(mem_hatDomains_iff.1 hD).2.1 z, (mem_hatDomains_iff.1 hD).2.1 z']

/-- **The hat differential of the joined system** is that of `H` on their common chain group, for
any Euler characteristics of the joined regions agreeing with `χ` on the regions containing no
basepoint, in particular for `TauCeti.HeegaardRegionSystem.joinedEuler`. -/
theorem hatDifferential_joinBasepoints {χ : Region → ℤ} {χ' : H.JoinedRegion → ℤ}
    (hχ' : ∀ s, χ' (some s) = χ s) :
    H.joinBasepoints.hatDifferential χ' = H.hatDifferential χ :=
  Finsupp.lhom_ext fun x a => Finsupp.ext fun y => by
    rw [hatDifferential_single_apply, hatDifferential_single_apply,
      H.hatCoefficient_joinBasepoints hχ']

/-! ### Relative gradings -/

/-- **The relative grading of the joined system.** Let the basepoints of `H` lie in distinct
components of `Σ - α` and let the relative grading of `H` be normalized (`hself`), as it is for a
balanced diagram whose components of `Σ - α` are spheres with holes by
`IsDomainBetween.maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices`. Then the relative
Maslov grading of the singly pointed joined system, for the joined Euler characteristics, is that
of `H` modulo the periodic Maslov indices, which are the same for both systems
(`TauCeti.HeegaardRegionSystem.periodicMaslovIndices_joinBasepoints`). -/
theorem coe_relativeGrading_joinBasepoints [Fintype Basepoint] {χ : Region → ℤ}
    (hz : ∀ z z', H.SameAlphaComponent (H.basepoint z) (H.basepoint z') → z = z')
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x)
    (x y : H.Generator) :
    (H.joinBasepoints.relativeGrading (H.joinedEuler χ) x y : ℚ ⧸ H.periodicMaslovIndices χ x) =
      H.relativeGrading χ x y := by
  have hinj : Injective H.basepoint := fun z z' h => hz z z' (h ▸ SameAlphaComponent.refl _)
  by_cases hxy : ∃ D, H.IsDomainBetween x y D
  · obtain ⟨D', hD'⟩ := (H.exists_isDomainBetween_joinBasepoints_iff hz).2 hxy
    have h := hD'.coe_relativeGrading_eq
      (H.maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_joinBasepoints hinj hself)
    rw [H.periodicMaslovIndices_joinBasepoints (joinedEuler_some H χ) x,
      H.maslovIndex_joinBasepoints_sub_two_mul_sum hinj] at h
    rw [h, ((isDomainBetween_mapRegion_iff _ _ _).1 hD').coe_relativeGrading_eq hself]
  · -- no domain joins `x` to `y` in either system, so both gradings are `0`
    have hxy' := mt (H.exists_isDomainBetween_joinBasepoints_iff hz (x := x) (y := y)).1 hxy
    rw [relativeGrading_of_forall_not_isDomainBetween (not_exists.1 hxy),
      relativeGrading_of_forall_not_isDomainBetween (not_exists.1 hxy')]

end Maslov

end HeegaardRegionSystem

end TauCeti
