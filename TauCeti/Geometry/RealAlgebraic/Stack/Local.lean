/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation

/-!
# Gluing local delineations

Local delineations of a real polynomial family glue over a preconnected base.
The ordered real roots have no permutation ambiguity on overlaps, so their number,
multiplicities, and the degrees and nullification status of the family members are constant.
The resulting continuous root functions form one global delineation. No finiteness assumption
on the family or continuity assumption on its coefficients is needed: local delineations
already provide finite root lists and local sign-invariance.

The gluing of the ordered root lists, `TauCeti.exists_roots_of_locally`, uses only local
continuous increasing enumerations of an intrinsic root set, so it also glues the root
functions of local Lazard delineations.

This gives the passage from local analytic root constructions to a global stack. Analyticity
of its root functions can then be obtained from the analytic root-section API.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), 242–268 (globalization of local delineability).
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

variable {X ι : Type*} [TopologicalSpace X] {P : ι → X → ℝ[X]}

private theorem invariants_of_local_delineations [PreconnectedSpace X] [Nonempty X]
    {U : X → Set X} (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (D : ∀ x, Delineation fun k (y : U x) ↦ P k y) :
    (∀ k x y, (P k x).natDegree = (P k y).natDegree) ∧
      ∀ k, (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0 := by
  let a₀ : X := Classical.arbitrary X
  have hdeg (k : ι) (x y : X) : (P k x).natDegree = (P k y).natDegree := by
    have hd : IsLocallyConstant fun z ↦ (P k z).natDegree := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
      filter_upwards [(hU a).mem_nhds (hxU a)] with z hz
      exact (D a).natDegree_eq k ⟨z, hz⟩ ⟨a, hxU a⟩
    exact hd.apply_eq_of_preconnectedSpace x y
  have hnull (k : ι) : (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0 := by
    have hz : IsLocallyConstant fun z ↦ P k z = 0 := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
      filter_upwards [(hU a).mem_nhds (hxU a)] with z hza
      apply propext
      rcases (D a).eq_zero_or_ne_zero k with h | h <;>
        simp [h ⟨z, hza⟩, h ⟨a, hxU a⟩]
    by_cases h : P k a₀ = 0
    · exact .inl fun x ↦ (hz.apply_eq_of_preconnectedSpace x a₀).mpr h
    · exact .inr fun x hx ↦ h ((hz.apply_eq_of_preconnectedSpace x a₀).mp hx)
  exact ⟨hdeg, hnull⟩

/-- Local continuous strictly increasing enumerations `θ a` of an intrinsic set `Z y ⊆ ℝ` on
open neighborhoods `U a` glue over a nonempty preconnected base. The local counts are globally
constant, the glued root functions are continuous, strictly increasing and enumerate `Z`, and
they agree with every local enumeration. If every local enumeration has constant root
multiplicities in a family `P`, so do the glued roots. -/
theorem exists_roots_of_locally [PreconnectedSpace X] [Nonempty X] {Z : X → Set ℝ}
    {U : X → Set X} (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x) {c : X → ℕ}
    {θ : ∀ a, Fin (c a) → U a → ℝ} {μ : ∀ a, ι → Fin (c a) → ℕ}
    (hθc : ∀ a i, Continuous (θ a i)) (hθmono : ∀ a (y : U a), StrictMono fun i ↦ θ a i y)
    (hθrange : ∀ a (y : U a), range (fun i ↦ θ a i y) = Z y)
    (hθmult : ∀ a k i (y : U a), (P k y).rootMultiplicity (θ a i y) = μ a k i) :
    ∃ (n : ℕ) (hc : ∀ x, c x = n) (r : Fin n → X → ℝ) (m : ι → Fin n → ℕ),
      (∀ i, Continuous (r i)) ∧ (∀ x, StrictMono fun i ↦ r i x) ∧
      (∀ x, range (fun i ↦ r i x) = Z x) ∧
      (∀ k i x, (P k x).rootMultiplicity (r i x) = m k i) ∧
      ∀ a (y : U a) i, r i y = θ a (Fin.cast (hc a).symm i) y := by
  classical
  let a₀ : X := Classical.arbitrary X
  have hcard (a : X) (y : U a) : Nat.card (Z y) = c a := by
    rw [← hθrange a y, Nat.card_range_of_injective (hθmono a y).injective]
    simp
  -- The number of roots is locally constant, hence globally constant.
  have hclocal : IsLocallyConstant fun x ↦ Nat.card (Z x) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
    filter_upwards [(hU a).mem_nhds (hxU a)] with y hy
    exact (hcard a ⟨y, hy⟩).trans (hcard a ⟨a, hxU a⟩).symm
  let n := Nat.card (Z a₀)
  have hc (a : X) : c a = n :=
    (hcard a ⟨a, hxU a⟩).symm.trans (hclocal.apply_eq_of_preconnectedSpace a a₀)
  let r (i : Fin n) (x : X) := θ x (Fin.cast (hc x).symm i) ⟨x, hxU x⟩
  have hrmono (x : X) : StrictMono fun i ↦ r i x :=
    (hθmono x ⟨x, hxU x⟩).comp (Fin.cast_strictMono (hc x).symm)
  have hrrange (x : X) : range (fun i ↦ r i x) = Z x := by
    exact ((Fin.castOrderIso (hc x).symm).surjective.range_comp _).trans
      (hθrange x ⟨x, hxU x⟩)
  -- Increasing complete lists agree on overlaps. This identifies the pointwise
  -- choice with each local continuous root function, including its multiplicity.
  have hrU (a : X) (y : U a) (i : Fin n) : r i y = θ a (Fin.cast (hc a).symm i) y := by
    have hmono := (hθmono a y).comp (Fin.cast_strictMono (hc a).symm)
    apply congrFun (((hrmono y).range_inj_of_wellFoundedLT hmono).1 ?_) i
    exact (hrrange y).trans (((Fin.castOrderIso (hc a).symm).surjective.range_comp _).trans
      (hθrange a y)).symm
  have hrc (i : Fin n) : Continuous (r i) := by
    refine continuous_iff_continuousAt.2 fun a ↦ ?_
    have hcont : ContinuousOn (r i) (U a) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (hθc a _).congr fun y ↦ (hrU a y i).symm
    exact (hU a).continuousOn_iff.mp hcont (hxU a)
  let m (k : ι) (i : Fin n) := (P k a₀).rootMultiplicity (r i a₀)
  have hm (k : ι) (i : Fin n) (x : X) : (P k x).rootMultiplicity (r i x) = m k i := by
    have hmult : IsLocallyConstant fun y ↦ (P k y).rootMultiplicity (r i y) := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
      filter_upwards [(hU a).mem_nhds (hxU a)] with y hy
      rw [hrU a ⟨y, hy⟩ i, hrU a ⟨a, hxU a⟩ i, hθmult, hθmult]
    exact hmult.apply_eq_of_preconnectedSpace x a₀
  exact ⟨n, hc, r, m, hrc, hrmono, hrrange, hm, hrU⟩

private theorem signs_of_local_delineations [PreconnectedSpace X]
    {U : X → Set X} (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (D : ∀ x, Delineation fun k (y : U x) ↦ P k y)
    {n : ℕ} (hc : ∀ x, (D x).count = n) {r : Fin n → X → ℝ}
    (hrc : ∀ i, Continuous (r i)) (hrmono : ∀ x, StrictMono fun i ↦ r i x)
    (hrU : ∀ a (y : U a) i, r i y = (D a).root (Fin.cast (hc a).symm i) y) :
    (∀ k i, SignInvariant (fun z : X × ℝ ↦ (P k z.1).eval z.2) (sectionSet r i)) ∧
      ∀ k j, SignInvariant (fun z : X × ℝ ↦ (P k z.1).eval z.2) (sectorSet r j) := by
  constructor
  · intro k i
    apply (isPreconnected_sectionSet (hrc i)).signInvariant_of_locally
    intro z _
    let a := z.1
    refine ⟨Prod.fst ⁻¹' U a, (hU a).preimage continuous_fst, hxU a, ?_⟩
    rw [signInvariant_def]
    intro v hv w hw
    apply signInvariant_def.mp ((D a).signInvariant_sectionSet k (Fin.cast (hc a).symm i))
      (⟨v.1, hv.2⟩, v.2) ?_ (⟨w.1, hw.2⟩, w.2) ?_
    · exact mem_sectionSet.mpr ((hrU a ⟨v.1, hv.2⟩ i).symm.trans (mem_sectionSet.mp hv.1))
    · exact mem_sectionSet.mpr ((hrU a ⟨w.1, hw.2⟩ i).symm.trans (mem_sectionSet.mp hw.1))
  · intro k j
    apply (isPreconnected_sectorSet hrc hrmono j).signInvariant_of_locally
    intro z _
    let a := z.1
    refine ⟨Prod.fst ⁻¹' U a, (hU a).preimage continuous_fst, hxU a, ?_⟩
    have hmem {v : X × ℝ} (hv : v ∈ sectorSet r j ∩ (Prod.fst ⁻¹' U a)) :
        (⟨v.1, hv.2⟩, v.2) ∈ sectorSet (D a).root (Fin.cast (congrArg (· + 1) (hc a).symm) j) := by
      rw [mem_sectorSet]
      constructor
      · intro i hi
        have hi' : (Fin.cast (hc a) i).castSucc < j := by
          simpa only [Fin.lt_def, Fin.val_cast, Fin.val_castSucc] using hi
        simpa only [hrU a ⟨v.1, hv.2⟩, Fin.cast_cast, Fin.cast_refl, id_eq] using
          (mem_sectorSet.mp hv.1).1 (Fin.cast (hc a) i) hi'
      · intro i hi
        have hi' : j ≤ (Fin.cast (hc a) i).castSucc := by
          simpa only [Fin.le_def, Fin.val_cast, Fin.val_castSucc] using hi
        simpa only [hrU a ⟨v.1, hv.2⟩, Fin.cast_cast, Fin.cast_refl, id_eq] using
          (mem_sectorSet.mp hv.1).2 (Fin.cast (hc a) i) hi'
    rw [signInvariant_def]
    exact fun v hv w hw ↦ signInvariant_def.mp ((D a).signInvariant_sectorSet k _)
      _ (hmem hv) _ (hmem hw)

/-- A family with a delineation on a neighborhood of every point has a global delineation on
any preconnected base. Local root counts, multiplicities, degrees, nullification and
signs are allowed to depend on the neighborhood; their global constancy is a conclusion. -/
theorem nonempty_delineation_of_locally [PreconnectedSpace X]
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      Nonempty (Delineation fun k (y : U) ↦ P k y)) :
    Nonempty (Delineation P) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · exact Delineation.nonempty_of_isEmpty P
  choose U hU hxU hD using hlocal
  let D (x : X) := (hD x).some
  obtain ⟨hdeg, hnull⟩ := invariants_of_local_delineations hU hxU D
  obtain ⟨n, hc, r, m, hrc, hrmono, hrrange, hm, hrU⟩ :=
    exists_roots_of_locally (Z := fun x ↦ {t | ∃ k, P k x ≠ 0 ∧ (P k x).IsRoot t}) hU hxU
      (fun a ↦ (D a).continuous_root)
      (fun a ↦ (D a).strictMono_root) (fun a ↦ (D a).range_root)
      (fun a ↦ (D a).rootMultiplicity_root)
  obtain ⟨hsection, hsector⟩ := signs_of_local_delineations hU hxU D hc hrc hrmono hrU
  refine ⟨{
    count := n
    root := r
    continuous_root := hrc
    strictMono_root := hrmono
    multiplicity := m
    rootMultiplicity_root := hm
    exists_root_eq := fun k x hk t ht ↦ Set.mem_range.mp ((hrrange x).symm.le ⟨k, hk, ht⟩)
    exists_multiplicity_pos := fun i ↦ ?_
    eq_zero_or_ne_zero := hnull
    natDegree_eq := hdeg
    signInvariant_sectionSet := hsection
    signInvariant_sectorSet := hsector }⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨k, hk, ht⟩ := (hrrange x).le (mem_range_self i)
  exact ⟨k, (hm k i x) ▸ (rootMultiplicity_pos hk).2 ht⟩

end TauCeti
