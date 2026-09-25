/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ENat.LeastBound
public import TauCeti.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Cohomological dimension of a topological group

For a topological group `G`, a natural number `p` and `n : ℕ`, this file defines the two vanishing
predicates behind cohomological dimension, stated against Mathlib's continuous cohomology
`Hⁱ(G, M) = continuousCohomology i (ofDiscreteModule ℤ G M)` of discrete `G`-modules `M` with a
continuous action:

* `CohomologicalDimensionLE p G n`: `Hⁱ(G, M) = 0` for every `i > n` and every `p`-primary
  torsion `M`;
* `StrictCohomologicalDimensionLE p G n`: the `p`-primary component of `Hⁱ(G, M)` vanishes for
  every `i > n` and **every** `M`.

The two differ in both places at once: the ordinary predicate restricts the coefficients and asks
the whole group to vanish, the strict one allows all coefficients and asks only the `p`-primary
part to vanish. The `p`-cohomological dimension `cd_p G = cohomologicalDimensionAt p G` and the
strict one `scd_p G = strictCohomologicalDimensionAt p G` are the least `n` in `ℕ∞` satisfying
them (`⊤` when none does), and the cohomological dimension `cd G = cohomologicalDimension G` is
the supremum of `cd_p G` over the primes `p`.

The first comparison between them is `cd_p G ≤ scd_p G` for compact `G` (NSW (3.3.3)). It rests
on `isPPrimaryTorsion_continuousCohomology`: over a compact group, the continuous cohomology of a
discrete `p`-primary torsion representation is `p`-primary torsion in every degree. A continuous
cochain out of a compact group into a discrete module has finite image, so a single power of `p`
kills it; that bound propagates through the iterated function spaces of the homogeneous cochain
complex, and hence to its homology.

The definitions do not use that `p` is prime; they are meant for prime `p`, where `p`-primary is
the intended notion.

## Main definitions

* `TauCeti.CohomologicalDimensionLE`, `TauCeti.StrictCohomologicalDimensionLE`: the vanishing
  predicates.
* `TauCeti.cohomologicalDimensionAt`, `TauCeti.strictCohomologicalDimensionAt`,
  `TauCeti.cohomologicalDimension`: the invariants `cd_p`, `scd_p` and `cd`, valued in `ℕ∞`.

## Main results

* `TauCeti.isPPrimaryTorsion_continuousCohomology`: continuous cohomology of a discrete
  `p`-primary torsion representation of a compact group is `p`-primary torsion.
* `TauCeti.cohomologicalDimensionAt_le_iff`, `TauCeti.strictCohomologicalDimensionAt_le_iff`,
  `TauCeti.cohomologicalDimension_le_iff`: each invariant is at most `n` exactly when the
  corresponding predicate holds at `n`.
* `TauCeti.cohomologicalDimensionAt_le_strictCohomologicalDimensionAt`: `cd_p G ≤ scd_p G` for
  compact `G`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III §3,
  (3.3.1) and (3.3.3).
* J.-P. Serre, *Galois Cohomology*, Ch. I §3.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable {p : ℕ}

/-! ### Torsion of continuous cochains and of continuous cohomology -/

section Torsion

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] (X : TopRep k G) [DiscreteTopology X.V]

/-- Every term of the coinduced resolution of a discrete `p`-primary torsion representation of a
compact group is `p`-primary torsion. -/
theorem isPPrimaryTorsion_resolutionX (h : IsPPrimaryTorsion p X.V) :
    ∀ n : ℕ, IsPPrimaryTorsion p (TopRep.resolutionX X n).V
  | 0 => h
  -- the successor term is `TopRep.coind₁`, whose underlying module is `C(G, -)` by definition
  | n + 1 => (isPPrimaryTorsion_resolutionX h n).continuousMap G

/-- Every term of the homogeneous cochain complex of a discrete `p`-primary torsion
representation of a compact group is `p`-primary torsion. -/
theorem isPPrimaryTorsion_homogeneousCochains (h : IsPPrimaryTorsion p X.V) (n : ℕ) :
    IsPPrimaryTorsion p ((TopRep.homogeneousCochains X).X n) :=
  -- degree `n` of the complex is the invariants of the shifted resolution, an additive subgroup
  (isPPrimaryTorsion_resolutionX X h (n + 1)).of_injective
    (TopRep.resolutionX X (n + 1)).ρ.invariants.subtype Subtype.val_injective

/-- **The continuous cohomology of a discrete `p`-primary torsion representation of a compact
group is `p`-primary torsion**, in every degree. -/
theorem isPPrimaryTorsion_continuousCohomology (h : IsPPrimaryTorsion p X.V) (n : ℕ) :
    IsPPrimaryTorsion p (continuousCohomology n X) := by
  set S := (TopRep.homogeneousCochains X).sc n
  have hker : IsPPrimaryTorsion p (TopModuleCat.ker S.g) :=
    (isPPrimaryTorsion_homogeneousCochains X h n).of_injective (TopModuleCat.kerι S.g).hom
      Subtype.val_injective
  have hcycles : IsPPrimaryTorsion p S.cycles :=
    hker.of_surjective (S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)).hom.hom
      (S.isoCyclesOfIsLimit _).toContinuousLinearEquiv.surjective
  exact hcycles.of_surjective S.homologyπ.hom S.homologyπ_surjective

end Torsion

/-! ### The vanishing predicates and the invariants -/

section CohomologicalDimension

variable (p) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `CohomologicalDimensionLE p G n` says that `Hⁱ(G, M)` vanishes for every `i > n` and every
discrete `p`-primary torsion `G`-module `M` with a continuous action. -/
def CohomologicalDimensionLE (n : ℕ) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M →
    ∀ i : ℕ, n < i → Subsingleton (continuousCohomology i (ofDiscreteModule ℤ G M))

/-- `StrictCohomologicalDimensionLE p G n` says that the `p`-primary component of `Hⁱ(G, M)`
vanishes for every `i > n` and every discrete `G`-module `M` with a continuous action. -/
def StrictCohomologicalDimensionLE (n : ℕ) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M], ∀ i : ℕ, n < i →
    AddCommGroup.primaryComponent (continuousCohomology i (ofDiscreteModule ℤ G M)) p = ⊥

/-- The `p`-cohomological dimension of `G`, written `cd_p G`: the least `n` with
`CohomologicalDimensionLE p G n`, and `⊤` when there is none. -/
noncomputable def cohomologicalDimensionAt : ℕ∞ :=
  leastENatBound (CohomologicalDimensionLE p G)

/-- The strict `p`-cohomological dimension of `G`, written `scd_p G`: the least `n` with
`StrictCohomologicalDimensionLE p G n`, and `⊤` when there is none. -/
noncomputable def strictCohomologicalDimensionAt : ℕ∞ :=
  leastENatBound (StrictCohomologicalDimensionLE p G)

/-- The cohomological dimension of `G`, written `cd G`: the supremum over the primes `q` of the
`q`-cohomological dimension `cohomologicalDimensionAt q G`. -/
noncomputable def cohomologicalDimension : ℕ∞ :=
  ⨆ q : Nat.Primes, cohomologicalDimensionAt q G

variable {p G}

/-- Unfolding `CohomologicalDimensionLE`. -/
theorem cohomologicalDimensionLE_iff {n : ℕ} :
    CohomologicalDimensionLE p G n ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M →
        ∀ i : ℕ, n < i → Subsingleton (continuousCohomology i (ofDiscreteModule ℤ G M)) :=
  Iff.rfl

/-- Unfolding `StrictCohomologicalDimensionLE`. -/
theorem strictCohomologicalDimensionLE_iff {n : ℕ} :
    StrictCohomologicalDimensionLE p G n ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M], ∀ i : ℕ, n < i →
        AddCommGroup.primaryComponent (continuousCohomology i (ofDiscreteModule ℤ G M)) p = ⊥ :=
  Iff.rfl

/-- The ordinary vanishing predicate is upward closed in `n`. -/
theorem CohomologicalDimensionLE.mono {m n : ℕ} (h : CohomologicalDimensionLE p G m)
    (hmn : m ≤ n) : CohomologicalDimensionLE p G n :=
  fun M _ _ _ _ _ hM i hi ↦ h M hM i (hmn.trans_lt hi)

/-- The strict vanishing predicate is upward closed in `n`. -/
theorem StrictCohomologicalDimensionLE.mono {m n : ℕ} (h : StrictCohomologicalDimensionLE p G m)
    (hmn : m ≤ n) : StrictCohomologicalDimensionLE p G n :=
  fun M _ _ _ _ _ i hi ↦ h M i (hmn.trans_lt hi)

variable (p G)

/-- `cohomologicalDimensionAt p G ≤ n` exactly when `Hⁱ(G, M)` vanishes above `n` for every
discrete `p`-primary torsion `M`. -/
@[simp] theorem cohomologicalDimensionAt_le_iff (n : ℕ) :
    cohomologicalDimensionAt p G ≤ n ↔ CohomologicalDimensionLE p G n :=
  leastENatBound_le_iff (fun _ _ hmn h ↦ h.mono hmn) n

/-- `strictCohomologicalDimensionAt p G ≤ n` exactly when the `p`-primary component of
`Hⁱ(G, M)` vanishes above `n` for every discrete `M`. -/
@[simp] theorem strictCohomologicalDimensionAt_le_iff (n : ℕ) :
    strictCohomologicalDimensionAt p G ≤ n ↔ StrictCohomologicalDimensionLE p G n :=
  leastENatBound_le_iff (fun _ _ hmn h ↦ h.mono hmn) n

/-- The `p`-cohomological dimension is infinite exactly when the ordinary vanishing predicate
holds at no `n`. -/
@[simp] theorem cohomologicalDimensionAt_eq_top_iff :
    cohomologicalDimensionAt p G = ⊤ ↔ ∀ n : ℕ, ¬CohomologicalDimensionLE p G n :=
  leastENatBound_eq_top_iff

/-- The strict `p`-cohomological dimension is infinite exactly when the strict vanishing
predicate holds at no `n`. -/
@[simp] theorem strictCohomologicalDimensionAt_eq_top_iff :
    strictCohomologicalDimensionAt p G = ⊤ ↔ ∀ n : ℕ, ¬StrictCohomologicalDimensionLE p G n :=
  leastENatBound_eq_top_iff

/-- `cohomologicalDimension G ≤ n` exactly when `CohomologicalDimensionLE q G n` holds for every
prime `q`. -/
@[simp] theorem cohomologicalDimension_le_iff (n : ℕ) :
    cohomologicalDimension G ≤ n ↔ ∀ q : ℕ, q.Prime → CohomologicalDimensionLE q G n := by
  simp only [cohomologicalDimension, iSup_le_iff, cohomologicalDimensionAt_le_iff, Nat.Primes,
    Subtype.forall]

/-- The cohomological dimension is the supremum of the `q`-cohomological dimensions over the
primes `q`. -/
theorem cohomologicalDimension_eq_iSup :
    cohomologicalDimension G = ⨆ q : Nat.Primes, cohomologicalDimensionAt q G :=
  (rfl)

/-- The `p`-cohomological dimension is at most the cohomological dimension, for prime `p`. -/
theorem cohomologicalDimensionAt_le_cohomologicalDimension (hp : p.Prime) :
    cohomologicalDimensionAt p G ≤ cohomologicalDimension G :=
  le_iSup (fun q : Nat.Primes ↦ cohomologicalDimensionAt q G) ⟨p, hp⟩

/-- Over a compact group, the strict vanishing predicate implies the ordinary one at the same
`n`: for `p`-primary torsion coefficients the cohomology is itself `p`-primary torsion, so the
vanishing of its `p`-primary component is the vanishing of the whole group. -/
theorem StrictCohomologicalDimensionLE.cohomologicalDimensionLE [CompactSpace G] {n : ℕ}
    (h : StrictCohomologicalDimensionLE p G n) : CohomologicalDimensionLE p G n := by
  intro M _ _ _ _ _ hM i hi
  have hH := isPPrimaryTorsion_continuousCohomology (ofDiscreteModule ℤ G M) hM i
  exact subsingleton_of_forall_eq 0 fun x ↦ AddSubgroup.mem_bot.1 (h M i hi ▸ hH.mem x)

/-- **`cd_p ≤ scd_p`** (NSW (3.3.3)): over a compact group, the `p`-cohomological dimension is
at most the strict `p`-cohomological dimension. -/
theorem cohomologicalDimensionAt_le_strictCohomologicalDimensionAt [CompactSpace G] :
    cohomologicalDimensionAt p G ≤ strictCohomologicalDimensionAt p G :=
  leastENatBound_antitone fun _ h ↦ h.cohomologicalDimensionLE

end CohomologicalDimension

end TauCeti
