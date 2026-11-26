/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Invariant.Profinite
public import TauCeti.Topology.Algebra.GroupAction.Inertia

/-!
# Decomposition groups and residue extensions for profinite actions

Let a compact totally disconnected group `G` act continuously on a commutative ring `S` with the
discrete topology, with invariant ring `R` (`Algebra.IsInvariant R S G`), and let `Q` be a prime
of `S` over `P = Q ∩ R`. This is the setting of Mathlib's
`Mathlib/RingTheory/Invariant/Profinite.lean`, which covers infinite Galois extensions such as
the action of an absolute Galois group on the integral closure of a Dedekind domain. That file
proves that the decomposition group `D_Q = MulAction.stabilizer G Q` surjects onto the
automorphisms of the residue extension (`Ideal.Quotient.stabilizerHom_surjective_of_profinite`),
and Mathlib's `Ideal.Quotient.ker_stabilizerHom` identifies the kernel with the inertia group
`I_Q`. This file adds the profinite forms of the remaining finite-group statements of
`Mathlib/RingTheory/Invariant/Basic.lean` and `Mathlib/RingTheory/Invariant/Galois.lean` about
the residue extension, and the topological facts that let the surjectivity theorem be applied to
`D_Q` and its closed subgroups.

The residue extension is in general infinite (for the integral closure of `ℤ` in an algebraic
closure of `ℚ` it is an algebraic closure of `𝔽_p` over `𝔽_p`), so Mathlib's finite-group proofs,
which bound degrees by `#G`, do not apply.
Normality is proved by reduction to the finite quotients of `G` by open normal subgroups: the
residue class of `b ∈ S` already comes from the residue extension of the invariants of an open
normal subgroup fixing `b`, which is normal by Mathlib's `Ideal.Quotient.normal`.

The closedness statements need no compactness: for a continuous action on a discrete ring, each
condition `g • x ∈ Q` or `g • x - x ∈ Q` cuts out a clopen subset of `G`. For inertia only
closedness of the subgroup matters, and Tau Ceti's `AddSubgroup.isClosed_inertia`
(`TauCeti/Topology/Algebra/GroupAction/Inertia.lean`) covers a closed additive subgroup of any
topological additive group.

## Main results

* `Ideal.isClosed_stabilizer`: the decomposition group of an ideal is closed, and hence compact
  when `G` is (an instance).
* `Ideal.isClosed_inertia`: the inertia group of an ideal is closed, and hence compact when `G` is
  (an instance).
* `Ideal.Quotient.stabilizerQuotientInertiaEquivOfProfinite`: `D_Q / I_Q ≃* Aut((S ⧸ Q)/(R ⧸ P))`.
* `Ideal.Quotient.normal_of_profinite`: for `Q` maximal, `S ⧸ Q` is a normal extension of `R ⧸ P`.
* `Ideal.Quotient.isGalois_of_profinite`: if moreover `R ⧸ P` is perfect, it is Galois, so that
  `D_Q / I_Q` is its Galois group.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9 (decomposition and inertia
  groups and the residue extension for finite Galois extensions) and Chapter II, §9 (their
  analogues for infinite Galois extensions of valued fields).
-/

public section

open MulAction Pointwise

/-! ### Closedness of decomposition and inertia groups -/

section Closed

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {S : Type*} [TopologicalSpace S] [DiscreteTopology S]

/-- **Decomposition groups are closed.** If `G` acts continuously on a semiring `S` with the
discrete topology, then the stabilizer of any ideal `Q` of `S` is closed in `G`. -/
theorem Ideal.isClosed_stabilizer [Semiring S] [MulSemiringAction G S] [ContinuousSMul G S]
    (Q : Ideal S) : IsClosed (stabilizer G Q : Set G) := by
  have : (stabilizer G Q : Set G) = ⋂ x : S, (· • x) ⁻¹' {y | y ∈ Q ↔ x ∈ Q} := by
    ext g
    simp only [SetLike.mem_coe, mem_stabilizer_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_ofPred_eq]
    refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
    · nth_rewrite 1 [← h]
      exact Ideal.smul_mem_pointwise_smul_iff
    · ext y
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h, smul_inv_smul]
  rw [this]
  exact isClosed_iInter fun _ ↦ (isClosed_discrete _).preimage (continuous_id.smul continuous_const)

instance Ideal.compactSpace_stabilizer [CompactSpace G] [Semiring S] [MulSemiringAction G S]
    [ContinuousSMul G S] (Q : Ideal S) : CompactSpace (stabilizer G Q) :=
  isCompact_iff_compactSpace.mp Q.isClosed_stabilizer.isCompact

/-- **Inertia groups of ideals are closed.** If `G` acts continuously on a ring `S` with the
discrete topology, then the inertia group of any ideal `Q` of `S` is closed in `G`. -/
theorem Ideal.isClosed_inertia [Ring S] [MulAction G S] [ContinuousSMul G S]
    (Q : Ideal S) : IsClosed (Q.inertia G : Set G) :=
  AddSubgroup.isClosed_inertia (isClosed_discrete _)

instance Ideal.compactSpace_inertia [CompactSpace G] [Ring S] [MulAction G S]
    [ContinuousSMul G S] (Q : Ideal S) : CompactSpace (Q.inertia G) :=
  isCompact_iff_compactSpace.mp Q.isClosed_inertia.isCompact

end Closed

/-! ### The residue extension -/

section Residue

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
  [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul G S] [Algebra.IsInvariant R S G]
  (P : Ideal R) (Q : Ideal S) [Q.LiesOver P]

/-- **The decomposition group modulo inertia is the residue automorphism group**, for a profinite
group: `D_Q / I_Q ≃* Aut((S ⧸ Q)/(R ⧸ P))`. This is the profinite form of Mathlib's
`Ideal.Quotient.stabilizerQuotientInertiaEquiv`; no finiteness of the residue extension is
assumed. -/
noncomputable def Ideal.Quotient.stabilizerQuotientInertiaEquivOfProfinite [Q.IsPrime] :
    stabilizer G Q ⧸ Q.inertia (stabilizer G Q) ≃* ((S ⧸ Q) ≃ₐ[R ⧸ P] (S ⧸ Q)) :=
  QuotientGroup.liftEquiv (N := Q.inertia (stabilizer G Q))
    (stabilizerHom_surjective_of_profinite P Q) (ker_stabilizerHom Q P G).symm

@[simp]
theorem Ideal.Quotient.stabilizerQuotientInertiaEquivOfProfinite_mk [Q.IsPrime]
    (g : stabilizer G Q) :
    stabilizerQuotientInertiaEquivOfProfinite G P Q g = stabilizerHom Q P G g := by
  rw [stabilizerQuotientInertiaEquivOfProfinite, QuotientGroup.liftEquiv_coe]

include G in
attribute [local instance] Ideal.Quotient.field Subgroup.finiteIndex_of_finite_quotient in
/-- **The residue extension of a profinite action is normal.** For `Q` maximal over `P` (which is
then maximal as well), `S ⧸ Q` is a normal extension of `R ⧸ P`. This is the profinite form of
Mathlib's `Ideal.Quotient.normal`; the extension need not be finite. -/
theorem Ideal.Quotient.normal_of_profinite [P.IsMaximal] [Q.IsMaximal] :
    Normal (R ⧸ P) (S ⧸ Q) := by
  have := Algebra.IsInvariant.isIntegral_of_profinite (A := R) (B := S) (G := G)
  have : Algebra.IsAlgebraic (R ⧸ P) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  refine { this with splits' := fun x ↦ ?_ }
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G b) (one_mem _)
  let S' := FixedPoints.subalgebra R S N.toOpenSubgroup.toSubgroup
  let Q' : Ideal S' := Q.under S'
  have : Q'.LiesOver P := ⟨by rw [Ideal.under_under, ← Ideal.LiesOver.over (P := Q) (p := P)]⟩
  have : Q'.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) Q'
    (by rw [← Ideal.LiesOver.over (P := Q') (p := P)]; infer_instance)
  have hn : Normal (R ⧸ P) (S' ⧸ Q') := normal (G ⧸ N.toOpenSubgroup.toSubgroup) P Q'
  let f : (S' ⧸ Q') →ₐ[R ⧸ P] S ⧸ Q :=
    { toRingHom := Ideal.quotientMap _ (algebraMap S' S) le_rfl
      commutes' r := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.algebraMap_mk_of_liesOver]
        exact Ideal.quotientMap_mk }
  have hx : Ideal.Quotient.mk Q b = f (Ideal.Quotient.mk Q' ⟨b, fun g ↦ hN g.property⟩) := by
    simp [f]
  rw [hx, minpoly.algHom_eq f f.injective]
  simpa [Polynomial.map_map] using (hn.splits _).map f.toRingHom

include G in
attribute [local instance] Ideal.Quotient.field in
/-- **The residue extension of a profinite action over a perfect residue field is Galois.** For
`Q` maximal over `P` with `R ⧸ P` perfect (for instance finite), `S ⧸ Q` is a Galois extension of
`R ⧸ P`, so `Ideal.Quotient.stabilizerQuotientInertiaEquivOfProfinite` identifies `D_Q / I_Q` with
its Galois group. -/
theorem Ideal.Quotient.isGalois_of_profinite [P.IsMaximal] [Q.IsMaximal] [PerfectField (R ⧸ P)] :
    IsGalois (R ⧸ P) (S ⧸ Q) :=
  have := normal_of_profinite G P Q
  have : Algebra.IsAlgebraic (R ⧸ P) (S ⧸ Q) := Normal.toIsAlgebraic
  IsGalois.mk

end Residue
