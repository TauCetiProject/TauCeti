/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Eigenspace
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Finite
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Hom
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints

/-!
# Openness of the grade-two centralizer orbit and conjugacy of `sl₂` triples sharing `h`

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero, with Lie algebra `𝔤`, and let `(h, e, f)` be an `sl₂` triple in `𝔤`. Consider
any closed subgroup `K ⊆ C_G(h)` whose Lie algebra contains `𝔤(0) = ker (ad h)`, such as the full
centralizer `C_G(h)` or its identity component `C_G(h)°`.

By `IsSl2Triple.range_differential_flip_eigenspace_two_eq_top_of_lieSubalgebra_le`, the
differentiated action of `Lie(K)` at `e` sweeps out the entire grade-two eigenspace
`𝔤(2) = ker (ad h - 2)`. Applying the characteristic-zero vector-orbit dimension and density theory
(`TauCeti.Comodule.topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range` and
`TauCeti.Comodule.isOpen_range_projectiveOrbitMap_mk_one_of_range_eq_top`) to the restricted
representation of `K` on `𝔤(2)` yields the Malcev–Kostant change-of-triple theorem at fixed neutral
element:

* the `K`-orbit of `e` in `P(𝔤(2) × k)` has full dimension `dim 𝔤(2)`, and is open and dense in
  `P(𝔤(2) × k)`;
* for any second `sl₂` triple `(h, e', f')` sharing `h`, the scheme-theoretic `K`-orbits of `e` and
  `e'` in `P(𝔤(2) × k)` coincide, and some `k`-point `g ∈ K(k)` carries `(h, e, f)` to `(h, e', f')`
  under `Ad(g)`: first `g` carries `e` to `e'` while fixing `h`, and then `Ad(g) f = f'` follows
  because `(h, e')` uniquely determines its lowering partner (`IsSl2Triple.eq_of_isSl2Triple`);
* consequently, `e` and `e'` have the same scheme-theoretic adjoint `G`-orbit in `P(𝔤 × k)`.

Specializing `K` to `C_G(h)°` and combining with injectivity of the weighted Dynkin diagram on
dominant neutral elements in a Cartan subalgebra
(`RootPairing.Base.weightedDynkinDiagram_injective`) shows that two `sl₂` triples whose dominant
neutral elements have equal weighted Dynkin diagrams are conjugate by a `k`-point of `C_G(h)°`, and
their nilpositive elements define the same scheme-theoretic nilpotent `G`-orbit in `P(𝔤 × k)`.

## Main declarations

* `IsSl2Triple.topologicalKrullDim_range_projectiveOrbitMap_eigenspace_two_of_lieSubalgebra_le`,
  `IsSl2Triple.closure_range_projectiveOrbitMap_eigenspace_two_eq_univ_of_lieSubalgebra_le`, and
  `IsSl2Triple.isOpen_range_projectiveOrbitMap_eigenspace_two_of_lieSubalgebra_le`: full dimension,
  density, and openness of the `K`-orbit of `e` in `P(𝔤(2) × k)` for any closed subgroup
  `K ⊆ C_G(h)` whose Lie algebra contains `𝔤(0)`.
* `IsSl2Triple.range_projectiveOrbitMap_eigenspace_two_eq_of_lieSubalgebra_le` and
  `IsSl2Triple.exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_of_lieSubalgebra_le`:
  scheme-theoretic coincidence of the grade-two `K`-orbits and `K(k)`-conjugacy of `sl₂` triples
  sharing `h`.
* `IsSl2Triple.isOpen_range_projectiveOrbitMap_eigenspace_two`,
  `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq`,
  `IsSl2Triple.isOpen_range_projectiveOrbitMap_eigenspace_two_identityComponent`, and
  `IsSl2Triple.exists_mem_quotientPointsSubgroup_identityComponent_basePointsRepresentation_eq`:
  specializations to `C_G(h)` and to the connected centralizer `C_G(h)°`.
* `IsSl2Triple.range_projectiveOrbitMap_adjoint_eq`: two `sl₂` triples sharing `h` have the same
  scheme-theoretic adjoint `G`-orbit in `P(𝔤 × k)`.
* `IsSl2Triple.exists_mem_quotientPointsSubgroup_identityComponent_of_weightedDynkinDiagram_eq`
  and `IsSl2Triple.range_projectiveOrbitMap_adjoint_eq_of_weightedDynkinDiagram_eq`: triples whose
  dominant neutral elements have equal weighted Dynkin diagrams are conjugate under `C_G(h)°(k)` and
  have the same scheme-theoretic nilpotent `G`-orbit.

## References

* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, Theorem 3.6 and §4.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, Lemma 3.4.6, Theorem 3.4.10, and Theorem 3.5.4.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
-/

public section

open CategoryTheory TauCeti WithConv

namespace IsSl2Triple

universe u

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial
attribute [local instance 100] LieRing.ofAssociativeRing

section Subgroup

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  {h e f e' f' : Module.Dual k (Bialgebra.CotangentSpace k H)}

/-- **Dimension of the grade-two centralizer orbit.** For any closed subgroup `K = Spec (H ⧸ J)` of
`C_G(h)` whose Lie algebra contains `𝔤(0)`, the `K`-orbit of `e` in `P(𝔤(2) × k)` has full dimension
`dim 𝔤(2)`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_eigenspace_two_of_lieSubalgebra_le
    (t : IsSl2Triple h e f) {J : HopfIdeal k H} (hJ : centralizerHopfIdeal H h ≤ J)
    (hlie : (centralizerHopfIdeal H h).lieSubalgebra (B := k) ≤ J.lieSubalgebra (B := k)) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap (H := H ⧸ J.toIdeal)
        ((⟨e, t.e_mem_eigenspace_two_of_le hJ⟩, 1) : (centralizerAdHom h hJ).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _))) =
      Module.finrank k
        ((LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) h).eigenspace 2) := by
  let := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
  have : Algebra.FiniteType k (H ⧸ J.toIdeal) :=
    .of_surjective (Ideal.Quotient.mkₐ k J.toIdeal) Ideal.Quotient.mk_surjective
  rw [Comodule.topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range,
    t.range_differential_flip_eigenspace_two_eq_top_of_lieSubalgebra_le hJ hlie, finrank_top]
  congr 1
  rw [← centralizerAdHom_toLinearMap (J := J) h hJ,
    ← (centralizerAdHom h hJ).eigenspace_toSubmodule 2]
  exact LinearEquiv.finrank_eq
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- **Density of the grade-two centralizer orbit.** For any closed subgroup `K = Spec (H ⧸ J)` of
`C_G(h)` whose Lie algebra contains `𝔤(0)`, the `K`-orbit of `e` is dense in the projective
completion `P(𝔤(2) × k)` of `𝔤(2)`. -/
theorem closure_range_projectiveOrbitMap_eigenspace_two_eq_univ_of_lieSubalgebra_le
    (t : IsSl2Triple h e f) {J : HopfIdeal k H} (hJ : centralizerHopfIdeal H h ≤ J)
    (hlie : (centralizerHopfIdeal H h).lieSubalgebra (B := k) ≤ J.lieSubalgebra (B := k)) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
    closure (Set.range (Comodule.projectiveOrbitMap (H := H ⧸ J.toIdeal)
        ((⟨e, t.e_mem_eigenspace_two_of_le hJ⟩, 1) : (centralizerAdHom h hJ).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _))) = Set.univ := by
  let := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
  have : Algebra.FiniteType k (H ⧸ J.toIdeal) :=
    .of_surjective (Ideal.Quotient.mkₐ k J.toIdeal) Ideal.Quotient.mk_surjective
  exact Comodule.closure_range_projectiveOrbitMap_mk_one_eq_univ_of_range_eq_top _
    (t.range_differential_flip_eigenspace_two_eq_top_of_lieSubalgebra_le hJ hlie)

/-- **Openness of the grade-two centralizer orbit.** For any closed subgroup `K = Spec (H ⧸ J)` of
`C_G(h)` whose Lie algebra contains `𝔤(0)`, the `K`-orbit of `e` is open in `P(𝔤(2) × k)`. -/
theorem isOpen_range_projectiveOrbitMap_eigenspace_two_of_lieSubalgebra_le
    (t : IsSl2Triple h e f) {J : HopfIdeal k H} (hJ : centralizerHopfIdeal H h ≤ J)
    (hlie : (centralizerHopfIdeal H h).lieSubalgebra (B := k) ≤ J.lieSubalgebra (B := k)) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
    IsOpen (Set.range (Comodule.projectiveOrbitMap (H := H ⧸ J.toIdeal)
        ((⟨e, t.e_mem_eigenspace_two_of_le hJ⟩, 1) : (centralizerAdHom h hJ).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _))) := by
  let := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
  have : Algebra.FiniteType k (H ⧸ J.toIdeal) :=
    .of_surjective (Ideal.Quotient.mkₐ k J.toIdeal) Ideal.Quotient.mk_surjective
  exact Comodule.isOpen_range_projectiveOrbitMap_mk_one_of_range_eq_top _
    (t.range_differential_flip_eigenspace_two_eq_top_of_lieSubalgebra_le hJ hlie)

/-- **Coincidence of grade-two centralizer orbits.** For any closed subgroup `K = Spec (H ⧸ J)` of
`C_G(h)` whose Lie algebra contains `𝔤(0)` and any two `sl₂` triples `(h, e, f)` and `(h, e', f')`
sharing `h`, the scheme-theoretic `K`-orbits of `e` and `e'` in `P(𝔤(2) × k)` coincide. -/
theorem range_projectiveOrbitMap_eigenspace_two_eq_of_lieSubalgebra_le
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h e' f') {J : HopfIdeal k H}
    (hJ : centralizerHopfIdeal H h ≤ J)
    (hlie : (centralizerHopfIdeal H h).lieSubalgebra (B := k) ≤ J.lieSubalgebra (B := k)) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
    Set.range (Comodule.projectiveOrbitMap (H := H ⧸ J.toIdeal)
        ((⟨e, t.e_mem_eigenspace_two_of_le hJ⟩, 1) : (centralizerAdHom h hJ).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _)) =
      Set.range (Comodule.projectiveOrbitMap (H := H ⧸ J.toIdeal)
        ((⟨e', t'.e_mem_eigenspace_two_of_le hJ⟩, 1) : (centralizerAdHom h hJ).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _)) := by
  let := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
  have : Algebra.FiniteType k (H ⧸ J.toIdeal) :=
    .of_surjective (Ideal.Quotient.mkₐ k J.toIdeal) Ideal.Quotient.mk_surjective
  exact Comodule.range_projectiveOrbitMap_mk_one_eq_of_range_eq_top _ _
    (t.range_differential_flip_eigenspace_two_eq_top_of_lieSubalgebra_le hJ hlie)
    (t'.range_differential_flip_eigenspace_two_eq_top_of_lieSubalgebra_le hJ hlie)

/-- **Conjugacy of `sl₂` triples sharing `h` under a centralizer subgroup with Lie algebra `𝔤(0)`.**
If `K = Spec (H ⧸ J)` is a closed subgroup of `C_G(h)` whose Lie algebra contains `𝔤(0)` and
`(h, e, f)`, `(h, e', f')` are two `sl₂` triples sharing `h`, then some `k`-point `g ∈ K(k)` fixes
`h` and carries `e` to `e'` and `f` to `f'` under the adjoint action. -/
theorem exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_of_lieSubalgebra_le
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h e' f') {J : HopfIdeal k H}
    (hJ : centralizerHopfIdeal H h ≤ J)
    (hlie : (centralizerHopfIdeal H h).lieSubalgebra (B := k) ≤ J.lieSubalgebra (B := k)) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' := by
  have ⟨g, hvan, hge⟩ : ∃ g : WithConv (H →ₐ[k] k),
      (∀ a : H, a ∈ J → g.ofConv a = 0) ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e =
          e' := by
    let π : H →ₐc[k] H ⧸ J.toIdeal := Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
    let := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H)) π.toCoalgHom
    have : Algebra.FiniteType k (H ⧸ J.toIdeal) :=
      .of_surjective (Ideal.Quotient.mkₐ k J.toIdeal) Ideal.Quotient.mk_surjective
    obtain ⟨q, hq⟩ := Comodule.exists_basePointsRepresentation_eq_of_range_eq_top _ _
      (t.range_differential_flip_eigenspace_two_eq_top_of_lieSubalgebra_le hJ hlie)
      (t'.range_differential_flip_eigenspace_two_eq_top_of_lieSubalgebra_le hJ hlie)
    have hqe := congrArg Subtype.val hq
    rw [Subcomodule.coe_basePointsRepresentation,
      Comodule.basePointsRepresentation_corestrict π q] at hqe
    refine ⟨BialgHom.mapDomain π q, fun a ha ↦ ?_, hqe⟩
    rw [BialgHom.mapDomain_apply_apply, Bialgebra.Quotient.mkBialgHom_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr ha), map_zero]
  have hgJ : g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
      (CommAlgCat.of k k) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff (_root_.CommHopfAlgCat.of k H) J
      (CommAlgCat.of k k) g).mpr hvan
  have hgh :
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h :=
    (Comodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff h g).mp <| by
      rw [← centralizerHopfIdeal_def]
      exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff (_root_.CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H h) (CommAlgCat.of k k) g).mpr fun a ha ↦ hvan a (hJ ha)
  have hgf :
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
        f' := by
    have tg := t.basePointsRepresentation_adjointComodule g
    rw [hgh, hge] at tg
    exact tg.eq_of_isSl2Triple k t'
  exact ⟨g, hgJ, hgh, hge, hgf⟩

/-! ### Specializations to `C_G(h)` -/

/-- The `C_G(h)`-orbit of `e` in `P(𝔤(2) × k)` has full dimension `dim 𝔤(2)`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_eigenspace_two (t : IsSl2Triple h e f) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) (centralizerHopfIdeal H h).toIdeal).toCoalgHom
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := H ⧸ (centralizerHopfIdeal H h).toIdeal)
        ((⟨e, t.e_mem_eigenspace_two⟩, 1) : (centralizerAdHom h le_rfl).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _))) =
      Module.finrank k
        ((LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) h).eigenspace 2) :=
  t.topologicalKrullDim_range_projectiveOrbitMap_eigenspace_two_of_lieSubalgebra_le le_rfl le_rfl

/-- The `C_G(h)`-orbit of `e` is dense in `P(𝔤(2) × k)`. -/
theorem closure_range_projectiveOrbitMap_eigenspace_two_eq_univ (t : IsSl2Triple h e f) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) (centralizerHopfIdeal H h).toIdeal).toCoalgHom
    closure (Set.range (Comodule.projectiveOrbitMap (H := H ⧸ (centralizerHopfIdeal H h).toIdeal)
        ((⟨e, t.e_mem_eigenspace_two⟩, 1) : (centralizerAdHom h le_rfl).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _))) = Set.univ :=
  t.closure_range_projectiveOrbitMap_eigenspace_two_eq_univ_of_lieSubalgebra_le le_rfl le_rfl

/-- The `C_G(h)`-orbit of `e` is open in `P(𝔤(2) × k)`. -/
theorem isOpen_range_projectiveOrbitMap_eigenspace_two (t : IsSl2Triple h e f) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) (centralizerHopfIdeal H h).toIdeal).toCoalgHom
    IsOpen (Set.range (Comodule.projectiveOrbitMap (H := H ⧸ (centralizerHopfIdeal H h).toIdeal)
        ((⟨e, t.e_mem_eigenspace_two⟩, 1) : (centralizerAdHom h le_rfl).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _))) :=
  t.isOpen_range_projectiveOrbitMap_eigenspace_two_of_lieSubalgebra_le le_rfl le_rfl

/-- Two `sl₂` triples sharing `h` have the same scheme-theoretic `C_G(h)`-orbit in `P(𝔤(2) × k)`. -/
theorem range_projectiveOrbitMap_eigenspace_two_eq
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h e' f') :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) (centralizerHopfIdeal H h).toIdeal).toCoalgHom
    Set.range (Comodule.projectiveOrbitMap (H := H ⧸ (centralizerHopfIdeal H h).toIdeal)
        ((⟨e, t.e_mem_eigenspace_two⟩, 1) : (centralizerAdHom h le_rfl).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _)) =
      Set.range (Comodule.projectiveOrbitMap (H := H ⧸ (centralizerHopfIdeal H h).toIdeal)
        ((⟨e', t'.e_mem_eigenspace_two⟩, 1) : (centralizerAdHom h le_rfl).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _)) :=
  t.range_projectiveOrbitMap_eigenspace_two_eq_of_lieSubalgebra_le t' le_rfl le_rfl

/-- Any two `sl₂` triples sharing `h` are conjugate by a rational point of `C_G(h)`. -/
theorem exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h e' f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H h) (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' :=
  t.exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_of_lieSubalgebra_le t' le_rfl
    le_rfl

/-- **Two `sl₂` triples sharing `h` define the same nilpotent `G`-orbit.** Their nilpositive
elements have identical scheme-theoretic adjoint orbit images in `P(𝔤 × k)`. -/
theorem range_projectiveOrbitMap_adjoint_eq (t : IsSl2Triple h e f) (t' : IsSl2Triple h e' f') :
    Set.range (Comodule.projectiveOrbitMap (H := H)
        ((e, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one e)) =
      Set.range (Comodule.projectiveOrbitMap (H := H)
        ((e', 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one e')) := by
  obtain ⟨g, -, -, rfl, -⟩ :=
    t.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq t'
  exact (Comodule.range_projectiveOrbitMap_mk_one_basePointsRepresentation g e).symm

end Subgroup

section IdentityComponent

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  {h e f e' f' : Module.Dual k (Bialgebra.CotangentSpace k H)}

/-- For the connected centralizer `C_G(h)°`, the differential at `e` of the orbit map on `𝔤(2)` is
onto. -/
theorem range_differential_flip_eigenspace_two_identityComponent_eq_top (t : IsSl2Triple h e f) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k)
        (centralizerHopfIdeal H h).identityComponent.toIdeal).toCoalgHom
    LinearMap.range ((Comodule.differential (R := k)
        (H := H ⧸ (centralizerHopfIdeal H h).identityComponent.toIdeal)
        (M := (centralizerAdHom h (centralizerHopfIdeal H h).le_identityComponent).eigenspace 2)
        ).toLinearMap.flip
        ⟨e, t.e_mem_eigenspace_two_of_le (centralizerHopfIdeal H h).le_identityComponent⟩) = ⊤ :=
  t.range_differential_flip_eigenspace_two_eq_top_of_lieSubalgebra_le
    (centralizerHopfIdeal H h).le_identityComponent
    (centralizerHopfIdeal H h).lieSubalgebra_identityComponent.ge

/-- The `C_G(h)°`-orbit of `e` in `P(𝔤(2) × k)` has full dimension `dim 𝔤(2)`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_eigenspace_two_identityComponent
    (t : IsSl2Triple h e f) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k)
        (centralizerHopfIdeal H h).identityComponent.toIdeal).toCoalgHom
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := H ⧸ (centralizerHopfIdeal H h).identityComponent.toIdeal)
        ((⟨e, t.e_mem_eigenspace_two_of_le (centralizerHopfIdeal H h).le_identityComponent⟩, 1) :
          (centralizerAdHom h (centralizerHopfIdeal H h).le_identityComponent).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _))) =
      Module.finrank k
        ((LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) h).eigenspace 2) :=
  t.topologicalKrullDim_range_projectiveOrbitMap_eigenspace_two_of_lieSubalgebra_le
    (centralizerHopfIdeal H h).le_identityComponent
    (centralizerHopfIdeal H h).lieSubalgebra_identityComponent.ge

/-- The `C_G(h)°`-orbit of `e` is dense in `P(𝔤(2) × k)`. -/
theorem closure_range_projectiveOrbitMap_eigenspace_two_identityComponent_eq_univ
    (t : IsSl2Triple h e f) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k)
        (centralizerHopfIdeal H h).identityComponent.toIdeal).toCoalgHom
    closure (Set.range (Comodule.projectiveOrbitMap
        (H := H ⧸ (centralizerHopfIdeal H h).identityComponent.toIdeal)
        ((⟨e, t.e_mem_eigenspace_two_of_le (centralizerHopfIdeal H h).le_identityComponent⟩, 1) :
          (centralizerAdHom h (centralizerHopfIdeal H h).le_identityComponent).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _))) = Set.univ :=
  t.closure_range_projectiveOrbitMap_eigenspace_two_eq_univ_of_lieSubalgebra_le
    (centralizerHopfIdeal H h).le_identityComponent
    (centralizerHopfIdeal H h).lieSubalgebra_identityComponent.ge

/-- **Openness of the connected centralizer orbit on `𝔤(2)`.** The `C_G(h)°`-orbit of `e` is open
in `P(𝔤(2) × k)`. -/
theorem isOpen_range_projectiveOrbitMap_eigenspace_two_identityComponent
    (t : IsSl2Triple h e f) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k)
        (centralizerHopfIdeal H h).identityComponent.toIdeal).toCoalgHom
    IsOpen (Set.range (Comodule.projectiveOrbitMap
        (H := H ⧸ (centralizerHopfIdeal H h).identityComponent.toIdeal)
        ((⟨e, t.e_mem_eigenspace_two_of_le (centralizerHopfIdeal H h).le_identityComponent⟩, 1) :
          (centralizerAdHom h (centralizerHopfIdeal H h).le_identityComponent).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _))) :=
  t.isOpen_range_projectiveOrbitMap_eigenspace_two_of_lieSubalgebra_le
    (centralizerHopfIdeal H h).le_identityComponent
    (centralizerHopfIdeal H h).lieSubalgebra_identityComponent.ge

/-- Two `sl₂` triples sharing `h` have the same scheme-theoretic `C_G(h)°`-orbit in
`P(𝔤(2) × k)`. -/
theorem range_projectiveOrbitMap_eigenspace_two_identityComponent_eq
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h e' f') :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k)
        (centralizerHopfIdeal H h).identityComponent.toIdeal).toCoalgHom
    Set.range (Comodule.projectiveOrbitMap
        (H := H ⧸ (centralizerHopfIdeal H h).identityComponent.toIdeal)
        ((⟨e, t.e_mem_eigenspace_two_of_le (centralizerHopfIdeal H h).le_identityComponent⟩, 1) :
          (centralizerAdHom h (centralizerHopfIdeal H h).le_identityComponent).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _)) =
      Set.range (Comodule.projectiveOrbitMap
        (H := H ⧸ (centralizerHopfIdeal H h).identityComponent.toIdeal)
        ((⟨e', t'.e_mem_eigenspace_two_of_le (centralizerHopfIdeal H h).le_identityComponent⟩, 1) :
          (centralizerAdHom h (centralizerHopfIdeal H h).le_identityComponent).eigenspace 2 × k)
        (Module.isUnimodular_mk_one _)) :=
  t.range_projectiveOrbitMap_eigenspace_two_eq_of_lieSubalgebra_le t'
    (centralizerHopfIdeal H h).le_identityComponent
    (centralizerHopfIdeal H h).lieSubalgebra_identityComponent.ge

/-- **Malcev–Kostant conjugacy at fixed neutral element.** Any two `sl₂` triples `(h, e, f)` and
`(h, e', f')` in `Lie(G)` sharing `h` are conjugate by a rational point of the connected
centralizer `C_G(h)°`. -/
theorem exists_mem_quotientPointsSubgroup_identityComponent_basePointsRepresentation_eq
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h e' f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H h).identityComponent (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' :=
  t.exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_of_lieSubalgebra_le t'
    (centralizerHopfIdeal H h).le_identityComponent
    (centralizerHopfIdeal H h).lieSubalgebra_identityComponent.ge

end IdentityComponent

section WeightedDynkinDiagram

/-- **Weighted Dynkin diagram uniqueness up to `C_G(h)°`-conjugacy.** If two `sl₂` triples in
`Lie(G)` have dominant neutral elements in a fixed Cartan subalgebra with the same weighted Dynkin
diagram, then some rational point of `C_G(h₁)°` carries the first triple to the second. -/
theorem exists_mem_quotientPointsSubgroup_identityComponent_of_weightedDynkinDiagram_eq
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    {b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base} {h₁ h₂ : b.dominantNeutralElements}
    {e₁ f₁ e₂ f₂ : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t₁ : IsSl2Triple (h₁ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₁ f₁)
    (t₂ : IsSl2Triple (h₂ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₂ f₂)
    (hdiag : b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H
          (h₁ : Module.Dual k (Bialgebra.CotangentSpace k H))).identityComponent
        (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g
          (h₁ : Module.Dual k (Bialgebra.CotangentSpace k H)) = h₂ ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e₁ =
          e₂ ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f₁ =
          f₂ := by
  obtain rfl := b.weightedDynkinDiagram_injective hdiag
  exact t₁.exists_mem_quotientPointsSubgroup_identityComponent_basePointsRepresentation_eq t₂

/-- **Weighted Dynkin diagrams determine the nilpotent `G`-orbit.** If two `sl₂` triples in
`Lie(G)` have dominant neutral elements in a fixed Cartan subalgebra with the same weighted Dynkin
diagram, then their nilpositive elements define the same scheme-theoretic adjoint `G`-orbit in
`P(𝔤 × k)`. -/
theorem range_projectiveOrbitMap_adjoint_eq_of_weightedDynkinDiagram_eq
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    {b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base} {h₁ h₂ : b.dominantNeutralElements}
    {e₁ f₁ e₂ f₂ : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t₁ : IsSl2Triple (h₁ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₁ f₁)
    (t₂ : IsSl2Triple (h₂ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₂ f₂)
    (hdiag : b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂) :
    Set.range (Comodule.projectiveOrbitMap (H := H)
        ((e₁, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one e₁)) =
      Set.range (Comodule.projectiveOrbitMap (H := H)
        ((e₂, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one e₂)) := by
  obtain rfl := b.weightedDynkinDiagram_injective hdiag
  exact t₁.range_projectiveOrbitMap_adjoint_eq t₂

end WeightedDynkinDiagram

end IsSl2Triple
