/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Boundary
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Exponential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Nilpotent.Cone
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Finite
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.GradeTwoOrbit
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant

/-!
# Nilpotent adjoint orbits, weighted Dynkin diagrams, and orbit closures

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero whose tangent Lie algebra `𝔤` has nondegenerate Killing form. Fix a Cartan
subalgebra `𝔥` of `𝔤` and a base `b` of its root system.

The rational adjoint orbits form the quotient `TauCeti.Comodule.VectorOrbit k H 𝔤` with the
closure partial order `O ≤ O' ↔ O ⊆ closure O'`. The subset of nilpotent orbits
(`TauCeti.nilpotentAdjointOrbits`) splits as `{0}` together with the nonzero nilpotent orbits
(`TauCeti.nonzeroNilpotentAdjointOrbits`).

## Main results

### Without connectedness
* `IsSl2Triple.exists_mem_quotientPointsSubgroup_identityComponent_dominant` and
  `TauCeti.exists_mem_quotientPointsSubgroup_identityComponent_dominant_isSl2Triple`: every `sl₂`
  triple (and every nonzero `ad`-nilpotent element) is conjugate under `G°(k)` to one whose neutral
  element is dominant for `b`.
* `TauCeti.exists_basePointsRepresentation_eq_smul_of_isNilpotent_ad` and
  `TauCeti.mk_zero_le_mk_of_isNilpotent_ad`: every nilpotent adjoint orbit is closed under nonzero
  scalar multiplication and contains `0` in its closure.
* `TauCeti.dominantNeutralOrbit` and `TauCeti.range_dominantNeutralOrbit`: sending a dominant
  neutral element `h ∈ b.dominantNeutralElements` to the adjoint orbit of any nilpositive element
  completing `h` to an `sl₂` triple is independent of the triple and surjects onto the nonzero
  nilpotent adjoint orbits.
* `TauCeti.finite_nonzeroNilpotentAdjointOrbits`, `TauCeti.finite_nilpotentAdjointOrbits`,
  `TauCeti.ncard_nonzeroNilpotentAdjointOrbits_le`, and `TauCeti.ncard_nilpotentAdjointOrbits_le`:
  there are finitely many nilpotent adjoint orbits, at most `3 ^ finrank k 𝔥` nonzero ones and at
  most `3 ^ finrank k 𝔥 + 1` in total.
* `TauCeti.nilpotentConeIdeal_le_ker_lift_eval_of_mk_le_mk`: the nilpotent cone is downward-closed
  in the closure order, in arbitrary characteristic and without connectedness or semisimplicity.

### For connected `G`
* `TauCeti.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq`: two dominant neutral
  elements conjugate under `G(k)` are equal, because `G`-invariant and `𝔤`-invariant polynomials
  coincide and separate dominant Weyl orbits.
* `TauCeti.dominantNeutralOrbitEquiv`: `b.dominantNeutralElements ≃ nonzeroNilpotentAdjointOrbits`.
* `TauCeti.mk_eq_mk_iff_weightedDynkinDiagram_eq` and
  `TauCeti.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`: two dominant `sl₂`
  triples give conjugate nilpositive elements if and only if their weighted Dynkin diagrams agree.
* `TauCeti.weightedDynkinDiagramOfOrbit`, `TauCeti.weightedDynkinDiagramOfOrbit_mk`, and
  `TauCeti.weightedDynkinDiagramOfOrbit_injective`: the canonical injection of nonzero nilpotent
  adjoint orbits into `b.support → Fin 3`, invariant under change of dominant triple.
* `TauCeti.isNilpotent_ad_of_mk_le_mk` and `TauCeti.isLowerSet_nilpotentAdjointOrbits`: the
  nilpotent adjoint orbits form a lower set in the closure order.
* `TauCeti.closure_image_inter_basicOpen_snd_eq_biUnion_le_of_mem_nilpotentAdjointOrbits` and
  `TauCeti.closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt_of_mem_nilpotentAdjointOrbits`:
  inside the affine chart `𝔤` of `P(𝔤 × k)`, the closure and boundary of every nilpotent orbit are
  the exact finite unions of the full scheme-point orbit images below it.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, Chapters 3 and 6.
* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032.
* J. C. Jantzen, *Nilpotent Orbits in Representation Theory*, Progress in Mathematics 228 (2004).
-/

public section

open AlgebraicGeometry WithConv

namespace TauCeti

section Basic

universe u v

section Ring

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

attribute [local instance] Derivation.adjointComodule

/-- The base-point adjoint action preserves and reflects `ad`-nilpotence. -/
@[simp]
theorem isNilpotent_ad_basePointsRepresentation_iff (g : WithConv (H →ₐ[R] R))
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    IsNilpotent (LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H))
        (Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g x)) ↔
      IsNilpotent (LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x) := by
  simpa only [Derivation.basePointsAdjointLieEquiv_apply] using
    (Derivation.basePointsAdjointLieEquiv (R := R) (H := H) g).isNilpotent_ad_apply_iff x

end Ring

section Field

variable (k : Type u) (H : Type v) [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

attribute [local instance] Derivation.adjointComodule

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- The set of nilpotent rational adjoint orbits of `G = Spec H` in its Lie algebra `𝔤`. -/
def nilpotentAdjointOrbits : Set (Comodule.VectorOrbit k H 𝔤) :=
  {O | ∃ e : 𝔤, IsNilpotent (LieAlgebra.ad k 𝔤 e) ∧ O = Comodule.VectorOrbit.mk e}

/-- The set of nonzero nilpotent rational adjoint orbits of `G = Spec H` in its Lie algebra `𝔤`. -/
def nonzeroNilpotentAdjointOrbits : Set (Comodule.VectorOrbit k H 𝔤) :=
  {O | ∃ e : 𝔤, e ≠ 0 ∧ IsNilpotent (LieAlgebra.ad k 𝔤 e) ∧ O = Comodule.VectorOrbit.mk e}

variable {k H}

/-- The adjoint orbit of `e` is nilpotent if and only if `ad e` is nilpotent. -/
@[simp]
theorem mem_nilpotentAdjointOrbits_mk {e : 𝔤} :
    Comodule.VectorOrbit.mk e ∈ nilpotentAdjointOrbits k H ↔ IsNilpotent (LieAlgebra.ad k 𝔤 e) := by
  refine ⟨?_, fun he ↦ ⟨e, he, rfl⟩⟩
  rintro ⟨e', he', hmk⟩
  obtain ⟨g, rfl⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp hmk.symm
  exact (isNilpotent_ad_basePointsRepresentation_iff g e').mpr he'

/-- The adjoint orbit of `e` is a nonzero nilpotent orbit if and only if `e ≠ 0` and `ad e` is
nilpotent. -/
@[simp]
theorem mem_nonzeroNilpotentAdjointOrbits_mk {e : 𝔤} :
    Comodule.VectorOrbit.mk e ∈ nonzeroNilpotentAdjointOrbits k H ↔
      e ≠ 0 ∧ IsNilpotent (LieAlgebra.ad k 𝔤 e) := by
  refine ⟨?_, fun ⟨he0, he⟩ ↦ ⟨e, he0, he, rfl⟩⟩
  rintro ⟨e', he'0, he', hmk⟩
  obtain ⟨g, rfl⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp hmk.symm
  refine ⟨fun h0 ↦ he'0 ?_, (isNilpotent_ad_basePointsRepresentation_iff g e').mpr he'⟩
  rw [← Derivation.basePointsAdjointLieEquiv_apply] at h0
  exact (map_eq_zero_iff _ (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).injective).mp
    h0

/-- The zero orbit is a nilpotent adjoint orbit. -/
theorem mk_zero_mem_nilpotentAdjointOrbits :
    (Comodule.VectorOrbit.mk (0 : 𝔤) : Comodule.VectorOrbit k H 𝔤) ∈
      nilpotentAdjointOrbits k H := by
  rw [mem_nilpotentAdjointOrbits_mk, map_zero]
  exact IsNilpotent.zero

/-- The zero orbit is not a nonzero nilpotent adjoint orbit. -/
theorem mk_zero_notMem_nonzeroNilpotentAdjointOrbits :
    (Comodule.VectorOrbit.mk (0 : 𝔤) : Comodule.VectorOrbit k H 𝔤) ∉
      nonzeroNilpotentAdjointOrbits k H := by
  simp

/-- Every nonzero nilpotent adjoint orbit is a nilpotent adjoint orbit. -/
theorem nonzeroNilpotentAdjointOrbits_subset_nilpotentAdjointOrbits :
    nonzeroNilpotentAdjointOrbits k H ⊆ nilpotentAdjointOrbits k H := by
  rintro _ ⟨e, -, he, rfl⟩
  exact ⟨e, he, rfl⟩

/-- The nilpotent adjoint orbits are the zero orbit together with the nonzero nilpotent orbits. -/
theorem nilpotentAdjointOrbits_eq_insert_zero :
    nilpotentAdjointOrbits k H =
      insert (Comodule.VectorOrbit.mk (0 : 𝔤)) (nonzeroNilpotentAdjointOrbits k H) := by
  ext O
  induction O using Comodule.VectorOrbit.ind with | h e
  simp only [mem_nilpotentAdjointOrbits_mk, Set.mem_insert_iff,
    mem_nonzeroNilpotentAdjointOrbits_mk]
  constructor
  · intro he
    by_cases h0 : e = 0
    · exact Or.inl (by rw [h0])
    · exact Or.inr ⟨h0, he⟩
  · rintro (h0 | ⟨-, he⟩)
    · obtain ⟨g, hg⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp h0
      rw [← Derivation.basePointsAdjointLieEquiv_apply] at hg
      have he0 : e = 0 :=
        (map_eq_zero_iff _ (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).injective).mp
          hg
      rw [he0, map_zero]
      exact IsNilpotent.zero
    · exact he

end Field

end Basic

end TauCeti

namespace IsSl2Triple

open TauCeti

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

attribute [local instance] Derivation.adjointComodule

/-- **Conjugating an `sl₂` triple into the dominant chamber by `G°(k)`.** For any Cartan subalgebra
`𝔥` of `𝔤` and base `b` of its root system, every `sl₂` triple `(h, e, f)` in `𝔤` is conjugate by
a rational point `g ∈ G°(k)` to a triple whose neutral element lies in `b.dominantNeutralElements`.
No connectedness of `G` is assumed. -/
theorem exists_mem_quotientPointsSubgroup_identityComponent_dominant
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)} (t : IsSl2Triple h e f) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∃ h' ∈ b.dominantNeutralElements,
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h' ∧
          IsSl2Triple (h' : Module.Dual k (Bialgebra.CotangentSpace k H))
            (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e)
            (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g
              f) := by
  let _ : LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
    ratLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))
  obtain ⟨φ, hφ, h', hh', hφh, t'⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  obtain ⟨g, hg, hgeq⟩ :=
    exists_mem_closure_unipotent_identityComponent_of_mem_intLieAlgebra (H := H) hφ
  have hg_mem : g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨hu, _⟩; exact hu) hg
  have hact (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g x =
        φ • x := by
    rw [← hgeq]
    simp [Derivation.basePointsAdjointLieEquiv_apply]
  refine ⟨g, hg_mem, h', hh', ?_, ?_⟩
  · rwa [hact]
  · simpa only [hact] using t'

end IsSl2Triple

namespace TauCeti

section Finiteness

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]

attribute [local instance] Derivation.adjointComodule

/-- **Conjugating a nonzero nilpotent element to a dominant `sl₂` triple by `G°(k)`.** Over an
algebraically closed field of characteristic zero, every nonzero `ad`-nilpotent element of a
Killing tangent Lie algebra is conjugate under `G°(k)` to the nilpositive element of an `sl₂`
triple whose neutral element is dominant for `b`. No connectedness of `G` is assumed. -/
theorem exists_mem_quotientPointsSubgroup_identityComponent_dominant_isSl2Triple
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (he : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))
    (he0 : e ≠ 0) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∃ h ∈ b.dominantNeutralElements, ∃ f : Module.Dual k (Bialgebra.CotangentSpace k H),
        IsSl2Triple (h : Module.Dual k (Bialgebra.CotangentSpace k H))
          (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e)
          f := by
  obtain ⟨h₀, f₀, t⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
  obtain ⟨g, hg, h, hh, -, t'⟩ :=
    t.exists_mem_quotientPointsSubgroup_identityComponent_dominant b
  exact ⟨g, hg, h, hh, _, t'⟩

variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Nilpotent adjoint orbits are conical.** Every nonzero scalar multiple of an `ad`-nilpotent
element lies in its rational adjoint orbit. No connectedness of `G` is assumed. -/
theorem exists_basePointsRepresentation_eq_smul_of_isNilpotent_ad {e : 𝔤}
    (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) {t : k} (ht : t ≠ 0) :
    ∃ g : WithConv (H →ₐ[k] k), Comodule.basePointsRepresentation 𝔤 g e = t • e := by
  by_cases he0 : e = 0
  · exact ⟨1, by simp [he0]⟩
  · obtain ⟨h, f, tr⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
    have tr' : IsSl2Triple h (t • e) (t⁻¹ • f) :=
      { h_ne_zero := tr.h_ne_zero
        lie_e_f := by rw [smul_lie, lie_smul, tr.lie_e_f, smul_smul, mul_inv_cancel₀ ht, one_smul]
        lie_h_e_nsmul := by rw [lie_smul, tr.lie_h_e_nsmul, smul_comm]
        lie_h_f_nsmul := by rw [lie_smul, tr.lie_h_f_nsmul, smul_neg, smul_comm] }
    let G : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of k H
    obtain ⟨g, -, -, hge, -⟩ :=
      tr.exists_mem_quotientPointsSubgroup_identityComponent_basePointsRepresentation_eq
        (H := G) tr'
    exact ⟨g, hge⟩

/-- **Zero lies in the closure of every nilpotent adjoint orbit.** No connectedness of `G` is
assumed. -/
theorem mk_zero_le_mk_of_isNilpotent_ad {e : 𝔤} (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) :
    (Comodule.VectorOrbit.mk (0 : 𝔤) : Comodule.VectorOrbit k H 𝔤) ≤
      Comodule.VectorOrbit.mk e :=
  Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul fun _ ht ↦
    exists_basePointsRepresentation_eq_smul_of_isNilpotent_ad he ht

/-- The adjoint orbit attached to a dominant neutral element `h ∈ b.dominantNeutralElements`: the
rational orbit of the nilpositive element of any `sl₂` triple with neutral element `h`. By
`TauCeti.dominantNeutralOrbit_eq_mk`, this is independent of the choice of triple. -/
noncomputable def dominantNeutralOrbit {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements) :
    Comodule.VectorOrbit k H 𝔤 :=
  Comodule.VectorOrbit.mk (((b.mem_dominantNeutralElements_iff _).mp h.property).1.choose)

/-- **Independence of triple.** For every `sl₂` triple `(h, e, f)` with dominant neutral element
`h`, the orbit attached to `h` is `Comodule.VectorOrbit.mk e`. -/
theorem dominantNeutralOrbit_eq_mk {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements)
    {e f : 𝔤} (t : IsSl2Triple (h : 𝔤) e f) :
    dominantNeutralOrbit (H := H) b h = Comodule.VectorOrbit.mk e := by
  let G : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of k H
  have hex := ((b.mem_dominantNeutralElements_iff _).mp h.property).1
  have t₀ : IsSl2Triple (h : 𝔤) hex.choose hex.choose_spec.choose := hex.choose_spec.choose_spec
  obtain ⟨g, -, -, hge, -⟩ :=
    t₀.exists_mem_quotientPointsSubgroup_identityComponent_basePointsRepresentation_eq (H := G) t
  exact Comodule.VectorOrbit.mk_eq_mk_iff.mpr ⟨g, hge⟩

/-- The orbit attached to a dominant neutral element is a nonzero nilpotent adjoint orbit. -/
theorem dominantNeutralOrbit_mem_nonzeroNilpotentAdjointOrbits {𝔥 : LieSubalgebra k 𝔤}
    [𝔥.IsCartanSubalgebra] (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (h : b.dominantNeutralElements) :
    dominantNeutralOrbit (H := H) b h ∈ nonzeroNilpotentAdjointOrbits k H := by
  obtain ⟨e, f, t⟩ := ((b.mem_dominantNeutralElements_iff _).mp h.property).1
  rw [dominantNeutralOrbit_eq_mk b h t]
  exact mem_nonzeroNilpotentAdjointOrbits_mk.mpr ⟨t.e_ne_zero, t.isNilpotent_toEnd_e (M := 𝔤)⟩

/-- **Every nonzero nilpotent adjoint orbit comes from a dominant neutral element.** No
connectedness of `G` is assumed. -/
theorem range_dominantNeutralOrbit {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Set.range (dominantNeutralOrbit (H := H) b) = nonzeroNilpotentAdjointOrbits k H := by
  ext O
  constructor
  · rintro ⟨h, rfl⟩
    exact dominantNeutralOrbit_mem_nonzeroNilpotentAdjointOrbits b h
  · intro hO
    induction O using Comodule.VectorOrbit.ind with | h e
    obtain ⟨he0, he⟩ := mem_nonzeroNilpotentAdjointOrbits_mk.mp hO
    let G : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of k H
    obtain ⟨g, -, h, hh, f, t⟩ :=
      exists_mem_quotientPointsSubgroup_identityComponent_dominant_isSl2Triple (H := G) b he he0
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [dominantNeutralOrbit_eq_mk b ⟨h, hh⟩ t, Comodule.VectorOrbit.mk_basePointsRepresentation]

variable (k H) in
/-- **Finiteness of nonzero nilpotent adjoint orbits.** Over an algebraically closed field of
characteristic zero, a finite-type affine group whose Lie algebra has nondegenerate Killing form
has only finitely many nonzero nilpotent adjoint orbits. No connectedness of `G` is assumed. -/
theorem finite_nonzeroNilpotentAdjointOrbits : (nonzeroNilpotentAdjointOrbits k H).Finite := by
  obtain ⟨𝔥, h𝔥, ⟨b⟩⟩ := exists_isCartanSubalgebra_base k 𝔤
  rw [← range_dominantNeutralOrbit (H := H) b]
  exact Set.finite_range _

variable (k H) in
/-- **Finiteness of nilpotent adjoint orbits.** Over an algebraically closed field of
characteristic zero, a finite-type affine group whose Lie algebra has nondegenerate Killing form
has only finitely many nilpotent adjoint orbits. No connectedness of `G` is assumed. -/
theorem finite_nilpotentAdjointOrbits : (nilpotentAdjointOrbits k H).Finite := by
  rw [nilpotentAdjointOrbits_eq_insert_zero]
  exact (finite_nonzeroNilpotentAdjointOrbits k H).insert _

/-- **Explicit upper bound on nonzero nilpotent adjoint orbits.** There are at most
`3 ^ finrank k 𝔥` nonzero nilpotent adjoint orbits, where `𝔥` is any Cartan subalgebra of `𝔤`.
No connectedness of `G` is assumed. -/
theorem ncard_nonzeroNilpotentAdjointOrbits_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    (nonzeroNilpotentAdjointOrbits k H).ncard ≤ 3 ^ Module.finrank k 𝔥 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  rw [← range_dominantNeutralOrbit (H := H) b, ← Set.image_univ]
  have hle : (dominantNeutralOrbit (H := H) b '' Set.univ).ncard ≤
      (Set.univ : Set b.dominantNeutralElements).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_coe_set_eq] at hle
  exact hle.trans b.ncard_dominantNeutralElements_le

/-- **Explicit upper bound on nilpotent adjoint orbits.** There are at most
`3 ^ finrank k 𝔥 + 1` nilpotent adjoint orbits (including the zero orbit), where `𝔥` is any Cartan
subalgebra of `𝔤`. No connectedness of `G` is assumed. -/
theorem ncard_nilpotentAdjointOrbits_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    (nilpotentAdjointOrbits k H).ncard ≤ 3 ^ Module.finrank k 𝔥 + 1 := by
  rw [nilpotentAdjointOrbits_eq_insert_zero]
  exact (Set.ncard_insert_le _ _).trans
    (Nat.add_le_add_right (ncard_nonzeroNilpotentAdjointOrbits_le (H := H) 𝔥) 1)

end Finiteness

section

universe u

private theorem mem_coinvariants_of_mem_adjointInvariantPolynomials {k H : Type u} [Field k]
    [CommRing H] [HopfAlgebra k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]
    {p : SymmetricAlgebra k (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H)))}
    (hp : p ∈ adjointInvariantPolynomials k H) :
    letI := Derivation.adjointComodule (R := k) (H := H)
    letI := Comodule.dual k H (Module.Dual k (Bialgebra.CotangentSpace k H))
    letI := ComoduleAlgebra.symmetricAlgebra k H
      (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    p ∈ ComoduleAlgebra.coinvariants k H
      (SymmetricAlgebra k (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H)))) := by
  let _ := Derivation.adjointComodule (R := k) (H := H)
  let _ := Comodule.dual k H (Module.Dual k (Bialgebra.CotangentSpace k H))
  let f₁ :=
    let _ := adjointPolynomialComoduleAlgebra k H
    ComoduleAlgebra.coactAlgHom k H
      (SymmetricAlgebra k (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H))))
  let f₂ :=
    let _ := ComoduleAlgebra.symmetricAlgebra k H
      (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    ComoduleAlgebra.coactAlgHom k H
      (SymmetricAlgebra k (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H))))
  have hf₁ (x) : f₁ x =
      (let _ := adjointPolynomialComoduleAlgebra k H; Comodule.coact (R := k) (C := H) x) :=
    let _ := adjointPolynomialComoduleAlgebra k H
    ComoduleAlgebra.coactAlgHom_apply x
  have hf₂ (x) : f₂ x =
      (let _ := ComoduleAlgebra.symmetricAlgebra k H
        (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H)))
      Comodule.coact (R := k) (C := H) x) :=
    let _ := ComoduleAlgebra.symmetricAlgebra k H
      (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    ComoduleAlgebra.coactAlgHom_apply x
  have hcoact : f₂ = f₁ := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun φ ↦ ?_)
    change f₂ (SymmetricAlgebra.ι k _ φ) = f₁ (SymmetricAlgebra.ι k _ φ)
    rw [hf₂, hf₁, adjointPolynomialComoduleAlgebra_coact_ι (k := k) (H := H) φ]
    let _ := ComoduleAlgebra.symmetricAlgebra k H
      (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    dsimp only
    rw [ComoduleAlgebra.symmetricAlgebra_coact, AlgHom.toLinearMap_apply,
      Comodule.symmetricAlgebraCoact_ι, Comodule.dual_coact]
  let _ := ComoduleAlgebra.symmetricAlgebra k H
    (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H)))
  rw [ComoduleAlgebra.mem_coinvariants, ← hf₂ p, hcoact, hf₁ p]
  exact mem_adjointInvariantPolynomials.mp hp

end

section Classification

universe u

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

attribute [local instance] Derivation.adjointComodule

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Dominant neutral elements are rigid under `Ad(G(k))`.** For a connected finite-type affine
group over an algebraically closed field of characteristic zero whose Lie algebra has nondegenerate
Killing form, two dominant neutral elements conjugate under `G(k)` are equal. -/
theorem eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq
    {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h₁ h₂ : 𝔥}
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : WithConv (H →ₐ[k] k)} (hgh : Comodule.basePointsRepresentation 𝔤 g (h₁ : 𝔤) = h₂) :
    h₁ = h₂ := by
  let G : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of k H
  refine b.eq_of_mem_dominantNeutralElements_of_forall_mem_lieInvariants_eq hh₁ hh₂ fun p hp ↦ ?_
  have hp' : p ∈ adjointInvariantPolynomials k G := by
    rwa [adjointInvariantPolynomials_eq_lieInvariants]
  have hval := Comodule.lift_eval_basePointsRepresentation_eq_of_mem_coinvariants g (h₁ : 𝔤)
    (mem_coinvariants_of_mem_adjointInvariantPolynomials hp')
  rw [hgh] at hval
  exact hval.symm

/-- **Distinct dominant neutral elements give distinct nilpotent orbits.** For connected `G`, the
map `TauCeti.dominantNeutralOrbit` is injective on `b.dominantNeutralElements`. -/
theorem dominantNeutralOrbit_injective {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Injective (dominantNeutralOrbit (H := H) b) := by
  intro h₁ h₂ horb
  obtain ⟨e₁, f₁, t₁⟩ := ((b.mem_dominantNeutralElements_iff _).mp h₁.property).1
  obtain ⟨e₂, f₂, t₂⟩ := ((b.mem_dominantNeutralElements_iff _).mp h₂.property).1
  rw [dominantNeutralOrbit_eq_mk b h₁ t₁, dominantNeutralOrbit_eq_mk b h₂ t₂] at horb
  obtain ⟨g, hge⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp horb
  have t₁' : IsSl2Triple (Comodule.basePointsRepresentation 𝔤 g (h₁ : 𝔤)) e₂
      (Comodule.basePointsRepresentation 𝔤 g f₁) := by
    simpa only [hge] using t₁.basePointsRepresentation_adjointComodule g
  obtain ⟨u, -, huh, -, -⟩ := t₁'.exists_mem_closure_unipotent_centralizerHopfIdeal_eq t₂
  refine Subtype.ext
    (eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq b h₁.property h₂.property
      (g := u * g) ?_)
  simpa only [map_mul, mul_apply_eq_comp] using huh

/-- **Bijection between dominant neutral elements and nonzero nilpotent adjoint orbits.** For
connected `G`, `b.dominantNeutralElements` parametrizes `nonzeroNilpotentAdjointOrbits k H`
bijectively. -/
noncomputable def dominantNeutralOrbitEquiv {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    b.dominantNeutralElements ≃ nonzeroNilpotentAdjointOrbits k H :=
  Equiv.ofBijective
    (fun h ↦ ⟨dominantNeutralOrbit (H := H) b h,
      dominantNeutralOrbit_mem_nonzeroNilpotentAdjointOrbits b h⟩)
    ⟨fun _ _ h ↦ dominantNeutralOrbit_injective b (congrArg Subtype.val h), fun ⟨O, hO⟩ ↦ by
      obtain ⟨h, rfl⟩ := (range_dominantNeutralOrbit (H := H) b).symm.subset hO
      exact ⟨h, rfl⟩⟩

/-- **Weighted Dynkin diagram classification of nilpotent adjoint orbits.** Two dominant `sl₂`
triples determine the same adjoint orbit if and only if their weighted Dynkin diagrams agree. -/
theorem mk_eq_mk_iff_weightedDynkinDiagram_eq {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h₁ h₂ : b.dominantNeutralElements}
    {e₁ f₁ e₂ f₂ : 𝔤} (t₁ : IsSl2Triple (h₁ : 𝔤) e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤) e₂ f₂) :
    (Comodule.VectorOrbit.mk e₁ : Comodule.VectorOrbit k H 𝔤) = Comodule.VectorOrbit.mk e₂ ↔
      b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂ := by
  rw [← dominantNeutralOrbit_eq_mk b h₁ t₁, ← dominantNeutralOrbit_eq_mk b h₂ t₂,
    (dominantNeutralOrbit_injective b).eq_iff, b.weightedDynkinDiagram_injective.eq_iff]

/-- **Conjugacy criterion by weighted Dynkin diagrams.** The nilpositive elements of two dominant
`sl₂` triples are conjugate under `G(k)` if and only if their weighted Dynkin diagrams agree. -/
theorem exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq {𝔥 : LieSubalgebra k 𝔤}
    [𝔥.IsCartanSubalgebra] (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h₁ h₂ : b.dominantNeutralElements} {e₁ f₁ e₂ f₂ : 𝔤}
    (t₁ : IsSl2Triple (h₁ : 𝔤) e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤) e₂ f₂) :
    (∃ g : WithConv (H →ₐ[k] k), Comodule.basePointsRepresentation 𝔤 g e₁ = e₂) ↔
      b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂ := by
  rw [← Comodule.VectorOrbit.mk_eq_mk_iff]
  exact mk_eq_mk_iff_weightedDynkinDiagram_eq b t₁ t₂

/-- **The weighted Dynkin diagram of a nonzero nilpotent adjoint orbit.** For connected `G`, this
assigns to each nonzero nilpotent adjoint orbit the labeling `b.support → Fin 3` of the unique
dominant neutral element in its conjugacy class. -/
noncomputable def weightedDynkinDiagramOfOrbit {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (O : nonzeroNilpotentAdjointOrbits k H) : b.support → Fin 3 :=
  b.weightedDynkinDiagram ((dominantNeutralOrbitEquiv (H := H) b).symm O)

/-- **Change-of-triple law.** For any dominant `sl₂` triple `(h, e, f)`, the weighted Dynkin
diagram of the orbit of `e` is `b.weightedDynkinDiagram h`. -/
theorem weightedDynkinDiagramOfOrbit_mk {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h : b.dominantNeutralElements}
    {e f : 𝔤} (t : IsSl2Triple (h : 𝔤) e f)
    (hmem : Comodule.VectorOrbit.mk e ∈ nonzeroNilpotentAdjointOrbits k H :=
      mem_nonzeroNilpotentAdjointOrbits_mk.mpr ⟨t.e_ne_zero, t.isNilpotent_toEnd_e (M := 𝔤)⟩) :
    weightedDynkinDiagramOfOrbit (H := H) b ⟨Comodule.VectorOrbit.mk e, hmem⟩ =
      b.weightedDynkinDiagram h := by
  unfold weightedDynkinDiagramOfOrbit
  congr 1
  apply (dominantNeutralOrbitEquiv (H := H) b).injective
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext (dominantNeutralOrbit_eq_mk b h t).symm

/-- **Injectivity of the weighted Dynkin diagram map.** For connected `G`, nonzero nilpotent
adjoint orbits inject into the finite set `b.support → Fin 3` of weighted Dynkin diagrams. -/
theorem weightedDynkinDiagramOfOrbit_injective {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Injective (weightedDynkinDiagramOfOrbit (H := H) b) :=
  b.weightedDynkinDiagram_injective.comp (dominantNeutralOrbitEquiv (H := H) b).symm.injective

end Classification

section ClosureOrder

universe u

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Closure stability of the nilpotent cone.** If `e` lies on the nilpotent cone and the adjoint
orbit of `y` lies in the closure of the adjoint orbit of `e`, then `y` also lies on the nilpotent
cone. No characteristic, connectedness, or semisimplicity hypothesis is needed. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_of_mk_le_mk {e y : 𝔤}
    (he : nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 e)))
    (hle : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤
      Comodule.VectorOrbit.mk e) :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 y)) := by
  rw [nilpotentConeIdeal_le_iff] at he ⊢
  intro p hp hp₀
  rw [RingHom.mem_ker,
    Comodule.VectorOrbit.lift_eval_eq_of_le hle
      (mem_coinvariants_of_mem_adjointInvariantPolynomials hp)]
  exact he p hp hp₀

section Connected

variable [CharZero k] [ConnectedSpace (PrimeSpectrum H)]

/-- Any adjoint orbit in the closure of an orbit on the nilpotent cone consists of `ad`-nilpotent
elements. No semisimplicity hypothesis is needed. -/
theorem isNilpotent_ad_of_nilpotentConeIdeal_of_mk_le_mk {e y : 𝔤}
    (he : nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 e)))
    (hle : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤
      Comodule.VectorOrbit.mk e) :
    IsNilpotent (LieAlgebra.ad k 𝔤 y) := by
  let G : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of k H
  exact isNilpotent_ad_of_nilpotentConeIdeal_le_ker_lift_eval (H := G)
    (nilpotentConeIdeal_le_ker_lift_eval_of_mk_le_mk he hle)

section Killing

variable [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

/-- **Closure stability of `ad`-nilpotence.** For a connected finite-type affine group with Killing
Lie algebra, every vector in the closure of a nilpotent adjoint orbit is `ad`-nilpotent. -/
theorem isNilpotent_ad_of_mk_le_mk {e y : 𝔤} (he : IsNilpotent (LieAlgebra.ad k 𝔤 e))
    (hle : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤
      Comodule.VectorOrbit.mk e) :
    IsNilpotent (LieAlgebra.ad k 𝔤 y) :=
  isNilpotent_ad_of_nilpotentConeIdeal_of_mk_le_mk
    (nilpotentConeIdeal_le_ker_lift_eval_of_isNilpotent he) hle

/-- **The nilpotent adjoint orbits form a lower set in the closure order.** -/
theorem isLowerSet_nilpotentAdjointOrbits : IsLowerSet (nilpotentAdjointOrbits k H) := by
  intro O₁ O₂ hle hO₁
  induction O₁ using Comodule.VectorOrbit.ind with | h e
  induction O₂ using Comodule.VectorOrbit.ind with | h y
  exact mem_nilpotentAdjointOrbits_mk.mpr
    (isNilpotent_ad_of_mk_le_mk (mem_nilpotentAdjointOrbits_mk.mp hO₁) hle)

/-- Only finitely many adjoint orbits lie below a nilpotent adjoint orbit in the closure order. -/
theorem finite_lowerSet_of_mem_nilpotentAdjointOrbits {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentAdjointOrbits k H) :
    {O' : Comodule.VectorOrbit k H 𝔤 | O' ≤ O}.Finite :=
  (finite_nilpotentAdjointOrbits k H).subset fun _ hle ↦
    isLowerSet_nilpotentAdjointOrbits hle hO

/-- **Orbit closure decomposition for nilpotent orbits.** Inside the affine chart `𝔤 = {t ≠ 0}` of
`P(𝔤 × k)`, the closure of a nilpotent adjoint orbit `O` is the finite union of the full
scheme-point orbit images of the nilpotent orbits `O' ≤ O`. -/
theorem closure_image_inter_basicOpen_snd_eq_biUnion_le_of_mem_nilpotentAdjointOrbits
    {O : Comodule.VectorOrbit k H 𝔤} (hO : O ∈ nilpotentAdjointOrbits k H) :
    closure O.image ∩
        (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : Comodule.VectorOrbit k H 𝔤 | O' ≤ O}, O'.image :=
  Comodule.VectorOrbit.closure_image_inter_basicOpen_snd_eq_biUnion_le
    (finite_lowerSet_of_mem_nilpotentAdjointOrbits hO)

/-- **Orbit boundary decomposition for nilpotent orbits.** Inside the affine chart `𝔤 = {t ≠ 0}` of
`P(𝔤 × k)`, the boundary `closure O \ O` of a nilpotent adjoint orbit `O` is the finite union of
the full scheme-point orbit images of the strictly smaller nilpotent orbits `O' < O`. -/
theorem closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt_of_mem_nilpotentAdjointOrbits
    {O : Comodule.VectorOrbit k H 𝔤} (hO : O ∈ nilpotentAdjointOrbits k H) :
    (closure O.image \ O.image) ∩
        (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : Comodule.VectorOrbit k H 𝔤 | O' < O}, O'.image :=
  Comodule.VectorOrbit.closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt
    (finite_lowerSet_of_mem_nilpotentAdjointOrbits hO)

end Killing

end Connected

end ClosureOrder

end TauCeti
