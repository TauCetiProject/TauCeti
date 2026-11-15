/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Invariants
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.GradeTwoOrbit
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Exponential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Uniqueness
import Mathlib.Data.Set.Card
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.Algebra.Lie.Sl2.RangeKer

/-!
# Classification and finiteness of nilpotent orbits via weighted Dynkin diagrams

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero whose Lie algebra `𝔤 = (𝔪 / 𝔪²)*` has nondegenerate Killing form. Fix a Cartan
subalgebra `𝔥` of `𝔤` and a base `b` of its root system.

Combining the Jacobson–Morozov theorem, dominant-chamber normalization under `Int(𝔤)`, integration
of `Int(𝔤)` into `G°(k)` (`TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent`),
and Malcev–Kostant conjugacy at a shared neutral element
(`IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq`),
every nonzero `ad`-nilpotent element of `𝔤` is carried by `G°(k)` (hence `G(k)`) to the nilpositive
element of an `sl₂` triple with neutral element in `RootPairing.Base.dominantNeutralElements b`, and
the resulting nonzero nilpotent `G(k)`-orbits are exhausted by `b.dominantNeutralElements`. Thus
`G(k)` has only finitely many nilpotent orbits in `𝔤`
(`TauCeti.Comodule.VectorOrbit.finite_setOf_isNilpotentAd`), at most `3 ^ finrank k 𝔥` nonzero ones
and `3 ^ finrank k 𝔥 + 1` in total, without assuming `G` is connected.

When `G` is connected, `O(𝔤)^G = S(𝔤*)^𝔤` (`TauCeti.adjointInvariantPolynomials_eq_lieInvariants`),
so two dominant `sl₂` triples have `G(k)`-conjugate nilpositive elements if and only if their
weighted Dynkin diagrams coincide
(`IsSl2Triple.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`). This gives an
explicit equivalence `RootPairing.Base.dominantNeutralElementsEquivNilpotentOrbit` between
`Option b.dominantNeutralElements` and the subtype of nilpotent `G(k)`-orbits, and an injective
orbit-level weighted Dynkin diagram invariant
`RootPairing.Base.nilpotentOrbitWeightedDynkinDiagram`. Moreover, invariant polynomials are constant
on orbit closures (`TauCeti.Comodule.VectorOrbit.lift_eval_eq_of_mk_le_mk`), so nilpotent orbits are
downward closed in the closure order (`TauCeti.Comodule.VectorOrbit.IsNilpotentAd.of_le`) and every
nilpotent orbit closure decomposes into the orbit together with finitely many strictly lower
nilpotent orbits.

## Main declarations

* `TauCeti.Comodule.VectorOrbit.IsNilpotentAd`: predicate for nilpotent rational adjoint orbits,
  downward closed for connected `G` (`TauCeti.Comodule.VectorOrbit.IsNilpotentAd.of_le`).
* `TauCeti.Comodule.VectorOrbit.finite_setOf_isNilpotentAd`,
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_ne_zero_le`, and
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_le`: finiteness and `3 ^ rank` bounds for
  nilpotent `G(k)`-orbits.
* `IsSl2Triple.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`: for connected `G`,
  nilpositive elements of dominant `sl₂` triples are `G(k)`-conjugate iff their weighted Dynkin
  diagrams agree.
* `RootPairing.Base.dominantNeutralElementsEquivNilpotentOrbit` and
  `RootPairing.Base.nilpotentOrbitWeightedDynkinDiagram`: bijection with
  `Option b.dominantNeutralElements` and injective weighted Dynkin diagram classification of
  nilpotent orbits of connected `G`.
* `TauCeti.Comodule.VectorOrbit.finite_setOf_le_of_isNilpotentAd` and
  `TauCeti.Comodule.VectorOrbit.setOf_mk_le_eq_union_biUnion_of_isNilpotentAd`: finiteness of
  sub-orbits and decomposition of nilpotent orbit closures into finite unions of nilpotent orbits.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §§3.5 and 6.2.
* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

section Invariants

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

private theorem coactAlgHom_adjointPolynomialComoduleAlgebra :
    letI := adjointPolynomialComoduleAlgebra k H
    letI := Comodule.dual k H 𝔤
    ComoduleAlgebra.coactAlgHom k H (SymmetricAlgebra k (Module.Dual k 𝔤)) =
      Comodule.symmetricAlgebraCoact k H (Module.Dual k 𝔤) := by
  let := adjointPolynomialComoduleAlgebra k H
  let := Comodule.dual k H 𝔤
  ext φ
  simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    ComoduleAlgebra.coactAlgHom_apply, adjointPolynomialComoduleAlgebra_coact_ι,
    Comodule.symmetricAlgebraCoact_ι, Comodule.dual_coact]

open scoped TensorProduct in
private theorem mem_coinvariants_of_mem_adjointInvariantPolynomials
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)} (hp : p ∈ adjointInvariantPolynomials k H) :
    letI := Comodule.dual k H 𝔤
    letI := ComoduleAlgebra.symmetricAlgebra k H (Module.Dual k 𝔤)
    p ∈ ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k 𝔤)) := by
  have h1 : (letI := adjointPolynomialComoduleAlgebra k H
      letI := Comodule.dual k H 𝔤
      ComoduleAlgebra.coactAlgHom k H (SymmetricAlgebra k (Module.Dual k 𝔤)) p) =
      p ⊗ₜ[k] (1 : H) := by
    let := adjointPolynomialComoduleAlgebra k H
    let := Comodule.dual k H 𝔤
    rw [ComoduleAlgebra.coactAlgHom_apply]
    exact mem_adjointInvariantPolynomials.mp hp
  rw [coactAlgHom_adjointPolynomialComoduleAlgebra] at h1
  let := Comodule.dual k H 𝔤
  let := ComoduleAlgebra.symmetricAlgebra k H (Module.Dual k 𝔤)
  simpa [ComoduleAlgebra.mem_coinvariants, ComoduleAlgebra.symmetricAlgebra_coact] using h1

/-- **Adjoint-invariant polynomials are preserved by rational group points.** -/
theorem lift_eval_basePointsRepresentation_of_mem_adjointInvariantPolynomials
    (g : WithConv (H →ₐ[k] k)) (x : 𝔤) {p : SymmetricAlgebra k (Module.Dual k 𝔤)}
    (hp : p ∈ adjointInvariantPolynomials k H) :
    SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 (Comodule.basePointsRepresentation 𝔤 g x)) p =
      SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p :=
  Comodule.lift_eval_basePointsRepresentation_of_mem_coinvariants x g
    (mem_coinvariants_of_mem_adjointInvariantPolynomials hp)

/-- **Adjoint-invariant polynomials are constant on adjoint orbit closures.** -/
theorem lift_eval_eq_of_mk_le_mk_of_mem_adjointInvariantPolynomials [IsAlgClosed k]
    [Algebra.FiniteType k H] {x y : 𝔤}
    (h : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤ Comodule.VectorOrbit.mk x)
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)} (hp : p ∈ adjointInvariantPolynomials k H) :
    SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 y) p =
      SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p :=
  Comodule.VectorOrbit.lift_eval_eq_of_mk_le_mk h
    (mem_coinvariants_of_mem_adjointInvariantPolynomials hp)

/-- **The nilpotent cone is closed under adjoint orbit specialization.** If the adjoint orbit of `y`
lies below that of `x` in the closure order and `x` lies on the nilpotent cone, so does `y`. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_of_mk_le_mk [IsAlgClosed k] [Algebra.FiniteType k H]
    {x y : 𝔤}
    (h : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤ Comodule.VectorOrbit.mk x)
    (hx : nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x))) :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 y)) :=
  nilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦ by
    rw [RingHom.mem_ker, lift_eval_eq_of_mk_le_mk_of_mem_adjointInvariantPolynomials h hp]
    exact nilpotentConeIdeal_le_iff.mp hx p hp hp₀

end Invariants

namespace Comodule.VectorOrbit

section Predicate

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- A rational adjoint orbit is **nilpotent** when its elements act nilpotently under `ad`. -/
def IsNilpotentAd (O : VectorOrbit k H 𝔤) : Prop :=
  O.lift (fun x ↦ IsNilpotent (LieAlgebra.ad k 𝔤 x)) fun g x ↦ by
    rw [← Derivation.basePointsAdjointLieEquiv_apply]
    exact propext ((Derivation.basePointsAdjointLieEquiv g).isNilpotent_ad_apply_iff x)

/-- The orbit of `x ∈ 𝔤` is nilpotent precisely when `ad x` is nilpotent. -/
@[simp]
theorem isNilpotentAd_mk_iff {x : 𝔤} :
    (mk x : VectorOrbit k H 𝔤).IsNilpotentAd ↔ IsNilpotent (LieAlgebra.ad k 𝔤 x) := by
  rw [IsNilpotentAd, lift_mk]

/-- The zero adjoint orbit is nilpotent. -/
theorem isNilpotentAd_mk_zero : (mk (0 : 𝔤) : VectorOrbit k H 𝔤).IsNilpotentAd := by
  simp

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- Only `0` lies in the zero rational orbit of a linear representation. -/
@[simp]
theorem mk_eq_mk_zero_iff {M : Type*} [AddCommGroup M] [Module k M] [Comodule k H M] {v : M} :
    (mk v : VectorOrbit k H M) = mk 0 ↔ v = 0 := by
  rw [mk_eq_mk_iff]
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun hv ↦ ⟨1, by simp [hv]⟩⟩
  have hinv := congrArg (basePointsRepresentation M g⁻¹) hg
  simpa [Representation.inv_self_apply] using hinv

end Predicate

end Comodule.VectorOrbit

end TauCeti

namespace IsSl2Triple

open TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

/-- **Every `sl₂` triple is `G°(k)`-conjugate to one with dominant neutral element.** -/
theorem exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)} (t : IsSl2Triple h e f) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∃ h' ∈ b.dominantNeutralElements,
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h =
            h' ∧
          IsSl2Triple (h' : Module.Dual k (Bialgebra.CotangentSpace k H))
            (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e)
            (Comodule.basePointsRepresentation
              (Module.Dual k (Bialgebra.CotangentSpace k H)) g f) := by
  let _ := ratLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))
  obtain ⟨u, hu, h', hh', huh, tu⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  obtain ⟨g, hg, hgu⟩ :=
    intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent (H := H) hu
  have hact (z : Module.Dual k (Bialgebra.CotangentSpace k H)) :
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g z =
        u • z := by
    have := LinearMap.congr_fun (congrArg Units.val hgu) z
    rwa [MonoidHom.coe_toHomUnits] at this
  exact ⟨g, hg, h', hh', (hact h).trans huh, by rwa [hact e, hact f]⟩

end IsSl2Triple

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

section Finiteness

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Every nonzero `ad`-nilpotent element is `G(k)`-conjugate to a dominant `sl₂` triple.** -/
theorem exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad
    {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {e : 𝔤}
    (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) (he0 : e ≠ 0) :
    ∃ (g : WithConv (H →ₐ[k] k)), ∃ h ∈ b.dominantNeutralElements, ∃ f : 𝔤,
      IsSl2Triple (h : 𝔤) (Comodule.basePointsRepresentation 𝔤 g e) f := by
  let _ := ratLieAlgebra k 𝔤
  obtain ⟨u, hu, h, hh, f, t⟩ :=
    exists_mem_intLieAlgebra_isSl2Triple_smul_of_isNilpotent_ad b he he0
  obtain ⟨g, hgu⟩ := intLieAlgebra_le_range_basePointsRepresentation (H := H) hu
  have hact : Comodule.basePointsRepresentation 𝔤 g e = u • e := by
    have := LinearMap.congr_fun (congrArg Units.val hgu) e
    rwa [MonoidHom.coe_toHomUnits] at this
  exact ⟨g, h, hh, f, hact.symm ▸ t⟩

/-- Map sending each dominant neutral element to the rational adjoint orbit of its nilpositive
partner; by Malcev–Kostant conjugacy at fixed `h`, this orbit is independent of the partner. -/
private noncomputable def dominantNilpotentOrbit {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements) :
    Comodule.VectorOrbit k H 𝔤 :=
  Comodule.VectorOrbit.mk (Classical.choose ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1)

private theorem dominantNilpotentOrbit_eq_mk_of_isSl2Triple {𝔥 : LieSubalgebra k 𝔤}
    [𝔥.IsCartanSubalgebra] (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (h : b.dominantNeutralElements) {e f : 𝔤} (t : IsSl2Triple (h : 𝔤) e f) :
    dominantNilpotentOrbit (H := H) b h = Comodule.VectorOrbit.mk e := by
  obtain ⟨f₀, t₀⟩ :=
    Classical.choose_spec ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
  obtain ⟨g, -, -, hge, -⟩ :=
    t₀.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq t
  exact Comodule.VectorOrbit.mk_eq_mk_iff.mpr ⟨g, hge⟩

private theorem range_dominantNilpotentOrbit_eq {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Set.range (dominantNilpotentOrbit (H := H) b) =
      {O : Comodule.VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ Comodule.VectorOrbit.mk 0} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨h, rfl⟩
    obtain ⟨f₀, t₀⟩ :=
      Classical.choose_spec ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
    exact ⟨Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr (t₀.isNilpotent_toEnd_e (K := k) (M := 𝔤)),
      mt Comodule.VectorOrbit.mk_eq_mk_zero_iff.mp t₀.e_ne_zero⟩
  · intro O ⟨hO, hne⟩
    induction O using Comodule.VectorOrbit.ind with | h e =>
    have he0 : e ≠ 0 := mt Comodule.VectorOrbit.mk_eq_mk_zero_iff.mpr hne
    obtain ⟨g, h, hh, f, t⟩ :=
      exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad b
        (Comodule.VectorOrbit.isNilpotentAd_mk_iff.mp hO) he0
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [dominantNilpotentOrbit_eq_mk_of_isSl2Triple b ⟨h, hh⟩ t,
      Comodule.VectorOrbit.mk_basePointsRepresentation]

namespace Comodule.VectorOrbit

/-- **Bound on nonzero nilpotent orbits.** Over an algebraically closed field of characteristic
zero, `G(k)` has at most `3 ^ finrank k 𝔥` nonzero nilpotent adjoint orbits in `𝔤`, for any Cartan
subalgebra `𝔥` of `𝔤`. No connectedness hypothesis on `G` is needed. -/
theorem ncard_setOf_isNilpotentAd_ne_zero_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ mk 0}.ncard ≤ 3 ^ Module.finrank k 𝔥 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  rw [← range_dominantNilpotentOrbit_eq (H := H) b, ← Set.image_univ]
  refine (Set.ncard_image_le Set.finite_univ).trans ?_
  rw [Set.ncard_univ, Nat.card_coe_set_eq]
  exact b.ncard_dominantNeutralElements_le

/-- **Finiteness of nilpotent orbits.** Over an algebraically closed field of characteristic zero,
an affine group of finite type whose Lie algebra has nondegenerate Killing form has only finitely
many nilpotent rational adjoint orbits. No connectedness hypothesis on `G` is needed. -/
theorem finite_setOf_isNilpotentAd : {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd}.Finite := by
  obtain ⟨x, _⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k 𝔤
  let b := (LieAlgebra.IsKilling.rootSystem (LieSubalgebra.engel k x)).nonempty_base.some
  have hsub : {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd} ⊆
      insert (mk 0) (Set.range (dominantNilpotentOrbit (H := H) b)) := by
    intro O hO
    rw [range_dominantNilpotentOrbit_eq]
    rcases eq_or_ne O (mk 0) with rfl | h0
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨hO, h0⟩
  exact ((Set.finite_range _).insert (mk 0)).subset hsub

/-- The subtype of nilpotent rational adjoint orbits is finite. -/
instance : Finite {O : VectorOrbit k H 𝔤 // O.IsNilpotentAd} :=
  finite_setOf_isNilpotentAd.to_subtype

/-- **Bound on all nilpotent orbits.** Including the zero orbit, `G(k)` has at most
`3 ^ finrank k 𝔥 + 1` nilpotent adjoint orbits in `𝔤`. -/
theorem ncard_setOf_isNilpotentAd_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd}.ncard ≤ 3 ^ Module.finrank k 𝔥 + 1 := by
  have heq : {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd} =
      insert (mk 0) {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ mk 0} := by
    ext O
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    exact ⟨fun hO ↦ (em (O = mk 0)).imp_right (⟨hO, ·⟩),
      by rintro (rfl | ⟨hO, -⟩); exacts [isNilpotentAd_mk_zero, hO]⟩
  rw [heq]
  exact (Set.ncard_insert_le _ _).trans
    (Nat.add_le_add_right (ncard_setOf_isNilpotentAd_ne_zero_le 𝔥) 1)

end Comodule.VectorOrbit

end Finiteness

end TauCeti

section Connected

open TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

namespace IsSl2Triple

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Uniqueness of dominant neutral elements under `G(k)`-conjugacy for connected `G`.** -/
theorem eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h₁ h₂ : 𝔥} {e₁ f₁ e₂ f₂ : 𝔤}
    (t₁ : IsSl2Triple (h₁ : 𝔤) e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : WithConv (H →ₐ[k] k)} (hge : Comodule.basePointsRepresentation 𝔤 g e₁ = e₂) :
    h₁ = h₂ :=
  t₁.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq b t₂ hh₁ hh₂
    (Derivation.basePointsAdjointLieEquiv g)
    (by rwa [Derivation.basePointsAdjointLieEquiv_apply]) fun _ hp z ↦ by
      rw [Derivation.basePointsAdjointLieEquiv_apply]
      exact lift_eval_basePointsRepresentation_of_mem_adjointInvariantPolynomials g z
        ((adjointInvariantPolynomials_eq_lieInvariants
          (H := FiniteTypeCommHopfAlgCat.of k H)).symm ▸ hp)

/-- **Classification of nilpositive elements by weighted Dynkin diagrams.** For a connected affine
group `G` over an algebraically closed field of characteristic zero with Killing Lie algebra `𝔤`,
two `sl₂` triples `(h₁, e₁, f₁)` and `(h₂, e₂, f₂)` with dominant neutral elements in the same Weyl
chamber have `G(k)`-conjugate nilpositive elements if and only if their weighted Dynkin diagrams
coincide. -/
theorem exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h₁ h₂ : 𝔥} {e₁ f₁ e₂ f₂ : 𝔤}
    (t₁ : IsSl2Triple (h₁ : 𝔤) e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements) :
    (∃ g : WithConv (H →ₐ[k] k), Comodule.basePointsRepresentation 𝔤 g e₁ = e₂) ↔
      b.weightedDynkinDiagram ⟨h₁, hh₁⟩ = b.weightedDynkinDiagram ⟨h₂, hh₂⟩ := by
  constructor
  · rintro ⟨g, hge⟩
    congr 1
    exact Subtype.ext
      (t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq b t₂ hh₁ hh₂ hge)
  · intro hdiag
    obtain ⟨g, -, -, hge, -⟩ :=
      t₁.exists_mem_quotientPointsSubgroup_identityComponent_of_weightedDynkinDiagram_eq
        (H := FiniteTypeCommHopfAlgCat.of k H) (h₁ := ⟨h₁, hh₁⟩) (h₂ := ⟨h₂, hh₂⟩) t₂ hdiag
    exact ⟨g, hge⟩

end IsSl2Triple

namespace RootPairing.Base

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- Auxiliary map sending `none` to the zero nilpotent orbit and `some h` to the nilpotent orbit of
a nilpositive partner of `h ∈ b.dominantNeutralElements`. -/
private noncomputable def optionDominantToNilpotentOrbit
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Option b.dominantNeutralElements → {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd}
  | none => ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩
  | some h =>
    ⟨TauCeti.dominantNilpotentOrbit (H := H) b h,
      ((TauCeti.range_dominantNilpotentOrbit_eq (H := H) b).subset
        (Set.mem_range_self h)).1⟩

private theorem optionDominantToNilpotentOrbit_bijective
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Bijective (b.optionDominantToNilpotentOrbit (H := H)) := by
  constructor
  · rintro (_ | h₁) (_ | h₂) heq
    · rfl
    · exfalso
      exact ((TauCeti.range_dominantNilpotentOrbit_eq (H := H) b).subset
        (Set.mem_range_self h₂)).2 (congrArg Subtype.val heq).symm
    · exfalso
      exact ((TauCeti.range_dominantNilpotentOrbit_eq (H := H) b).subset
        (Set.mem_range_self h₁)).2 (congrArg Subtype.val heq)
    · congr 1
      obtain ⟨f₁, t₁⟩ :=
        Classical.choose_spec ((b.mem_dominantNeutralElements_iff h₁.1).mp h₁.2).1
      obtain ⟨f₂, t₂⟩ :=
        Classical.choose_spec ((b.mem_dominantNeutralElements_iff h₂.1).mp h₂.2).1
      obtain ⟨g, hge⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp (congrArg Subtype.val heq)
      exact Subtype.ext
        (t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq
          (H := H) b t₂ h₁.2 h₂.2 hge)
  · rintro ⟨O, hO⟩
    by_cases h0 : O = Comodule.VectorOrbit.mk 0
    · exact ⟨none, Subtype.ext h0.symm⟩
    · obtain ⟨h, hh⟩ : O ∈ Set.range (TauCeti.dominantNilpotentOrbit (H := H) b) := by
        rw [TauCeti.range_dominantNilpotentOrbit_eq]
        exact ⟨hO, h0⟩
      exact ⟨some h, Subtype.ext hh⟩

/-- **Bijection between `Option b.dominantNeutralElements` and nilpotent orbits.** For connected
`G`, `none` corresponds to the zero orbit and `some h` corresponds to the nilpotent `G(k)`-orbit of
any nilpositive partner of `h`. -/
noncomputable def dominantNeutralElementsEquivNilpotentOrbit
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Option b.dominantNeutralElements ≃ {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd} :=
  Equiv.ofBijective (b.optionDominantToNilpotentOrbit (H := H))
    (b.optionDominantToNilpotentOrbit_bijective (H := H))

/-- `none` maps to the zero nilpotent orbit. -/
@[simp]
theorem dominantNeutralElementsEquivNilpotentOrbit_none
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    (b.dominantNeutralElementsEquivNilpotentOrbit (H := H) none :
        Comodule.VectorOrbit k H 𝔤) = Comodule.VectorOrbit.mk 0 := by
  simp [dominantNeutralElementsEquivNilpotentOrbit, optionDominantToNilpotentOrbit]

/-- `some h` maps to the nilpotent orbit of any nilpositive partner `e` of `(h : 𝔤)`. -/
theorem dominantNeutralElementsEquivNilpotentOrbit_some_of_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements) {e f : 𝔤}
    (t : IsSl2Triple (h : 𝔤) e f) :
    (b.dominantNeutralElementsEquivNilpotentOrbit (H := H) (some h) :
        Comodule.VectorOrbit k H 𝔤) = Comodule.VectorOrbit.mk e := by
  simpa [dominantNeutralElementsEquivNilpotentOrbit, optionDominantToNilpotentOrbit] using
    TauCeti.dominantNilpotentOrbit_eq_mk_of_isSl2Triple (H := H) b h t

/-- **The weighted Dynkin diagram of a nilpotent orbit.** Sends the zero orbit to `none` and every
nonzero nilpotent orbit to `some` of the `{0, 1, 2}` simple-root labeling of its unique dominant
neutral element. -/
noncomputable def nilpotentOrbitWeightedDynkinDiagram
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (O : {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd}) :
    Option (b.support → Fin 3) :=
  ((b.dominantNeutralElementsEquivNilpotentOrbit (H := H)).symm O).map b.weightedDynkinDiagram

/-- The zero nilpotent orbit has diagram `none`. -/
@[simp]
theorem nilpotentOrbitWeightedDynkinDiagram_mk_zero
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    b.nilpotentOrbitWeightedDynkinDiagram (H := H)
        ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩ = none := by
  have hsymm :
      (b.dominantNeutralElementsEquivNilpotentOrbit (H := H)).symm
        ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩ = none :=
    (b.dominantNeutralElementsEquivNilpotentOrbit (H := H)).symm_apply_eq.mpr
      (Subtype.ext (b.dominantNeutralElementsEquivNilpotentOrbit_none (H := H)).symm)
  simp [nilpotentOrbitWeightedDynkinDiagram, hsymm]

/-- On the orbit of the nilpositive element of a dominant `sl₂` triple `(h, e, f)`, the orbit-level
weighted Dynkin diagram is `some (b.weightedDynkinDiagram ⟨h, hh⟩)`. -/
theorem nilpotentOrbitWeightedDynkinDiagram_mk_of_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h : 𝔥} {e f : 𝔤}
    (t : IsSl2Triple (h : 𝔤) e f) (hh : h ∈ b.dominantNeutralElements) :
    b.nilpotentOrbitWeightedDynkinDiagram (H := H)
        ⟨Comodule.VectorOrbit.mk e,
          Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr (t.isNilpotent_toEnd_e (K := k) (M := 𝔤))⟩ =
      some (b.weightedDynkinDiagram ⟨h, hh⟩) := by
  have hsymm :
      (b.dominantNeutralElementsEquivNilpotentOrbit (H := H)).symm
        ⟨Comodule.VectorOrbit.mk e,
          Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr (t.isNilpotent_toEnd_e (K := k) (M := 𝔤))⟩ =
        some ⟨h, hh⟩ :=
    (b.dominantNeutralElementsEquivNilpotentOrbit (H := H)).symm_apply_eq.mpr
      (Subtype.ext (b.dominantNeutralElementsEquivNilpotentOrbit_some_of_isSl2Triple
        (H := H) ⟨h, hh⟩ t).symm)
  simp [nilpotentOrbitWeightedDynkinDiagram, hsymm]

/-- **Weighted Dynkin diagrams classify nilpotent orbits of a connected group.** -/
theorem nilpotentOrbitWeightedDynkinDiagram_injective
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Injective (b.nilpotentOrbitWeightedDynkinDiagram (H := H)) := by
  refine Function.Injective.comp ?_
    (b.dominantNeutralElementsEquivNilpotentOrbit (H := H)).symm.injective
  rintro (_ | h₁) (_ | h₂) h <;> simp_all [b.weightedDynkinDiagram_injective.eq_iff]

end RootPairing.Base

namespace TauCeti.Comodule.VectorOrbit

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Nilpotent orbits are downward closed in the closure order.** For a connected affine group
over an algebraically closed field of characteristic zero with Killing Lie algebra, any orbit in the
closure of a nilpotent orbit is again nilpotent. -/
theorem IsNilpotentAd.of_le {O O' : VectorOrbit k H 𝔤} (hle : O' ≤ O)
    (hO : O.IsNilpotentAd) : O'.IsNilpotentAd := by
  induction O using VectorOrbit.ind with | h x =>
  induction O' using VectorOrbit.ind with | h y =>
  rw [isNilpotentAd_mk_iff,
    ← nilpotentConeIdeal_le_ker_lift_eval_iff (H := FiniteTypeCommHopfAlgCat.of k H)] at hO ⊢
  exact nilpotentConeIdeal_le_ker_lift_eval_of_mk_le_mk hle hO

/-- **A nilpotent orbit closure contains only finitely many orbits.** -/
theorem finite_setOf_le_of_isNilpotentAd {O : VectorOrbit k H 𝔤} (hO : O.IsNilpotentAd) :
    {O' : VectorOrbit k H 𝔤 | O' ≤ O}.Finite :=
  finite_setOf_isNilpotentAd.subset fun _ hle ↦ hO.of_le hle

/-- **A nilpotent orbit boundary contains only finitely many orbits.** -/
theorem finite_setOf_lt_of_isNilpotentAd {O : VectorOrbit k H 𝔤} (hO : O.IsNilpotentAd) :
    {O' : VectorOrbit k H 𝔤 | O' < O}.Finite :=
  (finite_setOf_le_of_isNilpotentAd hO).subset fun (_ : VectorOrbit k H 𝔤) (hlt : _ < O) ↦
    hlt.le

/-- **Orbit-closure decomposition for nilpotent orbits.** The vectors of `𝔤` whose orbit lies in the
closure of a nilpotent orbit `O` decompose into `O` together with the finite union of all strictly
smaller nilpotent orbits. -/
theorem setOf_mk_le_eq_union_biUnion_of_isNilpotentAd {O : VectorOrbit k H 𝔤}
    (hO : O.IsNilpotentAd) :
    {y : 𝔤 | (mk y : VectorOrbit k H 𝔤) ≤ O} =
      {y : 𝔤 | mk y = O} ∪
        ⋃ O' ∈ {O' : VectorOrbit k H 𝔤 | O'.IsNilpotentAd ∧ O' < O},
          {y : 𝔤 | mk y = O'} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, exists_prop]
  refine ⟨fun hle ↦ ?_, ?_⟩
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨mk y, ⟨hO.of_le hle, hlt⟩, rfl⟩
  · rintro (rfl | ⟨_, ⟨-, hlt⟩, rfl⟩)
    · exact le_rfl
    · exact hlt.le

end TauCeti.Comodule.VectorOrbit

end Connected
