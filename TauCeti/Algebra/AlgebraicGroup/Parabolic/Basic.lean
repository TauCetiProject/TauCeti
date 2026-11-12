/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugacy.Existence
import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
import TauCeti.Algebra.AlgebraicGroup.Smooth.BaseChange

/-!
# Parabolic subgroups in Hopf coordinates

A closed subgroup `P` of an affine group `G` of finite type over a field `k` is **parabolic** when
it is smooth and its base change to an algebraic closure contains a Borel subgroup of the
geometric fibre. For smooth `G` this is the classical characterization of the smooth closed
subgroups `P` for which `G/P` is proper, and it is the notion of parabolic `k`-subgroup used in
the structure theory of reductive groups over arbitrary fields. Containment of a Borel subgroup
is taken as the definition because it is stated purely in terms of closed subgroups, without a
represented quotient `G/P`.

Smoothness is imposed explicitly: in positive characteristic a closed subgroup scheme containing
a Borel subgroup need not be reduced. As for Borel subgroups, Hopf ideals reverse inclusion, so
the subgroup cut out by `I` contains the Borel subgroup cut out by `J` exactly when `I ≤ J`.

Over an algebraically closed field, conjugacy of Borel subgroups shows that every parabolic
subgroup is conjugate to one containing a prescribed Borel subgroup. The parabolic subgroups are
therefore exactly the smooth closed subgroups having a conjugate that contains that Borel.

## Main declarations

* `TauCeti.HopfIdeal.IsParabolicOverAlgClosed`: the parabolic-subgroup predicate over an
  algebraically closed field.
* `TauCeti.HopfIdeal.IsBorelOverAlgClosed.isParabolicOverAlgClosed`: Borel subgroups are
  parabolic.
* `TauCeti.HopfIdeal.IsParabolicOverAlgClosed.of_le`: a smooth closed subgroup containing a
  parabolic subgroup is parabolic.
* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_bot_iff`: the whole group is parabolic in itself
  exactly when it is smooth.
* `TauCeti.HopfIdeal.IsParabolicOverAlgClosed.comapOfIso_iff`: parabolicity is invariant under
  an ambient Hopf-algebra isomorphism.
* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_conjugate_iff`: parabolicity is invariant under
  conjugation by a rational point.
* `TauCeti.HopfIdeal.IsParabolicOverAlgClosed.exists_conjugate_le` and
  `TauCeti.HopfIdeal.isParabolicOverAlgClosed_iff_exists_conjugate_le`: every parabolic subgroup
  has a conjugate containing a prescribed Borel subgroup, and this characterizes parabolics among
  smooth closed subgroups.
* `TauCeti.HopfIdeal.IsParabolic`: the parabolic-subgroup predicate over an arbitrary field,
  tested after base change to an algebraic closure.
* `TauCeti.HopfIdeal.isParabolic_iff`: a closed subgroup is parabolic exactly when it is smooth
  over the base field and its base change to an algebraic closure contains a Borel subgroup.
* `TauCeti.HopfIdeal.IsBorel.isParabolic`, `TauCeti.HopfIdeal.IsParabolic.smooth`,
  `TauCeti.HopfIdeal.IsParabolic.exists_le_isBorelOverAlgClosed`,
  `TauCeti.HopfIdeal.IsParabolic.of_le`, `TauCeti.HopfIdeal.isParabolic_bot_iff`,
  `TauCeti.HopfIdeal.IsParabolic.comapOfIso_iff` and
  `TauCeti.HopfIdeal.isParabolic_conjugate_iff`: the corresponding statements over an arbitrary
  field.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.2.
* J. S. Milne, *Algebraic Groups* (2017), §17.c.
* B. Conrad, *Reductive Group Schemes* (2014), §5.2.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

universe u v

/-- Over an algebraically closed field, a Hopf ideal defines a **parabolic subgroup** when its
quotient coordinate algebra is smooth and the closed subgroup it cuts out contains a Borel
subgroup. In the contravariant Hopf-ideal order, containing the Borel subgroup cut out by `J` is
the inequality `I ≤ J`. -/
def IsParabolicOverAlgClosed (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, v} k) (I : HopfIdeal k H) : Prop :=
  IsAlgClosed k ∧ smoothCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I).obj ∧
    ∃ J : HopfIdeal k H, IsBorelOverAlgClosed k H J ∧ I ≤ J

/-- The algebraically-closed-field parabolic condition asserts algebraic closedness, smoothness,
and containment of a Borel subgroup. -/
@[simp]
theorem isParabolicOverAlgClosed_iff (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, v} k) (I : HopfIdeal k H) :
    IsParabolicOverAlgClosed k H I ↔
      IsAlgClosed k ∧ smoothCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I).obj ∧
        ∃ J : HopfIdeal k H, IsBorelOverAlgClosed k H J ∧ I ≤ J :=
  Iff.rfl

namespace IsParabolicOverAlgClosed

variable {k : Type u} [Field k]
variable {H L : FiniteTypeCommHopfAlgCat.{u, v} k} {I : HopfIdeal k H}

/-- The base field of a parabolic subgroup in the algebraically closed formulation is
algebraically closed. -/
theorem isAlgClosed (hI : IsParabolicOverAlgClosed k H I) : IsAlgClosed k :=
  hI.1

/-- A parabolic subgroup is smooth. -/
theorem smooth (hI : IsParabolicOverAlgClosed k H I) :
    smoothCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I).obj :=
  hI.2.1

/-- A parabolic subgroup contains a Borel subgroup. -/
theorem exists_le_isBorelOverAlgClosed (hI : IsParabolicOverAlgClosed k H I) :
    ∃ J : HopfIdeal k H, IsBorelOverAlgClosed k H J ∧ I ≤ J :=
  hI.2.2

/-- A smooth closed subgroup containing a parabolic subgroup is parabolic. -/
theorem of_le (hI : IsParabolicOverAlgClosed k H I) {J : HopfIdeal k H} (hJI : J ≤ I)
    (hJ : smoothCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H J).obj) :
    IsParabolicOverAlgClosed k H J := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_le_isBorelOverAlgClosed
  exact ⟨hI.isAlgClosed, hJ, B, hB, hJI.trans hIB⟩

/-- Pulling a parabolic subgroup back across an ambient Hopf-algebra isomorphism gives a
parabolic subgroup in the source. -/
theorem comapOfIso {J : HopfIdeal k L} (hJ : IsParabolicOverAlgClosed k L J) (e : H ≅ L) :
    IsParabolicOverAlgClosed k H
      (J.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  obtain ⟨B, hB, hJB⟩ := hJ.exists_le_isBorelOverAlgClosed
  refine ⟨hJ.isAlgClosed, ?_, _, hB.comapOfIso e, comapOfSurjective_mono _ _ hJB⟩
  exact (smoothCommHopfAlgProperty k).prop_of_iso
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k) (_root_.CommHopfAlgCat.{v} k)).mapIso
      (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e J)).symm hJ.smooth

open FiniteTypeCommHopfAlgCat in
/-- Over an algebraically closed field, parabolicity is invariant under pulling the defining
ideal back across an ambient Hopf-algebra isomorphism. -/
theorem comapOfIso_iff (e : H ≅ L) (J : HopfIdeal k L) :
    IsParabolicOverAlgClosed k H
        (J.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
          (ConcreteCategory.bijective_of_isIso e.hom).2) ↔
      IsParabolicOverAlgClosed k L J := by
  constructor
  · intro hJ
    simpa only [HopfIdeal.comapOfSurjective_comapOfSurjective, ← toBialgHom_comp,
      Iso.symm_hom, e.inv_hom_id, toBialgHom_id, HopfIdeal.comapOfSurjective_id]
      using hJ.comapOfIso e.symm
  · exact fun hJ ↦ hJ.comapOfIso e

end IsParabolicOverAlgClosed

/-- Over an algebraically closed field, a Borel subgroup is parabolic. -/
theorem IsBorelOverAlgClosed.isParabolicOverAlgClosed {k : Type u} [Field k]
    {H : FiniteTypeCommHopfAlgCat.{u, v} k} {I : HopfIdeal k H}
    (hI : IsBorelOverAlgClosed k H I) : IsParabolicOverAlgClosed k H I :=
  have hI' := (isBorelOverAlgClosed_iff k H I).mp hI
  ⟨hI'.1, hI'.2.prop.smooth, I, hI, le_rfl⟩

/-- Over an algebraically closed field, the whole group is a parabolic subgroup of itself exactly
when it is smooth. The whole group is cut out by the zero Hopf ideal.

This is not a `simp` lemma: `isParabolicOverAlgClosed_iff` unfolds `IsParabolicOverAlgClosed` on
the left-hand side, so the statement is never in `simp`-normal form. -/
theorem isParabolicOverAlgClosed_bot_iff {k : Type u} [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsParabolicOverAlgClosed k H ⊥ ↔ IsAlgClosed k ∧ smoothCommHopfAlgProperty k H.obj := by
  let e := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k) (_root_.CommHopfAlgCat.{u} k)).mapIso
    (FiniteTypeCommHopfAlgCat.quotientBotIso H)
  constructor
  · intro h
    exact ⟨h.isAlgClosed, (smoothCommHopfAlgProperty k).prop_of_iso e h.smooth⟩
  · rintro ⟨hk, hH⟩
    obtain ⟨B, hB⟩ := exists_minimal_isBorelCandidate H
    exact ⟨hk, (smoothCommHopfAlgProperty k).prop_of_iso e.symm hH, B,
      (isBorelOverAlgClosed_iff k H B).mpr ⟨hk, hB⟩, bot_le⟩

section Conjugation

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- Over an algebraically closed field, the conjugate of a parabolic subgroup by a rational point
is parabolic. -/
theorem IsParabolicOverAlgClosed.conjugate {I : HopfIdeal k H}
    (hI : IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I)
    (g : WithConv (H →ₐ[k] k)) :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) (I.conjugate g) := by
  have h := hI.comapOfIso (HopfAlgebra.pointConjugationFiniteTypeIso g)
  rw [conjugate_eq_comapOfSurjective]
  simpa only [HopfAlgebra.pointConjugationFiniteTypeIso_hom] using h

/-- The algebraically closed parabolic property is invariant under conjugation by a rational
point.

This is not a `simp` lemma: `isParabolicOverAlgClosed_iff` unfolds `IsParabolicOverAlgClosed` on
the left-hand side, so the statement is never in `simp`-normal form. -/
theorem isParabolicOverAlgClosed_conjugate_iff (I : HopfIdeal k H)
    (g : WithConv (H →ₐ[k] k)) :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) (I.conjugate g) ↔
      IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I := by
  constructor
  · intro hI
    simpa using hI.conjugate g⁻¹
  · exact fun hI ↦ hI.conjugate g

end Conjugation

section StandardParabolic

variable {k : Type u} [Field k]
variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- **Every parabolic subgroup has a conjugate containing a prescribed Borel subgroup.** Over an
algebraically closed field, if `I` cuts out a parabolic subgroup and `J` a Borel subgroup, some
rational point conjugates the parabolic to a subgroup containing the Borel. -/
theorem IsParabolicOverAlgClosed.exists_conjugate_le {I J : HopfIdeal k H}
    (hI : IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I)
    (hJ : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) J) :
    ∃ g : WithConv (H →ₐ[k] k), I.conjugate g ≤ J := by
  have := hI.isAlgClosed
  obtain ⟨B, hB, hIB⟩ := hI.exists_le_isBorelOverAlgClosed
  obtain ⟨g, rfl⟩ := hB.exists_conjugate_eq hJ
  exact ⟨g, conjugate_mono g hIB⟩

/-- **Parabolic subgroups relative to a fixed Borel subgroup.** Over an algebraically closed
field, a closed subgroup is parabolic exactly when it is smooth and one of its conjugates by a
rational point contains the prescribed Borel subgroup. -/
theorem isParabolicOverAlgClosed_iff_exists_conjugate_le {I J : HopfIdeal k H}
    (hJ : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) J) :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I ↔
      smoothCommHopfAlgProperty k
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I).obj ∧
        ∃ g : WithConv (H →ₐ[k] k), I.conjugate g ≤ J := by
  refine ⟨fun hI ↦ ⟨hI.smooth, hI.exists_conjugate_le hJ⟩, ?_⟩
  rintro ⟨hsmooth, g, hg⟩
  refine ⟨((isBorelOverAlgClosed_iff _ _ _).mp hJ).1, hsmooth, J.conjugate g⁻¹,
    hJ.conjugate g⁻¹, ?_⟩
  simpa using conjugate_mono g⁻¹ hg

end StandardParabolic

/-- A Hopf ideal defines a **parabolic subgroup** when its base change to an algebraic closure
defines a smooth closed subgroup of the geometric fibre containing a Borel subgroup.

The order is contravariant: `I ≤ J` says that the subgroup cut out by `I` contains the subgroup
cut out by `J`. -/
def IsParabolic (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{v} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) : Prop :=
  let K := AlgebraicClosure k
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K)
    ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
  let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  IsParabolicOverAlgClosed K H' I'

/-- The general-field parabolic predicate is the algebraically-closed-field parabolic predicate
after base change to an algebraic closure. -/
theorem isParabolic_iff_isParabolicOverAlgClosed_baseChange
    (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{v} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) :
    let K := AlgebraicClosure k
    let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K)
      ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
    let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
    IsParabolic k H I ↔ IsParabolicOverAlgClosed K H' I' :=
  Iff.rfl

/-- A Borel subgroup over an arbitrary field is parabolic. -/
theorem IsBorel.isParabolic {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}
    [Algebra.FiniteType k H] {I : HopfIdeal k H} (hI : IsBorel k H I) : IsParabolic k H I :=
  (isParabolic_iff_isParabolicOverAlgClosed_baseChange k H I).mpr
    (IsBorelOverAlgClosed.isParabolicOverAlgClosed
      ((isBorel_iff_isBorelOverAlgClosed_baseChange k H I).mp hI))

namespace IsParabolic

variable {k : Type u} [Field k]

/-- Pulling a parabolic subgroup back across an ambient Hopf-algebra isomorphism gives a
parabolic subgroup in the source. -/
theorem comapOfIso {H L : FiniteTypeCommHopfAlgCat.{u, v} k} {I : HopfIdeal k L.obj}
    (hI : IsParabolic k L.obj I) (e : H ≅ L) :
    IsParabolic k H.obj
      (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  let eK := (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).mapIso e
  have hbaseChange :
      CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k)
          (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
            (ConcreteCategory.bijective_of_isIso e.hom).2) =
        (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I).comapOfSurjective
          (FiniteTypeCommHopfAlgCat.toBialgHom eK.hom)
          (ConcreteCategory.bijective_of_isIso eK.hom).2 :=
    CommHopfAlgCat.baseChangeHopfIdeal_comapOfIso (K := AlgebraicClosure k) I
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k)
        (_root_.CommHopfAlgCat.{v} k)).mapIso e)
  -- `IsParabolic k L.obj I` base-changes the bundled object `⟨L.obj, _⟩`, which is `L` by
  -- structure eta, so it is the algebraically closed predicate for the base change of `L`.
  have h := IsParabolicOverAlgClosed.comapOfIso
    ((isParabolic_iff_isParabolicOverAlgClosed_baseChange k L.obj I).mp hI) eK
  rw [← hbaseChange] at h
  exact (isParabolic_iff_isParabolicOverAlgClosed_baseChange k H.obj _).mpr h

open FiniteTypeCommHopfAlgCat in
/-- Parabolicity is invariant under pulling the defining ideal back across an ambient
Hopf-algebra isomorphism. -/
theorem comapOfIso_iff {H L : FiniteTypeCommHopfAlgCat.{u, v} k} (e : H ≅ L)
    (I : HopfIdeal k L.obj) :
    IsParabolic k H.obj
        (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
          (ConcreteCategory.bijective_of_isIso e.hom).2) ↔
      IsParabolic k L.obj I := by
  constructor
  · intro hI
    simpa only [HopfIdeal.comapOfSurjective_comapOfSurjective, ← toBialgHom_comp,
      Iso.symm_hom, e.inv_hom_id, toBialgHom_id, HopfIdeal.comapOfSurjective_id]
      using hI.comapOfIso e.symm
  · exact fun hI ↦ hI.comapOfIso e

variable {H : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k H] {I : HopfIdeal k H}

/-- A parabolic subgroup over an arbitrary field is smooth over that field. Smoothness of its
geometric fibre descends along the faithfully flat extension to an algebraic closure. -/
theorem smooth (hI : IsParabolic k H I) :
    smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H I) :=
  -- `FiniteTypeCommHopfAlgCat.quotient` and `FiniteTypeCommHopfAlgCat.baseChange` are
  -- abbreviations bundling the `CommHopfAlgCat` constructions, so the `.obj` of the finite-type
  -- quotient is the `CommHopfAlgCat` quotient of the base change.
  (smoothCommHopfAlgProperty_quotient_baseChange_iff (K := AlgebraicClosure k) I).mp
    ((isParabolic_iff_isParabolicOverAlgClosed_baseChange k H I).mp hI).smooth

/-- The base change of a parabolic subgroup to an algebraic closure contains a Borel subgroup of
the geometric fibre. -/
theorem exists_le_isBorelOverAlgClosed (hI : IsParabolic k H I) :
    ∃ J : HopfIdeal (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩).obj,
      IsBorelOverAlgClosed (AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
            ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩) J ∧
        CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I ≤ J :=
  ((isParabolic_iff_isParabolicOverAlgClosed_baseChange k H I).mp
    hI).exists_le_isBorelOverAlgClosed

/-- A closed subgroup that is smooth over the base field and contains a parabolic subgroup is
parabolic. -/
theorem of_le (hI : IsParabolic k H I) {J : HopfIdeal k H} (hJI : J ≤ I)
    (hJ : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H J)) :
    IsParabolic k H J :=
  -- As in `IsParabolic.smooth`, the finite-type quotient of the base change unfolds to the
  -- `CommHopfAlgCat` quotient by abbreviation.
  (isParabolic_iff_isParabolicOverAlgClosed_baseChange k H J).mpr
    (((isParabolic_iff_isParabolicOverAlgClosed_baseChange k H I).mp hI).of_le
      (CommHopfAlgCat.baseChangeHopfIdeal_mono hJI)
      ((smoothCommHopfAlgProperty_quotient_baseChange_iff (K := AlgebraicClosure k) J).mpr hJ))

end IsParabolic

/-- The Hopf-ideal criterion for a parabolic subgroup: it is smooth over the base field, and its
base change to an algebraic closure contains a Borel subgroup of the geometric fibre. -/
@[simp]
theorem isParabolic_iff (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{v} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) :
    let K := AlgebraicClosure k
    let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K)
      ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
    let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
    IsParabolic k H I ↔
      smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H I) ∧
        ∃ J : HopfIdeal K H'.obj, IsBorelOverAlgClosed K H' J ∧ I' ≤ J := by
  refine ⟨fun hI ↦ ⟨hI.smooth, hI.exists_le_isBorelOverAlgClosed⟩, ?_⟩
  rintro ⟨hsmooth, J, hJ, hIJ⟩
  -- As in `IsParabolic.smooth`, the finite-type quotient of the base change unfolds to the
  -- `CommHopfAlgCat` quotient by abbreviation.
  exact (isParabolic_iff_isParabolicOverAlgClosed_baseChange k H I).mpr
    ⟨inferInstance,
      (smoothCommHopfAlgProperty_quotient_baseChange_iff (K := AlgebraicClosure k) I).mpr hsmooth,
      J, hJ, hIJ⟩

/-- The whole group is a parabolic subgroup of itself exactly when it is smooth. The whole group
is cut out by the zero Hopf ideal.

This is not a `simp` lemma: `isParabolic_iff` unfolds `IsParabolic` on the left-hand side, so the
statement is never in `simp`-normal form. -/
theorem isParabolic_bot_iff {k : Type u} [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] :
    IsParabolic k H ⊥ ↔ smoothCommHopfAlgProperty k H := by
  constructor
  · intro h
    exact (smoothCommHopfAlgProperty k).prop_of_iso (CommHopfAlgCat.quotientBotIso H) h.smooth
  · intro hH
    let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff _).mp hH
    have h := (isParabolicOverAlgClosed_bot_iff
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩)).mpr
      ⟨inferInstance, (smoothCommHopfAlgProperty_iff _).mpr inferInstance⟩
    rw [← CommHopfAlgCat.baseChangeHopfIdeal_bot (K := AlgebraicClosure k) (H := H)] at h
    exact (isParabolic_iff_isParabolicOverAlgClosed_baseChange k H ⊥).mpr h

section Conjugation

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- The conjugate of a parabolic subgroup by a rational point is parabolic. -/
theorem IsParabolic.conjugate {I : HopfIdeal k H}
    (hI : IsParabolic k (_root_.CommHopfAlgCat.of k H) I) (g : WithConv (H →ₐ[k] k)) :
    IsParabolic k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) := by
  have h := hI.comapOfIso (HopfAlgebra.pointConjugationFiniteTypeIso g)
  rw [conjugate_eq_comapOfSurjective]
  simpa only [HopfAlgebra.pointConjugationFiniteTypeIso_hom] using h

/-- Parabolicity is invariant under conjugation by a rational point.

This is not a `simp` lemma: `isParabolic_iff` unfolds `IsParabolic` on the left-hand side, so the
statement is never in `simp`-normal form. -/
theorem isParabolic_conjugate_iff (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    IsParabolic k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) ↔
      IsParabolic k (_root_.CommHopfAlgCat.of k H) I := by
  constructor
  · intro hI
    simpa using hI.conjugate g⁻¹
  · exact fun hI ↦ hI.conjugate g

end Conjugation

end TauCeti.HopfIdeal
