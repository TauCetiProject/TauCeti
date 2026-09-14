/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Reflection.Acyclic
public import TauCeti.RepresentationTheory.Quiver.Reflection.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Reflection.FullyFaithful
public import TauCeti.RepresentationTheory.Quiver.Reflection.Uniqueness
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic

/-!
# Reflecting the generalized Kronecker quiver at its sink

The generalized Kronecker quiver has a source `src`, a target `tgt`, and one arrow `src ⟶ tgt` for
each element of an arrow type `A`; the `A₂` quiver `• → •` is the case of a one-element `A`. Its
target is a sink, and this file computes the Bernstein--Gelfand--Ponomarev reflection there on the
representations that the `A₂` classification of
`TauCeti.RepresentationTheory.Quiver.Kronecker.Indecomposable` singles out.

Reflecting reverses the single family of arrows, so the reflected quiver is again a generalized
Kronecker quiver, read the other way round: `src` becomes a sink, `tgt` becomes a source, and the
paths `tgt → src` of the reflected quiver are again the elements of `A`.

On representations the reflection does three things:

* it **annihilates the sink simple** `S_tgt`, the one representation concentrated at `tgt`;
* it carries the **projective** `P_src` to the **vertex simple** `S_src` of the reflected quiver;
* it carries the **source simple** `S_src` to an indecomposable representation of dimension vector
  `(1, #A)`, the value at `(1, 0)` of the simple reflection at `tgt`.

For the `A₂` quiver these are the three indecomposables `S_tgt`, `P_src`, `S_src`, of dimension
vectors `(0,1)`, `(1,1)`, `(1,0)`, and the last statement sharpens to an isomorphism with the
projective `P_tgt` of the reflected quiver: reflection kills one indecomposable and exchanges the
other two, realizing the simple reflection at `tgt` on the three positive roots of `A₂`.

## Main definitions

* `TauCeti.Quiver.Kronecker.reflectArrowPath`: the path `tgt → src` of the reflected quiver traced
  by the reversed arrow attached to an element of `A`.
* `TauCeti.Quiver.Kronecker.reflectPathEquivArrow`: the resulting identification of the paths
  `tgt → src` of the reflected quiver with `A`.

## Main results

* `TauCeti.Quiver.Kronecker.isSink_reflect_src`: in the reflected quiver the source vertex is a
  sink, so the reflected quiver is the generalized Kronecker quiver with the opposite orientation.
* `TauCeti.isZero_reflectRep_simpleRep_tgt`: **reflection annihilates the sink simple** `S_tgt`.
* `TauCeti.nonempty_iso_reflectRep_indecProjRep_src`: **reflection carries the projective `P_src`
  to the vertex simple `S_src`** of the reflected quiver.
* `TauCeti.indecomposable_reflectRep_simpleRep_src` and
  `TauCeti.dimVector_reflectRep_simpleRep_src`: **reflection carries the source simple `S_src` to
  an indecomposable representation of dimension vector `(1, #A)`**.
* `TauCeti.nonempty_iso_reflectRep_simpleRep_src_indecProjRep`: over the `A₂` quiver that
  indecomposable is the projective `P_tgt` of the reflected quiver.

## Implementation notes

Nothing below needs the reflection functor on morphisms, only its value `TauCeti.reflectRep` on
objects, so no naturality is checked here.

Two of the three computations go through the general boundary lemmas of
`TauCeti.RepresentationTheory.Quiver.Reflection.Representation`: the sink simple is a
representation concentrated at the sink, which `TauCeti.isZero_reflectRep` annihilates, and the
reflection of `P_src` is concentrated at `src`, so
`TauCeti.nonempty_iso_of_dimVector_eq_of_forall_subsingleton` identifies it with the vertex simple
there with no natural transformation written down. The third is the one that sees the quiver: the
reflection of `S_src` has full support, so it is compared with `P_tgt` through the Gabriel
injection `TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic`, whose
positive-definiteness hypothesis holds for the reflected quiver by `TauCeti.titsForm_reflect` and
confines that last statement to the `A₂` case — as it must, since the Kronecker quiver `• ⇉ •`
carries a whole family of pairwise non-isomorphic indecomposables at the single dimension vector
`(1, 1)`, by `TauCeti.nonempty_kroneckerLineRep_iso_iff`.

A vertex of the reflected quiver has to be written `@IsSink (Reflect (Kronecker A) tgt) _ src`
rather than `IsSink (src : Reflect (Kronecker A) tgt)`: `TauCeti.Quiver.Reflect` is a type synonym
for the vertex type, so the ascription is discharged definitionally and the quiver instance
elaborated from it would be the unreflected one.

The arrow type is taken in `Type`, as in
`TauCeti.RepresentationTheory.Quiver.Kronecker.AlmostSplit`: the vertex spaces of the reflection
are cut out of a product indexed by the arrows, so they live in the maximum of the arrow universe
and the universe of the field, while those of the vertex simple are the field itself.

## References

This supplies the reflection half of the “`A₂` quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, which asks that the
reflection functor at the sink kill the sink simple and realize the simple reflection there on the
dimension vectors of the remaining indecomposables. See Bernstein--Gelfand--Ponomarev, *Coxeter
functors and Gabriel's theorem*, and Derksen--Weyman, *An Introduction to Quiver
Representations*, Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open _root_.Quiver
open _root_.TauCeti.Quiver

universe u

namespace Quiver.Kronecker

variable {A : Type}

/-! ### The reflected quiver -/

/-- **In the reflected quiver the source vertex is a sink.** Reflecting at `tgt` reverses every
arrow, so the generalized Kronecker quiver becomes the same quiver read the other way round. -/
theorem isSink_reflect_src : @IsSink (Reflect (Kronecker A) tgt) _ src :=
  (@IsSink_def (Reflect (Kronecker A) tgt) _ src).mpr fun b ↦ ⟨fun e ↦ by
    cases b with
    | src =>
      exact (isEmpty_hom_to_src (A := A) src).elim
        (cast ((hom_reflect tgt src src).trans
          (reflectHom_of_ne_of_ne src_ne_tgt src_ne_tgt)) e)
    | tgt =>
      exact (isEmpty_hom_to_src (A := A) tgt).elim
        (cast ((hom_reflect tgt src tgt).trans (reflectHom_right tgt src)) e)⟩

/-- In the reflected quiver the target vertex is a source, since it was a sink. -/
theorem isSource_reflect_tgt : @IsSource (Reflect (Kronecker A) tgt) _ tgt :=
  (isSink_tgt (A := A)).isSource_reflect

/-- The only closed path at the source of the reflected quiver is the trivial one. -/
instance : Unique (@Path (Reflect (Kronecker A) tgt) _ src src) where
  default := Path.nil
  uniq := isSink_reflect_src.path_self_eq_nil

/-- The only closed path at the target of the reflected quiver is the trivial one. -/
instance : Unique (@Path (Reflect (Kronecker A) tgt) _ tgt tgt) where
  default := Path.nil
  uniq := isSource_reflect_tgt.path_self_eq_nil

/-- The reflected quiver has no path from the source to the target: its arrows all run the other
way. -/
instance : IsEmpty (@Path (Reflect (Kronecker A) tgt) _ src tgt) :=
  ⟨fun p ↦ src_ne_tgt (isSink_reflect_src.eq_of_path p)⟩

/-- The length-one path of the reflected quiver traced by the reversed arrow attached to an
element of the arrow type. -/
noncomputable def reflectArrowPath (a : A) : @Path (Reflect (Kronecker A) tgt) _ tgt src :=
  (reflectArrow tgt (arrow a)).toPath

/-- The path attached to an element of the arrow type is the one its reversed arrow traces. -/
theorem reflectArrowPath_eq (a : A) :
    reflectArrowPath a = (reflectArrow tgt (arrow a)).toPath :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `reflectArrowPath` to be `@[expose]`.
  (rfl)

/-- Reading a reversed arrow `tgt ⟶ src` of the reflected quiver back as an arrow `src ⟶ tgt` of
the generalized Kronecker quiver. -/
private theorem hom_reflect_tgt_src :
    (@Hom (Reflect (Kronecker A) tgt) _ tgt src) = ((src : Kronecker A) ⟶ tgt) :=
  (hom_reflect tgt tgt src).trans (reflectHom_left tgt src)

/-- Distinct arrows trace distinct paths in the reflected quiver. -/
theorem reflectArrowPath_injective : Function.Injective (reflectArrowPath (A := A)) := by
  intro a b h
  rw [reflectArrowPath_eq, reflectArrowPath_eq] at h
  have h₁ : reflectArrow tgt (arrow a) = reflectArrow tgt (arrow b) := by injection h
  have h₂ := congrArg (cast (hom_reflect_tgt_src (A := A))) h₁
  rw [cast_reflectArrow, cast_reflectArrow] at h₂
  exact arrowPath_injective
    (((toPath_arrow a).symm.trans (congrArg Hom.toPath h₂)).trans (toPath_arrow b))

/-- **Every path from the target to the source of the reflected quiver is a single reversed
arrow**: the target is a source there and the source is a sink, so no two arrows compose. -/
theorem reflectArrowPath_surjective : Function.Surjective (reflectArrowPath (A := A)) := by
  intro p
  cases p with
  | @cons b _ q e =>
    cases b with
    | src => exact (isSink_reflect_src.isEmpty_hom _).elim e
    | tgt =>
      obtain ⟨a, ha⟩ := arrowPath_surjective (cast (hom_reflect_tgt_src (A := A)) e).toPath
      refine ⟨a, ?_⟩
      have h₁ : (arrow a).toPath = (cast (hom_reflect_tgt_src (A := A)) e).toPath :=
        (toPath_arrow a).trans ha
      have h₂ : arrow a = cast (hom_reflect_tgt_src (A := A)) e := by injection h₁
      rw [reflectArrowPath_eq, isSource_reflect_tgt.path_self_eq_nil q, h₂,
        reflectArrow_cast]
      rfl

/-- **The paths `tgt → src` of the reflected quiver are the elements of the arrow type**, exactly
as the paths `src → tgt` of the generalized Kronecker quiver are, by
`TauCeti.Quiver.Kronecker.pathEquivArrow`. -/
noncomputable def reflectPathEquivArrow : @Path (Reflect (Kronecker A) tgt) _ tgt src ≃ A :=
  (Equiv.ofBijective reflectArrowPath
    ⟨reflectArrowPath_injective, reflectArrowPath_surjective⟩).symm

/-- The inverse of the classification sends an element of the arrow type to the path its reversed
arrow traces; the two are the same construction, so this holds definitionally. -/
@[simp]
theorem reflectPathEquivArrow_symm_apply (a : A) :
    reflectPathEquivArrow.symm a = reflectArrowPath a :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `reflectPathEquivArrow` to be `@[expose]`; the three lemmas here are the whole
  -- interface.
  (rfl)

/-- The classification sends the path traced by a reversed arrow back to the element of the arrow
type it came from. -/
@[simp]
theorem reflectPathEquivArrow_reflectArrowPath (a : A) :
    reflectPathEquivArrow (reflectArrowPath a) = a := by
  rw [← reflectPathEquivArrow_symm_apply, Equiv.apply_symm_apply]

/-- Every path from the target to the source of the reflected quiver is traced by the reversed
arrow it classifies. -/
@[simp]
theorem reflectArrowPath_reflectPathEquivArrow (p : @Path (Reflect (Kronecker A) tgt) _ tgt src) :
    reflectArrowPath (reflectPathEquivArrow p) = p := by
  rw [← reflectPathEquivArrow_symm_apply, Equiv.symm_apply_apply]

/-- The reflected quiver has as many paths `tgt → src` as the generalized Kronecker quiver has
arrows. -/
theorem card_path_reflect_tgt_src :
    Nat.card (@Path (Reflect (Kronecker A) tgt) _ tgt src) = Nat.card A :=
  Nat.card_congr reflectPathEquivArrow

end Quiver.Kronecker

/-! ### Reflecting the indecomposables -/

open Quiver.Kronecker

variable {k : Type u} [Field k] {A : Type} [Fintype A]

/-- **Reflection annihilates the sink simple.** The vertex simple `S_tgt` is concentrated at the
sink, the one boundary case in which `TauCeti.incomingSum` fails to be onto and reflection
therefore does not act by the simple reflection on dimension vectors. -/
theorem isZero_reflectRep_simpleRep_tgt :
    IsZero (reflectRep (simpleRep k (Kronecker A) tgt) isSink_tgt) :=
  isZero_reflectRep _ isSink_tgt fun _ ha ↦
    ModuleCat.subsingleton_of_isZero (isZero_simpleRep_obj ha)

/-! #### The vertex simple at the source -/

/-- The sum of the arrows into the sink is onto for the source simple, whose target space is zero.
This is the hypothesis under which reflection acts by the simple reflection on dimension vectors,
and it is what distinguishes `S_src` from `S_tgt`. -/
theorem surjective_incomingSum_simpleRep_src :
    Function.Surjective (incomingSum (simpleRep k (Kronecker A) src) tgt) := by
  have : Subsingleton ((simpleRep k (Kronecker A) src).obj tgt) :=
    ModuleCat.subsingleton_of_isZero (isZero_simpleRep_obj src_ne_tgt.symm)
  exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

/-- **Reflection carries the source simple to an indecomposable representation** of the reflected
quiver. -/
theorem indecomposable_reflectRep_simpleRep_src :
    Indecomposable (reflectRep (simpleRep k (Kronecker A) src) isSink_tgt) :=
  indecomposable_reflectRep isSink_tgt (indecomposable_of_simple _)
    surjective_incomingSum_simpleRep_src

/-- **The dimension vector of the reflection of the source simple is `(1, #A)`**, the simple
reflection at `tgt` applied to the dimension vector `(1, 0)` of `S_src`. -/
theorem dimVector_reflectRep_simpleRep_src :
    dimVector (reflectRep (simpleRep k (Kronecker A) src) isSink_tgt)
      = fun j ↦ if j = src then 1 else Fintype.card A := by
  have hsrc : dimVector (reflectRep (simpleRep k (Kronecker A) src) isSink_tgt) src = 1 := by
    rw [dimVector_reflectRep_of_ne _ isSink_tgt src_ne_tgt, dimVector_simpleRep,
      Pi.single_eq_same]
  have htgt : dimVector (reflectRep (simpleRep k (Kronecker A) src) isSink_tgt) tgt
      = Fintype.card A := by
    have h := dimVector_reflectRep_self_add (simpleRep k (Kronecker A) src) isSink_tgt
      (fun e ↦ finiteDimensional_simpleRep_obj src e.1) surjective_incomingSum_simpleRep_src
    rw [dimVector_simpleRep, sum_univ] at h
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne src_ne_tgt.symm, card_hom_src_tgt,
      Fintype.card_eq_zero, mul_one, Nat.mul_zero, Nat.add_zero] at h
    omega
  funext j
  cases j with
  | src => simpa using hsrc
  | tgt => simpa [src_ne_tgt.symm] using htgt

/-! #### The projective at the source -/

/-- The sum of the arrows into the sink is onto for the projective `P_src`: the basis vector of a
path `src → tgt` is the image, under the arrow that path traces, of the basis vector of the
trivial path. -/
theorem surjective_incomingSum_indecProjRep_src :
    Function.Surjective (incomingSum (indecProjRep k (Kronecker A) src) tgt) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (indecProjRepBasis k src tgt).span_eq,
    Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  obtain ⟨a, rfl⟩ := arrowPath_surjective p
  have h := map_toPath_mem_range_incomingSum (indecProjRep k (Kronecker A) src) (arrow a)
    (indecProjRepBasis k src src Path.nil)
  rwa [show ((indecProjRep k (Kronecker A) src).map (arrow a).toPath).hom
      (indecProjRepBasis k src src Path.nil)
      = indecProjRepBasis k src tgt (arrowPath a) from
    (indecProjRep_map_basis src (arrow a).toPath Path.nil).trans
      (by rw [Path.nil_comp, toPath_arrow])] at h

/-- **The reflection of the projective `P_src` vanishes at the sink**: the sum of the arrows into
the sink is onto there, and it has as many paths `src → tgt` in its target as it has arrows in its
source. -/
theorem subsingleton_reflectRep_indecProjRep_obj_tgt :
    Subsingleton ((reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt).obj tgt) := by
  have hfd : FiniteDimensional k
      ((reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt).obj tgt) :=
    finiteDimensional_reflectRep_obj _ isSink_tgt (fun a ↦ by cases a <;> infer_instance) tgt
  have h := dimVector_reflectRep_self_add (indecProjRep k (Kronecker A) src) isSink_tgt
    (fun e ↦ by cases e.1 <;> infer_instance) surjective_incomingSum_indecProjRep_src
  have hA : Nat.card (Path (src : Kronecker A) tgt) = Fintype.card A := by
    rw [Nat.card_eq_fintype_card, card_path_src_tgt]
  rw [sum_univ] at h
  simp only [dimVector_indecProjRep, hA, Nat.card_unique, card_hom_src_tgt, Fintype.card_eq_zero,
    mul_one, Nat.zero_mul, Nat.add_zero] at h
  have h0 : dimVector (reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt) tgt = 0 := by
    omega
  have h1 : Module.finrank k
      ((reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt).obj tgt) = 0 :=
    (dimVector_apply (reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt) tgt).symm.trans h0
  exact Module.finrank_zero_iff.mp h1

/-- **Reflection carries the projective at the source to the vertex simple at the source** of the
reflected quiver. Both are concentrated at `src`, which is a sink there, and both are a line at
that vertex. -/
theorem nonempty_iso_reflectRep_indecProjRep_src :
    Nonempty (reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt
      ≅ simpleRep k (Reflect (Kronecker A) tgt) src) := by
  have hsrc : dimVector (reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt) src = 1 := by
    rw [dimVector_reflectRep_of_ne _ isSink_tgt src_ne_tgt, dimVector_indecProjRep,
      Nat.card_unique]
  have hss : Subsingleton ((reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt).obj
      ((Paths.of (Reflect (Kronecker A) tgt)).obj tgt)) :=
    subsingleton_reflectRep_indecProjRep_obj_tgt
  have htgt : dimVector (reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt) tgt = 0 := by
    refine (dimVector_apply (reflectRep (indecProjRep k (Kronecker A) src) isSink_tgt) tgt).trans ?_
    exact Module.finrank_zero_of_subsingleton
  refine nonempty_iso_of_dimVector_eq_of_forall_subsingleton isSink_reflect_src
    (fun a ha ↦ ?_) ?_
    (isFinDim_iff.mpr fun a ↦
      finiteDimensional_simpleRep_obj (k := k) (Q := Reflect (Kronecker A) tgt) src a) ?_
  · cases a with
    | src => exact absurd rfl ha
    | tgt => exact subsingleton_reflectRep_indecProjRep_obj_tgt
  · exact finiteDimensional_reflectRep_obj _ isSink_tgt
      (fun a ↦ by cases a <;> infer_instance) src
  · have hs1 : dimVector (simpleRep k (Reflect (Kronecker A) tgt) src) src = 1 := by
      refine (dimVector_apply (simpleRep k (Reflect (Kronecker A) tgt) src) src).trans ?_
      refine (congrArg (fun X : ModuleCat.{u} k ↦ Module.finrank k X)
        (simpleRep_obj_self (k := k) (Q := Reflect (Kronecker A) tgt) src)).trans ?_
      exact Module.finrank_self k
    have hzero : Subsingleton ((simpleRep k (Reflect (Kronecker A) tgt) src).obj
        ((Paths.of (Reflect (Kronecker A) tgt)).obj tgt)) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_simpleRep_obj (k := k) (Q := Reflect (Kronecker A) tgt) src_ne_tgt.symm)
    have hs0 : dimVector (simpleRep k (Reflect (Kronecker A) tgt) src) tgt = 0 := by
      refine (dimVector_apply (simpleRep k (Reflect (Kronecker A) tgt) src) tgt).trans ?_
      exact Module.finrank_zero_of_subsingleton
    funext j
    cases j with
    | src => exact hsrc.trans hs1.symm
    | tgt => exact htgt.trans hs0.symm

/-! #### The `A₂` quiver -/

section A2

variable [Unique A]

/-- Over the `A₂` quiver the reflected quiver has positive definite Tits form: reflecting changes
the orientation of a quiver, not its underlying graph. -/
theorem titsForm_reflect_kronecker_posDef :
    (titsForm (Reflect (Kronecker A) tgt)).PosDef := by
  intro d hd
  exact lt_of_lt_of_eq (titsForm_posDef (A := A) (le_of_eq Fintype.card_unique) d hd)
    (titsForm_reflect (V := Kronecker A) tgt d).symm

/-- **Over the `A₂` quiver reflection carries the source simple to the projective at the target**
of the reflected quiver. Both are indecomposable of dimension vector `(1, 1)`, and over a quiver
with positive definite Tits form the dimension vector of an indecomposable determines it.

Together with `TauCeti.isZero_reflectRep_simpleRep_tgt` and
`TauCeti.nonempty_iso_reflectRep_indecProjRep_src` this is the whole action of the reflection at
the sink on the three indecomposables of the `A₂` quiver: it annihilates `S_tgt` and exchanges
`S_src` with `P_src`, realizing the simple reflection at `tgt` on the three positive roots. -/
theorem nonempty_iso_reflectRep_simpleRep_src_indecProjRep :
    Nonempty (reflectRep (simpleRep k (Kronecker A) src) isSink_tgt
      ≅ indecProjRep k (Reflect (Kronecker A) tgt) tgt) := by
  have hfinS : Finite (@Path (Reflect (Kronecker A) tgt) _ tgt src) :=
    Finite.of_equiv _ reflectPathEquivArrow.symm
  have hsubT : Subsingleton (@Path (Reflect (Kronecker A) tgt) _ tgt tgt) :=
    ⟨fun p q ↦ (isSource_reflect_tgt.path_self_eq_nil p).trans
      (isSource_reflect_tgt.path_self_eq_nil q).symm⟩
  have hfinT : Finite (@Path (Reflect (Kronecker A) tgt) _ tgt tgt) := Finite.of_subsingleton
  have hfdM : IsFinDim k (Reflect (Kronecker A) tgt)
      (reflectRep (simpleRep k (Kronecker A) src) isSink_tgt) :=
    isFinDim_iff.mpr fun a ↦
      finiteDimensional_reflectRep_obj _ isSink_tgt (fun _ ↦ inferInstance) a
  have hfdN : IsFinDim k (Reflect (Kronecker A) tgt)
      (indecProjRep k (Reflect (Kronecker A) tgt) tgt) :=
    isFinDim_iff.mpr fun a ↦ by
      cases a with
      | src =>
        exact finiteDimensional_indecProjRep_obj (k := k) (Q := Reflect (Kronecker A) tgt) tgt src
      | tgt =>
        exact finiteDimensional_indecProjRep_obj (k := k) (Q := Reflect (Kronecker A) tgt) tgt tgt
  refine nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic
    (IsAcyclic.reflect_of_isSink isAcyclic isSink_tgt) titsForm_reflect_kronecker_posDef _ _
    indecomposable_reflectRep_simpleRep_src
    (indecomposable_indecProjRep_of_isAcyclic (IsAcyclic.reflect_of_isSink isAcyclic isSink_tgt)
      tgt)
    hfdM hfdN ?_
  have hcardS : Nat.card (@Path (Reflect (Kronecker A) tgt) _ tgt src) = 1 :=
    card_path_reflect_tgt_src.trans Nat.card_unique
  rw [dimVector_reflectRep_simpleRep_src]
  funext j
  refine Eq.trans ?_
    (dimVector_indecProjRep (k := k) (Q := Reflect (Kronecker A) tgt) tgt j).symm
  cases j with
  | src => simpa using hcardS.symm
  | tgt => simp [src_ne_tgt.symm, Fintype.card_unique]

end A2

end TauCeti
