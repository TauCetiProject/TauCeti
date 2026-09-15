/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Reflection.Acyclic
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
Kronecker quiver, read the other way round; that is settled in
`TauCeti.RepresentationTheory.Quiver.Kronecker.Basic`.

On representations the reflection does three things:

* it **annihilates the sink simple** `S_tgt`, the one representation concentrated at `tgt`;
* it carries the **projective** `P_src` to the **vertex simple** `S_src` of the reflected quiver;
* it carries the **source simple** `S_src` to an indecomposable representation of dimension vector
  `(1, #A)`, the value at `(1, 0)` of the simple reflection at `tgt`.

For the `A₂` quiver these are the three indecomposables `S_tgt`, `P_src`, `S_src`, of dimension
vectors `(0,1)`, `(1,1)`, `(1,0)`, and the last statement sharpens to an isomorphism with the
projective `P_tgt` of the reflected quiver: reflection kills `S_tgt` and exchanges the other two.
On those other two the dimension vector follows the simple reflection `s_tgt`, which swaps `(1,0)`
and `(1,1)`. The sink simple is the exception and not merely a third case: `s_tgt` sends its
dimension vector `(0,1)` to the negative root `(0,-1)`, which is the dimension vector of no
representation, and reflection sends `S_tgt` to zero instead.

## Main results

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

The identification of the reflection of `S_src` is confined to the `A₂` case, and cannot be had
beyond it: the Kronecker quiver `• ⇉ •` already carries a whole family of pairwise
non-isomorphic indecomposables at the single dimension vector `(1, 1)`, by
`TauCeti.nonempty_kroneckerLineRep_iso_iff`.

The arrow type is taken in `Type`, as in
`TauCeti.RepresentationTheory.Quiver.Kronecker.AlmostSplit`: the vertex spaces of the reflection
are cut out of a product indexed by the arrows, so they live in the maximum of the arrow universe
and the universe of the field, while those of the vertex simple are the field itself.

## References

Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and Derksen--Weyman,
*An Introduction to Quiver Representations*, Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open _root_.Quiver
open _root_.TauCeti.Quiver

universe u

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
  have himage : ((indecProjRep k (Kronecker A) src).map (arrow a).toPath).hom
      (indecProjRepBasis k src src Path.nil)
      = indecProjRepBasis k src tgt (arrowPath a) :=
    (indecProjRep_map_basis src (arrow a).toPath Path.nil).trans
      (by rw [Path.nil_comp, toPath_arrow])
  have h := map_toPath_mem_range_incomingSum (indecProjRep k (Kronecker A) src) (arrow a)
    (indecProjRepBasis k src src Path.nil)
  rwa [himage] at h

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

/-- **Over the `A₂` quiver reflection carries the source simple to the projective at the target**
of the reflected quiver. Both are indecomposable of dimension vector `(1, 1)`, and over a quiver
with positive definite Tits form the dimension vector of an indecomposable determines it.

Together with `TauCeti.isZero_reflectRep_simpleRep_tgt` and
`TauCeti.nonempty_iso_reflectRep_indecProjRep_src` this is the whole action of the reflection at
the sink on the three indecomposables of the `A₂` quiver: it annihilates `S_tgt` and exchanges
`S_src` with `P_src`. So it realizes the simple reflection at `tgt` on the dimension vectors
`(1,0)` and `(1,1)` of the latter two only; on the sink simple the two disagree, reflection
sending `S_tgt` to zero where `s_tgt` sends `(0,1)` to `(0,-1)`. -/
theorem nonempty_iso_reflectRep_simpleRep_src_indecProjRep :
    Nonempty (reflectRep (simpleRep k (Kronecker A) src) isSink_tgt
      ≅ indecProjRep k (Reflect (Kronecker A) tgt) tgt) := by
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
    (IsAcyclic.reflect_of_isSink isAcyclic isSink_tgt)
    (titsForm_reflect_posDef (le_of_eq Fintype.card_unique)) _ _
    indecomposable_reflectRep_simpleRep_src
    (indecomposable_indecProjRep_of_isAcyclic (IsAcyclic.reflect_of_isSink isAcyclic isSink_tgt)
      tgt)
    hfdM hfdN ?_
  rw [dimVector_reflectRep_simpleRep_src]
  funext j
  refine Eq.trans ?_
    (dimVector_indecProjRep (k := k) (Q := Reflect (Kronecker A) tgt) tgt j).symm
  cases j with
  | src => simp
  | tgt => simp [src_ne_tgt.symm, Fintype.card_unique]

end A2

end TauCeti
