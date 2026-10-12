/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Injective.Envelope
public import TauCeti.RepresentationTheory.Quiver.Representation.Comparison

/-!
# The vertex injective is the injective envelope of the vertex simple

For a vertex `i` of a quiver `Q`, the embedding `Sᵢ ↪ Iᵢ` of
`TauCeti.RepresentationTheory.Quiver.Representation.Comparison` places the vertex simple inside
the vertex injective. This file proves that when the trivial path is the only path `i → i`, this
embedding is an **injective envelope**: it is an essential monomorphism into an injective object.

The local hypothesis is sharp. For the one-loop quiver, `(Iᵢ)ᵢ` is the full dual of `k[X]`, while
the image of `Sᵢ` is only the functional reading the constant coefficient; it is not an essential
subobject. Acyclicity of the whole quiver is a sufficient uniform hypothesis, but cycles away from
`i` play no role.

The result gives the strong form of essentiality: a morphism out of `Iᵢ` which remains monic on
`Sᵢ` is a split monomorphism. Consequently, the general essential-monomorphism API identifies
`Iᵢ` as the minimal injective object containing `Sᵢ` and makes it unique up to isomorphism under
`Sᵢ`.

## Main results

* `TauCeti.isSplitMono_of_mono_simpleRepToIndecInjRep_comp`: a map out of `Iᵢ` which is monic on
  `Sᵢ` is a split monomorphism.
* `TauCeti.isEssentialMono_simpleRepToIndecInjRep`: `Sᵢ ↪ Iᵢ` is an essential monomorphism.

## References

The construction is dual to
`TauCeti/RepresentationTheory/Quiver/Representation/Projective/Cover.lean`.

See I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, I.5 and III.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v w

variable (k : Type (max v w)) {Q : Type v} [Field k] [Quiver.{w} Q]

/-- With no nontrivial path `i → i`, the value of the vertex injective at `i` is the line spanned
by the image of the generator of the vertex simple. -/
theorem eq_smul_simpleRepToIndecInjRep_app_generator {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    (x : (indecInjRep k Q i).obj ((Paths.of Q).obj i)) :
    x = x Quiver.Path.nil •
      (simpleRepToIndecInjRep k i).app ((Paths.of Q).obj i) (simpleRepGenerator k i) := by
  funext p
  obtain rfl := h p
  -- `(Iᵢ)ᵢ` is definitionally the function space on closed paths only after unfolding the
  -- free-category object wrapper; expose that identification before evaluating the scalar action.
  change x Quiver.Path.nil = x Quiver.Path.nil *
    (simpleRepToIndecInjRep k i).app ((Paths.of Q).obj i)
      (simpleRepGenerator k i) Quiver.Path.nil
  have hgen :
      (simpleRepToIndecInjRep k i).app ((Paths.of Q).obj i)
          (simpleRepGenerator k i) Quiver.Path.nil = 1 :=
    (simpleRepToIndecInjRep_app_apply k (simpleRepGenerator k i) Quiver.Path.nil).trans <|
      (congrArg (simpleRepSelfEquiv k i)
        (QuiverRep.map_nil_apply (simpleRep k Q i) i (simpleRepGenerator k i))).trans <|
          simpleRepSelfEquiv_apply_generator k i
  rw [hgen, mul_one]

/-- A morphism out of `Iᵢ` which is monic on the embedded `Sᵢ` is injective at the vertex `i`.
This is the linear-algebra core of essentiality: under the local acyclicity hypothesis `(Iᵢ)ᵢ`
is the line spanned by the image of the generator of `(Sᵢ)ᵢ`. -/
private theorem indecInjRep_app_injective_of_mono_simpleRepToIndecInjRep_comp {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil) {X : QuiverRep k Q}
    (g : indecInjRep k Q i ⟶ X) (hg : Mono (simpleRepToIndecInjRep k i ≫ g)) :
    Function.Injective (g.app ((Paths.of Q).obj i)) := by
  have hcomp : Function.Injective
      ((simpleRepToIndecInjRep k i ≫ g).app ((Paths.of Q).obj i)) :=
    (ModuleCat.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app (simpleRepToIndecInjRep k i ≫ g)).1 hg _)
  let u := (simpleRepToIndecInjRep k i).app ((Paths.of Q).obj i) (simpleRepGenerator k i)
  have hu : g.app ((Paths.of Q).obj i) u ≠ 0 := by
    intro hgu
    apply simpleRepGenerator_ne_zero k i
    apply hcomp
    -- Composition of natural transformations is componentwise, but the concrete `ModuleCat`
    -- coercions hide that equation until the component map is exposed explicitly.
    change g.app ((Paths.of Q).obj i) u =
      g.app ((Paths.of Q).obj i)
        ((simpleRepToIndecInjRep k i).app ((Paths.of Q).obj i) 0)
    rw [hgu, map_zero, map_zero]
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have hxu := eq_smul_simpleRepToIndecInjRep_app_generator k h x
  have hsmul : x Quiver.Path.nil • g.app ((Paths.of Q).obj i) u = 0 := by
    rw [← map_smul, ← hxu]
    exact hx
  have hxnil : x Quiver.Path.nil = 0 := (smul_eq_zero.mp hsmul).resolve_right hu
  rw [hxu, hxnil, zero_smul]

/-- **`Sᵢ ↪ Iᵢ` is an essential monomorphism, in the strong split form**: with no nontrivial
path `i → i`, a morphism out of `Iᵢ` which remains monic after restriction to `Sᵢ` is already a
split monomorphism. -/
theorem isSplitMono_of_mono_simpleRepToIndecInjRep_comp {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil) {X : QuiverRep k Q}
    (g : indecInjRep k Q i ⟶ X) (hg : Mono (simpleRepToIndecInjRep k i ≫ g)) :
    IsSplitMono g := by
  have hinj := indecInjRep_app_injective_of_mono_simpleRepToIndecInjRep_comp k h g hg
  exact isSplitMono_of_indecInjRep_app_injective g hinj

/-- **The vertex injective is the injective envelope of the vertex simple.** If the trivial path
is the only path `i → i`, the canonical embedding `Sᵢ ↪ Iᵢ` is an essential monomorphism;
together with `TauCeti.injective_indecInjRep`, this characterizes `Iᵢ` as the injective envelope.
-/
theorem isEssentialMono_simpleRepToIndecInjRep {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil) :
    IsEssentialMono (simpleRepToIndecInjRep k i) where
  mono := inferInstance
  mono_of_comp_mono g hg := by
    have := isSplitMono_of_mono_simpleRepToIndecInjRep_comp k h g hg
    infer_instance

end TauCeti
