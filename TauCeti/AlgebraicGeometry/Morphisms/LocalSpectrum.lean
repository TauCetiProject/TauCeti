/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
public import TauCeti.AlgebraicGeometry.Scheme.LocalSpectrum

/-!
# Unramifiedness on the spectrum of a stalk

For `f : X ⟶ Y` and `x : X`, regard the source stalk as an algebra over the target stalk
via `f.stalkMap x`. Unramifiedness of this algebra at a prime is equivalent to formal
unramifiedness of the scheme's stalk map at the corresponding generization of `x`.
In particular, the codimension-one generization condition is exactly unramifiedness at all
height-one primes of the source stalk.

These comparisons require no finiteness or Noetherian hypotheses. They allow a pointwise
ramification hypothesis to be used in finite local algebra after isolating a fibre.

## References

* The Stacks Project, proof of Lemma 58.21.4 (0BMB), the passage to spectra of local rings.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- Unramifiedness of the stalk algebra at a prime is equivalent to formal unramifiedness of
`f` at the corresponding generization. -/
theorem isUnramifiedAt_stalkMap_iff (f : X ⟶ Y) (x : X)
    (q : PrimeSpectrum (X.presheaf.stalk x)) :
    letI := (f.stalkMap x).hom.toAlgebra
    Algebra.IsUnramifiedAt (Y.presheaf.stalk (f x)) q.asIdeal ↔
      (f.stalkMap (X.fromSpecStalk x q)).hom.FormallyUnramified := by
  let := (f.stalkMap x).hom.toAlgebra
  have hspec : ((Spec.map (f.stalkMap x)).stalkMap q).hom.FormallyUnramified ↔
      Algebra.IsUnramifiedAt (Y.presheaf.stalk (f x)) q.asIdeal := by
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using
      (formallyUnramified_stalkMap_specMap_iff (R := Y.presheaf.stalk (f x)) q)
  have hw := congrArg (fun k : Spec (X.presheaf.stalk x) ⟶ Y ↦
    (k.stalkMap q).hom.FormallyUnramified) (Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x))
  rw [Scheme.Hom.stalkMap_comp (Spec.map (f.stalkMap x)) (Y.fromSpecStalk (f x)) q,
    Scheme.Hom.stalkMap_comp (X.fromSpecStalk x) f q] at hw
  have : IsIso ((X.fromSpecStalk x).stalkMap q) :=
    Scheme.isIso_stalkMap_fromSpecStalk X x q
  exact hspec.symm.trans <|
    (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso _ _).symm.trans <|
      (iff_of_eq hw).trans
        (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ _)

/-- Unramifiedness at all codimension-one generizations of `x` is equivalent to unramifiedness
at all height-one primes of the source stalk, as an algebra over the target stalk. -/
theorem formallyUnramified_stalk_codimOne_iff_isUnramifiedAt (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    (∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 →
      (f.stalkMap z).hom.FormallyUnramified) ↔
    (∀ q : Ideal (X.presheaf.stalk x), ∀ (_ : q.IsPrime), q.height = 1 →
      Algebra.IsUnramifiedAt (Y.presheaf.stalk (f x)) q) := by
  let := (f.stalkMap x).hom.toAlgebra
  constructor
  · intro h q hq hheight
    let z : Spec (X.presheaf.stalk x) := ⟨q, hq⟩
    apply (f.isUnramifiedAt_stalkMap_iff x z).mpr
    have hz : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := Set.mem_range_self z
    rw [Scheme.range_fromSpecStalk] at hz
    apply h _ hz
    rw [← Scheme.height_eq_ringKrullDim_fromSpecStalk X x z, hheight]
    exact WithBot.coe_one
  · intro h z hzx hdim
    obtain ⟨q, rfl⟩ := (show z ∈ Set.range (X.fromSpecStalk x) by
      rw [Scheme.range_fromSpecStalk]
      exact hzx)
    apply (f.isUnramifiedAt_stalkMap_iff x q).mp
    apply h q.asIdeal q.isPrime
    have heq := Scheme.height_eq_ringKrullDim_fromSpecStalk X x q
    rw [hdim] at heq
    exact WithBot.coe_eq_one.mp heq

end AlgebraicGeometry.Scheme.Hom
