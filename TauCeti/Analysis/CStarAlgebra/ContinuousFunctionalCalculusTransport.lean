/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# Transporting a continuous functional calculus along an isomorphism

`ContinuousFunctionalCalculus R A p` is an existential statement about `A`: every `a` with
`p a` admits a continuous injective `⋆`-algebra map from symbols on its spectrum sending the
identity symbol to `a`.  Nothing in it is intrinsic to the *carrier*, so it transports along
any isomorphism of topological `R`-`⋆`-algebras that matches the two predicates:

```text
(A ≃⋆ₐ[R] B) → ContinuousFunctionalCalculus R B q → ContinuousFunctionalCalculus R A p
```

Mathlib has no such transport.  Its instances are all built directly, and the two mechanisms
it does provide for moving a calculus — `SpectrumRestricts` for shrinking the scalar ring and
`StarAlgHom` images for subalgebras — do not cover a change of carrier.

## Why this repository needs it

`ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint` is registered at `𝕜 = ℂ` by
Mathlib and at `𝕜 = ℝ` by `ForTauCeti/Analysis/InnerProductSpace/`
`RealContinuousFunctionalCalculus.lean`, and an arbitrary `RCLike` field is isomorphic to one
of those two.  Transporting the calculus across that isomorphism is what turns the hypothesis
block

```text
[Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
[ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
```

that the operator-modulus and angle-operator API carries into an inferable instance, so that a
scalar-generic theorem about angles between subspaces exposes `[RCLike 𝕜]` and nothing else.

The statement below is deliberately about an arbitrary pair of algebras rather than about that
application: it is the general fact, and it is the shape a reviewer would expect to see
upstream.

## Only one direction of continuity is used

`Continuous Φ.symm` is a hypothesis; `Continuous Φ` is not, and adding it would be dead
weight.  The calculus of `a` is built as the calculus of `Φ a` followed by `Φ.symm`, so only
that composite has to be continuous.  Everything `Φ` itself contributes is algebraic:
`AlgEquiv.spectrum_eq` identifies the spectra, and `hpq` identifies the predicates.
-/

public section

namespace ContinuousFunctionalCalculus

variable {R A B : Type*}
  [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A]
  [Ring B] [StarRing B] [TopologicalSpace B] [Algebra R B]
  {p : A → Prop} {q : B → Prop}

/-- The identity, read as a map from the spectrum of `a` to the spectrum of `Φ a`.  The two
spectra are equal as subsets of `R`, so this moves no points and is a bijection. -/
private def spectrumEquivMap (Φ : A ≃⋆ₐ[R] B) (a : A) :
    C(spectrum R (Φ a), spectrum R a) :=
  ⟨Set.inclusion (AlgEquiv.spectrum_eq Φ a).subset, continuous_inclusion _⟩

omit [StarRing R] [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]
  [TopologicalSpace B] in
private theorem spectrumEquivMap_surjective (Φ : A ≃⋆ₐ[R] B) (a : A) :
    Function.Surjective (spectrumEquivMap Φ a) := fun y =>
  ⟨⟨(y : R), by rw [AlgEquiv.spectrum_eq Φ a]; exact y.2⟩, Subtype.ext rfl⟩

/-- **A continuous functional calculus transports along an isomorphism of topological
`R`-`⋆`-algebras** that matches the two predicates.

Every field of the class is read off through `Φ`: spectra agree by `AlgEquiv.spectrum_eq`, so
the symbol algebras agree, and the calculus of `a` is the calculus of `Φ a` followed by
`Φ.symm`. -/
theorem of_starAlgEquiv [ContinuousFunctionalCalculus R B q]
    (Φ : A ≃⋆ₐ[R] B) (hΦsymm : Continuous Φ.symm) (hpq : ∀ a, p a ↔ q (Φ a)) :
    ContinuousFunctionalCalculus R A p := by
  have hspec : ∀ a : A, spectrum R (Φ a) = spectrum R a := fun a => AlgEquiv.spectrum_eq Φ a
  refine
    { predicate_zero := (hpq 0).2 (by
        rw [map_zero]
        exact ContinuousFunctionalCalculus.predicate_zero R (A := B))
      compactSpace_spectrum := fun a => ?_
      spectrum_nonempty := fun a ha => ?_
      exists_cfc_of_predicate := fun a ha => ?_ }
  · rw [← hspec a]
    exact ContinuousFunctionalCalculus.compactSpace_spectrum (R := R) (Φ a)
  · have : Nontrivial B := ⟨Φ 0, Φ 1, fun h => zero_ne_one (Φ.injective h)⟩
    rw [← hspec a]
    exact ContinuousFunctionalCalculus.spectrum_nonempty (R := R) (Φ a) ((hpq a).1 ha)
  · have hb : q (Φ a) := (hpq a).1 ha
    refine
      ⟨(Φ.symm.toStarAlgHom.comp
          ((cfcHom hb).comp (ContinuousMap.compStarAlgHom' R R (spectrumEquivMap Φ a)))),
        ?_, ?_, ?_, ?_, ?_⟩
    · exact hΦsymm.comp
        ((cfcHom_continuous hb).comp (ContinuousMap.continuous_precomp (spectrumEquivMap Φ a)))
    · intro f g hfg
      have h := cfcHom_injective hb (Φ.symm.injective hfg)
      refine ContinuousMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := spectrumEquivMap_surjective Φ a x
      exact congrFun (congrArg DFunLike.coe h) y
    · have hid : ((ContinuousMap.id R).restrict (spectrum R a)).comp (spectrumEquivMap Φ a) =
          (ContinuousMap.id R).restrict (spectrum R (Φ a)) := ContinuousMap.ext fun _ => rfl
      change Φ.symm (cfcHom hb (((ContinuousMap.id R).restrict (spectrum R a)).comp
        (spectrumEquivMap Φ a))) = a
      rw [hid, cfcHom_id hb, Φ.symm_apply_apply]
    · intro f
      change spectrum R (Φ.symm (cfcHom hb (f.comp (spectrumEquivMap Φ a)))) = Set.range f
      rw [AlgEquiv.spectrum_eq Φ.symm, cfcHom_map_spectrum hb]
      exact (spectrumEquivMap_surjective Φ a).range_comp f
    · intro f
      refine (hpq _).2 ?_
      change q (Φ (Φ.symm (cfcHom hb (f.comp (spectrumEquivMap Φ a)))))
      rw [Φ.apply_symm_apply]
      exact cfcHom_predicate hb _

/-! ## Naturality of `cfc`

The transport also computes: an isomorphism carries the calculus of `a` to the calculus of
`Φ a`, symbol by symbol.  This is the form a consumer uses, and it needs the calculus on both
sides rather than producing one. -/

/-- The identity, read as a map from the spectrum of `Φ a` to the spectrum of `a`. -/
private def spectrumEquivMap' (Φ : A ≃⋆ₐ[R] B) (a : A) :
    C(spectrum R a, spectrum R (Φ a)) :=
  ⟨Set.inclusion (AlgEquiv.spectrum_eq Φ a).symm.subset, continuous_inclusion _⟩

/-- **A `⋆`-algebra isomorphism commutes with the continuous functional calculus.**

Both `Φ ∘ cfcHom` and `cfcHom` at `Φ a` are continuous `⋆`-algebra maps out of the symbol
algebra sending the identity symbol to `Φ a`, and `ContinuousMap.UniqueHom` says there is only
one such. -/
theorem map_cfc [ContinuousFunctionalCalculus R A p] [ContinuousFunctionalCalculus R B q]
    [ContinuousMap.UniqueHom R B]
    (Φ : A ≃⋆ₐ[R] B) (hΦ : Continuous Φ) (hpq : ∀ a, p a ↔ q (Φ a))
    (f : R → R) {a : A} (ha : p a) (hf : ContinuousOn f (spectrum R a)) :
    Φ (cfc f a) = cfc f (Φ a) := by
  have hb : q (Φ a) := (hpq a).1 ha
  have hsp : spectrum R (Φ a) = spectrum R a := AlgEquiv.spectrum_eq Φ a
  have hf' : ContinuousOn f (spectrum R (Φ a)) := by rw [hsp]; exact hf
  have hcfc : cfcHom hb =
      (Φ.toStarAlgHom.comp
        ((cfcHom ha).comp (ContinuousMap.compStarAlgHom' R R (spectrumEquivMap' Φ a)))) := by
    refine cfcHom_eq_of_continuous_of_map_id hb _ ?_ ?_
    · exact hΦ.comp
        ((cfcHom_continuous ha).comp (ContinuousMap.continuous_precomp (spectrumEquivMap' Φ a)))
    · have hid : ((ContinuousMap.id R).restrict (spectrum R (Φ a))).comp
          (spectrumEquivMap' Φ a) = (ContinuousMap.id R).restrict (spectrum R a) :=
        ContinuousMap.ext fun _ => rfl
      change Φ (cfcHom ha (((ContinuousMap.id R).restrict (spectrum R (Φ a))).comp
        (spectrumEquivMap' Φ a))) = Φ a
      rw [hid, cfcHom_id ha]
  rw [cfc_apply f a ha hf, cfc_apply f (Φ a) hb hf', hcfc]
  rfl

end ContinuousFunctionalCalculus
