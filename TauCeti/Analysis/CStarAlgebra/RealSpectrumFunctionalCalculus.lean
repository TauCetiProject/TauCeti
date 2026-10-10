/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Restrict
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The complex functional calculus of a self-adjoint element, on its real spectrum

For a self-adjoint `a` in a unital C⋆-algebra `A` over `ℂ`, Mathlib supplies two calculi:

* `cfcHom ha.isStarNormal : C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] A`, complex symbols on the complex
  spectrum;
* `cfcHom ha : C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] A`, real symbols on the real spectrum, obtained from
  the first by `SpectrumRestricts.starAlgHom`.

Neither is the object needed to state spectral multiplicity for a self-adjoint operator with a
*real* spectral parameter and *complex* matrix elements. This module supplies the third corner,

```text
TauCeti.realSpectrumCfcHom ha : C(spectrum ℝ a, ℂ) →⋆ₐ[ℂ] A
```

— the symbol **domain** lowered to `spectrum ℝ a`, the symbol **codomain** and the scalars kept
at `ℂ`.

## Why the domain and not the codomain

Lowering the codomain to `ℝ` is not an option on a complex Hilbert space, and this is not a
matter of missing API. The two-term real polarization identity recovers only `Re ⟪ψ, T ξ⟫`, for
every operator including the self-adjoint ones: on `H = ℂ` with `T = 1`, `ξ = 1` and `ψ = I`,
the two-term sum is `0` while the matrix element is `-I`. A complex Hilbert space therefore
forces complex-valued symbols, and the only remaining degree of freedom is the domain.

Lowering the domain costs nothing, because for a self-adjoint element the two spectra are
homeomorphic: `SpectrumRestricts.homeomorph` turns `IsSelfAdjoint.spectrumRestricts` into
`spectrum ℂ a ≃ₜ spectrum ℝ a`, with `Complex.re` one way and `Complex.ofReal` the other. The
construction here is a *transport*, not a new calculus, and `realSpectrumCfcHom_apply` together
with `cfcHom_eq_realSpectrumCfcHom` states the transport in both directions. Those two lemmas
are what make the definition usable from consumers already phrased over `spectrum ℂ a`.

## Main results

* `TauCeti.realSpectrumHomeomorph`: `spectrum ℂ a ≃ₜ spectrum ℝ a`, for self-adjoint `a`;
* `TauCeti.realSpectrumCfcHom`: the transported calculus, a `⋆`-algebra homomorphism over `ℂ`;
* `TauCeti.realSpectrumCfcHom_apply` and `TauCeti.cfcHom_eq_realSpectrumCfcHom`: the
  compatibility bridge with `cfcHom` on `spectrum ℂ a`, in both directions;
* `TauCeti.realSpectrumCfcHom_realSpectrumId`: the identity symbol is sent to `a`;
* `TauCeti.realSpectrumCfcHom_injective`, `TauCeti.continuous_realSpectrumCfcHom`,
  `TauCeti.realSpectrumCfcHom_map_spectrum`: injectivity, continuity, and the spectral mapping
  theorem, each inherited across the transport;
* `TauCeti.realSpectrumCfcHom_isSelfAdjoint`: a real-valued symbol has self-adjoint image.

Every statement is generic in the C⋆-algebra. The intended instance is `A := H →L[ℂ] H` for a
complex Hilbert space `H`, which the final section records.

## A note on `@[expose]`

The characteristic lemmas `realSpectrumCfcHom_apply`, `realSpectrumId_apply` and the
`realSpectrumHomeomorph` coercion lemmas hold by `rfl`, but a `rfl` proof in an *exported*
theorem would force `@[expose]` on each definition, against `ForTauCeti/README.md`. Each is
therefore proved by a `private` lemma, which may unfold the body, and re-exported. Downstream
consumers get the equations and never the bodies, which is what the `api-design` rubric asks
for.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.); written here, new for
  this library.
* Extraction class: **new**. The transport is standard C⋆-algebra practice and nothing was
  copied; `SpectrumRestricts.homeomorph` and `ContinuousMap.compStarAlgHom'` are the Mathlib
  ingredients, and Mathlib's `SpectrumRestricts.starAlgHom` is the sibling construction that
  lowers the codomain as well.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib.
* Proposed Mathlib destination:
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Restrict.lean`, beside
  `SpectrumRestricts.starAlgHom`, of which it is the domain-only analogue.
-/

public section

namespace TauCeti

section Symbol

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **The identity symbol** of the real-spectrum calculus: a real spectral point, read in `ℂ`.

This is the symbol that `realSpectrumCfcHom` sends back to the element itself, so it plays the
role `(ContinuousMap.id ℂ).restrict (spectrum ℂ a)` plays for `cfcHom`. -/
noncomputable def realSpectrumId (a : A) : C(spectrum ℝ a, ℂ) :=
  ⟨fun x => ((x : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

private theorem realSpectrumId_apply_aux (a : A) (x : spectrum ℝ a) :
    realSpectrumId a x = ((x : ℝ) : ℂ) := rfl

/-- The identity symbol is the inclusion `ℝ → ℂ` on spectral points. -/
@[simp]
theorem realSpectrumId_apply (a : A) (x : spectrum ℝ a) :
    realSpectrumId a x = ((x : ℝ) : ℂ) :=
  realSpectrumId_apply_aux a x

end Symbol

section Transport

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- **The two spectra of a self-adjoint element are homeomorphic.**

`Complex.re` maps `spectrum ℂ a` onto `spectrum ℝ a` and `Complex.ofReal` inverts it, because
`IsSelfAdjoint.spectrumRestricts` says the complex spectrum is real. This is
`SpectrumRestricts.homeomorph` at the restriction witness of a self-adjoint element, under the
name the rest of this file uses. -/
noncomputable def realSpectrumHomeomorph {a : A} (ha : IsSelfAdjoint a) :
    spectrum ℂ a ≃ₜ spectrum ℝ a :=
  SpectrumRestricts.homeomorph (f := (Complex.reCLM : C(ℂ, ℝ))) ha.spectrumRestricts

private theorem realSpectrumHomeomorph_eq_aux {a : A} (ha : IsSelfAdjoint a) :
    realSpectrumHomeomorph ha
      = SpectrumRestricts.homeomorph (f := (Complex.reCLM : C(ℂ, ℝ))) ha.spectrumRestricts :=
  rfl

/-- `realSpectrumHomeomorph` is `SpectrumRestricts.homeomorph`: the characteristic lemma, so no
consumer needs the body. -/
theorem realSpectrumHomeomorph_eq {a : A} (ha : IsSelfAdjoint a) :
    realSpectrumHomeomorph ha
      = SpectrumRestricts.homeomorph (f := (Complex.reCLM : C(ℂ, ℝ))) ha.spectrumRestricts :=
  realSpectrumHomeomorph_eq_aux ha

private theorem realSpectrumHomeomorph_apply_coe_aux {a : A} (ha : IsSelfAdjoint a)
    (z : spectrum ℂ a) : ((realSpectrumHomeomorph ha z : ℝ)) = (z : ℂ).re := rfl

/-- The homeomorphism takes a point of the complex spectrum to its real part. -/
@[simp]
theorem realSpectrumHomeomorph_apply_coe {a : A} (ha : IsSelfAdjoint a) (z : spectrum ℂ a) :
    ((realSpectrumHomeomorph ha z : ℝ)) = (z : ℂ).re :=
  realSpectrumHomeomorph_apply_coe_aux ha z

/-- Reading the real part back into `ℂ` returns the original spectral point: the complex
spectrum of a self-adjoint element is real. -/
theorem coe_realSpectrumHomeomorph {a : A} (ha : IsSelfAdjoint a) (z : spectrum ℂ a) :
    (((realSpectrumHomeomorph ha z : ℝ) : ℂ)) = (z : ℂ) := by
  rw [realSpectrumHomeomorph_apply_coe]
  simpa using ha.spectrumRestricts.rightInvOn z.2

private theorem realSpectrumHomeomorph_symm_apply_coe_aux {a : A} (ha : IsSelfAdjoint a)
    (x : spectrum ℝ a) : (((realSpectrumHomeomorph ha).symm x : ℂ)) = ((x : ℝ) : ℂ) := rfl

/-- The inverse homeomorphism is the inclusion `ℝ → ℂ` on spectral points. -/
@[simp]
theorem realSpectrumHomeomorph_symm_apply_coe {a : A} (ha : IsSelfAdjoint a)
    (x : spectrum ℝ a) : (((realSpectrumHomeomorph ha).symm x : ℂ)) = ((x : ℝ) : ℂ) :=
  realSpectrumHomeomorph_symm_apply_coe_aux ha x

/-- **The complex functional calculus of a self-adjoint element, on its real spectrum.**

Symbols are continuous `ℂ`-valued functions of a *real* spectral parameter; the scalars, the
values, and the `⋆`-algebra structure all stay complex. It is `cfcHom` precomposed with symbol
reindexing along `realSpectrumHomeomorph`, so it is a `⋆`-algebra homomorphism by construction
and inherits every property of `cfcHom` through `realSpectrumCfcHom_apply`. -/
noncomputable def realSpectrumCfcHom {a : A} (ha : IsSelfAdjoint a) :
    C(spectrum ℝ a, ℂ) →⋆ₐ[ℂ] A :=
  (cfcHom ha.isStarNormal).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ
      (realSpectrumHomeomorph ha : C(spectrum ℂ a, spectrum ℝ a)))

private theorem realSpectrumCfcHom_apply_aux {a : A} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℂ)) :
    realSpectrumCfcHom ha f
      = cfcHom ha.isStarNormal
          (f.comp (realSpectrumHomeomorph ha : C(spectrum ℂ a, spectrum ℝ a))) := rfl

/-- **The compatibility bridge, forward direction.**

A real-spectrum symbol is evaluated by reindexing it along `realSpectrumHomeomorph` and feeding
the result to the ordinary complex calculus. This identity is how every property of `cfcHom`
transfers, and how a consumer phrased over `spectrum ℂ a` reaches `realSpectrumCfcHom`. -/
theorem realSpectrumCfcHom_apply {a : A} (ha : IsSelfAdjoint a) (f : C(spectrum ℝ a, ℂ)) :
    realSpectrumCfcHom ha f
      = cfcHom ha.isStarNormal
          (f.comp (realSpectrumHomeomorph ha : C(spectrum ℂ a, spectrum ℝ a))) :=
  realSpectrumCfcHom_apply_aux ha f

/-- **The compatibility bridge, backward direction.**

Every value of the ordinary complex calculus is a value of the transported one: reindex the
symbol along the inverse homeomorphism. With `realSpectrumCfcHom_apply` this says the two
homomorphisms have the same range, and names the real-spectrum symbol realizing a given
operator. -/
theorem cfcHom_eq_realSpectrumCfcHom {a : A} (ha : IsSelfAdjoint a) (g : C(spectrum ℂ a, ℂ)) :
    cfcHom ha.isStarNormal g
      = realSpectrumCfcHom ha
          (g.comp ((realSpectrumHomeomorph ha).symm : C(spectrum ℝ a, spectrum ℂ a))) := by
  rw [realSpectrumCfcHom_apply]
  congr 1
  refine ContinuousMap.ext fun z => ?_
  exact congrArg g ((realSpectrumHomeomorph ha).symm_apply_apply z).symm

/-- **The transported calculus recovers the element**, the analogue of `cfcHom_id`. With
`realSpectrumCfcHom_apply` and continuity this pins `realSpectrumCfcHom` down uniquely among
continuous `⋆`-algebra homomorphisms. -/
@[simp]
theorem realSpectrumCfcHom_realSpectrumId {a : A} (ha : IsSelfAdjoint a) :
    realSpectrumCfcHom ha (realSpectrumId a) = a := by
  rw [realSpectrumCfcHom_apply]
  have hsymb : (realSpectrumId a).comp
      (realSpectrumHomeomorph ha : C(spectrum ℂ a, spectrum ℝ a))
      = (ContinuousMap.id ℂ).restrict (spectrum ℂ a) :=
    ContinuousMap.ext fun z => coe_realSpectrumHomeomorph ha z
  rw [hsymb, cfcHom_id]

/-- Constants go to constants: the transported calculus is unital and `ℂ`-linear. -/
@[simp]
theorem realSpectrumCfcHom_algebraMap {a : A} (ha : IsSelfAdjoint a) (r : ℂ) :
    realSpectrumCfcHom ha (algebraMap ℂ C(spectrum ℝ a, ℂ) r) = algebraMap ℂ A r :=
  AlgHomClass.commutes _ r

/-- The transported calculus is continuous: `cfcHom` is continuous and precomposition with a
continuous map is continuous for the compact-open topology. -/
theorem continuous_realSpectrumCfcHom {a : A} (ha : IsSelfAdjoint a) :
    Continuous (realSpectrumCfcHom ha) :=
  (cfcHom_continuous ha.isStarNormal).comp (ContinuousMap.continuous_precomp _)

/-- The transported calculus is injective: reindexing along a homeomorphism is bijective on
symbols, and `cfcHom` is injective. -/
theorem realSpectrumCfcHom_injective {a : A} (ha : IsSelfAdjoint a) :
    Function.Injective (realSpectrumCfcHom ha) := by
  intro f g hfg
  rw [realSpectrumCfcHom_apply, realSpectrumCfcHom_apply] at hfg
  have h := cfcHom_injective ha.isStarNormal hfg
  refine ContinuousMap.ext fun x => ?_
  have hx := ContinuousMap.congr_fun h ((realSpectrumHomeomorph ha).symm x)
  simpa using hx

/-- **The spectral mapping theorem** across the transport: the spectrum of the value at `f` is
the range of the real-spectrum symbol `f`. -/
theorem realSpectrumCfcHom_map_spectrum {a : A} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℂ)) :
    spectrum ℂ (realSpectrumCfcHom ha f) = Set.range f := by
  rw [realSpectrumCfcHom_apply, cfcHom_map_spectrum]
  refine Set.ext fun z => ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    exact ⟨realSpectrumHomeomorph ha w, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(realSpectrumHomeomorph ha).symm x, ?_⟩
    simp

/-- Every value of the transported calculus is star-normal, being a value of `cfcHom`. -/
theorem realSpectrumCfcHom_isStarNormal {a : A} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℂ)) : IsStarNormal (realSpectrumCfcHom ha f) := by
  rw [realSpectrumCfcHom_apply]
  exact cfcHom_predicate ha.isStarNormal _

/-- **A real-valued symbol has self-adjoint image.** This is the reason the construction is
usable for spectral multiplicity: the symbol algebra is complex, but the real-valued symbols
inside it still land in the self-adjoint part of `A`. -/
theorem realSpectrumCfcHom_isSelfAdjoint {a : A} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℂ)) (hf : ∀ x, (f x).im = 0) :
    IsSelfAdjoint (realSpectrumCfcHom ha f) := by
  have hstar : star f = f := by
    refine ContinuousMap.ext fun x => ?_
    simpa using Complex.conj_eq_iff_im.2 (hf x)
  have hmap := map_star (realSpectrumCfcHom ha) f
  rw [hstar] at hmap
  exact hmap.symm

end Transport

section RealSymbols

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal] [ContinuousMap.UniqueHom ℝ A]

/-- **The bridge to Mathlib's real calculus.**

On a real-valued symbol, read into `ℂ`, the transported calculus agrees with
`cfcHom ha : C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] A`. Together with `realSpectrumCfcHom_apply` this places
`realSpectrumCfcHom` between the two calculi Mathlib already has: it restricts to the real one
on real symbols and is the complex one after reindexing. Uniqueness of the calculus over `ℝ`
enters through `SpectrumRestricts.cfcHom_eq_restrict`, hence the `ContinuousMap.UniqueHom`
hypothesis. -/
theorem realSpectrumCfcHom_ofReal_comp {a : A} (ha : IsSelfAdjoint a)
    (g : C(spectrum ℝ a, ℝ)) :
    realSpectrumCfcHom ha ((Complex.ofRealCLM : C(ℝ, ℂ)).comp g) = cfcHom ha g := by
  rw [SpectrumRestricts.cfcHom_eq_restrict (R := ℝ) (S := ℂ) (Complex.reCLM : C(ℂ, ℝ))
      ha ha.isStarNormal ha.spectrumRestricts, SpectrumRestricts.starAlgHom_apply,
    realSpectrumCfcHom_apply]
  congr 1

end RealSymbols

end TauCeti
