/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem

/-!
# The orientation local system of the negative normal bundle

Let `i : S → M` be a nondegenerate critical submanifold of a function `f` on a boundaryless
manifold, of constant Morse index `r`, and let `g` be a `C^k` fibre metric on its normal bundle.
The metric selects the negative normal spaces `ν⁻_g`, on which the normal Hessian is negative
definite, and these form a vector bundle of rank `r` over `S`, the negative normal bundle
(`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_negativeNormalSpace`, in
the namespace `TauCeti.SmoothEmbedding`). Crossing the critical level of `S` attaches its disc
bundle, and the relative homology across the level is the homology of `S` shifted by `r` and
twisted by the orientation local system `o(ν⁻_g)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`).

The subspaces `ν⁻_g` depend on `g`, but this file shows that the twisting coefficients do not. For
a second `C^k` fibre metric `g'`, projecting along the positive normal spaces of `g` is a
fibrewise linear isomorphism `ν⁻_{g'} ≃ ν⁻_g` which is continuous on total spaces
(`IsNondegenerateCriticalSubmanifold.continuous_negativeNormalSpaceEquiv`), and isomorphic
bundles have isomorphic orientation local systems
(`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise`). So
`o(ν⁻_g) ≅ o(ν⁻_{g'})` (`negativeNormalSpaceSignLocalSystemIso`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`), and homology or cohomology with
coefficients in the orientation local system of the negative normal bundle does not depend on the
fibre metric. Likewise, the negative normal bundle relative to `g` is orientable if and only if
the one relative to `g'` is
(`nonempty_vectorBundleOrientation_negativeNormalSpace_iff`), so whether the untwisted
identification of the homology across the level applies is independent of the metric too.

The computation of the homology across a level gives the negative normal spaces the bundle
structures of arbitrary local frames, not only those of the smooth frames above. For any such
frames, the homology of `S` with coefficients in `o(ν⁻_g)` and in `o(ν⁻_{g'})` is the same,
`Hₚ(S; o(ν⁻_g) ⊗ R) ≅ Hₚ(S; o(ν⁻_{g'}) ⊗ R)`, in every degree and over every ring `R`, `ℤ`
included (`negativeNormalSpaceTwistedHomologyIso`).

## Main definitions

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `negativeNormalSpaceSignLocalSystemIso`: the isomorphism between the orientation local systems
  of the negative normal bundles of two fibre metrics.
* `negativeNormalSpaceTwistedHomologyIso`: the isomorphism between the homologies of `S` with
  coefficients in these orientation local systems, over every ring, for any local frames.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `negativeNormalSpaceSignLocalSystemIso_def`: the isomorphism of orientation local systems is the
  one induced by projecting along the positive normal spaces of `g`.
* `nonempty_vectorBundleOrientation_negativeNormalSpace_iff`: the negative normal bundles of two
  fibre metrics are orientable together.
* `negativeNormalSpaceTwistedHomologyIso_hom`: the isomorphism of twisted homologies is the map
  induced by projecting along the positive normal spaces of `g`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover and twisted coefficients).
-/

public section

open Bundle Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

universe u

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {k : ℕ∞ω} [IsManifold I (k + 2) M] [IsManifold J (k + 1) S]

variable (R : Type u) [Ring R]

/-- **The orientation local system of the negative normal bundle does not depend on the fibre
metric.** Let `i` be a nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along
it, `i` of class `C^{k+1}` and Morse index `r` at every point, and let `g` and `g'` be two `C^k`
fibre metrics on its normal bundle. The orientation local systems of the negative normal bundles
relative to `g` and to `g'` are isomorphic: projecting along the positive normal spaces of `g` is
an isomorphism of these vector bundles, which transports orientations of fibres. -/
def negativeNormalSpaceSignLocalSystemIso
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g g' : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr).fiberBundle
    haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g
      hr).vectorBundle
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g' hr).fiberBundle
    haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g'
      hr).vectorBundle
    VectorBundleOrientationCover.signLocalSystem (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) R
        (ι := Fin r) (by simp) ≅
      VectorBundleOrientationCover.signLocalSystem (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g'.toRiemannianMetric s) R
        (ι := Fin r) (by simp) :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr).fiberBundle
  haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g
    hr).vectorBundle
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
  letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g' hr).fiberBundle
  haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g'
    hr).vectorBundle
  VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise R (F := Fin r → ℝ)
    (F' := Fin r → ℝ) (ι := Fin r) (φ := fun s ↦ (h.negativeNormalSpaceEquiv hn
      g'.toRiemannianMetric g.toRiemannianMetric s).toContinuousLinearEquiv) (by simp) (by simp)
    (h.continuous_negativeNormalSpaceEquiv hn hk hf hdim g g' hr)

/-- The isomorphism between the orientation local systems of the negative normal bundles of two
fibre metrics is the one induced by projecting along the positive normal spaces of `g`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise`). -/
@[simp]
theorem negativeNormalSpaceSignLocalSystemIso_def
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g g' : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr).fiberBundle
    haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g
      hr).vectorBundle
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g' hr).fiberBundle
    haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g'
      hr).vectorBundle
    h.negativeNormalSpaceSignLocalSystemIso hn R hk hf hdim g g' hr =
      VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise R (F := Fin r → ℝ)
        (F' := Fin r → ℝ) (ι := Fin r) (φ := fun s ↦ (h.negativeNormalSpaceEquiv hn
          g'.toRiemannianMetric g.toRiemannianMetric s).toContinuousLinearEquiv) (by simp) (by simp)
        (h.continuous_negativeNormalSpaceEquiv hn hk hf hdim g g' hr) :=
  (rfl)

/-- **The negative normal bundles of two fibre metrics are orientable together.** In the setting of
`negativeNormalSpaceSignLocalSystemIso`, the negative normal bundle relative to `g` is orientable
if and only if the one relative to `g'` is. -/
theorem nonempty_vectorBundleOrientation_negativeNormalSpace_iff
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g g' : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr).fiberBundle
    haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g
      hr).vectorBundle
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g' hr).fiberBundle
    haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g'
      hr).vectorBundle
    Nonempty (VectorBundleOrientation (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) (Fin r)) ↔
      Nonempty (VectorBundleOrientation (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g'.toRiemannianMetric s) (Fin r)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr).fiberBundle
  have := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g
    hr).vectorBundle
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
  let := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g' hr).fiberBundle
  have := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g'
    hr).vectorBundle
  exact VectorBundleOrientation.nonempty_iff_of_fiberwise (F := Fin r → ℝ) (F' := Fin r → ℝ)
    (φ := fun s ↦ (h.negativeNormalSpaceEquiv hn g.toRiemannianMetric
      g'.toRiemannianMetric s).toContinuousLinearEquiv) (by simp)
    (h.continuous_negativeNormalSpaceEquiv hn hk hf hdim g' g hr)

open CategoryTheory LocalCoefficientSystem in
/-- **The twisted homology of a Morse–Bott submanifold does not depend on the fibre metric.** In
the setting of `negativeNormalSpaceSignLocalSystemIso`, give the negative normal spaces relative to
`g` and to `g'` the vector bundle structures of any local frames `hV` and `hV'`. Then the homology
of `S` with coefficients in the orientation local systems of the two negative normal bundles is the
same, `Hₚ(S; o(ν⁻_g) ⊗ R) ≅ Hₚ(S; o(ν⁻_{g'}) ⊗ R)`, in every degree `p` and over every ring `R`,
`ℤ` included: projecting along the positive normal spaces of `g` identifies the two negative normal
bundles, hence their orientation local systems. -/
def negativeNormalSpaceTwistedHomologyIso
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g g' : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
    (hV : haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
      haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric))
    (hV' : haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
      haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g'.toRiemannianMetric))
    (p : ℕ) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    haveI := hV.vectorBundle
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
    letI := hV'.fiberBundle
    haveI := hV'.vectorBundle
    twistedHomology (VectorBundleOrientationCover.signLocalSystem (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) R (ι := Fin r) (by simp)) p ≅
      twistedHomology (VectorBundleOrientationCover.signLocalSystem (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g'.toRiemannianMetric s) R (ι := Fin r) (by simp))
          p :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  letI := hV.fiberBundle
  haveI := hV.vectorBundle
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
  letI := hV'.fiberBundle
  haveI := hV'.vectorBundle
  asIso (twistedHomologyCoefficientMap
    (VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise R _ _
      (φ := fun s ↦ (h.negativeNormalSpaceEquiv hn g'.toRiemannianMetric
        g.toRiemannianMetric s).toContinuousLinearEquiv)
    (h.continuous_negativeNormalSpaceEquiv hn hk hf hdim g g'
      (h.manifoldMorseIndex_eq_of_hasLocalSubbundleFrames hn _ hV))).hom p)

open CategoryTheory LocalCoefficientSystem in
/-- The isomorphism between the homologies of `S` with coefficients in the orientation local
systems of the negative normal bundles of two fibre metrics is the map induced by projecting along
the positive normal spaces of `g`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise`). -/
theorem negativeNormalSpaceTwistedHomologyIso_hom
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g g' : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
    (hV : haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
      haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric))
    (hV' : haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
      haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g'.toRiemannianMetric))
    (p : ℕ) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    haveI := hV.vectorBundle
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
    letI := hV'.fiberBundle
    haveI := hV'.vectorBundle
    (h.negativeNormalSpaceTwistedHomologyIso hn R hk hf hdim g g' hV hV' p).hom =
      twistedHomologyCoefficientMap
        (VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise R _ _
          (φ := fun s ↦ (h.negativeNormalSpaceEquiv hn g'.toRiemannianMetric
            g.toRiemannianMetric s).toContinuousLinearEquiv)
        (h.continuous_negativeNormalSpaceEquiv hn hk hf hdim g g'
          (h.manifoldMorseIndex_eq_of_hasLocalSubbundleFrames hn _ hV))).hom p :=
  (rfl)

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
