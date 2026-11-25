/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Quotient

/-!
# The quotient of the tangent bundle by a distribution

Let `D` be a `C^n` distribution of rank `k` on a manifold `M` of dimension `k + r`, modelled on a
finite-dimensional space over a complete field, and with `C^(n+1)` transition maps. The quotient
spaces `T_x M ⧸ D x`, each with its quotient topology, form a `C^n` vector bundle `TM ⧸ D` of rank
`r` (`TauCeti.IsContMDiffDistribution.contMDiffVectorBundle_quotientPrebundle`), whose local
trivializations are given by vector fields completing local frames of `D` to local frames of the
tangent bundle. The quotient map `TM → TM ⧸ D`, `(x, v) ↦ (x, [v])`, is `C^n`
(`TauCeti.IsContMDiffDistribution.contMDiff_totalSpace_mkQ`); on each fibre it is the quotient map
`Submodule.mkQ`, surjective with kernel `D x`. Every `C^n` section of `TM ⧸ D` is locally the
class of a `C^n` vector field (`TauCeti.IsContMDiffDistribution.exists_contMDiffOn_mk_eq`).

For a hyperplane field `ξ`, of rank `dim M - 1`, this is the line bundle `TM ⧸ ξ`; when `ξ` is a
contact structure it is the contact line, in which the Levi form of `ξ`
(`TauCeti.distributionLeviForm`) takes its values. The construction is the specialization to the
tangent bundle of the quotient of a vector bundle by a subbundle with local frames,
`TauCeti.HasLocalContMDiffSubbundleFrames.quotientPrebundle`.

## Main definitions

* `TauCeti.IsContMDiffDistribution.quotientPrebundle`: the quotient bundle `TM ⧸ D`, as a vector
  prebundle with model fibre `Fin r → 𝕜`.

## Main results

* `TauCeti.IsContMDiffDistribution.mem_pretrivializationAtlas_quotientPrebundle_iff`: the
  pretrivializations of `TM ⧸ D` are those of its `C^n` local frames.
* `TauCeti.IsContMDiffDistribution.contMDiffVectorBundle_quotientPrebundle`: `TM ⧸ D` is a `C^n`
  vector bundle.
* `trivializationOfMemPretrivializationAtlas_quotientPrebundle_apply`, in the namespace
  `TauCeti.IsContMDiffDistribution`: the trivializations of `TM ⧸ D` send a class to its
  coordinates in the corresponding frame.
* `TauCeti.IsContMDiffDistribution.contMDiff_totalSpace_mkQ`: the quotient map `TM → TM ⧸ D` is
  `C^n`.
* `TauCeti.IsContMDiffDistribution.exists_contMDiffOn_mk_eq`: `C^n` sections of `TM ⧸ D` lift
  locally to `C^n` vector fields.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (subbundles and local frames) and Chapter 19 (distributions).
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.IsContMDiffDistribution

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : ℕ∞ω}
  [IsManifold I (n + 1) M] {k r : ℕ} {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}
  (hD : IsContMDiffDistribution I n k D) (hr : k + r = finrank 𝕜 E)

/-- **The quotient bundle `TM ⧸ D`** of a `C^n` distribution `D` of rank `k` on a manifold of
dimension `k + r`: the quotients `T_x M ⧸ D x`, with their quotient topologies, form a vector
prebundle with model fibre `Fin r → 𝕜`. Its pretrivializations are those of the `C^n` local
frames of `TM ⧸ D` (`TauCeti.IsQuotientFrameOn`). Install the total-space topology
`(hD.quotientPrebundle hr).totalSpaceTopology` and the fibre bundle structure
`(hD.quotientPrebundle hr).toFiberBundle` with `letI`. -/
def quotientPrebundle : VectorPrebundle 𝕜 (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.quotientPrebundle (by simpa using hr)

/-- The pretrivializations of the quotient bundle `TM ⧸ D` are those of the `C^n` local frames of
`TM ⧸ D` on open sets. -/
theorem mem_pretrivializationAtlas_quotientPrebundle_iff
    (e : Pretrivialization (Fin r → 𝕜) (π (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x)) :
    e ∈ (hD.quotientPrebundle hr).pretrivializationAtlas ↔
      ∃ (U : Set M) (hU : IsOpen U) (Y : Fin r → Π x : M, TangentSpace I x)
        (hY : IsQuotientFrameOn D Y U), (∀ j, CMDiff[U] n (T% (Y j))) ∧
          hY.pretrivialization hU = e :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.mem_pretrivializationAtlas_quotientPrebundle_iff
    (by simpa using hr) e

/-- **The quotient of the tangent bundle by a `C^n` distribution is a `C^n` vector bundle.** -/
theorem contMDiffVectorBundle_quotientPrebundle :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD.quotientPrebundle hr).toVectorBundle
    ContMDiffVectorBundle n (Fin r → 𝕜) (fun x ↦ TangentSpace I x ⧸ D x) I :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.contMDiffVectorBundle_quotientPrebundle (by simpa using hr)

/-- In the quotient bundle `TM ⧸ D`, the trivialization given by a local frame `Y` of `TM ⧸ D` on
an open set `U` whose pretrivialization lies in the atlas sends a class over a point of `U` to its
coordinates in the frame. -/
theorem trivializationOfMemPretrivializationAtlas_quotientPrebundle_apply
    {Y : Fin r → Π x : M, TangentSpace I x} {U : Set M} {hY : IsQuotientFrameOn D Y U}
    {hU : IsOpen U}
    (he : hY.pretrivialization hU ∈ (hD.quotientPrebundle hr).pretrivializationAtlas)
    {p : TotalSpace (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x} (hp : p.proj ∈ U) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    (hD.quotientPrebundle hr).trivializationOfMemPretrivializationAtlas he p =
      (p.proj, (hY.basis hp).equivFun p.snd) :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  have hV := hD.hasLocalContMDiffSubbundleFrames
  hV.trivializationOfMemPretrivializationAtlas_quotientPrebundle_apply (by simpa using hr) he hp

/-- **The quotient map `TM → TM ⧸ D` is `C^n`.** -/
theorem contMDiff_totalSpace_mkQ :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    ContMDiff (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, Fin r → 𝕜)) n
      (fun v : TangentBundle I M ↦
        (⟨v.proj, Submodule.Quotient.mk v.snd⟩ : TotalSpace (Fin r → 𝕜)
          fun x ↦ TangentSpace I x ⧸ D x)) :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_mkQ (by simpa using hr)

/-- **Sections of `TM ⧸ D` lift locally to vector fields.** A `C^n` section of `TM ⧸ D` on an
open set `W` is, near every point of `W`, the class of a `C^n` vector field. -/
theorem exists_contMDiffOn_mk_eq {W : Set M} (hW : IsOpen W)
    {s : Π x : M, TangentSpace I x ⧸ D x}
    (hs : letI := (hD.quotientPrebundle hr).totalSpaceTopology
      letI := (hD.quotientPrebundle hr).toFiberBundle
      ContMDiffOn I (I.prod 𝓘(𝕜, Fin r → 𝕜)) n
        (fun x ↦ TotalSpace.mk' (Fin r → 𝕜) (E := fun x ↦ TangentSpace I x ⧸ D x) x (s x)) W)
    {x₀ : M} (hx₀ : x₀ ∈ W) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧ ∃ σ : (Π x : M, TangentSpace I x),
      CMDiff[U] n (T% σ) ∧ ∀ x ∈ U, Submodule.Quotient.mk (σ x) = s x :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.exists_contMDiffOn_mk_eq (by simpa using hr) hW hs hx₀

end TauCeti.IsContMDiffDistribution
