/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import TauCeti.Analysis.LocallyConvex.Polar

/-!
# The annihilator bundle is the dual of the quotient bundle

Let `D` be a `C^n` distribution of rank `k` on a manifold `M` of dimension `k + r`. Two vector
bundles of rank `r` are attached to it: the annihilator bundle `D⁰ ⊆ T*M` of covectors vanishing on
`D` (`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`), and the quotient bundle `TM ⧸ D`
(`TauCeti.IsContMDiffDistribution.quotientPrebundle`). This file identifies the first with the dual
of the second.

At a point `x`, a covector vanishing on `D x` descends to the quotient `T_x M ⧸ D x`, and every
functional on the quotient arises this way from its composite with the quotient map. This is the
linear equivalence `D⁰_x ≃ (T_x M ⧸ D x)*`
(`TauCeti.CotangentBundle.annihilatorSpaceEquivDualQuotient`), characterized by
`α ↦ ([v] ↦ α v)`, the instance at `D x` of the identification
`StrongDual.polarSubmoduleEquivDualQuotient` of the annihilator of a subspace of a
finite-dimensional topological vector space with the dual of the quotient. Together the fibre
maps are a `C^n` map of total spaces
(`TauCeti.IsContMDiffDistribution.contMDiff_totalSpace_annihilatorSpaceEquivDualQuotient`), so
they assemble to a `C^n` isomorphism of vector bundles

`D⁰ ≅ (TM ⧸ D)*`

(`TauCeti.IsContMDiffDistribution.annihilatorDualQuotientDiffeomorph`), a `C^n` diffeomorphism of
total spaces covering the identity and linear on each fibre, whose inverse composes a functional
on the quotient with the quotient map.

For a contact structure `ξ`, of rank `dim M - 1`, this is the identification `ξ⁰ ≅ L*` of the
annihilator line with the dual of the contact line `L = TM ⧸ ξ`, the line in which the Levi form
takes its values. Under it a local contact form defining `ξ`, a nowhere-zero local section of `ξ⁰`,
becomes a nowhere-zero local section of `L*`.

The smoothness proof tests the fibre maps on a local frame `[V_i]` of `TM ⧸ D`, whose members lift
locally to `C^n` vector fields `V_i` (`TauCeti.IsContMDiffDistribution.exists_contMDiffOn_mk_eq`):
the evaluations are the fibre-linear functions `α ↦ α(V_i)` on `D⁰`, which are `C^n` near the
point (`TauCeti.CotangentBundle.contMDiffAt_annihilatorPairing`).

## Main definitions

* `TauCeti.CotangentBundle.annihilatorSpaceEquivDualQuotient I D x`: the linear equivalence
  `D⁰_x ≃ (T_x M ⧸ D x)*`.
* `TauCeti.IsContMDiffDistribution.annihilatorDualQuotientDiffeomorph`: the `C^n` isomorphism of
  vector bundles `D⁰ ≅ (TM ⧸ D)*`.

## Main results

* `TauCeti.CotangentBundle.annihilatorSpaceEquivDualQuotient_apply_mk`,
  `TauCeti.CotangentBundle.annihilatorSpaceEquivDualQuotient_symm_apply`: the equivalence evaluates
  a covector on representatives, and its inverse composes with the quotient map.
* `TauCeti.IsContMDiffDistribution.contMDiff_totalSpace_annihilatorSpaceEquivDualQuotient`: the
  fibrewise equivalences form a `C^n` map of total spaces `D⁰ → (TM ⧸ D)*`.
* `TauCeti.IsContMDiffDistribution.annihilatorDualQuotientDiffeomorph_apply`,
  `TauCeti.IsContMDiffDistribution.annihilatorDualQuotientDiffeomorph_symm_apply`: the bundle
  isomorphism and its inverse on total spaces.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 1.1 (the annihilator line of a contact structure and coorientations).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (dual bundles and bundle homomorphisms) and Chapter 19 (annihilators of distributions).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

namespace CotangentBundle

/-! ### The fibrewise equivalence -/

section Fibre

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

variable (I D) in
/-- The **identification of the annihilator with the dual of the quotient** at a point `x`: a
covector `α` vanishing on `D x` descends to the functional `[v] ↦ α v` on `T_x M ⧸ D x`, and every
functional on the quotient is obtained from its composite with the quotient map. This is
`StrongDual.polarSubmoduleEquivDualQuotient` for the subspace `D x` of the tangent space. -/
def annihilatorSpaceEquivDualQuotient (x : M) :
    annihilatorSpace I D x ≃L[𝕜] (TangentSpace I x ⧸ D x →L[𝕜] 𝕜) :=
  (ContinuousLinearEquiv.ofEq _ _ (annihilatorSpace_def x)).trans
    (StrongDual.polarSubmoduleEquivDualQuotient (D x))

/-- The functional on `T_x M ⧸ D x` induced by a covector `α ∈ D⁰_x` takes the value `α v` on the
class of `v`. -/
@[simp]
theorem annihilatorSpaceEquivDualQuotient_apply_mk {x : M} (α : annihilatorSpace I D x)
    (v : TangentSpace I x) :
    annihilatorSpaceEquivDualQuotient I D x α (Submodule.Quotient.mk v) =
      (α : TangentSpace I x →L[𝕜] 𝕜) v :=
  StrongDual.polarSubmoduleEquivDualQuotient_apply_mk (D x) _ v

/-- The covector in `D⁰_x` corresponding to a functional `ℓ` on `T_x M ⧸ D x` takes the value
`ℓ [v]` on `v`. -/
@[simp]
theorem annihilatorSpaceEquivDualQuotient_symm_apply {x : M}
    (ℓ : TangentSpace I x ⧸ D x →L[𝕜] 𝕜) (v : TangentSpace I x) :
    ((annihilatorSpaceEquivDualQuotient I D x).symm ℓ : TangentSpace I x →L[𝕜] 𝕜) v =
      ℓ (Submodule.Quotient.mk v) :=
  StrongDual.polarSubmoduleEquivDualQuotient_symm_apply (D x) ℓ v

end Fibre

end CotangentBundle

open CotangentBundle

namespace IsContMDiffDistribution

/-! ### The bundle isomorphism -/

variable [CompleteSpace 𝕜] [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] {n : ℕ∞ω}
  [IsManifold I 1 M] [IsManifold I (n + 1) M] {k r : ℕ}
  (hD : IsContMDiffDistribution I n k D) (hr : k + r = finrank 𝕜 E)

include hD hr in
/-- **The identification `D⁰ ≅ (TM ⧸ D)*` is smooth.** For a `C^n` distribution `D` of rank `k` on
a manifold of dimension `k + r`, the map of total spaces `D⁰ → (TM ⧸ D)*` given on each fibre by
`TauCeti.CotangentBundle.annihilatorSpaceEquivDualQuotient`, `(x, α) ↦ (x, [v] ↦ α v)`, is `C^n`. -/
theorem contMDiff_totalSpace_annihilatorSpaceEquivDualQuotient :
    letI := hD.annihilatorFiberBundle hr
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD.quotientPrebundle hr).toVectorBundle
    ContMDiff (I.prod 𝓘(𝕜, Fin r → 𝕜)) (I.prod 𝓘(𝕜, (Fin r → 𝕜) →L[𝕜] 𝕜)) n
      (fun p : TotalSpace (Fin r → 𝕜) (fun x ↦ annihilatorSpace I D x) ↦
        TotalSpace.mk' ((Fin r → 𝕜) →L[𝕜] 𝕜) (E := fun x ↦ TangentSpace I x ⧸ D x →L[𝕜] 𝕜)
          p.proj (annihilatorSpaceEquivDualQuotient I D p.proj p.snd)) := by
  let := hD.annihilatorFiberBundle hr
  let := (hD.quotientPrebundle hr).totalSpaceTopology
  let := (hD.quotientPrebundle hr).toFiberBundle
  let := (hD.quotientPrebundle hr).toVectorBundle
  have : ContMDiffVectorBundle n (Fin r → 𝕜) (fun x ↦ TangentSpace I x ⧸ D x) I :=
    hD.contMDiffVectorBundle_quotientPrebundle hr
  intro p₀
  let eQ := trivializationAt (Fin r → 𝕜) (fun x ↦ TangentSpace I x ⧸ D x) p₀.proj
  let e𝕜 := Trivial.trivialization M 𝕜
  have : MemTrivializationAtlas e𝕜 := ⟨rfl⟩
  let u : Set (TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x) :=
    TotalSpace.proj ⁻¹' eQ.baseSet
  have hu : IsOpen u := eQ.open_baseSet.preimage (FiberBundle.continuous_proj _ _)
  have hp₀ : p₀ ∈ u := mem_baseSet_trivializationAt _ _ p₀.proj
  -- Test the fibre maps, along the bundle projection, on the local frame of `TM ⧸ D`.
  refine (Manifold.contMDiffOn_hom_of_localFrame (V' := Trivial M 𝕜) (e := eQ) (e' := e𝕜)
    (Pi.basisFun 𝕜 (Fin r)) (contMDiff_proj _).contMDiffOn (fun p hp ↦ ⟨hp, mem_univ _⟩)
    (u := u) fun i p hp ↦ ?_).contMDiffAt (hu.mem_nhds hp₀)
  rw [Bundle.contMDiffWithinAt_totalSpace_iff]
  refine ⟨(contMDiff_proj _ p).contMDiffWithinAt, ?_⟩
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]
  -- The frame vector `[V_i]` of `TM ⧸ D` lifts near `p` to a `C^n` vector field `σ`.
  obtain ⟨U, hU, hpU, -, σ, hσ, hσU⟩ := hD.exists_contMDiffOn_mk_eq hr eQ.open_baseSet
    (eQ.contMDiffOn_localFrame_baseSet (n := n) (Pi.basisFun 𝕜 (Fin r)) i) hp
  have hUp : TotalSpace.proj ⁻¹' U ∈ 𝓝 p :=
    (hU.preimage (FiberBundle.continuous_proj _ _)).mem_nhds hpU
  -- Near `p`, the evaluation on the frame is the pairing of the covector with `σ`.
  refine (contMDiffAt_annihilatorPairing hD hr (hσ.contMDiffAt (hU.mem_nhds hpU))
    ).contMDiffWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hUp] with z hz
    simp [annihilatorPairing_apply, ← hσU z.proj hz]
  · simp [annihilatorPairing_apply, ← hσU p.proj hpU]

/-- **The annihilator bundle is the dual of the quotient bundle.** For a `C^n` distribution `D` of
rank `k` on a manifold of dimension `k + r`, the annihilator bundle `D⁰ ⊆ T*M` is isomorphic to the
dual `(TM ⧸ D)*` of the quotient bundle by the `C^n` diffeomorphism of total spaces
`(x, α) ↦ (x, [v] ↦ α v)`, covering the identity of `M` and linear on each fibre. Its inverse sends
a functional `ℓ` on `T_x M ⧸ D x` to the covector `v ↦ ℓ [v]`.

For a contact structure `ξ` this identifies the annihilator line `ξ⁰` with the dual of the contact
line `TM ⧸ ξ`. -/
def annihilatorDualQuotientDiffeomorph :
    letI := hD.annihilatorFiberBundle hr
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD.quotientPrebundle hr).toVectorBundle
    TotalSpace (Fin r → 𝕜) (fun x ↦ annihilatorSpace I D x) ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin r → 𝕜),
      I.prod 𝓘(𝕜, (Fin r → 𝕜) →L[𝕜] 𝕜)⟯
      TotalSpace ((Fin r → 𝕜) →L[𝕜] 𝕜) (fun x ↦ TangentSpace I x ⧸ D x →L[𝕜] 𝕜) :=
  letI := hD.annihilatorFiberBundle hr
  letI := hD.annihilatorVectorBundle hr
  letI := (hD.quotientPrebundle hr).totalSpaceTopology
  letI := (hD.quotientPrebundle hr).toFiberBundle
  letI := (hD.quotientPrebundle hr).toVectorBundle
  bundleDiffeomorph (annihilatorSpaceEquivDualQuotient I D)
    (hD.contMDiff_totalSpace_annihilatorSpaceEquivDualQuotient hr)

/-- The bundle isomorphism `D⁰ ≅ (TM ⧸ D)*` sends a covector `α ∈ D⁰_x` to the functional
`[v] ↦ α v` over `x`. -/
@[simp]
theorem annihilatorDualQuotientDiffeomorph_apply
    (p : TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x) :
    letI := hD.annihilatorFiberBundle hr
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD.quotientPrebundle hr).toVectorBundle
    hD.annihilatorDualQuotientDiffeomorph hr p =
      ⟨p.proj, annihilatorSpaceEquivDualQuotient I D p.proj p.snd⟩ :=
  letI := hD.annihilatorFiberBundle hr
  letI := hD.annihilatorVectorBundle hr
  letI := (hD.quotientPrebundle hr).totalSpaceTopology
  letI := (hD.quotientPrebundle hr).toFiberBundle
  letI := (hD.quotientPrebundle hr).toVectorBundle
  bundleDiffeomorph_apply _ _ p

/-- The inverse of the bundle isomorphism `D⁰ ≅ (TM ⧸ D)*` sends a functional `ℓ` on
`T_x M ⧸ D x` to the covector `v ↦ ℓ [v]` over `x`. -/
@[simp]
theorem annihilatorDualQuotientDiffeomorph_symm_apply
    (p : TotalSpace ((Fin r → 𝕜) →L[𝕜] 𝕜) fun x ↦ TangentSpace I x ⧸ D x →L[𝕜] 𝕜) :
    letI := hD.annihilatorFiberBundle hr
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD.quotientPrebundle hr).toVectorBundle
    (hD.annihilatorDualQuotientDiffeomorph hr).symm p =
      ⟨p.proj, (annihilatorSpaceEquivDualQuotient I D p.proj).symm p.snd⟩ :=
  letI := hD.annihilatorFiberBundle hr
  letI := hD.annihilatorVectorBundle hr
  letI := (hD.quotientPrebundle hr).totalSpaceTopology
  letI := (hD.quotientPrebundle hr).toFiberBundle
  letI := (hD.quotientPrebundle hr).toVectorBundle
  bundleDiffeomorph_symm_apply _ _ p

end IsContMDiffDistribution

end TauCeti
