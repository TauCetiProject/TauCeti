/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.ContMDiff.Sigma

/-!
# Smooth functions on disjoint unions of manifolds

The `C^n` functions on a disjoint union `Σ i, M i` of manifolds on a common model are the families
of `C^n` functions on the components. Restriction to the component `M i`
(`TauCeti.sigmaRestrict i`) is an algebra homomorphism. It is surjective, since a `C^n` function on
`M i` extends by zero to the other components, and a function is determined by its restrictions to
all components.

## Main declarations

* `TauCeti.sigmaRestrict`: restriction of `C^n` functions to a component, an algebra homomorphism.
* `TauCeti.sigmaRestrict_surjective`: every `C^n` function on a component extends to the disjoint
  union.
* `TauCeti.sigmaRestrict_ext`: two functions with the same restrictions to every component are
  equal.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)] {n : ℕ∞ω}
  {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [ContMDiffRing 𝓘(𝕜, A) n A]

/-- Restriction of `C^n` functions on a disjoint union `Σ i, M i` to the component `M i`, as an
algebra homomorphism. -/
def sigmaRestrict (i : ι) : C^n⟮I, Σ i, M i; 𝓘(𝕜, A), A⟯ →ₐ[𝕜] C^n⟮I, M i; 𝓘(𝕜, A), A⟯ :=
  ContMDiffMap.compRightAlgHom 𝕜 A (⟨Sigma.mk i, contMDiff_sigmaMk i⟩ : C^n⟮I, M i; I, Σ i, M i⟯)

@[simp]
theorem sigmaRestrict_apply (i : ι) (f : C^n⟮I, Σ i, M i; 𝓘(𝕜, A), A⟯) (x : M i) :
    sigmaRestrict i f x = f ⟨i, x⟩ := by
  have h := ContMDiffMap.compRightAlgHom_apply (𝕜 := 𝕜) A
    (⟨Sigma.mk i, contMDiff_sigmaMk i⟩ : C^n⟮I, M i; I, Σ i, M i⟯) f
  exact congr($h x).trans (ContMDiffMap.comp_apply _ _ x)

/-- Every `C^n` function on a component extends, by zero, to a `C^n` function on the disjoint
union. -/
theorem sigmaRestrict_surjective (i : ι) :
    Function.Surjective (sigmaRestrict (I := I) (M := M) (n := n) (A := A) i) := by
  classical
  intro g
  have hext (x : M i) : Function.extend (Sigma.mk i) g 0 ⟨i, x⟩ = g x :=
    sigma_mk_injective.extend_apply _ _ x
  refine ⟨⟨Function.extend (Sigma.mk i) g 0, contMDiff_sigma_iff.2 fun j ↦ ?_⟩,
    ContMDiffMap.ext fun x ↦ (sigmaRestrict_apply i _ x).trans (hext x)⟩
  by_cases hj : j = i
  · subst hj
    exact g.contMDiff.congr hext
  · refine (contMDiff_const (c := (0 : A))).congr fun x ↦ ?_
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨y, hy⟩
    exact hj (congrArg Sigma.fst hy).symm

/-- A `C^n` function on a disjoint union is determined by its restrictions to the components. -/
theorem sigmaRestrict_ext {f g : C^n⟮I, Σ i, M i; 𝓘(𝕜, A), A⟯}
    (h : ∀ i, sigmaRestrict i f = sigmaRestrict i g) : f = g :=
  ContMDiffMap.ext fun ⟨i, x⟩ ↦ by simpa using congr($(h i) x)

end TauCeti
