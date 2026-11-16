/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Kernel
public import TauCeti.Algebra.Homology.Curved.Module.Right.Cokernel
public import TauCeti.Algebra.Homology.Curved.Module.Right.Biproduct
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# The closed category of curved right modules is abelian

Kernels and cokernels carry their inherited differentials. The faithful graded forgetful
functor preserves these constructions and reflects isomorphisms. The coimage-to-image
comparison in the closed category is an isomorphism, as detected in the abelian graded module
category. This characterizes the abelian structure on the closed category of curved modules.

The graded forgetful functor preserves finite limits and colimits. This ambient abelian
category and its forgetful functor support the graded-split exact structure on curved modules.

## References

* The Tau Ceti contributors, `TauCeti.Algebra.Category.GradedModuleCat.Abelian`.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed category keeps the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The closed category's coimage-to-image comparison is an isomorphism. -/
noncomputable instance
    {M N : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)}
    (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  have := IsIso.of_isIso_fac_right
    (Abelian.PreservesCoimage.hom_coimageImageComparison (forgetDifferential (h := h)) f).symm
  exact isIso_of_reflects_iso _ (forgetDifferential (h := h))

/-- The closed category of curved right modules is abelian, as detected by graded modules. -/
noncomputable instance instAbelianClosedCategory : Abelian
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  Abelian.ofCoimageImageComparisonIsIso

/-- The graded forgetful functor preserves finite limits of closed curved-module diagrams. -/
noncomputable instance : PreservesFiniteLimits (forgetDifferential (h := h)) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The graded forgetful functor preserves finite colimits of closed curved-module diagrams. -/
noncomputable instance : PreservesFiniteColimits (forgetDifferential (h := h)) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- A short complex in the closed category of curved right modules is short exact if and only if
its underlying maps form an exact sequence with injective first map and surjective second map. -/
theorem shortExact_iff
    (S : ShortComplex
      (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))) :
    S.ShortExact ↔
      Function.Injective (closedHom S.f) ∧ Function.Surjective (closedHom S.g) ∧
        Function.Exact (closedHom S.f) (closedHom S.g) := by
  let F := forgetDifferential (h := h)
  constructor
  · intro hS
    have hSF := hS.map_of_exact F
    exact ⟨(GradedModuleCat.mono_iff_injective _).1 hSF.mono_f,
      (GradedModuleCat.epi_iff_surjective _).1 hSF.epi_g,
      GradedModuleCat.exact_iff.1 hSF.exact⟩
  · rintro ⟨hf, hg, hex⟩
    have hSF : (S.map F).ShortExact :=
      { exact := GradedModuleCat.exact_iff.mpr hex
        mono_f := (GradedModuleCat.mono_iff_injective _).mpr hf
        epi_g := (GradedModuleCat.epi_iff_surjective _).mpr hg }
    let : ReflectsLimit (parallelPair S.g 0) F := reflectsLimit_of_reflectsIsomorphisms _ _
    let : ReflectsColimit (parallelPair S.f 0) F := reflectsColimit_of_reflectsIsomorphisms _ _
    have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
      isLimitOfReflects F ((isLimitMapConeForkEquiv' F S.zero).symm hSF.fIsKernel)
    have hCoker : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
      isColimitOfReflects F ((isColimitMapCoconeCoforkEquiv' F S.zero).symm hSF.gIsCokernel)
    have hExactMono := (S.exact_and_mono_f_iff_f_is_kernel).2 ⟨hKer⟩
    have hExactEpi := (S.exact_and_epi_g_iff_g_is_cokernel).2 ⟨hCoker⟩
    exact ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 hExactEpi.2

/-- A surjective closed morphism together with its canonical kernel inclusion forms a short exact
sequence in the closed category of curved right modules. -/
theorem shortExact_kernel_of_surjective {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (p : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)
    (hp : Function.Surjective (closedHom p)) :
    (ShortComplex.mk (kernelι p) p (kernelι_comp p)).ShortExact := by
  refine (shortExact_iff _).2 ⟨?_, hp, ?_⟩
  · intro x₁ x₂ hx
    dsimp only [ShortComplex.mk] at hx
    rw [hom_kernelι] at hx
    exact (kernelEquiv p).injective (Subtype.ext hx)
  · intro x
    dsimp only [ShortComplex.mk]
    rw [hom_kernelι]
    constructor
    · intro hx
      exact ⟨(kernelEquiv p).symm ⟨x, hx⟩, by simp⟩
    · rintro ⟨y, rfl⟩
      exact (kernelEquiv p y).2

end TauCeti.CurvedDGRightModuleCat
