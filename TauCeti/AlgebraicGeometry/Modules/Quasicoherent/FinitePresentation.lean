/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels

/-!
# Finitely presented approximation on affine schemes

On an affine scheme `X`, let `N` be a quasi-coherent `𝒪_X`-module that is finitely presented over
a quasi-compact open `V ⊆ X`. Then some finitely presented `𝒪_X`-module maps to `N` by a morphism
that is an isomorphism over `V`. Choose a finite-type quasi-coherent submodule `P ⊆ N` that is
all of `N` over `V`, and a surjection `𝒪_X^I ⟶ P` from a free module of finite rank. Its kernel
`K` is of finite type over `V`, because `P` is finitely presented there. A finite-type
quasi-coherent submodule of `K` that is all of `K` over `V` is in turn a quotient of a free
module `𝒪_X^J` of finite rank. The cokernel of the composite `𝒪_X^J ⟶ 𝒪_X^I` is finitely
presented and maps to `P`, isomorphically over `V`.

This is the affine input of the extension of finitely presented modules along quasi-compact
open immersions into quasi-compact quasi-separated schemes.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteType_kernel_of_epi`: the kernel of a surjection from
  a quasi-coherent module of finite type onto a finitely presented module is of finite type.
* `AlgebraicGeometry.Scheme.Modules.exists_isFinitePresentation_isIso_restrict`: the
  finitely presented approximation over a quasi-compact open of an affine scheme.

## References

* The Stacks Project, Section 28.23, the affine input of Lemmas 28.23.4 (Tag 01PI) and 28.23.5
  (Tag 0G41).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The kernel of an epimorphism from a quasi-coherent module of finite type onto a finitely
presented module is of finite type. -/
theorem isFiniteType_kernel_of_epi {M N : X.Modules} (π : M ⟶ N) [Epi π] [M.IsQuasicoherent]
    [M.IsFiniteType] [N.IsFinitePresentation] : (kernel π).IsFiniteType := by
  have : N.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation N
  refine isFiniteType_of_finite_sections _ fun U hU ↦ ?_
  have := M.finite_sections_of_isAffineOpen U hU
  have := N.finitePresentation_sections_of_isAffineOpen U hU
  let f : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) := ((sectionsFunctor U).map π).hom
  -- `f` is `π.app U` with its linear structure; the surjectivity statement uses the latter.
  have hker := Module.FinitePresentation.fg_ker f
    (by exact Hom.app_surjective_of_epi_of_isAffineOpen π U hU)
  -- Sections are the forgetful functor to presheaves followed by evaluation; instance search
  -- does not see through the definition of `sectionsFunctor`.
  let E := sectionsFunctor U
  have : PreservesFiniteLimits E := inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.evaluation _ (Opposite.op U)))
  let e : Γ(kernel π, U) ≃ₗ[Γ(X, U)] LinearMap.ker f :=
    ((PreservesKernel.iso E π) ≪≫ ModuleCat.kernelIsoKer _).toLinearEquiv
  have : Module.Finite Γ(X, U) (LinearMap.ker f) := Module.Finite.iff_fg.mpr hker
  exact Module.Finite.equiv e.symm

/-- **Finitely presented approximation on an affine scheme.** On an affine scheme `X`, let `N` be
a quasi-coherent module that is finitely presented over a quasi-compact open `V`. Then there is a
morphism `N' ⟶ N` from a finitely presented module that is an isomorphism over `V`. -/
theorem exists_isFinitePresentation_isIso_restrict [IsAffine X] {N : X.Modules}
    [N.IsQuasicoherent] (V : X.Opens) (hV : IsCompact (V : Set X))
    [(N.restrict V.ι).IsFinitePresentation] :
    ∃ (N' : X.Modules) (_ : N'.IsFinitePresentation) (i : N' ⟶ N),
      IsIso ((restrictFunctor V.ι).map i) := by
  let R := restrictFunctor V.ι
  have : (N.restrict V.ι).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (N.restrict V.ι)
  -- A finite-type submodule `P ⊆ N` that is everything over `V`, and generators `𝒪_X^I ⟶ P`.
  obtain ⟨P, _, _, a, _, ha⟩ := exists_isFiniteType_mono_isIso_restrict (N := N) V hV
  have := P.finite_sections_of_isAffineOpen ⊤ (isAffineOpen_top X)
  obtain ⟨I, _, π₀, hπ₀⟩ := exists_epi_free_of_finite P
  let F : X.Modules := SheafOfModules.free I
  let π : F ⟶ P := π₀
  have : Epi π := hπ₀
  have : F.IsFinitePresentation :=
    inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf) I).IsFinitePresentation
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : (R.obj F).IsQuasicoherent := isQuasicoherent_restrictFunctor _ _
  -- The kernel `K` of `π` is of finite type over `V`, where `P` is finitely presented.
  have : (P.restrict V.ι).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation V.toScheme.ringCatSheaf).prop_of_iso
      (asIso (R.map a)).symm inferInstance
  have : Epi (R.map π) := inferInstance
  have : (kernel (R.map π)).IsFiniteType := isFiniteType_kernel_of_epi (R.map π)
  have : ((kernel π).restrict V.ι).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (R := V.toScheme.ringCatSheaf)
      (PreservesKernel.iso R π).symm
  -- A finite-type submodule of `K` that is everything over `V`, and generators `𝒪_X^J ⟶ K`.
  obtain ⟨K, _, _, b, _, hb⟩ := exists_isFiniteType_mono_isIso_restrict (N := kernel π) V hV
  have := K.finite_sections_of_isAffineOpen ⊤ (isAffineOpen_top X)
  obtain ⟨J, _, σ₀, hσ₀⟩ := exists_epi_free_of_finite K
  let G : X.Modules := SheafOfModules.free J
  let σ : G ⟶ K := σ₀
  have : Epi σ := hσ₀
  -- The cokernel of `f : 𝒪_X^J ⟶ 𝒪_X^I` is finitely presented and maps to `P`.
  let f := σ ≫ b ≫ kernel.ι π
  let Pr := SheafOfModules.presentationOfIsCokernelFree f (cokernel.π f) (cokernel.condition f)
    (cokernelIsCokernel f)
  have : Pr.IsFinite := ⟨⟨(inferInstance : Finite I)⟩, ⟨(inferInstance : Finite J)⟩⟩
  have : (cokernel f).IsFinitePresentation := Pr.isFinitePresentation
  let g : cokernel f ⟶ P := cokernel.desc f π (by
    rw [Category.assoc, Category.assoc, kernel.condition, comp_zero, comp_zero])
  refine ⟨cokernel f, this, g ≫ a, ?_⟩
  -- Over `V`, `R.map π` is a cokernel of `R.map f` since `R.map (σ ≫ b)` is an epimorphism onto
  -- the kernel of `R.map π`; so `R.map g` compares two cokernels of `R.map f`.
  have : IsIso (R.map g) := by
    have : IsIso (R.map b) := hb
    have hK := (KernelFork.ofι (kernel.ι π) (kernel.condition π)).mapIsLimit (kernelIsKernel π) R
    have hP := isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ hK) (R.map σ ≫ R.map b)
      (h := R.map f) (by simp [f, Category.assoc])
    have hQ := (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)).mapIsColimit
      (cokernelIsCokernel f) R
    have : (hQ.coconePointUniqueUpToIso hP).hom = R.map g := by
      refine Cofork.IsColimit.hom_ext hQ ?_
      have h := IsColimit.comp_coconePointUniqueUpToIso_hom hQ hP WalkingParallelPair.one
      refine h.trans ?_
      simp [g, ← R.map_comp]
    rw [← this]
    infer_instance
  rw [Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
