/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels

/-!
# Extending quasi-coherent modules along quasi-compact open immersions

Let `j : U ⟶ X` be a quasi-compact open immersion. Every quasi-coherent `𝒪_U`-module `F` is the
restriction of a quasi-coherent `𝒪_X`-module, namely of `j_* F`: an open immersion is separated,
hence quasi-separated, so `j_* F` is quasi-coherent, and the counit `j^* j_* F ⟶ F` of the
restriction--pushforward adjunction is an isomorphism. Likewise every quasi-coherent submodule
`F ⊆ j^* G` of the restriction of a quasi-coherent `G` is the restriction of a quasi-coherent
submodule of `G`: the kernel of `G ⟶ j_* j^* G ⟶ j_* (j^* G / F)`. This extension changes
nothing away from where `F` is a proper submodule: on an open `V ⊆ X` over whose preimage `F` is
all of `j^* G`, the extension is all of `G`, because `j_* (j^* G / F)` vanishes on `V`.

Submodules are monomorphisms in the abelian category of `𝒪_X`-modules.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_restrict_iso`: every quasi-coherent
  module on `U` is the restriction of a quasi-coherent module on `X`.
* `AlgebraicGeometry.Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent`: every
  quasi-coherent submodule of `j^* G` is the restriction of a quasi-coherent submodule of `G`.

## References

* The Stacks Project, Lemma 28.23.1 (Tag 01PE).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Extension of quasi-coherent modules.** Along a quasi-compact open immersion `j : U ⟶ X`,
every quasi-coherent `𝒪_U`-module `F` is `j^* G` for a quasi-coherent `𝒪_X`-module `G`, namely
`G = j_* F`. Stacks, Lemma 28.23.1 (01PE), part (1). -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_restrict_iso
    [QuasiCompact j] (F : U.Modules) [F.IsQuasicoherent] :
    ∃ (G : X.Modules) (_ : G.IsQuasicoherent), Nonempty (G.restrict j ≅ F) :=
  ⟨_, inferInstance, ⟨(Scheme.Modules.restrictFunctorAdjCounitIso j).app F⟩⟩

/-- **Extension of quasi-coherent submodules.** Along a quasi-compact open immersion
`j : U ⟶ X`, let `G` be a quasi-coherent `𝒪_X`-module and `i : F ⟶ j^* G` a quasi-coherent
submodule. Then `F` is the restriction of a quasi-coherent submodule `i' : G' ⟶ G`: there is an
isomorphism `j^* G' ≅ F` carrying `j^* i'` to `i`. The module `G'` is the kernel of the
composite `G ⟶ j_* j^* G ⟶ j_* (j^* G / F)`. Moreover `i'` is an isomorphism over every open
`V ⊆ X` such that `i` is an isomorphism over `j⁻¹ V`. Stacks, Lemma 28.23.1 (01PE), part (2). -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent
    [QuasiCompact j] {G : X.Modules} [G.IsQuasicoherent] {F : U.Modules} [F.IsQuasicoherent]
    (i : F ⟶ G.restrict j) [Mono i] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (i' : G' ⟶ G) (_ : Mono i')
      (e : G'.restrict j ≅ F), (Scheme.Modules.restrictFunctor j).map i' = e.hom ≫ i ∧
        ∀ V : X.Opens, IsIso ((Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V).ι).map i) →
          IsIso ((Scheme.Modules.restrictFunctor V.ι).map i') := by
  let R := Scheme.Modules.restrictFunctor j
  let adj := Scheme.Modules.restrictAdjunction j
  let φ : G ⟶ (Scheme.Modules.pushforward j).obj (cokernel i) :=
    adj.homEquiv _ _ (cokernel.π i)
  -- On `U`, `φ` is the cokernel projection of `i` followed by the inverse counit.
  have hφ : R.map φ = cokernel.π i ≫ inv (adj.counit.app (cokernel i)) := by
    rw [IsIso.eq_comp_inv, ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  have hi : IsLimit (KernelFork.ofι i (by rw [hφ, cokernel.condition_assoc, zero_comp]) :
      KernelFork (R.map φ)) :=
    isKernelCompMono (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)) _ hφ
  -- `j^*` preserves the kernel of `φ`, which is therefore carried to `i`.
  let e : (kernel φ).restrict j ≅ F :=
    PreservesKernel.iso R φ ≪≫ (kernelIsKernel (R.map φ)).conePointUniqueUpToIso hi
  refine ⟨kernel φ, inferInstance, kernel.ι φ, inferInstance, e, ?_, fun V hV ↦ ?_⟩
  · have h : ((kernelIsKernel (R.map φ)).conePointUniqueUpToIso hi).hom ≫ i = kernel.ι _ :=
      (kernelIsKernel (R.map φ)).conePointUniqueUpToIso_hom_comp hi WalkingParallelPair.zero
    simp [e, h, R]
  -- Over `j⁻¹ V` the cokernel of `i` vanishes, hence so does `j_* (cokernel i)` over `V`.
  let R' := Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V).ι
  let RV := Scheme.Modules.restrictFunctor V.ι
  have hQ : IsZero ((cokernel i).restrict (j ⁻¹ᵁ V).ι) :=
    (isZero_cokernel_of_epi (R'.map i)).of_iso (PreservesCokernel.iso R' i)
  have hP : IsZero (((Scheme.Modules.pushforward j).obj (cokernel i)).restrict V.ι) :=
    ((Scheme.Modules.pushforward (j ∣_ V)).map_isZero hQ).of_iso
      ((restrictPushforwardIso j V).app (cokernel i))
  have := kernel.ι_of_zero (hP.eq_of_tgt (RV.map φ) 0)
  rw [← kernelComparison_comp_ι φ RV, ← PreservesKernel.iso_hom]
  infer_instance

end TauCeti.AlgebraicGeometry
