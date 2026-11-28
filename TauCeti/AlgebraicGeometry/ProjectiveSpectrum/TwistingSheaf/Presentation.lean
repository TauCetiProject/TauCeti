/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalGeneration
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation

/-!
# Finite presentations by twisting sheaves on `Proj`

On a compact, locally Noetherian projective spectrum `Proj 𝒜` covered by degree-one standard opens
`D₊(f i)` (in particular on `Proj (Sym_R M)` for a finite module `M` over a Noetherian ring `R`),
Serre's global generation theorem presents any quasi-coherent sheaf `F` of finite type as a
quotient of `𝒪^{⊕I} ⊗ 𝒪(-r)` for all sufficiently large `r`
(`AlgebraicGeometry.Proj.eventually_exists_epi_free_tensor_twistingSheaf`). Since
`𝒪^{⊕I} ⊗ 𝒪(-r)` is finitely presented on `Proj 𝒜` and the category of finitely presented
modules is abelian on a locally Noetherian scheme
(`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_kernel`), the kernel of such an
epimorphism is again finitely presented (hence quasi-coherent of finite type).

## Main results

* `AlgebraicGeometry.Proj.eventually_exists_epi_free_tensor_twistingSheaf_kernel`: for all
  sufficiently large `r`, `F` receives an epimorphism from `𝒪^{⊕I} ⊗ 𝒪(-r)` with finite `I` whose
  kernel is finitely presented.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TauCeti
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- On `Proj 𝒜` (when compact, locally Noetherian, and covered by degree-one standard opens), any
finite-type quasi-coherent sheaf `F` admits, for all sufficiently large `r`, an epimorphism
`𝒪^{⊕I} ⊗ 𝒪(-r) ⟶ F` with finite `I` whose kernel is finitely presented. -/
theorem eventually_exists_epi_free_tensor_twistingSheaf_kernel
    [CompactSpace (Proj 𝒜)] [IsLocallyNoetherian (Proj 𝒜)]
    {ι : Type*} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1) (hcover : ⨆ i, basicOpen 𝒜 (f i) = ⊤)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∀ᶠ r : ℕ in Filter.atTop, ∃ (I : Type u) (_ : Finite I)
      (π : ((SheafOfModules.free I : (Proj 𝒜).Modules) ⊗ twistingSheaf 𝒜 (-(r : ℤ)) :
        (Proj 𝒜).Modules) ⟶ F),
      Epi π ∧ (kernel π).IsFinitePresentation := by
  have hf' (a : Set.range f) : (a : A) ∈ 𝒜 1 := by
    obtain ⟨_, i, rfl⟩ := a
    exact hf i
  have hcover' : ⨆ a : Set.range f, basicOpen 𝒜 (a : A) = ⊤ :=
    (iSup_range' (basicOpen 𝒜) f).trans hcover
  filter_upwards [eventually_exists_epi_free_tensor_twistingSheaf f hf hcover F]
    with r ⟨I, hI, π, hπ⟩
  have : Epi π := hπ
  have := isInvertible_twistingSheaf_of_iSup_eq_top _ hf' hcover' (-(r : ℤ))
  -- `SheafOfModules.free I` has syntactic type `SheafOfModules (Proj 𝒜).ringCatSheaf` while
  -- `Scheme.Modules` is semireducible, so `inferInstance` at reducible transparency does not
  -- trigger `Scheme.Modules.isFinitePresentation_tensorObj`.
  have : (((SheafOfModules.free I : (Proj 𝒜).Modules) ⊗ twistingSheaf 𝒜 (-(r : ℤ)) :
      (Proj 𝒜).Modules)).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_tensorObj (Proj 𝒜) _ _
  exact ⟨I, hI, π, hπ, Scheme.Modules.isFinitePresentation_kernel π⟩

end AlgebraicGeometry.Proj

end
