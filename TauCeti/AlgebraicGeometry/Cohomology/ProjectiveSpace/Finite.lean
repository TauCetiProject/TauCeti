/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.DimensionShifting
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalGeneration
import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Monoidal

/-!
# Finiteness of the cohomology of coherent sheaves on projective schemes

Let `R` be a Noetherian ring and `X` a scheme projective over `R`, that is, a closed subscheme over
`R` of `Proj (Sym_R M)` for a finite `R`-module `M` (`AlgebraicGeometry.Scheme.IsProjectiveOver`).
This file proves that every quasi-coherent sheaf `F` of finite type on `X` has finitely generated
cohomology `Hᵠ(X, F)` over `R` in every degree. This is Hartshorne, Theorem III.5.2(a), the
projective case of the finiteness of the cohomology of coherent sheaves on proper schemes; over a
field it says that `Hᵠ(X, F)` is finite-dimensional.

The proof first treats projective space `ℙⁿ_R = Proj (Sym_R R^{n+1})` with `n ≥ 1`, through the
dimension-shifting criterion
`AlgebraicGeometry.Scheme.Modules.finite_cohomology_of_forall_exists_epi` with three inputs:

* quasi-coherent cohomology on `ℙⁿ_R` vanishes in degrees greater than `n`
  (`Module.Basis.subsingleton_cohomology_proj_of_card_le`);
* by Serre's theorem every `F` is a quotient of `𝒪^{⊕I} ⊗ 𝒪(-m)` for a finite `I` and some
  `m ≥ 0` (`AlgebraicGeometry.Proj.eventually_exists_epi_free_tensor_twistingSheaf`);
* the twisting sheaves `𝒪(m)` have finitely generated cohomology in every degree
  (`Module.Basis.finite_cohomology_twistingSheaf`), hence so do the finite sums of them.

A scheme projective over `R` is a closed subscheme of such a projective space
(`AlgebraicGeometry.Scheme.IsProjectiveOver.exists_isClosedImmersion_pi`). For a closed immersion
`i : X ⟶ ℙⁿ_R`, the direct image `i_* F` is quasi-coherent of finite type and has the same
cohomology as `F` (`AlgebraicGeometry.Scheme.Hom.moduleFinite_cohomology_pushforward_iff`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.finite_cohomology_of_isProjectiveOver`: for `X` projective over
  a Noetherian ring `R`, `Hᵠ(X, F)` is a finitely generated `R`-module.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TauCeti.SymmetricAlgebra
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace Module.Basis

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The cohomology of a quasi-coherent sheaf of finite type on projective space `Proj (Sym M)` of
positive dimension over a Noetherian ring `R`, for `M` free with a finite basis, is finitely
generated over `R`. This is the case of projective space in
`AlgebraicGeometry.Scheme.Modules.finite_cohomology_of_isProjectiveOver`. -/
private theorem finite_cohomology_proj [IsNoetherianRing R] {κ : Type*} [Finite κ] [Nontrivial κ]
    (b : Module.Basis κ R M) (F : (Proj (homogeneousSubmodule R M)).Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  have := Fintype.ofFinite κ
  have : Module.Finite R M := .of_basis b
  refine Scheme.Modules.finite_cohomology_of_forall_exists_epi R (Fintype.card κ)
    (fun F _ _ q hq ↦ b.subsingleton_cohomology_proj_of_card_le F q hq) (fun F _ _ ↦ ?_) F q
  -- Serre's theorem presents `F` as a quotient of `𝒪^{⊕I} ⊗ 𝒪(-n)`, which is finitely presented.
  obtain ⟨n, I, _, π, _⟩ := (Proj.eventually_exists_epi_free_tensor_twistingSheaf
    (fun i ↦ _root_.SymmetricAlgebra.ι R M (b i)) (fun i ↦ ι_mem_homogeneousSubmodule R M (b i))
    (iSup_basicOpen_ι_eq_top R M b b.span_eq) F).exists
  have : ((SheafOfModules.free I : (Proj (homogeneousSubmodule R M)).Modules) ⊗
      Proj.twistingSheaf (homogeneousSubmodule R M) (-n)).IsFinitePresentation :=
    TauCeti.SheafOfModules.isFinitePresentation_tensorObj (R := (Proj _).sheaf)
  refine ⟨_, π, ‹_›, inferInstance, inferInstance, fun q ↦ ?_⟩
  have := b.finite_cohomology_twistingSheaf (-n) q
  exact Scheme.Modules.finite_cohomology_free_tensor R I _ q

end Module.Basis

namespace AlgebraicGeometry.Scheme.Modules

/-- **The cohomology of a coherent sheaf on a projective scheme is finitely generated**
(Hartshorne, Theorem III.5.2(a)). Let `R` be a Noetherian ring and `X` a scheme projective over
`R`. Then for every quasi-coherent sheaf `F` of finite type on `X`, `Hᵠ(X, F)` is a finitely
generated `R`-module for every `q`. -/
instance finite_cohomology_of_isProjectiveOver (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨n, i, _, _⟩ := IsProjectiveOver.exists_isClosedImmersion_pi R (X := X)
  -- The direct image `i_* F` along the closed immersion into `ℙⁿ⁺¹_R` is coherent and has the
  -- cohomology of `F`.
  exact (i.moduleFinite_cohomology_pushforward_iff R F q).mp
    ((Pi.basisFun R (Fin (n + 2))).finite_cohomology_proj _ q)

end AlgebraicGeometry.Scheme.Modules
