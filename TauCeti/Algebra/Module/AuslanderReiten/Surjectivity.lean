/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Minimal
public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Finite
public import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.RingTheory.Artinian.FiniteLength
import TauCeti.Algebra.Category.ModuleCat.Projective.Stable
import TauCeti.Algebra.Category.ModuleCat.ProjectiveStable.Reflection
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Surjectivity of the Auslander–Reiten translate

Every finitely generated non-injective indecomposable module `M` over an Artin algebra is the
Auslander–Reiten translate of a finitely generated non-projective indecomposable: `τ (τ⁻ M) ≅ M`,
where the inverse translate `τ⁻ M = Tr D M` is the right transpose of a presentation of the Matlis
dual `D M`. A minimal presentation of this preimage then computes its translate.

The result concerns actual modules, rather than objects modulo injectives or projectives.
It supplies the surjectivity half of the correspondence on indecomposable isomorphism
classes. The algebra may be noncommutative.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

open CategoryTheory

universe u v w

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable {R : Type u} {A : Type v} {E : Type u} [CommRing R] [IsArtinianRing R] [Ring A]
  [Algebra R A] [Module.Finite R A] [AddCommGroup E] [Module R E] [Module.Injective R E]

/-- **`τ τ⁻ M ≅ M`.** Over an Artin algebra, `D Tr` of a minimal presentation of the inverse
translate `Tr D M` of a finitely generated non-injective indecomposable module `M` recovers `M`.
The presentation `Q` of the Matlis dual `D M` need not be minimal. -/
theorem nonempty_linearEquiv_translate_rightTranspose_matlisDual
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {M : ModuleCat.{max u v w} A} [Module.Finite A M] (hiM : IsIndecomposableModule A M)
    (hinj : ¬ Module.Injective A M)
    (Q : FiniteProjectivePresentation (ModuleCat.of Aᵐᵒᵖ (MatlisDual R E M)))
    (P : FiniteProjectivePresentation Q.rightTranspose)
    (hP : IsMinimalProjectivePresentation P.p P.π) :
    Nonempty (AuslanderReitenTranslate R E P.p ≃ₗ[A] M) := by
  have := IsArtinianRing.of_finite R A
  have := IsArtinianRing.of_finite R Aᵐᵒᵖ
  let N := ModuleCat.of Aᵐᵒᵖ (MatlisDual R E M)
  have hM : IsFiniteLength R M := isFiniteLength_of_finite_trans R A M
  have hN : IsFiniteLength R N := MatlisDual.isFiniteLength hE hM
  have : Module.Finite R (AuslanderReitenTranspose P.p) := Module.Finite.trans Aᵐᵒᵖ _
  have hiN : Indecomposable N := (indecomposable_iff_isIndecomposableModule N).mpr
    ((MatlisDual.isIndecomposableModule_op_iff hE hM).mpr hiM)
  -- A projective dual would make `M ≅ D (D M)` injective.
  have hpN : ¬ Projective N := fun h ↦ hinj <| by
    have : Module.Projective Aᵐᵒᵖ (MatlisDual R E M) := (IsProjective.iff_projective N).mpr h
    exact ((Module.Baer.of_injective inferInstance).of_equiv
      (MatlisDual.evalEquiv hE hM).symm).injective
  obtain ⟨e⟩ := (nonempty_linearEquiv_translate_rightTranspose_iff_isZero_projective_retract.{v,
    max u w, u, u} hE Q P hP.isSuperfluous_ker hN (isFiniteLength_of_finite R _)).mpr
      ((ModuleCat.indecomposable_iff_isZero_projective_retract N
        ((ModuleCat.indecomposable_projectiveStableFunctor_obj_iff N
          (isFiniteLength_of_tower R hN) hiN).mpr hpN)).mp hiN)
  exact ⟨e.trans (MatlisDual.evalEquiv hE hM).symm⟩

end TauCeti.FiniteProjectivePresentation
