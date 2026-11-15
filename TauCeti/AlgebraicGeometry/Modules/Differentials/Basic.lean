/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import TauCeti.Algebra.Category.ModuleCat.Differentials.Presheaf
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-!
# The sheaf of relative differentials of a scheme over a ring

Let `X` be a scheme over a commutative ring `R`, that is, over `Spec R`. The sheaf of relative
Kähler differentials `Ω_{X/R}` is the sheaf of `𝒪_X`-modules associated to the presheaf
`U ↦ Ω[Γ(X, U)⁄R]`, and it carries the universal `R`-derivation `d : 𝒪_X ⟶ Ω_{X/R}`. For a smooth
curve over a field `k`, `Ω_{X/k}` is the relative dualizing sheaf `ω_{X/k}` of Serre duality; in
general it is the first object of the cotangent formalism of `X` over `R`.

The construction follows Mathlib's presheaf of relative differentials
`PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'` of a morphism of
presheaves of commutative rings, applied to the morphism `Scheme.baseRingToStructurePresheaf`
from the constant presheaf `R` to the structure presheaf `𝒪_X`, followed by sheafification of
presheaves of modules. Since sheafification is left adjoint to the inclusion of sheaves of
modules, the universal property of the presheaf of differentials passes to the sheaf: morphisms
`Ω_{X/R} ⟶ M` to a sheaf of `𝒪_X`-modules correspond to `R`-derivations `𝒪_X ⟶ M`, by
composition with `d`.

The base is the affine scheme `Spec R`, which covers varieties over a field. Over a general base
scheme `S` the constant presheaf `R` would be replaced by the inverse image of `𝒪_S`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.Derivation R M`: the `R`-derivations of `𝒪_X` with values in
  a sheaf of `𝒪_X`-modules `M`;
* `AlgebraicGeometry.Scheme.relativeDifferentials R X`: the sheaf `Ω_{X/R}` of relative
  differentials;
* `AlgebraicGeometry.Scheme.universalDerivation R X`: the universal derivation
  `d : 𝒪_X ⟶ Ω_{X/R}`;
* `AlgebraicGeometry.Scheme.relativeDifferentialsHomEquiv R X M`: the universal property
  `(Ω_{X/R} ⟶ M) ≃ M.Derivation R`, with `AlgebraicGeometry.Scheme.relativeDifferentials_hom_ext`
  the corresponding uniqueness statement.

* `TauCeti.AlgebraicGeometry.globalDerivation R A`: the global
  component of a derivation on `Spec A`, viewed as an `R`-derivation of `A`.

## References

* The Stacks Project, Tag 01UM (differentials of a morphism of ringed spaces), in particular
  Lemma 01UP describing them as the sheafification of `U ↦ Ω_{𝒪_X(U)/R}`.
* R. Hartshorne, *Algebraic Geometry*, Section II.8.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

variable {X} in
/-- The `R`-derivations of the structure sheaf of a scheme `X` over `R` with values in a sheaf
of `𝒪_X`-modules `M`: compatible families of `R`-linear derivations `Γ(X, U) → Γ(M, U)`. -/
abbrev _root_.AlgebraicGeometry.Scheme.Modules.Derivation (M : X.Modules) : Type u :=
  PresheafOfModulesOfCommRing.Derivation' (R := X.presheaf) M.val
    (X.baseRingToStructurePresheaf R)

/-- The presheaf `U ↦ Ω[Γ(X, U)⁄R]` of relative differentials of a scheme `X` over `R`, as a
presheaf of `𝒪_X`-modules. Its sheafification is `Scheme.relativeDifferentials R X`. -/
def _root_.AlgebraicGeometry.Scheme.presheafRelativeDifferentials :
    PresheafOfModulesOfCommRing.{u} X.presheaf :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (X.baseRingToStructurePresheaf R)

/-- The **sheaf of relative differentials** `Ω_{X/R}` of a scheme `X` over a commutative ring
`R`: the sheafification of the presheaf `U ↦ Ω[Γ(X, U)⁄R]` of Kähler differentials. -/
def _root_.AlgebraicGeometry.Scheme.relativeDifferentials : X.Modules :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
    (X.presheafRelativeDifferentials R)

/-- The universal `R`-derivation `d : 𝒪_X ⟶ Ω_{X/R}`: on sections over `U`, the Kähler
differential `Γ(X, U) → Ω[Γ(X, U)⁄R]` followed by the sheafification map. -/
def _root_.AlgebraicGeometry.Scheme.universalDerivation :
    (X.relativeDifferentials R).Derivation R :=
  (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (X.baseRingToStructurePresheaf R)).postcomp
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (X.presheafRelativeDifferentials R))

/-- The **universal property of the sheaf of relative differentials**: morphisms
`Ω_{X/R} ⟶ M` of sheaves of `𝒪_X`-modules correspond to `R`-derivations of `𝒪_X` with values
in `M`, by composition with the universal derivation. -/
def _root_.AlgebraicGeometry.Scheme.relativeDifferentialsHomEquiv (M : X.Modules) :
    (X.relativeDifferentials R ⟶ M) ≃ M.Derivation R :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).trans
    ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
      (X.baseRingToStructurePresheaf R)).homEquiv _)

/-- The derivation corresponding to a morphism `f : Ω_{X/R} ⟶ M` is the universal derivation
followed by `f`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.relativeDifferentialsHomEquiv_apply {M : X.Modules}
    (f : X.relativeDifferentials R ⟶ M) :
    X.relativeDifferentialsHomEquiv R M f = (X.universalDerivation R).postcomp f.val := by
  unfold Scheme.relativeDifferentialsHomEquiv
  -- `rw` cannot be used here: the two presentations `TopCat.Sheaf` and `Sheaf` of the sheaf of
  -- rings of `X` agree only up to unfolding, so the rewritten goal would not be type-correct.
  refine (Equiv.trans_apply _ _ _).trans ?_
  refine (PresheafOfModulesOfCommRing.Derivation.Universal.homEquiv_apply _ _).trans ?_
  refine (congrArg _ (Adjunction.homEquiv_unit _ _ _ _)).trans ?_
  -- The right adjoint `forget ⋙ restrictScalars (𝟙 _)` of sheafification sends `f` to `f.val`
  -- with scalars restricted along the identity, which is `f.val` by definition.
  rfl

/-- Every `R`-derivation of `𝒪_X` with values in `M` is the universal derivation followed by
the corresponding morphism `Ω_{X/R} ⟶ M`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.relativeDifferentialsHomEquiv_symm_fac
    {M : X.Modules} (D : M.Derivation R) :
    (X.universalDerivation R).postcomp ((X.relativeDifferentialsHomEquiv R M).symm D).val = D := by
  rw [← Scheme.relativeDifferentialsHomEquiv_apply, Equiv.apply_symm_apply]

/-- The universal property of `Ω_{X/R}` is natural in the target module. -/
lemma _root_.AlgebraicGeometry.Scheme.relativeDifferentialsHomEquiv_comp {M N : X.Modules}
    (f : X.relativeDifferentials R ⟶ M) (g : M ⟶ N) :
    X.relativeDifferentialsHomEquiv R N (f ≫ g) =
      (X.relativeDifferentialsHomEquiv R M f).postcomp g.val := by
  -- As above, `rw` would produce a goal that is not type-correct, so rewrite by transitivity.
  refine (Scheme.relativeDifferentialsHomEquiv_apply R X (f ≫ g)).trans ?_
  refine Eq.trans ?_
    (congrArg (·.postcomp g.val) (Scheme.relativeDifferentialsHomEquiv_apply R X f)).symm
  exact (X.universalDerivation R).postcomp_comp f.val g.val

/-- Two morphisms out of `Ω_{X/R}` agree as soon as they agree on the differentials `d a` of all
local sections `a` of `𝒪_X`. -/
@[ext]
lemma _root_.AlgebraicGeometry.Scheme.relativeDifferentials_hom_ext {M : X.Modules}
    {f g : X.relativeDifferentials R ⟶ M}
    (h : ∀ (U : X.Opensᵒᵖ) (a : X.presheaf.obj U),
      f.val.app U ((X.universalDerivation R).d a) = g.val.app U ((X.universalDerivation R).d a)) :
    f = g := by
  refine (X.relativeDifferentialsHomEquiv R M).injective ?_
  rw [Scheme.relativeDifferentialsHomEquiv_apply, Scheme.relativeDifferentialsHomEquiv_apply]
  ext U a
  exact h U a

section Affine

variable (A : CommRingCat.{u}) [Algebra R A]

/-- The `R`-derivation `A → Γ(M, ⊤)` given by the global component of a derivation of
`𝒪_{Spec A}`. -/
def globalDerivation {M : (Spec A).Modules} (d : M.Derivation R) :
    Derivation R A Γ(M, ⊤) :=
  Derivation.mk'
    { toFun a := d.d (X := op ⊤) (algebraMap A Γ(Spec A, ⊤) a)
      map_add' a b := (congrArg d.d (map_add _ a b)).trans (map_add _ _ _)
      map_smul' r a := by
        have h₀ : d.d (X := op ⊤) (algebraMap A Γ(Spec A, ⊤) (algebraMap R A r)) = 0 := by
          rw [← Scheme.baseRingToStructurePresheaf_Spec_app_apply]
          exact d.d_app r
        rw [Algebra.smul_def, map_mul, d.d_mul, h₀, smul_zero, add_zero, RingHom.id_apply]
        exact algebraMap_smul (A := A) (M := Γ(M, ⊤)) r _ }
    fun a b ↦ (congrArg d.d (map_mul _ a b)).trans (d.d_mul _ _)

/-- Evaluating the global component of a sheaf derivation at `a : A` amounts to evaluating
that derivation on the corresponding global function. -/
@[simp]
lemma globalDerivation_apply {M : (Spec A).Modules}
    (d : M.Derivation R) (a : A) :
    globalDerivation R A d a =
      d.d (X := op ⊤) (algebraMap A Γ(Spec A, ⊤) a) :=
  (rfl)

end Affine

end

end AlgebraicGeometry

end TauCeti
