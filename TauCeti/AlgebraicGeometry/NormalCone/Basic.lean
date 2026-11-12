/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.IdealSheaf.ReesAlgebra
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Pullback

/-!
# The conormal sheaf and the normal cone

Let `i : X ⟶ Y` be a morphism of schemes with ideal sheaf `I = ker i ⊆ 𝒪_Y`; the case of interest
is a closed immersion, where `X = V(I)`. Pulling back the Rees algebra `⨁ₙ Iⁿ` of `I` along `i`
gives the graded quasi-coherent `𝒪_X`-algebra

`i^* (⨁ₙ Iⁿ) = ⨁ₙ i^* Iⁿ`,

the *normal cone algebra* of `i`. Its degree-zero component is `i^* I⁰ = i^* 𝒪_Y = 𝒪_X`
(`isIso_one_normalConeAlgebra`) and its degree-one component is the *conormal sheaf* `i^* I` of
`i`. The *normal cone* of `i` is the relative spectrum

`C_X Y = Spec_X (⨁ₙ i^* Iⁿ)`,

an affine scheme over `X`. For a closed immersion `i^* Iⁿ = Iⁿ ⊗ 𝒪_Y/I = Iⁿ/Iⁿ⁺¹`, so the normal
cone algebra is the associated graded algebra `⨁ₙ Iⁿ/Iⁿ⁺¹` of `I`, read as an algebra on `X`, the
conormal sheaf is `I/I²`, and `C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)` is Fulton's normal cone.

The normal cone is the linear approximation of `Y` along `X` used in intersection theory: the
deformation to the normal cone degenerates `i` to the zero section `X ⟶ C_X Y`, and for a regular
immersion `C_X Y` is the normal bundle `Spec_X (Sym (I/I²))`, a vector bundle whose dual is the
conormal sheaf.

The ideal sheaf `ker i` is the ideal of the scheme-theoretic image of `i`, so for a morphism `i`
which is not a closed immersion these constructions are the pullbacks along `i` of the
corresponding invariants of the closed immersion `V(ker i) ⟶ Y`. They agree with the conormal
sheaf of an immersion (Stacks, Tag 01R1) for closed immersions, and more generally for
quasi-compact immersions, but need not do so for an arbitrary immersion.

Defining the normal cone algebra as a pullback of the Rees algebra makes it a graded
quasi-coherent algebra on `X` directly, with its algebra structure transported from that of
`⨁ₙ Iⁿ` by the strong monoidal pullback of quasi-coherent sheaves.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.normalConeAlgebra i`: the graded quasi-coherent `𝒪_X`-algebra
  `⨁ₙ i^* Iⁿ`; for a closed immersion, `⨁ₙ Iⁿ/Iⁿ⁺¹`.
* `AlgebraicGeometry.Scheme.Hom.conormal i`: the conormal sheaf `i^* I`, as a quasi-coherent
  sheaf on `X`; for a closed immersion, `I/I²`.
* `AlgebraicGeometry.Scheme.Hom.normalConeOver i`: the normal cone `Spec_X (⨁ₙ i^* Iⁿ)`, as an
  affine scheme over `X`; for a closed immersion, `Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)`.
* `AlgebraicGeometry.Scheme.Hom.normalCone i` and
  `AlgebraicGeometry.Scheme.Hom.normalConeToBase i`: the normal cone and its projection to `X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.normalConeAlgebra_obj_X`: the homogeneous components of the
  normal cone algebra are the pullbacks `i^* Iⁿ`.
* `AlgebraicGeometry.Scheme.Hom.conormal_obj`: the conormal sheaf is the pullback `i^* I`, and
  `AlgebraicGeometry.Scheme.Hom.conormal_eq_degreeOne`: it is the degree-one component of the
  normal cone algebra.
* `AlgebraicGeometry.Scheme.Hom.isIso_one_normalConeAlgebra`: the unit `𝒪_X ⟶ i^* I⁰` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isAffineHom_normalConeToBase`: the projection of the normal cone
  is affine.
* `AlgebraicGeometry.Scheme.Hom.isZero_conormal`: a scheme-theoretically dominant morphism, for
  instance an isomorphism, has zero conormal sheaf; more generally all positive-degree components
  of its normal cone algebra vanish (`isZero_normalConeAlgebra_obj_X`).

## References

* W. Fulton, *Intersection Theory*, 2nd ed., §4.1 and Appendix B.6.
* [The Stacks Project, Tag 01R1](https://stacks.math.columbia.edu/tag/01R1): the conormal sheaf
  of an immersion.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

noncomputable section

variable {X Y : Scheme.{u}} (i : X ⟶ Y)

/-- The normal cone algebra `⨁ₙ i^* Iⁿ` of a morphism `i : X ⟶ Y` with ideal sheaf `I = ker i`:
the pullback along `i` of the Rees algebra `⨁ₙ Iⁿ` (`normalConeAlgebra_eq`). For a closed
immersion, `i^* Iⁿ = Iⁿ/Iⁿ⁺¹`, so this is the associated graded algebra `⨁ₙ Iⁿ/Iⁿ⁺¹` of `I`, as an
algebra on `X`. -/
def normalConeAlgebra : GradedQuasicoherentAlgebra X :=
  (GradedQuasicoherentAlgebra.pullback i).obj i.ker.reesAlgebra

/-- The normal cone algebra is the pullback along `i` of the Rees algebra of `ker i`. -/
theorem normalConeAlgebra_eq :
    i.normalConeAlgebra = (GradedQuasicoherentAlgebra.pullback i).obj i.ker.reesAlgebra :=
  (rfl)

/-- The homogeneous components of the normal cone algebra are the pullbacks `i^* Iⁿ` of the
powers of the ideal sheaf `I = ker i`. -/
@[simp]
theorem normalConeAlgebra_obj_X (n : ℕ) :
    i.normalConeAlgebra.obj.X n = (Scheme.Modules.pullback i).obj (i.ker ^ n).sheaf := by
  rw [normalConeAlgebra_eq, GradedQuasicoherentAlgebra.pullback_obj_obj_X,
    IdealSheafData.reesAlgebra_obj_X]

/-- The unit `𝒪_X ⟶ i^* I⁰` of the normal cone algebra is an isomorphism: `I⁰ = 𝒪_Y`, so the
degree-zero component `i^* I⁰` of the normal cone algebra is `i^* 𝒪_Y = 𝒪_X`. -/
instance isIso_one_normalConeAlgebra : IsIso i.normalConeAlgebra.obj.toMon.one :=
  inferInstanceAs
    (IsIso ((GradedQuasicoherentAlgebra.pullback i).obj i.ker.reesAlgebra).obj.toMon.one)

/-- The conormal sheaf `i^* I` of a morphism `i : X ⟶ Y` with ideal sheaf `I = ker i`, as a
quasi-coherent sheaf on `X`. It is the degree-one component of the normal cone algebra
(`conormal_eq_degreeOne`). For a closed immersion, `i^* I = I/I²` (Stacks, Tag 01R1). -/
def conormal : QuasicoherentSheaf X :=
  (GradedQuasicoherentAlgebra.degree 1).obj i.normalConeAlgebra

/-- The conormal sheaf is the degree-one component of the normal cone algebra. -/
theorem conormal_eq_degreeOne :
    i.conormal = GradedQuasicoherentAlgebra.degreeOne.obj i.normalConeAlgebra :=
  (rfl)

/-- The underlying module of the conormal sheaf is the pullback `i^* I` of the ideal sheaf
`I = ker i`. -/
@[simp]
theorem conormal_obj : i.conormal.obj = (Scheme.Modules.pullback i).obj i.ker.sheaf := by
  rw [conormal_eq_degreeOne, GradedQuasicoherentAlgebra.degree_obj_obj, normalConeAlgebra_obj_X,
    pow_one]

/-- The normal cone `Spec_X (⨁ₙ i^* Iⁿ)` of a morphism `i : X ⟶ Y` with ideal sheaf
`I = ker i`, as an affine scheme over `X`: the relative spectrum of the normal cone algebra
(`normalConeOver_eq`). For a closed immersion this is `C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)`. -/
@[expose]
def normalConeOver : AffineSchemeOver X :=
  (relativeSpec X).obj
    (op (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj i.normalConeAlgebra))

/-- The normal cone over `X` is the relative spectrum of the direct-sum algebra underlying the
normal cone algebra. -/
theorem normalConeOver_eq :
    i.normalConeOver =
      (relativeSpec X).obj
        (op (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj i.normalConeAlgebra)) :=
  rfl

/-- The normal cone `Spec_X (⨁ₙ i^* Iⁿ)` of a morphism `i : X ⟶ Y`; for a closed immersion this
is `C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)`. -/
@[expose]
def normalCone : Scheme.{u} :=
  i.normalConeOver.left

/-- The projection `C_X Y ⟶ X` of the normal cone. -/
@[expose]
def normalConeToBase : i.normalCone ⟶ X :=
  i.normalConeOver.hom

/-- The normal cone is the relative spectrum of the direct-sum algebra underlying the normal cone
algebra. -/
theorem normalCone_eq :
    i.normalCone =
      (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj
        i.normalConeAlgebra).obj.relativeSpec :=
  rfl

/-- The projection of the normal cone is the structure morphism of the relative spectrum. -/
theorem normalConeToBase_eq :
    i.normalConeToBase =
      (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj
        i.normalConeAlgebra).obj.relativeSpecToBase :=
  rfl

/-- The projection of the normal cone is affine. -/
instance isAffineHom_normalConeToBase : IsAffineHom i.normalConeToBase :=
  inferInstanceAs (IsAffineHom i.normalConeOver.hom)

/-- A scheme-theoretically dominant morphism, for instance an isomorphism, has ideal sheaf `⊥`, so
the positive-degree components `i^* Iⁿ` of its normal cone algebra vanish. -/
theorem isZero_normalConeAlgebra_obj_X [IsSchemeTheoreticallyDominant i] {n : ℕ} (hn : n ≠ 0) :
    IsZero (i.normalConeAlgebra.obj.X n) := by
  rw [normalConeAlgebra_obj_X, i.ker_eq_bot, ← IdealSheafData.zero_eq_bot, zero_pow hn,
    IdealSheafData.zero_eq_bot]
  exact (Scheme.Modules.pullback i).map_isZero IdealSheafData.isZero_sheaf_bot

/-- A scheme-theoretically dominant morphism, for instance an isomorphism, has zero conormal
sheaf, as a sheaf of modules. -/
theorem isZero_conormal_obj [IsSchemeTheoreticallyDominant i] : IsZero i.conormal.obj := by
  rw [conormal_eq_degreeOne, GradedQuasicoherentAlgebra.degree_obj_obj]
  exact i.isZero_normalConeAlgebra_obj_X one_ne_zero

/-- A scheme-theoretically dominant morphism, for instance an isomorphism, has zero conormal
sheaf. -/
theorem isZero_conormal [IsSchemeTheoreticallyDominant i] : IsZero i.conormal :=
  IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ i.isZero_conormal_obj

end

end AlgebraicGeometry.Scheme.Hom
