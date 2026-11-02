/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pushforward
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic

/-!
# Higher direct images commute with restriction to opens of the target

Let `f : X ⟶ Y` be a morphism of schemes and `U` an open subset of `Y`. Restricting the higher
direct image `R^q f_* M` to `U` gives the higher direct image of `M|_{f⁻¹ U}` along the restriction
`f ∣_ U : f⁻¹ U ⟶ U`, naturally in the sheaf of modules `M`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageRestrictIso`). So the formation of `R^q f_*` is
local on the target, which is how properties of higher direct images, such as coherence along a
proper morphism, are reduced to the case of an affine target.

Restriction to an open subscheme is exact, since it has both adjoints, and it preserves injective
sheaves of modules (`AlgebraicGeometry.Scheme.Modules.restrictFunctorPreservesInjectiveObjects`).
It therefore sends an injective resolution of `M` to an injective resolution of `M|_{f⁻¹ U}`, and
commutes with taking homology. Restriction to `U` of a direct image along `f` is the direct image
along `f ∣_ U` of the restriction to `f⁻¹ U`
(`TauCeti.AlgebraicGeometry.restrictPushforwardIso`), and the general comparison
`CategoryTheory.Functor.rightDerivedCompIso` for right derived functors gives the result.

In particular, the vanishing of `R^q f_* M` can be checked on an open cover of the target
(`AlgebraicGeometry.Scheme.Hom.isZero_higherDirectImage_iff_of_iSup_eq_top`).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Higher direct images are local on the target.** Restricting `R^q f_* M` to an open `U` of
the target is `R^q (f ∣_ U)_* (M|_{f⁻¹ U})`, naturally in `M`. -/
def higherDirectImageRestrictIso (U : Y.Opens) (q : ℕ) :
    f.higherDirectImage q ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙ (f ∣_ U).higherDirectImage q :=
  Functor.rightDerivedCompIso _ _ _ _ (TauCeti.AlgebraicGeometry.restrictPushforwardIso f U) q

/-- **Vanishing of higher direct images is local on the target.** For an open cover `U` of the
target, `R^q f_* M` vanishes exactly when every `R^q (f ∣_ U i)_* (M|_{f⁻¹ (U i)})` does. -/
theorem isZero_higherDirectImage_iff_of_iSup_eq_top {ι : Type*} (U : ι → Y.Opens)
    (hU : iSup U = ⊤) (M : X.Modules) (q : ℕ) :
    IsZero ((f.higherDirectImage q).obj M) ↔
      ∀ i, IsZero (((f ∣_ U i).higherDirectImage q).obj (M.restrict (f ⁻¹ᵁ U i).ι)) := by
  rw [Scheme.Modules.isZero_iff_of_iSup_eq_top U hU]
  exact forall_congr' fun i ↦ ((f.higherDirectImageRestrictIso (U i) q).app M).isZero_iff

end AlgebraicGeometry.Scheme.Hom
