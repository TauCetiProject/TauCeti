/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop

/-!
# A common blowup for two centres

The blowup of the product of two ideal sheaves maps canonically to the blowup of either
factor. Both ideals become effective Cartier on this common blowup. Consequently a map
on which both centres become effective Cartier lifts compatibly to all three blowups.
For centres of finite type these comparison maps are proper, and centres avoiding a
specified open give a proper common modification which leaves that open unchanged.

Since the exceptional divisor `(I * J)·𝒪` on the blowup of `I * J` is an effective Cartier
divisor, factor descent (`Scheme.IdealSheafData.IsEffectiveCartier.of_mul_left` and
`of_mul_right`) immediately shows that both factor ideals become effective Cartier on the
product blowup. No Noetherian or finite-generation assumption is needed for the Cartier or
factorization statements.

## References

* The Stacks Project, Lemma 31.33.12 (Tag 080A), on blowing up a product of ideals.
* The Stacks Project, Lemma 38.33.4 (Tag 0F3X), for the common blowup used in gluing
  modifications.

The construction uses `Scheme.IdealSheafData.blowupLift` and factor descent from the
exceptional divisor of `I * J`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry reesAlgebra
open scoped Pointwise

universe u

namespace Ideal

open TauCeti TauCeti.AlgebraicGeometry Scheme.IdealSheafData

/-- On the blowup of the product of two ideals of a ring, the first ideal becomes an
effective Cartier ideal. -/
theorem isEffectiveCartier_comap_toSpecCoeff_mul_left {R : Type u} [CommRing R]
    (I J : Ideal R) :
    ((ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
      (Proj.toSpecCoeff (grade (I * J)))).IsEffectiveCartier := by
  have h := isEffectiveCartier_comap_toSpecZero_reesAlgebra (I * J)
  rw [← toSpecCoeff_reesAlgebra, Ideal.map_mul, ofIdealTop_mul, comap_mul] at h
  exact h.of_mul_left

end Ideal

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X T : Scheme.{u}} (I J : X.IdealSheafData)

/-- The first factor ideal becomes effective Cartier on the blowup of the product centre. -/
theorem isEffectiveCartier_comap_blowupToBase_mul_left :
    (I.comap (I * J).blowupToBase).IsEffectiveCartier := by
  have h := (I * J).isEffectiveCartier_comap_blowupToBase
  rw [comap_mul] at h
  exact h.of_mul_left

/-- The second factor ideal becomes effective Cartier on the blowup of the product centre. -/
theorem isEffectiveCartier_comap_blowupToBase_mul_right :
    (J.comap (I * J).blowupToBase).IsEffectiveCartier := by
  rw [mul_comm I J]
  exact J.isEffectiveCartier_comap_blowupToBase_mul_left I

/-- The canonical morphism from the blowup of `I * J` to the blowup of `I`. -/
def blowupMulFst : (I * J).blowup ⟶ I.blowup :=
  I.blowupLift _ (I.isEffectiveCartier_comap_blowupToBase_mul_left J)

/-- The canonical morphism from the blowup of `I * J` to the blowup of `J`. -/
def blowupMulSnd : (I * J).blowup ⟶ J.blowup :=
  J.blowupLift _ (I.isEffectiveCartier_comap_blowupToBase_mul_right J)

@[reassoc (attr := simp)]
theorem blowupMulFst_blowupToBase : I.blowupMulFst J ≫ I.blowupToBase = (I * J).blowupToBase :=
  I.blowupLift_blowupToBase _ _

@[reassoc (attr := simp)]
theorem blowupMulSnd_blowupToBase : I.blowupMulSnd J ≫ J.blowupToBase = (I * J).blowupToBase :=
  J.blowupLift_blowupToBase _ _

/-- The first comparison is proper whenever the product-centre blowup is proper. -/
instance isProper_blowupMulFst [IsProper (I * J).blowupToBase] :
    IsProper (I.blowupMulFst J) := by
  have : IsProper (I.blowupMulFst J ≫ I.blowupToBase) := by
    rw [blowupMulFst_blowupToBase]
    infer_instance
  exact IsProper.of_comp _ I.blowupToBase

/-- The second comparison is proper whenever the product-centre blowup is proper. -/
instance isProper_blowupMulSnd [IsProper (I * J).blowupToBase] :
    IsProper (I.blowupMulSnd J) := by
  have : IsProper (I.blowupMulSnd J ≫ J.blowupToBase) := by
    rw [blowupMulSnd_blowupToBase]
    infer_instance
  exact IsProper.of_comp _ J.blowupToBase

/-- A lift to the product-centre blowup is compatible with the lift to the first factor. -/
@[reassoc]
theorem blowupLift_blowupMulFst (f : T ⟶ X) (hIJ : ((I * J).comap f).IsEffectiveCartier) :
    (I * J).blowupLift f hIJ ≫ I.blowupMulFst J =
      I.blowupLift f (I.comap_mul J f ▸ hIJ).of_mul_left := by
  apply I.eq_blowupLift
  simp

/-- A lift to the product-centre blowup is compatible with the lift to the second factor. -/
@[reassoc]
theorem blowupLift_blowupMulSnd (f : T ⟶ X) (hIJ : ((I * J).comap f).IsEffectiveCartier) :
    (I * J).blowupLift f hIJ ≫ I.blowupMulSnd J =
      J.blowupLift f (I.comap_mul J f ▸ hIJ).of_mul_right := by
  apply J.eq_blowupLift
  simp

/-- Two centres of finite type avoiding `U` admit a proper common blowup which still avoids
`U`. The maps to both original blowups are proper and lie over `X`. -/
theorem exists_blowup_common_refinement
    (hIfg : ∀ V : X.affineOpens, (I.ideal V).FG)
    (hJfg : ∀ V : X.affineOpens, (J.ideal V).FG) (U : X.Opens)
    (hI : Disjoint (U : Set X) (I.support : Set X))
    (hJ : Disjoint (U : Set X) (J.support : Set X)) :
    ∃ (K : X.IdealSheafData) (a : K.blowup ⟶ I.blowup) (b : K.blowup ⟶ J.blowup),
      IsProper K.blowupToBase ∧ Disjoint (U : Set X) (K.support : Set X) ∧
      IsIso (K.blowupToBase ∣_ U) ∧ IsProper a ∧ IsProper b ∧
      a ≫ I.blowupToBase = K.blowupToBase ∧ b ≫ J.blowupToBase = K.blowupToBase := by
  have hK : IsProper (I * J).blowupToBase := by
    apply isProper_blowupToBase
    intro V
    rw [ideal_mul, Pi.mul_apply]
    exact (hIfg V).mul (hJfg V)
  have hU : Disjoint (U : Set X) ((I * J).support : Set X) := by
    simpa only [support_mul, TopologicalSpace.Closeds.coe_sup, Set.disjoint_union_right]
      using And.intro hI hJ
  exact ⟨I * J, I.blowupMulFst J, I.blowupMulSnd J, hK, hU,
    (I * J).isIso_blowupToBase_restrict_of_disjoint_support hU,
    inferInstance, inferInstance, I.blowupMulFst_blowupToBase J,
    I.blowupMulSnd_blowupToBase J⟩

end AlgebraicGeometry.Scheme.IdealSheafData
