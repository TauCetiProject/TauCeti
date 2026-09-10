/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Basic

/-!
# The Weil divisor associated with a Cartier divisor

On a Noetherian integral curve, a Cartier divisor has an order at every codimension-one point:
choose a rational local equation and take its order of vanishing. This does not depend on the
equation, since two equations differ by a regular unit near the point. Only finitely many orders
are nonzero, so they form a Weil divisor.

This file constructs the resulting homomorphism from Cartier divisors to Weil divisors. It proves
that its values are locally principal and that it is inverse to the homomorphism which glues the
local equations of a locally principal Weil divisor. Consequently, locally principal Weil
divisors and Cartier divisors are additively equivalent on such a curve.

## Main declarations

* `Scheme.CartierDivisor.orderAt` is the order of a Cartier divisor at a codimension-one point;
* `Scheme.CartierDivisor.toWeilDivisorHom` sends a Cartier divisor to its Weil divisor;
* `Scheme.CartierDivisor.isLocallyPrincipal_toWeilDivisor` supplies its local equations;
* `SchemeWeilDivisor.equivCartierDivisor` is the Weil--Cartier additive equivalence.

The construction follows Hartshorne, *Algebraic Geometry*, II.6.11, and the Stacks Project,
*Divisors*, Tag 0BE9. No external formalization is vendored.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A regular unit on a nonempty open subset has order zero at every point of that subset. -/
lemma orderAt_regularUnitToFunctionField (U : X.Opens) [Nonempty U]
    (r : ((X.presheaf.obj (op U)) : Type u)ˣ) (x : CodimensionOnePoint X)
    (hx : (x : X) ∈ U) :
    orderAt x (Additive.ofMul (Scheme.regularUnitToFunctionField X U r)) = 0 := by
  rw [orderAt_apply, toMul_ofMul, Scheme.regularUnitToFunctionField_apply, Units.coe_map]
  have hmap : (X.germToFunctionField U).hom (r : Γ(X, U)) =
      X.germToFunctionField U (r : Γ(X, U)) := rfl
  exact (congrArg (fun f : X.functionField ↦ X.ord f (x : X)) hmap).trans
    (X.ord_of_isUnit r.isUnit hx)

/-- Two rational functions representing the same Cartier-divisor section have the same order at
each codimension-one point of the open subset. -/
theorem orderAt_eq_of_rationalUnitClass_eq (U : X.Opens) [Nonempty U]
    (f g : Additive X.functionFieldˣ)
    (hfg : Scheme.rationalUnitClass X U f = Scheme.rationalUnitClass X U g)
    (x : CodimensionOnePoint X) (hx : (x : X) ∈ U) :
    orderAt x f = orderAt x g := by
  have hsections :
      ((Scheme.toCartierDivisorSheaf X).hom.app (op U)).hom
          ((Scheme.rationalUnitSectionsEquiv X U).symm f) =
        ((Scheme.toCartierDivisorSheaf X).hom.app (op U)).hom
          ((Scheme.rationalUnitSectionsEquiv X U).symm g) := by
    simpa only [Scheme.rationalUnitClass_apply] using hfg
  obtain ⟨r, hr⟩ := (Scheme.toCartierDivisorSheaf_app_eq_iff X _ _).mp hsections
  have hr' : Additive.ofMul (Scheme.regularUnitToFunctionField X U (Additive.toMul r)) =
      f - g := by
    calc
      _ = Scheme.rationalUnitSectionsEquiv X U
          (((Scheme.toRationalUnitSheaf X).hom.app (op U)).hom r) := by
        rw [← ofMul_toMul r]
        exact (Scheme.rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U
          (Additive.toMul r)).symm
      _ = Scheme.rationalUnitSectionsEquiv X U
          ((Scheme.rationalUnitSectionsEquiv X U).symm f -
            (Scheme.rationalUnitSectionsEquiv X U).symm g) := congrArg _ hr
      _ = f - g := by simp
  have hzero : orderAt x (f - g) = 0 := by
    rw [← hr']
    exact orderAt_regularUnitToFunctionField U (Additive.toMul r) x hx
  rw [map_sub] at hzero
  omega

end SchemeWeilDivisor

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

namespace CartierDivisor

section LocallyNoetherian

/-- A Cartier divisor has a unique order compatible with any rational local equation at a fixed
codimension-one point. -/
theorem existsUnique_orderAt (D : CartierDivisor X) (x : CodimensionOnePoint X) :
    ∃! n : ℤ, ∃ (U : X.Opens) (_ : Nonempty U), (x : X) ∈ U ∧
      ∃ g : Additive X.functionFieldˣ,
        D |_ U = rationalUnitClass X U g ∧ n = SchemeWeilDivisor.orderAt x g := by
  obtain ⟨U, _, hxU, f, hf⟩ := exists_local_equation X D (x : X) (by simp)
  let _ : Nonempty U := ⟨⟨x, hxU⟩⟩
  let g := rationalUnitSectionsEquiv X U f
  have hDg : D |_ U = rationalUnitClass X U g := by
    rw [rationalUnitClass_apply]
    simpa only [g, AddEquiv.symm_apply_apply] using hf.symm
  refine ⟨SchemeWeilDivisor.orderAt x g, ⟨U, inferInstance, hxU, g, hDg, rfl⟩,
    fun n hn ↦ ?_⟩
  obtain ⟨V, hVne, hxV, h, hDh, hn⟩ := hn
  let _ : Nonempty V := hVne
  let _ : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hxU, hxV⟩⟩
  have heq : rationalUnitClass X (U ⊓ V : X.Opens) g =
      rationalUnitClass X (U ⊓ V : X.Opens) h := by
    calc
      _ = (rationalUnitClass X U g) |_ (U ⊓ V : X.Opens) :=
        (rationalUnitClass_restrict (X := X) (U := U) (V := U ⊓ V) inf_le_left g).symm
      _ = (D |_ U) |_ (U ⊓ V : X.Opens) := congrArg (fun E ↦ E |_ _) hDg.symm
      _ = D |_ (U ⊓ V : X.Opens) := TopCat.Presheaf.restrict_restrict _ _ _
      _ = (D |_ V) |_ (U ⊓ V : X.Opens) :=
        (TopCat.Presheaf.restrict_restrict _ _ _).symm
      _ = (rationalUnitClass X V h) |_ (U ⊓ V : X.Opens) :=
        congrArg (fun E ↦ E |_ _) hDh
      _ = _ := rationalUnitClass_restrict (X := X) (U := V) (V := U ⊓ V) inf_le_right h
  rw [hn]
  exact (SchemeWeilDivisor.orderAt_eq_of_rationalUnitClass_eq _ g h heq x
    ⟨hxU, hxV⟩).symm

/-- The order of a Cartier divisor at a codimension-one point. It is the order of any rational
local equation defined near that point. -/
def orderAt (D : CartierDivisor X) (x : CodimensionOnePoint X) : ℤ :=
  (existsUnique_orderAt D x).choose

/-- The order of a Cartier divisor is computed by any rational local equation defined near the
point. -/
theorem orderAt_eq_of_restrict_eq_rationalUnitClass (D : CartierDivisor X)
    (x : CodimensionOnePoint X) (U : X.Opens) [Nonempty U] (hx : (x : X) ∈ U)
    (g : Additive X.functionFieldˣ) (hDg : D |_ U = rationalUnitClass X U g) :
    D.orderAt x = SchemeWeilDivisor.orderAt x g := by
  exact ((existsUnique_orderAt D x).choose_spec.2 _
    ⟨U, inferInstance, hx, g, hDg, rfl⟩).symm

/-- A Cartier divisor has order zero at every codimension-one point where it vanishes locally. -/
theorem orderAt_eq_zero_of_restrict_eq_zero (D : CartierDivisor X)
    (x : CodimensionOnePoint X) (U : X.Opens) [Nonempty U] (hx : (x : X) ∈ U)
    (hD : D |_ U = 0) : D.orderAt x = 0 := by
  simpa only [map_zero] using
    orderAt_eq_of_restrict_eq_rationalUnitClass D x U hx 0 (by simpa using hD)

/-- The zero Cartier divisor has order zero at every codimension-one point. -/
@[simp]
theorem orderAt_zero (x : CodimensionOnePoint X) : (0 : CartierDivisor X).orderAt x = 0 := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨x, by simp⟩⟩
  apply orderAt_eq_zero_of_restrict_eq_zero 0 x ⊤ (by simp)
  simp

/-- The order of a sum of Cartier divisors is the sum of their orders. -/
@[simp]
theorem orderAt_add (D E : CartierDivisor X) (x : CodimensionOnePoint X) :
    (D + E).orderAt x = D.orderAt x + E.orderAt x := by
  obtain ⟨U, _, hxU, f, hf⟩ := exists_local_equation X D (x : X) (by simp)
  obtain ⟨V, _, hxV, g, hg⟩ := exists_local_equation X E (x : X) (by simp)
  let _ : Nonempty U := ⟨⟨x, hxU⟩⟩
  let _ : Nonempty V := ⟨⟨x, hxV⟩⟩
  let _ : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hxU, hxV⟩⟩
  let f' := rationalUnitSectionsEquiv X U f
  let g' := rationalUnitSectionsEquiv X V g
  have hDf : D |_ U = rationalUnitClass X U f' := by
    rw [rationalUnitClass_apply]
    simpa only [f', AddEquiv.symm_apply_apply] using hf.symm
  have hEg : E |_ V = rationalUnitClass X V g' := by
    rw [rationalUnitClass_apply]
    simpa only [g', AddEquiv.symm_apply_apply] using hg.symm
  have hsum : (D + E) |_ (U ⊓ V : X.Opens) =
      rationalUnitClass X (U ⊓ V : X.Opens) (f' + g') := by
    calc
      _ = (D |_ (U ⊓ V : X.Opens)) + (E |_ (U ⊓ V : X.Opens)) :=
        map_add ((cartierDivisorSheaf X).obj.map
          (homOfLE (le_top : (U ⊓ V : X.Opens) ≤ ⊤)).op).hom D E
      _ = (rationalUnitClass X U f') |_ (U ⊓ V : X.Opens) +
          (rationalUnitClass X V g') |_ (U ⊓ V : X.Opens) := by
        rw [← hDf, ← hEg, TopCat.Presheaf.restrict_restrict,
          TopCat.Presheaf.restrict_restrict]
      _ = rationalUnitClass X (U ⊓ V : X.Opens) f' +
          rationalUnitClass X (U ⊓ V : X.Opens) g' := by
        rw [rationalUnitClass_restrict (X := X) (U := U) (V := U ⊓ V) inf_le_left,
          rationalUnitClass_restrict (X := X) (U := V) (V := U ⊓ V) inf_le_right]
      _ = _ := (map_add (rationalUnitClass X (U ⊓ V : X.Opens)) f' g').symm
  have hxUV : (x : X) ∈ (U ⊓ V : X.Opens) := ⟨hxU, hxV⟩
  calc
    _ = SchemeWeilDivisor.orderAt x (f' + g') :=
      orderAt_eq_of_restrict_eq_rationalUnitClass (D + E) x (U ⊓ V) hxUV _ hsum
    _ = SchemeWeilDivisor.orderAt x f' + SchemeWeilDivisor.orderAt x g' := map_add _ _ _
    _ = _ := congrArg₂ (· + ·)
      (orderAt_eq_of_restrict_eq_rationalUnitClass D x U hxU f' hDf).symm
      (orderAt_eq_of_restrict_eq_rationalUnitClass E x V hxV g' hEg).symm

/-- The order of the negation of a Cartier divisor is the negative of its order. -/
@[simp]
theorem orderAt_neg (D : CartierDivisor X) (x : CodimensionOnePoint X) :
    (-D).orderAt x = -D.orderAt x :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← orderAt_add, neg_add_cancel, orderAt_zero]

/-- The order of a difference of Cartier divisors is the difference of their orders. -/
@[simp]
theorem orderAt_sub (D E : CartierDivisor X) (x : CodimensionOnePoint X) :
    (D - E).orderAt x = D.orderAt x - E.orderAt x := by
  rw [sub_eq_add_neg, orderAt_add, orderAt_neg, sub_eq_add_neg]

end LocallyNoetherian

section Noetherian

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- Only finitely many codimension-one points have nonzero order in a Cartier divisor. -/
theorem finite_support_orderAt (D : CartierDivisor X) :
    (Function.support D.orderAt).Finite := by
  let x : X := Classical.choice (inferInstanceAs (Nonempty X))
  obtain ⟨U, _, hxU, f, hf⟩ := exists_local_equation X D x (by simp)
  let _ : Nonempty U := ⟨⟨x, hxU⟩⟩
  let g := rationalUnitSectionsEquiv X U f
  have hDg : D |_ U = rationalUnitClass X U g := by
    rw [rationalUnitClass_apply]
    simpa only [g, AddEquiv.symm_apply_apply] using hf.symm
  refine ((SchemeWeilDivisor.finite_setOfPred_not_mem U).union
    (SchemeWeilDivisor.finite_support_orderAt g)).subset ?_
  intro y hy
  by_cases hyU : (y : X) ∈ U
  · right
    intro hzero
    apply hy
    rw [orderAt_eq_of_restrict_eq_rationalUnitClass D y U hyU g hDg]
    exact hzero
  · exact Or.inl hyU

/-- The Weil divisor associated with a Cartier divisor, obtained from its orders at
codimension-one points. -/
def toWeilDivisor (D : CartierDivisor X) : SchemeWeilDivisor X :=
  Finsupp.ofSupportFinite D.orderAt D.finite_support_orderAt

/-- The coefficient of the Weil divisor associated with a Cartier divisor is its local order. -/
@[simp]
theorem coeff_toWeilDivisor (D : CartierDivisor X) (x : CodimensionOnePoint X) :
    WeilDivisor.coeff D.toWeilDivisor x = D.orderAt x :=
  congrFun Finsupp.ofSupportFinite_coe x

/-- The construction from Cartier divisors to Weil divisors is additive. -/
def toWeilDivisorHom : CartierDivisor X →+ SchemeWeilDivisor X where
  toFun := toWeilDivisor
  map_zero' := by
    apply WeilDivisor.ext
    simp
  map_add' D E := by
    apply WeilDivisor.ext
    simp

/-- The Cartier-to-Weil homomorphism computes the divisor defined by local orders. -/
@[simp]
theorem toWeilDivisorHom_apply (D : CartierDivisor X) :
    toWeilDivisorHom D = D.toWeilDivisor :=
  (rfl)

/-- The Weil divisor associated with a Cartier divisor is locally principal, with the same
rational local equations. -/
theorem isLocallyPrincipal_toWeilDivisor (D : CartierDivisor X) :
    SchemeWeilDivisor.IsLocallyPrincipal D.toWeilDivisor := by
  rw [SchemeWeilDivisor.isLocallyPrincipal_iff]
  intro x
  obtain ⟨U, _, hxU, f, hf⟩ := exists_local_equation X D x (by simp)
  let _ : Nonempty U := ⟨⟨x, hxU⟩⟩
  let g := rationalUnitSectionsEquiv X U f
  have hDg : D |_ U = rationalUnitClass X U g := by
    rw [rationalUnitClass_apply]
    simpa only [g, AddEquiv.symm_apply_apply] using hf.symm
  refine ⟨U, hxU, g, fun y hy ↦ ?_⟩
  rw [coeff_toWeilDivisor,
    orderAt_eq_of_restrict_eq_rationalUnitClass D y U hy g hDg]

end Noetherian

end CartierDivisor

end Scheme

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

/-- Sending a locally principal Weil divisor to its Cartier divisor and taking local orders
recovers the original Weil divisor. -/
@[simp]
theorem toWeilDivisor_cartierDivisor (hX : ∀ x : X, coheight x ≤ 1)
    (D : locallyPrincipalSubgroup X) :
    (IsLocallyPrincipal.cartierDivisor hX
      (mem_locallyPrincipalSubgroup.mp D.2)).toWeilDivisor = D := by
  apply WeilDivisor.ext
  intro x
  obtain ⟨U, hxU, g, hg⟩ := isLocallyPrincipal_iff.mp
    (mem_locallyPrincipalSubgroup.mp D.2) x
  let _ : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hcartier : (IsLocallyPrincipal.cartierDivisor hX
      (mem_locallyPrincipalSubgroup.mp D.2)) |_ U =
      Scheme.rationalUnitClass X U g := by
    exact IsLocallyPrincipal.cartierDivisor_restrict hX
      (mem_locallyPrincipalSubgroup.mp D.2) U g hg
  calc
    WeilDivisor.coeff (IsLocallyPrincipal.cartierDivisor hX
        (mem_locallyPrincipalSubgroup.mp D.2)).toWeilDivisor x =
        (IsLocallyPrincipal.cartierDivisor hX
          (mem_locallyPrincipalSubgroup.mp D.2)).orderAt x :=
      Scheme.CartierDivisor.coeff_toWeilDivisor _ _
    _ = SchemeWeilDivisor.orderAt x g :=
      Scheme.CartierDivisor.orderAt_eq_of_restrict_eq_rationalUnitClass
        (IsLocallyPrincipal.cartierDivisor hX
          (mem_locallyPrincipalSubgroup.mp D.2)) x U hxU g hcartier
    _ = WeilDivisor.coeff D x := (hg x hxU).symm

/-- Gluing the local equations of the Weil divisor associated with a Cartier divisor recovers the
Cartier divisor. -/
@[simp]
theorem cartierDivisor_toWeilDivisor (hX : ∀ x : X, coheight x ≤ 1)
    (D : Scheme.CartierDivisor X) :
    IsLocallyPrincipal.cartierDivisor hX
        (Scheme.CartierDivisor.isLocallyPrincipal_toWeilDivisor D) = D := by
  apply (IsLocallyPrincipal.eq_cartierDivisor hX
    (Scheme.CartierDivisor.isLocallyPrincipal_toWeilDivisor D) fun x ↦ ?_).symm
  obtain ⟨U, _, hxU, f, hf⟩ := Scheme.exists_local_equation X D x (by simp)
  let _ : Nonempty U := ⟨⟨x, hxU⟩⟩
  let g := Scheme.rationalUnitSectionsEquiv X U f
  have hDg : D |_ U = Scheme.rationalUnitClass X U g := by
    rw [Scheme.rationalUnitClass_apply]
    simpa only [g, AddEquiv.symm_apply_apply] using hf.symm
  refine ⟨U, inferInstance, g, hxU, fun y hy ↦ ?_, hDg⟩
  rw [Scheme.CartierDivisor.coeff_toWeilDivisor,
    Scheme.CartierDivisor.orderAt_eq_of_restrict_eq_rationalUnitClass D y U hy g hDg]

/-- **The Weil--Cartier equivalence.** On a Noetherian integral curve whose codimension-one local
rings are discrete valuation rings, locally principal Weil divisors are additively equivalent to
Cartier divisors. -/
def equivCartierDivisor (hX : ∀ x : X, coheight x ≤ 1) :
    locallyPrincipalSubgroup X ≃+ Scheme.CartierDivisor X where
  toFun := toCartierDivisorHom hX
  invFun D := ⟨D.toWeilDivisor, mem_locallyPrincipalSubgroup.mpr
    (Scheme.CartierDivisor.isLocallyPrincipal_toWeilDivisor D)⟩
  left_inv D := Subtype.ext <| by
    simpa only [toCartierDivisorHom_apply] using toWeilDivisor_cartierDivisor hX D
  right_inv D := by
    simpa only [toCartierDivisorHom_apply] using cartierDivisor_toWeilDivisor hX D
  map_add' := map_add (toCartierDivisorHom hX)

/-- The forward map of the Weil--Cartier equivalence glues the local equations of a locally
principal Weil divisor. -/
@[simp]
theorem equivCartierDivisor_apply (hX : ∀ x : X, coheight x ≤ 1)
    (D : locallyPrincipalSubgroup X) :
    equivCartierDivisor hX D = toCartierDivisorHom hX D :=
  (rfl)

/-- The inverse of the Weil--Cartier equivalence is the associated Weil divisor with its local
principalness witness. -/
@[simp]
theorem equivCartierDivisor_symm_apply (hX : ∀ x : X, coheight x ≤ 1)
    (D : Scheme.CartierDivisor X) :
    (equivCartierDivisor hX).symm D =
      ⟨D.toWeilDivisor, mem_locallyPrincipalSubgroup.mpr
        (Scheme.CartierDivisor.isLocallyPrincipal_toWeilDivisor D)⟩ :=
  (rfl)

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
