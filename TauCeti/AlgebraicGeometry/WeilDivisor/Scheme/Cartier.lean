/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Regular
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.LocallyPrincipal

/-!
# The Cartier divisor of a locally principal Weil divisor

Let `X` be a Noetherian integral scheme of dimension at most one whose codimension-one local
rings are discrete valuation rings. A Weil divisor `D` on `X` which is locally principal is
described near every point by one nonzero rational function, its *local equation* there. This
file glues those local equations into a single Cartier divisor, that is, into a global section
of `𝒦_X^× / 𝒪_X^×`.

The gluing is possible because two local equations for the same divisor on the same open subset
differ by a rational function of order zero at every codimension-one point, and such a function is
a regular unit by the one-dimensional algebraic Hartogs' principle of
`TauCeti/AlgebraicGeometry/Scheme/Regular.lean`. The resulting Cartier divisor is characterized —
and hence uniquely determined — by the requirement that it restrict to the class of `g` over every
open subset carrying a local equation `g`.

## Main declarations

* `SchemeWeilDivisor.rationalUnitClass_eq_of_forall_coeff_eq`: two local equations of the same
  divisor have the same Cartier class;
* `SchemeWeilDivisor.IsLocallyPrincipal.existsUnique_cartierDivisor`: the characterizing
  existence-and-uniqueness statement;
* `SchemeWeilDivisor.IsLocallyPrincipal.cartierDivisor`, the Cartier divisor of `D`, with its
  defining property `SchemeWeilDivisor.IsLocallyPrincipal.cartierDivisor_restrict`;
* `SchemeWeilDivisor.IsLocallyPrincipal.cartierDivisor_add` and
  `SchemeWeilDivisor.cartierDivisor_principalDivisor`: the construction is additive and sends the
  divisor of `g` to the principal Cartier divisor of `g`;
* `SchemeWeilDivisor.toCartierDivisorHom`, the resulting homomorphism from the group of locally
  principal Weil divisors to the group of Cartier divisors.

The construction follows Hartshorne, *Algebraic Geometry*, II.6.11, and the Stacks Project,
*Divisors*, Tag 0BE9. The gluing uses Mathlib's unique gluing for sheaves on a topological space,
applied to the Cartier-divisor sheaf.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

section Curve

variable [IsLocallyNoetherian X]

/-- **Two local equations agree as Cartier divisors.** If two nonzero rational functions both have
the coefficients of `D` as their orders at every codimension-one point of a nonempty open subset
`U` of a curve, then they have the same class in `𝒦_X^× / 𝒪_X^×` over `U`.

Their ratio has order zero at every codimension-one point of `U`, hence is a regular unit on `U`
by the one-dimensional algebraic Hartogs' principle, and regular units have zero class. -/
theorem rationalUnitClass_eq_of_forall_coeff_eq {D : SchemeWeilDivisor X}
    {U : X.Opens} [Nonempty U] (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hU : ∀ y ∈ U, coheight y ≤ 1) {g h : Additive X.functionFieldˣ}
    (hg : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → WeilDivisor.coeff D y = orderAt y g)
    (hh : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → WeilDivisor.coeff D y = orderAt y h) :
    Scheme.rationalUnitClass X U g = Scheme.rationalUnitClass X U h := by
  have hord : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      X.ord ((Additive.toMul (g - h) : X.functionFieldˣ) : X.functionField) (y : X) = 0 := by
    intro y hy
    rw [← orderAt_apply y (g - h), map_sub, ← hg y hy, ← hh y hy, sub_self]
  obtain ⟨u, hu⟩ := Scheme.exists_unit_germToFunctionField_eq_of_ord_eq_zero
    (U := U) hDVR hU hord
  have hunit : Units.map (X.germToFunctionField U).hom u = Additive.toMul (g - h) :=
    Units.ext hu
  have hzero := Scheme.rationalUnitClass_germToFunctionField_eq_zero X U u
  rw [hunit] at hzero
  refine sub_eq_zero.mp ?_
  rw [← map_sub]
  simpa only [Scheme.rationalUnitClass_apply, ofMul_toMul] using hzero

/-- **The local criterion for the Cartier divisor of `D`.** If a Cartier divisor `E` restricts,
near every point, to the class of a local equation of `D`, then it does so over *every* nonempty
open subset carrying a local equation of `D`.

This is the sheaf-separatedness step: the two sections agree on a cover of the given open
subset. -/
theorem restrict_eq_rationalUnitClass {D : SchemeWeilDivisor X} {E : Scheme.CartierDivisor X}
    {U : X.Opens} [Nonempty U] (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hU : ∀ y ∈ U, coheight y ≤ 1)
    (hE : ∀ x : X, ∃ (W : X.Opens) (_ : Nonempty W) (k : Additive X.functionFieldˣ), x ∈ W ∧
      (∀ y : CodimensionOnePoint X, (y : X) ∈ W → WeilDivisor.coeff D y = orderAt y k) ∧
      E |_ W = Scheme.rationalUnitClass X W k)
    {g : Additive X.functionFieldˣ}
    (hg : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → WeilDivisor.coeff D y = orderAt y g) :
    E |_ U = Scheme.rationalUnitClass X U g := by
  choose W hWne k hxW hk hEW using hE
  have hne : ∀ x : X, Nonempty (W x ⊓ U : X.Opens) := fun x ↦ by
    simpa using nonempty_preirreducible_inter (W x).isOpen U.isOpen
      (by simpa using hWne x) (by simpa using (inferInstance : Nonempty U))
  refine (Scheme.cartierDivisorSheaf X).eq_of_locally_eq'
    (fun x : X ↦ (W x ⊓ U : X.Opens)) U (fun x ↦ homOfLE inf_le_right)
    (fun x hx ↦ Opens.mem_iSup.mpr ⟨x, ⟨hxW x, hx⟩⟩) _ _ fun x ↦ ?_
  -- Needed as an instance for the classes over `W x ⊓ U` below.
  have := hWne x
  have hrestrictLeft :
      (Scheme.rationalUnitClass X (W x) (k x)) |_ (W x ⊓ U : X.Opens) =
        Scheme.rationalUnitClass X (W x ⊓ U : X.Opens) (k x) := by
    simpa only [Scheme.rationalUnitClass_apply] using
      Scheme.rationalUnitClass_restrict (X := X) (U := W x) (V := W x ⊓ U)
        inf_le_left (k x)
  have hleft : E |_ (W x ⊓ U : X.Opens) =
      Scheme.rationalUnitClass X (W x ⊓ U : X.Opens) (k x) := by
    rw [← TopCat.Presheaf.restrict_restrict (inf_le_left : W x ⊓ U ≤ W x) (le_top : W x ≤ ⊤) E,
      hEW x, hrestrictLeft]
  have hright : (Scheme.rationalUnitClass X U g) |_ (W x ⊓ U : X.Opens) =
      Scheme.rationalUnitClass X (W x ⊓ U : X.Opens) g := by
    simpa only [Scheme.rationalUnitClass_apply] using
      Scheme.rationalUnitClass_restrict (X := X) (U := U) (V := W x ⊓ U)
        inf_le_right g
  refine (TopCat.Presheaf.restrict_restrict (inf_le_right : W x ⊓ U ≤ U)
    (le_top : U ≤ ⊤) E).trans
      (hleft.trans ((rationalUnitClass_eq_of_forall_coeff_eq (D := D)
        (fun y hy ↦ hDVR y (Opens.mem_inf.mp hy).2)
        (fun y hy ↦ hU y (Opens.mem_inf.mp hy).2)
        (fun y hy ↦ hk x y (Opens.mem_inf.mp hy).1)
        fun y hy ↦ hg y (Opens.mem_inf.mp hy).2).trans hright.symm))

namespace IsLocallyPrincipal

variable {D E : SchemeWeilDivisor X}
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

/-- **The Cartier divisor of a locally principal Weil divisor exists and is unique.** On a curve,
a locally principal Weil divisor `D` determines a unique Cartier divisor whose restriction to
every nonempty open subset carrying a local equation `g` of `D` is the class of `g`. -/
theorem existsUnique_cartierDivisor (hX : ∀ y : X, coheight y ≤ 1)
    (hD : IsLocallyPrincipal D) :
    ∃! E : Scheme.CartierDivisor X, ∀ (U : X.Opens) (_ : Nonempty U)
      (g : Additive X.functionFieldˣ),
      (∀ y : CodimensionOnePoint X, (y : X) ∈ U → WeilDivisor.coeff D y = orderAt y g) →
        E |_ U = Scheme.rationalUnitClass X U g := by
  choose U hxU g hg using isLocallyPrincipal_iff.mp hD
  have hne : ∀ x : X, Nonempty (U x) := fun x ↦ ⟨⟨x, hxU x⟩⟩
  have hne₂ : ∀ x z : X, Nonempty (U x ⊓ U z : X.Opens) := fun x z ↦ by
    simpa using nonempty_preirreducible_inter (U x).isOpen (U z).isOpen
      (by simpa using hne x) (by simpa using hne z)
  have hcompat : TopCat.Presheaf.IsCompatible (Scheme.cartierDivisorSheaf X).obj U
      fun x ↦ Scheme.rationalUnitClass X (U x) (g x) := by
    intro x z
    have hx : (Scheme.rationalUnitClass X (U x) (g x)) |_ (U x ⊓ U z : X.Opens) =
        Scheme.rationalUnitClass X (U x ⊓ U z : X.Opens) (g x) := by
      simpa only [Scheme.rationalUnitClass_apply] using
        Scheme.rationalUnitClass_restrict (X := X) (U := U x) (V := U x ⊓ U z)
          inf_le_left (g x)
    have hz : (Scheme.rationalUnitClass X (U z) (g z)) |_ (U x ⊓ U z : X.Opens) =
        Scheme.rationalUnitClass X (U x ⊓ U z : X.Opens) (g z) := by
      simpa only [Scheme.rationalUnitClass_apply] using
        Scheme.rationalUnitClass_restrict (X := X) (U := U z) (V := U x ⊓ U z)
          inf_le_right (g z)
    exact hx.trans ((rationalUnitClass_eq_of_forall_coeff_eq (D := D)
      (fun _ _ ↦ inferInstance) (fun y _ ↦ hX y)
      (fun y hy ↦ hg x y (Opens.mem_inf.mp hy).1)
      fun y hy ↦ hg z y (Opens.mem_inf.mp hy).2).trans hz.symm)
  obtain ⟨E, hE, -⟩ := (Scheme.cartierDivisorSheaf X).existsUnique_gluing' U ⊤
    (fun _ ↦ homOfLE le_top) (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) _ hcompat
  have hlocal : ∀ x : X, ∃ (W : X.Opens) (_ : Nonempty W) (k : Additive X.functionFieldˣ),
      x ∈ W ∧
      (∀ y : CodimensionOnePoint X, (y : X) ∈ W → WeilDivisor.coeff D y = orderAt y k) ∧
      E |_ W = Scheme.rationalUnitClass X W k :=
    fun x ↦ ⟨U x, hne x, g x, hxU x, hg x, hE x⟩
  refine ⟨E, fun V hV k hk ↦ ?_, fun E' hE' ↦ ?_⟩
  · -- The nonemptiness of `V` is carried by the statement, not by instance search.
    have := hV
    exact restrict_eq_rationalUnitClass (fun _ _ ↦ inferInstance) (fun y _ ↦ hX y) hlocal hk
  · refine (Scheme.cartierDivisorSheaf X).eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top)
      (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) _ _ fun x ↦ ?_
    exact (hE' (U x) (hne x) (g x) (hg x)).trans (hE x).symm

/-- The Cartier divisor associated with a locally principal Weil divisor on a curve. -/
def cartierDivisor (hX : ∀ y : X, coheight y ≤ 1) (hD : IsLocallyPrincipal D) :
    Scheme.CartierDivisor X :=
  (existsUnique_cartierDivisor hX hD).choose

/-- **The defining property of the associated Cartier divisor.** Over a nonempty open subset
carrying a local equation `g` of `D`, the Cartier divisor of `D` restricts to the class of `g`. -/
theorem cartierDivisor_restrict (hX : ∀ y : X, coheight y ≤ 1) (hD : IsLocallyPrincipal D)
    (U : X.Opens) [Nonempty U] (g : Additive X.functionFieldˣ)
    (hg : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → WeilDivisor.coeff D y = orderAt y g) :
    (cartierDivisor hX hD) |_ U = Scheme.rationalUnitClass X U g :=
  (existsUnique_cartierDivisor hX hD).choose_spec.1 U ‹_› g hg

/-- A Cartier divisor which restricts, near every point, to the class of a local equation of `D`
is the Cartier divisor of `D`. -/
theorem eq_cartierDivisor (hX : ∀ y : X, coheight y ≤ 1) (hD : IsLocallyPrincipal D)
    {E : Scheme.CartierDivisor X}
    (hE : ∀ x : X, ∃ (W : X.Opens) (_ : Nonempty W) (k : Additive X.functionFieldˣ), x ∈ W ∧
      (∀ y : CodimensionOnePoint X, (y : X) ∈ W → WeilDivisor.coeff D y = orderAt y k) ∧
      E |_ W = Scheme.rationalUnitClass X W k) :
    E = cartierDivisor hX hD := by
  refine (existsUnique_cartierDivisor hX hD).choose_spec.2 E fun V hV k hk ↦ ?_
  -- The nonemptiness of `V` is carried by the statement, not by instance search.
  have := hV
  exact restrict_eq_rationalUnitClass (fun _ _ ↦ inferInstance) (fun y _ ↦ hX y) hE hk

/-- The zero Weil divisor has the zero Cartier divisor. -/
@[simp]
theorem cartierDivisor_zero (hX : ∀ y : X, coheight y ≤ 1) :
    cartierDivisor hX (isLocallyPrincipal_zero (X := X)) = 0 := by
  refine (eq_cartierDivisor hX _ fun x ↦ ?_).symm
  have hne : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  refine ⟨⊤, hne, 0, trivial, ?_, ?_⟩
  · intro y _
    rw [WeilDivisor.coeff_zero, map_zero]
  · rw [map_zero]
    exact map_zero ((Scheme.cartierDivisorSheaf X).obj.map
      (homOfLE (le_refl (⊤ : X.Opens))).op).hom

/-- **The construction is additive.** The Cartier divisor of a sum of locally principal Weil
divisors is the sum of their Cartier divisors: local equations multiply. -/
@[simp]
theorem cartierDivisor_add (hX : ∀ y : X, coheight y ≤ 1) (hD : IsLocallyPrincipal D)
    (hE : IsLocallyPrincipal E) :
    cartierDivisor hX (hD.add hE) = cartierDivisor hX hD + cartierDivisor hX hE := by
  refine (eq_cartierDivisor hX (hD.add hE) fun x ↦ ?_).symm
  obtain ⟨V, hxV, g, hg⟩ := isLocallyPrincipal_iff.mp hD x
  obtain ⟨W, hxW, h, hh⟩ := isLocallyPrincipal_iff.mp hE x
  have hne : Nonempty (V ⊓ W : X.Opens) := ⟨⟨x, hxV, hxW⟩⟩
  refine ⟨V ⊓ W, hne, g + h, ⟨hxV, hxW⟩, ?_, ?_⟩
  · intro y hy
    rw [WeilDivisor.coeff_add, hg y (Opens.mem_inf.mp hy).1, hh y (Opens.mem_inf.mp hy).2, map_add]
  · have hV : (cartierDivisor hX hD) |_ (V ⊓ W : X.Opens) =
        Scheme.rationalUnitClass X (V ⊓ W : X.Opens) g :=
      cartierDivisor_restrict hX hD _ g fun y hy ↦ hg y (Opens.mem_inf.mp hy).1
    have hW : (cartierDivisor hX hE) |_ (V ⊓ W : X.Opens) =
        Scheme.rationalUnitClass X (V ⊓ W : X.Opens) h :=
      cartierDivisor_restrict hX hE _ h fun y hy ↦ hh y (Opens.mem_inf.mp hy).2
    rw [map_add, ← hV, ← hW]
    exact map_add ((Scheme.cartierDivisorSheaf X).obj.map
      (homOfLE (le_top : (V ⊓ W : X.Opens) ≤ ⊤)).op).hom _ _

/-- The Cartier divisor of a locally principal Weil divisor depends only on the divisor. -/
theorem cartierDivisor_congr (hX : ∀ y : X, coheight y ≤ 1) (hD : IsLocallyPrincipal D)
    (hE : IsLocallyPrincipal E) (h : D = E) : cartierDivisor hX hD = cartierDivisor hX hE := by
  subst h
  rfl

/-- **The construction respects negation.** -/
@[simp]
theorem cartierDivisor_neg (hX : ∀ y : X, coheight y ≤ 1) (hD : IsLocallyPrincipal D) :
    cartierDivisor hX hD.neg = -cartierDivisor hX hD :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← cartierDivisor_add hX hD.neg hD,
      cartierDivisor_congr hX (hD.neg.add hD) (isLocallyPrincipal_zero (X := X))
        (neg_add_cancel D),
      cartierDivisor_zero]

end IsLocallyPrincipal

variable [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

/-- **The Weil-to-Cartier homomorphism.** On a curve, the group of locally principal Weil divisors
maps to the group of Cartier divisors, compatibly with local equations. -/
def toCartierDivisorHom (hX : ∀ y : X, coheight y ≤ 1) :
    locallyPrincipalSubgroup X →+ Scheme.CartierDivisor X where
  toFun D := IsLocallyPrincipal.cartierDivisor hX (mem_locallyPrincipalSubgroup.mp D.2)
  map_zero' := IsLocallyPrincipal.cartierDivisor_zero hX
  map_add' D E := IsLocallyPrincipal.cartierDivisor_add hX
    (mem_locallyPrincipalSubgroup.mp D.2) (mem_locallyPrincipalSubgroup.mp E.2)

/-- The Weil-to-Cartier homomorphism computes the Cartier divisor of the underlying divisor. -/
@[simp]
lemma toCartierDivisorHom_apply (hX : ∀ y : X, coheight y ≤ 1)
    (D : locallyPrincipalSubgroup X) :
    toCartierDivisorHom hX D =
      IsLocallyPrincipal.cartierDivisor hX (mem_locallyPrincipalSubgroup.mp D.2) :=
  (rfl)

end Curve

section Noetherian

variable [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

/-- **A principal Weil divisor has the principal Cartier divisor of the same rational function.**
The rational function is a global equation, so the two constructions agree over the whole
scheme. -/
@[simp]
theorem cartierDivisor_principalDivisor (hX : ∀ y : X, coheight y ≤ 1)
    (g : Additive X.functionFieldˣ) :
    IsLocallyPrincipal.cartierDivisor hX (isLocallyPrincipal_principalDivisor g) =
      Scheme.principalCartierDivisorAddHom X g := by
  refine (IsLocallyPrincipal.eq_cartierDivisor hX _ fun x ↦ ?_).symm
  have hne : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  refine ⟨⊤, hne, g, trivial, ?_, ?_⟩
  · intro y _
    rw [WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord]
  · exact Scheme.principalCartierDivisorAddHom_restrict X g ⊤

/-- The Weil-to-Cartier homomorphism carries principal Weil divisors to principal Cartier
divisors. -/
theorem toCartierDivisorHom_principalDivisor (hX : ∀ y : X, coheight y ≤ 1)
    (g : Additive X.functionFieldˣ) :
    toCartierDivisorHom hX ⟨(WeilDivisor.OrderSystem.ofScheme X).principalDivisor g,
        principalSubgroup_le_locallyPrincipalSubgroup
          ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor_mem_principalSubgroup g)⟩ =
      Scheme.principalCartierDivisorAddHom X g :=
  cartierDivisor_principalDivisor hX g

end Noetherian

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
