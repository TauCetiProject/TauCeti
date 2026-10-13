/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import TauCeti.Algebra.CharP.Frobenius.PowRingHom

/-!
# The absolute Frobenius of a scheme

Let `p` be a prime and `X` a scheme over `𝔽_p`, that is, a scheme with `p = 0` in `Γ(X, ⊤)`. The
*absolute Frobenius* `F_X : X ⟶ X` is the identity on the underlying topological space and the
`p`-th power map `s ↦ s ^ p` on every ring of sections. It is a morphism of locally ringed spaces
because `s ^ p` is a unit of a local ring only when `s` is.

Every morphism of schemes over `𝔽_p` commutes with the absolute Frobenius
(`AlgebraicGeometry.Scheme.frobenius_naturality`): unlike the relative Frobenius, it is not a
morphism over the base, and it is the input from which the relative Frobenius
`F_{X/S} : X ⟶ X ×_{S, F_S} S` of a scheme over `S` is built in
`TauCeti.AlgebraicGeometry.Frobenius.Relative`. On an affine scheme `Spec R` it is induced by the
`p`-th power map of `R` (`AlgebraicGeometry.Scheme.Spec_map_powRingHom`).

The hypothesis is stated on global sections, as `(p : Γ(X, ⊤)) = 0`, rather than through an
`ExpChar` instance: the ring of sections over the empty open is the zero ring, which has no
exponential characteristic `p`, so the `p`-th power map on sections is `TauCeti.powRingHom`.

## Main definitions

* `AlgebraicGeometry.Scheme.frobenius X p hX`: the absolute Frobenius `F_X : X ⟶ X` of a scheme
  `X` with `hX : (p : Γ(X, ⊤)) = 0`.

## Main results

* `AlgebraicGeometry.Scheme.frobenius_base` and
  `AlgebraicGeometry.Scheme.frobenius_appLE_apply`: `F_X` is the identity on points and the
  `p`-th power map on sections.
* `AlgebraicGeometry.Scheme.natCast_eq_zero_of_hom`: a scheme over a scheme over `𝔽_p` is a
  scheme over `𝔽_p`.
* `AlgebraicGeometry.Scheme.frobenius_naturality`: `F_X ≫ f = f ≫ F_Y` for every `f : X ⟶ Y`.
* `AlgebraicGeometry.Scheme.Spec_map_powRingHom`: the absolute Frobenius of `Spec R` is
  `Spec` of the `p`-th power map of `R`.

## References

* The Stacks Project, chapter Varieties, section Frobenii, for the absolute Frobenius of a scheme
  over `𝔽_p` and its naturality.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {p : ℕ} [hp : Fact p.Prime]

omit hp in
-- The prime `p` vanishes on every open of a scheme on which it vanishes globally.
private theorem natCast_app_eq_zero (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    (p : Γ(X, U)) = 0 := by
  simpa using congr(X.presheaf.map (homOfLE le_top).op $hX)

variable (X p) in
/-- The absolute Frobenius of `X` as a morphism of presheafed spaces: the identity on the
underlying space and the `p`-th power map on sections. -/
private noncomputable def frobeniusHom (hX : (p : Γ(X, ⊤)) = 0) :
    X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 _
  c :=
    { app U := CommRingCat.ofHom (TauCeti.powRingHom Γ(X, U.unop) p (natCast_app_eq_zero hX U.unop))
      naturality U V i := by
        ext s
        exact (TauCeti.powRingHom_apply _ _).trans <|
          (map_pow (X.presheaf.map i).hom s p).symm.trans
            (congrArg _ (TauCeti.powRingHom_apply _ s).symm) }

-- On stalks, the absolute Frobenius is again the `p`-th power map, since it is so on the sections
-- of which every element of the stalk is a germ.
private theorem frobeniusHom_stalkMap_apply (hX : (p : Γ(X, ⊤)) = 0) (x : X)
    (y : X.presheaf.stalk x) : ((frobeniusHom X p hX).stalkMap x).hom y = y ^ p := by
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq y
  refine (PresheafedSpace.stalkMap_germ_apply (frobeniusHom X p hX) U x hxU s).trans ?_
  exact (congrArg _ (TauCeti.powRingHom_apply _ s)).trans
    (map_pow (X.presheaf.germ U x hxU).hom s p)

variable (X p) in
/-- The **absolute Frobenius** `F_X : X ⟶ X` of a scheme `X` in which the prime `p` vanishes: the
identity on the underlying topological space and the `p`-th power map `s ↦ s ^ p` on sections. -/
noncomputable def frobenius (hX : (p : Γ(X, ⊤)) = 0) : X ⟶ X where
  toHom := frobeniusHom X p hX
  prop x := ⟨fun y hy ↦ by
    have h := frobeniusHom_stalkMap_apply hX x y
    exact (isUnit_pow_iff hp.out.ne_zero).1 (h ▸ hy)⟩

/-- The absolute Frobenius is the identity on the underlying topological space. -/
@[simp]
theorem frobenius_base (hX : (p : Γ(X, ⊤)) = 0) : (X.frobenius p hX).base = 𝟙 _ := (rfl)

/-- The absolute Frobenius fixes every point. -/
theorem frobenius_apply (hX : (p : Γ(X, ⊤)) = 0) (x : X) : X.frobenius p hX x = x := (rfl)

/-- The absolute Frobenius pulls back every open to itself. -/
theorem frobenius_preimage (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    X.frobenius p hX ⁻¹ᵁ U = U :=
  (rfl)

-- The absolute Frobenius is the `p`-th power map on sections; `Γ(X, F_X ⁻¹ᵁ U)` is `Γ(X, U)` by
-- definition.
private theorem frobenius_app_apply (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) (s : Γ(X, U)) :
    (X.frobenius p hX).app U s = (s ^ p : Γ(X, U)) :=
  TauCeti.powRingHom_apply _ s

/-- The absolute Frobenius is the `p`-th power map on sections: the section of `X` over `V`
induced by a section `s` over `U ⊇ V` is the `p`-th power of the restriction of `s`. -/
@[simp]
theorem frobenius_appLE_apply (hX : (p : Γ(X, ⊤)) = 0) (U V : X.Opens)
    (e : V ≤ X.frobenius p hX ⁻¹ᵁ U) (s : Γ(X, U)) :
    (X.frobenius p hX).appLE U V e s =
      X.presheaf.map (homOfLE (e.trans (frobenius_preimage hX U).le)).op s ^ p := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, frobenius_app_apply]
  -- `homOfLE e` and the restriction in the statement are the same map `Γ(X, U) ⟶ Γ(X, V)`,
  -- since `F_X ⁻¹ᵁ U` is `U` by definition
  exact map_pow (X.presheaf.map (homOfLE e).op).hom s p

omit hp in
/-- A scheme over a scheme in which `p` vanishes is a scheme in which `p` vanishes. -/
theorem natCast_eq_zero_of_hom (f : X ⟶ Y) (hY : (p : Γ(Y, ⊤)) = 0) : (p : Γ(X, ⊤)) = 0 := by
  simpa using congr(f.appTop $hY)

/-- **Every morphism of schemes over `𝔽_p` commutes with the absolute Frobenius.** -/
@[reassoc]
theorem frobenius_naturality (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y) :
    X.frobenius p hX ≫ f = f ≫ Y.frobenius p hY := by
  refine Scheme.Hom.ext (by rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, frobenius_base,
    frobenius_base, Category.id_comp, Category.comp_id]) fun U ↦ ?_
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.comp_appLE, Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE (f := Y.frobenius p hY)]
  ext s
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, frobenius_appLE_apply, map_pow]
  refine (frobenius_appLE_apply hX _ _ _ _).trans (congrArg (· ^ p) ?_)
  exact congr(($(f.map_appLE _ _)).hom s).symm

/-- On an affine scheme `Spec R`, the absolute Frobenius is induced by the `p`-th power map of
`R`. -/
theorem Spec_map_powRingHom (R : CommRingCat.{u}) (hR : (p : R) = 0) :
    Spec.map (CommRingCat.ofHom (TauCeti.powRingHom R p hR)) =
      (Spec R).frobenius p (by simpa using congr((ΓSpecIso R).inv $hR)) := by
  refine ext_of_isAffine (CommRingCat.hom_ext <| RingHom.ext fun s ↦ ?_)
  have h := congr($(ΓSpecIso_naturality (CommRingCat.ofHom (TauCeti.powRingHom R p hR))).hom s)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    TauCeti.powRingHom_apply, ← map_pow] at h
  exact (ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    (h.trans (congrArg _ (frobenius_app_apply _ ⊤ s).symm))

end AlgebraicGeometry.Scheme
