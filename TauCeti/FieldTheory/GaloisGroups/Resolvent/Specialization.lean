/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Symmetric
public import TauCeti.RingTheory.Polynomial.Vieta

/-!
# Specializing the universal resolvent at a polynomial

The universal resolvent of an invariant `Φ` in `n` formal roots is the product of `X - Ψ` over
the permutation orbit of `Φ`, and it is a polynomial in the elementary symmetric polynomials of
the formal roots: `MvPolynomial.existsUnique_orbitProduct` provides the unique integral
expression `D` with `D.map (esymmSubst n) = universalResolvent Φ`.

This file substitutes an actual polynomial into that expression. For a monic `f` of degree `n`,
Vieta's formulas say that the `(k+1)`-st elementary symmetric polynomial of its roots is
`(-1) ^ (k+1) * f.coeff (n - (k+1))`, a function of the coefficients of `f` alone. Substituting
those values is the ring morphism `TauCeti.vietaHom n f`, and `D.map (vietaHom n f)` is the
resolvent of `f`: a polynomial over the coefficient ring of `f`, defined without reference to a
splitting field.

The comparison with the roots is the last step of the descent. In a ring where `f` is the product
of the linear factors attached to a family `x` of roots, the substitution factors as evaluation
at `x` of the elementary symmetric polynomials, so the resolvent of `f` is the orbit product
`MvPolynomial.galResolvent Φ x` formed from the values of the orbit of `Φ` at `x`.

The orbit is taken in `MvPolynomial (Fin n) ℤ` and its elements are then evaluated. Forming the
orbit after mapping the coefficients into the target ring would be a different object: over a
ring where two integral renamings of `Φ` become equal the orbit is smaller, and the product over
it is not the substitution above.

## Main definitions

* `MvPolynomial.galResolvent`: the orbit product `∏ (X - C (Ψ x))` of the values at a root family
  `x` of the permutation orbit of `Φ`.
* `TauCeti.vietaHom`: the substitution of the signed coefficients of `f` for the elementary
  symmetric polynomials of its roots.

## Main results

* `TauCeti.vietaHom_eq_comp_esymmSubst`: **Vieta's formulas** in the form the descent uses, that
  the substitution is evaluation at the roots of the elementary-symmetric substitution.
* `TauCeti.map_vietaHom_eq_galResolvent`: **agreement**, that an integral expression for the
  universal resolvent specializes at `f` to the orbit product at the roots of `f`.
* `TauCeti.vietaHom_map`: the substitution commutes with a ring morphism applied to the
  coefficients of `f`, so the specialization of a fixed integral expression is compatible with
  base change.
* `MvPolynomial.monic_galResolvent` and `MvPolynomial.natDegree_galResolvent`: the orbit product
  is monic of degree the size of the orbit, whatever the values of the orbit at `x` are.
* `MvPolynomial.galResolvent_comp_perm` and `MvPolynomial.galResolvent_map`: it does not depend
  on the numbering of the roots, and it commutes with a ring morphism applied to them.
* `TauCeti.monic_map_vietaHom` and `TauCeti.natDegree_map_vietaHom`: the specialization is monic
  of degree the size of the orbit, over every nonzero coefficient ring.
-/

public section

open Polynomial

namespace MvPolynomial

variable {L : Type*} [CommRing L] {n : ℕ}

/-- The orbit resolvent of `Φ` at a family `x` of roots: the product of `X - Ψ(x)` over the
permutation orbit of `Φ`, each orbit element being an integral polynomial evaluated at `x`. -/
noncomputable def galResolvent (Φ : MvPolynomial (Fin n) ℤ) (x : Fin n → L) : L[X] :=
  ∏ Ψ ∈ renameOrbit Φ,
    (Polynomial.X - Polynomial.C (MvPolynomial.eval₂ (Int.castRingHom L) x Ψ))

/-- The orbit resolvent is the product of the monic linear factors attached to the values at `x`
of the elements of the rename-orbit. -/
theorem galResolvent_def (Φ : MvPolynomial (Fin n) ℤ) (x : Fin n → L) :
    galResolvent Φ x =
      ∏ Ψ ∈ renameOrbit Φ,
        (Polynomial.X - Polynomial.C (MvPolynomial.eval₂ (Int.castRingHom L) x Ψ)) := (rfl)

/-- The orbit resolvent at `x` is the image of the universal resolvent under evaluation at `x`. -/
theorem map_universalResolvent_eq_galResolvent (Φ : MvPolynomial (Fin n) ℤ) (x : Fin n → L) :
    (universalResolvent Φ).map (MvPolynomial.eval₂Hom (Int.castRingHom L) x) =
      galResolvent Φ x := by
  rw [universalResolvent_def, galResolvent_def, Polynomial.map_prod]
  simp

/-- The orbit resolvent is monic: it is a product of monic linear factors. -/
theorem monic_galResolvent (Φ : MvPolynomial (Fin n) ℤ) (x : Fin n → L) :
    (galResolvent Φ x).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- The orbit resolvent has degree the size of the orbit, whatever the values at `x` are. -/
@[simp]
theorem natDegree_galResolvent [Nontrivial L] (Φ : MvPolynomial (Fin n) ℤ) (x : Fin n → L) :
    (galResolvent Φ x).natDegree = (renameOrbit Φ).card := by
  rw [galResolvent, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

/-- Renumbering the roots leaves the orbit resolvent unchanged, since the product runs over the
whole permutation orbit of `Φ`. -/
theorem galResolvent_comp_perm (Φ : MvPolynomial (Fin n) ℤ) (x : Fin n → L)
    (σ : Equiv.Perm (Fin n)) : galResolvent Φ (x ∘ σ) = galResolvent Φ x := by
  have hcomp : (MvPolynomial.eval₂Hom (Int.castRingHom L) fun i => x (σ i)) =
      (MvPolynomial.eval₂Hom (Int.castRingHom L) x).comp
        (↑(MvPolynomial.rename (R := ℤ) (⇑σ)) :
          MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℤ) := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) (fun i => ?_)
    simp
  rw [← map_universalResolvent_eq_galResolvent, ← map_universalResolvent_eq_galResolvent,
    Function.comp_def, hcomp, ← Polynomial.map_map, universalResolvent_map_rename]

/-- The orbit resolvent commutes with a ring morphism applied to the roots. -/
theorem galResolvent_map {M : Type*} [CommRing M] (φ : L →+* M) (Φ : MvPolynomial (Fin n) ℤ)
    (x : Fin n → L) : (galResolvent Φ x).map φ = galResolvent Φ (φ ∘ x) := by
  have hcomp : φ.comp (MvPolynomial.eval₂Hom (Int.castRingHom L) x) =
      MvPolynomial.eval₂Hom (Int.castRingHom M) (φ ∘ x) := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) (fun i => ?_)
    simp
  rw [← map_universalResolvent_eq_galResolvent, ← map_universalResolvent_eq_galResolvent,
    Polynomial.map_map, hcomp]

end MvPolynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- The Vieta substitution of a polynomial `f`, sending the variable `xᵢ` — the slot of the
`(i+1)`-st elementary symmetric polynomial of the roots — to the signed coefficient
`(-1) ^ (i+1) * f.coeff (n - (i+1))`. For a monic `f` of degree `n` these values are the
elementary symmetric polynomials of the roots of `f`, which is
`TauCeti.vietaHom_eq_comp_esymmSubst`. -/
noncomputable def vietaHom (n : ℕ) (f : R[X]) : MvPolynomial (Fin n) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) fun i : Fin n =>
    (-1) ^ ((i : ℕ) + 1) * f.coeff (n - ((i : ℕ) + 1))

/-- The Vieta substitution sends the variable `xᵢ` to the signed coefficient of `f` in degree
`n - (i+1)`. -/
@[simp]
theorem vietaHom_X (f : R[X]) (i : Fin n) :
    vietaHom n f (MvPolynomial.X i) = (-1) ^ ((i : ℕ) + 1) * f.coeff (n - ((i : ℕ) + 1)) := by
  simp [vietaHom]

/-- The Vieta substitution reads only the coefficients of `f`, so mapping them along a ring
morphism `φ` substitutes the images. -/
theorem vietaHom_map (φ : R →+* S) (f : R[X]) :
    vietaHom n (f.map φ) = φ.comp (vietaHom n f) := by
  refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) (fun i => ?_)
  simp [vietaHom]

/-- **Vieta's formulas**, in the form the symmetric descent uses: if `f` is the product of the
linear factors attached to `x`, then substituting the signed coefficients of `f` is the same as
substituting the elementary symmetric polynomials and evaluating at `x`. -/
theorem vietaHom_eq_comp_esymmSubst {f : R[X]} {x : Fin n → R}
    (hf : f = ∏ i, (X - C (x i))) :
    vietaHom n f = (MvPolynomial.eval₂Hom (Int.castRingHom R) x).comp (esymmSubst n) := by
  refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) (fun i => ?_)
  have hk : (i : ℕ) + 1 ≤ Fintype.card (Fin n) := by
    simp
  have hesymm := MvPolynomial.aeval_esymm_eq_coeff_prod_X_sub_C (R := ℤ) (S := R) x hk
  rw [MvPolynomial.aeval_def, algebraMap_int_eq, Fintype.card_fin, ← hf] at hesymm
  rw [vietaHom_X, RingHom.comp_apply, esymmSubst_X, MvPolynomial.coe_eval₂Hom, hesymm]

/-- **Agreement of the two sides of the descent.** An integral expression `D` for the universal
resolvent of `Φ` in the elementary symmetric polynomials specializes, at a polynomial `f` that is
the product of the linear factors attached to `x`, to the orbit product of `Φ` at `x`. -/
theorem map_vietaHom_eq_galResolvent {Φ : MvPolynomial (Fin n) ℤ}
    {D : (MvPolynomial (Fin n) ℤ)[X]}
    (hD : D.map (esymmSubst n) = MvPolynomial.universalResolvent Φ) {f : R[X]} {x : Fin n → R}
    (hf : f = ∏ i, (X - C (x i))) :
    D.map (vietaHom n f) = MvPolynomial.galResolvent Φ x := by
  rw [vietaHom_eq_comp_esymmSubst hf, ← Polynomial.map_map, hD,
    MvPolynomial.map_universalResolvent_eq_galResolvent]

/-- **The specialization is monic.** An integral expression for the universal resolvent is monic,
and so is its substitution: reading the coefficients of `f` never lowers the leading coefficient. -/
theorem monic_map_vietaHom {Φ : MvPolynomial (Fin n) ℤ} {D : (MvPolynomial (Fin n) ℤ)[X]}
    (hD : D.map (esymmSubst n) = MvPolynomial.universalResolvent Φ) (f : R[X]) :
    (D.map (vietaHom n f)).Monic :=
  (MvPolynomial.monic_of_map_esymmSubst_eq hD).map _

/-- **The specialization keeps the full degree.** Over every nonzero coefficient ring and for
every `f`, monic or not, the substitution has degree the size of the orbit: what a specialization
can destroy is the distinctness of the orbit values, never the degree. -/
theorem natDegree_map_vietaHom [Nontrivial R] {Φ : MvPolynomial (Fin n) ℤ}
    {D : (MvPolynomial (Fin n) ℤ)[X]}
    (hD : D.map (esymmSubst n) = MvPolynomial.universalResolvent Φ) (f : R[X]) :
    (D.map (vietaHom n f)).natDegree = (MvPolynomial.renameOrbit Φ).card := by
  rw [(MvPolynomial.monic_of_map_esymmSubst_eq hD).natDegree_map,
    MvPolynomial.natDegree_of_map_esymmSubst_eq hD]

/-- **Agreement, from a root enumeration.** Over a domain, a monic `f` of degree `n` whose roots,
with multiplicity, are listed by `x` specializes an integral expression for the universal
resolvent to the orbit product at those roots. -/
theorem map_vietaHom_eq_galResolvent_of_roots [IsDomain R] {Φ : MvPolynomial (Fin n) ℤ}
    {D : (MvPolynomial (Fin n) ℤ)[X]}
    (hD : D.map (esymmSubst n) = MvPolynomial.universalResolvent Φ) {f : R[X]} {x : Fin n → R}
    (hf : f.Monic) (hdeg : f.natDegree = n) (hroots : f.roots = Finset.univ.val.map x) :
    D.map (vietaHom n f) = MvPolynomial.galResolvent Φ x :=
  map_vietaHom_eq_galResolvent hD
    (Polynomial.eq_prod_X_sub_C_of_monic_of_roots_eq hf (by simpa using hdeg) hroots)

end TauCeti
