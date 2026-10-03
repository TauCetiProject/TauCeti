/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RepresentationTheory.Invariants
import TauCeti.FieldTheory.GaloisCohomology.Hilbert90
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Solvable

/-!
# Reducing the bound on `H²(Gal(L/K), Lˣ)` to subextensions of prime degree

Let `L/K` be a finite Galois extension of fields whose Galois group is solvable. This file shows
that the order of the relative Brauer group `H²(Gal(L/K), Lˣ)` divides `[L : K]` as soon as the
same holds for every Galois subextension `F/E` of `L/K` of prime degree
(`TauCeti.natCard_groupCohomology_two_units_dvd_finrank`).

This is the field-theoretic form of the group-cohomological reduction
`TauCeti.groupCohomology.natCard_groupCohomology_two_dvd_natCard`, whose two hypotheses about
subgroups `H` of `Gal(L/K)` and their normal subgroups `N` are discharged by Galois theory:

* `H` is the Galois group of `L` over the fixed field `E` of `H`, so `H¹(H, Lˣ) = 0` is Noether's
  form of Hilbert's Theorem 90 for `L/E` (`TauCeti.isZero_groupCohomology_one_res_units`, in
  `TauCeti.FieldTheory.GaloisCohomology.Hilbert90`);
* for `F` the fixed field of `N`, the quotient `H ⧸ N` is `Gal(F/E)` and the `N`-invariant units
  of `L` are the units of `F`, compatibly with the two actions, so `H²(H ⧸ N, (Lˣ)^N)` is
  `H²(Gal(F/E), Fˣ)` and `[H : N] = [F : E]`.

For a finite Galois extension of nonarchimedean local fields the Galois group is solvable and
every subextension is again an extension of local fields, of which those of prime degree are
cyclic. So the local bound `#H²(Gal(L/K), Lˣ) ∣ [L : K]` reduces to cyclic extensions of prime
degree, where it is a Herbrand quotient computation.

## Main statements

* `TauCeti.natCard_groupCohomology_two_units_dvd_finrank`: if `Gal(L/K)` is solvable and every
  Galois subextension `F/E` of prime degree satisfies `#H²(Gal(F/E), Fˣ) ∣ [F : E]`, then
  `#H²(Gal(L/K), Lˣ) ∣ [L : K]`.

## References

* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §1.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter III, §2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Limits IntermediateField Module

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {H : Type} [Group H] [Finite H] {f : H →* Gal(L/K)} (hf : Function.Injective f)

section Quotient

/- The image `Q` of `N` in `Gal(L/E)` is a variable, tied to `N` by a hypothesis `hQ`, rather than
the term `N.map (galEquivOfInjective hf)`: the fixed field of `Q` then carries its field and
algebra instances without the elaborator unfolding that term. -/

variable (N : Subgroup H) [N.Normal] {Q : Subgroup Gal(L/fixedField f.range)}
  [Q.Normal]

/-- For `Q` the image of a normal subgroup `N` of `H` in `Gal(L/E)`, the quotient `H ⧸ N` is the
Galois group of the fixed field of `Q` over `E`. -/
private def quotientGalEquiv
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q) :
    H ⧸ N ≃* Gal(fixedField Q/fixedField f.range) :=
  (QuotientGroup.congr N Q (galEquivOfInjective hf) hQ).trans (IsGalois.normalAutEquivQuotient Q)

private theorem quotientGalEquiv_mk_apply
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q)
    (h : H) (x : fixedField Q) :
    (quotientGalEquiv hf N hQ (h : H ⧸ N) x : L) = f h x := by
  simp [quotientGalEquiv, IsGalois.normalAutEquivQuotient_apply,
    AlgEquiv.restrictNormalHom_apply]

omit [FiniteDimensional K L] [N.Normal] [Q.Normal] in
/-- An automorphism acts on a unit of a field, in the representation `Rep.ofMulDistribMulAction`,
by acting on its underlying element. -/
private theorem coe_toMul_ofMulDistribMulAction_ρ_apply {E F : Type} [Field E] [Field F]
    [Algebra E F] (σ : Gal(F/E)) (y : (Rep.ofMulDistribMulAction Gal(F/E) Fˣ).V) :
    ((Additive.toMul (Rep.toAdditive ((Rep.ofMulDistribMulAction Gal(F/E) Fˣ).ρ σ y)) : Fˣ) : F) =
      σ (Additive.toMul (Rep.toAdditive y) : Fˣ) :=
  rfl

omit [FiniteDimensional K L] [N.Normal] [Q.Normal] in
private theorem mem_fixedField_iff_of_map_eq
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q) (y : L) :
    y ∈ fixedField Q ↔ ∀ n ∈ N, f n y = y := by
  subst hQ
  simp [mem_fixedField_iff, galEquivOfInjective_apply]

omit [FiniteDimensional K L] [N.Normal] [Q.Normal] in
/-- A unit of `L` is invariant under `N` exactly when it lies in the fixed field of `Q`. -/
private theorem mem_invariants_iff
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q)
    (x : Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) :
    x ∈ Representation.invariants
        ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).ρ.comp N.subtype) ↔
      (((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x).toMul : Lˣ) : L) ∈ fixedField Q := by
  rw [mem_fixedField_iff_of_map_eq hf N hQ, Representation.mem_invariants, Subtype.forall]
  exact forall₂_congr fun n _ =>
    (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).injective.eq_iff.symm.trans <|
      Additive.toMul.injective.eq_iff.symm.trans Units.ext_iff

/-- An `N`-invariant unit of `L`, as a unit of the fixed field of `Q`. -/
private def invariantsToUnits
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q)
    (x : ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).V) :
    (fixedField Q)ˣ :=
  Units.mk0 ⟨(((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x.1).toMul : Lˣ) : L),
      (mem_invariants_iff hf N hQ _).1 x.2⟩
    (fun h => Units.ne_zero _ (congrArg Subtype.val h))

omit [FiniteDimensional K L] [Q.Normal] in
/-- The underlying element of `L` of `invariantsToUnits x` is that of `x`. -/
private theorem coe_invariantsToUnits
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q)
    (x : ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).V) :
    ((invariantsToUnits hf N hQ x : fixedField Q) : L) =
      (((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x.1).toMul : Lˣ) : L) :=
  rfl

omit [FiniteDimensional K L] [Q.Normal] in
/-- Addition of `N`-invariant units in the representation is multiplication of units of the fixed
field of `Q`. -/
private theorem invariantsToUnits_add
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q)
    (x y : ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).V) :
    invariantsToUnits hf N hQ (x + y) = invariantsToUnits hf N hQ x * invariantsToUnits hf N hQ y :=
  Units.ext <| Subtype.ext <| by
    rw [Units.val_mul, MulMemClass.coe_mul, coe_invariantsToUnits, coe_invariantsToUnits,
      coe_invariantsToUnits, Submodule.coe_add, map_add, toMul_add, Units.val_mul]

/-- A unit of the fixed field of `Q`, as an `N`-invariant unit of `L`. -/
private def unitsToInvariants
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q)
    (u : (fixedField Q)ˣ) :
    ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).V :=
  ⟨(Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm
      (Additive.ofMul (Units.map (algebraMap (fixedField Q) L : fixedField Q →* L) u)),
    (mem_invariants_iff hf N hQ _).2 (u : fixedField Q).2⟩

/-- The `N`-invariant units of `L` are the units of the fixed field of `Q`. -/
private def invariantsUnitsEquiv
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q) :
    ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).V ≃ₗ[ℤ]
      (Rep.ofMulDistribMulAction Gal(fixedField Q/fixedField f.range) (fixedField Q)ˣ).V :=
  AddEquiv.toIntLinearEquiv
  { toFun x := (Rep.toAdditive (M := Gal(fixedField Q/fixedField f.range))
      (G := (fixedField Q)ˣ)).symm (Additive.ofMul (invariantsToUnits hf N hQ x))
    invFun u := unitsToInvariants hf N hQ (Rep.toAdditive
      (M := Gal(fixedField Q/fixedField f.range)) (G := (fixedField Q)ˣ) u).toMul
    left_inv _ := by
      apply Subtype.ext
      apply (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).injective
      exact Additive.toMul.injective <| Units.ext <| by simp [unitsToInvariants, invariantsToUnits]
    right_inv _ := by
      apply (Rep.toAdditive (M := Gal(fixedField Q/fixedField f.range))
        (G := (fixedField Q)ˣ)).injective
      exact Additive.toMul.injective <| Units.ext <| Subtype.ext <| by
        simp [unitsToInvariants, invariantsToUnits]
    map_add' x y := by
      apply (Rep.toAdditive (M := Gal(fixedField Q/fixedField f.range))
        (G := (fixedField Q)ˣ)).injective
      simp only [map_add, AddEquiv.apply_symm_apply, ← ofMul_mul]
      exact congrArg Additive.ofMul (invariantsToUnits_add hf N hQ x y) }

omit [FiniteDimensional K L] [Q.Normal] in
/-- The underlying element of `L` of the image of an `N`-invariant unit under
`invariantsUnitsEquiv`. -/
private theorem coe_toMul_invariantsUnitsEquiv_apply
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q)
    (x : ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).V) :
    (((Additive.toMul (Rep.toAdditive (M := Gal(fixedField Q/fixedField f.range))
        (G := (fixedField Q)ˣ) (invariantsUnitsEquiv hf N hQ x)) : (fixedField Q)ˣ) :
          fixedField Q) : L) =
      ((Additive.toMul (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x.1) : Lˣ) : L) :=
  rfl

omit [FiniteDimensional K L] [Finite H] [Q.Normal] in
/-- The class of `h` acts on an `N`-invariant unit of `L` through the automorphism `f h`. -/
private theorem coe_toMul_quotientToInvariants_ρ_mk_apply (h : H)
    (x : ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).V) :
    ((Additive.toMul (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)
        (((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).ρ
          (h : H ⧸ N) x).1) : Lˣ) : L) =
      f h ((Additive.toMul (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x.1) : Lˣ) : L) :=
  rfl

/-- `invariantsUnitsEquiv` intertwines the action of `H ⧸ N` with that of the Galois group of the
fixed field of `Q` over `E`. -/
private theorem invariantsUnitsEquiv_ρ_mk_apply
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q) (h : H)
    (x : ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).V) :
    invariantsUnitsEquiv hf N hQ
        (((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N).ρ
          (h : H ⧸ N) x) =
      (Rep.ofMulDistribMulAction Gal(fixedField Q/fixedField f.range) (fixedField Q)ˣ).ρ
        (quotientGalEquiv hf N hQ h) (invariantsUnitsEquiv hf N hQ x) := by
  apply (Rep.toAdditive (M := Gal(fixedField Q/fixedField f.range))
    (G := (fixedField Q)ˣ)).injective
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  rw [coe_toMul_ofMulDistribMulAction_ρ_apply, quotientGalEquiv_mk_apply,
    coe_toMul_invariantsUnitsEquiv_apply, coe_toMul_invariantsUnitsEquiv_apply,
    coe_toMul_quotientToInvariants_ρ_mk_apply]

/-- The cohomology of `H ⧸ N` acting on the `N`-invariant units of `L` is the cohomology of the
Galois group of the fixed field of `Q` over `E` acting on the units of that field. -/
private def groupCohomologyQuotientToInvariantsIso
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q) (n : ℕ) :
    groupCohomology ((Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)).quotientToInvariants N)
        n ≅
      groupCohomology
        (Rep.ofMulDistribMulAction Gal(fixedField Q/fixedField f.range) (fixedField Q)ˣ) n :=
  groupCohomology.mapIso (quotientGalEquiv hf N hQ) (invariantsUnitsEquiv hf N hQ) (fun q => by
    induction q using QuotientGroup.induction_on with | H h => ?_
    ext x
    exact invariantsUnitsEquiv_ρ_mk_apply hf N hQ h x) n

end Quotient

/-- **The bound on `H²(Gal(L/K), Lˣ)` reduces to subextensions of prime degree.** Let `L/K` be a
finite Galois extension with solvable Galois group. If every Galois subextension `F/E` of `L/K` of
prime degree satisfies `#H²(Gal(F/E), Fˣ) ∣ [F : E]`, then `#H²(Gal(L/K), Lˣ) ∣ [L : K]`. -/
theorem natCard_groupCohomology_two_units_dvd_finrank [IsGalois K L]
    [Group.IsSolvable Gal(L/K)]
    (hprime : ∀ (E : IntermediateField K L) (F : IntermediateField E L) [IsGalois E F],
      (finrank E F).Prime →
        Nat.card (groupCohomology (Rep.ofMulDistribMulAction Gal(F/E) Fˣ) 2) ∣ finrank E F) :
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) ∣ finrank K L := by
  rw [← IsGalois.card_aut_eq_finrank]
  refine groupCohomology.natCard_groupCohomology_two_dvd_natCard _
    (fun H _ f hf => have := Finite.of_injective f hf; isZero_groupCohomology_one_res_units hf)
    (fun H _ f hf N _ hp => ?_)
  have := Finite.of_injective f hf
  let Q := N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range))
  have : Q.Normal := Subgroup.Normal.map ‹_› _ (galEquivOfInjective hf).surjective
  have hindex : N.index = finrank (fixedField f.range) (fixedField Q) := by
    rw [← IsGalois.card_aut_eq_finrank, Subgroup.index,
      Nat.card_congr (quotientGalEquiv hf N rfl).toEquiv]
  rw [Nat.card_congr (groupCohomologyQuotientToInvariantsIso hf N rfl 2).toLinearEquiv.toEquiv,
    hindex]
  exact hprime _ _ (hindex ▸ hp)

end TauCeti
