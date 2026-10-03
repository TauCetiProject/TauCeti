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
  form of Hilbert's Theorem 90 for `L/E` (`TauCeti.isZero_groupCohomology_one_res_units`);
* for `F` the fixed field of `N`, the quotient `H ⧸ N` is `Gal(F/E)` and the `N`-invariant units
  of `L` are the units of `F`, compatibly with the two actions, so `H²(H ⧸ N, (Lˣ)^N)` is
  `H²(Gal(F/E), Fˣ)` and `[H : N] = [F : E]`.

For a finite Galois extension of nonarchimedean local fields the Galois group is solvable and
every subextension is again an extension of local fields, of which those of prime degree are
cyclic. So the local bound `#H²(Gal(L/K), Lˣ) ∣ [L : K]` reduces to cyclic extensions of prime
degree, where it is a Herbrand quotient computation.

## Main statements

* `TauCeti.isZero_groupCohomology_one_res_units`: `H¹(H, Lˣ) = 0` for every group `H` acting on
  `L` through an injective homomorphism `H →* Gal(L/K)`.
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
  {H : Type} [Group H] {f : H →* Gal(L/K)} (hf : Function.Injective f)

/-- An injective homomorphism `f : H →* Gal(L/K)` identifies `H` with the Galois group of `L` over
the fixed field of the image of `f`. -/
private def galEquivOfInjective : H ≃* Gal(L/fixedField f.range) :=
  (MonoidHom.ofInjective hf).trans (subgroupEquivAlgEquiv f.range)

private theorem galEquivOfInjective_apply (h : H) (x : L) :
    galEquivOfInjective hf h x = f h x :=
  (rfl)

/-- The cohomology of `H` acting on `Lˣ` through an injective `f : H →* Gal(L/K)` is the
cohomology of `Gal(L/E)` acting on `Lˣ`, for `E` the fixed field of the image of `f`. -/
private def groupCohomologyResUnitsIso (n : ℕ) :
    groupCohomology (Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) n ≅
      groupCohomology (Rep.ofMulDistribMulAction Gal(L/fixedField f.range) Lˣ) n :=
  groupCohomology.mapIso (galEquivOfInjective hf) (LinearEquiv.refl ℤ _) (fun h => by
    ext x
    exact Additive.toMul.injective (Units.ext (galEquivOfInjective_apply hf h _).symm)) n

include hf in
/-- **Hilbert 90 for a group of automorphisms.** If `f : H →* Gal(L/K)` is injective, then
`H¹(H, Lˣ) = 0` for the action of `H` on `Lˣ` through `f`: the group `H` is the Galois group of
`L` over the fixed field of its image, and Noether's Hilbert 90 applies to that extension. -/
theorem isZero_groupCohomology_one_res_units :
    IsZero (groupCohomology (Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 1) := by
  refine IsZero.of_iso ?_ (groupCohomologyResUnitsIso hf 1)
  -- `Rep.ofAlgebraAutOnUnits` unfolds to `Rep.ofMulDistribMulAction`, and `H1` to degree one.
  have : Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction Gal(L/fixedField f.range) Lˣ) 1) :=
    inferInstanceAs <| Subsingleton <|
      groupCohomology.H1 (Rep.ofAlgebraAutOnUnits (fixedField f.range) L)
  exact ModuleCat.isZero_of_subsingleton _

section Quotient

/- The image `Q` of `N` in `Gal(L/E)` is a variable, tied to `N` by a hypothesis `hQ`, rather than
the term `N.map (galEquivOfInjective hf)`: the fixed field of `Q` then carries its field and
algebra instances without the elaborator unfolding that term. -/

variable [IsGalois K L] (N : Subgroup H) [N.Normal] {Q : Subgroup Gal(L/fixedField f.range)}
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
  rw [quotientGalEquiv, MulEquiv.trans_apply, QuotientGroup.congr_mk,
    IsGalois.normalAutEquivQuotient_apply, AlgEquiv.restrictNormalHom_apply,
    galEquivOfInjective_apply]

omit [IsGalois K L] [N.Normal] [Q.Normal] in
private theorem mem_fixedField_iff_of_map_eq
    (hQ : N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range)) = Q) (y : L) :
    y ∈ fixedField Q ↔ ∀ n ∈ N, f n y = y := by
  subst hQ
  simp [mem_fixedField_iff, galEquivOfInjective_apply]

omit [IsGalois K L] [N.Normal] [Q.Normal] in
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
    map_add' _ _ := by
      apply (Rep.toAdditive (M := Gal(fixedField Q/fixedField f.range))
        (G := (fixedField Q)ˣ)).injective
      -- Addition in the representation is multiplication of units, in `L` as in its subfield.
      exact Additive.toMul.injective <| Units.ext <| Subtype.ext rfl }

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
    apply (Rep.toAdditive (M := Gal(fixedField Q/fixedField f.range))
        (G := (fixedField Q)ˣ)).injective
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    -- Both sides are `f h` applied to the underlying element of `L`. The two `rfl` steps unfold
    -- the actions on `Lˣ` and on `(fixedField Q)ˣ` to the automorphisms `f h` of `L` and
    -- `quotientGalEquiv hf N hQ h` of the fixed field, applied to the underlying elements.
    refine Eq.trans ?_ <|
      (quotientGalEquiv_mk_apply hf N hQ h (invariantsToUnits hf N hQ x)).symm.trans ?_
    · rfl
    · rfl) n

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
    (fun H _ f hf => isZero_groupCohomology_one_res_units hf) (fun H _ f hf N _ hp => ?_)
  let Q := N.map (galEquivOfInjective hf : H →* Gal(L/fixedField f.range))
  have : Q.Normal := Subgroup.Normal.map ‹_› _ (galEquivOfInjective hf).surjective
  have hindex : N.index = finrank (fixedField f.range) (fixedField Q) := by
    rw [← IsGalois.card_aut_eq_finrank, Subgroup.index,
      Nat.card_congr (quotientGalEquiv hf N rfl).toEquiv]
  rw [Nat.card_congr (groupCohomologyQuotientToInvariantsIso hf N rfl 2).toLinearEquiv.toEquiv,
    hindex]
  exact hprime _ _ (hindex ▸ hp)

end TauCeti
