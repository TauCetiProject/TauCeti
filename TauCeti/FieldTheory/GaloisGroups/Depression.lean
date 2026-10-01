/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Label
public import TauCeti.RingTheory.Polynomial.Roots

/-!
# Translating the variable, and depressed quartics

Replacing `f(X)` by `f(X + t)` for a constant `t` of the base field moves every root of `f` by
`-t`. Since `t` is fixed by every automorphism over the base field, this changes neither the
splitting field nor the Galois action on the roots: the root sets correspond by `x ↦ x + t`,
equivariantly for every automorphism, and so the two Galois images are the same permutation group
read through that bijection. In particular `f(X + t)` and `f` carry the same transitive-group label.

The classical use is depression. Away from characteristic `2` the substitution `X ↦ X - a/4`
carries the quartic `X⁴ + aX³ + bX² + cX + d` to a quartic `X⁴ + pX² + qX + r` without cubic
term, with
```
p = b - 6s², q = c - 2bs + 8s³, r = d - cs + bs² - 3s⁴,   s = a/4.
```
So the label of any quartic is the label of a depressed one, which is the form in which the
resolvent cubic `TauCeti.resolventCubic` is written.

## Main definitions

* `Polynomial.rootSetCompXAddCEquiv`: the bijection `x ↦ x + t` from the roots of `f(X + t)` to
  the roots of `f`.

## Main results

* `Polynomial.isSplittingField_comp_X_add_C_iff`: `f(X + t)` and `f` have the same splitting
  fields.
* `Polynomial.galActionHom_restrict_rootSetCompXAddCEquiv`: the bijection of root sets is
  equivariant for every automorphism of a normal extension in which `f` splits.
* `Polynomial.map_range_galActionHom_comp_X_add_C`: the Galois images of `f(X + t)` and `f`
  correspond along that bijection.
* `TauCeti.hasGaloisLabel_comp_X_add_C_iff`: `f(X + t)` and `f` have the same label.
* `TauCeti.quartic_comp_X_sub_C`, `TauCeti.hasGaloisLabel_quartic_iff_depressed`: the depression
  of a quartic, and its invariance of the label.

## References

* K. Conrad, *Galois groups of cubics and quartics (not in characteristic 2)*, §1.
-/

public section

open Polynomial

namespace Polynomial

section CommRing

variable {R : Type*} [CommRing R]

/-- The bijection `x ↦ x + t` from the roots of `p(X + t)` to the roots of `p`. -/
def rootSetCompXAddCEquiv (p : R[X]) (t : R) (S : Type*) [CommRing S] [IsDomain S]
    [Algebra R S] : (p.comp (X + C t)).rootSet S ≃ p.rootSet S :=
  (Equiv.addRight (algebraMap R S t)).subtypeEquiv fun x => by
    rw [rootSet_comp_X_add_C, Set.mem_preimage, Equiv.coe_addRight]

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra R S]

/-- The bijection `Polynomial.rootSetCompXAddCEquiv` adds `t`. -/
@[simp]
theorem coe_rootSetCompXAddCEquiv_apply (p : R[X]) (t : R) (x : (p.comp (X + C t)).rootSet S) :
    (rootSetCompXAddCEquiv p t S x : S) = x + algebraMap R S t :=
  (rfl)

/-- The inverse of `Polynomial.rootSetCompXAddCEquiv` subtracts `t`. -/
@[simp]
theorem coe_rootSetCompXAddCEquiv_symm_apply (p : R[X]) (t : R) (x : p.rootSet S) :
    ((rootSetCompXAddCEquiv p t S).symm x : S) = x - algebraMap R S t := by
  obtain ⟨y, rfl⟩ := (rootSetCompXAddCEquiv p t S).surjective x
  simp

end CommRing

section Field

variable {F : Type*} [Field F]

/-- `p(X + t)` splits in an extension exactly when `p` does. -/
theorem splits_map_comp_X_add_C_iff {L : Type*} [Field L] [Algebra F L] {p : F[X]} {t : F} :
    ((p.comp (X + C t)).map (algebraMap F L)).Splits ↔ (p.map (algebraMap F L)).Splits := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.comp_X_add_C (algebraMap F L (-t))
    simpa [Polynomial.map_comp, comp_assoc, add_assoc] using this
  · simpa [Polynomial.map_comp] using h.comp_X_add_C (algebraMap F L t)

/-- `p(X + t)` and `p` have the same splitting fields: the roots of one are the roots of the other
moved by an element of the base field, so they generate the same subalgebra. -/
theorem isSplittingField_comp_X_add_C_iff {L : Type*} [Field L] [Algebra F L] {p : F[X]}
    {t : F} : IsSplittingField F L (p.comp (X + C t)) ↔ IsSplittingField F L p := by
  have hadj : Algebra.adjoin F ((p.comp (X + C t)).rootSet L) =
      Algebra.adjoin F (p.rootSet L) := by
    rw [rootSet_comp_X_add_C]
    refine le_antisymm (Algebra.adjoin_le fun x hx => ?_) (Algebra.adjoin_le fun x hx => ?_)
    · have hx : x + algebraMap F L t ∈ p.rootSet L := hx
      have hmem := sub_mem (Algebra.subset_adjoin (R := F) hx)
        (Subalgebra.algebraMap_mem (Algebra.adjoin F (p.rootSet L)) t)
      rwa [add_sub_cancel_right] at hmem
    · have hx' : x - algebraMap F L t ∈ (· + algebraMap F L t) ⁻¹' p.rootSet L := by
        rwa [Set.mem_preimage, sub_add_cancel]
      have hmem := add_mem (Algebra.subset_adjoin (R := F) hx')
        (Subalgebra.algebraMap_mem (Algebra.adjoin F _) t)
      rwa [sub_add_cancel] at hmem
  refine ⟨fun h => ⟨splits_map_comp_X_add_C_iff.mp h.splits', ?_⟩,
    fun h => ⟨splits_map_comp_X_add_C_iff.mpr h.splits', ?_⟩⟩
  · rw [← hadj]
    exact h.adjoin_rootSet'
  · rw [hadj]
    exact h.adjoin_rootSet'

variable {E : Type*} [Field E] [Algebra F E] (p : F[X]) (t : F)

/-- **The translation of roots is Galois-equivariant.** For an automorphism `ϕ` of an extension
in which `p` splits, moving a root of `p(X + t)` by `t` and then applying `ϕ` agrees with applying
`ϕ` and then moving by `t`, since `ϕ` fixes `t`. -/
theorem galActionHom_restrict_rootSetCompXAddCEquiv [Fact (p.map (algebraMap F E)).Splits]
    [Fact ((p.comp (X + C t)).map (algebraMap F E)).Splits] (ϕ : Gal(E/F))
    (x : (p.comp (X + C t)).rootSet E) :
    Gal.galActionHom p E (Gal.restrict p E ϕ) (rootSetCompXAddCEquiv p t E x) =
      rootSetCompXAddCEquiv p t E
        (Gal.galActionHom (p.comp (X + C t)) E (Gal.restrict (p.comp (X + C t)) E ϕ) x) := by
  apply Subtype.ext
  simp [Gal.galActionHom_restrict]

/-- **The Galois images of `p(X + t)` and `p` correspond.** Read through the bijection
`x ↦ x + t` of root sets, the permutations of the roots of `p(X + t)` induced by its Galois group
are exactly those of the roots of `p` induced by the Galois group of `p`. The roots may be taken in
any normal extension in which `p` splits. -/
theorem map_range_galActionHom_comp_X_add_C [Normal F E] [Fact (p.map (algebraMap F E)).Splits]
    [Fact ((p.comp (X + C t)).map (algebraMap F E)).Splits] :
    (Gal.galActionHom (p.comp (X + C t)) E).range.map
        (rootSetCompXAddCEquiv p t E).permCongrHom.toMonoidHom =
      (Gal.galActionHom p E).range := by
  have key : ∀ ϕ : Gal(E/F),
      (rootSetCompXAddCEquiv p t E).permCongrHom.toMonoidHom
          (Gal.galActionHom (p.comp (X + C t)) E (Gal.restrict (p.comp (X + C t)) E ϕ)) =
        Gal.galActionHom p E (Gal.restrict p E ϕ) := by
    intro ϕ
    ext y
    obtain ⟨x, rfl⟩ := (rootSetCompXAddCEquiv p t E).surjective y
    simp only [MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      Equiv.symm_apply_apply, galActionHom_restrict_rootSetCompXAddCEquiv]
  ext σ
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨τ, rfl⟩, rfl⟩
    obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective (p.comp (X + C t)) E τ
    exact ⟨_, (key ϕ).symm⟩
  · rintro ⟨τ, rfl⟩
    obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective p E τ
    exact ⟨_, ⟨_, rfl⟩, key ϕ⟩

end Field

end Polynomial

namespace TauCeti

variable {F : Type*} [Field F]

/-- **Translating the variable does not change the label.** `f(X + t)` carries the
transitive-group label `j` exactly when `f` does. -/
@[simp]
theorem hasGaloisLabel_comp_X_add_C_iff {f : F[X]} {t : F} {n : ℕ}
    {j : TransitiveGroupIndex n} :
    HasGaloisLabel (f.comp (X + C t)) j ↔ HasGaloisLabel f j := by
  set g := f.comp (X + C t) with hg
  set L := f.SplittingField
  have : Fact (f.map (algebraMap F L)).Splits := ⟨SplittingField.splits f⟩
  have : Fact (g.map (algebraMap F L)).Splits :=
    ⟨splits_map_comp_X_add_C_iff.mpr (SplittingField.splits f)⟩
  have : Fact (g.map (algebraMap F g.SplittingField)).Splits := ⟨SplittingField.splits g⟩
  -- Read in the splitting field of `f` and then moved by `t`, the Galois image of `g` in its own
  -- splitting field is the Galois image of `f`.
  let ε : g.rootSet g.SplittingField ≃ f.rootSet L :=
    (Gal.rootsEquivRoots g g.SplittingField L).trans (rootSetCompXAddCEquiv f t L)
  have hε : (Gal.galActionHom g g.SplittingField).range.map ε.permCongrHom.toMonoidHom =
      (Gal.galActionHom f L).range := by
    rw [← map_range_galActionHom_comp_X_add_C (E := L) f t]
    simp only [MonoidHom.map_range]
    congr 1
    ext σ x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
      Gal.galActionHom_eq_permCongr g g.SplittingField L σ]
    simp only [ε, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      Equiv.trans_apply, Equiv.symm_trans_apply]
  have key : ∀ e : f.rootSet L ≃ Fin n,
      (Gal.galActionHom g g.SplittingField).range.map (ε.trans e).permCongrHom.toMonoidHom =
        (Gal.galActionHom f L).range.map e.permCongrHom.toMonoidHom := by
    intro e
    rw [← hε, Subgroup.map_map]
    congr 1
  have hdeg : g.natDegree = f.natDegree := by simp [hg, natDegree_comp]
  constructor
  · intro h
    have hsep := separable_comp_X_add_C_iff.mp h.separable
    have hn : f.natDegree = n := hdeg ▸ h.natDegree_eq
    subst hn
    obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hsep
    refine HasGaloisLabel.mk hsep rfl e ?_
    rw [← key]
    exact h.transitiveGroupLabel _
  · intro h
    have hn := h.natDegree_eq
    subst hn
    obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f h.separable
    refine HasGaloisLabel.mk (separable_comp_X_add_C_iff.mpr h.separable) hdeg (ε.trans e) ?_
    rw [key]
    exact h.transitiveGroupLabel e

/-- **The depression of a quartic.** Substituting `X - s` into `X⁴ + 4s X³ + bX² + cX + d`
removes the cubic term. The identity holds over every commutative ring. -/
theorem quartic_comp_X_sub_C {R : Type*} [CommRing R] (s b c d : R) :
    (X ^ 4 + C (4 * s) * X ^ 3 + C b * X ^ 2 + C c * X + C d).comp (X - C s) =
      X ^ 4 + C (b - 6 * s ^ 2) * X ^ 2 + C (c - 2 * b * s + 8 * s ^ 3) * X +
        C (d - c * s + b * s ^ 2 - 3 * s ^ 4) := by
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, ofNat_comp, map_sub, map_add, map_mul,
    map_pow, map_ofNat]
  ring

/-- **Depression does not change the label.** Away from characteristic `2`, the quartic
`X⁴ + aX³ + bX² + cX + d` carries the same label as the depressed quartic `X⁴ + pX² + qX + r`
obtained from it by the substitution `X ↦ X - a/4`. -/
theorem hasGaloisLabel_quartic_iff_depressed (hchar : ringChar F ≠ 2) (a b c d : F)
    {j : TransitiveGroupIndex 4} :
    HasGaloisLabel (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) j ↔
      HasGaloisLabel (X ^ 4 + C (b - 6 * (a / 4) ^ 2) * X ^ 2 +
        C (c - 2 * b * (a / 4) + 8 * (a / 4) ^ 3) * X +
        C (d - c * (a / 4) + b * (a / 4) ^ 2 - 3 * (a / 4) ^ 4)) j := by
  have h4 : (4 : F) * (a / 4) = a := by
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    have : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]
      exact mul_ne_zero h2 h2
    field_simp
  rw [← quartic_comp_X_sub_C, h4, sub_eq_add_neg, ← C_neg, hasGaloisLabel_comp_X_add_C_iff]

end TauCeti
