/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.SplittingModule
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Augmentation
public import TauCeti.RepresentationTheory.Homological.TateCohomology.TrivialityCriterion
import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree

/-!
# Cohomological triviality of the splitting module

Let `G` be a finite group, `k` a commutative ring without additive torsion, `A` a representation
of `G` over `k` and `u ∈ H²(G, A)`. Suppose that for every subgroup `S` of `G` of prime-power
order

* `H¹(S, A) = 0`,
* the restriction of `u` generates `H²(S, A)`, and
* `H²(S, A)` has as many elements as `k ⧸ |S|k`.

Then the splitting module `A(u)` of `u` (`Rep.splittingModule`), the extension
`0 → A → A(u) → I_G → 0` of the augmentation ideal by `A` attached to `u`, is cohomologically
trivial: its Tate cohomology vanishes on every subgroup in every degree
(`TauCeti.TateCohomology.isZero_res_splittingModule`). For `k = ℤ` these are Tate's hypotheses
(J. Tate, *The higher dimensional cohomology groups of class field theory*, 1952), with
`ℤ ⧸ |S|ℤ` of order `|S|`; for `k = ℤ_p` the order of `ℤ_p ⧸ |S|ℤ_p` is the `p`-part of `|S|`.

The proof is the second dimension shift of Tate's theorem (Milne, *Class Field Theory*, II,
proof of Theorem 3.11). On a subgroup `S` of prime-power order, the long exact sequence of
`0 → A → A(u) → I_G → 0` reads

`H¹(S, A) → H¹(S, A(u)) → H¹(S, I_G) → H²(S, A) → H²(S, A(u)) → H²(S, I_G)`.

The connecting map is onto, because `u` restricts to a generator of `H²(S, A)` and dies in
`H²(S, A(u))` (`Rep.map_splittingModuleIncl_res_eq_zero`); its source `H¹(S, I_G)` is, by the
augmentation dimension shift, `H-hat^0(S, k) = k ⧸ |S|k`
(`TauCeti.TateCohomology.H0LinearEquivTrivial`), of the same finite order as its target, so it
is a bijection. With `H¹(S, A) = 0` and `H²(S, I_G) = 0` this makes
`H¹(S, A(u))` and `H²(S, A(u))` vanish, and Tate's cohomological triviality criterion
(`TauCeti.TateCohomology.isZero_of_forall_isPGroup`) concludes.

## Main statements

* `TauCeti.TateCohomology.isZero_res_splittingModule`: the splitting module of a class satisfying
  Tate's hypotheses on the subgroups of prime-power order is cohomologically trivial.

## References

* J. Tate, *The higher dimensional cohomology groups of class field theory*, Ann. of Math. 56
  (1952), 294–297.
* J. S. Milne, *Class Field Theory*, Chapter II, Theorems 3.10 and 3.11.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G]

variable (A : Rep k G) (u : groupCohomology A 2) [IsAddTorsionFree k]

/-- On a finite subgroup `S` on which `H¹(S, A) = 0`, the restriction of `u` generates
`H²(S, A)` and `H²(S, A)` has the finite order of `k ⧸ |S|k`, the splitting module has vanishing
first and second cohomology. -/
private theorem isZero_groupCohomology_res_splittingModule (S : Subgroup G) [Finite S]
    (h1 : IsZero (groupCohomology (res S.subtype A) 1))
    (hgen : ∀ x : groupCohomology (res S.subtype A) 2,
      ∃ m : ℤ, m • groupCohomology.map S.subtype (𝟙 (res S.subtype A)) 2 u = x)
    [Finite (k ⧸ Ideal.span {(Nat.card S : k)})]
    (hcard : Nat.card (groupCohomology (res S.subtype A) 2) =
      Nat.card (k ⧸ Ideal.span {(Nat.card S : k)})) :
    IsZero (groupCohomology (res S.subtype (splittingModule A u)) 1) ∧
      IsZero (groupCohomology (res S.subtype (splittingModule A u)) 2) := by
  have := Fintype.ofFinite S
  have hX := splittingModuleSES_res_shortExact A u S.subtype
  -- `splittingModuleSES` is not exposed: name its maps so that the sequence below computes.
  rw [splittingModuleSES_def] at hX
  let X := (ShortComplex.mk (splittingModuleIncl A u) (splittingModuleProj A u)
    (splittingModuleIncl_comp_splittingModuleProj A u)).map (resFunctor S.subtype)
  let δ := groupCohomology.δ hX 1 2 rfl
  -- `H¹(S, I_G)` is `H-hat^0(S, k) = k ⧸ |S|k`, by the augmentation dimension shift.
  have hcardI : Nat.card (groupCohomology X.X₃ 1) =
      Nat.card (k ⧸ Ideal.span {(Nat.card S : k)}) := by
    refine (Nat.card_congr
      ((_root_.TateCohomology.isoGroupCohomology 1).app X.X₃).toLinearEquiv.toEquiv).symm.trans ?_
    refine (Nat.card_congr (augmentationδIso k S 0).toLinearEquiv.toEquiv).symm.trans ?_
    -- The restriction of the trivial representation of `G` is the trivial representation of `S`.
    exact Nat.card_congr (H0LinearEquivTrivial k S).toEquiv
  have : Finite (groupCohomology X.X₃ 1) := Nat.finite_of_card_ne_zero (by
    rw [hcardI]
    exact Nat.card_pos.ne')
  -- The long exact sequence in degrees one and two, elementwise.
  have hex₁ := (ShortComplex.moduleCat_exact_iff _).1
    (groupCohomology.mapShortComplex₁_exact hX (i := 1) (j := 2) rfl)
  have hex₂ (n : ℕ) := (ShortComplex.moduleCat_exact_iff _).1
    (groupCohomology.mapShortComplex₂_exact hX n)
  have hex₃ := (ShortComplex.moduleCat_exact_iff _).1
    (groupCohomology.mapShortComplex₃_exact hX (i := 1) (j := 2) rfl)
  have hzero₁ := fun x ↦ ConcreteCategory.congr_hom
    (groupCohomology.mapShortComplex₁ hX (i := 1) (j := 2) rfl).zero x
  have hzero₃ := fun x ↦ ConcreteCategory.congr_hom
    (groupCohomology.mapShortComplex₃ hX (i := 1) (j := 2) rfl).zero x
  -- The connecting map `H¹(S, I_G) → H²(S, A)` is onto: `u` restricts to a generator and dies in
  -- the splitting module.
  have hδ : Function.Surjective δ := by
    intro x
    obtain ⟨m, rfl⟩ := hgen x
    have hcomp := groupCohomology.map_comp S.subtype (MonoidHom.id S) (𝟙 (res S.subtype A))
      ((resFunctor S.subtype).map (splittingModuleIncl A u)) 2
    obtain ⟨y, hy⟩ := hex₁ (groupCohomology.map S.subtype (𝟙 (res S.subtype A)) 2 u)
      ((ConcreteCategory.congr_hom hcomp u).symm.trans
        (map_splittingModuleIncl_res_eq_zero A u S.subtype))
    exact ⟨m • y, (map_zsmul δ.hom m y).trans (congrArg _ hy)⟩
  have hδbij : Function.Bijective δ :=
    -- `X.X₁` is `res S.subtype A` by definition of `ShortComplex.map`.
    hδ.bijective_of_nat_card_le (by rw [hcardI, ← hcard]; rfl)
  refine ⟨@ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun y y' ↦ ?_⟩,
    @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun y y' ↦ ?_⟩⟩
  · -- `H¹(S, A(u)) → H¹(S, I_G)` is injective, since `H¹(S, A) = 0`, and zero, since `δ` is.
    have h1' : Subsingleton (groupCohomology (res S.subtype A) 1) :=
      ModuleCat.subsingleton_of_isZero h1
    have hzero (z : groupCohomology X.X₂ 1) : z = 0 := by
      obtain ⟨a, rfl⟩ := hex₂ 1 z (hδbij.injective ((hzero₃ z).trans (map_zero δ.hom).symm))
      rw [@Subsingleton.elim _ h1' a 0]
      exact (groupCohomology.mapShortComplex₂ X 1).f.hom.map_zero
    rw [hzero y, hzero y']
  · -- `H²(S, A) → H²(S, A(u))` is zero, since `δ` is onto, and onto, since `H²(S, I_G) = 0`.
    have hI : Subsingleton (groupCohomology (res S.subtype (augmentationIdeal k G)) 2) :=
      ModuleCat.subsingleton_of_isZero
        (TauCeti.groupCohomology.isZero_H2_augmentationIdeal_res (k := k) S)
    have hzero (z : groupCohomology X.X₂ 2) : z = 0 := by
      obtain ⟨a, rfl⟩ := hex₂ 2 z (@Subsingleton.elim _ hI _ _)
      obtain ⟨b, rfl⟩ := hδ a
      exact hzero₁ b
    rw [hzero y, hzero y']

/-- **The splitting module is cohomologically trivial** (Tate; Milne, *Class Field Theory*, II,
proof of Theorem 3.11). Let `G` be a finite group, `k` a commutative ring without additive
torsion, `A` a representation of `G` over `k` and `u ∈ H²(G, A)`. Suppose that for every subgroup
`S` of `G` of prime-power order, `H¹(S, A) = 0`, the restriction of `u` generates `H²(S, A)`,
and `H²(S, A)` has the finite order of `k ⧸ |S|k`. Then the Tate cohomology of the splitting
module `A(u)` vanishes on every subgroup of `G` in every degree. -/
theorem isZero_res_splittingModule [Finite G]
    (h1 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      IsZero (groupCohomology (res S.subtype A) 1))
    (hgen : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      ∀ x : groupCohomology (res S.subtype A) 2,
        ∃ m : ℤ, m • groupCohomology.map S.subtype (𝟙 (res S.subtype A)) 2 u = x)
    (hfin : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      Finite (k ⧸ Ideal.span {(Nat.card S : k)}))
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      Nat.card (groupCohomology (res S.subtype A) 2) =
        Nat.card (k ⧸ Ideal.span {(Nat.card S : k)}))
    (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype (splittingModule A u)) n) := by
  have key (p : ℕ) [Fact p.Prime] (T : Subgroup G) [Fintype T] (hT : IsPGroup p T) :=
    have := hfin p T hT
    isZero_groupCohomology_res_splittingModule A u T (h1 p T hT) (hgen p T hT) (hcard p T hT)
  refine isZero_of_forall_isPGroup (splittingModule A u) (q := 1)
    (fun p _ T _ hT ↦ ?_) (fun p _ T _ hT ↦ ?_) S n
  · exact (key p T hT).1.of_iso
      ((_root_.TateCohomology.isoGroupCohomology 1).app (res T.subtype (splittingModule A u)))
  · exact (key p T hT).2.of_iso
      ((_root_.TateCohomology.isoGroupCohomology 2).app (res T.subtype (splittingModule A u)))

end TauCeti.TateCohomology
