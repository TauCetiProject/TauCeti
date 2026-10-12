/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.DegreeZero
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.TateTheorem

/-!
# Tate's theorem for a finite normal layer

Let `V ◁ U` be a finite normal layer of a formation with coefficient module `A`, and let
`u ∈ H²(U/V, A^V)`. Tate's theorem says that if, for every subgroup `H` of `U/V`,

* `H¹(H, A^V) = 0`,
* `H²(H, A^V)` has exactly `#H` elements,
* the restriction of `u` to `H` generates `H²(H, A^V)`,

then cup product with `u` is an isomorphism `H^r(U/V, ℤ) ≃ H^{r+2}(U/V, A^V)` in every integer
degree `r` (`TauCeti.ClassFieldTheory.tateTheorem`). The three hypotheses are separate explicit
arguments, quantified over the finite quotient system `H ↦ subgroupLayer H` of the layer, and
the underlying homomorphism of the isomorphism is the cup-product map `cupClass`
(`tateTheorem_toAddMonoidHom`). For a class formation the hypotheses hold for the fundamental
class, which gives the Tate isomorphisms `ClassFormation.tateIso` of Artin–Tate's Main Theorem.

The generic content is `TauCeti.TateCohomology.cup_bijective_of_cupTrivialInt_injective`. This
file connects it to the finite-layer language: Tate cohomology of the layer of a subgroup `H`
is Tate cohomology of `H` with coefficients in the restricted module
(`TauCeti.ClassFieldTheory.NormalLayer.subgroupLayerTateIso`), and the generation hypothesis
together with the order of `H²(U/V, A^V)` gives the degree-zero bijection on the whole Galois
group. The generic theorem needs the vanishing and order hypotheses only on subgroups of
prime-power order, and `cupClass_bijective` is stated in that form; `tateTheorem` is the roadmap's
statement with all three hypotheses over every subgroup.

## Main definitions

* `TauCeti.ClassFieldTheory.tateTheorem`: Tate's theorem for a finite normal layer, as an additive
  equivalence.
* `TauCeti.ClassFieldTheory.ClassFormation.tateIso`: Tate's theorem for a class formation, applied
  to the fundamental class.

## Main statements

* `TauCeti.ClassFieldTheory.cupClass_bijective`: cup product with `u` is bijective in every degree,
  with the vanishing and order hypotheses on subgroups of prime-power order and the generation
  hypothesis on the whole Galois group only.
* `TauCeti.ClassFieldTheory.tateTheorem_toAddMonoidHom`,
  `TauCeti.ClassFieldTheory.ClassFormation.tateIso_toAddMonoidHom`: the isomorphisms are the
  cup-product maps.

## References

* J. Tate, *The higher dimensional cohomology groups of class field theory*, Ann. of Math. 56
  (1952), 294–297.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV §4, Theorem 1.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

section TateTheorem

variable (F : Formation G) (L : NormalLayer G) (u : L.H F 2)

/-- Cup product with a class `u` generating `H²(U/V, A^V)`, a group of order `[U : V]`, is
bijective from `H^r(U/V, ℤ)` to `H^{r+2}(U/V, A^V)` in every integer degree `r`, provided
`H¹(H, A^V) = 0` and `H²(H, A^V)` has exactly `#H` elements for every subgroup `H` of `U/V` of
prime-power order. This is Tate's theorem with the vanishing and order hypotheses on prime-power
subgroups only and the generation hypothesis on the whole Galois group only; its forms on all
subgroups follow. -/
theorem cupClass_bijective
    (h1 : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup L.Gal), IsPGroup p H →
      Subsingleton ((L.subgroupLayer H).H F 1))
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup L.Gal), IsPGroup p H →
      Nat.card ((L.subgroupLayer H).H F 2) = Nat.card H)
    (hcardG : Nat.card (L.H F 2) = L.degree)
    (hgen : ∀ y : L.H F 2, ∃ m : ℤ, m • u = y)
    (r : ℤ) : Function.Bijective (cupClass F L u r) := by
  -- The degree-zero bijection on the whole Galois group.
  have h0 : Function.Bijective
      (TauCeti.TateCohomology.cupTrivialInt (L.rep F) ((L.tateHIsoH F 2).inv u)) := by
    rw [← cupClass_degree_zero_eq_cupTrivialInt]
    exact cupClass_degree_zero_bijective F L u hgen hcardG
  -- The generic theorem, with the hypotheses on subgroups read through `subgroupLayerTateIso`.
  have hbij := TauCeti.TateCohomology.cup_bijective_of_cupTrivialInt_injective (L.rep F)
    ((L.tateHIsoH F 2).inv u) h0.injective
    (fun p _ H _ hH ↦
      haveI := h1 p H hH
      (ModuleCat.isZero_of_subsingleton _).of_iso
        ((L.subgroupLayerTateIso F H 1).symm ≪≫ (L.subgroupLayer H).tateHIsoH F 1))
    (fun p _ H _ hH ↦
      (Nat.card_congr ((L.subgroupLayerTateIso F H 2).symm ≪≫
        (L.subgroupLayer H).tateHIsoH F 2).toLinearEquiv.toEquiv).trans (hcard p H hH))
    r (r + 2) rfl
  have heq : ⇑(cupClass F L u r) =
      ⇑((tateCohomologyFunctor (r + 2)).map (λ_ (L.rep F)).hom) ∘
        fun x : L.TrivialTateH r ↦ TauCeti.TateCohomology.cup (Rep.trivial ℤ L.Gal ℤ) (L.rep F)
          r 2 (r + 2) rfl x ((L.tateHIsoH F 2).inv u) :=
    funext fun x ↦ cupClass_apply F L u r x
  rw [heq]
  exact (ConcreteCategory.bijective_of_isIso _).comp hbij

/-- **Tate's theorem** (J. Tate, *The higher dimensional cohomology groups of class field theory*,
Ann. of Math. 56 (1952); Artin–Tate, Chapter XIV §4), with its hypotheses stated one by one over
the finite quotient system `H ↦ L.subgroupLayer H`:

* `h1`: `H¹(H, A^V) = 0` for every subgroup `H ≤ U/V`;
* `hcard`: `H²(H, A^V)` has exactly `#H` elements;
* `hgen`: the restriction of `u` to the layer of `H` generates that layer's `H²`.

Then cup product with `u` is an isomorphism `H^r(U/V, ℤ) ≃ H^{r+2}(U/V, A^V)` in every integer
degree `r`; its underlying homomorphism is `cupClass F L u r` (`tateTheorem_toAddMonoidHom`). -/
def tateTheorem
    (h1 : ∀ H : Subgroup L.Gal, Subsingleton ((L.subgroupLayer H).H F 1))
    (hcard : ∀ H : Subgroup L.Gal, Nat.card ((L.subgroupLayer H).H F 2) = Nat.card H)
    (hgen : ∀ (H : Subgroup L.Gal) (x : (L.subgroupLayer H).H F 2),
      ∃ m : ℤ, x = m • (L.subgroupRestriction H).cohomologyRes F 2 u)
    (r : ℤ) : L.TrivialTateH r ≃+ L.TateH F (r + 2) :=
  -- The order hypothesis at `H = ⊤` says that `H²(U/V, A^V)` has order `[U : V]`.
  have hcardG : Nat.card (L.H F 2) = L.degree := by
    rw [← congrArg (fun X : NormalLayer G ↦ Nat.card (X.H F 2)) L.subgroupLayer_top, hcard ⊤,
      Subgroup.card_top, L.degree_eq_natCard_gal]
  AddEquiv.ofBijective (cupClass F L u r) (cupClass_bijective F L u (fun _ _ H _ ↦ h1 H)
    (fun _ _ H _ ↦ hcard H) hcardG
    (L.exists_zsmul_eq_of_cohomologyRes_subgroupRestriction_top F u (hgen ⊤)) r)

/-- The isomorphism of Tate's theorem acts by cup product with `u`. -/
@[simp]
theorem tateTheorem_apply
    (h1 : ∀ H : Subgroup L.Gal, Subsingleton ((L.subgroupLayer H).H F 1))
    (hcard : ∀ H : Subgroup L.Gal, Nat.card ((L.subgroupLayer H).H F 2) = Nat.card H)
    (hgen : ∀ (H : Subgroup L.Gal) (x : (L.subgroupLayer H).H F 2),
      ∃ m : ℤ, x = m • (L.subgroupRestriction H).cohomologyRes F 2 u)
    (r : ℤ) (x : L.TrivialTateH r) :
    tateTheorem F L u h1 hcard hgen r x = cupClass F L u r x := by
  rw [tateTheorem]
  exact AddEquiv.ofBijective_apply _ _ x

/-- The isomorphism of Tate's theorem **is** cup product with `u`, not an unrelated equivalence
between two groups of the same cardinality. -/
theorem tateTheorem_toAddMonoidHom
    (h1 : ∀ H : Subgroup L.Gal, Subsingleton ((L.subgroupLayer H).H F 1))
    (hcard : ∀ H : Subgroup L.Gal, Nat.card ((L.subgroupLayer H).H F 2) = Nat.card H)
    (hgen : ∀ (H : Subgroup L.Gal) (x : (L.subgroupLayer H).H F 2),
      ∃ m : ℤ, x = m • (L.subgroupRestriction H).cohomologyRes F 2 u)
    (r : ℤ) :
    (tateTheorem F L u h1 hcard hgen r).toAddMonoidHom = cupClass F L u r :=
  AddMonoidHom.ext (tateTheorem_apply F L u h1 hcard hgen r)

end TateTheorem

namespace ClassFormation

variable {F : Formation G}

/-- **Tate's theorem for a class formation**, in every integer degree: the generic theorem applied
to the fundamental class, with the three hypotheses discharged by the three individually named
consequences of the axioms. This is Artin–Tate's Main Theorem (Chapter XIV §4, Theorem 1). -/
def tateIso (cf : ClassFormation F) (L : NormalLayer G) (r : ℤ) :
    L.TrivialTateH r ≃+ L.TateH F (r + 2) :=
  tateTheorem F L (cf.fundamentalClass L) (cf.h1_subgroupLayer L) (cf.card_H2_subgroupLayer L)
    (cf.fundamentalClass_restrict_generates L) r

/-- The Tate isomorphism of a class formation acts by cup product with the fundamental class. -/
@[simp]
theorem tateIso_apply (cf : ClassFormation F) (L : NormalLayer G) (r : ℤ)
    (x : L.TrivialTateH r) :
    cf.tateIso L r x = cf.cupFundamentalClass L r x := by
  rw [tateIso, tateTheorem_apply, cupFundamentalClass_apply]

/-- The Tate isomorphism of a class formation is the cup-product map with the fundamental class,
not an unrelated equivalence between groups of the same cardinality. -/
theorem tateIso_toAddMonoidHom (cf : ClassFormation F) (L : NormalLayer G) (r : ℤ) :
    (cf.tateIso L r).toAddMonoidHom = cf.cupFundamentalClass L r :=
  AddMonoidHom.ext (cf.tateIso_apply L r)

end ClassFormation

end TauCeti.ClassFieldTheory
