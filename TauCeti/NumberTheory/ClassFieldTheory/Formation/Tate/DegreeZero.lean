/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Cup
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.TrivialInt

/-!
# The degree-zero case of the Tate isomorphism

Cup product with a degree-two class sends the canonical generator of degree-zero Tate
cohomology with trivial integral coefficients to that class. Consequently, if the class
generates second cohomology and that group has the order of the Galois group, the degree-zero
cup-product map is an isomorphism. In a class formation these conditions hold for the
fundamental class. This is the degree-zero input to Tate's cup-product criterion.

The cup-product normalization follows Artin and Tate, *Class Field Theory*,
Preliminaries §2 and Chapter XIV §4.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- At degree zero, the class-formation cup map is the generic cup map with trivial integral
coefficients. The target degrees `0 + 2` and `2` agree by normalization. -/
theorem cupClass_degree_zero_eq_cupTrivialInt (F : Formation G) (L : NormalLayer G)
    (u : L.H F 2) :
    cupClass F L u 0 =
      TauCeti.TateCohomology.cupTrivialInt (L.rep F) ((L.tateHIsoH F 2).inv u) := by
  ext x
  rw [cupClass_apply, TauCeti.TateCohomology.cupTrivialInt_apply]
  rfl

/-- In degree zero, cup product with `u` sends the canonical trivial-coefficient class of `1`
to `u` in Tate degree two. This fixes the orientation of the degree-zero Tate isomorphism. -/
@[simp]
theorem cupClass_trivialTateHZeroOne (F : Formation G) (L : NormalLayer G) (u : L.H F 2) :
    cupClass F L u 0 (TauCeti.TateCohomology.trivialTateHZeroOne L.Gal) =
      (L.tateHIsoH F 2).inv u := by
  rw [cupClass_degree_zero_eq_cupTrivialInt]
  exact TauCeti.TateCohomology.cupTrivialInt_trivialTateHZeroOne
    (L.rep F) ((L.tateHIsoH F 2).inv u)

/-- Degree-zero case of Tate's cup-product criterion: if a degree-two class generates
`H²(U/V, A^V)` and this group has order `[U : V]`, cupping with it is an equivalence from
degree-zero Tate cohomology with trivial integral coefficients to Tate degree two. -/
theorem cupClass_degree_zero_bijective (F : Formation G) (L : NormalLayer G) (u : L.H F 2)
    (hgen : ∀ y : L.H F 2, ∃ m : ℤ, m • u = y)
    (hcardH : Nat.card (L.H F 2) = L.degree) :
    Function.Bijective (cupClass F L u 0) := by
  have hgen' : ∀ y : L.TateH F 2, ∃ m : ℤ, m • (L.tateHIsoH F 2).inv u = y := by
    intro y
    obtain ⟨m, hm⟩ := hgen ((L.tateHIsoH F 2).hom y)
    refine ⟨m, ?_⟩
    apply (L.tateHIsoH F 2).toLinearEquiv.injective
    rw [map_zsmul, Iso.toLinearEquiv_apply, Iso.inv_hom_id_apply]
    rw [Iso.toLinearEquiv_apply]
    exact hm
  have hcard' : Nat.card (L.TateH F 2) = Fintype.card L.Gal := by
    calc
      Nat.card (L.TateH F 2) = Nat.card (L.H F 2) :=
        Nat.card_congr (L.tateHIsoH F 2).toLinearEquiv.toEquiv
      _ = L.degree := hcardH
      _ = Nat.card L.Gal := L.degree_eq_natCard_gal
      _ = Fintype.card L.Gal := Nat.card_eq_fintype_card
  rw [cupClass_degree_zero_eq_cupTrivialInt]
  exact TauCeti.TateCohomology.cupTrivialInt_bijective (L.rep F)
    ((L.tateHIsoH F 2).inv u) hgen' hcard'

namespace ClassFormation

variable {F : Formation G}

/-- In degree zero, cup product with the fundamental class is bijective. This is the
degree-zero case of Tate's theorem for a class formation. -/
theorem cupFundamentalClass_zero_bijective (cf : ClassFormation F) (L : NormalLayer G) :
    Function.Bijective (cf.cupFundamentalClass L 0) := by
  have heq : cf.cupFundamentalClass L 0 = cupClass F L (cf.fundamentalClass L) 0 := by
    ext x
    exact cf.cupFundamentalClass_apply L 0 x
  rw [heq]
  exact cupClass_degree_zero_bijective F L (cf.fundamentalClass L)
    (fun y ↦ (cf.fundamentalClass_generates L y).imp fun _ h ↦ h.symm)
    (cf.natCard_H2 L)

/-- The degree-zero Tate isomorphism of a class formation, with underlying map cup product
by the fundamental class. -/
def cupFundamentalClassZeroEquiv (cf : ClassFormation F) (L : NormalLayer G) :
    L.TrivialTateH 0 ≃+ L.TateH F 2 :=
  AddEquiv.ofBijective (cf.cupFundamentalClass L 0)
    (cf.cupFundamentalClass_zero_bijective L)

/-- The degree-zero equivalence acts by cup product with the fundamental class. -/
@[simp]
theorem cupFundamentalClassZeroEquiv_apply (cf : ClassFormation F) (L : NormalLayer G)
    (x : L.TrivialTateH 0) :
    cf.cupFundamentalClassZeroEquiv L x = cf.cupFundamentalClass L 0 x := by
  simpa only [cupFundamentalClassZeroEquiv, zero_add] using
    AddEquiv.ofBijective_apply (cf.cupFundamentalClass L 0)
      (cf.cupFundamentalClass_zero_bijective L) x

/-- The underlying homomorphism of the degree-zero equivalence is cup product with the
fundamental class. -/
theorem cupFundamentalClassZeroEquiv_toAddMonoidHom (cf : ClassFormation F)
    (L : NormalLayer G) :
    (cf.cupFundamentalClassZeroEquiv L).toAddMonoidHom = cf.cupFundamentalClass L 0 := by
  ext x
  exact cf.cupFundamentalClassZeroEquiv_apply L x

end ClassFormation

end TauCeti.ClassFieldTheory
