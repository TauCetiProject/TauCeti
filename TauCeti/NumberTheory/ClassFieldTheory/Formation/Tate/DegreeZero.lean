/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Cup

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

namespace NormalLayer

variable (L : NormalLayer G)

/-- The canonical generator of degree-zero Tate cohomology with trivial integral coefficients:
the class of `1 ∈ ℤ`. -/
def trivialTateHZeroOne : L.TrivialTateH 0 :=
  TauCeti.TateCohomology.H0π (Rep.trivial ℤ L.Gal ℤ)
    ⟨1, by simp [Representation.invariants]⟩

/-- Under the identification with `ZMod |U/V|`, the class of `1` is `1`. -/
@[simp]
theorem H0LinearEquivTrivialIntZModCard_trivialTateHZeroOne :
    TauCeti.TateCohomology.H0LinearEquivTrivialIntZModCard L.Gal
      L.trivialTateHZeroOne = 1 := by
  simp [trivialTateHZeroOne]

end NormalLayer

/-- In degree zero, cup product with `u` sends the canonical trivial-coefficient class of `1`
to `u` in Tate degree two. This fixes the orientation of the degree-zero Tate isomorphism. -/
theorem cupClass_trivialTateHZeroOne (F : Formation G) (L : NormalLayer G) (u : L.H F 2) :
    cupClass F L u 0 L.trivialTateHZeroOne = (L.tateHIsoH F 2).inv u := by
  let one : (Rep.trivial ℤ L.Gal ℤ).ρ.invariants := ⟨1, by simp [Representation.invariants]⟩
  have hunit :
      Rep.tensorInvariant (L.rep F) one ≫ (β_ (L.rep F) (Rep.trivial ℤ L.Gal ℤ)).hom ≫
        (λ_ (L.rep F)).hom = 𝟙 (L.rep F) :=
    Rep.tensorInvariant_one_braiding_leftUnitor (L.rep F)
  have hcup : TauCeti.TateCohomology.cup (Rep.trivial ℤ L.Gal ℤ) (L.rep F)
      0 2 (0 + 2) (by omega) =
      TauCeti.TateCohomology.cup0H (Rep.trivial ℤ L.Gal ℤ) (L.rep F) 2 := by
    convert TauCeti.TateCohomology.cup_zero_left
      (Rep.trivial ℤ L.Gal ℤ) (L.rep F) 2 (by omega) using 1 <;> rfl
  rw [cupClass_apply, NormalLayer.trivialTateHZeroOne]
  rw [hcup]
  rw [TauCeti.TateCohomology.cup0H_H0π]
  -- The cup definition stores its target degree as `0 + 2`; after specialization it is `2`.
  change (tateCohomologyFunctor 2).map (λ_ (L.rep F)).hom
      ((tateCohomologyFunctor 2).map
        (Rep.tensorInvariant (L.rep F) one ≫
          (β_ (L.rep F) (Rep.trivial ℤ L.Gal ℤ)).hom)
          ((L.tateHIsoH F 2).inv u)) = (L.tateHIsoH F 2).inv u
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, Category.assoc, hunit]
  simp

/-- Degree-zero case of Tate's cup-product criterion: if a degree-two class generates
`H²(U/V, A^V)` and this group has order `[U : V]`, cupping with it is an equivalence from
degree-zero Tate cohomology with trivial integral coefficients to Tate degree two. -/
theorem cupClass_zero_bijective (F : Formation G) (L : NormalLayer G) (u : L.H F 2)
    (hgen : ∀ y : L.H F 2, ∃ m : ℤ, m • u = y)
    (hcardH : Nat.card (L.H F 2) = L.degree) :
    Function.Bijective (cupClass F L u 0) := by
  have hsurj : Function.Surjective (cupClass F L u 0) := by
    intro x
    obtain ⟨m, hm⟩ := hgen ((L.tateHIsoH F 2).hom x)
    refine ⟨m • L.trivialTateHZeroOne, ?_⟩
    rw [map_zsmul, cupClass_trivialTateHZeroOne]
    apply (L.tateHIsoH F 2).toLinearEquiv.injective
    rw [map_zsmul, Iso.toLinearEquiv_apply, Iso.inv_hom_id_apply]
    rw [Iso.toLinearEquiv_apply]
    exact hm
  have hcard : Nat.card (L.TrivialTateH 0) = Nat.card (L.TateH F 2) := by
    calc
      Nat.card (L.TrivialTateH 0) = Nat.card L.Gal :=
        TauCeti.TateCohomology.natCard_tateCohomology_zero_trivial_int_eq_card L.Gal
      _ = L.degree := L.degree_eq_natCard_gal.symm
      _ = Nat.card (L.H F 2) := hcardH.symm
      _ = Nat.card (L.TateH F 2) :=
        (Nat.card_congr (L.tateHIsoH F 2).toLinearEquiv.toEquiv).symm
  have hcard' : Nat.card (L.TrivialTateH 0) = Nat.card (L.TateH F (0 + 2)) := by
    simpa only [zero_add] using hcard
  have hsource : Nat.card (L.TrivialTateH 0) = L.degree := by
    exact TauCeti.TateCohomology.natCard_tateCohomology_zero_trivial_int_eq_card L.Gal |>.trans
      L.degree_eq_natCard_gal.symm
  have hsource_ne : Nat.card (L.TrivialTateH 0) ≠ 0 := by
    rw [hsource]
    exact L.degree_pos.ne'
  exact (@Nat.bijective_iff_surjective_and_card _ _
    (Nat.finite_of_card_ne_zero hsource_ne) (cupClass F L u 0)).2 ⟨hsurj, hcard'⟩

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
  exact cupClass_zero_bijective F L (cf.fundamentalClass L)
    (fun y ↦ (cf.fundamentalClass_generates L y).imp fun _ h ↦ h.symm)
    (cf.natCard_H2 L)

/-- The degree-zero Tate isomorphism of a class formation, with underlying map cup product
by the fundamental class. -/
def cupFundamentalClassZeroEquiv (cf : ClassFormation F) (L : NormalLayer G) :
    L.TrivialTateH 0 ≃+ L.TateH F 2 := by
  convert AddEquiv.ofBijective (cf.cupFundamentalClass L 0)
    (cf.cupFundamentalClass_zero_bijective L) using 1; rfl

/-- The degree-zero equivalence acts by cup product with the fundamental class. -/
@[simp]
theorem cupFundamentalClassZeroEquiv_apply (cf : ClassFormation F) (L : NormalLayer G)
    (x : L.TrivialTateH 0) :
    cf.cupFundamentalClassZeroEquiv L x = cf.cupFundamentalClass L 0 x := by
  simp [cupFundamentalClassZeroEquiv, AddEquiv.ofBijective]
  rfl

end ClassFormation

end TauCeti.ClassFieldTheory
