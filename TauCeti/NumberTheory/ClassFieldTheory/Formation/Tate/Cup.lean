/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ClassFormation
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product

/-!
# Cup product with a class of a finite normal layer

The cup product with a class in ordinary degree two gives a homomorphism from Tate cohomology
with trivial integral coefficients to Tate cohomology with formation coefficients. The ordinary
class is first transported to Tate degree two, and the tensor product with the trivial
representation is removed using the left unitor. For a class formation, the chosen class is its
fundamental class. This is the map whose invertibility is asserted by Tate's theorem.

The construction uses the Tate cup product of
`TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product`, following the cup product
formulation in Artin and Tate, *Class Field Theory*, Chapter XIV, §4.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- Cup product with a class in `H²(U/V, A^V)`, viewed in Tate degree two, followed by the
tensor-unit isomorphism `ℤ ⊗ A^V ≅ A^V`. -/
def cupClass (F : Formation G) (L : NormalLayer G) (u : L.H F 2) (r : ℤ) :
    L.TrivialTateH r →+ L.TateH F (r + 2) :=
  { toFun := fun x => (tateCohomologyFunctor (r + 2)).map (λ_ (L.rep F)).hom
      (TauCeti.TateCohomology.cup (Rep.trivial ℤ L.Gal ℤ) (L.rep F) r 2 (r + 2)
        (by omega) x ((L.tateHIsoH F 2).inv u))
    map_zero' := by simp
    map_add' := by intro x y; simp }

/-- The map `cupClass` evaluates by taking the Tate cup product with the degree-two image of
`u`, then applying the left unitor to the coefficient representation. -/
@[simp]
theorem cupClass_apply (F : Formation G) (L : NormalLayer G) (u : L.H F 2) (r : ℤ)
    (x : L.TrivialTateH r) :
    cupClass F L u r x =
      (tateCohomologyFunctor (r + 2)).map (λ_ (L.rep F)).hom
        (TauCeti.TateCohomology.cup (Rep.trivial ℤ L.Gal ℤ) (L.rep F) r 2 (r + 2)
          (by omega) x ((L.tateHIsoH F 2).inv u)) := by
  simp [cupClass]

/-- Cup product with the zero class is zero. -/
@[simp]
theorem cupClass_zero (F : Formation G) (L : NormalLayer G) (r : ℤ) :
    cupClass F L 0 r = 0 := by
  ext x
  simp [cupClass]

/-- Cup product is additive in the chosen degree-two class. -/
@[simp]
theorem cupClass_add (F : Formation G) (L : NormalLayer G) (u v : L.H F 2) (r : ℤ) :
    cupClass F L (u + v) r = cupClass F L u r + cupClass F L v r := by
  ext x
  simp [cupClass]

namespace ClassFormation

variable {F : Formation G}

/-- Cup product with the fundamental class of a finite normal layer. -/
def cupFundamentalClass (cf : ClassFormation F) (L : NormalLayer G) (r : ℤ) :
    L.TrivialTateH r →+ L.TateH F (r + 2) :=
  cupClass F L (cf.fundamentalClass L) r

/-- The map `cupFundamentalClass` evaluates as `cupClass` at the fundamental class. -/
@[simp]
theorem cupFundamentalClass_apply (cf : ClassFormation F) (L : NormalLayer G) (r : ℤ)
    (x : L.TrivialTateH r) :
    cf.cupFundamentalClass L r x = cupClass F L (cf.fundamentalClass L) r x := by
  rw [cupFundamentalClass]

end ClassFormation
end TauCeti.ClassFieldTheory
