/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree

/-!
# Cup product with trivial integral coefficients in degree zero

The canonical class of `1` acts as the identity under cup product after removing the left tensor
unit. Consequently, cup product with a generating class is bijective when the target has the
order of the finite group.

These Tate cohomology operations are parameterized by a representation and live alongside the
generic cup product in `TauCeti.TateCohomology`.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {H : Type} [Group H] [Fintype H]

/-- Cup product with a class of degree `q`, with trivial integral coefficients in degree zero
and the left tensor unit removed. -/
def cupTrivialInt (N : Rep ℤ H) {q : ℤ} (u : tateCohomology N q) :
    tateCohomology (Rep.trivial ℤ H ℤ) 0 →+ tateCohomology N q :=
  { toFun := fun x => (tateCohomologyFunctor q).map (λ_ N).hom
      (cup (Rep.trivial ℤ H ℤ) N 0 q q (by omega) x u)
    map_zero' := by simp
    map_add' := by intro x y; simp }

-- Keep this as a named rewrite: making it a simp lemma would make
-- `cupTrivialInt_trivialTateHZeroOne` fail `simpNF`.
/-- The trivial-integral cup map evaluates by cup product followed by the left unitor. -/
theorem cupTrivialInt_apply (N : Rep ℤ H) {q : ℤ} (u : tateCohomology N q)
    (x : tateCohomology (Rep.trivial ℤ H ℤ) 0) :
    cupTrivialInt N u x = (tateCohomologyFunctor q).map (λ_ N).hom
      (cup (Rep.trivial ℤ H ℤ) N 0 q q (by omega) x u) := by
  rfl

/-- The canonical degree-zero class of `1` acts as the identity under cup product. -/
@[simp]
theorem cupTrivialInt_trivialTateHZeroOne (N : Rep ℤ H) {q : ℤ}
    (u : tateCohomology N q) :
    cupTrivialInt N u (trivialTateHZeroOne H) = u := by
  let one : (Rep.trivial ℤ H ℤ).ρ.invariants := ⟨1, by simp [Representation.invariants]⟩
  have hunit :
      Rep.tensorInvariant N one ≫ (β_ N (Rep.trivial ℤ H ℤ)).hom ≫
        (λ_ N).hom = 𝟙 N :=
    Rep.tensorInvariant_one_braiding_leftUnitor N
  have hcup : cup (Rep.trivial ℤ H ℤ) N 0 q q (by omega) =
      cup0H (Rep.trivial ℤ H ℤ) N q := by
    convert cup_zero_left (Rep.trivial ℤ H ℤ) N q (by omega) using 1
  have hone : trivialTateHZeroOne H = H0π (Rep.trivial ℤ H ℤ) one := by
    apply (H0LinearEquivTrivialIntZModCard H).injective
    simp [H0LinearEquivTrivialIntZModCard_H0π, one]
  rw [hone, cupTrivialInt_apply, hcup, cup0H_H0π]
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, Category.assoc, hunit]
  simp

/-- Cupping with a generating degree-`q` class is bijective when the target has the order of
the finite group. -/
theorem cupTrivialInt_bijective (N : Rep ℤ H) {q : ℤ} (u : tateCohomology N q)
    (hgen : ∀ y : tateCohomology N q, ∃ m : ℤ, m • u = y)
    (hcard : Nat.card (tateCohomology N q) = Fintype.card H) :
    Function.Bijective (cupTrivialInt N u) := by
  have hsurj : Function.Surjective (cupTrivialInt N u) := by
    intro y
    obtain ⟨m, hm⟩ := hgen y
    refine ⟨m • trivialTateHZeroOne H, ?_⟩
    rw [map_zsmul, cupTrivialInt_trivialTateHZeroOne]
    exact hm
  have hsource : Nat.card (tateCohomology (Rep.trivial ℤ H ℤ) 0) = Fintype.card H := by
    rw [natCard_tateCohomology_zero_trivial_int_eq_card]
    exact Nat.card_eq_fintype_card
  have hsource_ne : Nat.card (tateCohomology (Rep.trivial ℤ H ℤ) 0) ≠ 0 := by
    rw [hsource]
    exact (Fintype.card_pos : 0 < Fintype.card H).ne'
  exact (@Nat.bijective_iff_surjective_and_card _ _
    (Nat.finite_of_card_ne_zero hsource_ne) (cupTrivialInt N u)).2
      ⟨hsurj, hsource.trans hcard.symm⟩

end TauCeti.TateCohomology
