/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Relative

/-!
# Fibre maps from specified square homotopies

A specified homotopy between the two composites in a square of cochain maps induces a map
of their mapping fibres. These maps compose using the sum of the transported square
homotopies. A specified second homotopy induces a homotopy of fibre maps; arbitrary choices
of the first homotopy need not induce the same map.

In relative coordinates, with differential `(x,y) ↦ (dx, f x - dy)`, a square homotopy
`h : u ≫ f' ∼ f ≫ v` gives `(x,y) ↦ (u x, v y + h x)`.
Applying this to the product difference maps of strict module towers gives maps of their
homotopy limits, including the contribution of the specified square homotopy.

The construction uses Joël Riou's `CochainComplex.mappingCone.mapOfHomotopy` and
`mappingCone.descHomotopy`, rather than introducing another fibre complex.

## References

* The Stacks Project, More on Algebra, Tags 07KX and 0CQD.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex

namespace CochainComplex.mappingCocone

open HomComplex

variable {C : Type*} [Category* C] [Preadditive C] [Limits.HasBinaryBiproducts C]
  {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ}
  {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} {f₃ : K₃ ⟶ L₃}
  {u : K₁ ⟶ K₂} {v : L₁ ⟶ L₂}

/-- The map of native mapping fibres induced by a specified square homotopy. -/
def mapOfHomotopy (H : Homotopy (f₁ ≫ v) (u ≫ f₂)) :
    mappingCocone f₁ ⟶ mappingCocone f₂ :=
  (mappingCone.mapOfHomotopy H)⟦(-1 : ℤ)⟧'

/-- A strictly commuting square gives the usual shifted cone map. -/
@[simp]
lemma mapOfHomotopy_ofEq (h : f₁ ≫ v = u ≫ f₂) :
    mapOfHomotopy (Homotopy.ofEq h) = (mappingCone.map f₁ f₂ u v h)⟦(-1 : ℤ)⟧' := by
  rw [mapOfHomotopy, mappingCone.map_eq_mapOfHomotopy]

/-- The fibre map commutes with the first projections. -/
@[reassoc (attr := simp)]
lemma mapOfHomotopy_fst (H : Homotopy (f₁ ≫ v) (u ≫ f₂)) :
    mapOfHomotopy H ≫ fst f₂ = fst f₁ ≫ u := by
  rw [mapOfHomotopy]
  ext p : 1
  -- Restate the composite before projecting: the native fibre is only definitionally the
  -- shifted cone, so `comp_f` cannot match at the default rewriting transparency.
  change ((mappingCone.mapOfHomotopy H)⟦(-1 : ℤ)⟧').f p ≫ (fst f₂).f p =
    (fst f₁).f p ≫ u.f p
  rw [fst_f, fst_f, shiftFunctor_map_f']
  change (mappingCone.mapOfHomotopy H).f (p + -1) ≫
      (mappingCone.fst f₂).1.v (p + -1) p (by omega) = _
  exact mappingCone.mapOfHomotopy_f_fst_v H _ _ (by omega)

/-- The second projection of the fibre map retains the square homotopy. -/
@[reassoc (attr := simp)]
lemma mapOfHomotopy_f_snd_v (H : Homotopy (f₁ ≫ v) (u ≫ f₂)) (p : ℤ) :
    (mapOfHomotopy H).f p ≫ (snd f₂).v p (p + -1) rfl =
      (fst f₁).f p ≫ H.hom p (p + -1) +
        (snd f₁).v p (p + -1) rfl ≫ v.f (p + -1) := by
  rw [mapOfHomotopy, snd_v, snd_v, fst_f, shiftFunctor_map_f']
  -- Expose the shifted cone indices before using the cone projection formula.
  change (mappingCone.mapOfHomotopy H).f (p + -1) ≫
      (mappingCone.snd f₂).v (p + -1) (p + -1) (add_zero _) = _
  exact mappingCone.mapOfHomotopy_f_snd_v H _ _ (by omega)

/-- Fibre maps compose using the transported sum of the specified square homotopies. -/
@[reassoc]
lemma mapOfHomotopy_comp {u' : K₂ ⟶ K₃} {v' : L₂ ⟶ L₃}
    (H : Homotopy (f₁ ≫ v) (u ≫ f₂)) (H' : Homotopy (f₂ ≫ v') (u' ≫ f₃)) :
    mapOfHomotopy (H.compSquare H') = mapOfHomotopy H ≫ mapOfHomotopy H' := by
  simp only [mapOfHomotopy, mappingCone.mapOfHomotopy_comp, Functor.map_comp]
  rfl

/-- A specified second homotopy gives a homotopy between the induced fibre maps. -/
def mapOfHomotopyHomotopy (H H' : Homotopy (f₁ ≫ v) (u ≫ f₂))
    (s : Cochain K₁ L₂ (-2))
    (hs : δ (-2) (-1) s = Cochain.ofHomotopy H - Cochain.ofHomotopy H') :
    Homotopy (mapOfHomotopy H) (mapOfHomotopy H') :=
  (mappingCone.mapOfHomotopyHomotopy H H' s hs).shift (-1)

/-- The second homotopy of fibre maps has the negative sign introduced by shifting the
cone homotopy by `-1`. -/
@[simp]
lemma mapOfHomotopyHomotopy_hom (H H' : Homotopy (f₁ ≫ v) (u ≫ f₂))
    (s : Cochain K₁ L₂ (-2))
    (hs : δ (-2) (-1) s = Cochain.ofHomotopy H - Cochain.ofHomotopy H')
    (p q : ℤ) (hpq : p + -1 = q) :
    (mapOfHomotopyHomotopy H H' s hs).hom p q =
      -((fst f₁).f p ≫ s.v p (q + -1) (by omega) ≫
        (inr f₂ : Cochain _ _ 1).v (q + -1) q (by omega)) := by
  have hi : (inr f₂ : Cochain L₂ (mappingCocone f₂) 1).v (q + -1) q (by omega) =
      (mappingCone.inr f₂).f (q + -1) := by
    -- Expose the inclusion's right-shifted cochain before applying its component formula.
    change ((Cochain.ofHom (mappingCone.inr f₂)).rightShift (-1) 1 (by omega)).v
      (q + -1) q (by omega) = _
    rw [Cochain.rightShift_v _ _ _ _ _ _ _ (q + -1) (add_zero _)]
    simp
  rw [hi, fst_f]
  -- Restate both sides on the cone objects before normalizing the shifted indices.
  change (-1 : ℤ).negOnePow •
    (mappingCone.mapOfHomotopyHomotopy H H' s hs).hom (p + -1) (q + -1) =
      -((mappingCone.fst f₁ : Cochain _ _ 1).v (p + -1) p (by omega) ≫
        s.v p (q + -1) (by omega) ≫ (mappingCone.inr f₂).f (q + -1))
  have hc := mappingCone.mapOfHomotopyHomotopy_hom H H' s hs
    (p + -1) (q + -1) (by omega)
  -- Work with the underlying cochain to compare intermediate degrees without transports.
  generalize (mappingCone.fst f₁ : Cochain (mappingCone f₁) K₁ 1) = t at hc ⊢
  rw [hc]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  congr 1
  rw [← Category.assoc, ← Category.assoc,
    ← Cochain.comp_v t s (show 1 + -2 = -1 by omega)
      (p + -1) (p + -1 + 1) (q + -1) rfl (by omega),
    ← Cochain.comp_v t s (show 1 + -2 = -1 by omega)
      (p + -1) p (q + -1) (by omega) (by omega)]

section Modules

variable {R : Type*} [Ring R]
  {K L K' L' : CochainComplex (ModuleCat R) ℤ} {f : K ⟶ L} {f' : K' ⟶ L'}
  {a : K ⟶ K'} {b : L ⟶ L'}

/-- In relative coordinates the square homotopy contributes with positive sign when oriented
from `a ≫ f'` to `f ≫ b`. -/
@[simp]
lemma relativeCoordinates_mapOfHomotopy (h : Homotopy (a ≫ f') (f ≫ b))
    (p q : ℤ) (hpq : p + -1 = q) (x : (mappingCocone f).X p) :
    relativeCoordinates f' p q hpq ((mapOfHomotopy h.symm).f p x) =
      (a.f p (relativeCoordinates f p q hpq x).1,
        b.f q (relativeCoordinates f p q hpq x).2 +
          h.hom p q (relativeCoordinates f p q hpq x).1) := by
  subst hpq
  rw [relativeCoordinates_apply, relativeCoordinates_apply]
  apply Prod.ext
  · exact congrArg (fun g : (mappingCocone f).X p ⟶ K'.X p ↦ g x)
      (congr_hom (mapOfHomotopy_fst h.symm) p)
  · have e := congrArg (fun g : (mappingCocone f).X p ⟶ L'.X (p + -1) ↦ g.hom x)
      (mapOfHomotopy_f_snd_v h.symm p)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
      LinearMap.add_apply, Homotopy.symm_hom, ModuleCat.hom_neg, LinearMap.neg_apply] at e
    rw [e]
    simp [add_comm]

end Modules

end CochainComplex.mappingCocone
