/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Eventually null-homotopic maps of cochain complexes

A map `f : A ⟶ B` of `ℤ`-indexed cochain complexes is **eventually null-homotopic** when, in all
sufficiently large degrees, it is the differential `δ z = d ∘ z + z ∘ d` of a cochain `z` of
degree `-1`. A map homotopic to an eventually null-homotopic map is eventually null-homotopic, and
a map which factors, up to homotopy, through a complex vanishing in high degrees is eventually
null-homotopic.

In the Keller–Vossieck theorem, a morphism vanishing in the singularity category gives a map of
injective resolutions factoring through a bounded complex, hence an eventually null-homotopic
map.

## Main definitions

* `CochainComplex.IsEventuallyNullHomotopic`: eventually null-homotopic maps.

## Main results

* `CochainComplex.IsEventuallyNullHomotopic.of_homotopy`: invariance under homotopy.
* `CochainComplex.isEventuallyNullHomotopic_of_quotient_map_eq_comp`: a map whose homotopy class
  factors through a complex vanishing in high degrees is eventually null-homotopic.

## References

* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
-/

public section

namespace CochainComplex

open CategoryTheory CategoryTheory.Limits HomComplex

variable {C : Type*} [Category* C] [Preadditive C] {A B D : CochainComplex C ℤ}

/-- A map of cochain complexes is **eventually null-homotopic** when, in all degrees `≥ n` for some
`n`, it equals `δ z` for a cochain `z` of degree `-1`. -/
def IsEventuallyNullHomotopic (f : A ⟶ B) : Prop :=
  ∃ (n : ℤ) (z : Cochain A B (-1)), ∀ p, n ≤ p → f.f p = (δ (-1) 0 z).v p p (add_zero p)

/-- The defining property of eventually null-homotopic maps. -/
theorem isEventuallyNullHomotopic_iff (f : A ⟶ B) :
    IsEventuallyNullHomotopic f ↔
      ∃ (n : ℤ) (z : Cochain A B (-1)), ∀ p, n ≤ p → f.f p = (δ (-1) 0 z).v p p (add_zero p) :=
  Iff.rfl

namespace IsEventuallyNullHomotopic

/-- A map vanishing in all degrees `≥ n` is eventually null-homotopic. -/
theorem of_eventually_eq_zero {f : A ⟶ B} (n : ℤ) (h : ∀ p, n ≤ p → f.f p = 0) :
    IsEventuallyNullHomotopic f :=
  ⟨n, 0, fun p hp ↦ by simpa using h p hp⟩

/-- A map homotopic to an eventually null-homotopic map is eventually null-homotopic. -/
theorem of_homotopy {f g : A ⟶ B} (h : Homotopy f g) (hg : IsEventuallyNullHomotopic g) :
    IsEventuallyNullHomotopic f := by
  obtain ⟨n, z, hz⟩ := hg
  obtain ⟨w, hw⟩ := Cochain.equivHomotopy f g h
  refine ⟨n, w + z, fun p hp ↦ ?_⟩
  have := Cochain.congr_v hw p p (add_zero p)
  rw [Cochain.add_v, Cochain.ofHom_v, Cochain.ofHom_v] at this
  rw [this, hz p hp, δ_add, Cochain.add_v]

end IsEventuallyNullHomotopic

/-- **Maps factoring through a complex bounded above are eventually null-homotopic**: if the
homotopy class of `f` factors through a complex vanishing in degrees `> b`, then `f` is
eventually null-homotopic. -/
theorem isEventuallyNullHomotopic_of_quotient_map_eq_comp {f : A ⟶ B} (b : ℤ)
    [D.IsStrictlyLE b] (u : (HomotopyCategory.quotient C (.up ℤ)).obj A ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj D)
    (v : (HomotopyCategory.quotient C (.up ℤ)).obj D ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj B)
    (h : (HomotopyCategory.quotient C (.up ℤ)).map f = u ≫ v) :
    IsEventuallyNullHomotopic f := by
  obtain ⟨u₀, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective u
  obtain ⟨v₀, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective v
  rw [← Functor.map_comp] at h
  refine .of_homotopy (HomotopyCategory.homotopyOfEq _ _ h)
    (.of_eventually_eq_zero (b + 1) fun p hp ↦ ?_)
  rw [HomologicalComplex.comp_f]
  rw [(D.isZero_of_isStrictlyLE b p (by lia)).eq_of_src (v₀.f p) 0, comp_zero]

end CochainComplex
