/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Additive functions on object properties

Let `C` be a category with zero morphisms, `P : ObjectProperty C` a property containing a zero
object and closed under isomorphisms, and `v : C → G` a function into an abelian group that is
additive on short exact sequences whose terms lie in `P`
(`CategoryTheory.ObjectProperty.IsAdditiveOn`):

```text
v S.X₂ = v S.X₁ + v S.X₃.
```

Then `v` vanishes on every zero object (`CategoryTheory.ObjectProperty.map_eq_zero_of_isZero`) and
takes equal values on isomorphic objects in `P` (`CategoryTheory.ObjectProperty.map_eq_of_iso`).
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.ObjectProperty

section IsAdditiveOn

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : ObjectProperty C)
  {G : Type*} [AddCommGroup G] (v : C → G)

/-- A function `v : C → G` into an abelian group is **additive on `P`** if
`v S.X₂ = v S.X₁ + v S.X₃` for every short exact sequence `S` whose three terms lie in `P`. -/
def IsAdditiveOn : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
    v S.X₂ = v S.X₁ + v S.X₃

/-- Characterization of `ObjectProperty.IsAdditiveOn` by short exact sequences in `P`. -/
lemma isAdditiveOn_iff :
    P.IsAdditiveOn v ↔
      ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
        v S.X₂ = v S.X₁ + v S.X₃ := Iff.rfl

variable {P v}

/-- Applying additivity on `P` to a short exact sequence whose terms lie in `P`. -/
lemma IsAdditiveOn.map_shortExact (hv : P.IsAdditiveOn v) {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) : v S.X₂ = v S.X₁ + v S.X₃ :=
  hv S hS h₁ h₂ h₃

end IsAdditiveOn

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  {G : Type*} [AddCommGroup G] {v : C → G}

/-- A function into an abelian group that is additive on short exact sequences in `P` vanishes on
every zero object, provided `P` contains zero and is closed under isomorphisms. -/
lemma map_eq_zero_of_isZero (hv : P.IsAdditiveOn v) {Z : C} (hZ : IsZero Z) : v Z = 0 := by
  have hS : (ShortComplex.mk (𝟙 Z) (𝟙 Z) (hZ.eq_of_src _ _)).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ hZ
      mono_f := inferInstance
      epi_g := inferInstance }
  have hPZ : P Z := P.prop_of_isZero hZ
  exact left_eq_add.mp (hv.map_shortExact hS hPZ hPZ hPZ)

/-- A function into an abelian group that is additive on short exact sequences in `P` takes the
same value on isomorphic objects in `P`. -/
lemma map_eq_of_iso (hv : P.IsAdditiveOn v) {X Y : C} (e : X ≅ Y) (hX : P X) : v X = v Y := by
  obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
  let S : ShortComplex C := ShortComplex.mk e.hom (0 : Y ⟶ Z) (by simp)
  have hepi : Epi S.g := ⟨fun _ _ _ ↦ hZ.eq_of_src _ _⟩
  have hExact : S.Exact :=
    (ShortComplex.HomologyData.ofIsColimitCokernelCofork S rfl _
      (CokernelCofork.IsColimit.ofEpiOfIsZero (CokernelCofork.ofπ (0 : Y ⟶ Z) comp_zero)
        (by dsimp [S]; infer_instance) hZ)).exact_iff.2 hZ
  have hS : S.ShortExact :=
    { exact := hExact
      mono_f := by dsimp [S]; infer_instance
      epi_g := hepi }
  have h := hv.map_shortExact hS hX (P.prop_of_iso e hX) hPZ
  dsimp [S] at h
  rw [P.map_eq_zero_of_isZero hv hZ, add_zero] at h
  exact h.symm

end CategoryTheory.ObjectProperty
