/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Duplex
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The Hom complex of two curved duplexes

For duplexes with the same curvature, the even and odd pairs of component maps form a
two-periodic complex. Its differential is the graded commutator with the duplex
differentials. The curvature terms cancel in its square. Degree-zero cycles are the closed
even morphisms of duplexes, and degree-zero boundaries are their null-homotopic morphisms.

The sign convention follows Frenkel, Khovanov, and Schiffmann, *Homological realization of
Nakajima varieties and Weyl group actions*, Compositio Mathematica **141** (2005),
Sections 2–3.
-/

public section

universe w v u

namespace TauCeti.CurvedDuplex

open CategoryTheory Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {R : Type w} [CommRing R] [Linear R C] {w₀ : R}
variable (X Y : CurvedDuplex C w₀)

/-- The degree-zero component of the Hom complex: pairs of maps preserving parity. -/
abbrev EvenCochain := (X.X₀ ⟶ Y.X₀) × (X.X₁ ⟶ Y.X₁)

/-- The degree-one component of the Hom complex: pairs of maps reversing parity. -/
abbrev OddCochain := (X.X₀ ⟶ Y.X₁) × (X.X₁ ⟶ Y.X₀)

/-- The graded commutator on even maps. -/
def evenDifferential : EvenCochain X Y →ₗ[R] OddCochain X Y where
  toFun f := (f.1 ≫ Y.d₀ - X.d₀ ≫ f.2, f.2 ≫ Y.d₁ - X.d₁ ≫ f.1)
  map_add' f g := by ext <;> simp [add_comp, comp_add, sub_add_sub_comm]
  map_smul' r f := by ext <;> simp [Linear.smul_comp, Linear.comp_smul, smul_sub]

/-- The graded commutator on odd maps. Its plus signs reflect that odd maps have
degree one modulo two. -/
def oddDifferential : OddCochain X Y →ₗ[R] EvenCochain X Y where
  toFun h := (X.d₀ ≫ h.2 + h.1 ≫ Y.d₁, X.d₁ ≫ h.1 + h.2 ≫ Y.d₀)
  map_add' f g := by ext <;> simp [add_comp, comp_add, add_add_add_comm]
  map_smul' r f := by ext <;> simp [Linear.smul_comp, Linear.comp_smul]

@[simp] theorem evenDifferential_apply (f : EvenCochain X Y) :
    evenDifferential X Y f =
      (f.1 ≫ Y.d₀ - X.d₀ ≫ f.2, f.2 ≫ Y.d₁ - X.d₁ ≫ f.1) := by
  simp [evenDifferential]

@[simp] theorem oddDifferential_apply (h : OddCochain X Y) :
    oddDifferential X Y h =
      (X.d₀ ≫ h.2 + h.1 ≫ Y.d₁, X.d₁ ≫ h.1 + h.2 ≫ Y.d₀) := by
  simp [oddDifferential]

/-- The even-to-odd differential followed by the odd-to-even differential vanishes. -/
@[simp] theorem oddDifferential_comp_evenDifferential :
    (oddDifferential X Y).comp (evenDifferential X Y) = 0 := by
  ext h : 1
  ext <;> simp [evenDifferential, oddDifferential, sub_comp, comp_sub, Category.assoc]

/-- The odd-to-even differential followed by the even-to-odd differential vanishes. -/
@[simp] theorem evenDifferential_comp_oddDifferential :
    (evenDifferential X Y).comp (oddDifferential X Y) = 0 := by
  ext f : 1
  ext <;> simp [evenDifferential, oddDifferential, add_comp, comp_add, Category.assoc]
    <;> abel

include X Y
/- The component types in the characteristic lemmas below require the object to unfold. -/
/-- The two-periodic Hom complex of curved duplexes with a common curvature. -/
@[expose]
def homComplex : CurvedDuplex (ModuleCat.{v} R) (0 : R) where
  X₀ := ModuleCat.of R (EvenCochain X Y)
  X₁ := ModuleCat.of R (OddCochain X Y)
  d₀ := ModuleCat.ofHom (evenDifferential X Y)
  d₁ := ModuleCat.ofHom (oddDifferential X Y)
  d₀_comp_d₁ := by
    rw [← ModuleCat.ofHom_comp, oddDifferential_comp_evenDifferential]
    simp
  d₁_comp_d₀ := by
    rw [← ModuleCat.ofHom_comp, evenDifferential_comp_oddDifferential]
    simp

@[simp] theorem homComplex_X₀ : (homComplex X Y).X₀ = ModuleCat.of R (EvenCochain X Y) := rfl
@[simp] theorem homComplex_X₁ : (homComplex X Y).X₁ = ModuleCat.of R (OddCochain X Y) := rfl
@[simp] theorem homComplex_d₀ : (homComplex X Y).d₀ = ModuleCat.ofHom (evenDifferential X Y) := rfl
@[simp] theorem homComplex_d₁ : (homComplex X Y).d₁ = ModuleCat.ofHom (oddDifferential X Y) := rfl

/-- An even pair is a degree-zero cycle exactly when it defines a closed duplex map. -/
theorem evenDifferential_eq_zero_iff (f : EvenCochain X Y) :
    evenDifferential X Y f = 0 ↔
      f.1 ≫ Y.d₀ = X.d₀ ≫ f.2 ∧ f.2 ≫ Y.d₁ = X.d₁ ≫ f.1 := by
  simp [Prod.ext_iff, sub_eq_zero]

/-- A closed even map gives a cycle in the Hom complex. -/
@[simp] theorem evenDifferential_eq_zero (f : X ⟶ Y) :
    (f.f₀ ≫ Y.d₀ - X.d₀ ≫ f.f₁, f.f₁ ≫ Y.d₁ - X.d₁ ≫ f.f₀) = 0 := by
  simpa only [evenDifferential_apply] using
    (evenDifferential_eq_zero_iff X Y (f.f₀, f.f₁)).2 ⟨f.comm₀, f.comm₁⟩

/-- Degree-zero cycles in the Hom complex are precisely closed even maps of duplexes. -/
def homEquivCycles : (X ⟶ Y) ≃ₗ[R] (evenDifferential X Y).ker where
  toFun f := ⟨(f.f₀, f.f₁), by
    rw [LinearMap.mem_ker]
    exact evenDifferential_eq_zero X Y f⟩
  invFun f :=
    { f₀ := f.1.1
      f₁ := f.1.2
      comm₀ := ((evenDifferential_eq_zero_iff X Y f.1).1
        ((LinearMap.mem_ker).1 f.2)).1
      comm₁ := ((evenDifferential_eq_zero_iff X Y f.1).1
        ((LinearMap.mem_ker).1 f.2)).2 }
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
  map_add' f g := by ext <;> rfl
  map_smul' r f := by ext <;> rfl

@[simp] theorem homEquivCycles_apply_val (f : X ⟶ Y) :
    (homEquivCycles X Y f).1 = (f.f₀, f.f₁) := by
  simp [homEquivCycles]

@[simp] theorem homEquivCycles_symm_f₀ (z : (evenDifferential X Y).ker) :
    ((homEquivCycles X Y).symm z).f₀ = z.1.1 := by
  simp [homEquivCycles]

@[simp] theorem homEquivCycles_symm_f₁ (z : (evenDifferential X Y).ker) :
    ((homEquivCycles X Y).symm z).f₁ = z.1.2 := by
  simp [homEquivCycles]

/-- An odd boundary is the pair of components of the null-homotopic map it defines. -/
theorem oddDifferential_eq_nullHomotopicMap_components (h : OddCochain X Y) :
    oddDifferential X Y h =
      ((nullHomotopicMap h.1 h.2).f₀, (nullHomotopicMap h.1 h.2).f₁) := by
  simp

/-- A closed map is null-homotopic exactly when its cycle is an odd boundary. -/
theorem mem_nullHomotopic_iff_exists_oddDifferential (f : X ⟶ Y) :
    f ∈ (nullHomotopic C w₀).hom X Y ↔
      ∃ h : OddCochain X Y, oddDifferential X Y h = (f.f₀, f.f₁) := by
  rw [mem_nullHomotopic_iff]
  constructor
  · rintro ⟨h₀, h₁, rfl⟩
    exact ⟨(h₀, h₁), oddDifferential_eq_nullHomotopicMap_components X Y _⟩
  · rintro ⟨h, hh⟩
    refine ⟨h.1, h.2, ?_⟩
    have hpair :
        ((nullHomotopicMap h.1 h.2).f₀, (nullHomotopicMap h.1 h.2).f₁) =
          (f.f₀, f.f₁) :=
      (oddDifferential_eq_nullHomotopicMap_components X Y h).symm.trans hh
    ext
    · exact congrArg Prod.fst hpair
    · exact congrArg Prod.snd hpair

end TauCeti.CurvedDuplex
