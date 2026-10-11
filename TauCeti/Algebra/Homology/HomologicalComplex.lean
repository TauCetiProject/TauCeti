/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive

/-!
# Additional API for homological complexes

This file records additivity of the cycles functor, degreewise recursion for powers of a
complex endomorphism, and the existence of coproducts of complexes, computed degreewise. It also
records the basic properties of the maps
`K.toCycles i j : K.X i ⟶ K.cycles j` induced by the differentials: they kill the cycles in degree
`i`, commute with morphisms of complexes, vanish after a morphism from a complex concentrated in
degree `i`, and are epimorphisms in degrees where the complex is exact. In a degree with no nonzero
differential into it, the identification of the homology with the cycles is natural
(`HomologicalComplex.isoHomologyπ_inv_naturality`). The sequence
`Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of cycles is exact (`HomologicalComplex.exact_iCycles_toCycles`), so the cycles of
a complex exact in degree `j` fit into short exact sequences `0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Zⱼ ⟶ 0`.
For chain complexes indexed by the natural numbers, the identification of zero chains with
cycles is natural (`ChainComplex.cycles₀Iso_inv_naturality`).
-/

public section

open CategoryTheory Limits

universe w v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c} {s : K ⟶ K}

/-- Degreewise recursion for the powers of a chain endomorphism. -/
lemma pow_f_succ (m : ℕ) (i : ι) :
    (End.of s ^ (m + 1)).f i = (End.of s ^ m).f i ≫ s.f i := by
  rw [pow_succ', End.mul_def, comp_f]

/-- Homological complexes have the coproducts that the underlying category has. They are
computed degreewise. -/
instance hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{w} (HomologicalComplex C c) :=
  fun _ ↦ inferInstance

/-! ### The maps onto the cycles -/

section Cycles

variable (K) {L : HomologicalComplex C c}

/-- The map from the cycles in degree `i` to the cycles in degree `j` induced by the differential
vanishes. -/
@[reassoc]
lemma iCycles_toCycles (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    K.iCycles i ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, toCycles_i, iCycles_d, zero_comp]

variable {K}

/-- The maps onto the cycles induced by the differentials commute with morphisms of complexes. -/
@[reassoc]
lemma toCycles_cyclesMap (φ : K ⟶ L) (i j : ι) [K.HasHomology j] [L.HasHomology j] :
    K.toCycles i j ≫ cyclesMap φ j = φ.f i ≫ L.toCycles i j :=
  (cancel_mono (L.iCycles j)).1 <| by simp

/-- In a degree `j` with no nonzero differential into it, the identifications
`K.isoHomologyπ i j` of the homology with the cycles commute with the maps induced by a morphism of
complexes. -/
@[reassoc]
lemma isoHomologyπ_inv_naturality (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i) (hK : K.d i j = 0)
    (hL : L.d i j = 0) [K.HasHomology j] [L.HasHomology j] :
    homologyMap φ j ≫ (L.isoHomologyπ i j hi hL).inv =
      (K.isoHomologyπ i j hi hK).inv ≫ cyclesMap φ j := by
  rw [← cancel_epi (K.isoHomologyπ i j hi hK).hom]
  simp

variable [HasZeroObject C] [DecidableEq ι] {i : ι} {X : C}

/-- A morphism from a complex concentrated in degree `i` vanishes after the differential out of
degree `i`. -/
@[reassoc]
lemma single_f_d (g : (single C c i).obj X ⟶ L) (j : ι) : g.f i ≫ L.d i j = 0 := by
  rw [g.comm i j, single_obj_d, zero_comp]

/-- A morphism from a complex concentrated in degree `i` vanishes after the map onto the cycles in
degree `j`. -/
@[reassoc]
lemma single_f_toCycles (g : (single C c i).obj X ⟶ L) (j : ι) [L.HasHomology j] :
    g.f i ≫ L.toCycles i j = 0 := by
  rw [← cancel_mono (L.iCycles j), Category.assoc, toCycles_i, single_f_d, zero_comp]

end Cycles

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

variable (K) in
/-- The sequence `Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of the cycles of a complex `K` is exact when `j` is the degree
following `i`: the cycles in degree `i` are the kernel of the differential. -/
lemma exact_iCycles_toCycles (i j : ι) (hij : c.next i = j) :
    (ShortComplex.mk _ _ (K.iCycles_toCycles i j)).Exact := by
  refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk _ _ (K.iCycles_toCycles i j))
    (S₂ := ShortComplex.mk _ _ (K.iCycles_d i j))
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j
      comm₁₂ := by simp
      comm₂₃ := (Category.id_comp _).trans (toCycles_i _ _ _).symm }).2 ?_
  exact ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i j hij)

/-- In a complex exact in degree `j`, the map onto the cycles in degree `j` from the preceding
degree is an epimorphism. -/
lemma epi_toCycles_of_exactAt {i j : ι} (h : K.ExactAt j) (hij : c.prev j = i) :
    Epi (K.toCycles i j) := by
  rw [exactAt_iff' _ i j (c.next j) hij rfl] at h
  rw [← epi_comp_iff_of_isIso _ (K.cyclesIsoSc' i j (c.next j) hij rfl).hom,
    K.toCycles_cyclesIsoSc'_hom]
  exact h.epi_toCycles

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- Taking cycles is additive on morphisms of complexes. -/
@[simp]
lemma cyclesMap_add (f g : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i := by
  apply (cancel_mono (L.iCycles i)).1
  simp only [Preadditive.add_comp, cyclesMap_i, add_f_apply, Preadditive.comp_add]

instance cyclesFunctor_additive [CategoryWithHomology C] (i : ι) :
    (cyclesFunctor C c i).Additive where
  map_add := by
    intro X Y f g
    -- `cyclesFunctor` is opaque, so expose its defining map before applying the map-level API.
    change cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i
    exact cyclesMap_add f g i

end HomologicalComplex

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {K L : ChainComplex C ℕ} [K.HasHomology 0] [L.HasHomology 0]

/-- The identification of degree-zero chains with degree-zero cycles is natural. -/
@[reassoc]
lemma cycles₀Iso_inv_naturality (φ : K ⟶ L) :
    K.cycles₀Iso.inv ≫ HomologicalComplex.cyclesMap φ 0 =
      φ.f 0 ≫ L.cycles₀Iso.inv := by
  apply (cancel_mono (L.iCycles 0)).1
  simp

end ChainComplex
