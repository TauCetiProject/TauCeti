/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Filtered.Alexander
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Maslov
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Maslov-graded Alexander-filtered grid complexes

The differential counting all empty rectangles lowers `O`-Maslov degree by one,
even when it crosses `X`-markings. Restricting it to Maslov-homogeneous polynomial
chains gives `GridDiagram.gradedFilteredComplex`, a chain complex indexed by `ℤ`
over the coefficient ring. Multiplication by a polynomial does not preserve
Maslov degree, so these degree objects are not polynomial-ring modules.

For an odd-component grid, intersecting each Maslov piece with the Alexander
filtration gives `OddComponentGridDiagram.alexanderFiltrationComplex`. The
inclusion chain maps make these levels an increasing family of subcomplexes of
the total Maslov-graded complex. The filtration is exhaustive and separated in
every Maslov degree. This packages the chain objects needed for filtered chain
maps and homotopies without forgetting the homological grading. No invariance
under grid moves is asserted here.

The grading and filtration conventions follow Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 13.
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*)

section CommSemiring

variable [CommSemiring R]

/-- Allowing `X`-markings in rectangles does not alter the Maslov degree of the
differential: it still lowers degree by one. -/
theorem filteredDifferential_mem_maslovChainMinusPiece {m : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.maslovChainMinusPiece R m) :
    G.filteredDifferential R c ∈ G.maslovChainMinusPiece R (m - 1) := by
  rw [mem_maslovChainMinusPiece] at hc ⊢
  intro y
  rw [filteredDifferential_apply_apply, Finsupp.sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun x _ => ?_
  convert (hc x).mul (G.isWeightedHomogeneous_filteredCoefficient R x y) using 1; ring

/-- The filtered grid differential restricted to consecutive Maslov pieces. -/
noncomputable def gradedFilteredDifferential (m : ℤ) :
    G.maslovChainMinusPiece R (m + 1) →ₗ[R] G.maslovChainMinusPiece R m :=
  ((G.filteredDifferential R).restrictScalars R).restrict fun c hc => by
    simpa using G.filteredDifferential_mem_maslovChainMinusPiece R hc

/-- Inclusion of Maslov pieces identifies the restricted and total differentials. -/
@[simp]
theorem coe_gradedFilteredDifferential (m : ℤ) (c : G.maslovChainMinusPiece R (m + 1)) :
    (G.gradedFilteredDifferential R m c : GridChainMinus R n) = G.filteredDifferential R c :=
  (rfl)

variable [CharP R 2]

/-- Consecutive Maslov-graded filtered differentials compose to zero. -/
theorem gradedFilteredDifferential_comp_eq_zero (m : ℤ) :
    (G.gradedFilteredDifferential R m).comp (G.gradedFilteredDifferential R (m + 1)) = 0 := by
  ext c : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, coe_gradedFilteredDifferential,
    ZeroMemClass.coe_zero]
  exact LinearMap.congr_fun (G.filteredDifferential_comp_self_eq_zero R) c

end CommSemiring

variable [CommRing R] [CharP R 2]

/-- The grid complex counting every empty rectangle, indexed by `O`-Maslov degree.
The Alexander grading is a filtration, not a second homological degree. -/
noncomputable def gradedFilteredComplex : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (G.maslovChainMinusPiece R m))
    (fun m => ModuleCat.ofHom (G.gradedFilteredDifferential R m)) (fun m => by
      rw [← ModuleCat.ofHom_comp, G.gradedFilteredDifferential_comp_eq_zero,
        ModuleCat.ofHom_zero])

/-- The degree objects of the filtered complex are the Maslov-homogeneous chains. -/
@[simp]
theorem gradedFilteredComplex_X (m : ℤ) :
    (G.gradedFilteredComplex R).X m = ModuleCat.of R (G.maslovChainMinusPiece R m) := (rfl)

-- Object transports keep the computation API well-typed while the complex body is unexposed.
/-- The consecutive differential is the restriction of the total filtered differential. -/
@[simp]
theorem gradedFilteredComplex_d (m : ℤ) :
    (G.gradedFilteredComplex R).d (m + 1) m =
      eqToHom (G.gradedFilteredComplex_X R (m + 1)) ≫
        ModuleCat.ofHom (G.gradedFilteredDifferential R m) ≫
          eqToHom (G.gradedFilteredComplex_X R m).symm := by
  simp only [gradedFilteredComplex, ChainComplex.of_d]
  -- The object identifications are identities on the explicit homogeneous chains.
  ext c
  rfl

end TauCeti.GridDiagram

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*)

section CommSemiring

variable [CommSemiring R]

/-- Maslov degree `m` chains in Alexander filtration level `a`. -/
noncomputable def alexanderFilteredChainPiece (a m : ℤ) : Submodule R (GridChainMinus R n) :=
  G.1.maslovChainMinusPiece R m ⊓ (G.alexanderFiltration R a).restrictScalars R

variable {G R} in
/-- A filtered homogeneous chain is Maslov homogeneous and satisfies the Alexander bound. -/
@[simp]
theorem mem_alexanderFilteredChainPiece {a m : ℤ} {c : GridChainMinus R n} :
    c ∈ G.alexanderFilteredChainPiece R a m ↔
      c ∈ G.1.maslovChainMinusPiece R m ∧ c ∈ G.alexanderFiltration R a := Iff.rfl

/-- The filtered homogeneous chain pieces increase with the Alexander bound. -/
theorem alexanderFilteredChainPiece_mono (m : ℤ) :
    Monotone (fun a => G.alexanderFilteredChainPiece R a m) :=
  fun _ _ hab _ hc => ⟨hc.1, G.alexanderFiltration_mono R hab hc.2⟩

/-- Every Maslov-homogeneous chain lies in some Alexander filtration level. -/
theorem iSup_alexanderFilteredChainPiece_eq (m : ℤ) :
    ⨆ a, G.alexanderFilteredChainPiece R a m = G.1.maslovChainMinusPiece R m := by
  refine le_antisymm (iSup_le fun _ => inf_le_left) fun c hc => ?_
  have ht : c ∈ ⨆ a, G.alexanderFiltration R a := by
    rw [G.iSup_alexanderFiltration_eq_top R]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_iSup_of_directed _
    (G.alexanderFiltration_mono R).directed_le).mp ht
  exact le_iSup (fun a => G.alexanderFilteredChainPiece R a m) a ⟨hc, ha⟩

/-- The Alexander filtration is separated within every Maslov degree. -/
theorem iInf_alexanderFilteredChainPiece_eq_bot (m : ℤ) :
    ⨅ a, G.alexanderFilteredChainPiece R a m = ⊥ := by
  refine eq_bot_iff.mpr fun c hc => ?_
  have ht : c ∈ ⨅ a, G.alexanderFiltration R a :=
    (Submodule.mem_iInf _).mpr fun a => ((Submodule.mem_iInf _).mp hc a).2
  simpa only [G.iInf_alexanderFiltration_eq_bot R, Submodule.mem_bot] using ht

/-- The filtered differential lowers Maslov degree and preserves the Alexander bound. -/
noncomputable def alexanderFilteredDifferential (a m : ℤ) :
    G.alexanderFilteredChainPiece R a (m + 1) →ₗ[R] G.alexanderFilteredChainPiece R a m :=
  ((G.1.filteredDifferential R).restrictScalars R).restrict fun c hc =>
    ⟨by simpa using G.1.filteredDifferential_mem_maslovChainMinusPiece R hc.1,
      G.filteredDifferential_mem_alexanderFiltration R hc.2⟩

/-- Inclusion identifies the filtered homogeneous differential with the total differential. -/
@[simp]
theorem coe_alexanderFilteredDifferential (a m : ℤ)
    (c : G.alexanderFilteredChainPiece R a (m + 1)) :
    (G.alexanderFilteredDifferential R a m c : GridChainMinus R n) =
      G.1.filteredDifferential R c := (rfl)

variable [CharP R 2]

/-- Consecutive differentials within one Alexander filtration level compose to zero. -/
theorem alexanderFilteredDifferential_comp_eq_zero (a m : ℤ) :
    (G.alexanderFilteredDifferential R a m).comp
      (G.alexanderFilteredDifferential R a (m + 1)) = 0 := by
  ext c : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, coe_alexanderFilteredDifferential,
    ZeroMemClass.coe_zero]
  exact LinearMap.congr_fun (G.1.filteredDifferential_comp_self_eq_zero R) c

end CommSemiring

variable [CommRing R] [CharP R 2]

/-- Alexander filtration level `a` as a Maslov-graded chain complex. -/
noncomputable def alexanderFiltrationComplex (a : ℤ) : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (G.alexanderFilteredChainPiece R a m))
    (fun m => ModuleCat.ofHom (G.alexanderFilteredDifferential R a m)) (fun m => by
      rw [← ModuleCat.ofHom_comp, G.alexanderFilteredDifferential_comp_eq_zero,
        ModuleCat.ofHom_zero])

/-- The degree objects of a filtration level are the filtered homogeneous chains. -/
@[simp]
theorem alexanderFiltrationComplex_X (a m : ℤ) :
    (G.alexanderFiltrationComplex R a).X m =
      ModuleCat.of R (G.alexanderFilteredChainPiece R a m) := (rfl)

/-- The consecutive differential in a filtration level is the restricted grid differential. -/
@[simp]
theorem alexanderFiltrationComplex_d (a m : ℤ) :
    (G.alexanderFiltrationComplex R a).d (m + 1) m =
      eqToHom (G.alexanderFiltrationComplex_X R a (m + 1)) ≫
        ModuleCat.ofHom (G.alexanderFilteredDifferential R a m) ≫
          eqToHom (G.alexanderFiltrationComplex_X R a m).symm := by
  simp only [alexanderFiltrationComplex, ChainComplex.of_d]
  -- The object identifications are identities on the explicit filtered homogeneous chains.
  ext c
  rfl

/-- Inclusion of one Alexander filtration level in a larger one, as a chain map. -/
noncomputable def alexanderFiltrationComplexMap {a b : ℤ} (hab : a ≤ b) :
    G.alexanderFiltrationComplex R a ⟶ G.alexanderFiltrationComplex R b :=
  ChainComplex.ofHom (fun m => ModuleCat.ofHom
    (Submodule.inclusion (G.alexanderFilteredChainPiece_mono R m hab))) (fun m => by
      simp only [alexanderFiltrationComplex_d]
      ext c
      -- Both restrictions apply the same ambient differential; inclusion changes only membership.
      rfl)

/-- Inclusion in the total Maslov-graded filtered grid complex. -/
noncomputable def alexanderFiltrationComplexι (a : ℤ) :
    G.alexanderFiltrationComplex R a ⟶ G.1.gradedFilteredComplex R :=
  ChainComplex.ofHom (fun _ => ModuleCat.ofHom
    (Submodule.inclusion fun _ hc => (mem_alexanderFilteredChainPiece.mp hc).1)) (fun m => by
    simp only [alexanderFiltrationComplex_d, GridDiagram.gradedFilteredComplex_d]
    ext c
    -- The restricted and total graded differentials have the same underlying chain.
    rfl)

-- As for the differentials, the transports identify the unexposed complexes' degree objects.
/-- The filtration inclusion acts by inclusion of the explicit chain submodules. -/
@[simp]
theorem alexanderFiltrationComplexMap_f {a b : ℤ} (hab : a ≤ b) (m : ℤ) :
    (G.alexanderFiltrationComplexMap R hab).f m =
      eqToHom (G.alexanderFiltrationComplex_X R a m) ≫
        ModuleCat.ofHom (Submodule.inclusion (G.alexanderFilteredChainPiece_mono R m hab)) ≫
          eqToHom (G.alexanderFiltrationComplex_X R b m).symm := (rfl)

/-- The inclusion into the total complex is the ordinary inclusion in each degree. -/
@[simp]
theorem alexanderFiltrationComplexι_f (a m : ℤ) :
    (G.alexanderFiltrationComplexι R a).f m =
      eqToHom (G.alexanderFiltrationComplex_X R a m) ≫
        ModuleCat.ofHom (Submodule.inclusion (p := G.alexanderFilteredChainPiece R a m)
          (p' := G.1.maslovChainMinusPiece R m)
          (fun _ hc => (mem_alexanderFilteredChainPiece.mp hc).1)) ≫
          eqToHom (G.1.gradedFilteredComplex_X R m).symm := (rfl)

/-- Filtration inclusion is injective in every Maslov degree. -/
instance mono_alexanderFiltrationComplexMap_f {a b : ℤ} (hab : a ≤ b) (m : ℤ) :
    Mono ((G.alexanderFiltrationComplexMap R hab).f m) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  exact Submodule.inclusion_injective (G.alexanderFilteredChainPiece_mono R m hab)

/-- Each filtration level embeds degreewise into the total complex. -/
instance mono_alexanderFiltrationComplexι_f (a m : ℤ) :
    Mono ((G.alexanderFiltrationComplexι R a).f m) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  exact Submodule.inclusion_injective
    (fun _ hc => (mem_alexanderFilteredChainPiece.mp hc).1)

/-- A filtration inclusion is a monomorphism of complexes. -/
instance mono_alexanderFiltrationComplexMap {a b : ℤ} (hab : a ≤ b) :
    Mono (G.alexanderFiltrationComplexMap R hab) :=
  HomologicalComplex.mono_of_mono_f _ fun _ => inferInstance

/-- Each filtration level is a subcomplex of the total complex. -/
instance mono_alexanderFiltrationComplexι (a : ℤ) :
    Mono (G.alexanderFiltrationComplexι R a) :=
  HomologicalComplex.mono_of_mono_f _ fun _ => inferInstance

/-- Inclusion of a level in itself is the identity chain map. -/
@[simp]
theorem alexanderFiltrationComplexMap_refl (a : ℤ) :
    G.alexanderFiltrationComplexMap R (le_refl a) = 𝟙 _ := by
  ext m c
  -- Self-inclusion leaves the underlying chain unchanged, as does the identity.
  rfl

/-- Filtration inclusions compose as inclusions. -/
@[simp]
theorem alexanderFiltrationComplexMap_comp {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    G.alexanderFiltrationComplexMap R hab ≫ G.alexanderFiltrationComplexMap R hbc =
      G.alexanderFiltrationComplexMap R (hab.trans hbc) := by
  ext m x
  -- Composite and direct inclusion differ only in their membership proofs.
  rfl

/-- Filtration inclusions commute with the inclusions into the total complex. -/
@[simp]
theorem alexanderFiltrationComplexMap_ι {a b : ℤ} (hab : a ≤ b) :
    G.alexanderFiltrationComplexMap R hab ≫ G.alexanderFiltrationComplexι R b =
      G.alexanderFiltrationComplexι R a := by
  ext m c
  -- Both routes include the same chain in its Maslov piece; membership proofs are irrelevant.
  rfl

end TauCeti.OddComponentGridDiagram
