/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Cohomology

/-!
# Homotopies of morphisms of right A-infinity modules

Let `f g : M ⟶ N` be morphisms of right `A∞` modules over a fixed algebra. A homotopy from
`f` to `g` is a degree-`-1` morphism `H` of their cofree bar comodules satisfying

`F - G = b_N H + H b_M`.

The comodule morphism `H` is determined by its suspended Taylor map, obtained by applying the
coalgebra counit. The homotopy equation can likewise be checked after applying the counit. Its
component with no algebra inputs is an ordinary chain homotopy between the linear parts of `f`
and `g`; consequently homotopic module morphisms induce the same map on cohomology and are
quasi-isomorphisms together.

Homotopies are reflexive, symmetric, and transitive, and they are preserved by composition with
module morphisms on either side.

## Main definitions

* `TauCeti.AInfinityRightModuleHom.Homotopy`: a homotopy of right `A∞` module morphisms.
* `TauCeti.AInfinityRightModuleHom.Homotopy.taylor`: its suspended Taylor map.
* `TauCeti.AInfinityRightModuleHom.Homotopy.linearHomotopy`: its unary component.
* `TauCeti.AInfinityRightModuleHom.Homotopy.ofBarHomotopy`: construction from a homogeneous
  comodule morphism satisfying the suspended component equation.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

universe uR uA uL uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {L : Type uL} {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

namespace AInfinityRightModuleHom

variable {LL : AInfinityRightModule AA L} {MM : AInfinityRightModule AA M}
  {NN : AInfinityRightModule AA N} {PP : AInfinityRightModule AA P}

/-- A homotopy from `f` to `g` is a degree-`-1` morphism of their cofree bar comodules whose
commutator with the module bar differentials is `F - G`. -/
structure Homotopy (f g : AInfinityRightModuleHom MM NN) where
  /-- The degree-`-1` morphism of cofree bar comodules. -/
  barHomotopy : Comodule.Hom R (TensorWords R A)
    (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A)
  /-- The bar homotopy lowers the total suspended degree by one. -/
  isHomogeneous_barHomotopy : LinearMap.IsHomogeneous barHomotopy.toLinearMap
    (AInfinityRightModule.barGrading AA MM.grading).piece
    (AInfinityRightModule.barGrading AA NN.grading).piece (-1)
  /-- The homotopy equation `F - G = b_N H + H b_M`. -/
  barMap_sub_barMap :
    f.barMap - g.barMap = NN.barDifferential ∘ₗ barHomotopy.toLinearMap +
      barHomotopy.toLinearMap ∘ₗ MM.barDifferential

namespace Homotopy

variable {f g k : AInfinityRightModuleHom MM NN}

/-- The underlying linear map of the bar-comodule homotopy. -/
abbrev barMap (h : Homotopy f g) := h.barHomotopy.toLinearMap

/-- The homotopy equation, applied to one bar-comodule element. -/
theorem barMap_sub_barMap_apply (h : Homotopy f g) (z : M ⊗[R] TensorWords R A) :
    f.barMap z - g.barMap z =
      NN.barDifferential (h.barMap z) + h.barMap (MM.barDifferential z) :=
  LinearMap.congr_fun h.barMap_sub_barMap z

/-- The suspended Taylor map of a module homotopy, obtained by applying the coalgebra counit. -/
noncomputable def taylor (h : Homotopy f g) : (M ⊗[R] TensorWords R A) →ₗ[R] N :=
  (TensorProduct.rid R N).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ h.barMap

theorem taylor_def (h : Homotopy f g) :
    h.taylor = (TensorProduct.rid R N).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ h.barMap := (rfl)

/-- The Taylor map of a homotopy lowers suspended degree by one. -/
theorem isHomogeneous_taylor (h : Homotopy f g) :
    LinearMap.IsHomogeneous h.taylor
      (AInfinityRightModule.barGrading AA MM.grading).piece
      (NN.grading.shift 1).piece (-1) := by
  rw [taylor_def]
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  have hz := h.isHomogeneous_barHomotopy.map_mem hx
  rw [AInfinityRightModule.barGrading_piece] at hz
  simpa only [LinearMap.comp_apply, add_zero] using
    (TensorWords.isHomogeneous_rid_comp_lTensor_counit (NN.grading.shift 1)
      (AA.grading.shift 1)).map_mem hz

/-- The bar homotopy is the cofree lift of its Taylor map. -/
theorem barMap_eq_cofreeLift (h : Homotopy f g) :
    h.barMap = (Comodule.Hom.cofreeLift (C := TensorWords R A) h.taylor).toLinearMap := by
  have e := (Comodule.Hom.cofreeEquiv (R := R) (C := TensorWords R A) (M := N)
    (P := M ⊗[R] TensorWords R A)).symm_apply_apply h.barHomotopy
  rw [Comodule.Hom.cofreeEquiv_apply, Comodule.Hom.cofreeEquiv_symm_apply] at e
  exact congrArg Comodule.Hom.toLinearMap e.symm

/-- Homotopies between fixed morphisms are determined by their Taylor maps. -/
@[ext]
theorem ext {h h' : Homotopy f g} (e : h.taylor = h'.taylor) : h = h' := by
  have hbar : h.barHomotopy = h'.barHomotopy :=
    (Comodule.Hom.cofreeEquiv (R := R) (C := TensorWords R A) (M := N)
      (P := M ⊗[R] TensorWords R A)).injective (by
        rw [Comodule.Hom.cofreeEquiv_apply, Comodule.Hom.cofreeEquiv_apply]
        exact e)
  cases h
  cases h'
  simp only at hbar
  subst hbar
  rfl

/-- For a degree-`-1` comodule morphism, the full homotopy equation is equivalent to its
projection to the cogenerator. -/
theorem barMap_sub_barMap_iff
    (H : Comodule.Hom R (TensorWords R A)
      (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A))
    (hH : LinearMap.IsHomogeneous H.toLinearMap
      (AInfinityRightModule.barGrading AA MM.grading).piece
      (AInfinityRightModule.barGrading AA NN.grading).piece (-1)) :
    f.barMap - g.barMap = NN.barDifferential ∘ₗ H.toLinearMap +
        H.toLinearMap ∘ₗ MM.barDifferential ↔
      f.taylor - g.taylor = NN.taylor ∘ₗ H.toLinearMap +
        ((TensorProduct.rid R N).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ H.toLinearMap) ∘ₗ
            MM.barDifferential := by
  let K := H.coderivationComm (r := -1) (q := 1) (b := AA.coaugmentedBarDifferential)
    (AInfinityRightModule.barGrading AA MM.grading)
    (AInfinityRightModule.barGrading AA NN.grading) hH MM.barDifferential NN.barDifferential
    MM.isGradedCoderivation_barDifferential NN.isGradedCoderivation_barDifferential
  have hK : K.toLinearMap = NN.barDifferential ∘ₗ H.toLinearMap +
      H.toLinearMap ∘ₗ MM.barDifferential := by
    rw [Comodule.Hom.coderivationComm_toLinearMap]
    norm_num
    module
  have hKtaylor :
      (TensorProduct.rid R N).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ K.toLinearMap =
        NN.taylor ∘ₗ H.toLinearMap +
          ((TensorProduct.rid R N).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ H.toLinearMap) ∘ₗ
              MM.barDifferential := by
    rw [hK, ← LinearMap.comp_assoc, LinearMap.comp_add]
    simp only [LinearMap.comp_assoc, AInfinityRightModule.taylor_def]
  constructor
  · intro e
    have e' := congrArg (fun F ↦ (TensorProduct.rid R N).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ F) e
    simpa only [LinearMap.comp_sub, LinearMap.comp_add, LinearMap.comp_assoc,
      AInfinityRightModuleHom.taylor_def, AInfinityRightModule.taylor_def] using e'
  · intro e
    have hhom : f.barHom = g.barHom + K := by
      apply (Comodule.Hom.cofreeEquiv (R := R) (C := TensorWords R A) (M := N)
        (P := M ⊗[R] TensorWords R A)).injective
      rw [Comodule.Hom.cofreeEquiv_apply, Comodule.Hom.cofreeEquiv_apply,
        Comodule.Hom.add_toLinearMap, LinearMap.comp_add, LinearMap.comp_add, hKtaylor]
      rw [← f.taylor_def, ← g.taylor_def]
      rw [sub_eq_iff_eq_add] at e
      simpa only [add_comm] using e
    have hlin := congrArg Comodule.Hom.toLinearMap hhom
    rw [Comodule.Hom.add_toLinearMap, hK] at hlin
    rw [sub_eq_iff_eq_add]
    simpa only [add_comm] using hlin

/-- The suspended component equation of a module homotopy. -/
theorem taylor_sub_taylor (h : Homotopy f g) :
    f.taylor - g.taylor = NN.taylor ∘ₗ h.barMap + h.taylor ∘ₗ MM.barDifferential :=
  (barMap_sub_barMap_iff h.barHomotopy h.isHomogeneous_barHomotopy).1 h.barMap_sub_barMap

/-- Construct a homotopy from a degree-`-1` comodule morphism satisfying the suspended
component equation. -/
noncomputable def ofBarHomotopy
    (H : Comodule.Hom R (TensorWords R A)
      (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A))
    (hH : LinearMap.IsHomogeneous H.toLinearMap
      (AInfinityRightModule.barGrading AA MM.grading).piece
      (AInfinityRightModule.barGrading AA NN.grading).piece (-1))
    (e : f.taylor - g.taylor = NN.taylor ∘ₗ H.toLinearMap +
      ((TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ H.toLinearMap) ∘ₗ
          MM.barDifferential) : Homotopy f g where
  barHomotopy := H
  isHomogeneous_barHomotopy := hH
  barMap_sub_barMap := (barMap_sub_barMap_iff H hH).2 e

@[simp]
theorem barHomotopy_ofBarHomotopy (H hH e) :
    (ofBarHomotopy (f := f) (g := g) H hH e).barHomotopy = H := (rfl)

/-- The Taylor map of a homotopy constructed from a bar-comodule morphism is its counit
component. -/
@[simp]
theorem taylor_ofBarHomotopy (H hH e) :
    (ofBarHomotopy (f := f) (g := g) H hH e).taylor =
      (TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ H.toLinearMap :=
  (rfl)

/-! ### The unary component -/

/-- The unary component of a module homotopy, evaluated on the empty algebra word. -/
noncomputable def linearHomotopy (h : Homotopy f g) : M →ₗ[R] N :=
  h.taylor ∘ₗ (TensorProduct.mk R M (TensorWords R A)).flip 1

@[simp]
theorem linearHomotopy_apply (h : Homotopy f g) (x : M) :
    h.linearHomotopy x = h.taylor (x ⊗ₜ[R] (1 : TensorWords R A)) := (rfl)

/-- A bar homotopy sends an empty algebra word to the empty word multiplied by its unary
component. -/
@[simp]
theorem barMap_tmul_one (h : Homotopy f g) (x : M) :
    h.barMap (x ⊗ₜ[R] (1 : TensorWords R A)) =
      h.linearHomotopy x ⊗ₜ[R] (1 : TensorWords R A) := by
  rw [barMap_eq_cofreeLift, Comodule.Hom.cofreeLift_toLinearMap]
  simp only [LinearMap.comp_apply, Comodule.cofree_coact_tmul,
    TensorWords.comul_eq_deconcatenation, TensorWords.deconcatenation_one,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, linearHomotopy_apply]

/-- The unary component of a module homotopy lowers the unsuspended degree by one. -/
theorem linearHomotopy_mem (h : Homotopy f g) {x : M} {p : ℤ}
    (hx : x ∈ MM.grading.piece p) : h.linearHomotopy x ∈ NN.grading.piece (p - 1) := by
  have hx' : x ∈ (MM.grading.shift 1).piece (p - 1) := by
    rw [InternalGrading.shift_piece, sub_add_cancel]
    exact hx
  have h1 : (1 : TensorWords R A) ∈
      (TensorWords.grading (AA.grading.shift 1)).piece 0 := by
    rw [TensorWords.grading_piece]
    exact TensorWords.one_mem_gradedPiece (AA.grading.shift 1)
  have hz : x ⊗ₜ[R] (1 : TensorWords R A) ∈
      (AInfinityRightModule.barGrading AA MM.grading).piece (p - 1) := by
    rw [AInfinityRightModule.barGrading_piece]
    simpa only [add_zero] using InternalGrading.tmul_mem_tensorProduct
      (MM.grading.shift 1) (TensorWords.grading (AA.grading.shift 1)) hx' h1
  have hh := h.isHomogeneous_taylor.map_mem hz
  -- Unsuspending the output adds one to the degree, which needs explicit normalization.
  simpa only [linearHomotopy_apply, InternalGrading.shift_piece,
    show p - 1 + -1 + 1 = p - 1 by ring] using hh

/-- The unary component is a chain homotopy between the linear parts. -/
theorem linearPart_sub_linearPart (h : Homotopy f g) (x : M) :
    f.linearPart x - g.linearPart x =
      NN.differential (h.linearHomotopy x) + h.linearHomotopy (MM.differential x) := by
  have e := LinearMap.congr_fun h.taylor_sub_taylor (x ⊗ₜ[R] (1 : TensorWords R A))
  have htaylorN (y : N) :
      NN.taylor (y ⊗ₜ[R] (1 : TensorWords R A)) = NN.differential y := by
    rw [AInfinityRightModule.taylor_tmul_one NN y (fun i ↦ i.elim0),
      AInfinityRightModule.differential_apply]
  have htaylorM (y : M) :
      MM.taylor (y ⊗ₜ[R] (1 : TensorWords R A)) = MM.differential y := by
    rw [AInfinityRightModule.taylor_tmul_one MM y (fun i ↦ i.elim0),
      AInfinityRightModule.differential_apply]
  simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    linearPart_apply, barMap_tmul_one, linearHomotopy_apply,
    AInfinityRightModule.barDifferential_tmul_one,
    htaylorN, htaylorM] using e

/-! ### Cohomology -/

/-- Homotopic module morphisms induce the same map on unary cohomology. -/
theorem cohomologyMap_eq (h : Homotopy f g) : f.cohomologyMap = g.cohomologyMap := by
  apply LinearMap.ext
  intro c
  obtain ⟨x, hx, rfl⟩ := MM.exists_cohomologyClass_eq c
  rw [cohomologyMap_cohomologyClass, cohomologyMap_cohomologyClass,
    NN.cohomologyClass_eq_iff, h.linearPart_sub_linearPart,
    MM.mem_cycles.1 hx, map_zero, add_zero]
  exact NN.mem_boundaries.2 ⟨h.linearHomotopy x, rfl⟩

/-- Homotopic module morphisms are quasi-isomorphisms together. -/
theorem isQuasiIso_iff (h : Homotopy f g) : f.IsQuasiIso ↔ g.IsQuasiIso := by
  rw [isQuasiIso_def, isQuasiIso_def, h.cohomologyMap_eq]

/-! ### Equivalence and composition laws -/

/-- The zero homotopy from a module morphism to itself. -/
def refl (f : AInfinityRightModuleHom MM NN) : Homotopy f f where
  barHomotopy := 0
  isHomogeneous_barHomotopy := LinearMap.isHomogeneous_zero _ _ _
  barMap_sub_barMap := by simp

@[simp]
theorem barMap_refl (f : AInfinityRightModuleHom MM NN) : (refl f).barMap = 0 := (rfl)

@[simp]
theorem taylor_refl (f : AInfinityRightModuleHom MM NN) : (refl f).taylor = 0 := by
  simp only [taylor_def, barMap_refl, LinearMap.comp_zero]

/-- Reverse a module homotopy. -/
def symm (h : Homotopy f g) : Homotopy g f where
  barHomotopy := (-1 : R) • h.barHomotopy
  isHomogeneous_barHomotopy := by
    rw [Comodule.Hom.smul_toLinearMap]
    rw [LinearMap.isHomogeneous_def]
    intro p x hx
    exact Submodule.smul_mem _ (-1 : R) (h.isHomogeneous_barHomotopy.map_mem hx)
  barMap_sub_barMap := by
    rw [Comodule.Hom.smul_toLinearMap]
    apply LinearMap.ext
    intro x
    have heq := LinearMap.congr_fun h.barMap_sub_barMap x
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, map_smul] at heq ⊢
    rw [neg_one_smul R, neg_one_smul R]
    calc
      g.barMap x - f.barMap x = -(f.barMap x - g.barMap x) := by abel
      _ = -(NN.barDifferential (h.barMap x) + h.barMap (MM.barDifferential x)) :=
        congrArg Neg.neg heq
      _ = -NN.barDifferential (h.barMap x) + -h.barMap (MM.barDifferential x) := by abel

@[simp]
theorem barMap_symm (h : Homotopy f g) : h.symm.barMap = -h.barMap := by
  -- `barMap` is an abbreviation over the stored comodule morphism, so expose that projection.
  change ((-1 : R) • h.barHomotopy).toLinearMap = -h.barMap
  rw [Comodule.Hom.smul_toLinearMap]
  exact neg_one_smul R h.barMap

/-- Concatenate two module homotopies. -/
def trans (h : Homotopy f g) (h' : Homotopy g k) : Homotopy f k where
  barHomotopy := h.barHomotopy + h'.barHomotopy
  isHomogeneous_barHomotopy := by
    rw [Comodule.Hom.add_toLinearMap]
    exact h.isHomogeneous_barHomotopy.add h'.isHomogeneous_barHomotopy
  barMap_sub_barMap := by
    rw [Comodule.Hom.add_toLinearMap, LinearMap.comp_add, LinearMap.add_comp]
    have heq := h.barMap_sub_barMap
    have heq' := h'.barMap_sub_barMap
    calc
      f.barMap - k.barMap = (f.barMap - g.barMap) + (g.barMap - k.barMap) := by module
      _ = (NN.barDifferential ∘ₗ h.barMap + h.barMap ∘ₗ MM.barDifferential) +
          (NN.barDifferential ∘ₗ h'.barMap + h'.barMap ∘ₗ MM.barDifferential) := by
            rw [heq, heq']
      _ = NN.barDifferential ∘ₗ h.barMap + NN.barDifferential ∘ₗ h'.barMap +
          (h.barMap ∘ₗ MM.barDifferential + h'.barMap ∘ₗ MM.barDifferential) := by module

@[simp]
theorem barMap_trans (h : Homotopy f g) (h' : Homotopy g k) :
    (h.trans h').barMap = h.barMap + h'.barMap := (rfl)

/-- Postcomposition of a homotopy by a module morphism. -/
def compRight (h : Homotopy f g) (l : AInfinityRightModuleHom NN PP) :
    Homotopy (l.comp f) (l.comp g) where
  barHomotopy := l.barHom.comp h.barHomotopy
  isHomogeneous_barHomotopy := by
    rw [Comodule.Hom.comp_toLinearMap]
    simpa only [add_zero] using l.isHomogeneous_barMap.comp h.isHomogeneous_barHomotopy
  barMap_sub_barMap := by
    rw [barMap_comp, barMap_comp, Comodule.Hom.comp_toLinearMap, ← LinearMap.comp_sub,
      h.barMap_sub_barMap]
    simp only [LinearMap.comp_add, ← LinearMap.comp_assoc,
      ← l.barDifferential_comp_barMap]

@[simp]
theorem barMap_compRight (h : Homotopy f g) (l : AInfinityRightModuleHom NN PP) :
    (h.compRight l).barMap = l.barMap ∘ₗ h.barMap := (rfl)

/-- Postcomposition applies the Taylor map of the outer morphism to the bar homotopy. -/
theorem taylor_compRight (h : Homotopy f g) (l : AInfinityRightModuleHom NN PP) :
    (h.compRight l).taylor = l.taylor ∘ₗ h.barMap := by
  simp only [taylor_def, barMap_compRight, AInfinityRightModuleHom.taylor_def,
    LinearMap.comp_assoc]

/-- Precomposition of a homotopy by a module morphism. -/
def compLeft (h : Homotopy f g) (l : AInfinityRightModuleHom LL MM) :
    Homotopy (f.comp l) (g.comp l) where
  barHomotopy := h.barHomotopy.comp l.barHom
  isHomogeneous_barHomotopy := by
    rw [Comodule.Hom.comp_toLinearMap]
    simpa only [zero_add] using h.isHomogeneous_barHomotopy.comp l.isHomogeneous_barMap
  barMap_sub_barMap := by
    rw [barMap_comp, barMap_comp, Comodule.Hom.comp_toLinearMap, ← LinearMap.sub_comp,
      h.barMap_sub_barMap]
    simp only [LinearMap.add_comp, LinearMap.comp_assoc, l.barDifferential_comp_barMap]

@[simp]
theorem barMap_compLeft (h : Homotopy f g) (l : AInfinityRightModuleHom LL MM) :
    (h.compLeft l).barMap = h.barMap ∘ₗ l.barMap := (rfl)

/-- Precomposition applies the Taylor map of the homotopy after the inner bar map. -/
theorem taylor_compLeft (h : Homotopy f g) (l : AInfinityRightModuleHom LL MM) :
    (h.compLeft l).taylor = h.taylor ∘ₗ l.barMap := by
  simp only [taylor_def, barMap_compLeft, LinearMap.comp_assoc]

end Homotopy

end AInfinityRightModuleHom

end TauCeti
