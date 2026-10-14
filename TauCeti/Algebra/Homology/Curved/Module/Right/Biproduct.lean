/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.ClosedCategory
public import TauCeti.Algebra.Module.GradedModule.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite biproducts of curved differential graded right modules

The zero right module and componentwise products carry curved differentials of the same
curvature. Their closed maps give a zero object and binary biproducts in the existing closed
category. These constructions will also supply the finite sums used by mapping cones.
The additive quotient functor sends the componentwise bicones to biproduct bicones in the
existing curved homotopy category, which therefore also has a zero object and finite biproducts.
-/

public section

open CategoryTheory CategoryTheory.Limits MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe uR uA uM uN

section Objects

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- The zero curved right module, with all homogeneous pieces and differential zero. -/
@[expose, implicit_reducible]
noncomputable def zero (h : IsCurvedDGAlgebra 𝒜 d w) :
    CurvedDGRightModuleCat.{uR, uA, uM} h := by
  let G : InternalGrading R PUnit.{uM + 1} :=
    { piece := fun _ ↦ ⊥
      isInternal := ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
        fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩ }
  letI : DirectSum.Decomposition G.piece := G.isInternal.chooseDecomposition
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece G.piece :=
    ⟨fun _ _ _ _ _ _ ↦ by
      -- Reduce the locally chosen grading in this membership goal to its bottom piece.
      change _ ∈ (⊥ : Submodule R PUnit.{uM + 1})
      simp⟩
  exact
    { carrier := PUnit.{uM + 1}
      grading := G.piece
      differential := 0
      isCurvedDGRightModule :=
        { isHomogeneous := LinearMap.isHomogeneous_zero _ _ _
          leibniz := fun _ _ ↦ Subsingleton.elim _ _
          sq_eq := fun _ ↦ Subsingleton.elim _ _ } }

instance (h : IsCurvedDGAlgebra 𝒜 d w) : Subsingleton (zero.{uR, uA, uM} h) :=
  inferInstanceAs (Subsingleton PUnit.{uM + 1})

variable {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The product curved right module has componentwise grading, action and differential. -/
@[expose, implicit_reducible]
noncomputable def prod (M : CurvedDGRightModuleCat.{uR, uA, uM} h)
    (N : CurvedDGRightModuleCat.{uR, uA, uN} h) :
    CurvedDGRightModuleCat.{uR, uA, max uM uN} h := by
  let G := (InternalGrading.ofDecomposition M.grading).prod
    (InternalGrading.ofDecomposition N.grading)
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece G.piece :=
    ⟨fun i j a x ha hx ↦ by
      simp only [G, InternalGrading.prod_piece, InternalGrading.ofDecomposition_piece,
        Submodule.mem_prod] at hx ⊢
      exact ⟨SetLike.GradedSMul.smul_mem ha hx.1, SetLike.GradedSMul.smul_mem ha hx.2⟩⟩
  refine
    { carrier := M × N
      grading := G.piece
      differential := M.differential.prodMap N.differential
      isCurvedDGRightModule := ?_ }
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.isHomogeneous_def.mpr
    intro p x hx
    simp only [G, InternalGrading.prod_piece, InternalGrading.ofDecomposition_piece,
      Submodule.mem_prod, LinearMap.prodMap_apply] at hx ⊢
    exact ⟨M.isCurvedDGRightModule.isHomogeneous.map_mem hx.1,
      N.isCurvedDGRightModule.isHomogeneous.map_mem hx.2⟩
  · intro p x hx a
    simp only [G, InternalGrading.prod_piece, InternalGrading.ofDecomposition_piece,
      Submodule.mem_prod] at hx
    apply Prod.ext
    · exact M.isCurvedDGRightModule.leibniz hx.1 a
    · exact N.isCurvedDGRightModule.leibniz hx.2 a
  · intro x
    apply Prod.ext
    · exact M.isCurvedDGRightModule.sq_eq x.1
    · exact N.isCurvedDGRightModule.sq_eq x.2

/-- The product grading is componentwise. -/
@[simp]
theorem prod_grading (M : CurvedDGRightModuleCat.{uR, uA, uM} h)
    (N : CurvedDGRightModuleCat.{uR, uA, uN} h) (p : ℤ) :
    (M.prod N).grading p = (M.grading p).prod (N.grading p) := by
  simp only [prod, InternalGrading.prod_piece, InternalGrading.ofDecomposition_piece]

/-- The product differential is componentwise. -/
@[simp]
theorem prod_differential_apply (M : CurvedDGRightModuleCat.{uR, uA, uM} h)
    (N : CurvedDGRightModuleCat.{uR, uA, uN} h) (x : M × N) :
    (M.prod N).differential x = (M.differential x.1, N.differential x.2) :=
  (rfl)

end Objects

universe u

section Closed

-- Mathlib's closed category keeps the enriched object carrier.
attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The zero curved module is a zero object in the closed category. -/
theorem isZero_closed_zero :
    IsZero (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (zero h)) := by
  refine ⟨fun X ↦ ⟨?_⟩, fun X ↦ ⟨?_⟩⟩
  · refine { default := 0, uniq := ?_ }
    intro f
    apply closedHom_ext
    intro x
    rw [Subsingleton.elim x 0]
    simp
  · refine { default := 0, uniq := ?_ }
    intro f
    apply closedHom_ext
    intro x
    exact Subsingleton.elim _ _

noncomputable instance : HasZeroObject
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  isZero_closed_zero.hasZeroObject

variable (M N : CurvedDGRightModuleCat.{u, u, u} h)

/-- The first projection of the product is a closed morphism. -/
noncomputable def closedProdFst :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.prod N) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  closedHomOf (LinearMap.fst Aᵐᵒᵖ M N)
    (fun p x hx ↦ by rw [prod_grading] at hx; exact hx.1) (fun _ ↦ rfl)

/-- The second projection of the product is a closed morphism. -/
noncomputable def closedProdSnd :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.prod N) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N :=
  closedHomOf (LinearMap.snd Aᵐᵒᵖ M N)
    (fun p x hx ↦ by rw [prod_grading] at hx; exact hx.2) (fun _ ↦ rfl)

/-- The first inclusion in the product is a closed morphism. -/
noncomputable def closedProdInl :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.prod N) :=
  closedHomOf (LinearMap.inl Aᵐᵒᵖ M N)
    (fun p x hx ↦ by rw [prod_grading]; exact ⟨hx, (N.grading p).zero_mem⟩)
    (fun x ↦ by
      -- The bundled product carrier hides the pair types, so inclusion rewrites do not match
      -- until the carrier and the componentwise differential are reduced.
      change (M.differential x, N.differential 0) = (M.differential x, 0)
      rw [map_zero])

/-- The second inclusion in the product is a closed morphism. -/
noncomputable def closedProdInr :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.prod N) :=
  closedHomOf (LinearMap.inr Aᵐᵒᵖ M N)
    (fun p x hx ↦ by rw [prod_grading]; exact ⟨(M.grading p).zero_mem, hx⟩)
    (fun x ↦ by
      -- The bundled product carrier hides the pair types, so inclusion rewrites do not match
      -- until the carrier and the componentwise differential are reduced.
      change (M.differential 0, N.differential x) = (0, N.differential x)
      rw [map_zero])

/-- The first closed projection is the usual linear projection. -/
@[simp]
theorem closedHom_closedProdFst :
    closedHom (closedProdFst M N) = LinearMap.fst Aᵐᵒᵖ M N := by
  dsimp only [closedProdFst]
  exact closedHom_closedHomOf _ _ _

/-- The second closed projection is the usual linear projection. -/
@[simp]
theorem closedHom_closedProdSnd :
    closedHom (closedProdSnd M N) = LinearMap.snd Aᵐᵒᵖ M N := by
  dsimp only [closedProdSnd]
  exact closedHom_closedHomOf _ _ _

/-- The first closed inclusion is the usual linear inclusion. -/
@[simp]
theorem closedHom_closedProdInl :
    closedHom (closedProdInl M N) = LinearMap.inl Aᵐᵒᵖ M N := by
  dsimp only [closedProdInl]
  exact closedHom_closedHomOf _ _ _

/-- The second closed inclusion is the usual linear inclusion. -/
@[simp]
theorem closedHom_closedProdInr :
    closedHom (closedProdInr M N) = LinearMap.inr Aᵐᵒᵖ M N := by
  dsimp only [closedProdInr]
  exact closedHom_closedHomOf _ _ _

/-- The four componentwise maps form a binary bicone in the closed category. -/
noncomputable def closedProdBicone :
    BinaryBicone (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) where
  pt := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.prod N)
  fst := closedProdFst M N
  snd := closedProdSnd M N
  inl := closedProdInl M N
  inr := closedProdInr M N
  inl_fst := by apply closedHom_ext; intro x; simp; rfl
  inl_snd := by apply closedHom_ext; intro x; simp; rfl
  inr_fst := by apply closedHom_ext; intro x; simp; rfl
  inr_snd := by apply closedHom_ext; intro x; simp; rfl

/-- The point of the closed product bicone is the componentwise product. -/
@[simp]
theorem closedProdBicone_pt :
    (closedProdBicone M N).pt =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.prod N) :=
  (rfl)

/-- The first projection of the closed bicone is the componentwise closed map. -/
@[simp]
theorem closedProdBicone_fst :
    (closedProdBicone M N).fst =
      eqToHom (closedProdBicone_pt M N) ≫ closedProdFst M N := by
  dsimp only [closedProdBicone]
  erw [eqToHom_refl, Category.id_comp]

/-- The second projection of the closed bicone is the componentwise closed map. -/
@[simp]
theorem closedProdBicone_snd :
    (closedProdBicone M N).snd =
      eqToHom (closedProdBicone_pt M N) ≫ closedProdSnd M N := by
  dsimp only [closedProdBicone]
  erw [eqToHom_refl, Category.id_comp]

/-- The first inclusion of the closed bicone is the componentwise closed map. -/
@[simp]
theorem closedProdBicone_inl :
    (closedProdBicone M N).inl =
      closedProdInl M N ≫ eqToHom (closedProdBicone_pt M N).symm := by
  dsimp only [closedProdBicone]
  erw [eqToHom_refl, Category.comp_id]

/-- The second inclusion of the closed bicone is the componentwise closed map. -/
@[simp]
theorem closedProdBicone_inr :
    (closedProdBicone M N).inr =
      closedProdInr M N ≫ eqToHom (closedProdBicone_pt M N).symm := by
  dsimp only [closedProdBicone]
  erw [eqToHom_refl, Category.comp_id]

/-- The componentwise bicone is both a limit and a colimit. -/
noncomputable def closedProdBiconeIsBilimit : (closedProdBicone M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (by
    dsimp only [closedProdBicone]
    apply closedHom_ext
    intro x
    erw [closedHom_add, closedHom_comp, closedHom_comp, closedHom_closedProdFst,
      closedHom_closedProdSnd, closedHom_closedProdInl, closedHom_closedProdInr, closedHom_id]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    -- The bundled carrier hides the pair types in these linear-map applications; expose them
    -- to identify the remaining inclusions and projections with their coordinate formulas.
    change (x.1, 0) + (0, x.2) = x
    exact Prod.ext (add_zero _) (zero_add _))

noncomputable instance
    (X Y : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := closedProdBicone (ForgetEnrichment.to _ X) (ForgetEnrichment.to _ Y)
      isBilimit := closedProdBiconeIsBilimit _ _ }

noncomputable instance : HasBinaryBiproducts
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  ⟨fun _ _ ↦ inferInstance⟩

noncomputable instance : HasFiniteProducts
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) := by
  let : HasTerminal (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} h)) := HasZeroObject.hasTerminal
  exact hasFiniteProducts_of_has_binary_and_terminal

noncomputable instance : HasFiniteBiproducts
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end Closed

section Homotopy

-- The quotient and its object wrappers retain the original curved-module carriers.
attribute [local implicit_reducible] dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The class of the zero curved module is a zero object. -/
theorem isZero_homotopy_zero : IsZero (DGHomotopyCategory.of R (zero h)) := by
  simpa only [dgClosedToHomotopy_obj, ForgetEnrichment.to_of] using
    (dgClosedToHomotopy R).map_isZero (isZero_closed_zero (h := h))

noncomputable instance : HasZeroObject
    (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  isZero_homotopy_zero.hasZeroObject

variable (M N : CurvedDGRightModuleCat.{u, u, u} h)

/-- The componentwise product bicone in the curved homotopy category. -/
noncomputable def homotopyProdBicone :
    BinaryBicone (DGHomotopyCategory.of R M) (DGHomotopyCategory.of R N) :=
  (dgClosedToHomotopy R).mapBinaryBicone (closedProdBicone M N)

/-- The point of the product bicone is the class of the componentwise product. -/
@[simp]
theorem homotopyProdBicone_pt :
    (homotopyProdBicone M N).pt = DGHomotopyCategory.of R (M.prod N) :=
  (rfl)

/-- The first homotopy projection is the class of the first closed projection. -/
@[simp]
theorem homotopyProdBicone_fst :
    (homotopyProdBicone M N).fst =
      eqToHom (homotopyProdBicone_pt M N) ≫ (dgClosedToHomotopy R).map (closedProdFst M N) := by
  dsimp only [homotopyProdBicone, Functor.mapBinaryBicone,
    BinaryBicones.functoriality, closedProdBicone]
  erw [eqToHom_refl, Category.id_comp]

/-- The second homotopy projection is the class of the second closed projection. -/
@[simp]
theorem homotopyProdBicone_snd :
    (homotopyProdBicone M N).snd =
      eqToHom (homotopyProdBicone_pt M N) ≫ (dgClosedToHomotopy R).map (closedProdSnd M N) := by
  dsimp only [homotopyProdBicone, Functor.mapBinaryBicone,
    BinaryBicones.functoriality, closedProdBicone]
  erw [eqToHom_refl, Category.id_comp]

/-- The first homotopy inclusion is the class of the first closed inclusion. -/
@[simp]
theorem homotopyProdBicone_inl :
    (homotopyProdBicone M N).inl =
      (dgClosedToHomotopy R).map (closedProdInl M N) ≫
        eqToHom (homotopyProdBicone_pt M N).symm := by
  dsimp only [homotopyProdBicone, Functor.mapBinaryBicone,
    BinaryBicones.functoriality, closedProdBicone]
  erw [eqToHom_refl, Category.comp_id]

/-- The second homotopy inclusion is the class of the second closed inclusion. -/
@[simp]
theorem homotopyProdBicone_inr :
    (homotopyProdBicone M N).inr =
      (dgClosedToHomotopy R).map (closedProdInr M N) ≫
        eqToHom (homotopyProdBicone_pt M N).symm := by
  dsimp only [homotopyProdBicone, Functor.mapBinaryBicone,
    BinaryBicones.functoriality, closedProdBicone]
  erw [eqToHom_refl, Category.comp_id]

/-- The componentwise bicone is a biproduct in the homotopy category. -/
noncomputable def homotopyProdBiconeIsBilimit : (homotopyProdBicone M N).IsBilimit := by
  let : PreservesBinaryBiproducts
      (dgClosedToHomotopy (C := CurvedDGRightModuleCat.{u, u, u} h) R) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact isBinaryBilimitOfPreserves
    (dgClosedToHomotopy (C := CurvedDGRightModuleCat.{u, u, u} h) R)
    (closedProdBiconeIsBilimit M N)

noncomputable instance
    (X Y : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := homotopyProdBicone (DGHomotopyCategory.underlying R X)
        (DGHomotopyCategory.underlying R Y)
      isBilimit := homotopyProdBiconeIsBilimit _ _ }

noncomputable instance : HasBinaryBiproducts
    (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  ⟨fun _ _ ↦ inferInstance⟩

noncomputable instance : HasFiniteProducts
    (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) := by
  let : HasTerminal (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
    HasZeroObject.hasTerminal
  exact hasFiniteProducts_of_has_binary_and_terminal

noncomputable instance : HasFiniteBiproducts
    (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end Homotopy

end TauCeti.CurvedDGRightModuleCat
