/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.Restriction.Shift
public import TauCeti.KnotTheory.Khovanov.Resolution.Cube
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# The normalized Khovanov complex

For a planar oriented PD-code, `TauCeti.OrientedPDCode.khovanovComplex` is a quantum-indexed
family of native cochain complexes. A state with B-resolutions `S` occurs in cochain degree
`|S| - n₋` and carries the quantum shift `|S| + n₊ - 2n₋`. The differential retains the cube
sign `(-1)^(#{b ∈ S | b < a})` on the saddle adding `a`.

`khovanovComplexXIso` identifies its terms with the finite biproduct of these quantum pieces.
The inclusions and projections characterize the terms, and `ι_khovanovComplex_d` gives the
signed saddle differential. The complex is supported in `[-n₋, n₊]`.

`khovanovComplexShiftIso` compares this explicit state convention to the native cochain shift
of the bracket. Its degree-`i` component is `(-1)^(i * n₋)`, since native shifts change the
differential by `(-1)^n₋`. Quantum shifts raise degrees: the component at `j` uses the bracket
at `j - (n₊ - 2n₋)`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Finset HomologicalComplex

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n)

variable (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- The normalized Khovanov complex of a planar oriented diagram. Quantum degree `j` uses
bracket degree `j - n₊ + 2n₋`, and cochain degree `i` uses cube height `i + n₋`.
Restriction translates indices while preserving the original signed saddle differential. -/
def khovanovComplex : GradedObject ℤ (CochainComplex (ModuleCat.{u} R) ℤ) :=
  fun j ↦ ((ComplexShape.embeddingUp'Add (1 : ℤ) D.negativeCrossingCount).restrictionFunctor
    (ModuleCat.{u} R)).obj ((D.toPDCode.resolutionCube hD R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).cubeComplex)

/-- The definition of the normalized complex as an index translation of the bracket. -/
theorem khovanovComplex_apply (j : ℤ) :
    D.khovanovComplex hD R j =
      ((ComplexShape.embeddingUp'Add (1 : ℤ) D.negativeCrossingCount).restrictionFunctor
        (ModuleCat.{u} R)).obj ((D.toPDCode.resolutionCube hD R
          (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).cubeComplex) := (rfl)

variable (j : ℤ)

/-- The normalized term in degree `i` is the signed cube term of height `i + n₋`. -/
theorem khovanovComplex_X (i : ℤ) :
    (D.khovanovComplex hD R j).X i =
      (D.toPDCode.resolutionCube hD R
        (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).cubeComplex.X
          (i + D.negativeCrossingCount) := (rfl)

/-- Normalization translates the differential without changing its cube signs. -/
theorem khovanovComplex_d (i l : ℤ) :
    (D.khovanovComplex hD R j).d i l =
      eqToHom (D.khovanovComplex_X hD R j i) ≫
        (D.toPDCode.resolutionCube hD R
          (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).cubeComplex.d
            (i + D.negativeCrossingCount) (l + D.negativeCrossingCount) ≫
              eqToHom (D.khovanovComplex_X hD R j l).symm := by
  exact restriction_d_eq (c := ComplexShape.up' (1 : ℤ))
    (c' := ComplexShape.up' (1 : ℤ)) _
    (ComplexShape.embeddingUp'Add (1 : ℤ) (D.negativeCrossingCount : ℤ)) rfl rfl

/-- Comparison with the native cochain shift of the quantum-shifted bracket. The comparison
multiplies cochain degree `i` by `(-1)^(i * n₋)`. -/
def khovanovComplexShiftIso :
    D.khovanovComplex hD R j ≅
      (D.toPDCode.khovanovBracket hD R
        (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount))⟦
          (D.negativeCrossingCount : ℤ)⟧ :=
  (CochainComplex.restrictionAddIsoShift (ModuleCat.{u} R)
    D.negativeCrossingCount).app _ ≪≫
      (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ)
        (D.negativeCrossingCount : ℤ)).mapIso
          (eqToIso (D.toPDCode.khovanovBracket_apply hD R _).symm)

/-- The forward shift comparison carries the degreewise normalization sign. -/
@[simp]
theorem khovanovComplexShiftIso_hom_f (i : ℤ) :
    (D.khovanovComplexShiftIso hD R j).hom.f i =
      (i * D.negativeCrossingCount).negOnePow •
        eqToHom (by
          rw [CochainComplex.shiftFunctor_obj_X', PDCode.khovanovBracket_apply,
            khovanovComplex_X]) := by
  -- The restriction functor uses `up' 1`; `erw` identifies it with the cochain shape `up ℤ`.
  dsimp only [khovanovComplexShiftIso, Iso.trans, Iso.app]
  erw [HomologicalComplex.comp_f, CochainComplex.restrictionAddIsoShift_hom_app_f]
  rw [Units.smul_def]
  erw [Preadditive.zsmul_comp, Category.id_comp]
  simp only [Functor.mapIso_hom, eqToIso.hom]
  erw [CochainComplex.shiftFunctor_map_f', HomologicalComplex.eqToHom_f]
  -- Both equality transports have the same endpoints; proof irrelevance identifies them.
  rfl

/-- The inverse shift comparison carries the same degreewise sign. -/
@[simp]
theorem khovanovComplexShiftIso_inv_f (i : ℤ) :
    (D.khovanovComplexShiftIso hD R j).inv.f i =
      (i * D.negativeCrossingCount).negOnePow •
        eqToHom (by
          rw [CochainComplex.shiftFunctor_obj_X', PDCode.khovanovBracket_apply,
            khovanovComplex_X]) := by
  rw [← cancel_mono ((D.khovanovComplexShiftIso hD R j).hom.f i)]
  calc
    _ = 𝟙 _ := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
        congrArg (fun f ↦ f.f i) (D.khovanovComplexShiftIso hD R j).inv_hom_id
    _ = _ := by
      rw [khovanovComplexShiftIso_hom_f]
      simp [Units.smul_def, smul_smul, ← Units.val_mul]

/-- The normalized cube vertex is precisely the quantum piece shifted by the state's
`stateQuantumShift`. -/
theorem resolutionCube_obj_normalized (S : Finset (Fin n)) :
    (D.toPDCode.resolutionCube hD R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj S =
        ModuleCat.of R ((Khovanov.circleQuantumGrading R
          (D.toPDCode.ResolvedCircle (PDCode.cubeState S))).piece
            (j - D.stateQuantumShift (PDCode.cubeState S))) := by
  rw [PDCode.resolutionCube_obj, stateQuantumShift_cubeState]
  have hq : j - D.positiveCrossingCount + 2 * D.negativeCrossingCount - (#S : ℤ) =
      j - ((#S : ℤ) + D.positiveCrossingCount - 2 * D.negativeCrossingCount) := by omega
  rw [hq]

/-- The inclusion of a state vertex into the normalized cochain term of height `i + n₋`. -/
def khovanovComplexι {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    (D.toPDCode.resolutionCube hD R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj S.1 ⟶
        (D.khovanovComplex hD R j).X i :=
  (D.toPDCode.resolutionCube hD R
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).cubeComplexι S ≫
      eqToHom (D.khovanovComplex_X hD R j i).symm

/-- The projection of a normalized cochain term onto a state vertex. -/
def khovanovComplexπ {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    (D.khovanovComplex hD R j).X i ⟶
      (D.toPDCode.resolutionCube hD R
        (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj S.1 :=
  eqToHom (D.khovanovComplex_X hD R j i) ≫
    (D.toPDCode.resolutionCube hD R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).cubeComplexπ S

/-- Inclusion followed by projection is the identity on a state summand. -/
@[reassoc (attr := simp)]
theorem khovanovComplexι_π_self {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    D.khovanovComplexι hD R j S ≫ D.khovanovComplexπ hD R j S = 𝟙 _ := by
  simp [khovanovComplexι, khovanovComplexπ]

/-- Inclusion followed by projection onto a distinct state vanishes. -/
@[reassoc (attr := simp)]
theorem khovanovComplexι_π_of_ne {i : ℤ}
    {S T : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}} (h : S ≠ T) :
    D.khovanovComplexι hD R j S ≫ D.khovanovComplexπ hD R j T = 0 := by
  simp [khovanovComplexι, khovanovComplexπ, Functor.cubeComplexι_π_of_ne _ h]

/-- Morphisms out of a normalized term are determined by their state restrictions. -/
@[ext]
theorem khovanovComplex_hom_ext {i : ℤ} {A : ModuleCat.{u} R}
    {f g : (D.khovanovComplex hD R j).X i ⟶ A}
    (h : ∀ S, D.khovanovComplexι hD R j S ≫ f = D.khovanovComplexι hD R j S ≫ g) : f = g := by
  rw [← cancel_epi (eqToHom (D.khovanovComplex_X hD R j i).symm)]
  apply Functor.cubeComplex_hom_ext
  simpa only [Category.assoc, khovanovComplexι] using h

/-- Morphisms into a normalized term are determined by their state projections. -/
@[ext 1001]
theorem khovanovComplex_hom_ext' {i : ℤ} {A : ModuleCat.{u} R}
    {f g : A ⟶ (D.khovanovComplex hD R j).X i}
    (h : ∀ S, f ≫ D.khovanovComplexπ hD R j S = g ≫ D.khovanovComplexπ hD R j S) : f = g := by
  rw [← cancel_mono (eqToHom (D.khovanovComplex_X hD R j i))]
  apply Functor.cubeComplex_hom_ext'
  simpa only [Category.assoc, khovanovComplexπ] using h

/-- Each normalized term is the finite biproduct of the quantum pieces of its states.
The index equation `|S| = i + n₋` is equivalent to `stateCochainDegree(S) = i`. -/
def khovanovComplexXIso (i : ℤ) :
    (D.khovanovComplex hD R j).X i ≅
      ⨁ fun S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount} ↦
        ModuleCat.of R ((Khovanov.circleQuantumGrading R
          (D.toPDCode.ResolvedCircle (PDCode.cubeState S.1))).piece
            (j - D.stateQuantumShift (PDCode.cubeState S.1))) :=
  eqToIso ((D.khovanovComplex_X hD R j i).trans
    ((D.toPDCode.resolutionCube hD R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).cubeComplex_X _)) ≪≫
    biproduct.mapIso (fun S : {S : Finset (Fin n) //
      (#S : ℤ) = i + D.negativeCrossingCount} ↦
        eqToIso (D.resolutionCube_obj_normalized hD R j S.1))

/-- On a state summand, the term comparison is the quantum-piece identification. -/
@[reassoc (attr := simp)]
theorem khovanovComplexι_comp_khovanovComplexXIso_hom {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    D.khovanovComplexι hD R j S ≫ (D.khovanovComplexXIso hD R j i).hom =
      eqToHom (D.resolutionCube_obj_normalized hD R j S.1) ≫
        biproduct.ι (fun T : {T : Finset (Fin n) // (#T : ℤ) = i + D.negativeCrossingCount} ↦
          ModuleCat.of R ((Khovanov.circleQuantumGrading R
            (D.toPDCode.ResolvedCircle (PDCode.cubeState T.1))).piece
              (j - D.stateQuantumShift (PDCode.cubeState T.1)))) S := by
  dsimp only [khovanovComplexXIso, Iso.trans]
  simp [khovanovComplexι, Category.assoc]

/-- The inverse term comparison includes a quantum piece as its state summand. -/
@[reassoc (attr := simp)]
theorem ι_comp_khovanovComplexXIso_inv {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    biproduct.ι (fun T : {T : Finset (Fin n) // (#T : ℤ) = i + D.negativeCrossingCount} ↦
      ModuleCat.of R ((Khovanov.circleQuantumGrading R
        (D.toPDCode.ResolvedCircle (PDCode.cubeState T.1))).piece
          (j - D.stateQuantumShift (PDCode.cubeState T.1)))) S ≫
            (D.khovanovComplexXIso hD R j i).inv =
      eqToHom (D.resolutionCube_obj_normalized hD R j S.1).symm ≫
        D.khovanovComplexι hD R j S := by
  rw [← cancel_mono (D.khovanovComplexXIso hD R j i).hom]
  simp

/-- Projecting the term comparison onto a quantum piece gives the state projection. -/
@[reassoc (attr := simp)]
theorem khovanovComplexXIso_hom_comp_π {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    (D.khovanovComplexXIso hD R j i).hom ≫
      biproduct.π (fun T : {T : Finset (Fin n) // (#T : ℤ) = i + D.negativeCrossingCount} ↦
        ModuleCat.of R ((Khovanov.circleQuantumGrading R
          (D.toPDCode.ResolvedCircle (PDCode.cubeState T.1))).piece
            (j - D.stateQuantumShift (PDCode.cubeState T.1)))) S =
      D.khovanovComplexπ hD R j S ≫
        eqToHom (D.resolutionCube_obj_normalized hD R j S.1) := by
  dsimp only [khovanovComplexXIso, Iso.trans]
  rw [eqToIso.hom, ← eqToHom_trans (D.khovanovComplex_X hD R j i)
    ((D.toPDCode.resolutionCube hD R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).cubeComplex_X _)]
  simp only [khovanovComplexπ, Category.assoc, biproduct.mapIso_hom, biproduct.map_π,
    eqToIso.hom, Functor.eqToHom_comp_cubeComplexπ_assoc]

/-- The product coordinates of the term comparison are its normalized state projections. -/
@[simp]
theorem khovanovComplexXIso_biproductIsoPi_apply (i : ℤ)
    (x : (D.khovanovComplex hD R j).X i)
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    ((ModuleCat.biproductIsoPi _).hom ((D.khovanovComplexXIso hD R j i).hom x)) S =
      (eqToHom (D.resolutionCube_obj_normalized hD R j S.1)).hom
        ((D.khovanovComplexπ hD R j S).hom x) := by
  have h := congrArg (fun f ↦ (D.khovanovComplexXIso hD R j i).hom ≫
    (ModuleCat.biproductIsoPi _).hom ≫ f)
    (ModuleCat.biproductIsoPi_inv_comp_π _ S)
  simp only [Iso.hom_inv_id_assoc, khovanovComplexXIso_hom_comp_π] at h
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.proj_apply] using (congrArg (fun f ↦ f.hom x) h).symm

/-- The inverse term comparison projects a quantum piece onto its state vertex. -/
@[reassoc (attr := simp)]
theorem khovanovComplexXIso_inv_comp_π {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    (D.khovanovComplexXIso hD R j i).inv ≫ D.khovanovComplexπ hD R j S =
      biproduct.π (fun T : {T : Finset (Fin n) // (#T : ℤ) = i + D.negativeCrossingCount} ↦
        ModuleCat.of R ((Khovanov.circleQuantumGrading R
          (D.toPDCode.ResolvedCircle (PDCode.cubeState T.1))).piece
            (j - D.stateQuantumShift (PDCode.cubeState T.1)))) S ≫
        eqToHom (D.resolutionCube_obj_normalized hD R j S.1).symm := by
  rw [← cancel_epi (D.khovanovComplexXIso hD R j i).hom]
  simp

/-- The normalized differential on a state is the sum of the saddle edges with the original
cube signs. Each cube edge is identified with its actual saddle by
`PDCode.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι`. -/
@[reassoc]
theorem ι_khovanovComplex_d {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    D.khovanovComplexι hD R j S ≫ (D.khovanovComplex hD R j).d i (i + 1) =
      ∑ a : (S.1ᶜ : Finset (Fin n)), ((-1 : ℤ) ^ #{b ∈ S.1 | b < a.1}) •
        (D.toPDCode.resolutionCube hD R
          (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).map
            (homOfLE (S.1.subset_insert a.1)) ≫
          D.khovanovComplexι hD R j ⟨insert a.1 S.1, by
            rw [card_insert_of_notMem (mem_compl.1 a.2), Nat.cast_succ, S.2]
            omega⟩ := by
  have h := (D.toPDCode.resolutionCube hD R
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).ι_cubeComplex_d S
  let F := D.toPDCode.resolutionCube hD R
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
  let e : (i + D.negativeCrossingCount : ℤ) + 1 = i + 1 + D.negativeCrossingCount := by omega
  have hh := congrArg (fun f ↦ f ≫ (F.cubeComplex.XIsoOfEq e).hom ≫
    eqToHom (D.khovanovComplex_X hD R j (i + 1)).symm) h
  simpa only [F, khovanovComplexι, khovanovComplex_d, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Preadditive.sum_comp, Preadditive.zsmul_comp,
    d_comp_XIsoOfEq_hom_assoc, Functor.cubeComplexι_comp_XIsoOfEq_hom_assoc] using hh

/-- No cochain terms occur below `-n₋`. -/
instance khovanovComplex_isStrictlyGE :
    (D.khovanovComplex hD R j).IsStrictlyGE (-(D.negativeCrossingCount : ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [khovanovComplex_X]
  exact (D.toPDCode.resolutionCube hD R
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).isZero_cubeComplex_X_of_neg
      (r := i + D.negativeCrossingCount) (by omega)

/-- No cochain terms occur above `n₊`. -/
instance khovanovComplex_isStrictlyLE :
    (D.khovanovComplex hD R j).IsStrictlyLE D.positiveCrossingCount := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have hn := D.positiveCrossingCount_add_negativeCrossingCount
  rw [khovanovComplex_X]
  exact (D.toPDCode.resolutionCube hD R
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).isZero_cubeComplex_X_of_card_lt
      (by simp only [Fintype.card_fin]; omega)

end TauCeti.OrientedPDCode
