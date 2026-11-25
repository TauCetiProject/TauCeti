/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import TauCeti.RingTheory.LocalProperties.Fiber.Splitting

/-!
# Splitting degree-zero cohomology off a nonnegative complex

Let `C` be a nonnegative cochain complex of finite projective modules and let `u : M[0] ⟶ C`
be a map from a finite projective module in degree zero. If `u` induces an isomorphism on
zeroth cohomology over every residue field, then `C` deformation retracts onto the sum of
`M[0]` and a complex of finite projective modules supported in strictly positive degrees. The
inclusion of `M[0]` is the given map `u`, and the complement inherits any upper degree bound
from `C`. The deformation retract is preserved by arbitrary scalar extension, since it is
given by cochain maps and a homotopy.

This is the constants-splitting argument for a finite projective model of the cohomology of the
structure sheaf. The certificate in degrees zero and one comes from
`LinearMap.exists_leftInverse_and_comp_add_comp_eq_id_of_residueField`.
For the cohomological application, see the Stacks Project, Tag
[0E62](https://stacks.math.columbia.edu/tag/0E62).
-/

public section

open CategoryTheory Limits HomologicalComplex
open CochainComplex.HomComplex

attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w w'

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Take the kernel of the idempotent cutting out the degree-zero summand and the
contractible summand in degrees zero and one. -/
private lemma exists_positive_complement
    (C : CochainComplex (ModuleCat.{v} R) ℤ) [C.IsStrictlyGE 0]
    [∀ i, Module.Finite R (C.X i)] [∀ i, Module.Projective R (C.X i)]
    {M : ModuleCat.{v} R} {u : (single _ (.up ℤ) 0).obj M ⟶ C}
    {ρ : C ⟶ (single _ (.up ℤ) 0).obj M} (hρ : u ≫ ρ = 𝟙 _)
    {n : C ⟶ C} (hn : Homotopy n 0)
    (hp₀ : (ρ ≫ u + n).f 0 = 𝟙 _) (hpp : (ρ ≫ u + n) ≫ (ρ ≫ u + n) = ρ ≫ u + n) :
    ∃ (Q : CochainComplex (ModuleCat.{v} R) ℤ)
      (e : HomotopyEquiv ((single _ (.up ℤ) 0).obj M ⊞ Q) C),
      Q.IsStrictlyGE 1 ∧ (∀ i, Module.Finite R (Q.X i) ∧ Module.Projective R (Q.X i)) ∧
      (∀ b, C.IsStrictlyLE b → Q.IsStrictlyLE b) ∧
      biprod.inl ≫ e.hom = u ∧ e.hom ≫ e.inv = 𝟙 _ := by
  let p := ρ ≫ u + n
  have hp₀' : p.f 0 = 𝟙 _ := hp₀
  have hup : u ≫ p = u := from_single_hom_ext (by simp [hp₀'])
  have hpρ : p ≫ ρ = ρ := to_single_hom_ext (by simp [hp₀'])
  let j := kernel.ι p
  have hpp' : p ≫ p = p := hpp
  let q := kernel.lift p (𝟙 C - p) (by simp [Preadditive.sub_comp, hpp'])
  have hqj : q ≫ j = 𝟙 C - p := kernel.lift_ι _ _ _
  have hjq : j ≫ q = 𝟙 _ := (cancel_mono j).mp (by simp [Category.assoc, hqj, j])
  have huq : u ≫ q = 0 := (cancel_mono j).mp (by simp [Category.assoc, hqj, hup])
  have hjρ : j ≫ ρ = 0 := by rw [← hpρ, ← Category.assoc, kernel.condition, zero_comp]
  have hde : biprod.desc u j ≫ biprod.lift ρ q = 𝟙 _ := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [hρ, huq, hjρ, hjq]
  let e : HomotopyEquiv ((single _ (.up ℤ) 0).obj M ⊞ kernel p) C := {
    hom := biprod.desc u j
    inv := biprod.lift ρ q
    homotopyHomInvId := Homotopy.ofEq hde
    homotopyInvHomId := Homotopy.equivSubZero.symm <|
      (Homotopy.ofEq (by rw [biprod.lift_desc, hqj]; dsimp [p]; abel)).trans
        (Homotopy.equivSubZero hn.symm) }
  have hterm (i : ℤ) (hz : j.f i = 0) : IsZero ((kernel p).X i) := by
    rw [IsZero.iff_id_eq_zero]
    simpa [hz] using (congrArg (fun a ↦ HomologicalComplex.Hom.f a i) hjq).symm
  refine ⟨kernel p, e, (isStrictlyGE_iff _ _).2 (fun i hi ↦ ?_), fun i ↦ ?_, ?_, by simp [e], hde⟩
  · have hj₀ : j.f i = 0 := by
      rcases eq_or_lt_of_le (show i ≤ 0 by omega) with rfl | hlt
      · have hz := congrArg (fun a : kernel p ⟶ C ↦ a.f 0) (kernel.condition p)
        rw [comp_f, zero_f_apply, hp₀', Category.comp_id] at hz
        exact hz
      exact (C.isZero_of_isStrictlyGE 0 i hlt).eq_of_tgt _ _
    exact hterm i hj₀
  · have hh : (q.f i).hom ∘ₗ (j.f i).hom = LinearMap.id :=
      congrArg (fun a : kernel p ⟶ kernel p ↦ (a.f i).hom) hjq
    exact ⟨Module.Finite.of_surjective _ (LinearMap.surjective_of_comp_eq_id _ _ hh),
      Module.Projective.of_split _ _ hh⟩
  · intro b hb
    exact (isStrictlyLE_iff _ b).2 fun i hi ↦
      hterm i ((C.isZero_of_isStrictlyLE b i hi).eq_of_tgt _ _)

/-- Splitting off a summand in the lowest cohomological degree. The residue-field condition is
written as exactness of `0 → M ⊗ κ(p) → C⁰ ⊗ κ(p) → C¹ ⊗ κ(p)`. The resulting homotopy
equivalence includes the specified copy of `M[0]`. -/
theorem exists_homotopyEquiv_biprod_single_of_residueField
    (C : CochainComplex (ModuleCat.{v} R) ℤ) [C.IsStrictlyGE 0]
    [∀ i, Module.Finite R (C.X i)] [∀ i, Module.Projective R (C.X i)]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Module.Projective R M]
    (u : (single _ (.up ℤ) 0).obj M ⟶ C)
    (hu : ∀ p : PrimeSpectrum R, Function.Injective
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor p.asIdeal.ResidueField))
    (he : ∀ p : PrimeSpectrum R, Function.Exact
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor p.asIdeal.ResidueField)
      ((C.d 0 1).hom.lTensor p.asIdeal.ResidueField)) :
    ∃ (Q : CochainComplex (ModuleCat.{v} R) ℤ)
      (e : HomotopyEquiv ((single _ (.up ℤ) 0).obj M ⊞ Q) C),
      Q.IsStrictlyGE 1 ∧ (∀ i, Module.Finite R (Q.X i) ∧ Module.Projective R (Q.X i)) ∧
      (∀ b, C.IsStrictlyLE b → Q.IsStrictlyLE b) ∧
      biprod.inl ≫ e.hom = u ∧ e.hom ≫ e.inv = 𝟙 _ := by
  let f := (singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0
  have hf : f ≫ C.d 0 1 = 0 := by simp [f, u.comm]
  obtain ⟨r, s, hr, hsplit⟩ :=
    f.hom.exists_leftInverse_and_comp_add_comp_eq_id_of_residueField (C.d 0 1).hom
      (by simpa using congrArg ModuleCat.Hom.hom hf) hu he
  let ρ : C ⟶ (single _ (.up ℤ) 0).obj M := mkHomToSingle (ModuleCat.ofHom r) (by
    intro i hi
    rw [ComplexShape.up_Rel] at hi
    exact (C.isZero_of_isStrictlyGE 0 i (by omega)).eq_of_src _ _)
  have hρ : u ≫ ρ = 𝟙 _ := by
    apply from_single_hom_ext
    have h : f ≫ ModuleCat.ofHom r = 𝟙 M := ModuleCat.hom_ext hr
    rw [comp_f, id_f]
    dsimp only [ρ]
    rw [mkHomToSingle_f]
    apply (cancel_mono (singleObjXSelf (.up ℤ) 0 M).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    apply (cancel_epi (singleObjXSelf (.up ℤ) 0 M).inv).mp
    simpa [f] using h
  -- The boundary of the cochain supported in bidegree `(1, 0)` contracts the first image.
  let h : Cochain C C (-1) := Cochain.single (ModuleCat.ofHom s) (-1)
  let n := Cocycle.homOf (Cocycle.mk (δ (-1) 0 h) 1 rfl (δ_δ _ _ _ _))
  have hn : Homotopy n 0 := (Cochain.equivHomotopy n 0).symm ⟨h, by simp [n]⟩
  have hn' (i : ℤ) : n.f i =
      (Cochain.single (ModuleCat.ofHom s ≫ C.d 0 1) 0 +
        Cochain.single (C.d 0 1 ≫ ModuleCat.ofHom s) 0).v i i (add_zero i) := by
    simp [n, h, Cochain.δ_single (K := C) (L := C) (p := 1) (q := 0) _ (-1) 0 rfl 0 1 rfl rfl]
  let p := ρ ≫ u + n
  have hp₀ : p.f 0 = 𝟙 _ := by
    have hh : ModuleCat.ofHom r ≫ f + C.d 0 1 ≫ ModuleCat.ofHom s = 𝟙 _ :=
      ModuleCat.hom_ext hsplit
    simpa [p, ρ, hn', f, Cochain.single_v_eq_zero _ _ _ _ _ (by decide : (0 : ℤ) ≠ 1)] using hh
  have hp₁ : p.f 1 = ModuleCat.ofHom s ≫ C.d 0 1 := by
    have hz : ρ.f 1 = 0 := (isZero_single_obj_X (.up ℤ) 0 M 1 (by decide)).eq_of_tgt _ _
    simp [p, hz, hn', Cochain.single_v_eq_zero _ _ _ _ _ (by decide : (1 : ℤ) ≠ 0)]
  have hp' (i : ℤ) (hi₀ : i ≠ 0) (hi₁ : i ≠ 1) : p.f i = 0 := by
    have hz : ρ.f i = 0 := (isZero_single_obj_X (.up ℤ) 0 M i hi₀).eq_of_tgt _ _
    simp [p, hz, hn', Cochain.single_v_eq_zero _ _ _ _ _ hi₀,
      Cochain.single_v_eq_zero _ _ _ _ _ hi₁]
  have hpp : p ≫ p = p := by
    refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
    by_cases hi₀ : i = 0
    · subst i
      simp [hp₀]
    by_cases hi₁ : i = 1
    · subst i
      have hcomm := p.comm 0 1
      rw [hp₀, Category.id_comp] at hcomm
      rw [comp_f, hp₁, Category.assoc, ← hp₁, ← hcomm, hp₁]
    simp [hp' _ hi₀ hi₁]
  exact exists_positive_complement C hρ hn hp₀ hpp

/-- A map from `M[0]` to a nonnegative complex of finite projective modules which induces an
isomorphism on degree-zero cohomology over every residue field still induces one after applying
any additive functor, in particular after arbitrary extension of scalars. -/
theorem isIso_homologyMap_zero_of_residueField
    {C : CochainComplex (ModuleCat.{v} R) ℤ} [C.IsStrictlyGE 0]
    [∀ i, Module.Finite R (C.X i)] [∀ i, Module.Projective R (C.X i)]
    {M : ModuleCat.{v} R} [Module.Finite R M] [Module.Projective R M]
    (u : (single _ (.up ℤ) 0).obj M ⟶ C)
    (hu : ∀ p : PrimeSpectrum R, Function.Injective
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor p.asIdeal.ResidueField))
    (he : ∀ p : PrimeSpectrum R, Function.Exact
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor p.asIdeal.ResidueField)
      ((C.d 0 1).hom.lTensor p.asIdeal.ResidueField))
    {D : Type w} [Category.{w'} D] [Abelian D] (F : ModuleCat.{v} R ⥤ D) [F.Additive] :
    IsIso (homologyMap ((F.mapHomologicalComplex (.up ℤ)).map u) 0) := by
  obtain ⟨Q, e, hQ, -, -, hinl, hret⟩ :=
    exists_homotopyEquiv_biprod_single_of_residueField C M u hu he
  let G := F.mapHomologicalComplex (.up ℤ)
  let H := G ⋙ homologyFunctor D (.up ℤ) 0
  let r := e.inv ≫ biprod.fst
  let t := e.inv ≫ biprod.snd
  let j := biprod.inr ≫ e.hom
  have hur : u ≫ r = 𝟙 _ := by
    rw [← hinl]
    dsimp only [r]
    rw [Category.assoc, ← Category.assoc e.hom e.inv, hret]
    simp
  have htotal : r ≫ u + t ≫ j = e.inv ≫ e.hom := by
    rw [← hinl]
    simp only [r, t, j, Category.assoc, ← Preadditive.comp_add]
    rw [← Category.assoc biprod.fst biprod.inl, ← Category.assoc biprod.snd biprod.inr,
      ← Preadditive.add_comp, biprod.total, Category.id_comp]
  have hz : IsZero (H.obj Q) := CochainComplex.isZero_of_isGE (G.obj Q) 1 0
  have hzero : H.map (t ≫ j) = 0 := by
    rw [H.map_comp, hz.eq_of_tgt (H.map t) 0, zero_comp]
  have hh : H.map (e.inv ≫ e.hom) = 𝟙 _ := by
    simpa [H, G] using (F.mapHomotopy e.homotopyInvHomId).homologyMap_eq 0
  have : IsIso (H.map u) := ⟨⟨H.map r, by rw [← H.map_comp, hur, H.map_id], by
    rw [← H.map_comp]
    rwa [← htotal, H.map_add, hzero, add_zero] at hh⟩⟩
  exact this

end CochainComplex
