/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
/-!
# Coefficient change for local homology

Coefficient-change functoriality and exact-functor comparison isomorphisms for `localHomology`
(requiring `[Abelian]` coefficients, unlike `SimplicialSet.Homology.Coefficients`,
`Relative.Coefficients`, and `MapCoefficients`). Feeds scalar extension and coefficient transport in
`Orientation.Module.{Basic,FundamentalClass}` (notably `ULift (ZMod 2) →+* R` when `(2 : R) = 0`),
adapting `Functor.singularHomologyFunctorObjCompIso`, `SSet.homologyExtendScalarsIso`, `IsSplitMono`
(`Relative.Basic`), and `map_localHomologyTransport_comp_of_restriction` (`LocalHomology.System`):
* `localHomologyMapOfCoefficients` / `localHomologyIsoOfCoefficientsIso`: maps/isos for `φ : R ⟶ R'`
  and `e : R ≅ R'`, natural in restriction, maps, transport, and `singularHomologyToLocalHomology`.
* `localHomologyObjIso`: `F (Hₖ(M, M ∖ S; R)) ≅ Hₖ(M, M ∖ S; F R)` for exact coproduct-preserving F.
* `localHomologyExtendScalarsIso`: `S ⊗[R] Hₖ(M, M ∖ A; R) ≅ Hₖ(M, M ∖ A; S)` for exact `f : R→+*S`
  via `(Functor.Monoidal.εIso (ModuleCat.extendScalars f)).symm` (Hatcher, §3.A/3.3).
-/
public noncomputable section
open CategoryTheory Limits
open CategoryTheory.ConcreteCategory (congr_hom)
open TopCat (toSSet)
open TopPair (ofSubset toSSetPair)
open scoped ChangeOfRings Simplicial
universe w v v' u u'
namespace TauCeti
section Coefficients
variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
section Hom
variable {R R' R'' : A} (φ : R ⟶ R')
section SingleSpace
variable {M : Type w} [TopologicalSpace M]
/-- A morphism of coefficient objects `φ : R ⟶ R'` induces a morphism on local homology. -/
def localHomologyMapOfCoefficients (S : Set M) (k : ℕ) :
    localHomology R S k ⟶ localHomology R' S k :=
  (SSetPair.homologyNatTransOfCoefficients φ k).app
    (toSSetPair.obj (ofSubset (Sᶜ : Set (TopCat.of M))))
lemma localHomologyMapOfCoefficients_def (S : Set M) (k : ℕ) :
    localHomologyMapOfCoefficients φ S k = (SSetPair.homologyNatTransOfCoefficients φ k).app
      (toSSetPair.obj (ofSubset (Sᶜ : Set (TopCat.of M)))) := (rfl)
@[simp] lemma localHomologyMapOfCoefficients_id (R : A) (S : Set M) (k : ℕ) :
    localHomologyMapOfCoefficients (𝟙 R) S k = 𝟙 _ := by simp [localHomologyMapOfCoefficients]
@[simp] lemma localHomologyMapOfCoefficients_comp (ψ : R' ⟶ R'') (S : Set M) (k : ℕ) :
    localHomologyMapOfCoefficients (φ ≫ ψ) S k =
      localHomologyMapOfCoefficients φ S k ≫ localHomologyMapOfCoefficients ψ S k := by
  simp [localHomologyMapOfCoefficients]
@[reassoc] lemma localHomologyRestriction_comp_localHomologyMapOfCoefficients {S T : Set M}
    (h : S ⊆ T) (k : ℕ) : localHomologyRestriction R h k ≫ localHomologyMapOfCoefficients φ S k =
      localHomologyMapOfCoefficients φ T k ≫ localHomologyRestriction R' h k := by
  rw [localHomologyRestriction_def, localHomologyRestriction_def]
  exact (SSetPair.homologyNatTransOfCoefficients φ k).naturality _
@[reassoc] lemma homologyNatTransOfCoefficients_app_comp_singularHomologyπ (S : Set M) (k : ℕ) :
    (SSet.homologyNatTransOfCoefficients φ k).app (toSSet.obj (TopCat.of M)) ≫
        (ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ R' k =
      (ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ R k ≫
        localHomologyMapOfCoefficients φ S k := by
  rw [SSet.homologyNatTransOfCoefficients_app, localHomologyMapOfCoefficients_def,
    SSetPair.homologyNatTransOfCoefficients_app]
  exact SSetPair.homologyπ_coefficient_naturality
    (toSSetPair.obj (ofSubset (Sᶜ : Set (TopCat.of M)))) φ k
end SingleSpace
@[reassoc] lemma localHomologyMap_comp_localHomologyMapOfCoefficients {M N : Type w}
    [TopologicalSpace M] [TopologicalSpace N] (j : C(M, N)) {S : Set M} {T : Set N}
    (h : j ⁻¹' T ⊆ S) (k : ℕ) : localHomologyMap R j h k ≫ localHomologyMapOfCoefficients φ T k =
      localHomologyMapOfCoefficients φ S k ≫ localHomologyMap R' j h k := by
  rw [localHomologyMap_def, localHomologyMap_def]
  exact (SSetPair.homologyNatTransOfCoefficients φ k).naturality _
@[reassoc] lemma localHomologyTransport_comp_localHomologyMapOfCoefficients {M E : Type w}
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (k : ℕ) {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomologyTransport R M E k f ≫ localHomologyMapOfCoefficients φ {y.as} k =
      localHomologyMapOfCoefficients φ {x.as} k ≫ localHomologyTransport R' M E k f :=
  map_localHomologyTransport_comp_of_restriction R (𝟭 A) R' k
    (localHomologyMapOfCoefficients φ · k)
    (fun h ↦ localHomologyRestriction_comp_localHomologyMapOfCoefficients φ h k) f
end Hom
lemma singularHomologyToLocalHomology_homologyNatTransOfCoefficients_app {M : Type w}
    [TopologicalSpace M] {Λ : Type u} [Ring Λ] {N N' : ModuleCat.{w} Λ} (φ : N ⟶ N') (x : M)
    (k : ℕ) (μ : ↑((toSSet.obj (TopCat.of M)).homology N k)) :
    singularHomologyToLocalHomology N' x k
        ((SSet.homologyNatTransOfCoefficients φ k).app (toSSet.obj (TopCat.of M)) μ) =
      localHomologyMapOfCoefficients φ {x} k (singularHomologyToLocalHomology N x k μ) := by
  refine (singularHomologyToLocalHomology_eq_singularHomologyπ N' x _).trans ?_
  refine (((comp_apply _ _ μ).symm.trans (congr_hom
    (homologyNatTransOfCoefficients_app_comp_singularHomologyπ φ {x} k) μ)).trans
      (comp_apply _ _ μ)).trans ?_
  exact congrArg (localHomologyMapOfCoefficients φ {x} k)
    (singularHomologyToLocalHomology_eq_singularHomologyπ N x μ).symm
section Iso
variable {R R' R'' : A} (e : R ≅ R')
section SingleSpace
variable {M : Type w} [TopologicalSpace M]
/-- A coefficient isomorphism `e : R ≅ R'` induces an isomorphism on local homology. -/
def localHomologyIsoOfCoefficientsIso (S : Set M) (k : ℕ) :
    localHomology R S k ≅ localHomology R' S k :=
  (SSetPair.homologyNatIsoOfCoefficientsIso e k).app
    (toSSetPair.obj (ofSubset (Sᶜ : Set (TopCat.of M))))
@[simp] lemma localHomologyIsoOfCoefficientsIso_hom (S : Set M) (k : ℕ) :
    (localHomologyIsoOfCoefficientsIso e S k).hom = localHomologyMapOfCoefficients e.hom S k := by
  simp [localHomologyIsoOfCoefficientsIso, localHomologyMapOfCoefficients]
@[simp] lemma localHomologyIsoOfCoefficientsIso_inv (S : Set M) (k : ℕ) :
    (localHomologyIsoOfCoefficientsIso e S k).inv = localHomologyMapOfCoefficients e.inv S k := by
  simp [localHomologyIsoOfCoefficientsIso, localHomologyMapOfCoefficients]
@[simp] lemma localHomologyIsoOfCoefficientsIso_refl (R : A) (S : Set M) (k : ℕ) :
    localHomologyIsoOfCoefficientsIso (Iso.refl R) S k = Iso.refl _ := Iso.ext <| by simp
@[simp] lemma localHomologyIsoOfCoefficientsIso_symm (S : Set M) (k : ℕ) :
    localHomologyIsoOfCoefficientsIso e.symm S k = (localHomologyIsoOfCoefficientsIso e S k).symm :=
  Iso.ext <| by simp
@[simp] lemma localHomologyIsoOfCoefficientsIso_trans (e₁ : R ≅ R') (e₂ : R' ≅ R'') (S : Set M)
    (k : ℕ) : localHomologyIsoOfCoefficientsIso (e₁ ≪≫ e₂) S k =
      localHomologyIsoOfCoefficientsIso e₁ S k ≪≫ localHomologyIsoOfCoefficientsIso e₂ S k :=
  Iso.ext <| by simp
@[reassoc] lemma localHomologyRestriction_comp_localHomologyIsoOfCoefficientsIso_hom {S T : Set M}
    (h : S ⊆ T) (k : ℕ) : localHomologyRestriction R h k ≫
      (localHomologyIsoOfCoefficientsIso e S k).hom =
      (localHomologyIsoOfCoefficientsIso e T k).hom ≫ localHomologyRestriction R' h k := by
  simpa using localHomologyRestriction_comp_localHomologyMapOfCoefficients e.hom h k
end SingleSpace
@[reassoc] lemma localHomologyMap_comp_localHomologyIsoOfCoefficientsIso_hom {M N : Type w}
    [TopologicalSpace M] [TopologicalSpace N] (j : C(M, N)) {S : Set M} {T : Set N}
    (h : j ⁻¹' T ⊆ S) (k : ℕ) :
    localHomologyMap R j h k ≫ (localHomologyIsoOfCoefficientsIso e T k).hom =
      (localHomologyIsoOfCoefficientsIso e S k).hom ≫ localHomologyMap R' j h k := by
  simpa using localHomologyMap_comp_localHomologyMapOfCoefficients e.hom j h k
@[reassoc] lemma localHomologyTransport_comp_localHomologyIsoOfCoefficientsIso_hom {M E : Type w}
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (k : ℕ) {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomologyTransport R M E k f ≫ (localHomologyIsoOfCoefficientsIso e {y.as} k).hom =
      (localHomologyIsoOfCoefficientsIso e {x.as} k).hom ≫ localHomologyTransport R' M E k f := by
  simpa using localHomologyTransport_comp_localHomologyMapOfCoefficients e.hom k f
end Iso
lemma singularHomologyToLocalHomology_homologyIsoOfCoefficientsIso_hom_apply {M : Type w}
    [TopologicalSpace M] {Λ : Type u} [Ring Λ] {N N' : ModuleCat.{w} Λ} (e : N ≅ N') (x : M)
    (k : ℕ) (μ : ↑((toSSet.obj (TopCat.of M)).homology N k)) :
    singularHomologyToLocalHomology N' x k
      ((SSet.homologyIsoOfCoefficientsIso e (toSSet.obj (TopCat.of M)) k).hom μ) =
      (localHomologyIsoOfCoefficientsIso e {x} k).hom
        (singularHomologyToLocalHomology N x k μ) := by
  rw [SSet.homologyIsoOfCoefficientsIso_hom, localHomologyIsoOfCoefficientsIso_hom]
  exact singularHomologyToLocalHomology_homologyNatTransOfCoefficients_app e.hom x k μ
section ObjIso
variable {B : Type u'} [Category.{v'} B] [HasCoproducts.{w} B] [Abelian B] (F : A ⥤ B) [F.Additive]
  [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] [F.PreservesHomology] (R : A)
section SingleSpace
variable {M : Type w} [TopologicalSpace M]
/-- **Local homology commutes with exact coproduct-preserving `F`**: `F Hₖ ≅ Hₖ F`. -/
def localHomologyObjIso (S : Set M) (k : ℕ) :
    F.obj (localHomology R S k) ≅ localHomology (F.obj R) S k :=
  TopPair.singularHomologyObjIso F R (ofSubset (Sᶜ : Set (TopCat.of M))) k
lemma localHomologyObjIso_hom (S : Set M) (k : ℕ) : (localHomologyObjIso F R S k).hom =
    (TopPair.singularHomologyObjIso F R (ofSubset (Sᶜ : Set (TopCat.of M))) k).hom := (rfl)
lemma localHomologyObjIso_inv (S : Set M) (k : ℕ) : (localHomologyObjIso F R S k).inv =
    (TopPair.singularHomologyObjIso F R (ofSubset (Sᶜ : Set (TopCat.of M))) k).inv := (rfl)
@[reassoc] lemma map_localHomologyRestriction_comp_localHomologyObjIso_hom {S T : Set M}
    (h : S ⊆ T) (k : ℕ) :
    F.map (localHomologyRestriction R h k) ≫ (localHomologyObjIso F R S k).hom =
      (localHomologyObjIso F R T k).hom ≫ localHomologyRestriction (F.obj R) h k := by
  rw [localHomologyRestriction_def, localHomologyRestriction_def]
  exact TopPair.map_singularHomologyMap_comp_singularHomologyObjIso_hom F R _ k
@[reassoc] lemma map_singularHomologyπ_comp_localHomologyObjIso_hom (S : Set M) (k : ℕ) :
    F.map ((ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ R k) ≫
        (localHomologyObjIso F R S k).hom =
      (SSet.homologyObjIso F R (toSSet.obj (TopCat.of M)) k).hom ≫
        (ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ (F.obj R) k :=
  TopPair.map_singularHomologyπ_comp_singularHomologyObjIso_hom F R _ k
end SingleSpace
@[reassoc] lemma map_localHomologyMap_comp_localHomologyObjIso_hom {M N : Type w}
    [TopologicalSpace M] [TopologicalSpace N] (j : C(M, N)) {S : Set M} {T : Set N}
    (h : j ⁻¹' T ⊆ S) (k : ℕ) :
    F.map (localHomologyMap R j h k) ≫ (localHomologyObjIso F R T k).hom =
      (localHomologyObjIso F R S k).hom ≫ localHomologyMap (F.obj R) j h k := by
  rw [localHomologyMap_def, localHomologyMap_def]
  exact TopPair.map_singularHomologyMap_comp_singularHomologyObjIso_hom F R _ k
/-- **Transport of local homology commutes with an exact coproduct-preserving functor `F`**. -/
@[reassoc] lemma map_localHomologyTransport_comp_localHomologyObjIso_hom {M E : Type w}
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (k : ℕ) {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    F.map (localHomologyTransport R M E k f) ≫ (localHomologyObjIso F R {y.as} k).hom =
      (localHomologyObjIso F R {x.as} k).hom ≫ localHomologyTransport (F.obj R) M E k f :=
  map_localHomologyTransport_comp_of_restriction R F (F.obj R) k
    (fun S ↦ (localHomologyObjIso F R S k).hom)
    (fun h ↦ map_localHomologyRestriction_comp_localHomologyObjIso_hom F R h k) f
end ObjIso
end Coefficients
section ExtendScalars
open ModuleCat (extendScalars of)
open ModuleCat.ExtendScalars (apply_tmul_of_comm)
open CategoryTheory.Functor.Monoidal (εIso)
variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
  [PreservesFiniteLimits (extendScalars.{w} f)]
section SingleSpace
variable {M : Type w} [TopologicalSpace M]
lemma singularHomologyToLocalHomology_homologyObjIso_hom_tmul (N : ModuleCat.{w} R) (x : M) (k : ℕ)
    (s : S) (μ : ↑((toSSet.obj (TopCat.of M)).homology N k)) :
    singularHomologyToLocalHomology ((extendScalars.{w} f).obj N) x k
        ((SSet.homologyObjIso (extendScalars.{w} f) N (toSSet.obj (TopCat.of M)) k).hom
          (s ⊗ₜ[R, f] μ)) = (localHomologyObjIso (extendScalars.{w} f) N {x} k).hom
        (s ⊗ₜ[R, f] singularHomologyToLocalHomology N x k μ) := by
  simp only [singularHomologyToLocalHomology_eq_singularHomologyπ]
  exact apply_tmul_of_comm f (map_singularHomologyπ_comp_localHomologyObjIso_hom _ N {x} k) s μ
/-- **Extension of scalars commutes with local homology** along exact `f : R →+* S`. -/
def localHomologyExtendScalarsIso (A : Set M) (k : ℕ) :
    (extendScalars.{w} f).obj (localHomology (of R R) A k) ≅ localHomology (of S S) A k :=
  localHomologyObjIso (extendScalars.{w} f) (of R R) A k ≪≫
    localHomologyIsoOfCoefficientsIso (εIso (extendScalars.{w} f)).symm A k
lemma localHomologyExtendScalarsIso_hom (A : Set M) (k : ℕ) :
    (localHomologyExtendScalarsIso f A k).hom =
      (localHomologyObjIso (extendScalars.{w} f) (of R R) A k).hom ≫
        (localHomologyIsoOfCoefficientsIso (εIso _).symm A k).hom := (rfl)
lemma localHomologyExtendScalarsIso_inv (A : Set M) (k : ℕ) :
    (localHomologyExtendScalarsIso f A k).inv =
      (localHomologyIsoOfCoefficientsIso (εIso _).symm A k).inv ≫
        (localHomologyObjIso (extendScalars.{w} f) (of R R) A k).inv := (rfl)
@[reassoc] lemma map_singularHomologyπ_comp_localHomologyExtendScalarsIso_hom (A : Set M) (k : ℕ) :
    (extendScalars.{w} f).map ((ofSubset (Aᶜ : Set (TopCat.of M))).singularHomologyπ (of R R) k) ≫
        (localHomologyExtendScalarsIso f A k).hom =
      (f.singularHomologyExtendScalarsIso M k).hom ≫
        (ofSubset (Aᶜ : Set (TopCat.of M))).singularHomologyπ (of S S) k := by
  let ε : (extendScalars.{w} f).obj (of R R) ≅ of S S := (εIso _).symm
  rw [localHomologyExtendScalarsIso_hom, f.singularHomologyExtendScalarsIso_hom]
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (map_singularHomologyπ_comp_localHomologyObjIso_hom _ (of R R) A k))).trans ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)).trans (Category.assoc _ _ _).symm
  rw [localHomologyIsoOfCoefficientsIso_hom, SSet.homologyIsoOfCoefficientsIso_hom]
  exact (homologyNatTransOfCoefficients_app_comp_singularHomologyπ ε.hom A k).symm
lemma singularHomologyToLocalHomology_singularHomologyExtendScalarsIso_hom_tmul (x : M) (k : ℕ)
    (s : S) (μ : ↑((toSSet.obj (TopCat.of M)).homology (of R R) k)) :
    singularHomologyToLocalHomology (of S S) x k
        ((f.singularHomologyExtendScalarsIso M k).hom (s ⊗ₜ[R, f] μ)) =
      (localHomologyExtendScalarsIso f {x} k).hom
        (s ⊗ₜ[R, f] singularHomologyToLocalHomology (of R R) x k μ) := by
  simp only [singularHomologyToLocalHomology_eq_singularHomologyπ]
  exact apply_tmul_of_comm f
    (map_singularHomologyπ_comp_localHomologyExtendScalarsIso_hom f {x} k) s μ
@[reassoc] lemma map_localHomologyRestriction_comp_localHomologyExtendScalarsIso_hom {A B : Set M}
    (h : A ⊆ B) (k : ℕ) : (extendScalars.{w} f).map (localHomologyRestriction (of R R) h k) ≫
        (localHomologyExtendScalarsIso f A k).hom =
      (localHomologyExtendScalarsIso f B k).hom ≫ localHomologyRestriction (of S S) h k := by
  rw [localHomologyExtendScalarsIso_hom, localHomologyExtendScalarsIso_hom,
    map_localHomologyRestriction_comp_localHomologyObjIso_hom_assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (localHomologyRestriction_comp_localHomologyIsoOfCoefficientsIso_hom
    ((εIso _).symm : _ ≅ of S S) h k)
end SingleSpace
@[reassoc] lemma map_localHomologyMap_comp_localHomologyExtendScalarsIso_hom {M N : Type w}
    [TopologicalSpace M] [TopologicalSpace N] (j : C(M, N)) {A : Set M} {B : Set N}
    (h : j ⁻¹' B ⊆ A) (k : ℕ) : (extendScalars.{w} f).map (localHomologyMap (of R R) j h k) ≫
        (localHomologyExtendScalarsIso f B k).hom =
      (localHomologyExtendScalarsIso f A k).hom ≫ localHomologyMap (of S S) j h k := by
  rw [localHomologyExtendScalarsIso_hom, localHomologyExtendScalarsIso_hom,
    map_localHomologyMap_comp_localHomologyObjIso_hom_assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (localHomologyMap_comp_localHomologyIsoOfCoefficientsIso_hom
    ((εIso _).symm : _ ≅ of S S) j h k)
@[reassoc] lemma map_localHomologyTransport_comp_localHomologyExtendScalarsIso_hom {M E : Type w}
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (k : ℕ) {x y : FundamentalGroupoid M} (g : x ⟶ y) :
    (extendScalars.{w} f).map (localHomologyTransport (of R R) M E k g) ≫
        (localHomologyExtendScalarsIso f {y.as} k).hom =
      (localHomologyExtendScalarsIso f {x.as} k).hom ≫ localHomologyTransport (of S S) M E k g := by
  rw [localHomologyExtendScalarsIso_hom, localHomologyExtendScalarsIso_hom,
    map_localHomologyTransport_comp_localHomologyObjIso_hom_assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (localHomologyTransport_comp_localHomologyIsoOfCoefficientsIso_hom
    ((εIso _).symm : _ ≅ of S S) k g)
end ExtendScalars
end TauCeti
