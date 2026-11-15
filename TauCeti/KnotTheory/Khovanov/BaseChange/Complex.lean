/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import TauCeti.Algebra.Algebra.ULift
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.Cube.Functor
public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology
public import TauCeti.Algebra.Homology.UniversalCoefficient.Tor
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Resolution.BaseChange

/-!
# Coefficient change and universe lifting for the Khovanov complex

Extending scalars along a homomorphism of commutative rings `f : R →+* S` commutes with the
signed cube totalization (`TauCeti.PDCode.khovanovBracketBaseChangeIso`) and with the cochain and
quantum degree shifts defining the normalized Khovanov complex
(`TauCeti.OrientedPDCode.khovanovComplexBaseChangeIso`). Composing `HomologicalComplex`'s canonical
right-exact comparison with this chain isomorphism produces the canonical `S`-linear map
`TauCeti.OrientedPDCode.khovanovHomologyBaseChangeMap` from `S ⊗[R] Khⁱʲ(D; R)` to `Khⁱʲ(D; S)`,
which is an isomorphism whenever scalar extension preserves homology (for example along flat ring
maps).

For coefficients in a ring `R : Type v` (in particular `ℤ : Type 0`) and a target universe `u`,
the exact functor `ModuleCat.uliftRingFunctor.{u, v} R` combines `ModuleCat.uliftFunctor` with
scalar restriction along `ULift.ringEquiv : ULift.{u} R ≃+* R` and identifies the cube, bracket,
normalized Khovanov complex, and Khovanov cohomology over `R` with those over `ULift.{u} R`.

## Main definitions and results

* `TauCeti.PDCode.cubeComplexBaseChangeIso` and `TauCeti.PDCode.khovanovBracketBaseChangeIso`:
  `S ⊗[R] ⟦D⟧_R ≅ ⟦D⟧_S` in each quantum degree.
* `TauCeti.OrientedPDCode.khovanovComplexBaseChangeIso`: `S ⊗[R] C(D; R) ≅ C(D; S)` in each
  quantum degree, preserving each state summand.
* `TauCeti.OrientedPDCode.khovanovHomologyBaseChangeMap` and
  `TauCeti.OrientedPDCode.khovanovHomologyBaseChangeIsoOfPreservesHomology`: induced `S`-linear
  comparison `S ⊗[R] Khⁱʲ(D; R) ⟶ Khⁱʲ(D; S)`, invertible when `extendScalars f` is exact.
* `ModuleCat.uliftRingFunctor`, `TauCeti.PDCode.resolutionCubeULiftIso`,
  `TauCeti.OrientedPDCode.khovanovComplexULiftIso`, and
  `TauCeti.OrientedPDCode.khovanovHomologyULiftIso`: exact universe-lifting identifications from
  `R : Type v` to `ULift.{u} R : Type (max v u)`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.
-/

public section

noncomputable section

open CategoryTheory Limits Finset TensorProduct HomologicalComplex

/-- Lift `R`-modules from universe `v` to `ULift.{u} R`-modules in universe `max v u`, combining
`ModuleCat.uliftFunctor` with restriction of scalars along `ULift.ringEquiv : ULift.{u} R ≃+* R`. -/
abbrev ModuleCat.uliftRingFunctor.{u, v} (R : Type v) [Ring R] :
    ModuleCat.{v} R ⥤ ModuleCat.{max v u} (ULift.{u} R) :=
  ModuleCat.uliftFunctor.{u, v} R ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv.{v, u} : ULift.{u} R ≃+* R).toRingHom

namespace HomologicalComplex

/-- Construct a chain isomorphism `(F.mapHomologicalComplex c).obj K ≅ L` from an isomorphism
`(F.mapHomologicalComplex c).obj K' ≅ L'` together with termwise and differential identifications
for `K` and `L` at shifted indices `g i`. -/
def mapTranslatedIso {C D : Type*} [Category* C] [Preadditive C] [Category* D] [Preadditive D]
    {ι : Type*} {c : ComplexShape ι} (F : C ⥤ D) [F.Additive]
    {K K' : HomologicalComplex C c} {L L' : HomologicalComplex D c}
    (g : ι → ι)
    (hKX : ∀ i, K.X i = K'.X (g i))
    (hKd : ∀ i j, K.d i j = eqToHom (hKX i) ≫ K'.d (g i) (g j) ≫ eqToHom (hKX j).symm)
    (hLX : ∀ i, L.X i = L'.X (g i))
    (hLd : ∀ i j, L.d i j = eqToHom (hLX i) ≫ L'.d (g i) (g j) ≫ eqToHom (hLX j).symm)
    (e : (F.mapHomologicalComplex c).obj K' ≅ L') :
    (F.mapHomologicalComplex c).obj K ≅ L :=
  Hom.isoOfComponents
    (fun i ↦ F.mapIso (eqToIso (hKX i)) ≪≫
      (eval D c (g i)).mapIso e ≪≫ eqToIso (hLX i).symm)
    fun i j _ ↦ by
      have hcomm := e.hom.comm (g i) (g j)
      dsimp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, eval_map,
        Functor.mapHomologicalComplex_obj_d] at hcomm ⊢
      simp only [hKd i j, hLd i j, F.map_comp, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      rw [reassoc_of% hcomm, ← F.map_comp_assoc (eqToHom (hKX j).symm), eqToHom_trans,
        eqToHom_refl, F.map_id, Category.id_comp]

/-- Degreewise formula for `(mapTranslatedIso F g hKX hKd hLX hLd e).hom`. -/
@[simp]
lemma mapTranslatedIso_hom_f {C D : Type*} [Category* C] [Preadditive C] [Category* D]
    [Preadditive D] {ι : Type*} {c : ComplexShape ι} (F : C ⥤ D) [F.Additive]
    {K K' : HomologicalComplex C c} {L L' : HomologicalComplex D c}
    (g : ι → ι)
    (hKX : ∀ i, K.X i = K'.X (g i))
    (hKd : ∀ i j, K.d i j = eqToHom (hKX i) ≫ K'.d (g i) (g j) ≫ eqToHom (hKX j).symm)
    (hLX : ∀ i, L.X i = L'.X (g i))
    (hLd : ∀ i j, L.d i j = eqToHom (hLX i) ≫ L'.d (g i) (g j) ≫ eqToHom (hLX j).symm)
    (e : (F.mapHomologicalComplex c).obj K' ≅ L') (i : ι) :
    (mapTranslatedIso F g hKX hKd hLX hLd e).hom.f i =
      F.map (eqToHom (hKX i)) ≫ e.hom.f (g i) ≫ eqToHom (hLX i).symm :=
  (rfl)

end HomologicalComplex

namespace TauCeti.PDCode

private def cubeComplexMapIso {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C]
    {ι : Type*} [Fintype ι] [LinearOrder ι] {F G : Finset ι ⥤ C} (α : F ≅ G) :
    F.cubeComplex ≅ G.cubeComplex where
  hom := NatTrans.cubeComplexMap α.hom
  inv := NatTrans.cubeComplexMap α.inv
  hom_inv_id := by rw [← NatTrans.cubeComplexMap_comp, α.hom_inv_id, NatTrans.cubeComplexMap_id]
  inv_hom_id := by rw [← NatTrans.cubeComplexMap_comp, α.inv_hom_id, NatTrans.cubeComplexMap_id]

section BaseChange

universe u

variable {n : ℕ} (D : PDCode n) (hD : D.IsPlanar) {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (j : ℤ)

/-- **Coefficient change for the signed cube complex of resolutions.** Extending scalars along
`f : R →+* S` termwise in `(D.resolutionCube hD R j).cubeComplex` gives
`(D.resolutionCube hD S j).cubeComplex`. -/
def cubeComplexBaseChangeIso :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj
        (D.resolutionCube hD R j).cubeComplex ≅
      (D.resolutionCube hD S j).cubeComplex :=
  (D.resolutionCube hD R j).mapCubeComplexIso (ModuleCat.extendScalars f) ≪≫
    cubeComplexMapIso (D.resolutionCubeBaseChangeIso hD f j)

/-- On each cube vertex `T` of height `r`, `cubeComplexBaseChangeIso` acts via
`resolutionCubeBaseChangeIso`. -/
@[reassoc (attr := simp)]
theorem map_cubeComplexι_comp_cubeComplexBaseChangeIso_hom {r : ℤ}
    (T : {T : Finset (Fin n) // (#T : ℤ) = r}) :
    (ModuleCat.extendScalars f).map ((D.resolutionCube hD R j).cubeComplexι T) ≫
        (D.cubeComplexBaseChangeIso hD f j).hom.f r =
      (D.resolutionCubeBaseChangeIso hD f j).hom.app T.1 ≫
        (D.resolutionCube hD S j).cubeComplexι T := by
  dsimp only [cubeComplexBaseChangeIso, cubeComplexMapIso, Iso.trans_hom,
    HomologicalComplex.comp_f]
  rw [Functor.map_cubeComplexι_comp_mapCubeComplexIso_hom_assoc, NatTrans.ι_cubeComplexMap_f]

/-- Projecting onto vertex `T` after `cubeComplexBaseChangeIso` projects in `R` and applies
`resolutionCubeBaseChangeIso`. -/
@[reassoc (attr := simp)]
theorem cubeComplexBaseChangeIso_hom_π {r : ℤ}
    (T : {T : Finset (Fin n) // (#T : ℤ) = r}) :
    (D.cubeComplexBaseChangeIso hD f j).hom.f r ≫
        (D.resolutionCube hD S j).cubeComplexπ T =
      (ModuleCat.extendScalars f).map ((D.resolutionCube hD R j).cubeComplexπ T) ≫
        (D.resolutionCubeBaseChangeIso hD f j).hom.app T.1 := by
  dsimp only [cubeComplexBaseChangeIso, cubeComplexMapIso, Iso.trans_hom,
    HomologicalComplex.comp_f]
  rw [Category.assoc, NatTrans.cubeComplexMap_f_π, Functor.mapCubeComplexIso_hom_π_assoc]

/-- **Coefficient change for the unnormalized Khovanov bracket.** Extending scalars along
`f : R →+* S` termwise in the quantum-degree-`j` bracket complex over `R` gives the bracket
complex over `S`. -/
def khovanovBracketBaseChangeIso :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj (D.khovanovBracket hD R j) ≅
      D.khovanovBracket hD S j :=
  ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapIso
      (eqToIso (D.khovanovBracket_apply hD R j)) ≪≫
    D.cubeComplexBaseChangeIso hD f j ≪≫
      eqToIso (D.khovanovBracket_apply hD S j).symm

end BaseChange

section ULift

universe u v

variable {n : ℕ} (D : PDCode n) (hD : D.IsPlanar) (R : Type v) [CommRing R] (j : ℤ)

private def uliftRingDown {R : Type v} [Ring R] {M : ModuleCat.{v} R}
    (x : (ModuleCat.uliftRingFunctor.{u, v} R).obj M) : M :=
  ULift.down (x : ULift.{u} M)

private def uliftRingUp {R : Type v} [Ring R] {M : ModuleCat.{v} R} (m : M) :
    (ModuleCat.uliftRingFunctor.{u, v} R).obj M :=
  (ULift.up m : ULift.{u} M)

private lemma uliftRing_ext {R : Type v} [Ring R] {M : ModuleCat.{v} R}
    {x y : (ModuleCat.uliftRingFunctor.{u, v} R).obj M}
    (h : uliftRingDown x = uliftRingDown y) : x = y :=
  ULift.down_injective h

private def tensorToUliftRingAux {R : Type v} [CommRing R] (M : ModuleCat.{v} R) :
    ULift.{u} R ⊗[R] M →ₗ[R] ULift.{u} M :=
  TensorProduct.lift
    { toFun s :=
        { toFun m := ULift.up (s.down • m)
          map_add' a b := ULift.down_injective (smul_add s.down a b)
          map_smul' r m := ULift.down_injective (smul_comm s.down r m) }
      map_add' s t := LinearMap.ext fun m ↦ ULift.down_injective (add_smul s.down t.down m)
      map_smul' r s := LinearMap.ext fun m ↦ ULift.down_injective (mul_smul r s.down m) }

private def tensorToUliftRing {R : Type v} [CommRing R] (M : ModuleCat.{v} R)
    (z : ULift.{u} R ⊗[R] M) : (ModuleCat.uliftRingFunctor.{u, v} R).obj M :=
  (tensorToUliftRingAux M z : ULift.{u} M)

/-- `ULift.{u} R`-linear identification of `(uliftRingFunctor R).obj M` with `ULift.{u} R ⊗[R] M`
sending `ULift.up m` to `1 ⊗ₜ m`. -/
private def uliftRingTensorEquiv {R : Type v} [CommRing R] (M : ModuleCat.{v} R) :
    (ModuleCat.uliftRingFunctor.{u, v} R).obj M ≃ₗ[ULift.{u} R] ULift.{u} R ⊗[R] M where
  toFun x := (1 : ULift.{u} R) ⊗ₜ[R] uliftRingDown x
  map_add' x y := tmul_add 1 (uliftRingDown x) (uliftRingDown y)
  map_smul' s x := by
    have hs : s.down • (1 : ULift.{u} R) = s := ULift.down_injective (mul_one s.down)
    have hdown : uliftRingDown (s • x) = s.down • uliftRingDown x := rfl
    have hsmul : s • ((1 : ULift.{u} R) ⊗ₜ[R] uliftRingDown x) =
        (s * 1) ⊗ₜ[R] uliftRingDown x := rfl
    rw [RingHom.id_apply, hdown, ← smul_tmul, hs, hsmul, mul_one]
  invFun := tensorToUliftRing M
  left_inv x := uliftRing_ext (one_smul R (uliftRingDown x))
  right_inv z := by
    dsimp only
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
      have hs : s.down • (1 : ULift.{u} R) = s := ULift.down_injective (mul_one s.down)
      have hdown : uliftRingDown (tensorToUliftRing M (s ⊗ₜ[R] m)) = s.down • m := rfl
      rw [hdown, ← smul_tmul, hs]
    | add x y hx hy =>
      have hadd : uliftRingDown (tensorToUliftRing M (x + y)) =
          uliftRingDown (tensorToUliftRing M x) + uliftRingDown (tensorToUliftRing M y) :=
        congrArg ULift.down (map_add (tensorToUliftRingAux M) x y)
      rw [hadd, tmul_add, hx, hy]

/-- Vertex component of `resolutionCubeULiftIso` at `T`. -/
private def resolutionCubeULiftApp (T : Finset (Fin n)) :
    (D.resolutionCube hD R j ⋙ ModuleCat.uliftRingFunctor.{u, v} R).obj T ≅
      (D.resolutionCube hD (ULift.{u} R) j).obj T :=
  (uliftRingTensorEquiv ((D.resolutionCube hD R j).obj T) ≪≫ₗ
    (D.resolutionCubeVertexEquiv hD R j T).baseChange R (ULift.{u} R) ≪≫ₗ
      Khovanov.circlePieceBaseChange R (ULift.{u} R) (D.ResolvedCircle (cubeState T)) (j - #T) ≪≫ₗ
        (D.resolutionCubeVertexEquiv hD (ULift.{u} R) j T).symm).toModuleIso

private theorem resolutionCubeι_resolutionCubeULiftApp_up (T : Finset (Fin n))
    (x : (D.resolutionCube hD R j).obj T) :
    D.resolutionCubeι hD (ULift.{u} R) j T
        ((resolutionCubeULiftApp.{u, v} D hD R j T).hom (uliftRingUp x)) =
      Khovanov.circleBaseChange R (ULift.{u} R) _
        ((1 : ULift.{u} R) ⊗ₜ[R] D.resolutionCubeι hD R j T x) := by
  calc _ = D.resolutionCubeι hD (ULift.{u} R) j T
        ((D.resolutionCubeVertexEquiv hD (ULift.{u} R) j T).symm
          (Khovanov.circlePieceBaseChange R (ULift.{u} R) _ _
            ((1 : ULift.{u} R) ⊗ₜ[R] D.resolutionCubeVertexEquiv hD R j T x))) := (rfl)
    _ = _ := by
      rw [← coe_resolutionCubeVertexEquiv, LinearEquiv.apply_symm_apply,
        Khovanov.subtype_circlePieceBaseChange, LinearMap.baseChange_tmul,
        Submodule.subtype_apply, coe_resolutionCubeVertexEquiv]

private theorem resolutionCubeULiftApp_naturality {T U : Finset (Fin n)} (h : T ⋖ U) :
    (D.resolutionCube hD R j ⋙ ModuleCat.uliftRingFunctor.{u, v} R).map (homOfLE h.le) ≫
        (resolutionCubeULiftApp.{u, v} D hD R j U).hom =
      (resolutionCubeULiftApp.{u, v} D hD R j T).hom ≫
        (D.resolutionCube hD (ULift.{u} R) j).map (homOfLE h.le) := by
  obtain ⟨a, ha, rfl⟩ := Finset.covBy_iff_exists_insert.mp h
  rw [← cancel_mono (D.resolutionCubeι hD (ULift.{u} R) j (insert a T))]
  refine ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
  have hx : x = uliftRingUp (uliftRingDown x) := rfl
  rw [hx]
  have hR := congr($(D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD R j ha)
    (uliftRingDown x))
  have hU := congr($(D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD (ULift.{u} R) j ha)
    ((resolutionCubeULiftApp.{u, v} D hD R j T).hom (uliftRingUp (uliftRingDown x))))
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ofHom_apply] at hR hU
  calc _ = D.resolutionCubeι hD (ULift.{u} R) j (insert a T)
        ((resolutionCubeULiftApp.{u, v} D hD R j (insert a T)).hom
          (uliftRingUp ((D.resolutionCube hD R j).map (homOfLE h.le) (uliftRingDown x)))) := (rfl)
    _ = D.resolutionCubeι hD (ULift.{u} R) j (insert a T)
        ((D.resolutionCube hD (ULift.{u} R) j).map (homOfLE h.le)
          ((resolutionCubeULiftApp.{u, v} D hD R j T).hom (uliftRingUp (uliftRingDown x)))) := by
      rw [resolutionCubeι_resolutionCubeULiftApp_up, hR, hU,
        resolutionCubeι_resolutionCubeULiftApp_up, ← circleBaseChange_resolutionEdgeMap,
        LinearMap.baseChange_tmul]
    _ = _ := (rfl)

/-- **Universe lifting for the cube of resolutions.** Applying `ModuleCat.uliftRingFunctor.{u, v} R`
vertexwise to the degree-`j` cube of resolutions over `R` gives the degree-`j` cube of resolutions
over `ULift.{u} R`. -/
def resolutionCubeULiftIso :
    D.resolutionCube hD R j ⋙ ModuleCat.uliftRingFunctor.{u, v} R ≅
      D.resolutionCube hD (ULift.{u} R) j :=
  NatIso.ofComponents (resolutionCubeULiftApp.{u, v} D hD R j) fun g ↦ by
    simpa only [NatTrans.ofCubeEdges_app] using
      (NatTrans.ofCubeEdges (fun T ↦ (resolutionCubeULiftApp.{u, v} D hD R j T).hom)
        fun _ _ h ↦ resolutionCubeULiftApp_naturality.{u, v} D hD R j h).naturality g

/-- **Universe lifting for the signed cube complex of resolutions.** -/
def cubeComplexULiftIso :
    ((ModuleCat.uliftRingFunctor.{u, v} R).mapHomologicalComplex (.up ℤ)).obj
        (D.resolutionCube hD R j).cubeComplex ≅
      (D.resolutionCube hD (ULift.{u} R) j).cubeComplex :=
  (D.resolutionCube hD R j).mapCubeComplexIso (ModuleCat.uliftRingFunctor.{u, v} R) ≪≫
    cubeComplexMapIso (D.resolutionCubeULiftIso.{u, v} hD R j)

/-- **Universe lifting for the unnormalized Khovanov bracket.** -/
def khovanovBracketULiftIso :
    ((ModuleCat.uliftRingFunctor.{u, v} R).mapHomologicalComplex (.up ℤ)).obj
        (D.khovanovBracket hD R j) ≅
      D.khovanovBracket hD (ULift.{u} R) j :=
  ((ModuleCat.uliftRingFunctor.{u, v} R).mapHomologicalComplex (.up ℤ)).mapIso
      (eqToIso (D.khovanovBracket_apply hD R j)) ≪≫
    D.cubeComplexULiftIso.{u, v} hD R j ≪≫
      eqToIso (D.khovanovBracket_apply hD (ULift.{u} R) j).symm

end ULift

end TauCeti.PDCode

namespace TauCeti.OrientedPDCode

section BaseChange

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
  {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- **Coefficient change for the normalized Khovanov complex.** Extending scalars along
`f : R →+* S` termwise in the quantum-degree-`j` normalized Khovanov complex over `R` gives the
normalized Khovanov complex over `S`. -/
def khovanovComplexBaseChangeIso (j : ℤ) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (D.khovanovComplex hD R j) ≅
      D.khovanovComplex hD S j :=
  HomologicalComplex.mapTranslatedIso (ModuleCat.extendScalars f)
    (fun i : ℤ ↦ i + D.negativeCrossingCount)
    (D.khovanovComplex_X hD R j)
    (D.khovanovComplex_d hD R j)
    (D.khovanovComplex_X hD S j)
    (D.khovanovComplex_d hD S j)
    (D.toPDCode.cubeComplexBaseChangeIso hD f
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount))

/-- On each state summand `T` in cochain degree `i`, `khovanovComplexBaseChangeIso` acts by
`resolutionCubeBaseChangeIso` at `T`. -/
@[reassoc (attr := simp)]
theorem map_khovanovComplexι_comp_khovanovComplexBaseChangeIso_hom (j : ℤ) {i : ℤ}
    (T : {T : Finset (Fin n) // (#T : ℤ) = i + D.negativeCrossingCount}) :
    (ModuleCat.extendScalars f).map (D.khovanovComplexι hD R j T) ≫
        (D.khovanovComplexBaseChangeIso hD f j).hom.f i =
      (D.toPDCode.resolutionCubeBaseChangeIso hD f
        (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).hom.app T.1 ≫
        D.khovanovComplexι hD S j T := by
  simp only [khovanovComplexBaseChangeIso, HomologicalComplex.mapTranslatedIso_hom_f,
    khovanovComplexι_def, Functor.map_comp, Category.assoc]
  rw [← (ModuleCat.extendScalars f).map_comp_assoc (eqToHom _), eqToHom_trans, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.id_comp,
    PDCode.map_cubeComplexι_comp_cubeComplexBaseChangeIso_hom_assoc]

/-- **Canonical `S`-linear comparison `S ⊗[R] Khⁱʲ(D; R) ⟶ Khⁱʲ(D; S)`** induced by a ring
homomorphism `f : R →+* S`, defined for arbitrary commutative rings without flatness or PID
hypotheses. -/
def khovanovHomologyBaseChangeMap (i j : ℤ) :
    (ModuleCat.extendScalars f).obj (D.khovanovHomology hD R i j) ⟶
      D.khovanovHomology hD S i j :=
  (D.khovanovComplex hD R j).mapHomologyComparison (ModuleCat.extendScalars f) i ≫
    homologyMap (D.khovanovComplexBaseChangeIso hD f j).hom i

/-- Definition of `khovanovHomologyBaseChangeMap` as `mapHomologyComparison` followed by the
cohomology isomorphism induced by `khovanovComplexBaseChangeIso`. -/
theorem khovanovHomologyBaseChangeMap_def (i j : ℤ) :
    D.khovanovHomologyBaseChangeMap hD f i j =
      (D.khovanovComplex hD R j).mapHomologyComparison (ModuleCat.extendScalars f) i ≫
        homologyMap (D.khovanovComplexBaseChangeIso hD f j).hom i :=
  (rfl)

/-- When `ModuleCat.extendScalars f` preserves homology (for example along a flat ring map), the
canonical comparison `khovanovHomologyBaseChangeMap` is an isomorphism. -/
instance isIso_khovanovHomologyBaseChangeMap_of_preservesHomology
    [(ModuleCat.extendScalars.{u, u, u} f).PreservesHomology] (i j : ℤ) :
    IsIso (D.khovanovHomologyBaseChangeMap hD f i j) := by
  have := (ModuleCat.extendScalars.{u, u, u} f).preservesFiniteColimits_of_preservesHomology
  have : IsIso ((D.khovanovComplex hD R j).mapHomologyComparison
      (ModuleCat.extendScalars.{u, u, u} f) i) :=
    HomologicalComplex.isIso_mapHomologyComparison_of_preservesHomology _ _ _
  have : IsIso (homologyMap (D.khovanovComplexBaseChangeIso hD f j).hom i) :=
    ((homologyFunctor _ _ i).mapIso (D.khovanovComplexBaseChangeIso hD f j)).isIso_hom
  rw [khovanovHomologyBaseChangeMap]
  exact IsIso.comp_isIso

/-- **Exact base-change isomorphism for Khovanov cohomology.** When `ModuleCat.extendScalars f`
preserves homology, `S ⊗[R] Khⁱʲ(D; R) ≅ Khⁱʲ(D; S)` as `S`-modules. -/
def khovanovHomologyBaseChangeIsoOfPreservesHomology
    [(ModuleCat.extendScalars.{u, u, u} f).PreservesHomology] (i j : ℤ) :
    (ModuleCat.extendScalars f).obj (D.khovanovHomology hD R i j) ≅
      D.khovanovHomology hD S i j :=
  asIso (D.khovanovHomologyBaseChangeMap hD f i j)

/-- The forward morphism of `khovanovHomologyBaseChangeIsoOfPreservesHomology` is
`khovanovHomologyBaseChangeMap`. -/
@[simp]
theorem khovanovHomologyBaseChangeIsoOfPreservesHomology_hom
    [(ModuleCat.extendScalars.{u, u, u} f).PreservesHomology] (i j : ℤ) :
    (D.khovanovHomologyBaseChangeIsoOfPreservesHomology hD f i j).hom =
      D.khovanovHomologyBaseChangeMap hD f i j :=
  (rfl)

end BaseChange

section ULift

universe u v

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) (R : Type v) [CommRing R]

/-- **Universe lifting for the normalized Khovanov complex.** Applying
`ModuleCat.uliftRingFunctor.{u, v} R` termwise to `D.khovanovComplex hD R j` gives
`D.khovanovComplex hD (ULift.{u} R) j`. -/
def khovanovComplexULiftIso (j : ℤ) :
    ((ModuleCat.uliftRingFunctor.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (D.khovanovComplex hD R j) ≅
      D.khovanovComplex hD (ULift.{u} R) j :=
  HomologicalComplex.mapTranslatedIso (ModuleCat.uliftRingFunctor.{u, v} R)
    (fun i : ℤ ↦ i + D.negativeCrossingCount)
    (D.khovanovComplex_X hD R j)
    (D.khovanovComplex_d hD R j)
    (D.khovanovComplex_X hD (ULift.{u} R) j)
    (D.khovanovComplex_d hD (ULift.{u} R) j)
    (D.toPDCode.cubeComplexULiftIso.{u, v} hD R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount))

/-- **Universe lifting for Khovanov cohomology.** Because `ModuleCat.uliftRingFunctor.{u, v} R` is
exact, lifting `Khⁱʲ(D; R)` from universe `v` to `ModuleCat.{max v u} (ULift.{u} R)` agrees up to
canonical isomorphism with `Khⁱʲ(D; ULift.{u} R)` (in particular for `R = ℤ` where `v = 0`). -/
def khovanovHomologyULiftIso (i j : ℤ) :
    (ModuleCat.uliftRingFunctor.{u, v} R).obj (D.khovanovHomology hD R i j) ≅
      D.khovanovHomology hD (ULift.{u} R) i j :=
  (((D.khovanovComplex hD R j).sc i).mapHomologyIso (ModuleCat.uliftRingFunctor.{u, v} R)).symm ≪≫
    (homologyFunctor (ModuleCat.{max v u} (ULift.{u} R)) (ComplexShape.up ℤ) i).mapIso
      (D.khovanovComplexULiftIso.{u, v} hD R j)

end ULift

end TauCeti.OrientedPDCode
