/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.Injective
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.Algebra.Homology.Cube.Dual.Complex
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic
public import TauCeti.KnotTheory.Khovanov.Complex
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Resolution.Mirror
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Module.Injective.DivisionRing

/-!
# Mirror duality for the Khovanov complex and Khovanov cohomology

For a planar oriented PD-code `D`, the normalized Khovanov complex of the mirror `D.mirror` in
quantum degree `j` is isomorphic to the dual of the normalized Khovanov complex of `D` in
quantum degree `-j`, the cochain complex `Hom(C(D)_{-j}, R)` of linear maps into `R` placed in
degree `0` (`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`). Its term in cochain degree `i` is
`Hom(C(D)^{-i}_{-j}, R)`, so the bidegree `(i, j)` of the mirror corresponds to `(-i, -j)`.

The isomorphism combines three identifications. The Frobenius pairing identifies the cube of
resolutions of the mirror with the dual cube of the cube of resolutions of `D`
(`TauCeti.PDCode.mirrorKhovanovBracketIso`). The totalization of a dual cube, shifted by
`b = n₊(D) = n₋(D.mirror)`, is the dual of the totalization shifted by `a = n₋(D)`, since
`a + b` is the number of crossings (`CategoryTheory.Functor.dualCubeComplexIso`). Finally the
normalized complexes are the native cochain shifts of the brackets by their negative crossing
counts (`TauCeti.OrientedPDCode.khovanovComplexShiftIso`). The resulting isomorphism respects the
differentials with all their signs; it is not merely an identification of ranks.

Passing to cohomology (`TauCeti.OrientedPDCode.khovanovHomologyMirrorIso`) and applying the cochain
universal coefficient theorem (`TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic`) yields
mirror duality on Khovanov cohomology:

* Over any commutative ring `R`, `khovanovMirrorKronecker` evaluates `Khⁱʲ(D.mirror; R)` on
  `Kh⁻ⁱ,⁻ʲ(D; R)`, and is an isomorphism whenever `R` is self-injective
  (`khovanovHomologyMirrorDualEquivOfInjective`).
* Over a field `F`, `Khⁱʲ(D.mirror; F) ≃ₗ[F] Dual F (Kh⁻ⁱ,⁻ʲ(D; F))`
  (`khovanovHomologyMirrorDualEquiv`), giving `finrank_khovanovHomology_mirror`.
* Over any hereditary commutative ring `R`, i.e.,
  `[∀ V : ModuleCat R, HasProjectiveDimensionLE V 1]` (in particular any principal ideal domain
  such as `ℤ`, via `ModuleCat.hasProjectiveDimensionLE_one_of_isPrincipalIdealRing`), there is a
  split short exact sequence
  `0 ⟶ Ext¹_R(Kh¹⁻ⁱ,⁻ʲ(D; R), R) ⟶ Khⁱʲ(D.mirror; R) ⟶ Dual_R(Kh⁻ⁱ,⁻ʲ(D; R)) ⟶ 0`
  (`khovanovMirrorUniversalCoefficientEquiv`, `khovanovMirrorUniversalCoefficientSplitting`).

## Main definitions and results

* `TauCeti.OrientedPDCode.khovanovComplexMirrorIso`, `khovanovComplexMirrorIso_hom_f_apply`, and
  `khovanovComplexMirrorIso_inv_f_apply`: chain-level mirror duality isomorphism and formulas.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorIso`, `khovanovMirrorKronecker`,
  `khovanovHomologyMirrorDualEquiv`, `khovanovHomologyMirrorDualIso`, and
  `finrank_khovanovHomology_mirror`: cohomology isomorphism, Kronecker pairing, and field duality.
* `TauCeti.OrientedPDCode.khovanovMirrorExtToHomology`, `khovanovMirrorKroneckerSection`,
  `khovanovMirrorUniversalCoefficientEquiv`, `khovanovMirrorUniversalCoefficientShortComplex`, and
  `khovanovMirrorUniversalCoefficientSplitting`: universal coefficient sequence and splitting over
  a hereditary commutative ring.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.3,
  Proposition 32 and Corollary 11.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.
-/

public section

noncomputable section

open CategoryTheory CochainComplex Opposite Finset

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]
  (j : ℤ)

/-- The quantum degree of the cube of `D` dual to the bracket degree of the mirror used in
quantum degree `j`. -/
private lemma mirror_cube_degree :
    (n : ℤ) - (j - D.mirror.positiveCrossingCount + 2 * D.mirror.negativeCrossingCount) =
      -j - D.positiveCrossingCount + 2 * D.negativeCrossingCount := by
  have := D.positiveCrossingCount_add_negativeCrossingCount
  simp only [positiveCrossingCount_mirror, negativeCrossingCount_mirror]
  omega

/-- The negative crossing counts of `D` and of its mirror add up to the number of crossings. -/
private lemma negativeCrossingCount_add_mirror :
    (D.negativeCrossingCount : ℤ) + D.mirror.negativeCrossingCount = Fintype.card (Fin n) := by
  have := D.positiveCrossingCount_add_negativeCrossingCount
  simp only [negativeCrossingCount_mirror, Fintype.card_fin]
  omega

/-- The brackets of equal codes agree. -/
private lemma khovanovBracket_congr {P Q : PDCode n} (e : P = Q) (hP : P.IsPlanar)
    (hQ : Q.IsPlanar) (k : ℤ) : P.khovanovBracket hP R k = Q.khovanovBracket hQ R k := by
  subst e
  rfl

/-- **The Khovanov complex of the mirror is the dual complex.** For a planar oriented code `D`,
the normalized Khovanov complex of `D.mirror` in quantum degree `j` is isomorphic to the dual
`Hom(C(D)_{-j}, R)` of the normalized Khovanov complex of `D` in quantum degree `-j`, the
`R`-linear Hom complex into `R` placed in degree `0`. In cochain degree `i` it pairs the states of
the mirror with `|S| - n₋(D.mirror) = i` with the complementary states of `D`, of cochain
degree `-i`, by the Frobenius pairing of their circle tensors, up to a sign depending on the state
and the degree (`TauCeti.OrientedPDCode.khovanovComplexMirrorIso_hom_f_apply` and
`TauCeti.OrientedPDCode.khovanovComplexMirrorIso_inv_f_apply`). Any planarity proof `hD'` for the
mirror may be used. -/
def khovanovComplexMirrorIso (hD' : D.mirror.toPDCode.IsPlanar) :
    D.mirror.khovanovComplex hD' R j ≅
      linearHomComplex R (D.khovanovComplex hD R (-j))
        ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :=
  D.mirror.khovanovComplexShiftIso hD' R j ≪≫
    (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ)
      (D.mirror.negativeCrossingCount : ℤ)).mapIso
        (eqToIso (khovanovBracket_congr R (mirror_toPDCode D) hD'
          ((PDCode.isPlanar_mirror D.toPDCode).2 hD) _) ≪≫
          D.toPDCode.mirrorKhovanovBracketIso hD R _ ≪≫
          eqToIso (by rw [mirror_cube_degree])) ≪≫
    (D.toPDCode.resolutionCube hD R
      (-j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).dualCubeComplexIso
        (negativeCrossingCount_add_mirror D) ≪≫
    ((TauCeti.linearHomComplexFunctor R).mapIso
      (D.khovanovComplexShiftIso hD R (-j) ≪≫
        (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ)
          (D.negativeCrossingCount : ℤ)).mapIso
            (eqToIso (D.toPDCode.khovanovBracket_apply hD R _))).op).app
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))

/-- Vertex inclusions commute with the transport between the totalizations of the cubes of equal
codes in equal quantum degrees. -/
@[reassoc]
private lemma cubeComplexι_eqToHom {P Q : PDCode n} (e : P = Q) (hP : P.IsPlanar)
    (hQ : Q.IsPlanar) {k k' : ℤ} (hk : k = k') {r : ℤ} (S : {S : Finset (Fin n) // (#S : ℤ) = r})
    (h : (P.resolutionCube hP R k).cubeComplex.X r = (Q.resolutionCube hQ R k').cubeComplex.X r) :
    (P.resolutionCube hP R k).cubeComplexι S ≫ eqToHom h =
      eqToHom (by subst e hk; rfl) ≫ (Q.resolutionCube hQ R k').cubeComplexι S := by
  subst e hk
  simp

/-- Vertex inclusions commute with the transport between the totalizations of the dual cubes in
equal quantum degrees. -/
@[reassoc]
private lemma dualCube_cubeComplexι_eqToHom {k k' : ℤ} (hk : k = k') {r : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = r})
    (h : (D.toPDCode.resolutionCube hD R k).dualCube.cubeComplex.X r =
      (D.toPDCode.resolutionCube hD R k').dualCube.cubeComplex.X r) :
    (D.toPDCode.resolutionCube hD R k).dualCube.cubeComplexι S ≫ eqToHom h =
      eqToHom (by subst hk; rfl) ≫ (D.toPDCode.resolutionCube hD R k').dualCube.cubeComplexι S := by
  subst hk
  simp

/-- Transporting a linear form on a vertex of the dual cube between equal quantum degrees
precomposes it with the inverse transport of the vertex of the cube. -/
private lemma eqToHom_dualCube_apply {k k' : ℤ} (hk : k = k') (T : Finset (Fin n))
    (h : (D.toPDCode.resolutionCube hD R k).dualCube.obj T =
      (D.toPDCode.resolutionCube hD R k').dualCube.obj T)
    (φ : (D.toPDCode.resolutionCube hD R k).dualCube.obj T)
    (y : (D.toPDCode.resolutionCube hD R k').obj Tᶜ) :
    (eqToHom h).hom φ y = φ ((eqToHom (show (D.toPDCode.resolutionCube hD R k').obj Tᶜ =
      (D.toPDCode.resolutionCube hD R k).obj Tᶜ by subst hk; rfl)).hom y) := by
  subst hk
  rfl

/-- Transporting a vertex of the cube between equal quantum degrees preserves its circle
tensors. -/
private lemma resolutionCubeι_eqToHom {k k' : ℤ} (hk : k = k') (T : Finset (Fin n))
    (h : (D.toPDCode.resolutionCube hD R k).obj T = (D.toPDCode.resolutionCube hD R k').obj T)
    (y : (D.toPDCode.resolutionCube hD R k).obj T) :
    (D.toPDCode.resolutionCubeι hD R k' T).hom ((eqToHom h).hom y) =
      (D.toPDCode.resolutionCubeι hD R k T).hom y := by
  subst hk
  rfl

/-- In cochain degree `i`, the mirror isomorphism sends an element `x` of the state `S` of the
mirror to the cochain of degree `i` on the projection onto the complementary state `Sᶜ` of `D`
followed by the Frobenius pairing with `x`, times `(-1)^(i n) * Finset.dualCubeSign S n₋(D)`. The
vertex `S` of the cube of `D.mirror` is identified with that of the mirror of the underlying
code of `D`, on which `TauCeti.PDCode.mirrorResolutionCubeIso` pairs circle tensors. -/
theorem khovanovComplexMirrorIso_hom_f_apply (hD' : D.mirror.toPDCode.IsPlanar) (i : ℤ)
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.mirror.negativeCrossingCount})
    (x : (D.mirror.toPDCode.resolutionCube hD' R
      (j - D.mirror.positiveCrossingCount + 2 * D.mirror.negativeCrossingCount)).obj S.1) :
    HomComplex.Cochain.toSingleEquiv (neg_add_cancel i)
        (((D.khovanovComplexMirrorIso hD R j hD').hom.f i).hom
          ((D.mirror.khovanovComplexι hD' R j S).hom x)) =
      ((i * n).negOnePow * S.1.dualCubeSign (D.negativeCrossingCount : ℤ)) •
        (D.khovanovComplexπ hD R (-j) ⟨S.1ᶜ, by
          have := card_compl_add_card S.1
          have := D.positiveCrossingCount_add_negativeCrossingCount
          have := S.2
          simp only [negativeCrossingCount_mirror, Fintype.card_fin] at *
          omega⟩ ≫ ModuleCat.ofHom
          (Khovanov.circleDuality R _ (PiTensorProduct.reindex R (fun _ ↦ DualNumber R)
            (PDCode.SmoothingEquiv.mirror D.toPDCode
              (PDCode.cubeState_compl S.1)).symm.resolvedCircleCongr
              ((D.toPDCode.mirror.resolutionCubeι ((PDCode.isPlanar_mirror _).2 hD) R
                (j - D.mirror.positiveCrossingCount + 2 * D.mirror.negativeCrossingCount)
                  S.1).hom ((eqToHom (show (D.mirror.toPDCode.resolutionCube hD' R
                    (j - D.mirror.positiveCrossingCount + 2 * D.mirror.negativeCrossingCount)).obj
                      S.1 = (D.toPDCode.mirror.resolutionCube ((PDCode.isPlanar_mirror _).2 hD) R
                    (j - D.mirror.positiveCrossingCount + 2 * D.mirror.negativeCrossingCount)).obj
                      S.1 by simp only [mirror_toPDCode])).hom x))) ∘ₗ
            (D.toPDCode.resolutionCubeι hD R _ S.1ᶜ).hom)) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  simp only [khovanovComplexMirrorIso, Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom, khovanovComplexShiftIso_hom_f, khovanovComplexι_def, Category.assoc,
    shiftFunctor_map_f', eqToIso.hom, HomologicalComplex.eqToHom_f,
    PDCode.mirrorKhovanovBracketIso_hom, eqToHom_trans_assoc, Linear.comp_units_smul,
    Linear.units_smul_comp]
  rw [cubeComplexι_eqToHom_assoc R (mirror_toPDCode D) _ ((PDCode.isPlanar_mirror _).2 hD) rfl,
    NatTrans.ι_cubeComplexMap_f_assoc, dualCube_cubeComplexι_eqToHom_assoc D hD R
      (mirror_cube_degree D j)]
  simp only [Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, map_zsmul]
  -- The last factor is typed as `linearHomComplexFunctor` applied to the shifted complex, which is
  -- `linearHomComplex` only up to unfolding; `erw` identifies the two.
  erw [Iso.trans_hom]
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    Functor.dualCubeComplexIso_hom_f_apply]
  rw [Iso.app_hom, Functor.mapIso_hom, Iso.op_hom, linearHomComplexFunctor_map_app]
  erw [linearHomComplexPrecomp_f_apply]
  rw [Quiver.Hom.unop_op, HomComplex.Cochain.comp_units_smul,
    ← HomComplex.Cochain.toSingleMk_precomp, Units.smul_def, map_zsmul,
    HomComplex.Cochain.toSingleEquiv_toSingleMk]
  simp only [Iso.trans_hom, HomologicalComplex.comp_f, khovanovComplexShiftIso_hom_f,
    Functor.mapIso_hom, shiftFunctor_map_f', eqToIso.hom, HomologicalComplex.eqToHom_f,
    Linear.units_smul_comp, Category.assoc, eqToHom_trans_assoc]
  rw [khovanovComplexπ_def]
  simp only [Units.smul_def, smul_smul, Units.val_mul]
  -- The normalization signs of the two shifts combine to `(-1)^(i n)`.
  have hs : (i * D.mirror.negativeCrossingCount).negOnePow *
      (-i * D.negativeCrossingCount).negOnePow = (i * n).negOnePow := by
    have h := D.positiveCrossingCount_add_negativeCrossingCount
    rw [negativeCrossingCount_mirror, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
    have h' : (n : ℤ) = D.positiveCrossingCount + D.negativeCrossingCount := by
      exact_mod_cast h.symm
    exact ⟨-i * D.negativeCrossingCount, by rw [h']; ring⟩
  rw [Category.assoc, mul_left_comm, mul_comm, ← Units.val_mul, hs]
  congr 3
  ext y
  rw [ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    eqToHom_dualCube_apply D hD R (mirror_cube_degree D j),
    PDCode.mirrorResolutionCubeIso_hom_app_apply, resolutionCubeι_eqToHom D hD R
      (mirror_cube_degree D j).symm]

/-- In cochain degree `i`, the inverse mirror isomorphism sends a cochain `f` to the element whose
component `x` on the state `S` of the mirror pairs with each `y` in the complementary state `Sᶜ`
of `D` to `f(y)`, times `(-1)^(i n) * Finset.dualCubeSign S n₋(D)`. Since the Frobenius pairing is
perfect, this determines the component. -/
theorem khovanovComplexMirrorIso_inv_f_apply (hD' : D.mirror.toPDCode.IsPlanar) (i : ℤ)
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.mirror.negativeCrossingCount})
    (f : HomComplex.Cochain (D.khovanovComplex hD R (-j))
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) i)
    (y : (D.toPDCode.resolutionCube hD R
      (-j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj S.1ᶜ) :
    Khovanov.circleDuality R _ (PiTensorProduct.reindex R (fun _ ↦ DualNumber R)
        (PDCode.SmoothingEquiv.mirror D.toPDCode
          (PDCode.cubeState_compl S.1)).symm.resolvedCircleCongr
          ((D.toPDCode.mirror.resolutionCubeι ((PDCode.isPlanar_mirror _).2 hD) R
            (j - D.mirror.positiveCrossingCount + 2 * D.mirror.negativeCrossingCount)
              S.1).hom ((eqToHom (show (D.mirror.toPDCode.resolutionCube hD' R
                (j - D.mirror.positiveCrossingCount + 2 * D.mirror.negativeCrossingCount)).obj
                  S.1 = (D.toPDCode.mirror.resolutionCube ((PDCode.isPlanar_mirror _).2 hD) R
                (j - D.mirror.positiveCrossingCount + 2 * D.mirror.negativeCrossingCount)).obj
                  S.1 by simp only [mirror_toPDCode])).hom
              ((D.mirror.khovanovComplexπ hD' R j S).hom
                (((D.khovanovComplexMirrorIso hD R j hD').inv.f i).hom f)))))
        ((D.toPDCode.resolutionCubeι hD R _ S.1ᶜ).hom y) =
      ((i * n).negOnePow * S.1.dualCubeSign (D.negativeCrossingCount : ℤ)) •
        (HomComplex.Cochain.toSingleEquiv (neg_add_cancel i) f).hom
          ((D.khovanovComplexι hD R (-j) ⟨S.1ᶜ, by
            have := card_compl_add_card S.1
            have := D.positiveCrossingCount_add_negativeCrossingCount
            have := S.2
            simp only [negativeCrossingCount_mirror, Fintype.card_fin] at *
            omega⟩).hom y) := by
  -- Write `f` as the image of `z`, and `z` as the sum of its state components.
  obtain ⟨z, rfl⟩ : ∃ z, ((D.khovanovComplexMirrorIso hD R j hD').hom.f i).hom z = f :=
    ⟨((D.khovanovComplexMirrorIso hD R j hD').inv.f i).hom f, by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f,
        Iso.inv_hom_id, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]⟩
  rw [← LinearMap.comp_apply (((D.khovanovComplexMirrorIso hD R j hD').inv.f i).hom),
    ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]
  have hz := congrArg (fun g ↦ g.hom z) (D.mirror.khovanovComplex_total hD' R j i)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at hz
  conv_rhs => rw [← hz]
  simp only [map_sum, ModuleCat.hom_sum, LinearMap.sum_apply, Finset.smul_sum,
    khovanovComplexMirrorIso_hom_f_apply]
  -- Only the state `S` pairs with the complementary state of `D`.
  have hιπ (T T' : {T : Finset (Fin n) // (#T : ℤ) = -i + D.negativeCrossingCount})
      (w : (D.toPDCode.resolutionCube hD R
        (-j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj T.1) :
      (D.khovanovComplexπ hD R (-j) T').hom ((D.khovanovComplexι hD R (-j) T).hom w) =
        if h : T = T' then (eqToHom (congrArg (fun T ↦ (D.toPDCode.resolutionCube hD R
          (-j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj T.1) h)).hom w
        else 0 := by
    split_ifs with h
    · subst h
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, khovanovComplexι_π_self]
      rfl
    · rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, khovanovComplexι_π_of_ne _ _ _ _ h]
      rfl
  rw [Fintype.sum_eq_single S fun T h ↦ by
    have h' : S.1 ≠ T.1 := fun e ↦ h (Subtype.ext e.symm)
    simp only [Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, hιπ, Subtype.mk.injEq, compl_inj_iff, h', ↓reduceDIte, map_zero,
      smul_zero]]
  simp only [Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, hιπ, ↓reduceDIte, ModuleCat.hom_ofHom, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul]
  -- The remaining transport of `y` is along a reflexive equality.
  rfl

section Homology

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
  (hD' : D.mirror.toPDCode.IsPlanar)

/-- **Mirror Khovanov cohomology is the cohomology of the dual complex.** In bidegree `(i, j)`,
`Khⁱʲ(D.mirror; R)` is isomorphic to `Hⁱ(Hom_R(C(D; R)_{-j}, R[0]))`. -/
def khovanovHomologyMirrorIso (R : Type u) [CommRing R] (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≅
      (linearHomComplex R (D.khovanovComplex hD R (-j))
        ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).homology i :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
    (D.khovanovComplexMirrorIso hD R j hD')

@[simp]
lemma khovanovHomologyMirrorIso_hom (R : Type u) [CommRing R] (i j : ℤ) :
    (D.khovanovHomologyMirrorIso hD hD' R i j).hom =
      HomologicalComplex.homologyMap (D.khovanovComplexMirrorIso hD R j hD').hom i := (rfl)

@[simp]
lemma khovanovHomologyMirrorIso_inv (R : Type u) [CommRing R] (i j : ℤ) :
    (D.khovanovHomologyMirrorIso hD hD' R i j).inv =
      HomologicalComplex.homologyMap (D.khovanovComplexMirrorIso hD R j hD').inv i := (rfl)

/-- **The mirror Kronecker evaluation**: evaluates classes in `Khⁱʲ(D.mirror; R)` as `R`-linear
forms on `Kh⁻ⁱ,⁻ʲ(D; R)`. -/
def khovanovMirrorKronecker (R : Type u) [CommRing R] (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j →ₗ[R]
      Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  (ModuleCat.homLinearEquiv (S := R)).toLinearMap.comp <|
    (TauCeti.cochainKronecker R (D.khovanovComplex hD R (-j))
      (ModuleCat.of R R) i).comp (D.khovanovHomologyMirrorIso hD hD' R i j).hom.hom

/-- Evaluating `khovanovMirrorKronecker` applies `TauCeti.cochainKronecker` after transporting along
`khovanovHomologyMirrorIso`. -/
lemma khovanovMirrorKronecker_apply (R : Type u) [CommRing R] (i j : ℤ)
    (x : D.mirror.khovanovHomology hD' R i j) :
    D.khovanovMirrorKronecker hD hD' R i j x =
      (TauCeti.cochainKronecker R (D.khovanovComplex hD R (-j)) (ModuleCat.of R R) i
        ((D.khovanovHomologyMirrorIso hD hD' R i j).hom.hom x)).hom := (rfl)

/-- Over a self-injective commutative ring `R`, the mirror Kronecker pairing is bijective. -/
theorem khovanovMirrorKronecker_bijective (R : Type u) [CommRing R] [Module.Injective R R]
    (i j : ℤ) : Function.Bijective (D.khovanovMirrorKronecker hD hD' R i j) := by
  have := Module.injective_object_of_injective_module R R
  exact (ModuleCat.homLinearEquiv (S := R)).bijective.comp <|
    (TauCeti.cochainKronecker_bijective
      (k := R) (K := D.khovanovComplex hD R (-j)) (Y := ModuleCat.of R R) i).comp
        (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv.bijective

/-- **Mirror Khovanov cohomology over a self-injective ring**: `Khⁱʲ(D.mirror; R) ≃ₗ[R]
Dual_R(Kh⁻ⁱ,⁻ʲ(D; R))` via `khovanovMirrorKronecker`. -/
def khovanovHomologyMirrorDualEquivOfInjective (R : Type u) [CommRing R] [Module.Injective R R]
    (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R]
      Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  letI := Module.injective_object_of_injective_module R R
  (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv.trans <|
    (TauCeti.cochainKroneckerEquiv R (D.khovanovComplex hD R (-j)) (ModuleCat.of R R) i).trans
      (ModuleCat.homLinearEquiv (S := R))

@[simp]
lemma khovanovHomologyMirrorDualEquivOfInjective_apply (R : Type u) [CommRing R]
    [Module.Injective R R] (i j : ℤ) (x : D.mirror.khovanovHomology hD' R i j) :
    D.khovanovHomologyMirrorDualEquivOfInjective hD hD' R i j x =
      D.khovanovMirrorKronecker hD hD' R i j x := by
  simp [khovanovHomologyMirrorDualEquivOfInjective, khovanovMirrorKronecker]

/-- Categorical form of `khovanovHomologyMirrorDualEquivOfInjective` in `ModuleCat R`. -/
def khovanovHomologyMirrorDualIsoOfInjective (R : Type u) [CommRing R] [Module.Injective R R]
    (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≅
      ModuleCat.of R (Module.Dual R (D.khovanovHomology hD R (-i) (-j))) :=
  (D.khovanovHomologyMirrorDualEquivOfInjective hD hD' R i j).toModuleIso

@[simp]
lemma khovanovHomologyMirrorDualIsoOfInjective_hom (R : Type u) [CommRing R]
    [Module.Injective R R] (i j : ℤ) :
    (D.khovanovHomologyMirrorDualIsoOfInjective hD hD' R i j).hom =
      ModuleCat.ofHom (D.khovanovMirrorKronecker hD hD' R i j) := by
  ext x
  simp [khovanovHomologyMirrorDualIsoOfInjective]

@[simp]
lemma khovanovHomologyMirrorDualIsoOfInjective_inv (R : Type u) [CommRing R]
    [Module.Injective R R] (i j : ℤ) :
    (D.khovanovHomologyMirrorDualIsoOfInjective hD hD' R i j).inv =
      ModuleCat.ofHom
        (D.khovanovHomologyMirrorDualEquivOfInjective hD hD' R i j).symm.toLinearMap := (rfl)

/-- **Mirror Khovanov cohomology over a field**: `Khⁱʲ(D.mirror; F) ≃ₗ[F] Dual_F(Kh⁻ⁱ,⁻ʲ(D; F))`. -/
def khovanovHomologyMirrorDualEquiv (F : Type u) [Field F] (i j : ℤ) :
    D.mirror.khovanovHomology hD' F i j ≃ₗ[F]
      Module.Dual F (D.khovanovHomology hD F (-i) (-j)) :=
  D.khovanovHomologyMirrorDualEquivOfInjective hD hD' F i j

@[simp]
lemma khovanovHomologyMirrorDualEquiv_apply (F : Type u) [Field F] (i j : ℤ)
    (x : D.mirror.khovanovHomology hD' F i j) :
    D.khovanovHomologyMirrorDualEquiv hD hD' F i j x =
      D.khovanovMirrorKronecker hD hD' F i j x := by
  simp [khovanovHomologyMirrorDualEquiv]

/-- Categorical form of `khovanovHomologyMirrorDualEquiv` in `ModuleCat F`. -/
def khovanovHomologyMirrorDualIso (F : Type u) [Field F] (i j : ℤ) :
    D.mirror.khovanovHomology hD' F i j ≅
      ModuleCat.of F (Module.Dual F (D.khovanovHomology hD F (-i) (-j))) :=
  (D.khovanovHomologyMirrorDualEquiv hD hD' F i j).toModuleIso

@[simp]
lemma khovanovHomologyMirrorDualIso_hom (F : Type u) [Field F] (i j : ℤ) :
    (D.khovanovHomologyMirrorDualIso hD hD' F i j).hom =
      ModuleCat.ofHom (D.khovanovMirrorKronecker hD hD' F i j) := by
  ext x
  simp [khovanovHomologyMirrorDualIso]

@[simp]
lemma khovanovHomologyMirrorDualIso_inv (F : Type u) [Field F] (i j : ℤ) :
    (D.khovanovHomologyMirrorDualIso hD hD' F i j).inv =
      ModuleCat.ofHom (D.khovanovHomologyMirrorDualEquiv hD hD' F i j).symm.toLinearMap := (rfl)

/-- **Mirror symmetry of Khovanov Betti numbers**: over any field `F`,
`finrank F Khⁱʲ(D.mirror; F) = finrank F Kh⁻ⁱ,⁻ʲ(D; F)`. -/
theorem finrank_khovanovHomology_mirror (F : Type u) [Field F] (i j : ℤ) :
    Module.finrank F (D.mirror.khovanovHomology hD' F i j) =
      Module.finrank F (D.khovanovHomology hD F (-i) (-j)) :=
  (D.khovanovHomologyMirrorDualEquiv hD hD' F i j).finrank_eq.trans Subspace.dual_finrank_eq

section Hereditary

variable (R : Type u) [CommRing R] [∀ V : ModuleCat.{u} R, HasProjectiveDimensionLE V 1]

/-- **The `Ext` map into mirror Khovanov cohomology** over a hereditary commutative ring: the
`R`-linear map `Ext¹_R(Kh¹⁻ⁱ,⁻ʲ(D; R), R) →ₗ[R] Khⁱʲ(D.mirror; R)` transported from
`TauCeti.cochainExtToHomology` along `khovanovHomologyMirrorIso`. -/
def khovanovMirrorExtToHomology (i j : ℤ) :
    Abelian.Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1 →ₗ[R]
      D.mirror.khovanovHomology hD' R i j :=
  (D.khovanovHomologyMirrorIso hD hD' R i j).inv.hom.comp <|
    TauCeti.cochainExtToHomology.{u} R (D.khovanovComplex hD R (-j))
      (ModuleCat.of R R) (show i + (1 - i) = 1 by omega)

/-- Evaluating `khovanovMirrorExtToHomology` transports `TauCeti.cochainExtToHomology` back along
`khovanovHomologyMirrorIso`. -/
lemma khovanovMirrorExtToHomology_apply (i j : ℤ)
    (e : Abelian.Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1) :
    D.khovanovMirrorExtToHomology hD hD' R i j e =
      (D.khovanovHomologyMirrorIso hD hD' R i j).inv.hom
        (TauCeti.cochainExtToHomology.{u} R (D.khovanovComplex hD R (-j))
          (ModuleCat.of R R) (show i + (1 - i) = 1 by omega) e) := (rfl)

/-- Over a hereditary commutative ring, `khovanovMirrorExtToHomology` is injective. -/
theorem khovanovMirrorExtToHomology_injective (i j : ℤ) :
    Function.Injective (D.khovanovMirrorExtToHomology hD hD' R i j) :=
  (D.khovanovHomologyMirrorIso hD hD' R i j).symm.toLinearEquiv.injective.comp
    (TauCeti.cochainExtToHomology_injective
      (k := R) (K := D.khovanovComplex hD R (-j)) (Y := ModuleCat.of R R)
      (show i + (1 - i) = 1 by omega))

/-- **Exactness of the mirror Khovanov universal coefficient sequence** over a hereditary
commutative ring: `ker khovanovMirrorKronecker = range khovanovMirrorExtToHomology`. -/
theorem exact_khovanovMirrorExtToHomology_khovanovMirrorKronecker (i j : ℤ) :
    Function.Exact (D.khovanovMirrorExtToHomology hD hD' R i j)
      (D.khovanovMirrorKronecker hD hD' R i j) := by
  let eM := (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv
  have h1 : Function.Exact
      (eM.symm.toLinearMap.comp (TauCeti.cochainExtToHomology.{u} R
        (D.khovanovComplex hD R (-j)) (ModuleCat.of R R) (show i + (1 - i) = 1 by omega)))
      ((TauCeti.cochainKronecker R (D.khovanovComplex hD R (-j))
        (ModuleCat.of R R) i).comp eM.toLinearMap) :=
    (eM.conj_symm_exact_iff_exact _ _).2
      (TauCeti.exact_cochainExtToHomology_cochainKronecker.{u}
        (k := R) (K := D.khovanovComplex hD R (-j)) (Y := ModuleCat.of R R)
        (show i + (1 - i) = 1 by omega))
  exact (ModuleCat.homLinearEquiv (S := R)).postcomp_exact_iff_exact.2 h1

/-- **A splitting section of `khovanovMirrorKronecker`** over a hereditary commutative ring. -/
def khovanovMirrorKroneckerSection (i j : ℤ) :
    Module.Dual R (D.khovanovHomology hD R (-i) (-j)) →ₗ[R]
      D.mirror.khovanovHomology hD' R i j :=
  (D.khovanovHomologyMirrorIso hD hD' R i j).inv.hom.comp <|
    (TauCeti.cochainKroneckerSection R (D.khovanovComplex hD R (-j))
      (ModuleCat.of R R) i).comp
        (ModuleCat.homLinearEquiv (R := R) (S := R)
          (M := D.khovanovHomology hD R (-i) (-j)) (N := ModuleCat.of R R)).symm.toLinearMap

/-- Evaluating `khovanovMirrorKroneckerSection` transports `TauCeti.cochainKroneckerSection` back
along `khovanovHomologyMirrorIso`. -/
lemma khovanovMirrorKroneckerSection_apply (i j : ℤ)
    (g : Module.Dual R (D.khovanovHomology hD R (-i) (-j))) :
    D.khovanovMirrorKroneckerSection hD hD' R i j g =
      (D.khovanovHomologyMirrorIso hD hD' R i j).inv.hom
        (TauCeti.cochainKroneckerSection R (D.khovanovComplex hD R (-j))
          (ModuleCat.of R R) i (ModuleCat.ofHom g)) := (rfl)

@[simp]
theorem khovanovMirrorKronecker_khovanovMirrorKroneckerSection (i j : ℤ)
    (g : Module.Dual R (D.khovanovHomology hD R (-i) (-j))) :
    D.khovanovMirrorKronecker hD hD' R i j
        (D.khovanovMirrorKroneckerSection hD hD' R i j g) = g := by
  simp only [khovanovMirrorKronecker, khovanovMirrorKroneckerSection, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    TauCeti.cochainKronecker_cochainKroneckerSection, LinearEquiv.apply_symm_apply]

/-- Over a hereditary commutative ring, `khovanovMirrorKronecker` is surjective. -/
theorem khovanovMirrorKronecker_surjective (i j : ℤ) :
    Function.Surjective (D.khovanovMirrorKronecker hD hD' R i j) := fun g ↦
  ⟨D.khovanovMirrorKroneckerSection hD hD' R i j g,
    D.khovanovMirrorKronecker_khovanovMirrorKroneckerSection hD hD' R i j g⟩

/-- **The universal coefficient decomposition for mirror Khovanov cohomology** over a hereditary
commutative ring:
`Khⁱʲ(D.mirror; R) ≃ₗ[R] Ext¹_R(Kh¹⁻ⁱ,⁻ʲ(D; R), R) × Dual_R(Kh⁻ⁱ,⁻ʲ(D; R))`. -/
def khovanovMirrorUniversalCoefficientEquiv (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R]
      Abelian.Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1 ×
        Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv.trans <|
    (TauCeti.cochainUniversalCoefficientEquiv.{u} R (D.khovanovComplex hD R (-j))
      (ModuleCat.of R R) (show i + (1 - i) = 1 by omega)).trans <|
        LinearEquiv.prodCongr (LinearEquiv.refl R _) (ModuleCat.homLinearEquiv (S := R))

@[simp]
lemma khovanovMirrorUniversalCoefficientEquiv_symm_apply (i j : ℤ)
    (e : Abelian.Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1)
    (g : Module.Dual R (D.khovanovHomology hD R (-i) (-j))) :
    (D.khovanovMirrorUniversalCoefficientEquiv hD hD' R i j).symm (e, g) =
      D.khovanovMirrorExtToHomology hD hD' R i j e +
        D.khovanovMirrorKroneckerSection hD hD' R i j g := by
  simp [khovanovMirrorUniversalCoefficientEquiv, khovanovMirrorExtToHomology,
    khovanovMirrorKroneckerSection]

@[simp]
lemma khovanovMirrorUniversalCoefficientEquiv_apply_snd (i j : ℤ)
    (x : D.mirror.khovanovHomology hD' R i j) :
    (D.khovanovMirrorUniversalCoefficientEquiv hD hD' R i j x).2 =
      D.khovanovMirrorKronecker hD hD' R i j x := by
  simp [khovanovMirrorUniversalCoefficientEquiv, khovanovMirrorKronecker]

/-- **The mirror universal coefficient short complex** in `ModuleCat R`:
`Ext¹_R(Kh¹⁻ⁱ,⁻ʲ(D; R), R) ⟶ Khⁱʲ(D.mirror; R) ⟶ Dual_R(Kh⁻ⁱ,⁻ʲ(D; R))`. -/
def khovanovMirrorUniversalCoefficientShortComplex (i j : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (D.khovanovMirrorExtToHomology hD hD' R i j))
    (ModuleCat.ofHom (D.khovanovMirrorKronecker hD hD' R i j))
    (ModuleCat.hom_ext <| LinearMap.ext fun e ↦
      (D.exact_khovanovMirrorExtToHomology_khovanovMirrorKronecker hD hD' R i j
        ).apply_apply_eq_zero e)

/-- The left object of `khovanovMirrorUniversalCoefficientShortComplex` is `Ext¹`. -/
@[simp]
lemma khovanovMirrorUniversalCoefficientShortComplex_X₁ (i j : ℤ) :
    (D.khovanovMirrorUniversalCoefficientShortComplex hD hD' R i j).X₁ =
      ModuleCat.of R
        (Abelian.Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1) := (rfl)

/-- The middle object of `khovanovMirrorUniversalCoefficientShortComplex` is mirror Khovanov
cohomology. -/
@[simp]
lemma khovanovMirrorUniversalCoefficientShortComplex_X₂ (i j : ℤ) :
    (D.khovanovMirrorUniversalCoefficientShortComplex hD hD' R i j).X₂ =
      D.mirror.khovanovHomology hD' R i j := (rfl)

/-- The right object of `khovanovMirrorUniversalCoefficientShortComplex` is the `R`-linear dual of
Khovanov cohomology. -/
@[simp]
lemma khovanovMirrorUniversalCoefficientShortComplex_X₃ (i j : ℤ) :
    (D.khovanovMirrorUniversalCoefficientShortComplex hD hD' R i j).X₃ =
      ModuleCat.of R (Module.Dual R (D.khovanovHomology hD R (-i) (-j))) := (rfl)

/-- The mirror universal coefficient sequence consists of `khovanovMirrorExtToHomology` and
`khovanovMirrorKronecker`. This constructor equation also identifies the dependent carriers of its
two maps. -/
lemma khovanovMirrorUniversalCoefficientShortComplex_def (i j : ℤ) :
    D.khovanovMirrorUniversalCoefficientShortComplex hD hD' R i j =
      ShortComplex.mk
        (ModuleCat.ofHom (D.khovanovMirrorExtToHomology hD hD' R i j))
        (ModuleCat.ofHom (D.khovanovMirrorKronecker hD hD' R i j))
        (ModuleCat.hom_ext <| LinearMap.ext fun e ↦
          (D.exact_khovanovMirrorExtToHomology_khovanovMirrorKronecker hD hD' R i j
            ).apply_apply_eq_zero e) := (rfl)

/-- **Splitting of `khovanovMirrorUniversalCoefficientShortComplex`** in `ModuleCat R`. -/
def khovanovMirrorUniversalCoefficientSplitting (i j : ℤ) :
    (D.khovanovMirrorUniversalCoefficientShortComplex hD hD' R i j).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      (D.exact_khovanovMirrorExtToHomology_khovanovMirrorKronecker hD hD' R i j))
    (ModuleCat.ofHom (D.khovanovMirrorKroneckerSection hD hD' R i j))
    (ModuleCat.hom_ext <| LinearMap.ext
      (D.khovanovMirrorKronecker_khovanovMirrorKroneckerSection hD hD' R i j))
    ((ModuleCat.mono_iff_injective _).2 (D.khovanovMirrorExtToHomology_injective hD hD' R i j))

/-- The section of `khovanovMirrorUniversalCoefficientSplitting` is
`khovanovMirrorKroneckerSection`. -/
lemma khovanovMirrorUniversalCoefficientSplitting_s (i j : ℤ) :
    (D.khovanovMirrorUniversalCoefficientSplitting hD hD' R i j).s =
      eqToHom (D.khovanovMirrorUniversalCoefficientShortComplex_X₃ hD hD' R i j) ≫
        ModuleCat.ofHom (D.khovanovMirrorKroneckerSection hD hD' R i j) ≫
        eqToHom (D.khovanovMirrorUniversalCoefficientShortComplex_X₂ hD hD' R i j).symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- `khovanovMirrorUniversalCoefficientShortComplex` is short exact in `ModuleCat R`. -/
theorem khovanovMirrorUniversalCoefficientShortComplex_shortExact (i j : ℤ) :
    (D.khovanovMirrorUniversalCoefficientShortComplex hD hD' R i j).ShortExact :=
  (D.khovanovMirrorUniversalCoefficientSplitting hD hD' R i j).shortExact

/-- Over a hereditary commutative ring, if `Kh¹⁻ⁱ,⁻ʲ(D; R)` is projective,
`khovanovMirrorKronecker` is an equivalence. -/
def khovanovHomologyMirrorDualEquivOfProjective (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))] :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R]
      Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv.trans <|
    (TauCeti.cochainKroneckerEquivOfProjectiveHomology R (D.khovanovComplex hD R (-j))
      (ModuleCat.of R R) (show i + (1 - i) = 1 by omega)).trans
        (ModuleCat.homLinearEquiv (S := R))

@[simp]
lemma khovanovHomologyMirrorDualEquivOfProjective_apply (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))]
    (x : D.mirror.khovanovHomology hD' R i j) :
    D.khovanovHomologyMirrorDualEquivOfProjective hD hD' R i j x =
      D.khovanovMirrorKronecker hD hD' R i j x := by
  simp [khovanovHomologyMirrorDualEquivOfProjective, khovanovMirrorKronecker]

/-- Over a hereditary commutative ring, if `Kh¹⁻ⁱ,⁻ʲ(D; R)` is projective and `Kh⁻ⁱ,⁻ʲ(D; R)`
vanishes, so does `Khⁱʲ(D.mirror; R)`. -/
theorem isZero_khovanovHomology_mirror_of_projective (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))]
    (h0 : Limits.IsZero (D.khovanovHomology hD R (-i) (-j))) :
    Limits.IsZero (D.mirror.khovanovHomology hD' R i j) :=
  (TauCeti.isZero_homology_linearHomComplex_of_projective_homology
    (k := R) (K := D.khovanovComplex hD R (-j)) (Y := ModuleCat.of R R)
    (show i + (1 - i) = 1 by omega) h0).of_iso (D.khovanovHomologyMirrorIso hD hD' R i j)

end Hereditary

end Homology

end TauCeti.OrientedPDCode
