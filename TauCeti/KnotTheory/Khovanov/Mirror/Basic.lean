/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.Dual.Complex
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.KnotTheory.Khovanov.Complex
public import TauCeti.KnotTheory.Khovanov.Resolution.Mirror

/-!
# The Khovanov complex of the mirror diagram is the dual complex

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

## Main definitions

* `TauCeti.OrientedPDCode.khovanovComplexMirrorIso D hD R j`: the isomorphism from the
  normalized Khovanov complex of `D.mirror` in quantum degree `j` to the dual of the normalized
  Khovanov complex of `D` in quantum degree `-j`.

## Main results

* `TauCeti.OrientedPDCode.khovanovComplexMirrorIso_hom_f_apply`: the isomorphism sends an
  element `x` of the state `S` of the mirror to the cochain pairing `x` with the complementary
  state `Sᶜ` of `D` by the Frobenius pairing of circle tensors, times the sign
  `(-1)^(i n) * Finset.dualCubeSign S n₋(D)`.
* `TauCeti.OrientedPDCode.khovanovComplexMirrorIso_inv_f_apply`: the inverse isomorphism sends a
  cochain `f` to the element whose state-`S` component pairs with `y` in the state `Sᶜ` of `D`
  to `f(y)`, times the same sign.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.3.
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

end TauCeti.OrientedPDCode
