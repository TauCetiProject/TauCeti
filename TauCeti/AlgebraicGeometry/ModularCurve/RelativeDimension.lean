/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy.FourTorsion
public import TauCeti.AlgebraicGeometry.ModularCurve.YOne
import TauCeti.AlgebraicGeometry.ModularCurve.Rigidifier.LevelThree
import TauCeti.AlgebraicGeometry.ModularCurve.Simultaneous.Projections
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Descent

/-!
# Relative dimension of the fine modular curve `Y₁(N)`

For `N ≥ 4` invertible on a base scheme `B`, the fine moduli scheme `Y₁(N)` (`EllObj.yOne B N`) is
already known to be smooth over `B` (`EllObj.smooth_yOne_structureMap`), by exhibiting it as a
retract over `B` of a finite étale cover of the two-dimensional universal Tate normal form base
`B × Spec ℤ[A, B][Δ⁻¹]`. Because a retract of a smooth scheme of relative dimension `2` need not
have relative dimension `1`, that argument does not determine the dimension of the fibres of
`Y₁(N)`.

This file proves that `Y₁(N)` is smooth of relative dimension `1` over `B`
(`EllObj.smoothOfRelativeDimension_one_yOne_structureMap`), by comparing `[Γ₁(N)]` with explicit
one-dimensional rigidifiers over open subsets covering `B`:

1. **Transfer along a rigidifier.** If `𝒫` and `𝒬` are representable, relatively representable,
   étale moduli problems over `Ell/B`, with `𝒬` surjective over `Ell/B`, then the simultaneous
   moduli scheme `𝕄(𝒬, 𝒫)` is étale and surjective over `𝕄(𝒫)` and étale over `𝕄(𝒬)`. Once `𝕄(𝒫)`
   is smooth over `B` and `𝕄(𝒬)` is smooth of relative dimension `n` over `B`, descent of smooth
   relative dimension along étale surjective morphisms on the source
   (`AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_etale_of_surjective`) shows that `𝕄(𝒫)`
   is smooth of relative dimension `n` over `B`
   (`ModuliProblem.RelRepData.smoothOfRelativeDimension_of_representableBy`).
2. **Explicit presentation of `Y₁(4)`.** On an elliptic Tate normal form `Y² + AXY + BY = X³ + BX²`
   over an arbitrary commutative ring, `4 • (0, 0) = 0` holds if and only if `A = 1`
   (`WeierstrassCurve.tateNormalForm_projModelMulBy_four_eq_projModelZero_iff`), while `(0, 0)`,
   `2 • (0, 0)` and `3 • (0, 0)` miss the zero section everywhere. Consequently `Y₁(4)` over `ℤ` is
   isomorphic to `Spec ℤ[B, (B(1 - 16B))⁻¹]` (`UniversalTate.yOneFourIso`), and `EllObj.yOne B 4` is
   smooth of relative dimension `1` over every scheme `B` without any invertibility assumption
   (`EllObj.smoothOfRelativeDimension_one_yOne_four_structureMap`).
3. **Covering `B` by `B[1/2]` and `B[1/3]`.** At every point of `B`, either `2` (and hence `4`) or
   `3` is invertible in the residue field. Over `B[1/2]`, comparing `[Γ₁(N)]` with the étale
   surjective rigidifier `[Γ₁(4)]` transfers relative dimension `1` from `Y₁(4)` to `Y₁(N)`. Over
   `B[1/3]`, comparing `[Γ₁(N)]` with `[Γ(3)]`, represented by `EllObj.universalLevelThree` of
   relative dimension `1` (`EllObj.smoothOfRelativeDimension_universalLevelThree_structureMap`),
   transfers relative dimension `1` to `Y₁(N)`. Since `EllObj.yOne B N` commutes with base change
   in `B` (`EllObj.isPullback_yOneBaseMap`), target-locality concludes the proof.

## Main definitions

* `TauCeti.AlgebraicGeometry.UniversalTate.yOneFourIso`: the isomorphism
  `Y₁(4) ≅ Spec ℤ[B, (B(1 - 16B))⁻¹]`.
* `TauCeti.AlgebraicGeometry.EllObj.yOneBaseIsoProd`: for every `N ≠ 0`, the identification of the
  base of `EllObj.yOne B N` with `B × Y₁(N)`.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.smoothOfRelativeDimension_of_representableBy`:
  smooth relative dimension transfers from an étale surjective rigidifier to any smooth
  representable étale moduli problem.
* `TauCeti.AlgebraicGeometry.EllObj.isPullback_yOneBaseMap`: the base of `EllObj.yOne B N` commutes
  with arbitrary base change `B' ⟶ B`.
* `TauCeti.AlgebraicGeometry.EllObj.smoothOfRelativeDimension_one_yOne_four_structureMap`: `Y₁(4)`
  is smooth of relative dimension `1` over every base scheme `B`.
* `TauCeti.AlgebraicGeometry.EllObj.smoothOfRelativeDimension_one_yOne_structureMap`: for `N ≥ 4`
  invertible on `B`, `Y₁(N)` is smooth of relative dimension `1` over `B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2, 4.7 and 4.12.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
* D. Loeffler, *Modular Curves*, lecture notes, §3.3 and §3.8.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj WeierstrassCurve

namespace TauCeti.AlgebraicGeometry

/-! ### Rigidifier transfer of smooth relative dimension -/

namespace ModuliProblem.RelRepData

variable {B : Scheme.{u}} {n : ℕ}

/-- **Transfer of smooth relative dimension along a rigidifier.** Let `𝒫` and `𝒬` be moduli
problems over `Ell/B` represented by `U` and `V`, both relatively representable and étale over
`Ell/B`, with `𝒬` also surjective over `Ell/B`. If the base of `U` is smooth over `B` and the base
of `V` is smooth of relative dimension `n` over `B`, then the base of `U` is smooth of relative
dimension `n` over `B`: the simultaneous moduli scheme `𝕄(𝒬, 𝒫)` maps étale-surjectively to `U`
and étale to `V`. -/
theorem smoothOfRelativeDimension_of_representableBy {P Q : ModuliProblem B} {U V : EllObj B}
    (RP : P.RepresentableBy U) (RQ : Q.RepresentableBy V)
    (DP : P.RelRepData) (DQ : Q.RelRepData)
    (heP : DP.HasProperty @Etale) (heQ : DQ.HasProperty @Etale)
    (hsQ : DQ.HasProperty @Surjective)
    [Smooth U.structureMap] [SmoothOfRelativeDimension n V.structureMap] :
    SmoothOfRelativeDimension n U.structureMap := by
  let S := DQ.tensorRepresentableBy RP
  let a₁ := U.baseChangeFunctorHom (DQ.rep U)
  let a₂ := RQ.homEquiv.symm (S.homEquiv (𝟙 _)).1
  have : Etale a₁.base := by
    rw [EllObj.baseChangeFunctorHom_base]
    exact DQ.hasProperty_iff.mp heQ U
  have : Surjective a₁.base := by
    rw [EllObj.baseChangeFunctorHom_base]
    exact DQ.hasProperty_iff.mp hsQ U
  have ha₂ : RQ.homEquiv a₂ = (S.homEquiv (𝟙 _)).1 := RQ.homEquiv.apply_symm_apply _
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Etale a₂.base := DP.mem_base_of_forget_snd RQ S a₂ ha₂ (DP.hasProperty_iff.mp heP V)
  have hW : SmoothOfRelativeDimension (0 + n) (a₂.base ≫ V.structureMap) := inferInstance
  have : SmoothOfRelativeDimension n (a₁.base ≫ U.structureMap) := by
    rw [a₁.base_structureMap, ← a₂.base_structureMap]
    simpa only [Nat.zero_add] using hW
  exact SmoothOfRelativeDimension.of_comp_of_etale_of_surjective a₁.base U.structureMap

/-- Two representable, relatively representable, étale and surjective moduli problems over `Ell/B`
whose bases are smooth over `B` have bases of the same smooth relative dimension over `B`. -/
theorem smoothOfRelativeDimension_iff_of_representableBy {P Q : ModuliProblem B} {U V : EllObj B}
    (RP : P.RepresentableBy U) (RQ : Q.RepresentableBy V)
    (DP : P.RelRepData) (DQ : Q.RelRepData)
    (heP : DP.HasProperty @Etale) (hsP : DP.HasProperty @Surjective)
    (heQ : DQ.HasProperty @Etale) (hsQ : DQ.HasProperty @Surjective)
    [Smooth U.structureMap] [Smooth V.structureMap] :
    SmoothOfRelativeDimension n U.structureMap ↔ SmoothOfRelativeDimension n V.structureMap :=
  ⟨fun _ ↦ smoothOfRelativeDimension_of_representableBy RQ RP DQ DP heQ heP hsP,
    fun _ ↦ smoothOfRelativeDimension_of_representableBy RP RQ DP DQ heP heQ hsQ⟩

end ModuliProblem.RelRepData

/-! ### Explicit presentation of `Y₁(4)` -/

namespace UniversalTate

open UniversalTate

private theorem pointHom_pow_left (k : ℕ) :
    (pointHom.{u} ^ k).left =
      UniversalTate.point ≫ curveULift.projModelMulBy k ≫
        (toEllipticCurveGeomIso curveULift).inv := by
  have hk : (pointHom.{u} ^ k).left = pointHom.{u}.left ≫ (curveGeom.mulBy k).left := by
    rw [← Over.comp_left, EllipticCurveGeom.comp_mulBy, zpow_natCast]
  rw [hk, pointHom_left, Category.assoc, projModelMulBy_eq]
  simp

/-- On the universal Tate normal form, `(0, 0)`, `2 • (0, 0)` and `3 • (0, 0)` miss the zero
section at every point of the base, so `exactOrderOpens 4` is the whole base. -/
@[simp]
theorem exactOrderOpens_four : exactOrderOpens.{u} 4 = ⊤ := by
  rw [eq_top_iff]
  intro t _
  rw [mem_exactOrderOpens_iff]
  intro k hk0 hk4 heq
  rw [pointHom_pow_left] at heq
  have hzero : curveGeom.{u}.zero =
      curveULift.projModelZero ≫ (toEllipticCurveGeomIso curveULift).inv := by
    simp [← zero_toEllipticCurveGeomIso_hom]
  rw [hzero, ← Category.assoc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at heq
  have heq' : (UniversalTate.point ≫ curveULift.projModelMulBy k) t =
      curveULift.projModelZero t := by
    have h := congrArg (toEllipticCurveGeomIso curveULift.{u}).hom heq
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.inv_hom_id] at h
    simpa using h
  interval_cases k <;> simp only [Nat.cast_one, Nat.cast_ofNat] at heq'
  · rw [show curveULift.{u}.projModelMulBy 1 = 𝟙 _ by simp [projModelMulBy_eq],
      Category.comp_id] at heq'
    exact UniversalTate.point_ne_projModelZero t heq'
  · exact UniversalTate.point_projModelMulBy_two_ne_projModelZero t heq'
  · exact UniversalTate.point_projModelMulBy_three_ne_projModelZero t heq'

/-- The open subset `yOneOpens 4` cutting `Y₁(4)` out of the `4`-torsion locus is the whole
`4`-torsion locus. -/
@[simp]
theorem yOneOpens_four : yOneOpens.{u} 4 = ⊤ := by
  ext z
  simp

/-- The open immersion `Y₁(4) ⟶ torsionLocus 4` is an isomorphism. -/
instance isIso_yOneOpens_four_ι : IsIso (yOneOpens.{u} 4).ι := by
  rw [yOneOpens_four, ← Scheme.topIso_hom]
  infer_instance

/-- Over `ℤ`, the immersion `Y₁(4) ⟶ Spec ℤ[A, B][Δ⁻¹]` is a closed immersion. -/
instance isClosedImmersion_yOneι_four : IsClosedImmersion (yOneι.{u} 4) := by
  rw [yOneι_def]
  infer_instance

/-- The scheme `Y₁(4)` over `ℤ` is affine. -/
instance isAffine_yOne_four : IsAffine (yOne.{u} 4) :=
  isAffine_of_isAffineHom (yOneι.{u} 4)

-- Along `Spec φ`, the `4`-th multiple of `(0, 0)` vanishes if and only if `φ` maps `A` to `1`.
private theorem specMap_comp_pointHom_pow_four_eq_zero_iff {R : Type u} [CommRing R]
    (φ : ULift.{u} UniversalTate.Ring →+* R) :
    Spec.map (CommRingCat.ofHom φ) ≫ (pointHom.{u} ^ 4).left =
        Spec.map (CommRingCat.ofHom φ) ≫ curveGeom.zero ↔
      φ curveULift.a₁ = 1 := by
  have hzero : curveGeom.{u}.zero =
      curveULift.projModelZero ≫ (toEllipticCurveGeomIso curveULift).inv := by
    simp [← zero_toEllipticCurveGeomIso_hom]
  rw [pointHom_pow_left, Nat.cast_ofNat, hzero]
  simp only [← Category.assoc, cancel_mono (toEllipticCurveGeomIso curveULift).inv]
  have hbc := curveULift.isPullback_projModelBaseChange φ
  rw [point_def, ← curveULift.projModelAffinePoint_projModelBaseChange φ, Category.assoc,
    ← curveULift.projModelMulBy_projModelBaseChange φ 4, ← Category.assoc,
    ← curveULift.projModelZero_projModelBaseChange φ]
  have hext : ((curveULift.map φ).projModelAffinePoint (equation_curveULift_zero.map φ) ≫
        (curveULift.map φ).projModelMulBy 4) ≫ curveULift.projModelBaseChange φ =
      (curveULift.map φ).projModelZero ≫ curveULift.projModelBaseChange φ ↔
      (curveULift.map φ).projModelAffinePoint (equation_curveULift_zero.map φ) ≫
        (curveULift.map φ).projModelMulBy 4 = (curveULift.map φ).projModelZero :=
    ⟨fun h ↦ hbc.hom_ext h (by simp), fun h ↦ by rw [h]⟩
  rw [hext]
  -- Rewrite `curveULift.map φ` to `tateNormalForm (φ a₁) (φ a₃)` so the 4-torsion criterion applies
  have key {W : WeierstrassCurve R} [W.IsElliptic]
      (hW : W = tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃))
      (h₀ : W.toAffine.Equation (φ 0) (φ 0)) :
      W.projModelAffinePoint h₀ ≫ W.projModelMulBy 4 = W.projModelZero ↔ φ curveULift.a₁ = 1 := by
    subst hW
    have hpt : (tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)).projModelAffinePoint h₀ =
        (tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)).projModelAffinePoint
          (equation_tateNormalForm_zero _ _) :=
      (projModelAffinePoint_inj h₀).mpr ⟨map_zero φ, map_zero φ⟩
    rw [hpt]
    exact tateNormalForm_projModelMulBy_four_eq_projModelZero_iff
  exact key (map_curveULift φ) (equation_curveULift_zero.map φ)

/-- The ring homomorphism `ULift ℤ[A, B][Δ⁻¹] →+* ULift ℤ[B, (B(1 - 16B))⁻¹]` specializing `A` to
`1` and `B` to `param`. -/
noncomputable def toUniversalGammaOneFourULift :
    ULift.{u} UniversalTate.Ring →+* ULift.{u} UniversalGammaOneFour.Ring :=
  ULift.ringEquiv.symm.toRingHom.comp
    (UniversalGammaOneFour.toUniversalTate.comp ULift.ringEquiv.toRingHom)

/-- `toUniversalGammaOneFourULift` maps the coefficient `a₁` of `curveULift` to `1`. -/
theorem toUniversalGammaOneFourULift_a₁ :
    toUniversalGammaOneFourULift.{u} curveULift.a₁ = 1 := by
  ext
  simp [toUniversalGammaOneFourULift, ULift.ringEquiv, WeierstrassCurve.baseChange]

/-- `toUniversalGammaOneFourULift` maps the coefficient `a₃` of `curveULift` to `param`. -/
theorem toUniversalGammaOneFourULift_a₃ :
    toUniversalGammaOneFourULift.{u} curveULift.a₃ = .up UniversalGammaOneFour.param := by
  ext
  simp [toUniversalGammaOneFourULift, ULift.ringEquiv, WeierstrassCurve.baseChange]

-- Any morphism from an affine scheme `X` to `Spec ℤ[A, B][Δ⁻¹]` killing `4 • (0, 0)` factors
-- through `Spec ℤ[B, (B(1 - 16B))⁻¹]`.
private theorem exists_toSpec_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of (ULift.{u} UniversalTate.Ring)))
    (hf : f ≫ (pointHom.{u} ^ 4).left = f ≫ curveGeom.zero) :
    ∃ hom : X ⟶ Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)),
      hom ≫ Spec.map (CommRingCat.ofHom toUniversalGammaOneFourULift) = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f)
  have hN : Spec.map φ ≫ (pointHom.{u} ^ 4).left = Spec.map φ ≫ curveGeom.zero := by
    rw [hφ, Category.assoc, hf, Category.assoc]
  have ha₁ : φ.hom curveULift.a₁ = 1 :=
    (specMap_comp_pointHom_pow_four_eq_zero_iff φ.hom).mp hN
  have hmap : curveULift.map φ.hom = tateNormalForm 1 (φ.hom curveULift.a₃) := by
    rw [map_curveULift, ha₁]
  have hΔ : IsUnit (tateNormalForm 1 (φ.hom curveULift.a₃)).Δ :=
    hmap ▸ (curveULift.map φ.hom).isUnit_Δ
  let ψ : CommRingCat.of (ULift.{u} UniversalGammaOneFour.Ring) ⟶ Γ(X, ⊤) :=
    CommRingCat.ofHom ((UniversalGammaOneFour.lift hΔ).comp ULift.ringEquiv.toRingHom)
  have hφlift : φ.hom.comp (ULift.ringEquiv.symm : _ ≃+* ULift.{u} _).toRingHom =
      UniversalTate.lift hΔ :=
    UniversalTate.eq_lift hΔ (by rw [← map_map, ← curveULift_eq, hmap])
  have hcomp : CommRingCat.ofHom toUniversalGammaOneFourULift ≫ ψ = φ := by
    ext x
    change (UniversalGammaOneFour.lift hΔ) (UniversalGammaOneFour.toUniversalTate x.down) =
      φ.hom x
    exact (RingHom.congr_fun (UniversalGammaOneFour.lift_comp_toUniversalTate hΔ) x.down).trans
      (RingHom.congr_fun hφlift x.down).symm
  refine ⟨X.isoSpec.hom ≫ Spec.map ψ, ?_⟩
  rw [Category.assoc, ← Spec.map_comp, hcomp, hφ, Iso.hom_inv_id_assoc]

private theorem exists_yOneFourToSpec :
    ∃ hom : yOne.{u} 4 ⟶ Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)),
      hom ≫ Spec.map (CommRingCat.ofHom toUniversalGammaOneFourULift) = yOneι.{u} 4 :=
  exists_toSpec_of_isAffine (yOneι.{u} 4)
    (((exists_comp_yOneι_eq_iff (yOneι.{u} 4) 4).mp ⟨𝟙 _, Category.id_comp _⟩).1)

private theorem exists_specToYOneFour :
    ∃ inv : Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)) ⟶ yOne.{u} 4,
      inv ≫ yOneι 4 = Spec.map (CommRingCat.ofHom toUniversalGammaOneFourULift) :=
  (exists_comp_yOneι_eq_iff _ 4).mpr
    ⟨(specMap_comp_pointHom_pow_four_eq_zero_iff _).mpr toUniversalGammaOneFourULift_a₁,
      fun _ ↦ by simp⟩

/-- **`Y₁(4)` over `ℤ` is `Spec ℤ[B, (B(1 - 16B))⁻¹]`.** -/
noncomputable def yOneFourIso :
    yOne.{u} 4 ≅ Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)) where
  hom := exists_yOneFourToSpec.choose
  inv := exists_specToYOneFour.choose
  hom_inv_id := by
    refine (cancel_mono (yOneι.{u} 4)).mp ?_
    rw [Category.assoc, exists_specToYOneFour.choose_spec, exists_yOneFourToSpec.choose_spec,
      Category.id_comp]
  inv_hom_id := by
    obtain ⟨χ, hχ⟩ := Spec.map_surjective
      (exists_specToYOneFour.{u}.choose ≫ exists_yOneFourToSpec.choose)
    have hχj : Spec.map (CommRingCat.ofHom toUniversalGammaOneFourULift ≫ χ) =
        Spec.map (CommRingCat.ofHom toUniversalGammaOneFourULift) := by
      rw [Spec.map_comp, hχ, Category.assoc, exists_yOneFourToSpec.choose_spec,
        exists_specToYOneFour.choose_spec]
    have hχπ : χ.hom.comp toUniversalGammaOneFourULift = toUniversalGammaOneFourULift :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective hχj)
    have hparam : χ.hom (.up UniversalGammaOneFour.param) = .up UniversalGammaOneFour.param := by
      have h := RingHom.congr_fun hχπ curveULift.a₃
      rwa [RingHom.comp_apply, toUniversalGammaOneFourULift_a₃] at h
    have hχid : χ = 𝟙 _ := by
      refine CommRingCat.hom_ext ?_
      have h₀ : (ULift.ringEquiv.toRingHom.comp χ.hom).comp ULift.ringEquiv.symm.toRingHom =
          RingHom.id UniversalGammaOneFour.Ring := by
        ext
        exact congrArg ULift.down hparam
      ext x
      simpa [ULift.ringEquiv] using RingHom.congr_fun h₀ x.down
    rw [← hχ, hχid, Spec.map_id]

/-- The base `Spec ℤ[B, (B(1 - 16B))⁻¹]` is smooth of relative dimension `1` over `Spec ℤ`. -/
instance smoothOfRelativeDimension_one_terminal_from_universalGammaOneFour :
    SmoothOfRelativeDimension 1
      (terminal.from (Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)))) := by
  let _ : Algebra (ULift.{u} ℤ) ℤ := ULift.algebra' ℤ ℤ
  let _ : Algebra (ULift.{u} ℤ) (ULift.{u} UniversalGammaOneFour.Ring) :=
    ULift.algebra' ℤ (ULift.{u} UniversalGammaOneFour.Ring)
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (ULift.{u} ℤ) ℤ :=
    .of_algebraMap_bijective ULift.ringEquiv.bijective
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 ℤ
      (ULift.{u} UniversalGammaOneFour.Ring) :=
    .of_algEquiv 1 (AlgEquiv.ofRingEquiv (f := ULift.ringEquiv.symm) fun _ : ℤ ↦ rfl)
  have h01 : Algebra.IsStandardSmoothOfRelativeDimension (0 + 1) (ULift.{u} ℤ)
      (ULift.{u} UniversalGammaOneFour.Ring) :=
    .trans 0 1 (ULift.{u} ℤ) ℤ (ULift.{u} UniversalGammaOneFour.Ring)
  have h1 : Algebra.IsStandardSmoothOfRelativeDimension 1 (ULift.{u} ℤ)
      (ULift.{u} UniversalGammaOneFour.Ring) := by
    simpa only [Nat.zero_add] using h01
  have hf : (algebraMap (ULift.{u} ℤ) (ULift.{u} UniversalGammaOneFour.Ring))
      |>.IsStandardSmoothOfRelativeDimension 1 :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr h1
  have : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (ULift.{u} UniversalGammaOneFour.Ring)))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hf)
  have e := specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal
  have : SmoothOfRelativeDimension (1 + 0) (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (ULift.{u} UniversalGammaOneFour.Ring))) ≫ e.hom) :=
    inferInstance
  rwa [terminal.hom_ext (terminal.from _) (Spec.map (CommRingCat.ofHom
    (algebraMap (ULift.{u} ℤ) (ULift.{u} UniversalGammaOneFour.Ring))) ≫ e.hom)]

/-- `Y₁(4)` over `ℤ` is smooth of relative dimension `1` over `Spec ℤ`. -/
instance smoothOfRelativeDimension_one_terminal_from_yOne_four :
    SmoothOfRelativeDimension 1 (terminal.from (yOne.{u} 4)) := by
  have h : SmoothOfRelativeDimension (0 + 1)
      (yOneFourIso.{u}.hom ≫
        terminal.from (Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)))) :=
    inferInstance
  rw [terminal.hom_ext (terminal.from (yOne.{u} 4))
    (yOneFourIso.{u}.hom ≫ terminal.from _)]
  simpa only [Nat.zero_add] using h

end UniversalTate

/-! ### Base change of `EllObj.yOne B N` and smoothness of relative dimension `1` -/

namespace EllObj

open UniversalTate EllipticCurveGeom

section BaseChange

variable (B : Scheme.{u}) (N : ℕ) [NeZero N]

-- On the base change of `universalTate B` along `t`, the pullback of `(0, 0)` has naive exact
-- order `N` if and only if `t ≫ prod.snd` factors through `UniversalTate.yOne N`.
private theorem isOfNaiveExactOrder_universalTatePoint_iff {S : Scheme.{u}}
    (t : S ⟶ B ⨯ Spec (.of (ULift.{u} UniversalTate.Ring))) :
    (universalTate B).curve.IsOfNaiveExactOrder
        (toUnit (Over.mk t) ≫ universalTatePoint B) N ↔
      ∃ h : S ⟶ UniversalTate.yOne.{u} N, h ≫ UniversalTate.yOneι N = t ≫ prod.snd := by
  let hbc := (universalTate B).curve.isPullback_baseChange t
  have hbc0 : ((universalTate B).curve.baseChange t).zero ≫
      ((universalTate B).curve.baseChangeIso t).hom ≫ pullback.fst _ _ =
      t ≫ (universalTate B).curve.zero := by simp
  let P_S := pointsPullback hbc hbc0 (universalTatePoint B)
  have hPS : pointsBaseChangeEquiv hbc hbc0 P_S = toUnit (Over.mk t) ≫ universalTatePoint B := by
    ext1
    simp [P_S]
  rw [← hPS, isOfNaiveExactOrder_pointsBaseChangeEquiv_iff hbc hbc0]
  have hg : IsPullback
      (((universalTate B).curve.baseChangeIso t).hom ≫ pullback.fst _ _ ≫
        prodCurveProj B curveGeom)
      ((universalTate B).curve.baseChange t).structureMap curveGeom.structureMap
      (t ≫ prod.snd) :=
    hbc.paste_horiz (isPullback_prodCurveProj B curveGeom)
  have h₀ : ((universalTate B).curve.baseChange t).zero ≫
      (((universalTate B).curve.baseChangeIso t).hom ≫ pullback.fst _ _ ≫
        prodCurveProj B curveGeom) = (t ≫ prod.snd) ≫ curveGeom.zero := by
    rw [reassoc_of% hbc0, Category.assoc, zero_prodCurveProj]
  have hP : P_S = pointsPullback hg h₀ pointHom := by
    refine (eq_pointsPullback_iff hg h₀).mpr ?_
    rw [← Category.assoc ((universalTate B).curve.baseChangeIso t).hom,
      ← Category.assoc P_S.left, pointsPullback_left_comp, Category.assoc,
      universalTatePoint_def, prodCurvePoint_left_prodCurveProj, Category.assoc]
    exact rfl
  have hpow : P_S ^ N = 1 ↔
      (t ≫ prod.snd) ≫ (pointHom ^ N).left = (t ≫ prod.snd) ≫ curveGeom.zero := by
    rw [hP, ← map_pow]
    simpa [Over.OverMorphism.ext_iff, hom_one_left] using
      comp_pointsPullback_left_eq_comp_zero_iff hg h₀ (pointHom ^ N) (𝟙 S)
  have happ (k : ℕ) (s : S) : (P_S ^ k).left s =
        ((universalTate B).curve.baseChange t).zero s ↔
      (pointHom ^ k).left ((t ≫ prod.snd) s) = curveGeom.zero ((t ≫ prod.snd) s) := by
    rw [hP, ← map_pow]
    exact pointsPullback_left_apply_eq_zero_iff hg h₀ (pointHom ^ k) s
  rw [isOfNaiveExactOrder_iff_forall_lt, exists_comp_yOneι_eq_iff, hpow]
  refine and_congr_right' ⟨fun h s ↦ mem_exactOrderOpens_iff.mpr fun k hk0 hkN ↦
    mt (happ k s).mpr ((isEmpty_equalizer_one_iff _).mp (h k hk0 hkN) s), fun h k hk0 hkN ↦
    (isEmpty_equalizer_one_iff _).mpr fun s ↦
      mt (happ k s).mp (mem_exactOrderOpens_iff.mp (h s) k hk0 hkN)⟩

-- Morphisms `S ⟶ B × Spec ℤ[A, B][Δ⁻¹]` factor through `(yOne B N).base` if and only if their
-- second projection factors through `UniversalTate.yOne N`.
private theorem exists_comp_yOneι_base_iff {S : Scheme.{u}}
    (t : S ⟶ B ⨯ Spec (.of (ULift.{u} UniversalTate.Ring))) :
    (∃ l : S ⟶ (yOne B N).base, l ≫ (yOneι B N).base = t) ↔
      ∃ h : S ⟶ UniversalTate.yOne.{u} N, h ≫ UniversalTate.yOneι N = t ≫ prod.snd := by
  simp only [yOneι_base]
  exact (exists_lift_naiveExactOrderPreimageι_iff N (universalTatePoint B)
    (Z := Over.mk t) (x := toUnit (Over.mk t) ≫ universalTatePoint B) rfl).trans
    (isOfNaiveExactOrder_universalTatePoint_iff B N t)

/-- The canonical projection `(yOne B N).base ⟶ UniversalTate.yOne N`. -/
noncomputable def yOneSnd : (yOne B N).base ⟶ UniversalTate.yOne.{u} N :=
  ((exists_comp_yOneι_base_iff B N (yOneι B N).base).mp ⟨𝟙 _, Category.id_comp _⟩).choose

/-- The projection `yOneSnd B N` commutes with the inclusions into the base of the universal Tate
normal form. -/
@[reassoc (attr := simp)]
theorem yOneSnd_yOneι :
    yOneSnd B N ≫ UniversalTate.yOneι N = (yOneι B N).base ≫ prod.snd :=
  ((exists_comp_yOneι_base_iff B N (yOneι B N).base).mp ⟨𝟙 _, Category.id_comp _⟩).choose_spec

private theorem exists_prodToYOne :
    ∃ inv : B ⨯ UniversalTate.yOne.{u} N ⟶ (yOne B N).base,
      inv ≫ (yOneι B N).base = prod.map (𝟙 B) (UniversalTate.yOneι.{u} N) :=
  (exists_comp_yOneι_base_iff B N
    (prod.map (𝟙 B) (UniversalTate.yOneι.{u} N))).mpr ⟨prod.snd, by simp⟩

/-- **The base of `EllObj.yOne B N` is `B × Y₁(N)`.** -/
noncomputable def yOneBaseIsoProd : (yOne B N).base ≅ B ⨯ UniversalTate.yOne.{u} N where
  hom := prod.lift (yOne B N).structureMap (yOneSnd B N)
  inv := (exists_prodToYOne B N).choose
  hom_inv_id := by
    refine (cancel_mono (yOneι B N).base).mp ?_
    rw [Category.assoc, (exists_prodToYOne B N).choose_spec, Category.id_comp]
    refine prod.hom_ext ?_ ?_ <;> simp [yOne_structureMap]
  inv_hom_id := by
    have hinv := (exists_prodToYOne B N).choose_spec
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.lift_fst, yOne_structureMap, reassoc_of% hinv, prod.map_fst,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, prod.lift_snd, Category.id_comp]
      refine (cancel_mono (UniversalTate.yOneι.{u} N)).mp ?_
      rw [Category.assoc, yOneSnd_yOneι, reassoc_of% hinv, prod.map_snd]

/-- Under `yOneBaseIsoProd`, the first projection is `(yOne B N).structureMap`. -/
@[reassoc (attr := simp)]
theorem yOneBaseIsoProd_hom_fst :
    (yOneBaseIsoProd B N).hom ≫ prod.fst = (yOne B N).structureMap :=
  prod.lift_fst _ _

/-- Under `(yOneBaseIsoProd B N).inv`, the structure morphism of `yOne B N` is the first
projection. -/
@[reassoc]
theorem yOneBaseIsoProd_inv_structureMap :
    (yOneBaseIsoProd B N).inv ≫ (yOne B N).structureMap = prod.fst := by
  rw [← yOneBaseIsoProd_hom_fst, Iso.inv_hom_id_assoc]

/-- For a morphism of base schemes `g : B' ⟶ B`, the induced morphism
`(yOne B' N).base ⟶ (yOne B N).base`. -/
noncomputable def yOneBaseMap {B' B : Scheme.{u}} (g : B' ⟶ B) (N : ℕ) [NeZero N] :
    (yOne B' N).base ⟶ (yOne B N).base :=
  (yOneBaseIsoProd B' N).hom ≫ prod.map g (𝟙 _) ≫ (yOneBaseIsoProd B N).inv

/-- **The base of `EllObj.yOne B N` commutes with arbitrary base change `g : B' ⟶ B`.** -/
theorem isPullback_yOneBaseMap {B' B : Scheme.{u}} (g : B' ⟶ B) (N : ℕ) [NeZero N] :
    IsPullback (yOneBaseMap g N) (yOne B' N).structureMap (yOne B N).structureMap g := by
  have hprod := (IsPullback.of_prod_fst_with_id g (UniversalTate.yOne.{u} N)).flip
  refine hprod.of_iso' (yOneBaseIsoProd B' N) (yOneBaseIsoProd B N) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_ <;> simp [yOneBaseMap]

/-- **`Y₁(4)` is smooth of relative dimension `1` over every base scheme `B`.** -/
instance smoothOfRelativeDimension_one_yOne_four_structureMap (B : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (yOne B 4).structureMap := by
  have hfst : SmoothOfRelativeDimension 1 (prod.fst : B ⨯ UniversalTate.yOne.{u} 4 ⟶ B) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' _ _).flip inferInstance
  have h : SmoothOfRelativeDimension (0 + 1)
      ((yOneBaseIsoProd B 4).hom ≫ (prod.fst : B ⨯ UniversalTate.yOne.{u} 4 ⟶ B)) :=
    inferInstance
  rw [← yOneBaseIsoProd_hom_fst]
  simpa only [Nat.zero_add] using h

end BaseChange

/-! ### Relative dimension of `Y₁(N)` for `N ≥ 4` -/

private theorem natCast_residueField_basicOpen_ne_zero (B : Scheme.{u}) (m : ℕ)
    (x : B.basicOpen (m : Γ(B, ⊤))) :
    (m : (B.basicOpen (m : Γ(B, ⊤))).toScheme.residueField x) ≠ 0 := by
  let U := B.basicOpen (m : Γ(B, ⊤))
  have hx : U.ι x ∈ U := by simpa only [Scheme.Opens.ι_apply] using x.2
  refine Scheme.Hom.natCast_residueField_ne_zero U.ι ?_
  simpa only [map_natCast] using (B.evaluation_ne_zero_iff_mem_basicOpen (U.ι x) trivial _).mpr hx

private theorem smoothOfRelativeDimension_restrict_yOne_of_open (B : Scheme.{u}) (U : B.Opens)
    (N : ℕ) [NeZero N] (hU : SmoothOfRelativeDimension 1 (yOne U.toScheme N).structureMap) :
    SmoothOfRelativeDimension 1 ((yOne B N).structureMap ∣_ U) := by
  let h₁ := (isPullback_morphismRestrict (yOne B N).structureMap U).flip
  let h₂ := isPullback_yOneBaseMap U.ι N
  let e : ↑((yOne B N).structureMap ⁻¹ᵁ U) ≅ (yOne U.toScheme N).base :=
    h₁.isoPullback ≪≫ h₂.isoPullback.symm
  have he : ((yOne B N).structureMap ∣_ U) = e.hom ≫ (yOne U.toScheme N).structureMap := by
    simp [e]
  have h : SmoothOfRelativeDimension (0 + 1) (e.hom ≫ (yOne U.toScheme N).structureMap) :=
    inferInstance
  rw [he]
  simpa only [Nat.zero_add] using h

-- Over `D(2) ⊆ B`, `4` is invertible, so `[Γ₁(4)]` transfers relative dimension `1` to `Y₁(N)`.
private theorem smoothOfRelativeDimension_one_yOne_restrict_basicOpen_two (B : Scheme.{u})
    (N : ℕ) [NeZero N] (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (h4 : 4 ≤ N) :
    SmoothOfRelativeDimension 1 ((yOne B N).structureMap ∣_ B.basicOpen (2 : Γ(B, ⊤))) := by
  let U : B.Opens := B.basicOpen (2 : Γ(B, ⊤))
  have hNU (x : U.toScheme) : (N : U.toScheme.residueField x) ≠ 0 :=
    Scheme.Hom.natCast_residueField_ne_zero U.ι (hN _)
  have h4U (x : U.toScheme) : (4 : U.toScheme.residueField x) ≠ 0 := by
    have hx2 := natCast_residueField_basicOpen_ne_zero B 2 x
    rw [show (4 : U.toScheme.residueField x) = (2 : _) * 2 by norm_num]
    exact mul_ne_zero hx2 hx2
  have : Smooth (yOne U.toScheme N).structureMap :=
    smooth_yOne_structureMap U.toScheme N hNU h4
  exact smoothOfRelativeDimension_restrict_yOne_of_open B U N <|
    ModuliProblem.RelRepData.smoothOfRelativeDimension_of_representableBy
      (ModuliProblem.gammaOneNaiveRepresentableBy h4)
      (ModuliProblem.gammaOneNaiveRepresentableBy (N := 4) le_rfl)
      ModuliProblem.gammaOneNaiveRelRepData ModuliProblem.gammaOneNaiveRelRepData
      (ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData hNU)
      (ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData h4U)
      (ModuliProblem.hasProperty_surjective_gammaOneNaiveRelRepData h4U)

-- Over `D(3) ⊆ B`, `3` is invertible, so `[Γ(3)]` transfers relative dimension `1` to `Y₁(N)`.
private theorem smoothOfRelativeDimension_one_yOne_restrict_basicOpen_three (B : Scheme.{u})
    (N : ℕ) [NeZero N] (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (h4 : 4 ≤ N) :
    SmoothOfRelativeDimension 1 ((yOne B N).structureMap ∣_ B.basicOpen (3 : Γ(B, ⊤))) := by
  let U : B.Opens := B.basicOpen (3 : Γ(B, ⊤))
  have hNU (x : U.toScheme) : (N : U.toScheme.residueField x) ≠ 0 :=
    Scheme.Hom.natCast_residueField_ne_zero U.ι (hN _)
  have h3U (x : U.toScheme) : (3 : U.toScheme.residueField x) ≠ 0 :=
    natCast_residueField_basicOpen_ne_zero B 3 x
  have : Smooth (yOne U.toScheme N).structureMap :=
    smooth_yOne_structureMap U.toScheme N hNU h4
  exact smoothOfRelativeDimension_restrict_yOne_of_open B U N <|
    ModuliProblem.RelRepData.smoothOfRelativeDimension_of_representableBy
      (ModuliProblem.gammaOneNaiveRepresentableBy h4)
      (ModuliProblem.gammaNaiveThreeRepresentableBy U.toScheme)
      ModuliProblem.gammaOneNaiveRelRepData ModuliProblem.gammaNaiveRelRepData
      (ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData hNU)
      (ModuliProblem.hasProperty_etale_gammaNaiveRelRepData h3U)
      (ModuliProblem.hasProperty_surjective_gammaNaiveRelRepData h3U)

variable (B : Scheme.{u}) (N : ℕ) [NeZero N]

/-- **`Y₁(N)` is smooth of relative dimension `1` over `B`.** For `N ≥ 4` invertible on `B`, the
structure morphism of the fine moduli scheme `Y₁(N)` to `B` is smooth of relative dimension `1`. -/
theorem smoothOfRelativeDimension_one_yOne_structureMap
    (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (h4 : 4 ≤ N) :
    SmoothOfRelativeDimension 1 (yOne B N).structureMap := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} 1)
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := @SmoothOfRelativeDimension.{u} 1) fun b ↦ ?_
  by_cases h2 : (2 : B.residueField b) = 0
  · have h3 : (3 : B.residueField b) ≠ 0 := by
      rw [show (3 : B.residueField b) = (2 : _) + 1 by norm_num, h2, zero_add]
      exact one_ne_zero
    exact ⟨B.basicOpen (3 : Γ(B, ⊤)),
      (B.evaluation_ne_zero_iff_mem_basicOpen b trivial (3 : Γ(B, ⊤))).mp
        (by simpa only [map_ofNat] using h3),
      smoothOfRelativeDimension_one_yOne_restrict_basicOpen_three B N hN h4⟩
  · exact ⟨B.basicOpen (2 : Γ(B, ⊤)),
      (B.evaluation_ne_zero_iff_mem_basicOpen b trivial (2 : Γ(B, ⊤))).mp
        (by simpa only [map_ofNat] using h2),
      smoothOfRelativeDimension_one_yOne_restrict_basicOpen_two B N hN h4⟩

end EllObj

end TauCeti.AlgebraicGeometry
