/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Sl2Triple.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Dimension
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.FiniteEtale
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Augmentation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Etale
import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.SpecialLinear
import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Tangent.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Center.FiniteFlat
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The central kernel of an integrated `sl₂` triple and `PGL₂` factorization

For a finite-type affine group `G = Spec H` over a characteristic-zero field `k` and an `sl₂`
triple `t : IsSl2Triple h e f` in `Lie(G)`, the differential of `t.sl2CoordinateMap : H ⟶ O(SL₂)`
is injective. Hence the scheme-theoretic kernel of `SL₂ ⟶ G` has trivial Lie algebra, is finite
étale and central in `SL₂` (`ker ⊆ Z(SL₂) = μ₂`), and satisfies a dichotomy
(`kernelHopfIdeal_sl2CoordinateMap_dichotomy`): it is either trivial (`HopfIdeal.augmentation`) or
the full center `Z(SL₂)` (`centerDefiningIdeal`, characterized by unique `PGL₂` factorization in
`existsUnique_comp_conjugationMap_sl2CoordinateMap_iff`). Both branches occur over every
characteristic-zero field via `sl2StandardTriple` and `pgl2StandardTriple`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., §7; J. S. Milne, *Algebraic Groups*, Ch. 10, 21.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, §3.3, §3.7.
-/

public section

open CategoryTheory LieAlgebra TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsSl2Triple

universe u

section Kernel

variable {k : Type u} [Field k] [CharZero k]
variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
variable {h e f : Derivation k H (Bialgebra.CounitAlgebra k H k)}

/-- **The differential of `t.sl2CoordinateMap` is injective.** -/
theorem derivationCompLieHom_sl2CoordinateMap_injective (t : IsSl2Triple h e f) :
    Function.Injective (derivationCompLieHom (B := k) t.sl2CoordinateMap.hom) := by
  rw [t.derivationCompLieHom_sl2CoordinateMap, LieHom.coe_comp, LieEquiv.coe_toLieHom]
  exact (t.toLieHom_injective k).comp
    (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).injective

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` has trivial tangent Lie algebra.** -/
@[simp]
theorem lieSubalgebra_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).lieSubalgebra (B := k) = ⊥ := by
  ext d
  rw [CommHopfAlgCat.lieSubalgebra_kernelHopfIdeal, LieIdeal.mem_toLieSubalgebra, LieHom.mem_ker,
    LieSubalgebra.mem_bot]
  exact ⟨fun hd ↦ t.derivationCompLieHom_sl2CoordinateMap_injective (hd.trans (map_zero _).symm),
    fun hd ↦ hd ▸ map_zero _⟩

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` is étale over `k`.** -/
theorem algebraEtale_quotient_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    Algebra.Etale k
      (SpecialLinear.coordinateHopfAlgebra k 2 ⧸
        (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).toIdeal) :=
  (CommHopfAlgCat.algebraEtale_quotient_kernelHopfIdeal_iff t.sl2CoordinateMap).mpr
    t.derivationCompLieHom_sl2CoordinateMap_injective

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` is finite over `k`.** -/
theorem moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    Module.Finite k
      (SpecialLinear.coordinateHopfAlgebra k 2 ⧸
        (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).toIdeal) :=
  CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal_of_derivationCompLieHom_injective
    t.derivationCompLieHom_sl2CoordinateMap_injective

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` is central in `SL₂`.** -/
theorem isCentral_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).IsCentral := by
  let _ : Module.Finite k (CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k 2)
      (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap)) :=
    t.moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap
  let _ : Algebra.Etale k (CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k 2)
      (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap)) :=
    t.algebraEtale_quotient_kernelHopfIdeal_sl2CoordinateMap
  have h : ∀ C : _root_.CommHopfAlgCat.{u} k,
      C = (SpecialLinear.finiteTypeCoordinateHopfAlgebra k 2).obj →
      ∀ [Algebra.IsGeometricallyReduced k C] (I : HopfIdeal k C)
        [Module.Finite k (CommHopfAlgCat.quotient C I)]
        [Algebra.IsGeometricallyReduced k (CommHopfAlgCat.quotient C I)],
        I.IsNormal → I.IsCentral := by
    rintro _ rfl _ I _ _ hI; exact hI.isCentral_of_finite_of_isGeometricallyReduced
      (H := SpecialLinear.finiteTypeCoordinateHopfAlgebra k 2)
      (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k 2 ▸
        SpecialLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2)
  exact h _ (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k 2).symm _
    (CommHopfAlgCat.isNormal_kernelHopfIdeal t.sl2CoordinateMap)

/-- **The scheme-theoretic kernel of `SL₂ ⟶ G` is contained in `Z(SL₂) = μ₂`.** -/
theorem centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    CommHopfAlgCat.centerDefiningIdeal (SpecialLinear.coordinateHopfAlgebra k 2) ≤
      CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap :=
  (CommHopfAlgCat.centerDefiningIdeal_le_iff _ _).mpr t.isCentral_kernelHopfIdeal_sl2CoordinateMap

/-- **Kernel dichotomy for integrated `sl₂` triples.** The scheme-theoretic kernel of `SL₂ ⟶ G` is
either trivial (`HopfIdeal.augmentation`) or the full center `Z(SL₂)` (`centerDefiningIdeal`). -/
theorem kernelHopfIdeal_sl2CoordinateMap_dichotomy (t : IsSl2Triple h e f) :
    CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap =
        HopfIdeal.augmentation k (SpecialLinear.coordinateHopfAlgebra k 2) ∨
      CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap =
        CommHopfAlgCat.centerDefiningIdeal (SpecialLinear.coordinateHopfAlgebra k 2) := by
  let A := SpecialLinear.coordinateHopfAlgebra k 2
  let Z := CommHopfAlgCat.centerDefiningIdeal A
  let K := CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap
  let ε := HopfIdeal.augmentation k A
  have hZK : Z ≤ K := t.centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap
  have hKε : K ≤ ε := HopfIdeal.le_augmentation k A K
  let _ : Module.Finite k (CommHopfAlgCat.quotient A Z) :=
    SpecialLinear.moduleFinite_centerCoordinate 2 zero_lt_two
  let _ := t.moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap
  let _ := HopfIdeal.moduleFinite_quotient_augmentation (R := k) A
  have hdimZ := SpecialLinear.finrank_centerCoordinate (k := k) 2 zero_lt_two
  have hdimε := HopfIdeal.finrank_quotient_augmentation (R := k) A
  have hle2 := (LinearMap.finrank_le_finrank_of_surjective
    (CommHopfAlgCat.quotientMapOfLe_surjective A hZK)).trans hdimZ.le
  have hge1 := hdimε.symm.le.trans (LinearMap.finrank_le_finrank_of_surjective
    (CommHopfAlgCat.quotientMapOfLe_surjective A hKε))
  rcases (by omega : Module.finrank k (CommHopfAlgCat.quotient A K) = 1 ∨
      Module.finrank k (CommHopfAlgCat.quotient A K) = 2) with h1 | h2
  · exact Or.inl (HopfIdeal.eq_of_le_of_finrank_quotient_eq hKε (h1.trans hdimε.symm))
  · exact Or.inr (HopfIdeal.eq_of_le_of_finrank_quotient_eq hZK (hdimZ.trans h2.symm)).symm

/-- **`PGL₂` factorization.** `t.sl2CoordinateMap` factors (uniquely) through `SL₂ ⟶ PGL₂`
(`SpecialLinear.conjugationMap 2 k`) if and only if its scheme-theoretic kernel equals `Z(SL₂)`. -/
theorem existsUnique_comp_conjugationMap_sl2CoordinateMap_iff (t : IsSl2Triple h e f) :
    (∃! ψ : CommHopfAlgCat.of k H ⟶ ProjectiveGeneralLinear.coordinateHopfAlgebra 2 k,
        ψ ≫ SpecialLinear.conjugationMap 2 k = t.sl2CoordinateMap) ↔
      CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap =
        CommHopfAlgCat.centerDefiningIdeal (SpecialLinear.coordinateHopfAlgebra k 2) := by
  refine ⟨fun ⟨ψ, hψ, _⟩ ↦ le_antisymm ?_ t.centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap,
    fun hker ↦ ?_⟩
  · rw [← hψ, ← SpecialLinear.kernelHopfIdeal_conjugationMap]
    exact CommHopfAlgCat.kernelHopfIdeal_comp_le ψ (SpecialLinear.conjugationMap 2 k)
  · let hSL := SpecialLinear.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k 2
    let eqSL := eqToIso (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k 2).symm
    have hgen : ∀ (B : _root_.CommHopfAlgCat.{u} k) (heq : B = _),
        CommHopfAlgCat.kernelHopfIdeal (t.sl2CoordinateMap ≫ eqToHom heq.symm) ≤
          CommHopfAlgCat.centerDefiningIdeal B := by rintro _ rfl; simpa using hker.le
    let ψ₀ : CommHopfAlgCat.of k H ⟶ ProjectiveGeneralLinear.coordinateHopfAlgebra 2 k :=
      hSL.reductive.liftCenterQuotient (t.sl2CoordinateMap ≫ eqSL.hom)
        (hgen _ (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k 2)) ≫
        (ProjectiveGeneralLinear.specialLinearCenterQuotientIso 2 k).inv
    have hψ₀ : ψ₀ ≫ SpecialLinear.conjugationMap 2 k = t.sl2CoordinateMap := by
      simp only [ψ₀, Category.assoc,
        ProjectiveGeneralLinear.specialLinearCenterQuotientIso_inv_comp]; simp [eqSL]
    refine ⟨ψ₀, hψ₀, fun ψ hψ ↦ ?_⟩
    apply CommHopfAlgCat.hom_ext; ext x
    exact SpecialLinear.injective_conjugationMap 2 k
      (DFunLike.congr_fun (congrArg CommHopfAlgCat.Hom.hom (hψ.trans hψ₀.symm)) x)

end Kernel

end IsSl2Triple

namespace TauCeti.SpecialLinear

universe u

section DichotomyWitnesses

/-- The center `Z(SL₂) = μ₂` is nontrivial over any field. -/
theorem centerDefiningIdeal_two_ne_augmentation (k : Type u) [Field k] :
    CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k 2) ≠
      HopfIdeal.augmentation k (coordinateHopfAlgebra k 2) := by
  intro heq
  have h2 := finrank_centerCoordinate (k := k) 2 zero_lt_two
  have h1 : Module.finrank k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k 2)
      (HopfIdeal.augmentation k (coordinateHopfAlgebra k 2))) = 1 :=
    HopfIdeal.finrank_quotient_augmentation (coordinateHopfAlgebra k 2)
  rw [heq] at h2; omega

variable (k : Type u) [Field k] [CharZero k]

private theorem tangentLieEquivSl_symm_singleSubSingle_ne_zero :
    (tangentLieEquivSl (R := k) (B := k) 2).symm.toLieHom
      (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1) ≠ 0 := by
  intro h0
  have h1 : (LieAlgebra.SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : k)) = 0 :=
    (tangentLieEquivSl (R := k) (B := k) 2).symm.injective
      ((tangentLieEquivSl (R := k) (B := k) 2).symm.map_zero ▸ h0)
  have h00 := congr_fun (congr_fun (congrArg Subtype.val h1) 0) 0
  simp [LieAlgebra.SpecialLinear.val_singleSubSingle] at h00

/-- **The standard `sl₂` triple in `Lie(SL₂)`.** -/
theorem sl2StandardTriple :
    IsSl2Triple
      ((tangentLieEquivSl (R := k) (B := k) 2).symm
        (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1))
      ((tangentLieEquivSl (R := k) (B := k) 2).symm
        (LieAlgebra.SpecialLinear.single 0 1 zero_ne_one 1))
      ((tangentLieEquivSl (R := k) (B := k) 2).symm
        (LieAlgebra.SpecialLinear.single 1 0 one_ne_zero 1)) :=
  (isSl2Triple_single (R := k) (zero_ne_one : (0 : Fin 2) ≠ 1)).map
    (tangentLieEquivSl (R := k) (B := k) 2).symm.toLieHom
    (tangentLieEquivSl_symm_singleSubSingle_ne_zero k)

/-- `sl2StandardTriple k` integrates to `𝟙` with trivial scheme-theoretic kernel. -/
@[simp]
theorem kernelHopfIdeal_sl2CoordinateMap_sl2StandardTriple :
    CommHopfAlgCat.kernelHopfIdeal (sl2StandardTriple k).sl2CoordinateMap =
      HopfIdeal.augmentation k (coordinateHopfAlgebra k 2) := by
  rw [IsSl2Triple.sl2CoordinateMap_isSl2Triple_single
      (tangentLieEquivSl_symm_singleSubSingle_ne_zero k)]
  exact CommHopfAlgCat.kernelHopfIdeal_eq_augmentation_of_surjective _ Function.surjective_id

private theorem derivationCompLieHom_conjugationMap_two_ne_zero :
    derivationCompLieHom (B := k) (conjugationMap 2 k).hom
        ((tangentLieEquivSl (R := k) (B := k) 2).symm
          (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1)) ≠ 0 := by
  intro h0
  let d₀ := (tangentLieEquivSl (R := k) (B := k) 2).symm
    (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1)
  have hd : ProjectiveGeneralLinear.tangentEnd 2
      (derivationComp (B := k) (conjugationMap 2 k).hom d₀) = 0 := by
    rw [← derivationCompLieHom_apply, h0, map_zero]
  have hmat : GeneralLinear.tangentMatrix 2 (derivationComp (B := k) (coordinateMap k 2).hom d₀) =
      (LieAlgebra.SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : k)).val := by
    rw [coordinateMap, CommHopfAlgCat.hom_mkQuotient, ← HopfIdeal.quotientLieHom_apply,
      ← tangentMatrix_apply_coe, ← tangentLieEquivSl_apply, LieEquiv.apply_symm_apply]
  rw [conjugationMap_def, CommHopfAlgCat.hom_comp, derivationComp_comp, LinearMap.comp_apply,
    ProjectiveGeneralLinear.tangentEnd_derivationComp_conjugationMap, hmat] at hd
  have heval := congr_fun (congr_fun
    (LinearMap.congr_fun hd (Matrix.single (0 : Fin 2) 1 (1 : k))) 0) 1
  simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    LieAlgebra.SpecialLinear.val_singleSubSingle, LinearMap.zero_apply, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply, Fin.sum_univ_two,
    Fin.isValue] at heval
  norm_num at heval

/-- **The standard `sl₂` triple in `Lie(PGL₂)`.** -/
theorem pgl2StandardTriple :
    IsSl2Triple
      (derivationCompLieHom (B := k) (conjugationMap 2 k).hom ((tangentLieEquivSl (R := k)
        (B := k) 2).symm (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1)))
      (derivationCompLieHom (B := k) (conjugationMap 2 k).hom ((tangentLieEquivSl (R := k)
        (B := k) 2).symm (LieAlgebra.SpecialLinear.single 0 1 zero_ne_one 1)))
      (derivationCompLieHom (B := k) (conjugationMap 2 k).hom ((tangentLieEquivSl (R := k)
        (B := k) 2).symm (LieAlgebra.SpecialLinear.single 1 0 one_ne_zero 1))) :=
  (sl2StandardTriple k).map (derivationCompLieHom (B := k) (conjugationMap 2 k).hom)
    (derivationCompLieHom_conjugationMap_two_ne_zero k)

/-- `pgl2StandardTriple k` integrates to the central isogeny `SL₂ ⟶ PGL₂`. -/
@[simp]
theorem sl2CoordinateMap_pgl2StandardTriple :
    (pgl2StandardTriple k).sl2CoordinateMap = conjugationMap 2 k := by
  rw [(sl2StandardTriple k).sl2CoordinateMap_map (conjugationMap 2 k)
      (derivationCompLieHom_conjugationMap_two_ne_zero k),
    IsSl2Triple.sl2CoordinateMap_isSl2Triple_single
      (tangentLieEquivSl_symm_singleSubSingle_ne_zero k), Category.comp_id]

/-- `pgl2StandardTriple k` has scheme-theoretic kernel `Z(SL₂) = μ₂`. -/
@[simp]
theorem kernelHopfIdeal_sl2CoordinateMap_pgl2StandardTriple :
    CommHopfAlgCat.kernelHopfIdeal (pgl2StandardTriple k).sl2CoordinateMap =
      CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k 2) := by
  rw [sl2CoordinateMap_pgl2StandardTriple, kernelHopfIdeal_conjugationMap]

end DichotomyWitnesses

end TauCeti.SpecialLinear
