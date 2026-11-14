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

Let `G = Spec H` be an affine group scheme of finite type over a field `k` of characteristic zero,
and let `t : IsSl2Triple h e f` be an `sl₂` triple in `Lie(G)` with integrated algebraic group
homomorphism `t.sl2CoordinateMap : H ⟶ O(SL₂)` (`SL₂ ⟶ G`). Because `t.toLieHom k` is injective on
`sl (Fin 2) k`, the differential of `t.sl2CoordinateMap` is injective. Consequently:

* the tangent Lie algebra of the scheme-theoretic kernel of `SL₂ ⟶ G` is trivial, so the kernel is
  finite étale over `k`;
* as a finite geometrically reduced normal closed subgroup scheme of the smooth geometrically
  connected group `SL₂`, the kernel is central, i.e., contained in the center `Z(SL₂) = μ₂`;
* since `O(Z(SL₂))` has dimension `2` over `k`, the scheme-theoretic kernel is either the trivial
  subgroup scheme (cut out by the augmentation ideal, when `SL₂ ↪ G` is a closed immersion) or the
  full center `Z(SL₂) = μ₂` (cut out by `CommHopfAlgCat.centerDefiningIdeal`, when `SL₂ ⟶ G`
  descends uniquely through `SL₂ ⟶ PGL₂`).

Both cases of the dichotomy occur over every field of characteristic zero: the standard triple of
`SL₂` integrates to the identity of `SL₂` with trivial kernel, whereas its image in `Lie(PGL₂)`
integrates to the adjoint quotient `SL₂ ⟶ PGL₂` with kernel `Z(SL₂) = μ₂`.

## Main declarations

* `IsSl2Triple.derivationCompLieHom_sl2CoordinateMap_injective` and
  `IsSl2Triple.lieSubalgebra_kernelHopfIdeal_sl2CoordinateMap`: injectivity of the differential and
  triviality of the kernel Lie algebra.
* `IsSl2Triple.algebraEtale_quotient_kernelHopfIdeal_sl2CoordinateMap` and
  `IsSl2Triple.moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap`: finite étaleness of the
  scheme-theoretic kernel.
* `IsSl2Triple.isCentral_kernelHopfIdeal_sl2CoordinateMap` and
  `IsSl2Triple.centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap`: centrality of the kernel
  (`ker(SL₂ ⟶ G) ⊆ Z(SL₂)`).
* `IsSl2Triple.kernelHopfIdeal_sl2CoordinateMap_dichotomy`: the scheme-theoretic kernel is either
  trivial or the full center `Z(SL₂)`.
* `IsSl2Triple.existsUnique_comp_conjugationMap_sl2CoordinateMap_iff`: unique factorization through
  `SL₂ ⟶ PGL₂` holds if and only if the kernel equals `Z(SL₂)`.
* `TauCeti.SpecialLinear.sl2StandardTriple`, `TauCeti.SpecialLinear.pgl2StandardTriple`,
  `TauCeti.SpecialLinear.kernelHopfIdeal_sl2CoordinateMap_sl2StandardTriple`, and
  `TauCeti.SpecialLinear.kernelHopfIdeal_sl2CoordinateMap_pgl2StandardTriple`: concrete triples in
  `Lie(SL₂)` and `Lie(PGL₂)` realizing both branches of the kernel dichotomy.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, Springer, 1991, §7.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.3 and §3.7.
* J. E. Humphreys, *Conjugacy Classes in Semisimple Algebraic Groups*, AMS, 1995, §8.4.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017, Chapters 10 and 21.
-/

public section

open CategoryTheory LieAlgebra TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsSl2Triple

universe u

@[reducible]
private noncomputable def finiteTypeSL2 (k : Type u) [Field k] :
    FiniteTypeCommHopfAlgCat.{u, u} k :=
  ⟨SpecialLinear.coordinateHopfAlgebra k 2, by
    rw [← SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj]
    exact (SpecialLinear.finiteTypeCoordinateHopfAlgebra k 2).property⟩

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
        (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).toIdeal) := by
  let _ : Algebra.FiniteType k (SpecialLinear.coordinateHopfAlgebra k 2) :=
    (finiteTypeSL2 k).property
  exact (CommHopfAlgCat.algebraEtale_quotient_kernelHopfIdeal_iff t.sl2CoordinateMap).mpr
    t.derivationCompLieHom_sl2CoordinateMap_injective

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` is finite over `k`.** -/
theorem moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    Module.Finite k
      (SpecialLinear.coordinateHopfAlgebra k 2 ⧸
        (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).toIdeal) := by
  let _ : Algebra.FiniteType k (SpecialLinear.coordinateHopfAlgebra k 2) :=
    (finiteTypeSL2 k).property
  exact CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal_of_derivationCompLieHom_injective
    t.derivationCompLieHom_sl2CoordinateMap_injective

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` is central in `SL₂`.** -/
theorem isCentral_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).IsCentral := by
  let _ : Module.Finite k
      (CommHopfAlgCat.quotient (finiteTypeSL2 k).obj
        (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap)) :=
    t.moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap
  let _ : Algebra.Etale k
      (CommHopfAlgCat.quotient (finiteTypeSL2 k).obj
        (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap)) :=
    t.algebraEtale_quotient_kernelHopfIdeal_sl2CoordinateMap
  exact (CommHopfAlgCat.isNormal_kernelHopfIdeal
    t.sl2CoordinateMap).isCentral_of_finite_of_isGeometricallyReduced (H := finiteTypeSL2 k)
      (SpecialLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2)

/-- **The scheme-theoretic kernel of `SL₂ ⟶ G` is contained in the center `Z(SL₂) = μ₂`.**
Hopf ideals reverse subgroup inclusion, so `centerDefiningIdeal ≤ kernelHopfIdeal` expresses
`ker(SL₂ ⟶ G) ⊆ Z(SL₂)`. -/
theorem centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    CommHopfAlgCat.centerDefiningIdeal (SpecialLinear.coordinateHopfAlgebra k 2) ≤
      CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap :=
  (CommHopfAlgCat.centerDefiningIdeal_le_iff _ _).mpr t.isCentral_kernelHopfIdeal_sl2CoordinateMap

/-- **Kernel dichotomy for integrated `sl₂` triples.** The scheme-theoretic kernel of `SL₂ ⟶ G` is
either the trivial subgroup scheme (cut out by `HopfIdeal.augmentation`) or the full center
`Z(SL₂) = μ₂` (cut out by `CommHopfAlgCat.centerDefiningIdeal`). -/
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
  let _ : Module.Finite k (CommHopfAlgCat.quotient A K) :=
    t.moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap
  let _ : Module.Finite k (CommHopfAlgCat.quotient A ε) :=
    HopfIdeal.moduleFinite_quotient_augmentation A
  have hdimZ : Module.finrank k (CommHopfAlgCat.quotient A Z) = 2 :=
    SpecialLinear.finrank_centerCoordinate 2 zero_lt_two
  have hdimε : Module.finrank k (CommHopfAlgCat.quotient A ε) = 1 :=
    HopfIdeal.finrank_quotient_augmentation A
  have hle2 : Module.finrank k (CommHopfAlgCat.quotient A K) ≤ 2 :=
    (LinearMap.finrank_le_finrank_of_surjective
      (CommHopfAlgCat.quotientMapOfLe_surjective A hZK)).trans hdimZ.le
  have hge1 : 1 ≤ Module.finrank k (CommHopfAlgCat.quotient A K) :=
    hdimε.symm.le.trans
      (LinearMap.finrank_le_finrank_of_surjective (CommHopfAlgCat.quotientMapOfLe_surjective A hKε))
  have hcases : Module.finrank k (CommHopfAlgCat.quotient A K) = 1 ∨
      Module.finrank k (CommHopfAlgCat.quotient A K) = 2 := by omega
  rcases hcases with h1 | h2
  · exact Or.inl (HopfIdeal.eq_of_le_of_finrank_quotient_eq hKε (h1.trans hdimε.symm))
  · exact Or.inr (HopfIdeal.eq_of_le_of_finrank_quotient_eq hZK (hdimZ.trans h2.symm)).symm

/-- **`PGL₂` factorization.** The integrated homomorphism `SL₂ ⟶ G` factors (necessarily uniquely)
through the adjoint quotient `SL₂ ⟶ PGL₂` (`SpecialLinear.conjugationMap 2 k`) if and only if its
scheme-theoretic kernel equals `Z(SL₂)`. -/
theorem existsUnique_comp_conjugationMap_sl2CoordinateMap_iff (t : IsSl2Triple h e f) :
    (∃! ψ : CommHopfAlgCat.of k H ⟶ ProjectiveGeneralLinear.coordinateHopfAlgebra 2 k,
        ψ ≫ SpecialLinear.conjugationMap 2 k = t.sl2CoordinateMap) ↔
      CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap =
        CommHopfAlgCat.centerDefiningIdeal (SpecialLinear.coordinateHopfAlgebra k 2) := by
  constructor
  · rintro ⟨ψ, hψ, -⟩
    apply le_antisymm
    · rw [← hψ, ← SpecialLinear.kernelHopfIdeal_conjugationMap]
      exact CommHopfAlgCat.kernelHopfIdeal_comp_le ψ (SpecialLinear.conjugationMap 2 k)
    · exact t.centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap
  · intro hker
    let hSL := SpecialLinear.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k 2
    let eqSL := eqToIso (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k 2).symm
    have hgen : ∀ (B : _root_.CommHopfAlgCat.{u} k)
        (heq : B = SpecialLinear.coordinateHopfAlgebra k 2),
        CommHopfAlgCat.kernelHopfIdeal (t.sl2CoordinateMap ≫ eqToHom heq.symm) ≤
          CommHopfAlgCat.centerDefiningIdeal B := by
      rintro B rfl
      simpa using hker.le
    have hle : CommHopfAlgCat.kernelHopfIdeal (t.sl2CoordinateMap ≫ eqSL.hom) ≤
        CommHopfAlgCat.centerDefiningIdeal
          (SpecialLinear.finiteTypeCoordinateHopfAlgebra k 2).obj :=
      hgen _ (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k 2)
    let ψ₀ : CommHopfAlgCat.of k H ⟶ ProjectiveGeneralLinear.coordinateHopfAlgebra 2 k :=
      hSL.reductive.liftCenterQuotient (t.sl2CoordinateMap ≫ eqSL.hom) hle ≫
        (ProjectiveGeneralLinear.specialLinearCenterQuotientIso 2 k).inv
    have hψ₀ : ψ₀ ≫ SpecialLinear.conjugationMap 2 k = t.sl2CoordinateMap := by
      simp only [ψ₀, Category.assoc,
        ProjectiveGeneralLinear.specialLinearCenterQuotientIso_inv_comp,
        reductiveCommHopfAlgProperty.liftCenterQuotient_comp_centerQuotientι_assoc]
      simp [eqSL]
    refine ⟨ψ₀, hψ₀, fun ψ hψ ↦ ?_⟩
    apply CommHopfAlgCat.hom_ext
    ext x
    apply SpecialLinear.injective_conjugationMap 2 k
    exact DFunLike.congr_fun (congrArg CommHopfAlgCat.Hom.hom (hψ.trans hψ₀.symm)) x

end Kernel

end IsSl2Triple

namespace TauCeti.SpecialLinear

universe u

section DichotomyWitnesses

/-- The center `Z(SL₂) = μ₂` is nontrivial as a closed subgroup scheme over any field: its defining
Hopf ideal is strictly contained in the augmentation ideal. -/
theorem centerDefiningIdeal_two_ne_augmentation (k : Type u) [Field k] :
    CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k 2) ≠
      HopfIdeal.augmentation k (coordinateHopfAlgebra k 2) := by
  intro heq
  have h2 := finrank_centerCoordinate (k := k) 2 zero_lt_two
  rw [heq] at h2
  have h1 : Module.finrank k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k 2)
        (HopfIdeal.augmentation k (coordinateHopfAlgebra k 2))) = 1 := by
    rw [HopfIdeal.augmentation_def]
    exact (HopfIdeal.kerLiftBialgEquiv
      (Bialgebra.counitBialgHom k (coordinateHopfAlgebra k 2))
      Bialgebra.counit_surjective).toAlgEquiv.toLinearEquiv.finrank_eq.trans (Module.finrank_self k)
  omega

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

/-- The standard `sl₂` triple in `Lie(SL₂)` integrates to the identity of `O(SL₂)` and has trivial
scheme-theoretic kernel (realizing the first branch of the kernel dichotomy). -/
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
  have hmat : GeneralLinear.tangentMatrix 2
      (derivationComp (B := k) (coordinateMap k 2).hom d₀) =
      (LieAlgebra.SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : k)).val := by
    rw [coordinateMap, CommHopfAlgCat.hom_mkQuotient, ← HopfIdeal.quotientLieHom_apply,
      ← tangentMatrix_apply_coe, ← tangentLieEquivSl_apply, LieEquiv.apply_symm_apply]
  rw [conjugationMap_def, CommHopfAlgCat.hom_comp, derivationComp_comp, LinearMap.comp_apply,
    ProjectiveGeneralLinear.tangentEnd_derivationComp_conjugationMap, hmat] at hd
  have heval := congr_fun (congr_fun
    (LinearMap.congr_fun hd (Matrix.single (0 : Fin 2) 1 (1 : k))) 0) 1
  simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    LieAlgebra.SpecialLinear.val_singleSubSingle, LinearMap.zero_apply, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply, Fin.sum_univ_two, Fin.isValue]
    at heval
  norm_num at heval

/-- **The standard `sl₂` triple in `Lie(PGL₂)`**, obtained by pushing `sl2StandardTriple k` forward
along the differential of `SL₂ ⟶ PGL₂`. -/
theorem pgl2StandardTriple :
    IsSl2Triple
      (derivationCompLieHom (B := k) (conjugationMap 2 k).hom
        ((tangentLieEquivSl (R := k) (B := k) 2).symm
          (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1)))
      (derivationCompLieHom (B := k) (conjugationMap 2 k).hom
        ((tangentLieEquivSl (R := k) (B := k) 2).symm
          (LieAlgebra.SpecialLinear.single 0 1 zero_ne_one 1)))
      (derivationCompLieHom (B := k) (conjugationMap 2 k).hom
        ((tangentLieEquivSl (R := k) (B := k) 2).symm
          (LieAlgebra.SpecialLinear.single 1 0 one_ne_zero 1))) :=
  (sl2StandardTriple k).map (derivationCompLieHom (B := k) (conjugationMap 2 k).hom)
    (derivationCompLieHom_conjugationMap_two_ne_zero k)

/-- The standard `sl₂` triple in `Lie(PGL₂)` integrates to the central isogeny `SL₂ ⟶ PGL₂`. -/
@[simp]
theorem sl2CoordinateMap_pgl2StandardTriple :
    (pgl2StandardTriple k).sl2CoordinateMap = conjugationMap 2 k := by
  rw [(sl2StandardTriple k).sl2CoordinateMap_map (conjugationMap 2 k)
      (derivationCompLieHom_conjugationMap_two_ne_zero k),
    IsSl2Triple.sl2CoordinateMap_isSl2Triple_single
      (tangentLieEquivSl_symm_singleSubSingle_ne_zero k),
    Category.comp_id]

/-- The standard `sl₂` triple in `Lie(PGL₂)` has scheme-theoretic kernel `Z(SL₂) = μ₂` (realizing
the second, nontrivial branch of the kernel dichotomy). -/
@[simp]
theorem kernelHopfIdeal_sl2CoordinateMap_pgl2StandardTriple :
    CommHopfAlgCat.kernelHopfIdeal (pgl2StandardTriple k).sl2CoordinateMap =
      CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k 2) := by
  rw [sl2CoordinateMap_pgl2StandardTriple, kernelHopfIdeal_conjugationMap]

end DichotomyWitnesses

end TauCeti.SpecialLinear
