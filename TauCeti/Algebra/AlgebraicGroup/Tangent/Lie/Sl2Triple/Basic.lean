/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Scheme
public import TauCeti.Algebra.Lie.Sl2.Embedding
import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
import TauCeti.Algebra.AlgebraicGroup.Representation.Tangent
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Integration
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Naturality
import TauCeti.Algebra.AlgebraicGroup.Tangent.Rigidity

/-!
# Integrating an `sl₂` triple to an algebraic `SL₂` homomorphism

For a finite-type affine group `G = Spec H` over a characteristic-zero field `k` and an `sl₂`
triple `t : IsSl2Triple h e f` in `Lie(G)`, this file constructs the unique algebraic group
homomorphism `SL₂ ⟶ G` (`IsSl2Triple.sl2CoordinateMap`, `IsSl2Triple.sl2GroupSchemeHom`) whose
differential agrees with `t.toLieHom k` across `SpecialLinear.tangentLieEquivSl`, without assuming
algebraic closure of `k` or smoothness/connectedness of `G`. Downstream, `sl2CoordinateMap`
feeds the neutral cocharacter and dynamic gradings (`Sl2Triple/Cocharacter.lean`) and the central
kernel dichotomy and `PGL₂` factorization (`Sl2Triple/Kernel.lean`). When `Lie(G)` is `IsKilling`,
this gives the algebraic-group Jacobson–Morozov theorem
(`TauCeti.exists_sl2CoordinateMap_of_isNilpotent_ad`,
`TauCeti.exists_injective_derivationCompLieHom_coordinateHopfAlgebra_two_iff`).

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., §7; J. S. Milne, *Algebraic Groups*, Ch. 4, 10.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, §3.3, §3.7.
* J. E. Humphreys, *Conjugacy Classes in Semisimple Algebraic Groups*, AMS, 1995, §8.4.
-/

public section

open CategoryTheory AlgebraicGeometry LieAlgebra TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SpecialLinear

universe u

/-- **The standard `sl₂` triple in `Lie(SL₂)`.** -/
theorem isSl2Triple_tangentLieEquivSl_symm_single (R : Type u) [CommRing R] [Nontrivial R] :
    IsSl2Triple
      ((tangentLieEquivSl (R := R) (B := R) 2).symm (SpecialLinear.singleSubSingle 0 1 1))
      ((tangentLieEquivSl (R := R) (B := R) 2).symm (SpecialLinear.single 0 1 zero_ne_one 1))
      ((tangentLieEquivSl (R := R) (B := R) 2).symm (SpecialLinear.single 1 0 one_ne_zero 1)) :=
  (isSl2Triple_single (R := R) (zero_ne_one : (0 : Fin 2) ≠ 1)).map
    (tangentLieEquivSl (R := R) (B := R) 2).symm.toLieHom fun h0 ↦
      singleSubSingle_ne_zero zero_ne_one one_ne_zero
        ((tangentLieEquivSl (R := R) (B := R) 2).symm.injective (h0.trans (map_zero _).symm))

end TauCeti.SpecialLinear

namespace IsSl2Triple

universe u

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] {h e f : Derivation k H (Bialgebra.CounitAlgebra k H k)}

/-- **Every `sl₂` triple in `Lie(G)` over a characteristic-zero field integrates to a unique
algebraic `SL₂` homomorphism.** -/
theorem existsUnique_sl2CoordinateMap (t : IsSl2Triple h e f) :
    ∃! φ : CommHopfAlgCat.of k H ⟶ SpecialLinear.coordinateHopfAlgebra k 2,
      derivationCompLieHom (B := k) φ.hom =
        (t.toLieHom k).comp (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).toLieHom := by
  obtain ⟨M, n, b, hq⟩ := Comodule.exists_coordinateBialgHom_surjective (k := k) (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  have _ : Module.Finite k M := Module.Finite.of_basis b
  let ρLie := (Comodule.differential (R := k) (H := H) (M := M)).comp (t.toLieHom k)
  let _ : LieRingModule (SpecialLinear.sl (Fin 2) k) M := LieRingModule.compLieHom M ρLie
  let _ : LieModule k (SpecialLinear.sl (Fin 2) k) M := LieModule.compLieHom M ρLie
  let _ : Comodule k (SpecialLinear.coordinateHopfAlgebra k 2) M :=
    SpecialLinear.comoduleOfLieModule k M
  let A := SpecialLinear.coordinateHopfAlgebra k 2
  have hdiff : (derivationCompLieHom (B := k) (Comodule.coordinateBialgHom (H := H) b)).comp
      ((t.toLieHom k).comp (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).toLieHom) =
      derivationCompLieHom (B := k) (Comodule.coordinateBialgHom (H := A) b) := by
    ext d : 1; rw [LieHom.comp_apply, LieHom.comp_apply, LieEquiv.coe_toLieHom,
      derivationCompLieHom_apply, derivationCompLieHom_apply]
    apply (GeneralLinear.tangentLinearEquivMatrix (R := k) (B := k) n).injective; ext i j
    rw [GeneralLinear.tangentLinearEquivMatrix_apply, GeneralLinear.tangentLinearEquivMatrix_apply,
      d.tangentMatrix_derivationComp_coordinateBialgHom_apply (H := A) b i j,
      Derivation.tangentMatrix_derivationComp_coordinateBialgHom_apply _ (H := H) b i j,
      Comodule.coefficientMatrix_apply (C := A) b i j,
      Comodule.coefficientMatrix_apply (C := H) b i j,
      d.apply_matrixCoefficient (H := A) (b.coord i) (b j),
      Derivation.apply_matrixCoefficient _ (H := H) (b.coord i) (b j),
      SpecialLinear.differential_comoduleOfLieModule]
    exact (congrArg (b.coord i) (LieRingModule.compLieHom_apply M ρLie _ (b j))).symm
  have hconn := SpecialLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2
  obtain ⟨φ, ⟨-, hφ⟩, -⟩ :=
    CommHopfAlgCat.existsUnique_hom_of_surjective_of_derivationCompLieHom_eq hconn _ hq _ _ hdiff
  exact ⟨φ, hφ, fun ψ hψ ↦
    ψ.eq_of_derivationCompLieHom_eq_of_geometricallyConnected hconn φ (hψ.trans hφ.symm)⟩

/-- **The coordinate Hopf-algebra morphism `H ⟶ O(SL₂)` attached to an `sl₂` triple.** -/
noncomputable def sl2CoordinateMap (t : IsSl2Triple h e f) :
    CommHopfAlgCat.of k H ⟶ SpecialLinear.coordinateHopfAlgebra k 2 :=
  t.existsUnique_sl2CoordinateMap.choose

/-- The differential of `t.sl2CoordinateMap` is `(t.toLieHom k).comp (tangentLieEquivSl 2)`. -/
@[simp] theorem derivationCompLieHom_sl2CoordinateMap (t : IsSl2Triple h e f) :
    derivationCompLieHom (B := k) t.sl2CoordinateMap.hom =
      (t.toLieHom k).comp (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).toLieHom :=
  t.existsUnique_sl2CoordinateMap.choose_spec.1

/-- **The differential of `t.sl2CoordinateMap` is injective.** -/
theorem derivationCompLieHom_sl2CoordinateMap_injective (t : IsSl2Triple h e f) :
    Function.Injective (derivationCompLieHom (B := k) t.sl2CoordinateMap.hom) := by
  rw [t.derivationCompLieHom_sl2CoordinateMap, LieHom.coe_comp, LieEquiv.coe_toLieHom]
  exact (t.toLieHom_injective k).comp
    (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).injective

/-- Pointwise form of the differential of `t.sl2CoordinateMap`. -/
@[simp] theorem derivationComp_sl2CoordinateMap (t : IsSl2Triple h e f)
    (d : Derivation k (SpecialLinear.coordinateHopfAlgebra k 2)
      (Bialgebra.CounitAlgebra k (SpecialLinear.coordinateHopfAlgebra k 2) k)) :
    derivationComp (B := k) t.sl2CoordinateMap.hom d =
      t.toLieHom k (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2 d) := by
  simpa only [derivationCompLieHom_apply, LieHom.comp_apply, LieEquiv.coe_toLieHom] using
    LieHom.congr_fun t.derivationCompLieHom_sl2CoordinateMap d

/-- Differential of `t.sl2CoordinateMap` on `(tangentLieEquivSl 2).symm A`. -/
@[simp] theorem derivationComp_sl2CoordinateMap_symm (t : IsSl2Triple h e f)
    (A : SpecialLinear.sl (Fin 2) k) :
    derivationComp (B := k) t.sl2CoordinateMap.hom
        ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm A) = t.toLieHom k A := by
  rw [t.derivationComp_sl2CoordinateMap, LieEquiv.apply_symm_apply]

/-- The image of the differential of `t.sl2CoordinateMap` is `t.toLieSubalgebra k`. -/
theorem range_derivationCompLieHom_sl2CoordinateMap (t : IsSl2Triple h e f) :
    (derivationCompLieHom (B := k) t.sl2CoordinateMap.hom).range = t.toLieSubalgebra k := by
  ext x; rw [← t.range_toLieHom k, LieHom.mem_range, LieHom.mem_range]
  refine ⟨fun ⟨d, hd⟩ ↦ ⟨SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2 d, ?_⟩,
    fun ⟨A, hA⟩ ↦ ⟨(SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm A, ?_⟩⟩
  · rwa [derivationCompLieHom_apply, t.derivationComp_sl2CoordinateMap] at hd
  · rwa [derivationCompLieHom_apply, t.derivationComp_sl2CoordinateMap_symm]

/-- Uniqueness characterization of `t.sl2CoordinateMap` by its differential. -/
theorem eq_sl2CoordinateMap_iff (t : IsSl2Triple h e f)
    {φ : CommHopfAlgCat.of k H ⟶ SpecialLinear.coordinateHopfAlgebra k 2} :
    φ = t.sl2CoordinateMap ↔ derivationCompLieHom (B := k) φ.hom =
      (t.toLieHom k).comp (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).toLieHom :=
  ⟨fun hφ ↦ hφ ▸ t.derivationCompLieHom_sl2CoordinateMap,
    t.existsUnique_sl2CoordinateMap.choose_spec.2 φ⟩

/-- **Naturality.** Pushing an `sl₂` triple forward along `G ⟶ G'` composes `sl2CoordinateMap`. -/
theorem sl2CoordinateMap_map {H' : Type u} [CommRing H'] [HopfAlgebra k H']
    [Algebra.FiniteType k H'] (t : IsSl2Triple h e f)
    (ψ : CommHopfAlgCat.of k H' ⟶ CommHopfAlgCat.of k H)
    (hψ : derivationCompLieHom (B := k) ψ.hom h ≠ 0) :
    (t.map (derivationCompLieHom (B := k) ψ.hom) hψ).sl2CoordinateMap = ψ ≫ t.sl2CoordinateMap := by
  symm; rw [eq_sl2CoordinateMap_iff, CommHopfAlgCat.hom_comp, derivationCompLieHom_comp,
    t.derivationCompLieHom_sl2CoordinateMap, t.toLieHom_map k _ hψ]
  ext d; simp only [LieHom.comp_apply]

/-- On `SL₂` itself, the standard `sl₂` triple integrates to the identity of `O(SL₂)`. -/
@[simp] theorem sl2CoordinateMap_tangentLieEquivSl_symm_single
    (t : IsSl2Triple
      ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm
        (SpecialLinear.singleSubSingle 0 1 1))
      ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm
        (SpecialLinear.single 0 1 zero_ne_one 1))
      ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm
        (SpecialLinear.single 1 0 one_ne_zero 1))) :
    t.sl2CoordinateMap = 𝟙 (SpecialLinear.coordinateHopfAlgebra k 2) := by
  have ht : t = (isSl2Triple_single (R := k) (zero_ne_one : (0 : Fin 2) ≠ 1)).map
      (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm.toLieHom t.h_ne_zero :=
    Subsingleton.elim _ _
  symm; rw [eq_sl2CoordinateMap_iff, TauCeti.CommHopfAlgCat.hom_id, derivationCompLieHom_id, ht,
    (isSl2Triple_single (R := k) zero_ne_one).toLieHom_map k _ t.h_ne_zero,
    toLieHom_isSl2Triple_single, LieHom.comp_id]
  exact LieHom.ext fun d ↦
    ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm_apply_apply d).symm

/-- Along `x₀₁ : 𝔾ₐ ⟶ SL₂`, the differential of `t.sl2CoordinateMap` sends `1` to `e`. -/
theorem derivationComp_sl2CoordinateMap_rootSubgroup_zero_one (t : IsSl2Triple h e f) :
    derivationComp (B := k) (t.sl2CoordinateMap ≫
        SpecialLinear.rootSubgroupCoordinateMap (R := k) (zero_ne_one : (0 : Fin 2) ≠ 1)).hom
      ((AdditiveGroup.gaTangentLinearEquiv (R := k) (B := k)).symm 1) = e := by
  rw [CommHopfAlgCat.hom_comp, derivationComp_comp, LinearMap.comp_apply,
    t.derivationComp_sl2CoordinateMap, SpecialLinear.tangentLieEquivSl_apply,
    SpecialLinear.tangentMatrix_derivationComp_rootSubgroup, LinearEquiv.apply_symm_apply,
    t.toLieHom_single_zero_one k]

/-- Along `x₁₀ : 𝔾ₐ ⟶ SL₂`, the differential of `t.sl2CoordinateMap` sends `1` to `f`. -/
theorem derivationComp_sl2CoordinateMap_rootSubgroup_one_zero (t : IsSl2Triple h e f) :
    derivationComp (B := k) (t.sl2CoordinateMap ≫
        SpecialLinear.rootSubgroupCoordinateMap (R := k) (one_ne_zero : (1 : Fin 2) ≠ 0)).hom
      ((AdditiveGroup.gaTangentLinearEquiv (R := k) (B := k)).symm 1) = f := by
  rw [CommHopfAlgCat.hom_comp, derivationComp_comp, LinearMap.comp_apply,
    t.derivationComp_sl2CoordinateMap, SpecialLinear.tangentLieEquivSl_apply,
    SpecialLinear.tangentMatrix_derivationComp_rootSubgroup, LinearEquiv.apply_symm_apply,
    t.toLieHom_single_one_zero k]

/-- **The algebraic group-scheme homomorphism `SL₂ ⟶ G` attached to an `sl₂` triple.** -/
noncomputable def sl2GroupSchemeHom (t : IsSl2Triple h e f) :
    SpecialLinear.groupScheme k 2 ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).obj (Opposite.op (CommHopfAlgCat.of k H)) :=
  eqToHom (SpecialLinear.groupScheme_def k 2) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map t.sl2CoordinateMap.op

/-- Explicit formula for `t.sl2GroupSchemeHom` via `hopfSpec`. -/
theorem sl2GroupSchemeHom_def (t : IsSl2Triple h e f) :
    t.sl2GroupSchemeHom = eqToHom (SpecialLinear.groupScheme_def k 2) ≫
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map t.sl2CoordinateMap.op := (rfl)

end IsSl2Triple

namespace TauCeti

universe u

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsKilling k (Derivation k H (Bialgebra.CounitAlgebra k H k))]

/-- **The Jacobson–Morozov theorem for algebraic groups.** When `Lie(G)` is `IsKilling`, every
nonzero `ad`-nilpotent tangent vector `e` extends to an `sl₂` triple integrated by `SL₂ ⟶ G`. -/
theorem exists_sl2CoordinateMap_of_isNilpotent_ad
    {e : Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (he : IsNilpotent (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) e)) (he0 : e ≠ 0) :
    ∃ (h f : Derivation k H (Bialgebra.CounitAlgebra k H k)) (t : IsSl2Triple h e f)
      (φ : CommHopfAlgCat.of k H ⟶ SpecialLinear.coordinateHopfAlgebra k 2),
      φ = t.sl2CoordinateMap ∧ Function.Injective (derivationCompLieHom (B := k) φ.hom) ∧
        derivationComp (B := k) φ.hom ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm
          (SpecialLinear.single 0 1 zero_ne_one 1)) = e := by
  obtain ⟨h, f, t⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
  exact ⟨h, f, t, t.sl2CoordinateMap, rfl, t.derivationCompLieHom_sl2CoordinateMap_injective, by
    rw [t.derivationComp_sl2CoordinateMap_symm, t.toLieHom_single_zero_one k]⟩

/-- When `Lie(G)` is `IsKilling`, `e` is nonzero and `ad`-nilpotent iff some `SL₂ ⟶ G` with
injective differential sends `E₀₁` to `e`. -/
theorem exists_injective_derivationCompLieHom_coordinateHopfAlgebra_two_iff
    {e : Derivation k H (Bialgebra.CounitAlgebra k H k)} :
    (∃ φ : CommHopfAlgCat.of k H ⟶ SpecialLinear.coordinateHopfAlgebra k 2,
      Function.Injective (derivationCompLieHom (B := k) φ.hom) ∧
        derivationComp (B := k) φ.hom ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm
          (SpecialLinear.single 0 1 zero_ne_one 1)) = e) ↔
      IsNilpotent (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) e) ∧ e ≠ 0 := by
  have _ := finite_of_isKilling (R := k) (L := Derivation k H (Bialgebra.CounitAlgebra k H k))
  rw [← exists_injective_lieHom_slFinTwo_iff]
  refine ⟨fun ⟨φ, hφ, he⟩ ↦ ⟨(derivationCompLieHom (B := k) φ.hom).comp
    (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm.toLieHom,
    hφ.comp (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm.injective, by
      simpa only [LieHom.comp_apply, LieEquiv.coe_toLieHom, derivationCompLieHom_apply] using he⟩,
    fun ⟨ψ, hψ, he⟩ ↦ ?_⟩
  subst he; have hH := ψ.injective_iff_map_singleSubSingle_ne_zero.mp hψ
  let t := (isSl2Triple_single (R := k) (zero_ne_one : (0 : Fin 2) ≠ 1)).map ψ hH
  exact ⟨t.sl2CoordinateMap, t.derivationCompLieHom_sl2CoordinateMap_injective, by
    rw [t.derivationComp_sl2CoordinateMap_symm, ← ψ.eq_toLieHom_map hH]⟩

end TauCeti
