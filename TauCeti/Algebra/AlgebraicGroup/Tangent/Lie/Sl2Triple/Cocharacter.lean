/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Weights
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Coroot
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Sl2Triple.Basic
public import TauCeti.Algebra.Lie.AdjointAction.GradingAut
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Centralizer
import TauCeti.Algebra.AlgebraicGroup.Tangent.Rigidity
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.Algebra.Lie.Sl2.Spectrum

/-!
# The cocharacter of an `sl₂` triple and its weight decomposition

An `sl₂` triple `t : IsSl2Triple h e f` in `Lie(G)` grades `Lie(G)` into the `(n : k)`-eigenspaces
`𝔤(n)` of `ad h`. Composing `IsSl2Triple.sl2CoordinateMap : H ⟶ O(SL₂)` with
`SpecialLinear.simpleCorootCocharacter 1 k 0` upgrades this grading to `G = Spec H` via
`IsSl2Triple.cocharacter : H →ₐc[k] k[T;T⁻¹]`, whose unit tangent differential is `h`. Via
`AddMonoidAlgebra.toMultiplicativeBialgEquiv`, the `m`-weight space on any `H`-comodule equals the
`(m : k)`-eigenspace of `h` (`weightSpace_cocharacter_eq_eigenspace`), so `t.cocharacter` acts on
eigenspaces via `s ^ m` (`basePointsRepresentation_pointsHom_cocharacter_of_mem_eigenspace`) and
its adjoint action on `Lie(G)` is `TauCeti.gradingAut`
(`adDerivationLieEquiv_pointsHom_cocharacter`). Moreover, `P_G(t.cocharacter)`,
`U_G(t.cocharacter)`, and `Z_G(t.cocharacter)` have Lie algebras spanned by `𝔤(n)` for `0 ≤ n`,
`0 < n`, and `n = 0`; `Z_G(t.cocharacter)` lies in `C_G(h)` with the same Lie algebra;
`t.symm.cocharacter = t.cocharacter.oppositeCocharacter`; and adjoint conjugation by a rational
point `g` corresponds to `BialgHom.conjCocharacter g`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., §7; B. Conrad, O. Gabber, G. Prasad,
  *Pseudo-reductive Groups*, 2nd ed., §2.1.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, §3.3, §3.8.
* J. E. Humphreys, *Conjugacy Classes in Semisimple Algebraic Groups*, AMS, 1995, §8.4.
-/

public section

open CategoryTheory LieAlgebra TauCeti TauCeti.Cocharacter WithConv
open scoped LaurentPolynomial TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsSl2Triple

universe u w

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] {h e f : Derivation k H (Bialgebra.CounitAlgebra k H k)}

/-- **The cocharacter `𝔾ₘ ⟶ G` attached to an `sl₂` triple.** For finite-type `H` over a
characteristic-zero field `k`, `t.cocharacter` restricts `t.sl2CoordinateMap` along
`SpecialLinear.simpleCorootCocharacter 1 k 0` (`u ↦ diag(u, u⁻¹)`), so its unit tangent
differential is `h` (`derivationComp_cocharacter_unit`). -/
noncomputable def cocharacter (t : IsSl2Triple h e f) : H →ₐc[k] LaurentPolynomial k :=
  (SpecialLinear.simpleCorootCocharacter 1 k 0).comp t.sl2CoordinateMap.hom

/-- Unfolding `t.cocharacter` via `simpleCorootCocharacter 1 k 0` and `t.sl2CoordinateMap`. -/
theorem cocharacter_def (t : IsSl2Triple h e f) :
    t.cocharacter = (SpecialLinear.simpleCorootCocharacter 1 k 0).comp t.sl2CoordinateMap.hom :=
  (rfl)

/-- Differential of `t.cocharacter` on tangent vectors of `𝔾ₘ`. -/
@[simp] theorem derivationComp_cocharacter (t : IsSl2Triple h e f)
    (d : Derivation k (LaurentPolynomial k) (Bialgebra.CounitAlgebra k (LaurentPolynomial k) k)) :
    derivationComp (B := k) t.cocharacter d = MultiplicativeGroup.tangentLinearEquiv d • h := by
  rw [cocharacter_def, derivationComp_comp, LinearMap.comp_apply, t.derivationComp_sl2CoordinateMap,
    SpecialLinear.tangentLieEquivSl_apply,
    SpecialLinear.tangentMatrix_derivationComp_simpleCorootCocharacter, Fin.castSucc_zero,
    Fin.succ_zero_eq_one]
  have hsingle : SpecialLinear.singleSubSingle (0 : Fin 2) 1
      (MultiplicativeGroup.tangentLinearEquiv d) =
      MultiplicativeGroup.tangentLinearEquiv d • SpecialLinear.singleSubSingle (0 : Fin 2) 1 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (SpecialLinear.singleSubSingle (0 : Fin 2) 1 (R := k)).map_smul
        (MultiplicativeGroup.tangentLinearEquiv d) 1
  rw [hsingle, map_smul, t.toLieHom_singleSubSingle k]

/-- The unit tangent vector of `𝔾ₘ` maps under `t.cocharacter` to `h`. -/
theorem derivationComp_cocharacter_unit (t : IsSl2Triple h e f) :
    derivationComp (B := k) t.cocharacter
        ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1) = h := by
  rw [t.derivationComp_cocharacter, LinearEquiv.apply_symm_apply, one_smul]

/-- **Naturality of `t.cocharacter`** along a morphism of finite-type affine groups. -/
theorem cocharacter_map {H' : Type u} [CommRing H'] [HopfAlgebra k H'] [Algebra.FiniteType k H']
    (t : IsSl2Triple h e f) (ψ : CommHopfAlgCat.of k H' ⟶ CommHopfAlgCat.of k H)
    (hψ : derivationCompLieHom (B := k) ψ.hom h ≠ 0) :
    (t.map (derivationCompLieHom (B := k) ψ.hom) hψ).cocharacter = t.cocharacter.comp ψ.hom := by
  rw [cocharacter_def, t.sl2CoordinateMap_map ψ hψ, CommHopfAlgCat.hom_comp, ← BialgHom.comp_assoc,
    ← cocharacter_def]

/-- **Opposite triple gives the opposite cocharacter.** Reversing `(h, e, f)` to `(-h, f, e)`
inverts the attached cocharacter `𝔾ₘ ⟶ G`. -/
theorem cocharacter_symm (t : IsSl2Triple h e f) :
    t.symm.cocharacter = t.cocharacter.oppositeCocharacter := by
  let eMult := AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ
  let _ : Algebra.FiniteType k (LaurentPolynomial k) :=
    (MonoidAlgebra.finiteType_of_fg (R := k) (M := Multiplicative ℤ)).equiv eMult.symm.toAlgEquiv
  have hconn : geometricallyConnectedCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.of k (LaurentPolynomial k)) :=
    (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (_root_.CommHopfAlgCat.isoMk eMult.symm)
      (DiagonalizableGroup.geometricallyConnected_coordinateRing k
        (FGCommGrpCat.of.{0} (Multiplicative ℤ)))
  have hhom : _root_.CommHopfAlgCat.ofHom t.symm.cocharacter =
      _root_.CommHopfAlgCat.ofHom t.cocharacter.oppositeCocharacter := by
    apply CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq_of_geometricallyConnected hconn
    ext d x
    rw [_root_.CommHopfAlgCat.hom_ofHom, _root_.CommHopfAlgCat.hom_ofHom,
      derivationCompLieHom_apply, derivationCompLieHom_apply]
    have hopp_eq : t.cocharacter.oppositeCocharacter =
        (AddMonoidAlgebra.domCongrBialgEquiv k k (AddEquiv.neg ℤ)).toBialgHom.comp
          t.cocharacter :=
      BialgHom.ext fun a ↦ t.cocharacter.oppositeCocharacter_apply a
    have hopp : derivationComp (B := k) t.cocharacter.oppositeCocharacter d =
        derivationComp (B := k) t.cocharacter
          (derivationComp (B := k)
            (AddMonoidAlgebra.domCongrBialgEquiv k k (AddEquiv.neg ℤ)).toBialgHom d) := by
      rw [hopp_eq, derivationComp_comp, LinearMap.comp_apply]
    have hcoord : MultiplicativeGroup.tangentLinearEquiv
        (derivationComp (B := k)
          (AddMonoidAlgebra.domCongrBialgEquiv k k (AddEquiv.neg ℤ)).toBialgHom d) =
        -MultiplicativeGroup.tangentLinearEquiv d := by
      rw [MultiplicativeGroup.tangentLinearEquiv_apply, algEquivSelf_derivationComp_apply]
      have hT : (AddMonoidAlgebra.domCongrBialgEquiv k k (AddEquiv.neg ℤ)).toBialgHom.toAlgHom
          (LaurentPolynomial.T 1) = LaurentPolynomial.T (-1) := LaurentPolynomial.invert_T 1
      rw [hT, MultiplicativeGroup.derivation_T_zsmul, map_zsmul, neg_one_zsmul,
        MultiplicativeGroup.tangentLinearEquiv_apply]
    rw [t.symm.derivationComp_cocharacter, hopp, t.derivationComp_cocharacter, hcoord,
      smul_apply, smul_apply, neg_apply, smul_neg, neg_smul]
  exact congrArg _root_.CommHopfAlgCat.Hom.hom hhom

/-- **Conjugation compatibility of `t.cocharacter`.** Conjugating an `sl₂` triple by the adjoint
action of a rational point `g` conjugates its attached cocharacter via `BialgHom.conjCocharacter`.
-/
theorem cocharacter_adDerivationLieEquiv (t : IsSl2Triple h e f)
    (g : WithConv (H →ₐ[k] k)) :
    (t.map (Derivation.adDerivationLieEquiv k
        (Derivation.pointInCounitAlgebra (CommAlgCat.of k k) g)).toLieHom
        (by
          simpa only [LieEquiv.coe_toLieHom, map_zero] using
            (Derivation.adDerivationLieEquiv k
              (Derivation.pointInCounitAlgebra (CommAlgCat.of k k) g)).injective.ne
              t.h_ne_zero)).cocharacter =
      t.cocharacter.conjCocharacter g := by
  have hg : AlgHom.mapValue (H := H) (Algebra.ofId k (Bialgebra.CounitAlgebra k H k)) g =
      Derivation.pointInCounitAlgebra (CommAlgCat.of k k) g := by
    apply ofConv_injective; apply AlgHom.ext; intro x
    apply (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
    simp [AlgHom.mapValue_apply]
  have hφ : derivationCompLieHom (B := k) (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom =
      (Derivation.adDerivationLieEquiv k
        (Derivation.pointInCounitAlgebra (CommAlgCat.of k k) g)).toLieHom := by
    simpa only [hg] using TauCeti.derivationCompLieHom_pointConjugationBialgEquiv (B := k) g
  have hne : derivationCompLieHom (B := k)
      (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom h ≠ 0 := by
    rw [hφ]; simpa only [LieEquiv.coe_toLieHom, map_zero] using
      (Derivation.adDerivationLieEquiv k
        (Derivation.pointInCounitAlgebra (CommAlgCat.of k k) g)).injective.ne t.h_ne_zero
  have hmap : (t.map (Derivation.adDerivationLieEquiv k
        (Derivation.pointInCounitAlgebra (CommAlgCat.of k k) g)).toLieHom
        (by
          simpa only [LieEquiv.coe_toLieHom, map_zero] using
            (Derivation.adDerivationLieEquiv k
              (Derivation.pointInCounitAlgebra (CommAlgCat.of k k) g)).injective.ne
              t.h_ne_zero)).cocharacter =
      t.cocharacter.comp (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom := by
    simpa only [hφ, _root_.CommHopfAlgCat.hom_ofHom] using
      t.cocharacter_map
        (_root_.CommHopfAlgCat.ofHom (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom) hne
  rw [hmap]
  apply BialgHom.ext; intro a
  rw [BialgHom.comp_apply, BialgHom.conjCocharacter_apply]
  exact congrArg t.cocharacter
    (DFunLike.congr_fun (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g) a)

/-- **Weight spaces of `t.cocharacter` are `h`-eigenspaces** on every `H`-comodule `V`. -/
theorem weightSpace_cocharacter_eq_eigenspace (t : IsSl2Triple h e f) (V : Type w) [AddCommGroup V]
    [Module k V] [Comodule k H V] (m : ℤ) :
    DiagonalizableGroup.weightSpace V
        (((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp
          t.cocharacter).toCoalgHom) (Multiplicative.ofAdd m) =
      Module.End.eigenspace (Comodule.differential (R := k) (H := H) (M := V) h) (m : k) := by
  rw [t.cocharacter.weightSpace_cocharacter_eq_eigenspace V m, t.derivationComp_cocharacter_unit]

/-- **Point action on eigenspaces.** For every `H`-comodule `V` and every unit `s : kˣ`, the point
`t.cocharacter(s)` acts on the `(m : k)`-eigenspace of `Comodule.differential h` by `s ^ m`. -/
theorem basePointsRepresentation_pointsHom_cocharacter_of_mem_eigenspace (t : IsSl2Triple h e f)
    (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V] (s : kˣ) {m : ℤ} {v : V}
    (hv : v ∈ Module.End.eigenspace
      (Comodule.differential (R := k) (H := H) (M := V) h) (m : k)) :
    Comodule.basePointsRepresentation (H := H) V (Cocharacter.pointsHom k t.cocharacter s) v =
      ((s ^ m : kˣ) : k) • v := by
  rw [← t.weightSpace_cocharacter_eq_eigenspace V m] at hv
  let eMult := AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ
  let π : H →ₐc[k] MonoidAlgebra k (Multiplicative ℤ) := eMult.toBialgHom.comp t.cocharacter
  let q : WithConv (MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] k) :=
    toConv ((laurentEval (R := k) s).comp eMult.symm.toAlgEquiv.toAlgHom)
  have hmap : BialgHom.mapDomain π q = Cocharacter.pointsHom k t.cocharacter s := by
    rw [Cocharacter.pointsHom_apply]
    apply ofConv_injective; ext a
    simp [π, q, BialgHom.mapDomain_apply, eMult]
  have ht : eMult.symm.toAlgEquiv (MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : k)) =
      LaurentPolynomial.T m := by
    apply eMult.injective
    rw [← AddMonoidAlgebra.toMultiplicativeBialgEquiv_single (R := k) (A := k) (M := ℤ) m 1]
    exact eMult.apply_symm_apply _
  rw [← hmap, ← Comodule.basePointsRepresentation_corestrict π q]
  let _ : Comodule k (MonoidAlgebra k (Multiplicative ℤ)) V := Comodule.Corestrict π.toCoalgHom
  rw [Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul,
    Comodule.corestrict_coact_apply, DiagonalizableGroup.mem_weightSpace.mp hv]
  simp only [q, one_smul, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ht, laurentEval_T, TensorProduct.comm_tmul,
    TensorProduct.lid_tmul]

/-- **Adjoint weight spaces of `t.cocharacter` are `ad h`-eigenspaces.** -/
theorem adjointWeightSpace_cocharacter_eq_eigenspace (t : IsSl2Triple h e f) (m : ℤ) :
    Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp t.cocharacter)
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace (ad k (Module.Dual k (Bialgebra.CotangentSpace k H))
        ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm h)) (m : k) := by
  rw [t.cocharacter.adjointWeightSpace_cocharacter_eq_eigenspace m,
    t.derivationComp_cocharacter_unit]

/-- Transporting the `n`-adjoint weight space of `t.cocharacter` across `cotangentLinearEquiv`
yields the `(n : k)`-eigenspace of `ad h` on `Lie(G)`. -/
theorem map_cotangentLinearEquiv_adjointWeightSpace (t : IsSl2Triple h e f) (n : ℤ) :
    Submodule.map (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) : _ →ₗ[k] _)
        (Derivation.adjointWeightSpace
          ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp t.cocharacter)
          (Multiplicative.ofAdd n)) =
      Module.End.eigenspace (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [t.cocharacter.map_cotangentLinearEquiv_adjointWeightSpace_cocharacter n,
    t.derivationComp_cocharacter_unit]

/-- **The integer eigenspaces of `ad h` on `Lie(G)` form an internal direct sum.** -/
theorem isInternal_eigenspace_ad (t : IsSl2Triple h e f) :
    DirectSum.IsInternal fun j : ℤ ↦
      Module.End.eigenspace
        (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (j : k) := by
  simpa only [LieAlgebra.ad_eq_toEnd] using
    TauCeti.isInternal_eigenspace_toEnd_intCast
      (M := Derivation k H (Bialgebra.CounitAlgebra k H k)) t

/-- **The adjoint action of `t.cocharacter` at `s : kˣ` is the grading automorphism
`TauCeti.gradingAut`.** -/
theorem adDerivationLieEquiv_pointsHom_cocharacter (t : IsSl2Triple h e f) (s : kˣ) :
    Derivation.adDerivationLieEquiv k
        (Derivation.pointInCounitAlgebra (CommAlgCat.of k k)
          (Cocharacter.pointsHom k t.cocharacter s)) =
      TauCeti.gradingAut t.isInternal_eigenspace_ad s := by
  let _ := Derivation.adjointComodule (R := k) (H := H)
  apply LieEquiv.ext
  intro d
  refine LinearMap.congr_fun (TauCeti.eq_gradingAut t.isInternal_eigenspace_ad
    (φ := (Derivation.adDerivationLieEquiv k
      (Derivation.pointInCounitAlgebra (CommAlgCat.of k k)
        (Cocharacter.pointsHom k t.cocharacter s))).toLinearEquiv.toLinearMap) fun j y hy ↦ ?_) d
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).surjective y
  rw [← t.map_cotangentLinearEquiv_adjointWeightSpace j, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply, Derivation.adjointWeightSpace_eq_weightSpace,
    t.weightSpace_cocharacter_eq_eigenspace] at hy
  have hact := t.basePointsRepresentation_pointsHom_cocharacter_of_mem_eigenspace
    (Module.Dual k (Bialgebra.CotangentSpace k H)) s hy
  have hend := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (R := k) (H := H) (CommAlgCat.of k k) (Cocharacter.pointsHom k t.cocharacter s) (1 ⊗ₜ[k] x)
  have h1 : Comodule.endOfPoint (Module.Dual k (Bialgebra.CotangentSpace k H))
      (Cocharacter.pointsHom k t.cocharacter s).ofConv (1 ⊗ₜ[k] x) =
      1 ⊗ₜ[k] Comodule.basePointsRepresentation (H := H)
        (Module.Dual k (Bialgebra.CotangentSpace k H))
        (Cocharacter.pointsHom k t.cocharacter s) x := by
    rw [Comodule.endOfPoint_tmul, one_smul,
      Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
  have h1eq (f : Module.Dual k (Bialgebra.CotangentSpace k H)) :
      Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := CommAlgCat.of k k)
          (1 ⊗ₜ[k] f) =
        Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) f := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
    rw [Derivation.tangentScalarExtensionEquiv_tmul, TauCeti.algEquivSelf_derivation_smul_apply,
      one_mul, Algebra.ofId_self, Derivation.mapValue_id, LinearMap.id_apply]
  rw [h1, hact, h1eq, h1eq, map_smul] at hend
  rw [LinearEquiv.coe_toLinearMap, LieEquiv.coe_toLinearEquiv,
    Derivation.adDerivationLieEquiv_apply, ← hend]
  ext a
  rfl

/-- **The underlying submodule of `Lie(P_G(t.cocharacter))` is the supremum of the
`(n : k)`-eigenspaces of `ad h` on `Lie(G)` for `0 ≤ n`.** -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    ((parabolicDefiningHopfIdeal t.cocharacter).lieSubalgebra (B := k)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 ≤ n), Module.End.eigenspace
        (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [t.cocharacter.lieSubalgebra_parabolicDefiningHopfIdeal_eq_iSup_eigenspace,
    t.derivationComp_cocharacter_unit]

/-- **The underlying submodule of `Lie(U_G(t.cocharacter))` is the supremum of the
`(n : k)`-eigenspaces of `ad h` on `Lie(G)` for `0 < n`.** -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    (t.cocharacter.unipotentDefiningHopfIdeal.lieSubalgebra (B := k)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 < n), Module.End.eigenspace
        (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [t.cocharacter.lieSubalgebra_unipotentDefiningHopfIdeal_eq_iSup_eigenspace,
    t.derivationComp_cocharacter_unit]

/-- **The underlying submodule of `Lie(Z_G(t.cocharacter))` is the zero eigenspace of `ad h`
on `Lie(G)`.** -/
theorem lieSubalgebra_leviDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    ((leviDefiningHopfIdeal t.cocharacter).lieSubalgebra (B := k)).toSubmodule =
      Module.End.eigenspace
        (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) 0 := by
  rw [t.cocharacter.lieSubalgebra_leviDefiningHopfIdeal_eq_eigenspace,
    t.derivationComp_cocharacter_unit]

/-- **The dynamic Levi subgroup `Z_G(t.cocharacter)` and the centralizer `C_G(h)` have the same
tangent Lie algebra.** -/
theorem lieSubalgebra_leviDefiningHopfIdeal_cocharacter_eq_centralizerHopfIdeal
    (t : IsSl2Triple h e f) :
    (leviDefiningHopfIdeal t.cocharacter).lieSubalgebra (B := k) =
      (centralizerHopfIdeal H
        ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm h)).lieSubalgebra
          (B := k) := by
  simpa only [t.derivationComp_cocharacter_unit] using
    t.cocharacter.lieSubalgebra_leviDefiningHopfIdeal_eq_centralizerHopfIdeal

/-- **The dynamic Levi subgroup `Z_G(t.cocharacter)` is a closed subgroup scheme of the
centralizer `C_G(h)`** (contravariantly, the centralizer ideal lies in the Levi ideal). -/
theorem centralizerHopfIdeal_le_leviDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    centralizerHopfIdeal H ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm h) ≤
      leviDefiningHopfIdeal t.cocharacter := by
  simpa only [t.derivationComp_cocharacter_unit] using
    t.cocharacter.centralizerHopfIdeal_le_leviDefiningHopfIdeal

end IsSl2Triple
