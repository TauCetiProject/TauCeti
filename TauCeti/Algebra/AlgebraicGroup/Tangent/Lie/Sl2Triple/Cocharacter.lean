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
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Centralizer
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Connected
import TauCeti.Algebra.AlgebraicGroup.Tangent.Rigidity
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
theorem cocharacter_def (t : IsSl2Triple h e f) : t.cocharacter =
    (SpecialLinear.simpleCorootCocharacter 1 k 0).comp t.sl2CoordinateMap.hom := (rfl)

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
  have hhom : _root_.CommHopfAlgCat.ofHom t.symm.cocharacter =
      _root_.CommHopfAlgCat.ofHom t.cocharacter.oppositeCocharacter := by
    apply CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq_of_geometricallyConnected
      (MultiplicativeGroup.geometricallyConnectedCommHopfAlgProperty_laurentPolynomial k)
    ext d x
    rw [_root_.CommHopfAlgCat.hom_ofHom, _root_.CommHopfAlgCat.hom_ofHom,
      derivationCompLieHom_apply, derivationCompLieHom_apply]
    have hopp : derivationComp (B := k) t.cocharacter.oppositeCocharacter d =
        -derivationComp (B := k) t.cocharacter d := by
      rw [t.cocharacter.oppositeCocharacter_eq_comp_domCongrBialgEquiv_neg, derivationComp_comp,
        LinearMap.comp_apply, MultiplicativeGroup.derivationComp_invert, map_neg]
    rw [t.symm.derivationComp_cocharacter, hopp, neg_apply, t.derivationComp_cocharacter,
      smul_neg, neg_apply]
  exact congrArg _root_.CommHopfAlgCat.Hom.hom hhom

/-- **Conjugation compatibility of `t.cocharacter`.** Conjugating an `sl₂` triple by the adjoint
action of a rational point `g` conjugates its attached cocharacter via `BialgHom.conjCocharacter`.
-/
theorem cocharacter_adDerivationLieEquiv (t : IsSl2Triple h e f) (g : WithConv (H →ₐ[k] k)) :
    (t.mapLieEquiv (Derivation.adDerivationLieEquiv k
        (Derivation.pointInCounitAlgebra k g))).cocharacter = t.cocharacter.conjCocharacter g := by
  have hφ : derivationCompLieHom (B := k) (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom =
      (Derivation.adDerivationLieEquiv k (Derivation.pointInCounitAlgebra k g)).toLieHom := by
    rw [TauCeti.derivationCompLieHom_pointConjugationBialgEquiv (B := k) g,
      Derivation.mapValue_ofId_eq_pointInCounitAlgebra]
  have hne : derivationCompLieHom (B := k) (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom h ≠
      0 := hφ ▸ (t.mapLieEquiv _).h_ne_zero
  have hmap := t.cocharacter_map
    (_root_.CommHopfAlgCat.ofHom (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom) hne
  simp only [hφ, _root_.CommHopfAlgCat.hom_ofHom] at hmap
  rw [hmap]; apply BialgHom.ext; intro a; rw [BialgHom.comp_apply, BialgHom.conjCocharacter_apply]
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
    (hv : v ∈ Module.End.eigenspace (Comodule.differential (R := k) (H := H) (M := V) h) (m : k)) :
    Comodule.basePointsRepresentation (H := H) V (Cocharacter.pointsHom k t.cocharacter s) v =
      ((s ^ m : kˣ) : k) • v :=
  t.cocharacter.basePointsRepresentation_pointsHom_of_mem_weightSpace s
    ((t.weightSpace_cocharacter_eq_eigenspace V m).symm ▸ hv)

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
      Module.End.eigenspace (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (j : k) := by
  simpa only [LieAlgebra.ad_eq_toEnd] using TauCeti.isInternal_eigenspace_toEnd_intCast
    (M := Derivation k H (Bialgebra.CounitAlgebra k H k)) t

/-- **The adjoint action of `t.cocharacter` at `s : kˣ` is the grading automorphism
`TauCeti.gradingAut`.** -/
theorem adDerivationLieEquiv_pointsHom_cocharacter (t : IsSl2Triple h e f) (s : kˣ) :
    Derivation.adDerivationLieEquiv k (Derivation.pointInCounitAlgebra (CommAlgCat.of k k)
        (Cocharacter.pointsHom k t.cocharacter s)) =
      TauCeti.gradingAut t.isInternal_eigenspace_ad s := by
  let _ := Derivation.adjointComodule (R := k) (H := H); apply LieEquiv.ext; intro d
  refine LinearMap.congr_fun (TauCeti.eq_gradingAut t.isInternal_eigenspace_ad
    (φ := (Derivation.adDerivationLieEquiv k (Derivation.pointInCounitAlgebra (CommAlgCat.of k k)
      (Cocharacter.pointsHom k t.cocharacter s))).toLinearEquiv.toLinearMap) fun j y hy ↦ ?_) d
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).surjective y
  rw [← t.map_cotangentLinearEquiv_adjointWeightSpace j, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply, Derivation.adjointWeightSpace_eq_weightSpace,
    t.weightSpace_cocharacter_eq_eigenspace] at hy
  have hact := t.basePointsRepresentation_pointsHom_cocharacter_of_mem_eigenspace
    (Module.Dual k (Bialgebra.CotangentSpace k H)) s hy
  have hend := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (R := k) (H := H) (CommAlgCat.of k k) (Cocharacter.pointsHom k t.cocharacter s) (1 ⊗ₜ[k] x)
  have h1eq (f : Module.Dual k (Bialgebra.CotangentSpace k H)) :
      Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := CommAlgCat.of k k)
        (1 ⊗ₜ[k] f) = Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) f := by
    ext a; apply (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
    rw [Derivation.tangentScalarExtensionEquiv_tmul, TauCeti.algEquivSelf_derivation_smul_apply,
      one_mul, Algebra.ofId_self, Derivation.mapValue_id, LinearMap.id_apply]
  rw [Comodule.endOfPoint_tmul, one_smul,
    Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation, hact, h1eq, h1eq,
    map_smul] at hend
  rw [LinearEquiv.coe_toLinearMap, LieEquiv.coe_toLinearEquiv,
    Derivation.adDerivationLieEquiv_apply]; exact hend.symm

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
      Module.End.eigenspace (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) 0 := by
  rw [t.cocharacter.lieSubalgebra_leviDefiningHopfIdeal_eq_eigenspace,
    t.derivationComp_cocharacter_unit]

/-- **The dynamic Levi subgroup `Z_G(t.cocharacter)` and the centralizer `C_G(h)` have the same
tangent Lie algebra.** -/
theorem lieSubalgebra_leviDefiningHopfIdeal_cocharacter_eq_centralizerHopfIdeal
    (t : IsSl2Triple h e f) :
    (leviDefiningHopfIdeal t.cocharacter).lieSubalgebra (B := k) =
      (centralizerHopfIdeal H
        ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm h)).lieSubalgebra (B := k) := by
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
