/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Weights
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.FiniteType
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Algebra.AlgebraicGroup.Tangent.Rigidity

/-!
# Cocharacter weight spaces as eigenspaces and the dynamic Levi in characteristic zero

Let `l : H →ₐc[k] k[T;T⁻¹]` be a cocharacter of an affine group `G = Spec H` over a field `k` of
characteristic zero, and let `dl(1)` denote the image under `dl` of the canonical unit tangent
vector `(MultiplicativeGroup.tangentLinearEquiv).symm 1` of `𝔾ₘ`.

1. **Cocharacter weight spaces equal eigenspaces.** Over any field `k` of characteristic zero, the
   `m`-weight space of `l` in any `H`-comodule `V` coincides with the `(m : k)`-eigenspace of the
   differentiated endomorphism `Comodule.differential (dl(1))`
   (`TauCeti.Cocharacter.weightSpace_eq_eigenspace_differential`), with no finite-dimensionality,
   antipode, or algebraic-closure hypothesis.
2. **Adjoint eigenspaces and dynamic Lie algebras.** Specializing to the adjoint representation on
   `𝔤 = Module.Dual k (Bialgebra.CotangentSpace k H)` identifies the `m`-weight space of `l` with
   the `(m : k)`-eigenspace of `ad(dl(1))` (`BialgHom.adjointWeightSpace_eq_eigenspace_ad`), so the
   Lie algebras of `P(l)` and `U(l)` are `⨁_{n ≥ 0} ker(ad(dl(1)) - n)` and
   `⨁_{n > 0} ker(ad(dl(1)) - n)`
   (`BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_eq_iSup_eigenspace`,
   `BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_eq_iSup_eigenspace`).
3. **Dynamic Levi equals Lie centralizer.** Differentiating inner conjugation by a base-valued point
   `g` gives `Ad(g)` (`TauCeti.derivationComp_pointConjugationBialgEquiv`,
   `BialgHom.derivationComp_conjCocharacter`), while `g ∈ Z_G(l)(R)` holds if and only if
   `l.conjCocharacter g = l` (`TauCeti.Cocharacter.mem_levi_iff_conjCocharacter_eq`). Over an
   algebraically closed field of characteristic zero, connectedness of `𝔾ₘ`, Cartier smoothness, and
   homomorphism rigidity identify the dynamic Levi `Z_G(l)` as a closed subgroup scheme with the
   Lie centralizer `C_G(dl(1))` (`BialgHom.leviDefiningHopfIdeal_eq_centralizerHopfIdeal_unit`).

## Main declarations

* `TauCeti.derivationComp_pointConjugationBialgEquiv` and `BialgHom.derivationComp_conjCocharacter`:
  differentiating inner conjugation and conjugated cocharacters over any commutative ring.
* `TauCeti.Cocharacter.mem_levi_iff_conjCocharacter_eq`: a rational point lies in `levi R l` iff it
  fixes `l` under conjugation.
* `TauCeti.Cocharacter.weightSpace_eq_eigenspace_differential`: in characteristic zero, the
  `m`-weight space of `l` in any comodule equals the `(m : k)`-eigenspace of `dl(1)`.
* `BialgHom.adjointWeightSpace_eq_eigenspace_ad`,
  `BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_eq_iSup_eigenspace`, and
  `BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_eq_iSup_eigenspace`: eigenspace descriptions of
  adjoint weight spaces and the Lie algebras of `P(l)` and `U(l)`.
* `BialgHom.leviDefiningHopfIdeal_eq_centralizerHopfIdeal_unit`: over an algebraically closed field
  of characteristic zero, `leviDefiningHopfIdeal l` equals `centralizerHopfIdeal H (dl(1))`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 13.
-/

public section

open CategoryTheory TauCeti TauCeti.Cocharacter WithConv
open scoped DirectSum

universe u v w

/-! ### Differentiating inner conjugation and conjugated cocharacters -/

namespace TauCeti

section PointConjugation

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- Differentiating the inner-conjugation coordinate automorphism by a base-valued point `g` gives
the adjoint action `adDerivation R (pointInCounitAlgebra R g)`. -/
@[simp]
theorem derivationComp_pointConjugationBialgEquiv (g : WithConv (H →ₐ[R] R))
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    derivationComp (B := R) (HopfAlgebra.pointConjugationBialgEquiv g : H →ₐc[R] H) d =
      Derivation.adDerivation R (Derivation.pointInCounitAlgebra R g) d := by
  let C := Bialgebra.CounitAlgebra R H R
  let p := (derivationMulEquivTangentKer R H R (Multiplicative.ofAdd d)).val
  ext a
  have hd : d (HopfAlgebra.pointConjugationAlgHom g a) =
      TrivSqZeroExt.snd
        ((toConv (p.ofConv.comp (HopfAlgebra.pointConjugationAlgHom g))).ofConv a) :=
    (derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d)
      (HopfAlgebra.pointConjugationAlgHom g a)).symm
  have hmap : AlgHom.mapValue (H := H) (Algebra.ofId R (DualNumber C)) g =
      AlgHom.mapValue (H := H) (TrivSqZeroExt.inlAlgHom R C C)
        (Derivation.pointInCounitAlgebra R g) := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Derivation.pointInCounitAlgebra_eq_pointsMulEquiv_symm]
    rw [Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply R H R g b]
    have hb : (Bialgebra.CounitAlgebra.algEquivSelf R H R).symm (g.ofConv b) =
        algebraMap R C (g.ofConv b) := by
      simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
        (Bialgebra.CounitAlgebra.algEquivSelf R H R).symm.commutes (g.ofConv b)
    rw [hb, (TrivSqZeroExt.inlAlgHom R C C).commutes]
    rfl
  have hcoe : ((HopfAlgebra.pointConjugationBialgEquiv g : H →ₐc[R] H) : H →ₐ[R] H) a =
      HopfAlgebra.pointConjugationAlgHom g a := by
    simp [← HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
  rw [derivationComp_apply, hcoe, hd,
    HopfAlgebra.comp_pointConjugationAlgHom, hmap, Derivation.snd_conjugate_tangentPoint]

end PointConjugation

end TauCeti

namespace BialgHom

/-- Rewriting helper expressing `l.conjCocharacter g` as precomposition with
`pointConjugationBialgEquiv g`. -/
theorem conjCocharacter_eq_comp {R : Type u} {H : Type v}
    [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
    (l : H →ₐc[R] LaurentPolynomial R) (g : WithConv (H →ₐ[R] R)) :
    l.conjCocharacter g = l.comp (HopfAlgebra.pointConjugationBialgEquiv g : H →ₐc[R] H) := by
  ext h : 1
  rw [conjCocharacter_apply, comp_apply, BialgEquiv.coe_toBialgHom]
  exact (congrArg l
    (DFunLike.congr_fun (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g) h)).symm

/-- The differential of a conjugated cocharacter `l.conjCocharacter g` is the `Ad(g)`-conjugate of
the differential of `l`. -/
@[simp]
theorem derivationComp_conjCocharacter {R : Type u} {H : Type v}
    [CommRing R] [CommRing H] [HopfAlgebra R H]
    (l : H →ₐc[R] LaurentPolynomial R) (g : WithConv (H →ₐ[R] R))
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) R)) :
    derivationComp (B := R) (l.conjCocharacter g) d =
      Derivation.adDerivation R (Derivation.pointInCounitAlgebra R g)
        (derivationComp (B := R) l d) := by
  rw [conjCocharacter_eq_comp, derivationComp_comp, LinearMap.comp_apply,
    derivationComp_pointConjugationBialgEquiv]

end BialgHom

namespace TauCeti.Cocharacter

/-- A base-valued point `g` lies in the dynamic Levi `levi R l` if and only if conjugating `l` by
`g` leaves `l` unchanged. -/
theorem mem_levi_iff_conjCocharacter_eq {R : Type u} {H : Type v}
    [CommRing R] [CommRing H] [HopfAlgebra R H]
    (l : H →ₐc[R] LaurentPolynomial R) (g : WithConv (H →ₐ[R] R)) :
    g ∈ levi R l ↔ l.conjCocharacter g = l := by
  have hconst : AlgHom.mapValue (H := H) (Algebra.ofId R (LaurentPolynomial R)) g =
      constPoint R g := by
    rw [← constPoint_mapValue_ofId, Algebra.ofId_self, AlgHom.mapValue_id, MonoidHom.id_apply]
  rw [mem_levi_iff, conjugate_apply]
  constructor
  · intro h
    have hcomm : genericPoint R l * constPoint R g = constPoint R g * genericPoint R l :=
      mul_inv_eq_iff_eq_mul.mp h
    have hgen : genericPoint R (l.conjCocharacter g) = genericPoint R l := by
      rw [BialgHom.genericPoint_conjCocharacter, hconst, ← hcomm, mul_assoc, mul_inv_cancel,
        mul_one]
    ext a : 1
    have ha := DFunLike.congr_fun (congrArg WithConv.ofConv hgen) a
    ext n
    simpa [genericPoint_ofConv, AddMonoidAlgebra.coeff_mapAlgHom] using
      congrArg (fun p : LaurentPolynomial R ↦ p.coeff n) ha
  · intro h
    have hgen : genericPoint R (l.conjCocharacter g) = genericPoint R l := by
      rw [h]
    rw [BialgHom.genericPoint_conjCocharacter, hconst] at hgen
    have hcomm : constPoint R g * genericPoint R l = genericPoint R l * constPoint R g :=
      mul_inv_eq_iff_eq_mul.mp hgen
    exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm

/-! ### Characteristic-zero cocharacter weight spaces -/

section CharZeroWeights

variable {k : Type u} [Field k] [CharZero k]
variable {H : Type v} [CommRing H] [Bialgebra k H]
variable (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V]

/-- **Over a field of characteristic zero, the `m`-weight space of a cocharacter `l` in any
rational representation `V` equals the `(m : k)`-eigenspace of its differentiated unit tangent
vector.** No finite-dimensionality, antipode, or algebraic-closure assumption is needed. -/
theorem weightSpace_eq_eigenspace_differential
    (l : H →ₐc[k] LaurentPolynomial k) (m : ℤ) :
    DiagonalizableGroup.weightSpace V
        (((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l).toCoalgHom)
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace
        (Comodule.differential (R := k) (H := H) (M := V)
          (derivationComp (B := k) l
            ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1)))
        (m : k) := by
  let e := AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ
  let π := e.toBialgHom.comp l
  let d₀ := (MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1
  let d := derivationComp (B := k) e.symm.toBialgHom d₀
  have hcomp : e.symm.toBialgHom.comp π = l := by
    ext h
    simp [π, e]
  have hder : derivationComp (B := k) π d = derivationComp (B := k) l d₀ := by
    rw [← LinearMap.comp_apply, ← derivationComp_comp, hcomp]
  have hval (n : ℤ) :
      Bialgebra.CounitAlgebra.algEquivSelf k (MonoidAlgebra k (Multiplicative ℤ)) k
        (d (MonoidAlgebra.single (Multiplicative.ofAdd n) 1)) = (n : k) := by
    have hT : e.symm (MonoidAlgebra.single (Multiplicative.ofAdd n) (1 : k)) =
        LaurentPolynomial.T n := by
      apply e.injective
      rw [← AddMonoidAlgebra.toMultiplicativeBialgEquiv_single (R := k) (A := k) (M := ℤ) n 1]
      exact e.apply_symm_apply _
    rw [algEquivSelf_derivationComp_apply]
    change Bialgebra.CounitAlgebra.algEquivSelf k (LaurentPolynomial k) k
      (d₀ (e.symm (MonoidAlgebra.single (Multiplicative.ofAdd n) 1))) = (n : k)
    rw [hT, MultiplicativeGroup.tangentLinearEquiv_symm_apply_T, zsmul_one]
  have hle (n : ℤ) :
      DiagonalizableGroup.weightSpace V π.toCoalgHom (Multiplicative.ofAdd n) ≤
        Module.End.eigenspace
          (Comodule.differential (R := k) (H := H) (M := V) (derivationComp (B := k) l d₀))
          (n : k) := by
    simpa only [hder, hval n] using
      DiagonalizableGroup.weightSpace_le_eigenspace_differential V π d (Multiplicative.ofAdd n)
  refine le_antisymm (hle m) fun v hv ↦ ?_
  classical
  let : DecidableEq (Multiplicative ℤ) := Classical.decEq _
  let W := DiagonalizableGroup.weightSpace V π.toCoalgHom
  let _ : DirectSum.Decomposition W :=
    (DiagonalizableGroup.isInternal_weightSpace V π.toCoalgHom).chooseDecomposition
  let T : V →ₗ[k] V :=
    Comodule.differential (R := k) (H := H) (M := V) (derivationComp (B := k) l d₀) -
      (m : k) • LinearMap.id
  have hTv : T v = 0 := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Module.End.mem_eigenspace_iff.mp hv, sub_self]
  have hTw (α : Multiplicative ℤ) :
      T (DirectSum.decompose W v α : V) =
        ((α.toAdd : k) - (m : k)) • (DirectSum.decompose W v α : V) := by
    have hmem : (DirectSum.decompose W v α : V) ∈ W (Multiplicative.ofAdd α.toAdd) := by
      rw [ofAdd_toAdd]
      exact (DirectSum.decompose W v α).2
    have heig := Module.End.mem_eigenspace_iff.mp (hle α.toAdd hmem)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, heig, sub_smul]
  let s := (DirectSum.decompose W v).support
  have hsum : ∑ β ∈ s, ((β.toAdd : k) - (m : k)) • (DirectSum.decompose W v β : V) = 0 := by
    calc ∑ β ∈ s, ((β.toAdd : k) - (m : k)) • (DirectSum.decompose W v β : V)
        = ∑ β ∈ s, T (DirectSum.decompose W v β : V) :=
          Finset.sum_congr rfl fun β _ ↦ (hTw β).symm
      _ = T (∑ β ∈ s, (DirectSum.decompose W v β : V)) := (map_sum T _ s).symm
      _ = T v := by rw [DirectSum.sum_support_decompose W v]
      _ = 0 := hTv
  have hzero (α : Multiplicative ℤ) (hαs : α ∈ s) (hα : α ≠ Multiplicative.ofAdd m) :
      (DirectSum.decompose W v α : V) = 0 := by
    let pα : V →ₗ[k] V :=
      (W α).subtype.comp
        ((DirectSum.component k (Multiplicative ℤ) (fun i ↦ W i) α).comp
          (DirectSum.decomposeLinearEquiv W).toLinearMap)
    have hpα (x : V) : pα x = (DirectSum.decompose W x α : V) := rfl
    have hproj := congrArg pα hsum
    rw [map_sum, map_zero, Finset.sum_eq_single α] at hproj
    · have hmem : ((α.toAdd : k) - (m : k)) • (DirectSum.decompose W v α : V) ∈ W α :=
        Submodule.smul_mem _ _ (DirectSum.decompose W v α).2
      rw [hpα, DirectSum.decompose_of_mem_same W hmem] at hproj
      have hne : (α.toAdd : k) - (m : k) ≠ 0 := by
        refine sub_ne_zero.mpr (Int.cast_injective.ne fun heq ↦ hα ?_)
        rw [← heq, ofAdd_toAdd]
      exact (smul_eq_zero.mp hproj).resolve_left hne
    · intro β _ hβα
      have hmem : ((β.toAdd : k) - (m : k)) • (DirectSum.decompose W v β : V) ∈ W β :=
        Submodule.smul_mem _ _ (DirectSum.decompose W v β).2
      rw [hpα]
      exact DirectSum.decompose_of_mem_ne W hmem hβα
    · intro hnot
      exact (hnot hαs).elim
  rw [← DirectSum.sum_support_decompose W v]
  refine Submodule.sum_mem _ fun α hαs ↦ ?_
  by_cases hα : α = Multiplicative.ofAdd m
  · rw [hα]
    exact (DirectSum.decompose W v (Multiplicative.ofAdd m)).2
  · rw [hzero α hαs hα]
    exact Submodule.zero_mem _

end CharZeroWeights

end TauCeti.Cocharacter

namespace BialgHom

section CharZeroAdjoint

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]

attribute [local instance] Derivation.adjointComodule

section CotangentFinite

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- Over a field of characteristic zero, the `m`-weight space of a cocharacter `l` in the adjoint
representation is the `(m : k)`-eigenspace of `ad(dl(1))` on the cotangent-dual Lie algebra. -/
theorem adjointWeightSpace_eq_eigenspace_ad (l : H →ₐc[k] LaurentPolynomial k) (m : ℤ) :
    Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace
        (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H))
          ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
            (derivationComp (B := k) l
              ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1))))
        (m : k) := by
  rw [Derivation.adjointWeightSpace_eq_weightSpace,
    Cocharacter.weightSpace_eq_eigenspace_differential]
  congr 1
  ext x : 1
  exact Derivation.differential_adjointComodule _ x

/-- In characteristic zero, the Lie algebra of `P(l)` is the sum of the nonnegative eigenspaces of
`ad(dl(1))`, transported along `Derivation.cotangentLinearEquiv`. -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_eq_iSup_eigenspace
    (l : H →ₐc[k] LaurentPolynomial k) :
    ((parabolicDefiningHopfIdeal l).lieSubalgebra (B := k)).toSubmodule =
      (⨆ (n : ℤ) (_ : 0 ≤ n), Module.End.eigenspace
          (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H))
            ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
              (derivationComp (B := k) l
                ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1))))
          (n : k)).map
        (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).toLinearMap := by
  rw [lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule]
  simp only [adjointWeightSpace_eq_eigenspace_ad]

/-- In characteristic zero, the Lie algebra of `U(l)` is the sum of the strictly positive
eigenspaces of `ad(dl(1))`, transported along `Derivation.cotangentLinearEquiv`. -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_eq_iSup_eigenspace
    (l : H →ₐc[k] LaurentPolynomial k) :
    (l.unipotentDefiningHopfIdeal.lieSubalgebra (B := k)).toSubmodule =
      (⨆ (n : ℤ) (_ : 0 < n), Module.End.eigenspace
          (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H))
            ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
              (derivationComp (B := k) l
                ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1))))
          (n : k)).map
        (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).toLinearMap := by
  rw [lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule]
  simp only [adjointWeightSpace_eq_eigenspace_ad]

end CotangentFinite

section AlgClosed

variable [IsAlgClosed k] [Algebra.FiniteType k H]

private instance instFiniteTypeLaurentPolynomial : Algebra.FiniteType k (LaurentPolynomial k) :=
  inferInstanceAs (Algebra.FiniteType k (AddMonoidAlgebra k ℤ))

/-- **Over an algebraically closed field of characteristic zero, the dynamic Levi `Z_G(l)` of any
cocharacter equals the scheme-theoretic centralizer `C_G(dl(1))` of its unit tangent vector.** -/
theorem leviDefiningHopfIdeal_eq_centralizerHopfIdeal_unit
    (l : H →ₐc[k] LaurentPolynomial k) :
    leviDefiningHopfIdeal l =
      TauCeti.centralizerHopfIdeal H
        ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
          (derivationComp (B := k) l
            ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1))) := by
  let d₀ := (MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1
  let x := (Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
    (derivationComp (B := k) l d₀)
  let Hcat := _root_.CommHopfAlgCat.of k H
  let _ : Algebra.Smooth k (CommHopfAlgCat.quotient Hcat (leviDefiningHopfIdeal l)) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_charZero k
        (CommHopfAlgCat.quotient Hcat (leviDefiningHopfIdeal l)))
  let _ : IsReduced (CommHopfAlgCat.quotient Hcat (leviDefiningHopfIdeal l)) :=
    isReduced_of_smooth k _
  let _ : Algebra.Smooth k (CommHopfAlgCat.quotient Hcat (TauCeti.centralizerHopfIdeal H x)) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_charZero k
        (CommHopfAlgCat.quotient Hcat (TauCeti.centralizerHopfIdeal H x)))
  let _ : IsReduced (CommHopfAlgCat.quotient Hcat (TauCeti.centralizerHopfIdeal H x)) :=
    isReduced_of_smooth k _
  apply HopfIdeal.eq_of_quotientPointsSubgroup_eq (H := Hcat) (K := k)
  ext g
  rw [quotientPointsSubgroup_leviDefiningHopfIdeal,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff]
  change g ∈ levi k l ↔ _
  rw [Cocharacter.mem_levi_iff_conjCocharacter_eq]
  let Gm := FiniteTypeCommHopfAlgCat.of k (LaurentPolynomial k)
  let _ : ConnectedSpace (PrimeSpectrum Gm) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum (LaurentPolynomial k)))
  have hrig : l.conjCocharacter g = l ↔
      derivationCompLieHom (B := k) (l.conjCocharacter g) = derivationCompLieHom (B := k) l := by
    refine ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
    have hhom : (_root_.CommHopfAlgCat.ofHom (l.conjCocharacter g) : Hcat ⟶ Gm.obj) =
        _root_.CommHopfAlgCat.ofHom l :=
      _root_.CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq (K := Gm) _ _ h
    exact congrArg _root_.CommHopfAlgCat.Hom.hom hhom
  rw [hrig, LieEquiv.apply_symm_apply, Derivation.adDerivationLieEquiv_apply,
    EmbeddingLike.apply_eq_iff_eq]
  constructor
  · intro h
    have hd₀ := DFunLike.congr_fun h d₀
    simpa only [derivationCompLieHom_apply, derivationComp_conjCocharacter] using hd₀
  · intro h
    apply LieHom.ext
    intro d
    have hd : d = MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k) d • d₀ := by
      apply (MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).injective
      rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    rw [hd, map_smul, map_smul, derivationCompLieHom_apply, derivationCompLieHom_apply,
      derivationComp_conjCocharacter]
    exact congrArg (MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k) d • ·) h

end AlgClosed

end CharZeroAdjoint

end BialgHom
