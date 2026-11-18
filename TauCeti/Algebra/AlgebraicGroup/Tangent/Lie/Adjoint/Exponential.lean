/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.OneParameter
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Representation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.Lie.AdjointAction.ExpAdSubgroup
public import TauCeti.Algebra.Lie.AdjointAction.InnerAutomorphismGroup
public import TauCeti.Algebra.Lie.AdjointAction.InvariantZeroLocus
public import TauCeti.Algebra.Lie.Reductive.InvariantZeroLocus
public import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
import TauCeti.Algebra.Lie.TracePowerPolynomial

/-!
# Adjoint exponentials and group-level Kostant conjugacy

Let `G = Spec H` be an affine algebraic group of finite type over a field `k` of characteristic
zero, with Lie algebra `𝔤 = (CotangentSpace k H)*`. This file connects the intrinsic exponential
curves `Bialgebra.expPointAt` on `H` to inner automorphisms `exp (ad x)` of `𝔤`:

* **Automatic local nilpotence**: if `x ∈ 𝔤` vanishes on positive-degree invariants in `S(𝔤*)^𝔤`
  (in particular for `ad`-nilpotent elements in `⁅𝔤, 𝔤⁆` for reductive `𝔤`, or in `𝔤` when
  `IsKilling k 𝔤`), its left-invariant derivation is locally nilpotent on `H` (no `IsAlgClosed`
  or connectedness needed).
* **Adjoint action**: `basePointsAdjointLieEquiv (expPointAt x t) = expAd (t • x)`.
* **Realization & Kostant conjugacy**: `expAdSubgroup k e` lies in `C_G(e)(k)` (and `C_G(e)°(k)`
  for `IsAlgClosed k`); `Int(𝔤)` lies in `G(k)` (and `G°(k)`); `sl₂` triples sharing `e` are
  conjugate in `C_G(e)(k)` (`IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizer_eq`).

## References

* B. Kostant, Amer. J. Math. **81** (1959), 973–1032, Theorem 3.6.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, 1993,
  Theorem 3.4.10.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
-/

public section

open scoped TensorProduct
open WithConv LieAlgebra

namespace TauCeti

open _root_.TauCeti.Bialgebra Comodule
open Derivation hiding map_smul

universe u

section LocalNilpotence

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (CotangentSpace k H)

@[instance_reducible]
private noncomputable def comoduleLieRingModule (M : Type*) [AddCommGroup M] [Module k M]
    [Comodule k H M] : LieRingModule 𝔤 M where
  bracket x m :=
    differential (R := k) (H := H) (M := M) (cotangentDualLieEquiv (R := k) (H := H) x) m
  add_lie _ _ _ := by simp only [map_add, LinearMap.add_apply]
  lie_add _ m n := map_add _ m n
  leibniz_lie x y m := by
    let : LieRing (Module.End k M) := LieRing.ofAssociativeRing
    have hm := LinearMap.congr_fun ((differential (R := k) (H := H) (M := M)).map_lie
      (x := cotangentDualLieEquiv (R := k) (H := H) x)
      (y := cotangentDualLieEquiv (R := k) (H := H) y)) m
    rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, mul_apply_eq_comp,
      mul_apply_eq_comp] at hm
    rw [LieEquiv.map_lie, hm, sub_add_cancel]

omit [CharZero k] [Algebra.FiniteType k H] in
private theorem comoduleLieModule (M : Type*) [AddCommGroup M] [Module k M] [Comodule k H M] :
    letI := comoduleLieRingModule (k := k) (H := H) M
    LieModule k 𝔤 M :=
  letI := comoduleLieRingModule (k := k) (H := H) M
  { smul_lie := fun r x m ↦ by
      change differential (cotangentDualLieEquiv (r • x)) m =
        r • differential (cotangentDualLieEquiv x) m
      rw [map_smul, map_smul, LinearMap.smul_apply]
    lie_smul := fun r _ m ↦ map_smul _ r m }

/-- **Common zeros of positive-degree Lie invariants have locally nilpotent invariant
derivations.** Over a field of characteristic zero, if every `p ∈ S(𝔤*)^𝔤` with zero constant term
vanishes at `x ∈ 𝔤`, then the left-invariant derivation of `x` is locally nilpotent on `H`.
No algebraic-closure or connectedness hypothesis is needed. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_lift_eval_eq_zero {x : 𝔤}
    (hx : ∀ p ∈ SymmetricAlgebra.lieInvariants k 𝔤 (Module.Dual k 𝔤),
      SymmetricAlgebra.algebraMapInv p = 0 →
        _root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p = 0) :
    ∀ h : H, ∃ m,
      (leftInvariantDerivation (cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0 := by
  obtain ⟨M, n, b, hsurj⟩ := exists_coordinateBialgHom_surjective (k := k) (H := H)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k M := Module.Finite.of_basis b
  let : LieRingModule 𝔤 M := comoduleLieRingModule (k := k) (H := H) M
  let : LieModule k 𝔤 M := comoduleLieModule (k := k) (H := H) M
  have hnil : IsNilpotent
      (differential (R := k) (H := H) (M := M) (cotangentDualLieEquiv (R := k) (H := H) x)) :=
    (show LieModule.toEnd k 𝔤 M x = differential (cotangentDualLieEquiv x) from rfl) ▸
      isNilpotent_toEnd_of_forall_lift_eval_eq_zero (K := k) (L := 𝔤) M hx
  exact (cotangentDualLieEquiv (R := k) (H := H) x)
    |>.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential b hsurj hnil

/-- **Local nilpotence for `ad`-nilpotent elements in the derived ideal of a reductive Lie
algebra.** No algebraic-closure or connectedness hypothesis is needed. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_mem_derivedSeries_of_isNilpotent_ad
    [HasCentralRadical k 𝔤] {x : 𝔤}
    (hder : x ∈ derivedSeries k 𝔤 1) (hnil : IsNilpotent (ad k 𝔤 x)) :
    ∀ h : H, ∃ m,
      (leftInvariantDerivation (cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0 :=
  exists_iterate_leftInvariantDerivation_eq_zero_of_forall_lift_eval_eq_zero
    (mem_derivedSeries_and_isNilpotent_ad_iff_forall_lift_eval_eq_zero.mp ⟨hder, hnil⟩)

/-- **Local nilpotence for `ad`-nilpotent elements when the Killing form is nondegenerate.** No
algebraic-closure or connectedness hypothesis is needed. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad
    [IsKilling k 𝔤] {x : 𝔤} (hnil : IsNilpotent (ad k 𝔤 x)) :
    ∀ h : H, ∃ m,
      (leftInvariantDerivation (cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0 :=
  exists_iterate_leftInvariantDerivation_eq_zero_of_forall_lift_eval_eq_zero
    (isNilpotent_ad_iff_forall_lift_eval_eq_zero.mp hnil)

end LocalNilpotence

section AdjointAction

variable {k H : Type u} [CommRing k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (CotangentSpace k H)] [Module.Projective k (CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (CotangentSpace k H)

attribute [local instance] adjointComodule

private theorem differential_cotangentDualLieEquiv_eq_ad (x : 𝔤) :
    differential (R := k) (H := H) (M := 𝔤) (cotangentDualLieEquiv (R := k) (H := H) x) =
      ad k 𝔤 x := by
  ext y; rw [differential_adjointComodule, LieEquiv.symm_apply_apply, ad_apply]

/-- If the left-invariant derivation of `x ∈ 𝔤` is locally nilpotent on `H`, then `ad x` is
nilpotent on `𝔤`. -/
theorem isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero {x : 𝔤}
    (hx : ∀ h : H, ∃ m,
      (leftInvariantDerivation (cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0) :
    IsNilpotent (ad k 𝔤 x) :=
  differential_cotangentDualLieEquiv_eq_ad x ▸ isNilpotent_differential (M := 𝔤) _ hx

variable [Algebra ℚ H] [LieAlgebra ℚ (Module.Dual k (CotangentSpace k H))]

/-- **Adjoint action of an exponential curve.** The base-point adjoint automorphism of
`expPointAt x t` is `expAd (t • x)`. -/
theorem basePointsAdjointLieEquiv_expPointAt {x : 𝔤}
    (hx : ∀ h : H, ∃ m,
      (leftInvariantDerivation (cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0)
    (t : k) :
    basePointsAdjointLieEquiv (R := k) (H := H)
        (expPointAt (cotangentDualLieEquiv (R := k) (H := H) x) hx t) =
      expAd (K := k) (t • x)
        (((isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero hx).smul t)
          |>.exists_pow_apply_eq_zero |> fun h ↦ by simpa only [map_smul] using h) := by
  have hnil : IsNilpotent (ad k 𝔤 (t • x)) :=
    (map_smul (ad k 𝔤) t x).symm ▸
      (isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero hx).smul t
  refine LieEquiv.ext fun y ↦ ?_
  rw [basePointsAdjointLieEquiv_apply, basePointsRepresentation_expPointAt (M := 𝔤),
    differential_cotangentDualLieEquiv_eq_ad]
  have heq : t • ad k 𝔤 x = ad k 𝔤 (t • x) := (map_smul (ad k 𝔤) t x).symm
  conv_lhs => rw [heq]
  exact (expAd_apply (K := k) (t • x) hnil y).symm

/-- **Adjoint action of an exponential point.** The base-point adjoint automorphism of
`expPoint x` is `expAd x`. -/
theorem basePointsAdjointLieEquiv_expPoint {x : 𝔤}
    (hx : ∀ h : H, ∃ m,
      (leftInvariantDerivation (cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0) :
    basePointsAdjointLieEquiv (R := k) (H := H)
        (WithConv.toConv (expPoint (cotangentDualLieEquiv (R := k) (H := H) x) hx)) =
      expAd (K := k) x (IsNilpotent.exists_pow_apply_eq_zero
        (isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero hx)) := by
  rw [← expPointAt_one]
  refine LieEquiv.ext fun y ↦ ?_
  have hnil := isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero hx
  rw [DFunLike.congr_fun (basePointsAdjointLieEquiv_expPointAt (k := k) (H := H) hx 1) y,
    expAd_apply (K := k) _ (by simpa only [one_smul] using hnil),
    expAd_apply (K := k) _ hnil, one_smul]

end AdjointAction

section Realization

open LinearMap.GeneralLinearGroup _root_.TauCeti.CommHopfAlgCat

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (CotangentSpace k H)

attribute [local instance] adjointComodule

omit [CharZero k] in
private theorem adjointLinearEquiv_basePointsAdjointLieEquiv (g : WithConv (H →ₐ[k] k)) :
    (generalLinearEquiv k 𝔤).toMonoidHom
        (Representation.asGroupHom (basePointsRepresentation (H := H) 𝔤) g) =
      (basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv := by
  refine LinearEquiv.ext fun y ↦ ?_
  change (Representation.asGroupHom (basePointsRepresentation (H := H) 𝔤) g : Module.End k 𝔤) y = _
  rw [Representation.asGroupHom_apply, LieEquiv.coe_toLinearEquiv, basePointsAdjointLieEquiv_apply]

/-- **Realizing Kostant's subgroup inside a closed subgroup.** Let `𝔤` be reductive over a field
`k` of characteristic zero and let `I` be a Hopf ideal whose Lie subalgebra contains `ker (ad e)`.
Then every element of `expAdSubgroup k e` is realized as the adjoint automorphism of a rational
point in the closed subgroup cut out by `I`. No algebraic-closure or connectedness hypothesis is
needed. -/
theorem expAdSubgroup_le_map_quotientPointsSubgroup [HasCentralRadical k 𝔤] [LieAlgebra ℚ 𝔤]
    (e : 𝔤) (I : HopfIdeal k H)
    (hI : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ I.lieSubalgebra (B := k)) :
    expAdSubgroup k e ≤
      (quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k k)).map
        ((generalLinearEquiv k 𝔤).toMonoidHom.comp
          (Representation.asGroupHom (basePointsRepresentation (H := H) 𝔤))) := by
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  refine expAdSubgroup_le_iff.2 fun y hy hy_mem ↦ ?_
  obtain ⟨hyker, z, hz⟩ := Submodule.mem_inf.mp hy_mem
  have hD := exists_iterate_leftInvariantDerivation_eq_zero_of_mem_derivedSeries_of_isNilpotent_ad
    (H := H) (hz ▸ lie_mem_derivedSeries_one e z) hy
  set d := cotangentDualLieEquiv (R := k) (H := H) y
  have hdC : d ∈ (centralizerHopfIdeal H e).lieSubalgebra (B := k) := by
    rw [mem_lieSubalgebra_centralizerHopfIdeal_iff]
    rw [LinearMap.mem_ker, ad_apply] at hyker
    rw [← LieEquiv.map_lie, hyker, map_zero]
  refine ⟨expPointAt d hD (1 : k), I.expPointAt_mem_quotientPointsSubgroup (hI hdC) hD (1 : k), ?_⟩
  rw [MonoidHom.comp_apply, adjointLinearEquiv_basePointsAdjointLieEquiv, expPointAt_one,
    basePointsAdjointLieEquiv_expPoint (k := k) (H := H) hD]

/-- Pointwise form of `expAdSubgroup_le_map_quotientPointsSubgroup`: every element of
`expAdSubgroup k e` is realized by `g ∈ quotientPointsSubgroup I` whenever `Lie(C_G(e)) ≤ Lie(I)`.
-/
theorem exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup [HasCentralRadical k 𝔤]
    [LieAlgebra ℚ 𝔤] {e : 𝔤} (I : HopfIdeal k H)
    (hI : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ I.lieSubalgebra (B := k))
    {φ : 𝔤 ≃ₗ[k] 𝔤} (hφ : φ ∈ expAdSubgroup k e) :
    ∃ g ∈ quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k k),
      (basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = φ := by
  obtain ⟨g, hg, hgeq⟩ := expAdSubgroup_le_map_quotientPointsSubgroup (H := H) e I hI hφ
  exact ⟨g, hg, by simpa only [MonoidHom.comp_apply,
    adjointLinearEquiv_basePointsAdjointLieEquiv] using hgeq⟩

/-- Over any field of characteristic zero, `expAdSubgroup k e` is realized inside the centralizer
`C_G(e)(k)`. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_of_mem_expAdSubgroup [HasCentralRadical k 𝔤]
    [LieAlgebra ℚ 𝔤] {e : 𝔤} {φ : 𝔤 ≃ₗ[k] 𝔤} (hφ : φ ∈ expAdSubgroup k e) :
    ∃ g ∈ quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H e) (CommAlgCat.of k k),
      (basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = φ :=
  exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup (centralizerHopfIdeal H e) le_rfl hφ

/-- **Realizing `Int(𝔤)` inside a closed subgroup with full Lie algebra.** When `𝔤` has
nondegenerate Killing form over a field of characteristic zero and `I` is a Hopf ideal with
`I.lieSubalgebra = ⊤`, `Int(𝔤)` lies in the adjoint image of the rational points of `I`. -/
theorem intLieAlgebra_le_map_quotientPointsSubgroup [IsKilling k 𝔤] [LieAlgebra ℚ 𝔤]
    (I : HopfIdeal k H) (hI : I.lieSubalgebra (B := k) = ⊤) :
    intLieAlgebra k 𝔤 ≤
      (quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k k)).map
        (Representation.asGroupHom (basePointsRepresentation (H := H) 𝔤)) := by
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  refine intLieAlgebra_le_iff.2 fun x hx ↦ ?_
  have hD := exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad (H := H) hx
  set d := cotangentDualLieEquiv (R := k) (H := H) x
  refine ⟨expPointAt d hD (1 : k),
    I.expPointAt_mem_quotientPointsSubgroup (hI.symm ▸ LieSubalgebra.mem_top d) hD (1 : k),
    Units.ext <| LinearMap.ext fun y ↦ ?_⟩
  rw [Representation.asGroupHom_apply, coe_ofLinearEquiv_expAd x hx, expPointAt_one,
    ← basePointsAdjointLieEquiv_apply, basePointsAdjointLieEquiv_expPoint (k := k) (H := H) hD,
    expAd_apply (K := k) x hx y]

/-- When `𝔤` has nondegenerate Killing form, every element of `Int(𝔤)` is realized as the adjoint
action of a rational point of `G`, over any characteristic-zero field `k`. -/
theorem exists_basePointsRepresentation_eq_of_mem_intLieAlgebra [IsKilling k 𝔤] [LieAlgebra ℚ 𝔤]
    {φ : LinearMap.GeneralLinearGroup k 𝔤} (hφ : φ ∈ intLieAlgebra k 𝔤) :
    ∃ g : WithConv (H →ₐ[k] k),
      Representation.asGroupHom (basePointsRepresentation (H := H) 𝔤) g = φ := by
  obtain ⟨g, -, hgeq⟩ := intLieAlgebra_le_map_quotientPointsSubgroup (H := H) (⊥ : HopfIdeal k H)
    (HopfIdeal.lieSubalgebra_bot (R := k) (H := H) (B := k)) hφ
  exact ⟨g, hgeq⟩

end Realization

section IdentityComponent

open LinearMap.GeneralLinearGroup _root_.TauCeti.CommHopfAlgCat

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

local notation "𝔤" => Module.Dual k (CotangentSpace k H)

attribute [local instance] adjointComodule

/-- Over an algebraically closed field of characteristic zero, every element of `expAdSubgroup k e`
is realized by a rational point in the identity component `C_G(e)°(k)` of the centralizer. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_identityComponent_of_mem_expAdSubgroup
    [HasCentralRadical k 𝔤] [LieAlgebra ℚ 𝔤] {e : 𝔤} {φ : 𝔤 ≃ₗ[k] 𝔤}
    (hφ : φ ∈ expAdSubgroup k e) :
    ∃ g ∈ quotientPointsSubgroup H.obj (centralizerHopfIdeal H e).identityComponent
        (CommAlgCat.of k k),
      (basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = φ :=
  exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup
    (centralizerHopfIdeal H e).identityComponent
    (by rw [HopfIdeal.lieSubalgebra_identityComponent]) hφ

/-- Over an algebraically closed field of characteristic zero, when `𝔤` has nondegenerate Killing
form, every element of `Int(𝔤)` is realized by a rational point of the identity component `G°(k)`.
-/
theorem exists_mem_identityComponent_basePointsRepresentation_eq_of_mem_intLieAlgebra
    [IsKilling k 𝔤] [LieAlgebra ℚ 𝔤] {φ : LinearMap.GeneralLinearGroup k 𝔤}
    (hφ : φ ∈ intLieAlgebra k 𝔤) :
    ∃ g ∈ quotientPointsSubgroup H.obj (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (CommAlgCat.of k k),
      Representation.asGroupHom (basePointsRepresentation (H := H) 𝔤) g = φ :=
  intLieAlgebra_le_map_quotientPointsSubgroup (H := H)
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top hφ

end IdentityComponent

end TauCeti

namespace IsSl2Triple

open TauCeti WithConv CommHopfAlgCat Comodule

universe u

attribute [local instance] Derivation.adjointComodule

section General

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Group-level Kostant conjugacy in a closed subgroup.** Two `sl₂` triples `(h, e, f)` and
`(h', e, f')` sharing their nilpositive element `e` in a reductive Lie algebra over a field of
characteristic zero are conjugate by a rational point of any closed subgroup `I` whose Lie algebra
contains `ker (ad e)`. -/
theorem exists_mem_quotientPointsSubgroup_eq_of_centralizer_lieSubalgebra_le
    [LieAlgebra.HasCentralRadical k 𝔤]
    {h e f h' f' : 𝔤} (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') (I : HopfIdeal k H)
    (hI : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ I.lieSubalgebra (B := k)) :
    ∃ g ∈ quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k k),
      basePointsRepresentation (H := H) 𝔤 g e = e ∧
      basePointsRepresentation (H := H) 𝔤 g h = h' ∧
      basePointsRepresentation (H := H) 𝔤 g f = f' := by
  let : LieAlgebra ℚ 𝔤 := ratLieAlgebra k 𝔤
  obtain ⟨φ, hφ, hφe, hφh, hφf⟩ := t.exists_lieEquiv_apply_eq (K := k) t'
  obtain ⟨g, hg, hgeq⟩ := exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup I hI hφ
  have happly {x y : 𝔤} (hxy : φ x = y) : basePointsRepresentation (H := H) 𝔤 g x = y := by
    simpa only [LieEquiv.coe_toLinearEquiv, Derivation.basePointsAdjointLieEquiv_apply] using
      (LinearEquiv.congr_fun hgeq x).trans hxy
  exact ⟨g, hg, happly hφe, happly hφh, happly hφf⟩

/-- **Group-level Kostant conjugacy in `C_G(e)(k)`.** Two `sl₂` triples `(h, e, f)` and
`(h', e, f')` sharing `e` in a reductive Lie algebra over a characteristic-zero field are conjugate
by a rational point of `C_G(e)(k)`. No algebraic-closure or connectedness hypothesis is needed. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_eq [LieAlgebra.HasCentralRadical k 𝔤]
    {h e f h' f' : 𝔤} (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H e) (CommAlgCat.of k k),
      basePointsRepresentation (H := H) 𝔤 g e = e ∧
      basePointsRepresentation (H := H) 𝔤 g h = h' ∧
      basePointsRepresentation (H := H) 𝔤 g f = f' :=
  t.exists_mem_quotientPointsSubgroup_eq_of_centralizer_lieSubalgebra_le t'
    (centralizerHopfIdeal H e) le_rfl

end General

section IdentityComponent

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Group-level Kostant conjugacy in `C_G(e)°(k)`.** Over an algebraically closed field of
characteristic zero, two `sl₂` triples `(h, e, f)` and `(h', e, f')` sharing `e` in a reductive Lie
algebra are conjugate by a rational point of `C_G(e)°(k)`. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_identityComponent_eq
    [LieAlgebra.HasCentralRadical k 𝔤]
    {h e f h' f' : 𝔤} (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ quotientPointsSubgroup H.obj (centralizerHopfIdeal H e).identityComponent
        (CommAlgCat.of k k),
      basePointsRepresentation (H := H) 𝔤 g e = e ∧
      basePointsRepresentation (H := H) 𝔤 g h = h' ∧
      basePointsRepresentation (H := H) 𝔤 g f = f' :=
  t.exists_mem_quotientPointsSubgroup_eq_of_centralizer_lieSubalgebra_le t'
    (centralizerHopfIdeal H e).identityComponent
    (by rw [HopfIdeal.lieSubalgebra_identityComponent])

end IdentityComponent

end IsSl2Triple
