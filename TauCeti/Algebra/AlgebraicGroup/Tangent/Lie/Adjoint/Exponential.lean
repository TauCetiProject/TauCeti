/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Exponential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Comodule
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.Lie.AdjointAction.ExpAdSubgroup
import Mathlib.Algebra.Module.Rat
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.OneParameter
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Tangent
import TauCeti.LinearAlgebra.GeneralLinearGroup.Basic
import TauCeti.RepresentationTheory.Lie.AdNilpotent
import TauCeti.RingTheory.Nilpotent.Log

/-!
# Integrating `ad`-nilpotent elements and `Int(𝔤)` into `G°(k)`

Let `G = Spec H` be an affine group of finite type over a field `k` of characteristic zero whose
Lie algebra `𝔤 = (𝔪 / 𝔪²)*` has nondegenerate Killing form.

An `ad`-nilpotent element `x ∈ 𝔤` acts nilpotently in every finite-dimensional representation of `𝔤`
(`TauCeti.isNilpotent_apply_of_isNilpotent_ad`), hence on every finite-dimensional `G`-comodule
(`TauCeti.Comodule.isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad`). Choosing a
faithful finite-dimensional representation embeds `G` into `GL_d` with nilpotent tangent matrix,
showing that the left-invariant vector field of `x` on `H` is locally nilpotent
(`TauCeti.exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero`).

Its Taylor exponential therefore defines a `k`-point `TauCeti.expAdPoint hx : G(k)` whose action on
any finite-dimensional `ℚ`-module comodule `M` is
`IsNilpotent.exp (differential (cotangentDualLieEquiv x))`
(`TauCeti.Comodule.basePointsRepresentation_expAdPoint`), whose adjoint action on `𝔤` is the
operator exponential `IsNilpotent.exp (ad x) = expAd x`
(`TauCeti.basePointsRepresentation_expAdPoint`, `TauCeti.basePointsAdjointLieEquiv_expAdPoint`),
which is injective in `x` (`TauCeti.expAdPoint_eq_iff`, `TauCeti.expAdPoint_eq_one_iff`), and which
lands in any closed subgroup `Spec (H / I)` whose Lie algebra contains `x`
(`TauCeti.expAdPoint_mem_quotientPointsSubgroup`).
Over an algebraically closed field, `expAdPoint hx` lies in the identity component `G°(k)` and in
`C_G(y)°(k)` whenever `⁅x, y⁆ = 0`, so the entire inner automorphism group `Int(𝔤)` is realized by
rational points of `G°` (`TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent`).

## Main declarations

* `TauCeti.Comodule.isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad`: an
  `ad`-nilpotent element of `𝔤` acts nilpotently on every finite-dimensional `H`-comodule.
* `TauCeti.exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero`: its
  left-invariant derivation on `H` is locally nilpotent.
* `TauCeti.expAdPoint`: the rational point `exp x ∈ G(k)` attached to an `ad`-nilpotent `x ∈ 𝔤`,
  with characteristic lemmas `TauCeti.expAdPoint_def`, `TauCeti.expAdPoint_zero`,
  `TauCeti.expAdPoint_eq_iff`, `TauCeti.expAdPoint_eq_one_iff`,
  `TauCeti.Comodule.basePointsRepresentation_expAdPoint`,
  `TauCeti.basePointsRepresentation_expAdPoint`,
  `TauCeti.basePointsAdjointLieEquiv_expAdPoint`,
  `TauCeti.toHomUnits_basePointsRepresentation_expAdPoint`,
  `TauCeti.isUnipotentPoint_expAdPoint`, and
  `TauCeti.expAdPoint_mem_quotientPointsSubgroup`.
* `TauCeti.basePointsAdjointLieEquiv_expPointAt_toLinearMap`: the adjoint action of the
  one-parameter exponential curve `expPointAt` is `exp (t • ad x)`.
* `TauCeti.expAdPoint_mem_identityComponent` and
  `TauCeti.expAdPoint_mem_centralizer_identityComponent`: subgroup memberships in `G°(k)` and
  `C_G(y)°(k)`.
* `TauCeti.intLieAlgebra_le_range_basePointsRepresentation` and
  `TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent`: `Int(𝔤)` lies in the
  adjoint image of `G(k)` and, over an algebraically closed field, of `G°(k)`.
* `TauCeti.exists_mem_closure_unipotent_quotientPointsSubgroup_of_mem_intLieAlgebra`,
  `TauCeti.exists_mem_closure_unipotent_of_mem_intLieAlgebra`,
  `TauCeti.exists_mem_closure_unipotent_identityComponent_of_mem_intLieAlgebra`, and
  `TauCeti.exists_mem_closure_unipotent_quotientPointsSubgroup_of_mem_expAdSubgroup`: lifting
  `Int(𝔤)` and `expAdSubgroup` to products of unipotent rational points.

## References

* A. Borel, *Linear Algebraic Groups* (2nd ed.), Springer GTM 126, §7.3.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.4.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Comodule

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **An `ad`-nilpotent element of a Killing Lie algebra acts nilpotently on every
finite-dimensional comodule.** -/
theorem isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad
    {k H M : Type*} [Field k] [CharZero k] [CommRing H] [Bialgebra k H]
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M] [Comodule k H M]
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)) :
    IsNilpotent (differential (R := k) (H := H) (M := M)
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)) :=
  TauCeti.isNilpotent_apply_of_isNilpotent_ad
    (ρ := (differential (R := k) (H := H) (M := M)).comp
      (Derivation.cotangentDualLieEquiv (R := k) (H := H)).toLieHom) hx

end TauCeti.Comodule

namespace TauCeti

universe u v

attribute [local instance] Derivation.adjointComodule

section Field

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **An `ad`-nilpotent element of a Killing tangent Lie algebra induces a locally nilpotent
left-invariant derivation on `H`.** -/
theorem exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero
    {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    ∀ a : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] a = 0 := by
  obtain ⟨M, hfaith⟩ := Comodule.exists_isFaithful (k := k) (H := H)
  rcases Comodule.isFaithful_def.mp hfaith with ⟨d, b, _⟩
  have hsurj : Function.Surjective (Comodule.coordinateBialgHom (H := H) b) :=
    (Comodule.coordinateBialgHom_surjective_iff_isFaithful b).mpr hfaith
  exact Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential
    (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) b hsurj
    (Comodule.isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad hx)

/-- **The exponential `k`-point `exp x ∈ G(k)` attached to an `ad`-nilpotent element `x ∈ 𝔤`.** -/
noncomputable def expAdPoint {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    WithConv (H →ₐ[k] k) :=
  letI : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)
    (exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero hx))

/-- **`expAdPoint` unfolds to the Taylor exponential point of `cotangentDualLieEquiv x`.** -/
theorem expAdPoint_def {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    expAdPoint (H := H) hx =
      let : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
      toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)
        (exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero hx)) :=
  (rfl)

/-- **The exponential of `0 ∈ 𝔤` is the identity point of `G(k)`.** -/
@[simp]
theorem expAdPoint_zero (h0 : IsNilpotent (LieAlgebra.ad k 𝔤 (0 : 𝔤))) :
    expAdPoint (H := H) h0 = 1 := by
  let _ : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  simp only [expAdPoint_def, map_zero, Bialgebra.expPoint_zero]
  rfl

/-- **On any finite-dimensional comodule, `expAdPoint hx` acts by the operator exponential of its
differentiated action.** -/
theorem Comodule.basePointsRepresentation_expAdPoint
    {M : Type v} [AddCommGroup M] [Module k M] [Module ℚ M] [FiniteDimensional k M]
    [Comodule k H M] {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    Comodule.basePointsRepresentation (R := k) (H := H) M (expAdPoint (H := H) hx) =
      IsNilpotent.exp (Comodule.differential (R := k) (H := H) (M := M)
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)) := by
  let _ : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  exact Comodule.basePointsRepresentation_expPoint
    (exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero hx)
    (Comodule.isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad hx)

/-- **The adjoint action of `expAdPoint hx` on `𝔤` is the operator exponential `exp (ad x)`.** -/
@[simp]
theorem basePointsRepresentation_expAdPoint {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    Comodule.basePointsRepresentation (R := k) (H := H) 𝔤 (expAdPoint hx) =
      IsNilpotent.exp (LieAlgebra.ad k 𝔤 x) := by
  rw [Comodule.basePointsRepresentation_expAdPoint (M := 𝔤) hx,
    Derivation.differential_cotangentDualLieEquiv]

/-- **Two `ad`-nilpotent elements have the same exponential point if and only if they are equal.**
-/
@[simp]
theorem expAdPoint_eq_iff {x y : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x))
    (hy : IsNilpotent (LieAlgebra.ad k 𝔤 y)) :
    expAdPoint (H := H) hx = expAdPoint (H := H) hy ↔ x = y := by
  refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
  have had : IsNilpotent.exp (LieAlgebra.ad k 𝔤 x) = IsNilpotent.exp (LieAlgebra.ad k 𝔤 y) := by
    simpa [basePointsRepresentation_expAdPoint] using
      congrArg (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤) h
  let _ : Algebra ℚ (Module.End k 𝔤) := Algebra.compHom (Module.End k 𝔤) (algebraMap ℚ k)
  have hexp (z : 𝔤) :
      IsNilpotent.exp (LieAlgebra.ad k 𝔤 z) =
        @IsNilpotent.exp (Module.End k 𝔤) _ Algebra.toModule (LieAlgebra.ad k 𝔤 z) := by
    congr 1; exact Subsingleton.elim _ _
  rw [hexp x, hexp y] at had
  have hlog : LieAlgebra.ad k 𝔤 x = LieAlgebra.ad k 𝔤 y := by
    simpa only [IsNilpotent.log_exp hx, IsNilpotent.log_exp hy] using
      congrArg (@IsNilpotent.log (Module.End k 𝔤) _ Algebra.toModule) had
  exact LieModule.IsFaithful.injective_toEnd (R := k) (L := 𝔤) (M := 𝔤) hlog

/-- **The exponential point of an `ad`-nilpotent element is `1` if and only if the element is `0`.**
-/
@[simp]
theorem expAdPoint_eq_one_iff {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    expAdPoint (H := H) hx = 1 ↔ x = 0 := by
  rw [← expAdPoint_zero (k := k) (H := H) (by simp), expAdPoint_eq_iff]

/-- **If `x` lies in the Lie algebra of a closed subgroup `Spec (H / I)`, then `expAdPoint hx`
lies in that subgroup's `k`-points.** -/
theorem expAdPoint_mem_quotientPointsSubgroup (I : HopfIdeal k H)
    {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x))
    (hxI : Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈ I.lieSubalgebra (B := k)) :
    expAdPoint (H := H) hx ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H) I (CommAlgCat.of k k) := by
  let _ : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  exact I.toConv_expPoint_mem_quotientPointsSubgroup hxI
    (exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero hx)

/-- **As a Lie automorphism, `expAdPoint hx` acts on `𝔤` by `expAd x`.** -/
theorem basePointsAdjointLieEquiv_expAdPoint [LieAlgebra ℚ 𝔤]
    {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    Derivation.basePointsAdjointLieEquiv (R := k) (H := H) (expAdPoint hx) =
      expAd (K := k) x hx.exists_pow_apply_eq_zero := by
  refine LieEquiv.ext fun y ↦ ?_
  rw [Derivation.basePointsAdjointLieEquiv_apply, basePointsRepresentation_expAdPoint hx,
    expAd_apply (K := k) x hx y]
  congr!
  exact Subsingleton.elim _ _

/-- **As a linear automorphism unit, `expAdPoint hx` acts on `𝔤` by `expAd x`.** -/
theorem toHomUnits_basePointsRepresentation_expAdPoint [LieAlgebra ℚ 𝔤]
    {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤).toHomUnits (expAdPoint hx) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv
        (expAd (K := k) x hx.exists_pow_apply_eq_zero).toLinearEquiv := by
  refine Units.ext ?_
  rw [MonoidHom.coe_toHomUnits, basePointsRepresentation_expAdPoint hx,
    coe_ofLinearEquiv_expAd x hx]
  congr!
  exact Subsingleton.elim _ _

/-- **Every exponential point `expAdPoint hx` is unipotent.** -/
@[simp]
theorem isUnipotentPoint_expAdPoint {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    HopfAlgebra.IsUnipotentPoint (expAdPoint (H := H) hx) := by
  let _ : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  exact HopfAlgebra.isUnipotentPoint_expPoint _
    (exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero hx)

omit [CharZero k] [LieAlgebra.IsKilling k 𝔤] in
private theorem toHomUnits_basePointsRepresentation_eq_ofLinearEquiv
    (g : WithConv (H →ₐ[k] k)) :
    (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤).toHomUnits g =
      LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv :=
  Units.ext <| LinearMap.ext fun y ↦ by
    simp [Derivation.basePointsAdjointLieEquiv_apply]

/-- **Lifting `Int(𝔤)` into any closed subgroup with full Lie algebra.** Every inner
automorphism `φ ∈ Int(𝔤)` is realized as `Ad(g)` for a point `g` in the subgroup generated by
the unipotent rational points of any closed subgroup whose tangent Lie algebra is all of `𝔤`. -/
theorem exists_mem_closure_unipotent_quotientPointsSubgroup_of_mem_intLieAlgebra [LieAlgebra ℚ 𝔤]
    (I : HopfIdeal k H) (hI : I.lieSubalgebra (B := k) = ⊤)
    {φ : LinearMap.GeneralLinearGroup k 𝔤} (hφ : φ ∈ intLieAlgebra k 𝔤) :
    ∃ g ∈ Subgroup.closure
        {u ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
            (CommAlgCat.of k k) |
          HopfAlgebra.IsUnipotentPoint u},
      LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = φ := by
  let U : Subgroup (WithConv (H →ₐ[k] k)) :=
    Subgroup.closure
      {u ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
          (CommAlgCat.of k k) |
        HopfAlgebra.IsUnipotentPoint u}
  let toGL : WithConv (H →ₐ[k] k) →* LinearMap.GeneralLinearGroup k 𝔤 :=
    (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤).toHomUnits
  have hle : intLieAlgebra k 𝔤 ≤ U.map toGL := by
    rw [intLieAlgebra_le_iff]
    intro x hx
    refine ⟨expAdPoint hx, Subgroup.subset_closure
      ⟨expAdPoint_mem_quotientPointsSubgroup I hx (hI.symm ▸ LieSubalgebra.mem_top _),
        isUnipotentPoint_expAdPoint hx⟩,
      toHomUnits_basePointsRepresentation_expAdPoint hx⟩
  obtain ⟨g, hg, hgf⟩ := hle hφ
  exact ⟨g, hg, (toHomUnits_basePointsRepresentation_eq_ofLinearEquiv g).symm.trans hgf⟩

/-- **Lifting `Int(𝔤)` to products of unipotent rational points of `G`.** -/
theorem exists_mem_closure_unipotent_of_mem_intLieAlgebra [LieAlgebra ℚ 𝔤]
    {φ : LinearMap.GeneralLinearGroup k 𝔤} (hφ : φ ∈ intLieAlgebra k 𝔤) :
    ∃ g ∈ Subgroup.closure {u : WithConv (H →ₐ[k] k) | HopfAlgebra.IsUnipotentPoint u},
      LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = φ := by
  obtain ⟨g, hg, hgf⟩ := exists_mem_closure_unipotent_quotientPointsSubgroup_of_mem_intLieAlgebra
    (⊥ : HopfIdeal k H) HopfIdeal.lieSubalgebra_bot hφ
  refine ⟨g, ?_, hgf⟩
  refine Subgroup.closure_mono ?_ hg
  rintro _ ⟨-, h⟩
  exact h

/-- **Every inner automorphism in `Int(𝔤)` is the adjoint action of a `k`-point of `G`.** -/
theorem intLieAlgebra_le_range_basePointsRepresentation [LieAlgebra ℚ 𝔤] :
    intLieAlgebra k 𝔤 ≤
      (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤).toHomUnits.range := by
  intro φ hφ
  obtain ⟨g, -, rfl⟩ := exists_mem_closure_unipotent_of_mem_intLieAlgebra hφ
  exact ⟨g, toHomUnits_basePointsRepresentation_eq_ofLinearEquiv g⟩

/-- **Lifting `expAdSubgroup k e` into closed subgroups containing `ker (ad e)`.** If `I` cuts out
a closed subgroup whose tangent Lie algebra contains `Lie(C_G(e))`, then every automorphism in
`TauCeti.expAdSubgroup k e` is realized as `Ad(g)` for a point `g` in the subgroup generated by the
unipotent rational points of that closed subgroup. -/
theorem exists_mem_closure_unipotent_quotientPointsSubgroup_of_mem_expAdSubgroup [LieAlgebra ℚ 𝔤]
    (e : 𝔤) (I : HopfIdeal k H)
    (hI : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ I.lieSubalgebra (B := k))
    {ψ : 𝔤 ≃ₗ[k] 𝔤} (hψ : ψ ∈ expAdSubgroup k e) :
    ∃ g ∈ Subgroup.closure
        {u ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
            (CommAlgCat.of k k) |
          HopfAlgebra.IsUnipotentPoint u},
      (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = ψ := by
  let U : Subgroup (WithConv (H →ₐ[k] k)) :=
    Subgroup.closure
      {u ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
          (CommAlgCat.of k k) |
        HopfAlgebra.IsUnipotentPoint u}
  let toGL : WithConv (H →ₐ[k] k) →* LinearMap.GeneralLinearGroup k 𝔤 :=
    (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤).toHomUnits
  have hle :
      (expAdSubgroup k e).map
          (LinearMap.GeneralLinearGroup.generalLinearEquiv k 𝔤).symm.toMonoidHom ≤
        U.map toGL := by
    rw [Subgroup.map_le_iff_le_comap, expAdSubgroup_le_iff]
    intro y hy hy_mem
    have hy_ker : ⁅e, y⁆ = 0 := by
      simpa [LinearMap.mem_ker, LieAlgebra.ad_apply] using (Submodule.mem_inf.mp hy_mem).1
    have hy_lie : Derivation.cotangentDualLieEquiv (R := k) (H := H) y ∈
        I.lieSubalgebra (B := k) :=
      hI ((mem_lieSubalgebra_centralizerHopfIdeal_iff e _).mpr <| by
        rw [← LieEquiv.map_lie, hy_ker, map_zero])
    refine ⟨expAdPoint hy, Subgroup.subset_closure
      ⟨expAdPoint_mem_quotientPointsSubgroup I hy hy_lie, isUnipotentPoint_expAdPoint hy⟩, ?_⟩
    rw [toHomUnits_basePointsRepresentation_expAdPoint hy]
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv_symm_apply _).symm
  obtain ⟨g, hg, hgf⟩ := hle ⟨ψ, hψ, rfl⟩
  refine ⟨g, hg, ?_⟩
  have hgf' := congrArg (LinearMap.GeneralLinearGroup.generalLinearEquiv k 𝔤) hgf
  simpa [toGL, toHomUnits_basePointsRepresentation_eq_ofLinearEquiv] using hgf'

end Field

section Ring

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

local notation "𝔤" => Module.Dual R (Bialgebra.CotangentSpace R H)

/-- **The adjoint action of a one-parameter exponential point.** For any parameter `t : R`, the
adjoint action of `expPointAt (cotangentDualLieEquiv x) hd t` on `𝔤` is `exp (t • ad x)`. -/
theorem basePointsAdjointLieEquiv_expPointAt_toLinearMap [Algebra ℚ H]
    [Module ℚ 𝔤] (x : 𝔤)
    (hd : ∀ h : H, ∃ n,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := R) (H := H) x))^[n] h = 0)
    (t : R) :
    (Derivation.basePointsAdjointLieEquiv (R := R) (H := H)
        (Bialgebra.expPointAt
          (Derivation.cotangentDualLieEquiv (R := R) (H := H) x) hd t)).toLinearMap =
      IsNilpotent.exp (t • LieAlgebra.ad R 𝔤 x) := by
  rw [Derivation.basePointsAdjointLieEquiv_toLinearMap,
    Comodule.basePointsRepresentation_expPointAt, Derivation.differential_cotangentDualLieEquiv]

end Ring

section IsAlgClosed

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Over an algebraically closed field, `expAdPoint hx` lies in the identity component `G°(k)`.**
-/
theorem expAdPoint_mem_identityComponent {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    expAdPoint (H := H.obj) hx ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) :=
  expAdPoint_mem_quotientPointsSubgroup
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) hx (by
      rw [HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top]
      exact LieSubalgebra.mem_top _)

/-- **If `⁅x, y⁆ = 0`, `expAdPoint hx` lies in the connected centralizer `C_G(y)°(k)`.** -/
theorem expAdPoint_mem_centralizer_identityComponent {x y : 𝔤}
    (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) (hxy : ⁅x, y⁆ = 0) :
    expAdPoint (H := H.obj) hx ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H.obj y).identityComponent (CommAlgCat.of k k) :=
  expAdPoint_mem_quotientPointsSubgroup
    (centralizerHopfIdeal H.obj y).identityComponent hx (by
      rw [(centralizerHopfIdeal H.obj y).lieSubalgebra_identityComponent,
        mem_lieSubalgebra_centralizerHopfIdeal_iff, ← LieEquiv.map_lie, ← lie_skew, hxy, neg_zero,
        map_zero])

/-- **Lifting `Int(𝔤)` to products of unipotent rational points of `G°`.** -/
theorem exists_mem_closure_unipotent_identityComponent_of_mem_intLieAlgebra
    [LieAlgebra ℚ 𝔤] {φ : LinearMap.GeneralLinearGroup k 𝔤} (hφ : φ ∈ intLieAlgebra k 𝔤) :
    ∃ g ∈ Subgroup.closure
        {u ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
            (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) |
          HopfAlgebra.IsUnipotentPoint u},
      LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = φ :=
  exists_mem_closure_unipotent_quotientPointsSubgroup_of_mem_intLieAlgebra
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top hφ

/-- **Every inner automorphism in `Int(𝔤)` is the adjoint action of a point in `G°(k)`.** -/
theorem intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent [LieAlgebra ℚ 𝔤] :
    intLieAlgebra k 𝔤 ≤
      (CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (CommAlgCat.of k k)).map
          (Comodule.basePointsRepresentation (R := k) (H := H.obj) 𝔤).toHomUnits := by
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := exists_mem_closure_unipotent_identityComponent_of_mem_intLieAlgebra hφ
  refine ⟨g, ?_, toHomUnits_basePointsRepresentation_eq_ofLinearEquiv g⟩
  refine (Subgroup.closure_le _).mpr ?_ hg
  rintro _ ⟨h, -⟩
  exact h

end IsAlgClosed

end TauCeti
