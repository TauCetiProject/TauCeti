/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Comodule
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.Lie.AdjointAction.ExpAdSubgroup
public import TauCeti.Algebra.Lie.Reductive.InvariantZeroLocus
import Mathlib.Algebra.Module.Rat
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.OneParameter
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Tangent
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.Algebra.Lie.TracePowerPolynomial
import TauCeti.RepresentationTheory.Lie.AdNilpotent
import TauCeti.RingTheory.Nilpotent.Log

/-!
# Integrating nilpotent tangent elements, `expAdSubgroup`, and `Int(⁅𝔤, 𝔤⁆)` into `G(k)` and `G°(k)`

Let `G = Spec H` be an affine group of finite type over a field `k` of characteristic zero with Lie
algebra `𝔤 = (𝔪 / 𝔪²)*`.

* **Automatic local nilpotence**: any `x ∈ 𝔤` vanishing on all positive-degree Lie invariants in
  `S(𝔤*)^𝔤` acts nilpotently on every finite-dimensional `G`-comodule and hence induces a locally
  nilpotent left-invariant derivation on `H` (requiring neither `IsAlgClosed k` nor
  semisimplicity). In particular this applies to `ad`-nilpotent elements of `⁅𝔤, 𝔤⁆` when `𝔤` is
  reductive (`HasCentralRadical k 𝔤`), and to all `ad`-nilpotent elements when `IsKilling k 𝔤`.
* **Killing exponential point**: when `IsKilling k 𝔤`, `TauCeti.expAdPoint hx : G(k)` integrates
  an `ad`-nilpotent `x ∈ 𝔤` to a `k`-point acting by `IsNilpotent.exp (ad x) = expAd x`, injective
  in `x`, placing `Int(𝔤)` inside the adjoint image of `G(k)` and (over `IsAlgClosed k`) `G°(k)`.
* **Reductive realization and Kostant conjugacy**: when `𝔤` is reductive (`HasCentralRadical k 𝔤`),
  `expAdSubgroup k e` lies in the adjoint image of any closed subgroup containing `Lie(C_G(e))` (in
  particular `C_G(e)(k)` over any characteristic-zero field, and `C_G(e)°(k)` over `IsAlgClosed k`),
  lifting Kostant's conjugacy of `sl₂` triples sharing `e` to reductive groups, and `Int(⁅𝔤, 𝔤⁆)` is
  realized on `⁅𝔤, 𝔤⁆` by rational points of any closed subgroup containing `⁅𝔤, 𝔤⁆` (in particular
  `G` and `G°`).

## Main declarations

* `isNilpotent_differential_cotangentDualLieEquiv_of_forall_lift_eval_eq_zero` in
  `TauCeti.Comodule`, together with
  `exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero_of_mem_derivedSeries` and
  `exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero` in `TauCeti`: nilpotence on
  comodules and local nilpotence on `H`.
* `TauCeti.expAdPoint`: the rational point `exp x ∈ G(k)` attached to an `ad`-nilpotent `x ∈ 𝔤`
  when `IsKilling k 𝔤`, with its action, injectivity, and subgroup-membership API.
* `TauCeti.map_expAdSubgroup_le_map_quotientPointsSubgroup`,
  `TauCeti.map_expAdSubgroup_le_map_quotientPointsSubgroup_centralizer`,
  `TauCeti.map_expAdSubgroup_le_map_quotientPointsSubgroup_centralizer_identityComponent`, and
  `TauCeti.exists_mem_quotientPointsSubgroup_forall_derivedSeries_eq_of_mem_intLieAlgebra`:
  realizing `expAdSubgroup k e` and `Int(⁅𝔤, 𝔤⁆)` in the adjoint image of closed subgroups for
  reductive `𝔤`.
* `IsSl2Triple.exists_mem_quotientPointsSubgroup_eq_of_centralizer_lieSubalgebra_le`,
  `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizer_eq`, and
  `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizer_identityComponent_eq`: group-level
  Kostant conjugacy at fixed `e` for reductive `𝔤`.

## References

* A. Borel, *Linear Algebraic Groups* (2nd ed.), Springer GTM 126, §7.3.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.4.
* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, Theorem 3.6.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Comodule

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Any tangent vector vanishing on positive-degree Lie invariants acts nilpotently on every
finite-dimensional comodule.** No semisimplicity or algebraic-closure assumption is needed. -/
theorem isNilpotent_differential_cotangentDualLieEquiv_of_forall_lift_eval_eq_zero
    {k H M : Type*} [Field k] [CharZero k] [CommRing H] [Bialgebra k H]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M] [Comodule k H M]
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : ∀ p ∈ SymmetricAlgebra.lieInvariants k
        (Module.Dual k (Bialgebra.CotangentSpace k H))
        (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H))),
      SymmetricAlgebra.algebraMapInv p = 0 →
        _root_.SymmetricAlgebra.lift (Module.Dual.eval k _ x) p = 0) :
    IsNilpotent (differential (R := k) (H := H) (M := M)
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)) := by
  let f := (differential (R := k) (H := H) (M := M)).comp
    (Derivation.cotangentDualLieEquiv (R := k) (H := H)).toLieHom
  let _ : LieRingModule (Module.Dual k (Bialgebra.CotangentSpace k H)) M :=
    LieRingModule.compLieHom M f
  have : LieModule k (Module.Dual k (Bialgebra.CotangentSpace k H)) M :=
    LieModule.compLieHom M f
  have htoEnd : LieModule.toEnd k (Module.Dual k (Bialgebra.CotangentSpace k H)) M x =
      differential (R := k) (H := H) (M := M)
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) := by
    ext m
    simp [f, LieRingModule.compLieHom_apply, Module.End.lie_apply]
  exact htoEnd ▸ isNilpotent_toEnd_of_forall_lift_eval_eq_zero M hx

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

section LocalNilpotence

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Common zeros of positive-degree Lie invariants induce locally nilpotent left-invariant
derivations on `H`.** Holds over any field of characteristic zero, without semisimplicity,
connectedness, or algebraic closure. -/
theorem
    exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero_of_forall_lift_eval_eq_zero
    {x : 𝔤}
    (hx : ∀ p ∈ SymmetricAlgebra.lieInvariants k 𝔤 (Module.Dual k 𝔤),
      SymmetricAlgebra.algebraMapInv p = 0 →
        _root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p = 0) :
    ∀ a : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] a = 0 := by
  obtain ⟨M, hfaith⟩ := Comodule.exists_isFaithful (k := k) (H := H)
  rcases Comodule.isFaithful_def.mp hfaith with ⟨d, b, _⟩
  have hsurj : Function.Surjective (Comodule.coordinateBialgHom (H := H) b) :=
    (Comodule.coordinateBialgHom_surjective_iff_isFaithful b).mpr hfaith
  exact Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential
    (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) b hsurj
    (Comodule.isNilpotent_differential_cotangentDualLieEquiv_of_forall_lift_eval_eq_zero hx)

/-- **In a reductive tangent Lie algebra, every `ad`-nilpotent element of the derived ideal `⁅𝔤, 𝔤⁆`
induces a locally nilpotent left-invariant derivation on `H`.** -/
theorem exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero_of_mem_derivedSeries
    [LieAlgebra.HasCentralRadical k 𝔤] {x : 𝔤}
    (hder : x ∈ LieAlgebra.derivedSeries k 𝔤 1) (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    ∀ a : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] a = 0 :=
  exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero_of_forall_lift_eval_eq_zero
    (mem_derivedSeries_and_isNilpotent_ad_iff_forall_lift_eval_eq_zero.mp ⟨hder, hx⟩)

end LocalNilpotence

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
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] a = 0 :=
  exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero_of_forall_lift_eval_eq_zero
    (isNilpotent_ad_iff_forall_lift_eval_eq_zero.mp hx)

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
    Derivation.differential_cotangentDualLieEquiv_adjointComodule]

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

/-- **Every inner automorphism in `Int(𝔤)` is the adjoint action of a `k`-point of `G`.** -/
theorem intLieAlgebra_le_range_basePointsRepresentation [LieAlgebra ℚ 𝔤] :
    intLieAlgebra k 𝔤 ≤
      (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤).toHomUnits.range :=
  intLieAlgebra_le_iff.mpr fun _ hx ↦
    ⟨expAdPoint hx, toHomUnits_basePointsRepresentation_expAdPoint hx⟩

end Field

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

/-- **Every inner automorphism in `Int(𝔤)` is the adjoint action of a point in `G°(k)`.** -/
theorem intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent [LieAlgebra ℚ 𝔤] :
    intLieAlgebra k 𝔤 ≤
      (CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (CommAlgCat.of k k)).map
          (Comodule.basePointsRepresentation (R := k) (H := H.obj) 𝔤).toHomUnits :=
  intLieAlgebra_le_iff.mpr fun _ hx ↦
    ⟨expAdPoint hx, expAdPoint_mem_identityComponent hx,
      toHomUnits_basePointsRepresentation_expAdPoint hx⟩

end IsAlgClosed

section Reductive

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.HasCentralRadical k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Realizing `expAdSubgroup k e` inside a closed subgroup for a reductive tangent Lie algebra.**
Over any field of characteristic zero, if `I` is a Hopf ideal whose Lie subalgebra contains
`Lie(C_G(e))`, every element of `expAdSubgroup k e` lies in the adjoint image of
`quotientPointsSubgroup I`. -/
theorem map_expAdSubgroup_le_map_quotientPointsSubgroup [LieAlgebra ℚ 𝔤] (e : 𝔤)
    (I : HopfIdeal k H)
    (hI : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ I.lieSubalgebra (B := k)) :
    (expAdSubgroup k e).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k 𝔤).symm.toMonoidHom ≤
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H) I (CommAlgCat.of k k)).map
        (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤).toHomUnits := by
  let _ : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  rw [Subgroup.map_le_iff_le_comap, expAdSubgroup_le_iff]
  intro y hy hye
  obtain ⟨hyker, z, hz⟩ := Submodule.mem_inf.mp hye
  have hder : y ∈ LieAlgebra.derivedSeries k 𝔤 1 := by
    rw [← hz, LieAlgebra.ad_apply, LieAlgebra.derivedSeries_def,
      LieAlgebra.derivedSeriesOfIdeal_succ, LieAlgebra.derivedSeriesOfIdeal_zero]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top e) (LieSubmodule.mem_top z)
  have hD :=
    exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero_of_mem_derivedSeries
      (H := H) hder hy
  set d := Derivation.cotangentDualLieEquiv (R := k) (H := H) y
  have hdC : d ∈ (centralizerHopfIdeal H e).lieSubalgebra (B := k) := by
    have hye0 : ⁅e, y⁆ = 0 := LinearMap.mem_ker.mp hyker
    rw [mem_lieSubalgebra_centralizerHopfIdeal_iff, ← LieEquiv.map_lie, hye0, map_zero]
  refine ⟨toConv (Bialgebra.expPoint d hD),
    I.toConv_expPoint_mem_quotientPointsSubgroup (hI hdC) hD, Units.ext ?_⟩
  rw [MonoidHom.coe_toHomUnits,
    Comodule.basePointsRepresentation_expPoint hD
      (Derivation.differential_cotangentDualLieEquiv_adjointComodule y ▸ hy),
    Derivation.differential_cotangentDualLieEquiv_adjointComodule,
    MulEquiv.coe_toMonoidHom, ← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
    MulEquiv.apply_symm_apply]
  refine LinearMap.ext fun w ↦ ?_
  rw [LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv, expAd_apply (K := k) y hy w]
  congr!
  exact Subsingleton.elim _ _

/-- **Over any characteristic-zero field, `expAdSubgroup k e` lies in the adjoint image of
`C_G(e)(k)`** for a reductive tangent Lie algebra. -/
theorem map_expAdSubgroup_le_map_quotientPointsSubgroup_centralizer [LieAlgebra ℚ 𝔤] (e : 𝔤) :
    (expAdSubgroup k e).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k 𝔤).symm.toMonoidHom ≤
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H e) (CommAlgCat.of k k)).map
          (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤).toHomUnits :=
  map_expAdSubgroup_le_map_quotientPointsSubgroup e (centralizerHopfIdeal H e) le_rfl

/-- **Realizing `Int(⁅𝔤, 𝔤⁆)` on the derived ideal inside a closed subgroup containing `⁅𝔤, 𝔤⁆`.**
When `𝔤` is reductive over a characteristic-zero field and `I.lieSubalgebra` contains the derived
ideal `⁅𝔤, 𝔤⁆`, every element of `intLieAlgebra k ⁅𝔤, 𝔤⁆` is realized on `⁅𝔤, 𝔤⁆` by a rational
point in `quotientPointsSubgroup I`. -/
theorem exists_mem_quotientPointsSubgroup_forall_derivedSeries_eq_of_mem_intLieAlgebra
    [LieAlgebra ℚ (LieAlgebra.derivedSeries k 𝔤 1)] (I : HopfIdeal k H)
    (hI : (LieAlgebra.derivedSeries k 𝔤 1).toLieSubalgebra.map
      (Derivation.cotangentDualLieEquiv (R := k) (H := H)).toLieHom ≤ I.lieSubalgebra (B := k))
    {u : LinearMap.GeneralLinearGroup k (LieAlgebra.derivedSeries k 𝔤 1)}
    (hu : u ∈ intLieAlgebra k (LieAlgebra.derivedSeries k 𝔤 1)) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H) I (CommAlgCat.of k k),
      ∀ y : LieAlgebra.derivedSeries k 𝔤 1,
        Comodule.basePointsRepresentation (R := k) (H := H) 𝔤 g (y : 𝔤) =
          ((u • y : LieAlgebra.derivedSeries k 𝔤 1) : 𝔤) := by
  let _ : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  let 𝔤' := LieAlgebra.derivedSeries k 𝔤 1
  let S : Subgroup (LinearMap.GeneralLinearGroup k 𝔤') :=
    { carrier := {v | ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup
          (CommHopfAlgCat.of k H) I (CommAlgCat.of k k),
        ∀ y : 𝔤', Comodule.basePointsRepresentation (R := k) (H := H) 𝔤 g (y : 𝔤) =
          ((v • y : 𝔤') : 𝔤)}
      one_mem' := ⟨1, Subgroup.one_mem _, fun y ↦ by simp⟩
      mul_mem' := fun {v₁ v₂} ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩ ↦
        ⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂, fun y ↦ by
          rw [map_mul, mul_apply_eq_comp, h₂, h₁, mul_smul]⟩
      inv_mem' := fun {v} ⟨g, hg, hv⟩ ↦
        ⟨g⁻¹, Subgroup.inv_mem _ hg, fun y ↦ by
          have := congrArg (Comodule.basePointsRepresentation (R := k) (H := H) 𝔤 g⁻¹)
            (hv (v⁻¹ • y))
          simpa [Representation.inv_self_apply] using this.symm⟩ }
  suffices intLieAlgebra k 𝔤' ≤ S from this hu
  refine intLieAlgebra_le_iff.mpr fun x hx ↦ ?_
  have hx𝔤 : IsNilpotent (LieAlgebra.ad k 𝔤 (x : 𝔤)) := (LieIdeal.isNilpotent_ad_iff 𝔤').mp hx
  have hD :=
    exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero_of_mem_derivedSeries
      (H := H) x.property hx𝔤
  set d := Derivation.cotangentDualLieEquiv (R := k) (H := H) (x : 𝔤)
  have hdI : d ∈ I.lieSubalgebra (B := k) :=
    hI ((LieSubalgebra.mem_map _ _ _).mpr ⟨(x : 𝔤), x.property, rfl⟩)
  refine ⟨toConv (Bialgebra.expPoint d hD),
    I.toConv_expPoint_mem_quotientPointsSubgroup hdI hD, fun y ↦ ?_⟩
  obtain ⟨N, hN⟩ := hx𝔤
  have hN' : LieAlgebra.ad k 𝔤' x ^ N = 0 :=
    LinearMap.ext fun z ↦ Subtype.ext <| (𝔤'.incl.map_ad_pow x N z).trans (by simp [hN])
  rw [Comodule.basePointsRepresentation_expPoint hD
      (Derivation.differential_cotangentDualLieEquiv_adjointComodule (x : 𝔤) ▸ ⟨N, hN⟩),
    Derivation.differential_cotangentDualLieEquiv_adjointComodule,
    IsNilpotent.exp_eq_sum hN, LinearMap.sum_apply,
    LinearMap.GeneralLinearGroup.ofLinearEquiv_smul, LieEquiv.coe_toLinearEquiv,
    expAd_apply (K := k) x hx y, IsNilpotent.exp_eq_sum hN', LinearMap.sum_apply,
    ← 𝔤'.incl_apply (∑ _ ∈ _, _), _root_.map_sum 𝔤'.incl]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_rat_smul 𝔤'.incl (i.factorial : ℚ)⁻¹]
  exact congrArg (fun v ↦ (i.factorial : ℚ)⁻¹ • v) (𝔤'.incl.map_ad_pow x i y).symm

end Reductive

section ReductiveAlgClosed

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [LieAlgebra.HasCentralRadical k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Kostant's subgroup `expAdSubgroup k e` is realized by rational points of `C_G(e)°`** for any
reductive tangent Lie algebra over an algebraically closed field of characteristic zero. -/
theorem map_expAdSubgroup_le_map_quotientPointsSubgroup_centralizer_identityComponent
    [LieAlgebra ℚ 𝔤] (e : 𝔤) :
    (expAdSubgroup k e).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k 𝔤).symm.toMonoidHom ≤
      (CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H.obj e).identityComponent
        (CommAlgCat.of k k)).map
          (Comodule.basePointsRepresentation (R := k) (H := H.obj) 𝔤).toHomUnits :=
  map_expAdSubgroup_le_map_quotientPointsSubgroup e
    (centralizerHopfIdeal H.obj e).identityComponent
    (by rw [(centralizerHopfIdeal H.obj e).lieSubalgebra_identityComponent])

end ReductiveAlgClosed

end TauCeti

namespace IsSl2Triple

open TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

section General

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.HasCentralRadical k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Group-level Kostant conjugacy in a closed subgroup.** Over any field of characteristic zero,
if `𝔤` is reductive and `I` is a Hopf ideal whose Lie algebra contains `Lie(C_G(e))`, any two `sl₂`
triples `(h, e, f)` and `(h', e, f')` sharing `e` are conjugate by a rational point of `I`. -/
theorem exists_mem_quotientPointsSubgroup_eq_of_centralizer_lieSubalgebra_le
    {h f h' f' e : 𝔤} (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') (I : HopfIdeal k H)
    (hI : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ I.lieSubalgebra (B := k)) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H) I (CommAlgCat.of k k),
      Comodule.basePointsRepresentation 𝔤 g e = e ∧
        Comodule.basePointsRepresentation 𝔤 g h = h' ∧
        Comodule.basePointsRepresentation 𝔤 g f = f' := by
  let _ := ratLieAlgebra k 𝔤
  obtain ⟨φ, hφ, hφe, hφh, hφf⟩ := t.exists_lieEquiv_apply_eq (K := k) t'
  obtain ⟨g, hg, hgu⟩ :=
    map_expAdSubgroup_le_map_quotientPointsSubgroup (H := H) e I hI ⟨φ.toLinearEquiv, hφ, rfl⟩
  have hact (z : 𝔤) : Comodule.basePointsRepresentation 𝔤 g z = φ z := by
    have := LinearMap.congr_fun (congrArg Units.val hgu) z
    rwa [MonoidHom.coe_toHomUnits] at this
  exact ⟨g, hg, (hact e).trans hφe, (hact h).trans hφh, (hact f).trans hφf⟩

/-- **Group-level Kostant conjugacy in `C_G(e)(k)`.** Over any field of characteristic zero, any two
`sl₂` triples `(h, e, f)` and `(h', e, f')` sharing `e` in a reductive tangent Lie algebra are
conjugate by a rational point of `C_G(e)(k)`. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_eq
    {h f h' f' e : 𝔤} (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H e) (CommAlgCat.of k k),
      Comodule.basePointsRepresentation 𝔤 g e = e ∧
        Comodule.basePointsRepresentation 𝔤 g h = h' ∧
        Comodule.basePointsRepresentation 𝔤 g f = f' :=
  t.exists_mem_quotientPointsSubgroup_eq_of_centralizer_lieSubalgebra_le t'
    (centralizerHopfIdeal H e) le_rfl

end General

/-- **Kostant's conjugacy theorem at fixed nilpositive element, in `C_G(e)°(k)`.** Over an
algebraically closed field `k` of characteristic zero, if `G = Spec H` is of finite type with
reductive Lie algebra `𝔤`, any two `sl₂` triples `(h, e, f)` and `(h', e, f')` in `𝔤` sharing `e`
are conjugate by a rational point of the connected centralizer `C_G(e)°`. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_identityComponent_eq
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.HasCentralRadical k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {h f h' f' e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H.obj e).identityComponent (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' :=
  t.exists_mem_quotientPointsSubgroup_eq_of_centralizer_lieSubalgebra_le t'
    (centralizerHopfIdeal H.obj e).identityComponent
    (by rw [(centralizerHopfIdeal H.obj e).lieSubalgebra_identityComponent])

end IsSl2Triple
