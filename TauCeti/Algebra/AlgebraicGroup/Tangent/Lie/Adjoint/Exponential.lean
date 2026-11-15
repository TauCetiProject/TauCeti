/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Comodule
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.Lie.AdjointAction.ExpAdSubgroup
import Mathlib.Algebra.Module.Rat
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.RepresentationTheory.Lie.AdNilpotent

/-!
# Integrating `ad`-nilpotent elements and `Int(𝔤)` into `G°(k)`

Let `G = Spec H` be an affine group of finite type over a field `k` of characteristic zero whose
Lie algebra `𝔤 = (𝔪 / 𝔪²)*` has nondegenerate Killing form.

An `ad`-nilpotent element `x ∈ 𝔤` acts nilpotently in every finite-dimensional representation of `𝔤`
(`TauCeti.isNilpotent_apply_of_isNilpotent_ad`), hence on every finite-dimensional `G`-comodule
(`TauCeti.Comodule.isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad`). Choosing a
faithful finite-dimensional representation embeds `G` into `GL_d` with nilpotent tangent matrix,
showing that the left-invariant vector field of `x` on `H` is locally nilpotent
(`Derivation.exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero`).

Its Taylor exponential therefore defines a `k`-point `TauCeti.expAdPoint hx : G(k)` whose adjoint
action on `𝔤` is the operator exponential `IsNilpotent.exp (ad x) = expAd x`
(`TauCeti.basePointsRepresentation_expAdPoint`, `TauCeti.basePointsAdjointLieEquiv_expAdPoint`).
Over an algebraically closed field, `expAdPoint hx` lies in the identity component `G°(k)` and in
`C_G(y)°(k)` whenever `⁅x, y⁆ = 0`, so the entire inner automorphism group `Int(𝔤)` is realized by
rational points of `G°` (`TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent`),
and Kostant's subgroup `expAdSubgroup k e` is realized inside `C_G(e)°(k)`
(`TauCeti.map_expAdSubgroup_le_map_quotientPointsSubgroup_centralizer_identityComponent`), lifting
Kostant's conjugacy of `sl₂` triples sharing `e` to `C_G(e)°(k)`.

## Main declarations

* `TauCeti.Comodule.isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad`: an
  `ad`-nilpotent element of `𝔤` acts nilpotently on every finite-dimensional `H`-comodule.
* `Derivation.exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero`: its
  left-invariant derivation on `H` is locally nilpotent.
* `TauCeti.expAdPoint`: the rational point `exp x ∈ G(k)` attached to an `ad`-nilpotent `x ∈ 𝔤`,
  with adjoint action `TauCeti.basePointsRepresentation_expAdPoint`,
  `TauCeti.basePointsAdjointLieEquiv_expAdPoint`, and
  `TauCeti.toHomUnits_basePointsRepresentation_expAdPoint`.
* `TauCeti.expAdPoint_mem_identityComponent` and
  `TauCeti.expAdPoint_mem_centralizer_identityComponent`: subgroup memberships in `G°(k)` and
  `C_G(y)°(k)`.
* `TauCeti.intLieAlgebra_le_range_basePointsRepresentation` and
  `TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent`: `Int(𝔤)` lies in the
  adjoint image of `G(k)` and, over an algebraically closed field, of `G°(k)`.
* `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizer_identityComponent_eq`: Kostant's
  conjugacy of `sl₂` triples sharing `e` by a rational point of `C_G(e)°`.

## References

* A. Borel, *Linear Algebraic Groups* (2nd ed.), Springer GTM 126, §7.3.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.4.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Comodule

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **An `ad`-nilpotent element of a Killing Lie algebra acts nilpotently on every
finite-dimensional comodule.** -/
theorem isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad
    {k : Type u} [Field k] [CharZero k] {H : Type u} [CommRing H] [HopfAlgebra k H]
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {M : Type v} [AddCommGroup M] [Module k M] [FiniteDimensional k M] [Comodule k H M]
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)) :
    IsNilpotent (differential (R := k) (H := H) (M := M)
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)) :=
  TauCeti.isNilpotent_apply_of_isNilpotent_ad
    (ρ := (differential (R := k) (H := H) (M := M)).comp
      (Derivation.cotangentDualLieEquiv (R := k) (H := H)).toLieHom) hx

end TauCeti.Comodule

namespace Derivation

open TauCeti

universe u

/-- **An `ad`-nilpotent element of a Killing tangent Lie algebra induces a locally nilpotent
left-invariant derivation on `H`.** -/
theorem exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero
    {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)) :
    ∀ a : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (cotangentDualLieEquiv (R := k) (H := H) x))^[m] a = 0 := by
  obtain ⟨M, hfaith⟩ := Comodule.exists_isFaithful (k := k) (H := H)
  rcases Comodule.isFaithful_def.mp hfaith with ⟨d, b, _⟩
  have hsurj : Function.Surjective (Comodule.coordinateBialgHom (H := H) b) :=
    (Comodule.coordinateBialgHom_surjective_iff_isFaithful b).mpr hfaith
  exact exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential
    (cotangentDualLieEquiv (R := k) (H := H) x) b hsurj
    (Comodule.isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad hx)

end Derivation

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

section Field

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **The exponential `k`-point `exp x ∈ G(k)` attached to an `ad`-nilpotent element `x ∈ 𝔤`.** -/
noncomputable def expAdPoint {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    WithConv (H →ₐ[k] k) :=
  letI : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)
    (Derivation.exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero hx))

/-- **The adjoint action of `expAdPoint hx` on `𝔤` is the operator exponential `exp (ad x)`.** -/
@[simp]
theorem basePointsRepresentation_expAdPoint {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    Comodule.basePointsRepresentation (R := k) (H := H) 𝔤 (expAdPoint hx) =
      IsNilpotent.exp (LieAlgebra.ad k 𝔤 x) := by
  let _ : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  have hdiff : Comodule.differential (R := k) (H := H) (M := 𝔤)
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) = LieAlgebra.ad k 𝔤 x := by
    ext y
    rw [Derivation.differential_adjointComodule, LieEquiv.symm_apply_apply, LieAlgebra.ad_apply]
  rw [expAdPoint, Comodule.basePointsRepresentation_expPoint _ (hdiff ▸ hx), hdiff]

/-- **As a Lie automorphism, `expAdPoint hx` acts on `𝔤` by `expAd x`.** -/
@[simp]
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
@[simp]
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
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) := by
  let _ : Algebra ℚ H.obj := Algebra.compHom H.obj (algebraMap ℚ k)
  have hd : Derivation.cotangentDualLieEquiv (R := k) (H := H.obj) x ∈
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).lieSubalgebra (B := k) := by
    rw [HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top]
    exact LieSubalgebra.mem_top _
  exact HopfIdeal.toConv_expPoint_mem_quotientPointsSubgroup _ hd _

/-- **If `⁅x, y⁆ = 0`, `expAdPoint hx` lies in the connected centralizer `C_G(y)°(k)`.** -/
theorem expAdPoint_mem_centralizer_identityComponent {x y : 𝔤}
    (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) (hxy : ⁅x, y⁆ = 0) :
    expAdPoint (H := H.obj) hx ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H.obj y).identityComponent (CommAlgCat.of k k) := by
  let _ : Algebra ℚ H.obj := Algebra.compHom H.obj (algebraMap ℚ k)
  have hd : Derivation.cotangentDualLieEquiv (R := k) (H := H.obj) x ∈
      (centralizerHopfIdeal H.obj y).identityComponent.lieSubalgebra (B := k) := by
    rw [(centralizerHopfIdeal H.obj y).lieSubalgebra_identityComponent,
      mem_lieSubalgebra_centralizerHopfIdeal_iff, ← LieEquiv.map_lie, ← lie_skew, hxy, neg_zero,
      map_zero]
  exact HopfIdeal.toConv_expPoint_mem_quotientPointsSubgroup _ hd _

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

/-- **Kostant's subgroup `expAdSubgroup k e` is realized by rational points of `C_G(e)°`.** -/
theorem map_expAdSubgroup_le_map_quotientPointsSubgroup_centralizer_identityComponent
    [LieAlgebra ℚ 𝔤] (e : 𝔤) :
    (expAdSubgroup k e).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k 𝔤).symm.toMonoidHom ≤
      (CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H.obj e).identityComponent
        (CommAlgCat.of k k)).map
          (Comodule.basePointsRepresentation (R := k) (H := H.obj) 𝔤).toHomUnits := by
  rw [Subgroup.map_le_iff_le_comap, expAdSubgroup_le_iff]
  intro y hy hye
  have hcomm : ⁅y, e⁆ = 0 := by
    rw [← lie_skew, ← LieAlgebra.ad_apply (R := k), LinearMap.mem_ker.mp hye.1, neg_zero]
  exact ⟨expAdPoint hy, expAdPoint_mem_centralizer_identityComponent hy hcomm,
    toHomUnits_basePointsRepresentation_expAdPoint hy⟩

end IsAlgClosed

end TauCeti

namespace IsSl2Triple

open TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

/-- **Kostant's conjugacy theorem at fixed nilpositive element, in `C_G(e)°(k)`.** Over an
algebraically closed field `k` of characteristic zero, if `G = Spec H` is of finite type with
Killing Lie algebra `𝔤`, any two `sl₂` triples `(h, e, f)` and `(h', e, f')` in `𝔤` sharing `e` are
conjugate by a rational point of the connected centralizer `C_G(e)°`. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_identityComponent_eq
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {h f h' f' e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H.obj e).identityComponent (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' := by
  let _ := ratLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))
  obtain ⟨φ, hφ, hφe, hφh, hφf⟩ := t.exists_lieEquiv_apply_eq (K := k) t'
  obtain ⟨g, hg, hgu⟩ :=
    map_expAdSubgroup_le_map_quotientPointsSubgroup_centralizer_identityComponent (H := H) e
      ⟨φ.toLinearEquiv, hφ, rfl⟩
  have hact (z : Module.Dual k (Bialgebra.CotangentSpace k H)) :
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g z =
        φ z := by
    have := LinearMap.congr_fun (congrArg Units.val hgu) z
    rwa [MonoidHom.coe_toHomUnits] at this
  exact ⟨g, hg, (hact e).trans hφe, (hact h).trans hφh, (hact f).trans hφf⟩

end IsSl2Triple
