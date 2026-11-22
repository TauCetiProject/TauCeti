/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Comodule
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Representation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.Lie.AdjointAction.ExpAdSubgroup
import Mathlib.Algebra.Module.Rat
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.OneParameter
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.RepresentationTheory.Lie.AdNilpotent
import TauCeti.RingTheory.Nilpotent.Log

/-!
# Adjoint action of exponential points and subgroup realization of inner automorphisms

Let `G = Spec H` be an affine group over a ring or field `k` with augmentation cotangent space
`Bialgebra.CotangentSpace` and Lie algebra `𝔤 = Module.Dual k (Bialgebra.CotangentSpace k H)`.
Because the differentiated adjoint representation is the Lie bracket
(`Derivation.differential_adjointComodule`), the general comodule exponential formula
(`TauCeti.Comodule.basePointsRepresentation_expPoint`) shows that whenever `x ∈ 𝔤` is
`ad`-nilpotent and its left-invariant derivation on `H` is locally nilpotent, the rational point
`exp x` acts on `𝔤` as `exp (ad x)` (and the one-parameter subgroup `exp (t x)` acts as
`exp (t • ad x)`).

Over a field `k` of characteristic zero (`Module.Finite k (Bialgebra.CotangentSpace k H)`), local
nilpotence of the left-invariant derivation on `H` holds in two geometric settings:

1. **Kostant's centralizer subgroup `expAdSubgroup k e` (for any affine group `G`).** Every
   generator `y ∈ ker (ad e) ⊓ [e, 𝔤]` has the form `⁅e, z⁆` with `⁅e, ⁅e, z⁆⁆ = 0`, so its image in
   every finite-dimensional representation of `𝔤` is nilpotent by Jacobson's lemma
   (`LinearMap.isNilpotent_lie_of_lie_lie_eq_zero`), without any Killing, finite-type, or
   algebraic-closedness assumption on `G`. Consequently `expAdSubgroup k e` is realized inside any
   closed subgroup whose Lie algebra contains `Lie(C_G(e))`, in particular `C_G(e)(k)` and—over an
   algebraically closed field—`C_G(e)°(k)`, lifting Kostant's conjugacy of `sl₂` triples sharing
   `e` to rational points of `C_G(e)` and `C_G(e)°`.
2. **The inner automorphism group `Int(𝔤)` (when `𝔤` is Killing).** Every `ad`-nilpotent element
   `x ∈ 𝔤` acts nilpotently on every finite-dimensional representation of `𝔤`
   (`TauCeti.isNilpotent_apply_of_isNilpotent_ad`). This shows that `x` induces a locally nilpotent
   left-invariant derivation on `H`, realizes `Int(𝔤)` inside any closed subgroup with full Lie
   algebra, and (when `G` is of finite type) yields the packaged exponential point
   `TauCeti.expAdPoint hx : G(k)` landing in `G°(k)` (and `C_G(y)°(k)` when `⁅x, y⁆ = 0`).

## Main declarations

* `TauCeti.basePointsRepresentation_adjoint_expPoint`,
  `TauCeti.basePointsRepresentation_adjoint_expPoint_eq_expAd`, and
  `TauCeti.basePointsRepresentation_adjoint_expPointAt`: `exp x` and `exp (t x)` act on `𝔤` as
  `IsNilpotent.exp (ad x)` (equivalently `TauCeti.expAd x`) and `IsNilpotent.exp (t • ad x)`.
* `TauCeti.exists_iterate_leftInvariantDerivation_eq_zero_of_mem_ker_inf_range`,
  `TauCeti.map_expAdSubgroup_le_map_quotientPointsSubgroup`, and
  `TauCeti.exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_of_mem_expAdSubgroup`:
  elements of `ker (ad e) ⊓ [e, 𝔤]` have locally nilpotent invariant vector fields, and
  `expAdSubgroup k e` is realized in any closed subgroup whose Lie algebra contains `Lie(C_G(e))`.
* `IsSl2Triple.exists_mem_quotientPointsSubgroup_basePointsRepresentation_e_eq_of_lieSubalgebra_le`:
  **Kostant's conjugacy theorem at fixed `e`** in any closed subgroup containing `Lie(C_G(e))`,
  specialized to `C_G(e)(k)` and `C_G(e)°(k)` in
  `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_e_eq`
  and `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizer_identityComponent_eq`.
* `TauCeti.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad`,
  `TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup`,
  `TauCeti.exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_smul_of_mem_intLieAlgebra`,
  `TauCeti.expAdPoint`, `TauCeti.expAdPoint_mem_identityComponent`,
  `TauCeti.expAdPoint_mem_centralizer_identityComponent`,
  `TauCeti.intLieAlgebra_le_range_basePointsRepresentation`, and
  `TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent`:
  when `𝔤` is Killing, `ad`-nilpotent elements integrate to `G` and `Int(𝔤)` is realized by
  closed subgroups with full Lie algebra and by `G°(k)`.

## References

* A. Borel, *Linear Algebraic Groups* (2nd ed.), Springer GTM 126, §7.3.
* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, §3.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.4 and Theorem 3.4.10.
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
attribute [local instance 100] LieRing.ofAssociativeRing

section General

variable {R : Type u} {H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)] [Algebra ℚ H]

section ModuleRat

variable [Module ℚ (Module.Dual R (Bialgebra.CotangentSpace R H))]

/-- **The exponential point of an `ad`-nilpotent tangent vector acts on `𝔤` as `exp (ad x)`.** -/
theorem basePointsRepresentation_adjoint_expPoint
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)}
    (hd : ∀ a : H, ∃ n,
      (Bialgebra.leftInvariantDerivation (Derivation.cotangentDualLieEquiv (R := R) (H := H) x))^[n]
        a = 0)
    (hx : IsNilpotent (LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x)) :
    Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H))
        (toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := R) (H := H) x) hd)) =
      IsNilpotent.exp (LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x) := by
  have hnil : IsNilpotent (Comodule.differential (R := R) (H := H)
      (M := Module.Dual R (Bialgebra.CotangentSpace R H))
      (Derivation.cotangentDualLieEquiv (R := R) (H := H) x)) := by
    rwa [differential_adjointComodule_cotangentDualLieEquiv]
  rw [Comodule.basePointsRepresentation_expPoint hd hnil,
    differential_adjointComodule_cotangentDualLieEquiv]

/-- **The exponential one-parameter subgroup of an `ad`-nilpotent tangent vector acts on `𝔤` as
`exp (t • ad x)`.** -/
theorem basePointsRepresentation_adjoint_expPointAt
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)}
    (hd : ∀ a : H, ∃ n,
      (Bialgebra.leftInvariantDerivation (Derivation.cotangentDualLieEquiv (R := R) (H := H) x))^[n]
        a = 0)
    (hx : IsNilpotent (LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x)) (t : R) :
    Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H))
        (Bialgebra.expPointAt (Derivation.cotangentDualLieEquiv (R := R) (H := H) x) hd t) =
      IsNilpotent.exp (t • LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x) := by
  have hnil : IsNilpotent (Comodule.differential (R := R) (H := H)
      (M := Module.Dual R (Bialgebra.CotangentSpace R H))
      (Derivation.cotangentDualLieEquiv (R := R) (H := H) x)) := by
    rwa [differential_adjointComodule_cotangentDualLieEquiv]
  rw [Comodule.basePointsRepresentation_expPointAt_of_isNilpotent _ hd hnil t,
    differential_adjointComodule_cotangentDualLieEquiv]

end ModuleRat

/-- **The exponential point of an `ad`-nilpotent tangent vector acts on `𝔤` as `TauCeti.expAd x`.**
-/
theorem basePointsRepresentation_adjoint_expPoint_eq_expAd
    [LieAlgebra ℚ (Module.Dual R (Bialgebra.CotangentSpace R H))]
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)}
    (hd : ∀ a : H, ∃ n,
      (Bialgebra.leftInvariantDerivation (Derivation.cotangentDualLieEquiv (R := R) (H := H) x))^[n]
        a = 0)
    (hx : IsNilpotent (LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x))
    (y : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H))
        (toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := R) (H := H) x) hd))
        y =
      expAd x hx.exists_pow_apply_eq_zero y := by
  rw [expAd_apply x hx y, basePointsRepresentation_adjoint_expPoint hd hx]

end General

section KerInfRange

variable {k : Type u} {H : Type v} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]

/-- **Every element of `ker (ad e) ⊓ [e, 𝔤]` has a locally nilpotent left-invariant derivation.**
No Killing or reductivity hypothesis is required: Jacobson's lemma shows nilpotence on every
finite-dimensional subcomodule of `H`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_mem_ker_inf_range
    {e y : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hy : y ∈ LinearMap.ker (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ⊓
      LinearMap.range (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))
    (a : H) :
    ∃ n, (Bialgebra.leftInvariantDerivation
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) y))^[n] a = 0 := by
  obtain ⟨hye, z, rfl⟩ := Submodule.mem_inf.mp hy
  rw [LinearMap.mem_ker, LieAlgebra.ad_apply, LieAlgebra.ad_apply] at hye
  refine Bialgebra.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isNilpotent
    (fun N hN ↦ ?_) a
  have : Module.Finite k N := hN
  rw [LieAlgebra.ad_apply, LieEquiv.map_lie, LieHom.map_lie]
  refine LinearMap.isNilpotent_lie_of_lie_lie_eq_zero ?_
  rw [← LieHom.map_lie, ← LieHom.map_lie, ← LieEquiv.map_lie, ← LieEquiv.map_lie, hye, map_zero,
    map_zero]

end KerInfRange

section ExpAdSubgroup

variable {k : Type u} {H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **Kostant's subgroup `expAdSubgroup k e` lies in the adjoint image of any closed subgroup whose
Lie algebra contains `Lie(C_G(e))`.** -/
theorem map_expAdSubgroup_le_map_quotientPointsSubgroup
    [LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H))]
    (e : Module.Dual k (Bialgebra.CotangentSpace k H)) {J : HopfIdeal k H}
    (hlie : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ J.lieSubalgebra (B := k)) :
    (expAdSubgroup k e).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (Module.Dual k (Bialgebra.CotangentSpace k H))).symm.toMonoidHom ≤
      (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k)).map
          (Comodule.basePointsRepresentation (R := k) (H := H)
            (Module.Dual k (Bialgebra.CotangentSpace k H))).toHomUnits := by
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  rw [Subgroup.map_le_iff_le_comap, expAdSubgroup_le_iff]
  intro y hy hmem
  have hd := exists_iterate_leftInvariantDerivation_eq_zero_of_mem_ker_inf_range hmem
  have hyJ : Derivation.cotangentDualLieEquiv (R := k) (H := H) y ∈ J.lieSubalgebra (B := k) := by
    apply hlie
    rw [mem_lieSubalgebra_centralizerHopfIdeal_iff, ← LieEquiv.map_lie]
    have hker : ⁅e, y⁆ = 0 := LinearMap.mem_ker.mp hmem.1
    rw [hker, map_zero]
  refine ⟨toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) y) hd),
    J.toConv_expPoint_mem_quotientPointsSubgroup hyJ hd, ?_⟩
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (Module.Dual k (Bialgebra.CotangentSpace k H))).injective
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  refine LinearEquiv.ext fun z ↦ ?_
  simpa using basePointsRepresentation_adjoint_expPoint_eq_expAd hd hy z

/-- **Kostant's subgroup `expAdSubgroup k e` is realized by rational points of any closed subgroup
whose Lie algebra contains `Lie(C_G(e))`.** -/
theorem exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_of_mem_expAdSubgroup
    [LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {e : Module.Dual k (Bialgebra.CotangentSpace k H)} {J : HopfIdeal k H}
    (hlie : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ J.lieSubalgebra (B := k))
    {ψ : Module.Dual k (Bialgebra.CotangentSpace k H) ≃ₗ[k]
      Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hψ : ψ ∈ expAdSubgroup k e) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k),
      ∀ x : Module.Dual k (Bialgebra.CotangentSpace k H),
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g x =
          ψ x := by
  obtain ⟨g, hg, hge⟩ := map_expAdSubgroup_le_map_quotientPointsSubgroup e hlie ⟨ψ, hψ, rfl⟩
  refine ⟨g, hg, fun x ↦ ?_⟩
  have hx := congrArg (fun u : LinearMap.GeneralLinearGroup k _ ↦
    LinearMap.GeneralLinearGroup.generalLinearEquiv k _ u x) hge
  simpa using hx

end ExpAdSubgroup

section IsKilling

variable {k : Type u} [Field k] [CharZero k]

/-- **Every `ad`-nilpotent tangent vector of a Killing Lie algebra has a locally nilpotent
left-invariant derivation.** -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad
    {H : Type v} [CommRing H] [HopfAlgebra k H]
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x))
    (a : H) :
    ∃ n, (Bialgebra.leftInvariantDerivation
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[n] a = 0 := by
  refine Bialgebra.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isNilpotent
    (fun N hN ↦ ?_) a
  have : Module.Finite k N := hN
  let ρ : Module.Dual k (Bialgebra.CotangentSpace k H) →ₗ⁅k⁆ Module.End k N :=
    (Comodule.differential (R := k) (H := H) (M := N)).comp
      (Derivation.cotangentDualLieEquiv (R := k) (H := H)).toLieHom
  exact isNilpotent_apply_of_isNilpotent_ad (ρ := ρ) hx

/-- **Every inner automorphism in `Int(𝔤)` lies in the adjoint image of any closed subgroup with
full Lie algebra.** -/
theorem intLieAlgebra_le_map_quotientPointsSubgroup
    {H : Type u} [CommRing H] [HopfAlgebra k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    [LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {J : HopfIdeal k H} (hJ : J.lieSubalgebra (B := k) = ⊤) :
    intLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H)) ≤
      (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k)).map
          (Comodule.basePointsRepresentation (R := k) (H := H)
            (Module.Dual k (Bialgebra.CotangentSpace k H))).toHomUnits := by
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  refine intLieAlgebra_le_iff.mpr fun x hx ↦ ?_
  have hd := exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad hx
  have hxJ : Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈ J.lieSubalgebra (B := k) :=
    hJ.symm ▸ LieSubalgebra.mem_top _
  refine ⟨toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) hd),
    J.toConv_expPoint_mem_quotientPointsSubgroup hxJ hd, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro y
  simpa using basePointsRepresentation_adjoint_expPoint_eq_expAd hd hx y

/-- **Every inner automorphism in `Int(𝔤)` is realized by a rational point of any closed subgroup
with full Lie algebra.** -/
theorem exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_smul_of_mem_intLieAlgebra
    {H : Type u} [CommRing H] [HopfAlgebra k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    [LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {J : HopfIdeal k H} (hJ : J.lieSubalgebra (B := k) = ⊤)
    {γ : LinearMap.GeneralLinearGroup k (Module.Dual k (Bialgebra.CotangentSpace k H))}
    (hγ : γ ∈ intLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k),
      ∀ y : Module.Dual k (Bialgebra.CotangentSpace k H),
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g y =
          γ • y := by
  obtain ⟨g, hg, hgγ⟩ := intLieAlgebra_le_map_quotientPointsSubgroup hJ hγ
  refine ⟨g, hg, fun y ↦ ?_⟩
  have hy := congrArg (fun u : LinearMap.GeneralLinearGroup k _ ↦ u • y) hgγ
  simpa [Units.smul_def] using hy

end IsKilling

section Field

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

omit [Algebra.FiniteType k H] in
/-- **An `ad`-nilpotent element of a Killing tangent Lie algebra induces a locally nilpotent
left-invariant derivation on `H`.** -/
theorem exists_iterate_leftInvariantDerivation_cotangentDualLieEquiv_eq_zero
    {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    ∀ a : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] a = 0 :=
  exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad hx

/-- **The exponential `k`-point `exp x ∈ G(k)` attached to an `ad`-nilpotent element `x ∈ 𝔤`.** -/
noncomputable def expAdPoint {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    WithConv (H →ₐ[k] k) :=
  letI : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)
    (exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad hx))

omit [Algebra.FiniteType k H] in
/-- **`expAdPoint` unfolds to the Taylor exponential point of `cotangentDualLieEquiv x`.** -/
theorem expAdPoint_def {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    expAdPoint (H := H) hx =
      let : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
      toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)
        (exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad hx)) :=
  (rfl)

omit [Algebra.FiniteType k H] in
/-- **The exponential of `0 ∈ 𝔤` is the identity point of `G(k)`.** -/
@[simp]
theorem expAdPoint_zero (h0 : IsNilpotent (LieAlgebra.ad k 𝔤 (0 : 𝔤))) :
    expAdPoint (H := H) h0 = 1 := by
  let _ : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  simp only [expAdPoint_def, map_zero, Bialgebra.expPoint_zero]
  rfl

omit [Algebra.FiniteType k H] in
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
    (exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad hx)
    (Comodule.isNilpotent_differential_cotangentDualLieEquiv_of_isNilpotent_ad hx)

/-- **The adjoint action of `expAdPoint hx` on `𝔤` is the operator exponential `exp (ad x)`.** -/
@[simp]
theorem basePointsRepresentation_expAdPoint {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    Comodule.basePointsRepresentation (R := k) (H := H) 𝔤 (expAdPoint hx) =
      IsNilpotent.exp (LieAlgebra.ad k 𝔤 x) := by
  have hdiff : Comodule.differential (R := k) (H := H) (M := 𝔤)
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) = LieAlgebra.ad k 𝔤 x := by
    ext y
    rw [Derivation.differential_adjointComodule, LieEquiv.symm_apply_apply, LieAlgebra.ad_apply]
  rw [Comodule.basePointsRepresentation_expAdPoint (M := 𝔤) hx, hdiff]

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

omit [Algebra.FiniteType k H] in
/-- **If `x` lies in the Lie algebra of a closed subgroup `Spec (H / I)`, then `expAdPoint hx`
lies in that subgroup's `k`-points.** -/
theorem expAdPoint_mem_quotientPointsSubgroup (I : HopfIdeal k H)
    {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x))
    (hxI : Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈ I.lieSubalgebra (B := k)) :
    expAdPoint (H := H) hx ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H) I (CommAlgCat.of k k) := by
  let _ : Algebra ℚ H := Algebra.compHom H (algebraMap ℚ k)
  exact I.toConv_expPoint_mem_quotientPointsSubgroup hxI
    (exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad hx)

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
  (intLieAlgebra_le_map_quotientPointsSubgroup (J := ⊥) HopfIdeal.lieSubalgebra_bot).trans
    fun _ ⟨g, _, hg⟩ ↦ ⟨g, hg⟩

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
  intLieAlgebra_le_map_quotientPointsSubgroup
    (HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top (k := k) (H := H))

omit [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))] in
/-- **Kostant's subgroup `expAdSubgroup k e` is realized by rational points of `C_G(e)°`.** -/
theorem map_expAdSubgroup_le_map_quotientPointsSubgroup_centralizer_identityComponent
    [LieAlgebra ℚ 𝔤] (e : 𝔤) :
    (expAdSubgroup k e).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k 𝔤).symm.toMonoidHom ≤
      (CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H.obj e).identityComponent
        (CommAlgCat.of k k)).map
          (Comodule.basePointsRepresentation (R := k) (H := H.obj) 𝔤).toHomUnits :=
  map_expAdSubgroup_le_map_quotientPointsSubgroup e
    (centralizerHopfIdeal H.obj e).lieSubalgebra_identityComponent.ge

end IsAlgClosed

end TauCeti

namespace IsSl2Triple

open CategoryTheory TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

section Subgroup

variable {k : Type u} {H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]
  {h e f h' f' : Module.Dual k (Bialgebra.CotangentSpace k H)}

/-- **Kostant's conjugacy theorem at fixed `e` in any closed subgroup whose Lie algebra contains
`Lie(C_G(e))`.** Two `sl₂` triples `(h, e, f)` and `(h', e, f')` in `Lie(G)` sharing `e` are
conjugate by a rational point of `J`. Neither algebraic closedness of `k` nor a Killing hypothesis
on `Lie(G)` is required. -/
theorem exists_mem_quotientPointsSubgroup_basePointsRepresentation_e_eq_of_lieSubalgebra_le
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') {J : HopfIdeal k H}
    (hlie : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ J.lieSubalgebra (B := k)) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' := by
  let := ratLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))
  obtain ⟨φ, hφ, hφe, hφh, hφf⟩ := t.exists_lieEquiv_apply_eq (K := k) t'
  obtain ⟨g, hg, hgx⟩ :=
    exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_of_mem_expAdSubgroup hlie hφ
  exact ⟨g, hg, (hgx e).trans hφe, (hgx h).trans hφh, (hgx f).trans hφf⟩

/-- **Kostant's conjugacy theorem at fixed `e` in `C_G(e)(k)`.** Over any field of characteristic
zero, two `sl₂` triples `(h, e, f)` and `(h', e, f')` in `Lie(G)` sharing `e` are conjugate by a
rational point of the centralizer `C_G(e)`. -/
theorem exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_e_eq
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H e) (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' :=
  t.exists_mem_quotientPointsSubgroup_basePointsRepresentation_e_eq_of_lieSubalgebra_le t' le_rfl

end Subgroup

/-- **Kostant's conjugacy theorem at fixed nilpositive element, in `C_G(e)°(k)`.** Over an
algebraically closed field `k` of characteristic zero, if `G = Spec H` is of finite type, any two
`sl₂` triples `(h, e, f)` and `(h', e, f')` in `Lie(G)` sharing `e` are conjugate by a rational
point of the connected centralizer `C_G(e)°`. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_identityComponent_eq
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    {h f h' f' e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H.obj e).identityComponent (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' :=
  t.exists_mem_quotientPointsSubgroup_basePointsRepresentation_e_eq_of_lieSubalgebra_le t'
    (centralizerHopfIdeal H.obj e).lieSubalgebra_identityComponent.ge

end IsSl2Triple
