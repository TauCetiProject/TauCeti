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
public import TauCeti.Algebra.Lie.AdjointAction.ExpAdSubgroup
public import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.RepresentationTheory.Lie.AdNilpotent

/-!
# Adjoint action of exponential points and subgroup realization of inner automorphisms

Let `G = Spec H` be an affine group scheme over `R` with finite projective augmentation cotangent
space and Lie algebra `𝔤 = Module.Dual R (Bialgebra.CotangentSpace R H)`. Because the differentiated
adjoint representation is the Lie bracket (`Derivation.differential_adjointComodule`), the general
comodule exponential formula (`TauCeti.Comodule.basePointsRepresentation_expPoint_of_isNilpotent`)
shows that whenever `x ∈ 𝔤` is `ad`-nilpotent and its left-invariant derivation on `H` is locally
nilpotent, the rational point `exp x` acts on `𝔤` as `exp (ad x)`.

Over a field `k` of characteristic zero (`Module.Finite k (Bialgebra.CotangentSpace k H)`), local
nilpotence of the left-invariant derivation on `H` is automatic in two geometric settings, by
testing nilpotence on all finite-dimensional subcomodules of the regular representation `H`
(`TauCeti.Bialgebra.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isNilpotent`):

1. **Kostant's centralizer subgroup `expAdSubgroup k e` (for any affine group `G`).** Every
   generator `y ∈ ker (ad e) ⊓ [e, 𝔤]` has the form `⁅e, z⁆` with `⁅e, ⁅e, z⁆⁆ = 0`, so its image in
   every finite-dimensional representation of `𝔤` is nilpotent by Jacobson's lemma
   (`LinearMap.isNilpotent_lie_of_lie_lie_eq_zero`), without any Killing or reductivity assumption
   on `G`. Since `y` commutes with `e`, its exponential point lies in `C_G(e)(k)`—and over an
   algebraically closed field in `C_G(e)°(k)`. Hence every automorphism in `expAdSubgroup k e` is
   realized by a rational point of `C_G(e)` (and of `C_G(e)°`), upgrading Kostant's conjugacy
   theorem at fixed nilpositive element `e` (`IsSl2Triple.exists_lieEquiv_apply_eq`) to conjugacy by
   a rational point of `C_G(e)` (and of `C_G(e)°`).
2. **The inner automorphism group `Int(𝔤)` (when `𝔤` is Killing).** Every `ad`-nilpotent element
   `x ∈ 𝔤` acts nilpotently on every finite-dimensional representation of `𝔤`
   (`TauCeti.isNilpotent_apply_of_isNilpotent_ad`). Consequently `Int(𝔤)` is realized by rational
   points of any closed subgroup of `G` with full Lie algebra `𝔤`, in particular by `G(k)` and—over
   an algebraically closed field—by the identity component `G⁰(k)`.

## Main results

* `TauCeti.basePointsRepresentation_adjoint_expPoint` and
  `TauCeti.basePointsRepresentation_adjoint_expPointAt`: `exp x` and `exp (t x)` act on `𝔤` as
  `IsNilpotent.exp (ad x)` and `IsNilpotent.exp (t • ad x)`.
* `TauCeti.exists_iterate_leftInvariantDerivation_of_mem_ker_inf_range` and
  `TauCeti.exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup`: elements of
  `ker (ad e) ⊓ [e, 𝔤]` have locally nilpotent invariant vector fields, and `expAdSubgroup k e` is
  realized in any closed subgroup whose Lie algebra contains `Lie(C_G(e))`.
* `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_eq` and
  `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_identityComponent_eq`:
  **Kostant's conjugacy theorem at fixed `e`** in `C_G(e)(k)` and in `C_G(e)°(k)`.
* `TauCeti.exists_iterate_leftInvariantDerivation_of_isNilpotent_ad`,
  `TauCeti.exists_mem_quotientPointsSubgroup_of_mem_intLieAlgebra`, and
  `TauCeti.exists_mem_quotientPointsSubgroup_bot_identityComponent_of_mem_intLieAlgebra`: when `𝔤`
  is Killing, `ad`-nilpotent elements integrate to `G` and `Int(𝔤)` is realized by `G⁰(k)`.

## References

* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, §3.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, Theorem 3.4.10.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v

attribute [local instance] Derivation.adjointComodule
attribute [local instance 100] LieRing.ofAssociativeRing

section General

variable {R : Type u} {H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- The differentiated adjoint representation at `cotangentLinearEquiv x` is `ad x`. -/
@[simp]
theorem differential_adjointComodule_cotangentLinearEquiv
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Comodule.differential (R := R) (H := H)
        (M := Module.Dual R (Bialgebra.CotangentSpace R H))
        (Derivation.cotangentLinearEquiv (R := R) (A := H) x) =
      LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x := by
  ext y
  rw [Derivation.differential_adjointComodule, ← Derivation.cotangentDualLieEquiv_apply,
    LieEquiv.symm_apply_apply, LieAlgebra.ad_apply]

/-- The differentiated adjoint representation at `cotangentDualLieEquiv x` is `ad x`. -/
theorem differential_adjointComodule_cotangentDualLieEquiv
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Comodule.differential (R := R) (H := H)
        (M := Module.Dual R (Bialgebra.CotangentSpace R H))
        (Derivation.cotangentDualLieEquiv (R := R) (H := H) x) =
      LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x := by
  rw [Derivation.cotangentDualLieEquiv_apply, differential_adjointComodule_cotangentLinearEquiv]

variable [Algebra ℚ H] [Module ℚ (Module.Dual R (Bialgebra.CotangentSpace R H))]

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
  rw [Comodule.basePointsRepresentation_expPoint_of_isNilpotent _ hd hnil,
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

omit [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  [Module ℚ (Module.Dual R (Bialgebra.CotangentSpace R H))] in
/-- If `d = cotangentDualLieEquiv x` lies in the Lie algebra of a closed subgroup `J`, its
exponential point lies in `J(R)`. -/
theorem expPoint_cotangentDualLieEquiv_mem_quotientPointsSubgroup (J : HopfIdeal R H)
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)}
    (hJ : Derivation.cotangentDualLieEquiv (R := R) (H := H) x ∈ J.lieSubalgebra (B := R))
    (hd : ∀ a : H, ∃ n,
      (Bialgebra.leftInvariantDerivation (Derivation.cotangentDualLieEquiv (R := R) (H := H) x))^[n]
        a = 0) :
    toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := R) (H := H) x) hd) ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) J
        (CommAlgCat.of R R) := by
  rw [← Bialgebra.expPointAt_one]
  exact J.expPointAt_mem_quotientPointsSubgroup hJ hd (1 : R)

end General

section KerInfRange

variable {k : Type u} {H : Type v} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]

/-- **Every element of `ker (ad e) ⊓ [e, 𝔤]` has a locally nilpotent left-invariant derivation.**
No Killing or reductivity hypothesis is required: Jacobson's lemma shows nilpotence on every
finite-dimensional subcomodule of `H`. -/
theorem exists_iterate_leftInvariantDerivation_of_mem_ker_inf_range
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
  let ρ : Module.Dual k (Bialgebra.CotangentSpace k H) →ₗ⁅k⁆ Module.End k N :=
    (Comodule.differential (R := k) (H := H) (M := N)).comp
      (Derivation.cotangentDualLieEquiv (R := k) (H := H)).toLieHom
  change IsNilpotent (ρ (LieAlgebra.ad k _ e z))
  rw [LieAlgebra.ad_apply, LieHom.map_lie]
  refine LinearMap.isNilpotent_lie_of_lie_lie_eq_zero ?_
  rw [← LieHom.map_lie, ← LieHom.map_lie, hye, map_zero]

end KerInfRange

section ExpAdSubgroup

variable {k : Type u} {H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **Kostant's subgroup `expAdSubgroup k e` is realized by rational points of any closed subgroup
whose Lie algebra contains `Lie(C_G(e))`.** -/
theorem exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup
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
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  let G := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
    (CommAlgCat.of k k)
  let Φ : WithConv (H →ₐ[k] k) →*
      (Module.Dual k (Bialgebra.CotangentSpace k H) ≃ₗ[k]
        Module.Dual k (Bialgebra.CotangentSpace k H)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k
      (Module.Dual k (Bialgebra.CotangentSpace k H))).toMonoidHom.comp
      (Comodule.basePointsRepresentation
        (Module.Dual k (Bialgebra.CotangentSpace k H))).toHomUnits
  have hle : expAdSubgroup k e ≤ G.map Φ := by
    refine expAdSubgroup_le_iff.mpr fun y hy hmem ↦ ?_
    have hd := exists_iterate_leftInvariantDerivation_of_mem_ker_inf_range hmem
    have hyJ : Derivation.cotangentDualLieEquiv (R := k) (H := H) y ∈ J.lieSubalgebra (B := k) := by
      apply hlie
      rw [mem_lieSubalgebra_centralizerHopfIdeal_iff, ← LieEquiv.map_lie]
      have hker : ⁅e, y⁆ = 0 := LinearMap.mem_ker.mp hmem.1
      rw [hker, map_zero]
    refine ⟨toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) y) hd),
      expPoint_cotangentDualLieEquiv_mem_quotientPointsSubgroup J hyJ hd, ?_⟩
    apply LinearEquiv.ext
    intro x
    have hact := LinearMap.congr_fun
      (@basePointsRepresentation_adjoint_expPoint k H _ _ _ _ _ _
        (LieAlgebra.toModule (R := ℚ)) _ hd hy) x
    simpa [Φ, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      expAd_apply y hy] using hact
  obtain ⟨g, hg, hgψ⟩ := hle hψ
  refine ⟨g, hg, fun x ↦ ?_⟩
  have hx := LinearEquiv.congr_fun hgψ.symm x
  simpa [Φ, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap] using hx.symm

end ExpAdSubgroup

section IsKilling

variable {k : Type u} [Field k] [CharZero k]

/-- **Every `ad`-nilpotent tangent vector of a Killing Lie algebra has a locally nilpotent
left-invariant derivation.** -/
theorem exists_iterate_leftInvariantDerivation_of_isNilpotent_ad
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

/-- **Every inner automorphism in `Int(𝔤)` is realized by a rational point of any closed subgroup
with full Lie algebra.** -/
theorem exists_mem_quotientPointsSubgroup_of_mem_intLieAlgebra
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
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  let G := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
    (CommAlgCat.of k k)
  let Φ := (Comodule.basePointsRepresentation (R := k) (H := H)
    (Module.Dual k (Bialgebra.CotangentSpace k H))).toHomUnits
  have hle : intLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H)) ≤ G.map Φ := by
    refine intLieAlgebra_le_iff.mpr fun x hx ↦ ?_
    have hd := exists_iterate_leftInvariantDerivation_of_isNilpotent_ad hx
    have hxJ : Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈ J.lieSubalgebra (B := k) :=
      hJ.symm ▸ LieSubalgebra.mem_top _
    refine ⟨toConv (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) hd),
      expPoint_cotangentDualLieEquiv_mem_quotientPointsSubgroup J hxJ hd, ?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro y
    have hact := LinearMap.congr_fun
      (@basePointsRepresentation_adjoint_expPoint k H _ _ _ _ _ _
        (LieAlgebra.toModule (R := ℚ)) _ hd hx) y
    have hexp := LinearMap.congr_fun (coe_ofLinearEquiv_expAd x hx) y
    simpa only [Φ, MonoidHom.coe_toHomUnits] using hact.trans hexp.symm
  obtain ⟨g, hg, hgγ⟩ := hle hγ
  refine ⟨g, hg, fun y ↦ ?_⟩
  have hy := congrArg (fun u : LinearMap.GeneralLinearGroup k _ ↦ u • y) hgγ
  simpa [Φ, Units.smul_def] using hy

/-- **Every inner automorphism in `Int(𝔤)` is realized by a rational point of `G⁰`.** -/
theorem exists_mem_quotientPointsSubgroup_bot_identityComponent_of_mem_intLieAlgebra
    [IsAlgClosed k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    [LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {γ : LinearMap.GeneralLinearGroup k (Module.Dual k (Bialgebra.CotangentSpace k H))}
    (hγ : γ ∈ intLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj (⊥ : HopfIdeal k H).identityComponent
        (CommAlgCat.of k k),
      ∀ y : Module.Dual k (Bialgebra.CotangentSpace k H),
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g y =
          γ • y := by
  refine exists_mem_quotientPointsSubgroup_of_mem_intLieAlgebra ?_ hγ
  rw [HopfIdeal.lieSubalgebra_identityComponent, HopfIdeal.lieSubalgebra_bot]

end IsKilling

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
theorem exists_mem_quotientPointsSubgroup_eq_of_lieSubalgebra_le
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') {J : HopfIdeal k H}
    (hlie : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ J.lieSubalgebra (B := k)) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' := by
  let _ : LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
    { lie_smul := fun q x y ↦ map_rat_smul (LieAlgebra.ad k _ x) q y }
  obtain ⟨φ, hφ, hφe, hφh, hφf⟩ := t.exists_lieEquiv_apply_eq (K := k) t'
  obtain ⟨g, hg, hgx⟩ := exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup hlie hφ
  exact ⟨g, hg, (hgx e).trans hφe, (hgx h).trans hφh, (hgx f).trans hφf⟩

/-- **Kostant's conjugacy theorem at fixed `e` in `C_G(e)(k)`.** Over any field of characteristic
zero, two `sl₂` triples `(h, e, f)` and `(h', e, f')` in `Lie(G)` sharing `e` are conjugate by a
rational point of the centralizer `C_G(e)`. -/
theorem exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_eq
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H e) (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' :=
  t.exists_mem_quotientPointsSubgroup_eq_of_lieSubalgebra_le t' le_rfl

end Subgroup

section IdentityComponent

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  {h e f h' f' : Module.Dual k (Bialgebra.CotangentSpace k H)}

/-- **Kostant's conjugacy theorem at fixed `e` in `C_G(e)°(k)`.** Over an algebraically closed
field of characteristic zero, any two `sl₂` triples `(h, e, f)` and `(h', e, f')` in `Lie(G)`
sharing `e` are conjugate by a rational point of the connected centralizer `C_G(e)°`. -/
theorem exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_identityComponent_eq
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H e).identityComponent (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' :=
  t.exists_mem_quotientPointsSubgroup_eq_of_lieSubalgebra_le t'
    (centralizerHopfIdeal H e).lieSubalgebra_identityComponent.ge

end IdentityComponent

end IsSl2Triple
