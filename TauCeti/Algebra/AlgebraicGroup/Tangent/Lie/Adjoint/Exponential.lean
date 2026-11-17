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
curves `Bialgebra.expPointAt` on `H` to the inner automorphisms `exp (ad x)` of `𝔤`, realizing
both Kostant's subgroup `expAdSubgroup k e` inside the centralizer `C_G(e)` and the inner
automorphism group `Int(𝔤)` inside `G`:

* **Automatic local nilpotence.** If `x ∈ 𝔤` is a common zero of the Lie-invariant polynomial
  functions `S(𝔤*)^𝔤` of positive degree, then `x` acts nilpotently on every finite-dimensional
  `𝔤`-module (`TauCeti.isNilpotent_toEnd_of_forall_lift_eval_eq_zero`), in particular on a faithful
  comodule representation of `G`. By descent along the coordinate morphism
  (`Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential`), the
  left-invariant derivation of `x` is locally nilpotent on `H`
  (`TauCeti.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_lift_eval_eq_zero`). This
  applies in particular to:
  * any `ad`-nilpotent element of `⁅𝔤, 𝔤⁆` when `𝔤` is reductive (`LieAlgebra.HasCentralRadical`),
  * any `ad`-nilpotent element of `𝔤` when `𝔤` has nondegenerate Killing form
    (`LieAlgebra.IsKilling`),
  with **no** algebraic-closure or connectedness hypothesis on `G`.
* **Adjoint action of exponentials.** Whenever the left-invariant derivation of `x` is locally
  nilpotent on `H`, `ad x` is nilpotent and the adjoint automorphism of `expPointAt x t` is
  `exp (ad (t • x))` (`TauCeti.basePointsAdjointLieEquiv_expPointAt`,
  `TauCeti.basePointsAdjointLieEquiv_expPoint`).
* **Realizing `expAdSubgroup` and `Int(𝔤)`.** For a reductive Lie algebra, every generator
  `y ∈ ker (ad e) ⊓ [e, 𝔤]` of `expAdSubgroup k e` lies in `⁅𝔤, 𝔤⁆`, so its exponential lies in
  every closed subgroup `K` whose Lie algebra contains `ker (ad e)`. In particular:
  * `expAdSubgroup k e` lies in the adjoint image of `C_G(e)(k)` over any characteristic-zero field
    `k`, and
  * over an algebraically closed field `k`, `expAdSubgroup k e` lies in the adjoint image of the
    identity component `C_G(e)°(k)`.
  Similarly, when `𝔤` has nondegenerate Killing form, `Int(𝔤)` lies in the adjoint image of `G(k)`
  (and of `G°(k)` over an algebraically closed field).
* **Group-level Kostant conjugacy.** Combining this realization with the Lie-algebraic Kostant
  conjugacy theorem (`IsSl2Triple.exists_lieEquiv_apply_eq`), any two `sl₂` triples `(h, e, f)`
  and `(h', e, f')` sharing their nilpositive element `e` in a reductive Lie algebra are conjugate
  under `C_G(e)(k)` (without algebraic closure or connectedness), and under `C_G(e)°(k)` when `k`
  is algebraically closed.

## Main declarations

* `TauCeti.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_lift_eval_eq_zero`:
  common zeros of `S(𝔤*)^𝔤` of positive degree have locally nilpotent invariant derivations.
* `TauCeti.exists_iterate_leftInvariantDerivation_eq_zero_of_mem_derivedSeries_of_isNilpotent_ad`:
  specialization to `ad`-nilpotent elements in `⁅𝔤, 𝔤⁆` for reductive `𝔤`.
* `TauCeti.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad`:
  specialization to `ad`-nilpotent elements when `𝔤` has nondegenerate Killing form.
* `TauCeti.basePointsAdjointLieEquiv_expPointAt` and `TauCeti.basePointsAdjointLieEquiv_expPoint`:
  the adjoint Lie automorphism of `expPointAt` / `expPoint` is `expAd`.
* `TauCeti.expAdSubgroup_le_map_quotientPointsSubgroup`: realization of `expAdSubgroup k e` inside
  any closed subgroup whose Lie algebra contains `ker (ad e)`.
* `TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup`: realization of `Int(𝔤)` inside any closed
  subgroup with full Lie algebra when `𝔤` has nondegenerate Killing form.
* `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizer_eq` and
  `IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizer_identityComponent_eq`:
  group-level Kostant conjugacy in `C_G(e)(k)` and `C_G(e)°(k)`.

## References

* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, Theorem 3.6.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, Theorem 3.4.10.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
-/

public section

open scoped TensorProduct
open WithConv LieAlgebra

namespace TauCeti

universe u

section LocalNilpotence

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- The `𝔤`-module structure on any `H`-comodule `M`, induced by differentiating the coaction
through `Derivation.cotangentDualLieEquiv`. -/
@[instance_reducible]
private noncomputable def comoduleLieRingModule (M : Type*) [AddCommGroup M] [Module k M]
    [Comodule k H M] : LieRingModule 𝔤 M where
  bracket x m := Comodule.differential (R := k) (H := H) (M := M)
    (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) m
  add_lie x y m := by
    simp only [map_add, LinearMap.add_apply]
  lie_add x m n := map_add _ m n
  leibniz_lie x y m := by
    let : LieRing (Module.End k M) := LieRing.ofAssociativeRing
    have hlie := (Comodule.differential (R := k) (H := H) (M := M)).map_lie
      (x := Derivation.cotangentDualLieEquiv (R := k) (H := H) x)
      (y := Derivation.cotangentDualLieEquiv (R := k) (H := H) y)
    have hm := LinearMap.congr_fun hlie m
    rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, mul_apply_eq_comp,
      mul_apply_eq_comp] at hm
    rw [LieEquiv.map_lie, hm, sub_add_cancel]

omit [CharZero k] [Algebra.FiniteType k H] in
private theorem comoduleLieModule (M : Type*) [AddCommGroup M] [Module k M]
    [Comodule k H M] :
    letI := comoduleLieRingModule (k := k) (H := H) M
    LieModule k 𝔤 M :=
  letI := comoduleLieRingModule (k := k) (H := H) M
  { smul_lie := fun r x m ↦ by
      -- Unfold the local bracket definition to use linearity of `differential`.
      change Comodule.differential (R := k) (H := H) (M := M)
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) (r • x)) m =
          r • Comodule.differential (R := k) (H := H) (M := M)
            (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) m
      rw [map_smul, map_smul, LinearMap.smul_apply]
    lie_smul := fun r x m ↦ by
      -- Unfold the local bracket definition to apply `map_smul` of `differential`.
      change Comodule.differential (R := k) (H := H) (M := M)
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) (r • m) =
          r • Comodule.differential (R := k) (H := H) (M := M)
            (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) m
      exact map_smul _ r m }

/-- **Common zeros of positive-degree Lie invariants have locally nilpotent invariant
derivations.** Over a field of characteristic zero, if every `p ∈ S(𝔤*)^𝔤` with zero constant term
vanishes at `x ∈ 𝔤`, then the left-invariant derivation of `x` is locally nilpotent on `H`.
No algebraic-closure or connectedness hypothesis is needed. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_lift_eval_eq_zero {x : 𝔤}
    (hx : ∀ p ∈ SymmetricAlgebra.lieInvariants k 𝔤 (Module.Dual k 𝔤),
      SymmetricAlgebra.algebraMapInv p = 0 →
        _root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p = 0) :
    ∀ h : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0 := by
  obtain ⟨M, n, b, hsurj⟩ := Comodule.exists_coordinateBialgHom_surjective (k := k) (H := H)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k M := Module.Finite.of_basis b
  let : LieRingModule 𝔤 M := comoduleLieRingModule (k := k) (H := H) M
  let : LieModule k 𝔤 M := comoduleLieModule (k := k) (H := H) M
  have hnil : IsNilpotent (Comodule.differential (R := k) (H := H) (M := M)
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)) := by
    have hto := isNilpotent_toEnd_of_forall_lift_eval_eq_zero (K := k) (L := 𝔤) M hx
    have heq : LieModule.toEnd k 𝔤 M x =
        Comodule.differential (R := k) (H := H) (M := M)
          (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) :=
      LinearMap.ext fun _ ↦ rfl
    rwa [heq] at hto
  exact (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)
    |>.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential b hsurj hnil

/-- **Local nilpotence for `ad`-nilpotent elements in the derived ideal of a reductive Lie
algebra.** No algebraic-closure or connectedness hypothesis is needed. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_mem_derivedSeries_of_isNilpotent_ad
    [HasCentralRadical k 𝔤] {x : 𝔤}
    (hder : x ∈ derivedSeries k 𝔤 1) (hnil : IsNilpotent (ad k 𝔤 x)) :
    ∀ h : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0 :=
  exists_iterate_leftInvariantDerivation_eq_zero_of_forall_lift_eval_eq_zero
    (mem_derivedSeries_and_isNilpotent_ad_iff_forall_lift_eval_eq_zero.mp ⟨hder, hnil⟩)

/-- **Local nilpotence for `ad`-nilpotent elements when the Killing form is nondegenerate.** No
algebraic-closure or connectedness hypothesis is needed. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad
    [IsKilling k 𝔤] {x : 𝔤} (hnil : IsNilpotent (ad k 𝔤 x)) :
    ∀ h : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0 :=
  exists_iterate_leftInvariantDerivation_eq_zero_of_forall_lift_eval_eq_zero
    (isNilpotent_ad_iff_forall_lift_eval_eq_zero.mp hnil)

end LocalNilpotence

section AdjointAction

variable {k H : Type u} [CommRing k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [Module.Projective k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

attribute [local instance] Derivation.adjointComodule

/-- If the left-invariant derivation of `x ∈ 𝔤` is locally nilpotent on `H`, then `ad x` is
nilpotent on `𝔤`. -/
theorem isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero
    {x : 𝔤}
    (hx : ∀ h : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0) :
    IsNilpotent (ad k 𝔤 x) := by
  have hdiff : Comodule.differential (R := k) (H := H) (M := 𝔤)
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) = ad k 𝔤 x := by
    ext y
    rw [Derivation.differential_adjointComodule, LieEquiv.symm_apply_apply, ad_apply]
  rw [← hdiff]
  exact Comodule.isNilpotent_differential (M := 𝔤) _ hx

variable [Algebra ℚ H] [LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H))]

/-- **Adjoint action of an exponential curve.** The base-point adjoint automorphism of
`expPointAt x t` is `expAd (t • x)`. -/
theorem basePointsAdjointLieEquiv_expPointAt {x : 𝔤}
    (hx : ∀ h : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0)
    (t : k) :
    Derivation.basePointsAdjointLieEquiv (R := k) (H := H)
        (Bialgebra.expPointAt (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) hx t) =
      expAd (K := k) (t • x)
        (((isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero hx).smul t)
          |>.exists_pow_apply_eq_zero |> fun h ↦ by simpa only [map_smul] using h) := by
  have hnil : IsNilpotent (ad k 𝔤 (t • x)) := by
    rw [map_smul]
    exact (isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero hx).smul t
  have hdiff : Comodule.differential (R := k) (H := H) (M := 𝔤)
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) = ad k 𝔤 x := by
    ext y
    rw [Derivation.differential_adjointComodule, LieEquiv.symm_apply_apply, ad_apply]
  refine LieEquiv.ext fun y ↦ ?_
  rw [Derivation.basePointsAdjointLieEquiv_apply,
    Comodule.basePointsRepresentation_expPointAt (M := 𝔤), hdiff]
  have heq : t • ad k 𝔤 x = ad k 𝔤 (t • x) := (map_smul (ad k 𝔤) t x).symm
  conv_lhs => rw [heq]
  exact (expAd_apply (K := k) (t • x) hnil y).symm

/-- **Adjoint action of an exponential point.** The base-point adjoint automorphism of
`expPoint x` is `expAd x`. -/
theorem basePointsAdjointLieEquiv_expPoint {x : 𝔤}
    (hx : ∀ h : H, ∃ m,
      (Bialgebra.leftInvariantDerivation
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x))^[m] h = 0) :
    Derivation.basePointsAdjointLieEquiv (R := k) (H := H)
        (WithConv.toConv
          (Bialgebra.expPoint (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) hx)) =
      expAd (K := k) x
        (IsNilpotent.exists_pow_apply_eq_zero
          (isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero hx)) := by
  rw [← Bialgebra.expPointAt_one]
  refine LieEquiv.ext fun y ↦ ?_
  have h := DFunLike.congr_fun (basePointsAdjointLieEquiv_expPointAt (k := k) (H := H) hx 1) y
  have hnil := isNilpotent_ad_of_exists_iterate_leftInvariantDerivation_eq_zero hx
  rw [h, expAd_apply (K := k) _ (by simpa only [one_smul] using hnil),
    expAd_apply (K := k) _ hnil, one_smul]

end AdjointAction

section Realization

open LinearMap.GeneralLinearGroup

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

attribute [local instance] Derivation.adjointComodule

omit [CharZero k] in
private theorem adjointLinearEquiv_basePointsAdjointLieEquiv (g : WithConv (H →ₐ[k] k)) :
    (generalLinearEquiv k 𝔤).toMonoidHom
        (Representation.asGroupHom (Comodule.basePointsRepresentation (H := H) 𝔤) g) =
      (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv := by
  refine LinearEquiv.ext fun y ↦ ?_
  -- Unfold `generalLinearEquiv` application via `Representation.asGroupHom`.
  change (Representation.asGroupHom (Comodule.basePointsRepresentation (H := H) 𝔤) g :
      Module.End k 𝔤) y = _
  rw [Representation.asGroupHom_apply, LieEquiv.coe_toLinearEquiv,
    Derivation.basePointsAdjointLieEquiv_apply]

/-- **Realizing Kostant's subgroup inside a closed subgroup.** Let `𝔤` be reductive over a field
`k` of characteristic zero and let `I` be a Hopf ideal whose Lie subalgebra contains `ker (ad e)`.
Then every element of `expAdSubgroup k e` is realized as the adjoint automorphism of a rational
point in the closed subgroup cut out by `I`. No algebraic-closure or connectedness hypothesis is
needed. -/
theorem expAdSubgroup_le_map_quotientPointsSubgroup [HasCentralRadical k 𝔤] [LieAlgebra ℚ 𝔤]
    (e : 𝔤) (I : HopfIdeal k H)
    (hI : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ I.lieSubalgebra (B := k)) :
    expAdSubgroup k e ≤
      (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
          (CommAlgCat.of k k)).map
        ((generalLinearEquiv k 𝔤).toMonoidHom.comp
          (Representation.asGroupHom (Comodule.basePointsRepresentation (H := H) 𝔤))) := by
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  refine expAdSubgroup_le_iff.2 fun y hy hy_mem ↦ ?_
  obtain ⟨hyker, hyrange⟩ := Submodule.mem_inf.mp hy_mem
  have hder : y ∈ derivedSeries k 𝔤 1 := by
    obtain ⟨z, rfl⟩ := hyrange
    exact lie_mem_derivedSeries_one e z
  have hD := exists_iterate_leftInvariantDerivation_eq_zero_of_mem_derivedSeries_of_isNilpotent_ad
    (H := H) hder hy
  set d := Derivation.cotangentDualLieEquiv (R := k) (H := H) y
  have hdC : d ∈ (centralizerHopfIdeal H e).lieSubalgebra (B := k) := by
    rw [mem_lieSubalgebra_centralizerHopfIdeal_iff]
    rw [LinearMap.mem_ker, ad_apply] at hyker
    rw [← LieEquiv.map_lie, hyker, map_zero]
  refine ⟨Bialgebra.expPointAt d hD (1 : k),
    I.expPointAt_mem_quotientPointsSubgroup (hI hdC) hD (1 : k), ?_⟩
  rw [MonoidHom.comp_apply, adjointLinearEquiv_basePointsAdjointLieEquiv, Bialgebra.expPointAt_one,
    basePointsAdjointLieEquiv_expPoint (k := k) (H := H) hD]

/-- Pointwise form of `expAdSubgroup_le_map_quotientPointsSubgroup`: every element of
`expAdSubgroup k e` is realized by `g ∈ quotientPointsSubgroup I` whenever `Lie(C_G(e)) ≤ Lie(I)`.
-/
theorem exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup [HasCentralRadical k 𝔤]
    [LieAlgebra ℚ 𝔤] {e : 𝔤} (I : HopfIdeal k H)
    (hI : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ I.lieSubalgebra (B := k))
    {φ : 𝔤 ≃ₗ[k] 𝔤} (hφ : φ ∈ expAdSubgroup k e) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
        (CommAlgCat.of k k),
      (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = φ := by
  obtain ⟨g, hg, hgeq⟩ := expAdSubgroup_le_map_quotientPointsSubgroup (H := H) e I hI hφ
  refine ⟨g, hg, ?_⟩
  simpa only [MonoidHom.comp_apply, adjointLinearEquiv_basePointsAdjointLieEquiv] using hgeq

/-- Over any field of characteristic zero, `expAdSubgroup k e` is realized inside the centralizer
`C_G(e)(k)`. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_of_mem_expAdSubgroup [HasCentralRadical k 𝔤]
    [LieAlgebra ℚ 𝔤] {e : 𝔤} {φ : 𝔤 ≃ₗ[k] 𝔤} (hφ : φ ∈ expAdSubgroup k e) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H e) (CommAlgCat.of k k),
      (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = φ :=
  exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup (centralizerHopfIdeal H e) le_rfl hφ

/-- **Realizing `Int(𝔤)` inside a closed subgroup with full Lie algebra.** When `𝔤` has
nondegenerate Killing form over a field of characteristic zero and `I` is a Hopf ideal with
`I.lieSubalgebra = ⊤` (such as `⊥`, or `identityComponentHopfIdeal` over an algebraically closed
field), `Int(𝔤)` lies in the adjoint image of the rational points of `I`. -/
theorem intLieAlgebra_le_map_quotientPointsSubgroup [IsKilling k 𝔤] [LieAlgebra ℚ 𝔤]
    (I : HopfIdeal k H) (hI : I.lieSubalgebra (B := k) = ⊤) :
    intLieAlgebra k 𝔤 ≤
      (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
          (CommAlgCat.of k k)).map
        (Representation.asGroupHom (Comodule.basePointsRepresentation (H := H) 𝔤)) := by
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  refine intLieAlgebra_le_iff.2 fun x hx ↦ ?_
  have hD := exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_ad (H := H) hx
  set d := Derivation.cotangentDualLieEquiv (R := k) (H := H) x
  have hdI : d ∈ I.lieSubalgebra (B := k) := hI.symm ▸ LieSubalgebra.mem_top d
  refine ⟨Bialgebra.expPointAt d hD (1 : k),
    I.expPointAt_mem_quotientPointsSubgroup hdI hD (1 : k), ?_⟩
  apply Units.ext
  refine LinearMap.ext fun y ↦ ?_
  rw [Representation.asGroupHom_apply, coe_ofLinearEquiv_expAd x hx, Bialgebra.expPointAt_one,
    ← Derivation.basePointsAdjointLieEquiv_apply,
    basePointsAdjointLieEquiv_expPoint (k := k) (H := H) hD, expAd_apply (K := k) x hx y]

/-- When `𝔤` has nondegenerate Killing form, every element of `Int(𝔤)` is realized as the adjoint
action of a rational point of `G`, over any characteristic-zero field `k`. -/
theorem exists_basePointsRepresentation_eq_of_mem_intLieAlgebra [IsKilling k 𝔤] [LieAlgebra ℚ 𝔤]
    {φ : LinearMap.GeneralLinearGroup k 𝔤} (hφ : φ ∈ intLieAlgebra k 𝔤) :
    ∃ g : WithConv (H →ₐ[k] k),
      Representation.asGroupHom (Comodule.basePointsRepresentation (H := H) 𝔤) g = φ := by
  obtain ⟨g, -, hgeq⟩ :=
    intLieAlgebra_le_map_quotientPointsSubgroup (H := H) (⊥ : HopfIdeal k H)
      (HopfIdeal.lieSubalgebra_bot (R := k) (H := H) (B := k)) hφ
  exact ⟨g, hgeq⟩

end Realization

section IdentityComponent

open LinearMap.GeneralLinearGroup

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

attribute [local instance] Derivation.adjointComodule

/-- Over an algebraically closed field of characteristic zero, every element of `expAdSubgroup k e`
is realized by a rational point in the identity component `C_G(e)°(k)` of the centralizer. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_identityComponent_of_mem_expAdSubgroup
    [HasCentralRadical k 𝔤] [LieAlgebra ℚ 𝔤] {e : 𝔤} {φ : 𝔤 ≃ₗ[k] 𝔤}
    (hφ : φ ∈ expAdSubgroup k e) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H e).identityComponent (CommAlgCat.of k k),
      (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g).toLinearEquiv = φ :=
  exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup
    (centralizerHopfIdeal H e).identityComponent
    (by rw [HopfIdeal.lieSubalgebra_identityComponent]) hφ

/-- Over an algebraically closed field of characteristic zero, when `𝔤` has nondegenerate Killing
form, every element of `Int(𝔤)` is realized by a rational point of the identity component `G°(k)`.
-/
theorem exists_mem_identityComponent_basePointsRepresentation_eq_of_mem_intLieAlgebra
    [IsKilling k 𝔤] [LieAlgebra ℚ 𝔤] {φ : LinearMap.GeneralLinearGroup k 𝔤}
    (hφ : φ ∈ intLieAlgebra k 𝔤) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      Representation.asGroupHom (Comodule.basePointsRepresentation (H := H) 𝔤) g = φ := by
  exact intLieAlgebra_le_map_quotientPointsSubgroup (H := H)
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top hφ

end IdentityComponent

end TauCeti

namespace IsSl2Triple

open TauCeti WithConv

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
    {h e f h' f' : 𝔤} (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f')
    (I : HopfIdeal k H)
    (hI : (centralizerHopfIdeal H e).lieSubalgebra (B := k) ≤ I.lieSubalgebra (B := k)) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
        (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (H := H) 𝔤 g e = e ∧
      Comodule.basePointsRepresentation (H := H) 𝔤 g h = h' ∧
      Comodule.basePointsRepresentation (H := H) 𝔤 g f = f' := by
  let : LieAlgebra ℚ 𝔤 := ratLieAlgebra k 𝔤
  obtain ⟨φ, hφ, hφe, hφh, hφf⟩ := t.exists_lieEquiv_apply_eq (K := k) t'
  obtain ⟨g, hg, hgeq⟩ := exists_mem_quotientPointsSubgroup_of_mem_expAdSubgroup I hI hφ
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · have := LinearEquiv.congr_fun hgeq e
    simpa only [LieEquiv.coe_toLinearEquiv, Derivation.basePointsAdjointLieEquiv_apply] using
      this.trans hφe
  · have := LinearEquiv.congr_fun hgeq h
    simpa only [LieEquiv.coe_toLinearEquiv, Derivation.basePointsAdjointLieEquiv_apply] using
      this.trans hφh
  · have := LinearEquiv.congr_fun hgeq f
    simpa only [LieEquiv.coe_toLinearEquiv, Derivation.basePointsAdjointLieEquiv_apply] using
      this.trans hφf

/-- **Group-level Kostant conjugacy in `C_G(e)(k)`.** Two `sl₂` triples `(h, e, f)` and
`(h', e, f')` with the same nilpositive element `e` in a reductive Lie algebra over a field of
characteristic zero are conjugate by a rational point of the centralizer `C_G(e)(k)`. No
algebraic-closure or connectedness hypothesis is needed. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_eq [LieAlgebra.HasCentralRadical k 𝔤]
    {h e f h' f' : 𝔤} (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (centralizerHopfIdeal H e) (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (H := H) 𝔤 g e = e ∧
      Comodule.basePointsRepresentation (H := H) 𝔤 g h = h' ∧
      Comodule.basePointsRepresentation (H := H) 𝔤 g f = f' :=
  t.exists_mem_quotientPointsSubgroup_eq_of_centralizer_lieSubalgebra_le t'
    (centralizerHopfIdeal H e) le_rfl

end General

section IdentityComponent

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Group-level Kostant conjugacy in `C_G(e)°(k)`.** Over an algebraically closed field of
characteristic zero, two `sl₂` triples `(h, e, f)` and `(h', e, f')` sharing their nilpositive
element `e` in a reductive Lie algebra are conjugate by a rational point of the connected
centralizer `C_G(e)°(k)`. -/
theorem exists_mem_quotientPointsSubgroup_centralizer_identityComponent_eq
    [LieAlgebra.HasCentralRadical k 𝔤]
    {h e f h' f' : 𝔤} (t : IsSl2Triple h e f) (t' : IsSl2Triple h' e f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H e).identityComponent (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (H := H) 𝔤 g e = e ∧
      Comodule.basePointsRepresentation (H := H) 𝔤 g h = h' ∧
      Comodule.basePointsRepresentation (H := H) 𝔤 g f = f' :=
  t.exists_mem_quotientPointsSubgroup_eq_of_centralizer_lieSubalgebra_le t'
    (centralizerHopfIdeal H e).identityComponent
    (by rw [HopfIdeal.lieSubalgebra_identityComponent])

end IdentityComponent

end IsSl2Triple
