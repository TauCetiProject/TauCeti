/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.FixedPoints.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.Algebra.Polynomial.Laurent.Smooth
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.RingTheory.Invariant.Coinvariant

/-!
# Smoothness of fixed-point closed subgroup schemes under tame finite group actions

Let `H` be a commutative Hopf algebra over a commutative ring `R`, representing an affine group
scheme `G = Spec H`, and let `Θ` be a finite group acting on `H` by Hopf-algebra automorphisms
(`ρ : Θ →* Aut H`). When `|Θ|` is invertible in `R` and `H` is smooth over `R`, **Edixhoven's
smoothness theorem** (`TauCeti.smooth_quotient_of_eq_iSup_span_range_sub`, formalizing Propositions
3.1 and 3.4 of Edixhoven 1992) shows that the fixed-point coordinate Hopf algebra `H ⧸ I_Θ` is
again smooth over `R`.

Contravariantly, the fixed-point subfunctor `G^Θ` of a smooth affine group scheme `G` over any
commutative ring `R` (in particular over a discrete valuation ring with no Henselian hypothesis, or
over a field of characteristic not dividing `|Θ|`) is represented by a **smooth** closed subgroup
scheme.

## Main declarations

* `TauCeti.CommHopfAlgCat.autToAlgEquiv`: the group homomorphism `Aut H →* (H ≃ₐ[R] H)`.
* `TauCeti.CommHopfAlgCat.formallySmooth_fixedPoints` and
  `TauCeti.CommHopfAlgCat.smoothCommHopfAlgProperty_fixedPoints`: formal smoothness and smoothness
  of `fixedPoints (fun θ ↦ (ρ θ).asIso.hom)` when `IsUnit (Nat.card Θ : R)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.smooth_fixedPoints`: the packaged existence statement for
  finite-type affine group schemes, producing the smooth quotient `H ⟶ H'` representing `Θ`-fixed
  points over every `R`-algebra.
* `TauCeti.CommHopfAlgCat.fixedPointsIsoOfEqOne` and
  `TauCeti.FiniteTypeCommHopfAlgCat.fixedPointsIsoOfEqOne`: for the trivial group action `ρ = 1`,
  the fixed-point group scheme is isomorphic to `H`.
* `TauCeti.CommHopfAlgCat.swapAction`, `TauCeti.CommHopfAlgCat.fixedPointsSwapActionIso`, and
  `TauCeti.CommHopfAlgCat.geometricallyConnected_fixedPoints_swapAction`: for the `ℤ/2`-action
  swapping the factors of `G × G`, the fixed subgroup scheme is the diagonal `G` (connected when
  `G` is).
* `TauCeti.CommHopfAlgCat.antipodeAction`,
  `TauCeti.CommHopfAlgCat.not_connectedSpace_primeSpectrum_fixedPoints_multiplicativeGroup`, and
  `TauCeti.CommHopfAlgCat.not_geometricallyConnected_fixedPoints_multiplicativeGroup`: for the
  inversion `ℤ/2`-action on `𝔾ₘ` with `2` invertible, the fixed subgroup scheme `μ₂` is smooth
  with `A`-points `{ u : Aˣ | u ^ 2 = 1 }`, yet is disconnected.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992),
  Propositions 3.1 and 3.4, pp. 293–295.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom
open CategoryTheory TensorProduct WithConv
open scoped LaurentPolynomial

namespace TauCeti

universe u v w w'

namespace CommHopfAlgCat

section Smooth

variable {R : Type u} [CommRing R]

/-- Viewing a Hopf-algebra automorphism `e : Aut H` as an `R`-algebra equivalence `H ≃ₐ[R] H` is a
group homomorphism: both `Aut H` and `H ≃ₐ[R] H` multiply by composition of maps on `H`
(`(e₁ * e₂) x = e₁ (e₂ x)`). -/
noncomputable def autToAlgEquiv (H : _root_.CommHopfAlgCat.{v} R) : Aut H →* (H ≃ₐ[R] H) where
  toFun e := (_root_.CommHopfAlgCat.ofIso e.asIso).toAlgEquiv
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

/-- `autToAlgEquiv H e` acts on elements by `e.asIso.hom.hom`. -/
@[simp]
theorem autToAlgEquiv_apply (H : _root_.CommHopfAlgCat.{v} R) (e : Aut H) (x : H) :
    autToAlgEquiv H e x = e.asIso.hom.hom x := by
  rw [autToAlgEquiv]
  rfl

/-- **Edixhoven's formal smoothness theorem for affine group schemes**: if a finite group `Θ` of
order invertible in `R` acts on a formally smooth commutative Hopf `R`-algebra `H`, then the
fixed-point coordinate Hopf algebra is formally smooth over `R`. -/
theorem formallySmooth_fixedPoints {H : _root_.CommHopfAlgCat.{v} R} [Algebra.FormallySmooth R H]
    {Θ : Type w} [Group Θ] [_root_.Finite Θ] (ρ : Θ →* Aut H)
    (hΘ : IsUnit (Nat.card Θ : R)) :
    Algebra.FormallySmooth R (fixedPoints fun θ ↦ (ρ θ).asIso.hom) :=
  formallySmooth_quotient_of_eq_iSup_span_range_sub ((autToAlgEquiv H).comp ρ)
    (fixedPointsHopfIdeal_toIdeal _) hΘ

/-- **Edixhoven's smoothness theorem for affine group schemes**: if a finite group `Θ` of order
invertible in `R` acts on a smooth commutative Hopf `R`-algebra `H`, then the fixed-point closed
subgroup scheme is smooth over `R`. -/
theorem smoothCommHopfAlgProperty_fixedPoints {H : _root_.CommHopfAlgCat.{v} R}
    (hH : smoothCommHopfAlgProperty R H) {Θ : Type w} [Group Θ] [_root_.Finite Θ]
    (ρ : Θ →* Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R (fixedPoints fun θ ↦ (ρ θ).asIso.hom) := by
  rw [smoothCommHopfAlgProperty_iff] at hH ⊢
  exact smooth_quotient_of_eq_iSup_span_range_sub ((autToAlgEquiv H).comp ρ)
    (fixedPointsHopfIdeal_toIdeal _) hΘ

/-- For the trivial group action `ρ = 1`, the fixed-point Hopf algebra is canonically isomorphic to
`H`. -/
noncomputable def fixedPointsIsoOfEqOne {H : _root_.CommHopfAlgCat.{v} R} {Θ : Type w} [Group Θ]
    {ρ : Θ →* Aut H} (hρ : ρ = 1) :
    fixedPoints (fun θ ↦ (ρ θ).asIso.hom) ≅ H :=
  fixedPointsIsoOfEqId fun θ ↦ by
    rw [hρ, MonoidHom.one_apply]
    rfl

end Smooth

section Involution

variable {R : Type u} [CommRing R]

/-- Package an involutive endomorphism `f : H ⟶ H` (`f ≫ f = 𝟙 H`) as an action of
`Multiplicative (ZMod 2)` on `H` sending the generator `ofAdd 1` to `f`. -/
noncomputable def involutionAction {H : _root_.CommHopfAlgCat.{v} R} (f : H ⟶ H)
    (hf : f ≫ f = 𝟙 H) : Multiplicative (ZMod 2) →* Aut H :=
  (zmodMonoidHomEquiv 2 (Aut H)).symm ⟨Aut.of ⟨f, f, hf, hf⟩, by
    rw [sq]
    exact Aut.ext (Iso.ext hf)⟩

/-- `ofAdd 0` acts as the identity morphism under `involutionAction`. -/
theorem involutionAction_ofAdd_zero {H : _root_.CommHopfAlgCat.{v} R} (f : H ⟶ H)
    (hf : f ≫ f = 𝟙 H) :
    (involutionAction f hf (.ofAdd 0)).asIso.hom = 𝟙 H := by
  rw [ofAdd_zero, map_one]
  rfl

/-- The generator `ofAdd 1` acts as `f` under `involutionAction`. -/
@[simp]
theorem involutionAction_ofAdd_one {H : _root_.CommHopfAlgCat.{v} R} (f : H ⟶ H)
    (hf : f ≫ f = 𝟙 H) :
    (involutionAction f hf (.ofAdd 1)).asIso.hom = f := by
  rw [involutionAction, zmodMonoidHomEquiv_symm_apply_ofAdd_one]

/-- Every element of `Multiplicative (ZMod 2)` acts either as `𝟙 H` or as `f`. -/
theorem involutionAction_hom_eq_id_or {H : _root_.CommHopfAlgCat.{v} R} (f : H ⟶ H)
    (hf : f ≫ f = 𝟙 H) (θ : Multiplicative (ZMod 2)) :
    (involutionAction f hf θ).asIso.hom = 𝟙 H ∨
      (involutionAction f hf θ).asIso.hom = f := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod 2, Multiplicative.ofAdd a = θ := ⟨θ.toAdd, rfl⟩
  have ha : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases ha a with rfl | rfl
  · exact .inl (involutionAction_ofAdd_zero f hf)
  · exact .inr (involutionAction_ofAdd_one f hf)

/-- On `A`-points, the fixed points of `involutionAction f hf` are the points fixed by `f`. -/
theorem range_mapDomain_mkFixedPoints_involutionAction {H : _root_.CommHopfAlgCat.{v} R}
    (f : H ⟶ H) (hf : f ≫ f = 𝟙 H) (A : Type w') [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A)
        (mkFixedPoints fun θ ↦ (involutionAction f hf θ).asIso.hom).hom) =
      {g | BialgHom.mapDomain (A := A) f.hom g = g} := by
  rw [range_mapDomain_mkFixedPoints]
  ext g
  refine ⟨fun hg ↦ ?_, fun hg θ ↦ ?_⟩
  · have h1 := hg (.ofAdd 1)
    rwa [involutionAction_ofAdd_one] at h1
  · rcases involutionAction_hom_eq_id_or f hf θ with hθ | hθ
    · rw [hθ]
      exact DFunLike.congr_fun BialgHom.mapDomain_id g
    · rwa [hθ]

/-- The `ℤ/2`-action on `H ⊗[R] H` swapping the two tensor factors. -/
noncomputable def swapAction (H : _root_.CommHopfAlgCat.{v} R) :
    Multiplicative (ZMod 2) →* Aut (_root_.CommHopfAlgCat.of R (H ⊗[R] H)) :=
  involutionAction (swapEnd H) (swapEnd_comp_swapEnd H)

/-- The fixed-point Hopf algebra of the factor-swap `ℤ/2`-action on `H ⊗[R] H` is canonically
isomorphic to `H` (the diagonal `G ↪ G × G`). -/
noncomputable def fixedPointsSwapActionIso (H : _root_.CommHopfAlgCat.{v} R) :
    fixedPoints (fun θ ↦ (swapAction H θ).asIso.hom) ≅ H :=
  fixedPointsOfSwapIso H ⟨.ofAdd 1, involutionAction_ofAdd_one _ _⟩
    (involutionAction_hom_eq_id_or _ _)

/-- Over a field `k`, if `H` is geometrically connected (for instance `𝔾ₘ`), then the fixed-point
subgroup scheme of the factor-swap `ℤ/2`-action on `H ⊗[k] H` is also geometrically connected. -/
theorem geometricallyConnected_fixedPoints_swapAction {k : Type u} [Field k]
    {H : _root_.CommHopfAlgCat.{v} k} (hH : geometricallyConnectedCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty k
      (fixedPoints fun θ ↦ (swapAction H θ).asIso.hom) :=
  (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso (fixedPointsSwapActionIso H).symm hH

end Involution

section Antipode

variable {R : Type u} [CommRing R]

/-- The antipode endomorphism of a commutative and cocommutative Hopf algebra in
`CommHopfAlgCat R`, representing inversion `g ↦ g⁻¹` on a commutative affine group scheme. -/
noncomputable def antipodeEnd (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] : H ⟶ H :=
  _root_.CommHopfAlgCat.ofHom (HopfAlgebra.antipodeBialgHom (R := R) (A := H))

/-- Underlying bialgebra morphism of `antipodeEnd H`. -/
@[simp]
theorem antipodeEnd_hom (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    (antipodeEnd H).hom = HopfAlgebra.antipodeBialgHom (R := R) (A := H) :=
  _root_.CommHopfAlgCat.hom_ofHom _

/-- The antipode endomorphism of a commutative and cocommutative Hopf algebra is involutive. -/
@[simp]
theorem antipodeEnd_comp_antipodeEnd (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    antipodeEnd H ≫ antipodeEnd H = 𝟙 H := by
  apply _root_.CommHopfAlgCat.hom_ext
  ext x
  simp [HopfAlgebra.antipode_antipode]

/-- The `ℤ/2`-action by group-scheme inversion (`g ↦ g⁻¹`) on any commutative and cocommutative
Hopf algebra `H`. -/
noncomputable def antipodeAction (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    Multiplicative (ZMod 2) →* Aut H :=
  involutionAction (antipodeEnd H) (antipodeEnd_comp_antipodeEnd H)

/-- On `A`-points of a commutative affine group scheme `Spec H`, the fixed points of
`antipodeAction H` are the 2-torsion points `{ g | g⁻¹ = g }`. -/
theorem range_mapDomain_mkFixedPoints_antipodeAction (H : _root_.CommHopfAlgCat.{v} R)
    [Coalgebra.IsCocomm R H] (A : Type w') [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A)
        (mkFixedPoints fun θ ↦ (antipodeAction H θ).asIso.hom).hom) =
      {g | g⁻¹ = g} := by
  rw [antipodeAction, range_mapDomain_mkFixedPoints_involutionAction]
  ext g
  refine ⟨fun (hg : BialgHom.mapDomain (A := A) (antipodeEnd H).hom g = g) ↦ ?_,
    fun (hg : g⁻¹ = g) ↦ ?_⟩ <;>
  · apply ofConv_injective
    ext x
    have hx := congrArg (fun m : WithConv (H →ₐ[R] A) ↦ m.ofConv x) hg
    simpa only [WithConv.algHom_inv_apply, BialgHom.mapDomain_apply_apply, antipodeEnd_hom,
      HopfAlgebra.antipodeBialgHom_apply] using hx

/-- When `2` is invertible in `R`, the fixed-point closed subgroup scheme of `𝔾ₘ` under inversion
is smooth over `R`. -/
theorem smoothCommHopfAlgProperty_fixedPoints_multiplicativeGroup (h2 : IsUnit (2 : R)) :
    smoothCommHopfAlgProperty R
      (fixedPoints fun θ ↦
        (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom) := by
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2))).trans
      (Nat.card_zmod 2)
  exact smoothCommHopfAlgProperty_fixedPoints
    ((smoothCommHopfAlgProperty_iff _).mpr (inferInstanceAs (Algebra.Smooth R R[T;T⁻¹])))
    (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹])) (by rwa [hcard, Nat.cast_two])

/-- Under `MultiplicativeGroup.pointsMulEquiv`, the `A`-points of `𝔾ₘ` fixed by inversion are
the square roots of unity `{ u : Aˣ | u ^ 2 = 1 }`. -/
theorem image_pointsMulEquiv_fixedPoints_multiplicativeGroup (A : Type w') [CommRing A]
    [Algebra R A] :
    MultiplicativeGroup.pointsMulEquiv (R := R) (A := A) ''
        Set.range (BialgHom.mapDomain (A := A)
          (mkFixedPoints fun θ ↦
            (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom).hom) =
      {u : Aˣ | u ^ 2 = 1} := by
  rw [range_mapDomain_mkFixedPoints_antipodeAction]
  ext u
  refine ⟨?_, fun (hu : u ^ 2 = 1) ↦ ?_⟩
  · rintro ⟨g, hg : g⁻¹ = g, rfl⟩
    change MultiplicativeGroup.pointsMulEquiv g ^ 2 = 1
    rw [sq, ← inv_eq_iff_mul_eq_one, ← map_inv, hg]
  · refine ⟨(MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm u, ?_,
      (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).apply_symm_apply u⟩
    change ((MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm u)⁻¹ = _
    apply (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).injective
    rw [map_inv, MulEquiv.apply_symm_apply, inv_eq_iff_mul_eq_one, ← sq]
    exact hu

private theorem exists_nontrivial_idempotent_fixedPoints_multiplicativeGroup [Nontrivial R]
    (h2 : IsUnit (2 : R)) :
    ∃ e : fixedPoints (fun θ ↦
        (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom),
      IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  set G := _root_.CommHopfAlgCat.of R R[T;T⁻¹]
  set f : Multiplicative (ZMod 2) → (G ⟶ G) := fun θ ↦ (antipodeAction G θ).asIso.hom
  set q : G ⟶ fixedPoints f := mkFixedPoints f
  let t : fixedPoints f := q.hom (LaurentPolynomial.T 1)
  have ht_inv : q.hom (LaurentPolynomial.T (-1)) = t := by
    have hcomp := congrArg (fun m : G ⟶ fixedPoints f ↦ m.hom (LaurentPolynomial.T 1))
      (comp_mkFixedPoints f (.ofAdd 1))
    rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at hcomp
    have hant : (f (.ofAdd 1)).hom (LaurentPolynomial.T 1) = LaurentPolynomial.T (-1) := by
      dsimp only [f, antipodeAction]
      rw [involutionAction_ofAdd_one, antipodeEnd_hom, HopfAlgebra.antipodeBialgHom_apply]
      exact LaurentPolynomial.antipode_T 1
    rwa [hant] at hcomp
  have ht_sq : t * t = 1 := by
    calc t * t = q.hom (LaurentPolynomial.T (-1)) * q.hom (LaurentPolynomial.T 1) := by
          rw [ht_inv]
      _ = q.hom (LaurentPolynomial.T (-1 + 1)) := by
          rw [← map_mul, ← LaurentPolynomial.T_add]
      _ = 1 := by rw [neg_add_cancel, LaurentPolynomial.T_zero, map_one]
  let c : R := ((h2.unit⁻¹ : Rˣ) : R)
  have hc2 : c * 2 = 1 := by
    rw [← h2.unit_spec, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have heval (u : Rˣ) (hu : u ^ 2 = 1) : ∃ φ : (fixedPoints f : Type u) →ₐ[R] R,
      φ t = (u : R) := by
    let g : WithConv (R[T;T⁻¹] →ₐ[R] R) :=
      (MultiplicativeGroup.pointsMulEquiv (R := R) (A := R)).symm u
    have hg : g ∈ Set.range (BialgHom.mapDomain (A := R) q.hom) := by
      rw [range_mapDomain_mkFixedPoints_antipodeAction]
      change g⁻¹ = g
      apply (MultiplicativeGroup.pointsMulEquiv (R := R) (A := R)).injective
      rw [map_inv, MulEquiv.apply_symm_apply, inv_eq_iff_mul_eq_one, ← sq]
      exact hu
    obtain ⟨p, hp⟩ := hg
    refine ⟨p.ofConv, ?_⟩
    have hpT := congrArg
      (fun m : WithConv (R[T;T⁻¹] →ₐ[R] R) ↦ m.ofConv (LaurentPolynomial.T 1)) hp
    rw [BialgHom.mapDomain_apply_apply] at hpT
    exact hpT.trans (by
      dsimp only [g]
      rw [MultiplicativeGroup.pointsMulEquiv_symm_apply]
      exact laurentEval_T_one u)
  rcases heval 1 (one_pow 2) with ⟨φ₁, hφ₁⟩
  rcases heval (-1) (by simp) with ⟨φ₂, hφ₂⟩
  refine ⟨c • (1 + t), ?_, fun he0 ↦ ?_, fun he1 ↦ ?_⟩
  · change c • (1 + t) * (c • (1 + t)) = c • (1 + t)
    have h1t : (1 + t) * (1 + t) = (2 : R) • (1 + t) := by
      rw [Algebra.smul_def, map_ofNat]
      calc (1 + t) * (1 + t) = 1 + t + t + t * t := by ring
        _ = 1 + t + t + 1 := by rw [ht_sq]
        _ = 2 * (1 + t) := by ring
    rw [smul_mul_smul_comm, h1t, ← mul_smul, mul_assoc, hc2, mul_one]
  · have h1 := congrArg φ₁ he0
    rw [map_zero, show φ₁ (c • (1 + t)) = c * (1 + φ₁ t) by simp [Algebra.smul_def], hφ₁,
      Units.val_one, one_add_one_eq_two, hc2] at h1
    exact one_ne_zero h1
  · have h2' := congrArg φ₂ he1
    rw [map_one, show φ₂ (c • (1 + t)) = c * (1 + φ₂ t) by simp [Algebra.smul_def], hφ₂,
      Units.val_neg, Units.val_one, add_neg_cancel, mul_zero] at h2'
    exact zero_ne_one h2'

/-- Over a nontrivial commutative ring `R` in which `2` is invertible, the fixed-point coordinate
ring of `𝔾ₘ` under inversion contains the nontrivial idempotent `2⁻¹ (1 + T)` and therefore has
disconnected prime spectrum. -/
theorem not_connectedSpace_primeSpectrum_fixedPoints_multiplicativeGroup [Nontrivial R]
    (h2 : IsUnit (2 : R)) :
    ¬ ConnectedSpace (PrimeSpectrum
        (fixedPoints fun θ ↦
          (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom)) := by
  intro hconn
  obtain ⟨e, he, he0, he1⟩ := exists_nontrivial_idempotent_fixedPoints_multiplicativeGroup h2
  exact he.eq_zero_or_eq_one_of_preconnectedSpace.elim he0 he1

/-- Over any field `k` of characteristic not `2`, the fixed-point closed subgroup scheme of `𝔾ₘ`
under inversion (`μ₂`) is smooth (`smoothCommHopfAlgProperty_fixedPoints_multiplicativeGroup`)
but **not** geometrically connected. -/
theorem not_geometricallyConnected_fixedPoints_multiplicativeGroup {k : Type u} [Field k]
    (h2 : (2 : k) ≠ 0) :
    ¬ geometricallyConnectedCommHopfAlgProperty k
        (fixedPoints fun θ ↦
          (antipodeAction (_root_.CommHopfAlgCat.of k k[T;T⁻¹]) θ).asIso.hom) :=
  fun hconn ↦
    not_connectedSpace_primeSpectrum_fixedPoints_multiplicativeGroup h2.isUnit
      (hconn.connectedSpace k _)

end Antipode

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [CommRing k]

/-- Viewing an automorphism `e : Aut H` in `FiniteTypeCommHopfAlgCat k` as a `k`-algebra
equivalence `H.obj ≃ₐ[k] H.obj` is a group homomorphism. -/
noncomputable def autToAlgEquiv (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    Aut H →* (H.obj ≃ₐ[k] H.obj) where
  toFun e := AlgEquiv.ofAlgHom (toBialgHom e.asIso.hom).toAlgHom
    (toBialgHom e.asIso.inv).toAlgHom
    (congrArg BialgHom.toAlgHom (congrArg toBialgHom e.asIso.inv_hom_id))
    (congrArg BialgHom.toAlgHom (congrArg toBialgHom e.asIso.hom_inv_id))
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

/-- `autToAlgEquiv H e` acts on elements by `e.asIso.hom.hom.hom`. -/
@[simp]
theorem autToAlgEquiv_apply (H : FiniteTypeCommHopfAlgCat.{u, v} k) (e : Aut H) (x : H.obj) :
    autToAlgEquiv H e x = e.asIso.hom.hom.hom x := by
  rw [autToAlgEquiv]
  rfl

/-- **Edixhoven's smoothness theorem** in `FiniteTypeCommHopfAlgCat`: if a finite group `Θ` of
invertible order acts on a smooth finite-type commutative Hopf `k`-algebra `H`, then its
fixed-point closed subgroup scheme is smooth over `k`. -/
theorem smoothCommHopfAlgProperty_fixedPoints (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) {Θ : Type w} [Group Θ] [_root_.Finite Θ]
    (ρ : Θ →* Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    smoothCommHopfAlgProperty k (fixedPoints fun θ ↦ (ρ θ).asIso.hom).obj := by
  rw [smoothCommHopfAlgProperty_iff] at hH ⊢
  have hI : (fixedPointsHopfIdeal (H := H) fun θ ↦ (ρ θ).asIso.hom).toIdeal =
      ⨆ θ : Θ, Ideal.span (Set.range fun x : H.obj ↦
        ((autToAlgEquiv H).comp ρ) θ x - x) := by
    simpa only [MonoidHom.comp_apply, autToAlgEquiv_apply] using
      CommHopfAlgCat.fixedPointsHopfIdeal_toIdeal (H := H.obj) fun θ ↦ (ρ θ).asIso.hom.hom
  exact smooth_quotient_of_eq_iSup_span_range_sub ((autToAlgEquiv H).comp ρ) hI hΘ

/-- **Fixed-point closed subgroup scheme of a smooth affine group under a tame finite group.**

Let `H` be a smooth finite-type commutative Hopf `k`-algebra over any commutative ring `k`, and let
`Θ` be a finite group of order invertible in `k` acting on `H` by group-scheme automorphisms. Then
there is a surjective Hopf-algebra morphism `f : H ⟶ H'` onto a smooth finite-type commutative Hopf
`k`-algebra `H'` whose `R`-points over every commutative `k`-algebra `R` are precisely the
`Θ`-fixed `R`-points of `H` (Edixhoven 1992, Propositions 3.1 and 3.4). -/
theorem smooth_fixedPoints (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) (Θ : Type w) [Group Θ] [_root_.Finite Θ]
    (ρ : Θ →* Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    ∃ (H' : FiniteTypeCommHopfAlgCat.{u, v} k) (f : H ⟶ H'),
      smoothCommHopfAlgProperty k H'.obj ∧ Function.Surjective f.hom.hom ∧
      ∀ (R : Type w') [CommRing R] [Algebra k R],
        Set.range (BialgHom.mapDomain (A := R) (f.hom.hom : (H : Type v) →ₐc[k] H')) =
          {g | ∀ θ : Θ,
            BialgHom.mapDomain (A := R)
              ((ρ θ).asIso.hom.hom.hom : (H : Type v) →ₐc[k] H) g = g} :=
  ⟨fixedPoints fun θ ↦ (ρ θ).asIso.hom, mkFixedPoints fun θ ↦ (ρ θ).asIso.hom,
    smoothCommHopfAlgProperty_fixedPoints H hH ρ hΘ,
    mkFixedPoints_surjective fun θ ↦ (ρ θ).asIso.hom,
    fun R _ _ ↦ range_mapDomain_mkFixedPoints (fun θ ↦ (ρ θ).asIso.hom) R⟩

/-- For the trivial group action `ρ = 1`, the finite-type fixed-point Hopf algebra is canonically
isomorphic to `H`. -/
noncomputable def fixedPointsIsoOfEqOne (H : FiniteTypeCommHopfAlgCat.{u, v} k) {Θ : Type w}
    [Group Θ] {ρ : Θ →* Aut H} (hρ : ρ = 1) :
    fixedPoints (fun θ ↦ (ρ θ).asIso.hom) ≅ H :=
  fixedPointsIsoOfEqId fun θ ↦ by
    rw [hρ, MonoidHom.one_apply]
    rfl

end FiniteTypeCommHopfAlgCat

end TauCeti
