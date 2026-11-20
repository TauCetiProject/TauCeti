/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.CongruenceSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import TauCeti.Algebra.AlgebraicGroup.Trivial
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The action of formal coordinate changes on arcs

Let `H` be a bialgebra over a commutative semiring `k` and `R` a commutative `k`-algebra. The
arcs of `G = Spec H` over `R` are the points `G(R⟦X⟧) = WithConv (H →ₐ[k] R⟦X⟧)`, the positive
loop group `L⁺G(R)` when `H` is a commutative Hopf algebra. A formal coordinate
`φ ∈ TauCeti.FormalCoordinate R` gives the substitution automorphism `σ_φ : f ↦ f (φ)` of
`R⟦X⟧`, and these compose contravariantly: `σ_φ ∘ σ_ψ = σ_(ψ ∘ φ)`. Substituting the inverse
coordinate turns this right action into a left one,

  `ρ_φ (g) = σ_(φ⁻¹) ∘ g`,

so that `ρ_(φ ∘ ψ) = ρ_φ ∘ ρ_ψ` and `ρ_X = id`. Since `ρ_φ` is post-composition with an algebra
automorphism of the coefficients, it is multiplicative for the convolution product. This file
records `ρ` as a `MulDistribMulAction` of `FormalCoordinate R` on `G(R⟦X⟧)`; Mathlib's
`MulDistribMulAction.toMulAut` then makes each `ρ_φ` a group automorphism, and the
semidirect product `G(R⟦X⟧) ⋊ FormalCoordinate R` has the multiplication
`(g, φ) (h, ψ) = (g ρ_φ (h), φ ∘ ψ)`.

The action is natural in the coefficient algebra `R`, along `PowerSeries.mapAlgHom f` on arcs
and `TauCeti.FormalCoordinate.map f` on coordinates, and in the bialgebra `H`, along
pre-composition with bialgebra maps. Substitution of a series of zero constant coefficient
preserves divisibility by `X ^ N`, so `ρ_φ` maps each congruence subgroup
`K_N(R) = ker (G(R⟦X⟧) → G(R⟦X⟧ ⧸ (X ^ N)))` onto itself. Substitution is `R`-linear, so the
constant arcs, the images of `G(R)`, are fixed.

For the additive group `ρ_φ` is `f ↦ f (φ⁻¹)` on `𝔾ₐ(R⟦X⟧) = R⟦X⟧`, and for the
multiplicative group it is the same substitution on units. For instance the homothety
`φ = a X` sends the point `1 + X` of `𝔾ₘ` to `1 + a⁻¹ X`.

## Main declarations

* `TauCeti.FormalCoordinate.instMulDistribMulActionWithConv`: the action
  `φ • g = σ_(φ⁻¹) ∘ g` of formal coordinates on arcs, with `TauCeti.FormalCoordinate.smul_def`
  and `TauCeti.FormalCoordinate.ofConv_smul_apply`.
* `TauCeti.FormalCoordinate.mapValue_mapAlgHom_smul`: naturality in the coefficient algebra.
* `TauCeti.FormalCoordinate.mapDomain_smul`: naturality in the bialgebra.
* `TauCeti.FormalCoordinate.smul_mem_congruenceSubgroup_span_X_pow_iff` and
  `TauCeti.FormalCoordinate.smul_congruenceSubgroup_span_X_pow`: the action maps each
  congruence subgroup `K_N(R)` onto itself.
* `TauCeti.FormalCoordinate.smul_toConv_toAlgHom_comp`: constant arcs are fixed.
* `TauCeti.FormalCoordinate.toAdd_gaPointsMulEquiv_smul` and
  `TauCeti.FormalCoordinate.pointsMulEquiv_smul`: the action for `𝔾ₐ` and `𝔾ₘ`.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge University Press (2007),
  §1.3.1 for the loop group and its congruence subgroups, §§3.5.3–3.5.4 for the group of
  coordinate changes.
-/

public section

open PowerSeries WithConv
open scoped Pointwise LaurentPolynomial

namespace TauCeti

namespace FormalCoordinate

variable {k H R : Type*} [CommSemiring k] [CommRing R] [Algebra k R]

section Bialgebra

variable [Semiring H] [Bialgebra k H]

/-- A formal coordinate `φ` acts on the arcs `G(R⟦X⟧)` by post-composition with the substitution
automorphism `σ_(φ⁻¹) : f ↦ f (φ⁻¹)` of the coefficients. -/
noncomputable instance instSMulWithConv : SMul (FormalCoordinate R) (WithConv (H →ₐ[k] R⟦X⟧)) where
  smul φ g := AlgHom.mapValue (φ⁻¹.substAlgEquiv.toAlgHom.restrictScalars k) g

/-- The action of `φ` on arcs is `AlgHom.mapValue` of the substitution automorphism of `φ⁻¹`. -/
theorem smul_def (φ : FormalCoordinate R) (g : WithConv (H →ₐ[k] R⟦X⟧)) :
    φ • g = AlgHom.mapValue (φ⁻¹.substAlgEquiv.toAlgHom.restrictScalars k) g :=
  (rfl)

/-- The arc `φ • g` takes the value `g (h) (φ⁻¹)` at `h`. -/
@[simp]
theorem ofConv_smul_apply (φ : FormalCoordinate R) (g : WithConv (H →ₐ[k] R⟦X⟧)) (h : H) :
    (φ • g).ofConv h = (g.ofConv h).subst φ⁻¹.toPowerSeries := by
  simp [smul_def]

/-- Formal coordinates act on the arcs `G(R⟦X⟧)` on the left by monoid automorphisms:
`ρ_φ (g) = σ_(φ⁻¹) ∘ g` satisfies `ρ_(φ ∘ ψ) = ρ_φ ∘ ρ_ψ` because substitution reverses
composition. -/
noncomputable instance instMulDistribMulActionWithConv :
    MulDistribMulAction (FormalCoordinate R) (WithConv (H →ₐ[k] R⟦X⟧)) where
  one_smul g := ofConv_injective <| _root_.AlgHom.ext fun h ↦ by simp
  mul_smul φ ψ g := ofConv_injective <| _root_.AlgHom.ext fun h ↦ by
    rw [ofConv_smul_apply, ofConv_smul_apply, ofConv_smul_apply, subst_subst, mul_inv_rev]
  smul_mul φ g g' := map_mul (AlgHom.mapValue _) g g'
  smul_one φ := map_one (AlgHom.mapValue _)

/-- The action on arcs is natural in the coefficient algebra: changing coefficients along
`f : R →ₐ[k] S` carries `φ • g` to `map f φ • g'`, where `g'` is the base-changed arc. -/
theorem mapValue_mapAlgHom_smul {S : Type*} [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
    (φ : FormalCoordinate R) (g : WithConv (H →ₐ[k] R⟦X⟧)) :
    AlgHom.mapValue (mapAlgHom f) (φ • g) =
      map (f : R →+* S) φ • AlgHom.mapValue (mapAlgHom f) g := by
  refine ofConv_injective <| _root_.AlgHom.ext fun h ↦ ?_
  simp only [AlgHom.mapValue_apply, ofConv_toConv, _root_.AlgHom.comp_apply, mapAlgHom_apply,
    ofConv_smul_apply, ← map_inv, toPowerSeries_map]
  -- `PowerSeries.map` is by definition `MvPowerSeries.map` over `Unit`, the form in which
  -- Mathlib states `PowerSeries.map_subst`
  exact map_subst φ⁻¹.hasSubst _

/-- The action on arcs is natural in the bialgebra: pre-composition with a bialgebra map
commutes with every `ρ_φ`. -/
theorem mapDomain_smul {H' : Type*} [Semiring H'] [Bialgebra k H'] (ψ : H' →ₐc[k] H)
    (φ : FormalCoordinate R) (g : WithConv (H →ₐ[k] R⟦X⟧)) :
    BialgHom.mapDomain ψ (φ • g) = φ • BialgHom.mapDomain ψ g := by
  rw [smul_def, smul_def, ← MonoidHom.comp_apply, BialgHom.mapValue_mapDomain,
    MonoidHom.comp_apply]

/-- Coordinate changes fix the constant arcs, the images `R → R⟦X⟧ ∘ x` of the points
`x ∈ G(R)` under the inclusion of constant series. The constant arc is written as
`toConv ((IsScalarTower.toAlgHom k R R⟦X⟧).comp x)`, the simp-normal form of
`AlgHom.mapValue (IsScalarTower.toAlgHom k R R⟦X⟧) (toConv x)`. -/
@[simp]
theorem smul_toConv_toAlgHom_comp (φ : FormalCoordinate R) (x : H →ₐ[k] R) :
    φ • toConv ((IsScalarTower.toAlgHom k R R⟦X⟧).comp x) =
      toConv ((IsScalarTower.toAlgHom k R R⟦X⟧).comp x) := by
  refine ofConv_injective <| _root_.AlgHom.ext fun h ↦ ?_
  simp only [ofConv_smul_apply, _root_.AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    ← substAlgEquiv_apply, AlgEquiv.commutes]

end Bialgebra

section HopfAlgebra

variable [Semiring H] [HopfAlgebra k H]

/-- Coordinate changes preserve the congruence subgroups `K_N(R)` of arcs trivial modulo
`X ^ N`. -/
theorem smul_mem_congruenceSubgroup_span_X_pow {N : ℕ} (φ : FormalCoordinate R)
    {g : WithConv (H →ₐ[k] R⟦X⟧)}
    (hg : g ∈ HopfAlgebra.congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N})) :
    φ • g ∈ HopfAlgebra.congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}) := by
  refine HopfAlgebra.congruenceSubgroup_le_comap_mapValue _ (fun f hf ↦ ?_) hg
  rw [Ideal.mem_span_singleton] at hf
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  simpa using X_pow_dvd_subst φ⁻¹.constantCoeff_toPowerSeries hf

/-- An arc lies in the congruence subgroup `K_N(R)` exactly when its image under a coordinate
change does. -/
@[simp]
theorem smul_mem_congruenceSubgroup_span_X_pow_iff {N : ℕ} (φ : FormalCoordinate R)
    {g : WithConv (H →ₐ[k] R⟦X⟧)} :
    φ • g ∈ HopfAlgebra.congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}) ↔
      g ∈ HopfAlgebra.congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}) :=
  ⟨fun hg ↦ by simpa using smul_mem_congruenceSubgroup_span_X_pow φ⁻¹ hg,
    smul_mem_congruenceSubgroup_span_X_pow φ⟩

/-- Each coordinate change maps the congruence subgroup `K_N(R)` onto itself. -/
@[simp]
theorem smul_congruenceSubgroup_span_X_pow (N : ℕ) (φ : FormalCoordinate R) :
    φ • HopfAlgebra.congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}) =
      HopfAlgebra.congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, smul_mem_congruenceSubgroup_span_X_pow_iff]

/-- In the semidirect product of the arcs by the coordinate changes, built from the action by
`MulDistribMulAction.toMulAut`, multiplication is `(g, φ) (h, ψ) = (g ρ_φ (h), φ ∘ ψ)`. -/
example (g h : WithConv (H →ₐ[k] R⟦X⟧)) (φ ψ : FormalCoordinate R) :
    (⟨g, φ⟩ * ⟨h, ψ⟩ :
        WithConv (H →ₐ[k] R⟦X⟧) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) =
      ⟨g * φ • h, φ * ψ⟩ := by
  ext <;> simp

end HopfAlgebra

section Examples

/-- For the trivial group `Spec k` the action on arcs is trivial. -/
example (φ : FormalCoordinate R) (g : WithConv (k →ₐ[k] R⟦X⟧)) : φ • g = g :=
  (WithConv.convPoint_eq_one _).trans (WithConv.convPoint_eq_one g).symm

/-- For the additive group, `ρ_φ` is the substitution `f ↦ f (φ⁻¹)` on `𝔾ₐ(R⟦X⟧) = R⟦X⟧`. -/
theorem toAdd_gaPointsMulEquiv_smul (φ : FormalCoordinate R)
    (g : WithConv (SymmetricAlgebra k k →ₐ[k] R⟦X⟧)) :
    Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (φ • g)) =
      (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g)).subst φ⁻¹.toPowerSeries := by
  simp

/-- For the multiplicative group, `ρ_φ` is the substitution `u ↦ u (φ⁻¹)` on
`𝔾ₘ(R⟦X⟧) = R⟦X⟧ˣ`. -/
theorem pointsMulEquiv_smul (φ : FormalCoordinate R) (g : WithConv (k[T;T⁻¹] →ₐ[k] R⟦X⟧)) :
    (MultiplicativeGroup.pointsMulEquiv (φ • g) : R⟦X⟧) =
      (MultiplicativeGroup.pointsMulEquiv g : R⟦X⟧).subst φ⁻¹.toPowerSeries := by
  rw [smul_def, MultiplicativeGroup.pointsMulEquiv_mapValue, Units.coe_map]
  simp

/-- For the multiplicative group, the homothety `X ↦ a X` sends the point `1 + X` to
`1 + a⁻¹ X`. -/
example (a : Rˣ) (u : R⟦X⟧ˣ) (hu : (u : R⟦X⟧) = 1 + X) :
    (MultiplicativeGroup.pointsMulEquiv
        (homothety a • (MultiplicativeGroup.pointsMulEquiv (R := k)).symm u) : R⟦X⟧) =
      1 + (↑a⁻¹ : R) • X := by
  rw [pointsMulEquiv_smul, MulEquiv.apply_symm_apply, hu, ← map_inv, toPowerSeries_homothety,
    subst_add (HasSubst.smul_X' _), subst_X (HasSubst.smul_X' _), ← map_one (C (R := R)),
    subst_C]
  simp

end Examples

end FormalCoordinate

end TauCeti
