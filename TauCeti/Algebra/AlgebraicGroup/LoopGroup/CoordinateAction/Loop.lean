/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.CoordinateAction.Basic
public import TauCeti.RingTheory.LaurentSeries.Substitution.Coordinate
import TauCeti.Algebra.AlgebraicGroup.Trivial

/-!
# The action of formal coordinate changes on loops

Let `H` be an algebra over a commutative semiring `k` and `R` a commutative `k`-algebra, and give
`R⸨X⸩` its coefficientwise `k`-algebra structure, as in `TauCeti.HopfAlgebra.loopGroup`. A formal
coordinate `φ ∈ TauCeti.FormalCoordinate R` gives the substitution automorphism `σ_φ : f ↦ f (φ)`
of `R⸨X⸩` (`TauCeti.LaurentSeries.substAlgEquiv`), and these compose contravariantly. As for arcs
(`TauCeti.FormalCoordinate.instMulActionWithConv`), substituting the inverse coordinate turns this
right action into a left one on the convolution points `WithConv (H →ₐ[k] R⸨X⸩)`,

  `ρ_φ (g) = σ_(φ⁻¹) ∘ g`.

When `H` is a bialgebra, the convolution points form a monoid and `ρ` is a `MulDistribMulAction`;
for a Hopf algebra Mathlib's `MulDistribMulAction.toMulAut` then makes each `ρ_φ` a group
automorphism, and the semidirect product `WithConv (H →ₐ[k] R⸨X⸩) ⋊ FormalCoordinate R` has the
multiplication `(g, φ) (h, ψ) = (g ρ_φ (h), φ ∘ ψ)`. When `H` is a commutative Hopf algebra, the
convolution points are the loops `G(R⸨X⸩)` of `G = Spec H`, the loop group `LG(R)`.

The Laurent series `R⸨X⸩` carry several `k`-algebra structures that agree only propositionally;
the action uses the coefficientwise one, `HahnSeries.instAlgebra`, which callers select with
`attribute [local instance 1100] HahnSeries.instAlgebra`, as this file does.

The action is natural in the coefficient algebra `R`, along `HahnSeries.mapAlgHom f` on loops and
`TauCeti.FormalCoordinate.map f` on coordinates, and in the bialgebra `H`, along pre-composition
with bialgebra maps. The inclusion `R⟦X⟧ → R⸨X⸩` carries the action on arcs to the action on
loops, so `ρ_φ` maps the positive loops `L⁺G(R)` onto themselves, and `ρ_φ` fixes the constant
loops, the images of `G(R)`. The pieces of pole-bounded loops are preserved as well, in
`TauCeti.Algebra.AlgebraicGroup.LoopGroup.PoleBounded.CoordinateAction`.

For the additive group `ρ_φ` is `f ↦ f (φ⁻¹)` on `𝔾ₐ(R⸨X⸩) = R⸨X⸩`. For the multiplicative group
it is the same substitution on units, and the homothety `φ = a X` sends the loop `X ^ n` to
`a ^ (-n) X ^ n`, so it moves `X ^ n` exactly when `a ^ n ≠ 1`.

## Main declarations

* `TauCeti.LaurentSeries.instMulActionWithConv`: the action `φ • g = σ_(φ⁻¹) ∘ g` of formal
  coordinates on convolution points, with `TauCeti.LaurentSeries.ofConv_smul_apply`.
* `TauCeti.LaurentSeries.instMulDistribMulActionWithConv`: for a bialgebra the action is by
  monoid automorphisms, with `TauCeti.LaurentSeries.smul_def`.
* `TauCeti.LaurentSeries.mapValue_mapAlgHom_smul`: naturality in the coefficient algebra.
* `TauCeti.LaurentSeries.mapDomain_smul`: naturality in the bialgebra.
* `TauCeti.LaurentSeries.mapValue_ofPowerSeriesAlg_smul`: the inclusion of arcs into loops is
  equivariant, and `TauCeti.LaurentSeries.smul_mrange_mapValue_ofPowerSeriesAlg`: the action maps
  the image of the arcs, the positive loops for a commutative Hopf algebra, onto itself.
* `TauCeti.LaurentSeries.smul_toConv_toAlgHom_comp`: constant loops are fixed.
* `TauCeti.LaurentSeries.toAdd_gaPointsMulEquiv_smul` and
  `TauCeti.LaurentSeries.pointsMulEquiv_smul`: the action for `𝔾ₐ` and `𝔾ₘ`;
  `TauCeti.LaurentSeries.pointsMulEquiv_homothety_smul_pointsMulEquiv_symm_unitX_zpow`: the
  homothety `a X` sends the loop `X ^ n` of `𝔾ₘ` to `a ^ (-n) X ^ n`, and
  `TauCeti.LaurentSeries.homothety_smul_pointsMulEquiv_symm_unitX_zpow_eq_iff_zpow_eq_one`: the
  homothety `a X` fixes the loop `X ^ n` of `𝔾ₘ` exactly when `a ^ n = 1`.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge University Press (2007),
  §1.3.1 for the loop group, §§3.5.3–3.5.4 for the group of coordinate changes.
-/

public section

open HahnSeries WithConv
open scoped Pointwise LaurentSeries LaurentPolynomial PowerSeries

-- The coefficientwise `k`-algebra structure on Laurent series, as in `CommAlgCat.laurentSeries`.
attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.LaurentSeries

variable {k H R : Type*} [CommSemiring k] [CommRing R] [Algebra k R]

section Algebra

variable [Semiring H] [Algebra k H]

/-- A formal coordinate `φ` acts on the convolution points `WithConv (H →ₐ[k] R⸨X⸩)` by
post-composition with the substitution automorphism `σ_(φ⁻¹) : f ↦ f (φ⁻¹)` of the coefficients. -/
noncomputable instance instSMulWithConv :
    SMul (FormalCoordinate R) (WithConv (H →ₐ[k] R⸨X⸩)) where
  smul φ g := toConv ((substAlgEquivRestrictScalars k φ⁻¹).toAlgHom.comp g.ofConv)

/-- The point `φ • g` takes the value `g (h) (φ⁻¹)` at `h`. -/
@[simp]
theorem ofConv_smul_apply (φ : FormalCoordinate R) (g : WithConv (H →ₐ[k] R⸨X⸩)) (h : H) :
    (φ • g).ofConv h = substAlgEquiv φ⁻¹ (g.ofConv h) :=
  substAlgEquivRestrictScalars_apply k φ⁻¹ (g.ofConv h)

/-- Formal coordinates act on the convolution points `WithConv (H →ₐ[k] R⸨X⸩)` on the left:
`ρ_φ (g) = σ_(φ⁻¹) ∘ g` satisfies `ρ_(φ ∘ ψ) = ρ_φ ∘ ρ_ψ` because substitution reverses
composition. -/
noncomputable instance instMulActionWithConv :
    MulAction (FormalCoordinate R) (WithConv (H →ₐ[k] R⸨X⸩)) where
  one_smul g := ofConv_injective <| AlgHom.ext fun h ↦ by simp
  mul_smul φ ψ g := ofConv_injective <| AlgHom.ext fun h ↦ by
    simp only [ofConv_smul_apply, mul_inv_rev, substAlgEquiv_mul, AlgEquiv.mul_apply]

/-- Coordinate changes fix the constant points, the composites `H →ₐ[k] R →ₐ[k] R⸨X⸩` of points
`x : H →ₐ[k] R` with the inclusion of constant series. -/
@[simp]
theorem smul_toConv_toAlgHom_comp (φ : FormalCoordinate R) (x : H →ₐ[k] R) :
    φ • toConv ((IsScalarTower.toAlgHom k R R⸨X⸩).comp x) =
      toConv ((IsScalarTower.toAlgHom k R R⸨X⸩).comp x) := by
  refine ofConv_injective <| AlgHom.ext fun h ↦ ?_
  simp only [ofConv_smul_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, C_apply,
    substAlgEquiv_single_zero]

end Algebra

section Bialgebra

variable [Semiring H] [Bialgebra k H]

/-- The action of `φ` on loops is `AlgHom.mapValue` of the substitution automorphism of `φ⁻¹`. -/
theorem smul_def (φ : FormalCoordinate R) (g : WithConv (H →ₐ[k] R⸨X⸩)) :
    φ • g = AlgHom.mapValue (substAlgEquivRestrictScalars k φ⁻¹).toAlgHom g :=
  (AlgHom.mapValue_apply _ g).symm

/-- For a bialgebra `H`, formal coordinates act on the convolution monoid
`WithConv (H →ₐ[k] R⸨X⸩)` by monoid automorphisms, since each `ρ_φ` is `AlgHom.mapValue` of an
algebra automorphism. -/
noncomputable instance instMulDistribMulActionWithConv :
    MulDistribMulAction (FormalCoordinate R) (WithConv (H →ₐ[k] R⸨X⸩)) where
  smul_mul φ g g' := by simp only [smul_def, map_mul]
  smul_one φ := by simp only [smul_def, map_one]

/-- The action on loops is natural in the coefficient algebra: changing coefficients along
`f : R →ₐ[k] S` carries `φ • g` to `map f φ • g'`, where `g'` is the base-changed loop. -/
theorem mapValue_mapAlgHom_smul {S : Type*} [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
    (φ : FormalCoordinate R) (g : WithConv (H →ₐ[k] R⸨X⸩)) :
    AlgHom.mapValue (mapAlgHom f) (φ • g) =
      FormalCoordinate.map (f : R →+* S) φ • AlgHom.mapValue (mapAlgHom f) g := by
  refine ofConv_injective <| AlgHom.ext fun h ↦ ?_
  simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, ofConv_smul_apply,
    ← map_inv]
  have hf := mapRingHom_substAlgEquiv (f : R →+* S) φ⁻¹ (g.ofConv h)
  rw [← coe_mapAlgHom] at hf
  exact hf

/-- The action on loops is natural in the bialgebra: pre-composition with a bialgebra map
commutes with every `ρ_φ`. -/
theorem mapDomain_smul {H' : Type*} [Semiring H'] [Bialgebra k H'] (ψ : H' →ₐc[k] H)
    (φ : FormalCoordinate R) (g : WithConv (H →ₐ[k] R⸨X⸩)) :
    BialgHom.mapDomain ψ (φ • g) = φ • BialgHom.mapDomain ψ g := by
  rw [smul_def, smul_def, ← MonoidHom.comp_apply, BialgHom.mapValue_mapDomain,
    MonoidHom.comp_apply]

/-- The inclusion `WithConv (H →ₐ[k] R⟦X⟧) → WithConv (H →ₐ[k] R⸨X⸩)` of convolution monoids
is equivariant for the actions of formal coordinates: substitution of power series is the
restriction of substitution of Laurent series. For a commutative Hopf algebra `H` this is the
inclusion `G(R⟦X⟧) → G(R⸨X⸩)` of arcs into loops of `G = Spec H`. -/
theorem mapValue_ofPowerSeriesAlg_smul (φ : FormalCoordinate R) (g : WithConv (H →ₐ[k] R⟦X⟧)) :
    AlgHom.mapValue (ofPowerSeriesAlg ℤ k) (φ • g) =
      φ • AlgHom.mapValue (ofPowerSeriesAlg ℤ k) g := by
  refine ofConv_injective <| AlgHom.ext fun h ↦ ?_
  simp [FormalCoordinate.substAlgEquiv_apply]

/-- Each coordinate change maps the image of `WithConv (H →ₐ[k] R⟦X⟧)` in the convolution monoid
`WithConv (H →ₐ[k] R⸨X⸩)` onto itself. For a commutative Hopf algebra `H` this image is the
positive loop group `L⁺G(R)`, the image of the arcs `G(R⟦X⟧)` in the loops `G(R⸨X⸩)` of
`G = Spec H`. -/
@[simp]
theorem smul_mrange_mapValue_ofPowerSeriesAlg (φ : FormalCoordinate R) :
    φ • MonoidHom.mrange (AlgHom.mapValue (H := H) (ofPowerSeriesAlg ℤ k (A := R))) =
      MonoidHom.mrange (AlgHom.mapValue (H := H) (ofPowerSeriesAlg ℤ k (A := R))) := by
  refine SetLike.coe_injective ?_
  rw [Submonoid.coe_pointwise_smul, MonoidHom.coe_mrange, Set.smul_set_range]
  simp_rw [← mapValue_ofPowerSeriesAlg_smul]
  exact (MulAction.toPerm φ).surjective.range_comp _

/-- An element of `WithConv (H →ₐ[k] R⸨X⸩)` lies in the image of `WithConv (H →ₐ[k] R⟦X⟧)`, the
positive loops for a commutative Hopf algebra `H`, exactly when its image under a coordinate
change does. -/
theorem smul_mem_mrange_mapValue_ofPowerSeriesAlg_iff (φ : FormalCoordinate R)
    {g : WithConv (H →ₐ[k] R⸨X⸩)} :
    φ • g ∈ MonoidHom.mrange (AlgHom.mapValue (H := H) (ofPowerSeriesAlg ℤ k (A := R))) ↔
      g ∈ MonoidHom.mrange (AlgHom.mapValue (H := H) (ofPowerSeriesAlg ℤ k (A := R))) := by
  conv_lhs => rw [← smul_mrange_mapValue_ofPowerSeriesAlg φ]
  exact Submonoid.smul_mem_pointwise_smul_iff

end Bialgebra

section HopfAlgebra

variable [Semiring H] [HopfAlgebra k H]

/-- In the semidirect product of the loops by the coordinate changes, built from the action by
`MulDistribMulAction.toMulAut`, multiplication is `(g, φ) (h, ψ) = (g ρ_φ (h), φ ∘ ψ)`. -/
example (g h : WithConv (H →ₐ[k] R⸨X⸩)) (φ ψ : FormalCoordinate R) :
    (⟨g, φ⟩ * ⟨h, ψ⟩ :
        WithConv (H →ₐ[k] R⸨X⸩) ⋊[MulDistribMulAction.toMulAut _ _] FormalCoordinate R) =
      ⟨g * φ • h, φ * ψ⟩ := by
  ext <;> simp

end HopfAlgebra

section Examples

/-- For the trivial group `Spec k` the action on loops is trivial. -/
example (φ : FormalCoordinate R) (g : WithConv (k →ₐ[k] R⸨X⸩)) : φ • g = g :=
  (WithConv.convPoint_eq_one _).trans (WithConv.convPoint_eq_one g).symm

/-- For the additive group, `ρ_φ` is the substitution `f ↦ f (φ⁻¹)` on `𝔾ₐ(R⸨X⸩) = R⸨X⸩`. -/
theorem toAdd_gaPointsMulEquiv_smul (φ : FormalCoordinate R)
    (g : WithConv (SymmetricAlgebra k k →ₐ[k] R⸨X⸩)) :
    Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (φ • g)) =
      substAlgEquiv φ⁻¹ (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g)) := by
  simp

/-- For the multiplicative group, `ρ_φ` is the substitution `u ↦ u (φ⁻¹)` on
`𝔾ₘ(R⸨X⸩) = R⸨X⸩ˣ`. -/
theorem pointsMulEquiv_smul (φ : FormalCoordinate R) (g : WithConv (k[T;T⁻¹] →ₐ[k] R⸨X⸩)) :
    (MultiplicativeGroup.pointsMulEquiv (φ • g) : R⸨X⸩) =
      substAlgEquiv φ⁻¹ (MultiplicativeGroup.pointsMulEquiv g : R⸨X⸩) := by
  rw [smul_def, MultiplicativeGroup.pointsMulEquiv_mapValue, Units.coe_map]
  simp

/-- For the multiplicative group, the homothety `X ↦ a X` sends the loop `X ^ n` to
`a ^ (-n) X ^ n`. -/
theorem pointsMulEquiv_homothety_smul_pointsMulEquiv_symm_unitX_zpow (a : Rˣ) (n : ℤ) :
    (MultiplicativeGroup.pointsMulEquiv
        (FormalCoordinate.homothety a •
          (MultiplicativeGroup.pointsMulEquiv (R := k) (A := R⸨X⸩)).symm (unitX ^ n)) : R⸨X⸩) =
      single n ↑(a ^ (-n)) := by
  rw [pointsMulEquiv_smul, ← map_inv FormalCoordinate.homothety a, substAlgEquiv_homothety]
  -- the monomial `X ^ n` is `single n 1`, and `rescale a⁻¹` scales it by `a ^ (-n)`
  simp only [MulEquiv.apply_symm_apply, val_unitX_zpow, rescale_single]
  simp

/-- The homothety `X ↦ a X` fixes the loop `X ^ n` of the multiplicative group exactly when
`a ^ n = 1`. -/
theorem homothety_smul_pointsMulEquiv_symm_unitX_zpow_eq_iff_zpow_eq_one (a : Rˣ) (n : ℤ) :
    FormalCoordinate.homothety a •
        (MultiplicativeGroup.pointsMulEquiv (R := k) (A := R⸨X⸩)).symm (unitX ^ n) =
      (MultiplicativeGroup.pointsMulEquiv (R := k) (A := R⸨X⸩)).symm (unitX ^ n) ↔
      a ^ n = 1 := by
  rw [← (MultiplicativeGroup.pointsMulEquiv (R := k) (A := R⸨X⸩)).injective.eq_iff,
    ← Units.val_inj, pointsMulEquiv_homothety_smul_pointsMulEquiv_symm_unitX_zpow]
  simp [(single_injective n).eq_iff]

end Examples

end TauCeti.LaurentSeries
