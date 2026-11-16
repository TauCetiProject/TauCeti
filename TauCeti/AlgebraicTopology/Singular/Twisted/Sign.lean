/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coinvariants
public import TauCeti.RepresentationTheory.Coinvariants

/-!
# Zeroth homology with sign coefficients

A local coefficient system `L` on a path-connected space whose fibre at `x` is a copy of `R`, and
whose loops at `x` act by `1` or by `-1`, has zeroth homology either `R` or `R ⧸ 2R`. Twisted zeroth
homology is the coinvariants of the monodromy representation
(`TauCeti.LocalCoefficientSystem.twistedHomology₀IsoCoinvariants`). If every loop acts by `1`,
these coinvariants are the fibre itself
(`TauCeti.LocalCoefficientSystem.twistedHomology₀EquivOfIsTrivial`). If some loop acts by `-1`,
the class of a coefficient `a` agrees with that of `-a`, and the coinvariants are the fibre modulo
`2` (`TauCeti.LocalCoefficientSystem.twistedHomology₀EquivQuotientTwo`).

The sign local system of a double cover `p : E → X` with deck involution `σ`
(`IsCoveringMap.signLocalSystem`) is of this kind. Its fibre over `x` consists of the functions on
`p ⁻¹' {x}` changing sign under `σ`, and a loop at `x` acts by `1` when its lift starting at a
point `e` of the fibre closes up, and by `-1` when that lift ends at `σ e`
(`IsCoveringMap.monodromyRepresentation_signLocalSystem_eq_one`,
`IsCoveringMap.monodromyRepresentation_signLocalSystem_eq_neg_one`). Every loop does one or the
other, since `e` and `σ e` are the only points of the fibre
(`IsCoveringMap.monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one`).

For the orientation local system `o(E)` of a real vector bundle `E` with integer coefficients, this
is the familiar dichotomy: over a connected base, `H₀(B; o(E))` is `ℤ` when `E` is orientable and
`ℤ/2` otherwise. The bundle form is in `TauCeti.Topology.VectorBundle.Orientation.TwistedHomology`.

## Main definitions

* `TauCeti.LocalCoefficientSystem.twistedHomology₀EquivOfIsTrivial`: zeroth homology of a local
  system with trivial monodromy is its fibre.
* `TauCeti.LocalCoefficientSystem.twistedHomology₀EquivQuotientTwo`: zeroth homology of a local
  system with fibre `R` on which some loop acts by `-1` and every loop by `±1` is `R ⧸ 2R`.

## Main results

* `IsCoveringMap.monodromyRepresentation_signLocalSystem_eq_one` and
  `IsCoveringMap.monodromyRepresentation_signLocalSystem_eq_neg_one`: the action of a loop on the
  sign local system of a double cover.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (zeroth homology with local coefficients as
  coinvariants, and the orientation system of a manifold).
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [CommRing R] {X : TopCat.{v}} [PathConnectedSpace X]
  (L : LocalCoefficientSystem.{u, v, max v w} R X) (x : X)

/-- **Zeroth homology with trivial monodromy.** If every loop at `x` acts trivially on the fibre of
`L` at `x`, twisted zeroth homology is that fibre. -/
def twistedHomology₀EquivOfIsTrivial [(monodromyRepresentation L x).IsTrivial] :
    twistedHomology L 0 ≃ₗ[R] L.obj (FundamentalGroupoid.mk x) :=
  (twistedHomology₀IsoCoinvariants L x).toLinearEquiv ≪≫ₗ
    Representation.coinvariantsEquivOfIsTrivial _

/-- The identification of zeroth homology with the fibre sends the class of a coefficient at `x` to
that coefficient. -/
@[simp]
theorem twistedHomology₀EquivOfIsTrivial_ιTwistedHomology₀
    [(monodromyRepresentation L x).IsTrivial] (a : L.obj (FundamentalGroupoid.mk x)) :
    twistedHomology₀EquivOfIsTrivial L x (ιTwistedHomology₀ L x a) = a := by
  rw [twistedHomology₀EquivOfIsTrivial, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    ιTwistedHomology₀_isoCoinvariants_hom_apply,
    Representation.coinvariantsEquivOfIsTrivial_mk]

/-- **Zeroth homology modulo two.** Let the fibre of `L` at `x` be identified with `R` by `e`. If
every loop at `x` acts on it by `1` or by `-1`, and some loop acts by `-1`, twisted zeroth homology
is `R ⧸ 2R`. -/
def twistedHomology₀EquivQuotientTwo (e : L.obj (FundamentalGroupoid.mk x) ≃ₗ[R] R)
    (h : ∀ g, monodromyRepresentation L x g = 1 ∨ monodromyRepresentation L x g = -1)
    {g₀ : FundamentalGroup X x} (hg₀ : monodromyRepresentation L x g₀ = -1) :
    twistedHomology L 0 ≃ₗ[R] R ⧸ Ideal.span {(2 : R)} :=
  (twistedHomology₀IsoCoinvariants L x).toLinearEquiv ≪≫ₗ
    Representation.coinvariantsEquivQuotientTwo h hg₀ ≪≫ₗ
    Submodule.Quotient.equiv _ _ e (by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, Ideal.smul_eq_mul,
        Ideal.mul_top])

/-- The identification of zeroth homology with `R ⧸ 2R` sends the class of a coefficient `a` at `x`
to the residue of `e a`. -/
@[simp]
theorem twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀
    (e : L.obj (FundamentalGroupoid.mk x) ≃ₗ[R] R)
    (h : ∀ g, monodromyRepresentation L x g = 1 ∨ monodromyRepresentation L x g = -1)
    {g₀ : FundamentalGroup X x} (hg₀ : monodromyRepresentation L x g₀ = -1)
    (a : L.obj (FundamentalGroupoid.mk x)) :
    twistedHomology₀EquivQuotientTwo L x e h hg₀ (ιTwistedHomology₀ L x a) =
      Ideal.Quotient.mk _ (e a) := by
  rw [twistedHomology₀EquivQuotientTwo, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    Iso.toLinearEquiv_apply, ιTwistedHomology₀_isoCoinvariants_hom_apply,
    Representation.coinvariantsEquivQuotientTwo_mk, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearEquiv.coe_coe, Ideal.Quotient.mk_eq_mk]

end TauCeti.LocalCoefficientSystem

namespace IsCoveringMap

open TauCeti.LocalCoefficientSystem

variable {R : Type u} [CommRing R] {E : Type w} [TopologicalSpace E] {X : TopCat.{v}} {p : E → X}
  (hp : IsCoveringMap p) {σ : C(E, E)} {hσ : p ∘ σ = p}
  (hfix : ∀ e, σ e ≠ e) (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

include hfix hfib

/-- A loop at `x` whose lift starting at `e` closes up acts trivially on the sign local system of a
double cover. -/
theorem monodromyRepresentation_signLocalSystem_eq_one {x : X} {g : FundamentalGroup X x}
    {e : p ⁻¹' {x}} (he : hp.monodromy g.asHom e = e) :
    monodromyRepresentation (hp.signLocalSystem R σ hσ) x g = 1 := by
  ext f
  apply ((hp.signLocalSystemObjEquiv σ hσ _).trans
    (TauCeti.signFiberEquiv (R := R) (hσ := hσ) hfix hfib e)).injective
  have hf := hp.signLocalSystemObjEquiv_map_apply_monodromy σ hσ g.asHom f e
  rw [he] at hf
  simpa using hf

/-- A loop at `x` whose lift starting at `e` ends at `σ e` acts by `-1` on the sign local system of
a double cover. -/
theorem monodromyRepresentation_signLocalSystem_eq_neg_one {x : X} {g : FundamentalGroup X x}
    {e : p ⁻¹' {x}} (he : hp.monodromy g.asHom e = Function.fiberMap σ hσ x e) :
    monodromyRepresentation (hp.signLocalSystem R σ hσ) x g =
      -1 := by
  ext f
  apply ((hp.signLocalSystemObjEquiv σ hσ _).trans
    (TauCeti.signFiberEquiv (R := R) (hσ := hσ) hfix hfib e)).injective
  have hf := hp.signLocalSystemObjEquiv_map_apply_monodromy σ hσ g.asHom f e
  rw [he] at hf
  -- The value at `σ e` of a function changing sign under `σ` is minus its value at `e`.
  have hneg := TauCeti.signFiberEquiv_fiberMap (R := R) (hσ := hσ) hfix hfib e
    (hp.signLocalSystemObjEquiv σ hσ _ (((hp.signLocalSystem R σ hσ).map g.asHom).hom f))
  simp only [TauCeti.signFiberEquiv_apply] at hneg
  simp only [monodromyRepresentation_apply,
    LinearEquiv.trans_apply, TauCeti.signFiberEquiv_apply, LinearMap.neg_apply,
    one_apply_eq_self, map_neg]
  rw [← neg_eq_iff_eq_neg, ← hneg]
  exact hf

/-- Every loop at `x` acts by `1` or by `-1` on the sign local system of a double cover. -/
theorem monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one {x : X}
    (g : FundamentalGroup X x) :
    monodromyRepresentation (hp.signLocalSystem R σ hσ) x g = 1 ∨
      monodromyRepresentation (hp.signLocalSystem R σ hσ) x g =
        -1 := by
  rcases isEmpty_or_nonempty (p ⁻¹' {x}) with hx | ⟨⟨e⟩⟩
  · -- Over an empty fibre the sign module is zero.
    refine .inl (LinearMap.ext fun f ↦ (hp.signLocalSystemObjEquiv σ hσ _).injective
      (Subtype.ext (funext fun e ↦ (IsEmpty.false e).elim)))
  rcases hfib e (hp.monodromy g.asHom e) ((hp.monodromy g.asHom e).2.trans e.2.symm) with h | h
  · exact .inl (hp.monodromyRepresentation_signLocalSystem_eq_one hfix hfib (Subtype.ext h))
  · exact .inr (hp.monodromyRepresentation_signLocalSystem_eq_neg_one hfix hfib
      (Subtype.ext (h.trans (Function.fiberMap_apply_coe σ hσ x e).symm)))

end IsCoveringMap
