/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic
public import TauCeti.AlgebraicTopology.NotSimplyConnected
public import TauCeti.Geometry.Manifold.Instances.KodairaThurston

/-!
# The fundamental group and first homology of the Kodaira–Thurston manifold

The Kodaira–Thurston manifold `TauCeti.KodairaThurston` is the quotient of the cover `ℝ⁴` by the
free, properly discontinuous action of the deck group `Γ = H(ℤ) × ℤ`
(`TauCeti.KodairaThurston.DeckGroup`), where `H(ℤ)` is the integer Heisenberg group. The cover is
contractible, so the orbit projection is a universal cover, and the fundamental group of the
Kodaira–Thurston manifold is the deck group:

  `π₁(KT) ≃* H(ℤ) × ℤ` (`TauCeti.KodairaThurston.fundamentalGroupMulEquiv`).

Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv` identifies the fundamental group with the
opposite group `Γᵐᵒᵖ`, since the monodromy of the composite of two loops applies the second loop
first. The deck group is isomorphic to its opposite by the anti-automorphism
`((x, y, z), n) ↦ ((x, y, x y - z), n)` (`TauCeti.KodairaThurston.DeckGroup.opMulEquiv`), which
fixes the coordinates `x`, `y` and `n`. Through it, a loop at `[0]` whose lift from `0` ends at
`g • 0` corresponds to an element with the same coordinates `x`, `y` and `n` as `g`. The
fundamental group is not commutative, so the Kodaira–Thurston manifold is not simply connected.

The abelianization of the deck group is `ℤ³`, through `((x, y, z), n) ↦ (x, y, n)`
(`TauCeti.KodairaThurston.DeckGroup.abelianizationMulEquiv`): the commutator subgroup of `H(ℤ)` is
its centre `{(0, 0, z)}`. With the Hurewicz theorem this computes the first singular homology
group with integer coefficients,

  `H₁(KT; ℤ) ≃+ ℤ³` (`TauCeti.KodairaThurston.firstHomologyAddEquiv`),

which sends the class of the loop covered by the straight segment from `0` to `g • 0`
(`TauCeti.KodairaThurston.deckLoop g`) to `(x, y, n)`, the coordinates of `g`. Its rank three is
the first Betti number; the periods of the closed forms `dx`, `dy` and `dt` on these loops compute
the first de Rham cohomology in `TauCeti.Geometry.Manifold.DeRham.KodairaThurston`.

## Main definitions

* `TauCeti.KodairaThurston.DeckGroup.opMulEquiv`: the deck group is isomorphic to its opposite.
* `TauCeti.KodairaThurston.fundamentalGroupMulEquiv`: `π₁(KT, x) ≃* H(ℤ) × ℤ`, for a chosen lift
  of the base point to the cover.
* `TauCeti.KodairaThurston.DeckGroup.abelianizationMulEquiv`: the abelianization of the deck group
  is `ℤ³`.
* `TauCeti.KodairaThurston.deckLoop g`: the loop at `[0]` covered by the segment from `0` to
  `g • 0`.
* `TauCeti.KodairaThurston.firstHomologyAddEquiv`: `H₁(KT; ℤ) ≃+ ℤ × ℤ × ℤ`.

## Main results

* `TauCeti.KodairaThurston.isQuotientCoveringMap_mk`: the orbit projection is a covering map
  with group the deck group.
* `TauCeti.KodairaThurston.fundamentalGroupMulEquiv_apply_eq_iff`: the element assigned to a loop
  is read off from its monodromy.
* `TauCeti.KodairaThurston.not_isMulCommutative_fundamentalGroup`: the fundamental group is not
  commutative.
* `TauCeti.KodairaThurston.not_simplyConnectedSpace`: the Kodaira–Thurston manifold is not simply
  connected.
* `TauCeti.KodairaThurston.firstHomologyAddEquiv_loopClass_deckLoop`: the first homology class of
  `deckLoop g` has coordinates `(x, y, n)`.

## References

* W. P. Thurston, *Some simple examples of symplectic manifolds*, Proceedings of the American
  Mathematical Society 55 (1976), 467–468.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Proposition 1.40 (the
  fundamental group of the quotient of a simply connected space by a covering space action) and
  Theorem 2A.1 (the Hurewicz theorem in degree one).
* The fundamental-group development follows the computation of the fundamental group of a lens
  space in `TauCeti.AlgebraicTopology.UniversalCover.LensSpace.FundamentalGroup`.
-/

public section

noncomputable section

open TauCeti.HurewiczOne

namespace TauCeti

namespace KodairaThurston

open Cover

/-! ### The deck group -/

namespace DeckGroup

/-- **The deck group is isomorphic to its opposite**, by the anti-automorphism
`((x, y, z), n) ↦ ((x, y, x y - z), n)` (`TauCeti.HeisenbergGroup.opMulEquiv` on the Heisenberg
factor), which fixes the coordinates `x`, `y` and `n`. -/
def opMulEquiv : DeckGroup ≃* DeckGroupᵐᵒᵖ where
  toFun g := .op ((HeisenbergGroup.opMulEquiv g.1).unop, g.2)
  invFun g := (HeisenbergGroup.opMulEquiv.symm (.op g.unop.1), g.unop.2)
  left_inv g := by simp
  right_inv g := MulOpposite.unop_injective <| by simp
  map_mul' g h := MulOpposite.unop_injective <| by
    simp only [Prod.fst_mul, map_mul, MulOpposite.unop_mul, Prod.snd_mul, MulOpposite.unop_op,
      Prod.mk_mul_mk, mul_comm g.2]

@[simp]
theorem unop_opMulEquiv (g : DeckGroup) :
    (opMulEquiv g).unop = (⟨g.1.x, g.1.y, g.1.x * g.1.y - g.1.z⟩, g.2) := by
  simp [opMulEquiv]

@[simp]
theorem opMulEquiv_symm_op (g : DeckGroup) :
    opMulEquiv.symm (.op g) = (⟨g.1.x, g.1.y, g.1.x * g.1.y - g.1.z⟩, g.2) := by
  simp [opMulEquiv]

/-- **The abelianization of the deck group** `H(ℤ) × ℤ` is `ℤ³`, through the coordinates
`((x, y, z), n) ↦ (x, y, n)`. -/
def abelianizationMulEquiv : Abelianization DeckGroup ≃* Multiplicative (ℤ × ℤ × ℤ) :=
  (Abelianization.prodMulEquiv _).trans <|
    (HeisenbergGroup.abelianizationMulEquiv.prodCongr Abelianization.equivOfComm.symm).trans <|
      (MulEquiv.prodMultiplicative (ℤ × ℤ) ℤ).symm.trans
        (AddEquiv.prodAssoc (M := ℤ) (N := ℤ) (P := ℤ)).toMultiplicative

@[simp]
theorem abelianizationMulEquiv_of (g : DeckGroup) :
    abelianizationMulEquiv (Abelianization.of g) = .ofAdd (g.1.x, g.1.y, g.2.toAdd) := by
  simp [abelianizationMulEquiv, MulEquiv.prodCongr]

end DeckGroup

/-! ### The universal cover and the fundamental group -/

/-- The orbit projection from the cover `ℝ⁴` to the Kodaira–Thurston manifold is a covering map,
whose fibres are the orbits of the free action of the deck group. -/
theorem isQuotientCoveringMap_mk : IsQuotientCoveringMap mk DeckGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The orbit projection from the cover is a covering map. -/
theorem isCoveringMap_mk : IsCoveringMap mk :=
  isQuotientCoveringMap_mk.isCoveringMap

/-- The Kodaira–Thurston manifold is path-connected, as a quotient of `ℝ⁴`. -/
instance instPathConnectedSpace : PathConnectedSpace KodairaThurston :=
  inferInstanceAs (PathConnectedSpace (Quotient (MulAction.orbitRel DeckGroup Cover)))

/-- **The fundamental group of the Kodaira–Thurston manifold** is the deck group `H(ℤ) × ℤ`, at
any base point `x` with a chosen lift `e` to the cover. A loop whose lift from `e` ends at `h • e`
corresponds to `((a, b, a b - c), n)` when `h = ((a, b, c), n)`
(`TauCeti.KodairaThurston.fundamentalGroupMulEquiv_apply_eq_iff`). -/
def fundamentalGroupMulEquiv {x : KodairaThurston} (e : mk ⁻¹' {x}) :
    FundamentalGroup KodairaThurston x ≃* DeckGroup :=
  (isQuotientCoveringMap_mk.fundamentalGroupEquiv e).trans DeckGroup.opMulEquiv.symm

/-- A loop class corresponds to `g` exactly when its monodromy carries the chosen lift `e` of the
base point to `h • e`, where `h` is the image of `g` under the anti-automorphism
`((x, y, z), n) ↦ ((x, y, x y - z), n)`. -/
theorem fundamentalGroupMulEquiv_apply_eq_iff {x : KodairaThurston} (e : mk ⁻¹' {x})
    (γ : FundamentalGroup KodairaThurston x) (g : DeckGroup) :
    fundamentalGroupMulEquiv e γ = g ↔
      (DeckGroup.opMulEquiv g).unop • (e : Cover) = isCoveringMap_mk.monodromy γ.asHom e := by
  rw [fundamentalGroupMulEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
  -- Mathlib has no apply lemma for `IsQuotientCoveringMap.fundamentalGroupEquiv`, which is
  -- `MulEquiv.ofBijective` of `fundamentalGroupToMulOpposite`; its value unfolds by `rfl`.
  have hF : isQuotientCoveringMap_mk.fundamentalGroupEquiv e γ =
      isQuotientCoveringMap_mk.fundamentalGroupToMulOpposite e γ :=
    rfl
  rw [hF, IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_iff]

/-- The loop class of the image of a path `Γ` in the cover from `e` to `h • e` corresponds to the
image of `h` under the anti-automorphism `((x, y, z), n) ↦ ((x, y, x y - z), n)`. -/
theorem fundamentalGroupMulEquiv_mk_eq {x : KodairaThurston} {e : mk ⁻¹' {x}} {γ : Path x x}
    {h : DeckGroup} {Γ : C(unitInterval, Cover)} (hΓ : mk ∘ Γ = γ) (hΓ₀ : Γ 0 = e)
    (hΓ₁ : Γ 1 = h • (e : Cover)) :
    fundamentalGroupMulEquiv e (.of (.mk γ)) = DeckGroup.opMulEquiv.symm (.op h) := by
  have hF : isQuotientCoveringMap_mk.fundamentalGroupEquiv e (.of (.mk γ)) = .op h :=
    isQuotientCoveringMap_mk.fundamentalGroupToMulOpposite_apply_mk_eq hΓ hΓ₀ hΓ₁
  rw [fundamentalGroupMulEquiv, MulEquiv.trans_apply, hF]

/-- The deck group is not commutative: the commutator of `((1, 0, 0), 0)` and `((0, 1, 0), 0)` is
`((0, 0, 1), 0)`. -/
theorem DeckGroup.not_isMulCommutative : ¬ IsMulCommutative DeckGroup := by
  intro h
  have hc := (h.is_comm.comm ((⟨1, 0, 0⟩ : HeisenbergGroup ℤ), 1)
    ((⟨0, 1, 0⟩ : HeisenbergGroup ℤ), 1))
  have hz := congrArg (fun g : DeckGroup ↦ g.1.z) hc
  simp at hz

/-- **The fundamental group of the Kodaira–Thurston manifold is not commutative.** -/
theorem not_isMulCommutative_fundamentalGroup (x : KodairaThurston) :
    ¬ IsMulCommutative (FundamentalGroup KodairaThurston x) := by
  obtain ⟨p, rfl⟩ := mk_surjective x
  intro h
  refine DeckGroup.not_isMulCommutative ⟨⟨fun g g' ↦ ?_⟩⟩
  have e := fundamentalGroupMulEquiv (x := mk p) ⟨p, rfl⟩
  apply e.symm.injective
  rw [map_mul, map_mul, h.is_comm.comm]

/-- **The Kodaira–Thurston manifold is not simply connected.** -/
theorem not_simplyConnectedSpace : ¬ SimplyConnectedSpace KodairaThurston := by
  intro h
  let x : KodairaThurston := mk 0
  have : Subsingleton (FundamentalGroup KodairaThurston x) :=
    (simplyConnectedSpace_iff_forall_subsingleton_fundamentalGroup.1 h).2 x
  exact not_isMulCommutative_fundamentalGroup x ⟨⟨fun _ _ ↦ Subsingleton.elim _ _⟩⟩

/-! ### The first homology group -/

/-- The straight segment `s ↦ s • (g • 0)` from `0` to `g • 0` in the cover. -/
def deckPath (g : DeckGroup) : Path (0 : Cover) (g • 0) where
  toFun s := (s : ℝ) • (g • (0 : Cover))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
theorem deckPath_apply (g : DeckGroup) (s : unitInterval) :
    deckPath g s = (s : ℝ) • (g • (0 : Cover)) :=
  (rfl)

/-- The loop at `[0]` covered by the straight segment `TauCeti.KodairaThurston.deckPath g` from
`0` to `g • 0` in the cover. -/
def deckLoop (g : DeckGroup) : Path (mk 0) (mk 0) :=
  ((deckPath g).map continuous_mk).cast rfl (mk_eq_mk_iff.2 ⟨g, rfl⟩).symm

/-- The loop `deckLoop g` is the image of the segment `deckPath g`, with its endpoint `[g • 0]`
recast as `[0]`. -/
theorem deckLoop_eq_cast_map (g : DeckGroup) :
    deckLoop g = ((deckPath g).map continuous_mk).cast rfl (mk_eq_mk_iff.2 ⟨g, rfl⟩).symm :=
  (rfl)

@[simp]
theorem deckLoop_apply (g : DeckGroup) (s : unitInterval) :
    deckLoop g s = mk ((s : ℝ) • (g • (0 : Cover))) :=
  (rfl)

/-- The loop `deckLoop g` corresponds, in the fundamental group based at `[0]` with the lift `0`,
to the image of `g` under the anti-automorphism `((x, y, z), n) ↦ ((x, y, x y - z), n)`. -/
theorem fundamentalGroupMulEquiv_deckLoop (g : DeckGroup) :
    fundamentalGroupMulEquiv (x := mk 0) ⟨0, rfl⟩ (.of (.mk (deckLoop g))) =
      DeckGroup.opMulEquiv.symm (.op g) :=
  fundamentalGroupMulEquiv_mk_eq (Γ := (deckPath g).toContinuousMap) rfl (deckPath g).source
    (deckPath g).target

/-- **The first homology of the Kodaira–Thurston manifold** is `ℤ³`: the first singular homology
group with integer coefficients is the abelianization `ℤ³` of its fundamental group, by the
Hurewicz theorem. The class of `deckLoop g` has the coordinates `(x, y, n)` of `g`
(`TauCeti.KodairaThurston.firstHomologyAddEquiv_loopClass_deckLoop`). -/
def firstHomologyAddEquiv :
    ((singularChains ℤ).obj (TopCat.of KodairaThurston)).homology 1 ≃+ ℤ × ℤ × ℤ :=
  (hurewiczHomologyAddEquiv (X := TopCat.of KodairaThurston) (mk 0)).symm.trans
    (AddEquiv.toMultiplicativeRight.symm
      ((fundamentalGroupMulEquiv (x := mk 0) ⟨0, rfl⟩).abelianizationCongr.trans
        DeckGroup.abelianizationMulEquiv))

/-- The class of the loop `deckLoop g` in the first homology of the Kodaira–Thurston manifold has
coordinates `(x, y, n)`, where `g = ((x, y, z), n)`. -/
@[simp]
theorem firstHomologyAddEquiv_loopClass_deckLoop (g : DeckGroup) :
    firstHomologyAddEquiv
        (H₁AddEquivHomology _ (loopClass (X := TopCat.of KodairaThurston) (deckLoop g))) =
      (g.1.x, g.1.y, g.2.toAdd) := by
  have h := (AddEquiv.symm_apply_eq _).2
    (hurewiczHomologyAddEquiv_ofMul_of_mk (X := TopCat.of KodairaThurston) (deckLoop g)).symm
  rw [firstHomologyAddEquiv, AddEquiv.trans_apply, h]
  simp [AddEquiv.toMultiplicativeRight, fundamentalGroupMulEquiv_deckLoop]

/-- The inverse of `TauCeti.KodairaThurston.firstHomologyAddEquiv` sends `(a, b, n)` to the class
of the loop covered by the segment from `0` to `(a, b, 0, n)`. -/
theorem firstHomologyAddEquiv_symm_apply (v : ℤ × ℤ × ℤ) :
    firstHomologyAddEquiv.symm v =
      H₁AddEquivHomology _ (loopClass (X := TopCat.of KodairaThurston)
        (deckLoop (⟨v.1, v.2.1, 0⟩, .ofAdd v.2.2))) := by
  simp [AddEquiv.symm_apply_eq]

end KodairaThurston

end TauCeti
