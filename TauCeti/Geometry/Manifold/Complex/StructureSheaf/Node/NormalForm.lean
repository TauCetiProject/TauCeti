/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Rechart
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
import Mathlib.RingTheory.AdjoinRoot

/-!
# The Weierstrass normal form of a holomorphic node equation

The local model for smoothing a node over a base `E` is the hypersurface `xy = s(b)` in
`(E × ℂ) × ℂ`, for a holomorphic base germ `s`. Its local ring at the node `((b, 0), 0)` is the
quotient of the holomorphic stalk by the node equation `xy - s(b)`
(`TauCeti.holomorphicStructureSheaf.nodeEquation`). No condition is imposed on `s`: it may vanish
identically (a permanent node) or to any order, as in `xy = b²`, and then the total space is
singular.

The linear change of coordinates `x = u + v`, `y = u - v` turns `xy - s(b)` into
`u² - (v² + s(b))`. This is a monic quadratic polynomial in `u` over the ring `𝒪_{E × ℂ, (b, 0)}`
of holomorphic germs in the transverse coordinates `(b, v)`
(`TauCeti.holomorphicStructureSheaf.nodeNormalForm`). When `s(b) = 0`, so that the node lies on
the hypersurface, it is a distinguished polynomial. Weierstrass division then presents the local
ring of the node as a finite free module over `𝒪_{E × ℂ, (b, 0)}`.

## Main definitions

* `TauCeti.holomorphicStructureSheaf.nodeEquation`: the germ of `xy - s(b)` at a point of
  `(E × ℂ) × ℂ`.
* `TauCeti.holomorphicStructureSheaf.nodeNormalForm`: the polynomial `X² - (v² + s(b))` over
  `𝒪_{E × ℂ, (b, 0)}`.
* `TauCeti.holomorphicStructureSheaf.nodeQuotientEquiv`: the coordinate change identifies the local
  ring `𝒪 ⧸ (xy - s(b))` of the node with the normal form quotient `𝒪 ⧸ (u² - (v² + s(b)))`.
* `TauCeti.holomorphicStructureSheaf.nodeTransverseHom`: the structure map
  `𝒪_{E × ℂ, (b, 0)} → 𝒪 ⧸ (xy - s(b))`, pulling a germ back along
  `((b, x), y) ↦ (b, (x - y) / 2)` (`nodeTransverseHom_eq_mk`).

## Main results

* `TauCeti.holomorphicStructureSheaf.nodeTransverseHom_comp_stalkPrecomp_fst`: the structure map
  extends the pullback of base germs along `((b, x), y) ↦ b`.
* `TauCeti.holomorphicStructureSheaf.nodeTransverseHom_flat`,
  `TauCeti.holomorphicStructureSheaf.nodeTransverseHom_finite`: the local ring of the node is a
  flat and finite algebra over `𝒪_{E × ℂ, (b, 0)}`, for every holomorphic base germ `s`.
* `TauCeti.holomorphicStructureSheaf.bijective_nodeTransverseHom_add_mul`: if `s(b) = 0`, the local
  ring of the node is free of rank two over `𝒪_{E × ℂ, (b, 0)}`, with basis `1` and the class
  of `(x + y) / 2`.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the local models `xy = a` of nodal families.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II,
  for Weierstrass division and analytic hypersurface local rings.
-/

public noncomputable section

open Polynomial Filter Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### The node equation and the coordinate change -/

/-- The holomorphic germ of `xy - s(b)` at a point of the ambient base times two lines.
The parameter is an arbitrary holomorphic base germ, not a globally defined function. -/
def nodeEquation (b : E) (x y : ℂ)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, x), y) :=
  germOfContMDiff (fun z : (E × ℂ) × ℂ ↦ z.1.2 * z.2)
      (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, x), y) -
    stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) (fun z ↦ z.1.1)
      (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, x), y) s

/-- In any representative of the base germ, the node equation is `xy - s(b)`. -/
theorem toFilterGerm_nodeEquation (b : E) (x y : ℂ)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b)
    {f : E → ℂ} (hf : toFilterGerm 𝓘(ℂ, E) E b (𝓝 b) le_rfl s = f) :
    toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, x), y) (𝓝 ((b, x), y)) le_rfl
      (nodeEquation b x y s) = (fun z : (E × ℂ) × ℂ ↦ z.1.2 * z.2 - f z.1.1) := by
  rw [nodeEquation, map_sub, toFilterGerm_germOfContMDiff, toFilterGerm_stalkPrecomp,
    hf, Germ.coe_compTendsto, ← Germ.coe_sub]
  rfl

/-- Evaluation of the defining equation at its ambient base point. -/
@[simp]
theorem eval_nodeEquation (b : E) (x y : ℂ)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    eval 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, x), y) (nodeEquation b x y s) =
      x * y - eval 𝓘(ℂ, E) E b s := by
  simp [nodeEquation, eval_stalkPrecomp]

/-- The linear change of coordinates `((b, v), u) ↦ ((b, u + v), u - v)` of `(E × ℂ) × ℂ`, that is
`x = u + v` and `y = u - v`. It carries `xy` to `u² - v²` and fixes the base coordinate `b`.
It is reducible so that the preserved base coordinate stays visible in dependent stalk types. -/
private abbrev nodeCoordinateChange :
    ((E × ℂ) × ℂ) ≃ₘ^ω⟮𝓘(ℂ, (E × ℂ) × ℂ), 𝓘(ℂ, (E × ℂ) × ℂ)⟯ ((E × ℂ) × ℂ) where
  toFun p := ((p.1.1, p.2 + p.1.2), p.2 - p.1.2)
  invFun p := ((p.1.1, (p.1.2 - p.2) / 2), (p.1.2 + p.2) / 2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  contMDiff_toFun := contMDiff_iff_contDiff.mpr (by dsimp; fun_prop)
  contMDiff_invFun := contMDiff_iff_contDiff.mpr (by dsimp; fun_prop)

private theorem nodeCoordinateChange_apply (p : (E × ℂ) × ℂ) :
    nodeCoordinateChange p = ((p.1.1, p.2 + p.1.2), p.2 - p.1.2) := (rfl)

/-! ### The normal form polynomial -/

/-- The Weierstrass normal form `X² - (v² + s(b))` of the node equation, a polynomial over the
holomorphic germs at `(b, 0)` in the transverse coordinates `(b, v)`. -/
def nodeNormalForm (b : E) (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0))[X] :=
  X ^ 2 - C (evalVertical b 0 (X ^ 2 + C s))

theorem nodeNormalForm_def (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    nodeNormalForm b s = X ^ 2 - C (evalVertical b 0 (X ^ 2 + C s)) := (rfl)

theorem monic_nodeNormalForm (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (nodeNormalForm b s).Monic :=
  monic_X_pow_sub_C _ two_ne_zero

@[simp]
theorem natDegree_nodeNormalForm (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (nodeNormalForm b s).natDegree = 2 :=
  natDegree_X_pow_sub_C _

/-- At a node on the hypersurface, that is when `s(b) = 0`, the normal form is distinguished. -/
theorem isDistinguishedAt_nodeNormalForm {b : E}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b}
    (hs : eval 𝓘(ℂ, E) E b s = 0) :
    (nodeNormalForm b s).IsDistinguishedAt (IsLocalRing.maximalIdeal
      ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0))) where
  mem {n} hn := by
    rw [natDegree_nodeNormalForm] at hn
    rw [maximalIdeal_stalk, RingHom.mem_ker]
    interval_cases n
    · rw [nodeNormalForm, coeff_sub, coeff_C_zero, map_sub, eval_evalVertical]
      simp [hs]
    · rw [nodeNormalForm, coeff_sub, coeff_C]
      simp
  monic := monic_nodeNormalForm b s

/-! ### The coordinate change on the stalk at the node -/

/-- The origin `((b, 0), 0)` is fixed by `nodeCoordinateChange`. -/
private theorem nodeCoordinateChange_origin (b : E) :
    ((b, (0 : ℂ)), (0 : ℂ)) = nodeCoordinateChange ((b, (0 : ℂ)), (0 : ℂ)) := by
  simp [nodeCoordinateChange_apply]

/-- Pullback along `nodeCoordinateChange`, as a ring automorphism of the holomorphic stalk at the
origin, which the coordinate change fixes. -/
private def nodeCoordinateStalkEquiv (b : E) :
    (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0) ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0) :=
  (RingEquiv.cast (R := fun p ↦
    (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk p)
    (nodeCoordinateChange_origin b)).trans
    (nodeCoordinateChange.holomorphicStalkEquiv ((b, 0), 0))

/-- The stalk automorphism composes representatives with the coordinate change. -/
private theorem toFilterGerm_nodeCoordinateStalkEquiv {b : E}
    {g : (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0)}
    {f : (E × ℂ) × ℂ → ℂ}
    (hg : toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, 0), 0) (𝓝 ((b, 0), 0)) le_rfl g = f) :
    toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, 0), 0) (𝓝 ((b, 0), 0)) le_rfl
        (nodeCoordinateStalkEquiv b g) = (f ∘ nodeCoordinateChange : (E × ℂ) × ℂ → ℂ) := by
  rw [nodeCoordinateStalkEquiv, RingEquiv.trans_apply, Diffeomorph.holomorphicStalkEquiv_apply,
    toFilterGerm_stalkPrecomp, toFilterGerm_ringEquivCast _ hg, Germ.coe_compTendsto]

/-- The coordinate change carries the node equation to its normal form. -/
private theorem nodeCoordinateStalkEquiv_nodeEquation (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    nodeCoordinateStalkEquiv b (nodeEquation b 0 0 s) =
      evalVertical (b, (0 : ℂ)) 0 (nodeNormalForm b s) := by
  obtain ⟨f, _, hfs⟩ := exists_toFilterGerm_eq b s
  apply toFilterGerm_nhds_injective ((b, (0 : ℂ)), 0)
  rw [toFilterGerm_nodeCoordinateStalkEquiv (toFilterGerm_nodeEquation b 0 0 s (hfs _ le_rfl))]
  simp only [nodeNormalForm, map_sub, map_pow, map_add, evalVertical_X, evalVertical_C,
    toFilterGerm_germOfContMDiff, toFilterGerm_stalkPrecomp, hfs _ le_rfl,
    Germ.coe_compTendsto, ← Germ.coe_add, ← Germ.coe_pow, ← Germ.coe_sub]
  congr 1
  funext p
  simp only [Function.comp_apply, nodeCoordinateChange_apply, sub_zero,
    Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
  ring

/-- The coordinate change fixes germs pulled back from the base `E`. -/
private theorem nodeCoordinateStalkEquiv_stalkPrecomp (b : E)
    (a : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    nodeCoordinateStalkEquiv b (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) (fun z ↦ z.1.1)
        (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, 0), 0) a) =
      stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) (fun z ↦ z.1.1)
        (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, 0), 0) a := by
  obtain ⟨f, _, hfa⟩ := exists_toFilterGerm_eq b a
  apply toFilterGerm_nhds_injective ((b, (0 : ℂ)), 0)
  rw [toFilterGerm_nodeCoordinateStalkEquiv (by rw [toFilterGerm_stalkPrecomp, hfa _ le_rfl,
    Germ.coe_compTendsto]), toFilterGerm_stalkPrecomp, hfa _ le_rfl, Germ.coe_compTendsto]
  -- The coordinate change preserves the base coordinate on the nose.
  rfl

/-! ### The local ring of the node in normal form -/

/-- **The node in Weierstrass normal form.** The coordinate change `x = u + v`, `y = u - v`
identifies the local ring `𝒪 ⧸ (xy - s(b))` of the node `((b, 0), 0)` with the quotient
`𝒪 ⧸ (u² - (v² + s(b)))` by the normal form, read as a polynomial in the vertical coordinate `u`
with coefficients in the transverse coordinates `(b, v)`. -/
def nodeQuotientEquiv (b : E) (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    ((holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0) ⧸
        Ideal.span {nodeEquation b 0 0 s}) ≃+*
      ((holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0) ⧸
        Ideal.span {evalVertical (b, (0 : ℂ)) 0 (nodeNormalForm b s)}) :=
  Ideal.quotientEquiv _ _ (nodeCoordinateStalkEquiv b) (by
    rw [Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom,
      nodeCoordinateStalkEquiv_nodeEquation])

/-- The isomorphism `nodeQuotientEquiv` sends the class of a germ represented by `f` near the
node to the class of the germ of `((b, v), u) ↦ f ((b, u + v), u - v)`. -/
theorem nodeQuotientEquiv_mk {b : E} {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b}
    {g g' :
      (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0)}
    {f : (E × ℂ) × ℂ → ℂ}
    (hg : toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, 0), 0) (𝓝 ((b, 0), 0)) le_rfl g = f)
    (hg' : toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, 0), 0) (𝓝 ((b, 0), 0)) le_rfl g' =
      (fun z : (E × ℂ) × ℂ ↦ f ((z.1.1, z.2 + z.1.2), z.2 - z.1.2))) :
    nodeQuotientEquiv b s (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ g' := by
  rw [nodeQuotientEquiv, Ideal.quotientEquiv_mk]
  congr 1
  apply toFilterGerm_nhds_injective ((b, (0 : ℂ)), 0)
  rw [toFilterGerm_nodeCoordinateStalkEquiv hg, hg']
  -- `f ∘ nodeCoordinateChange` is the displayed function by `nodeCoordinateChange_apply`.
  rfl

/-- The structure map of the local ring of the node over the holomorphic germs at `(b, 0)` in the
transverse coordinates `(b, v)`, with `v = (x - y) / 2` (`nodeTransverseHom_eq_mk`). Under
`nodeQuotientEquiv` it is pullback along the projection `((b, v), u) ↦ (b, v)`. -/
def nodeTransverseHom (b : E) (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0) →+*
      (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0) ⧸
        Ideal.span {nodeEquation b 0 0 s} :=
  (nodeQuotientEquiv b s).symm.toRingHom.comp ((Ideal.Quotient.mk _).comp
    (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) Prod.fst
      (contMDiff_iff_contDiff.mpr contDiff_fst) ((b, 0), 0)))

/-- Under `nodeQuotientEquiv`, the structure map is pullback along `((b, v), u) ↦ (b, v)`. -/
@[simp]
theorem nodeQuotientEquiv_nodeTransverseHom (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b)
    (a : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0)) :
    nodeQuotientEquiv b s (nodeTransverseHom b s a) = Ideal.Quotient.mk _
      (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) Prod.fst
        (contMDiff_iff_contDiff.mpr contDiff_fst) ((b, 0), 0) a) := by
  simp [nodeTransverseHom]

/-- The structure map sends a germ represented by `f` near `(b, 0)` to the class of the germ of
`((b, x), y) ↦ f (b, (x - y) / 2)`. -/
theorem nodeTransverseHom_eq_mk {b : E}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b}
    {a : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0)}
    {q : (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0)}
    {f : E × ℂ → ℂ} (ha : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (b, 0) (𝓝 (b, 0)) le_rfl a = f)
    (hq : toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, 0), 0) (𝓝 ((b, 0), 0)) le_rfl q =
      (fun z : (E × ℂ) × ℂ ↦ f (z.1.1, (z.1.2 - z.2) / 2))) :
    nodeTransverseHom b s a = Ideal.Quotient.mk _ q := by
  apply (nodeQuotientEquiv b s).injective
  rw [nodeQuotientEquiv_nodeTransverseHom, nodeQuotientEquiv_mk hq]
  rw [toFilterGerm_stalkPrecomp, ha, Germ.coe_compTendsto]
  congr 1
  funext z
  simp only [Function.comp_apply]
  congr 1
  ext
  · rfl
  · ring

/-- The structure map extends pullback of base germs along `((b, x), y) ↦ b`: the local ring of
the node is an algebra over the base `𝒪_{E, b}` through `𝒪_{E × ℂ, (b, 0)}`. -/
theorem nodeTransverseHom_comp_stalkPrecomp_fst (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (nodeTransverseHom b s).comp (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst
        (contMDiff_iff_contDiff.mpr contDiff_fst) (b, 0)) =
      (Ideal.Quotient.mk _).comp (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) (fun z ↦ z.1.1)
        (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, 0), 0)) := by
  ext a
  apply (nodeQuotientEquiv b s).injective
  rw [RingHom.comp_apply, nodeQuotientEquiv_nodeTransverseHom, RingHom.comp_apply,
    nodeQuotientEquiv, Ideal.quotientEquiv_mk,
    nodeCoordinateStalkEquiv_stalkPrecomp, ← stalkPrecomp_comp]
  -- `Prod.fst ∘ Prod.fst` is the projection `fun z ↦ z.1.1`.
  rfl

/-- The normal form is monic, so its vertical slice does not vanish identically. -/
private theorem map_residue_verticalPowerSeries_nodeNormalForm_ne_zero (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (verticalPowerSeries (b, (0 : ℂ)) 0 (evalVertical (b, 0) 0 (nodeNormalForm b s))).map
      (IsLocalRing.residue _) ≠ 0 := by
  rw [verticalPowerSeries_evalVertical, ← Polynomial.polynomial_map_coe, Ne,
    Polynomial.coe_eq_zero_iff]
  exact ((monic_nodeNormalForm b s).map _).ne_zero

variable [FiniteDimensional ℂ E]

/-- **The node is flat over its transverse coordinates.** For every holomorphic base germ `s`,
the local ring of the node is a flat algebra over `𝒪_{E × ℂ, (b, 0)}`. -/
theorem nodeTransverseHom_flat (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (nodeTransverseHom b s).Flat :=
  (flat_quotientMk_comp_stalkPrecomp_fst _
    (map_residue_verticalPowerSeries_nodeNormalForm_ne_zero b s)).comp
    (RingHom.Flat.of_bijective (nodeQuotientEquiv b s).symm.bijective)

/-- **The node is finite over its transverse coordinates.** For every holomorphic base germ `s`,
the local ring of the node is a finite algebra over `𝒪_{E × ℂ, (b, 0)}`. -/
theorem nodeTransverseHom_finite (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (nodeTransverseHom b s).Finite :=
  RingHom.Finite.comp
    (RingHom.Finite.of_surjective _ (nodeQuotientEquiv b s).symm.surjective)
    (finite_quotientMk_comp_stalkPrecomp_fst _
      (map_residue_verticalPowerSeries_nodeNormalForm_ne_zero b s))

/-- **The node is free of rank two over its transverse coordinates.** If `s(b) = 0`, every
element of the local ring of the node is uniquely `α + β u` with `α` and `β` in the image of
`nodeTransverseHom`, where `u` is the class of `(x + y) / 2`. -/
theorem bijective_nodeTransverseHom_add_mul {b : E}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b}
    (hs : eval 𝓘(ℂ, E) E b s = 0) :
    Function.Bijective fun c :
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0) ×
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0) ↦
      nodeTransverseHom b s c.1 + nodeTransverseHom b s c.2 *
        Ideal.Quotient.mk _ (germOfContMDiff (fun z : (E × ℂ) × ℂ ↦ (z.1.2 + z.2) / 2)
          (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, 0), 0)) := by
  -- `AdjoinRoot P` is by definition the quotient of the polynomial ring by `P`.
  let Ψ : AdjoinRoot (nodeNormalForm b s) ≃+* _ :=
    quotientEquivOfIsDistinguishedAt (b, (0 : ℂ)) 0 (isDistinguishedAt_nodeNormalForm hs)
  -- The quotient by the monic quadratic `P` has the basis `1, X`.
  let pb := AdjoinRoot.powerBasis' (monic_nodeNormalForm b s)
  let B := pb.basis.reindex (finCongr ((AdjoinRoot.powerBasis'_dim _).trans
    (natDegree_nodeNormalForm b s)))
  have hΨ (a : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0)) :
      Ψ (AdjoinRoot.of _ a) = Ideal.Quotient.mk _ (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)
        Prod.fst (contMDiff_iff_contDiff.mpr contDiff_fst) ((b, 0), 0) a) :=
    RingHom.congr_fun (quotientEquivOfIsDistinguishedAt_comp_algebraMap _ _) a
  have hu : nodeQuotientEquiv b s (Ideal.Quotient.mk _ (germOfContMDiff
      (fun z : (E × ℂ) × ℂ ↦ (z.1.2 + z.2) / 2) (contMDiff_iff_contDiff.mpr (by fun_prop))
        ((b, 0), 0))) = Ψ (AdjoinRoot.root (nodeNormalForm b s)) := by
    refine (nodeQuotientEquiv_mk (g' := evalVertical (b, (0 : ℂ)) 0 X)
      (toFilterGerm_germOfContMDiff _ _ le_rfl) ?_).trans
        (quotientEquivOfIsDistinguishedAt_mk _ _ _ X).symm
    rw [evalVertical_X, toFilterGerm_germOfContMDiff]
    congr 1
    funext z
    ring
  have hB (c : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0) ×
      (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0)) :
      B.equivFun.symm ((finTwoArrowEquiv _).symm c) =
        AdjoinRoot.of _ c.1 + AdjoinRoot.of _ c.2 * AdjoinRoot.root (nodeNormalForm b s) := by
    simp [B, pb, Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, Algebra.smul_def]
  convert (nodeQuotientEquiv b s).symm.bijective.comp (Ψ.bijective.comp
    (B.equivFun.symm.bijective.comp (finTwoArrowEquiv _).symm.bijective)) using 1
  funext c
  apply (nodeQuotientEquiv b s).injective
  simp only [Function.comp_apply, RingEquiv.apply_symm_apply]
  rw [map_add, map_mul, hu, nodeQuotientEquiv_nodeTransverseHom,
    nodeQuotientEquiv_nodeTransverseHom, hB, map_add, map_mul, hΨ, hΨ]

end TauCeti.holomorphicStructureSheaf
