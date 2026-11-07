/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Cartan
public import TauCeti.Geometry.Lie.Exponential.Matrix.SpecialLinear

/-!
# The Cartan decomposition of `GL(n, 𝕜)` and `SL(n, 𝕜)` for `𝕜 = ℝ` or `ℂ`

Over `𝕜 = ℝ` or `ℂ`, every invertible matrix `g` factors uniquely as `g = k * exp X` with `k`
unitary (orthogonal when `𝕜 = ℝ`) and `X` Hermitian (symmetric when `𝕜 = ℝ`), and both factors
depend continuously on `g`. In Lie-theoretic terms, `𝔤𝔩(n, 𝕜) = 𝔨 ⊕ 𝔭` is the eigenspace
decomposition of the Cartan involution `X ↦ -Xᴴ`, with `𝔨` the skew-Hermitian and `𝔭` the Hermitian
matrices, and the map `K × 𝔭 → G`, `(k, X) ↦ k * exp X`, is a homeomorphism from the product of the
maximal compact subgroup `K = U(n, 𝕜)` and the vector space `𝔭` onto `G = GL(n, 𝕜)`.

This file specializes `TauCeti.cartanHomeomorph`, stated for complete normed real algebras with an
isometric continuous functional calculus, to matrices. Those structures exist on `Matrix n n 𝕜` only
for the scoped `ℓ²` operator norm, so the specialization is stated here for the default (entrywise)
topology, which that norm induces.

The decomposition restricts to the special linear group: `SL(n, 𝕜) = SU(n, 𝕜) · exp 𝔭₀`, where
`𝔭₀` is the space of trace-free Hermitian matrices, the Hermitian part of `𝔰𝔩(n, 𝕜)`. Indeed
`det (k * exp X) = det k * exp (trace X)` with `|det k| = 1` and `exp (trace X) > 0`, so a product
of determinant one has both factors of determinant one. This is the instance of
`Subgroup.cartanHomeomorph` for the subgroup of determinant-one matrices, which is closed
under conjugate transpose and contains the whole line `exp (t X)` once it contains `exp X`.

## Main declarations

* `Matrix.GeneralLinearGroup.cartanHomeomorph`: the homeomorphism
  `unitaryGroup n 𝕜 × selfAdjoint (Matrix n n 𝕜) ≃ₜ GL n 𝕜`, `(k, X) ↦ k * exp X`.
* `Matrix.GeneralLinearGroup.val_cartanHomeomorph_apply`,
  `Matrix.GeneralLinearGroup.cartanHomeomorph_symm_apply_fst`,
  `Matrix.GeneralLinearGroup.coe_cartanHomeomorph_symm_apply_snd`: the map and its inverse, whose
  factors are the unitary polar factor `g.polarUnitary` and the logarithm `log √(gᴴ g)` of the
  positive polar factor, written `cfc Real.log`.
* `Matrix.SpecialLinearGroup.cartanHomeomorph`: the homeomorphism
  `specialUnitaryGroup n 𝕜 × {X ∈ selfAdjoint (Matrix n n 𝕜) | trace X = 0} ≃ₜ SL n 𝕜`,
  `(k, X) ↦ k * exp X`, with `Matrix.SpecialLinearGroup.val_cartanHomeomorph_apply`,
  `Matrix.SpecialLinearGroup.coe_cartanHomeomorph_symm_apply_fst` and
  `Matrix.SpecialLinearGroup.coe_cartanHomeomorph_symm_apply_snd` computing it and its inverse.

## References

* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 1.
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open scoped MatrixOrder

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

variable (n 𝕜) in
/-- **The Cartan decomposition of `GL(n, 𝕜)`**, for `𝕜 = ℝ` or `ℂ`: the map `(k, X) ↦ k * exp X` is
a homeomorphism from the product of the unitary group (the orthogonal group when `𝕜 = ℝ`) and the
Hermitian (symmetric) matrices onto the general linear group. -/
def cartanHomeomorph : unitaryGroup n 𝕜 × selfAdjoint (Matrix n n 𝕜) ≃ₜ GL n 𝕜 := by
  -- The general statement needs a complete normed `ℝ`-algebra with an isometric functional
  -- calculus, which `Matrix n n 𝕜` is for the scoped `ℓ²` operator norm.
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  exact TauCeti.cartanHomeomorph (Matrix n n 𝕜)

/-- The Cartan decomposition map of `GL(n, 𝕜)` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanHomeomorph_apply (p : unitaryGroup n 𝕜 × selfAdjoint (Matrix n n 𝕜)) :
    (cartanHomeomorph n 𝕜 p : Matrix n n 𝕜) = p.1 * NormedSpace.exp (p.2 : Matrix n n 𝕜) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  exact TauCeti.val_cartanHomeomorph_apply p

/-- The unitary factor of the Cartan decomposition of `g` is its polar unitary factor. -/
@[simp]
theorem cartanHomeomorph_symm_apply_fst (g : GL n 𝕜) :
    ((cartanHomeomorph n 𝕜).symm g).1 = g.polarUnitary := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  exact TauCeti.cartanHomeomorph_symm_apply_fst g

/-- The Hermitian factor of the Cartan decomposition of `g` is the logarithm of `√(gᴴ g)`. -/
@[simp]
theorem coe_cartanHomeomorph_symm_apply_snd (g : GL n 𝕜) :
    (((cartanHomeomorph n 𝕜).symm g).2 : Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star (g : Matrix n n 𝕜) * g)) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  -- `CFC.log` is `cfc Real.log`; it is only defined for normed algebras, and matrices carry a
  -- norm only in the `ℓ²` operator norm scope, so the statement uses `cfc Real.log` directly.
  exact TauCeti.coe_cartanHomeomorph_symm_apply_snd g

end Matrix.GeneralLinearGroup

namespace Matrix.SpecialLinearGroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

-- `TauCeti.expUnit` is stated for normed `ℚ`-algebras; the `ℓ²` operator norm gives a normed
-- `ℝ`-algebra, whose scalars this instance restricts.
attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable (n 𝕜) in
/-- **The Cartan decomposition of `SL(n, 𝕜)`**, for `𝕜 = ℝ` or `ℂ`: the map `(k, X) ↦ k * exp X` is
a homeomorphism from the product of the special unitary group (the special orthogonal group when
`𝕜 = ℝ`) and the trace-free Hermitian (symmetric) matrices onto the special linear group.

It is the restriction of the Cartan decomposition of `GL(n, 𝕜)` to the determinant-one matrices,
which form a subgroup closed under conjugate transpose whose Hermitian Lie algebra elements are the
trace-free Hermitian matrices (`Subgroup.cartanHomeomorph`). -/
def cartanHomeomorph :
    specialUnitaryGroup n 𝕜 × {X : selfAdjoint (Matrix n n 𝕜) // (X : Matrix n n 𝕜).trace = 0} ≃ₜ
      SpecialLinearGroup n 𝕜 := by
  -- The general statement needs a complete normed `ℝ`-algebra with an isometric functional
  -- calculus, which `Matrix n n 𝕜` is for the scoped `ℓ²` operator norm.
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  let G := (GeneralLinearGroup.det : GL n 𝕜 →* 𝕜ˣ).ker
  have hG (g : GL n 𝕜) : g ∈ G ↔ (g : Matrix n n 𝕜).det = 1 := by
    simp [G, Units.ext_iff]
  have hstar (g : GL n 𝕜) (hg : g ∈ G) : star g ∈ G := by
    rw [hG] at hg ⊢
    rw [Units.coe_star, star_eq_conjTranspose, det_conjTranspose, hg, star_one]
  have hexpG {x : Matrix n n 𝕜} (hx : IsSelfAdjoint x) : TauCeti.expUnit x ∈ G ↔ x.trace = 0 := by
    rw [hG, TauCeti.expUnit_coe]
    exact hx.isHermitian.det_exp_eq_one_iff
  have hline (x : Matrix n n 𝕜) : (∀ t : ℝ, TauCeti.expUnit (t • x) ∈ G) ↔ x.trace = 0 := by
    simp only [hG, TauCeti.expUnit_coe]
    exact (forall_det_exp_smul_eq_one_iff_mem_sl x).trans LieAlgebra.SpecialLinear.mem_sl_iff
  let eK : specialUnitaryGroup n 𝕜 ≃ₜ {u : unitaryGroup n 𝕜 // Unitary.toUnits u ∈ G} :=
    { toFun k := ⟨⟨k, (mem_specialUnitaryGroup_iff.1 k.2).1⟩,
        (hG _).2 (mem_specialUnitaryGroup_iff.1 k.2).2⟩
      invFun u := ⟨u.1, mem_specialUnitaryGroup_iff.2 ⟨u.1.2, (hG _).1 u.2⟩⟩
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let eP : {X : selfAdjoint (Matrix n n 𝕜) // (X : Matrix n n 𝕜).trace = 0} ≃ₜ
      {x : selfAdjoint (Matrix n n 𝕜) // ∀ t : ℝ, TauCeti.expUnit (t • (x : Matrix n n 𝕜)) ∈ G} :=
    { toFun X := ⟨X.1, (hline _).2 X.2⟩
      invFun x := ⟨x.1, (hline _).1 x.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  let eSL : G ≃ₜ SpecialLinearGroup n 𝕜 :=
    { toEquiv := toGLKerEquiv.symm.toEquiv
      continuous_toFun := (Units.continuous_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := continuous_toGL.subtype_mk _ }
  exact (eK.prodCongr eP).trans
    ((G.cartanHomeomorph hstar fun x hx h ↦ (hline x).2 ((hexpG hx).1 h)).trans eSL)

/-- The Cartan decomposition map of `SL(n, 𝕜)` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanHomeomorph_apply
    (p : specialUnitaryGroup n 𝕜 ×
      {X : selfAdjoint (Matrix n n 𝕜) // (X : Matrix n n 𝕜).trace = 0}) :
    (cartanHomeomorph n 𝕜 p : Matrix n n 𝕜) =
      p.1 * NormedSpace.exp ((p.2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  simp [cartanHomeomorph]

/-- The special unitary factor of the Cartan decomposition of `g` is the polar unitary factor
of `g`. -/
@[simp]
theorem coe_cartanHomeomorph_symm_apply_fst (g : SpecialLinearGroup n 𝕜) :
    (((cartanHomeomorph n 𝕜).symm g).1 : Matrix n n 𝕜) = (toGL g).polarUnitary := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  simp [cartanHomeomorph]

/-- The trace-free Hermitian factor of the Cartan decomposition of `g` is the logarithm of
`√(gᴴ g)`. -/
@[simp]
theorem coe_cartanHomeomorph_symm_apply_snd (g : SpecialLinearGroup n 𝕜) :
    ((((cartanHomeomorph n 𝕜).symm g).2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star (g : Matrix n n 𝕜) * g)) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  -- `CFC.log` is `cfc Real.log`; it is only defined for normed algebras, and matrices carry a
  -- norm only in the `ℓ²` operator norm scope, so the statement uses `cfc Real.log` directly.
  simp [cartanHomeomorph, CFC.log]

end Matrix.SpecialLinearGroup
