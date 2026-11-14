/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan
public import TauCeti.Analysis.Matrix.Exponential.Log
public import TauCeti.Analysis.Matrix.Polar.GLSymplectic
public import TauCeti.Geometry.Lie.Exponential.Matrix.Symplectic
public import TauCeti.Topology.Algebra.Matrix.Realify

/-!
# Cartan decompositions of the real symplectic group and of the realified `GL(n, ℂ)`

Two closed subgroups `H` of `GL(2n, ℝ) = GL (n ⊕ n) ℝ` have the realified unitary group `U(n)` as
their orthogonal part `H ∩ O(2n)`: the real symplectic group `Sp(2n, ℝ)`
(`TauCeti.GLSymplectic.inf_unitarySubgroup`) and the realification `C_ℝ` of `GL(n, ℂ)`, the
invertible real matrices commuting with `J`
(`Matrix.GeneralLinearGroup.unitarySubgroup_inf_range_realify`).
Both are stable under transposition (`TauCeti.GLSymplectic.star_mem`,
`Matrix.GeneralLinearGroup.star_mem_range_realify`). This file proves their global Cartan
decompositions

`U(n) × 𝔭_H ≃ₜ H`,  `(U, X) ↦ realify U * exp X`,

where `𝔭_H` is the space of symmetric matrices in the Lie algebra of `H`: the symmetric matrices in
the symplectic Lie algebra `𝔰𝔭(2n, ℝ)` for `H = Sp(2n, ℝ)`, and the symmetric matrices commuting
with `J` for `H = C_ℝ`. The unitary factor of `A ∈ H` is the orthogonal polar factor of `A`, so for
`Sp(2n, ℝ)` it is the factor `TauCeti.GLSymplectic.polarUnitary` of the direct polar argument,
and the symmetric factor is the logarithm `log √(Aᵀ A)` of its positive polar factor.

Both decompositions instantiate `Subgroup.cartanHomeomorph`, which needs two inputs. The subgroup
must be closed under transposition, and an exponential `exp X` of a symmetric matrix `X` may lie
in `H` only when the whole line `exp (t X)` does. The second input holds because the logarithm
inverts the exponential on symmetric matrices:

* `exp X` commutes with `J` exactly when `X` does, since `X = log (exp X)` lies in the functional
  calculus of `exp X` (`Matrix.IsHermitian.commute_exp_iff`);
* `exp X` is symplectic exactly when `X ∈ 𝔰𝔭(2n, ℝ)`, since then
  `exp X = (exp X)ᵀ = J (exp X)⁻¹ J⁻¹ = exp (J (-X) J⁻¹)` with `J (-X) J⁻¹` symmetric, as `J` is
  orthogonal, and the exponential is injective on symmetric matrices
  (`Matrix.IsHermitian.exp_mem_symplecticGroup_iff`).

The compact factor `{u ∈ O(2n) | u ∈ H}` produced by the generic theorem is then identified with
`U(n)` by realification (`Matrix.GeneralLinearGroup.realifyUnitaryHomeomorph`).

## Main results

* `TauCeti.GLSymplectic.cartanHomeomorph`: the Cartan decomposition
  `U(n) × (𝔰𝔭(2n, ℝ) ∩ Sym) ≃ₜ Sp(2n, ℝ)`, with
  `TauCeti.GLSymplectic.unitaryGroupEquivSymplecticInfOrthogonal_cartanHomeomorph_symm_apply_fst`
  comparing its unitary factor with `TauCeti.GLSymplectic.polarUnitary`.
* `Matrix.GeneralLinearGroup.realifyCartanHomeomorph`: the Cartan decomposition
  `U(n) × {X ∈ Sym | J X = X J} ≃ₜ C_ℝ`.

## References

* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I, Section 17 (global Cartan decomposition of a closed linear
  group stable under transpose) and Chapter VI, Section 2.
* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2 (Proposition 2.2.4
  and Lemma 2.2.11 on `Sp(2n, ℝ) ∩ O(2n) = U(n)` and polar factors of symplectic matrices).
-/

public section

noncomputable section

open TauCeti
open scoped MatrixOrder

open Matrix Matrix.GeneralLinearGroup

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

-- `TauCeti.expUnit` is stated for normed `ℚ`-algebras; the `ℓ²` operator norm gives a normed
-- `ℝ`-algebra, whose scalars this instance restricts.
attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable (n) in
/-- **The Cartan decomposition of the real symplectic group**: the map
`(U, X) ↦ realify U * exp X` is a homeomorphism from the product of the unitary group `U(n)` and
the symmetric matrices in the symplectic Lie algebra `𝔰𝔭(2n, ℝ)` onto `Sp(2n, ℝ)`.

The unitary factor of `A` is its orthogonal polar factor `TauCeti.GLSymplectic.polarUnitary`
(`TauCeti.GLSymplectic.unitaryGroupEquivSymplecticInfOrthogonal_cartanHomeomorph_symm_apply_fst`),
and the symmetric factor is the logarithm of its positive polar factor `√(Aᵀ A)`. -/
def cartanHomeomorph :
    unitaryGroup n ℂ × {X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ) //
        (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) ∈ LieAlgebra.Symplectic.sp n ℝ} ≃ₜ
      GLSymplectic n ℝ := by
  -- The general statement needs a complete normed `ℝ`-algebra with an isometric functional
  -- calculus, which `Matrix (n ⊕ n) (n ⊕ n) ℝ` is for the scoped `ℓ²` operator norm.
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n ⊕ n) (𝕜 := ℝ)
  have hline (x : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
      (∀ t : ℝ, expUnit (t • x) ∈ GLSymplectic n ℝ) ↔ x ∈ LieAlgebra.Symplectic.sp n ℝ := by
    simp only [mem_iff_mem_symplecticGroup, expUnit_coe]
    exact forall_exp_smul_mem_symplecticGroup_iff_mem_sp x
  let eP : {X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ) //
        (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) ∈ LieAlgebra.Symplectic.sp n ℝ} ≃ₜ
      {x : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ) //
        ∀ t : ℝ, expUnit (t • (x : Matrix (n ⊕ n) (n ⊕ n) ℝ)) ∈ GLSymplectic n ℝ} :=
    { toFun X := ⟨X.1, (hline _).2 X.2⟩
      invFun x := ⟨x.1, (hline _).1 x.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  exact ((realifyUnitaryHomeomorph inf_unitarySubgroup).prodCongr eP).trans
    ((GLSymplectic n ℝ).cartanHomeomorph (fun _ ↦ star_mem) fun x hx h ↦ (hline x).2
      ((IsHermitian.exp_mem_symplecticGroup_iff hx.isHermitian).1 (by simpa using h)))

/-- The Cartan decomposition map of `Sp(2n, ℝ)` sends `(U, X)` to `realify U * exp X`. -/
@[simp]
theorem val_cartanHomeomorph_apply
    (p : unitaryGroup n ℂ × {X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ) //
      (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) ∈ LieAlgebra.Symplectic.sp n ℝ}) :
    ((cartanHomeomorph n p : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (p.1 : Matrix n n ℂ).realify *
        NormedSpace.exp
          ((p.2 : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ)) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n ⊕ n) (𝕜 := ℝ)
  simp [cartanHomeomorph]

/-- The unitary factor of the Cartan decomposition of `A ∈ Sp(2n, ℝ)` realifies to the orthogonal
polar factor of `A`. -/
@[simp]
theorem realify_cartanHomeomorph_symm_apply_fst (A : GLSymplectic n ℝ) :
    ((((cartanHomeomorph n).symm A).1 : unitaryGroup n ℂ) : Matrix n n ℂ).realify =
      ((A : GL (n ⊕ n) ℝ).polarUnitary : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n ⊕ n) (𝕜 := ℝ)
  simp [cartanHomeomorph]

/-- The unitary factor of the Cartan decomposition of `A ∈ Sp(2n, ℝ)` is the orthogonal polar
factor `TauCeti.GLSymplectic.polarUnitary A`, under the identification
`Matrix.unitaryGroupEquivSymplecticInfOrthogonal` of `U(n)` with `Sp(2n, ℝ) ∩ O(2n)`. -/
theorem unitaryGroupEquivSymplecticInfOrthogonal_cartanHomeomorph_symm_apply_fst
    (A : GLSymplectic n ℝ) :
    unitaryGroupEquivSymplecticInfOrthogonal ((cartanHomeomorph n).symm A).1 = polarUnitary A :=
  Subtype.ext (Units.ext (by simp))

/-- The symmetric factor of the Cartan decomposition of `A ∈ Sp(2n, ℝ)` is the logarithm of its
positive polar factor `√(Aᵀ A)`. -/
@[simp]
theorem coe_cartanHomeomorph_symm_apply_snd (A : GLSymplectic n ℝ) :
    ((((cartanHomeomorph n).symm A).2 : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ)) :
        Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      cfc Real.log (CFC.sqrt (star ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n ⊕ n) (𝕜 := ℝ)
  simp [cartanHomeomorph, CFC.log]

end TauCeti.GLSymplectic

namespace Matrix.GeneralLinearGroup

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

-- `TauCeti.expUnit` is stated for normed `ℚ`-algebras; the `ℓ²` operator norm gives a normed
-- `ℝ`-algebra, whose scalars this instance restricts.
attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable (n) in
/-- **The Cartan decomposition of the realified complex general linear group**: the map
`(U, X) ↦ realify U * exp X` is a homeomorphism from the product of the unitary group `U(n)` and
the symmetric real matrices commuting with `J` onto the subgroup of `GL (n ⊕ n) ℝ` of invertible
real matrices commuting with `J`, the realification of `GL(n, ℂ)`.

The unitary factor of `A` realifies to its orthogonal polar factor, and the symmetric factor is the
logarithm of its positive polar factor `√(Aᵀ A)`. -/
def realifyCartanHomeomorph :
    unitaryGroup n ℂ × {X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ) //
        Commute (J n ℝ) (X : Matrix (n ⊕ n) (n ⊕ n) ℝ)} ≃ₜ
      (realify n ℂ).range := by
  -- The general statement needs a complete normed `ℝ`-algebra with an isometric functional
  -- calculus, which `Matrix (n ⊕ n) (n ⊕ n) ℝ` is for the scoped `ℓ²` operator norm.
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n ⊕ n) (𝕜 := ℝ)
  have hline {x : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hx : x.IsHermitian) :
      (∀ t : ℝ, expUnit (t • x) ∈ (realify n ℂ).range) ↔ Commute (J n ℝ) x := by
    simp only [mem_range_realify_iff, expUnit_coe]
    exact ⟨fun h ↦ hx.commute_exp_iff.1 (by simpa using h 1),
      fun h t ↦ (h.smul_right t).exp_right⟩
  let eP : {X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ) //
        Commute (J n ℝ) (X : Matrix (n ⊕ n) (n ⊕ n) ℝ)} ≃ₜ
      {x : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ) //
        ∀ t : ℝ, expUnit (t • (x : Matrix (n ⊕ n) (n ⊕ n) ℝ)) ∈ (realify n ℂ).range} :=
    { toFun X := ⟨X.1, (hline (isHermitian_iff_isSelfAdjoint.2 X.1.2)).2 X.2⟩
      invFun x := ⟨x.1, (hline (isHermitian_iff_isSelfAdjoint.2 x.1.2)).1 x.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  exact ((realifyUnitaryHomeomorph (inf_comm (realify n ℂ).range _ ▸
      unitarySubgroup_inf_range_realify)).prodCongr eP).trans
    ((realify n ℂ).range.cartanHomeomorph (fun _ ↦ star_mem_range_realify) fun x hx h ↦
      (hline hx.isHermitian).2 ((IsHermitian.commute_exp_iff hx.isHermitian).1
        (by simpa using mem_range_realify_iff.1 h)))

/-- The Cartan decomposition map of the realified `GL(n, ℂ)` sends `(U, X)` to
`realify U * exp X`. -/
@[simp]
theorem val_realifyCartanHomeomorph_apply
    (p : unitaryGroup n ℂ × {X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ) //
      Commute (J n ℝ) (X : Matrix (n ⊕ n) (n ⊕ n) ℝ)}) :
    ((realifyCartanHomeomorph n p : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (p.1 : Matrix n n ℂ).realify *
        NormedSpace.exp
          ((p.2 : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ)) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n ⊕ n) (𝕜 := ℝ)
  simp [realifyCartanHomeomorph]

/-- The unitary factor of the Cartan decomposition of an element `A` of the realified `GL(n, ℂ)`
realifies to the orthogonal polar factor of `A`. -/
@[simp]
theorem realify_realifyCartanHomeomorph_symm_apply_fst (A : (realify n ℂ).range) :
    ((((realifyCartanHomeomorph n).symm A).1 : unitaryGroup n ℂ) : Matrix n n ℂ).realify =
      ((A : GL (n ⊕ n) ℝ).polarUnitary : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n ⊕ n) (𝕜 := ℝ)
  simp [realifyCartanHomeomorph]

/-- The symmetric factor of the Cartan decomposition of an element `A` of the realified
`GL(n, ℂ)` is the logarithm of its positive polar factor `√(Aᵀ A)`. -/
@[simp]
theorem coe_realifyCartanHomeomorph_symm_apply_snd (A : (realify n ℂ).range) :
    ((((realifyCartanHomeomorph n).symm A).2 : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℝ)) :
        Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      cfc Real.log (CFC.sqrt (star ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n ⊕ n) (𝕜 := ℝ)
  simp [realifyCartanHomeomorph, CFC.log]

end Matrix.GeneralLinearGroup
