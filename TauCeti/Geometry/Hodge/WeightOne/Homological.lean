/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Tate.Twist
public import TauCeti.Geometry.Hodge.WeightOne.Lattice
import TauCeti.LinearAlgebra.Eigenspace.Smul

/-!
# The homological Hodge structure of a lattice with a complex structure

For a complex torus `V_ℝ / Λ`, the lattice `Λ = H₁` carries the **homological** Hodge structure:
weight `-1`, with `H^{-1,0}` the `+i`-eigenspace of the complex structure `J` and `H^{0,-1}` the
`-i`-eigenspace. Its Weil operator is `C = -J`. It is the Tate twist by one of the effective
weight-one structure `TauCeti.AlmostComplexStructure.latticeHodgeStructure` of `-J`.

The construction follows the Stanford VIGRE notes, *Complex theory of abelian varieties*,
Definitions 1.13–1.14, and Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.

## Main declarations

* `TauCeti.AlmostComplexStructure.RiemannForm.homological`: the weight `-1` Hodge structure, with
  `homological_def` identifying it with the Tate twist.
* `TauCeti.AlmostComplexStructure.RiemannForm.homological_F`: its Hodge filtration is `⊤` in
  degrees `≤ -1`, the `-i`-eigenspace of `J` in degree `0`, and `⊥` above.
* `TauCeti.AlmostComplexStructure.RiemannForm.homological_piece_neg_one`,
  `TauCeti.AlmostComplexStructure.RiemannForm.homological_piece_zero`: `H^{-1,0}` and `H^{0,-1}`
  are the `+i`- and `-i`-eigenspaces of `J`.
* `TauCeti.AlmostComplexStructure.RiemannForm.homological_weilOperator`: the Weil operator is
  `-J`.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

namespace RiemannForm

variable (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ)

/-- The **homological Hodge structure** of a lattice with a complex structure `J` on its
realification: the weight `-1` structure on `Λ = H₁` with `H^{-1,0}` the `+i`-eigenspace of `J`
(`homological_piece_neg_one`) and Weil operator `-J` (`homological_weilOperator`). It is the Tate
twist by one of the weight-one structure of `-J`. -/
noncomputable def homological : Hodge.HodgeStructure hℂ (-1) :=
  ((-J).latticeHodgeStructure hℂ).tateTwist 1

/-- The homological structure is the Tate twist by one of the weight-one structure of `-J`. -/
theorem homological_def : homological J hℂ = ((-J).latticeHodgeStructure hℂ).tateTwist 1 :=
  (rfl)

/-- The Hodge filtration of the homological structure is top in degrees at most `-1`, the
`-i`-eigenspace of `J` in degree zero, and bottom in positive degrees. -/
@[simp]
theorem homological_F (p : ℤ) :
    (homological J hℂ).F p = if p ≤ -1 then ⊤ else if p = 0 then
      Module.End.eigenspace (J.latticeComplexification hℂ) (-Complex.I) else ⊥ := by
  rw [homological_def, Hodge.HodgeStructureOn.tateTwist_F, latticeHodgeStructure_F,
    latticeComplexification_neg, Module.End.eigenspace_neg]
  split_ifs <;> first | rfl | omega

/-- The Hodge components of the homological structure are those of the weight-one structure of
`-J`, shifted by one. -/
theorem homological_piece (p : ℤ) :
    (homological J hℂ).piece p = ((-J).latticeHodgeStructure hℂ).piece (p + 1) := by
  rw [homological_def, Hodge.HodgeStructureOn.tateTwist_piece]

/-- The component `H^{-1,0}` of the homological structure is the `+i`-eigenspace of `J`. -/
@[simp]
theorem homological_piece_neg_one :
    (homological J hℂ).piece (-1) =
      Module.End.eigenspace (J.latticeComplexification hℂ) Complex.I := by
  rw [homological_piece, neg_add_cancel, latticeHodgeStructure_piece_zero,
    latticeComplexification_neg]
  simp [Module.End.eigenspace_neg]

/-- The component `H^{0,-1}` of the homological structure is the `-i`-eigenspace of `J`. -/
@[simp]
theorem homological_piece_zero :
    (homological J hℂ).piece 0 =
      Module.End.eigenspace (J.latticeComplexification hℂ) (-Complex.I) := by
  rw [homological_piece, zero_add, latticeHodgeStructure_piece_one, latticeComplexification_neg,
    Module.End.eigenspace_neg]

/-- Every Hodge component of the homological structure other than `H^{-1,0}` and `H^{0,-1}`
vanishes. -/
theorem homological_piece_eq_bot {p : ℤ} (hp : p ≠ -1) (hp' : p ≠ 0) :
    (homological J hℂ).piece p = ⊥ := by
  rw [homological_piece]
  exact (-J).latticeHodgeStructure_piece_eq_bot hℂ (by omega) (by omega)

/-- **The Weil operator of the homological structure is `C = -J`.** -/
@[simp]
theorem homological_weilOperator :
    (homological J hℂ).weilOperator = -J.latticeComplexification hℂ := by
  rw [homological_def, Hodge.HodgeStructureOn.tateTwist_weilOperator,
    latticeHodgeStructure_weilOperator, latticeComplexification_neg]

end RiemannForm

end TauCeti.AlmostComplexStructure
