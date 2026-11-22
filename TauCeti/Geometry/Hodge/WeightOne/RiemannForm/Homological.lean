/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Tate.Twist
public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm.Hermitian

/-!
# The homological Hodge structure of a lattice with a Riemann form

For a complex torus `V_ℝ / Λ`, the lattice `Λ = H₁` carries the **homological** Hodge structure:
weight `-1`, with `H^{-1,0}` the `+i`-eigenspace of the complex structure `J` and `H^{0,-1}` the
`-i`-eigenspace. Its Weil operator is `C = -J`, and a Riemann form `E` for `J` gives the
polarizing form `Q = -E` in Tau Ceti's sign convention `0 < Q (C x) x`: indeed
`Q (C v) v = E (J v) v > 0`.

This differs from `TauCeti.AlmostComplexStructure.latticeHodgeStructure`, which puts on the same
lattice the effective weight-one structure with Weil operator `J` and polarizing form `E`. The
homological structure is the Tate twist by one of the weight-one structure of `-J`; it is
polarized by `-E` because `-E` is a Riemann form for `-J`
(`TauCeti.AlmostComplexStructure.IsRiemannForm.neg`).

The construction follows the Stanford VIGRE notes, *Complex theory of abelian varieties*,
Definitions 1.13–1.14 and Lemma 1.16, and Voisin, *Hodge Theory and Complex Algebraic Geometry I*,
§7.1.

## Main declarations

* `TauCeti.AlmostComplexStructure.latticeComplexification_neg`: the transported extension of `-J`
  is minus that of `J`.
* `TauCeti.AlmostComplexStructure.RiemannForm.homological`: the weight `-1` Hodge structure.
* `TauCeti.AlmostComplexStructure.RiemannForm.homological_piece_neg_one`,
  `TauCeti.AlmostComplexStructure.RiemannForm.homological_piece_zero`: `H^{-1,0}` and `H^{0,-1}`
  are the `+i`- and `-i`-eigenspaces of `J`.
* `TauCeti.AlmostComplexStructure.RiemannForm.homological_weilOperator`: the Weil operator is
  `-J`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.isPolarization_homological`: a Riemann form `E`
  for `J` makes `-E` a polarization of the homological structure.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.homologicalPolarization`: the bundled
  polarization.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- The transported complex-linear extension of `-J` is minus that of `J`. -/
@[simp]
theorem latticeComplexification_neg (J : AlmostComplexStructure (Hodge.Realification V))
    (hℂ : IsBaseChange ℂ ιℂ) :
    (-J).latticeComplexification hℂ = -J.latticeComplexification hℂ := by
  ext x
  obtain ⟨y, rfl⟩ := (Hodge.realificationComplexEquiv hℂ).surjective x
  rw [LinearMap.neg_apply, ← realificationComplexEquiv_baseChange_apply,
    ← realificationComplexEquiv_baseChange_apply, neg_toLinearMap, LinearMap.baseChange_neg,
    LinearMap.neg_apply, map_neg]

namespace RiemannForm

variable (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ)

/-- The **homological Hodge structure** of a lattice with a complex structure `J` on its
realification: the weight `-1` structure on `Λ = H₁` with `H^{-1,0}` the `+i`-eigenspace of `J`
(`homological_piece_neg_one`) and Weil operator `-J` (`homological_weilOperator`). It is the Tate
twist by one of the weight-one structure of `-J`. -/
noncomputable def homological : Hodge.HodgeStructure hℂ (-1) :=
  ((-J).latticeHodgeStructure hℂ).tateTwist 1

/-- The Hodge filtration of the homological structure is that of the weight-one structure of `-J`,
shifted by one. -/
theorem homological_F (p : ℤ) :
    (homological J hℂ).F p = ((-J).latticeHodgeStructure hℂ).F (p + 1) := by
  rw [homological, Hodge.HodgeStructureOn.tateTwist_F]

/-- The Hodge components of the homological structure are those of the weight-one structure of
`-J`, shifted by one. -/
theorem homological_piece (p : ℤ) :
    (homological J hℂ).piece p = ((-J).latticeHodgeStructure hℂ).piece (p + 1) := by
  rw [homological, Hodge.HodgeStructureOn.tateTwist_piece]

/-- The eigenspaces of `-f` for `-μ` are those of `f` for `μ`. -/
private theorem eigenspace_neg_neg (f : Vℂ →ₗ[ℂ] Vℂ) (μ : ℂ) :
    Module.End.eigenspace (-f) (-μ) = Module.End.eigenspace f μ := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, LinearMap.neg_apply, neg_smul, neg_inj]

/-- The component `H^{-1,0}` of the homological structure is the `+i`-eigenspace of `J`. -/
@[simp]
theorem homological_piece_neg_one :
    (homological J hℂ).piece (-1) =
      Module.End.eigenspace (J.latticeComplexification hℂ) Complex.I := by
  rw [homological_piece, neg_add_cancel, latticeHodgeStructure_piece_zero,
    latticeComplexification_neg, eigenspace_neg_neg]

/-- The component `H^{0,-1}` of the homological structure is the `-i`-eigenspace of `J`. -/
@[simp]
theorem homological_piece_zero :
    (homological J hℂ).piece 0 =
      Module.End.eigenspace (J.latticeComplexification hℂ) (-Complex.I) := by
  rw [homological_piece, zero_add, latticeHodgeStructure_piece_one, latticeComplexification_neg,
    ← eigenspace_neg_neg, neg_neg]

/-- **The Weil operator of the homological structure is `C = -J`.** -/
@[simp]
theorem homological_weilOperator :
    (homological J hℂ).weilOperator = -J.latticeComplexification hℂ := by
  rw [← latticeComplexification_neg, ← latticeHodgeStructure_weilOperator]
  symm
  refine (homological J hℂ).weilOperator_unique _ fun p x hx ↦ ?_
  rw [homological_piece] at hx
  rw [((-J).latticeHodgeStructure hℂ).weilOperator_apply_of_mem hx]
  congr 2
  ring

end RiemannForm

namespace IsRiemannForm

variable {J : AlmostComplexStructure (Hodge.Realification V)} {E : LinearMap.BilinForm ℤ V}

/-- **A Riemann form `E` for `J` makes `Q = -E` a polarization of the homological Hodge
structure**, on a flat integral module. The sign is forced by the convention `0 < Q (C x) x` with
Weil operator `C = -J`: `Q (C v) v = E (J v) v`. -/
theorem isPolarization_homological [Module.Flat ℤ V] (h : J.IsRiemannForm E)
    (hℂ : IsBaseChange ℂ ιℂ) : Hodge.IsPolarization hℂ (RiemannForm.homological J hℂ) (-E) :=
  (h.neg.isPolarization hℂ).tateTwist 1

/-- The polarization `Q = -E` of the homological Hodge structure defined by a Riemann form `E`. -/
noncomputable def homologicalPolarization [Module.Flat ℤ V] (h : J.IsRiemannForm E)
    (hℂ : IsBaseChange ℂ ιℂ) : Hodge.Polarization hℂ (RiemannForm.homological J hℂ) where
  Qint := -E
  isPolarization := h.isPolarization_homological hℂ

/-- The integral form of the homological polarization of a Riemann form `E` is `-E`. -/
@[simp]
theorem homologicalPolarization_Qint [Module.Flat ℤ V] (h : J.IsRiemannForm E)
    (hℂ : IsBaseChange ℂ ιℂ) : (h.homologicalPolarization hℂ).Qint = -E :=
  (rfl)

end IsRiemannForm

end TauCeti.AlmostComplexStructure
