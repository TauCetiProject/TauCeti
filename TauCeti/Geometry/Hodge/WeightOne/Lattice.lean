/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Realification
public import TauCeti.Geometry.Hodge.WeightOne.Basic

/-!
# Weight-one Hodge structures from complex structures on lattices

Let `V` be an integral lattice and let `J` be an almost complex structure on its realification
`Vℝ = ℝ ⊗[ℤ] V`.  Extending `J` to `ℂ` and transporting it to any chosen abstract
complexification `Vℂ` of `V` gives complementary `i`- and `-i`-eigenspaces.  They define an
effective Hodge structure of weight one on `V`.

This file carries the construction on a real vector space through the base-change comparison from
`TauCeti.Geometry.Hodge.Realification`.  In particular the resulting filtration, Hodge pieces, and
Weil operator are described directly in the chosen ambient complexification, so geometric models
need no transport isomorphism in their public statements.

## Main declarations

* `TauCeti.AlmostComplexStructure.latticeComplexification`: the complex-linear extension of `J`
  acting on the chosen abstract complexification.
* `TauCeti.AlmostComplexStructure.latticeHodgeStructure`: the associated effective integral Hodge
  structure of weight one.
* `TauCeti.AlmostComplexStructure.latticeHodgeStructure_piece_one` and
  `TauCeti.AlmostComplexStructure.latticeHodgeStructure_piece_zero`: its two nonzero pieces.
* `TauCeti.AlmostComplexStructure.latticeHodgeStructure_weilOperator`: the Weil operator recovers
  the transported complex structure.

The construction follows Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §6, and
Peters--Steenbrink, *Mixed Hodge Structures*, §2.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- The complex-linear extension of an almost complex structure on the realification of a lattice,
transported to a chosen abstract complexification of that lattice. -/
noncomputable def latticeComplexification
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    Vℂ →ₗ[ℂ] Vℂ :=
  (Hodge.realificationComplexEquiv hℂ).toLinearMap ∘ₗ
    J.toLinearMap.baseChange ℂ ∘ₗ
      (Hodge.realificationComplexEquiv hℂ).symm.toLinearMap

/-- The realification comparison intertwines the scalar extension of `J` with its transported
action on the abstract complexification. -/
theorem realificationComplexEquiv_baseChange_apply
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ)
    (x : ℂ ⊗[ℝ] Hodge.Realification V) :
    Hodge.realificationComplexEquiv hℂ (J.toLinearMap.baseChange ℂ x) =
      J.latticeComplexification hℂ (Hodge.realificationComplexEquiv hℂ x) := by
  simp [latticeComplexification]

/-- The transported complex structure still squares to minus the identity. -/
theorem latticeComplexification_comp_self
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    J.latticeComplexification hℂ ∘ₗ J.latticeComplexification hℂ = -LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (Hodge.realificationComplexEquiv hℂ).surjective x
  have h := congrArg (LinearMap.baseChange ℂ) J.square_neg
  have hbase : J.toLinearMap.baseChange ℂ ∘ₗ J.toLinearMap.baseChange ℂ =
      -LinearMap.id := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_neg,
      LinearMap.baseChange_id] using h
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply]
  rw [← realificationComplexEquiv_baseChange_apply]
  rw [← realificationComplexEquiv_baseChange_apply,
    ← LinearMap.comp_apply, hbase, LinearMap.neg_apply, LinearMap.id_apply, map_neg]

/-- The eigenspaces of the transported endomorphism are the transports of the eigenspaces of the
literal scalar extension. -/
theorem eigenspace_latticeComplexification
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) (z : ℂ) :
    Module.End.eigenspace (J.latticeComplexification hℂ) z =
      (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) z).map
        (Hodge.realificationComplexEquiv hℂ).toLinearMap := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨(Hodge.realificationComplexEquiv hℂ).symm x, ?_, by simp⟩
    apply (Hodge.realificationComplexEquiv hℂ).injective
    rw [realificationComplexEquiv_baseChange_apply, LinearEquiv.apply_symm_apply, hx,
      map_smul, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩
    simp only [latticeComplexification, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, hy, map_smul]

/-- The effective weight-one Hodge structure determined by a complex structure on the realification
of an integral lattice. -/
noncomputable def latticeHodgeStructure
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    Hodge.HodgeStructure hℂ 1 :=
  Hodge.HodgeStructureOn.comap (Hodge.realificationComplexEquiv hℂ).symm
    (fun x ↦ by simpa only [Hodge.latticeConjugation_toEquiv_apply] using
      Hodge.realificationComplexEquiv_symm_conj hℂ x) J.hodgeStructure

/-- The filtration associated with a lattice complex structure is top in nonpositive degrees, its
`i`-eigenspace in degree one, and bottom above degree one. -/
@[simp]
theorem latticeHodgeStructure_F
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) (p : ℤ) :
    (J.latticeHodgeStructure hℂ).F p = if p ≤ 0 then ⊤ else if p = 1 then
      Module.End.eigenspace (J.latticeComplexification hℂ) Complex.I else ⊥ := by
  rw [latticeHodgeStructure, Hodge.HodgeStructureOn.comap_F, hodgeStructure_F]
  by_cases hp : p ≤ 0
  · simp [hp]
  · by_cases hpone : p = 1
    · subst p
      simp only [hp, ↓reduceIte, Submodule.comap_equiv_eq_map_symm]
      exact (J.eigenspace_latticeComplexification hℂ Complex.I).symm
    · simp [hp, hpone]

/-- The weight-one Hodge structure associated with a lattice complex structure is effective. -/
theorem isEffective_latticeHodgeStructure
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    (J.latticeHodgeStructure hℂ).IsEffective := by
  simp [Hodge.HodgeStructureOn.isEffective_iff]

/-- The `H^{1,0}` component associated with a lattice complex structure is its `i`-eigenspace. -/
@[simp]
theorem latticeHodgeStructure_piece_one
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    (J.latticeHodgeStructure hℂ).piece 1 =
      Module.End.eigenspace (J.latticeComplexification hℂ) Complex.I := by
  rw [latticeHodgeStructure, Hodge.HodgeStructureOn.comap_piece, hodgeStructure_piece_one,
    Submodule.comap_equiv_eq_map_symm]
  exact (J.eigenspace_latticeComplexification hℂ Complex.I).symm

/-- The `H^{0,1}` component associated with a lattice complex structure is its `-i`-eigenspace. -/
@[simp]
theorem latticeHodgeStructure_piece_zero
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    (J.latticeHodgeStructure hℂ).piece 0 =
      Module.End.eigenspace (J.latticeComplexification hℂ) (-Complex.I) := by
  rw [latticeHodgeStructure, Hodge.HodgeStructureOn.comap_piece, hodgeStructure_piece_zero,
    Submodule.comap_equiv_eq_map_symm]
  exact (J.eigenspace_latticeComplexification hℂ (-Complex.I)).symm

/-- Every Hodge component of the structure associated with a lattice complex structure other than
`H^{1,0}` and `H^{0,1}` vanishes. -/
theorem latticeHodgeStructure_piece_eq_bot
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) {p : ℤ}
    (hpzero : p ≠ 0) (hpone : p ≠ 1) : (J.latticeHodgeStructure hℂ).piece p = ⊥ := by
  by_cases hp : p < 0
  · exact (J.isEffective_latticeHodgeStructure hℂ).piece_eq_bot_of_neg hp
  · exact (J.isEffective_latticeHodgeStructure hℂ).piece_eq_bot_of_weight_lt (by omega)

/-- The Weil operator of the Hodge structure associated with a lattice complex structure is the
transported complex-linear extension of that structure. -/
@[simp]
theorem latticeHodgeStructure_weilOperator
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    (J.latticeHodgeStructure hℂ).weilOperator = J.latticeComplexification hℂ := by
  symm
  apply (J.latticeHodgeStructure hℂ).weilOperator_unique
  intro p x hx
  by_cases hpone : p = 1
  · subst p
    rw [J.latticeHodgeStructure_piece_one hℂ, Module.End.mem_eigenspace_iff] at hx
    norm_num
    exact hx
  by_cases hpzero : p = 0
  · subst p
    rw [J.latticeHodgeStructure_piece_zero hℂ, Module.End.mem_eigenspace_iff] at hx
    norm_num
    simpa only [neg_smul] using hx
  rw [J.latticeHodgeStructure_piece_eq_bot hℂ hpzero hpone, Submodule.mem_bot] at hx
  subst x
  simp

end TauCeti.AlmostComplexStructure
