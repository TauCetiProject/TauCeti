/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Realification
public import TauCeti.Geometry.Hodge.WeightOne.Basic

/-!
# Weight-one Hodge structures from complex structures on integral modules

Let `V` be an integral module and let `J` be an almost complex structure on its realification
`Vℝ = ℝ ⊗[ℤ] V`.  Extending `J` to `ℂ` and transporting it to any chosen abstract
complexification `Vℂ` of `V` gives complementary `i`- and `-i`-eigenspaces.  They define an
effective Hodge structure of weight one on `V`.

This file carries the construction on a real vector space through the base-change comparison from
`TauCeti.Geometry.Hodge.Realification`.  In particular the resulting filtration, Hodge pieces, and
Weil operator are described directly in the chosen ambient complexification, so geometric models
need no transport isomorphism in their public statements.

Conversely, the Weil operator of an effective Hodge structure of weight one on `V` is real and
squares to `-1`, so it restricts to a complex structure on `Vℝ`. The two constructions are
mutually inverse. Effective weight-one examples, such as the first cohomology of a complex torus,
can therefore be given either by a Hodge filtration or by a complex structure on the real
lattice span, and the two descriptions agree.

## Main declarations

* `TauCeti.AlmostComplexStructure.latticeComplexification`: the complex-linear extension of `J`
  acting on the chosen abstract complexification; on the real points coming from the realification
  it acts by `J` (`latticeComplexification_realificationComplexEquiv_one_tmul`).
* `TauCeti.AlmostComplexStructure.latticeHodgeStructure`: the associated effective integral Hodge
  structure of weight one.
* `TauCeti.AlmostComplexStructure.latticeHodgeStructure_piece_one` and
  `TauCeti.AlmostComplexStructure.latticeHodgeStructure_piece_zero`: its degree-one and
  degree-zero pieces.
* `TauCeti.AlmostComplexStructure.latticeHodgeStructure_weilOperator`: the Weil operator recovers
  the transported complex structure.
* `TauCeti.Hodge.HodgeStructureOn.latticeAlmostComplexStructure`: conversely, the complex structure
  on `Vℝ` induced by an integral Hodge structure of odd weight on `V`, which complexifies to its
  Weil operator (`latticeComplexification_latticeAlmostComplexStructure`).
* `TauCeti.AlmostComplexStructure.latticeHodgeStructureEquiv`: the two constructions are mutually
  inverse, so complex structures on `Vℝ` are exactly the effective integral Hodge structures of
  weight one on `V`.

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

/-- The complex-linear extension of an almost complex structure on the realification of an integral
module, transported to a chosen abstract complexification of that module. -/
noncomputable def latticeComplexification
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    Vℂ →ₗ[ℂ] Vℂ :=
  (Hodge.realificationComplexEquiv hℂ).conj (J.toLinearMap.baseChange ℂ)

/-- The realification comparison intertwines the scalar extension of `J` with its transported
action on the abstract complexification. -/
@[simp]
theorem realificationComplexEquiv_baseChange_apply
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ)
    (x : ℂ ⊗[ℝ] Hodge.Realification V) :
    Hodge.realificationComplexEquiv hℂ (J.toLinearMap.baseChange ℂ x) =
      J.latticeComplexification hℂ (Hodge.realificationComplexEquiv hℂ x) := by
  simp [latticeComplexification]

/-- The transported complex structure acts on the image of a real vector by the original almost
complex structure. -/
@[simp]
theorem latticeComplexification_realificationComplexEquiv_one_tmul
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ)
    (x : Hodge.Realification V) :
    J.latticeComplexification hℂ (Hodge.realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x)) =
      Hodge.realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] J x) := by
  rw [← realificationComplexEquiv_baseChange_apply, LinearMap.baseChange_tmul]

/-- The transported complex structure still squares to minus the identity. -/
theorem latticeComplexification_comp_self
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    J.latticeComplexification hℂ ∘ₗ J.latticeComplexification hℂ = -LinearMap.id := by
  have hbase : J.toLinearMap.baseChange ℂ ∘ₗ J.toLinearMap.baseChange ℂ = -LinearMap.id := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_neg, LinearMap.baseChange_id]
      using congrArg (LinearMap.baseChange ℂ) J.square_neg
  rw [latticeComplexification, ← LinearEquiv.conj_comp, hbase, map_neg, LinearEquiv.conj_id]

/-- The eigenspaces of the transported endomorphism are the transports of the eigenspaces of the
literal scalar extension. -/
theorem eigenspace_latticeComplexification
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) (z : ℂ) :
    Module.End.eigenspace (J.latticeComplexification hℂ) z =
      (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) z).map
        (Hodge.realificationComplexEquiv hℂ).toLinearMap := by
  rw [eigenspace_eq_comap_of_intertwine (J.realificationComplexEquiv_baseChange_apply hℂ) z,
    Submodule.map_comap_eq_of_surjective (Hodge.realificationComplexEquiv hℂ).surjective]

/-- The effective weight-one Hodge structure determined by a complex structure on the realification
of an integral module. -/
noncomputable def latticeHodgeStructure
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    Hodge.HodgeStructure hℂ 1 :=
  Hodge.HodgeStructureOn.comap (Hodge.realificationComplexEquiv hℂ).symm
    (fun x ↦ by
      simpa only [Hodge.latticeConjugation_toEquiv_apply,
        Hodge.complexificationConjugation_toEquiv_apply] using
        Hodge.realificationComplexEquiv_symm_conj hℂ x) J.hodgeStructure

/-- The filtration associated with the complex structure is top in nonpositive degrees, its
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

/-- The weight-one Hodge structure associated with the complex structure is effective. -/
theorem isEffective_latticeHodgeStructure
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    (J.latticeHodgeStructure hℂ).IsEffective := by
  simp [Hodge.HodgeStructureOn.isEffective_iff]

/-- The `H^{1,0}` component associated with the complex structure is its `i`-eigenspace. -/
@[simp]
theorem latticeHodgeStructure_piece_one
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    (J.latticeHodgeStructure hℂ).piece 1 =
      Module.End.eigenspace (J.latticeComplexification hℂ) Complex.I := by
  rw [latticeHodgeStructure, Hodge.HodgeStructureOn.comap_piece, hodgeStructure_piece_one,
    Submodule.comap_equiv_eq_map_symm]
  exact (J.eigenspace_latticeComplexification hℂ Complex.I).symm

/-- The `H^{0,1}` component associated with the complex structure is its `-i`-eigenspace. -/
@[simp]
theorem latticeHodgeStructure_piece_zero
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    (J.latticeHodgeStructure hℂ).piece 0 =
      Module.End.eigenspace (J.latticeComplexification hℂ) (-Complex.I) := by
  rw [latticeHodgeStructure, Hodge.HodgeStructureOn.comap_piece, hodgeStructure_piece_zero,
    Submodule.comap_equiv_eq_map_symm]
  exact (J.eigenspace_latticeComplexification hℂ (-Complex.I)).symm

/-- Every Hodge component of the structure associated with the complex structure other than
`H^{1,0}` and `H^{0,1}` vanishes. -/
theorem latticeHodgeStructure_piece_eq_bot
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) {p : ℤ}
    (hpzero : p ≠ 0) (hpone : p ≠ 1) : (J.latticeHodgeStructure hℂ).piece p = ⊥ := by
  by_cases hp : p < 0
  · exact (J.isEffective_latticeHodgeStructure hℂ).piece_eq_bot_of_neg hp
  · exact (J.isEffective_latticeHodgeStructure hℂ).piece_eq_bot_of_weight_lt (by omega)

/-- The Weil operator of the Hodge structure associated with the complex structure is the
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

/-! ### Effective weight-one Hodge structures on a lattice are complex structures -/

namespace TauCeti.Hodge.HodgeStructureOn

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ}

/-- The realification comparison intertwines the two bundled conjugations. -/
private theorem realificationComplexEquiv_conjugation (hℂ : IsBaseChange ℂ ιℂ)
    (x : ℂ ⊗[ℝ] Realification V) :
    realificationComplexEquiv hℂ ((complexificationConjugation (Realification V)).toEquiv x) =
      (latticeConjugation hℂ).toEquiv (realificationComplexEquiv hℂ x) := by
  rw [complexificationConjugation_toEquiv_apply, latticeConjugation_toEquiv_apply,
    realificationComplexEquiv_conj]

/-- The almost complex structure on the realification `ℝ ⊗[ℤ] V` determined by an integral Hodge
structure of odd weight on `V`: its Weil operator, which is real, restricted to the real points of
the complexification. -/
noncomputable def latticeAlmostComplexStructure (hs : HodgeStructure hℂ n) (hn : Odd n) :
    AlmostComplexStructure (Realification V) :=
  (hs.comap (realificationComplexEquiv hℂ)
    (realificationComplexEquiv_conjugation hℂ)).almostComplexStructure hn

/-- **The induced complex structure complexifies to the Weil operator** on the chosen abstract
complexification. -/
@[simp]
theorem latticeComplexification_latticeAlmostComplexStructure (hs : HodgeStructure hℂ n)
    (hn : Odd n) :
    (hs.latticeAlmostComplexStructure hn).latticeComplexification hℂ = hs.weilOperator := by
  rw [AlmostComplexStructure.latticeComplexification, latticeAlmostComplexStructure,
    baseChange_almostComplexStructure, weilOperator_comap]
  ext x
  simp

/-- An effective integral Hodge structure of weight one is the Hodge structure of its induced
complex structure on the realification. -/
@[simp]
theorem latticeHodgeStructure_latticeAlmostComplexStructure (hs : HodgeStructure hℂ 1)
    (h : hs.F 0 = ⊤) :
    (hs.latticeAlmostComplexStructure odd_one).latticeHodgeStructure hℂ = hs :=
  eq_of_weilOperator_eq (AlmostComplexStructure.isEffective_latticeHodgeStructure _ hℂ)
    (hs.isEffective_iff.mpr h)
    (by simp)

end TauCeti.Hodge.HodgeStructureOn

namespace TauCeti.AlmostComplexStructure

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- A complex structure on the realification is determined by its transport to a chosen abstract
complexification. -/
theorem latticeComplexification_injective (hℂ : IsBaseChange ℂ ιℂ) :
    Function.Injective fun J : AlmostComplexStructure (Hodge.Realification V) ↦
      J.latticeComplexification hℂ := by
  intro J J' h
  simp only [latticeComplexification] at h
  exact baseChange_injective ((Hodge.realificationComplexEquiv hℂ).conj.injective h)

/-- The complex structure induced by the weight-one Hodge structure of `J` is `J`. -/
@[simp]
theorem latticeAlmostComplexStructure_latticeHodgeStructure
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ) :
    (J.latticeHodgeStructure hℂ).latticeAlmostComplexStructure odd_one = J :=
  latticeComplexification_injective hℂ (by simp)

/-- **Complex structures on the realification of `V` are the effective integral Hodge structures
of weight one on `V`**, for any chosen abstract complexification of `V`. The forward map is
`TauCeti.AlmostComplexStructure.latticeHodgeStructure`, and the inverse restricts the Weil operator
to the real points. -/
noncomputable def latticeHodgeStructureEquiv (hℂ : IsBaseChange ℂ ιℂ) :
    AlmostComplexStructure (Hodge.Realification V) ≃
      {hs : Hodge.HodgeStructure hℂ 1 // hs.IsEffective} where
  toFun J := ⟨J.latticeHodgeStructure hℂ, J.isEffective_latticeHodgeStructure hℂ⟩
  invFun hs := hs.1.latticeAlmostComplexStructure odd_one
  left_inv J := J.latticeAlmostComplexStructure_latticeHodgeStructure hℂ
  right_inv hs := Subtype.ext
    (hs.1.latticeHodgeStructure_latticeAlmostComplexStructure (hs.1.isEffective_iff.mp hs.2))

/-- The equivalence sends `J` to its integral weight-one Hodge structure. -/
@[simp]
theorem coe_latticeHodgeStructureEquiv_apply (hℂ : IsBaseChange ℂ ιℂ)
    (J : AlmostComplexStructure (Hodge.Realification V)) :
    (latticeHodgeStructureEquiv hℂ J : Hodge.HodgeStructure hℂ 1) = J.latticeHodgeStructure hℂ :=
  (rfl)

/-- The inverse equivalence sends a Hodge structure to its induced complex structure. -/
@[simp]
theorem latticeHodgeStructureEquiv_symm_apply (hℂ : IsBaseChange ℂ ιℂ)
    (hs : {hs : Hodge.HodgeStructure hℂ 1 // hs.IsEffective}) :
    (latticeHodgeStructureEquiv hℂ).symm hs = hs.1.latticeAlmostComplexStructure odd_one :=
  (rfl)

end TauCeti.AlmostComplexStructure
