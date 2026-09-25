/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeilOperator
public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Effective Hodge structures of weight one

An effective pure Hodge structure of weight one has only the two Hodge components
`H^{1,0}` and `H^{0,1}`. Its Weil operator acts on them by `i` and `-i`, respectively, and
therefore descends to an almost complex structure on the real form fixed by conjugation.

This file identifies the `i`- and `-i`-eigenspaces of the Weil operator with `H^{1,0}` and
`H^{0,1}`. It then transfers those identifications to the scalar extension of the real almost
complex structure constructed in `TauCeti.Geometry.Hodge.WeilOperator`. In weight one without
effectivity, the two eigenspaces aggregate all Hodge components according to their first index
modulo two.

Conversely, an almost complex structure on a real vector space determines an effective pure Hodge
structure of weight one on its complexification. Its Hodge components are the `i`- and
`-i`-eigenspaces of the complex-linear extension, and its Weil operator is that extension.

The two constructions are mutually inverse. An effective weight-one Hodge structure is determined
by its Weil operator, and on the complexification `ℂ ⊗[ℝ] U` of a real vector space the Weil
operator of a Hodge structure of odd weight is real, so it is the scalar extension of an almost
complex structure on `U`. Hence the almost complex structures on `U` are exactly the effective
weight-one Hodge structures on `ℂ ⊗[ℝ] U`.

The real form and its structure map are the generic constructions `TauCeti.realPoints` and
`TauCeti.realPointsLift`; `TauCeti.realPointsEquiv` identifies its complexification with the
original complex vector space. The almost-complex structure reuses
`TauCeti.AlmostComplexStructure`, rather than introducing a Hodge-specific copy of that notion.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.eigenspace_weilOperator_I` and
  `TauCeti.Hodge.HodgeStructureOn.eigenspace_weilOperator_neg_I`: for an effective structure, the
  two eigenspaces of the Weil operator are the two Hodge components.
* `TauCeti.Hodge.HodgeStructureOn.eigenspace_baseChange_realAlmostComplexStructure_I` and
  `TauCeti.Hodge.HodgeStructureOn.eigenspace_baseChange_realAlmostComplexStructure_neg_I`: the same
  comparison on the literal complexification of the real form.
* `TauCeti.AlmostComplexStructure.hodgeStructure`: the effective weight-one Hodge structure
  associated with an almost complex structure.
* `TauCeti.AlmostComplexStructure.hodgeStructure_weilOperator`: its Weil operator is the
  complexification of the original almost complex structure.
* `TauCeti.Hodge.HodgeStructureOn.eq_of_weilOperator_eq`: an effective weight-one Hodge structure
  is determined by its Weil operator.
* `TauCeti.AlmostComplexStructure.hodgeStructureEquiv`: almost complex structures on `U` are
  equivalent to effective weight-one Hodge structures on `ℂ ⊗[ℝ] U`.

The construction and conventions follow Voisin, *Hodge Theory and Complex Algebraic Geometry I*,
§6, and Peters--Steenbrink, *Mixed Hodge Structures*, §2.
-/

public section

namespace TauCeti.Hodge

universe u

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W}

/-- If an endomorphism acts by two distinct scalars on a pair of complementary subspaces, its
eigenspace for the first scalar is the first subspace. -/
private theorem eigenspace_eq_of_isCompl {f : W →ₗ[ℂ] W} {A B : Submodule ℂ W} {μ ν : ℂ}
    (hAB : IsCompl A B) (hA : ∀ x ∈ A, f x = μ • x) (hB : ∀ x ∈ B, f x = ν • x)
    (hνμ : ν ≠ μ) : Module.End.eigenspace f μ = A := by
  apply le_antisymm
  · intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    have htop : x ∈ A ⊔ B := by rw [hAB.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop
    have hscalar : ν • b = μ • b := by
      apply add_left_cancel (a := μ • a)
      calc
        μ • a + ν • b = f (a + b) := by rw [map_add, hA a ha, hB b hb]
        _ = f x := congrArg f hab
        _ = μ • x := hx
        _ = μ • (a + b) := congrArg (fun y : W ↦ μ • y) hab.symm
        _ = μ • a + μ • b := smul_add μ a b
    have hbzero : (b : W) = 0 := by
      have hsmul : (ν - μ) • (b : W) = 0 := by rw [sub_smul, hscalar, sub_self]
      exact (smul_eq_zero.mp hsmul).resolve_left (sub_ne_zero.mpr hνμ)
    rw [← hab, hbzero, add_zero]
    exact ha
  · intro x hx
    rw [Module.End.mem_eigenspace_iff]
    exact hA x hx

/-- In an effective weight-one Hodge structure, `H^{1,0}` and `H^{0,1}` are complementary. -/
private theorem isCompl_piece_one_piece_zero (hs : HodgeStructureOn W ω 1)
    (heff : hs.IsEffective) : IsCompl (hs.piece 1) (hs.piece 0) := by
  have hFzero : hs.F 0 = ⊤ := heff.F_eq_top_of_nonpos (by norm_num)
  have hone : hs.piece 1 = hs.F 1 := heff.piece_weight_eq_F
  have hzero : hs.piece 0 = hs.conjF 1 := by
    rw [hs.piece_def]
    norm_num [hFzero]
  rw [hone, hzero]
  have hcompl := hs.isCompl_F_conjF 1
  norm_num at hcompl
  exact hcompl

/-- For an effective weight-one Hodge structure, the `i`-eigenspace of the Weil operator is
exactly the Hodge component `H^{1,0}`.

This and the other effective weight-one eigenspace equalities are intentionally not simp lemmas:
`isEffective_iff` simplifies their `IsEffective` hypothesis, so `simpNF` rejects the attributes.
Use them as explicit rewrite rules. -/
theorem eigenspace_weilOperator_I (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace hs.weilOperator Complex.I = hs.piece 1 := by
  refine eigenspace_eq_of_isCompl (μ := Complex.I) (ν := -Complex.I)
    (hs.isCompl_piece_one_piece_zero heff)
    (fun x hx ↦ hs.weilOperator_apply_of_mem_piece_one hx)
    (fun x hx ↦ by simpa only [neg_smul] using hs.weilOperator_apply_of_mem_piece_zero hx) ?_
  exact neg_ne_self.mpr Complex.I_ne_zero

/-- For an effective weight-one Hodge structure, the `-i`-eigenspace of the Weil operator is
exactly the conjugate Hodge component `H^{0,1}`. -/
theorem eigenspace_weilOperator_neg_I (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace hs.weilOperator (-Complex.I) = hs.piece 0 := by
  refine eigenspace_eq_of_isCompl (μ := -Complex.I) (ν := Complex.I)
    (hs.isCompl_piece_one_piece_zero heff).symm
    (fun x hx ↦ by simpa only [neg_smul] using hs.weilOperator_apply_of_mem_piece_zero hx)
    (fun x hx ↦ hs.weilOperator_apply_of_mem_piece_one hx) ?_
  exact (neg_ne_self.mpr Complex.I_ne_zero).symm

/-- **An effective weight-one Hodge structure is determined by its Weil operator.** Its filtration
is `⊤` in nonpositive degrees and `⊥` above degree one, while `F¹ = H^{1,0}` is the
`i`-eigenspace of the Weil operator. -/
theorem eq_of_weilOperator_eq {hs hs' : HodgeStructureOn W ω 1} (h : hs.IsEffective)
    (h' : hs'.IsEffective) (hC : hs.weilOperator = hs'.weilOperator) : hs = hs' := by
  ext1
  funext p
  rcases le_or_gt p 0 with hp | hp
  · rw [h.F_eq_top_of_nonpos hp, h'.F_eq_top_of_nonpos hp]
  have hp1 : (1 : ℤ) ≤ p := by omega
  rcases hp1.eq_or_lt with rfl | hp
  · rw [← h.piece_weight_eq_F, ← h'.piece_weight_eq_F, ← hs.eigenspace_weilOperator_I h,
      ← hs'.eigenspace_weilOperator_I h', hC]
  · rw [h.F_eq_bot_of_weight_lt hp, h'.F_eq_bot_of_weight_lt hp]

/-- On the literal complexification `ℂ ⊗[ℝ] V_ℝ`, the `i`-eigenspace of the scalar extension of
the real almost complex structure corresponds to `H^{1,0}` under `realPointsEquiv`. -/
theorem eigenspace_baseChange_realAlmostComplexStructure_I
    (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace
        (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
          Complex.I =
      (hs.piece 1).comap (realPointsEquiv ω.involutive).toLinearMap := by
  rw [eigenspace_eq_comap_of_intertwine
    (hs.realPointsEquiv_baseChange_realAlmostComplexStructure_apply (by norm_num)) Complex.I,
    hs.eigenspace_weilOperator_I heff]

/-- On the literal complexification `ℂ ⊗[ℝ] V_ℝ`, the `-i`-eigenspace of the scalar extension of
the real almost complex structure corresponds to `H^{0,1}` under `realPointsEquiv`. -/
theorem eigenspace_baseChange_realAlmostComplexStructure_neg_I
    (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace
        (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
          (-Complex.I) =
      (hs.piece 0).comap (realPointsEquiv ω.involutive).toLinearMap := by
  rw [eigenspace_eq_comap_of_intertwine
    (hs.realPointsEquiv_baseChange_realAlmostComplexStructure_apply (by norm_num)) (-Complex.I),
    hs.eigenspace_weilOperator_neg_I heff]

end HodgeStructureOn

end TauCeti.Hodge

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The effective pure Hodge structure of weight one associated with a real almost complex
structure. Its `F¹` is the `i`-eigenspace of the complexified endomorphism. -/
noncomputable def hodgeStructure (J : AlmostComplexStructure V) :
    Hodge.HodgeStructureOn (ℂ ⊗[ℝ] V) (Hodge.complexificationConjugation V) 1 where
  F p := if p ≤ 0 then ⊤ else if p = 1 then
    Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I else ⊥
  F_antitone p q hpq := by
    -- Expose the piecewise filtration stored in the structure field so its integer cases can be
    -- reduced directly; no rewrite theorem exists until `hodgeStructure` has been defined.
    change (if q ≤ 0 then ⊤ else if q = 1 then
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I else ⊥) ≤
        if p ≤ 0 then ⊤ else if p = 1 then
          Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I else ⊥
    by_cases hp : p ≤ 0
    · rw [ite_eq_left hp]
      exact le_top
    have hq : ¬q ≤ 0 := by omega
    rw [ite_eq_right hp, ite_eq_right hq]
    by_cases hq_one : q = 1
    · have hp_one : p = 1 := by omega
      subst p
      subst q
      exact le_rfl
    rw [ite_eq_right hq_one]
    exact bot_le
  F_top := ⟨0, by simp⟩
  opposed p := by
    by_cases hp : p ≤ 0
    · have hother : ¬ 1 + 1 - p ≤ 0 := by omega
      have hotherone : 1 + 1 - p ≠ 1 := by omega
      rw [ite_eq_left hp, ite_eq_right hother, ite_eq_right hotherone, Submodule.map_bot]
      exact isCompl_top_bot
    · by_cases hpone : p = 1
      · subst p
        norm_num
        exact J.isCompl_eigenspace_baseChange_I_neg_I
      · have hpge : 2 ≤ p := by omega
        have hother : 1 + 1 - p ≤ 0 := by omega
        have hmaptop : (⊤ : Submodule ℂ (ℂ ⊗[ℝ] V)).map
            (Hodge.complexificationConjugation V).toEquiv.toLinearMap = ⊤ := by
          rw [Submodule.map_top, LinearMap.range_eq_top]
          exact (Hodge.complexificationConjugation V).toEquiv.surjective
        rw [ite_eq_right hp, ite_eq_right hpone, ite_eq_left hother, hmaptop]
        exact isCompl_bot_top

/-- The filtration of the Hodge structure associated with `J` is top in nonpositive degrees,
the `i`-eigenspace in degree one, and bottom above degree one. -/
@[simp]
theorem hodgeStructure_F (J : AlmostComplexStructure V) (p : ℤ) :
    J.hodgeStructure.F p =
      if p ≤ 0 then ⊤ else if p = 1 then
        Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I else ⊥ :=
  (rfl)

/-- The Hodge structure associated with an almost complex structure is effective. -/
theorem isEffective_hodgeStructure (J : AlmostComplexStructure V) :
    J.hodgeStructure.IsEffective := by
  simp [Hodge.HodgeStructureOn.isEffective_iff]

/-- The `H^{1,0}` component associated with `J` is the `i`-eigenspace of its complexification. -/
@[simp]
theorem hodgeStructure_piece_one (J : AlmostComplexStructure V) :
    J.hodgeStructure.piece 1 =
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I := by
  rw [Hodge.HodgeStructureOn.piece_def, Hodge.HodgeStructureOn.conjF_def]
  norm_num [hodgeStructure_F]

/-- The `H^{0,1}` component associated with `J` is the `-i`-eigenspace of its complexification. -/
@[simp]
theorem hodgeStructure_piece_zero (J : AlmostComplexStructure V) :
    J.hodgeStructure.piece 0 =
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) := by
  rw [Hodge.HodgeStructureOn.piece_def, Hodge.HodgeStructureOn.conjF_def]
  norm_num [hodgeStructure_F]

/-- Every Hodge component of the structure associated with `J` other than `H^{1,0}` and
`H^{0,1}` vanishes. -/
theorem hodgeStructure_piece_eq_bot (J : AlmostComplexStructure V) {p : ℤ}
    (hpzero : p ≠ 0) (hpone : p ≠ 1) : J.hodgeStructure.piece p = ⊥ := by
  by_cases hp : p < 0
  · exact J.isEffective_hodgeStructure.piece_eq_bot_of_neg hp
  · exact J.isEffective_hodgeStructure.piece_eq_bot_of_weight_lt (by omega)

/-- The Weil operator of the Hodge structure associated with `J` is the complex-linear scalar
extension of `J`. Thus the construction recovers the original almost complex structure after
complexification. -/
@[simp]
theorem hodgeStructure_weilOperator (J : AlmostComplexStructure V) :
    J.hodgeStructure.weilOperator = J.toLinearMap.baseChange ℂ := by
  symm
  apply J.hodgeStructure.weilOperator_unique
  intro p x hx
  by_cases hpone : p = 1
  · subst p
    rw [J.hodgeStructure_piece_one, Module.End.mem_eigenspace_iff] at hx
    norm_num
    exact hx
  by_cases hpzero : p = 0
  · subst p
    rw [J.hodgeStructure_piece_zero, Module.End.mem_eigenspace_iff] at hx
    norm_num
    simpa only [neg_smul] using hx
  rw [J.hodgeStructure_piece_eq_bot hpzero hpone, Submodule.mem_bot] at hx
  subst x
  simp

end TauCeti.AlmostComplexStructure

/-! ### Effective weight-one Hodge structures are almost complex structures -/

namespace TauCeti.Hodge.HodgeStructureOn

open scoped TensorProduct

variable {U : Type*} [AddCommGroup U] [Module ℝ U] {n : ℤ}

/-- An effective weight-one Hodge structure on `ℂ ⊗[ℝ] U` is the Hodge structure of its induced
almost complex structure. -/
@[simp]
theorem hodgeStructure_almostComplexStructure
    (hs : HodgeStructureOn (ℂ ⊗[ℝ] U) (complexificationConjugation U) 1)
    (h : hs.F 0 = ⊤) :
    (hs.almostComplexStructure odd_one).hodgeStructure = hs :=
  eq_of_weilOperator_eq (AlmostComplexStructure.isEffective_hodgeStructure _)
    (hs.isEffective_iff.mpr h) (by simp)

end TauCeti.Hodge.HodgeStructureOn

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

/-- An almost complex structure is determined by its complex-linear scalar extension. -/
theorem baseChange_injective :
    Function.Injective fun J : AlmostComplexStructure U ↦ J.toLinearMap.baseChange ℂ := by
  intro J J' h
  ext u
  apply Module.Flat.tensorProduct_mk_injective ℝ U ℂ
  simpa using LinearMap.congr_fun h (1 ⊗ₜ[ℝ] u)

/-- The almost complex structure induced by the weight-one Hodge structure of `J` is `J`. -/
@[simp]
theorem almostComplexStructure_hodgeStructure (J : AlmostComplexStructure U) :
    J.hodgeStructure.almostComplexStructure odd_one = J :=
  baseChange_injective (by simp)

/-- **Almost complex structures on a real vector space `U` are the effective weight-one Hodge
structures on its complexification.** The forward map is
`TauCeti.AlmostComplexStructure.hodgeStructure`, and the inverse restricts the Weil operator to
the real vectors. -/
noncomputable def hodgeStructureEquiv :
    AlmostComplexStructure U ≃
      {hs : Hodge.HodgeStructureOn (ℂ ⊗[ℝ] U) (Hodge.complexificationConjugation U) 1 //
        hs.IsEffective} where
  toFun J := ⟨J.hodgeStructure, J.isEffective_hodgeStructure⟩
  invFun hs := hs.1.almostComplexStructure odd_one
  left_inv := almostComplexStructure_hodgeStructure
  right_inv hs := Subtype.ext
    (hs.1.hodgeStructure_almostComplexStructure (hs.1.isEffective_iff.mp hs.2))

/-- The equivalence sends `J` to its weight-one Hodge structure. -/
@[simp]
theorem coe_hodgeStructureEquiv_apply (J : AlmostComplexStructure U) :
    (hodgeStructureEquiv J : Hodge.HodgeStructureOn (ℂ ⊗[ℝ] U)
      (Hodge.complexificationConjugation U) 1) = J.hodgeStructure :=
  (rfl)

/-- The inverse equivalence sends a Hodge structure to its induced almost complex structure. -/
@[simp]
theorem hodgeStructureEquiv_symm_apply
    (hs : {hs : Hodge.HodgeStructureOn (ℂ ⊗[ℝ] U) (Hodge.complexificationConjugation U) 1 //
      hs.IsEffective}) :
    hodgeStructureEquiv.symm hs = hs.1.almostComplexStructure odd_one :=
  (rfl)

end TauCeti.AlmostComplexStructure
