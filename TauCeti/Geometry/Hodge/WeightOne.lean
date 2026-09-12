/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeilOperator
public import TauCeti.Geometry.Hodge.Polarization
public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

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
* `TauCeti.Hodge.StandardWeightOne.hodgeStructure`: the standard rank-two integral example,
  polarized by `TauCeti.Hodge.StandardWeightOne.riemannForm`.

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
  have hconjFzero : hs.conjF 0 = ⊤ := by
    apply top_unique
    intro x _
    rw [hs.mem_conjF_iff, hFzero]
    exact Submodule.mem_top
  have hone : hs.piece 1 = hs.F 1 := by
    rw [hs.piece_def]
    norm_num [hconjFzero]
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

/-- An intertwining linear equivalence identifies the eigenspaces of the two endomorphisms. -/
private theorem eigenspace_eq_comap_of_intertwine {U : Type*} [AddCommGroup U] [Module ℂ U]
    (e : U ≃ₗ[ℂ] W) (f : U →ₗ[ℂ] U) (g : W →ₗ[ℂ] W)
    (h : ∀ x, e (f x) = g (e x)) (μ : ℂ) :
    Module.End.eigenspace f μ = (Module.End.eigenspace g μ).comap e.toLinearMap := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_comap]
  constructor
  · intro hx
    calc
      g (e x) = e (f x) := (h x).symm
      _ = e (μ • x) := congrArg e hx
      _ = μ • e x := map_smul e μ x
  · intro hx
    apply e.injective
    calc
      e (f x) = g (e x) := h x
      _ = μ • e x := hx
      _ = e (μ • x) := (map_smul e μ x).symm

/-- On the literal complexification `ℂ ⊗[ℝ] V_ℝ`, the `i`-eigenspace of the scalar extension of
the real almost complex structure corresponds to `H^{1,0}` under `realPointsEquiv`. -/
theorem eigenspace_baseChange_realAlmostComplexStructure_I
    (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace
        (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
          Complex.I =
      (hs.piece 1).comap (realPointsEquiv ω.involutive).toLinearMap := by
  rw [eigenspace_eq_comap_of_intertwine (realPointsEquiv ω.involutive)
    (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
    hs.weilOperator (hs.realPointsEquiv_baseChange_realAlmostComplexStructure_apply (by norm_num))
    Complex.I,
    hs.eigenspace_weilOperator_I heff]

/-- On the literal complexification `ℂ ⊗[ℝ] V_ℝ`, the `-i`-eigenspace of the scalar extension of
the real almost complex structure corresponds to `H^{0,1}` under `realPointsEquiv`. -/
theorem eigenspace_baseChange_realAlmostComplexStructure_neg_I
    (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace
        (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
          (-Complex.I) =
      (hs.piece 0).comap (realPointsEquiv ω.involutive).toLinearMap := by
  rw [eigenspace_eq_comap_of_intertwine (realPointsEquiv ω.involutive)
    (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
    hs.weilOperator (hs.realPointsEquiv_baseChange_realAlmostComplexStructure_apply (by norm_num))
    (-Complex.I),
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

namespace TauCeti.Hodge.StandardWeightOne

open scoped ComplexOrder

/-! ### The standard rank-two lattice and its complex structure -/

/-- The integral lattice underlying the standard rank-two weight-one example. -/
abbrev Lattice := ℤ × ℤ

/-- The rational vector space underlying the standard rank-two weight-one example. -/
abbrev RationalSpace := ℚ × ℚ

/-- The complex vector space underlying the standard rank-two weight-one example. -/
abbrev ComplexSpace := ℂ × ℂ

/-- Coordinatewise inclusion of the standard lattice into its rationalization. -/
def latticeToRational : Lattice →ₗ[ℤ] RationalSpace :=
  (Algebra.linearMap ℤ ℚ).prodMap (Algebra.linearMap ℤ ℚ)

/-- Coordinatewise inclusion of the standard lattice into its complexification. -/
def latticeToComplex : Lattice →ₗ[ℤ] ComplexSpace :=
  (Algebra.linearMap ℤ ℂ).prodMap (Algebra.linearMap ℤ ℂ)

/-- Coordinatewise inclusion of the rationalization into the complexification. -/
noncomputable def rationalToComplex : RationalSpace →ₗ[ℚ] ComplexSpace :=
  (Algebra.linearMap ℚ ℂ).prodMap (Algebra.linearMap ℚ ℂ)

@[simp]
theorem latticeToRational_apply (x : Lattice) :
    latticeToRational x = ((x.1 : ℚ), (x.2 : ℚ)) := by
  simp [latticeToRational]

@[simp]
theorem latticeToComplex_apply (x : Lattice) :
    latticeToComplex x = ((x.1 : ℂ), (x.2 : ℂ)) := by
  simp [latticeToComplex]

@[simp]
theorem rationalToComplex_apply (x : RationalSpace) :
    rationalToComplex x = ((x.1 : ℂ), (x.2 : ℂ)) := by
  simp [rationalToComplex]

/-- The coordinatewise rational inclusion is a base change from `ℤ` to `ℚ`. -/
theorem isBaseChange_latticeToRational : IsBaseChange ℚ latticeToRational :=
  IsBaseChange.prodMap _ _ (IsBaseChange.linearMap ℤ ℚ) (IsBaseChange.linearMap ℤ ℚ)

/-- The coordinatewise complex inclusion is a base change from `ℤ` to `ℂ`. -/
theorem isBaseChange_latticeToComplex : IsBaseChange ℂ latticeToComplex :=
  IsBaseChange.prodMap _ _ (IsBaseChange.linearMap ℤ ℂ) (IsBaseChange.linearMap ℤ ℂ)

/-- The coordinatewise inclusion from `ℚ × ℚ` to `ℂ × ℂ` is a base change. -/
theorem isBaseChange_rationalToComplex : IsBaseChange ℂ rationalToComplex :=
  IsBaseChange.prodMap _ _ (IsBaseChange.linearMap ℚ ℂ) (IsBaseChange.linearMap ℚ ℂ)

/-- The standard complex structure `J(x, y) = (-y, x)` on the complexified rank-two lattice. -/
def complexStructure : ComplexSpace →ₗ[ℂ] ComplexSpace where
  toFun z := (-z.2, z.1)
  map_add' z w := by ext <;> simp [add_comm]
  map_smul' c z := by ext <;> simp

@[simp]
theorem complexStructure_apply (z : ComplexSpace) :
    complexStructure z = (-z.2, z.1) := by
  simp [complexStructure]

/-- The standard complex structure squares to minus the identity. -/
theorem complexStructure_sq :
    complexStructure.comp complexStructure = -(LinearMap.id : ComplexSpace →ₗ[ℂ] ComplexSpace) := by
  apply LinearMap.ext
  rintro ⟨z, w⟩
  ext <;> simp

private noncomputable def coordinateConjugation :
    ComplexSpace →ₛₗ[starRingEnd ℂ] ComplexSpace where
  toFun z := (starRingEnd ℂ z.1, starRingEnd ℂ z.2)
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp

/-- Lattice conjugation for the coordinate complexification is coordinatewise complex
conjugation. -/
@[simp]
theorem latticeConj_apply (z : ComplexSpace) :
    latticeConj isBaseChange_latticeToComplex z =
      (starRingEnd ℂ z.1, starRingEnd ℂ z.2) := by
  rw [← latticeConj_unique isBaseChange_latticeToComplex coordinateConjugation]
  · rfl
  · intro x
    ext <;> simp [coordinateConjugation]

private theorem map_eigenspace_I :
    (Module.End.eigenspace complexStructure Complex.I).map
        (latticeConjugation isBaseChange_latticeToComplex).toEquiv.toLinearMap =
      Module.End.eigenspace complexStructure (-Complex.I) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ Module.End.eigenspace complexStructure Complex.I := hw
    rw [Module.End.mem_eigenspace_iff] at hw'
    rw [Module.End.mem_eigenspace_iff]
    rw [LinearEquiv.coe_coe, latticeConjugation_toEquiv_apply, latticeConj_apply]
    have hfst := congrArg Prod.fst hw'
    have hsnd := congrArg Prod.snd hw'
    apply Prod.ext
    · simpa using congrArg (starRingEnd ℂ) hfst
    · simpa using congrArg (starRingEnd ℂ) hsnd
  · intro hz
    rw [Module.End.mem_eigenspace_iff] at hz
    have hfst := congrArg Prod.fst hz
    have hsnd := congrArg Prod.snd hz
    refine ⟨(starRingEnd ℂ z.1, starRingEnd ℂ z.2), ?_, ?_⟩
    · have hw : (starRingEnd ℂ z.1, starRingEnd ℂ z.2) ∈
          Module.End.eigenspace complexStructure Complex.I := by
        rw [Module.End.mem_eigenspace_iff]
        apply Prod.ext
        · simpa using congrArg (starRingEnd ℂ) hfst
        · simpa using congrArg (starRingEnd ℂ) hsnd
      exact hw
    · rw [LinearEquiv.coe_coe, latticeConjugation_toEquiv_apply, latticeConj_apply]
      simp

private theorem isCompl_eigenspaces :
    IsCompl (Module.End.eigenspace complexStructure Complex.I)
      (Module.End.eigenspace complexStructure (-Complex.I)) :=
  Module.End.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id complexStructure complexStructure_sq

private def filtration (p : ℤ) : Submodule ℂ ComplexSpace :=
  if p ≤ 0 then ⊤ else if p = 1 then
    Module.End.eigenspace complexStructure Complex.I else ⊥

private theorem filtration_antitone : Antitone filtration := by
  intro p q hpq
  change (if q ≤ 0 then ⊤ else if q = 1 then
      Module.End.eigenspace complexStructure Complex.I else ⊥) ≤
    if p ≤ 0 then ⊤ else if p = 1 then
      Module.End.eigenspace complexStructure Complex.I else ⊥
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

/-- The standard effective Hodge structure of weight one on `ℤ × ℤ`. Its degree-one
filtration is the `i`-eigenspace of `J(x, y) = (-y, x)`. -/
noncomputable def hodgeStructure :
    HodgeStructure isBaseChange_latticeToComplex 1 where
  F := filtration
  F_antitone := filtration_antitone
  F_top := ⟨0, by simp [filtration]⟩
  opposed p := by
    by_cases hp : p ≤ 0
    · have hother : ¬1 + 1 - p ≤ 0 := by omega
      have hotherone : 1 + 1 - p ≠ 1 := by omega
      rw [filtration, ite_eq_left hp, filtration, ite_eq_right hother,
        ite_eq_right hotherone,
        Submodule.map_bot]
      exact isCompl_top_bot
    · by_cases hpone : p = 1
      · subst p
        norm_num [filtration, map_eigenspace_I]
        exact isCompl_eigenspaces
      · have hpge : 2 ≤ p := by omega
        have hother : 1 + 1 - p ≤ 0 := by omega
        have hmaptop : (⊤ : Submodule ℂ ComplexSpace).map
            (latticeConjugation isBaseChange_latticeToComplex).toEquiv.toLinearMap = ⊤ := by
          rw [Submodule.map_top, LinearMap.range_eq_top]
          exact (latticeConjugation isBaseChange_latticeToComplex).toEquiv.surjective
        rw [filtration, ite_eq_right hp, ite_eq_right hpone, filtration,
          ite_eq_left hother, hmaptop]
        exact isCompl_bot_top

/-- The filtration is top in nonpositive degrees, the `i`-eigenspace in degree one, and bottom
above degree one. -/
@[simp]
theorem hodgeStructure_F (p : ℤ) :
    hodgeStructure.F p = if p ≤ 0 then ⊤ else if p = 1 then
      Module.End.eigenspace complexStructure Complex.I else ⊥ :=
  by
    -- Expose the private filtration definition while keeping its implementation private.
    change filtration p = _
    rfl

/-- The standard weight-one Hodge structure is effective. -/
theorem hodgeStructure_isEffective : hodgeStructure.IsEffective := by
  simp [HodgeStructureOn.isEffective_iff]

/-- The `H^{1,0}` piece is the `i`-eigenspace of the standard complex structure. -/
@[simp]
theorem hodgeStructure_piece_one :
    hodgeStructure.piece 1 = Module.End.eigenspace complexStructure Complex.I := by
  rw [HodgeStructureOn.piece_def, HodgeStructureOn.conjF_def]
  norm_num [hodgeStructure_F]

/-- The `H^{0,1}` piece is the `-i`-eigenspace of the standard complex structure. -/
@[simp]
theorem hodgeStructure_piece_zero :
    hodgeStructure.piece 0 = Module.End.eigenspace complexStructure (-Complex.I) := by
  rw [HodgeStructureOn.piece_def, HodgeStructureOn.conjF_def]
  norm_num [hodgeStructure_F, map_eigenspace_I]

/-- Every Hodge piece except `H^{1,0}` and `H^{0,1}` vanishes. -/
theorem hodgeStructure_piece_eq_bot {p : ℤ} (hpzero : p ≠ 0) (hpone : p ≠ 1) :
    hodgeStructure.piece p = ⊥ := by
  by_cases hp : p < 0
  · exact hodgeStructure_isEffective.piece_eq_bot_of_neg hp
  · exact hodgeStructure_isEffective.piece_eq_bot_of_weight_lt (by omega)

/-! ### The standard Riemann form -/

/-- The standard alternating Riemann form
`Q((x, y), (u, v)) = y * u - x * v` on `ℤ × ℤ`. -/
def riemannForm : LinearMap.BilinForm ℤ Lattice :=
  LinearMap.mk₂ ℤ (fun x y : Lattice ↦ x.2 * y.1 - x.1 * y.2)
    (by rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩; simp; ring)
    (by rintro c ⟨a, b⟩ ⟨d, e⟩; simp; ring)
    (by rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩; simp; ring)
    (by rintro c ⟨a, b⟩ ⟨d, e⟩; simp; ring)

@[simp]
theorem riemannForm_apply (x y : Lattice) :
    riemannForm x y = x.2 * y.1 - x.1 * y.2 := by
  simp [riemannForm]

/-- The standard Riemann form has no left or right radical. -/
theorem riemannForm_nondegenerate : riemannForm.Nondegenerate := by
  constructor
  · intro x hx
    have hfst := hx (0, 1)
    have hsnd := hx (1, 0)
    apply Prod.ext
    · simpa using neg_eq_zero.mp (by simpa using hfst)
    · simpa using hsnd
  · intro y hy
    have hfst := hy (0, 1)
    have hsnd := hy (1, 0)
    apply Prod.ext
    · simpa using hfst
    · simpa using neg_eq_zero.mp (by simpa using hsnd)

private def complexRiemannForm : LinearMap.BilinForm ℂ ComplexSpace :=
  LinearMap.mk₂ ℂ (fun x y : ComplexSpace ↦ x.2 * y.1 - x.1 * y.2)
    (by rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩; simp; ring)
    (by rintro c ⟨a, b⟩ ⟨d, e⟩; simp; ring)
    (by rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩; simp; ring)
    (by rintro c ⟨a, b⟩ ⟨d, e⟩; simp; ring)

private theorem integralFormBaseChange_riemannForm :
    integralFormBaseChange isBaseChange_latticeToComplex riemannForm = complexRiemannForm := by
  symm
  apply integralFormBaseChange_unique
  intro x y
  simp [complexRiemannForm]

/-- The complexification of the standard Riemann form has the same coordinate formula. -/
@[simp]
theorem integralFormBaseChange_riemannForm_apply (x y : ComplexSpace) :
    integralFormBaseChange isBaseChange_latticeToComplex riemannForm x y =
      x.2 * y.1 - x.1 * y.2 := by
  rw [integralFormBaseChange_riemannForm]
  simp [complexRiemannForm]

private theorem snd_eq_neg_I_mul_fst_of_mem_I {x : ComplexSpace}
    (hx : x ∈ Module.End.eigenspace complexStructure Complex.I) :
    x.2 = -Complex.I * x.1 := by
  rw [Module.End.mem_eigenspace_iff] at hx
  have h := congrArg Prod.fst hx
  calc
    x.2 = -(-x.2) := by simp
    _ = -(Complex.I * x.1) := congrArg Neg.neg (by simpa using h)
    _ = -Complex.I * x.1 := by ring

private theorem snd_eq_I_mul_fst_of_mem_neg_I {x : ComplexSpace}
    (hx : x ∈ Module.End.eigenspace complexStructure (-Complex.I)) :
    x.2 = Complex.I * x.1 := by
  rw [Module.End.mem_eigenspace_iff] at hx
  have h := congrArg Prod.fst hx
  calc
    x.2 = -(-x.2) := by simp
    _ = -((-Complex.I) * x.1) := congrArg Neg.neg (by simpa using h)
    _ = Complex.I * x.1 := by ring

private theorem positive_coordinate_I (z : ℂ) (hz : z ≠ 0) :
    0 < Complex.I *
      ((-Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (-Complex.I * z)) := by
  have hcalc : Complex.I *
      ((-Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (-Complex.I * z)) = (2 * Complex.normSq z : ℝ) := by
    rw [map_mul, map_neg]
    norm_num
    rw [Complex.normSq_eq_conj_mul_self]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hcalc]
  exact Complex.zero_lt_real.mpr (mul_pos (by norm_num) (Complex.normSq_pos.mpr hz))

private theorem positive_coordinate_neg_I (z : ℂ) (hz : z ≠ 0) :
    0 < (-Complex.I) *
      ((Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (Complex.I * z)) := by
  have hcalc : (-Complex.I) *
      ((Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (Complex.I * z)) = (2 * Complex.normSq z : ℝ) := by
    rw [map_mul]
    norm_num
    rw [Complex.normSq_eq_conj_mul_self]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hcalc]
  exact Complex.zero_lt_real.mpr (mul_pos (by norm_num) (Complex.normSq_pos.mpr hz))

/-- The standard alternating form satisfies the Hodge–Riemann relations for the standard
weight-one Hodge structure. -/
theorem isPolarization_riemannForm :
    IsPolarization isBaseChange_latticeToComplex hodgeStructure riemannForm where
  symm_weight x y := by
    norm_num [riemannForm_apply]
    ring
  nondegenerate := riemannForm_nondegenerate
  orthogonal p x hx y hy := by
    by_cases hp : p ≤ 0
    · have hother : ¬1 + 1 - p ≤ 0 := by omega
      have hotherone : 1 + 1 - p ≠ 1 := by omega
      have hyzero : y = 0 := by
        have : y ∈ (⊥ : Submodule ℂ ComplexSpace) := by
          rw [hodgeStructure_F, ite_eq_right hother, ite_eq_right hotherone] at hy
          exact hy
        exact this
      subst y
      simp
    · by_cases hpone : p = 1
      · subst p
        have hxI : x ∈ Module.End.eigenspace complexStructure Complex.I := by
          simpa [hodgeStructure_F] using hx
        have hyI : y ∈ Module.End.eigenspace complexStructure Complex.I := by
          simpa [hodgeStructure_F] using hy
        rw [integralFormBaseChange_riemannForm_apply,
          snd_eq_neg_I_mul_fst_of_mem_I hxI, snd_eq_neg_I_mul_fst_of_mem_I hyI]
        ring
      · have hxzero : x = 0 := by
          have : x ∈ (⊥ : Submodule ℂ ComplexSpace) := by
            rw [hodgeStructure_F, ite_eq_right hp, ite_eq_right hpone] at hx
            exact hx
          exact this
        subst x
        simp
  positive p x hx hx0 := by
    by_cases hpone : p = 1
    · subst p
      rw [hodgeStructure_piece_one] at hx
      have hrel := snd_eq_neg_I_mul_fst_of_mem_I hx
      have hfst : x.1 ≠ 0 := by
        intro hzero
        apply hx0
        apply Prod.ext <;> simp [hzero, hrel]
      rw [integralFormBaseChange_riemannForm_apply, latticeConj_apply, hrel]
      norm_num
      simpa using positive_coordinate_I x.1 hfst
    by_cases hpzero : p = 0
    · subst p
      rw [hodgeStructure_piece_zero] at hx
      have hrel := snd_eq_I_mul_fst_of_mem_neg_I hx
      have hfst : x.1 ≠ 0 := by
        intro hzero
        apply hx0
        apply Prod.ext <;> simp [hzero, hrel]
      rw [integralFormBaseChange_riemannForm_apply, latticeConj_apply, hrel]
      norm_num
      simpa using positive_coordinate_neg_I x.1 hfst
    · rw [hodgeStructure_piece_eq_bot hpzero hpone, Submodule.mem_bot] at hx
      exact (hx0 hx).elim

/-- The standard Riemann form bundled as a polarization of the standard weight-one Hodge
structure. -/
noncomputable def polarization :
    Polarization isBaseChange_latticeToComplex hodgeStructure where
  Qint := riemannForm
  isPolarization := isPolarization_riemannForm

end TauCeti.Hodge.StandardWeightOne
