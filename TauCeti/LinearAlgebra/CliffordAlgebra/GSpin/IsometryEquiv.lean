/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.CliffordGroup
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# Functoriality of the Clifford and general spin groups along isometries

A quadratic isometry equivalence `e : Q₁ ≃ Q₂` over a commutative ring induces an algebra
isomorphism `CliffordAlgebra.equivOfIsometry e : C(Q₁) ≃ C(Q₂)` that commutes with the grade
involution and with reversal and preserves the `ℤ/2`-grading. This file shows, in every
characteristic, that it carries the Clifford group `GPin(Q₁)`, the general spin group `GSpin(Q₁)`,
and the norm-one groups `Pin(Q₁)`, `Spin(Q₁)` onto those of `Q₂`, compatibly with the Clifford
norm `N(g) = star(g) g`, the general spin norm `ν(g) = reverse(g) g`, and the vector action
`ρ : GPin(Q) → O(Q)`, which is transported by conjugation by `e`.

Local homogeneity and evenness are preserved by the map of any isometry; the condition that
twisted conjugation preserves the vectors needs the isometry to be onto.

## Main declarations

* `QuadraticMap.IsometryEquiv.units_map_mem_vectorNormalizer`,
  `QuadraticMap.IsometryEquiv.units_map_mem_vectorNormalizer_iff`: the induced map on Clifford
  units preserves and reflects the vector normalizer.
* `QuadraticMap.IsometryEquiv.cliffordGroupEquiv`,
  `QuadraticMap.IsometryEquiv.specialCliffordGroupEquiv`: `GPin(Q₁) ≃* GPin(Q₂)` and
  `GSpin(Q₁) ≃* GSpin(Q₂)`, with the functor laws `_refl`, `_trans` and `_symm`.
* `QuadraticMap.IsometryEquiv.coe_cliffordGroupNorm_cliffordGroupEquiv`,
  `QuadraticMap.IsometryEquiv.coe_specialCliffordGroupNorm_specialCliffordGroupEquiv`: the norms
  are natural.
* `QuadraticMap.IsometryEquiv.units_map_mem_cliffordGroup_iff`,
  `QuadraticMap.IsometryEquiv.units_map_mem_specialCliffordGroup_iff`,
  `QuadraticMap.IsometryEquiv.units_map_mem_normOnePinGroup_iff`,
  `QuadraticMap.IsometryEquiv.units_map_mem_normOneSpinGroup_iff`: the groups correspond.
* `QuadraticMap.IsometryEquiv.normOnePinGroupEquiv`,
  `QuadraticMap.IsometryEquiv.normOneSpinGroupEquiv`: `Pin(Q₁) ≃* Pin(Q₂)` and
  `Spin(Q₁) ≃* Spin(Q₂)`, with the functor laws `_refl`, `_trans` and `_symm`.
* `QuadraticMap.IsometryEquiv.cliffordGroupToOrthogonal_cliffordGroupEquiv_apply`: the vector
  action is transported by conjugation by `e`.
-/

public section

open CliffordAlgebra

namespace CliffordAlgebra

variable {R : Type*} [CommRing R] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- The map induced by a quadratic isometry preserves local homogeneity. -/
theorem IsLocallyHomogeneous.map (f : Q₁ →qᵢ Q₂) {x : CliffordAlgebra Q₁}
    (hx : IsLocallyHomogeneous x) : IsLocallyHomogeneous (map f x) := by
  obtain ⟨r, hr, h0, h1⟩ := isLocallyHomogeneous_iff.mp hx
  exact isLocallyHomogeneous_iff.mpr ⟨r, hr, by rw [← map_smul]; exact map_mem_evenOdd f h0,
    by rw [← map_smul]; exact map_mem_evenOdd f h1⟩

end CliffordAlgebra

namespace QuadraticMap.IsometryEquiv

variable {R : Type*} [CommRing R] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Twisted conjugation conditions transport along the Clifford algebra isomorphism of an
isometry equivalence. -/
private theorem involute_mul_ι_mul_mem_range (e : Q₁.IsometryEquiv Q₂) {a b : CliffordAlgebra Q₁}
    (h : ∀ m, involute a * ι Q₁ m * b ∈ LinearMap.range (ι Q₁)) (m : M₂) :
    involute (equivOfIsometry e a) * ι Q₂ m * equivOfIsometry e b ∈ LinearMap.range (ι Q₂) := by
  obtain ⟨w, hw⟩ := h (e.symm m)
  refine ⟨e w, ?_⟩
  rw [← equivOfIsometry_ι, hw, map_mul, map_mul, equivOfIsometry_ι, e.apply_symm_apply,
    equivOfIsometry_apply e (involute a), map_involute, ← equivOfIsometry_apply]

/-- **An isometry equivalence preserves the vector normalizer**: the induced map on Clifford
units sends `vectorNormalizer Q₁` into `vectorNormalizer Q₂`. -/
theorem units_map_mem_vectorNormalizer (e : Q₁.IsometryEquiv Q₂) {x : (CliffordAlgebra Q₁)ˣ}
    (hx : x ∈ vectorNormalizer Q₁) :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      vectorNormalizer Q₂ := by
  rw [mem_vectorNormalizer_iff] at hx ⊢
  rw [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_ofClass]
  exact ⟨involute_mul_ι_mul_mem_range e hx.1, involute_mul_ι_mul_mem_range e hx.2⟩

/-- An isometry equivalence maps exactly the vector normalizer into the vector normalizer. -/
theorem units_map_mem_vectorNormalizer_iff (e : Q₁.IsometryEquiv Q₂)
    {x : (CliffordAlgebra Q₁)ˣ} :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      vectorNormalizer Q₂ ↔ x ∈ vectorNormalizer Q₁ := by
  refine ⟨fun h => ?_, units_map_mem_vectorNormalizer e⟩
  have := units_map_mem_vectorNormalizer e.symm h
  rwa [units_map_equivOfIsometry_symm_units_map] at this

/-- An isometry equivalence maps the Clifford group into the Clifford group. -/
theorem units_map_mem_cliffordGroup (e : Q₁.IsometryEquiv Q₂) {x : (CliffordAlgebra Q₁)ˣ}
    (hx : x ∈ cliffordGroup Q₁) :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      cliffordGroup Q₂ := by
  rw [mem_cliffordGroup_iff] at hx ⊢
  refine ⟨units_map_mem_vectorNormalizer e hx.1, ?_⟩
  rw [Units.coe_map, MonoidHom.coe_ofClass, equivOfIsometry_apply]
  exact hx.2.map e.toIsometry

/-- **The Clifford group corresponds under an isometry equivalence.** -/
theorem units_map_mem_cliffordGroup_iff (e : Q₁.IsometryEquiv Q₂)
    {x : (CliffordAlgebra Q₁)ˣ} :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      cliffordGroup Q₂ ↔ x ∈ cliffordGroup Q₁ := by
  refine ⟨fun h => ?_, units_map_mem_cliffordGroup e⟩
  have := units_map_mem_cliffordGroup e.symm h
  rwa [units_map_equivOfIsometry_symm_units_map] at this

/-- An isometry equivalence maps the general spin group into the general spin group. -/
theorem units_map_mem_specialCliffordGroup (e : Q₁.IsometryEquiv Q₂) {x : (CliffordAlgebra Q₁)ˣ}
    (hx : x ∈ specialCliffordGroup Q₁) :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      specialCliffordGroup Q₂ := by
  rw [mem_specialCliffordGroup_iff] at hx ⊢
  refine ⟨units_map_mem_vectorNormalizer e hx.1, ?_⟩
  rw [Units.coe_map, MonoidHom.coe_ofClass, equivOfIsometry_apply]
  exact map_mem_even e.toIsometry hx.2

/-- **The general spin group corresponds under an isometry equivalence.** -/
theorem units_map_mem_specialCliffordGroup_iff (e : Q₁.IsometryEquiv Q₂)
    {x : (CliffordAlgebra Q₁)ˣ} :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      specialCliffordGroup Q₂ ↔ x ∈ specialCliffordGroup Q₁ := by
  refine ⟨fun h => ?_, units_map_mem_specialCliffordGroup e⟩
  have := units_map_mem_specialCliffordGroup e.symm h
  rwa [units_map_equivOfIsometry_symm_units_map] at this

/-- **The Clifford group is functorial along isometry equivalences**: `GPin(Q₁) ≃* GPin(Q₂)`,
the restriction of `CliffordAlgebra.equivOfIsometry`. -/
noncomputable def cliffordGroupEquiv (e : Q₁.IsometryEquiv Q₂) :
    cliffordGroup Q₁ ≃* cliffordGroup Q₂ where
  toFun x := ⟨_, units_map_mem_cliffordGroup e x.property⟩
  invFun x := ⟨_, units_map_mem_cliffordGroup e.symm x.property⟩
  left_inv x := Subtype.ext (units_map_equivOfIsometry_symm_units_map e x)
  right_inv x := Subtype.ext (units_map_equivOfIsometry_symm_units_map e.symm x)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The equivalence of Clifford groups is the Clifford algebra isomorphism. -/
@[simp]
theorem coe_cliffordGroupEquiv_apply (e : Q₁.IsometryEquiv Q₂) (x : cliffordGroup Q₁) :
    (((e.cliffordGroupEquiv x : (CliffordAlgebra Q₂)ˣ)) : CliffordAlgebra Q₂) =
      equivOfIsometry e ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) :=
  (rfl)

/-- The inverse of the equivalence of Clifford groups is the equivalence of `e.symm`. -/
@[simp]
theorem cliffordGroupEquiv_symm (e : Q₁.IsometryEquiv Q₂) :
    e.cliffordGroupEquiv.symm = e.symm.cliffordGroupEquiv :=
  (rfl)

/-- The identity isometry induces the identity equivalence of Clifford groups. -/
@[simp]
theorem cliffordGroupEquiv_refl (Q₁ : QuadraticForm R M₁) :
    (IsometryEquiv.refl Q₁).cliffordGroupEquiv = MulEquiv.refl (cliffordGroup Q₁) :=
  MulEquiv.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [coe_cliffordGroupEquiv_apply, equivOfIsometry_refl, AlgEquiv.coe_refl, id_eq,
      MulEquiv.refl_apply]

/-- The equivalences of Clifford groups respect composition of isometry equivalences. -/
@[simp]
theorem cliffordGroupEquiv_trans {M₃ : Type*} [AddCommGroup M₃] [Module R M₃]
    {Q₃ : QuadraticForm R M₃} (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (e₁₂.trans e₂₃).cliffordGroupEquiv = e₁₂.cliffordGroupEquiv.trans e₂₃.cliffordGroupEquiv :=
  MulEquiv.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [coe_cliffordGroupEquiv_apply, MulEquiv.trans_apply, coe_cliffordGroupEquiv_apply,
      coe_cliffordGroupEquiv_apply, ← equivOfIsometry_trans, AlgEquiv.trans_apply]

/-- **The general spin group is functorial along isometry equivalences**:
`GSpin(Q₁) ≃* GSpin(Q₂)`, the restriction of `CliffordAlgebra.equivOfIsometry`. -/
noncomputable def specialCliffordGroupEquiv (e : Q₁.IsometryEquiv Q₂) :
    specialCliffordGroup Q₁ ≃* specialCliffordGroup Q₂ where
  toFun x := ⟨_, units_map_mem_specialCliffordGroup e x.property⟩
  invFun x := ⟨_, units_map_mem_specialCliffordGroup e.symm x.property⟩
  left_inv x := Subtype.ext (units_map_equivOfIsometry_symm_units_map e x)
  right_inv x := Subtype.ext (units_map_equivOfIsometry_symm_units_map e.symm x)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The equivalence of general spin groups is the Clifford algebra isomorphism. -/
@[simp]
theorem coe_specialCliffordGroupEquiv_apply (e : Q₁.IsometryEquiv Q₂)
    (x : specialCliffordGroup Q₁) :
    (((e.specialCliffordGroupEquiv x : (CliffordAlgebra Q₂)ˣ)) : CliffordAlgebra Q₂) =
      equivOfIsometry e ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) :=
  (rfl)

/-- The inverse of the equivalence of general spin groups is the equivalence of `e.symm`. -/
@[simp]
theorem specialCliffordGroupEquiv_symm (e : Q₁.IsometryEquiv Q₂) :
    e.specialCliffordGroupEquiv.symm = e.symm.specialCliffordGroupEquiv :=
  (rfl)

/-- The identity isometry induces the identity equivalence of general spin groups. -/
@[simp]
theorem specialCliffordGroupEquiv_refl (Q₁ : QuadraticForm R M₁) :
    (IsometryEquiv.refl Q₁).specialCliffordGroupEquiv =
      MulEquiv.refl (specialCliffordGroup Q₁) :=
  MulEquiv.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [coe_specialCliffordGroupEquiv_apply, equivOfIsometry_refl, AlgEquiv.coe_refl, id_eq,
      MulEquiv.refl_apply]

/-- The equivalences of general spin groups respect composition of isometry equivalences. -/
@[simp]
theorem specialCliffordGroupEquiv_trans {M₃ : Type*} [AddCommGroup M₃] [Module R M₃]
    {Q₃ : QuadraticForm R M₃} (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (e₁₂.trans e₂₃).specialCliffordGroupEquiv =
      e₁₂.specialCliffordGroupEquiv.trans e₂₃.specialCliffordGroupEquiv :=
  MulEquiv.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [coe_specialCliffordGroupEquiv_apply, MulEquiv.trans_apply,
      coe_specialCliffordGroupEquiv_apply, coe_specialCliffordGroupEquiv_apply,
      ← equivOfIsometry_trans, AlgEquiv.trans_apply]

/-- **The Clifford norm is natural**: `N(e g) = e(N(g))`. -/
theorem coe_cliffordGroupNorm_cliffordGroupEquiv (e : Q₁.IsometryEquiv Q₂)
    (x : cliffordGroup Q₁) :
    (((cliffordGroupNorm Q₂ (e.cliffordGroupEquiv x) : (CliffordAlgebra Q₂)ˣ)) :
        CliffordAlgebra Q₂) =
      equivOfIsometry e (((cliffordGroupNorm Q₁ x : (CliffordAlgebra Q₁)ˣ)) :
        CliffordAlgebra Q₁) := by
  rw [coe_cliffordGroupNorm, coe_cliffordGroupNorm, coe_cliffordGroupEquiv_apply, map_mul,
    equivOfIsometry_apply, equivOfIsometry_apply, CliffordAlgebra.map_star]

/-- **The general spin norm is natural**: `ν(e g) = e(ν(g))`. -/
theorem coe_specialCliffordGroupNorm_specialCliffordGroupEquiv (e : Q₁.IsometryEquiv Q₂)
    (x : specialCliffordGroup Q₁) :
    (((specialCliffordGroupNorm Q₂ (e.specialCliffordGroupEquiv x) : (CliffordAlgebra Q₂)ˣ)) :
        CliffordAlgebra Q₂) =
      equivOfIsometry e (((specialCliffordGroupNorm Q₁ x : (CliffordAlgebra Q₁)ˣ)) :
        CliffordAlgebra Q₁) := by
  rw [coe_specialCliffordGroupNorm, coe_specialCliffordGroupNorm,
    coe_specialCliffordGroupEquiv_apply, map_mul, equivOfIsometry_apply, equivOfIsometry_apply,
    CliffordAlgebra.map_reverse]

/-- An isometry equivalence maps `Pin` into `Pin`. -/
theorem units_map_mem_normOnePinGroup (e : Q₁.IsometryEquiv Q₂) {x : (CliffordAlgebra Q₁)ˣ}
    (hx : x ∈ normOnePinGroup Q₁) :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      normOnePinGroup Q₂ := by
  rw [mem_normOnePinGroup_iff] at hx ⊢
  refine ⟨units_map_mem_cliffordGroup e hx.1, ?_⟩
  rw [Units.coe_map, MonoidHom.coe_ofClass, equivOfIsometry_apply, ← CliffordAlgebra.map_star,
    ← map_mul, hx.2, map_one]

/-- An isometry equivalence maps `Spin` into `Spin`. -/
theorem units_map_mem_normOneSpinGroup (e : Q₁.IsometryEquiv Q₂) {x : (CliffordAlgebra Q₁)ˣ}
    (hx : x ∈ normOneSpinGroup Q₁) :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      normOneSpinGroup Q₂ := by
  rw [mem_normOneSpinGroup_iff] at hx ⊢
  refine ⟨units_map_mem_specialCliffordGroup e hx.1, ?_⟩
  rw [Units.coe_map, MonoidHom.coe_ofClass, equivOfIsometry_apply, ← CliffordAlgebra.map_reverse,
    ← map_mul, hx.2, map_one]

/-- **`Pin` corresponds under an isometry equivalence.** -/
theorem units_map_mem_normOnePinGroup_iff (e : Q₁.IsometryEquiv Q₂)
    {x : (CliffordAlgebra Q₁)ˣ} :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      normOnePinGroup Q₂ ↔ x ∈ normOnePinGroup Q₁ := by
  refine ⟨fun h => ?_, units_map_mem_normOnePinGroup e⟩
  have := units_map_mem_normOnePinGroup e.symm h
  rwa [units_map_equivOfIsometry_symm_units_map] at this

/-- **`Spin` corresponds under an isometry equivalence.** -/
theorem units_map_mem_normOneSpinGroup_iff (e : Q₁.IsometryEquiv Q₂)
    {x : (CliffordAlgebra Q₁)ˣ} :
    Units.map (equivOfIsometry e : CliffordAlgebra Q₁ →* CliffordAlgebra Q₂) x ∈
      normOneSpinGroup Q₂ ↔ x ∈ normOneSpinGroup Q₁ := by
  refine ⟨fun h => ?_, units_map_mem_normOneSpinGroup e⟩
  have := units_map_mem_normOneSpinGroup e.symm h
  rwa [units_map_equivOfIsometry_symm_units_map] at this

/-- **`Pin` is functorial along isometry equivalences**: `Pin(Q₁) ≃* Pin(Q₂)`, the restriction
of `CliffordAlgebra.equivOfIsometry`. -/
noncomputable def normOnePinGroupEquiv (e : Q₁.IsometryEquiv Q₂) :
    normOnePinGroup Q₁ ≃* normOnePinGroup Q₂ where
  toFun x := ⟨_, units_map_mem_normOnePinGroup e x.property⟩
  invFun x := ⟨_, units_map_mem_normOnePinGroup e.symm x.property⟩
  left_inv x := Subtype.ext (units_map_equivOfIsometry_symm_units_map e x)
  right_inv x := Subtype.ext (units_map_equivOfIsometry_symm_units_map e.symm x)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The equivalence of `Pin` groups is the Clifford algebra isomorphism. -/
@[simp]
theorem coe_normOnePinGroupEquiv_apply (e : Q₁.IsometryEquiv Q₂) (x : normOnePinGroup Q₁) :
    (((e.normOnePinGroupEquiv x : (CliffordAlgebra Q₂)ˣ)) : CliffordAlgebra Q₂) =
      equivOfIsometry e ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) :=
  (rfl)

/-- The inverse of the equivalence of `Pin` groups is the equivalence of `e.symm`. -/
@[simp]
theorem normOnePinGroupEquiv_symm (e : Q₁.IsometryEquiv Q₂) :
    e.normOnePinGroupEquiv.symm = e.symm.normOnePinGroupEquiv :=
  (rfl)

/-- The identity isometry induces the identity equivalence of `Pin` groups. -/
@[simp]
theorem normOnePinGroupEquiv_refl (Q₁ : QuadraticForm R M₁) :
    (IsometryEquiv.refl Q₁).normOnePinGroupEquiv = MulEquiv.refl (normOnePinGroup Q₁) :=
  MulEquiv.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [coe_normOnePinGroupEquiv_apply, equivOfIsometry_refl, AlgEquiv.coe_refl, id_eq,
      MulEquiv.refl_apply]

/-- The equivalences of `Pin` groups respect composition of isometry equivalences. -/
@[simp]
theorem normOnePinGroupEquiv_trans {M₃ : Type*} [AddCommGroup M₃] [Module R M₃]
    {Q₃ : QuadraticForm R M₃} (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (e₁₂.trans e₂₃).normOnePinGroupEquiv =
      e₁₂.normOnePinGroupEquiv.trans e₂₃.normOnePinGroupEquiv :=
  MulEquiv.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [coe_normOnePinGroupEquiv_apply, MulEquiv.trans_apply, coe_normOnePinGroupEquiv_apply,
      coe_normOnePinGroupEquiv_apply, ← equivOfIsometry_trans, AlgEquiv.trans_apply]

/-- **`Spin` is functorial along isometry equivalences**: `Spin(Q₁) ≃* Spin(Q₂)`, the restriction
of `CliffordAlgebra.equivOfIsometry`. -/
noncomputable def normOneSpinGroupEquiv (e : Q₁.IsometryEquiv Q₂) :
    normOneSpinGroup Q₁ ≃* normOneSpinGroup Q₂ where
  toFun x := ⟨_, units_map_mem_normOneSpinGroup e x.property⟩
  invFun x := ⟨_, units_map_mem_normOneSpinGroup e.symm x.property⟩
  left_inv x := Subtype.ext (units_map_equivOfIsometry_symm_units_map e x)
  right_inv x := Subtype.ext (units_map_equivOfIsometry_symm_units_map e.symm x)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The equivalence of `Spin` groups is the Clifford algebra isomorphism. -/
@[simp]
theorem coe_normOneSpinGroupEquiv_apply (e : Q₁.IsometryEquiv Q₂) (x : normOneSpinGroup Q₁) :
    (((e.normOneSpinGroupEquiv x : (CliffordAlgebra Q₂)ˣ)) : CliffordAlgebra Q₂) =
      equivOfIsometry e ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) :=
  (rfl)

/-- The inverse of the equivalence of `Spin` groups is the equivalence of `e.symm`. -/
@[simp]
theorem normOneSpinGroupEquiv_symm (e : Q₁.IsometryEquiv Q₂) :
    e.normOneSpinGroupEquiv.symm = e.symm.normOneSpinGroupEquiv :=
  (rfl)

/-- The identity isometry induces the identity equivalence of `Spin` groups. -/
@[simp]
theorem normOneSpinGroupEquiv_refl (Q₁ : QuadraticForm R M₁) :
    (IsometryEquiv.refl Q₁).normOneSpinGroupEquiv = MulEquiv.refl (normOneSpinGroup Q₁) :=
  MulEquiv.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [coe_normOneSpinGroupEquiv_apply, equivOfIsometry_refl, AlgEquiv.coe_refl, id_eq,
      MulEquiv.refl_apply]

/-- The equivalences of `Spin` groups respect composition of isometry equivalences. -/
@[simp]
theorem normOneSpinGroupEquiv_trans {M₃ : Type*} [AddCommGroup M₃] [Module R M₃]
    {Q₃ : QuadraticForm R M₃} (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (e₁₂.trans e₂₃).normOneSpinGroupEquiv =
      e₁₂.normOneSpinGroupEquiv.trans e₂₃.normOneSpinGroupEquiv :=
  MulEquiv.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [coe_normOneSpinGroupEquiv_apply, MulEquiv.trans_apply, coe_normOneSpinGroupEquiv_apply,
      coe_normOneSpinGroupEquiv_apply, ← equivOfIsometry_trans, AlgEquiv.trans_apply]

/-- **The vector action is transported by conjugation**: `ρ(e g) = e ∘ ρ(g) ∘ e⁻¹`, whenever `ι`
and the scalars embed in both Clifford algebras. -/
theorem cliffordGroupToOrthogonal_cliffordGroupEquiv_apply (e : Q₁.IsometryEquiv Q₂)
    (hι₁ : Function.Injective (ι Q₁))
    (hinj₁ : Function.Injective (algebraMap R (CliffordAlgebra Q₁)))
    (hι₂ : Function.Injective (ι Q₂))
    (hinj₂ : Function.Injective (algebraMap R (CliffordAlgebra Q₂))) (x : cliffordGroup Q₁)
    (m : M₂) :
    (cliffordGroupToOrthogonal Q₂ hι₂ hinj₂ (e.cliffordGroupEquiv x) : M₂ ≃ₗ[R] M₂) m =
      e ((cliffordGroupToOrthogonal Q₁ hι₁ hinj₁ x : M₁ ≃ₗ[R] M₁) (e.symm m)) := by
  apply hι₂
  have hm : ι Q₂ m = equivOfIsometry e (ι Q₁ (e.symm m)) := by
    rw [equivOfIsometry_ι, e.apply_symm_apply]
  rw [ι_cliffordGroupToOrthogonal_apply, ← equivOfIsometry_ι, ι_cliffordGroupToOrthogonal_apply,
    hm, ← Subgroup.coe_inv, ← map_inv, coe_cliffordGroupEquiv_apply,
    coe_cliffordGroupEquiv_apply, Subgroup.coe_inv, map_mul, map_mul,
    equivOfIsometry_apply e (involute _), CliffordAlgebra.map_involute, ← equivOfIsometry_apply]

end QuadraticMap.IsometryEquiv
