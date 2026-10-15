/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Classification
public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Kernel

/-!
# The hyperbolic base action of the Sasaki isometry group

Every isometry of the universal-cover Sasaki model descends to a unique isometry of
the hyperbolic plane. The descent respects composition, giving `baseIsomHom`. Its
kernel is exactly the subgroup of vertical translations, canonically isomorphic to
the additive group of real numbers. Two lifts of the same base isometry differ by a
unique vertical translation. Conjugation acts on this kernel by a single sign.

These results identify the kernel in the full isometry-group classification. They do
not assert that every hyperbolic isometry has a lift: surjectivity of `baseIsomHom`
is a separate question.

The construction uses `existsUnique_isometry_projection_eq_of_isometry` for descent,
`eq_translate_of_base_eq` for the kernel, and `exists_apply_vertical_eq` for conjugation.
Reference: P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc.
15 (1983), Section 4, pp. 464–465 (the unit-tangent-bundle model).
-/

public noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "J" => 𝓘(ℝ, ℝ × ℝ × ℝ)
local notation "K" => 𝓘(ℝ, WithLp 2 (ℝ × ℝ))

private def baseIsom (Φ : Isom J SL2Tilde) : Isom K (UpperHalfSpace ℝ) :=
  Classical.choose (existsUnique_isometry_projection_eq_of_isometry Φ)

private theorem baseIsom_projection (Φ : Isom J SL2Tilde) (p : SL2Tilde) :
    baseIsom Φ (projection p) = projection (Φ p) :=
  (Classical.choose_spec (existsUnique_isometry_projection_eq_of_isometry Φ)).1 p

/-- The action of all Sasaki isometries on the hyperbolic base, as a group homomorphism. -/
def baseIsomHom : Isom J SL2Tilde →* Isom K (UpperHalfSpace ℝ) where
  toFun := baseIsom
  map_one' := by
    apply RiemannianIsometry.ext
    intro q
    obtain ⟨p, rfl⟩ := projection_surjective q
    simp only [baseIsom_projection, RiemannianIsometry.one_apply]
  map_mul' Φ Ψ := by
    apply RiemannianIsometry.ext
    intro q
    obtain ⟨p, rfl⟩ := projection_surjective q
    simp only [RiemannianIsometry.mul_apply, baseIsom_projection]

/-- The descended isometry commutes with projection. -/
@[simp] theorem baseIsomHom_apply_projection (Φ : Isom J SL2Tilde) (p : SL2Tilde) :
    baseIsomHom Φ (projection p) = projection (Φ p) :=
  baseIsom_projection Φ p

/-- Evaluate the base action by lifting a point with the canonical projection section. -/
theorem baseIsomHom_apply (Φ : Isom J SL2Tilde) (q : UpperHalfSpace ℝ) :
    baseIsomHom Φ q = projection (Φ (projectionSection q)) := by
  simpa only [projection_projectionSection] using
    baseIsomHom_apply_projection Φ (projectionSection q)

/-- The base action is the unique isometry commuting with projection. -/
theorem baseIsomHom_eq_iff (Φ : Isom J SL2Tilde) (Ψ : Isom K (UpperHalfSpace ℝ)) :
    baseIsomHom Φ = Ψ ↔ ∀ p, Ψ (projection p) = projection (Φ p) := by
  constructor
  · rintro rfl
    exact baseIsomHom_apply_projection Φ
  · intro h
    apply RiemannianIsometry.ext
    intro q
    obtain ⟨p, rfl⟩ := projection_surjective q
    exact (baseIsomHom_apply_projection Φ p).trans (h p).symm

/-- The explicit affine Sasaki lifts induce the corresponding hyperbolic similarities;
their fibre-translation parameter has no effect on the base. -/
@[simp] theorem baseIsomHom_translate (a s c : ℝ) :
    baseIsomHom (translate a s c) =
      UpperHalfSpace.similarity (Real.exp s) (Real.exp_pos s) (.refl ℝ ℝ) a :=
  (baseIsomHom_eq_iff _ _).mpr (fun p => (projection_translate a s c p).symm)

/-- Vertical translation is a faithful action of the additive group of real numbers.
`Multiplicative` expresses this additive parameter as the source of a group homomorphism. -/
def fiberTranslationHom : Multiplicative ℝ →* Isom J SL2Tilde where
  toFun c := translate 0 0 c.toAdd
  map_one' := translate_zero
  map_mul' c d := by simp [translate_mul_translate]

/-- The fibre-translation action is the existing explicit Sasaki translation. -/
@[simp] theorem fiberTranslationHom_apply (c : Multiplicative ℝ) :
    fiberTranslationHom c = translate 0 0 c.toAdd := (rfl)

/-- Distinct translation parameters give distinct isometries. -/
theorem fiberTranslationHom_injective : Injective fiberTranslationHom := by
  intro c d h
  exact congrArg Multiplicative.ofAdd ((translate_inj.mp h).2.2)

/-- An isometry acts trivially on the base precisely when it is a vertical translation. -/
theorem mem_ker_baseIsomHom_iff (Φ : Isom J SL2Tilde) :
    Φ ∈ baseIsomHom.ker ↔ ∃ c : ℝ, Φ = translate 0 0 c := by
  rw [MonoidHom.mem_ker, baseIsomHom_eq_iff]
  constructor
  · intro h
    have hbase (p : SL2Tilde) : projection (Φ p) = projection p := by
      simpa only [RiemannianIsometry.one_apply] using (h p).symm
    have hxy := fun p => (projection_eq_projection_iff (Φ p) p).mp (hbase p)
    exact ⟨(Φ (mk 0 0 0)).z,
      eq_translate_of_base_eq Φ (fun p => (hxy p).1) (fun p => (hxy p).2)⟩
  · rintro ⟨c, rfl⟩ p
    rw [RiemannianIsometry.one_apply, projection_eq_projection_iff]
    simp

/-- The kernel of the hyperbolic base action is exactly the vertical-translation subgroup. -/
theorem ker_baseIsomHom : baseIsomHom.ker = fiberTranslationHom.range := by
  ext Φ
  rw [mem_ker_baseIsomHom_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c.toAdd, rfl⟩

/-- The vertical-translation parameter identifies the kernel with the additive real line.
The inverse reads the fibre coordinate of the image of the origin. -/
def fiberTranslationKerEquiv : Multiplicative ℝ ≃* baseIsomHom.ker where
  toFun c := ⟨fiberTranslationHom c, (mem_ker_baseIsomHom_iff _).mpr ⟨c.toAdd, rfl⟩⟩
  invFun Φ := Multiplicative.ofAdd ((Φ.1 (mk 0 0 0)).z)
  left_inv c := by simp
  right_inv Φ := by
    apply Subtype.ext
    obtain ⟨c, hc⟩ := (mem_ker_baseIsomHom_iff Φ.1).mp Φ.2
    simp [hc]
  map_mul' c d := Subtype.ext (map_mul fiberTranslationHom c d)

/-- The kernel equivalence acts by vertical translation. -/
@[simp] theorem fiberTranslationKerEquiv_apply (c : Multiplicative ℝ) :
    (fiberTranslationKerEquiv c).1 = translate 0 0 c.toAdd := (rfl)

/-- Recover the translation parameter from the image of the origin. -/
@[simp] theorem fiberTranslationKerEquiv_symm_apply (Φ : baseIsomHom.ker) :
    fiberTranslationKerEquiv.symm Φ = Multiplicative.ofAdd ((Φ.1 (mk 0 0 0)).z) := (rfl)

/-- Two lifts of one hyperbolic isometry differ by exactly one vertical translation. -/
theorem baseIsomHom_eq_iff_existsUnique_translate_mul (Φ Ψ : Isom J SL2Tilde) :
    baseIsomHom Φ = baseIsomHom Ψ ↔ ∃! c : ℝ, Φ = translate 0 0 c * Ψ := by
  constructor
  · intro h
    have hxy (p : SL2Tilde) : (Φ p).x = (Ψ p).x ∧ (Φ p).y = (Ψ p).y := by
      apply (projection_eq_projection_iff _ _).mp
      rw [← baseIsomHom_apply_projection, ← baseIsomHom_apply_projection, h]
    exact existsUnique_translate_mul_of_base_eq Φ Ψ
      (fun p => (hxy p).1) (fun p => (hxy p).2)
  · rintro ⟨c, rfl, _⟩
    have hc := (mem_ker_baseIsomHom_iff (translate 0 0 c)).mpr ⟨c, rfl⟩
    simp only [map_mul, MonoidHom.mem_ker.mp hc, one_mul]

/-- Conjugation by an arbitrary Sasaki isometry acts on every vertical translation
by the same sign. In particular, fibre-reversing isometries invert this kernel. -/
theorem exists_conj_translate_eq (Φ : Isom J SL2Tilde) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ c : ℝ, Φ * translate 0 0 c * Φ⁻¹ = translate 0 0 (ε * c) := by
  obtain ⟨ε, hε, hΦ⟩ := exists_apply_vertical_eq Φ
  refine ⟨ε, hε, fun c => ?_⟩
  apply RiemannianIsometry.ext
  intro p
  have ht : translate 0 0 c (Φ⁻¹ p) =
      mk (Φ⁻¹ p).x (Φ⁻¹ p).y ((Φ⁻¹ p).z + c) := by ext <;> simp
  simp only [RiemannianIsometry.mul_apply]
  rw [ht, hΦ]
  simp only [RiemannianIsometry.inv_apply, RiemannianIsometry.apply_symm_apply]
  ext <;> simp

end TauCeti.SL2Tilde
