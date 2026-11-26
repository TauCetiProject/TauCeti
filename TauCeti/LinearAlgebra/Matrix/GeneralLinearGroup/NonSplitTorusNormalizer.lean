/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The normalizer of the non-split torus of `GL₂`

Let `E/F` be a field extension of degree `2`. The normalizer of the non-split torus
`TauCeti.GL2NonSplitTorus F E ≅ Eˣ` of `GL₂(F)` consists of the `F`-linear automorphisms of `E` of
the form `v ↦ c τ(v)` with `c ∈ Eˣ` and `τ` an `F`-algebra automorphism of `E`, read in the basis
`TauCeti.nonSplitTorusBasis`. The pair `(c, τ)` is unique, so the normalizer is in bijection with
`Eˣ × Gal(E/F)` (`TauCeti.GL2NonSplitTorus.normalizerEquiv`). Over a finite field with `q`
elements it therefore has `2(q² - 1)` elements, the torus has index `2` in it, and its index in
`GL₂(F)` is `q(q - 1) / 2` (`TauCeti.GL2NonSplitTorus.natCard_normalizer`,
`TauCeti.GL2NonSplitTorus.relIndex_normalizer`,
`TauCeti.GL2NonSplitTorus.two_mul_index_normalizer`). This is the subgroup `C_ns⁺(ℓ)` of the
standard levels of modular curves.

The computation is made for the general linear group of `E` as an `F`-vector space, where the
torus is the image of `Eˣ` under left multiplication `Algebra.lmul F E`
(`TauCeti.lmulUnitsRange`): an automorphism `φ` normalizing it satisfies
`φ ∘ (x ·) = (τ x ·) ∘ φ` for a map `τ`, and evaluating at `1` gives `φ x = τ(x) φ(1)`, so
`τ = φ(1)⁻¹ φ` is multiplicative.

## Main declarations

* `TauCeti.mem_normalizer_lmulUnitsRange_iff`: the normalizer of `Eˣ` in
  `GL_F(E)` consists of the maps `v ↦ c τ(v)`.
* `TauCeti.normalizerLmulUnitsRangeEquiv`: the bijection with `Eˣ × Gal(E/F)`.
* `TauCeti.GL2NonSplitTorus.normalizerEquiv`, `TauCeti.GL2NonSplitTorus.natCard_normalizer`,
  `TauCeti.GL2NonSplitTorus.relIndex_normalizer`,
  `TauCeti.GL2NonSplitTorus.two_mul_index_normalizer`,
  `TauCeti.GL2NonSplitTorus.neg_one_mem_normalizer`.

## References

* D. Zywina, *On the possible images of the mod `ℓ` representations associated to elliptic curves
  over `ℚ`*, arXiv:1508.07660, §1 (Notation).
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

variable (F E) in
/-- The units of `E` acting on `E` by left multiplication, as a subgroup of `GL_F(E)`. -/
noncomputable def lmulUnitsRange : Subgroup (LinearMap.GeneralLinearGroup F E) :=
  (Units.map (Algebra.lmul F E).toMonoidHom).range

omit [Field F] in
private theorem lmul_apply_apply [CommSemiring F] [Algebra F E] (x v : E) :
    Algebra.lmul F E x v = x * v := by
  rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']

/-- The `F`-linear automorphism `v ↦ c τ(v)` of `E`, for `c ∈ Eˣ` and `τ ∈ Gal(E/F)`. -/
noncomputable def mulGaloisEquiv (c : Eˣ) (τ : E ≃ₐ[F] E) : E ≃ₗ[F] E where
  toFun v := c * τ v
  invFun w := τ.symm (c⁻¹ * w)
  map_add' v w := by rw [map_add, mul_add]
  map_smul' a v := by rw [map_smul, mul_smul_comm, RingHom.id_apply]
  left_inv v := by simp
  right_inv w := by simp

/-- The automorphism `v ↦ c τ(v)` of `E` as an element of `GL_F(E)`. -/
noncomputable def mulGalois (c : Eˣ) (τ : E ≃ₐ[F] E) : LinearMap.GeneralLinearGroup F E :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (mulGaloisEquiv c τ)

/-- The value of `v ↦ c τ(v)` at `v`. -/
@[simp]
theorem mulGalois_apply (c : Eˣ) (τ : E ≃ₐ[F] E) (v : E) :
    (mulGalois c τ : E →ₗ[F] E) v = c * τ v :=
  (rfl)

/-- `v ↦ c τ(v)` conjugates multiplication by `x` to multiplication by `τ x`. -/
theorem mulGalois_mul_lmul (c : Eˣ) (τ : E ≃ₐ[F] E) (x : E) :
    (mulGalois c τ : E →ₗ[F] E) * Algebra.lmul F E x =
      Algebra.lmul F E (τ x) * (mulGalois c τ : E →ₗ[F] E) := by
  ext v
  simp only [mul_apply_eq_comp, mulGalois_apply, lmul_apply_apply, map_mul]
  ring

/-- The inverse of `v ↦ c τ(v)` is `w ↦ τ⁻¹(c⁻¹) τ⁻¹(w)`. -/
theorem mulGalois_inv (c : Eˣ) (τ : E ≃ₐ[F] E) :
    (mulGalois c τ)⁻¹ = mulGalois (Units.map (τ.symm : E →* E) c⁻¹) τ.symm := by
  refine inv_eq_of_mul_eq_one_right (Units.ext (LinearMap.ext fun v ↦ ?_))
  simp

/-- Conjugation by `v ↦ c τ(v)` maps the units of `E` acting by multiplication into themselves. -/
theorem mulGalois_conj_mem_lmulUnitsRange (c : Eˣ) (τ : E ≃ₐ[F] E)
    {u : LinearMap.GeneralLinearGroup F E} (hu : u ∈ lmulUnitsRange F E) :
    mulGalois c τ * u * (mulGalois c τ)⁻¹ ∈ lmulUnitsRange F E := by
  obtain ⟨x, rfl⟩ := hu
  refine ⟨Units.map (τ : E →* E) x, Units.ext ?_⟩
  have h := mulGalois_mul_lmul c τ (x : E)
  have h1 : ((mulGalois c τ : LinearMap.GeneralLinearGroup F E) : E →ₗ[F] E) *
      (((mulGalois c τ)⁻¹ : LinearMap.GeneralLinearGroup F E) : E →ₗ[F] E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  change Algebra.lmul F E (τ x) = (mulGalois c τ : E →ₗ[F] E) * Algebra.lmul F E x *
    (((mulGalois c τ)⁻¹ : LinearMap.GeneralLinearGroup F E) : E →ₗ[F] E)
  rw [h, mul_assoc, h1, mul_one]

/-- A unit `φ` with `φ ∘ (x ·) = (τ x ·) ∘ φ` for some `τ` and every `x` is `v ↦ τ(v) φ(1)`. -/
theorem apply_eq_of_mul_lmul {φ : E →ₗ[F] E} {τ : E → E}
    (h : ∀ x, φ * Algebra.lmul F E x = Algebra.lmul F E (τ x) * φ) (v : E) :
    φ v = τ v * φ 1 := by
  simpa [lmul_apply_apply] using congrArg (fun ψ : E →ₗ[F] E ↦ ψ 1) (h v)

section FiniteDimensional

variable [FiniteDimensional F E]

/-- **The normalizer of `Eˣ` in `GL_F(E)`** consists of the maps `v ↦ c τ(v)` with `c ∈ Eˣ` and
`τ ∈ Gal(E/F)`. -/
theorem mem_normalizer_lmulUnitsRange_iff {φ : LinearMap.GeneralLinearGroup F E} :
    φ ∈ Subgroup.normalizer (lmulUnitsRange F E : Set (LinearMap.GeneralLinearGroup F E)) ↔
      ∃ c : Eˣ, ∃ τ : E ≃ₐ[F] E, φ = mulGalois c τ := by
  constructor
  · intro hφ
    -- conjugation by `φ` carries multiplication by `x` to multiplication by some `τ x`
    have hconj (x : E) : ∃ y : E, (φ : E →ₗ[F] E) * Algebra.lmul F E x =
        Algebra.lmul F E y * (φ : E →ₗ[F] E) := by
      obtain rfl | hx := eq_or_ne x 0
      · exact ⟨0, by simp⟩
      obtain ⟨y, hy⟩ := (Subgroup.mem_normalizer_iff.1 hφ
        (Units.map (Algebra.lmul F E).toMonoidHom (Units.mk0 x hx))).1 ⟨_, rfl⟩
      refine ⟨y, ?_⟩
      have := congrArg (fun u : LinearMap.GeneralLinearGroup F E ↦ (u : E →ₗ[F] E) *
        (φ : E →ₗ[F] E)) hy
      simp only [Units.val_mul, Units.coe_map, mul_assoc, Units.inv_mul, mul_one] at this
      exact this.symm
    choose τ hτ using hconj
    have hφ1 : (φ : E →ₗ[F] E) 1 ≠ 0 := fun h0 ↦ one_ne_zero
      ((LinearMap.GeneralLinearGroup.toLinearEquiv φ).injective (h0.trans (map_zero _).symm))
    have hφv := apply_eq_of_mul_lmul hτ
    have hτv (v : E) : τ v = (φ : E →ₗ[F] E) v * ((φ : E →ₗ[F] E) 1)⁻¹ := by
      rw [hφv v, mul_inv_cancel_right₀ hφ1]
    -- `τ` is an `F`-algebra endomorphism of `E`
    let τ' : E →ₐ[F] E :=
      { toFun := τ
        map_one' := by rw [hτv, mul_inv_cancel₀ hφ1]
        map_mul' := fun x y ↦ by
          have h := congrArg (fun ψ : E →ₗ[F] E ↦ ψ y) (hτ x)
          simp only [mul_apply_eq_comp, lmul_apply_apply] at h
          rw [hτv (x * y), h, hτv y]
          ring
        map_zero' := by rw [hτv, map_zero, zero_mul]
        map_add' := fun x y ↦ by rw [hτv, hτv, hτv, map_add, add_mul]
        commutes' := fun a ↦ by
          rw [hτv, Algebra.algebraMap_eq_smul_one, map_smul, smul_mul_assoc,
            mul_inv_cancel₀ hφ1] }
    refine ⟨Units.mk0 _ hφ1, AlgEquiv.ofBijective τ' (AlgHom.bijective τ'), ?_⟩
    ext v
    simp only [mulGalois_apply, Units.val_mk0, AlgEquiv.ofBijective_apply]
    rw [hφv v, mul_comm]
    rfl
  · rintro ⟨c, τ, rfl⟩
    refine Subgroup.mem_normalizer_iff.2 fun u ↦ ?_
    refine ⟨mulGalois_conj_mem_lmulUnitsRange c τ, fun hu ↦ ?_⟩
    have h := mulGalois_conj_mem_lmulUnitsRange (Units.map (τ.symm : E →* E) c⁻¹) τ.symm hu
    rwa [← mulGalois_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
      mul_assoc, inv_mul_cancel, mul_one] at h

omit [FiniteDimensional F E] in
/-- The factorization `v ↦ c τ(v)` is unique. -/
theorem mulGalois_injective :
    Function.Injective fun p : Eˣ × (E ≃ₐ[F] E) ↦ mulGalois p.1 p.2 := by
  rintro ⟨c, τ⟩ ⟨c', τ'⟩ h
  have h' (v : E) := congrArg (fun u : LinearMap.GeneralLinearGroup F E ↦ (u : E →ₗ[F] E) v) h
  simp only [mulGalois_apply] at h'
  have hc : c = c' := Units.ext (by simpa using h' 1)
  subst hc
  exact Prod.ext rfl (AlgEquiv.ext fun v ↦ mul_left_cancel₀ c.ne_zero (h' v))

/-- **The normalizer of `Eˣ` in `GL_F(E)` is in bijection with `Eˣ × Gal(E/F)`**, by
`(c, τ) ↦ (v ↦ c τ(v))`. -/
noncomputable def normalizerLmulUnitsRangeEquiv :
    Eˣ × (E ≃ₐ[F] E) ≃
      Subgroup.normalizer (lmulUnitsRange F E : Set (LinearMap.GeneralLinearGroup F E)) :=
  Equiv.ofBijective
    (fun p ↦ ⟨mulGalois p.1 p.2, mem_normalizer_lmulUnitsRange_iff.2 ⟨p.1, p.2, rfl⟩⟩)
    ⟨fun _ _ h ↦ mulGalois_injective (congrArg Subtype.val h), fun ⟨_, hφ⟩ ↦ by
      obtain ⟨c, τ, rfl⟩ := mem_normalizer_lmulUnitsRange_iff.1 hφ
      exact ⟨(c, τ), rfl⟩⟩

/-- The bijection sends `(c, τ)` to `v ↦ c τ(v)`. -/
@[simp]
theorem coe_normalizerLmulUnitsRangeEquiv_apply (p : Eˣ × (E ≃ₐ[F] E)) :
    (normalizerLmulUnitsRangeEquiv p : LinearMap.GeneralLinearGroup F E) = mulGalois p.1 p.2 :=
  (rfl)

end FiniteDimensional

namespace GL2NonSplitTorus

variable [Algebra.IsQuadraticExtension F E]

/-- The basis isomorphism `GL₂(F) ≃* GL_F(E)` carries the non-split torus to the units of `E`
acting by multiplication. -/
theorem map_toLin' :
    (GL2NonSplitTorus F E).map
        (Matrix.GeneralLinearGroup.toLin' (nonSplitTorusBasis F E)).toMonoidHom =
      lmulUnitsRange F E := by
  have h (x : Eˣ) : Matrix.GeneralLinearGroup.toLin' (nonSplitTorusBasis F E)
      (GL2NonSplitTorusHom F E x) = Units.map (Algebra.lmul F E).toMonoidHom x := by
    refine Units.ext (LinearMap.ext fun v ↦ ?_)
    have := Matrix.GeneralLinearGroup.toLin'_apply (nonSplitTorusBasis F E)
      (GL2NonSplitTorusHom F E x) v
    rw [coe_gl2NonSplitTorusHom, Algebra.leftMulMatrix_mulVec_repr,
      Fintype.linearCombination_apply, Module.Basis.sum_repr] at this
    simpa [lmul_apply_apply] using this
  ext u
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, lmulUnitsRange,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨x, rfl⟩ := mem_iff.1 hg
    exact ⟨x, (h x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, mem_iff.2 ⟨x, rfl⟩, h x⟩

/-- **The normalizer of the non-split torus is in bijection with `Eˣ × Gal(E/F)`.** -/
noncomputable def normalizerEquiv :
    Eˣ × (E ≃ₐ[F] E) ≃ Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F)) :=
  have h : (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))).map
      (Matrix.GeneralLinearGroup.toLin' (nonSplitTorusBasis F E)).toMonoidHom =
      Subgroup.normalizer
        (lmulUnitsRange F E : Set (LinearMap.GeneralLinearGroup F E)) := by
    rw [Subgroup.map_equiv_normalizer_eq, map_toLin']
  normalizerLmulUnitsRangeEquiv.trans ((MulEquiv.subgroupCongr h.symm).toEquiv.trans
    ((Matrix.GeneralLinearGroup.toLin' (nonSplitTorusBasis F E)).subgroupMap _).symm.toEquiv)

/-- **The order of the normalizer of the non-split torus**: over a field with `q` elements it has
`2(q² - 1)` elements. -/
theorem natCard_normalizer [Finite F] :
    Nat.card (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))) =
      2 * (Nat.card F ^ 2 - 1) := by
  have := Module.finite_of_finite F (M := E)
  rw [← Nat.card_congr normalizerEquiv, Nat.card_prod, ← natCard_eq (F := F) (E := E),
    ← Nat.card_congr (unitsEquiv (F := F) (E := E)).toEquiv, IsGalois.card_aut_eq_finrank,
    Algebra.IsQuadraticExtension.finrank_eq_two, mul_comm]

/-- **The index of the normalizer of the non-split torus**: over a field with `q` elements it is
`q(q - 1) / 2`. -/
theorem two_mul_index_normalizer [Finite F] :
    2 * (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))).index =
      Nat.card F * (Nat.card F - 1) := by
  have hq : 0 < Nat.card F ^ 2 - 1 := by
    have : 1 < Nat.card F := Finite.one_lt_card
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow two_ne_zero this
    omega
  have h := (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))).card_mul_index
  rw [natCard_normalizer, natCard_GL_fin_two_eq_sq_sub_one_mul] at h
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  rw [← h]
  ring

/-- The non-split torus has index `2` in its normalizer, over a finite field. -/
theorem relIndex_normalizer [Finite F] :
    (GL2NonSplitTorus F E).relIndex
      (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))) = 2 := by
  have hpos : 0 < (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))).index :=
    Subgroup.index_pos
  have h := Subgroup.relIndex_mul_index (Subgroup.le_normalizer (H := GL2NonSplitTorus F E))
  rw [index_eq, ← two_mul_index_normalizer (E := E)] at h
  exact Nat.eq_of_mul_eq_mul_right hpos h

/-- `-1` lies in the normalizer of the non-split torus. -/
theorem neg_one_mem_normalizer :
    (-1 : GL (Fin 2) F) ∈ Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F)) := by
  refine Subgroup.le_normalizer ?_
  have := scalar_mem (F := F) (E := E) (-1)
  convert this using 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.GeneralLinearGroup.coe_scalar, h]

end GL2NonSplitTorus

end TauCeti
