/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Functoriality of multiplier algebras of C⋆-algebras

Mathlib's multiplier algebra `𝓜(𝕜, A)` consists of double centralizers `(L, R)`. This file
proves that, when `A` has a proper star (for example, when it is a C⋆-ring), the left and right
centralizers are module maps for right and left multiplication respectively, so that the
products of a multiplier with an element of `A` are again elements of `A`, and the canonical
map `A → 𝓜(𝕜, A)` is injective. For C⋆-algebras this map is isometric.

A star-algebra equivalence `e : A ≃⋆ₐ[ℂ] B` of complex C⋆-algebras extends to a star-algebra
equivalence `DoubleCentralizer.congr e : 𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, B)`, sending `(L, R)` to
`(e ∘ L ∘ e⁻¹, e ∘ R ∘ e⁻¹)`. It is compatible with the inclusions of `A` and `B`, and it is
the only multiplicative map with this property. Applied to the automorphisms of a C⋆-dynamical
system, this gives the induced action on the multiplier algebra.

## References

* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Section 2.3, for multiplier algebras.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for the extension of
  automorphisms to multiplier algebras.
-/

public section

noncomputable section

open scoped MultiplierAlgebra

namespace DoubleCentralizer

section ProperStar

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [StarRing A] [IsProperStar A]

/-- The left centralizer of a multiplier commutes with right multiplication. -/
theorem fst_mul (m : 𝓜(𝕜, A)) (a b : A) : m.fst (a * b) = m.fst a * b := by
  have h : ∀ y : A, y * (m.fst (a * b) - m.fst a * b) = 0 := fun y => by
    simp [mul_sub, ← m.central, ← mul_assoc]
  exact sub_eq_zero.mp (star_mul_self_eq_zero.mp (h _))

/-- The right centralizer of a multiplier commutes with left multiplication. -/
theorem snd_mul (m : 𝓜(𝕜, A)) (a b : A) : m.snd (a * b) = a * m.snd b := by
  have h : ∀ y : A, (m.snd (a * b) - a * m.snd b) * y = 0 := fun y => by
    simp [sub_mul, mul_assoc, m.central]
  exact sub_eq_zero.mp (mul_star_self_eq_zero.mp (h _))

/-- A multiplier times an element of `A` is the element obtained from the left centralizer. -/
@[simp]
theorem mul_coe_eq_coe_fst (m : 𝓜(𝕜, A)) (a : A) : m * (a : 𝓜(𝕜, A)) = (m.fst a : 𝓜(𝕜, A)) :=
  DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun b => by simp [fst_mul])
    (ContinuousLinearMap.ext fun b => by simp [m.central])

/-- An element of `A` times a multiplier is the element obtained from the right centralizer. -/
@[simp]
theorem coe_mul_eq_coe_snd (a : A) (m : 𝓜(𝕜, A)) : (a : 𝓜(𝕜, A)) * m = (m.snd a : 𝓜(𝕜, A)) :=
  DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun b => by simp [m.central])
    (ContinuousLinearMap.ext fun b => by simp [snd_mul])

/-- The canonical map of `A` into its multiplier algebra is injective. -/
theorem coe_injective : Function.Injective (DoubleCentralizer.coe 𝕜 : A → 𝓜(𝕜, A)) := by
  intro a b h
  have h' : (a - b) * star (a - b) = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact congrArg (fun m : 𝓜(𝕜, A) => m.fst (star (a - b))) h
  exact sub_eq_zero.mp (mul_star_self_eq_zero.mp h')

@[simp, norm_cast]
theorem coe_inj {a b : A} : (a : 𝓜(𝕜, A)) = b ↔ a = b :=
  coe_injective.eq_iff

end ProperStar

section CStarAlgebra

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- The inclusion of a C⋆-algebra into its multiplier algebra is isometric. -/
@[simp, norm_cast]
theorem norm_coe (a : A) : ‖(a : 𝓜(ℂ, A))‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (coeHom (𝕜 := ℂ) (A := A)) coe_injective a

theorem isometry_coe : Isometry (DoubleCentralizer.coe ℂ : A → 𝓜(ℂ, A)) :=
  NonUnitalStarAlgHom.isometry (coeHom (𝕜 := ℂ) (A := A)) coe_injective

/-- Conjugation of a continuous linear endomorphism by a star-algebra equivalence. Mathlib's
`ContinuousLinearEquiv.conjContinuousAlgEquiv` would need `e` bundled as a continuous linear
equivalence, which Mathlib does not provide for star-algebra equivalences. -/
private def conjCLM (e : A ≃⋆ₐ[ℂ] B) (f : A →L[ℂ] A) : B →L[ℂ] B where
  toFun b := e (f (e.symm b))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := (StarAlgEquiv.isometry e).continuous.comp <|
    f.continuous.comp (StarAlgEquiv.isometry e.symm).continuous

@[simp]
private theorem conjCLM_apply (e : A ≃⋆ₐ[ℂ] B) (f : A →L[ℂ] A) (b : B) :
    conjCLM e f b = e (f (e.symm b)) :=
  (rfl)

/-- The multiplier `(e ∘ L ∘ e⁻¹, e ∘ R ∘ e⁻¹)` obtained by transporting `(L, R)` along `e`. -/
private def conj (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) : 𝓜(ℂ, B) where
  fst := conjCLM e m.fst
  snd := conjCLM e m.snd
  central x y := by
    calc e (m.snd (e.symm x)) * y = e (m.snd (e.symm x) * e.symm y) := by simp
      _ = e (e.symm x * m.fst (e.symm y)) := by rw [m.central]
      _ = x * e (m.fst (e.symm y)) := by simp

private theorem conj_symm_conj (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) : conj e.symm (conj e m) = m :=
  DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun a => by simp [conj])
    (ContinuousLinearMap.ext fun a => by simp [conj])

/-- A star-algebra equivalence of C⋆-algebras extends to their multiplier algebras: the pair
`(L, R)` is sent to `(e ∘ L ∘ e⁻¹, e ∘ R ∘ e⁻¹)`. -/
def congr (e : A ≃⋆ₐ[ℂ] B) : 𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, B) where
  toFun := conj e
  invFun := conj e.symm
  left_inv := conj_symm_conj e
  right_inv m := by simpa using conj_symm_conj e.symm m
  map_add' _ _ := DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => by simp [conj])
    (ContinuousLinearMap.ext fun _ => by simp [conj])
  map_mul' _ _ := DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => by simp [conj])
    (ContinuousLinearMap.ext fun _ => by simp [conj])
  map_star' _ := DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => by simp [conj, map_star])
    (ContinuousLinearMap.ext fun _ => by simp [conj, map_star])
  map_smul' _ _ := DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => by simp [conj])
    (ContinuousLinearMap.ext fun _ => by simp [conj])

@[simp]
theorem congr_apply_fst (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) (b : B) :
    (congr e m).fst b = e (m.fst (e.symm b)) :=
  (rfl)

@[simp]
theorem congr_apply_snd (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) (b : B) :
    (congr e m).snd b = e (m.snd (e.symm b)) :=
  (rfl)

@[simp]
theorem congr_symm (e : A ≃⋆ₐ[ℂ] B) : (congr e).symm = congr e.symm :=
  (rfl)

@[simp]
theorem congr_refl : congr (StarAlgEquiv.refl ℂ A) = StarAlgEquiv.refl ℂ 𝓜(ℂ, A) := by
  ext m : 1
  exact DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => by simp) (ContinuousLinearMap.ext fun _ => by simp)

theorem congr_trans (e : A ≃⋆ₐ[ℂ] B) (f : B ≃⋆ₐ[ℂ] C) :
    congr (e.trans f) = (congr e).trans (congr f) := by
  ext m : 1
  exact DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => by simp) (ContinuousLinearMap.ext fun _ => by simp)

/-- The extension of `e` to multiplier algebras restricts to `e` on `A`. -/
@[simp]
theorem congr_coe (e : A ≃⋆ₐ[ℂ] B) (a : A) : congr e (a : 𝓜(ℂ, A)) = (e a : 𝓜(ℂ, B)) :=
  DoubleCentralizer.ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => by simp) (ContinuousLinearMap.ext fun _ => by simp)

/-- `congr e` is the unique multiplicative map of multiplier algebras extending `e`. -/
theorem eq_congr_of_apply_coe {F : Type*} [FunLike F 𝓜(ℂ, A) 𝓜(ℂ, B)]
    [MulHomClass F 𝓜(ℂ, A) 𝓜(ℂ, B)] (e : A ≃⋆ₐ[ℂ] B) (φ : F)
    (hφ : ∀ a : A, φ a = (e a : 𝓜(ℂ, B))) : ⇑φ = congr e := by
  funext m
  refine DoubleCentralizer.ext _ _ _ _ <| Prod.ext (ContinuousLinearMap.ext fun b => ?_)
    (ContinuousLinearMap.ext fun b => ?_)
  · apply coe_injective (𝕜 := ℂ)
    calc ((φ m).fst b : 𝓜(ℂ, B)) = φ m * φ (e.symm b : 𝓜(ℂ, A)) := by
          rw [hφ, e.apply_symm_apply, mul_coe_eq_coe_fst]
      _ = (e (m.fst (e.symm b)) : 𝓜(ℂ, B)) := by rw [← map_mul, mul_coe_eq_coe_fst, hφ]
  · apply coe_injective (𝕜 := ℂ)
    calc ((φ m).snd b : 𝓜(ℂ, B)) = φ (e.symm b : 𝓜(ℂ, A)) * φ m := by
          rw [hφ, e.apply_symm_apply, coe_mul_eq_coe_snd]
      _ = (e (m.snd (e.symm b)) : 𝓜(ℂ, B)) := by rw [← map_mul, coe_mul_eq_coe_snd, hφ]

end CStarAlgebra

end DoubleCentralizer
