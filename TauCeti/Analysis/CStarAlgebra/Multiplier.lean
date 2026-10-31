/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.CStarAlgebra.Hom

/-!
# Functoriality of multiplier algebras of C⋆-algebras

Mathlib's multiplier algebra `𝓜(𝕜, A)` consists of double centralizers `(L, R)`. This file
proves that, when `A` has a proper involution (for example, when it is a C⋆-ring), the left and
right centralizers are module maps for right and left multiplication respectively, so that the
products of a multiplier with an element of `A` are again elements of `A`, and the canonical
map `A → 𝓜(𝕜, A)` is injective. For regular normed algebras (`RegularNormedAlgebra`), including
real and complex C⋆-algebras, this map is isometric; consequently a real path in `A` has a
derivative in `A` exactly when it has the same derivative in `𝓜(ℂ, A)`
(`DoubleCentralizer.hasDerivAt_coe_iff`).

A star-algebra equivalence `e : A ≃⋆ₐ[ℂ] B` of complex C⋆-algebras extends to a star-algebra
equivalence `DoubleCentralizer.congr e : 𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, B)`, sending `(L, R)` to
`(e ∘ L ∘ e⁻¹, e ∘ R ∘ e⁻¹)`. It is compatible with the inclusions of `A` and `B`, and it is
the only multiplicative map with this property. Applied to the automorphisms of a C⋆-dynamical
system, this gives the induced action on the multiplier algebra; `DoubleCentralizer.congrAut`
records that `e ↦ congr e` is a monoid homomorphism of automorphism groups.

Conjugation `a ↦ u a u⋆` by a unitary multiplier `u` preserves `A`; this gives the monoid
homomorphism `DoubleCentralizer.conjStarAlgAut : unitary 𝓜(ℂ, A) →* (A ≃⋆ₐ[ℂ] A)`, the
nonunital analogue of `Unitary.conjStarAlgAut`.

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

section NontriviallyNormed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-- Two multipliers are equal if their left and right centralizers agree pointwise. -/
theorem ext_fst_snd {m n : 𝓜(𝕜, A)} (h₁ : ∀ a, m.fst a = n.fst a)
    (h₂ : ∀ a, m.snd a = n.snd a) : m = n :=
  DoubleCentralizer.ext _ _ _ _ <|
    Prod.ext (ContinuousLinearMap.ext h₁) (ContinuousLinearMap.ext h₂)

end NontriviallyNormed

section ProperStar

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [Star A] [IsProperStar A]

/-- The left centralizer of a multiplier commutes with right multiplication. -/
theorem fst_mul (m : 𝓜(𝕜, A)) (a b : A) : m.fst (a * b) = m.fst a * b := by
  have h : ∀ y : A, y * (m.fst (a * b) - m.fst a * b) = 0 := fun y => by
    simp [mul_sub, ← m.central, ← mul_assoc]
  exact sub_eq_zero.mp (star_mul_self_eq_zero.mp (h _))

/-- A multiplier times an element of `A` is the element obtained from the left centralizer. -/
@[simp]
theorem mul_coe_eq_coe_fst (m : 𝓜(𝕜, A)) (a : A) : m * (a : 𝓜(𝕜, A)) = (m.fst a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp [fst_mul]) (fun _ => by simp [m.central])

/-- The canonical map of `A` into its multiplier algebra is injective. -/
theorem coe_injective : Function.Injective (DoubleCentralizer.coe 𝕜 : A → 𝓜(𝕜, A)) := by
  intro a b h
  have h' : star (a - b) * (a - b) = 0 := by
    rw [mul_sub, sub_eq_zero]
    simpa using congrArg (fun m : 𝓜(𝕜, A) => m.snd (star (a - b))) h
  exact sub_eq_zero.mp (star_mul_self_eq_zero.mp h')

@[simp, norm_cast]
theorem coe_inj {a b : A} : (a : 𝓜(𝕜, A)) = b ↔ a = b :=
  coe_injective.eq_iff

end ProperStar

section InvolutiveStar

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [InvolutiveStar A] [IsProperStar A]

/-- The right centralizer of a multiplier commutes with left multiplication. -/
theorem snd_mul (m : 𝓜(𝕜, A)) (a b : A) : m.snd (a * b) = a * m.snd b := by
  have h : ∀ y : A, (m.snd (a * b) - a * m.snd b) * y = 0 := fun y => by
    simp [sub_mul, mul_assoc, m.central]
  have hs : star (m.snd (a * b) - a * m.snd b) = 0 :=
    star_mul_self_eq_zero.mp (by simpa only [star_star] using h (star _))
  exact sub_eq_zero.mp (star_mul_self_eq_zero.mp (by rw [hs, zero_mul]))

/-- An element of `A` times a multiplier is the element obtained from the right centralizer. -/
@[simp]
theorem coe_mul_eq_coe_snd (a : A) (m : 𝓜(𝕜, A)) : (a : 𝓜(𝕜, A)) * m = (m.snd a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp [m.central]) (fun _ => by simp [snd_mul])

end InvolutiveStar

section RegularNormedAlgebra

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [RegularNormedAlgebra 𝕜 A]

/-- The inclusion of a regular normed algebra into its multiplier algebra preserves the norm. -/
@[simp, norm_cast]
theorem norm_coe (a : A) : ‖(a : 𝓜(𝕜, A))‖ = ‖a‖ := by
  simp only [norm_def, Prod.norm_def, toProdHom_apply, coe_fst, coe_snd,
    ContinuousLinearMap.opNorm_mul_apply]
  exact max_eq_left <| ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun b => by
    simpa [mul_comm] using norm_mul_le b a

/-- The inclusion of a regular normed algebra into its multiplier algebra is isometric. -/
theorem isometry_coe : Isometry (DoubleCentralizer.coe 𝕜 : A → 𝓜(𝕜, A)) := by
  intro a b
  have h : ((a - b : A) : 𝓜(𝕜, A)) = (a : 𝓜(𝕜, A)) - b :=
    ext_fst_snd (fun _ => by simp) (fun _ => by simp)
  simp only [edist_dist, dist_eq_norm, ← h, norm_coe]

end RegularNormedAlgebra

section Deriv

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A] [SMulCommClass ℂ A A]
  [IsScalarTower ℂ A A] [RegularNormedAlgebra ℂ A]

/-- A real path in `A` has derivative `d` exactly when it does in `𝓜(ℂ, A)`, since the
inclusion is real linear and isometric. -/
theorem hasDerivAt_coe_iff {f : ℝ → A} {d : A} {x : ℝ} :
    HasDerivAt (fun t => (f t : 𝓜(ℂ, A))) (d : 𝓜(ℂ, A)) x ↔ HasDerivAt f d x := by
  have h (y : ℝ) : ‖(f y : 𝓜(ℂ, A)) - f x - (y - x) • (d : 𝓜(ℂ, A))‖ =
      ‖f y - f x - (y - x) • d‖ := by
    rw [← norm_coe (𝕜 := ℂ) (f y - f x - (y - x) • d)]
    congr 1
    exact ext_fst_snd (fun _ => by simp) (fun _ => by simp)
  simp only [hasDerivAt_iff_isLittleO, ← Asymptotics.isLittleO_norm_left (f' := fun y => _ - _),
    h]

end Deriv

section CStarAlgebra

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- The multiplier `(e ∘ L ∘ e⁻¹, e ∘ R ∘ e⁻¹)` obtained by transporting `(L, R)` along `e`. -/
private def conj (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) : 𝓜(ℂ, B) where
  fst := e.toContinuousLinearEquiv.conjContinuousAlgEquiv m.fst
  snd := e.toContinuousLinearEquiv.conjContinuousAlgEquiv m.snd
  central x y := by
    simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
      StarAlgEquiv.toContinuousLinearEquiv_symm, StarAlgEquiv.coe_toContinuousLinearEquiv]
    calc e (m.snd (e.symm x)) * y = e (m.snd (e.symm x) * e.symm y) := by simp
      _ = e (e.symm x * m.fst (e.symm y)) := by rw [m.central]
      _ = x * e (m.fst (e.symm y)) := by simp

private theorem conj_apply_fst (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) (b : B) :
    (conj e m).fst b = e (m.fst (e.symm b)) := by
  simp [conj]

private theorem conj_apply_snd (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) (b : B) :
    (conj e m).snd b = e (m.snd (e.symm b)) := by
  simp [conj]

private theorem conj_symm_conj (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) : conj e.symm (conj e m) = m :=
  ext_fst_snd (fun _ => by simp [conj]) (fun _ => by simp [conj])

/-- A star-algebra equivalence of C⋆-algebras extends to their multiplier algebras: the pair
`(L, R)` is sent to `(e ∘ L ∘ e⁻¹, e ∘ R ∘ e⁻¹)`. -/
def congr (e : A ≃⋆ₐ[ℂ] B) : 𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, B) where
  toFun := conj e
  invFun := conj e.symm
  left_inv := conj_symm_conj e
  right_inv m := by simpa using conj_symm_conj e.symm m
  map_add' _ _ := ext_fst_snd (fun _ => by simp [conj]) (fun _ => by simp [conj])
  map_mul' _ _ := ext_fst_snd (fun _ => by simp [conj]) (fun _ => by simp [conj])
  map_star' _ := ext_fst_snd (fun _ => by simp [conj, map_star])
    (fun _ => by simp [conj, map_star])
  map_smul' _ _ := ext_fst_snd (fun _ => by simp [conj]) (fun _ => by simp [conj])

@[simp]
theorem congr_apply_fst (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) (b : B) :
    (congr e m).fst b = e (m.fst (e.symm b)) :=
  conj_apply_fst e m b

@[simp]
theorem congr_apply_snd (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜(ℂ, A)) (b : B) :
    (congr e m).snd b = e (m.snd (e.symm b)) :=
  conj_apply_snd e m b

@[simp]
theorem congr_symm (e : A ≃⋆ₐ[ℂ] B) : (congr e).symm = congr e.symm :=
  (rfl)

@[simp]
theorem congr_refl : congr (StarAlgEquiv.refl ℂ A) = StarAlgEquiv.refl ℂ 𝓜(ℂ, A) := by
  ext m : 1
  exact ext_fst_snd (fun _ => by simp) (fun _ => by simp)

@[simp]
theorem congr_trans (e : A ≃⋆ₐ[ℂ] B) (f : B ≃⋆ₐ[ℂ] C) :
    congr (e.trans f) = (congr e).trans (congr f) := by
  ext m : 1
  exact ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- Extension to multiplier algebras, as a monoid homomorphism of automorphism groups. -/
def congrAut : (A ≃⋆ₐ[ℂ] A) →* (𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)) where
  toFun := congr
  map_one' := congr_refl
  map_mul' e f := congr_trans f e

@[simp]
theorem congrAut_apply (e : A ≃⋆ₐ[ℂ] A) : congrAut e = congr e :=
  (rfl)

/-- The extension of `e` to multiplier algebras restricts to `e` on `A`. -/
@[simp]
theorem congr_coe (e : A ≃⋆ₐ[ℂ] B) (a : A) : congr e (a : 𝓜(ℂ, A)) = (e a : 𝓜(ℂ, B)) :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- `congr e` is the unique multiplicative map of multiplier algebras extending `e`. -/
theorem eq_congr_of_apply_coe {F : Type*} [FunLike F 𝓜(ℂ, A) 𝓜(ℂ, B)]
    [MulHomClass F 𝓜(ℂ, A) 𝓜(ℂ, B)] (e : A ≃⋆ₐ[ℂ] B) (φ : F)
    (hφ : ∀ a : A, φ a = (e a : 𝓜(ℂ, B))) : ⇑φ = congr e := by
  funext m
  refine ext_fst_snd (fun b => ?_) (fun b => ?_)
  · rw [congr_apply_fst]
    apply coe_injective (𝕜 := ℂ)
    calc ((φ m).fst b : 𝓜(ℂ, B)) = φ m * φ (e.symm b : 𝓜(ℂ, A)) := by
          rw [hφ, e.apply_symm_apply, mul_coe_eq_coe_fst]
      _ = (e (m.fst (e.symm b)) : 𝓜(ℂ, B)) := by rw [← map_mul, mul_coe_eq_coe_fst, hφ]
  · rw [congr_apply_snd]
    apply coe_injective (𝕜 := ℂ)
    calc ((φ m).snd b : 𝓜(ℂ, B)) = φ (e.symm b : 𝓜(ℂ, A)) * φ m := by
          rw [hφ, e.apply_symm_apply, coe_mul_eq_coe_snd]
      _ = (e (m.snd (e.symm b)) : 𝓜(ℂ, B)) := by rw [← map_mul, coe_mul_eq_coe_snd, hφ]

/-- Conjugation `a ↦ m a m⋆` of `A` by a multiplier `m`, computed through its centralizers. -/
private def conjMul (m : 𝓜(ℂ, A)) (a : A) : A :=
  (star m).snd (m.fst a)

private theorem coeHom_conjMul (m : 𝓜(ℂ, A)) (a : A) :
    coeHom (𝕜 := ℂ) (conjMul m a) = m * coeHom (𝕜 := ℂ) a * star m := by
  simp [conjMul]

private theorem conjMul_mul_conjMul (u v : 𝓜(ℂ, A)) (a : A) :
    conjMul u (conjMul v a) = conjMul (u * v) a :=
  coe_injective (𝕜 := ℂ) <| by
    simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conjMul, star_mul, mul_assoc]

private theorem conjMul_one (a : A) : conjMul 1 a = a :=
  coe_injective (𝕜 := ℂ) <| by
    simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conjMul, star_one, one_mul, mul_one]

private theorem conjMul_star_conjMul {u : 𝓜(ℂ, A)} (hu : u ∈ unitary 𝓜(ℂ, A)) (a : A) :
    conjMul (star u) (conjMul u a) = a := by
  rw [conjMul_mul_conjMul, Unitary.star_mul_self_of_mem hu, conjMul_one]

/-- Conjugation `a ↦ u a u⋆` of `A` by unitary multipliers `u`, as a monoid homomorphism into
the star-algebra automorphisms of `A`. -/
def conjStarAlgAut : unitary 𝓜(ℂ, A) →* (A ≃⋆ₐ[ℂ] A) where
  toFun u :=
    { toFun := conjMul u
      invFun := conjMul (star u : 𝓜(ℂ, A))
      left_inv := conjMul_star_conjMul u.2
      right_inv a := by
        simpa using conjMul_star_conjMul (star u).2 a
      map_add' a b := coe_injective (𝕜 := ℂ) <| by
        simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conjMul, map_add, mul_add, add_mul]
      map_mul' a b := coe_injective (𝕜 := ℂ) <| by
        simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conjMul, map_mul, mul_assoc]
        simp only [← mul_assoc (star (u : 𝓜(ℂ, A))), Unitary.star_mul_self_of_mem u.2, one_mul]
      map_star' a := coe_injective (𝕜 := ℂ) <| by
        simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conjMul, map_star, star_mul, star_star,
          mul_assoc]
      map_smul' c a := coe_injective (𝕜 := ℂ) <| by
        simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conjMul, map_smul, mul_smul_comm,
          smul_mul_assoc] }
  map_one' := StarAlgEquiv.ext conjMul_one
  map_mul' u v := by
    ext a
    rw [StarAlgEquiv.mul_apply]
    exact (conjMul_mul_conjMul (u : 𝓜(ℂ, A)) v a).symm

/-- Conjugation by a unitary multiplier, seen in the multiplier algebra. -/
@[simp]
theorem coe_conjStarAlgAut_apply (u : unitary 𝓜(ℂ, A)) (a : A) :
    ((conjStarAlgAut u a : A) : 𝓜(ℂ, A)) = u * a * star (u : 𝓜(ℂ, A)) :=
  coeHom_conjMul _ a

end CStarAlgebra

end DoubleCentralizer
