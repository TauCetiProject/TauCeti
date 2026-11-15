/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Star
public import TauCeti.Algebra.Star.Basic
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.Normed.Algebra.DoubleCentralizer

/-!
# Functoriality of multiplier algebras of C⋆-algebras

Mathlib's multiplier algebra `𝓜(𝕜, A)` consists of double centralizers `(L, R)`. The basic
API for algebras with zero left and right annihilators (the module laws `DoubleCentralizer.fst_mul`
and `DoubleCentralizer.snd_mul`, injectivity of `A → 𝓜(𝕜, A)`, and `DoubleCentralizer.ext_fst`)
is in `TauCeti.Analysis.Normed.Algebra.DoubleCentralizer`. It applies to every C⋆-ring, since a
proper involution makes both annihilators zero (`TauCeti.faithfulSMul_mulOpposite_of_isProperStar`
and `TauCeti.faithfulSMul_of_isProperStar`). For regular normed algebras
(`RegularNormedAlgebra`), including real and complex C⋆-algebras, the canonical map is isometric.

A bounded operator `L` with an adjoint `L'` for the pairing `(x, y) ↦ star x * y` is the left
centralizer of the multiplier `DoubleCentralizer.ofAdjoint L L'`, whose right centralizer is
`star ∘ L' ∘ star`. This is how multipliers are built from left actions on a dense subalgebra,
such as the canonical multipliers of a crossed product.

A star-algebra equivalence `e : A ≃⋆ₐ[ℂ] B` of complex C⋆-algebras extends to a star-algebra
equivalence `DoubleCentralizer.congr e : 𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, B)`, sending `(L, R)` to
`(e ∘ L ∘ e⁻¹, e ∘ R ∘ e⁻¹)`. It is compatible with the inclusions of `A` and `B`, and it is
the only multiplicative map with this property. Applied to the automorphisms of a C⋆-dynamical
system, this gives the induced action on the multiplier algebra; `DoubleCentralizer.congrAut`
records that `e ↦ congr e` is a monoid homomorphism of automorphism groups.

Since `A` is an ideal of `𝓜(ℂ, A)`, conjugation `a ↦ u * a * u⋆` by a unitary multiplier `u`
maps `A` to itself; `DoubleCentralizer.conjStarAlgAut` records it as a monoid homomorphism from
the unitary multipliers to the automorphisms of `A`. As the inclusion of `A` is a linear isometry,
a real path in `A` has derivative `v` exactly when its image in `𝓜(ℂ, A)` has derivative `↑v`,
`DoubleCentralizer.hasDerivAt_coe_iff`, so derivatives may be computed in the multiplier algebra.
Consequently, conjugating a path in `A` by a path of multipliers `U` with `U 0 = 1` and
`U' 0 = i Q`, for self-adjoint `Q ∈ A`, adds `i[Q, ·]` to its derivative at `0`,
`DoubleCentralizer.hasDerivAt_conj_zero`.

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

section Adjoint

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NonUnitalNormedRing A]
  [StarRing A] [NormedStarGroup A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A]
  [IsScalarTower 𝕜 A A] [StarModule 𝕜 A]

/-- A bounded operator `L` on `A` with an adjoint `L'` for the pairing `(x, y) ↦ star x * y`,
that is `star (L' x) * y = star x * L y`, is the left centralizer of the multiplier
`(L, star ∘ L' ∘ star)`. -/
def ofAdjoint (L L' : A →L[𝕜] A) (h : ∀ x y, star (L' x) * y = star x * L y) : 𝓜(𝕜, A) where
  fst := L
  snd := (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp L').comp
    ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)
  central x y := by simpa using h (star x) y

variable {L L' : A →L[𝕜] A} {h : ∀ x y, star (L' x) * y = star x * L y}

@[simp]
theorem ofAdjoint_fst : (ofAdjoint L L' h).fst = L :=
  (rfl)

@[simp]
theorem ofAdjoint_snd_apply (x : A) : (ofAdjoint L L' h).snd x = star (L' (star x)) :=
  (rfl)

/-- The adjoint of the multiplier with left centralizer `L` has left centralizer `L'`. -/
@[simp]
theorem star_ofAdjoint :
    star (ofAdjoint L L' h) =
      ofAdjoint L' L fun x y => by simpa using congr(star $(h y x)).symm :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

end Adjoint

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
  simp only [edist_dist, dist_eq_norm, ← coe_sub, norm_coe]

end RegularNormedAlgebra

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

section Conj

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The element `u * a * u⋆` of `A`, for a multiplier `u`. -/
private def conj' (u : 𝓜(ℂ, A)) (a : A) : A :=
  (star u).snd (u.fst a)

private theorem coeHom_conj' (u : unitary 𝓜(ℂ, A)) (a : A) :
    coeHom (𝕜 := ℂ) (conj' (u : 𝓜(ℂ, A)) a) =
      Unitary.conjStarAlgAut ℂ 𝓜(ℂ, A) u (coeHom (𝕜 := ℂ) a) := by
  rw [coeHom_apply, coeHom_apply, conj', Unitary.conjStarAlgAut_apply, mul_coe_eq_coe_fst,
    coe_mul_eq_coe_snd]

/-- Conjugation by a unitary multiplier, as a star-algebra automorphism of `A`. -/
private def conjAux (u : unitary 𝓜(ℂ, A)) : A ≃⋆ₐ[ℂ] A where
  toFun := conj' (u : 𝓜(ℂ, A))
  invFun := conj' ((star u : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A))
  left_inv a := coe_injective (𝕜 := ℂ) <| by
    simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conj', ← Unitary.conjStarAlgAut_symm,
      StarAlgEquiv.symm_apply_apply]
  right_inv a := coe_injective (𝕜 := ℂ) <| by
    simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conj', ← Unitary.conjStarAlgAut_symm,
      StarAlgEquiv.apply_symm_apply]
  map_mul' a b := coe_injective (𝕜 := ℂ) <| by
    simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conj', map_mul]
  map_add' a b := coe_injective (𝕜 := ℂ) <| by
    simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conj', map_add]
  map_smul' c a := coe_injective (𝕜 := ℂ) <| by
    simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conj', map_smul]
  map_star' a := coe_injective (𝕜 := ℂ) <| by
    simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conj', map_star]

private theorem coeHom_conjAux_apply (u : unitary 𝓜(ℂ, A)) (a : A) :
    coeHom (𝕜 := ℂ) (conjAux u a) = Unitary.conjStarAlgAut ℂ 𝓜(ℂ, A) u (coeHom (𝕜 := ℂ) a) :=
  coeHom_conj' u a

/-- Conjugation `a ↦ u * a * u⋆` of `A` by a unitary multiplier `u`, as a star-algebra
automorphism of `A`. Since `A` is an ideal of `𝓜(ℂ, A)`, this is the restriction to `A` of the
inner automorphism `Unitary.conjStarAlgAut ℂ 𝓜(ℂ, A) u` of the multiplier algebra. -/
def conjStarAlgAut : unitary 𝓜(ℂ, A) →* (A ≃⋆ₐ[ℂ] A) where
  toFun := conjAux
  map_one' := by
    ext a
    exact coe_injective (𝕜 := ℂ) <| by
      simp only [← coeHom_apply (𝕜 := ℂ), coeHom_conjAux_apply, map_one, StarAlgEquiv.one_apply]
  map_mul' u v := by
    ext a
    exact coe_injective (𝕜 := ℂ) <| by
      simp only [← coeHom_apply (𝕜 := ℂ), StarAlgEquiv.mul_apply, coeHom_conjAux_apply, map_mul]

/-- Conjugation by a unitary multiplier `u` sends `a` to `u * a * u⋆`, computed in the multiplier
algebra. -/
@[simp]
theorem coe_conjStarAlgAut_apply (u : unitary 𝓜(ℂ, A)) (a : A) :
    ((conjStarAlgAut u a : A) : 𝓜(ℂ, A)) = u * a * star (u : 𝓜(ℂ, A)) :=
  (coeHom_conjAux_apply u a).trans (Unitary.conjStarAlgAut_apply u _)

end Conj

/-- A real path in `A` has derivative `v` exactly when its image in the multiplier algebra has
derivative `v`: the inclusion `A → 𝓜(ℂ, A)` is a linear isometry. -/
theorem hasDerivAt_coe_iff {A : Type*} [NonUnitalCStarAlgebra A] {f : ℝ → A} {v : A} {x : ℝ} :
    HasDerivAt (fun t => (f t : 𝓜(ℂ, A))) (v : 𝓜(ℂ, A)) x ↔ HasDerivAt f v x := by
  have key (h : ℝ) : (f (x + h) : 𝓜(ℂ, A)) - f x - h • (v : 𝓜(ℂ, A)) =
      ((f (x + h) - f x - h • v : A) : 𝓜(ℂ, A)) := by
    simp only [← Complex.coe_smul, coe_sub, coe_smul]
  rw [hasDerivAt_iff_isLittleO_nhds_zero, hasDerivAt_iff_isLittleO_nhds_zero,
    ← Asymptotics.isLittleO_norm_left, ← Asymptotics.isLittleO_norm_left (f' := fun h => _ - _)]
  simp only [key, norm_coe]

/-- Conjugating a differentiable path in `A` by a path of multipliers `U` with `U 0 = 1` and
`U' 0 = i Q`, for self-adjoint `Q ∈ A`, adds the commutator `i[Q, ·]` to its derivative at
`0`. -/
theorem hasDerivAt_conj_zero {A : Type*} [NonUnitalCStarAlgebra A] {Q : A}
    (hQ : IsSelfAdjoint Q) {U : ℝ → 𝓜(ℂ, A)} (hU₀ : U 0 = 1)
    (hU : HasDerivAt U (Complex.I • (Q : 𝓜(ℂ, A))) 0) {f g : ℝ → A}
    (hfg : ∀ t, (g t : 𝓜(ℂ, A)) = U t * f t * star (U t)) {v : A} (hf : HasDerivAt f v 0) :
    HasDerivAt g (v + Complex.I • (Q * f 0 - f 0 * Q)) 0 := by
  rw [← hasDerivAt_coe_iff, funext hfg]
  convert (hU.mul (hasDerivAt_coe_iff.2 hf)).mul hU.star using 1
  simp only [Pi.mul_apply, hU₀, star_one, mul_one, one_mul, star_smul, Complex.star_def,
    Complex.conj_I, ← coe_star, hQ.star_eq, coe_add, coe_smul, coe_sub, coe_mul,
    smul_mul_assoc, mul_smul_comm, neg_smul, mul_neg, smul_sub]
  abel

end CStarAlgebra

end DoubleCentralizer
