/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.ApproximateDiagonal
public import TauCeti.Analysis.Normed.Algebra.Unitization

/-!
# Completed universal one-forms

For a unital Banach algebra `B`, the kernel of multiplication on `B ⊗̂π B` is a Banach
bimodule for the outer actions. The bounded derivation `d b = 1 ⊗ b - b ⊗ 1` represents
bounded derivations into unital Banach bimodules: every such derivation factors uniquely
through a bounded bimodule map on this kernel, with norm at most `‖L‖ * ‖D‖`.
Actions are bounded bilinear maps and need not be contractive. The identity norm need
not be normalized.

In particular, taking `B = WithLp 1 (Unitization 𝕜 A)` gives the completed universal
one-forms of a possibly nonunital algebra `A`. The tensor formula underlying the lift
is `x ⊗ y ↦ L x (D y)`. This is the completed analogue of
`TauCeti.UniversalOneForms.tensorLift` and its universal property in
`TauCeti.NoncommutativeGeometry.UniversalDifferential.OneForms`.

## References

* V. Runde, *Lectures on Amenability*, §2.2.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.8.
-/

public section

noncomputable section

open scoped TensorProduct

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Composing a bounded derivation with the nonunital coordinate projection extends its
Leibniz rule to unital actions of the ℓ¹ unitization. -/
theorem comp_unitizationSndL_mul (D : A →L[𝕜] E)
    (L R : WithLp 1 (Unitization 𝕜 A) →L[𝕜] E →L[𝕜] E)
    (h1L : ∀ x, L 1 x = x) (h1R : ∀ x, R 1 x = x)
    (hD : ∀ a b, D (a * b) =
      L (WithLp.toLp 1 (a : Unitization 𝕜 A)) (D b) +
      R (WithLp.toLp 1 (b : Unitization 𝕜 A)) (D a))
    (u v : WithLp 1 (Unitization 𝕜 A)) :
    (D ∘L WithLp.unitizationSndL 𝕜 A) (u * v) =
      L u ((D ∘L WithLp.unitizationSndL 𝕜 A) v) +
      R v ((D ∘L WithLp.unitizationSndL 𝕜 A) u) := by
  rw [L.unitization_apply_eq_fst_smul_add u, R.unitization_apply_eq_fst_smul_add v]
  simp only [comp_apply, WithLp.unitizationSndL_apply, WithLp.unitization_mul,
    Unitization.snd_mul, map_add, map_smul, hD, add_apply, smul_apply, h1L, h1R]
  abel

end ContinuousLinearMap

namespace TauCeti

open CompletedProjectiveTensor

variable (𝕜 B : Type*) [NontriviallyNormedField 𝕜] [NormedRing B]
  [NormedAlgebra 𝕜 B] [CompleteSpace B]

/-- Completed universal one-forms of a unital Banach algebra: the kernel of multiplication
on its completed projective tensor square. For a nonunital algebra, apply this to its
external ℓ¹ unitization. -/
abbrev CompletedUniversalOneForms : Submodule 𝕜 (CompletedProjectiveTensor 𝕜 B B) :=
  (mul' 𝕜 B).ker

namespace CompletedUniversalOneForms

/-- Restrict a bounded action preserving the multiplication kernel, using the original
operator norm as a bound for the restricted action. -/
private def restrictAction
    (M : B →L[𝕜] CompletedProjectiveTensor 𝕜 B B →L[𝕜] CompletedProjectiveTensor 𝕜 B B)
    (hM : ∀ a t, t ∈ CompletedUniversalOneForms 𝕜 B →
      M a t ∈ CompletedUniversalOneForms 𝕜 B) :
    B →L[𝕜] CompletedUniversalOneForms 𝕜 B →L[𝕜] CompletedUniversalOneForms 𝕜 B :=
  LinearMap.mkContinuous
    { toFun a := (M a).restrict (hM a)
      map_add' a b := by ext t; exact congrArg (fun f ↦ f t.1) (map_add M a b)
      map_smul' c a := by
        ext t
        exact congrArg (fun f ↦ f t.1) (map_smul M c a) }
    ‖M‖ fun a ↦ by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro t
      exact M.le_opNorm₂ a t.1

/-- The bounded left outer action on completed universal one-forms. -/
def left : B →L[𝕜] CompletedUniversalOneForms 𝕜 B →L[𝕜] CompletedUniversalOneForms 𝕜 B :=
  restrictAction 𝕜 B (mulLeft 𝕜 B) fun a t ht ↦ by
    simpa using congrArg (a * ·) (LinearMap.mem_ker.mp ht)

/-- The bounded right outer action on completed universal one-forms. -/
def right : B →L[𝕜] CompletedUniversalOneForms 𝕜 B →L[𝕜] CompletedUniversalOneForms 𝕜 B :=
  restrictAction 𝕜 B (mulRight 𝕜 B) fun a t ht ↦ by
    simpa using congrArg (· * a) (LinearMap.mem_ker.mp ht)

variable {𝕜 B}

/-- The left action is the restriction of the outer action on completed tensors. -/
@[simp]
theorem coe_left (a : B) (t : CompletedUniversalOneForms 𝕜 B) :
    (left 𝕜 B a t : CompletedProjectiveTensor 𝕜 B B) = mulLeft 𝕜 B a t := (rfl)

/-- The right action is the restriction of the outer action on completed tensors. -/
@[simp]
theorem coe_right (a : B) (t : CompletedUniversalOneForms 𝕜 B) :
    (right 𝕜 B a t : CompletedProjectiveTensor 𝕜 B B) = mulRight 𝕜 B a t := (rfl)

/-- Associativity of the left action. -/
theorem left_mul (a b : B) (t : CompletedUniversalOneForms 𝕜 B) :
    left 𝕜 B (a * b) t = left 𝕜 B a (left 𝕜 B b t) := by
  apply Subtype.ext
  simpa only [coe_left] using mulLeft_mul_apply (𝕜 := 𝕜) a b t.1

/-- Associativity of the right action, with the order reversed. -/
theorem right_mul (a b : B) (t : CompletedUniversalOneForms 𝕜 B) :
    right 𝕜 B (a * b) t = right 𝕜 B b (right 𝕜 B a t) := by
  apply Subtype.ext
  simpa only [coe_right] using mulRight_mul_apply (𝕜 := 𝕜) a b t.1

/-- The left and right outer actions commute. -/
theorem left_right_comm (a b : B) (t : CompletedUniversalOneForms 𝕜 B) :
    left 𝕜 B a (right 𝕜 B b t) = right 𝕜 B b (left 𝕜 B a t) := by
  apply Subtype.ext
  simpa only [coe_left, coe_right] using mulLeft_mulRight_apply_comm (𝕜 := 𝕜) a b t.1

/-- The identity acts as the identity on the left. -/
@[simp]
theorem left_one (t : CompletedUniversalOneForms 𝕜 B) : left 𝕜 B 1 t = t := by
  have h : mulLeft 𝕜 B 1 = ContinuousLinearMap.id 𝕜 _ := by ext x y; simp
  apply Subtype.ext
  simp [h]

/-- The identity acts as the identity on the right. -/
@[simp]
theorem right_one (t : CompletedUniversalOneForms 𝕜 B) : right 𝕜 B 1 t = t := by
  have h : mulRight 𝕜 B 1 = ContinuousLinearMap.id 𝕜 _ := by ext x y; simp
  apply Subtype.ext
  simp [h]

variable (𝕜 B)

/-- The universal bounded derivation `b ↦ 1 ⊗ b - b ⊗ 1`. -/
def d : B →L[𝕜] CompletedUniversalOneForms 𝕜 B :=
  (tmulL (1 : B) - tmulL.flip (1 : B)).codRestrict _ fun b ↦ by simp

/-- The universal derivation has the usual tensor formula. -/
@[simp]
theorem coe_d (b : B) :
    (d 𝕜 B b : CompletedProjectiveTensor 𝕜 B B) = tmulL (1 : B) b - tmulL b (1 : B) := (rfl)

/-- A bound for the universal derivation, retaining the identity norm. -/
theorem norm_d_le : ‖d 𝕜 B‖ ≤ 2 * ‖(1 : B)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  rw [← Submodule.norm_coe (d 𝕜 B b), coe_d, tmulL_apply, tmulL_apply]
  calc
    _ ≤ ‖(1 : B)‖ * ‖b‖ + ‖b‖ * ‖(1 : B)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_coe_tmul_le _ _) (norm_coe_tmul_le _ _))
    _ = 2 * ‖(1 : B)‖ * ‖b‖ := by ring

variable {𝕜 B}

/-- The universal derivation kills the identity. -/
@[simp]
theorem d_one : d 𝕜 B 1 = 0 := Subtype.ext (sub_self _)

/-- The universal derivation satisfies the bimodule Leibniz rule. -/
theorem d_mul (a b : B) :
    d 𝕜 B (a * b) = left 𝕜 B a (d 𝕜 B b) + right 𝕜 B b (d 𝕜 B a) := by
  apply Subtype.ext
  simp only [coe_d, Submodule.coe_add, coe_left, coe_right, map_sub, tmulL_apply,
    mulLeft_apply_coe_tmul, mulRight_apply_coe_tmul, mul_one, one_mul]
  abel

/-- Projection onto the multiplication kernel along the tensors `b ⊗ 1`. -/
def projection : CompletedProjectiveTensor 𝕜 B B →L[𝕜] CompletedUniversalOneForms 𝕜 B :=
  (mul' 𝕜 B).projKerOfRightInverse (tmulL.flip (1 : B)) fun b ↦ by simp

/-- The projection subtracts the tensor of the product with the identity. -/
@[simp]
theorem coe_projection (t : CompletedProjectiveTensor 𝕜 B B) :
    (projection t : CompletedProjectiveTensor 𝕜 B B) = t - tmulL (mul' 𝕜 B t) (1 : B) :=
  ContinuousLinearMap.coe_projKerOfRightInverse_apply ..

/-- On a pure tensor, the projection is `x · d y`. -/
@[simp]
theorem projection_tmul (x y : B) :
    projection ((⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 B B) : CompletedProjectiveTensor 𝕜 B B) =
      left 𝕜 B x (d 𝕜 B y) := by
  apply Subtype.ext
  simp

/-- The projection is the identity on universal one-forms. -/
@[simp]
theorem projection_coe (t : CompletedUniversalOneForms 𝕜 B) : projection t.1 = t :=
  ContinuousLinearMap.projKerOfRightInverse_apply_idem ..

section Lift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (L R : B →L[𝕜] E →L[𝕜] E) (D : B →L[𝕜] E)

/-- The factor map on completed universal one-forms induced by the tensor formula
`x ⊗ y ↦ L x (D y)`. The bimodule and derivation laws guarantee its universal property. -/
def lift : CompletedUniversalOneForms 𝕜 B →L[𝕜] E :=
  (liftIsometry 𝕜 B B E (L.flip.comp D).flip).domRestrict _

/-- The factor map is the restriction of the bounded tensor lift. -/
theorem lift_apply (t : CompletedUniversalOneForms 𝕜 B) :
    lift L D t = liftIsometry 𝕜 B B E (L.flip.comp D).flip t.1 := (rfl)

/-- The induced factor map has norm at most the product of the left action and derivation
norms. In particular, the left action need not be contractive. -/
theorem norm_lift_le : ‖lift L D‖ ≤ ‖L‖ * ‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro t
  exact ((liftIsometry 𝕜 B B E (L.flip.comp D).flip).le_opNorm t.1).trans <| by
    rw [LinearIsometryEquiv.norm_map]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [ContinuousLinearMap.opNorm_flip]
    simpa only [ContinuousLinearMap.opNorm_flip] using ContinuousLinearMap.opNorm_comp_le L.flip D

variable (hL : ∀ a b x, L (a * b) x = L a (L b x))
  (hLR : ∀ a b x, L a (R b x) = R b (L a x))
  (h1 : ∀ x, L 1 x = x) (hD : ∀ a b, D (a * b) = L a (D b) + R b (D a))
  (hD1 : D 1 = 0)

include h1 hD1 in
/-- The factor map recovers the given derivation. -/
@[simp]
theorem lift_d (b : B) : lift L D (d 𝕜 B b) = D b := by
  simp [lift, coe_d, h1, hD1]

include hL in
/-- The factor map intertwines the left actions. -/
theorem lift_left (a : B) (t : CompletedUniversalOneForms 𝕜 B) :
    lift L D (left 𝕜 B a t) = L a (lift L D t) := by
  have h : liftIsometry 𝕜 B B E (L.flip.comp D).flip ∘L mulLeft 𝕜 B a =
      L a ∘L liftIsometry 𝕜 B B E (L.flip.comp D).flip := by
    ext x y
    simp [hL]
  exact congrArg (fun f ↦ f t.1) h

include hL hLR hD in
/-- On the multiplication kernel, the correction term in the right Leibniz identity
vanishes, so the factor map intertwines the right actions. -/
theorem lift_right (b : B) (t : CompletedUniversalOneForms 𝕜 B) :
    lift L D (right 𝕜 B b t) = R b (lift L D t) := by
  let T := liftIsometry 𝕜 B B E (L.flip.comp D).flip
  have h : T ∘L mulRight 𝕜 B b = R b ∘L T + (L.flip (D b)) ∘L mul' 𝕜 B := by
    ext x y
    simp [T, hD, hLR, hL, add_comm]
  have ht := congrArg (fun f ↦ f t.1) h
  have ht0 : mul' 𝕜 B t.1 = 0 := LinearMap.mem_ker.mp t.2
  simpa [T, lift, ht0] using ht

/-- A bounded left-module map on completed universal one-forms is determined by its values
on the universal differentials. Right intertwining is not needed for uniqueness. -/
theorem lift_unique (f : CompletedUniversalOneForms 𝕜 B →L[𝕜] E)
    (hfL : ∀ a t, f (left 𝕜 B a t) = L a (f t)) (hf : ∀ a, f (d 𝕜 B a) = D a) :
    f = lift L D := by
  have h : f ∘L projection = liftIsometry 𝕜 B B E (L.flip.comp D).flip := by
    ext x y
    simp [hfL, hf]
  ext t
  simpa [lift] using congrArg (fun g ↦ g t.1) h

include hL hLR h1 hD hD1 in
/-- Every bounded derivation into a unital Banach bimodule factors uniquely through a
bounded bimodule map from the completed multiplication kernel. -/
theorem existsUnique_lift :
    ∃! f : CompletedUniversalOneForms 𝕜 B →L[𝕜] E,
      (∀ a, f (d 𝕜 B a) = D a) ∧
      (∀ a t, f (left 𝕜 B a t) = L a (f t)) ∧
      (∀ a t, f (right 𝕜 B a t) = R a (f t)) := by
  exact ⟨lift L D, ⟨lift_d L D h1 hD1, lift_left L D hL,
    lift_right L R D hL hLR hD⟩, fun f hf ↦ lift_unique L D f hf.2.1 hf.1⟩

end Lift

section NonUnital

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
  [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- The universal differential of a nonunital Banach algebra, with values in the
multiplication kernel of the completed tensor square of its external ℓ¹ unitization. -/
def dNonUnital : A →L[𝕜] CompletedUniversalOneForms 𝕜 (WithLp 1 (Unitization 𝕜 A)) :=
  d 𝕜 (WithLp 1 (Unitization 𝕜 A)) ∘L WithLp.unitizationInrL 𝕜 A

/-- The nonunital universal differential is the restriction of the unitized differential. -/
@[simp]
theorem dNonUnital_apply (a : A) :
    dNonUnital 𝕜 A a = d 𝕜 (WithLp 1 (Unitization 𝕜 A))
      (WithLp.toLp 1 (a : Unitization 𝕜 A)) := by
  simp [dNonUnital]

/-- Restricting the universal differential to the original algebra satisfies Leibniz. -/
theorem dNonUnital_mul (a b : A) :
    dNonUnital 𝕜 A (a * b) =
      left 𝕜 _ (WithLp.toLp 1 (a : Unitization 𝕜 A)) (dNonUnital 𝕜 A b) +
      right 𝕜 _ (WithLp.toLp 1 (b : Unitization 𝕜 A)) (dNonUnital 𝕜 A a) := by
  simpa only [dNonUnital, ContinuousLinearMap.comp_apply,
    ← WithLp.unitizationInrL_apply, WithLp.unitizationInrL_mul] using
    d_mul (𝕜 := 𝕜) (WithLp.unitizationInrL 𝕜 A a) (WithLp.unitizationInrL 𝕜 A b)

/-- The nonunital universal differential has norm at most two for the ℓ¹ unitization. -/
theorem norm_dNonUnital_le : ‖dNonUnital 𝕜 A‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro a
  have h := (d 𝕜 (WithLp 1 (Unitization 𝕜 A))).le_of_opNorm_le
    (by simpa using norm_d_le 𝕜 (WithLp 1 (Unitization 𝕜 A)))
    (WithLp.toLp 1 (a : Unitization 𝕜 A))
  simpa only [dNonUnital_apply, WithLp.unitization_norm_inr] using h

variable {𝕜 A} {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A bounded derivation of a nonunital algebra into a unital bimodule over its external
ℓ¹ unitization factors uniquely through completed universal one-forms. The factor is bounded
by `‖L‖ * ‖D‖`; no contractivity of the module actions is required. -/
theorem existsUnique_lift_nonUnital
    (L R : WithLp 1 (Unitization 𝕜 A) →L[𝕜] E →L[𝕜] E) (D : A →L[𝕜] E)
    (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (h1L : ∀ x, L 1 x = x) (h1R : ∀ x, R 1 x = x)
    (hD : ∀ a b, D (a * b) =
      L (WithLp.toLp 1 (a : Unitization 𝕜 A)) (D b) +
      R (WithLp.toLp 1 (b : Unitization 𝕜 A)) (D a)) :
    ∃! f : CompletedUniversalOneForms 𝕜 (WithLp 1 (Unitization 𝕜 A)) →L[𝕜] E,
      (∀ a, f (dNonUnital 𝕜 A a) = D a) ∧
      (∀ a t, f (left 𝕜 _ a t) = L a (f t)) ∧
      (∀ a t, f (right 𝕜 _ a t) = R a (f t)) ∧ ‖f‖ ≤ ‖L‖ * ‖D‖ := by
  let D' := D ∘L WithLp.unitizationSndL 𝕜 A
  have hD' (u : WithLp 1 (Unitization 𝕜 A)) : D' u = D (WithLp.ofLp u).snd := by
    simp [D']
  have hd := D.comp_unitizationSndL_mul L R h1L h1R hD
  have hd1 : D' 1 = 0 := by simp [D']
  have hn : ‖D'‖ ≤ ‖D‖ := D.norm_comp_unitizationSndL_le
  refine ⟨lift L D', ⟨?_, lift_left L D' hL, lift_right L R D' hL hLR hd,
    (norm_lift_le L D').trans (by gcongr)⟩, ?_⟩
  · intro a
    simpa [hD'] using lift_d L D' h1L hd1 (WithLp.toLp 1 (a : Unitization 𝕜 A))
  · intro f hf
    apply lift_unique L D' f hf.2.1
    intro u
    conv_lhs => rw [WithLp.unitization_eq_fst_smul_one_add_inr u]
    simp only [map_add, map_smul, d_one, smul_zero, zero_add,
      ← dNonUnital_apply, hf.1, hD']

end NonUnital

end CompletedUniversalOneForms

end TauCeti
