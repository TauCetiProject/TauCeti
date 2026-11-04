/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Basic
public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.CStarAlgebra.Multiplier

/-!
# Multiplier homomorphisms of two-sided star ideals

Every two-sided star ideal `I` of a nonunital normed star algebra `A` over `𝕜` acts on itself by
left and right multiplication in `A` (with right absorption deduced from left absorption via
`StarMemClass.mul_mem_right_of_mul_mem_left`). This yields a canonical contractive nonunital
star-algebra homomorphism `I.multiplierHom hmul : A →⋆ₙₐ[𝕜] 𝓜(𝕜, I)` extending the inclusion of
`I` into its multiplier algebra.

When `A` has a proper involution (in particular, when `A` is a C⋆-algebra), the kernel of
`I.multiplierHom hmul` is the left annihilator `{a : A | ∀ x ∈ I, a * x = 0}` of `I` in `A`, so
`I.multiplierHom hmul` is injective precisely when `I` has trivial left annihilator (that is, `I`
is an essential ideal).

## Main definitions and results

* `NonUnitalStarSubalgebra.multiplierHom`: the canonical star-algebra homomorphism
  `A →⋆ₙₐ[𝕜] 𝓜(𝕜, I)` attached to a star ideal `I` of `A`.
* `NonUnitalStarSubalgebra.multiplierHom_fst_apply` and
  `NonUnitalStarSubalgebra.multiplierHom_snd_apply`: left and right action formulas on `I`.
* `NonUnitalStarSubalgebra.multiplierHom_coe` and
  `NonUnitalStarSubalgebra.multiplierHom_comp_subtype`: compatibility with the canonical
  inclusion `I → 𝓜(𝕜, I)`.
* `NonUnitalStarSubalgebra.norm_multiplierHom_le` and
  `NonUnitalStarSubalgebra.continuous_multiplierHom`: contractivity and continuity.
* `NonUnitalStarSubalgebra.multiplierHom_eq_zero_iff` and
  `NonUnitalStarSubalgebra.multiplierHom_injective_iff`: under `IsProperStar A`, an ambient element
  acts as the zero multiplier on `I` precisely when it left-annihilates `I`.

## References

* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Section 2.3 and Proposition 2.54.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open scoped MultiplierAlgebra

namespace NonUnitalStarSubalgebra

section NormedStarAlgebra

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
  [StarRing A] (I : NonUnitalStarSubalgebra 𝕜 A)

omit [IsScalarTower 𝕜 A A] in
/-- Left multiplication by `a : A` as a continuous linear endomorphism of a star ideal `I`. -/
private def idealMulLeftCLM (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) : I →L[𝕜] I :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨a * x, hmul a x x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add a x y)
      map_smul' := fun c x => Subtype.ext (mul_smul_comm c a x) }
    ‖a‖ fun x => norm_mul_le a (x : A)

omit [SMulCommClass 𝕜 A A] in
/-- Right multiplication by `a : A` as a continuous linear endomorphism of a star ideal `I`. -/
private def idealMulRightCLM (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) : I →L[𝕜] I :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨x * a, StarMemClass.mul_mem_right_of_mul_mem_left hmul a x.2⟩
      map_add' := fun x y => Subtype.ext (add_mul (x : A) y a)
      map_smul' := fun c x => Subtype.ext (smul_mul_assoc c (x : A) a) }
    ‖a‖ fun x => (norm_mul_le (x : A) a).trans_eq (mul_comm ‖(x : A)‖ ‖a‖)

omit [IsScalarTower 𝕜 A A] in
@[simp]
private theorem coe_idealMulLeftCLM_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    ((I.idealMulLeftCLM hmul a x : I) : A) = a * x :=
  rfl

omit [SMulCommClass 𝕜 A A] in
@[simp]
private theorem coe_idealMulRightCLM_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    ((I.idealMulRightCLM hmul a x : I) : A) = x * a :=
  rfl

/-- The double centralizer on `I` given by left and right multiplication by `a : A`. -/
private def idealMultiplier (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) : 𝓜(𝕜, I) where
  fst := I.idealMulLeftCLM hmul a
  snd := I.idealMulRightCLM hmul a
  central x y := Subtype.ext (mul_assoc (x : A) a y)

variable [StarRing 𝕜] [StarModule 𝕜 A] [NormedStarGroup A]

/-- The canonical nonunital star-algebra homomorphism `A →⋆ₙₐ[𝕜] 𝓜(𝕜, I)` induced by left and
right multiplication of `A` on a star ideal `I`. -/
def multiplierHom (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) : A →⋆ₙₐ[𝕜] 𝓜(𝕜, I) where
  toFun := I.idealMultiplier hmul
  map_smul' c a := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (smul_mul_assoc c a x))
    (fun x => Subtype.ext (mul_smul_comm c (x : A) a))
  map_zero' := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (zero_mul (x : A)))
    (fun x => Subtype.ext (mul_zero (x : A)))
  map_add' a b := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (add_mul a b x))
    (fun x => Subtype.ext (mul_add (x : A) a b))
  map_mul' a b := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (mul_assoc a b x))
    (fun x => Subtype.ext (mul_assoc (x : A) a b).symm)
  map_star' a := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext <| by simp [idealMultiplier, DoubleCentralizer.star_fst])
    (fun x => Subtype.ext <| by simp [idealMultiplier, DoubleCentralizer.star_snd])

variable {I}

/-- The left centralizer of `I.multiplierHom hmul a` acts on `I` by left multiplication by `a`. -/
@[simp]
theorem multiplierHom_fst_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    (I.multiplierHom hmul a).fst x = ⟨a * x, hmul a x x.2⟩ :=
  (rfl)

/-- The right centralizer of `I.multiplierHom hmul a` acts on `I` by right multiplication by `a`. -/
@[simp]
theorem multiplierHom_snd_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    (I.multiplierHom hmul a).snd x =
      ⟨x * a, StarMemClass.mul_mem_right_of_mul_mem_left hmul a x.2⟩ :=
  (rfl)

/-- Coercing `(I.multiplierHom hmul a).fst x` to `A` gives `a * x`. -/
theorem coe_multiplierHom_fst_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    (((I.multiplierHom hmul a).fst x : I) : A) = a * x :=
  (rfl)

/-- Coercing `(I.multiplierHom hmul a).snd x` to `A` gives `x * a`. -/
theorem coe_multiplierHom_snd_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    (((I.multiplierHom hmul a).snd x : I) : A) = x * a :=
  (rfl)

/-- On elements of `I`, `I.multiplierHom hmul` agrees with the canonical inclusion into
`𝓜(𝕜, I)`. -/
@[simp]
theorem multiplierHom_coe (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (x : I) :
    I.multiplierHom hmul (x : A) = (x : 𝓜(𝕜, I)) :=
  DoubleCentralizer.ext_fst_snd (fun _ => Subtype.ext rfl) (fun _ => Subtype.ext rfl)

/-- Composing `I.multiplierHom hmul` with the subtype inclusion of `I` recovers
`DoubleCentralizer.coeHom`. -/
@[simp]
theorem multiplierHom_comp_subtype (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (I.multiplierHom hmul).comp (NonUnitalStarSubalgebraClass.subtype I) =
      DoubleCentralizer.coeHom :=
  NonUnitalStarAlgHom.ext (I.multiplierHom_coe hmul)

/-- The canonical map from `A` into the multiplier algebra of a star ideal is contractive. -/
theorem norm_multiplierHom_le (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) :
    ‖I.multiplierHom hmul a‖ ≤ ‖a‖ := by
  rw [DoubleCentralizer.norm_def, DoubleCentralizer.toProdHom_apply, Prod.norm_def]
  exact max_le
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x => norm_mul_le a (x : A))
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x =>
      (norm_mul_le (x : A) a).trans_eq (mul_comm ‖(x : A)‖ ‖a‖))

/-- The canonical map `I.multiplierHom hmul : A →⋆ₙₐ[𝕜] 𝓜(𝕜, I)` is norm continuous. -/
@[fun_prop]
theorem continuous_multiplierHom (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    Continuous (I.multiplierHom hmul) :=
  AddMonoidHomClass.continuous_of_bound (I.multiplierHom hmul) 1 fun a => by
    simpa only [one_mul] using I.norm_multiplierHom_le hmul a

/-- When `A` has a proper involution, `I.multiplierHom hmul a = 0` precisely when `a`
left-annihilates `I`. -/
theorem multiplierHom_eq_zero_iff [IsProperStar A] (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) {a : A} :
    I.multiplierHom hmul a = 0 ↔ ∀ x ∈ I, a * x = 0 := by
  refine ⟨fun h x hx => ?_, fun h => DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (h x x.2)) fun x => Subtype.ext ?_⟩
  · have := congrArg (fun m : 𝓜(𝕜, I) => ((m.fst ⟨x, hx⟩ : I) : A)) h
    simpa using this
  · -- Right annihilation `x * a = 0` follows from `(x * a) * star (x * a) = x * (a * _) = 0`.
    have hzero : (x : A) * a * star ((x : A) * a) = 0 := by
      rw [mul_assoc, h _ (star_mem (StarMemClass.mul_mem_right_of_mul_mem_left hmul a x.2)),
        mul_zero]
    exact mul_star_self_eq_zero.mp hzero

/-- When `A` has a proper involution, `I.multiplierHom hmul` is injective if and only if `I` has
trivial left annihilator in `A`. -/
theorem multiplierHom_injective_iff [IsProperStar A] (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    Function.Injective (I.multiplierHom hmul) ↔ ∀ a : A, (∀ x ∈ I, a * x = 0) → a = 0 := by
  rw [injective_iff_map_eq_zero]
  exact forall_congr' fun _ => imp_congr_left (I.multiplierHom_eq_zero_iff hmul)

end NormedStarAlgebra

end NonUnitalStarSubalgebra
