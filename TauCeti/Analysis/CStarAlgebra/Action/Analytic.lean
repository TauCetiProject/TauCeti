/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Generator.Basic
public import TauCeti.Analysis.Complex.RealIdentity

/-!
# Entire analytic elements of C⋆-algebra actions

For a point-norm continuous real action `α` on a possibly nonunital C⋆-algebra `A`, an element
`a` is *entire analytic* when its orbit `t ↦ α_t a` is the restriction to the real line of an
entire `A`-valued function. That function is unique, and `α.entireExtension a z` is its value
`α_z a` at complex time `z`.

The entire analytic elements form a nonunital star subalgebra, on which the complex-time
extension is complex linear, multiplicative and satisfies `α_z (a⋆) = (α_{conj z} a)⋆`. It is
invariant under the action and its complex-time extension: `α_w (α_z a) = α_{z + w} a`. The
norm of `α_z a` depends only on the imaginary part of `z`, so the extension is bounded on
every horizontal strip of bounded width. Entire analytic elements lie in the domain of the
generator `δ` of `α`, where `δ a` is the complex derivative of the extension at `0`, and the
subalgebra is invariant under `δ`.

These are the elements on which the analytic form `ω(a α_{iβ}(b)) = ω(b a)` of the KMS
condition is stated.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
Section 2.5.3, for entire analytic elements of one-parameter groups of automorphisms.
-/

public section

noncomputable section

open scoped ComplexConjugate

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- An element is entire analytic for a real action when its orbit `t ↦ α_t a` is the
restriction to the real line of an entire `A`-valued function. -/
def IsEntireAnalytic (α : CStarAction (Multiplicative ℝ) A) (a : A) : Prop :=
  ∃ F : ℂ → A, Differentiable ℂ F ∧ ∀ t : ℝ, F t = α (Multiplicative.ofAdd t) a

open scoped Classical in
/-- The complex-time action `z ↦ α_z a` on an entire analytic element `a`: the unique entire
continuation of its orbit. It is identically zero when `a` is not entire analytic. -/
def entireExtension (α : CStarAction (Multiplicative ℝ) A) (a : A) : ℂ → A :=
  if h : α.IsEntireAnalytic a then h.choose else 0

variable {α : CStarAction (Multiplicative ℝ) A} {a b : A}

/-- The complex-time extension vanishes away from the entire analytic elements. -/
@[simp]
theorem entireExtension_of_not_isEntireAnalytic (h : ¬α.IsEntireAnalytic a) :
    α.entireExtension a = 0 := by
  rw [entireExtension, dite_eq_right h]

namespace IsEntireAnalytic

/-- The complex-time extension of an entire analytic element is entire. -/
theorem differentiable_entireExtension (h : α.IsEntireAnalytic a) :
    Differentiable ℂ (α.entireExtension a) := by
  rw [entireExtension, dite_eq_left h]
  exact h.choose_spec.1

/-- At real times the complex-time extension is the action. -/
@[simp]
theorem entireExtension_ofReal (h : α.IsEntireAnalytic a) (t : ℝ) :
    α.entireExtension a t = α (Multiplicative.ofAdd t) a := by
  rw [entireExtension, dite_eq_left h]
  exact h.choose_spec.2 t

/-- At time zero the complex-time extension is the identity. -/
@[simp]
theorem entireExtension_apply_zero (h : α.IsEntireAnalytic a) : α.entireExtension a 0 = a := by
  simpa using h.entireExtension_ofReal 0

end IsEntireAnalytic

/-- **Uniqueness of continuation.** Any entire extension of the orbit of `a` is the
complex-time extension of `a`. -/
theorem entireExtension_eq_of_differentiable {F : ℂ → A} (hF : Differentiable ℂ F)
    (hFt : ∀ t : ℝ, F t = α (Multiplicative.ofAdd t) a) : α.entireExtension a = F := by
  have h : α.IsEntireAnalytic a := ⟨F, hF, hFt⟩
  exact h.differentiable_entireExtension.eq_of_ofReal_eq hF fun t => by
    rw [h.entireExtension_ofReal, hFt]

/-- An element is entire analytic exactly when its complex-time extension is an entire
extension of its orbit. -/
theorem isEntireAnalytic_iff :
    α.IsEntireAnalytic a ↔ Differentiable ℂ (α.entireExtension a) ∧
      ∀ t : ℝ, α.entireExtension a t = α (Multiplicative.ofAdd t) a :=
  ⟨fun h => ⟨h.differentiable_entireExtension, h.entireExtension_ofReal⟩,
    fun h => ⟨_, h.1, h.2⟩⟩

namespace IsEntireAnalytic

/-- **Time shift.** Translating complex time by a real time `t` is the action of `t`. -/
theorem entireExtension_add_ofReal (h : α.IsEntireAnalytic a) (z : ℂ) (t : ℝ) :
    α.entireExtension a (z + t) = α (Multiplicative.ofAdd t) (α.entireExtension a z) := by
  have hF := h.differentiable_entireExtension
  have := (hF.comp (differentiable_id.add_const (t : ℂ))).eq_of_ofReal_eq
    ((α.toContinuousLinearMap (Multiplicative.ofAdd t)).differentiable.comp hF) fun s => by
      simp only [Function.comp_apply, id_eq, toContinuousLinearMap_apply, ← Complex.ofReal_add,
        h.entireExtension_ofReal, ofAdd_add, mul_comm (Multiplicative.ofAdd s), mul_apply]
  simpa using congrFun this z

/-- The values of the complex-time extension are again entire analytic. -/
theorem isEntireAnalytic_entireExtension (h : α.IsEntireAnalytic a) (z : ℂ) :
    α.IsEntireAnalytic (α.entireExtension a z) :=
  ⟨fun w => α.entireExtension a (z + w),
    h.differentiable_entireExtension.comp (differentiable_const z |>.add differentiable_id),
    h.entireExtension_add_ofReal z⟩

/-- **Group law in complex time.** `α_w (α_z a) = α_{z + w} a`. -/
theorem entireExtension_entireExtension (h : α.IsEntireAnalytic a) (z w : ℂ) :
    α.entireExtension (α.entireExtension a z) w = α.entireExtension a (z + w) :=
  congrFun (entireExtension_eq_of_differentiable
    (h.differentiable_entireExtension.comp (differentiable_const z |>.add differentiable_id))
    (h.entireExtension_add_ofReal z)) w

/-- The action at a real time preserves entire analyticity. -/
theorem apply (h : α.IsEntireAnalytic a) (t : ℝ) :
    α.IsEntireAnalytic (α (Multiplicative.ofAdd t) a) := by
  simpa only [h.entireExtension_ofReal] using h.isEntireAnalytic_entireExtension t

/-- The complex-time extension of a real translate is the translated extension. -/
theorem entireExtension_action (h : α.IsEntireAnalytic a) (t : ℝ) (z : ℂ) :
    α.entireExtension (α (Multiplicative.ofAdd t) a) z = α.entireExtension a (t + z) := by
  simpa only [h.entireExtension_ofReal] using h.entireExtension_entireExtension t z

/-- The norm of `α_z a` depends only on the imaginary part of `z`. -/
theorem norm_entireExtension (h : α.IsEntireAnalytic a) (z : ℂ) :
    ‖α.entireExtension a z‖ = ‖α.entireExtension a (z.im * Complex.I)‖ := by
  conv_lhs => rw [← Complex.re_add_im z, add_comm, h.entireExtension_add_ofReal]
  exact StarAlgEquiv.norm_map _ _

/-- **Strip bound.** The complex-time extension is bounded on every horizontal strip whose
imaginary parts form a bounded set. -/
theorem isBounded_image_im_preimage (h : α.IsEntireAnalytic a) {s : Set ℝ}
    (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (α.entireExtension a '' (Complex.im ⁻¹' s)) := by
  have hcont : Continuous fun y : ℝ => α.entireExtension a (y * Complex.I) :=
    h.differentiable_entireExtension.continuous.comp
      (Complex.continuous_ofReal.mul continuous_const)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (hs.isCompact_closure.image hcont).isBounded
  refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [h.norm_entireExtension]
  exact hC _ ⟨z.im, subset_closure hz, rfl⟩

end IsEntireAnalytic

/-- An element is entire analytic exactly when one of its real translates is. -/
@[simp]
theorem isEntireAnalytic_apply_iff (t : ℝ) :
    α.IsEntireAnalytic (α (Multiplicative.ofAdd t) a) ↔ α.IsEntireAnalytic a := by
  refine ⟨fun h => ?_, fun h => h.apply t⟩
  simpa only [ofAdd_neg, inv_apply_apply] using h.apply (-t)

/-! ### Algebraic operations -/

/-- Zero is entire analytic. -/
@[simp]
theorem isEntireAnalytic_zero : α.IsEntireAnalytic 0 :=
  ⟨0, differentiable_const 0, fun t => by simp⟩

/-- The complex-time extension of zero vanishes. -/
@[simp]
theorem entireExtension_zero : α.entireExtension 0 = 0 :=
  entireExtension_eq_of_differentiable (differentiable_const 0) fun t => by simp

namespace IsEntireAnalytic

/-- Sums of entire analytic elements are entire analytic. -/
theorem add (ha : α.IsEntireAnalytic a) (hb : α.IsEntireAnalytic b) :
    α.IsEntireAnalytic (a + b) :=
  ⟨_, ha.differentiable_entireExtension.add hb.differentiable_entireExtension, fun t => by
    simp [ha.entireExtension_ofReal, hb.entireExtension_ofReal]⟩

/-- The complex-time extension is additive. -/
@[simp]
theorem entireExtension_add (ha : α.IsEntireAnalytic a) (hb : α.IsEntireAnalytic b) (z : ℂ) :
    α.entireExtension (a + b) z = α.entireExtension a z + α.entireExtension b z :=
  congrFun (entireExtension_eq_of_differentiable
    (ha.differentiable_entireExtension.add hb.differentiable_entireExtension) fun t => by
      simp [ha.entireExtension_ofReal, hb.entireExtension_ofReal]) z

/-- Scalar multiples of entire analytic elements are entire analytic. -/
theorem smul (c : ℂ) (ha : α.IsEntireAnalytic a) : α.IsEntireAnalytic (c • a) :=
  ⟨_, ha.differentiable_entireExtension.const_smul c, fun t => by
    simp [ha.entireExtension_ofReal]⟩

/-- The complex-time extension is complex linear. -/
@[simp]
theorem entireExtension_smul (c : ℂ) (ha : α.IsEntireAnalytic a) (z : ℂ) :
    α.entireExtension (c • a) z = c • α.entireExtension a z :=
  congrFun (entireExtension_eq_of_differentiable
    (ha.differentiable_entireExtension.const_smul c) fun t => by
      simp [ha.entireExtension_ofReal]) z

/-- The pointwise product of the complex-time extensions of two entire analytic elements is
entire. The bilinear form of the product rule applies in a possibly nonunital algebra. -/
private theorem differentiable_entireExtension_mul (ha : α.IsEntireAnalytic a)
    (hb : α.IsEntireAnalytic b) :
    Differentiable ℂ fun z => α.entireExtension a z * α.entireExtension b z :=
  (ContinuousLinearMap.mul ℂ A).isBoundedBilinearMap.differentiable.comp
    (ha.differentiable_entireExtension.prodMk hb.differentiable_entireExtension)

/-- Negatives of entire analytic elements are entire analytic. -/
theorem neg (ha : α.IsEntireAnalytic a) : α.IsEntireAnalytic (-a) :=
  ⟨_, ha.differentiable_entireExtension.neg, fun t => by simp [ha.entireExtension_ofReal]⟩

/-- The complex-time extension commutes with negation. -/
@[simp]
theorem entireExtension_neg (ha : α.IsEntireAnalytic a) (z : ℂ) :
    α.entireExtension (-a) z = -α.entireExtension a z :=
  congrFun (entireExtension_eq_of_differentiable ha.differentiable_entireExtension.neg fun t => by
    simp [ha.entireExtension_ofReal]) z

/-- Differences of entire analytic elements are entire analytic. -/
theorem sub (ha : α.IsEntireAnalytic a) (hb : α.IsEntireAnalytic b) :
    α.IsEntireAnalytic (a - b) :=
  ⟨_, ha.differentiable_entireExtension.sub hb.differentiable_entireExtension, fun t => by
    simp [ha.entireExtension_ofReal, hb.entireExtension_ofReal]⟩

/-- The complex-time extension commutes with subtraction. -/
@[simp]
theorem entireExtension_sub (ha : α.IsEntireAnalytic a) (hb : α.IsEntireAnalytic b) (z : ℂ) :
    α.entireExtension (a - b) z = α.entireExtension a z - α.entireExtension b z :=
  congrFun (entireExtension_eq_of_differentiable
    (ha.differentiable_entireExtension.sub hb.differentiable_entireExtension) fun t => by
      simp [ha.entireExtension_ofReal, hb.entireExtension_ofReal]) z

/-- Products of entire analytic elements are entire analytic. -/
theorem mul (ha : α.IsEntireAnalytic a) (hb : α.IsEntireAnalytic b) :
    α.IsEntireAnalytic (a * b) :=
  ⟨_, ha.differentiable_entireExtension_mul hb,
    fun t => by simp [ha.entireExtension_ofReal, hb.entireExtension_ofReal]⟩

/-- The complex-time extension is multiplicative: `α_z (a b) = α_z a α_z b`. -/
@[simp]
theorem entireExtension_mul (ha : α.IsEntireAnalytic a) (hb : α.IsEntireAnalytic b) (z : ℂ) :
    α.entireExtension (a * b) z = α.entireExtension a z * α.entireExtension b z :=
  congrFun (entireExtension_eq_of_differentiable (ha.differentiable_entireExtension_mul hb)
    fun t => by simp [ha.entireExtension_ofReal, hb.entireExtension_ofReal]) z

/-- The entire continuation of the orbit of `a⋆` is `z ↦ (α_{conj z} a)⋆`. -/
private theorem differentiable_star_entireExtension_conj (ha : α.IsEntireAnalytic a) :
    Differentiable ℂ fun z => star (α.entireExtension a (conj z)) := fun z => by
  simpa [Function.comp_def] using
    (ha.differentiable_entireExtension (conj z)).star_conj

/-- Adjoints of entire analytic elements are entire analytic. -/
theorem star (ha : α.IsEntireAnalytic a) : α.IsEntireAnalytic (star a) :=
  ⟨_, ha.differentiable_star_entireExtension_conj, fun t => by
    simp [ha.entireExtension_ofReal, map_star]⟩

/-- **Star relation.** `α_z (a⋆) = (α_{conj z} a)⋆`. -/
@[simp]
theorem entireExtension_star (ha : α.IsEntireAnalytic a) (z : ℂ) :
    α.entireExtension (Star.star a) z = Star.star (α.entireExtension a (conj z)) :=
  congrFun (entireExtension_eq_of_differentiable ha.differentiable_star_entireExtension_conj
    fun t => by simp [ha.entireExtension_ofReal, map_star]) z

end IsEntireAnalytic

/-- Star preserves entire analyticity in both directions. -/
@[simp]
theorem isEntireAnalytic_star_iff : α.IsEntireAnalytic (star a) ↔ α.IsEntireAnalytic a :=
  ⟨fun h => by simpa using h.star, IsEntireAnalytic.star⟩

/-- The entire analytic elements of a real action, as a nonunital star subalgebra. -/
def entireAnalytic (α : CStarAction (Multiplicative ℝ) A) : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | α.IsEntireAnalytic a}
  zero_mem' := isEntireAnalytic_zero
  add_mem' := IsEntireAnalytic.add
  smul_mem' c _ h := h.smul c
  mul_mem' := IsEntireAnalytic.mul
  star_mem' := IsEntireAnalytic.star

/-- Membership in the entire analytic subalgebra is entire analyticity. -/
@[simp]
theorem mem_entireAnalytic : a ∈ α.entireAnalytic ↔ α.IsEntireAnalytic a :=
  Iff.rfl

/-! ### The generator -/

namespace IsEntireAnalytic

/-- The real derivative of an orbit is the complex derivative of its entire extension. -/
private theorem hasDerivAt_orbit (h : α.IsEntireAnalytic a) (t : ℝ) :
    HasDerivAt (fun s : ℝ => α (Multiplicative.ofAdd s) a) (deriv (α.entireExtension a) t) t := by
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul,
    h.entireExtension_ofReal] using
    (h.differentiable_entireExtension (t : ℂ)).hasDerivAt.scomp t Complex.ofRealCLM.hasDerivAt

/-- Entire analytic elements lie in the domain of the generator. -/
theorem mem_generator_domain (h : α.IsEntireAnalytic a) : a ∈ α.generator.domain :=
  (α.mem_generator_domain_iff_differentiableAt a).mpr (h.hasDerivAt_orbit 0).differentiableAt

/-- On an entire analytic element the generator is the complex derivative at time zero of the
complex-time extension. -/
theorem generator_eq_deriv (h : α.IsEntireAnalytic a) :
    α.generator ⟨a, h.mem_generator_domain⟩ = deriv (α.entireExtension a) 0 := by
  simpa using α.generator_eq_of_hasDerivAt h.mem_generator_domain (h.hasDerivAt_orbit 0)

/-- The complex-time extension of the generator value is the derivative of the extension. -/
theorem entireExtension_generator (h : α.IsEntireAnalytic a) :
    α.entireExtension (α.generator ⟨a, h.mem_generator_domain⟩) =
      deriv (α.entireExtension a) :=
  entireExtension_eq_of_differentiable h.differentiable_entireExtension.deriv fun t =>
    (h.hasDerivAt_orbit t).unique (α.hasDerivAt ⟨a, h.mem_generator_domain⟩ t)

/-- The generator maps entire analytic elements to entire analytic elements. -/
theorem generator (h : α.IsEntireAnalytic a) :
    α.IsEntireAnalytic (α.generator ⟨a, h.mem_generator_domain⟩) :=
  ⟨_, h.differentiable_entireExtension.deriv, fun t =>
    (h.hasDerivAt_orbit t).unique (α.hasDerivAt ⟨a, h.mem_generator_domain⟩ t)⟩

end IsEntireAnalytic

/-- The entire analytic subalgebra is contained in the generator domain. -/
theorem entireAnalytic_le_generatorDomain (α : CStarAction (Multiplicative ℝ) A) :
    α.entireAnalytic ≤ α.generatorDomain := fun a h =>
  (α.mem_generatorDomain a).mpr (IsEntireAnalytic.mem_generator_domain h)

/-! ### Examples -/

/-- For the trivial action every element is entire analytic. -/
@[simp]
theorem isEntireAnalytic_trivial (a : A) : (trivial : CStarAction _ A).IsEntireAnalytic a :=
  ⟨fun _ => a, differentiable_const a, fun t => by simp⟩

/-- For the trivial action the complex-time extension is constant. -/
@[simp]
theorem entireExtension_trivial (a : A) :
    (trivial : CStarAction _ A).entireExtension a = fun _ => a :=
  entireExtension_eq_of_differentiable (differentiable_const a) fun t => by simp

section Unital

variable {B : Type*} [CStarAlgebra B]

/-- In a unital algebra the identity is entire analytic. -/
@[simp]
theorem isEntireAnalytic_one (α : CStarAction (Multiplicative ℝ) B) : α.IsEntireAnalytic 1 :=
  ⟨fun _ => 1, differentiable_const 1, fun t => by simp⟩

/-- The complex-time extension of the identity is constant. -/
@[simp]
theorem entireExtension_one (α : CStarAction (Multiplicative ℝ) B) :
    α.entireExtension 1 = fun _ => 1 :=
  entireExtension_eq_of_differentiable (differentiable_const 1) fun t => by simp

end Unital

end TauCeti.CStarAction
