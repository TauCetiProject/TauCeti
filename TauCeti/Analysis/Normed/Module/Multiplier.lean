/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.DoubleCentralizer

/-!
# Extending essential Banach modules to multipliers

A bounded multiplicative action `π : A →L[𝕜] (E →L[𝕜] E)` whose ranges span a dense
subspace extends uniquely to a unital bounded representation of `𝓜(𝕜, A)`, provided
`A` has a bounded left approximate identity. The action need not be contractive,
and `E` need not be a Hilbert space. The extension satisfies
`π'(m) (π(a) x) = π(m.fst a) x` and `‖π'(m)‖ ≤ C * ‖π‖ * ‖m‖`.
These identities also show that bounded intertwiners extend to the multiplier actions.

The construction uses `DoubleCentralizer.exists_clm_tendsto_fst`. Its algebraic
assembly generalizes the Hilbert-space construction in
`NonUnitalStarAlgHom.multiplierExtension`.

## References

* M. A. Rieffel, *C⋆-algebras*, Math 208 lectures, UC Berkeley, Spring 2008,
  notes by T. Johnson-Freyd, p. 38.
-/

public noncomputable section

open Filter Topology
open scoped MultiplierAlgebra

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (π : A →L[𝕜] E →L[𝕜] E)
  (hmul : ∀ a b, π (a * b) = π a * π b)
  (hdense : Dense (Submodule.span 𝕜 (⋃ a, Set.range (π a)) : Set E))
  {l : Filter A} [l.NeBot] {C : ℝ}
  (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a))

private def multiplierOp (m : 𝓜(𝕜, A)) : E →L[𝕜] E :=
  (m.exists_clm_tendsto_fst hC hl (fun _ => by fun_prop) hmul π.le_opNorm hdense).choose

private theorem multiplierOp_spec (m : 𝓜(𝕜, A)) :
    (∀ a, multiplierOp π hmul hdense hC hl m * π a = π (m.fst a)) ∧
      ∀ x, Tendsto (fun e => π (m.fst e) x) l
        (𝓝 (multiplierOp π hmul hdense hC hl m x)) :=
  (m.exists_clm_tendsto_fst hC hl (fun _ => by fun_prop) hmul π.le_opNorm hdense).choose_spec

private theorem eq_multiplierOp {m : 𝓜(𝕜, A)} {T : E →L[𝕜] E}
    (hT : ∀ a, T * π a = π (m.fst a)) : T = multiplierOp π hmul hdense hC hl m := by
  refine ContinuousLinearMap.ext_on hdense fun x hx => ?_
  obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.1 hx
  exact congrArg (fun S : E →L[𝕜] E => S y)
    ((hT a).trans ((multiplierOp_spec π hmul hdense hC hl m).1 a).symm)

/-- The unique unital extension of a bounded essential action to the multiplier algebra.
Only a bounded left approximate identity is needed. -/
def multiplierExtension : 𝓜(𝕜, A) →ₐ[𝕜] (E →L[𝕜] E) where
  toFun := multiplierOp π hmul hdense hC hl
  map_one' := (eq_multiplierOp π hmul hdense hC hl fun a => by simp).symm
  map_mul' m n := (eq_multiplierOp π hmul hdense hC hl fun a => by
    simp [mul_assoc, (multiplierOp_spec π hmul hdense hC hl _).1]).symm
  map_zero' := (eq_multiplierOp π hmul hdense hC hl fun a => by simp).symm
  map_add' m n := (eq_multiplierOp π hmul hdense hC hl fun a => by
    simp [add_mul, (multiplierOp_spec π hmul hdense hC hl _).1]).symm
  commutes' r := (eq_multiplierOp π hmul hdense hC hl fun a => by
    simp [Algebra.algebraMap_eq_smul_one]).symm

/-- The multiplier extension acts on the essential generators by the left centralizer. -/
@[simp]
theorem multiplierExtension_mul_eq_fst (m : 𝓜(𝕜, A)) (a : A) :
    π.multiplierExtension hmul hdense hC hl m * π a = π (m.fst a) :=
  (multiplierOp_spec π hmul hdense hC hl m).1 a

/-- Pointwise formula for the action on an essential generator. -/
@[simp]
theorem multiplierExtension_apply_apply (m : 𝓜(𝕜, A)) (a : A) (x : E) :
    π.multiplierExtension hmul hdense hC hl m (π a x) = π (m.fst a) x :=
  congrArg (fun S : E →L[𝕜] E => S x)
    (π.multiplierExtension_mul_eq_fst hmul hdense hC hl m a)

/-- The defining identity characterizes the extended operator uniquely. -/
theorem eq_multiplierExtension_iff {m : 𝓜(𝕜, A)} {T : E →L[𝕜] E} :
    T = π.multiplierExtension hmul hdense hC hl m ↔ ∀ a, T * π a = π (m.fst a) :=
  ⟨fun h a => h ▸ π.multiplierExtension_mul_eq_fst hmul hdense hC hl m a,
    eq_multiplierOp π hmul hdense hC hl⟩

/-- Right multiplication by the extension is given by the right centralizer. -/
@[simp]
theorem mul_multiplierExtension_eq_snd (m : 𝓜(𝕜, A)) (a : A) :
    π a * π.multiplierExtension hmul hdense hC hl m = π (m.snd a) := by
  refine ContinuousLinearMap.ext_on hdense fun x hx => ?_
  obtain ⟨b, y, rfl⟩ := Set.mem_iUnion.1 hx
  simp only [mul_apply_eq_comp, multiplierExtension_apply_apply]
  rw [← mul_apply_eq_comp, ← hmul, ← m.central, hmul, mul_apply_eq_comp]

/-- The extension agrees with the original action on canonical multipliers. -/
@[simp]
theorem multiplierExtension_coe (a : A) :
    π.multiplierExtension hmul hdense hC hl (a : 𝓜(𝕜, A)) = π a :=
  ((π.eq_multiplierExtension_iff hmul hdense hC hl).2 fun b => by simp [hmul]).symm

/-- Strong-limit construction of the extended action. -/
theorem tendsto_multiplierExtension_apply (m : 𝓜(𝕜, A)) (x : E) :
    Tendsto (fun e => π (m.fst e) x) l
      (𝓝 (π.multiplierExtension hmul hdense hC hl m x)) :=
  (multiplierOp_spec π hmul hdense hC hl m).2 x

/-- The extension has norm bound `C * ‖π‖`; no contractivity of the action is assumed. -/
theorem norm_multiplierExtension_le (m : 𝓜(𝕜, A)) :
    ‖π.multiplierExtension hmul hdense hC hl m‖ ≤ C * ‖π‖ * ‖m‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg hC.exists.choose).trans hC.exists.choose_spec
  refine opNorm_le_bound _ (by positivity) fun x => ?_
  apply le_of_tendsto (π.tendsto_multiplierExtension_apply hmul hdense hC hl m x).norm
  filter_upwards [hC] with e he
  calc
    ‖π (m.fst e) x‖ ≤ ‖π‖ * (‖m.fst‖ * ‖e‖) * ‖x‖ := by
      exact (π (m.fst e)).le_opNorm x |>.trans <|
        mul_le_mul_of_nonneg_right
          ((π.le_opNorm _).trans (mul_le_mul_of_nonneg_left (m.fst.le_opNorm e)
            (norm_nonneg π))) (norm_nonneg x)
    _ ≤ ‖π‖ * (‖m‖ * C) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul (DoubleCentralizer.norm_fst_le m) he (norm_nonneg e) (norm_nonneg m))
          (norm_nonneg π)) (norm_nonneg x)
    _ = C * ‖π‖ * ‖m‖ * ‖x‖ := by ring

/-- The unital algebra homomorphism on multipliers is bounded. -/
@[fun_prop]
theorem continuous_multiplierExtension :
    Continuous (π.multiplierExtension hmul hdense hC hl) :=
  AddMonoidHomClass.continuous_of_bound (π.multiplierExtension hmul hdense hC hl)
    (C * ‖π‖) (π.norm_multiplierExtension_le hmul hdense hC hl)

/-- Every multiplicative map extending the original action is the multiplier extension.
In particular the result is independent of the approximate identity and its bound. -/
theorem eq_multiplierExtension_of_apply_coe {G : Type*}
    [FunLike G 𝓜(𝕜, A) (E →L[𝕜] E)] [MulHomClass G 𝓜(𝕜, A) (E →L[𝕜] E)]
    (ψ : G) (hψ : ∀ a : A, ψ a = π a) :
    ⇑ψ = π.multiplierExtension hmul hdense hC hl := by
  have := TauCeti.faithfulSMul_mulOpposite_of_tendsto_mul_right hl
  funext m
  refine (π.eq_multiplierExtension_iff hmul hdense hC hl).2 fun a => ?_
  rw [← hψ, ← map_mul, DoubleCentralizer.mul_coe_eq_coe_fst, hψ]

/-- Bounded intertwiners of essential actions also intertwine their multiplier extensions. -/
theorem comp_multiplierExtension {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] (ρ : A →L[𝕜] F →L[𝕜] F)
    (hρmul : ∀ a b, ρ (a * b) = ρ a * ρ b)
    (hρdense : Dense (Submodule.span 𝕜 (⋃ a, Set.range (ρ a)) : Set F))
    (S : E →L[𝕜] F) (hS : ∀ a, S.comp (π a) = (ρ a).comp S) (m : 𝓜(𝕜, A)) :
    S.comp (π.multiplierExtension hmul hdense hC hl m) =
      (ρ.multiplierExtension hρmul hρdense hC hl m).comp S := by
  refine ContinuousLinearMap.ext_on hdense fun x hx => ?_
  obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.1 hx
  have hSy (b : A) (z : E) : S (π b z) = ρ b (S z) :=
    congrArg (fun T : E →L[𝕜] F => T z) (hS b)
  simp [hSy]

end ContinuousLinearMap
