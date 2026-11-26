/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily.Basic
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.RayClass
public import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Cyclic families viewed as ray class characters of ℚ

The primitive rational character dictionary sends a cyclic Dirichlet family to a finite set of
ray class characters. A weight function on the Dirichlet family extends by zero to a finitely
supported ray class weight. Its support consists of precisely the images of the nonzero-weight
members, and weighted sums over the support recover the original cyclic-family sums. This lets
one apply analytic estimates for weighted families of ray class characters to cyclic sums.

The underlying cyclic family is that of Levent Alpöge's `Formalism.HC.Level.cyc` and
`Formalism.HC.Level.ofSub`, as described in the cyclic-family basic module.
-/

public section

open scoped NumberField
open TauCeti.LFunctions

namespace TauCeti.PrimitiveDirichletCharacter

/-- The image of a cyclic Dirichlet family under the primitive rational character dictionary. -/
noncomputable def cyclicFamilyRayClass (ψ : PrimitiveDirichletCharacter) :
    Finset (PrimitiveRayClassCharacter ℚ) :=
  ψ.cyclicFamily.map toPrimitiveRayClassCharacter.toEmbedding

/-- Defining equation of `cyclicFamilyRayClass`: the image of the cyclic family under the
dictionary, as a `Finset.map`. -/
theorem cyclicFamilyRayClass_def (ψ : PrimitiveDirichletCharacter) :
    ψ.cyclicFamilyRayClass = ψ.cyclicFamily.map toPrimitiveRayClassCharacter.toEmbedding :=
  (rfl)

/-- A primitive ray class character of `ℚ` belongs to the image family precisely when its
Dirichlet counterpart belongs to the original cyclic family. -/
theorem mem_cyclicFamilyRayClass {ψ : PrimitiveDirichletCharacter}
    {η : PrimitiveRayClassCharacter ℚ} :
    η ∈ ψ.cyclicFamilyRayClass ↔ toPrimitiveRayClassCharacter.symm η ∈ ψ.cyclicFamily := by
  rw [cyclicFamilyRayClass, Finset.mem_map_equiv]

/-- The rational ray class family has as many members as the order of the generator. -/
@[simp] theorem card_cyclicFamilyRayClass (ψ : PrimitiveDirichletCharacter) :
    ψ.cyclicFamilyRayClass.card = orderOf ψ.character := by
  simp [cyclicFamilyRayClass]

/-- The trivial ray class character belongs to every rational cyclic family. -/
@[simp] theorem one_mem_cyclicFamilyRayClass (ψ : PrimitiveDirichletCharacter) :
    1 ∈ ψ.cyclicFamilyRayClass := by
  rw [← toPrimitiveRayClassCharacter_one, mem_cyclicFamilyRayClass, Equiv.symm_apply_apply]
  exact ψ.one_mem_cyclicFamily

/-- The rational dictionary preserves and reflects cyclic-family membership. -/
@[simp] theorem toPrimitiveRayClassCharacter_mem_cyclicFamilyRayClass
    {ψ κ : PrimitiveDirichletCharacter} :
    toPrimitiveRayClassCharacter κ ∈ ψ.cyclicFamilyRayClass ↔ κ ∈ ψ.cyclicFamily := by
  rw [mem_cyclicFamilyRayClass, Equiv.symm_apply_apply]

/-- The rational cyclic family of the trivial character contains only the trivial character. -/
@[simp] theorem cyclicFamilyRayClass_one : (1 : PrimitiveDirichletCharacter).cyclicFamilyRayClass =
    {1} := by
  simp [cyclicFamilyRayClass]

/-- The rational cyclic family is closed under inversion. -/
@[simp] theorem inv_mem_cyclicFamilyRayClass {ψ : PrimitiveDirichletCharacter}
    {η : PrimitiveRayClassCharacter ℚ} :
    η⁻¹ ∈ ψ.cyclicFamilyRayClass ↔ η ∈ ψ.cyclicFamilyRayClass := by
  obtain ⟨κ, rfl⟩ := toPrimitiveRayClassCharacter.surjective η
  simp only [← toPrimitiveRayClassCharacter_inv, mem_cyclicFamilyRayClass, Equiv.symm_apply_apply,
    inv_mem_cyclicFamily]

/-- The finite conductor of each member divides the finite conductor of the generator. -/
theorem finitePart_dvd_of_mem_cyclicFamilyRayClass {ψ : PrimitiveDirichletCharacter}
    {η : PrimitiveRayClassCharacter ℚ} (hη : η ∈ ψ.cyclicFamilyRayClass) :
    η.conductor.finitePart ∣ (toPrimitiveRayClassCharacter ψ).conductor.finitePart := by
  obtain ⟨κ, rfl⟩ := toPrimitiveRayClassCharacter.surjective η
  rw [mem_cyclicFamilyRayClass, Equiv.symm_apply_apply] at hη
  obtain ⟨d, hd⟩ := level_dvd_of_mem_cyclicFamily hη
  simp only [finitePart_conductor_toPrimitiveRayClassCharacter,
    Ideal.span_singleton_dvd_span_singleton_iff_dvd]
  exact ⟨d, by exact_mod_cast hd⟩

/-- Transfer weights on a cyclic Dirichlet family to primitive ray class characters of `ℚ`,
extending by zero outside the image family. Values outside the Dirichlet family are ignored. -/
noncomputable def cyclicFamilyWeights (ψ : PrimitiveDirichletCharacter)
    (w : PrimitiveDirichletCharacter → ℝ) : PrimitiveRayClassCharacter ℚ →₀ ℝ :=
  Finsupp.indicator ψ.cyclicFamilyRayClass (fun η _ ↦ w (toPrimitiveRayClassCharacter.symm η))

open scoped Classical in
/-- The transferred weight pulls back to the original weight on the cyclic family and to zero
elsewhere. -/
@[simp] theorem cyclicFamilyWeights_apply (ψ : PrimitiveDirichletCharacter)
    (w : PrimitiveDirichletCharacter → ℝ) (η : PrimitiveRayClassCharacter ℚ) :
    ψ.cyclicFamilyWeights w η =
      if η ∈ ψ.cyclicFamilyRayClass then w (toPrimitiveRayClassCharacter.symm η) else 0 := by
  simp only [cyclicFamilyWeights, Finsupp.indicator_apply, dite_eq_ite]

/-- Transfer preserves and reflects nonnegativity on the cyclic family. -/
@[simp] theorem cyclicFamilyWeights_nonneg (ψ : PrimitiveDirichletCharacter)
    (w : PrimitiveDirichletCharacter → ℝ) :
    0 ≤ ψ.cyclicFamilyWeights w ↔ ∀ κ ∈ ψ.cyclicFamily, 0 ≤ w κ := by
  classical
  rw [Finsupp.le_def]
  constructor
  · intro h κ hκ
    simpa [hκ] using h (toPrimitiveRayClassCharacter κ)
  · intro h η
    by_cases hη : η ∈ ψ.cyclicFamilyRayClass
    · simpa [hη] using h _ (mem_cyclicFamilyRayClass.mp hη)
    · simp [hη]

/-- A member contributes to the support exactly when its original weight is nonzero. -/
theorem mem_support_cyclicFamilyWeights {ψ : PrimitiveDirichletCharacter}
    {w : PrimitiveDirichletCharacter → ℝ} {η : PrimitiveRayClassCharacter ℚ} :
    η ∈ (ψ.cyclicFamilyWeights w).support ↔
      η ∈ ψ.cyclicFamilyRayClass ∧ w (toPrimitiveRayClassCharacter.symm η) ≠ 0 := by
  classical
  by_cases hη : η ∈ ψ.cyclicFamilyRayClass <;> simp [Finsupp.mem_support_iff, hη]

/-- The transferred weight has full support precisely when every weight on the original
cyclic family is nonzero. In particular, strict positivity of the weights suffices. -/
theorem support_cyclicFamilyWeights_eq_iff {ψ : PrimitiveDirichletCharacter}
    {w : PrimitiveDirichletCharacter → ℝ} :
    (ψ.cyclicFamilyWeights w).support = ψ.cyclicFamilyRayClass ↔
      ∀ κ ∈ ψ.cyclicFamily, w κ ≠ 0 := by
  constructor
  · intro h κ hκ
    have hmem : toPrimitiveRayClassCharacter κ ∈ (ψ.cyclicFamilyWeights w).support := by
      simpa [h] using hκ
    simpa using (mem_support_cyclicFamilyWeights.mp hmem).2
  · intro h
    ext η
    rw [mem_support_cyclicFamilyWeights]
    exact and_iff_left_of_imp fun hη ↦ h _ (mem_cyclicFamilyRayClass.mp hη)

/-- Pairing the transferred weight with a ray class observable is the original weighted sum,
with the observable evaluated under the rational dictionary. This applies to both real and
complex valued observables. -/
theorem sum_cyclicFamilyWeights {E : Type*} [AddCommMonoid E] [SMulWithZero ℝ E]
    (ψ : PrimitiveDirichletCharacter) (w : PrimitiveDirichletCharacter → ℝ)
    (f : PrimitiveRayClassCharacter ℚ → E) :
    (ψ.cyclicFamilyWeights w).sum (fun η c ↦ c • f η) =
      ∑ κ ∈ ψ.cyclicFamily, w κ • f (toPrimitiveRayClassCharacter κ) := by
  rw [cyclicFamilyWeights, Finsupp.sum_indicator_index, cyclicFamilyRayClass, Finset.sum_map]
  · simp
  · simp

end TauCeti.PrimitiveDirichletCharacter
