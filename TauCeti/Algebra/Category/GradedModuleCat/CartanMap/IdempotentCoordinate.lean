/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.IdempotentGradedDimension

/-!
# Idempotent coordinates on the graded Grothendieck group of finite graded modules

Let `A` be a finite-dimensional algebra over a field `k`, with homogeneous pieces
`𝒜 : ℤ → Submodule k A`, and let `e ∈ 𝒜 0` be an idempotent of degree zero. For a finitely
generated graded `A`-module `M`, the subspaces `e • Mₚ` are finite-dimensional and vanish for all
but finitely many degrees `p`, so they have a graded dimension

```text
gdim_e(M) = ∑ₚ dim_k(e • Mₚ) qᵖ ∈ ℤ[q,q⁻¹].
```

Because `e` is an idempotent of degree zero, `M ↦ e • Mₚ` is exact in each degree, so `gdim_e` is
additive on short exact sequences of graded modules. Shifting the grading multiplies it by a power
of `q`, so it descends to a `ℤ[q,q⁻¹]`-linear coordinate

```text
TauCeti.gradedIdempotentCoordinate : G₀^gr(mod A) ⟶ ℤ[q,q⁻¹]
```

on the Laurent Grothendieck group of finite graded modules, the target of the graded Cartan map
`TauCeti.gradedCartanMap`.

For `e = 1` this is the graded dimension of `M`. In general `e • Mₚ` is the degree-`p` piece of
the summand `e • M`. Suppose the graded simple modules are the shifts `Sᵢ{d}` of modules `Sᵢ`
concentrated in degree zero, and the idempotents `eᵢ` satisfy `dim_k(eᵢ • Sⱼ) = δᵢⱼ`, as for the
vertex idempotents of a basic algebra whose simple modules are one-dimensional. Then additivity
along a graded composition series shows that `dim_k(eᵢ • Mₚ)` counts the composition factors of
`M` isomorphic to `Sᵢ{p}`, so these coordinates read graded composition multiplicities, and in
particular the entries of the graded Cartan matrix. The last result of this file turns
Kronecker-delta coordinates into linear independence of classes over `ℤ[q,q⁻¹]`.

## Main definitions

* `TauCeti.gradedIdempotentCoordinate`: the induced `ℤ[q,q⁻¹]`-linear coordinate on the graded
  Grothendieck group of finite graded modules.

## Main results

* `TauCeti.gradedIdempotentCoordinate_of`: the coordinate of the class of `M` is `gdim_e(M)`.
* `TauCeti.linearIndependent_laurentK0_of_smulGradedDimension`: classes with Kronecker-delta
  idempotent coordinates are linearly independent over `ℤ[q,q⁻¹]`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded modules
  and their degree shifts.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Grothendieck group as a `ℤ[q,q⁻¹]`-module and graded dimensions.
* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the ungraded coordinates `dim_k(e M)` on the
  Grothendieck group and the Cartan matrix.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA

/-! ### The coordinate on the graded Grothendieck group -/

section Coordinate

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [Module.Finite k A]

variable {e : A}

/-- The graded dimension of `e • M` as a shift-compatible invariant of finite graded modules. -/
private def smulGradedDimensionInvariant (he : IsIdempotentElem e) (he₀ : e ∈ 𝒜 0) :
    GradedExactStructure.ShiftInvariant (gradedFiniteModulesExactStructure 𝒜)
      (laurentTAut ℤ (LaurentPolynomial ℤ)) where
  obj M := M.obj.smulGradedDimension e
  map_conflation S hS := by
    rw [gradedFiniteModulesExactStructure_conflation_iff] at hS
    have : Module.Finite k (S.map (gradedFiniteModules 𝒜).ι).X₁ :=
      inferInstanceAs (Module.Finite k S.X₁.obj)
    have : Module.Finite k (S.map (gradedFiniteModules 𝒜).ι).X₂ :=
      inferInstanceAs (Module.Finite k S.X₂.obj)
    have : Module.Finite k (S.map (gradedFiniteModules 𝒜).ι).X₃ :=
      inferInstanceAs (Module.Finite k S.X₃.obj)
    exact GradedModuleCat.smulGradedDimension_shortExact he he₀ hS
  map_shift M := by
    -- The restricted shift agrees with the ambient shift `M ↦ M{1}` up to isomorphism.
    have : Module.Finite k
        (((gradedFiniteModules 𝒜).ι ⋙ (GradedModuleCat.shift 𝒜).functor).obj M) :=
      inferInstanceAs (Module.Finite k M.obj)
    have : Module.Finite k
        (((gradedFiniteModulesExactStructure 𝒜).shift.functor ⋙
          (gradedFiniteModules 𝒜).ι).obj M) :=
      inferInstanceAs
        (Module.Finite k ((gradedFiniteModulesExactStructure 𝒜).shift.functor.obj M).obj)
    refine (GradedModuleCat.smulGradedDimension_congr e
      ((gradedFiniteModulesExactStructureShiftFunctorCompιIso (𝒜 := 𝒜)).app M)).trans ?_
    rw [laurentTAut_apply, smul_eq_mul]
    exact M.obj.smulGradedDimension_shiftObj e 1

/-- **The idempotent coordinate** on the graded Grothendieck group of finite graded modules over a
finite-dimensional algebra: the `ℤ[q,q⁻¹]`-linear map sending the class of `M` to the graded
dimension `∑ₚ dim_k(e • Mₚ) qᵖ` of `e • M`, for an idempotent `e` of degree zero. -/
def gradedIdempotentCoordinate (he : IsIdempotentElem e) (he₀ : e ∈ 𝒜 0) :
    LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentPolynomial ℤ :=
  LaurentK0.lift _ (smulGradedDimensionInvariant he he₀)

/-- **The idempotent coordinate of a class.** Evaluating `gradedIdempotentCoordinate` on the class
`[M]` of a finite graded module recovers the graded dimension `∑ₚ dim_k(e • Mₚ) qᵖ` of `e • M`. -/
@[simp]
theorem gradedIdempotentCoordinate_of (he : IsIdempotentElem e) (he₀ : e ∈ 𝒜 0)
    (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    gradedIdempotentCoordinate he he₀
        (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M) =
      M.obj.smulGradedDimension e :=
  LaurentK0.lift_of.{uA} _ M

/-- **Classes with Kronecker-delta idempotent coordinates are linearly independent.** If the
graded dimension of `eᵢ • Sⱼ` is `1` for `i = j` and `0` otherwise, the classes of the finite
graded modules `Sⱼ` are linearly independent over `ℤ[q,q⁻¹]`. -/
theorem linearIndependent_laurentK0_of_smulGradedDimension {I : Type*} {e : I → A}
    (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory)
    (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1) :
    LinearIndependent (LaurentPolynomial ℤ) fun i =>
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i) :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun i => gradedIdempotentCoordinate (he i) (he₀ i))
    (fun i j hij => by simpa using hne hij) (fun i => by simpa using hself i)

end Coordinate

end TauCeti
