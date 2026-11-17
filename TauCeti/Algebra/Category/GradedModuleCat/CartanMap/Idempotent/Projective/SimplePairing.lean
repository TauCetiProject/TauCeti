/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.ForgetGrading
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# The graded projective/simple multiplicity pairing

Let `A` be a finite-dimensional nonnegatively graded algebra over a field `k` whose degree-zero
part is a semisimple ring, and let `eᵢ` be a complete family of orthogonal primitive idempotents
of degree zero whose left ideals `A eᵢ` are pairwise nonisomorphic. The graded projectives `A eᵢ`
form a `ℤ[q,q⁻¹]`-basis of `K₀^gr(proj A)` and their graded heads `Sᵢ = A eᵢ / A₊eᵢ` form a
`ℤ[q,q⁻¹]`-basis of `G₀^gr(mod A)`. The `i`th coordinate of the class of a finite graded module
`M` in the head basis is its graded multiplicity `[M : Sᵢ]_q = ∑_d [M : Sᵢ{d}] q^d`.

This file defines the graded multiplicity pairing

```text
⟨-, -⟩ : K₀^gr(proj A) × G₀^gr(mod A) ⟶ ℤ[q,q⁻¹],   ⟨[A eᵢ], [M]⟩ = [M : Sᵢ]_q,
```

q-antilinear in the projective variable and q-linear in the module variable, with the same
convention as the q-Euler form `TauCeti.gradedProjectiveExtEuler`. It is the graded counterpart
of the integral pairing `TauCeti.projectiveSimplePairing`. It is perfect on both sides, it reads
the graded Cartan matrix, and evaluating it at `q = 1` gives the ungraded pairing of the
underlying classes.

The pairing differs from the q-Euler form when the field does not split the simples: pairing
`[A eᵢ]` with `[M]` under the q-Euler form gives the graded dimension of `eᵢ • M`, which is
`dim_k End_A(Sᵢ)` times the graded multiplicity. The two pairings agree exactly when every
`End_A(Sᵢ)` is one-dimensional.

## Main definitions

* `TauCeti.gradedProjectiveSimplePairing`: the graded multiplicity pairing.

## Main results

* `TauCeti.gradedProjectiveSimplePairing_of_left`: pairing with `[A eᵢ]` is the `i`th
  coordinate in the head basis.
* `TauCeti.gradedProjectiveSimplePairing_of_right`: pairing with `[Sᵢ]` conjugates the `i`th
  coordinate in the projective basis.
* `TauCeti.gradedProjectiveSimplePairing_basis_shiftObj`: `⟨[A eᵢ], [Sⱼ{d}]⟩ = δᵢⱼ qᵈ`.
* `TauCeti.gradedProjectiveSimplePairing_bijective`,
  `TauCeti.gradedProjectiveSimplePairing_flip_bijective`: the pairing identifies each
  Grothendieck group with the linear or semilinear dual of the other.
* `TauCeti.gradedCartanMatrix_apply_eq_gradedProjectiveSimplePairing`: graded Cartan-matrix
  entries are graded multiplicities of projectives.
* `TauCeti.gradedProjectiveExtEuler_of_left_eq_mul_gradedProjectiveSimplePairing`:
  `χ_q([A eᵢ], y) = dim_k End_A(Sᵢ) · ⟨[A eᵢ], y⟩`.
* `TauCeti.gradedProjectiveExtEuler_eq_gradedProjectiveSimplePairing_iff`: the q-Euler form is the
  multiplicity pairing exactly when every `End_A(Sᵢ)` is one-dimensional.
* `TauCeti.laurentEval_one_gradedProjectiveSimplePairing`: at `q = 1` the pairing is the ungraded
  pairing of the underlying classes.

## References

* Peter Webb, *A Course in Finite Group Representation Theory*, Section 7.4, Proposition 7.4.1,
  for the factor `dim_k End_A(S)` relating Hom dimensions and composition multiplicities.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Sections 2.2 and 3.1, for the
  graded Grothendieck groups and the q-antilinear/q-linear convention.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [IsSemisimpleRing (𝒜 0)]
  {I : Type uI} [Fintype I] {e : I → A}
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hnoniso : Pairwise fun i j =>
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)))

/-- The basis `[A eᵢ]` of `K₀^gr(proj A)`. -/
local notation "bP" => gradedIdempotentProjectiveBasisOfPrimitive he
  (fun i ↦ Ideal.isHomogeneous_span_singleton 𝒜
    (SetLike.isHomogeneousElem_coe (Subtype.mk (e i) (he₀ i) : 𝒜 0)))
  hprim hnoniso

/-- The basis `[Sᵢ]` of `G₀^gr(mod A)`. -/
local notation "bS" => gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso

/-- The graded projective `A eᵢ`, as an object of finite graded projectives. -/
local notation "P" => (fun i : I ↦
  (ObjectProperty.FullSubcategory.mk (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i})
      (Ideal.isHomogeneous_span_singleton 𝒜
        (SetLike.isHomogeneousElem_coe (Subtype.mk (e i) (he₀ i) : 𝒜 0))))
    (gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i)
      (Ideal.isHomogeneous_span_singleton 𝒜
        (SetLike.isHomogeneousElem_coe (Subtype.mk (e i) (he₀ i) : 𝒜 0)))) :
        ObjectProperty.FullSubcategory (gradedFiniteProjectiveModules 𝒜)))

/-- The graded head `Sᵢ = A eᵢ / A₊eᵢ`, as an object of finite graded modules. -/
local notation "S" => (fun i : I ↦
  (ObjectProperty.FullSubcategory.mk (gradedPositiveMulQuotient 𝒜 (he₀ i))
    (gradedFiniteModules_gradedPositiveMulQuotient 𝒜 (he₀ i)) :
      ObjectProperty.FullSubcategory (gradedFiniteModules 𝒜)))

omit [IsSemisimpleRing (𝒜 0)] in
/-- The class `[A eᵢ]` is the `i`th vector of the basis `bP`, with its homogeneity proof fixed so
that it can be rewritten backwards. -/
private theorem projective_eq_basis (i : I) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i) = (bP) i :=
  (gradedIdempotentProjectiveBasisOfPrimitive_apply _ _ _ _ i).symm

/-- **The graded projective/simple multiplicity pairing**
`K₀^gr(proj A) × G₀^gr(mod A) → ℤ[q,q⁻¹]`. Pairing the class of `A eᵢ` with the class of a finite
graded module `M` gives the graded multiplicity `[M : Sᵢ]_q = ∑_d [M : Sᵢ{d}] q^d` of the graded
head `Sᵢ = A eᵢ / A₊eᵢ`. It is q-antilinear in the projective variable and q-linear in the module
variable, as the q-Euler form `TauCeti.gradedProjectiveExtEuler` is. This is the graded
counterpart of `TauCeti.projectiveSimplePairing`. -/
def gradedProjectiveSimplePairing :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      →ₛₗ[(LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
      LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
        LaurentPolynomial ℤ :=
  open scoped Classical in
  Matrix.toLinearMapₛₗ₂ _ (bP) (bS) 1

/-- In coordinates, the graded multiplicity pairing multiplies the conjugated projective-basis
coordinates of its first argument with the head-basis coordinates of its second. -/
theorem gradedProjectiveSimplePairing_apply
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))
    (y : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
    gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso x y =
      ∑ i, invert ((bP).repr x i) * (bS).repr y i := by
  classical
  rw [gradedProjectiveSimplePairing, Matrix.toLinearMapₛₗ₂_apply]
  simp [Matrix.one_apply]

/-- **Pairing with `[A eᵢ]` reads the graded multiplicity of `Sᵢ`**: it is the `i`th coordinate
in the basis of graded heads. -/
@[simp]
theorem gradedProjectiveSimplePairing_of_left (i : I)
    (y : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
    gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso (LaurentK0.of.{uA} _ (P i)) y =
      (bS).repr y i := by
  classical
  rw [gradedProjectiveSimplePairing_apply, projective_eq_basis he he₀ hprim hnoniso,
    Module.Basis.repr_self]
  simp [Finsupp.single_apply]

/-- Pairing a projective class with `[Sᵢ]` conjugates its `i`th coordinate in the basis
`[A eᵢ]`. -/
@[simp]
theorem gradedProjectiveSimplePairing_of_right
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) (i : I) :
    gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso x (LaurentK0.of.{uA} _ (S i)) =
      invert ((bP).repr x i) := by
  classical
  rw [gradedProjectiveSimplePairing_apply,
    ← gradedIdempotentHeadBasisOfPrimitive_apply hneg he he₀ hprim hnoniso, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

/-- **The graded multiplicity convention**: `⟨[A eᵢ], [Sⱼ{d}]⟩ = δᵢⱼ qᵈ`. Thus the `qᵈ`
coefficient of `⟨[A eᵢ], [M]⟩` counts the composition factors `Sᵢ{d}`. -/
@[simp high]
theorem gradedProjectiveSimplePairing_basis_shiftObj [DecidableEq I] (i j : I) (d : ℤ) :
    gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso (LaurentK0.of.{uA} _ (P i))
        (LaurentK0.of.{uA} _
          ⟨(gradedPositiveMulQuotient 𝒜 (he₀ j)).shiftObj d,
            gradedFiniteModules_shiftObj (gradedFiniteModules_gradedPositiveMulQuotient 𝒜 (he₀ j))
              d⟩) =
      if i = j then T d else 0 := by
  rw [laurentK0_of_shiftObj (S j), map_smul, gradedProjectiveSimplePairing_of_right,
    projective_eq_basis he he₀ hprim hnoniso,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

/-- The basis classes `[A eᵢ]` and `[Sⱼ]` pair as a Kronecker delta. -/
@[simp high]
theorem gradedProjectiveSimplePairing_basis [DecidableEq I] (i j : I) :
    gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso (LaurentK0.of.{uA} _ (P i))
        (LaurentK0.of.{uA} _ (S j)) =
      if i = j then 1 else 0 := by
  rw [gradedProjectiveSimplePairing_of_right, projective_eq_basis he he₀ hprim hnoniso,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

/-! ### Perfectness -/

/-- **The multiplicity pairing represents every linear functional on `G₀^gr(mod A)`** by exactly
one projective class. -/
theorem gradedProjectiveSimplePairing_bijective :
    Function.Bijective (gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso) := by
  constructor
  · intro x y hxy
    refine (bP).ext_elem fun i ↦ (invert (R := ℤ)).injective ?_
    simpa only [gradedProjectiveSimplePairing_of_right] using
      DFunLike.congr_fun hxy (LaurentK0.of.{uA} _ (S i))
  · classical
    intro f
    refine ⟨∑ i, invert (f (LaurentK0.of.{uA} _ (S i))) • (bP) i, (bS).ext fun j ↦ ?_⟩
    rw [gradedIdempotentHeadBasisOfPrimitive_apply, gradedProjectiveSimplePairing_of_right]
    simp [-gradedIdempotentProjectiveBasisOfPrimitive_apply, Finsupp.single_apply,
      involutive_invert (R := ℤ) _]

/-- **The multiplicity pairing represents every `q ↦ q⁻¹` semilinear functional on
`K₀^gr(proj A)`** by exactly one module class. -/
theorem gradedProjectiveSimplePairing_flip_bijective :
    Function.Bijective (gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso).flip := by
  constructor
  · intro x y hxy
    refine (bS).ext_elem fun i ↦ ?_
    simpa only [LinearMap.flip_apply, gradedProjectiveSimplePairing_of_left] using
      DFunLike.congr_fun hxy (LaurentK0.of.{uA} _ (P i))
  · classical
    intro f
    refine ⟨∑ i, f ((bP) i) • (bS) i, (bP).ext fun j ↦ ?_⟩
    rw [LinearMap.flip_apply, gradedIdempotentProjectiveBasisOfPrimitive_apply,
      gradedProjectiveSimplePairing_of_left]
    simp [-gradedIdempotentHeadBasisOfPrimitive_apply, Finsupp.single_apply]

/-- Both radicals of the graded multiplicity pairing vanish. -/
theorem gradedProjectiveSimplePairing_nondegenerate :
    (gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso).Nondegenerate :=
  ⟨LinearMap.separatingLeft_iff_ker_eq_bot.2 <| LinearMap.ker_eq_bot_of_injective
      (gradedProjectiveSimplePairing_bijective hneg he he₀ hprim hnoniso).injective,
    LinearMap.separatingRight_iff_flip_ker_eq_bot.2 <| LinearMap.ker_eq_bot_of_injective
      (gradedProjectiveSimplePairing_flip_bijective hneg he he₀ hprim hnoniso).injective⟩

/-! ### The graded Cartan matrix -/

/-- **Graded Cartan-matrix entries are graded multiplicities**: the `(i, j)` entry of the graded
Cartan matrix in the bases `[A eᵢ]` and `[Sᵢ]` pairs `[A eᵢ]` with the image of `[A eⱼ]` under
the graded Cartan map, so it is `[A eⱼ : Sᵢ]_q`. -/
theorem gradedCartanMatrix_apply_eq_gradedProjectiveSimplePairing (i j : I) :
    gradedCartanMatrix 𝒜 (bP) (bS) i j =
      gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso (LaurentK0.of.{uA} _ (P i))
        (gradedCartanMap 𝒜 (LaurentK0.of.{uA} _ (P j))) := by
  rw [gradedCartanMatrix_apply, gradedIdempotentProjectiveBasisOfPrimitive_apply,
    gradedProjectiveSimplePairing_of_left]

/-! ### Comparison with the q-Euler form -/

section ExtEuler

variable [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]

/-- **The q-Euler form against `[A eᵢ]` is `dim_k End_A(Sᵢ)` times the graded multiplicity.**
This is the graded form of `dim_k Hom_A(Pᵢ, M) = dim_k End_A(Sᵢ) · [M : Sᵢ]`. -/
theorem gradedProjectiveExtEuler_of_left_eq_mul_gradedProjectiveSimplePairing (i : I)
    (y : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
    gradedProjectiveExtEuler 𝒜 (LaurentK0.of.{uA} _ (P i)) y =
      C (Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 (he₀ i))) : ℤ) *
        gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso (LaurentK0.of.{uA} _ (P i)) y := by
  rw [gradedProjectiveExtEuler_ofIdeal_span_singleton (he.idem i) (he₀ i),
    gradedIdempotentCoordinate_eq_mul_gradedIdempotentHeadBasisOfPrimitive_repr hneg he he₀ hprim
      hnoniso, gradedProjectiveSimplePairing_of_left]

/-- **The q-Euler form is the multiplicity pairing exactly when the simples are split**:
`χ_q(x, y) = ⟨x, y⟩` for all projective classes `x` and module classes `y` if and only if every
`End_A(Sᵢ)` is one-dimensional. -/
theorem gradedProjectiveExtEuler_eq_gradedProjectiveSimplePairing_iff :
    gradedProjectiveExtEuler 𝒜 = gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso ↔
      ∀ i, Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 (he₀ i))) = 1 := by
  classical
  refine ⟨fun h i ↦ ?_, fun hend ↦ (bP).ext fun i ↦ LinearMap.ext fun y ↦ ?_⟩
  · -- Pair `[A eᵢ]` with `[Sᵢ]`: the q-Euler form gives `dim_k End_A(Sᵢ)`, the pairing gives `1`.
    have hi := LinearMap.congr_fun₂ h (LaurentK0.of.{uA} _ (P i)) (LaurentK0.of.{uA} _ (S i))
    rw [gradedProjectiveExtEuler_of_left_eq_mul_gradedProjectiveSimplePairing hneg he he₀ hprim
      hnoniso, gradedProjectiveSimplePairing_basis] at hi
    simpa using congrArg (laurentEval (1 : ℤˣ)) hi
  · rw [gradedIdempotentProjectiveBasisOfPrimitive_apply,
      gradedProjectiveExtEuler_of_left_eq_mul_gradedProjectiveSimplePairing hneg he he₀ hprim
        hnoniso i y, hend i, Nat.cast_one, map_one, one_mul]

end ExtEuler

/-! ### Forgetting the grading -/

include hneg in
/-- **At `q = 1`, the graded multiplicity pairing is the ungraded multiplicity pairing** of the
underlying classes, in the projectives `A eᵢ` and the underlying heads `Sᵢ`. -/
theorem laurentEval_one_gradedProjectiveSimplePairing
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))
    (y : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
    letI : IsArtinianRing A := IsArtinianRing.of_finite k A
    letI : ∀ i, IsSimpleModule A (FGModuleCat.of A (gradedPositiveMulQuotient 𝒜 (he₀ i))) :=
      fun i ↦ isSimpleModule_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)
    laurentEval (1 : ℤˣ) (gradedProjectiveSimplePairing hneg he he₀ hprim hnoniso x y) =
      projectiveSimplePairing (fun i ↦ (⟨ModuleCat.of A (Ideal.span {e i}),
          finiteProjectiveModules_iff.2 ⟨inferInstance, (he.idem i).projective_span_singleton⟩⟩ :
            (finiteProjectiveModules A).FullSubcategory))
        (fun i ↦ FGModuleCat.of A (gradedPositiveMulQuotient 𝒜 (he₀ i)))
        (fun i ↦ (hprim i).isIndecomposableModule) hnoniso
        (isExhaustiveIndecomposableProjectiveFamily_span_singleton he hprim)
        (hnoniso.mono fun i j ↦
          isEmpty_linearEquiv_gradedPositiveMulQuotient hneg (hprim i) (he₀ i) (hprim j) (he₀ j))
        (isExhaustiveSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀
          hprim)
        (gradedFiniteProjectiveModulesForgetK0 𝒜 (LaurentSpecialization.mk 1 x))
        (gradedFiniteModulesForgetK0 𝒜 (LaurentSpecialization.mk 1 y)) := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  let _ : ∀ i, IsSimpleModule A (FGModuleCat.of A (gradedPositiveMulQuotient 𝒜 (he₀ i))) :=
    fun i ↦ isSimpleModule_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)
  -- Forgetting the grading carries the specialized graded coordinates to the ordinary ones.
  have hx := Module.Basis.repr_map_eq_of_map_basis _ _ _
    (gradedFiniteProjectiveModulesForgetK0_basis_gradedIdempotentProjectiveBasisOfPrimitive he he₀
      hprim hnoniso)
    (LaurentSpecialization.mk 1 x)
  have hy (i : I) := DFunLike.congr_fun (Module.Basis.repr_map_eq_of_map_basis _ _ _
    (gradedFiniteModulesForgetK0_basis_gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim
      hnoniso)
    (LaurentSpecialization.mk 1 y)) i
  simp only [simpleClassBasis_repr_apply, LaurentSpecialization.basis_repr_mk_apply] at hy
  rw [projectiveSimplePairing_apply, hx, gradedProjectiveSimplePairing_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hy, LaurentSpecialization.basis_repr_mk_apply, map_mul, laurentEval_invert, inv_one]

end TauCeti
