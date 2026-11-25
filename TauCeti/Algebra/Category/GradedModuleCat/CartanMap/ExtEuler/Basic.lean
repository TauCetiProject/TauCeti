/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.SimpleBasis
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Sesquilinear

/-!
# The q-Euler form between graded projectives and finite graded modules

Let `A` be a finite-dimensional algebra over a field `k`, graded by `𝒜 : ℤ → Submodule k A`. A
finitely generated graded projective `P` has no higher Ext, and its graded maps into the shifts
`M{j}` of a finite graded module `M` vanish for all but finitely many `j`. Hence every such pair
is graded Euler-admissible, and the q-Euler characteristic descends to a form

```text
χ_q : K₀^gr(proj A) × G₀^gr(mod A) ⟶ ℤ[q,q⁻¹],
```

q-antilinear in the first variable and q-linear in the second. It is defined on the same
Laurent Grothendieck groups as the graded Cartan map `TauCeti.gradedCartanMap`.

For an idempotent `f` of degree zero, a graded map `Af ⟶ M` is determined by the image of `f`,
which can be any vector of `f • M₀`. Therefore
`χ_q(Af, M) = ∑ⱼ q⁻ʲ dim_k(f • M₋ⱼ) = ∑ₚ dim_k(f • Mₚ) qᵖ`: pairing against `[Af]` is the
idempotent coordinate `TauCeti.gradedIdempotentCoordinate`. In particular, if the degree-zero
idempotents `eᵢ` cut out graded simples `Sᵢ` with `gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`, then
`χ_q([A eᵢ], [Sⱼ])` is `gdim(eᵢ • Sᵢ)` on the diagonal and `0` off it. When moreover every
`gdim(eᵢ • Sᵢ) = 1`, the classes `[A eᵢ]` pair with `G₀^gr(mod A)` as the coordinate
functionals of the graded simple-class basis. This is the graded form of the duality between
projective covers and simples.

## Main definitions

* `TauCeti.gradedProjectiveExtEulerTarget`: the q-Euler pairing `K₀^gr(proj A) → ℤ[q,q⁻¹]` against
  any fixed finite-dimensional graded module `N`, defined without assuming `A` is
  finite-dimensional over `k`.
* `TauCeti.gradedProjectiveExtEuler`: the q-Euler form `K₀^gr(proj A) × G₀^gr(mod A) → ℤ[q,q⁻¹]`.

## Main results

* `TauCeti.isGradedEulerAdmissible_gradedFiniteProjectiveModules_of_finite` and
  `TauCeti.isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules`: finite
  graded projectives and finite-dimensional (in particular, finite when `A` is finite-dimensional)
  graded modules form graded Euler-admissible pairs.
* `TauCeti.gradedExtEuler_ofIdeal_span_singleton`: `χ_q(Af, M) = ∑ₚ dim_k(f • Mₚ) qᵖ`.
* `TauCeti.gradedProjectiveExtEuler_ofIdeal_span_singleton`: pairing against `[Af]` is the
  idempotent coordinate of `f`.
* `TauCeti.gradedExtEulerSesquilinear_gradedCartanMap`: when every pair of finite graded modules is
  graded Euler-admissible, `χ_q(c x, y) = χ_q(x, y)` for the graded Cartan map `c`.
* `TauCeti.gradedProjectiveExtEuler_basis`: `χ_q([A eᵢ], [Sⱼ])` is `gdim(eᵢ • Sᵢ)` if `i = j` and
  `0` otherwise.
* `TauCeti.gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_mul_repr`: pairing against
  `[A eᵢ]` is `gdim(eᵢ • Sᵢ)` times the `i`th coordinate in the graded simple-class basis.
* `TauCeti.gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_repr`: when every
  `gdim(eᵢ • Sᵢ) = 1`, pairing against `[A eᵢ]` is the `i`th simple-class coordinate.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2, for the q-Euler form and its
  q-antilinear/q-linear convention.
* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the ungraded pairing of projective covers
  with simple modules.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded free and
  projective modules.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe w uk uA uI v uJ

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

omit [GradedAlgebra 𝒜] in
/-- The q-Euler characteristic of a finite direct sum of projective graded modules is the sum
of the characteristics of the summands, for any grading-shift autoequivalence and admissible
pairs. -/
theorem gradedExtEuler_directSumObj [HasExt.{w} (GradedModuleCat.{max uJ v} 𝒜)]
    {J : Type uJ} [Fintype J] (e : GradedModuleCat.{max uJ v} 𝒜 ≌ GradedModuleCat.{max uJ v} 𝒜)
    (M : J → GradedModuleCat.{max uJ v} 𝒜) [∀ j, Projective (M j)]
    (Y : GradedModuleCat.{max uJ v} 𝒜)
    (h : IsGradedEulerAdmissible.{w} k e (GradedModuleCat.directSumObj M) Y)
    (hj : ∀ j, IsGradedEulerAdmissible.{w} k e (M j) Y) :
    gradedExtEuler k e h = ∑ j, gradedExtEuler k e (hj j) := by
  classical
  rw [gradedExtEuler_projective]
  ext p
  rw [coeff_targetShiftGradedDimension]
  let _ (j : J) : Module.Finite k (M j ⟶ (e ^ (-p)).functor.obj Y) :=
    (((hj j).internallyFinite.finiteLaurentSupport 0).of_equiv
      fun _ ↦ CategoryTheory.Abelian.Ext.linearEquiv₀ (R := k)).finiteDimensional (-p)
  rw [GradedModuleCat.finrank_hom_directSumObj, Nat.cast_sum,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [gradedExtEuler_projective, coeff_targetShiftGradedDimension]

/-! ### Evaluation against `Af` -/

/-- **The q-Euler characteristic against `Af` is the idempotent graded dimension**: for an
idempotent `f` of degree zero and a finite-dimensional graded module `M`,
`χ_q(Af, M) = ∑ₚ dim_k(f • Mₚ) qᵖ`. This holds for every admissibility witness and every
`HasExt` instance. -/
@[simp]
theorem gradedExtEuler_ofIdeal_span_singleton [HasExt.{w} (GradedModuleCat.{uA} 𝒜)] {f : A}
    (hf : IsIdempotentElem f) (hf₀ : f ∈ 𝒜 0) (hI : (Ideal.span {f} : Ideal A).IsHomogeneous 𝒜)
    (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M]
    (h : IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜)
      (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {f}) hI) M) :
    gradedExtEuler k (GradedModuleCat.shift 𝒜) h = M.smulGradedDimension f := by
  have := GradedModuleCat.projective_ofIdeal_span_singleton hf hI
  rw [gradedExtEuler_projective]
  ext p
  rw [coeff_targetShiftGradedDimension, GradedModuleCat.coeff_smulGradedDimension,
    (GradedModuleCat.homShiftPowEquiv 𝒜 _ M (-p)).finrank_eq,
    (GradedModuleCat.ofIdealSpanSingletonHomEquiv hf hf₀ hI _).finrank_eq]
  rw [InternalGrading.shift_piece, neg_neg, zero_add]

/-! ### Pairing with a finite-dimensional target -/

/-- Any finite graded projective and any finite-dimensional graded module form a graded
Euler-admissible pair, without assuming the algebra is finite-dimensional over `k`. -/
theorem isGradedEulerAdmissible_gradedFiniteProjectiveModules_of_finite
    [HasExt.{w} (GradedModuleCat.{uA} 𝒜)]
    {P : GradedModuleCat.{uA} 𝒜} (hP : gradedFiniteProjectiveModules 𝒜 P)
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N] :
    IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜) P N := by
  let _ : Module.Finite A P := (gradedFiniteProjectiveModules_iff.mp hP).left
  let _ : Module.Projective A P := (gradedFiniteProjectiveModules_iff.mp hP).right
  exact isGradedEulerAdmissible_of_projective k _ P N
    ((GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj P N).of_equiv fun j ↦
      (GradedModuleCat.homShiftPowEquiv 𝒜 P N j).symm)

private def gradedProjectiveExtEulerTargetInvariant
    [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N] :
    GradedExactStructure.ShiftInvariant (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (laurentTAut ℤ (LaurentPolynomial ℤ)) where
  obj P := invert (gradedExtEuler k (GradedModuleCat.shift 𝒜)
    (isGradedEulerAdmissible_gradedFiniteProjectiveModules_of_finite P.property N))
  map_conflation {S} hS := by
    have hS' : (S.map (gradedFiniteProjectiveModules 𝒜).ι).ShortExact :=
      (gradedFiniteProjectiveModulesExactStructure_conflation_iff S).mp hS
    rw [← map_add, ← gradedExtEuler_shortExact₁ hS' N
      (isGradedEulerAdmissible_gradedFiniteProjectiveModules_of_finite S.X₁.property N)
      (isGradedEulerAdmissible_gradedFiniteProjectiveModules_of_finite S.X₃.property N)]
  map_shift P := by
    have hiso := gradedExtEuler_of_iso k
      (isGradedEulerAdmissible_gradedFiniteProjectiveModules_of_finite
        ((gradedFiniteProjectiveModulesExactStructure 𝒜).shift.functor.obj P).property N)
      (isGradedEulerAdmissible_gradedFiniteProjectiveModules_of_finite P.property N).shiftSource
      (gradedFiniteProjectiveModulesExactStructureShiftFunctorCompιIso.app P) (Iso.refl N)
    rw [hiso, gradedExtEuler_shiftSource, map_mul, invert_T, neg_neg, laurentTAut_apply,
      smul_eq_mul]

/-- **The q-Euler pairing against a fixed finite-dimensional graded module**,
`K₀^gr(proj A) → ℤ[q,q⁻¹]`. It is `q`-antilinear in the projective class and sends `[P]` to
`χ_q(P, N)`, with no finite-dimensionality assumption on `A`. -/
def gradedProjectiveExtEulerTarget [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N] :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      →ₛₗ[(LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom] LaurentPolynomial ℤ where
  toFun x := invert
    (LaurentK0.lift.{uA} _ (gradedProjectiveExtEulerTargetInvariant N) x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' r x := by
    rw [map_smul, smul_eq_mul, map_mul]
    rfl

/-- Evaluating `gradedProjectiveExtEulerTarget N` on `[P]` gives `χ_q(P, N)`. -/
@[simp]
theorem gradedProjectiveExtEulerTarget_of [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N]
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedProjectiveExtEulerTarget N (LaurentK0.of.{uA} _ P) =
      gradedExtEuler k (GradedModuleCat.shift 𝒜)
        (isGradedEulerAdmissible_gradedFiniteProjectiveModules_of_finite P.property N) := by
  simp only [gradedProjectiveExtEulerTarget, LinearMap.coe_mk, AddHom.coe_mk,
    LaurentK0.lift_of, gradedProjectiveExtEulerTargetInvariant]
  exact involutive_invert (R := ℤ) _

/-- Evaluating `gradedProjectiveExtEulerTarget N` on `[Af]` gives `gdim(f • N)`. -/
@[simp]
theorem gradedProjectiveExtEulerTarget_ofIdeal_span_singleton
    [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)] {f : A}
    (hf : IsIdempotentElem f) (hf₀ : f ∈ 𝒜 0) (hI : (Ideal.span {f} : Ideal A).IsHomogeneous 𝒜)
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N] :
    gradedProjectiveExtEulerTarget N (LaurentK0.of.{uA} _
        ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {f}) hI,
          gradedFiniteProjectiveModules_ofIdeal_span_singleton hf hI⟩) =
      N.smulGradedDimension f := by
  rw [gradedProjectiveExtEulerTarget_of, gradedExtEuler_ofIdeal_span_singleton hf hf₀ hI N]

/-! ### Graded Euler-admissibility of projective pairs -/

variable [Module.Finite k A]

/-- **Finite graded projectives and finite graded modules form graded Euler-admissible pairs**:
higher Ext out of a projective vanishes, and its graded Hom spaces into the shifts of a finite
graded module have finite Laurent support. -/
theorem isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules
    [HasExt.{w} (GradedModuleCat.{uA} 𝒜)] :
    IsGradedEulerAdmissibleOn.{w} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteProjectiveModules 𝒜) (gradedFiniteModules 𝒜) where
  isGradedEulerAdmissible P M hP hM := by
    let _ : Module.Finite A M := gradedFiniteModules_iff.mp hM
    have : Module.Finite k M := Module.Finite.trans A M
    exact isGradedEulerAdmissible_gradedFiniteProjectiveModules_of_finite hP M

/-! ### The q-Euler form on graded Grothendieck groups -/

variable [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]

variable (𝒜) in
/-- **The q-Euler form between graded projectives and finite graded modules**,
`K₀^gr(proj A) × G₀^gr(mod A) → ℤ[q,q⁻¹]`. It is q-antilinear in the first variable and q-linear
in the second, and its value on two classes is the graded Ext-Euler characteristic. -/
def gradedProjectiveExtEuler :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      →ₛₗ[(LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
      LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
        LaurentPolynomial ℤ :=
  gradedExtEulerSesquilinear _ _ _ _
    isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules

/-- The projective/module q-Euler form is the generic graded Ext-Euler sesquilinear form for the
two induced graded abelian exact subcategories. -/
theorem gradedProjectiveExtEuler_def :
    gradedProjectiveExtEuler 𝒜 =
      gradedExtEulerSesquilinear.{uA} _ _ _ _
        isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules :=
  gradedProjectiveExtEuler.eq_def 𝒜

/-- The q-Euler form evaluates on two classes as the graded Ext-Euler characteristic. -/
@[simp]
theorem gradedProjectiveExtEuler_of_of (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    gradedProjectiveExtEuler 𝒜 (LaurentK0.of.{uA} _ P) (LaurentK0.of.{uA} _ M) =
      gradedExtEuler k (GradedModuleCat.shift 𝒜)
        ((isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules
          (𝒜 := 𝒜)).isGradedEulerAdmissible
          P.property M.property) :=
  gradedExtEulerSesquilinear_of_of _ _ _ _ _ P M

/-- Over a finite-dimensional algebra, pairing a projective class `x` against `[M]` in `G₀^gr`
coincides with `gradedProjectiveExtEulerTarget M.obj x`. -/
theorem gradedProjectiveExtEuler_of_right
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))
    (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    gradedProjectiveExtEuler 𝒜 x (LaurentK0.of.{uA} _ M) =
      gradedProjectiveExtEulerTarget M.obj x := by
  have hinv (r : LaurentPolynomial ℤ) :
      invert ((LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom r) = r :=
    involutive_invert (R := ℤ) r
  let φ₁ : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
    { toFun := fun y ↦ invert (gradedProjectiveExtEuler 𝒜 y (LaurentK0.of.{uA} _ M))
      map_add' := fun y z ↦ by rw [map_add, LinearMap.add_apply, map_add]
      map_smul' := fun r y ↦ by
        rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, hinv r,
          RingHom.id_apply, smul_eq_mul] }
  let φ₂ : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
    { toFun := fun y ↦ invert (gradedProjectiveExtEulerTarget M.obj y)
      map_add' := fun y z ↦ by rw [map_add, map_add]
      map_smul' := fun r y ↦ by
        rw [map_smulₛₗ, smul_eq_mul, map_mul, hinv r, RingHom.id_apply, smul_eq_mul] }
  have hlin : φ₁ = φ₂ := LaurentK0.hom_ext _ fun P ↦ by
    dsimp only [φ₁, φ₂, LinearMap.coe_mk, AddHom.coe_mk]
    rw [gradedProjectiveExtEuler_of_of, gradedProjectiveExtEulerTarget_of]
  exact (LaurentPolynomial.invert (R := ℤ)).injective (LinearMap.congr_fun hlin x)

/-- **Pairing against `[Af]` is the idempotent coordinate of `f`**: for an idempotent `f` of degree
zero, `χ_q([Af], -)` is the `ℤ[q,q⁻¹]`-linear map sending `[M]` to `∑ₚ dim_k(f • Mₚ) qᵖ`. -/
@[simp]
theorem gradedProjectiveExtEuler_ofIdeal_span_singleton {f : A} (hf : IsIdempotentElem f)
    (hf₀ : f ∈ 𝒜 0) (hI : (Ideal.span {f} : Ideal A).IsHomogeneous 𝒜) :
    gradedProjectiveExtEuler 𝒜 (LaurentK0.of.{uA} _
        ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {f}) hI,
          gradedFiniteProjectiveModules_ofIdeal_span_singleton hf hI⟩) =
      gradedIdempotentCoordinate hf hf₀ := by
  refine LaurentK0.hom_ext _ fun M ↦ ?_
  rw [gradedProjectiveExtEuler_of_of, gradedIdempotentCoordinate_of]
  exact gradedExtEuler_ofIdeal_span_singleton hf hf₀ hI M.obj _

/-- **The q-Euler form is compatible with the graded Cartan map**: if every pair of finite graded
modules is graded Euler-admissible, then pairing the image of a projective class `x` under the
graded Cartan map against `y` gives the projective/module q-Euler form `χ_q(x, y)`. -/
@[simp]
theorem gradedExtEulerSesquilinear_gradedCartanMap
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))
    (y : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
    gradedExtEulerSesquilinear isExtensionClosed_gradedFiniteModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift
        gradedFiniteModules_gradedAbelian_shift h (gradedCartanMap 𝒜 x) y =
      gradedProjectiveExtEuler 𝒜 x y := by
  have hcomp := gradedExtEulerSesquilinear_unique (k := k)
    isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    gradedFiniteProjectiveModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift
    isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules
    ((gradedExtEulerSesquilinear isExtensionClosed_gradedFiniteModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift
        gradedFiniteModules_gradedAbelian_shift h).comp (gradedCartanMap 𝒜))
    fun X Y ↦ (congrArg (fun z ↦ gradedExtEulerSesquilinear
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift
        gradedFiniteModules_gradedAbelian_shift h z (LaurentK0.of _ Y))
      (gradedCartanMap_of X.property)).trans
      (gradedExtEulerSesquilinear_of_of _ _ _ _ h _ Y)
  rw [gradedProjectiveExtEuler_def, ← hcomp]
  -- `LinearMap.comp_apply` does not fire here: the composite is typed on the full-subcategory
  -- structure that `gradedFiniteModulesExactStructure 𝒜` unfolds to. It unfolds by `rfl`.
  rfl

/-! ### Duality with graded simples -/

section Simple

variable {I : Type uI} (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)

include he₀ hne in
/-- **Diagonal pairing under the q-Euler form**: if the finite graded modules `Sⱼ` and the
degree-zero idempotents `eᵢ` satisfy `gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`, then
`χ_q([A eᵢ], [Sⱼ])` is `gdim(eᵢ • Sᵢ)` for `i = j` and `0` otherwise. -/
@[simp]
theorem gradedProjectiveExtEuler_basis [DecidableEq I] (i j : I) :
    gradedProjectiveExtEuler 𝒜 (LaurentK0.of.{uA} _
        ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
          gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)
        (LaurentK0.of.{uA} _ (S j)) =
      if i = j then (S i).obj.smulGradedDimension (e i) else 0 := by
  rw [gradedProjectiveExtEuler_ofIdeal_span_singleton (he i) (he₀ i) (hI i),
    gradedIdempotentCoordinate_of]
  split_ifs with hij
  · rw [hij]
  · exact hne hij

/-- **Pairing against `[A eᵢ]` is a multiple of the `i`th simple-class coordinate**: for an
exhaustive family of graded simples `Sᵢ` cut out by degree-zero idempotents `eᵢ` with nonzero
diagonal graded dimensions, `χ_q([A eᵢ], x)` is `gdim(eᵢ • Sᵢ)` times the `i`th coordinate of `x`
in the graded simple-class basis of `G₀^gr(mod A)`. -/
theorem gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_mul_repr
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) (hS : IsExhaustiveGradedSimpleFamily S)
    (i : I) (x : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
    gradedProjectiveExtEuler 𝒜 (LaurentK0.of.{uA} _
        ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
          gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩) x =
      (S i).obj.smulGradedDimension (e i) *
        (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS).repr x i := by
  rw [gradedProjectiveExtEuler_ofIdeal_span_singleton (he i) (he₀ i) (hI i),
    gradedIdempotentCoordinate_eq_mul_gradedSimpleClassBasisOfNeZero_repr]

variable (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)

/-- **Pairing against `[A eᵢ]` is the `i`th simple-class coordinate**: for an exhaustive family of
graded simples `Sᵢ` cut out by degree-zero idempotents `eᵢ` with `gdim(eᵢ • Sⱼ) = δᵢⱼ`, the form
`χ_q([A eᵢ], -)` is the `i`th coordinate functional of the graded simple-class basis of
`G₀^gr(mod A)`. -/
@[simp]
theorem gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_repr
    (hS : IsExhaustiveGradedSimpleFamily S) (i : I)
    (x : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
    gradedProjectiveExtEuler 𝒜 (LaurentK0.of.{uA} _
        ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
          gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩) x =
      (gradedSimpleClassBasis S he he₀ hne hself hS).repr x i := by
  rw [gradedProjectiveExtEuler_ofIdeal_span_singleton (he i) (he₀ i) (hI i),
    gradedSimpleClassBasis_repr_apply]

end Simple

end TauCeti
