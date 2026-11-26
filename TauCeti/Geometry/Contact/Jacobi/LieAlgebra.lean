/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.VectorField
public import TauCeti.Geometry.Manifold.Distribution.Preserving.LieSubalgebra

/-!
# The Jacobi Lie algebra of a contact form

Let `α` be a contact form on a finite-dimensional manifold `M`, with Reeb vector field `R_α`, and
write `X_f` for the contact Hamiltonian vector field of a function `f`, fixed by `α(X_f) = f` and
`ι_(X_f) dα = (R_α f) α - df`. The Jacobi bracket
`{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)` (`TauCeti.SmoothForm.jacobiBracket`) of two smooth
functions is smooth (`TauCeti.SmoothForm.IsContactForm.contMDiff_jacobiBracket`), bilinear,
antisymmetric and satisfies the Jacobi identity
(`TauCeti.SmoothForm.IsContactForm.jacobiBracket_jacobi`). So it makes the smooth functions a real
Lie algebra, the **Jacobi Lie algebra** `TauCeti.SmoothForm.JacobiLieAlgebra α hα` of `α`.

Since `X_({f, g}_α) = [X_f, X_g]`
(`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_jacobiBracket`), the map
`f ↦ X_f` is a Lie algebra homomorphism into the smooth vector fields with their Lie bracket
(`TauCeti.SmoothForm.contactHamiltonianLieHom`). Unlike the map `f ↦ -X_f` of a symplectic form,
whose kernel contains the constants, it is injective, because `α(X_f) = f`
(`TauCeti.SmoothForm.contactHamiltonianLieHom_injective`); the constant `1` goes to the Reeb vector
field. Its range is the Lie algebra of contact vector fields, the smooth vector fields preserving
the contact structure `ker α` (`TauCeti.preservesDistributionLieSubalgebra`), since every contact
vector field `X` is the contact Hamiltonian vector field of `α(X)`
(`TauCeti.SmoothForm.IsContactForm.preservesDistribution_kerDistribution_iff_eq`). Hence

`f ↦ X_f : (C^∞(M), {·, ·}_α) ≃ {contact vector fields of ker α}`

is an isomorphism of Lie algebras (`TauCeti.SmoothForm.contactHamiltonianLieEquiv`), whose inverse
is contraction with `α`, `X ↦ α(X)`
(`TauCeti.SmoothForm.jacobiLieAlgebraEquiv_contactHamiltonianLieEquiv_symm_apply`).

The Jacobi Lie algebra is a type synonym of `C^∞⟮I, M; ℝ⟯` indexed by `α` and by the proof that `α`
is a contact form, as for the Poisson Lie algebra `TauCeti.SmoothTwoForm.PoissonLieAlgebra` of a
symplectic form. It carries only the Lie bracket, not the pointwise product of functions, and is
identified with the smooth functions by `TauCeti.SmoothForm.jacobiLieAlgebraEquiv`.

## Main definitions

* `TauCeti.SmoothForm.JacobiLieAlgebra α hα`: the smooth functions with the Jacobi bracket.
* `TauCeti.SmoothForm.contactHamiltonianLieHom α hα`: the Lie algebra homomorphism `f ↦ X_f`.
* `TauCeti.SmoothForm.contactHamiltonianLieEquiv α hα`: the Lie algebra isomorphism `f ↦ X_f` onto
  the contact vector fields.

## Main results

* `TauCeti.SmoothForm.contactHamiltonianLieHom_injective`: `f ↦ X_f` is injective.
* `TauCeti.SmoothForm.range_contactHamiltonianLieHom`: its range is the Lie algebra of contact
  vector fields.

## References

* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, American Mathematical Society, 1997, Section 43.15 (the Lie algebra of contact
  vector fields and the Lagrange bracket of functions).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Theorem 2.3.1 and Section 2.3 (contact vector fields and contact Hamiltonians).
* A. Lichnerowicz, *Les variétés de Jacobi et leurs algèbres de Lie associées*, J. Math. Pures
  Appl. 57 (1978), 453–488.
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1}

/-! ### The Jacobi Lie algebra -/

variable (α) in
/-- The **Jacobi Lie algebra** of a contact form `α`: the smooth real functions on `M` with the
Jacobi bracket `⁅f, g⁆ = {f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)` as Lie bracket. It is a
type synonym of `C^∞⟮I, M; ℝ⟯`, indexed by `α` and by the proof `hα` that `α` is a contact form,
and is identified with the smooth functions by `TauCeti.SmoothForm.jacobiLieAlgebraEquiv`. Only
the Lie algebra structure is put on it, not the pointwise product. -/
def JacobiLieAlgebra (_hα : α.IsContactForm) : Type _ := C^∞⟮I, M; ℝ⟯

namespace JacobiLieAlgebra

variable {hα : α.IsContactForm}

instance instAddCommGroup : AddCommGroup (α.JacobiLieAlgebra hα) :=
  inferInstanceAs (AddCommGroup C^∞⟮I, M; ℝ⟯)

instance instModule : Module ℝ (α.JacobiLieAlgebra hα) :=
  inferInstanceAs (Module ℝ C^∞⟮I, M; ℝ⟯)

end JacobiLieAlgebra

variable (α) in
/-- The identification of the Jacobi Lie algebra of `α` with the smooth functions. -/
def jacobiLieAlgebraEquiv (hα : α.IsContactForm) : α.JacobiLieAlgebra hα ≃ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  LinearEquiv.refl _ _

namespace JacobiLieAlgebra

variable {hα : α.IsContactForm}

omit [FiniteDimensional ℝ E] in
/-- Two elements of the Jacobi Lie algebra are equal when they agree as functions. -/
@[ext]
theorem ext {f g : α.JacobiLieAlgebra hα}
    (h : ∀ x, α.jacobiLieAlgebraEquiv hα f x = α.jacobiLieAlgebraEquiv hα g x) : f = g :=
  (α.jacobiLieAlgebraEquiv hα).injective <| ContMDiffMap.ext h

omit [FiniteDimensional ℝ E] in
/-- An element of the Jacobi Lie algebra is a `C²` function. -/
private theorem contMDiff_two (f : α.JacobiLieAlgebra hα) :
    ContMDiff I 𝓘(ℝ) 2 (α.jacobiLieAlgebraEquiv hα f) :=
  (α.jacobiLieAlgebraEquiv hα f).contMDiff.of_le (by simp)

omit [FiniteDimensional ℝ E] in
/-- An element of the Jacobi Lie algebra is differentiable at every point. -/
private theorem mdifferentiableAt (f : α.JacobiLieAlgebra hα) (x : M) :
    MDifferentiableAt I 𝓘(ℝ) (α.jacobiLieAlgebraEquiv hα f) x :=
  (α.jacobiLieAlgebraEquiv hα f).contMDiff.mdifferentiableAt (by simp)

/-- The Jacobi bracket of the Jacobi Lie algebra. -/
instance instBracket : Bracket (α.JacobiLieAlgebra hα) (α.JacobiLieAlgebra hα) where
  bracket f g := (α.jacobiLieAlgebraEquiv hα).symm
    ⟨α.jacobiBracket (α.jacobiLieAlgebraEquiv hα f) (α.jacobiLieAlgebraEquiv hα g),
      hα.contMDiff_jacobiBracket le_rfl
        ((α.jacobiLieAlgebraEquiv hα f).contMDiff.of_le (by simp))
        ((α.jacobiLieAlgebraEquiv hα g).contMDiff.of_le (by simp))⟩

end JacobiLieAlgebra

/-- The bracket of the Jacobi Lie algebra is the Jacobi bracket
`{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)`. -/
@[simp]
theorem jacobiLieAlgebraEquiv_lie_apply {hα : α.IsContactForm} (f g : α.JacobiLieAlgebra hα)
    (x : M) :
    α.jacobiLieAlgebraEquiv hα ⁅f, g⁆ x =
      α.jacobiBracket (α.jacobiLieAlgebraEquiv hα f) (α.jacobiLieAlgebraEquiv hα g) x :=
  (rfl)

/-- The bracket of the Jacobi Lie algebra is the Jacobi bracket, as an equality of functions. -/
theorem coe_jacobiLieAlgebraEquiv_lie {hα : α.IsContactForm} (f g : α.JacobiLieAlgebra hα) :
    ⇑(α.jacobiLieAlgebraEquiv hα ⁅f, g⁆) =
      α.jacobiBracket (α.jacobiLieAlgebraEquiv hα f) (α.jacobiLieAlgebraEquiv hα g) :=
  (rfl)

namespace JacobiLieAlgebra

variable {hα : α.IsContactForm}

/-- The Jacobi bracket makes the smooth functions a Lie ring: bilinearity and antisymmetry hold
pointwise, and the Leibniz rule is the Jacobi identity
(`TauCeti.SmoothForm.IsContactForm.jacobiBracket_jacobi`). -/
instance instLieRing : LieRing (α.JacobiLieAlgebra hα) where
  add_lie f g k := by
    ext x
    simp only [jacobiLieAlgebraEquiv_lie_apply, map_add, ContMDiffMap.coe_add, Pi.add_apply,
      jacobiBracket_add_left (mdifferentiableAt f x) (mdifferentiableAt g x)]
  lie_add f g k := by
    ext x
    simp only [jacobiLieAlgebraEquiv_lie_apply, map_add, ContMDiffMap.coe_add, Pi.add_apply,
      jacobiBracket_add_right (mdifferentiableAt g x) (mdifferentiableAt k x)]
  lie_self f := by
    ext x
    simp only [jacobiLieAlgebraEquiv_lie_apply, jacobiBracket_self, map_zero,
      ContMDiffMap.coe_zero, Pi.zero_apply]
  leibniz_lie f g k := by
    ext x
    simp only [jacobiLieAlgebraEquiv_lie_apply, coe_jacobiLieAlgebraEquiv_lie, map_add,
      ContMDiffMap.coe_add, Pi.add_apply]
    set F := α.jacobiLieAlgebraEquiv hα f
    set G := α.jacobiLieAlgebraEquiv hα g
    set K := α.jacobiLieAlgebraEquiv hα k
    -- Rewrite `{G, {F, K}}` as `-{G, {K, F}}` and `{{F, G}, K}` as `-{K, {F, G}}`, then apply the
    -- Jacobi identity.
    have hFK : α.jacobiBracket F K = -α.jacobiBracket K F :=
      funext fun y ↦ by rw [Pi.neg_apply, neg_jacobiBracket]
    rw [hFK, jacobiBracket_neg_right, ← neg_jacobiBracket α (α.jacobiBracket F G) K]
    linear_combination hα.jacobiBracket_jacobi (contMDiff_two f) (contMDiff_two g)
      (contMDiff_two k) x

/-- The Jacobi Lie algebra of a contact form is a real Lie algebra. -/
instance instLieAlgebra : LieAlgebra ℝ (α.JacobiLieAlgebra hα) where
  lie_smul c f g := by
    ext x
    simp only [jacobiLieAlgebraEquiv_lie_apply, map_smul, ContMDiffMap.coe_smul,
      jacobiBracket_const_smul_right, Pi.smul_apply]

end JacobiLieAlgebra

/-! ### The Lie algebra homomorphism `f ↦ X_f` -/

/-- The contact Hamiltonian vector field `X_f` of an element of the Jacobi Lie algebra, as a smooth
vector field. -/
private def contactHamiltonianSection (hα : α.IsContactForm) (f : α.JacobiLieAlgebra hα) :
    (LieAlgebroid.tangent I M).Sections :=
  (LieAlgebroid.tangent I M).sectionsEquiv.symm
    ⟨α.contactHamiltonianVectorField (α.jacobiLieAlgebraEquiv hα f),
      hα.contMDiff_contactHamiltonianVectorField le_rfl
        ((α.jacobiLieAlgebraEquiv hα f).contMDiff.of_le (by simp))⟩

/-- The value of `X_f` at a point. -/
private theorem contactHamiltonianSection_apply (hα : α.IsContactForm) (f : α.JacobiLieAlgebra hα)
    (x : M) :
    (LieAlgebroid.tangent I M).sectionsEquiv (contactHamiltonianSection hα f) x =
      α.contactHamiltonianVectorField (α.jacobiLieAlgebraEquiv hα f) x := by
  rw [contactHamiltonianSection, LinearEquiv.apply_symm_apply, ContMDiffSection.coeFn_mk]

variable (α) in
/-- **The Lie algebra homomorphism `f ↦ X_f`** from the Jacobi Lie algebra of a contact form to the
smooth vector fields with their Lie bracket, the sections of the tangent Lie algebroid. That it
preserves brackets is `X_({f, g}_α) = [X_f, X_g]`
(`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_jacobiBracket`). It is injective
(`TauCeti.SmoothForm.contactHamiltonianLieHom_injective`), with range the contact vector fields
(`TauCeti.SmoothForm.range_contactHamiltonianLieHom`). -/
def contactHamiltonianLieHom (hα : α.IsContactForm) :
    α.JacobiLieAlgebra hα →ₗ⁅ℝ⁆ (LieAlgebroid.tangent I M).Sections where
  toFun := contactHamiltonianSection hα
  map_add' f g := (LieAlgebroid.tangent I M).sectionsEquiv.injective <|
    ContMDiffSection.ext fun x ↦ by
      simp only [map_add, ContMDiffSection.coe_add, Pi.add_apply, contactHamiltonianSection_apply,
        ContMDiffMap.coe_add]
      exact contactHamiltonianVectorField_add (JacobiLieAlgebra.mdifferentiableAt f x)
        (JacobiLieAlgebra.mdifferentiableAt g x)
  map_smul' c f := (LieAlgebroid.tangent I M).sectionsEquiv.injective <|
    ContMDiffSection.ext fun x ↦ by
      rw [RingHom.id_apply, LinearMapClass.map_smul_of_tower]
      simp only [ContMDiffSection.coe_smul, Pi.smul_apply, contactHamiltonianSection_apply,
        map_smul, ContMDiffMap.coe_smul, contactHamiltonianVectorField_const_smul]
  map_lie' {f g} := (LieAlgebroid.tangent I M).sectionsEquiv.injective <|
    ContMDiffSection.ext fun x ↦ by
      simp only [LieAlgebroid.coe_tangent_sectionsEquiv_lie,
        funext (contactHamiltonianSection_apply hα _), coe_jacobiLieAlgebraEquiv_lie]
      rw [hα.contactHamiltonianVectorField_jacobiBracket (JacobiLieAlgebra.contMDiff_two f)
        (JacobiLieAlgebra.contMDiff_two g)]

/-- The vector field of `f ↦ X_f` is the contact Hamiltonian vector field. -/
@[simp]
theorem contactHamiltonianLieHom_apply (hα : α.IsContactForm) (f : α.JacobiLieAlgebra hα)
    (x : M) :
    (LieAlgebroid.tangent I M).sectionsEquiv (α.contactHamiltonianLieHom hα f) x =
      α.contactHamiltonianVectorField (α.jacobiLieAlgebraEquiv hα f) x :=
  contactHamiltonianSection_apply hα f x

/-- The contact form recovers a function from its contact Hamiltonian vector field:
`α(X_f) = f`. -/
theorem apply_contactHamiltonianLieHom (hα : α.IsContactForm) (f : α.JacobiLieAlgebra hα)
    (x : M) :
    α.val x ![(LieAlgebroid.tangent I M).sectionsEquiv (α.contactHamiltonianLieHom hα f) x] =
      α.jacobiLieAlgebraEquiv hα f x := by
  rw [contactHamiltonianLieHom_apply, hα.apply_contactHamiltonianVectorField]

/-- **`f ↦ X_f` is injective**: a function is recovered from its contact Hamiltonian vector field
by contraction with `α`. -/
theorem contactHamiltonianLieHom_injective (hα : α.IsContactForm) :
    Function.Injective (α.contactHamiltonianLieHom hα) := fun f g hfg ↦
  JacobiLieAlgebra.ext fun x ↦ by
    rw [← apply_contactHamiltonianLieHom hα f, ← apply_contactHamiltonianLieHom hα g, hfg]

/-- **Contact Hamiltonian vector fields are contact vector fields**: `X_f` preserves the contact
structure `ker α`. -/
theorem contactHamiltonianLieHom_mem_preservesDistributionLieSubalgebra (hα : α.IsContactForm)
    (f : α.JacobiLieAlgebra hα) :
    α.contactHamiltonianLieHom hα f ∈ preservesDistributionLieSubalgebra I α.kerDistribution := by
  rw [mem_preservesDistributionLieSubalgebra_iff,
    funext (contactHamiltonianLieHom_apply hα f)]
  exact (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField _).preservesDistribution
    (hα.mdifferentiable_contactHamiltonianVectorField (JacobiLieAlgebra.contMDiff_two f))

/-- **Every contact vector field is a contact Hamiltonian vector field**: a smooth vector field `X`
preserving `ker α` is `X_f` for the smooth function `f = α(X)`. -/
theorem exists_contactHamiltonianLieHom_eq (hα : α.IsContactForm)
    {X : (LieAlgebroid.tangent I M).Sections}
    (hX : X ∈ preservesDistributionLieSubalgebra I α.kerDistribution) :
    ∃ f : α.JacobiLieAlgebra hα, α.contactHamiltonianLieHom hα f = X ∧
      ∀ x, α.jacobiLieAlgebraEquiv hα f x =
        α.val x ![(LieAlgebroid.tangent I M).sectionsEquiv X x] := by
  set X' := (LieAlgebroid.tangent I M).sectionsEquiv X
  obtain ⟨g, hg⟩ : ∃ g : C^∞⟮I, M; ℝ⟯, ⇑g = fun x ↦ α.val x ![X' x] :=
    ⟨⟨_, α.contMDiff_apply_vectorField X'.contMDiff⟩, rfl⟩
  set f := (α.jacobiLieAlgebraEquiv hα).symm g
  have hf : ⇑(α.jacobiLieAlgebraEquiv hα f) = fun x ↦ α.val x ![X' x] := by
    rw [LinearEquiv.apply_symm_apply, hg]
  refine ⟨f, (LieAlgebroid.tangent I M).sectionsEquiv.injective <| ContMDiffSection.ext fun x ↦ ?_,
    fun x ↦ congrFun hf x⟩
  rw [contactHamiltonianLieHom_apply, hf,
    ← (hα.preservesDistribution_kerDistribution_iff_eq X'.mdifferentiable).1
      ((mem_preservesDistributionLieSubalgebra_iff).1 hX)]

/-- **The range of `f ↦ X_f` is the Lie algebra of contact vector fields**: the smooth vector fields
preserving the contact structure `ker α`. -/
theorem range_contactHamiltonianLieHom (hα : α.IsContactForm) :
    (α.contactHamiltonianLieHom hα).range =
      preservesDistributionLieSubalgebra I α.kerDistribution := by
  ext X
  rw [LieHom.mem_range]
  refine ⟨?_, fun hX ↦ (exists_contactHamiltonianLieHom_eq hα hX).imp fun _ ↦ And.left⟩
  rintro ⟨f, rfl⟩
  exact contactHamiltonianLieHom_mem_preservesDistributionLieSubalgebra hα f

/-! ### The Lie algebra isomorphism with the contact vector fields -/

variable (α) in
/-- **The Jacobi Lie algebra is isomorphic to the Lie algebra of contact vector fields** by
`f ↦ X_f`. Its inverse is contraction with `α`, `X ↦ α(X)`
(`TauCeti.SmoothForm.jacobiLieAlgebraEquiv_contactHamiltonianLieEquiv_symm_apply`). -/
def contactHamiltonianLieEquiv (hα : α.IsContactForm) :
    α.JacobiLieAlgebra hα ≃ₗ⁅ℝ⁆ preservesDistributionLieSubalgebra I α.kerDistribution :=
  (LieEquiv.ofInjective _ (contactHamiltonianLieHom_injective hα)).trans
    (LieEquiv.ofEq _ _ (congrArg SetLike.coe (range_contactHamiltonianLieHom hα)))

/-- The contact vector field of `f` under the isomorphism with the contact vector fields is
`X_f`. -/
@[simp]
theorem coe_contactHamiltonianLieEquiv_apply (hα : α.IsContactForm) (f : α.JacobiLieAlgebra hα) :
    (α.contactHamiltonianLieEquiv hα f : (LieAlgebroid.tangent I M).Sections) =
      α.contactHamiltonianLieHom hα f :=
  (rfl)

/-- **The inverse of `f ↦ X_f` is contraction with `α`**: the function corresponding to a contact
vector field `X` is `α(X)`. -/
@[simp]
theorem jacobiLieAlgebraEquiv_contactHamiltonianLieEquiv_symm_apply (hα : α.IsContactForm)
    (X : preservesDistributionLieSubalgebra I α.kerDistribution) (x : M) :
    α.jacobiLieAlgebraEquiv hα ((α.contactHamiltonianLieEquiv hα).symm X) x =
      α.val x ![(LieAlgebroid.tangent I M).sectionsEquiv
        (X : (LieAlgebroid.tangent I M).Sections) x] := by
  conv_rhs => rw [← (α.contactHamiltonianLieEquiv hα).apply_symm_apply X,
    coe_contactHamiltonianLieEquiv_apply, apply_contactHamiltonianLieHom]

end SmoothForm

end TauCeti
