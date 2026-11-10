/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Ideal
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import TauCeti.Geometry.Symplectic.Hamiltonian.Bracket
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# The Lie algebras of symplectic and Hamiltonian vector fields

Let `σ` be a closed two-form on a finite-dimensional manifold `M`. The smooth vector fields of `M`
form a real Lie algebra under the Lie bracket of vector fields, the sections
`(TauCeti.LieAlgebroid.tangent I M).Sections` of the tangent Lie algebroid. This file shows that
the brackets of the exact sequence

`0 → H⁰_dR(M) → C^∞(M) → {symplectic vector fields} → H¹_dR(M) → 0`

of `TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField` are compatible with Lie
brackets.

* The symplectic vector fields, those with `L_X σ = 0`, form a Lie subalgebra
  (`TauCeti.SmoothTwoForm.symplecticLieSubalgebra`), because the bracket of two symplectic vector
  fields is the Hamiltonian vector field of the smooth function `σ(Y, X)`
  (`TauCeti.SmoothTwoForm.isHamiltonianVectorField_mlieBracket`).
* The Hamiltonian vector fields of smooth functions form a Lie ideal of it
  (`TauCeti.SmoothTwoForm.hamiltonianLieIdeal`), the kernel of the class map
  `X ↦ [ι_X σ] ∈ H¹_dR(M)`
  (`TauCeti.SmoothTwoForm.mem_hamiltonianLieIdeal_iff_interiorClass_eq_zero`).
  It contains every bracket of symplectic vector fields
  (`TauCeti.SmoothTwoForm.lie_mem_hamiltonianLieIdeal`), so the class map vanishes on brackets
  (`TauCeti.SmoothTwoForm.interiorClass_lie`): it is a Lie algebra homomorphism to the abelian Lie
  algebra `H¹_dR(M)`.

For a symplectic form `σ`, the Poisson bracket `{f, g} = σ(X_f, X_g)` of smooth functions is
smooth (`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_poissonBracket`) and makes the smooth
functions a real Lie algebra, the **Poisson Lie algebra**
`TauCeti.SmoothTwoForm.PoissonLieAlgebra σ hσ` of `(M, σ)`. Since `X_{{f, g}} = -[X_f, X_g]`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`), the map
`f ↦ -X_f` is a Lie algebra homomorphism from the Poisson Lie algebra to the symplectic vector
fields (`TauCeti.SmoothTwoForm.negHamiltonianLieHom`). Its kernel consists of the functions with
vanishing differential (`TauCeti.SmoothTwoForm.mem_ker_negHamiltonianLieHom_iff`), the closed
`0`-forms making up `H⁰_dR(M)`, and its range is the ideal of Hamiltonian vector fields
(`TauCeti.SmoothTwoForm.range_negHamiltonianLieHom`). Together with the surjectivity of the class
map (`TauCeti.SmoothTwoForm.IsNondegenerate.interiorClass_surjective`), this makes

`0 → H⁰_dR(M) → (C^∞(M), {·, ·}) → {symplectic vector fields} → H¹_dR(M) → 0`

an exact sequence of Lie algebras, with `H⁰_dR(M)` and `H¹_dR(M)` abelian.

The Poisson Lie algebra is a type synonym of `C^∞⟮I, M; ℝ⟯` indexed by `σ` and by the proof that
`σ` is symplectic, so that the Poisson brackets of different forms live on different types. It
carries only the Lie bracket, not the pointwise product of functions. It is identified with the
smooth functions by `TauCeti.SmoothTwoForm.poissonLieAlgebraEquiv`.

## Main definitions

* `TauCeti.SmoothTwoForm.symplecticLieSubalgebra σ hσ`: the Lie subalgebra of symplectic vector
  fields of a closed two-form.
* `TauCeti.SmoothTwoForm.hamiltonianLieIdeal σ hσ`: the Lie ideal of Hamiltonian vector fields of
  smooth functions.
* `TauCeti.SmoothTwoForm.PoissonLieAlgebra σ hσ`: the smooth functions with the Poisson bracket.
* `TauCeti.SmoothTwoForm.negHamiltonianLieHom σ hσ`: the Lie algebra homomorphism `f ↦ -X_f`.

## Main results

* `TauCeti.SmoothTwoForm.interiorClass_lie`: the class `[ι_[X, Y] σ]` of a bracket vanishes.
* `TauCeti.SmoothTwoForm.mem_ker_negHamiltonianLieHom_iff`,
  `TauCeti.SmoothTwoForm.range_negHamiltonianLieHom`: kernel and range of `f ↦ -X_f`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1 (the Lie algebras of symplectic and Hamiltonian vector fields, and the exact sequence
  `0 → ℝ → C^∞(M) → symplectic vector fields → H¹(M; ℝ) → 0` of Lie algebras).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.3 (the Poisson algebra of a symplectic manifold).
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M}

/-! ### The Lie subalgebra of symplectic vector fields -/

/-- The bracket of two symplectic vector fields of a closed two-form is the Hamiltonian vector
field of a smooth function, namely of `σ(Y, X)`. -/
theorem exists_isHamiltonianVectorField_lie (hσ : σ.IsClosed)
    {X Y : (LieAlgebroid.tangent I M).Sections}
    (hX : (LieAlgebroid.tangent I M).sectionsEquiv X ∈ σ.symplecticVectorFields)
    (hY : (LieAlgebroid.tangent I M).sectionsEquiv Y ∈ σ.symplecticVectorFields) :
    ∃ φ : SmoothForm I M ℝ 0, σ.IsHamiltonianVectorField (fun y ↦ φ.1 y 0)
      ((LieAlgebroid.tangent I M).sectionsEquiv ⁅X, Y⁆) := by
  set X' := (LieAlgebroid.tangent I M).sectionsEquiv X
  set Y' := (LieAlgebroid.tangent I M).sectionsEquiv Y
  let g : C^∞⟮I, M; ℝ⟯ := ⟨fun x ↦ SmoothBundleForm.eval₂ σ x (Y' x) (X' x),
    SmoothForm.contMDiff_apply σ Y'.contMDiff X'.contMDiff⟩
  refine ⟨SmoothForm.ofFunction g, ?_⟩
  -- The bracket of the sections is the Lie bracket of the underlying vector fields.
  have hbr : ⇑((LieAlgebroid.tangent I M).sectionsEquiv ⁅X, Y⁆) = mlieBracket I X' Y' :=
    funext fun x ↦ by
      rw [LieAlgebroid.sectionsEquiv_lie, LieAlgebroid.tangent_bracket_apply]
  rw [hbr, SmoothForm.ofFunction_apply_zero]
  exact isHamiltonianVectorField_mlieBracket hσ hX hY

variable (σ) in
/-- The **Lie algebra of symplectic vector fields** of a closed two-form `σ`: the smooth vector
fields `X` with closed contraction `ι_X σ`, equivalently with `L_X σ = 0`, as a Lie subalgebra of
the Lie algebra of smooth vector fields. -/
def symplecticLieSubalgebra (hσ : σ.IsClosed) :
    LieSubalgebra ℝ (LieAlgebroid.tangent I M).Sections where
  toSubmodule := σ.symplecticVectorFields.comap
    ((LieAlgebroid.tangent I M).sectionsEquiv.restrictScalars ℝ).toLinearMap
  lie_mem' {X Y} hX hY := by
    obtain ⟨φ, hφ⟩ := exists_isHamiltonianVectorField_lie hσ hX hY
    exact mem_symplecticVectorFields_of_isHamiltonianVectorField hφ

/-- A smooth vector field lies in the Lie algebra of symplectic vector fields exactly when it is a
symplectic vector field. -/
@[simp]
theorem mem_symplecticLieSubalgebra_iff (hσ : σ.IsClosed)
    {X : (LieAlgebroid.tangent I M).Sections} :
    X ∈ σ.symplecticLieSubalgebra hσ ↔
      (LieAlgebroid.tangent I M).sectionsEquiv X ∈ σ.symplecticVectorFields :=
  Iff.rfl

variable (σ) in
/-- The elements of the Lie algebra of symplectic vector fields are the symplectic vector fields:
the identification of `TauCeti.SmoothTwoForm.symplecticLieSubalgebra` with the space
`TauCeti.SmoothTwoForm.symplecticVectorFields` on which the class map
`TauCeti.SmoothTwoForm.interiorClass` is defined. -/
def symplecticLieSubalgebraEquiv (hσ : σ.IsClosed) :
    σ.symplecticLieSubalgebra hσ ≃ₗ[ℝ] σ.symplecticVectorFields :=
  ((LieAlgebroid.tangent I M).sectionsEquiv.restrictScalars ℝ).ofSubmodule' σ.symplecticVectorFields

/-- The symplectic vector field of an element of the Lie algebra of symplectic vector fields is the
underlying smooth vector field. -/
@[simp]
theorem coe_symplecticLieSubalgebraEquiv_apply (hσ : σ.IsClosed)
    (X : σ.symplecticLieSubalgebra hσ) :
    (σ.symplecticLieSubalgebraEquiv hσ X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) =
      (LieAlgebroid.tangent I M).sectionsEquiv X :=
  (rfl)

/-- The element of the Lie algebra of symplectic vector fields corresponding to a symplectic vector
field has that field as its underlying smooth vector field. -/
@[simp]
theorem coe_symplecticLieSubalgebraEquiv_symm_apply (hσ : σ.IsClosed)
    (X : σ.symplecticVectorFields) :
    ((σ.symplecticLieSubalgebraEquiv hσ).symm X : (LieAlgebroid.tangent I M).Sections) =
      (LieAlgebroid.tangent I M).sectionsEquiv.symm X :=
  (rfl)

/-- Two elements of the Lie algebra of symplectic vector fields are equal when their underlying
vector fields agree at every point. -/
@[ext]
theorem symplecticLieSubalgebra.ext {hσ : σ.IsClosed} {X Y : σ.symplecticLieSubalgebra hσ}
    (h : ∀ x, (LieAlgebroid.tangent I M).sectionsEquiv (X : (LieAlgebroid.tangent I M).Sections) x =
      (LieAlgebroid.tangent I M).sectionsEquiv (Y : (LieAlgebroid.tangent I M).Sections) x) :
    X = Y :=
  Subtype.ext <| (LieAlgebroid.tangent I M).sectionsEquiv.injective <| ContMDiffSection.ext h

/-! ### The Lie ideal of Hamiltonian vector fields -/

variable (σ) in
/-- The **Lie ideal of Hamiltonian vector fields** of a closed two-form `σ`: the symplectic vector
fields `X` whose class `[ι_X σ] ∈ H¹_dR(M)` vanishes, that is, with `ι_X σ = df` for a smooth
function `f` (`TauCeti.SmoothTwoForm.mem_hamiltonianLieIdeal_iff`). It contains every bracket of
symplectic vector fields (`TauCeti.SmoothTwoForm.lie_mem_hamiltonianLieIdeal`). -/
def hamiltonianLieIdeal (hσ : σ.IsClosed) : LieIdeal ℝ (σ.symplecticLieSubalgebra hσ) where
  toSubmodule := (LinearMap.ker σ.interiorClass).comap (σ.symplecticLieSubalgebraEquiv hσ)
  lie_mem {Y X} _ := by
    obtain ⟨φ, hφ⟩ := exists_isHamiltonianVectorField_lie hσ Y.2 X.2
    refine (interiorClass_eq_zero_iff (σ.symplecticLieSubalgebraEquiv hσ ⁅Y, X⁆)).2 ⟨φ, ?_⟩
    rwa [coe_symplecticLieSubalgebraEquiv_apply, LieSubalgebra.coe_bracket]

/-- A symplectic vector field is Hamiltonian exactly when its class `[ι_X σ] ∈ H¹_dR(M)` vanishes:
the Lie ideal of Hamiltonian vector fields is the kernel of the class map. -/
theorem mem_hamiltonianLieIdeal_iff_interiorClass_eq_zero (hσ : σ.IsClosed)
    {X : σ.symplecticLieSubalgebra hσ} :
    X ∈ σ.hamiltonianLieIdeal hσ ↔ σ.interiorClass (σ.symplecticLieSubalgebraEquiv hσ X) = 0 := by
  rw [hamiltonianLieIdeal, LieSubmodule.mem_mk_iff', Submodule.mem_comap, LinearMap.mem_ker,
    LinearEquiv.coe_coe]

/-- A symplectic vector field lies in the Lie ideal of Hamiltonian vector fields exactly when it is
the Hamiltonian vector field of a smooth function. -/
theorem mem_hamiltonianLieIdeal_iff (hσ : σ.IsClosed) {X : σ.symplecticLieSubalgebra hσ} :
    X ∈ σ.hamiltonianLieIdeal hσ ↔ ∃ φ : SmoothForm I M ℝ 0,
      σ.IsHamiltonianVectorField (fun y ↦ φ.1 y 0)
        ((LieAlgebroid.tangent I M).sectionsEquiv (X : (LieAlgebroid.tangent I M).Sections)) := by
  rw [mem_hamiltonianLieIdeal_iff_interiorClass_eq_zero, interiorClass_eq_zero_iff,
    coe_symplecticLieSubalgebraEquiv_apply]

/-- **Brackets of symplectic vector fields are Hamiltonian**: the bracket of two symplectic vector
fields lies in the Lie ideal of Hamiltonian vector fields. Hence the quotient of the symplectic
vector fields by the Hamiltonian ones is abelian. -/
theorem lie_mem_hamiltonianLieIdeal (hσ : σ.IsClosed) (X Y : σ.symplecticLieSubalgebra hσ) :
    ⁅X, Y⁆ ∈ σ.hamiltonianLieIdeal hσ := by
  rw [mem_hamiltonianLieIdeal_iff, LieSubalgebra.coe_bracket]
  exact exists_isHamiltonianVectorField_lie hσ X.2 Y.2

/-- **The class map vanishes on brackets**: `[ι_[X, Y] σ] = 0` in `H¹_dR(M)` for symplectic vector
fields `X` and `Y`. So `X ↦ [ι_X σ]` is a Lie algebra homomorphism to the abelian Lie algebra
`H¹_dR(M)`. -/
@[simp]
theorem interiorClass_lie (hσ : σ.IsClosed) (X Y : σ.symplecticLieSubalgebra hσ) :
    σ.interiorClass (σ.symplecticLieSubalgebraEquiv hσ ⁅X, Y⁆) = 0 :=
  (mem_hamiltonianLieIdeal_iff_interiorClass_eq_zero hσ).1 (lie_mem_hamiltonianLieIdeal hσ X Y)

/-! ### The Poisson Lie algebra -/

variable (σ) in
/-- The **Poisson Lie algebra** of a symplectic form `σ`: the smooth real functions on `M` with the
Poisson bracket `⁅f, g⁆ = {f, g} = σ(X_f, X_g)` as Lie bracket. It is a type synonym of
`C^∞⟮I, M; ℝ⟯`, indexed by `σ` and by the proof `hσ` that `σ` is symplectic, and is identified with
the smooth functions by `TauCeti.SmoothTwoForm.poissonLieAlgebraEquiv`. Only the Lie algebra
structure is put on it, not the pointwise product. -/
def PoissonLieAlgebra (_hσ : σ.IsSymplectic) : Type _ := C^∞⟮I, M; ℝ⟯

namespace PoissonLieAlgebra

variable {hσ : σ.IsSymplectic}

instance instAddCommGroup : AddCommGroup (σ.PoissonLieAlgebra hσ) :=
  inferInstanceAs (AddCommGroup C^∞⟮I, M; ℝ⟯)

instance instModule : Module ℝ (σ.PoissonLieAlgebra hσ) :=
  inferInstanceAs (Module ℝ C^∞⟮I, M; ℝ⟯)

end PoissonLieAlgebra

variable (σ) in
/-- The identification of the Poisson Lie algebra of `σ` with the smooth functions. -/
def poissonLieAlgebraEquiv (hσ : σ.IsSymplectic) : σ.PoissonLieAlgebra hσ ≃ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  LinearEquiv.refl _ _

namespace PoissonLieAlgebra

variable {hσ : σ.IsSymplectic}

/-- The Poisson bracket of the Poisson Lie algebra. -/
instance instBracket : Bracket (σ.PoissonLieAlgebra hσ) (σ.PoissonLieAlgebra hσ) where
  bracket f g := (σ.poissonLieAlgebraEquiv hσ).symm
    ⟨σ.poissonBracket (σ.poissonLieAlgebraEquiv hσ f) (σ.poissonLieAlgebraEquiv hσ g),
      hσ.isNondegenerate.contMDiff_poissonBracket le_rfl
        ((σ.poissonLieAlgebraEquiv hσ f).contMDiff.of_le (by simp))
        ((σ.poissonLieAlgebraEquiv hσ g).contMDiff.of_le (by simp))⟩

end PoissonLieAlgebra

/-- The bracket of the Poisson Lie algebra is the Poisson bracket `{f, g} = σ(X_f, X_g)`. -/
@[simp]
theorem poissonLieAlgebraEquiv_lie_apply {hσ : σ.IsSymplectic} (f g : σ.PoissonLieAlgebra hσ)
    (x : M) :
    σ.poissonLieAlgebraEquiv hσ ⁅f, g⁆ x =
      σ.poissonBracket (σ.poissonLieAlgebraEquiv hσ f) (σ.poissonLieAlgebraEquiv hσ g) x :=
  (rfl)

/-- The bracket of the Poisson Lie algebra is the Poisson bracket `{f, g} = σ(X_f, X_g)`, as an
equality of functions. -/
theorem coe_poissonLieAlgebraEquiv_lie {hσ : σ.IsSymplectic} (f g : σ.PoissonLieAlgebra hσ) :
    ⇑(σ.poissonLieAlgebraEquiv hσ ⁅f, g⁆) =
      σ.poissonBracket (σ.poissonLieAlgebraEquiv hσ f) (σ.poissonLieAlgebraEquiv hσ g) :=
  (rfl)

namespace PoissonLieAlgebra

variable {hσ : σ.IsSymplectic}

omit [FiniteDimensional ℝ E] in
/-- Two elements of the Poisson Lie algebra are equal when they agree as functions. -/
@[ext]
theorem ext {f g : σ.PoissonLieAlgebra hσ}
    (h : ∀ x, σ.poissonLieAlgebraEquiv hσ f x = σ.poissonLieAlgebraEquiv hσ g x) : f = g :=
  (σ.poissonLieAlgebraEquiv hσ).injective <| ContMDiffMap.ext h

omit [FiniteDimensional ℝ E] in
/-- A smooth function is differentiable at every point. -/
private theorem mdifferentiableAt (f : σ.PoissonLieAlgebra hσ) (x : M) :
    MDifferentiableAt I 𝓘(ℝ) (σ.poissonLieAlgebraEquiv hσ f) x :=
  (σ.poissonLieAlgebraEquiv hσ f).contMDiff.mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] in
/-- A smooth function is `C^2`. -/
private theorem contMDiff_two (f : σ.PoissonLieAlgebra hσ) :
    ContMDiff I 𝓘(ℝ) 2 (σ.poissonLieAlgebraEquiv hσ f) :=
  (σ.poissonLieAlgebraEquiv hσ f).contMDiff.of_le (by simp)

/-- The Poisson bracket makes the smooth functions a Lie ring: bilinearity and antisymmetry hold
pointwise, and the Leibniz rule is the Jacobi identity of the Poisson bracket
(`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_poissonBracket`). -/
instance instLieRing : LieRing (σ.PoissonLieAlgebra hσ) where
  add_lie f g k := by
    ext x
    simp only [poissonLieAlgebraEquiv_lie_apply, map_add, ContMDiffMap.coe_add, Pi.add_apply,
      poissonBracket_add_left (mdifferentiableAt f x) (mdifferentiableAt g x)]
  lie_add f g k := by
    ext x
    simp only [poissonLieAlgebraEquiv_lie_apply, map_add, ContMDiffMap.coe_add, Pi.add_apply,
      poissonBracket_add_right (mdifferentiableAt g x) (mdifferentiableAt k x)]
  lie_self f := by
    ext x
    simp only [poissonLieAlgebraEquiv_lie_apply, poissonBracket_self, map_zero,
      ContMDiffMap.coe_zero, Pi.zero_apply]
  leibniz_lie f g k := by
    ext x
    simp only [map_add, ContMDiffMap.coe_add, Pi.add_apply, poissonLieAlgebraEquiv_lie_apply,
      coe_poissonLieAlgebraEquiv_lie]
    rw [hσ.isNondegenerate.poissonBracket_poissonBracket hσ.isClosed (contMDiff_two f)
        (contMDiff_two g) (contMDiff_two k),
      ← neg_poissonBracket σ (σ.poissonBracket _ _) (σ.poissonLieAlgebraEquiv hσ g)]
    ring

/-- The Poisson Lie algebra is a real Lie algebra. -/
instance instLieAlgebra : LieAlgebra ℝ (σ.PoissonLieAlgebra hσ) where
  lie_smul c f g := by
    ext x
    simp only [poissonLieAlgebraEquiv_lie_apply, map_smul, ContMDiffMap.coe_smul,
      poissonBracket_const_smul_right, Pi.smul_apply]

end PoissonLieAlgebra

/-! ### The Lie algebra homomorphism `f ↦ -X_f` -/

/-- The vector field `-X_f` of a smooth function `f`, as a symplectic vector field. -/
private def negHamiltonian (hσ : σ.IsSymplectic) (f : σ.PoissonLieAlgebra hσ) :
    σ.symplecticLieSubalgebra hσ.isClosed :=
  (σ.symplecticLieSubalgebraEquiv hσ.isClosed).symm
    (hσ.isNondegenerate.negHamiltonianₗ (SmoothForm.ofFunction (σ.poissonLieAlgebraEquiv hσ f)))

/-- The value of `-X_f` at a point. -/
private theorem negHamiltonian_apply (hσ : σ.IsSymplectic) (f : σ.PoissonLieAlgebra hσ) (x : M) :
    (LieAlgebroid.tangent I M).sectionsEquiv
        (negHamiltonian hσ f : (LieAlgebroid.tangent I M).Sections) x =
      -σ.hamiltonianVectorField (σ.poissonLieAlgebraEquiv hσ f) x := by
  rw [negHamiltonian, coe_symplecticLieSubalgebraEquiv_symm_apply, LinearEquiv.apply_symm_apply,
    IsNondegenerate.coe_negHamiltonianₗ, SmoothForm.ofFunction_apply_zero]

variable (σ) in
/-- **The Lie algebra homomorphism `f ↦ -X_f`** from the Poisson Lie algebra of a symplectic form to
its symplectic vector fields. That it preserves brackets is `X_{{f, g}} = -[X_f, X_g]`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`). -/
def negHamiltonianLieHom (hσ : σ.IsSymplectic) :
    σ.PoissonLieAlgebra hσ →ₗ⁅ℝ⁆ σ.symplecticLieSubalgebra hσ.isClosed where
  toFun := negHamiltonian hσ
  map_add' f g := by
    ext x
    simp [negHamiltonian_apply, add_comm, hamiltonianVectorField_add
      (PoissonLieAlgebra.mdifferentiableAt f x) (PoissonLieAlgebra.mdifferentiableAt g x)]
  map_smul' c f := by
    ext x
    rw [SetLike.val_smul, LinearMapClass.map_smul_of_tower]
    simp [negHamiltonian_apply]
  map_lie' {f g} := by
    ext x
    have hneg : ∀ u, ⇑((LieAlgebroid.tangent I M).sectionsEquiv
        (negHamiltonian hσ u : (LieAlgebroid.tangent I M).Sections)) =
        -σ.hamiltonianVectorField (σ.poissonLieAlgebraEquiv hσ u) :=
      fun u ↦ funext (negHamiltonian_apply hσ u)
    rw [LieSubalgebra.coe_bracket, LieAlgebroid.sectionsEquiv_lie,
      LieAlgebroid.tangent_bracket_apply, hneg, hneg, hneg, coe_poissonLieAlgebraEquiv_lie,
      hσ.isNondegenerate.hamiltonianVectorField_poissonBracket hσ.isClosed
        (PoissonLieAlgebra.contMDiff_two f) (PoissonLieAlgebra.contMDiff_two g)]
    simp [mlieBracket_neg_left, mlieBracket_neg_right]

/-- The vector field of `f ↦ -X_f` is the negated Hamiltonian vector field. -/
@[simp]
theorem negHamiltonianLieHom_apply (hσ : σ.IsSymplectic) (f : σ.PoissonLieAlgebra hσ) (x : M) :
    (LieAlgebroid.tangent I M).sectionsEquiv
        (σ.negHamiltonianLieHom hσ f : (LieAlgebroid.tangent I M).Sections) x =
      -σ.hamiltonianVectorField (σ.poissonLieAlgebraEquiv hσ f) x :=
  negHamiltonian_apply hσ f x

/-- As a symplectic vector field, `-X_f` is the image of `f` under the map `f ↦ -X_f` of
`TauCeti.SmoothTwoForm.IsNondegenerate.negHamiltonianₗ`, defined on smooth `0`-forms. -/
theorem symplecticLieSubalgebraEquiv_negHamiltonianLieHom (hσ : σ.IsSymplectic)
    (f : σ.PoissonLieAlgebra hσ) :
    σ.symplecticLieSubalgebraEquiv hσ.isClosed (σ.negHamiltonianLieHom hσ f) =
      hσ.isNondegenerate.negHamiltonianₗ (SmoothForm.ofFunction (σ.poissonLieAlgebraEquiv hσ f)) :=
  LinearEquiv.apply_symm_apply _ _

/-- **The kernel of `f ↦ -X_f`** consists of the smooth functions with vanishing differential. -/
theorem mem_ker_negHamiltonianLieHom_iff (hσ : σ.IsSymplectic) {f : σ.PoissonLieAlgebra hσ} :
    f ∈ (σ.negHamiltonianLieHom hσ).ker ↔
      ∀ x, mvfderiv I (σ.poissonLieAlgebraEquiv hσ f) x = 0 := by
  simp_rw [LieHom.mem_ker, ← hσ.isNondegenerate.hamiltonianVectorField_eq_zero_iff,
    ← neg_eq_zero (a := σ.hamiltonianVectorField _ _), ← negHamiltonianLieHom_apply]
  constructor
  · intro h x
    rw [h, ZeroMemClass.coe_zero, map_zero, ContMDiffSection.coe_zero, Pi.zero_apply]
  · intro h
    ext x
    simp [h x]

/-- **The range of `f ↦ -X_f`** is the Lie ideal of Hamiltonian vector fields. -/
theorem range_negHamiltonianLieHom (hσ : σ.IsSymplectic) :
    (σ.negHamiltonianLieHom hσ).range = (σ.hamiltonianLieIdeal hσ.isClosed).toLieSubalgebra := by
  ext X
  rw [LieHom.mem_range, LieIdeal.mem_toLieSubalgebra,
    mem_hamiltonianLieIdeal_iff_interiorClass_eq_zero,
    hσ.isNondegenerate.exact_negHamiltonianₗ_interiorClass _, Set.mem_range]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨_, (symplecticLieSubalgebraEquiv_negHamiltonianLieHom hσ f).symm⟩
  · rintro ⟨φ, hφ⟩
    -- Every smooth `0`-form is the form of a smooth function.
    let g : C^∞⟮I, M; ℝ⟯ := ⟨fun y ↦ φ.1 y 0,
      isSmoothForm_ofFunction_iff.1 (by rw [← RoughForm.eq_ofFunction]; exact φ.isSmoothForm)⟩
    have hg : SmoothForm.ofFunction g = φ :=
      Subtype.ext <| (SmoothForm.coe_ofFunction g).trans (RoughForm.eq_ofFunction φ.1).symm
    refine ⟨(σ.poissonLieAlgebraEquiv hσ).symm g, (σ.symplecticLieSubalgebraEquiv _).injective ?_⟩
    rw [symplecticLieSubalgebraEquiv_negHamiltonianLieHom, LinearEquiv.apply_symm_apply, hg, hφ]

end SmoothTwoForm

end TauCeti
