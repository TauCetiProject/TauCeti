/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import TauCeti.Geometry.Symplectic.Hamiltonian.Bracket
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# The Lie algebra of Hamiltonian functions

Let `σ` be a two-form on a manifold `M` modelled on a real normed space, possibly of infinite
dimension. A smooth function `f` is a **Hamiltonian function** when it has a smooth Hamiltonian
vector field: a smooth vector field `X` with `ι_X σ = df`. The Hamiltonian functions form a real
vector space (`TauCeti.SmoothTwoForm.hamiltonianFunctions`).

In infinite dimension a fiberwise nondegenerate form need not have surjective flat maps
`v ↦ σ(v, ·)`, so a smooth function need not have a Hamiltonian vector field, and the field
`TauCeti.SmoothTwoForm.hamiltonianVectorField`, defined through the inverse of the flat map, is
zero wherever that map is not invertible. The bracket of Hamiltonian functions is therefore taken
through their Hamiltonian vector fields themselves, which are unique for a fiberwise nondegenerate
form.

For a symplectic form, that is closed and fiberwise nondegenerate, on a manifold modelled on a
Banach space, the bracket `⁅f, g⁆ = σ(X_f, X_g)` makes the Hamiltonian functions a real Lie
algebra, `TauCeti.SmoothTwoForm.HamiltonianLieAlgebra σ hσ`.

* `σ(X_f, X_g)` is again a Hamiltonian function, with the Hamiltonian vector field `-[X_f, X_g]`
  (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.neg_mlieBracket`), so
  `X_{⁅f, g⁆} = -[X_f, X_g]` (`TauCeti.SmoothTwoForm.HamiltonianLieAlgebra.vectorField_lie`).
* The Jacobi identity of the bracket is the Jacobi identity
  `σ([X, Y], Z) + σ([Y, Z], X) + σ([Z, X], Y) = 0` for Hamiltonian vector fields
  (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.eval₂_mlieBracket_jacobi`).
* The map `f ↦ -X_f` is a Lie algebra homomorphism into the smooth vector fields with their Lie
  bracket (`TauCeti.SmoothTwoForm.HamiltonianLieAlgebra.negVectorFieldLieHom`), whose kernel
  consists of the functions with vanishing differential
  (`TauCeti.SmoothTwoForm.HamiltonianLieAlgebra.mem_ker_negVectorFieldLieHom_iff`).

On a finite-dimensional manifold every smooth function is Hamiltonian
(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianFunctions_eq_top`), and the bracket is the
Poisson bracket `TauCeti.SmoothTwoForm.poissonBracket`
(`TauCeti.SmoothTwoForm.HamiltonianLieAlgebra.lie_apply_eq_poissonBracket`), the bracket of the
Poisson Lie algebra `TauCeti.SmoothTwoForm.PoissonLieAlgebra`.

The Lie algebra is a type synonym of the Hamiltonian functions indexed by the proof `hσ` that `σ`
is symplectic, as for `TauCeti.SmoothTwoForm.PoissonLieAlgebra`. It carries only the Lie bracket,
not the pointwise product of functions, and is identified with the Hamiltonian functions by
`TauCeti.SmoothTwoForm.hamiltonianLieAlgebraEquiv`.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.3 (Hamiltonian vector fields, Poisson brackets and the Lie algebra of functions on a
  weakly symplectic manifold).
* P. R. Chernoff, J. E. Marsden, *Properties of Infinite Dimensional Hamiltonian Systems*,
  Lecture Notes in Mathematics 425, Springer, 1974 (weakly and strongly nondegenerate forms on
  Banach manifolds).
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-! ### Hamiltonian functions -/

variable (σ) in
/-- The **Hamiltonian functions** of a two-form `σ`: the smooth functions `f` with a smooth
Hamiltonian vector field, `ι_X σ = df` for a smooth vector field `X`. -/
def hamiltonianFunctions : Submodule ℝ C^∞⟮I, M; ℝ⟯ where
  carrier := {f | ∃ X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯, σ.IsHamiltonianVectorField f X}
  add_mem' := by
    rintro f g ⟨X, hX⟩ ⟨Y, hY⟩
    refine ⟨X + Y, isHamiltonianVectorField_iff.2 fun x v ↦ ?_⟩
    rw [ContMDiffSection.coe_add, Pi.add_apply, SmoothBundleForm.eval₂_add_left,
      isHamiltonianVectorField_iff.1 hX x v, isHamiltonianVectorField_iff.1 hY x v,
      ContMDiffMap.coe_add, mvfderiv_add (f.contMDiff.mdifferentiableAt (by simp))
        (g.contMDiff.mdifferentiableAt (by simp)), add_apply]
  zero_mem' := ⟨0, isHamiltonianVectorField_iff.2 fun x v ↦ by
    rw [ContMDiffSection.coe_zero, Pi.zero_apply, SmoothBundleForm.eval₂_zero_left,
      ContMDiffMap.coe_zero, mvfderiv_zero, zero_apply]⟩
  smul_mem' := by
    rintro c f ⟨X, hX⟩
    refine ⟨c • X, isHamiltonianVectorField_iff.2 fun x v ↦ ?_⟩
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, SmoothBundleForm.eval₂_smul_left,
      isHamiltonianVectorField_iff.1 hX x v, ContMDiffMap.coe_smul, mvfderiv_const_smul_field,
      smul_apply]

/-- A smooth function is Hamiltonian exactly when it has a smooth Hamiltonian vector field. -/
@[simp]
theorem mem_hamiltonianFunctions_iff {f : C^∞⟮I, M; ℝ⟯} :
    f ∈ σ.hamiltonianFunctions ↔
      ∃ X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯, σ.IsHamiltonianVectorField f X :=
  Iff.rfl

/-- **The pairing of two Hamiltonian vector fields is a Hamiltonian function.** For a closed form
`σ` on a manifold modelled on a Banach space and smooth Hamiltonian vector fields `X` of `f` and
`Y` of `g`, the smooth function `σ(X, Y)` is Hamiltonian, with the Hamiltonian vector field
`-[X, Y]` (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.neg_mlieBracket`). -/
theorem eval₂_mem_hamiltonianFunctions [CompleteSpace E] (hσ : σ.IsClosed)
    {f g : C^∞⟮I, M; ℝ⟯} {X Y : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯}
    (hX : σ.IsHamiltonianVectorField f X) (hY : σ.IsHamiltonianVectorField g Y) :
    (⟨fun x ↦ SmoothBundleForm.eval₂ σ x (X x) (Y x),
      SmoothForm.contMDiff_apply σ X.contMDiff Y.contMDiff⟩ : C^∞⟮I, M; ℝ⟯) ∈
        σ.hamiltonianFunctions := by
  refine ⟨-(LieAlgebroid.tangent I M).bracket X Y, ?_⟩
  have hXY : ⇑(-(LieAlgebroid.tangent I M).bracket X Y) = -mlieBracket I X Y :=
    funext fun x ↦ by
      rw [ContMDiffSection.coe_neg, Pi.neg_apply, LieAlgebroid.tangent_bracket_apply,
        Pi.neg_apply]
  rw [hXY]
  exact hX.neg_mlieBracket hσ hY (f.contMDiff.of_le (by simp)) (g.contMDiff.of_le (by simp))
    (X.contMDiff.mdifferentiable (by simp)) (Y.contMDiff.mdifferentiable (by simp))

/-- **Every smooth function is Hamiltonian in finite dimension.** For a fiberwise nondegenerate
form on a finite-dimensional manifold, the Hamiltonian vector field `X_f = (σ♭)⁻¹ df` of a smooth
function is smooth. -/
theorem IsNondegenerate.hamiltonianFunctions_eq_top [FiniteDimensional ℝ E]
    (h : σ.IsNondegenerate) : σ.hamiltonianFunctions = ⊤ :=
  eq_top_iff.2 fun f _ ↦
    ⟨⟨σ.hamiltonianVectorField f, h.contMDiff_hamiltonianVectorField le_rfl
        (f.contMDiff.of_le (by simp))⟩,
      h.isHamiltonianVectorField_hamiltonianVectorField f⟩

/-! ### The Lie algebra of Hamiltonian functions -/

variable (σ) in
/-- The **Lie algebra of Hamiltonian functions** of a symplectic form `σ`: the smooth functions
with a smooth Hamiltonian vector field, with the bracket `⁅f, g⁆ = σ(X_f, X_g)`. It is a type
synonym of `TauCeti.SmoothTwoForm.hamiltonianFunctions`, indexed by the proof `hσ` that `σ` is
symplectic, and is identified with the Hamiltonian functions by
`TauCeti.SmoothTwoForm.hamiltonianLieAlgebraEquiv`. The Lie algebra structure needs the model space
to be complete. -/
def HamiltonianLieAlgebra (_hσ : σ.IsSymplectic) : Type _ := σ.hamiltonianFunctions

namespace HamiltonianLieAlgebra

variable {hσ : σ.IsSymplectic}

instance instAddCommGroup : AddCommGroup (σ.HamiltonianLieAlgebra hσ) :=
  inferInstanceAs (AddCommGroup σ.hamiltonianFunctions)

instance instModule : Module ℝ (σ.HamiltonianLieAlgebra hσ) :=
  inferInstanceAs (Module ℝ σ.hamiltonianFunctions)

end HamiltonianLieAlgebra

variable (σ) in
/-- The identification of the Lie algebra of Hamiltonian functions of `σ` with the Hamiltonian
functions. -/
def hamiltonianLieAlgebraEquiv (hσ : σ.IsSymplectic) :
    σ.HamiltonianLieAlgebra hσ ≃ₗ[ℝ] σ.hamiltonianFunctions :=
  LinearEquiv.refl _ _

namespace HamiltonianLieAlgebra

variable {hσ : σ.IsSymplectic}

/-- Two elements of the Lie algebra of Hamiltonian functions are equal when they agree as
functions. -/
@[ext]
theorem ext {f g : σ.HamiltonianLieAlgebra hσ}
    (h : ∀ x, (σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯) x =
      (σ.hamiltonianLieAlgebraEquiv hσ g : C^∞⟮I, M; ℝ⟯) x) : f = g :=
  (σ.hamiltonianLieAlgebraEquiv hσ).injective <| Subtype.ext <| ContMDiffMap.ext h

/-- The **Hamiltonian vector field** `X_f` of a Hamiltonian function `f`: the smooth vector field
with `ι_{X_f} σ = df`, unique because `σ` is fiberwise nondegenerate
(`TauCeti.SmoothTwoForm.HamiltonianLieAlgebra.isHamiltonianVectorField_iff_eq_vectorField`). -/
def vectorField (f : σ.HamiltonianLieAlgebra hσ) : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ :=
  (σ.hamiltonianLieAlgebraEquiv hσ f).property.choose

/-- The vector field of a Hamiltonian function is a Hamiltonian vector field of it. -/
theorem isHamiltonianVectorField_vectorField (f : σ.HamiltonianLieAlgebra hσ) :
    σ.IsHamiltonianVectorField (σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯)
      (vectorField f) :=
  (σ.hamiltonianLieAlgebraEquiv hσ f).property.choose_spec

/-- **Uniqueness of Hamiltonian vector fields.** The vector field of a Hamiltonian function is its
only Hamiltonian vector field. -/
theorem isHamiltonianVectorField_iff_eq_vectorField {f : σ.HamiltonianLieAlgebra hσ}
    {X : (x : M) → TangentSpace I x} :
    σ.IsHamiltonianVectorField (σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯) X ↔
      X = vectorField f := by
  refine ⟨fun hX ↦ hσ.isNondegenerate.interior_injective ?_, fun hX ↦ hX ▸
    isHamiltonianVectorField_vectorField f⟩
  exact (isHamiltonianVectorField_iff_interior_eq.1 hX).trans
    (isHamiltonianVectorField_iff_interior_eq.1 (isHamiltonianVectorField_vectorField f)).symm

/-- The vector field of a sum of Hamiltonian functions is the sum of their vector fields. -/
@[simp]
theorem vectorField_add (f g : σ.HamiltonianLieAlgebra hσ) :
    vectorField (f + g) = vectorField f + vectorField g := by
  refine ContMDiffSection.coe_injective <| (isHamiltonianVectorField_iff_eq_vectorField.1 <|
    isHamiltonianVectorField_iff.2 fun x v ↦ ?_).symm
  have hf := isHamiltonianVectorField_iff.1 (isHamiltonianVectorField_vectorField f) x v
  have hg := isHamiltonianVectorField_iff.1 (isHamiltonianVectorField_vectorField g) x v
  rw [ContMDiffSection.coe_add, Pi.add_apply, SmoothBundleForm.eval₂_add_left, hf, hg, map_add,
    Submodule.coe_add, ContMDiffMap.coe_add,
    mvfderiv_add ((σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯).contMDiff.mdifferentiableAt
      (by simp)) ((σ.hamiltonianLieAlgebraEquiv hσ g : C^∞⟮I, M; ℝ⟯).contMDiff.mdifferentiableAt
      (by simp)), add_apply]

/-- The vector field of a real multiple of a Hamiltonian function is the same multiple of its
vector field. -/
@[simp]
theorem vectorField_smul (c : ℝ) (f : σ.HamiltonianLieAlgebra hσ) :
    vectorField (c • f) = c • vectorField f := by
  refine ContMDiffSection.coe_injective <| (isHamiltonianVectorField_iff_eq_vectorField.1 <|
    isHamiltonianVectorField_iff.2 fun x v ↦ ?_).symm
  rw [ContMDiffSection.coe_smul, Pi.smul_apply, SmoothBundleForm.eval₂_smul_left,
    isHamiltonianVectorField_iff.1 (isHamiltonianVectorField_vectorField f) x v, map_smul,
    Submodule.coe_smul, ContMDiffMap.coe_smul, mvfderiv_const_smul_field,
    smul_apply]

variable [CompleteSpace E]

/-- The bracket `⁅f, g⁆ = σ(X_f, X_g)` of the Lie algebra of Hamiltonian functions. -/
instance instBracket : Bracket (σ.HamiltonianLieAlgebra hσ) (σ.HamiltonianLieAlgebra hσ) where
  bracket f g := (σ.hamiltonianLieAlgebraEquiv hσ).symm
    ⟨_, eval₂_mem_hamiltonianFunctions hσ.isClosed (isHamiltonianVectorField_vectorField f)
      (isHamiltonianVectorField_vectorField g)⟩

end HamiltonianLieAlgebra

/-- The bracket of the Lie algebra of Hamiltonian functions is `⁅f, g⁆ = σ(X_f, X_g)`. -/
@[simp]
theorem hamiltonianLieAlgebraEquiv_lie_apply [CompleteSpace E] {hσ : σ.IsSymplectic}
    (f g : σ.HamiltonianLieAlgebra hσ) (x : M) :
    (σ.hamiltonianLieAlgebraEquiv hσ ⁅f, g⁆ : C^∞⟮I, M; ℝ⟯) x =
      SmoothBundleForm.eval₂ σ x (HamiltonianLieAlgebra.vectorField f x)
        (HamiltonianLieAlgebra.vectorField g x) :=
  (rfl)

namespace HamiltonianLieAlgebra

variable [CompleteSpace E] {hσ : σ.IsSymplectic}

/-- The bracket of Hamiltonian functions is the derivative of the first along the vector field of
the second: `⁅f, g⁆ = σ(X_f, X_g) = df(X_g)`. -/
theorem lie_apply_eq_mvfderiv (f g : σ.HamiltonianLieAlgebra hσ) (x : M) :
    (σ.hamiltonianLieAlgebraEquiv hσ ⁅f, g⁆ : C^∞⟮I, M; ℝ⟯) x =
      mvfderiv I (σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯) x (vectorField g x) := by
  rw [hamiltonianLieAlgebraEquiv_lie_apply,
    isHamiltonianVectorField_iff.1 (isHamiltonianVectorField_vectorField f)]

/-- **`f ↦ X_f` reverses brackets**: the Hamiltonian vector field of `⁅f, g⁆` is
`-[X_f, X_g]`. -/
@[simp]
theorem vectorField_lie (f g : σ.HamiltonianLieAlgebra hσ) :
    ⇑(vectorField ⁅f, g⁆) = -mlieBracket I (vectorField f) (vectorField g) := by
  refine (isHamiltonianVectorField_iff_eq_vectorField.1 ?_).symm
  exact (isHamiltonianVectorField_vectorField f).neg_mlieBracket hσ.isClosed
    (isHamiltonianVectorField_vectorField g)
    ((σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯).contMDiff.of_le (by simp))
    ((σ.hamiltonianLieAlgebraEquiv hσ g : C^∞⟮I, M; ℝ⟯).contMDiff.of_le (by simp))
    ((vectorField f).contMDiff.mdifferentiable (by simp))
    ((vectorField g).contMDiff.mdifferentiable (by simp))

/-- The Hamiltonian functions of a symplectic form on a manifold modelled on a Banach space form a
Lie ring under the bracket `⁅f, g⁆ = σ(X_f, X_g)`. -/
instance instLieRing : LieRing (σ.HamiltonianLieAlgebra hσ) where
  add_lie f g k := by
    ext x
    simp only [hamiltonianLieAlgebraEquiv_lie_apply, vectorField_add, map_add, Submodule.coe_add,
      ContMDiffMap.coe_add, ContMDiffSection.coe_add, Pi.add_apply,
      SmoothBundleForm.eval₂_add_left]
  lie_add f g k := by
    ext x
    simp only [hamiltonianLieAlgebraEquiv_lie_apply, vectorField_add, map_add, Submodule.coe_add,
      ContMDiffMap.coe_add, ContMDiffSection.coe_add, Pi.add_apply,
      SmoothBundleForm.eval₂_add_right]
  lie_self f := by
    ext x
    rw [hamiltonianLieAlgebraEquiv_lie_apply, SmoothBundleForm.eval₂_self, map_zero,
      Submodule.coe_zero, ContMDiffMap.coe_zero, Pi.zero_apply]
  leibniz_lie f g k := by
    ext x
    simp only [map_add, Submodule.coe_add, ContMDiffMap.coe_add, Pi.add_apply,
      hamiltonianLieAlgebraEquiv_lie_apply, vectorField_lie, Pi.neg_apply,
      SmoothBundleForm.eval₂_neg_left, SmoothBundleForm.eval₂_neg_right]
    -- The Leibniz rule is the Jacobi identity for the Hamiltonian vector fields of `f`, `g`, `k`.
    have h := (isHamiltonianVectorField_vectorField f).eval₂_mlieBracket_jacobi hσ.isClosed
      (isHamiltonianVectorField_vectorField g) (isHamiltonianVectorField_vectorField k)
      ((σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯).contMDiff.contMDiffAt.of_le (by simp))
      ((σ.hamiltonianLieAlgebraEquiv hσ g : C^∞⟮I, M; ℝ⟯).contMDiff.contMDiffAt.of_le (by simp))
      ((σ.hamiltonianLieAlgebraEquiv hσ k : C^∞⟮I, M; ℝ⟯).contMDiff.contMDiffAt.of_le (by simp))
      ((vectorField f).contMDiff.mdifferentiableAt (by simp) (x := x))
      ((vectorField g).contMDiff.mdifferentiableAt (by simp))
      ((vectorField k).contMDiff.mdifferentiableAt (by simp))
    rw [SmoothBundleForm.eval₂_swap σ x (mlieBracket I _ _ x) (vectorField f x),
      mlieBracket_swap_apply (V := vectorField k), SmoothBundleForm.eval₂_neg_left,
      SmoothBundleForm.eval₂_swap σ x (mlieBracket I _ _ x) (vectorField g x)] at h
    linear_combination h

/-- The Hamiltonian functions of a symplectic form on a manifold modelled on a Banach space form a
real Lie algebra. -/
instance instLieAlgebra : LieAlgebra ℝ (σ.HamiltonianLieAlgebra hσ) where
  lie_smul c f g := by
    ext x
    rw [hamiltonianLieAlgebraEquiv_lie_apply, vectorField_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, SmoothBundleForm.eval₂_smul_right, map_smul, Submodule.coe_smul,
      ContMDiffMap.coe_smul, Pi.smul_apply, hamiltonianLieAlgebraEquiv_lie_apply]

/-! ### The Lie algebra homomorphism `f ↦ -X_f` -/

variable (σ hσ) in
/-- **The Lie algebra homomorphism `f ↦ -X_f`** from the Hamiltonian functions of a symplectic form
to the smooth vector fields with their Lie bracket, the sections of the tangent Lie algebroid. It is
a homomorphism because `X_{⁅f, g⁆} = -[X_f, X_g]`
(`TauCeti.SmoothTwoForm.HamiltonianLieAlgebra.vectorField_lie`). -/
def negVectorFieldLieHom :
    σ.HamiltonianLieAlgebra hσ →ₗ⁅ℝ⁆ (LieAlgebroid.tangent I M).Sections where
  toFun f := (LieAlgebroid.tangent I M).sectionsEquiv.symm (-vectorField f)
  map_add' f g := by
    rw [vectorField_add, neg_add, map_add]
  map_smul' c f := by
    rw [vectorField_smul, ← smul_neg, LinearMapClass.map_smul_of_tower, RingHom.id_apply]
  map_lie' {f g} := (LieAlgebroid.tangent I M).sectionsEquiv.injective <|
    ContMDiffSection.ext fun x ↦ by
      rw [LieAlgebroid.sectionsEquiv_lie, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        LieAlgebroid.tangent_bracket_apply, ContMDiffSection.coe_neg, ContMDiffSection.coe_neg,
        ContMDiffSection.coe_neg, Pi.neg_apply, vectorField_lie, Pi.neg_apply, neg_neg,
        mlieBracket_neg_left, mlieBracket_neg_right, neg_neg]

/-- The vector field of `f ↦ -X_f` is the negated Hamiltonian vector field. -/
@[simp]
theorem negVectorFieldLieHom_apply (f : σ.HamiltonianLieAlgebra hσ) (x : M) :
    (LieAlgebroid.tangent I M).sectionsEquiv (negVectorFieldLieHom σ hσ f) x =
      -vectorField f x := by
  rw [negVectorFieldLieHom, LieHom.coe_mk, LinearEquiv.apply_symm_apply, ContMDiffSection.coe_neg,
    Pi.neg_apply]

/-- **The kernel of `f ↦ -X_f`** consists of the Hamiltonian functions with vanishing
differential. -/
theorem mem_ker_negVectorFieldLieHom_iff {f : σ.HamiltonianLieAlgebra hσ} :
    f ∈ (negVectorFieldLieHom σ hσ).ker ↔
      ∀ x, mvfderiv I (σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯) x = 0 := by
  have hX := isHamiltonianVectorField_iff.1 (isHamiltonianVectorField_vectorField f)
  rw [LieHom.mem_ker]
  constructor
  · intro h x
    have hx : vectorField f x = 0 := by
      rw [← neg_eq_zero, ← negVectorFieldLieHom_apply, h, map_zero, ContMDiffSection.coe_zero,
        Pi.zero_apply]
    ext v
    rw [← hX, hx, SmoothBundleForm.eval₂_zero_left, zero_apply]
  · intro h
    refine (LieAlgebroid.tangent I M).sectionsEquiv.injective <| ContMDiffSection.ext fun x ↦ ?_
    rw [negVectorFieldLieHom_apply, map_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
      neg_eq_zero]
    refine congrFun ((isHamiltonianVectorField_iff_eq_vectorField (X := 0)).1
      (isHamiltonianVectorField_iff.2 fun y v ↦ ?_)).symm x
    rw [Pi.zero_apply, SmoothBundleForm.eval₂_zero_left, h y, zero_apply]

/-! ### Comparison with the Poisson bracket in finite dimension -/

omit [CompleteSpace E] in
/-- In finite dimension the vector field of a Hamiltonian function is `X_f = (σ♭)⁻¹ df`. -/
theorem vectorField_eq_hamiltonianVectorField [FiniteDimensional ℝ E]
    (f : σ.HamiltonianLieAlgebra hσ) :
    ⇑(vectorField f) =
      σ.hamiltonianVectorField (σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯) :=
  (hσ.isNondegenerate.isHamiltonianVectorField_iff_eq.1
    (isHamiltonianVectorField_vectorField f))

/-- In finite dimension the bracket of Hamiltonian functions is the Poisson bracket
`{f, g} = σ(X_f, X_g)` with `X_f = (σ♭)⁻¹ df`. -/
theorem lie_apply_eq_poissonBracket [FiniteDimensional ℝ E] (f g : σ.HamiltonianLieAlgebra hσ)
    (x : M) :
    (σ.hamiltonianLieAlgebraEquiv hσ ⁅f, g⁆ : C^∞⟮I, M; ℝ⟯) x =
      σ.poissonBracket (σ.hamiltonianLieAlgebraEquiv hσ f : C^∞⟮I, M; ℝ⟯)
        (σ.hamiltonianLieAlgebraEquiv hσ g : C^∞⟮I, M; ℝ⟯) x := by
  rw [hamiltonianLieAlgebraEquiv_lie_apply, poissonBracket_def,
    vectorField_eq_hamiltonianVectorField, vectorField_eq_hamiltonianVectorField]

end HamiltonianLieAlgebra

end SmoothTwoForm

end TauCeti
