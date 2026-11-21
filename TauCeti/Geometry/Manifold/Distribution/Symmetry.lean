/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Vector fields preserving a distribution, and basic functions

Let `D` be a distribution on a real manifold `M`. A vector field `X` **preserves** `D`
(`TauCeti.PreservesDistribution`) when its Lie bracket with every local smooth section of `D` is
again a section of `D`: if `Y` is smooth on an open set `U` and tangent to `D` there, then so is
`[X, Y]`. A function is **basic** for `D` when its differential vanishes on `D`, so that it is
locally constant along the integral manifolds of `D`.

These are the infinitesimal symmetries and the invariants of `D`:

* the smooth vector fields preserving `D` form a Lie subalgebra of the Lie algebra of smooth vector
  fields (`TauCeti.distributionPreservingLieSubalgebra`), by the Jacobi identity
  `[[X, X'], Y] = [X, [X', Y]] - [X', [X, Y]]`;
* the smooth basic functions form a subalgebra of the smooth functions
  (`TauCeti.distributionBasicSubalgebra`), by the Leibniz rule for differentials;
* multiplying a vector field preserving `D` by a basic function gives a vector field preserving `D`
  (`TauCeti.PreservesDistribution.smul`), since `[aX, Y] = a[X, Y] - Y(a) X` and `Y(a) = 0`;
* when `D` is involutive, every differentiable vector field tangent to `D` preserves it
  (`TauCeti.IsInvolutiveDistribution.preservesDistribution`).

In geometric quantization, `D` is a real polarization of a symplectic manifold, the Hamiltonians
whose vector fields preserve `D` are the observables that act on polarized sections, and the
basic functions are the functions constant on the leaves of the polarization.

## References

* P. Molino, *Riemannian Foliations*, Progress in Mathematics 73, Birkhäuser, 1988, Chapter 2
  (foliate vector fields and basic functions).
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {X X' : Π x : M, TangentSpace I x}

/-! ### Basic functions -/

variable (I) in
/-- The **basic functions** of a distribution `D`: the smooth functions whose differential vanishes
on `D`, so that they are locally constant along the integral manifolds of `D`. They form a
subalgebra of the smooth functions. -/
def distributionBasicSubalgebra (D : Π x : M, Submodule ℝ (TangentSpace I x)) :
    Subalgebra ℝ C^∞⟮I, M; ℝ⟯ where
  carrier := {f | ∀ x, ∀ v ∈ D x, mvfderiv I f x v = 0}
  mul_mem' {f g} hf hg x v hv := by
    rw [Set.mem_ofPred_eq] at hf hg
    rw [ContMDiffMap.coe_mul, mvfderiv_mul f.mdifferentiableAt g.mdifferentiableAt]
    simp [hf x v hv, hg x v hv]
  add_mem' {f g} hf hg x v hv := by
    rw [Set.mem_ofPred_eq] at hf hg
    rw [ContMDiffMap.coe_add, mvfderiv_add f.mdifferentiableAt g.mdifferentiableAt]
    simp [hf x v hv, hg x v hv]
  algebraMap_mem' c x v _ := by
    rw [Algebra.algebraMap_eq_smul_one, ContMDiffMap.coe_smul, ContMDiffMap.coe_one]
    simp [Pi.smul_def, mvfderiv_const]

/-- A smooth function is basic for `D` exactly when its differential vanishes on `D`. -/
@[simp]
theorem mem_distributionBasicSubalgebra_iff {f : C^∞⟮I, M; ℝ⟯} :
    f ∈ distributionBasicSubalgebra I D ↔ ∀ x, ∀ v ∈ D x, mvfderiv I f x v = 0 :=
  Iff.rfl

variable [IsManifold I 1 M]

/-! ### Vector fields preserving a distribution -/

variable (I) in
/-- A vector field `X` **preserves** the distribution `D` when its Lie bracket with every local
smooth section of `D` is a section of `D`: whenever `Y` is a smooth vector field on an open set `U`
that is tangent to `D` on `U`, the bracket `[X, Y]` is tangent to `D` on `U`. -/
def PreservesDistribution (D : Π x : M, Submodule ℝ (TangentSpace I x))
    (X : Π x : M, TangentSpace I x) : Prop :=
  ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃Y : Π x : M, TangentSpace I x⦄, CMDiff[U] ∞ (T% Y) →
    (∀ x ∈ U, Y x ∈ D x) → ∀ x ∈ U, mlieBracket I X Y x ∈ D x

/-- The defining property of a vector field preserving a distribution. -/
theorem preservesDistribution_iff : PreservesDistribution I D X ↔
    ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃Y : Π x : M, TangentSpace I x⦄, CMDiff[U] ∞ (T% Y) →
      (∀ x ∈ U, Y x ∈ D x) → ∀ x ∈ U, mlieBracket I X Y x ∈ D x :=
  Iff.rfl

/-- The zero vector field preserves every distribution. -/
theorem preservesDistribution_zero : PreservesDistribution I D 0 := by
  intro U _ Y _ _ x _
  rw [mlieBracket_zero_left]
  exact (D x).zero_mem

namespace PreservesDistribution

/-- The opposite of a vector field preserving `D` preserves `D`. -/
theorem neg (h : PreservesDistribution I D X) : PreservesDistribution I D (-X) := by
  intro U hU Y hY hYD x hx
  rw [mlieBracket_neg_left]
  exact (D x).neg_mem (h hU hY hYD x hx)

/-- A constant multiple of a vector field preserving `D` preserves `D`. -/
theorem const_smul (h : PreservesDistribution I D X) (c : ℝ) :
    PreservesDistribution I D (c • X) := by
  intro U hU Y hY hYD x hx
  rw [mlieBracket_const_smul_left_field]
  exact (D x).smul_mem c (h hU hY hYD x hx)

/-- The sum of two differentiable vector fields preserving `D` preserves `D`. -/
theorem add [IsManifold I 2 M] [CompleteSpace E] (hXd : MDiff (T% X)) (hX'd : MDiff (T% X'))
    (h : PreservesDistribution I D X) (h' : PreservesDistribution I D X') :
    PreservesDistribution I D (X + X') := by
  intro U hU Y hY hYD x hx
  rw [mlieBracket_add_left (hXd x) (hX'd x)]
  exact (D x).add_mem (h hU hY hYD x hx) (h' hU hY hYD x hx)

/-- **Multiplication by a basic function.** If `X` is a differentiable vector field preserving `D`
and the differentiable function `a` is constant along `D`, in the sense that its differential
vanishes on `D`, then `a • X` preserves `D`: `[aX, Y] = a[X, Y] - Y(a) X` and `Y(a) = 0` for `Y`
tangent to `D`. -/
theorem smul [IsManifold I 2 M] [CompleteSpace E] {a : M → ℝ} (ha : MDiff a)
    (haD : ∀ x, ∀ v ∈ D x, mvfderiv I a x v = 0) (hXd : MDiff (T% X))
    (h : PreservesDistribution I D X) : PreservesDistribution I D (a • X) := by
  intro U hU Y hY hYD x hx
  rw [mlieBracket_smul_left (ha x) (hXd x), haD x _ (hYD x hx), neg_zero, zero_smul, zero_add]
  exact (D x).smul_mem _ (h hU hY hYD x hx)

/-- **The bracket of two vector fields preserving `D` preserves `D`.** For `Y` tangent to `D`, the
Jacobi identity gives `[[X, X'], Y] = [X, [X', Y]] - [X', [X, Y]]`, and both `[X', Y]` and
`[X, Y]` are again smooth sections of `D`. -/
theorem mlieBracket [IsManifold I ∞ M] [CompleteSpace E] (hXs : CMDiff ∞ (T% X))
    (hX's : CMDiff ∞ (T% X')) (h : PreservesDistribution I D X)
    (h' : PreservesDistribution I D X') : PreservesDistribution I D (mlieBracket I X X') := by
  have : IsManifold I (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((⊤ : ℕ∞) + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  -- The bracket of a smooth global field with a smooth section over `U` is smooth over `U`.
  have hbr : ∀ {Z : Π x : M, TangentSpace I x}, CMDiff ∞ (T% Z) → ∀ {U : Set M}, IsOpen U →
      ∀ {Y : Π x : M, TangentSpace I x}, CMDiff[U] ∞ (T% Y) →
        CMDiff[U] ∞ (T% (VectorField.mlieBracket I Z Y)) := fun hZ U hU Y hY y hy ↦
    ((hZ y).mlieBracket_vectorField (m := ⊤) (n := ⊤) (hY.contMDiffAt (hU.mem_nhds hy))
      (by simp)).contMDiffWithinAt
  intro U hU Y hY hYD x hx
  have hJ := leibniz_identity_mlieBracket_apply ((hXs x).of_le (by simp))
    ((hX's x).of_le (by simp)) ((hY.contMDiffAt (hU.mem_nhds hx)).of_le (by simp))
  rw [eq_sub_of_add_eq hJ.symm]
  exact (D x).sub_mem (h hU (hbr hX's hU hY) (h' hU hY hYD) x hx)
    (h' hU (hbr hXs hU hY) (h hU hY hYD) x hx)

end PreservesDistribution

/-- **Sections of an involutive distribution preserve it.** If `D` is involutive, every
differentiable vector field tangent to `D` preserves `D`. -/
theorem IsInvolutiveDistribution.preservesDistribution (hD : IsInvolutiveDistribution I D)
    (hXd : MDiff (T% X)) (hXD : ∀ x, X x ∈ D x) : PreservesDistribution I D X :=
  fun _ hU _ hY hYD ↦ isInvolutiveDistribution_iff.1 hD hU hXd.mdifferentiableOn
    (hY.mdifferentiableOn (by simp)) (fun x _ ↦ hXD x) hYD

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

variable (I) in
/-- The **Lie algebra of vector fields preserving a distribution** `D`: the smooth vector fields
`X` whose brackets with local smooth sections of `D` are sections of `D`, as a Lie subalgebra of
the Lie algebra of smooth vector fields. -/
def distributionPreservingLieSubalgebra (D : Π x : M, Submodule ℝ (TangentSpace I x)) :
    LieSubalgebra ℝ (LieAlgebroid.tangent I M).Sections where
  carrier := {X | PreservesDistribution I D ((LieAlgebroid.tangent I M).sectionsEquiv X)}
  add_mem' {X X'} hX hX' := by
    have hadd : ⇑((LieAlgebroid.tangent I M).sectionsEquiv (X + X')) =
        ⇑((LieAlgebroid.tangent I M).sectionsEquiv X) +
          ⇑((LieAlgebroid.tangent I M).sectionsEquiv X') := by
      rw [map_add, ContMDiffSection.coe_add]
    simp only [Set.mem_ofPred_eq, hadd]
    exact hX.add (ContMDiffSection.mdifferentiable _) (ContMDiffSection.mdifferentiable _) hX'
  zero_mem' := by
    simpa only [Set.mem_ofPred_eq, map_zero, ContMDiffSection.coe_zero] using
      preservesDistribution_zero
  smul_mem' c X hX := by
    have hsmul : ⇑((LieAlgebroid.tangent I M).sectionsEquiv (c • X)) =
        c • ⇑((LieAlgebroid.tangent I M).sectionsEquiv X) := by
      rw [LinearMapClass.map_smul_of_tower, ContMDiffSection.coe_smul]
    simp only [Set.mem_ofPred_eq, hsmul]
    exact hX.const_smul c
  lie_mem' {X X'} hX hX' := by
    have hbr : ⇑((LieAlgebroid.tangent I M).sectionsEquiv ⁅X, X'⁆) =
        mlieBracket I ((LieAlgebroid.tangent I M).sectionsEquiv X)
          ((LieAlgebroid.tangent I M).sectionsEquiv X') :=
      funext fun x ↦ by rw [LieAlgebroid.sectionsEquiv_lie, LieAlgebroid.tangent_bracket_apply]
    simp only [Set.mem_ofPred_eq, hbr]
    exact hX.mlieBracket (ContMDiffSection.contMDiff _) (ContMDiffSection.contMDiff _) hX'

/-- A smooth vector field lies in `distributionPreservingLieSubalgebra I D` exactly when it
preserves `D`. -/
@[simp]
theorem mem_distributionPreservingLieSubalgebra_iff {X : (LieAlgebroid.tangent I M).Sections} :
    X ∈ distributionPreservingLieSubalgebra I D ↔
      PreservesDistribution I D ((LieAlgebroid.tangent I M).sectionsEquiv X) :=
  Iff.rfl

end TauCeti
