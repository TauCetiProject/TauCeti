/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.BasicFunctions
public import TauCeti.Geometry.Symplectic.Hamiltonian.LieAlgebra
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive

/-!
# Observables preserving a polarization

In geometric quantization only the functions whose Hamiltonian flows preserve the polarization
`P` are quantized directly on the polarized sections. Infinitesimally, the Hamiltonian vector field
`X_f` of `f` **preserves** a distribution `P` when `[X_f, Y]` is tangent to `P` for every smooth
local vector field `Y` tangent to `P`, that is `[X_f, Γ_loc(P)] ⊆ Γ_loc(P)`
(`TauCeti.SmoothTwoForm.PreservesDistribution`).

* For any distribution `P` of a symplectic manifold, the smooth functions preserving `P` form a
  Lie subalgebra of the Poisson Lie algebra containing the constants
  (`TauCeti.SmoothTwoForm.observableLieSubalgebra`). Bracket closure comes from
  `X_{{f, g}} = -[X_f, X_g]` and the Jacobi identity
  `[[X_f, X_g], Y] = [X_f, [X_g, Y]] - [X_g, [X_f, Y]]` for vector fields.
* For a real polarization `P`, or more generally an involutive distribution with coisotropic
  fibres, the Hamiltonian vector field of a basic function `a` (`TauCeti.basicFunctions`, `da`
  vanishes on `P`) is tangent to `P`, since `σ(X_a, v) = da(v)` vanishes on `P` and `P^σ ⊆ P`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_mem_of_mem_basicFunctions`). By
  involutivity basic functions preserve `P`.
* For such `P`, the observables form a module over the basic functions under pointwise
  multiplication (`TauCeti.SmoothTwoForm.IsNondegenerate.observableSubmodule`):
  by `X_{af} = a X_f + f X_a` and the Leibniz rule for the Lie bracket,
  `[X_{af}, Y] = a [X_f, Y] - Y(a) X_f + f [X_a, Y] - Y(f) X_a`, where `Y(a) = 0` and the other
  three vectors lie in `P`.

Nothing here asserts closure of the observables under pointwise multiplication, which fails in
general: for the vertical polarization `P = span{∂_p}` of `T*ℝ`, `p` preserves `P` but `p²` does
not, since `[X_{p²}, ∂_p] = -2 ∂_q`.

## Main definitions

* `TauCeti.SmoothTwoForm.PreservesDistribution σ P f`: the Hamiltonian vector field of `f`
  preserves `P`.
* `TauCeti.SmoothTwoForm.observableLieSubalgebra σ P hσ`: the Lie subalgebra of the Poisson Lie
  algebra of functions preserving `P`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.observableSubmodule`: for an involutive distribution `P`
  with coisotropic fibres, such as a real polarization, the functions preserving `P` as a module
  over the basic functions of `P`.

## Main results

* `TauCeti.SmoothTwoForm.PreservesDistribution.poissonBracket`: the Poisson bracket of two
  functions preserving `P` preserves `P`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.preservesDistribution_of_mem_basicFunctions`: basic
  functions preserve an involutive coisotropic distribution, such as a real polarization.
* `TauCeti.SmoothTwoForm.IsNondegenerate.preservesDistribution_mul_of_mem_basicFunctions`: the
  product of a basic function and a function preserving such a distribution preserves it.
* `SmoothTwoForm.symm_poissonLieAlgebraEquiv_mem_observableLieSubalgebra_of_mem_basicFunctions`
  (in `TauCeti`): basic functions are observables.

## References

* M. Schottenloher, *Geometric Quantization*, lecture notes, version 15.6, Section 9.
* N. M. J. Woodhouse, *Geometric Quantization*, 2nd ed., Oxford, 1992, Sections 5.7 and 8.4.
-/

public section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {P : Π x : M, Submodule ℝ (TangentSpace I x)} {f g : M → ℝ}

/-! ### Hamiltonians preserving a distribution -/

variable (σ P) in
/-- The Hamiltonian vector field of `f` **preserves** the distribution `P` when its Lie bracket
with every smooth vector field tangent to `P` on an open set is tangent to `P` on that set:
`[X_f, Γ_loc(P)] ⊆ Γ_loc(P)`. -/
def PreservesDistribution (f : M → ℝ) : Prop :=
  ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃Y : Π x : M, TangentSpace I x⦄, CMDiff[U] ∞ (T% Y) →
    (∀ x ∈ U, Y x ∈ P x) → ∀ x ∈ U, mlieBracket I (σ.hamiltonianVectorField f) Y x ∈ P x

/-- The defining property of a Hamiltonian preserving a distribution. -/
theorem preservesDistribution_iff : σ.PreservesDistribution P f ↔
    ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃Y : Π x : M, TangentSpace I x⦄, CMDiff[U] ∞ (T% Y) →
      (∀ x ∈ U, Y x ∈ P x) → ∀ x ∈ U, mlieBracket I (σ.hamiltonianVectorField f) Y x ∈ P x :=
  Iff.rfl

/-- The Hamiltonian vector field of a constant vanishes, so it preserves every distribution. -/
theorem preservesDistribution_const (c : ℝ) : σ.PreservesDistribution P fun _ ↦ c := by
  intro U _ Y _ _ x _
  rw [hamiltonianVectorField_const, mlieBracket_zero_left]
  exact zero_mem _

/-- The zero function preserves every distribution. -/
theorem preservesDistribution_zero : σ.PreservesDistribution P 0 :=
  preservesDistribution_const 0

namespace PreservesDistribution

/-- A constant multiple of a function preserving `P` preserves `P`. -/
theorem const_smul (hf : σ.PreservesDistribution P f) (c : ℝ) :
    σ.PreservesDistribution P (c • f) := by
  intro U hU Y hY hYP x hx
  have hX : σ.hamiltonianVectorField (c • f) = c • σ.hamiltonianVectorField f :=
    funext fun y ↦ hamiltonianVectorField_const_smul c y
  rw [hX, mlieBracket_const_smul_left_field]
  exact Submodule.smul_mem _ c (hf hU hY hYP x hx)

/-- The opposite of a function preserving `P` preserves `P`. -/
theorem neg (hf : σ.PreservesDistribution P f) : σ.PreservesDistribution P (-f) := by
  simpa using hf.const_smul (-1)

variable [FiniteDimensional ℝ E] (hσ : σ.IsNondegenerate)
include hσ

/-- The sum of two `C²` functions preserving `P` preserves `P`. -/
theorem add (hf2 : ContMDiff I 𝓘(ℝ) 2 f) (hg2 : ContMDiff I 𝓘(ℝ) 2 g)
    (hf : σ.PreservesDistribution P f) (hg : σ.PreservesDistribution P g) :
    σ.PreservesDistribution P (f + g) := by
  intro U hU Y hY hYP x hx
  have hX : σ.hamiltonianVectorField (f + g) =
      σ.hamiltonianVectorField f + σ.hamiltonianVectorField g :=
    funext fun y ↦ hamiltonianVectorField_add ((hf2 y).mdifferentiableAt two_ne_zero)
      ((hg2 y).mdifferentiableAt two_ne_zero)
  rw [hX, mlieBracket_add_left (hσ.mdifferentiable_hamiltonianVectorField hf2 x)
    (hσ.mdifferentiable_hamiltonianVectorField hg2 x)]
  exact add_mem (hf hU hY hYP x hx) (hg hU hY hYP x hx)

end PreservesDistribution

variable [FiniteDimensional ℝ E]

/-- **Bracket closure.** For a symplectic form, the Poisson bracket of two smooth functions
preserving a distribution `P` preserves `P`: `X_{{f, g}} = -[X_f, X_g]`, and by the Jacobi identity
`[[X_f, X_g], Y] = [X_f, [X_g, Y]] - [X_g, [X_f, Y]]` is tangent to `P` whenever `Y` is. -/
theorem PreservesDistribution.poissonBracket (hσ : σ.IsSymplectic) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hgs : ContMDiff I 𝓘(ℝ) ∞ g) (hf : σ.PreservesDistribution P f)
    (hg : σ.PreservesDistribution P g) :
    σ.PreservesDistribution P (σ.poissonBracket f g) := by
  intro U hU Y hY hYP x hx
  have : IsManifold I (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hXf := hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl (by simpa using hfs)
  have hXg := hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl (by simpa using hgs)
  have hYat {y : M} (hy : y ∈ U) : CMDiffAt ∞ (T% Y) y := (hY y hy).contMDiffAt (hU.mem_nhds hy)
  -- The brackets `[X_f, Y]` and `[X_g, Y]` are again smooth on `U` and tangent to `P` there.
  have hbr {Z : Π x : M, TangentSpace I x} (hZ : CMDiff ∞ (T% Z)) :
      CMDiff[U] ∞ (T% (mlieBracket I Z Y)) := fun y hy ↦
    (ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤) (hZ y) (hYat hy)
      (by simp)).contMDiffWithinAt
  rw [hσ.isNondegenerate.hamiltonianVectorField_poissonBracket hσ.isClosed (hfs.of_le (by simp))
    (hgs.of_le (by simp)), mlieBracket_neg_left]
  have hJ := leibniz_identity_mlieBracket_apply (I := I) ((hXf x).of_le (by simp))
    ((hXg x).of_le (by simp)) ((hYat hx).of_le (by simp))
  rw [eq_sub_of_add_eq hJ.symm]
  exact neg_mem (sub_mem (hf hU (hbr hXg) (hg hU hY hYP) x hx)
    (hg hU (hbr hXf) (hf hU hY hYP) x hx))

/-! ### The Lie algebra of observables -/

variable (σ P) in
/-- The **observables** of a distribution `P` of a symplectic manifold: the smooth functions whose
Hamiltonian vector fields preserve `P`, as a Lie subalgebra of the Poisson Lie algebra. -/
def observableLieSubalgebra (hσ : σ.IsSymplectic) : LieSubalgebra ℝ (σ.PoissonLieAlgebra hσ) where
  carrier := {f | σ.PreservesDistribution P (σ.poissonLieAlgebraEquiv hσ f)}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, map_add, ContMDiffMap.coe_add] at hf hg ⊢
    exact hf.add hσ.isNondegenerate ((σ.poissonLieAlgebraEquiv hσ f).contMDiff.of_le (by simp))
      ((σ.poissonLieAlgebraEquiv hσ g).contMDiff.of_le (by simp)) hg
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, ContMDiffMap.coe_zero]
    exact preservesDistribution_zero
  smul_mem' c f hf := by
    simp only [Set.mem_ofPred_eq, map_smul, ContMDiffMap.coe_smul] at hf ⊢
    exact hf.const_smul c
  lie_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, coe_poissonLieAlgebraEquiv_lie] at hf hg ⊢
    exact hf.poissonBracket hσ (σ.poissonLieAlgebraEquiv hσ f).contMDiff
      (σ.poissonLieAlgebraEquiv hσ g).contMDiff hg

/-- A function is an observable of `P` when its Hamiltonian vector field preserves `P`. -/
@[simp]
theorem mem_observableLieSubalgebra_iff {hσ : σ.IsSymplectic} {f : σ.PoissonLieAlgebra hσ} :
    f ∈ σ.observableLieSubalgebra P hσ ↔
      σ.PreservesDistribution P (σ.poissonLieAlgebraEquiv hσ f) :=
  Iff.rfl

/-- The constants are observables of every distribution. -/
theorem const_mem_observableLieSubalgebra (hσ : σ.IsSymplectic) (c : ℝ) :
    (σ.poissonLieAlgebraEquiv hσ).symm (ContMDiffMap.const c) ∈ σ.observableLieSubalgebra P hσ := by
  rw [mem_observableLieSubalgebra_iff, LinearEquiv.apply_symm_apply]
  exact preservesDistribution_const c

/-! ### Basic functions and the module of observables

The results of this section hold for an involutive distribution `P` whose fibres are coisotropic,
`P_x^σ ⊆ P_x`. A real polarization is such a distribution
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsRealPolarization.isCoisotropic`,
`TauCeti.SmoothTwoForm.IsNondegenerate.IsRealPolarization.isInvolutive`). -/

namespace IsNondegenerate

variable {hσ : σ.IsNondegenerate}

/-- **The Hamiltonian vector field of a basic function is tangent to a coisotropic distribution**,
for instance a real polarization. -/
theorem hamiltonianVectorField_mem_of_mem_basicFunctions {x : M}
    (hPx : (hσ.symplecticFormAt x).IsCoisotropic (P x)) {a : C^∞⟮I, M; ℝ⟯}
    (ha : a ∈ basicFunctions I P) : σ.hamiltonianVectorField a x ∈ P x :=
  hσ.hamiltonianVectorField_mem_of_forall_mvfderiv_eq_zero hPx fun _ hv ↦
    mvfderiv_apply_eq_zero_of_mem_basicFunctions ha hv

/-- **Basic functions preserve an involutive coisotropic distribution**, for instance a real
polarization. The Hamiltonian vector field of a basic function is tangent to the distribution, so
involutivity makes its bracket with a vector field tangent to the distribution tangent to it. -/
theorem preservesDistribution_of_mem_basicFunctions
    (hP : ∀ x, (hσ.symplecticFormAt x).IsCoisotropic (P x)) (hPi : IsInvolutiveDistribution I P)
    {a : C^∞⟮I, M; ℝ⟯} (ha : a ∈ basicFunctions I P) : σ.PreservesDistribution P a :=
  fun _ hU _ hY hYP _ hx ↦ hPi.mlieBracket_mem hU
    (hσ.mdifferentiable_hamiltonianVectorField (a.contMDiff.of_le (by simp))).mdifferentiableOn
    (hY.mdifferentiableOn (by simp))
    (fun y _ ↦ hamiltonianVectorField_mem_of_mem_basicFunctions (hP y) ha) hYP hx

/-- **The observables of an involutive coisotropic distribution are a module over its basic
functions.** For a real polarization these are the observables and the basic functions of
geometric quantization. The product of a basic function `a` and a function `f` preserving the
distribution preserves it: `[X_{af}, Y] = a [X_f, Y] - Y(a) X_f + f [X_a, Y] - Y(f) X_a`, where
`Y(a) = 0` and the three other vectors lie in the distribution. -/
theorem preservesDistribution_mul_of_mem_basicFunctions
    (hP : ∀ x, (hσ.symplecticFormAt x).IsCoisotropic (P x)) (hPi : IsInvolutiveDistribution I P)
    {a f : C^∞⟮I, M; ℝ⟯} (ha : a ∈ basicFunctions I P)
    (hf : σ.PreservesDistribution P f) : σ.PreservesDistribution P ⇑(a * f) := by
  intro U hU Y hY hYP x hx
  have ha1 : MDiff a := a.contMDiff.mdifferentiable (by simp)
  have hf1 : MDiff f := f.contMDiff.mdifferentiable (by simp)
  have hXa := hσ.mdifferentiable_hamiltonianVectorField (a.contMDiff.of_le (by simp))
  have hXf := hσ.mdifferentiable_hamiltonianVectorField (f.contMDiff.of_le (by simp))
  have hX : σ.hamiltonianVectorField ⇑(a * f) =
      ⇑a • σ.hamiltonianVectorField f + ⇑f • σ.hamiltonianVectorField a :=
    funext fun y ↦ by
      rw [ContMDiffMap.coe_mul, hamiltonianVectorField_mul (ha1 y) (hf1 y), Pi.add_apply,
        Pi.smul_apply', Pi.smul_apply']
  rw [hX, mlieBracket_add_left ((ha1 x).smul_section (hXf x)) ((hf1 x).smul_section (hXa x)),
    mlieBracket_smul_left (ha1 x) (hXf x), mlieBracket_smul_left (hf1 x) (hXa x),
    mvfderiv_apply_eq_zero_of_mem_basicFunctions ha (hYP x hx), neg_zero, zero_smul, zero_add]
  have hXaP := hamiltonianVectorField_mem_of_mem_basicFunctions (hP x) ha
  have hbrP := preservesDistribution_of_mem_basicFunctions hP hPi ha hU hY hYP x hx
  exact add_mem (Submodule.smul_mem _ _ (hf hU hY hYP x hx))
    (add_mem (Submodule.smul_mem _ _ hXaP) (Submodule.smul_mem _ _ hbrP))

variable (hσ) in
/-- The **module of observables** of an involutive distribution `P` with coisotropic fibres, such
as a real polarization: the smooth functions whose Hamiltonian vector fields preserve `P`, as a
module over the basic functions of `P` under pointwise multiplication. -/
def observableSubmodule (hP : ∀ x, (hσ.symplecticFormAt x).IsCoisotropic (P x))
    (hPi : IsInvolutiveDistribution I P) : Submodule (basicFunctions I P) C^∞⟮I, M; ℝ⟯ where
  carrier := {f | σ.PreservesDistribution P f}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ContMDiffMap.coe_add] at hf hg ⊢
    exact hf.add hσ (f.contMDiff.of_le (by simp)) (g.contMDiff.of_le (by simp)) hg
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ContMDiffMap.coe_zero]
    exact preservesDistribution_zero
  smul_mem' a f hf := by
    rw [Set.mem_ofPred_eq, Subalgebra.smul_def, smul_eq_mul]
    exact preservesDistribution_mul_of_mem_basicFunctions hP hPi a.2 hf

/-- A smooth function lies in the module of observables when its Hamiltonian vector field
preserves the distribution. -/
@[simp]
theorem mem_observableSubmodule_iff {hP : ∀ x, (hσ.symplecticFormAt x).IsCoisotropic (P x)}
    {hPi : IsInvolutiveDistribution I P} {f : C^∞⟮I, M; ℝ⟯} :
    f ∈ hσ.observableSubmodule hP hPi ↔ σ.PreservesDistribution P f :=
  Iff.rfl

end IsNondegenerate

/-- For an involutive distribution `P` with coisotropic fibres, such as a real polarization of a
symplectic form, the basic functions of `P` are observables of `P`. -/
theorem symm_poissonLieAlgebraEquiv_mem_observableLieSubalgebra_of_mem_basicFunctions
    (hσ : σ.IsSymplectic) (hP : ∀ x, (hσ.isNondegenerate.symplecticFormAt x).IsCoisotropic (P x))
    (hPi : IsInvolutiveDistribution I P) {a : C^∞⟮I, M; ℝ⟯} (ha : a ∈ basicFunctions I P) :
    (σ.poissonLieAlgebraEquiv hσ).symm a ∈ σ.observableLieSubalgebra P hσ := by
  rw [mem_observableLieSubalgebra_iff, LinearEquiv.apply_symm_apply]
  exact IsNondegenerate.preservesDistribution_of_mem_basicFunctions hP hPi ha

end SmoothTwoForm

end TauCeti
