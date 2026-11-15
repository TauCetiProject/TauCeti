/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import TauCeti.CategoryTheory.Semisimple.Rigid
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Characters of the Grothendieck ring of a fusion category are ⋆-characters

Let `C` be a rigid monoidal category which is `k`-linear abelian and finite semisimple, over an
algebraically closed field `k`, with finite-dimensional morphism spaces and finitely many simple
classes. Its Grothendieck ring `TauCeti.SplitK0 C` carries the duality `[X] ↦ [Xᘁ]`. This file
shows that every ring homomorphism `ψ` from the Grothendieck ring to `ℝ` or `ℂ` intertwines the
duality with complex conjugation: `ψ [Xᘁ] = conj (ψ [X])`.

The proof is the common-eigenvector argument of Etingof–Gelaki–Nikshych–Ostrik. The vector
`v = (ψ [T])_T` of values of `ψ` on the simple classes is nonzero, since `ψ 1 = 1`, and it is an
eigenvector of the fusion matrix `N_S` of every simple class `S`, with eigenvalue `ψ [S]`
(`TauCeti.SplitK0.fusionMatrix_map_mulVec_ringHom`). Frobenius reciprocity says that the fusion
matrix of the dual class is the transpose, `N_{Sᘁ} = N_Sᵀ` (`TauCeti.fusionMatrix_dual`), and
since `N_S` has real entries this is its conjugate transpose. Pairing with `v` in the standard
Hermitian form gives `ψ [S] ‖v‖² = ⟨N_S v, v⟩ = ⟨v, N_{Sᘁ} v⟩ = conj (ψ [Sᘁ]) ‖v‖²`.

No pivotal structure and no simplicity of the tensor unit is needed: the duality is formed with
right duals, and Frobenius reciprocity holds for them in any rigid category.

For instance, a real-valued character takes the same value on `[X]` and on `[Xᘁ]`; and for a
complex-valued character `ψ (x * dual x) = ψ x * conj (ψ x)` is the squared absolute value of
`ψ x`, the input to the nonvanishing of the global dimension of a fusion category in
characteristic zero (Etingof–Nikshych–Ostrik).

## Main declarations

* `TauCeti.SplitK0.ringHom_apply_dual`: a ring homomorphism `ψ` from the Grothendieck ring to
  `ℝ` or `ℂ` satisfies `ψ (dual x) = conj (ψ x)`.
* `TauCeti.SplitK0.ringHom_apply_simpleBasis_dual`: the same identity on the basis of simple
  classes.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§3.3, 4.5
* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  proof of Theorem 2.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ComplexConjugate Matrix

namespace TauCeti

namespace SplitK0

universe w w' v u

variable (k : Type w') [Field k] [IsAlgClosed k] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [RigidCategory C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
  [EssentiallySmall.{w} C] [Finite (SimpleClasses C)]
  {𝕜 : Type*} [RCLike 𝕜]

-- The field `k` enters only through the Frobenius reciprocity of the fusion coefficients.
include k

-- The order on `𝕜` makes the standard Hermitian form positive definite.
open scoped ComplexOrder in
/-- A ring homomorphism `ψ` from the Grothendieck ring of a fusion category to `ℝ` or `ℂ` takes
the dual of a simple class to the complex conjugate: `ψ [Sᘁ] = conj (ψ [S])`. -/
theorem ringHom_apply_simpleBasis_dual (ψ : SplitK0 C →+* 𝕜) (S : SimpleClasses C) :
    ψ (simpleBasis C S.dual) = conj (ψ (simpleBasis C S)) := by
  have := Fintype.ofFinite (SimpleClasses C)
  set v : SimpleClasses C → 𝕜 := fun T ↦ ψ (simpleBasis C T)
  set A := (fusionMatrix k S).map (Nat.cast : ℕ → 𝕜)
  -- The fusion matrix has real entries, so its conjugate transpose is its transpose, which is
  -- the fusion matrix of the dual class by Frobenius reciprocity.
  have hA : Aᴴ = (fusionMatrix k S.dual).map Nat.cast := by
    ext T U
    simp [A]
  -- `v` is nonzero, since otherwise `ψ` would vanish on a basis, hence on `1`.
  have hv : v ≠ 0 := by
    simpa only [v, Function.comp_def] using (simpleBasis C).ringHom_comp_ne_zero ψ
  -- Pair the two eigenvector equations with `v` in the standard Hermitian form.
  have key : ψ (simpleBasis C S) * (star v ⬝ᵥ v) =
      conj (ψ (simpleBasis C S.dual)) * (star v ⬝ᵥ v) := by
    calc ψ (simpleBasis C S) * (star v ⬝ᵥ v)
        = star v ⬝ᵥ (A *ᵥ v) := by
          rw [fusionMatrix_map_mulVec_ringHom k ψ S, dotProduct_smul, smul_eq_mul]
      _ = star (Aᴴ *ᵥ v) ⬝ᵥ v := by
          rw [dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]
      _ = conj (ψ (simpleBasis C S.dual)) * (star v ⬝ᵥ v) := by
          rw [hA, fusionMatrix_map_mulVec_ringHom k ψ S.dual, star_smul, smul_dotProduct,
            smul_eq_mul, RCLike.star_def]
  rw [mul_left_inj' (mt dotProduct_star_self_eq_zero.1 hv)] at key
  rw [key, RCLike.conj_conj]

/-- **Characters of the Grothendieck ring are ⋆-characters.** A ring homomorphism `ψ` from the
Grothendieck ring of a fusion category to `ℝ` or `ℂ` intertwines the duality `[X] ↦ [Xᘁ]` with
complex conjugation. -/
theorem ringHom_apply_dual (ψ : SplitK0 C →+* 𝕜) (x : SplitK0 C) :
    ψ (dual x) = conj (ψ x) := by
  have h : ((ψ : SplitK0 C →+ 𝕜).comp dual).toIntLinearMap =
      ((starRingEnd 𝕜 : 𝕜 →+ 𝕜).comp ψ).toIntLinearMap :=
    (simpleBasis C).ext fun S ↦ by
      simpa [dual_simpleBasis] using ringHom_apply_simpleBasis_dual k ψ S
  simpa using LinearMap.congr_fun h x

end SplitK0

end TauCeti
