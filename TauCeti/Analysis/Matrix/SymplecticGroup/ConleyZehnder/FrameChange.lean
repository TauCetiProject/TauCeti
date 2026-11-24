/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.Analysis.Calculus.Deriv.SymplecticGroup
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Naturality
public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov

/-!
# Change of frame for the Conley–Zehnder index

Let `Φ(t)` be a path of linear symplectic maps between the fibres of a symplectic vector bundle
over `[0, 1]`, for instance the linearized flow along a closed orbit of a Hamiltonian, and let
`e(t)` be a symplectic frame of the fibres. In this frame `Φ` is the path of symplectic matrices
`Ψ(t) = e(t)⁻¹ Φ(t) e(0)`. Another frame `e′(t) = e(t) g(t)` differs from `e` by a path `g` of
symplectic matrices, and when both frames are frames of a bundle over a circle, `g` is a loop.
In the new frame the path becomes the coordinate path

`Ψ′(t) = g(t)⁻¹ Ψ(t) g(0)`

(`TauCeti.GLSymplectic.frameChange`), and its Conley–Zehnder index changes by twice the Maslov
index of the loop `g`:

`CZ(Ψ′) = CZ(Ψ) + 2 μ(g)`

(`TauCeti.GLSymplectic.conleyZehnderIndex_frameChange`). For a loop `g` of unitary matrices `μ(g)`
is the winding number of `det g` (`TauCeti.GLSymplectic.maslovIndex_map_ofUnitary`), so this is the
law `CZ_(e′) = CZ_e + 2 wind(det g)`. The proof writes `Ψ′` as the product of the loop
`t ↦ g(t)⁻¹ g(0)`, based at the identity, with the conjugate `g(0)⁻¹ Ψ g(0)` of `Ψ`. The loop
axiom `TauCeti.GLSymplectic.conleyZehnderIndex_mul` accounts for the first factor, since the
Maslov index of the pointwise inverse of a loop is minus its Maslov index, and naturality
`TauCeti.GLSymplectic.conleyZehnderIndex_map_conj` removes the conjugation.

The Conley–Zehnder index of an asymptotic operator `-J ∂ₜ - S(t)` is that of the path solving
`Ψ' = J S Ψ`, `Ψ(0) = 1`. The frame change transforms this equation: if `g` is a differentiable
path of symplectic matrices and `Ψ' = J S Ψ`, then `Ψ′ = g⁻¹ Ψ P` satisfies

`Ψ′' = J S′ Ψ′`, `S′ = gᵀ S g + gᵀ J g'`

for every constant matrix `P` (`Matrix.hasDerivAt_inv_mul_mul_of_mem_symplecticGroup`, in
`TauCeti.Analysis.Calculus.Deriv.SymplecticGroup`), and `S′` is symmetric when `S` is
(`Matrix.IsSymm.transpose_mul_mul_add_transpose_mul_J_mul`, in
`TauCeti.LinearAlgebra.SymplecticGroup`). Both rest on the linearized symplectic condition
`g'ᵀ J g + gᵀ J g' = 0`, obtained by differentiating `gᵀ J g = J`. For paths in the symplectic
subgroup of the general linear group, the extension of
`TauCeti.GLSymplectic.frameChange` to `ℝ` satisfies the transformed equation
(`TauCeti.GLSymplectic.hasDerivAt_frameChange_extend`). So changing the frame of an asymptotic
operator along a loop `g` replaces `S` by `S′` and changes its Conley–Zehnder index by `2 μ(g)`.

The matrix `J` is Mathlib's `Matrix.J`, the symplectic group is defined by `A J Aᵀ = J`, and the
Conley–Zehnder index is `TauCeti.GLSymplectic.conleyZehnderIndex`, minus the Robbin–Salamon index
of the graphs.

## Main definitions

* `TauCeti.GLSymplectic.frameChange`: the coordinate path `t ↦ g(t)⁻¹ Ψ(t) g(0)` of a path `Ψ`
  after the change of frame by a loop `g`.

## Main results

* `TauCeti.GLSymplectic.conleyZehnderIndex_frameChange`: `CZ(g⁻¹ Ψ g(0)) = CZ(Ψ) + 2 μ(g)`.
* `TauCeti.GLSymplectic.hasDerivAt_frameChange_extend`: the frame change transforms `Ψ' = J S Ψ`
  into `Ψ′' = J (gᵀ S g + gᵀ J g') Ψ′`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Appendix C.3 (the Conley–Zehnder index of an
  asymptotic operator and its dependence on the trivialization).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the loop axiom and the change of trivialization).
-/

public section

open Matrix
open scoped unitInterval Topology Matrix.Norms.Operator

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The path `Ψ` read in a frame changed by the loop `g`: the coordinate path
`t ↦ g(t)⁻¹ Ψ(t) g(0)`. If `Ψ(t) = e(t)⁻¹ Φ(t) e(0)` in a frame `e`, this is
`e′(t)⁻¹ Φ(t) e′(0)` in the frame `e′(t) = e(t) g(t)`. -/
def frameChange {A B C : GLSymplectic n ℝ} (g : Path A A) (Ψ : Path B C) :
    Path (A⁻¹ * B * A) (A⁻¹ * C * A) where
  toFun t := (g t)⁻¹ * Ψ t * A
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- The frame-changed path at time `t` is `g(t)⁻¹ Ψ(t) g(0)`. -/
@[simp]
theorem frameChange_apply {A B C : GLSymplectic n ℝ} (g : Path A A) (Ψ : Path B C) (t : I) :
    frameChange g Ψ t = (g t)⁻¹ * Ψ t * A :=
  (rfl)

/-- The extension of the frame-changed path to `ℝ` is the frame change of the extensions. -/
@[simp]
theorem frameChange_extend {A B C : GLSymplectic n ℝ} (g : Path A A) (Ψ : Path B C) (s : ℝ) :
    (frameChange g Ψ).extend s = (g.extend s)⁻¹ * Ψ.extend s * A := by
  simp only [Path.extend, ContinuousMap.coe_mk, Set.IccExtend_apply, frameChange_apply]

/-- **Change of frame for the Conley–Zehnder index.** Reading a path `Ψ` of symplectic matrices in
a frame changed by a loop `g` of symplectic matrices, that is, passing to the coordinate path
`t ↦ g(t)⁻¹ Ψ(t) g(0)`, adds twice the Maslov index of `g` to its Conley–Zehnder index. -/
theorem conleyZehnderIndex_frameChange {A B C : GLSymplectic n ℝ} (g : Path A A)
    (Ψ : Path B C) :
    conleyZehnderIndex (frameChange g Ψ) = conleyZehnderIndex Ψ + 2 * maslovIndex g := by
  -- The loop `t ↦ g(t)⁻¹ g(0)`, based at the identity.
  let φ : Path (1 : GLSymplectic n ℝ) 1 :=
    (g.inv.mul (Path.refl A)).cast (inv_mul_cancel A).symm (inv_mul_cancel A).symm
  have hφ : maslovIndex φ = -maslovIndex g := by
    have h : maslovIndex φ = maslovIndex (g.inv.mul (Path.refl A)) := by
      rw [maslovIndex_def, maslovIndex_def]
      exact Circle.degree_congr _ _ fun t ↦ by simp [φ]
    rw [h, maslovIndex_mul, maslovIndex_inv, maslovIndex_refl, add_zero]
  -- The frame-changed path is `φ` times the conjugate `g(0)⁻¹ Ψ g(0)` of `Ψ`.
  let δ := Ψ.map (f := fun X ↦ A⁻¹ * X * A⁻¹⁻¹) (by fun_prop)
  have h : conleyZehnderIndex (frameChange g Ψ) = conleyZehnderIndex (φ.mul δ) :=
    conleyZehnderIndex_congr _ _ fun t ↦ by simp [φ, δ, mul_assoc]
  rw [h, conleyZehnderIndex_mul, conleyZehnderIndex_map_conj, hφ]
  push_cast
  ring

end TauCeti.GLSymplectic

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Change of frame in the equation of a Hamiltonian path**, for paths in the symplectic
subgroup of the general linear group. If the extension of `Ψ` to `ℝ` satisfies `Ψ' = J S Ψ` at
`t` and the extension of the loop `g` has derivative `g'` there, then the extension of the
frame-changed path `TauCeti.GLSymplectic.frameChange g Ψ` satisfies `Ψ′' = J S′ Ψ′` at `t`, with
`S′ = gᵀ S g + gᵀ J g'`. Its Conley–Zehnder index is
`TauCeti.GLSymplectic.conleyZehnderIndex_frameChange`. -/
theorem hasDerivAt_frameChange_extend {A B C : GLSymplectic n ℝ} (g : Path A A) (Ψ : Path B C)
    {g' S : Matrix (n ⊕ n) (n ⊕ n) ℝ} {t : ℝ}
    (hg : HasDerivAt (fun s ↦ ((g.extend s : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) g' t)
    (hΨ : HasDerivAt (fun s ↦ ((Ψ.extend s : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))
      (J n ℝ * S * ((Ψ.extend t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) t) :
    HasDerivAt
      (fun s ↦ (((frameChange g Ψ).extend s : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))
      (J n ℝ * ((((g.extend t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᵀ * S *
          ((g.extend t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) +
        (((g.extend t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᵀ * J n ℝ * g') *
        (((frameChange g Ψ).extend t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) t := by
  have h := hasDerivAt_inv_mul_mul_of_mem_symplecticGroup
    (Filter.Eventually.of_forall fun s ↦
      GLSymplectic.mem_iff_mem_symplecticGroup.mp (g.extend s).property) hg hΨ
    ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  simpa only [frameChange_extend, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
    coe_units_inv] using h

end TauCeti.GLSymplectic
