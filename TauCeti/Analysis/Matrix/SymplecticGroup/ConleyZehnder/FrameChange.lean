/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.Analysis.Calculus.Deriv.Matrix
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

for every constant matrix `P` (`Matrix.hasDerivAt_inv_mul_mul_of_mem_symplecticGroup`), and `S′` is
symmetric when `S` is (`Matrix.IsSymm.transpose_mul_mul_add_transpose_mul_J_mul`). Both rest on
the linearized symplectic condition `g'ᵀ J g + gᵀ J g' = 0`
(`HasDerivAt.transpose_mul_J_mul_add_transpose_mul_J_mul_eq_zero`), obtained by differentiating
`gᵀ J g = J`. For paths in the symplectic subgroup of the general linear group, the extension of
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
* `HasDerivAt.transpose_mul_J_mul_add_transpose_mul_J_mul_eq_zero`: a path of symplectic matrices
  satisfies `g'ᵀ J g + gᵀ J g' = 0`.
* `Matrix.hasDerivAt_inv_mul_mul_of_mem_symplecticGroup`: the frame change transforms `Ψ' = J S Ψ`
  into `Ψ′' = J (gᵀ S g + gᵀ J g') Ψ′`.
* `Matrix.IsSymm.transpose_mul_mul_add_transpose_mul_J_mul`: the transformed matrix is symmetric.
* `TauCeti.GLSymplectic.hasDerivAt_frameChange_extend`: the same transformation for
  `TauCeti.GLSymplectic.frameChange`.

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
theorem frameChange_extend {A B C : GLSymplectic n ℝ} (g : Path A A) (Ψ : Path B C) (s : ℝ) :
    (frameChange g Ψ).extend s = (g.extend s)⁻¹ * Ψ.extend s * A :=
  (rfl)

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

section HamiltonianEquation

variable {𝕜 R n : Type*} [NontriviallyNormedField 𝕜] [CommRing R] [Fintype n] [DecidableEq n]

/-- **The linearized symplectic condition.** The derivative `g'` of a path `g` of symplectic
matrices satisfies `g'ᵀ J g + gᵀ J g' = 0`, the derivative of `gᵀ J g = J`. -/
theorem HasDerivAt.transpose_mul_J_mul_add_transpose_mul_J_mul_eq_zero
    {g : 𝕜 → Matrix (n ⊕ n) (n ⊕ n) 𝕜} {g' : Matrix (n ⊕ n) (n ⊕ n) 𝕜} {t : 𝕜}
    (hg' : HasDerivAt g g' t) (hg : ∀ᶠ s in 𝓝 t, g s ∈ symplecticGroup n 𝕜) :
    g'ᵀ * J n 𝕜 * g t + (g t)ᵀ * J n 𝕜 * g' = 0 := by
  have h₁ : HasDerivAt (fun s ↦ (g s)ᵀ * J n 𝕜 * g s)
      (g'ᵀ * J n 𝕜 * g t + (g t)ᵀ * J n 𝕜 * g') t :=
    (hg'.matrix_transpose.mul_const (J n 𝕜)).mul hg'
  have h₂ : HasDerivAt (fun s ↦ (g s)ᵀ * J n 𝕜 * g s) 0 t :=
    (hasDerivAt_const t (J n 𝕜)).congr_of_eventuallyEq
      (hg.mono fun s hs ↦ SymplecticGroup.mem_iff'.mp hs)
  exact h₁.unique h₂

namespace Matrix

/-- **The transformed Hamiltonian is symmetric.** If `S` is symmetric and `g'ᵀ J g + gᵀ J g' = 0`,
as for the derivative `g'` of a path `g` of symplectic matrices, then `gᵀ S g + gᵀ J g'` is
symmetric. -/
theorem IsSymm.transpose_mul_mul_add_transpose_mul_J_mul {S G G' : Matrix (n ⊕ n) (n ⊕ n) R}
    (hS : S.IsSymm) (h : G'ᵀ * J n R * G + Gᵀ * J n R * G' = 0) :
    (Gᵀ * S * G + Gᵀ * J n R * G').IsSymm := by
  have h' : G'ᵀ * (-J n R * G) = Gᵀ * J n R * G' := by
    rw [Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, neg_neg]
  rw [IsSymm, transpose_add, transpose_mul, transpose_mul, transpose_mul, transpose_mul,
    transpose_transpose, hS.eq, J_transpose, h', Matrix.mul_assoc, Matrix.mul_assoc]

/-- **Change of frame in the equation of a Hamiltonian path.** Let `g` be a path of symplectic
matrices with derivative `g'` at `t`, and let `Ψ` satisfy `Ψ' = J S Ψ` at `t`. Then for every
constant matrix `P` the path `g⁻¹ Ψ P` satisfies `(g⁻¹ Ψ P)' = J S′ (g⁻¹ Ψ P)` at `t`, with
`S′ = gᵀ S g + gᵀ J g'`. For `P = g(0)` this is the frame-changed path. -/
theorem hasDerivAt_inv_mul_mul_of_mem_symplecticGroup {g Ψ : 𝕜 → Matrix (n ⊕ n) (n ⊕ n) 𝕜}
    {g' S : Matrix (n ⊕ n) (n ⊕ n) 𝕜} {t : 𝕜} (hg : ∀ᶠ s in 𝓝 t, g s ∈ symplecticGroup n 𝕜)
    (hg' : HasDerivAt g g' t) (hΨ : HasDerivAt Ψ (J n 𝕜 * S * Ψ t) t)
    (P : Matrix (n ⊕ n) (n ⊕ n) 𝕜) :
    HasDerivAt (fun s ↦ (g s)⁻¹ * Ψ s * P)
      (J n 𝕜 * ((g t)ᵀ * S * g t + (g t)ᵀ * J n 𝕜 * g') * ((g t)⁻¹ * Ψ t * P)) t := by
  have hT := hg'.transpose_mul_J_mul_add_transpose_mul_J_mul_eq_zero hg
  have hgt : g t ∈ symplecticGroup n 𝕜 := hg.self_of_nhds
  have hinv : g t * (g t)⁻¹ = 1 := mul_nonsing_inv _ (SymplecticGroup.symplectic_det hgt)
  -- Near `t` the inverse of `g` is `-J gᵀ J`, which is differentiated by the product rule.
  have h₁ : HasDerivAt (fun s ↦ -J n 𝕜 * (g s)ᵀ * J n 𝕜 * Ψ s * P)
      ((-J n 𝕜 * g'ᵀ * J n 𝕜 * Ψ t + -J n 𝕜 * (g t)ᵀ * J n 𝕜 * (J n 𝕜 * S * Ψ t)) * P) t :=
    (((hg'.matrix_transpose.const_mul (-J n 𝕜)).mul_const (J n 𝕜)).mul hΨ).mul_const P
  refine (h₁.congr_deriv ?_).congr_of_eventuallyEq
    (hg.mono fun s hs ↦ by dsimp only; rw [SymplecticGroup.inv_eq_symplectic_inv _ hs])
  rw [SymplecticGroup.inv_eq_symplectic_inv _ hgt] at hinv ⊢
  set G := g t
  set K := -J n 𝕜 * Gᵀ * J n 𝕜
  have hT' : Gᵀ * J n 𝕜 * g' = -(g'ᵀ * J n 𝕜 * G) := eq_neg_of_add_eq_zero_right hT
  have e₁ : J n 𝕜 * (Gᵀ * S * G + Gᵀ * J n 𝕜 * g') * (K * Ψ t * P) =
      J n 𝕜 * Gᵀ * S * (G * K) * Ψ t * P + J n 𝕜 * (Gᵀ * J n 𝕜 * g') * K * Ψ t * P := by
    noncomm_ring
  have e₂ : (-J n 𝕜 * g'ᵀ * J n 𝕜 * Ψ t + K * (J n 𝕜 * S * Ψ t)) * P =
      -(J n 𝕜 * g'ᵀ * J n 𝕜 * Ψ t * P) - J n 𝕜 * Gᵀ * (J n 𝕜 * J n 𝕜) * S * Ψ t * P := by
    simp only [K]
    noncomm_ring
  have e₃ : J n 𝕜 * -(g'ᵀ * J n 𝕜 * G) * K * Ψ t * P =
      -(J n 𝕜 * g'ᵀ * J n 𝕜 * (G * K) * Ψ t * P) := by
    noncomm_ring
  rw [e₁, e₂, hinv, hT', e₃, hinv, J_squared]
  noncomm_ring

end Matrix

end HamiltonianEquation

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
      GLSymplectic.mem_iff_mem_symplecticGroup.mp (g.extend s).2) hg hΨ
    ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  simpa only [frameChange_extend, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
    coe_units_inv] using h

end TauCeti.GLSymplectic
