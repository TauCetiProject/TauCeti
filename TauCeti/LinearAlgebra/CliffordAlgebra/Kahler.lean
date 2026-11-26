/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.TorusCharacter
import TauCeti.LinearAlgebra.Eigenspace.Involution
import TauCeti.LinearAlgebra.End.Restrict

/-!
# The Clifford action of the Kähler form

Let `J` be an orthogonal complex structure on a finite-dimensional real inner product space `V`,
with Kähler two-vector `ω` (`TauCeti.AlmostComplexStructure.kahlerForm`). For the quadratic form
`Q v = -‖v‖²`, write `c = CliffordAlgebra.ι Q` and `c₂ = CliffordAlgebra.bivectorExterior Q` for
Clifford multiplication by vectors and by two-forms.

The commutator of the Clifford image of any two-vector `F` with a generator is the Clifford image
of the contraction `v ⌟ F` (`TauCeti.twoVectorContraction`): `⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)`
(`TauCeti.bivectorExterior_lie_ι_of_eq_neg_norm_sq`). For the Kähler two-vector `v ⌟ ω = J v`
(`TauCeti.AlmostComplexStructure.twoVectorContraction_kahlerForm`), so the commutator of `c₂(ω)`
with a generator is the Clifford image of `J`: `⁅c₂(ω), c(v)⁆ = 2 c(J v)`. On a Clifford module
this is how the eigenspaces of `c₂(ω)` see `J`.
For instance, on Taubes's canonical line, the `-2i`-eigenline of `c₂(ω)` in the positive
half-spinors of a four-dimensional spin module, `v ↦ c(v) u` turns `J` into multiplication by `i`
(`TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_self`).

In dimension four, with a unitary frame `(e₀, e₁, e₂, e₃)`, `J e₀ = e₁` and `J e₂ = e₃`, the
Kähler two-vector is `ω = e₀ ∧ e₁ + e₂ ∧ e₃`, and `c₂` sends it to `c(e₀) c(e₁) + c(e₂) c(e₃)`.

On any complex Clifford module `W`, with `c(v) = ρ (ι Q v)`, this pins down Clifford multiplication
on the eigenvectors of `c₂(ω)`, with no Hermitian structure, chirality or orientation assumed. On
`ψ ∈ W` with `c₂(ω) ψ = μ ψ`, `μ ≠ 0`, the commuting square roots of `-1` `c(e₀) c(e₁)` and
`c(e₂) c(e₃)` both act by `μ / 2`, so `2 c(J v) ψ = -μ c(v) ψ`. The canonical eigenspace is the
`-2i`-eigenspace of `c₂(ω)`, which contains Taubes's canonical line. In the basis `(e₀, e₂)` of
the complex vector space `(V, J)` (`TauCeti.AlmostComplexStructure.basisOfOrthonormalBasisFinFour`),
with coordinates `z₀(v) = ⟪e₀, v⟫ + i ⟪e₁, v⟫` and `z₂(v) = ⟪e₂, v⟫ + i ⟪e₃, v⟫`, a canonical
eigenvector `ψ` satisfies `c(v) ψ = z₀(v) c(e₀) ψ + z₂(v) c(e₂) ψ` and

`c(v) c(w) ψ = (z₀(v) z₂(w) - z₂(v) z₀(w)) c(e₀) c(e₂) ψ - (⟪v, w⟫ - i ⟪v, J w⟫) ψ`,

where `c(e₀) c(e₂) ψ` lies in the `2i`-eigenspace.

## Main results

* `TauCeti.AlmostComplexStructure.bivectorExterior_kahlerForm`:
  `c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)` in a unitary frame.
* `TauCeti.AlmostComplexStructure.ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply_eq_smul`,
  `TauCeti.AlmostComplexStructure.bivectorExterior_apply_eq_smul_of_ι_one_apply_of_ι_three_apply`,
  and `TauCeti.AlmostComplexStructure.two_smul_ι_apply_apply_of_bivectorExterior_apply_eq_smul`:
  `c(e₁) ψ = -(μ / 2) c(e₀) ψ`, `c(e₃) ψ = -(μ / 2) c(e₂) ψ` and `2 c(J v) ψ = -μ c(v) ψ` for
  `c₂(ω) ψ = μ ψ` with `μ ≠ 0`, and conversely `c(e₁) ψ = μ c(e₀) ψ`, `c(e₃) ψ = μ c(e₂) ψ` imply
  `c₂(ω) ψ = (-2 μ) ψ`.
* `TauCeti.AlmostComplexStructure.ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply`:
  `c(e₁) ψ = i c(e₀) ψ` and `c(e₃) ψ = i c(e₂) ψ` for `c₂(ω) ψ = -2i ψ`, with the resulting
  frame products `TauCeti.AlmostComplexStructure.ι_apply_ι_zero_apply_of_bivectorExterior_apply`,
  `TauCeti.AlmostComplexStructure.ι_apply_ι_two_apply_of_bivectorExterior_apply` and
  `TauCeti.AlmostComplexStructure.ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply`.
* `TauCeti.AlmostComplexStructure.sum_smul_ι_apply_of_bivectorExterior_apply` and
  `TauCeti.AlmostComplexStructure.sum_smul_ι_apply_eq_zero_iff_of_bivectorExterior_apply`:
  `∑ₖ x_k c(e_k) ψ = (x₀ + i x₁) c(e₀) ψ + (x₂ + i x₃) c(e₂) ψ` for `c₂(ω) ψ = -2i ψ`, vanishing
  iff `ψ = 0` or `x₀ + i x₁ = x₂ + i x₃ = 0`.
* `TauCeti.AlmostComplexStructure.ι_apply_of_bivectorExterior_apply` and
  `TauCeti.AlmostComplexStructure.ι_apply_apply_of_bivectorExterior_apply`:
  `c(v) ψ = z₀(v) c(e₀) ψ + z₂(v) c(e₂) ψ` and `c(J v) ψ = i c(v) ψ` for `c₂(ω) ψ = -2i ψ`.
* `TauCeti.AlmostComplexStructure.ι_apply_ι_apply_of_bivectorExterior_apply`: the formula for
  `c(v) c(w) ψ` above, and
  `bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply` (also in
  `TauCeti.AlmostComplexStructure`): `c(e₀) c(e₂)` takes the `μ`-eigenspace to the
  `-μ`-eigenspace for every scalar `μ`.
* `TauCeti.AlmostComplexStructure.exists_ne_zero_bivectorExterior_apply`: a nontrivial complex
  Clifford module has a nonzero positive half-spinor of Kähler eigenvalue `-2i` in the complex
  orientation. In the opposite orientation, a positive half-spinor of nonzero Kähler eigenvalue
  vanishes (`eq_zero_of_bivectorExterior_apply_of_orientation_eq_neg`).
* `TauCeti.AlmostComplexStructure.canonicalSubmodulePositiveBasis`: in the invariant Clifford
  submodule generated from a nonzero positive `-2i`-eigenspinor `u`, the positive half-spinors
  have basis `u` and `c(e₀) c(e₂) u`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
-/

public section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) {J : AlmostComplexStructure V}

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

include hQ h₀ h₂ in
/-- **The Clifford image of the Kähler form** in a unitary frame:
`c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)`. -/
theorem bivectorExterior_kahlerForm :
    bivectorExterior Q J.kahlerForm = ι Q (e 0) * ι Q (e 1) + ι Q (e 2) * ι Q (e 3) := by
  have hortho {i j : Fin 4} (hij : i ≠ j) : Q.IsOrtho (e i) (e j) :=
    (QuadraticMap.isOrtho_iff_inner_eq_zero hQ).2 (e.orthonormal.2 hij)
  rw [kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, map_add, bivectorExterior_apply_ιMulti,
    bivectorExterior_apply_ιMulti, bivector_eq_ι_mul_ι_of_isOrtho Q (hortho (by decide)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (hortho (by decide))]

/-! ### Clifford multiplication on the eigenvectors of `c₂(ω)`

These formulas are purely algebraic: they hold on any complex Clifford module, with no Hermitian
structure or finite dimensionality on `W`. -/

section ComplexModule

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

include hQ h₀ h₂ in
/-- `c₂(ω) x = c(e₀) c(e₁) x + c(e₂) c(e₃) x` in a unitary frame
(`bivectorExterior_kahlerForm`). -/
private theorem map_bivectorExterior_kahlerForm_apply (x : W) :
    ρ (bivectorExterior Q J.kahlerForm) x =
      ρ (ι Q (e 0)) (ρ (ι Q (e 1)) x) + ρ (ι Q (e 2)) (ρ (ι Q (e 3)) x) := by
  rw [bivectorExterior_kahlerForm hQ h₀ h₂, map_add, map_mul, map_mul,
    LinearMap.add_apply, mul_apply_eq_comp, mul_apply_eq_comp]

include hQ h₀ h₂ in
/-- On an eigenvector `ψ ∈ W` of `c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)` with nonzero eigenvalue `μ`,
the commuting square roots of `-1` `c(e₀) c(e₁)` and `c(e₂) c(e₃)` both act by `μ / 2`, so
`c(e₁) ψ = -(μ / 2) c(e₀) ψ` and `c(e₃) ψ = -(μ / 2) c(e₂) ψ`. No chirality or orientation is
needed. -/
theorem ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply_eq_smul {μ : ℂ} (hμ : μ ≠ 0)
    {ψ : W} (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = μ • ψ) :
    ρ (ι Q (e 1)) ψ = -(μ / 2) • ρ (ι Q (e 0)) ψ ∧
      ρ (ι Q (e 3)) ψ = -(μ / 2) • ρ (ι Q (e 2)) ψ := by
  -- Write `a = c(e₀) c(e₁) ψ` and `b = c(e₂) c(e₃) ψ`, so that `a + b = μ ψ`.
  have hab : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) ψ) + ρ (ι Q (e 2)) (ρ (ι Q (e 3)) ψ) = μ • ψ := by
    rwa [map_bivectorExterior_kahlerForm_apply hQ h₀ h₂] at hψ
  have hsq (i j : Fin 4) (hij : i ≠ j) (x : W) :
      ρ (ι Q (e i)) (ρ (ι Q (e j)) (ρ (ι Q (e i)) (ρ (ι Q (e j)) x))) = -x := by
    rw [e.map_ι_apply_map_ι_apply_comm hQ ρ hij.symm, map_neg,
      e.map_ι_apply_map_ι_apply hQ ρ, e.map_ι_apply_map_ι_apply hQ ρ, neg_neg]
  have hcomm : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) (ρ (ι Q (e 2)) (ρ (ι Q (e 3)) ψ))) =
      ρ (ι Q (e 2)) (ρ (ι Q (e 3)) (ρ (ι Q (e 0)) (ρ (ι Q (e 1)) ψ))) := by
    simp only [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 2) (by decide),
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 0) (j := 2) (by decide),
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 3) (by decide),
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 0) (j := 3) (by decide), map_neg, neg_neg]
  -- Applying `c(e₀) c(e₁)` and `c(e₂) c(e₃)` to `a + b = μ ψ` gives `μ (a - b) = 0`.
  have ha := congrArg (fun x ↦ ρ (ι Q (e 0)) (ρ (ι Q (e 1)) x)) hab
  have hb := congrArg (fun x ↦ ρ (ι Q (e 2)) (ρ (ι Q (e 3)) x)) hab
  simp only [map_add, map_smul, hsq 0 1 (by decide), hsq 2 3 (by decide)] at ha hb
  have hdiff : μ • (ρ (ι Q (e 0)) (ρ (ι Q (e 1)) ψ) - ρ (ι Q (e 2)) (ρ (ι Q (e 3)) ψ)) = 0 := by
    linear_combination (norm := module) hb - ha + hcomm
  have heq := sub_eq_zero.1 ((smul_eq_zero.1 hdiff).resolve_left hμ)
  -- So `a = b = (μ / 2) ψ`, and multiplying by `c(e₀)`, resp. `c(e₂)`, gives the claim.
  have h01 := congrArg (ρ (ι Q (e 0))) (show ρ (ι Q (e 0)) (ρ (ι Q (e 1)) ψ) =
    (μ / 2) • ψ by linear_combination (norm := module) (2⁻¹ : ℂ) • (hab + heq))
  have h23 := congrArg (ρ (ι Q (e 2))) (show ρ (ι Q (e 2)) (ρ (ι Q (e 3)) ψ) =
    (μ / 2) • ψ by linear_combination (norm := module) (2⁻¹ : ℂ) • (hab - heq))
  rw [e.map_ι_apply_map_ι_apply hQ ρ, map_smul] at h01 h23
  exact ⟨by linear_combination (norm := module) -h01, by linear_combination (norm := module) -h23⟩

include hQ h₀ h₂ in
/-- Conversely to `ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply_eq_smul`, if
`c(e₁) ψ = μ c(e₀) ψ` and `c(e₃) ψ = μ c(e₂) ψ` in a unitary frame, then
`c₂(ω) ψ = (-2 μ) ψ`. No chirality or orientation is needed. -/
theorem bivectorExterior_apply_eq_smul_of_ι_one_apply_of_ι_three_apply {μ : ℂ} {ψ : W}
    (h1 : ρ (ι Q (e 1)) ψ = μ • ρ (ι Q (e 0)) ψ)
    (h3 : ρ (ι Q (e 3)) ψ = μ • ρ (ι Q (e 2)) ψ) :
    ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * μ) • ψ := by
  rw [map_bivectorExterior_kahlerForm_apply hQ h₀ h₂, h1, h3, map_smul, map_smul,
    e.map_ι_apply_map_ι_apply hQ ρ, e.map_ι_apply_map_ι_apply hQ ρ]
  module

include hQ h₀ h₂ in
/-- On a `-2i`-eigenvector `ψ ∈ W` of `c₂(ω)`, `c(e₁) ψ = i c(e₀) ψ` and `c(e₃) ψ = i c(e₂) ψ`
(`ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply_eq_smul`). A positive half-spinor fixed
by `P_α` is such an eigenvector
(`TauCeti.SeibergWitten.bivectorExterior_apply_of_cliffordProjection_apply_eq_self`). -/
theorem ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (ι Q (e 1)) ψ = Complex.I • ρ (ι Q (e 0)) ψ ∧
      ρ (ι Q (e 3)) ψ = Complex.I • ρ (ι Q (e 2)) ψ := by
  have h := ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply_eq_smul hQ h₀ h₂
    (by simp) hψ
  rwa [show -(-2 * Complex.I / 2) = Complex.I by ring] at h

include hQ h₀ h₂ in
/-- On an eigenvector `ψ ∈ W` of `c₂(ω)` with nonzero eigenvalue `μ`, Clifford multiplication
intertwines `J` with the scalar `-μ / 2`: `2 c(J v) ψ = -μ c(v) ψ`. No chirality or orientation is
needed. -/
theorem two_smul_ι_apply_apply_of_bivectorExterior_apply_eq_smul {μ : ℂ} (hμ : μ ≠ 0) {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = μ • ψ) (v : V) :
    (2 : ℂ) • ρ (ι Q (J v)) ψ = -μ • ρ (ι Q v) ψ := by
  obtain ⟨h₁, h₃⟩ := ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply_eq_smul hQ h₀ h₂ hμ hψ
  -- Applying `c(e₀)` and `c(e₁)` to `h₁` gives `(1 + (μ / 2) ^ 2) ψ = 0`.
  have k₀ := congrArg (ρ (ι Q (e 0))) h₁
  have k₁ := congrArg (ρ (ι Q (e 1))) h₁
  rw [map_smul, e.map_ι_apply_map_ι_apply hQ ρ] at k₀ k₁
  rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 0) (by decide)] at k₁
  have hsq : (1 + (μ / 2) ^ 2) • ψ = 0 := by
    linear_combination (norm := module) -k₁ - (μ / 2) • k₀
  have hsq₀ := congrArg (ρ (ι Q (e 0))) hsq
  have hsq₂ := congrArg (ρ (ι Q (e 2))) hsq
  simp only [map_smul, map_zero] at hsq₀ hsq₂
  rw [e.map_ι_apply_eq_sum ρ (J v), e.map_ι_apply_eq_sum ρ v]
  simp only [← e.repr_apply_apply, repr_apply h₀ h₂, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, h₁, h₃]
  linear_combination (norm := module) (-2 * e.repr v 1 : ℂ) • hsq₀ + (-2 * e.repr v 3 : ℂ) • hsq₂

include hQ h₀ h₂ in
/-- **Clifford multiplication of a complex covector on the canonical eigenspace**: if
`c₂(ω) ψ = -2i ψ`, then `∑ₖ x_k c(e_k) ψ = (x₀ + i x₁) c(e₀) ψ + (x₂ + i x₃) c(e₂) ψ`. Only the two
`∂bar`-components `x₀ + i x₁` and `x₂ + i x₃` of the covector survive. A positive half-spinor fixed
by `P_α` is such an eigenvector
(`TauCeti.SeibergWitten.bivectorExterior_apply_of_cliffordProjection_apply_eq_self`). -/
theorem sum_smul_ι_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) (x : Fin 4 → ℂ) :
    ∑ k, x k • ρ (ι Q (e k)) ψ =
      (x 0 + Complex.I * x 1) • ρ (ι Q (e 0)) ψ + (x 2 + Complex.I * x 3) • ρ (ι Q (e 2)) ψ := by
  obtain ⟨h₁, h₃⟩ := ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  rw [Fin.sum_univ_four, h₁, h₃]
  module

include hQ h₀ h₂ in
/-- **Clifford multiplication on the canonical eigenspace in complex coordinates**: if
`c₂(ω) ψ = -2i ψ`, then `c(v) ψ = z₀(v) c(e₀) ψ + z₂(v) c(e₂) ψ`, where
`z₀(v) = ⟪e₀, v⟫ + i ⟪e₁, v⟫` and `z₂(v) = ⟪e₂, v⟫ + i ⟪e₃, v⟫` are the coordinates of `v` in the
basis `(e₀, e₂)` of the complex vector space `(V, J)`
(`basisOfOrthonormalBasisFinFour`). A positive half-spinor fixed by `P_α` is such an eigenvector
(`TauCeti.SeibergWitten.bivectorExterior_apply_of_cliffordProjection_apply_eq_self`). -/
theorem ι_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) (v : V) :
    letI := J.complexModule
    ρ (ι Q v) ψ =
      (basisOfOrthonormalBasisFinFour h₀ h₂).repr v 0 • ρ (ι Q (e 0)) ψ +
        (basisOfOrthonormalBasisFinFour h₀ h₂).repr v 1 •
          ρ (ι Q (e 2)) ψ := by
  rw [e.map_ι_apply_eq_sum ρ v ψ]
  simp only [← Complex.coe_smul, sum_smul_ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ,
    basisOfOrthonormalBasisFinFour_repr_apply_zero,
    basisOfOrthonormalBasisFinFour_repr_apply_one]

include hQ h₀ h₂ in
/-- **On the canonical eigenspace, Clifford multiplication turns `J` into `i`**: if
`c₂(ω) ψ = -2i ψ`, then `c(J v) ψ = i c(v) ψ`, because the complex coordinates of `J v` are `i`
times those of `v` (`ι_apply_of_bivectorExterior_apply`). -/
theorem ι_apply_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) (v : V) :
    ρ (ι Q (J v)) ψ = Complex.I • ρ (ι Q v) ψ := by
  let := J.complexModule
  rw [ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ (J v),
    ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ v, ← J.complexModule_I_smul v, map_smul]
  simp only [Finsupp.smul_apply, smul_eq_mul, smul_add, smul_smul]

include hQ h₀ h₂ in
/-- Clifford multiplication by the frame on `c(e₀) ψ`, for a `-2i`-eigenvector `ψ` of `c₂(ω)`:
`c(e₁) c(e₀) ψ = i ψ` and `c(e₃) c(e₀) ψ = -i c(e₀) c(e₂) ψ`. -/
theorem ι_apply_ι_zero_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 0)) ψ) = Complex.I • ψ ∧
      ρ (ι Q (e 3)) (ρ (ι Q (e 0)) ψ) = -(Complex.I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ)) := by
  obtain ⟨h₁, h₃⟩ := ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  constructor
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), h₁, map_smul,
      e.map_ι_apply_map_ι_apply hQ ρ, smul_neg, neg_neg]
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), h₃, map_smul]

include hQ h₀ h₂ in
/-- Clifford multiplication by the frame on `c(e₂) ψ`, for a `-2i`-eigenvector `ψ` of `c₂(ω)`:
`c(e₁) c(e₂) ψ = i c(e₀) c(e₂) ψ` and `c(e₃) c(e₂) ψ = i ψ`. -/
theorem ι_apply_ι_two_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 2)) ψ) = Complex.I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ) ∧
      ρ (ι Q (e 3)) (ρ (ι Q (e 2)) ψ) = Complex.I • ψ := by
  obtain ⟨h₁, h₃⟩ := ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  constructor
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), h₁, map_smul,
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide), smul_neg, neg_neg]
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), h₃, map_smul,
      e.map_ι_apply_map_ι_apply hQ ρ, smul_neg, neg_neg]

include hQ h₀ h₂ in
/-- Clifford multiplication by the frame on `c(e₀) c(e₂) ψ`, for a `-2i`-eigenvector `ψ` of
`c₂(ω)`: `c(e₁) c(e₀) c(e₂) ψ = i c(e₂) ψ` and `c(e₃) c(e₀) c(e₂) ψ = -i c(e₀) ψ`. -/
theorem ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ)) = Complex.I • ρ (ι Q (e 2)) ψ ∧
      ρ (ι Q (e 3)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ)) = (-Complex.I) • ρ (ι Q (e 0)) ψ := by
  obtain ⟨p12, p32⟩ := ι_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  constructor
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), p12, map_smul,
      e.map_ι_apply_map_ι_apply hQ ρ, smul_neg, neg_neg]
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), p32, map_smul, neg_smul]

include hQ h₀ h₂ in
/-- **Two Clifford multiplications on the canonical eigenspace**: if `c₂(ω) ψ = -2i ψ`, then
`c(v) c(w) ψ = (z₀(v) z₂(w) - z₂(v) z₀(w)) c(e₀) c(e₂) ψ - (⟪v, w⟫ - i ⟪v, J w⟫) ψ`,
where `z₀(v) = ⟪e₀, v⟫ + i ⟪e₁, v⟫` and `z₂(v) = ⟪e₂, v⟫ + i ⟪e₃, v⟫` are the coordinates of `v` in
the basis `(e₀, e₂)` of the complex vector space `(V, J)`. The first coefficient is the complex
determinant of `v, w` in this basis, and `⟪v, w⟫ - i ⟪v, J w⟫` is the Hermitian product of
`(V, J)`. -/
theorem ι_apply_ι_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) (v w : V) :
    letI := J.complexModule
    ρ (ι Q v) (ρ (ι Q w) ψ) =
      ((basisOfOrthonormalBasisFinFour h₀ h₂).repr v 0 *
            (basisOfOrthonormalBasisFinFour h₀ h₂).repr w 1 -
          (basisOfOrthonormalBasisFinFour h₀ h₂).repr v 1 *
            (basisOfOrthonormalBasisFinFour h₀ h₂).repr w 0) •
        ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ) -
      ((⟪v, w⟫ : ℂ) - ⟪v, J w⟫ * Complex.I) • ψ := by
  obtain ⟨p10, p30⟩ := ι_apply_ι_zero_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  obtain ⟨p12, p32⟩ := ι_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  have p20 := e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide) ψ
  -- The inner products of `(V, J)` in the frame.
  have hvw : ⟪v, w⟫ = ⟪e 0, v⟫ * ⟪e 0, w⟫ + ⟪e 1, v⟫ * ⟪e 1, w⟫ + ⟪e 2, v⟫ * ⟪e 2, w⟫ +
      ⟪e 3, v⟫ * ⟪e 3, w⟫ := by
    rw [← e.sum_inner_mul_inner v w, Fin.sum_univ_four]
    simp only [real_inner_comm v]
  have hvJw : ⟪v, J w⟫ = -⟪e 0, v⟫ * ⟪e 1, w⟫ + ⟪e 1, v⟫ * ⟪e 0, w⟫ - ⟪e 2, v⟫ * ⟪e 3, w⟫ +
      ⟪e 3, v⟫ * ⟪e 2, w⟫ := by
    rw [← e.sum_inner_mul_inner v (J w), Fin.sum_univ_four]
    simp only [real_inner_comm v, ← e.repr_apply_apply,
      repr_apply h₀ h₂]
    simp only [e.repr_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ w]
  simp only [map_add, map_smul, e.map_ι_apply_eq_sum ρ v, Fin.sum_univ_four, p10, p20, p30, p12,
    p32, e.map_ι_apply_map_ι_apply hQ ρ, hvw, hvJw,
    basisOfOrthonormalBasisFinFour_repr_apply_zero,
    basisOfOrthonormalBasisFinFour_repr_apply_one, ← Complex.coe_smul]
  push_cast
  match_scalars
  · linear_combination (⟪e 1, v⟫ * ⟪e 1, w⟫ + ⟪e 3, v⟫ * ⟪e 3, w⟫ : ℂ) * Complex.I_sq
  · ring

include hQ h₀ h₂ in
/-- The product `c(e₀) c(e₂)` exchanges the `μ`- and `-μ`-eigenspaces of the Kähler action. -/
theorem bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply {μ : ℂ} {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = μ • ψ) :
    ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ)) =
      -μ • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ) := by
  rw [neg_smul, ← map_smul, ← map_smul, ← hψ]
  simp only [map_bivectorExterior_kahlerForm_apply hQ h₀ h₂, map_add,
    e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 0) (by decide),
    e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide),
    e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 3) (j := 0) (by decide),
    e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 1) (by decide),
    e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 3) (j := 2) (by decide),
    e.map_ι_apply_map_ι_apply hQ ρ, map_neg, neg_neg]
  abel

include hQ h₀ h₂ in
/-- **The Dirac symbol on the canonical eigenspace vanishes exactly on `∂bar`-closed covectors**:
if `c₂(ω) ψ = -2i ψ`, then `∑ₖ x_k c(e_k) ψ = 0` if and only if `ψ = 0` or
`x₀ + i x₁ = x₂ + i x₃ = 0`. No Hermitian structure, chirality or orientation is needed. -/
theorem sum_smul_ι_apply_eq_zero_iff_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) (x : Fin 4 → ℂ) :
    ∑ k, x k • ρ (ι Q (e k)) ψ = 0 ↔
      ψ = 0 ∨ (x 0 + Complex.I * x 1 = 0 ∧ x 2 + Complex.I * x 3 = 0) := by
  rw [sum_smul_ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ]
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- Applying `c(e₀)` sends `c(e₀) ψ` to `-ψ` (eigenvalue `-2i`) and `c(e₂) ψ` to `c(e₀) c(e₂) ψ`
    -- (eigenvalue `2i`), which lie in disjoint eigenspaces of `c₂(ω)`.
    have h1 := congrArg (ρ (ι Q (e 0))) h
    simp only [map_add, map_smul, map_zero, e.map_ι_apply_map_ι_apply hQ ρ] at h1
    have h20 := bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply
      hQ h₀ h₂ hψ
    set T := ρ (bivectorExterior Q J.kahlerForm)
    have hmem0 : (x 0 + Complex.I * x 1) • (-ψ) ∈ T.genEigenspace (-2 * Complex.I) 1 :=
      Submodule.smul_mem _ _ (Submodule.neg_mem _ (Module.End.mem_genEigenspace_one.2 hψ))
    have hmem2 : (x 2 + Complex.I * x 3) • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ) ∈
        T.genEigenspace (2 * Complex.I) 1 :=
      Submodule.smul_mem _ _ (Module.End.mem_genEigenspace_one.2 (by simpa using h20))
    have hne : (-2 * Complex.I : ℂ) ≠ 2 * Complex.I := by norm_num [Complex.ext_iff]
    obtain ⟨hz0, hz2'⟩ :=
      (Submodule.disjoint_iff_add_eq_zero.1 (T.disjoint_genEigenspace hne 1 1))
        hmem0 hmem2 h1
    have hz2 : (x 2 + Complex.I * x 3) • ψ = 0 := by
      have := congrArg (fun w ↦ ρ (ι Q (e 2)) (ρ (ι Q (e 0)) w)) hz2'
      simpa only [map_smul, map_zero, e.map_ι_apply_map_ι_apply hQ ρ, map_neg, neg_neg] using this
    rw [smul_neg, neg_eq_zero, smul_eq_zero] at hz0
    rw [smul_eq_zero] at hz2
    tauto
  · rintro (h | ⟨h0, h2'⟩)
    · simp [h]
    · simp [h0, h2']

end ComplexModule

end Frame

end TauCeti.AlmostComplexStructure

namespace OrthonormalBasis

open CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  (e : OrthonormalBasis (Fin 4) ℝ V) (u : W)

/-- The complex subspace `span {u, c(e₀) c(e₂) u, c(e₀) u, c(e₂) u}` generated
by a spinor and its Clifford translates. -/
noncomputable abbrev canonicalSubmodule : Submodule ℂ W :=
  Submodule.span ℂ {u, ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u), ρ (ι Q (e 0)) u, ρ (ι Q (e 2)) u}

/-- The canonical submodule contains its generating spinor. -/
@[simp]
theorem self_mem_canonicalSubmodule : u ∈ e.canonicalSubmodule (ρ := ρ) u :=
  Submodule.subset_span (by simp)

/-- The canonical submodule contains the double Clifford translate of its generating spinor. -/
@[simp]
theorem ι_zero_apply_ι_two_apply_mem_canonicalSubmodule :
    ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) ∈ e.canonicalSubmodule (ρ := ρ) u :=
  Submodule.subset_span (by simp)

/-- The canonical submodule contains the translate by the zeroth frame vector. -/
@[simp]
theorem ι_zero_apply_mem_canonicalSubmodule :
    ρ (ι Q (e 0)) u ∈ e.canonicalSubmodule (ρ := ρ) u :=
  Submodule.subset_span (by simp)

/-- The canonical submodule contains the translate by the second frame vector. -/
@[simp]
theorem ι_two_apply_mem_canonicalSubmodule :
    ρ (ι Q (e 2)) u ∈ e.canonicalSubmodule (ρ := ρ) u :=
  Submodule.subset_span (by simp)

/-- The canonical submodule is the least submodule containing the four Clifford translates. -/
theorem canonicalSubmodule_le_iff {P : Submodule ℂ W} :
    e.canonicalSubmodule (ρ := ρ) u ≤ P ↔ u ∈ P ∧ ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) ∈ P ∧
      ρ (ι Q (e 0)) u ∈ P ∧ ρ (ι Q (e 2)) u ∈ P := by
  simp [canonicalSubmodule, Submodule.span_le, Set.insert_subset_iff]

/-- Membership in the canonical submodule amounts to writing the vector in the four generators. -/
theorem mem_canonicalSubmodule_iff {w : W} :
    w ∈ e.canonicalSubmodule (ρ := ρ) u ↔ ∃ a b c d : ℂ,
      w = a • u + b • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) +
        c • ρ (ι Q (e 0)) u + d • ρ (ι Q (e 2)) u := by
  constructor
  · intro hw
    obtain ⟨a, _, hx, rfl⟩ := Submodule.mem_span_insert.1 hw
    obtain ⟨b, _, hy, rfl⟩ := Submodule.mem_span_insert.1 hx
    obtain ⟨c, _, hz, rfl⟩ := Submodule.mem_span_insert.1 hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨a, b, c, d, by simp only [add_assoc]⟩
  · rintro ⟨a, b, c, d, rfl⟩
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (by simp)) (Submodule.smul_mem _ _ (by simp)))
      (Submodule.smul_mem _ _ (by simp))) (Submodule.smul_mem _ _ (by simp))

end OrthonormalBasis

namespace TauCeti.AlmostComplexStructure

noncomputable section

open CliffordAlgebra Module Module.End
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)} {J : AlmostComplexStructure V}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- The rank-four hypothesis supplies finite dimensionality for the Kähler action. -/
local instance finiteDimensionalKahlerHalfSpinors : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

/-- If `e` is a unitary frame of `J` with opposite orientation `o = -e.toBasis.orientation`, then
`c₂(ω)` vanishes on `W⁺(o)`, so every eigenvector of `c₂(ω)` in `W⁺(o)` with nonzero eigenvalue is
zero. -/
theorem eq_zero_of_bivectorExterior_apply_of_orientation_eq_neg
    {e : OrthonormalBasis (Fin 4) ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hne : o = -e.toBasis.orientation)
    {μ : ℂ} (hμ : μ ≠ 0) {ψ : eigenspace (ρ (chirality Q o)) 1}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = μ • (ψ : W)) :
    (ψ : W) = 0 := by
  have hchir : chirality Q o = -chirality Q e.toBasis.orientation := by
    rw [hne, chirality_eq_neg_volumeElement, volumeElement_neg_orientation,
      ← chirality_eq_neg_volumeElement]
  have hmem : (ψ : W) ∈ eigenspace (ρ (chirality Q e.toBasis.orientation)) (-1) := by
    have hψ' : ρ (chirality Q o) (ψ : W) = (ψ : W) := by
      simpa using mem_eigenspace_iff.1 ψ.property
    have hneg : -ρ (chirality Q e.toBasis.orientation) (ψ : W) = (ψ : W) := by
      calc -ρ (chirality Q e.toBasis.orientation) (ψ : W)
          = ρ (-chirality Q e.toBasis.orientation) (ψ : W) := by rw [map_neg, LinearMap.neg_apply]
        _ = ρ (chirality Q o) (ψ : W) := congrArg (fun a ↦ ρ a (ψ : W)) hchir.symm
        _ = (ψ : W) := hψ'
    rw [mem_eigenspace_iff, neg_one_smul, ← neg_eq_iff_eq_neg.1 hneg]
  have h23 := map_ι_mul_ι_two_three_apply e hQ ρ rfl hmem
  rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂, map_add, LinearMap.add_apply,
    h23, neg_one_smul, add_neg_cancel] at hψ
  exact (smul_eq_zero.1 hψ.symm).resolve_left hμ

/-- Any nontrivial complex Clifford module has a nonzero `-2i`-eigenvector of `c₂(ω)` in `W⁺(o)`
when `J` induces the orientation `o`. -/
theorem exists_ne_zero_bivectorExterior_apply [Nontrivial W] (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (ho : J.orientation Fact.out = o) :
    ∃ u : eigenspace (ρ (chirality Q o)) 1, (u : W) ≠ 0 ∧
      ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W) := by
  obtain ⟨e, hωe, h₀, h₂⟩ :=
    exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation
      (ω := J.symplecticForm hJ) (fun v w ↦ by rw [J.symplecticForm_apply hJ, hJ])
  have he : e.toBasis.orientation = o :=
    hωe.trans <| (J.orientation_eq_of_tames
      (J.symplecticForm_compatible hJ).tames Fact.out).symm.trans ho
  obtain ⟨ψ, hψ₀⟩ := exists_ne_zero_eigenspace_chirality o hQ ρ (ε := 1) (by simp)
  -- On `W⁺(o)`, `c₂(ω) = 2 T` where `T = c(e₀) c(e₁)` satisfies `T² = -1`.
  set T : Module.End ℂ W := ρ (ι Q (e 0) * ι Q (e 1))
  have hT_pos (z : eigenspace (ρ (chirality Q o)) 1) : T z ∈ eigenspace (ρ (chirality Q o)) 1 :=
    mapsTo_genEigenspace_of_comm
      ((commute_chirality_of_mem_even o (ι_mul_ι_mem_evenOdd_zero Q (e 0) (e 1))).map ρ)
      1 1 z.property
  have hω (z : eigenspace (ρ (chirality Q o)) 1) :
      ρ (bivectorExterior Q J.kahlerForm) z = (2 : ℂ) • T z := by
    rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂, map_add, LinearMap.add_apply,
      map_ι_mul_ι_two_three_apply e hQ ρ he z.property, one_smul, two_smul]
  have hT2 (z : W) : T (T z) = -z := by
    simp only [T, map_mul, mul_apply_eq_comp]
    rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 0) (by decide), map_neg,
      e.map_ι_apply_map_ι_apply hQ ρ, e.map_ι_apply_map_ι_apply hQ ρ, neg_neg]
  let S : Module.End ℂ (eigenspace (ρ (chirality Q o)) 1) :=
    Complex.I • T.restrict (fun z hz ↦ hT_pos ⟨z, hz⟩)
  have hS : Function.Involutive S := by
    intro z
    apply Subtype.ext
    simp [S, map_smul, hT2, smul_smul]
  have hωS (z : eigenspace (ρ (chirality Q o)) 1) :
      ρ (bivectorExterior Q J.kahlerForm) z = (-2 * Complex.I) • (S z : W) := by
    rw [hω]
    simp [S, smul_smul, mul_assoc]
  let : Nontrivial (eigenspace (ρ (chirality Q o)) 1) :=
    ⟨⟨ψ, 0, fun h ↦ hψ₀ (congrArg Subtype.val h)⟩⟩
  rcases hasEigenvalue_or_neg_of_involutive hS (one_mul (1 : ℂ)) with h | h
  · obtain ⟨z, hz, hz₀⟩ := h.exists_hasEigenvector
    refine ⟨z, fun h ↦ hz₀ (Subtype.ext h), ?_⟩
    simpa [mem_eigenspace_iff.1 hz] using hωS z
  · obtain ⟨z, hz, hz₀⟩ := h.exists_hasEigenvector
    have hzω : ρ (bivectorExterior Q J.kahlerForm) z = (2 * Complex.I) • (z : W) := by
      simpa [mem_eigenspace_iff.1 hz] using hωS z
    refine ⟨⟨_, map_ι_apply_map_ι_apply_mem_eigenspace_chirality o z.property (e 0) (e 2)⟩, ?_, ?_⟩
    · exact e.map_ι_apply_map_ι_apply_ne_zero hQ ρ 0 2 fun h ↦ hz₀ (Subtype.ext h)
    · simpa using bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply
        hQ h₀ h₂ hzω

/-- Each frame generator `c(e k)` maps the four generators of `e.canonicalSubmodule u` back into
`e.canonicalSubmodule u`. -/
private theorem canonicalSubmodule_le_comap_ι_basis {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u)
    (k : Fin 4) : e.canonicalSubmodule (ρ := ρ) u ≤
      (e.canonicalSubmodule (ρ := ρ) u).comap (ρ (ι Q (e k))) := by
  set M := e.canonicalSubmodule (ρ := ρ) u
  have hb₀M : u ∈ M := by simp [M]
  have hb₁M : ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) ∈ M := by simp [M]
  have hb₂M : ρ (ι Q (e 0)) u ∈ M := by simp [M]
  have hb₃M : ρ (ι Q (e 2)) u ∈ M := by simp [M]
  obtain ⟨h1u, h3u⟩ :=
    AlmostComplexStructure.ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  obtain ⟨p10, p30⟩ :=
    AlmostComplexStructure.ι_apply_ι_zero_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  obtain ⟨p12, p32⟩ :=
    AlmostComplexStructure.ι_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  obtain ⟨p102, p302⟩ :=
    AlmostComplexStructure.ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  apply (e.canonicalSubmodule_le_iff u).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Submodule.mem_comap] <;>
    match k with
    | 0 => ?_
    | 1 => ?_
    | 2 => ?_
    | 3 => ?_
  · exact hb₂M
  · rw [h1u]; exact M.smul_mem _ hb₂M
  · exact hb₃M
  · rw [h3u]; exact M.smul_mem _ hb₃M
  · rw [e.map_ι_apply_map_ι_apply hQ ρ]; exact M.neg_mem hb₃M
  · rw [p102]; exact M.smul_mem _ hb₃M
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide),
      e.map_ι_apply_map_ι_apply hQ ρ, map_neg, neg_neg]
    exact hb₂M
  · rw [p302]; exact M.smul_mem _ hb₂M
  · rw [e.map_ι_apply_map_ι_apply hQ ρ]; exact M.neg_mem hb₀M
  · rw [p10]; exact M.smul_mem _ hb₀M
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide)]
    exact M.neg_mem hb₁M
  · rw [p30]; exact M.neg_mem (M.smul_mem _ hb₁M)
  · exact hb₁M
  · rw [p12]; exact M.smul_mem _ hb₁M
  · rw [e.map_ι_apply_map_ι_apply hQ ρ]; exact M.neg_mem hb₀M
  · rw [p32]; exact M.smul_mem _ hb₀M

/-- `e.canonicalSubmodule u` is invariant under every Clifford element `a : CliffordAlgebra Q`. -/
theorem mapsTo_canonicalSubmodule {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u)
    (a : CliffordAlgebra Q) :
    ∀ w ∈ e.canonicalSubmodule (ρ := ρ) u, ρ a w ∈ e.canonicalSubmodule (ρ := ρ) u := by
  set M := e.canonicalSubmodule (ρ := ρ) u
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
    intro w hw
    rw [AlgHom.commutes]
    exact M.smul_mem (r : ℂ) hw
  | ι v =>
    intro w hw
    rw [e.map_ι_apply_eq_sum ρ v w]
    refine Submodule.sum_mem M fun k _ ↦ M.smul_mem (⟪e k, v⟫ : ℂ) ?_
    exact canonicalSubmodule_le_comap_ι_basis hQ h₀ h₂ hu k hw
  | mul a b ha hb =>
    intro w hw
    rw [map_mul, mul_apply_eq_comp]
    exact ha _ (hb _ hw)
  | add a b ha hb =>
    intro w hw
    rw [map_add, LinearMap.add_apply]
    exact M.add_mem (ha _ hw) (hb _ hw)

/-- The Clifford action `ρ` restricted to `e.canonicalSubmodule u`. -/
noncomputable def canonicalSubmoduleAlgHom {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u) :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ (e.canonicalSubmodule (ρ := ρ) u) :=
  ρ.restrictEnd _ (mapsTo_canonicalSubmodule hQ h₀ h₂ hu)

/-- The restricted Clifford action on `e.canonicalSubmodule u` agrees with `ρ` on underlying
vectors. -/
@[simp]
theorem coe_canonicalSubmoduleAlgHom_apply {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u)
    (a : CliffordAlgebra Q) (w : e.canonicalSubmodule (ρ := ρ) u) :
    (canonicalSubmoduleAlgHom hQ h₀ h₂ hu a w : W) = ρ a w :=
  AlgHom.coe_restrictEnd_apply ρ _ _ a w

/-- Every positive half-spinor in `e.canonicalSubmodule u` is a linear combination of `u` and
`c(e₀) c(e₂) u`. -/
theorem mem_span_positive_canonicalSubmodule {e : OrthonormalBasis (Fin 4) ℝ V}
    {u : eigenspace (ρ (chirality Q o)) 1} {w : W} (hwM : w ∈ e.canonicalSubmodule (ρ := ρ) u)
    (hwΓ : ρ (chirality Q o) w = w) :
    ∃ c₀ c₁ : ℂ, w = c₀ • (u : W) + c₁ • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
  obtain ⟨c₀, c₁, c₂, c₃, rfl⟩ := (e.mem_canonicalSubmodule_iff (u : W)).1 hwM
  have hΓ0 : ρ (chirality Q o) u = u := by simpa using mem_eigenspace_iff.1 u.property
  have hΓ1 : ρ (chirality Q o) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u)) =
      ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
    simpa using mem_eigenspace_iff.1
      (map_ι_apply_map_ι_apply_mem_eigenspace_chirality o u.property (e 0) (e 2))
  have hΓ2 : ρ (chirality Q o) (ρ (ι Q (e 0)) u) = -ρ (ι Q (e 0)) u := by
    simpa using mem_eigenspace_iff.1 (map_ι_apply_mem_eigenspace_chirality_neg o u.property (e 0))
  have hΓ3 : ρ (chirality Q o) (ρ (ι Q (e 2)) u) = -ρ (ι Q (e 2)) u := by
    simpa using mem_eigenspace_iff.1 (map_ι_apply_mem_eigenspace_chirality_neg o u.property (e 2))
  simp only [map_add, map_smul, hΓ0, hΓ1, hΓ2, hΓ3] at hwΓ
  have h2 : (2 : ℂ) • (c₂ • ρ (ι Q (e 0)) u + c₃ • ρ (ι Q (e 2)) u) = 0 := by
    linear_combination (norm := module) -hwΓ
  have h23 : c₂ • ρ (ι Q (e 0)) u + c₃ • ρ (ι Q (e 2)) u = 0 :=
    (smul_eq_zero.1 h2).resolve_left two_ne_zero
  exact ⟨c₀, c₁, by linear_combination (norm := module) h23⟩

/-- For a nonzero `-2i`-eigenvector `u ∈ W⁺(o)` of `c₂(ω)`, `(u, c(e₀) c(e₂) u)` is a `ℂ`-basis of
the positive half-spinors of `e.canonicalSubmodule u`. -/
noncomputable def canonicalSubmodulePositiveBasis {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : eigenspace (ρ (chirality Q o)) 1} (hu₀ : (u : W) ≠ 0)
    (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W)) :
    Basis (Fin 2) ℂ
      (eigenspace (canonicalSubmoduleAlgHom hQ h₀ h₂ hu (chirality Q o)) 1) := by
  let M := e.canonicalSubmodule (ρ := ρ) u
  let ρM := canonicalSubmoduleAlgHom hQ h₀ h₂ hu
  let b₁ : W := ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u)
  have hb₁ω : ρ (bivectorExterior Q J.kahlerForm) b₁ = (2 * Complex.I) • b₁ := by
    simpa using
      bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  have hb₁ne : b₁ ≠ 0 := e.map_ι_apply_map_ι_apply_ne_zero hQ ρ 0 2 hu₀
  let v₀ : eigenspace (ρM (chirality Q o)) 1 :=
    ⟨⟨u, by simp⟩,
      mem_eigenspace_iff.2 (Subtype.ext (by
        rw [coe_canonicalSubmoduleAlgHom_apply, Submodule.coe_smul]
        exact mem_eigenspace_iff.1 u.property))⟩
  let v₁ : eigenspace (ρM (chirality Q o)) 1 :=
    ⟨⟨b₁, by simp [b₁]⟩,
      mem_eigenspace_iff.2 (Subtype.ext (by
        rw [coe_canonicalSubmoduleAlgHom_apply, Submodule.coe_smul]
        exact mem_eigenspace_iff.1
          (map_ι_apply_map_ι_apply_mem_eigenspace_chirality o u.property (e 0) (e 2))))⟩
  refine Basis.mk (v := ![v₀, v₁]) ?_ ?_
  · refine LinearIndependent.of_comp (M.subtype.comp (eigenspace (ρM (chirality Q o)) 1).subtype) ?_
    have hcomp : (M.subtype.comp (eigenspace (ρM (chirality Q o)) 1).subtype) ∘ ![v₀, v₁] =
        ![(u : W), b₁] := by
      ext i
      fin_cases i <;> rfl
    rw [hcomp]
    refine Module.End.eigenvectors_linearIndependent' (ρ (bivectorExterior Q J.kahlerForm))
      ![-2 * Complex.I, 2 * Complex.I]
      (fun i j hij ↦ by
        fin_cases i <;> fin_cases j <;>
          first | rfl | exact absurd (congrArg Complex.im hij) (by norm_num))
      ![(u : W), b₁] (fun i ↦ ?_)
    fin_cases i
    · exact ⟨mem_eigenspace_iff.2 hu, hu₀⟩
    · exact ⟨mem_eigenspace_iff.2 hb₁ω, hb₁ne⟩
  · intro ⟨⟨w, hwM⟩, hwpos⟩ _
    have hwΓ : ρ (chirality Q o) w = w := by
      simpa [ρM, canonicalSubmoduleAlgHom] using congrArg Subtype.val (mem_eigenspace_iff.1 hwpos)
    obtain ⟨c₀, c₁, rfl⟩ := mem_span_positive_canonicalSubmodule hwM hwΓ
    have heq : (⟨⟨c₀ • (u : W) + c₁ • b₁, hwM⟩, hwpos⟩ : eigenspace (ρM (chirality Q o)) 1) =
        c₀ • v₀ + c₁ • v₁ := by
      ext; simp [v₀, v₁, b₁]
    rw [heq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- The zeroth vector of `canonicalSubmodulePositiveBasis` has underlying vector `u`. -/
@[simp]
theorem coe_canonicalSubmodulePositiveBasis_zero {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : eigenspace (ρ (chirality Q o)) 1} (hu₀ : (u : W) ≠ 0)
    (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W)) :
    ((canonicalSubmodulePositiveBasis hQ h₀ h₂ hu₀ hu 0 :
        e.canonicalSubmodule (ρ := ρ) u) : W) = u := by
  simp [canonicalSubmodulePositiveBasis]

/-- The first vector of `canonicalSubmodulePositiveBasis` has underlying vector `c(e₀) c(e₂) u`. -/
@[simp]
theorem coe_canonicalSubmodulePositiveBasis_one {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : eigenspace (ρ (chirality Q o)) 1} (hu₀ : (u : W) ≠ 0)
    (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W)) :
    ((canonicalSubmodulePositiveBasis hQ h₀ h₂ hu₀ hu 1 :
        e.canonicalSubmodule (ρ := ρ) u) : W) = ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
  simp [canonicalSubmodulePositiveBasis]

/-- Applying `c(A e₀) c(A e₂)` to a `-2i`-eigenvector `u` of `c₂(ω)`, for
`A = unitaryGroupFrameEquiv g`, scales `c(e₀) c(e₂) u` by `det g`. -/
theorem ι_apply_ι_apply_unitaryGroupFrameEquiv {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u)
    (g : Matrix.unitaryGroup (Fin 2) ℂ) :
    let A := (AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂ g :
      TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    ρ (ι Q ((A : V ≃ₗ[ℝ] V) (e 0))) (ρ (ι Q ((A : V ≃ₗ[ℝ] V) (e 2))) u) =
      (g : Matrix (Fin 2) (Fin 2) ℂ).det • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
  intro A
  let := J.complexModule
  set B := AlmostComplexStructure.basisOfOrthonormalBasisFinFour h₀ h₂
  rw [AlmostComplexStructure.ι_apply_ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hu]
  have hA_inner (v w : V) : ⟪(A : V ≃ₗ[ℝ] V) v, (A : V ≃ₗ[ℝ] V) w⟫ = ⟪v, w⟫ := by
    have hpol := QuadraticMap.polar_eq_neg_two_inner hQ
    have hAQ : ∀ z, Q ((A : V ≃ₗ[ℝ] V) z) = Q z :=
      QuadraticMap.mem_orthogonalGroup_iff.1
        (QuadraticMap.mem_specialOrthogonalGroup_iff.1 A.property).1
    have hp : QuadraticMap.polar Q ((A : V ≃ₗ[ℝ] V) v) ((A : V ≃ₗ[ℝ] V) w) =
        QuadraticMap.polar Q v w := by simp only [QuadraticMap.polar, ← map_add, hAQ]
    rw [hpol, hpol] at hp; linarith
  have h02 : ⟪(A : V ≃ₗ[ℝ] V) (e 0), (A : V ≃ₗ[ℝ] V) (e 2)⟫ = 0 := by
    rw [hA_inner, e.orthonormal.2 (by decide)]
  have h03 : ⟪(A : V ≃ₗ[ℝ] V) (e 0), J ((A : V ≃ₗ[ℝ] V) (e 2))⟫ = 0 := by
    rw [← AlmostComplexStructure.mem_unitaryGroup_iff.1
        (AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂ g).property (e 2),
      h₂, hA_inner, e.orthonormal.2 (by decide)]
  have hcoord (v : V) (i : Fin 2) : B.repr ((A : V ≃ₗ[ℝ] V) v) i =
      ((g : Matrix (Fin 2) (Fin 2) ℂ).mulVec (B.repr v)) i := by
    have h1 := AlmostComplexStructure.complexCoords_unitaryGroupFrameEquiv_apply hQ h₀ h₂ g v
    rw [← AlmostComplexStructure.basisOfOrthonormalBasisFinFour_equivFun_apply h₀ h₂,
      ← AlmostComplexStructure.basisOfOrthonormalBasisFinFour_equivFun_apply h₀ h₂] at h1
    simpa only [Basis.equivFun_apply] using congrFun h1 i
  have hre0 : B.repr (e 0) = Finsupp.single 0 1 := by
    rw [← AlmostComplexStructure.basisOfOrthonormalBasisFinFour_zero h₀ h₂, B.repr_self]
  have hre2 : B.repr (e 2) = Finsupp.single 1 1 := by
    rw [← AlmostComplexStructure.basisOfOrthonormalBasisFinFour_one h₀ h₂, B.repr_self]
  have hdet : B.repr ((A : V ≃ₗ[ℝ] V) (e 0)) 0 * B.repr ((A : V ≃ₗ[ℝ] V) (e 2)) 1 -
      B.repr ((A : V ≃ₗ[ℝ] V) (e 0)) 1 * B.repr ((A : V ≃ₗ[ℝ] V) (e 2)) 0 =
      (g : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [hcoord (e 0) 0, hcoord (e 2) 1, hcoord (e 0) 1, hcoord (e 2) 0, hre0, hre2,
      Matrix.det_fin_two]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [h02, h03, hdet]
  simp

end

end TauCeti.AlmostComplexStructure
