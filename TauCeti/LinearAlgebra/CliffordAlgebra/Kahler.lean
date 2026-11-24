/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

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
* `TauCeti.AlmostComplexStructure.ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply_eq_smul`
  and `TauCeti.AlmostComplexStructure.two_smul_ι_apply_apply_of_bivectorExterior_apply_eq_smul`:
  `c(e₁) ψ = -(μ / 2) c(e₀) ψ`, `c(e₃) ψ = -(μ / 2) c(e₂) ψ` and `2 c(J v) ψ = -μ c(v) ψ` for
  `c₂(ω) ψ = μ ψ` with `μ ≠ 0`.
* `TauCeti.AlmostComplexStructure.ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply`:
  `c(e₁) ψ = i c(e₀) ψ` and `c(e₃) ψ = i c(e₂) ψ` for `c₂(ω) ψ = -2i ψ`, with the resulting
  frame products `TauCeti.AlmostComplexStructure.ι_apply_ι_zero_apply_of_bivectorExterior_apply`,
  `TauCeti.AlmostComplexStructure.ι_apply_ι_two_apply_of_bivectorExterior_apply` and
  `TauCeti.AlmostComplexStructure.ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply`.
* `TauCeti.AlmostComplexStructure.sum_smul_ι_apply_of_bivectorExterior_apply`:
  `∑ₖ x_k c(e_k) ψ = (x₀ + i x₁) c(e₀) ψ + (x₂ + i x₃) c(e₂) ψ` for `c₂(ω) ψ = -2i ψ`.
* `TauCeti.AlmostComplexStructure.ι_apply_of_bivectorExterior_apply` and
  `TauCeti.AlmostComplexStructure.ι_apply_apply_of_bivectorExterior_apply`:
  `c(v) ψ = z₀(v) c(e₀) ψ + z₂(v) c(e₂) ψ` and `c(J v) ψ = i c(v) ψ` for `c₂(ω) ψ = -2i ψ`.
* `TauCeti.AlmostComplexStructure.ι_apply_ι_apply_of_bivectorExterior_apply`: the formula for
  `c(v) c(w) ψ` above, and
  `bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply` (also in
  `TauCeti.AlmostComplexStructure`): `c(e₀) c(e₂) ψ` lies in the `2i`-eigenspace.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
-/

public section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra _root_.exteriorPower
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
/-- **`c(e₀) c(e₂)` carries the canonical eigenspace into the complementary one**: if
`c₂(ω) ψ = -2i ψ`, then `c₂(ω) (c(e₀) c(e₂) ψ) = 2i c(e₀) c(e₂) ψ`. -/
theorem bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ)) =
      (2 * Complex.I) • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ) := by
  obtain ⟨h1, h3⟩ := ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  rw [map_bivectorExterior_kahlerForm_apply hQ h₀ h₂, h1, h3, map_smul, map_smul,
    e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide)]
  module

end ComplexModule

end Frame

end TauCeti.AlmostComplexStructure
