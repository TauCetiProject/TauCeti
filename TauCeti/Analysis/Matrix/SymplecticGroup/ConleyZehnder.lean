/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.Graph
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
import TauCeti.Basic.Real.Sign
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.MkOfDetNeZero

/-!
# The Conley–Zehnder index of a path of symplectic matrices

The **Conley–Zehnder index** of a path `γ` of real symplectic matrices is minus the
Robbin–Salamon index of the path of its graphs relative to the diagonal,
`CZ(γ) = -μ(Γ ∘ γ, Δ)` (`TauCeti.GLSymplectic.conleyZehnder`). Applied to the linearized flow
along a periodic orbit of a Hamiltonian, read in a symplectic trivialization, it is the degree
of the orbit as a generator of a Floer complex.

The graph `Γ(A)` of a symplectic matrix `A` is the Lagrangian subspace of
`ℂ^{n ⊕ n} = ℂⁿ × ℂⁿ` framed by the columns of the graph frame `F(A)` (`Matrix.graphFrame`), in
the identification of `TauCeti.Analysis.Matrix.SymplecticGroup.Graph`. Since `Γ(A)` is
Lagrangian, the Gram matrix `F(A)ᴴ F(A) = 1 + Aᵀ A` is real, so the unitary factor `U(A)` of the
polar decomposition `F(A) = U(A) √(1 + Aᵀ A)` frames the same Lagrangian
(`TauCeti.GLSymplectic.realImage_graphUnitary`). The graph of the identity is the diagonal `Δ`,
and `U(1) = F(1) / √2` carries `ℝ^{n ⊕ n}` onto it. So the **normalized graph frame**
`U(1)⋆ U(A)` (`TauCeti.GLSymplectic.normalizedGraphUnitary`) frames the image of `Γ(A)` under
the unitary, hence symplectic, automorphism `U(1)⋆` which carries `Δ` to `ℝ^{n ⊕ n}`. The
Robbin–Salamon index relative to `Δ` is invariant under such a change of coordinates, and
relative to `ℝ^{n ⊕ n}` it is Souriau's spectral index `Matrix.UnitaryGroup.maslovIndex`. The
Conley–Zehnder index is minus that index of the path of normalized graph frames.

With this sign convention a small counterclockwise rotation of `ℝ²` has index `-1`. More
generally, if `γ t` is the realification of `diag (e^{i θ_j t})` for continuous angles `θ_j`, then
`CZ(γ) = -∑ j, (c(θ_j 1) - c(θ_j 0))` with `c(θ) = ⌊θ / 2π⌋ + ⌈θ / 2π⌉`
(`TauCeti.GLSymplectic.conleyZehnder_eq_sum_of_diagonal`). For the path `t ↦ exp (t J S)` with
`S = diag (β, β)` and `|β_j| < 2π` this is `-sign S / 2`
(`TauCeti.GLSymplectic.conleyZehnder_eq_neg_sum_sign`).

## Main definitions

* `TauCeti.GLSymplectic.graphUnitary`: the unitary frame `U(A)` of the graph of `A`.
* `TauCeti.GLSymplectic.normalizedGraphUnitary`: the normalized graph frame `U(1)⋆ U(A)`.
* `TauCeti.GLSymplectic.conleyZehnder`: the Conley–Zehnder index of a path of symplectic
  matrices.

## Main results

* `TauCeti.GLSymplectic.realImage_graphUnitary`: the unitary graph frame frames the graph.
* `TauCeti.GLSymplectic.conleyZehnder_eq_of_homotopic`, `TauCeti.GLSymplectic.conleyZehnder_trans`,
  `TauCeti.GLSymplectic.conleyZehnder_symm`: homotopy invariance relative to the endpoints,
  additivity under catenation, and reversal.
* `TauCeti.GLSymplectic.conleyZehnder_eq_sum_of_diagonal`: the index of a path of realified
  diagonal unitary matrices.
* `TauCeti.GLSymplectic.conleyZehnder_eq_neg_sum_sign`: the normalization `CZ = -sign S / 2` for
  slow rotations of the complex coordinates.

## References

* C. Conley and E. Zehnder, *Morse-type index theory for flows and periodic solutions for
  Hamiltonian equations*, Comm. Pure Appl. Math. **37** (1984), 207–253.
* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index as the Maslov index of the graphs relative to the
  diagonal).
* D. Salamon, *Lectures on Floer homology*, Symplectic geometry and topology (Park City, 1997),
  IAS/Park City Math. Ser. 7, Amer. Math. Soc., 1999, Section 2.4.
-/

public section

open Matrix Complex
open scoped unitInterval MatrixOrder ComplexOrder

namespace TauCeti.GLSymplectic

open Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The graph frame of a symplectic matrix, as an invertible complex matrix. -/
noncomputable def graphFrameUnit (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero _ (det_graphFrame_ne_zero A)

@[simp]
theorem coe_graphFrameUnit (A : GLSymplectic n ℝ) :
    (graphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) = graphFrame (A : GL (n ⊕ n) ℝ) :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- The **unitary graph frame** of a symplectic matrix `A`: the unitary factor of the polar
decomposition of its graph frame. -/
noncomputable def graphUnitary (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  Units.polarUnitary (graphFrameUnit A)

theorem graphUnitary_def (A : GLSymplectic n ℝ) :
    graphUnitary A = Units.polarUnitary (graphFrameUnit A) :=
  (rfl)

/-- The graph frame depends continuously on the symplectic matrix, as an invertible matrix. -/
theorem continuous_graphFrameUnit : Continuous (graphFrameUnit : GLSymplectic n ℝ → _) :=
  GeneralLinearGroup.continuous_mkOfDetNeZero
    (continuous_graphFrame.comp (Units.continuous_val.comp continuous_subtype_val)) _

/-- The positive factor of the graph frame of a symplectic matrix `A` is the real matrix
`√(1 + Aᵀ A)`: the graph frame is the unitary graph frame times `√(1 + Aᵀ A)`. -/
theorem graphUnitary_mul_sqrt (A : GLSymplectic n ℝ) :
    (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ) *
        (CFC.sqrt (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
          (A : GL (n ⊕ n) ℝ))).map ((↑) : ℝ → ℂ) =
      graphFrame (A : GL (n ⊕ n) ℝ) := by
  have h := Units.polarUnitary_mul_sqrt_star_mul (graphFrameUnit A)
  have hs := sqrt_map_algebraMap (𝕜 := ℂ)
    (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
      ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))
  rw [Complex.coe_algebraMap] at hs
  rwa [coe_graphFrameUnit, star_eq_conjTranspose,
    conjTranspose_graphFrame_mul_graphFrame_of_mem (mem_iff_mem_symplecticGroup.1 A.2), hs] at h

/-- **The unitary graph frame frames the graph**: its columns span the graph of `A` over `ℝ`. -/
theorem realImage_graphUnitary (A : GLSymplectic n ℝ) :
    (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage = graphSubspace (A : GL (n ⊕ n) ℝ) := by
  have hpos : (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
      (A : GL (n ⊕ n) ℝ)).PosDef :=
    PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self _)
  rw [graphSubspace_def, ← graphUnitary_mul_sqrt,
    realImage_mul_map_ofReal _ (isStrictlyPositive_iff_posDef.2 hpos).sqrt.isUnit]

/-- The unitary graph frame depends continuously on the symplectic matrix. -/
theorem continuous_graphUnitary : Continuous (graphUnitary : GLSymplectic n ℝ → _) :=
  GeneralLinearGroup.continuous_polarUnitary.comp continuous_graphFrameUnit

/-- For an orthogonal symplectic matrix `A`, whose graph frame has Gram matrix `2`, the unitary
graph frame is the graph frame divided by `√2`. -/
theorem graphUnitary_of_transpose_mul_self_eq_one {A : GLSymplectic n ℝ}
    (hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * (A : GL (n ⊕ n) ℝ) = 1) :
    (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      ((Real.sqrt 2 : ℂ)⁻¹) • graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  have hsqrt : CFC.sqrt (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
      (A : GL (n ⊕ n) ℝ)) = Real.sqrt 2 • 1 := by
    rw [hA]
    refine CFC.sqrt_unique ?_ (smul_nonneg (Real.sqrt_nonneg 2) zero_le_one)
    rw [smul_mul_smul_comm, Matrix.one_mul, Real.mul_self_sqrt zero_le_two, two_smul]
  have h := graphUnitary_mul_sqrt A
  rw [hsqrt, Matrix.map_smul' _ _ _ (by simp), Matrix.map_one _ (by simp) (by simp),
    Matrix.mul_smul, Matrix.mul_one] at h
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  rw [← h, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-! ### The graph frame relative to the diagonal -/

/-- The unitary graph frame of `A`, moved by the inverse of the unitary graph frame of the
identity. The graph of the identity is the diagonal, so this unitary matrix frames the image of
the graph of `A` under a unitary, hence symplectic, automorphism of `ℂ^{n ⊕ n}` carrying the
diagonal to `ℝ^{n ⊕ n}`. -/
noncomputable def normalizedGraphUnitary (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  star (graphUnitary 1) * graphUnitary A

theorem normalizedGraphUnitary_def (A : GLSymplectic n ℝ) :
    normalizedGraphUnitary A = star (graphUnitary 1) * graphUnitary A :=
  (rfl)

/-- The normalized graph frame of the identity is the identity: the diagonal is carried to
`ℝ^{n ⊕ n}`. -/
@[simp]
theorem normalizedGraphUnitary_one : normalizedGraphUnitary (1 : GLSymplectic n ℝ) = 1 := by
  rw [normalizedGraphUnitary_def, Unitary.star_mul_self]

/-- The normalized graph frame frames the image of the graph of `A` under the adjoint of the
unitary graph frame of the identity. -/
theorem realImage_normalizedGraphUnitary (A : GLSymplectic n ℝ) :
    (normalizedGraphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (graphSubspace ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map
        (((toEuclideanCLM (𝕜 := ℂ)
            (star ((graphUnitary 1 : unitaryGroup (n ⊕ n) ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
          EuclideanSpace ℂ (n ⊕ n) →L[ℂ] EuclideanSpace ℂ (n ⊕ n)) :
            EuclideanSpace ℂ (n ⊕ n) →ₗ[ℂ] EuclideanSpace ℂ (n ⊕ n)).restrictScalars ℝ) := by
  rw [normalizedGraphUnitary_def, Submonoid.coe_mul, Unitary.coe_star, realImage_mul,
    realImage_graphUnitary]

/-- The normalized graph frame depends continuously on the symplectic matrix. -/
theorem continuous_normalizedGraphUnitary :
    Continuous (normalizedGraphUnitary : GLSymplectic n ℝ → _) :=
  continuous_const.mul continuous_graphUnitary

/-- The normalized graph frame of the realification of a unitary matrix `U` is
`½ [[1 + U, i (U - 1)], [i (1 - U), 1 + U]]`. -/
theorem coe_normalizedGraphUnitary_of_eq_realify {A : GLSymplectic n ℝ} {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ)
    (hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = U.realify) :
    (normalizedGraphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      (2⁻¹ : ℂ) • fromBlocks (1 + U) (Complex.I • (U - 1)) (Complex.I • (1 - U)) (1 + U) := by
  have hA' : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * (A : GL (n ⊕ n) ℝ) = 1 := by
    rw [hA, ← realify_conjTranspose, ← realify_mul, ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff'.1 hU), realify_one]
  have h1 : ((1 : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) = (1 : Matrix n n ℂ).realify := by
    simp
  have h1' : (((1 : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
      ((1 : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) = 1 := by
    simp
  have hsq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]
    norm_num
  rw [normalizedGraphUnitary_def, Submonoid.coe_mul, Unitary.coe_star,
    graphUnitary_of_transpose_mul_self_eq_one h1', graphUnitary_of_transpose_mul_self_eq_one hA',
    hA, h1, graphFrame_realify, graphFrame_realify]
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_eq_conjTranspose,
    fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 2 <;> simp [sub_eq_add_neg, add_comm, smul_smul, hsq]

/-- For the realification of a unitary matrix `U`, the Souriau map of the normalized graph frame
is `½ [[U + Uᵀ, i (U - Uᵀ)], [i (Uᵀ - U), U + Uᵀ]]`. For symmetric `U` it is `U ⊕ U`. -/
theorem coe_souriau_normalizedGraphUnitary_of_eq_realify {A : GLSymplectic n ℝ}
    {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = U.realify) :
    (souriau (normalizedGraphUnitary A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      (2⁻¹ : ℂ) • fromBlocks (U + Uᵀ) (Complex.I • (U - Uᵀ)) (Complex.I • (Uᵀ - U)) (U + Uᵀ) := by
  rw [coe_souriau, coe_normalizedGraphUnitary_of_eq_realify hU hA, transpose_smul,
    fromBlocks_transpose, Matrix.smul_mul, Matrix.mul_smul, smul_smul, fromBlocks_multiply]
  simp only [transpose_add, transpose_one, transpose_smul, transpose_sub]
  rw [← smul_smul, fromBlocks_smul (2⁻¹ : ℂ)]
  congr 1
  congr 1 <;>
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, I_mul_I, add_mul, mul_add, sub_mul,
      mul_sub, Matrix.one_mul, Matrix.mul_one, smul_add, smul_sub]
    module

/-! ### The Conley–Zehnder index -/

/-- The **Conley–Zehnder index** of a path `γ` of symplectic matrices: minus the
Robbin–Salamon index of the path of graphs of `γ` relative to the diagonal. It is computed as the
Maslov index `Matrix.UnitaryGroup.maslovIndex` relative to `ℝ^{n ⊕ n}` of the normalized graph
frames, which frame the images of the graphs under a symplectic automorphism carrying the
diagonal to `ℝ^{n ⊕ n}`. -/
noncomputable def conleyZehnder {A B : GLSymplectic n ℝ} (γ : Path A B) : ℝ :=
  -UnitaryGroup.maslovIndex (γ.map continuous_normalizedGraphUnitary)

theorem conleyZehnder_def {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnder γ = -UnitaryGroup.maslovIndex (γ.map continuous_normalizedGraphUnitary) :=
  (rfl)

/-- **Homotopy invariance.** Paths of symplectic matrices which are homotopic relative to their
endpoints have the same Conley–Zehnder index. -/
theorem conleyZehnder_eq_of_homotopic {A B : GLSymplectic n ℝ} {γ₀ γ₁ : Path A B}
    (h : γ₀.Homotopic γ₁) : conleyZehnder γ₀ = conleyZehnder γ₁ := by
  rw [conleyZehnder_def, conleyZehnder_def,
    UnitaryGroup.maslovIndex_eq_of_homotopic (h.map ⟨_, continuous_normalizedGraphUnitary⟩)]

/-- The constant path has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnder_refl (A : GLSymplectic n ℝ) : conleyZehnder (Path.refl A) = 0 := by
  have h : (Path.refl A).map continuous_normalizedGraphUnitary = Path.refl _ := by
    ext; simp
  rw [conleyZehnder_def, h, UnitaryGroup.maslovIndex_refl, neg_zero]

/-- **Catenation.** The Conley–Zehnder index is additive under concatenation of paths. -/
@[simp]
theorem conleyZehnder_trans {A B C : GLSymplectic n ℝ} (γ₁ : Path A B) (γ₂ : Path B C) :
    conleyZehnder (γ₁.trans γ₂) = conleyZehnder γ₁ + conleyZehnder γ₂ := by
  rw [conleyZehnder_def, conleyZehnder_def, conleyZehnder_def, Path.map_trans,
    UnitaryGroup.maslovIndex_trans, neg_add]

/-- Reversing a path negates its Conley–Zehnder index. -/
@[simp]
theorem conleyZehnder_symm {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnder γ.symm = -conleyZehnder γ := by
  rw [conleyZehnder_def, conleyZehnder_def, ← Path.map_symm, UnitaryGroup.maslovIndex_symm]

/-! ### Normalization on rotations -/

/-- **The Conley–Zehnder index of a diagonal unitary path.** Let `γ` be a path of symplectic
matrices which are the realifications of the diagonal unitary matrices
`diag (e^{i θ_j t})`, with continuous angles `θ_j`. Then
`CZ(γ) = -∑ j, (c(θ_j 1) - c(θ_j 0))`, where `c(θ) = ⌊θ / 2π⌋ + ⌈θ / 2π⌉` is `2k + 1` on
`(2πk, 2π(k + 1))` and `2k` at `2πk`. So a coordinate turning counterclockwise from angle `0`
through an angle in `(0, 2π)` contributes `-1`, and every further full turn contributes `-2`. -/
theorem conleyZehnder_eq_sum_of_diagonal {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (θ j t * Complex.I)).realify) :
    conleyZehnder γ = -∑ j, ((((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ) : ℝ)) -
      (((⌊θ j 0 / (2 * Real.pi)⌋ + ⌈θ j 0 / (2 * Real.pi)⌉ : ℤ) : ℝ))) := by
  -- Frame the same Lagrangians by the diagonal path `diag (e^{i θ_j t / 2}, e^{i θ_j t / 2})`.
  let φ : n ⊕ n → I → ℝ := fun k t => θ (Sum.elim id id k) t / 2
  have hφ : ∀ k, Continuous (φ k) := fun k => (hθ _).div_const 2
  let E : C(I, unitaryGroup (n ⊕ n) ℂ) :=
    ⟨fun t => TauCeti.unitaryTorusHom (n ⊕ n) fun k => Circle.exp (φ k t),
      TauCeti.continuous_unitaryTorusHom.comp
        (continuous_pi fun k => Circle.exp.continuous.comp (hφ k))⟩
  let p : Path (E 0) (E 1) := ⟨E, rfl, rfl⟩
  have hp : ∀ t, (p t : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonal fun k => Complex.exp (φ k t * Complex.I) := fun t => by
    simp [p, E, TauCeti.coe_unitaryTorusHom, Circle.coe_exp]
  have hsou : ∀ t, souriau ((γ.map continuous_normalizedGraphUnitary) t) = souriau (p t) := by
    intro t
    have hsq : (fun k => Complex.exp (φ k t * Complex.I) ^ 2) =
        Sum.elim (fun j => Complex.exp (θ j t * Complex.I))
          fun j => Complex.exp (θ j t * Complex.I) := by
      funext k
      rcases k with j | j <;>
      · simp only [Sum.elim_inl, Sum.elim_inr, id, φ, ← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
    apply Subtype.ext
    rw [Path.map_coe, Function.comp_apply,
      coe_souriau_normalizedGraphUnitary_of_eq_realify (by
        simpa [TauCeti.coe_unitaryTorusHom, Circle.coe_exp] using
          (TauCeti.unitaryTorusHom n fun j => Circle.exp (θ j t)).2) (hγ t),
      coe_souriau_of_coe_eq_diagonal (hp t), hsq, ← fromBlocks_diagonal]
    simp only [diagonal_transpose, sub_self, smul_zero, fromBlocks_smul]
    congr 1 <;> module
  rw [conleyZehnder_def, UnitaryGroup.maslovIndex_eq_of_souriau_eq _ p hsou,
    UnitaryGroup.maslovIndex_eq_sum_of_diagonal p hφ hp, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, id, φ, div_div, mul_comm (2 : ℝ) Real.pi]
  ring

/-- **Normalization.** Rotating the complex coordinates at angular speeds `β_j` with
`|β_j| < 2π`, the path `t ↦ diag (e^{i β_j t})` of realified unitary matrices has
Conley–Zehnder index `-∑ j, sign β_j`. This path is `t ↦ exp (t J S)` for the symmetric matrix
`S = diag (β, β)`, whose signature is `2 ∑ j, sign β_j`, so the index is `-sign S / 2`. In
particular a small counterclockwise rotation of `ℝ²` has index `-1`. -/
theorem conleyZehnder_eq_neg_sum_sign {A B : GLSymplectic n ℝ} (γ : Path A B) {β : n → ℝ}
    (hβ : ∀ j, |β j| < 2 * Real.pi)
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (↑(β j * t) * Complex.I)).realify) :
    conleyZehnder γ = -∑ j, Real.sign (β j) := by
  rw [conleyZehnder_eq_sum_of_diagonal γ (θ := fun j t => β j * t)
    (fun j => continuous_const.mul continuous_subtype_val) hγ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Set.Icc.coe_one, mul_one, Set.Icc.coe_zero, mul_zero, zero_div, Int.floor_zero,
    Int.ceil_zero, add_zero, Int.cast_zero, sub_zero]
  exact Real.floor_add_ceil_div_eq_sign Real.two_pi_pos (hβ j)

end TauCeti.GLSymplectic
