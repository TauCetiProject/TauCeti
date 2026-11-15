/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
public import TauCeti.LinearAlgebra.TotallyReal.Lagrangian
public import TauCeti.Topology.Algebra.Matrix.Realify
public import TauCeti.Topology.Algebra.SymplecticGroup
public import TauCeti.Topology.Instances.Matrix

/-!
# The Conley–Zehnder index of a path of symplectic matrices

Let `ω` be the standard symplectic form of `ℝ^{n ⊕ n}`, whose complex structure is the standard
alternating matrix `J = Matrix.J n ℝ`. Following Robbin and Salamon, the Conley–Zehnder index of a
path `Ψ` of symplectic matrices is read off the path of graphs `Γ(Ψ t)` relative to the diagonal
`Δ = Γ(1)`, Lagrangian subspaces of `(ℝ^{n ⊕ n} × ℝ^{n ⊕ n}, (-ω) ⊕ ω)`. The real-linear map

`(z, w) ↦ (z + w) + i J (z - w)`

identifies this symplectic space with `ℂ^{n ⊕ n}`, with its form `Im ⟪·, ·⟫`, up to a positive
factor, and carries `Δ` to the real points `ℝ^{n ⊕ n}`. It carries the graph of `A` to the real
span of the **diagonal graph frame** `(1 + A) + i J (1 - A)` (`Matrix.diagonalGraphFrame`), a
span which meets `ℝ^{n ⊕ n}` exactly in the image of the fixed points of `A`. For a symplectic `A`,
the Gram matrix of this frame is the real matrix `2 (1 + Aᵀ A)`
(`Matrix.conjTranspose_diagonalGraphFrame_mul_self`), so its real span is Lagrangian and its real
orthonormalization is a unitary frame of it (`TauCeti.GLSymplectic.diagonalFrame`), continuous in
`A`.

The **Conley–Zehnder index** of a path `γ` of symplectic matrices
(`TauCeti.GLSymplectic.conleyZehnderIndex`) is minus the Maslov index, relative to `ℝ^{n ⊕ n}`,
of this path of unitary frames (`Matrix.UnitaryGroup.maslovIndex`), that is, minus the
Robbin–Salamon index of the path of graphs relative to the diagonal. It counts the eigenvalue `1`
crossings of `γ t`, an endpoint at which `γ t` has the eigenvalue `1` counting one half. It does not
depend on the choice of unitary frames
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_maslovIndex`)
and has the formal properties of the Robbin–Salamon index:

* it is invariant under homotopies of paths fixing the endpoints
  (`TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopic`);
* it is additive under catenation (`TauCeti.GLSymplectic.conleyZehnderIndex_trans`) and changes
  sign under reversal (`TauCeti.GLSymplectic.conleyZehnderIndex_symm`).

**Localization.** When `1 + A` is invertible, the diagonal graph of a symplectic `A` is the graph
`{y + i B y}` of the real symmetric matrix `B = J (1 - A) (1 + A)⁻¹`
(`Matrix.symplecticCayley`, `J` times the Cayley transform of `A`), which is degenerate exactly
when `A` has the eigenvalue `1`. Along a path with `1 + γ t` invertible throughout, the index is
minus half the change of the signature of `B`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_sub`), by the localization axiom of
the Maslov index.

**Normalization.** The rotations `t ↦ e^{i t θ_j}` of the complex coordinate lines, realified,
with `|θ_j| < π`, have index `-∑ⱼ sign θⱼ`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_sum_sign_of_rotation`). This path is
`t ↦ exp (t J S)` for the diagonal symmetric matrix `S = diag (θ, θ)`, so its index is
`-signature (S) / 2`. In particular a small counterclockwise rotation of `ℝ²` has index `-1`, and a
small clockwise one, such as the flow of `H = ε (x² + y²) / 2`, `ε > 0`, for the convention
`ι_{X_H} ω = dH`, has index `+1`. This fixes the sign: the index is `-μ_RS` for the Robbin–Salamon
index `μ_RS` of the path of graphs relative to the diagonal.

## Main definitions

* `Matrix.diagonalGraphFrame`: the frame `(1 + A) + i J (1 - A)` of the diagonal graph of `A`.
* `Matrix.symplecticCayley`: the symmetric matrix `J (1 - A) (1 + A)⁻¹`.
* `TauCeti.GLSymplectic.diagonalFrame`: the unitary frame of the diagonal graph.
* `TauCeti.GLSymplectic.conleyZehnderIndex`: the Conley–Zehnder index of a symplectic path.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index as the Maslov index of graphs relative to the diagonal).
* C. Conley and E. Zehnder, *Morse-type index theory for flows and periodic solutions for
  Hamiltonian equations*, Comm. Pure Appl. Math. **37** (1984), 207–253.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7** (1999), 143–229 (the axioms and normalization of the Conley–Zehnder index).
-/

public section

noncomputable section

open Matrix Real
open scoped ComplexConjugate MatrixOrder unitInterval Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The diagonal graph frame -/

/-- The **diagonal graph frame** of a real matrix `A` on `ℝ^{n ⊕ n}`: the complex matrix
`(1 + A) + i J (1 - A)`. It sends a real vector `z` to the image of `(z, A z)` under
`(z, w) ↦ (z + w) + i J (z - w)`, which carries the diagonal to the real points. -/
def diagonalGraphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (1 + A).map (↑) + Complex.I • (J n ℝ * (1 - A)).map (↑)

/-- The diagonal graph frame depends continuously on the matrix. -/
theorem continuous_diagonalGraphFrame :
    Continuous (diagonalGraphFrame : Matrix (n ⊕ n) (n ⊕ n) ℝ → Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  unfold diagonalGraphFrame
  fun_prop

/-- The cross term of the Gram matrix of the diagonal graph frame of a symplectic matrix
vanishes: `(1 + A)ᵀ J (1 - A) = (J (1 - A))ᵀ (1 + A)`. -/
private theorem transpose_one_add_mul_J_mul_one_sub {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) :
    (1 + A)ᵀ * (J n ℝ * (1 - A)) = (J n ℝ * (1 - A))ᵀ * (1 + A) := by
  have hA' : Aᵀ * J n ℝ * A = J n ℝ := SymplecticGroup.mem_iff'.1 hA
  rw [transpose_mul, transpose_add, transpose_sub, transpose_one, J_transpose]
  -- Both sides expand to `J ± (Aᵀ J - J A) - Aᵀ J A`; the symplectic condition matches them.
  have h : (1 + Aᵀ) * (J n ℝ * (1 - A)) - (1 - Aᵀ) * -J n ℝ * (1 + A) =
      2 * (J n ℝ - Aᵀ * J n ℝ * A) := by noncomm_ring
  rw [hA', sub_self, mul_zero] at h
  exact sub_eq_zero.1 h

/-- **The Gram matrix of the diagonal graph frame.** For a symplectic matrix `A`, it is the real
matrix `2 (1 + Aᵀ A)`. -/
theorem conjTranspose_diagonalGraphFrame_mul_self {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) :
    (diagonalGraphFrame A)ᴴ * diagonalGraphFrame A = (2 * (1 + Aᵀ * A)).map (↑) := by
  have hJ : (J n ℝ)ᵀ * J n ℝ = 1 := by rw [J_transpose, neg_mul, J_squared, neg_neg]
  have hre : (1 + A)ᵀ * (1 + A) + (J n ℝ * (1 - A))ᵀ * (J n ℝ * (1 - A)) =
      2 * (1 + Aᵀ * A) := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (J n ℝ)ᵀ, hJ, Matrix.one_mul,
      transpose_add, transpose_sub, transpose_one]
    noncomm_ring
  rw [diagonalGraphFrame, conjTranspose_mul_self_map_ofReal_add_I_smul, hre,
    transpose_one_add_mul_J_mul_one_sub hA, sub_self, Matrix.map_zero _ (by simp), smul_zero,
    add_zero]

/-- The diagonal graph frame of a symplectic matrix is invertible. -/
theorem isUnit_det_diagonalGraphFrame {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) : IsUnit (diagonalGraphFrame A).det := by
  have hpos : (2 * (1 + Aᵀ * A)).PosDef := by
    have h := (PosDef.one (n := n ⊕ n) (R := ℝ)).add_posSemidef
      (by simpa using posSemidef_conjTranspose_mul_self A)
    rw [two_mul]
    exact h.add_posSemidef h.posSemidef
  have hdet := congrArg det (conjTranspose_diagonalGraphFrame_mul_self hA)
  have hmap : ((2 * (1 + Aᵀ * A)).map ((↑) : ℝ → ℂ)).det = ((2 * (1 + Aᵀ * A)).det : ℂ) :=
    (RingHom.map_det Complex.ofRealHom _).symm
  rw [det_mul, det_conjTranspose, hmap] at hdet
  refine isUnit_iff_ne_zero.2 fun h => ?_
  rw [h, mul_zero, eq_comm, Complex.ofReal_eq_zero] at hdet
  exact hpos.det_pos.ne' hdet

/-! ### The Cayley form of a symplectic matrix -/

/-- The **symplectic Cayley form** `J (1 - A) (1 + A)⁻¹` of a real matrix `A`: `J` times the
Cayley transform of `A`. For a symplectic `A` it is symmetric
(`Matrix.isHermitian_symplecticCayley`), and when `1 + A` is invertible the diagonal graph of `A`
is its graph `{y + i B y}` (`Matrix.diagonalGraphFrame_eq_mul`). -/
def symplecticCayley (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  J n ℝ * (1 - A) * (1 + A)⁻¹

/-- The defining equation of the symplectic Cayley form: `B (1 + A) = J (1 - A)`. -/
theorem symplecticCayley_mul_one_add {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} (h : IsUnit (1 + A).det) :
    symplecticCayley A * (1 + A) = J n ℝ * (1 - A) := by
  rw [symplecticCayley, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one]

/-- If `B (1 + A) = J (1 - A)`, then `1 + A` is invertible: `(1 - J B) / 2` is a left inverse. -/
theorem isUnit_det_one_add_of_mul_one_add {A B : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hB : B * (1 + A) = J n ℝ * (1 - A)) : IsUnit (1 + A).det := by
  have h2 : (1 - J n ℝ * B) * (1 + A) = 1 + 1 := by
    rw [sub_mul, Matrix.one_mul, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, J_squared]
    noncomm_ring
  refine isUnit_det_of_left_inverse (B := (2⁻¹ : ℝ) • (1 - J n ℝ * B)) ?_
  rw [smul_mul_assoc, h2, ← two_smul ℝ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- The symplectic Cayley form is the unique solution `B` of `B (1 + A) = J (1 - A)`. -/
theorem eq_symplecticCayley_of_mul_one_add {A B : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hB : B * (1 + A) = J n ℝ * (1 - A)) : B = symplecticCayley A := by
  rw [symplecticCayley, ← hB, Matrix.mul_assoc,
    mul_nonsing_inv _ (isUnit_det_one_add_of_mul_one_add hB), Matrix.mul_one]

/-- The symplectic Cayley form of a symplectic matrix is symmetric. When `1 + A` is not
invertible it is `0`. -/
theorem isHermitian_symplecticCayley {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) : (symplecticCayley A).IsHermitian := by
  by_cases h : IsUnit (1 + A).det
  swap
  · rw [symplecticCayley, nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero]
    exact isHermitian_zero
  have hP : IsUnit (1 + A) := (isUnit_iff_isUnit_det _).2 h
  have hPT : IsUnit (1 + A)ᵀ := (isUnit_iff_isUnit_det _).2 (by rwa [det_transpose])
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  -- Conjugating by `1 + A` turns both sides into `(1 + A)ᵀ J (1 - A)`.
  refine hP.mul_right_cancel (hPT.mul_left_cancel ?_)
  rw [symplecticCayley_mul_one_add h, ← Matrix.mul_assoc (1 + A)ᵀ (symplecticCayley A)ᵀ,
    ← transpose_mul, symplecticCayley_mul_one_add h, transpose_one_add_mul_J_mul_one_sub hA]

/-- The diagonal graph frame is the graph frame `1 + i B` of the symplectic Cayley form `B`,
followed by the real change of basis `1 + A`. -/
theorem diagonalGraphFrame_eq_mul {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} (h : IsUnit (1 + A).det) :
    diagonalGraphFrame A =
      (1 + Complex.I • (symplecticCayley A).map (↑)) * (1 + A).map ((↑) : ℝ → ℂ) := by
  rw [diagonalGraphFrame, add_mul, Matrix.one_mul, smul_mul_assoc,
    ← symplecticCayley_mul_one_add h]
  exact congrArg _ (congrArg _ (Matrix.map_mul (f := Complex.ofRealHom)))

end Matrix

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two unitary frames of the same real subspace have the same Souriau map: they differ by a real
orthogonal matrix. -/
theorem souriau_eq_of_realImage_eq {U V : unitaryGroup n ℂ}
    (h : (U : Matrix n n ℂ).realImage = (V : Matrix n n ℂ).realImage) : souriau U = souriau V := by
  have hre (W : unitaryGroup n ℂ) :
      (((Unitary.toUnits W : GL n ℂ) : Matrix n n ℂ)ᴴ * Unitary.toUnits W).map Complex.re = 1 := by
    rw [Unitary.val_toUnits_apply, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 W.2,
      Matrix.map_one _ (by simp) (by simp)]
  obtain ⟨O, hO, hVO⟩ := exists_mem_orthogonalGroup_eq_mul_map_ofReal
    (M := Unitary.toUnits U) (M' := Unitary.toUnits V) (by simpa using h) (hre U) (hre V)
  have hOu := map_ofReal_mem_unitaryGroup hO
  have hVO' : V = U * ⟨_, hOu⟩ := Subtype.ext (by simpa using hVO)
  have hOO : O * Oᵀ = 1 := by
    simpa [star_eq_conjTranspose] using (mem_orthogonalGroup_iff n ℝ).1 hO
  rw [hVO', souriau_mul_of_mul_transpose_eq_one]
  rw [Subtype.coe_mk, ← transpose_map]
  exact (map_mul Complex.ofRealHom.mapMatrix _ _).symm.trans ((congrArg _ hOO).trans (map_one _))

end Matrix.UnitaryGroup

namespace TauCeti.GLSymplectic

open Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The unitary frame of the diagonal graph -/

/-- The diagonal graph frame of a symplectic matrix, as an invertible complex matrix. -/
private def diagonalGraphFrameUnit (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  ((isUnit_iff_isUnit_det _).2
    (isUnit_det_diagonalGraphFrame (mem_iff_mem_symplecticGroup.1 A.2))).unit

private theorem coe_diagonalGraphFrameUnit (A : GLSymplectic n ℝ) :
    (diagonalGraphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
  IsUnit.unit_spec _

private theorem continuous_diagonalGraphFrameUnit :
    Continuous (diagonalGraphFrameUnit : GLSymplectic n ℝ → GL (n ⊕ n) ℂ) := by
  refine Units.isOpenEmbedding_val.continuous_iff.2 ((continuous_diagonalGraphFrame.comp
    (Units.continuous_val.comp continuous_subtype_val)).congr fun A => ?_)
  exact (coe_diagonalGraphFrameUnit A).symm

/-- The **unitary frame of the diagonal graph** of a symplectic matrix `A`: the real
orthonormalization of the diagonal graph frame `(1 + A) + i J (1 - A)`. Its real span is the
image of the graph of `A` (`TauCeti.GLSymplectic.realImage_diagonalFrame`), and it depends
continuously on `A` (`TauCeti.GLSymplectic.continuous_diagonalFrame`). -/
def diagonalFrame (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  ⟨GeneralLinearGroup.realOrthonormalize (diagonalGraphFrameUnit A),
    GeneralLinearGroup.realOrthonormalize_mem_unitaryGroup <| by
      rw [coe_diagonalGraphFrameUnit,
        conjTranspose_diagonalGraphFrame_mul_self (mem_iff_mem_symplecticGroup.1 A.2)]
      ext : 2
      simp⟩

/-- The unitary frame of the diagonal graph spans the same real subspace as the diagonal graph
frame. -/
@[simp]
theorem realImage_diagonalFrame (A : GLSymplectic n ℝ) :
    (diagonalFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).realImage := by
  rw [diagonalFrame, Subtype.coe_mk, GeneralLinearGroup.realImage_realOrthonormalize,
    coe_diagonalGraphFrameUnit]

/-- The unitary frame of the diagonal graph depends continuously on the symplectic matrix. -/
theorem continuous_diagonalFrame :
    Continuous (diagonalFrame : GLSymplectic n ℝ → unitaryGroup (n ⊕ n) ℂ) :=
  Continuous.subtype_mk (Units.continuous_val.comp
    (GeneralLinearGroup.continuous_realOrthonormalize continuous_diagonalGraphFrameUnit)) _

/-- **The Souriau map of the diagonal frame is the Cayley transform of the symplectic Cayley
form.** When `1 + A` is invertible, the diagonal graph of `A` is the graph `{y + i B y}` of the
symmetric matrix `B = J (1 - A) (1 + A)⁻¹`, so its unitary frames have Souriau map the Cayley
transform `(1 + i B) (1 - i B)⁻¹`. -/
theorem souriau_diagonalFrame {A : GLSymplectic n ℝ}
    (h : IsUnit (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    (souriau (diagonalFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      cayley ((symplecticCayley ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map (↑)) := by
  refine souriau_eq_cayley_of_coe_eq_mul
    (isHermitian_symplecticCayley (mem_iff_mem_symplecticGroup.1 A.2))
    (M := (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *
      (((diagonalGraphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ)ᴴ *
        diagonalGraphFrameUnit A).map Complex.re ^ (-(1 / 2) : ℝ))) ?_
  rw [diagonalFrame, Subtype.coe_mk, GeneralLinearGroup.coe_realOrthonormalize,
    coe_diagonalGraphFrameUnit, diagonalGraphFrame_eq_mul h, Matrix.mul_assoc]
  exact congrArg _ (map_mul Complex.ofRealHom.mapMatrix _ _).symm

/-! ### The Conley–Zehnder index -/

/-- The **Conley–Zehnder index** of a path `γ` of symplectic matrices: minus the Maslov index,
relative to `ℝ^{n ⊕ n}`, of the unitary frames of its diagonal graphs. This is minus the
Robbin–Salamon index of the path of graphs `Γ(γ t)` relative to the diagonal; it counts the
crossings of the eigenvalue `1`, an endpoint with the eigenvalue `1` counting one half. -/
def conleyZehnderIndex {A B : GLSymplectic n ℝ} (γ : Path A B) : ℝ :=
  -maslovIndex (γ.map continuous_diagonalFrame)

/-- The Conley–Zehnder index is minus the Maslov index of the path of unitary frames of the
diagonal graphs. -/
theorem conleyZehnderIndex_def {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnderIndex γ = -maslovIndex (γ.map continuous_diagonalFrame) :=
  (rfl)

/-- **Independence of the frames.** The Conley–Zehnder index is minus the Maslov index of every
path of unitary frames of the diagonal graphs. -/
theorem conleyZehnderIndex_eq_neg_maslovIndex {A B : GLSymplectic n ℝ} (γ : Path A B)
    {U V : unitaryGroup (n ⊕ n) ℂ} (δ : Path U V)
    (hδ : ∀ t, (δ t : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (diagonalGraphFrame ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).realImage) :
    conleyZehnderIndex γ = -maslovIndex δ := by
  rw [conleyZehnderIndex, maslovIndex_eq_of_souriau_eq _ δ fun t =>
    souriau_eq_of_realImage_eq ((realImage_diagonalFrame (γ t)).trans (hδ t).symm)]

/-- **Homotopy invariance.** Paths of symplectic matrices that are homotopic relative to their
endpoints have the same Conley–Zehnder index. -/
theorem conleyZehnderIndex_eq_of_homotopic {A B : GLSymplectic n ℝ} {γ₀ γ₁ : Path A B}
    (h : γ₀.Homotopic γ₁) : conleyZehnderIndex γ₀ = conleyZehnderIndex γ₁ := by
  rw [conleyZehnderIndex, conleyZehnderIndex,
    maslovIndex_eq_of_homotopic (h.map ⟨_, continuous_diagonalFrame⟩)]

/-- The constant path has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnderIndex_refl (A : GLSymplectic n ℝ) : conleyZehnderIndex (Path.refl A) = 0 := by
  rw [conleyZehnderIndex, maslovIndex_eq_of_souriau_eq ((Path.refl A).map continuous_diagonalFrame)
    (Path.refl (diagonalFrame A)) fun _ => by simp, maslovIndex_refl, neg_zero]

/-- **Catenation.** The Conley–Zehnder index of a concatenation of paths is the sum of their
indices. -/
@[simp]
theorem conleyZehnderIndex_trans {A B C : GLSymplectic n ℝ} (γ₁ : Path A B) (γ₂ : Path B C) :
    conleyZehnderIndex (γ₁.trans γ₂) = conleyZehnderIndex γ₁ + conleyZehnderIndex γ₂ := by
  rw [conleyZehnderIndex, conleyZehnderIndex, conleyZehnderIndex, Path.map_trans, maslovIndex_trans,
    neg_add]

/-- Reversing a path negates its Conley–Zehnder index. -/
@[simp]
theorem conleyZehnderIndex_symm {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnderIndex γ.symm = -conleyZehnderIndex γ := by
  rw [conleyZehnderIndex, conleyZehnderIndex, ← Path.map_symm, maslovIndex_symm]

/-! ### Localization -/

/-- **Localization.** Along a path `γ` of symplectic matrices with `1 + γ t` invertible for every
`t`, the Conley–Zehnder index is minus half the change of the signature of the symplectic Cayley
form `J (1 - γ t) (1 + γ t)⁻¹`. -/
theorem conleyZehnderIndex_eq_neg_signature_sub {A B : GLSymplectic n ℝ} (γ : Path A B)
    (h : ∀ t, IsUnit (1 + ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    conleyZehnderIndex γ =
      -((signature (symplecticCayley ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) -
        signature (symplecticCayley ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) : ℝ) /
          2) := by
  have hγ : Continuous fun t => ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
    Units.continuous_val.comp (continuous_subtype_val.comp γ.continuous)
  have hc : Continuous fun t =>
      symplecticCayley ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
    simp only [symplecticCayley]
    exact continuous_iff_continuousAt.2 fun t =>
      (continuous_const.mul (continuous_const.sub hγ)).continuousAt.mul
        ((continuous_const.add hγ).continuousAt.matrix_inv (h t).ne_zero)
  have hloc := maslovIndex_eq_signature_sub_of_souriau_eq_cayley (γ.map continuous_diagonalFrame)
    hc (fun t => isHermitian_symplecticCayley (mem_iff_mem_symplecticGroup.1 (γ t).2))
    fun t => souriau_diagonalFrame (h t)
  rw [conleyZehnderIndex, hloc, γ.source, γ.target]

/-! ### Normalization -/

/-- For `|φ| < π`, `tan (φ / 2) (1 + e^{i φ}) = i (1 - e^{i φ})`: the rotation by `φ` has
symplectic Cayley form `tan (φ / 2)`. -/
private theorem tan_half_mul_one_add_exp {φ : ℝ} (hφ : |φ| < π) :
    (Real.tan (φ / 2) : ℂ) * (1 + Complex.exp (φ * Complex.I)) =
      Complex.I * (1 - Complex.exp (φ * Complex.I)) := by
  have hc : 0 < Real.cos (φ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩
  have hφ2 : φ = 2 * (φ / 2) := by ring
  apply Complex.ext <;>
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [hφ2, Real.cos_two_mul, Real.sin_two_mul, Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]

/-- For `|φ| < π`, `1 + e^{i φ} ≠ 0`. -/
private theorem one_add_exp_ne_zero {φ : ℝ} (hφ : |φ| < π) :
    1 + Complex.exp (φ * Complex.I) ≠ 0 := by
  intro h
  have := tan_half_mul_one_add_exp hφ
  rw [h, mul_zero, eq_comm, mul_eq_zero, sub_eq_zero] at this
  rcases this with h' | h'
  · exact Complex.I_ne_zero h'
  · rw [← h'] at h
    norm_num at h

/-- For `|φ| < π`, `tan (φ / 2)` has the sign of `φ`. -/
private theorem sign_tan_half {φ : ℝ} (hφ : |φ| < π) :
    (if 0 < Real.tan (φ / 2) then 1 else if Real.tan (φ / 2) < 0 then -1 else 0 : ℝ) =
      Real.sign φ := by
  rcases lt_trichotomy φ 0 with hn | hz | hp
  · have := Real.tan_neg_of_neg_of_pi_div_two_lt (x := φ / 2) (by linarith)
      (by linarith [neg_abs_le φ])
    simp [Real.sign_of_neg hn, this, this.not_gt]
  · simp [hz]
  · have := Real.tan_pos_of_pos_of_lt_pi_div_two (x := φ / 2) (by linarith)
      (by linarith [le_abs_self φ])
    simp [Real.sign_of_pos hp, this]

/-- `1 + R` is invertible for the realified diagonal rotation `R = diag (e^{i φ_j})`, `|φ_j| < π`:
it is the realification of `diag (1 + e^{i φ_j})`. -/
private theorem isUnit_det_one_add_realify_diagonal_exp {φ : n → ℝ} (hφ : ∀ j, |φ j| < π) :
    IsUnit (1 + (diagonal fun j => Complex.exp (φ j * Complex.I)).realify).det := by
  rw [← realify_one (𝕜 := ℂ), ← realify_add, ← diagonal_one, diagonal_add, det_realify,
    det_diagonal, isUnit_iff_ne_zero, RCLike.normSq_eq_def', ne_eq, pow_eq_zero_iff two_ne_zero,
    norm_eq_zero]
  exact Finset.prod_ne_zero_iff.2 fun j _ => one_add_exp_ne_zero (hφ j)

/-- The symplectic Cayley form of the realified diagonal rotation `diag (e^{i φ_j})`, `|φ_j| < π`,
is the realification of `diag (tan (φ_j / 2))`. -/
private theorem symplecticCayley_realify_diagonal_exp {φ : n → ℝ} (hφ : ∀ j, |φ j| < π) :
    symplecticCayley (diagonal fun j => Complex.exp (φ j * Complex.I)).realify =
      fromBlocks (diagonal fun j => Real.tan (φ j / 2)) 0 0
        (diagonal fun j => Real.tan (φ j / 2)) := by
  refine (eq_symplecticCayley_of_mul_one_add ?_).symm
  rw [← realify_map_ofReal (𝕜 := ℂ), diagonal_map (by simp), ← realify_I_smul_one (n := n),
    ← realify_one (𝕜 := ℂ), sub_eq_add_neg, ← realify_neg, ← realify_add, ← realify_add,
    ← realify_mul, ← realify_mul]
  congr 1
  ext i k
  by_cases hik : i = k
  · subst hik
    simpa [sub_eq_add_neg] using tan_half_mul_one_add_exp (hφ i)
  · simp [hik]

/-- The signature of the symplectic Cayley form of the realified diagonal rotation
`diag (e^{i φ_j})`, `|φ_j| < π`, is `2 ∑ⱼ sign φⱼ`. -/
private theorem signature_symplecticCayley_realify_diagonal_exp {φ : n → ℝ}
    (hφ : ∀ j, |φ j| < π) :
    (signature (symplecticCayley (diagonal fun j => Complex.exp (φ j * Complex.I)).realify) : ℝ) =
      2 * ∑ j, Real.sign (φ j) := by
  rw [symplecticCayley_realify_diagonal_exp hφ, signature_fromBlocks_zero, signature_diagonal,
    ← two_mul]
  push_cast
  exact congrArg _ (Finset.sum_congr rfl fun j _ => sign_tan_half (hφ j))

/-- **Normalization by rotations.** Let `θ : n → ℝ` with `|θ j| < π`, and let `γ` be a path of
symplectic matrices whose value at time `t` is the realification of the diagonal unitary matrix
`diag (e^{i t θ_j})`: the rotation by the angle `t θ_j` in the `j`-th complex coordinate line,
counterclockwise when `θ_j > 0`. Then `CZ(γ) = -∑ⱼ sign θⱼ`. -/
theorem conleyZehnderIndex_eq_neg_sum_sign_of_rotation {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → ℝ} (hθ : ∀ j, |θ j| < π)
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (((t : ℝ) * θ j : ℝ) * Complex.I)).realify) :
    conleyZehnderIndex γ = -∑ j, Real.sign (θ j) := by
  have hθt (t : I) (j : n) : |(t : ℝ) * θ j| < π := by
    rw [abs_mul, abs_of_nonneg t.2.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) t.2.2).trans_lt (hθ j)
  have hsig (t : I) : (signature (symplecticCayley
      ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) : ℝ) =
        2 * ∑ j, Real.sign ((t : ℝ) * θ j) := by
    rw [hγ, signature_symplecticCayley_realify_diagonal_exp (hθt t)]
  have h0 := hsig 0
  have h1 := hsig 1
  rw [γ.source] at h0
  rw [γ.target] at h1
  rw [conleyZehnderIndex_eq_neg_signature_sub γ fun t => by
    rw [hγ]; exact isUnit_det_one_add_realify_diagonal_exp (hθt t), h0, h1]
  simp

end TauCeti.GLSymplectic
