/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.RingTheory.Idempotents.SquareRootOne
-- Private: the following are used only inside proofs: the dimension `2 ^ (n / 2)` of a spinor
-- module, the eigenspace splitting and anticommutation lemmas for endomorphisms, and the Morita
-- evaluation of eigenspaces.
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.Eigenspace.Anticommute
import TauCeti.LinearAlgebra.Eigenspace.Separation
import TauCeti.RingTheory.Morita.Eigenspace

/-!
# The chirality decomposition of a complex Clifford module

Let `V` be an oriented real inner product space of dimension `n`, `Q v = -‖v‖²`, and let `E` be
an arbitrary module over the complexified Clifford algebra `Cℓ = CliffordAlgebra (Q.baseChange ℂ)`.
The normalized complex volume element `Γ` (`CliffordAlgebra.complexVolume`) squares to `1`, so `E`
is the direct sum of its eigenspaces

`E⁺ = {ψ | Γ ψ = ψ}`,  `E⁻ = {ψ | Γ ψ = -ψ}`,

with the projections onto them given by the action of the idempotents `½ (1 ± Γ)`
(`TauCeti.halfOneAdd`). Nothing is assumed of `E`: it need not be finite-dimensional, irreducible
or Hermitian.

In even dimension `Γ` commutes with even elements and anticommutes with odd ones, so even elements
preserve `E⁺` and `E⁻` while odd elements, in particular all vectors, exchange them. For a unit
vector `v` the operator `c(v)` squares to `-1`, so it identifies the two eigenspaces and they have
the same dimension as soon as `n > 0`. In odd dimension `Γ` is central, so `E⁺` and `E⁻` are
preserved by the whole Clifford algebra: they are the two multiplicity pieces of `E` for the two
central factors labelled by `Γ = ±1`.

Finally, let `S` be a spinor module, a finite-dimensional `Cℓ`-module on which `Cℓ` acts as the
whole of `End_ℂ S`, as for the Fock module of an even-dimensional space
(`TauCeti.SpinPolarizationData.cliffordEquivEnd`). Then `dim S = 2 ^ (n / 2)`
(`CliffordAlgebra.finrank_eq_two_pow_of_bijective_lsmul`), its half-spin
spaces `S⁺` and `S⁻` both have dimension `2 ^ (n / 2 - 1)`, and by Morita evaluation
(`TauCeti.eigenspaceTensorEquivOfBijective`) every module satisfies

`E⁺ ≃ S⁺ ⊗ Hom_Cℓ(S, E)`,  `E⁻ ≃ S⁻ ⊗ Hom_Cℓ(S, E)`,

so that `dim E^± = 2 ^ (n / 2 - 1) · dim Hom_Cℓ(S, E)`.

## Main results

* `CliffordAlgebra.isCompl_eigenspace_complexVolume`: `E = E⁺ ⊕ E⁻`.
* `CliffordAlgebra.projection_eigenspace_complexVolume_apply` and
  `CliffordAlgebra.projection_eigenspace_complexVolume_neg_one_apply`: the projections onto `E⁺`
  and `E⁻` are `½ (1 + Γ)` and `½ (1 - Γ)`.
* `CliffordAlgebra.smul_mem_eigenspace_complexVolume_of_mem_even`,
  `CliffordAlgebra.smul_mem_eigenspace_complexVolume_neg_of_mem_odd` and
  `CliffordAlgebra.ι_smul_mem_eigenspace_complexVolume_neg`: in even dimension, even elements
  preserve the eigenspaces and odd elements and vectors exchange them.
* `CliffordAlgebra.smul_mem_eigenspace_complexVolume_of_odd`: in odd dimension, the whole
  Clifford algebra preserves the eigenspaces.
* `CliffordAlgebra.finrank_eigenspace_complexVolume_neg`: in even positive dimension,
  `dim E⁻ = dim E⁺`.
* `CliffordAlgebra.finrank_eigenspace_complexVolume_of_bijective_lsmul`: the half-spin spaces of
  a spinor module have dimension `2 ^ (n / 2 - 1)`.
* `CliffordAlgebra.finrank_eigenspace_complexVolume_eq_mul_finrank_linearMap`:
  `dim E^± = 2 ^ (n / 2 - 1) · dim Hom_Cℓ(S, E)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, the chapter on Clifford modules.
-/

public section

noncomputable section

open Module Module.End TauCeti
open scoped TensorProduct

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module (CliffordAlgebra (Q.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E]

/-! ### Clifford multiplication and the eigenspaces of `Γ` -/

/-- In even dimension an even Clifford element preserves each eigenspace of `Γ`. -/
theorem smul_mem_eigenspace_complexVolume_of_mem_even (hn : Even n)
    {x : CliffordAlgebra (Q.baseChange ℂ)} (hx : x ∈ evenOdd (Q.baseChange ℂ) 0) {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) :
    x • ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe] at hψ ⊢
  rw [← mul_smul, (commute_complexVolume_of_mem_even o hn hx).eq, mul_smul, hψ, smul_comm]

/-- In even dimension an odd Clifford element maps the `μ`-eigenspace of `Γ` into the
`-μ`-eigenspace. -/
theorem smul_mem_eigenspace_complexVolume_neg_of_mem_odd (hn : Even n)
    {x : CliffordAlgebra (Q.baseChange ℂ)} (hx : x ∈ evenOdd (Q.baseChange ℂ) 1) {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) :
    x • ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-μ) := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe] at hψ ⊢
  rw [← mul_smul, complexVolume_mul_of_mem_odd o hn hx, neg_smul, mul_smul, hψ, smul_comm,
    neg_smul]

/-- **Vectors exchange the half-spinors**: in even dimension Clifford multiplication by a vector
maps the `μ`-eigenspace of `Γ` into the `-μ`-eigenspace. -/
theorem ι_smul_mem_eigenspace_complexVolume_neg (hn : Even n) (w : ℂ ⊗[ℝ] V) {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) :
    ι (Q.baseChange ℂ) w • ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-μ) :=
  smul_mem_eigenspace_complexVolume_neg_of_mem_odd o hn (ι_mem_evenOdd_one _ w) hψ

/-- In odd dimension `Γ` is central, so every Clifford element preserves each eigenspace of `Γ`. -/
theorem smul_mem_eigenspace_complexVolume_of_odd (hn : Odd n)
    (x : CliffordAlgebra (Q.baseChange ℂ)) {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) :
    x • ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe] at hψ ⊢
  rw [← mul_smul, ← Subalgebra.mem_center_iff.1 (complexVolume_mem_center o hn) x, mul_smul, hψ,
    smul_comm]

/-! ### The decomposition `E = E⁺ ⊕ E⁻` -/

section Form

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **The chirality decomposition**: every module over the complexified Clifford algebra is the
direct sum of the `1`- and `-1`-eigenspaces of `Γ`. -/
theorem isCompl_eigenspace_complexVolume :
    IsCompl ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace 1)
      ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-1)) :=
  isCompl_eigenspace_one_neg_one two_ne_zero.isUnit fun ψ ↦ by
    simp only [Algebra.lsmul_coe]
    rw [← mul_smul, complexVolume_mul_self o hQ, one_smul]

/-- `½ (1 + Γ)` maps every vector into the `1`-eigenspace of `Γ`. -/
theorem halfOneAdd_smul_mem_eigenspace_complexVolume (ψ : E) :
    halfOneAdd ℂ (complexVolume Q o) • ψ ∈
      (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace 1 := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe]
  rw [← mul_smul, mul_halfOneAdd ℂ (complexVolume_mul_self o hQ), one_smul]

/-- `½ (1 - Γ)` maps every vector into the `-1`-eigenspace of `Γ`. -/
theorem halfOneAdd_neg_smul_mem_eigenspace_complexVolume (ψ : E) :
    halfOneAdd ℂ (-complexVolume Q o) • ψ ∈
      (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-1) := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe]
  rw [← mul_smul, mul_halfOneAdd_neg ℂ (complexVolume_mul_self o hQ), neg_smul, neg_one_smul]

omit hQ [Module ℂ E] [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E] in
/-- Every vector is the sum of its components `½ (1 + Γ) ψ` and `½ (1 - Γ) ψ`. -/
private theorem halfOneAdd_smul_add_halfOneAdd_neg_smul (ψ : E) :
    halfOneAdd ℂ (complexVolume Q o) • ψ + halfOneAdd ℂ (-complexVolume Q o) • ψ = ψ := by
  rw [← add_smul, halfOneAdd_add_halfOneAdd_neg, one_smul]

/-- **The projection onto the `1`-eigenspace** of `Γ`, along the `-1`-eigenspace, is the action
of `½ (1 + Γ)`. -/
theorem projection_eigenspace_complexVolume_apply (ψ : E) :
    Submodule.projection _ _ (isCompl_eigenspace_complexVolume (Q := Q) (E := E) o hQ) ψ =
      halfOneAdd ℂ (complexVolume Q o) • ψ := by
  conv_lhs => rw [← halfOneAdd_smul_add_halfOneAdd_neg_smul (Q := Q) o ψ]
  rw [map_add, Submodule.projection_apply_of_mem_left _
      (halfOneAdd_smul_mem_eigenspace_complexVolume o hQ ψ),
    Submodule.projection_apply_of_mem_right _
      (halfOneAdd_neg_smul_mem_eigenspace_complexVolume o hQ ψ), add_zero]

/-- **The projection onto the `-1`-eigenspace** of `Γ`, along the `1`-eigenspace, is the action
of `½ (1 - Γ)`. -/
theorem projection_eigenspace_complexVolume_neg_one_apply (ψ : E) :
    Submodule.projection _ _ (isCompl_eigenspace_complexVolume (Q := Q) (E := E) o hQ).symm ψ =
      halfOneAdd ℂ (-complexVolume Q o) • ψ := by
  conv_lhs => rw [← halfOneAdd_smul_add_halfOneAdd_neg_smul (Q := Q) o ψ]
  rw [map_add, Submodule.projection_apply_of_mem_right _
      (halfOneAdd_smul_mem_eigenspace_complexVolume o hQ ψ),
    Submodule.projection_apply_of_mem_left _
      (halfOneAdd_neg_smul_mem_eigenspace_complexVolume o hQ ψ), zero_add]

/-- **The half-spinors have equal dimension**: in even positive dimension, Clifford
multiplication by a unit vector identifies the `μ`- and `-μ`-eigenspaces of `Γ`. -/
theorem finrank_eigenspace_complexVolume_neg (hn : Even n) (hn0 : n ≠ 0) (μ : ℂ) :
    finrank ℂ ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-μ)) =
      finrank ℂ ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [Fact.out (p := finrank ℝ V = n)]; exact Nat.pos_of_ne_zero hn0)
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  set c := ι (Q.baseChange ℂ) (1 ⊗ₜ (‖u‖⁻¹ • u))
  -- The unit vector `‖u‖⁻¹ • u` has `c² = Q (‖u‖⁻¹ • u) = -1`.
  have hc : c * c = -1 := by
    have hv : ‖‖u‖⁻¹ • u‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hu)]
    rw [ι_sq_scalar, QuadraticForm.baseChange_tmul, hQ, hv, one_pow, mul_one, neg_smul, one_smul,
      map_neg, map_one]
  let e : E ≃ₗ[ℂ] E := .ofLinearMap (Algebra.lsmul ℂ ℂ E c) (Algebra.lsmul ℂ ℂ E (-c))
    (by ext ψ; simp [← mul_smul, hc]) (by ext ψ; simp [← mul_smul, hc])
  refine finrank_genEigenspace_neg_of_anticommute e ?_ μ 1
  have hanti : complexVolume Q o * c + c * complexVolume Q o = 0 := by
    rw [complexVolume_mul_ι_of_even o hn, neg_add_cancel]
  ext ψ
  simp [e, ← mul_smul, ← add_smul, hanti]

/-! ### The half-spin spaces of a spinor module -/

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S] [FiniteDimensional ℂ S]
  (h : Function.Bijective
    (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))

include h in
/-- **The half-spin spaces of a spinor module**: in even positive dimension, both eigenspaces of
`Γ` on a spinor module have dimension `2 ^ (n / 2 - 1)`. -/
theorem finrank_eigenspace_complexVolume_of_bijective_lsmul (hn : Even n) (hn0 : n ≠ 0) {μ : ℂ}
    (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace μ) = 2 ^ (n / 2 - 1) := by
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspace_complexVolume (E := S) o hQ)
  have hV : finrank ℂ (ℂ ⊗[ℝ] V) = n := by
    rw [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = n)]
  have hS : finrank ℂ S = 2 ^ (n / 2) := by
    rw [finrank_eq_two_pow_of_bijective_lsmul _ h (hV ▸ hn), hV]
  rw [hS, finrank_eigenspace_complexVolume_neg o hQ hn hn0 1] at hsum
  have hpow : 2 ^ (n / 2) = 2 * 2 ^ (n / 2 - 1) := by
    rw [← pow_succ']
    congr 1
    obtain ⟨m, rfl⟩ := hn
    omega
  have h1 : finrank ℂ ((Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace 1) =
      2 ^ (n / 2 - 1) := by
    omega
  rcases hμ with rfl | rfl
  · exact h1
  · rw [finrank_eigenspace_complexVolume_neg o hQ hn hn0 1, h1]

include h in
/-- **The half-spinors of an arbitrary module**: in even positive dimension, each eigenspace of
`Γ` on a module `E` has dimension `2 ^ (n / 2 - 1)` times the dimension of the multiplicity space
`S →ₗ[Cℓ] E` of a spinor module `S`; the underlying isomorphism `E^± ≃ S^± ⊗ Hom_Cℓ(S, E)` is
`TauCeti.eigenspaceTensorEquivOfBijective h (complexVolume Q o) (±1)`. -/
theorem finrank_eigenspace_complexVolume_eq_mul_finrank_linearMap (hn : Even n) (hn0 : n ≠ 0)
    {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) =
      2 ^ (n / 2 - 1) * finrank ℂ (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) := by
  rw [finrank_eigenspace_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul h,
    finrank_eigenspace_complexVolume_of_bijective_lsmul o hQ h hn hn0 hμ]

end Form

end CliffordAlgebra
