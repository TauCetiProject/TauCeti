/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Basic
-- Private: the grading of the exterior algebra, orthonormal bases in the Clifford algebra and the
-- separation of eigenspaces are used only inside proofs.
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import TauCeti.Geometry.Symplectic.Complex.QuadraticForm
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.Eigenspace.Separation

/-!
# The Kähler form on the Fock spinors of a complex structure

Let `V` be a real inner product space of dimension `n = 2ℓ`, `Q v = -‖v‖²`, and `J` an orthogonal
complex structure on `V`. The normalized Fock action
`c(v) = √2 (ε(v^(1,0)) - ι(v^(0,1)))` makes the exterior algebra `⋀ W` of the `i`-eigenspace `W`
of the complexified `J` a Clifford module (`TauCeti.AlmostComplexStructure.realFockAction`). This
is the pointwise model of the spinors of the canonical `Spinᶜ` structure of an almost Hermitian
manifold: `⋀ᵖ W` is the fibre of `Λ^(0,p)`, and for `n = 4` the positive half-spinors
`⋀⁰ W ⊕ ⋀² W` are the fibre of `1 ⊕ K⁻¹`, where `K` is the canonical line.

The Kähler form `ω` of `J` acts on this module diagonally in the exterior degree. For an
orthonormal basis `(e_k)` of `V`, the Clifford element `∑ₖ c(e_k) c(J e_k)` is twice the image
`c₂(ω)` of `ω` under Clifford multiplication by two-forms. It acts on a vector `v` by
`⁅∑ₖ c(e_k) c(J e_k), c(v)⁆ = 4 c(J v)`, and on the vacuum `1` by `-n i`, since
`c(u) c(J u) 1 = i Q(u)`. As `J` acts on `W` by `i`, the element `∑ₖ c(e_k) c(J e_k)` acts on
`⋀ᵖ W` by the scalar `i (4p - n)`, and `⋀ᵖ W` is exactly the eigenspace of this scalar.

In dimension four, for an orthonormal frame `(e₀, J e₀, e₂, J e₂)`, the Kähler form is
`ω = e₀ ∧ e₁ + e₂ ∧ e₃`, and `c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)` acts on `⋀ᵖ W` by
`i (2p - 2)`: by `-2i` on the vacuum line `⋀⁰ W`, by `0` on the negative half-spinors `⋀¹ W` and
by `2i` on the anticanonical line `⋀² W`. These are the eigenlines of `c₂(ω)` on the positive
half-spinors that enter Taubes's decomposition `ψ = α u₀ + β` of a positive spinor on a
symplectic four-manifold, with `u₀` the vacuum and `β` a section of `K⁻¹`.

## Main results

* `TauCeti.AlmostComplexStructure.sum_ι_mul_ι_lie_ι`: `⁅∑ₖ c(e_k) c(J e_k), c(v)⁆ = 4 c(J v)` in
  the Clifford algebra.
* `TauCeti.AlmostComplexStructure.realFockAction_sum_ι_mul_ι_of_mem_exteriorPower`:
  `∑ₖ c(e_k) c(J e_k)` acts on `⋀ᵖ W` by `i (4p - n)`.
* `TauCeti.AlmostComplexStructure.eigenspace_realFockAction_sum_ι_mul_ι`: its `i (4p - n)`
  eigenspace is `⋀ᵖ W`.
* `TauCeti.AlmostComplexStructure.realFockAction_bivectorExterior_of_mem_exteriorPower`: in
  dimension four, `c₂(ω)` acts on `⋀ᵖ W` by `i (2p - 2)`, and
  `TauCeti.AlmostComplexStructure.eigenspace_realFockAction_bivectorExterior`: its `i (2p - 2)`
  eigenspace is `⋀ᵖ W`.
* `TauCeti.AlmostComplexStructure.realFockAction_bivectorExterior_apply_one`: `c₂(ω) 1 = -2i`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra Module
open _root_.QuadraticMap (polar)
open scoped RealInnerProductSpace TensorProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℝ V) (e : OrthonormalBasis (Fin 4) ℝ V)

include hQJ hQ in
/-- **The Kähler element generates `J`**: for an orthonormal basis `(e_k)` of `V` and
`Q v = -‖v‖²`, the Clifford element `∑ₖ c(e_k) c(J e_k)`, which is twice the Clifford image of the
Kähler form of `J`, acts on generators by `⁅∑ₖ c(e_k) c(J e_k), c(v)⁆ = 4 c(J v)`. -/
theorem sum_ι_mul_ι_lie_ι (v : V) :
    ⁅∑ k, ι Q (b k) * ι Q (J (b k)), ι Q v⁆ = ι Q ((4 : ℝ) • J v) := by
  have hpolar (x y : V) : polar Q x y = -2 * ⟪x, y⟫ := by
    simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
    ring
  have h₁ : ∑ k, polar Q (J (b k)) v • b k = (2 : ℝ) • J v := by
    simp_rw [J.polar_apply_left_eq_neg_polar_apply_right hQJ, hpolar, neg_mul, neg_neg, mul_smul,
      ← Finset.smul_sum, b.sum_repr']
  have h₂ : ∑ k, polar Q (b k) v • J (b k) = (-2 : ℝ) • J v := by
    have h := congrArg J.toLinearMap (b.sum_repr' v)
    simp_rw [map_sum, map_smul] at h
    simp_rw [hpolar, mul_smul, ← Finset.smul_sum]
    exact congrArg _ h
  have hlie (u w : V) : ι Q u * ι Q w * ι Q v - ι Q v * (ι Q u * ι Q w) =
      ι Q (polar Q w v • u - polar Q u v • w) := by
    rw [← Ring.lie_def, ι_mul_ι_lie_ι]
  rw [Ring.lie_def, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [hlie]
  rw [← map_sum, Finset.sum_sub_distrib, h₁, h₂, ← sub_smul]
  norm_num

include hQJ hQ in
/-- The commutator of the complexified Kähler element with a complex generator:
`⁅∑ₖ c(e_k) c(J e_k), c(y)⁆ = 4 c(J y)` for every `y` in `ℂ ⊗ V`. -/
private theorem ofBaseChangeAux_sum_ι_mul_ι_mul_ι_sub (y : ℂ ⊗[ℝ] V) :
    ofBaseChangeAux ℂ Q (∑ k, ι Q (b k) * ι Q (J (b k))) * ι (Q.baseChange ℂ) y -
        ι (Q.baseChange ℂ) y * ofBaseChangeAux ℂ Q (∑ k, ι Q (b k) * ι Q (J (b k))) =
      (4 : ℂ) • ι (Q.baseChange ℂ) (J.toLinearMap.baseChange ℂ y) := by
  induction y using TensorProduct.inductionOn with
  | tmul c v =>
    have hc (w : V) : c ⊗ₜ[ℝ] w = c • ((1 : ℂ) ⊗ₜ[ℝ] w) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h := congrArg (ofBaseChangeAux ℂ Q) (J.sum_ι_mul_ι_lie_ι hQJ hQ b v)
    rw [Ring.lie_def, map_sub, map_mul, map_mul, ofBaseChangeAux_ι, ofBaseChangeAux_ι,
      TensorProduct.tmul_smul] at h
    rw [LinearMap.baseChange_tmul, hc, hc, map_smul, map_smul, smul_mul_assoc, mul_smul_comm,
      ← smul_sub, h, LinearMap.map_smul_of_tower]
    module
  | add y z hy hz => simp only [map_add, mul_add, add_mul, smul_add, ← hy, ← hz]; abel

include hQ in
/-- In an orthonormal frame `(e₀, J e₀, e₂, J e₂)`, the Clifford image of the Kähler form
`e₀ ∧ e₁ + e₂ ∧ e₃` is half of `∑ₖ c(e_k) c(J e_k)`. -/
private theorem bivectorExterior_kahler (he₁ : e 1 = J (e 0)) (he₃ : e 3 = J (e 2)) :
    bivectorExterior Q (exteriorPower.ιMulti ℝ 2 ![e 0, e 1] +
        exteriorPower.ιMulti ℝ 2 ![e 2, e 3]) =
      (2 : ℝ)⁻¹ • ∑ k, ι Q (e k) * ι Q (J (e k)) := by
  have hortho {i j : Fin 4} (hij : i ≠ j) : Q.IsOrtho (e i) (e j) :=
    (QuadraticMap.isOrtho_iff_inner_eq_zero hQ).2 (e.orthonormal.2 hij)
  have h₁ : ι Q (e 1) * ι Q (J (e 1)) = ι Q (e 0) * ι Q (e 1) := by
    rw [he₁, apply_apply, map_neg, mul_neg, ← he₁, ι_mul_ι_comm_of_isOrtho (hortho (by decide)),
      neg_neg]
  have h₃ : ι Q (e 3) * ι Q (J (e 3)) = ι Q (e 2) * ι Q (e 3) := by
    rw [he₃, apply_apply, map_neg, mul_neg, ← he₃, ι_mul_ι_comm_of_isOrtho (hortho (by decide)),
      neg_neg]
  rw [map_add, bivectorExterior_apply_ιMulti, bivectorExterior_apply_ιMulti,
    bivector_eq_ι_mul_ι_of_isOrtho Q (hortho (by decide)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (hortho (by decide)), Fin.sum_univ_four, h₁, h₃, ← he₁,
    ← he₃]
  module

/-! ### The action on the Fock module -/

section Fock

variable [FiniteDimensional ℝ V] (hQnd : Q.Nondegenerate)

include hQJ hQ in
/-- The Kähler element shifts the exterior degree of the Fock action by the scalar `4 i`:
`∑ₖ c(e_k) c(J e_k) (x ∧ s) = x ∧ (∑ₖ c(e_k) c(J e_k) s) + 4 i x ∧ s` for `x ∈ W`. -/
private theorem realFockAction_sum_ι_mul_ι_ι_mul (x : (J.spinPolarizationData hQJ hQnd).W)
    (s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :
    J.realFockAction hQJ hQnd (∑ k, ι Q (b k) * ι Q (J (b k))) (ExteriorAlgebra.ι ℂ x * s) =
      ExteriorAlgebra.ι ℂ x * J.realFockAction hQJ hQnd (∑ k, ι Q (b k) * ι Q (J (b k))) s +
        (4 * Complex.I) • (ExteriorAlgebra.ι ℂ x * s) := by
  have hx : J.toLinearMap.baseChange ℂ (x : ℂ ⊗[ℝ] V) = Complex.I • (x : ℂ ⊗[ℝ] V) := by
    have hmem : (x : ℂ ⊗[ℝ] V) ∈ Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I :=
      J.spinPolarizationData_W hQJ hQnd ▸ x.2
    exact Module.End.mem_eigenspace_iff.1 hmem
  have h := congr(J.fockAction hQJ hQnd
    $(J.ofBaseChangeAux_sum_ι_mul_ι_mul_ι_sub hQJ hQ b (x : ℂ ⊗[ℝ] V)) s)
  rw [hx] at h
  simp only [map_sub, map_mul, map_smul, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, fockAction_ι_coe_W, SpinPolarizationData.wedge_apply] at h
  rw [realFockAction_apply]
  refine smul_right_injective _ (by norm_num : (Real.sqrt 2 : ℂ) ≠ 0) ?_
  simp only [smul_add]
  linear_combination (norm := module) h

include hQ in
/-- The Kähler element acts on the vacuum `1` of the Fock module by `-n i`. -/
private theorem realFockAction_sum_ι_mul_ι_apply_one :
    J.realFockAction hQJ hQnd (∑ k, ι Q (b k) * ι Q (J (b k))) 1 =
      (-(Complex.I * finrank ℝ V)) • 1 := by
  simp only [map_sum, LinearMap.sum_apply,
    realFockAction_ι_mul_ι_apply_apply_one, hQ, b.orthonormal.1, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, finrank_eq_card_basis b.toBasis]
  congr 1
  push_cast
  ring

include hQ in
/-- **The Kähler form acts on the Fock module by the exterior degree.** For an orthonormal basis
`(e_k)` of `V` and `Q v = -‖v‖²`, the Clifford element `∑ₖ c(e_k) c(J e_k)`, twice the Clifford
image of the Kähler form of `J`, acts on `⋀ᵖ W` by the scalar `i (4p - n)`, where `n` is the
dimension of `V`. -/
theorem realFockAction_sum_ι_mul_ι_of_mem_exteriorPower {p : ℕ}
    {s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W}
    (hs : s ∈ ⋀[ℂ]^p (J.spinPolarizationData hQJ hQnd).W) :
    J.realFockAction hQJ hQnd (∑ k, ι Q (b k) * ι Q (J (b k))) s =
      (Complex.I * (4 * p - finrank ℝ V)) • s := by
  induction hs using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, J.realFockAction_sum_ι_mul_ι_apply_one hQJ hQ b,
      smul_comm]
    simp
  | add x y i _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨y, rfl⟩ := hm
    rw [J.realFockAction_sum_ι_mul_ι_ι_mul hQJ hQ b, hx, mul_smul_comm, ← add_smul]
    congr 1
    push_cast
    ring

include hQ in
/-- **The eigenspaces of the Kähler form on the Fock module are the exterior powers.** The
`i (4p - n)`-eigenspace of `∑ₖ c(e_k) c(J e_k)` on `⋀ W` is exactly `⋀ᵖ W`. -/
theorem eigenspace_realFockAction_sum_ι_mul_ι (p : ℕ) :
    Module.End.eigenspace (J.realFockAction hQJ hQnd (∑ k, ι Q (b k) * ι Q (J (b k))))
        (Complex.I * (4 * p - finrank ℝ V)) =
      ⋀[ℂ]^p (J.spinPolarizationData hQJ hQnd).W :=
  Module.End.eigenspace_eq_of_iSup_eq_top _ (W := fun q : ℕ ↦ ⋀[ℂ]^q _)
    (g := fun q : ℕ ↦ Complex.I * (4 * q - finrank ℝ V))
    (fun q ↦ fun _ hs ↦ Module.End.mem_eigenspace_iff.2
      (J.realFockAction_sum_ι_mul_ι_of_mem_exteriorPower hQJ hQ b hQnd hs))
    (DirectSum.Decomposition.isInternal _).submodule_iSup_eq_top
    (fun q q' h ↦ by simpa using mul_left_cancel₀ Complex.I_ne_zero h) p

/-! ### Dimension four -/

include hQ in
/-- **The Kähler form of a four-space acts on the Fock module by `i (2p - 2)` in degree `p`.** For
an orthonormal frame `(e₀, J e₀, e₂, J e₂)` and `Q v = -‖v‖²`, the Clifford image
`c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)` of the Kähler form `ω = e₀ ∧ e₁ + e₂ ∧ e₃` acts on `⋀ᵖ W` by
`i (2p - 2)`: by `-2i` on `⋀⁰ W`, by `0` on `⋀¹ W` and by `2i` on `⋀² W`. -/
theorem realFockAction_bivectorExterior_of_mem_exteriorPower (he₁ : e 1 = J (e 0))
    (he₃ : e 3 = J (e 2)) {p : ℕ} {s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W}
    (hs : s ∈ ⋀[ℂ]^p (J.spinPolarizationData hQJ hQnd).W) :
    J.realFockAction hQJ hQnd (bivectorExterior Q (exteriorPower.ιMulti ℝ 2 ![e 0, e 1] +
        exteriorPower.ιMulti ℝ 2 ![e 2, e 3])) s =
      (Complex.I * (2 * p - 2)) • s := by
  rw [J.bivectorExterior_kahler hQ e he₁ he₃, map_smul, LinearMap.smul_apply,
    J.realFockAction_sum_ι_mul_ι_of_mem_exteriorPower hQJ hQ e hQnd hs,
    finrank_eq_card_basis e.toBasis, Fintype.card_fin, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  ring

include hQ in
/-- **The vacuum is a `-2i`-eigenvector of the Kähler form**: in an orthonormal frame
`(e₀, J e₀, e₂, J e₂)`, `c₂(e₀ ∧ e₁ + e₂ ∧ e₃) 1 = -2i`. -/
theorem realFockAction_bivectorExterior_apply_one (he₁ : e 1 = J (e 0)) (he₃ : e 3 = J (e 2)) :
    J.realFockAction hQJ hQnd (bivectorExterior Q (exteriorPower.ιMulti ℝ 2 ![e 0, e 1] +
        exteriorPower.ιMulti ℝ 2 ![e 2, e 3])) 1 =
      (-2 * Complex.I) • 1 := by
  rw [J.realFockAction_bivectorExterior_of_mem_exteriorPower hQJ hQ e hQnd he₁ he₃
    (p := 0) (by simp)]
  congr 1
  push_cast
  ring

include hQ in
/-- **The eigenspaces of the Kähler form of a four-space on the Fock module.** In an orthonormal
frame `(e₀, J e₀, e₂, J e₂)`, the `i (2p - 2)`-eigenspace of `c₂(e₀ ∧ e₁ + e₂ ∧ e₃)` on `⋀ W` is
`⋀ᵖ W`. Thus the `-2i`-, `0`- and `2i`-eigenspaces are the vacuum line `⋀⁰ W`, the negative
half-spinors `⋀¹ W` and the anticanonical line `⋀² W`. -/
theorem eigenspace_realFockAction_bivectorExterior (he₁ : e 1 = J (e 0)) (he₃ : e 3 = J (e 2))
    (p : ℕ) :
    Module.End.eigenspace (J.realFockAction hQJ hQnd (bivectorExterior Q
        (exteriorPower.ιMulti ℝ 2 ![e 0, e 1] + exteriorPower.ιMulti ℝ 2 ![e 2, e 3])))
        (Complex.I * (2 * p - 2)) =
      ⋀[ℂ]^p (J.spinPolarizationData hQJ hQnd).W :=
  Module.End.eigenspace_eq_of_iSup_eq_top _ (W := fun q : ℕ ↦ ⋀[ℂ]^q _)
    (g := fun q : ℕ ↦ Complex.I * (2 * q - 2))
    (fun q ↦ fun _ hs ↦ Module.End.mem_eigenspace_iff.2
      (J.realFockAction_bivectorExterior_of_mem_exteriorPower hQJ hQ e hQnd he₁ he₃ hs))
    (DirectSum.Decomposition.isInternal _).submodule_iSup_eq_top
    (fun q q' h ↦ by simpa using mul_left_cancel₀ Complex.I_ne_zero h) p

end Fock

end TauCeti.AlmostComplexStructure
