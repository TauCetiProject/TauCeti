/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Basic
-- Private: the involution eigenspaces, orthonormal-basis orthogonality, the parity of the
-- dimension, list products of endomorphisms and the half-spin dimensions are used only inside
-- proofs.
import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.End.Basic
import TauCeti.RepresentationTheory.Spin.Dimension

/-!
# Chirality of the Fock module of an oriented Euclidean space

Let `V` be an oriented real inner product space of dimension `n`, `Q v = -‖v‖²`, and `J` an
orthogonal complex structure on `V`, so that `n = 2ℓ` is even. The `i`-eigenspace `W` of the
complexified `J` polarizes `Q.baseChange ℂ`, and the normalized Fock action
`c(v) = √2 (ε(v^(1,0)) - ι(v^(0,1)))` makes the exterior algebra `⋀ W` a module over the
complexified Clifford algebra (`TauCeti.AlmostComplexStructure.fockAction`). This is the native
model of the spinor module of `V`.

On the other hand, the orientation of `V` defines the normalized complex volume element
`Γ = i ^ ℓ c(e₁) ⋯ c(e₂ℓ)` (`CliffordAlgebra.complexVolume`), whose `±1` eigenspaces are the
half-spinors of the geometric model. This file compares the two when the orientation is the one
induced by `J`, that is, when some positively oriented orthonormal basis has the form
`(u₁, J u₁, …, u_ℓ, J u_ℓ)`: then **`Γ` acts on `⋀ W` by exterior parity**, the grade involution
of the exterior algebra. Consequently the positive half-spinors are the even forms, which contain
the vacuum `1`, the negative half-spinors are the odd forms, and both have complex dimension
`2 ^ (ℓ - 1)` when `ℓ ≠ 0`. Reversing the orientation negates `Γ`
(`CliffordAlgebra.complexVolume_neg_orientation`) and so interchanges the two labels.

In dimension four `Γ` is the chirality element `-c(e₁) c(e₂) c(e₃) c(e₄)`
(`CliffordAlgebra.chirality`) of the geometric model used by the Seiberg–Witten files, and the
comparison is restated for its action on `⋀ W` through the real Clifford algebra
(`TauCeti.AlmostComplexStructure.realFockAction`). Every orthogonal complex structure on a
four-space admits an adapted basis
(`TauCeti.AlmostComplexStructure.exists_adapted_orthonormalBasis`), so one of the two orientations
of `V` is always of this kind.

## Main results

* `TauCeti.AlmostComplexStructure.fockAction_complexVolume_apply_one`: the vacuum is a positive
  half-spinor, `Γ 1 = 1`.
* `TauCeti.AlmostComplexStructure.fockAction_complexVolume`: `Γ` acts on `⋀ W` by the grade
  involution `CliffordAlgebra.involute`.
* `TauCeti.AlmostComplexStructure.eigenspace_fockAction_complexVolume_one` and
  `TauCeti.AlmostComplexStructure.eigenspace_fockAction_complexVolume_neg_one`: the `+1` and `-1`
  eigenspaces of `Γ` are the even and odd half-spin summands `TauCeti.spinPlus` and
  `TauCeti.spinMinus`.
* `TauCeti.AlmostComplexStructure.finrank_eigenspace_fockAction_complexVolume_one` and
  `TauCeti.AlmostComplexStructure.finrank_eigenspace_fockAction_complexVolume_neg_one`: both
  half-spinor spaces have complex dimension `2 ^ (ℓ - 1)`.
* `TauCeti.AlmostComplexStructure.realFockAction_chirality`,
  `TauCeti.AlmostComplexStructure.positiveHalfSpinors_realFockAction` and
  `TauCeti.AlmostComplexStructure.eigenspace_realFockAction_chirality_neg_one`: the
  four-dimensional chirality element acts by exterior parity, with the even and odd forms as its
  eigenspaces, each of complex dimension two.

## Implementation notes

The vacuum is fixed by `Γ` because `c(u) c(J u) 1 = i Q(u) = -i` for every unit vector `u`, and
`i ^ ℓ (-i) ^ ℓ = 1`. The identity then propagates along exterior multiplication: a vector of `W`
acts by `√2` times exterior multiplication and anticommutes with `Γ`, as every complex vector does
in even dimension.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra Module
open scoped RealInnerProductSpace TensorProduct

/-! ### The normalized complex volume element in every even dimension -/

section ComplexVolume

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

/-- A space carrying a complex structure has even dimension. -/
private theorem even_of_almostComplexStructure (J : AlmostComplexStructure V) : Even n :=
  (Fact.out : finrank ℝ V = n) ▸ J.even_finrank_real

variable [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))
  (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)

/-- `Γ` anticommutes with exterior multiplication by a vector of `W`. -/
private theorem fockAction_complexVolume_ι_mul (x : (J.spinPolarizationData hQJ hQnd).W)
    (s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :
    J.fockAction hQJ hQnd (complexVolume Q o) (ExteriorAlgebra.ι ℂ x * s) =
      -(ExteriorAlgebra.ι ℂ x * J.fockAction hQJ hQnd (complexVolume Q o) s) := by
  have h := congr(J.fockAction hQJ hQnd $(complexVolume_mul_ι_of_even o
    (even_of_almostComplexStructure J) (x : ℂ ⊗[ℝ] V)) s)
  simp only [map_mul, map_neg, Module.End.mul_apply, LinearMap.neg_apply,
    J.fockAction_ι_coe_W hQJ hQnd, LinearMap.smul_apply, SpinPolarizationData.wedge_apply,
    map_smul, ← smul_neg] at h
  exact smul_right_injective _ (by norm_num : (Real.sqrt 2 : ℂ) ≠ 0) h

variable {o} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **The vacuum is a positive half-spinor**: if the orientation of `V` is induced by `J`, in the
sense that some positively oriented orthonormal basis has the form `(u₁, J u₁, …, u_ℓ, J u_ℓ)`,
then `Γ` fixes the vacuum `1` of `⋀ W`. -/
theorem fockAction_complexVolume_apply_one (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (k : ℕ) (hk : 2 * k + 1 < n), b ⟨2 * k + 1, hk⟩ = J (b ⟨2 * k, by omega⟩)) :
    J.fockAction hQJ hQnd (complexVolume Q o) 1 = 1 := by
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, n = 2 * ℓ := by
    obtain ⟨ℓ, hℓ⟩ := even_of_almostComplexStructure (n := n) J
    exact ⟨ℓ, by omega⟩
  have hQb (i : Fin (2 * ℓ)) : Q (b i) = -1 := by rw [hQ, b.orthonormal.1 i]; norm_num
  -- `Γ` is `i ^ ℓ` times the `ℓ` pairs `c(u) c(J u)`, each acting on the vacuum by `-i`.
  rw [complexVolume_eq_prod_pairs b hb (b.isOrthoᵢ_associated hQ), map_smul, map_list_prod,
    LinearMap.smul_apply, Module.End.list_prod_apply_eq_pow_smul (z := -Complex.I)]
  · simp [smul_smul, ← mul_pow]
  · simp only [List.mem_map, List.mem_ofFn, forall_exists_index, and_imp]
    rintro _ _ k rfl rfl
    rw [hbJ k (by omega), map_mul, ← realFockAction_ι, ← realFockAction_ι, ← map_mul,
      realFockAction_ι_mul_ι_apply_apply_one, hQb]
    simp

/-- **`Γ` is exterior parity on the Fock module.** If the orientation of `V` is induced by `J`, in
the sense that some positively oriented orthonormal basis has the form
`(u₁, J u₁, …, u_ℓ, J u_ℓ)`, then the normalized complex volume element `Γ` acts on `⋀ W` by the
grade involution. -/
theorem fockAction_complexVolume (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (k : ℕ) (hk : 2 * k + 1 < n), b ⟨2 * k + 1, hk⟩ = J (b ⟨2 * k, by omega⟩)) :
    J.fockAction hQJ hQnd (complexVolume Q o) = involute.toLinearMap := by
  have hvac := J.fockAction_complexVolume_apply_one hQJ hQnd hQ b hb hbJ
  refine LinearMap.ext fun s ↦ ?_
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, hvac]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul x m hx => simp [J.fockAction_complexVolume_ι_mul o hQJ hQnd, hx]

/-- **The positive half-spinors of the Fock module are the even forms**, for the orientation
induced by `J`. -/
theorem eigenspace_fockAction_complexVolume_one (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (k : ℕ) (hk : 2 * k + 1 < n), b ⟨2 * k + 1, hk⟩ = J (b ⟨2 * k, by omega⟩)) :
    Module.End.eigenspace (J.fockAction hQJ hQnd (complexVolume Q o)) 1 =
      spinPlus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  ext s
  rw [Module.End.mem_eigenspace_iff, J.fockAction_complexVolume hQJ hQnd hQ b hb hbJ,
    AlgHom.toLinearMap_apply, one_smul, involute_eq_self_iff, mem_spinPlus]

/-- **The negative half-spinors of the Fock module are the odd forms**, for the orientation
induced by `J`. -/
theorem eigenspace_fockAction_complexVolume_neg_one (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (k : ℕ) (hk : 2 * k + 1 < n), b ⟨2 * k + 1, hk⟩ = J (b ⟨2 * k, by omega⟩)) :
    Module.End.eigenspace (J.fockAction hQJ hQnd (complexVolume Q o)) (-1) =
      spinMinus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  ext s
  rw [Module.End.mem_eigenspace_iff, J.fockAction_complexVolume hQJ hQnd hQ b hb hbJ,
    AlgHom.toLinearMap_apply, neg_one_smul, involute_eq_neg_iff, mem_spinMinus]

/-- In positive dimension `n` the positive half-spinors of the Fock module have complex dimension
`2 ^ (n / 2 - 1)`. -/
theorem finrank_eigenspace_fockAction_complexVolume_one (hn : n ≠ 0)
    (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (k : ℕ) (hk : 2 * k + 1 < n), b ⟨2 * k + 1, hk⟩ = J (b ⟨2 * k, by omega⟩)) :
    finrank ℂ (Module.End.eigenspace (J.fockAction hQJ hQnd (complexVolume Q o)) 1) =
      2 ^ (n / 2 - 1) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [Fact.out (p := finrank ℝ V = n)]; omega)
  rw [J.eigenspace_fockAction_complexVolume_one hQJ hQnd hQ b hb hbJ,
    finrank_spinPlus _ (J.spinPolarizationData_W_ne_bot hQJ hQnd),
    J.finrank_spinPolarizationData_W hQJ hQnd, Fact.out (p := finrank ℝ V = n)]

/-- In positive dimension `n` the negative half-spinors of the Fock module have complex dimension
`2 ^ (n / 2 - 1)`. -/
theorem finrank_eigenspace_fockAction_complexVolume_neg_one (hn : n ≠ 0)
    (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (k : ℕ) (hk : 2 * k + 1 < n), b ⟨2 * k + 1, hk⟩ = J (b ⟨2 * k, by omega⟩)) :
    finrank ℂ (Module.End.eigenspace (J.fockAction hQJ hQnd (complexVolume Q o)) (-1)) =
      2 ^ (n / 2 - 1) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [Fact.out (p := finrank ℝ V = n)]; omega)
  rw [J.eigenspace_fockAction_complexVolume_neg_one hQJ hQnd hQ b hb hbJ,
    finrank_spinMinus _ (J.spinPolarizationData_W_ne_bot hQJ hQnd),
    J.finrank_spinPolarizationData_W hQJ hQnd, Fact.out (p := finrank ℝ V = n)]

end ComplexVolume

/-! ### The chirality element of an oriented four-space -/

section Chirality

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- **Chirality is exterior parity on the Fock module.** If the orientation of `V` is induced by
`J`, in the sense that some positively oriented orthonormal basis has the form
`(u₁, J u₁, u₂, J u₂)`, then the chirality element `Γ` acts on `⋀ W` by the grade involution. -/
theorem realFockAction_chirality (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    J.realFockAction hQJ hQnd (chirality Q o) = involute.toLinearMap := by
  rw [realFockAction_apply, ofBaseChangeAux_chirality,
    J.fockAction_complexVolume hQJ hQnd hQ b hb]
  intro k hk
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  exacts [hb₁, hb₃]

/-- **The positive half-spinors of the Fock module are the even forms** `⋀⁰ W ⊕ ⋀² W`, for the
orientation induced by `J`. -/
theorem positiveHalfSpinors_realFockAction (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    positiveHalfSpinors o (J.realFockAction hQJ hQnd) =
      spinPlus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  ext s
  rw [mem_positiveHalfSpinors, J.realFockAction_chirality hQJ hQnd hQ b hb hb₁ hb₃,
    AlgHom.toLinearMap_apply, involute_eq_self_iff, mem_spinPlus]

/-- **The negative half-spinors of the Fock module are the odd forms** `⋀¹ W`, for the
orientation induced by `J`. -/
theorem eigenspace_realFockAction_chirality_neg_one (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    Module.End.eigenspace (J.realFockAction hQJ hQnd (chirality Q o)) (-1) =
      spinMinus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  ext s
  rw [Module.End.mem_eigenspace_iff, J.realFockAction_chirality hQJ hQnd hQ b hb hb₁ hb₃,
    AlgHom.toLinearMap_apply, neg_one_smul, involute_eq_neg_iff, mem_spinMinus]

/-- The positive half-spinors of the Fock module have complex dimension two. -/
theorem finrank_positiveHalfSpinors_realFockAction (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    finrank ℂ (positiveHalfSpinors o (J.realFockAction hQJ hQnd)) = 2 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  rw [J.positiveHalfSpinors_realFockAction hQJ hQnd hQ b hb hb₁ hb₃,
    finrank_spinPlus _ (J.spinPolarizationData_W_ne_bot hQJ hQnd),
    J.finrank_spinPolarizationData_W hQJ hQnd, Fact.out (p := finrank ℝ V = 4)]
  norm_num

/-- The negative half-spinors of the Fock module have complex dimension two. -/
theorem finrank_eigenspace_realFockAction_chirality_neg_one (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    finrank ℂ (Module.End.eigenspace (J.realFockAction hQJ hQnd (chirality Q o)) (-1)) = 2 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  rw [J.eigenspace_realFockAction_chirality_neg_one hQJ hQnd hQ b hb hb₁ hb₃,
    finrank_spinMinus _ (J.spinPolarizationData_W_ne_bot hQJ hQnd),
    J.finrank_spinPolarizationData_W hQJ hQnd, Fact.out (p := finrank ℝ V = 4)]
  norm_num

end Chirality

end TauCeti.AlmostComplexStructure
