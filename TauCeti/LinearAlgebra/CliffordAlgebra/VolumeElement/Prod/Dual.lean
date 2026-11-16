/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Dual
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Dual
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.NegGrading

/-!
# Reverse duality of the graded complex Clifford tensor product

Let `V` be an oriented even-dimensional real inner product space of dimension `n = 2ℓ` with
`Q₁ v = -‖v‖²`, and let `W` be a real inner product space with quadratic form `Q₂`. On the reverse
dual `E*` (`AlgHom.cliffordReverseDual`), the chirality operator `Γ_V` acts by
`(-1) ^ ℓ Γ_Vᵀ` (`AlgHom.cliffordReverseDual_complexVolume`), whereas
`AlgHom.dualDistrib_cliffordProdTensor` uses the unnegated transpose `Γ_Vᵀ` as the grading on `E*`.

The comparison between `complexProdTensor` of the reverse duals on `E* ⊗ F*` and the reverse dual
of `complexProdTensor` on `(E ⊗ F)*` therefore splits by the parity of `ℓ = n / 2`:

* **When `ℓ` is even** (`n ≡ 0 mod 4`), `Γ_(E*) = Γ_Vᵀ`, so the canonical map
  `TensorProduct.dualDistrib ℂ E F : E* ⊗ F* → (E ⊗ F)*` directly intertwines the two Clifford
  actions, with no finiteness on `E`, `F` and no hypotheses on `W` or `Q₂`. When `E` and `F` are
  finite-dimensional, `TensorProduct.dualDistribEquiv` conjugates the two actions.
* **When `ℓ` is odd** (`n ≡ 2 mod 4`), `Γ_(E*) = -Γ_Vᵀ`. When `W` is even-dimensional and
  oriented, `Γ_(F*)` anticommutes with every vector of `W`, so the composite
  `dualDistrib ∘ (1 ⊗ Γ_(F*))` intertwines the two Clifford actions for an arbitrary quadratic
  form `Q₂` and arbitrary modules `E`, `F`. When moreover `Q₂ w = -‖w‖²` and `E`, `F` are
  finite-dimensional, `dualDistribEquiv ∘ (1 ⊗ Γ_(F*))` conjugates the two actions.

## Main results

* `CliffordAlgebra.dualDistrib_complexProdTensor_of_even`: for even `n / 2`, `dualDistrib`
  intertwines `complexProdTensor` of reverse duals with the reverse dual of `complexProdTensor`.
* `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_even`: equivalence form for
  finite-dimensional `E` and `F` when `n / 2` is even.
* `CliffordAlgebra.dualDistrib_comp_lTensor_complexProdTensor_of_odd`: for odd `n / 2` and even
  `m`, `dualDistrib ∘ (1 ⊗ Γ_(F*))` intertwines the two actions.
* `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_odd`: equivalence form for
  finite-dimensional `E` and `F`, even `m`, and `Q₂ w = -‖w‖²` when `n / 2` is odd.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- Reverse duality commutes with precomposition by an isometry equivalence of Clifford algebras,
because `CliffordAlgebra.map_reverse` holds for every quadratic isometry. -/
private theorem cliffordReverseDual_comp_equivOfIsometry {R K M₁ M₂ S : Type*} [CommRing R]
    [CommRing K] [Algebra R K] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    {P₁ : QuadraticForm R M₁} {P₂ : QuadraticForm R M₂}
    [AddCommGroup S] [Module K S] [Module R S] [IsScalarTower R K S]
    (e : P₁.IsometryEquiv P₂) (φ : CliffordAlgebra P₂ →ₐ[R] Module.End K S)
    (a : CliffordAlgebra P₁) :
    (φ.comp (equivOfIsometry e).toAlgHom).cliffordReverseDual a =
      φ.cliffordReverseDual (equivOfIsometry e a) := by
  ext ψ s
  simp [AlgHom.cliffordReverseDual_apply_apply, equivOfIsometry_apply]

section EvenHalfDim

/-- **Reverse duality of `complexProdTensor` in dimension `4k`**: when `n / 2` is even,
`Γ_(E*) = Γ_Vᵀ`, so `TensorProduct.dualDistrib` directly intertwines `complexProdTensor` of the
reverse duals with the reverse dual of `complexProdTensor`. No finiteness on `E` or `F`, and no
finiteness, parity, or metric assumption on `W`, is needed. -/
theorem dualDistrib_complexProdTensor_of_even (hℓ : Even (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ dualDistrib ℂ E F := by
  let e : Q.IsometryEquiv (Q₁.prod Q₂) :=
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (V × W), map_app' := fun x ↦ (hQ x).symm }
  rw [complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual
      ρ₂.cliffordReverseDual e (fun _ ↦ rfl),
    complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ e (fun _ ↦ rfl),
    cliffordReverseDual_comp_equivOfIsometry]
  have hγ : ρ₁.cliffordReverseDual (complexVolume Q₁ o₁) =
      (ρ₁ (complexVolume Q₁ o₁)).dualMap := by
    rw [AlgHom.cliffordReverseDual_complexVolume, hℓ.neg_one_pow, one_smul]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [AlgHom.cliffordProdTensor_congr_grading ρ₁.cliffordReverseDual _ _ _
    ρ₂.cliffordReverseDual _ _ hγ]
  exact AlgHom.dualDistrib_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁)) _ _ ρ₂
    (equivOfIsometry (e.baseChangeProd ℂ) a)

/-- Conjugation form of `CliffordAlgebra.dualDistrib_complexProdTensor_of_even` for
finite-dimensional modules `E` and `F`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_even
    [Module.Finite ℂ E] [Module.Finite ℂ F] (hℓ : Even (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (dualDistribEquiv ℂ E F).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  apply LinearMap.ext
  intro Φ
  obtain ⟨z, rfl⟩ := (dualDistribEquiv ℂ E F).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [LinearMap.comp_apply, ← toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun (dualDistrib_complexProdTensor_of_even hQ o₁ hQ₁ hn ρ₁ ρ₂ hℓ a) z).symm

end EvenHalfDim

section OddHalfDim

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
  (o₂ : Orientation ℝ W (Fin m))

/-- **Reverse duality of `complexProdTensor` in dimension `4k + 2`**: when `n / 2` is odd and `W`
is even-dimensional, `Γ_(E*) = -Γ_Vᵀ`, so the composite `dualDistrib ∘ (1 ⊗ Γ_(F*))` intertwines
`complexProdTensor` of the reverse duals with the reverse dual of `complexProdTensor`. No
finiteness on `E` or `F`, and no metric assumption on `Q₂`, is needed. -/
theorem dualDistrib_comp_lTensor_complexProdTensor_of_odd (hm : Even m) (hℓ : Odd (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (dualDistrib ℂ E F ∘ₗ
        (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ
        (dualDistrib ℂ E F ∘ₗ
          (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) := by
  let e : Q.IsometryEquiv (Q₁.prod Q₂) :=
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (V × W), map_app' := fun x ↦ (hQ x).symm }
  rw [complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual
      ρ₂.cliffordReverseDual e (fun _ ↦ rfl),
    complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ e (fun _ ↦ rfl),
    cliffordReverseDual_comp_equivOfIsometry]
  have hγ : ρ₁.cliffordReverseDual (complexVolume Q₁ o₁) =
      -(ρ₁ (complexVolume Q₁ o₁)).dualMap := by
    ext φ s
    simp [hℓ.neg_one_pow]
  have hsq : (ρ₁ (complexVolume Q₁ o₁)).dualMap * (ρ₁ (complexVolume Q₁ o₁)).dualMap = 1 := by
    rw [Module.End.mul_eq_comp, LinearMap.dualMap_comp_dualMap, ← Module.End.mul_eq_comp,
      ← map_mul, complexVolume_mul_self o₁ hQ₁, map_one, Module.End.one_eq_id, LinearMap.dualMap_id,
      ← Module.End.one_eq_id]
  have hanti := AlgHom.dualMap_mul_cliffordReverseDual_ι ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (fun v ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
  have hstep1 := AlgHom.lTensor_cliffordProdTensor_of_eq_neg ρ₁.cliffordReverseDual
    (ρ₁ (complexVolume Q₁ o₁)).dualMap hsq hanti ρ₂.cliffordReverseDual
    (by rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one])
    (fun v ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg]) hγ
    (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
    (fun w ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg])
    (equivOfIsometry (e.baseChangeProd ℂ) a)
  have hstep2 := AlgHom.dualDistrib_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (by rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one])
    (fun v ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg]) ρ₂
    (equivOfIsometry (e.baseChangeProd ℂ) a)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [LinearMap.comp_assoc, hstep1, ← LinearMap.comp_assoc, hstep2, LinearMap.comp_assoc]

/-- Conjugation form of `CliffordAlgebra.dualDistrib_comp_lTensor_complexProdTensor_of_odd` for
finite-dimensional modules `E` and `F` when `Q₂ w = -‖w‖²`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_odd (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) [Module.Finite ℂ E] [Module.Finite ℂ F] (hℓ : Odd (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (((LinearEquiv.ofInvolutive (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
            (involutive_apply_complexVolume o₂ hQ₂ ρ₂.cliffordReverseDual)).lTensor
          (Dual ℂ E)).trans (dualDistribEquiv ℂ E F)).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  set δ := ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)
  set eδ := (LinearEquiv.ofInvolutive δ
    (involutive_apply_complexVolume o₂ hQ₂ ρ₂.cliffordReverseDual)).lTensor (Dual ℂ E)
  set eqv := eδ.trans (dualDistribEquiv ℂ E F)
  have hcoe : (eqv : (Dual ℂ E ⊗[ℂ] Dual ℂ F) →ₗ[ℂ] Dual ℂ (E ⊗[ℂ] F)) =
      dualDistrib ℂ E F ∘ₗ δ.lTensor (Dual ℂ E) := by
    apply TensorProduct.ext'
    intro φ ψ
    simp [eqv, eδ, LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul,
      ← toLinearMap_dualDistribEquiv]
  apply LinearMap.ext
  intro Φ
  obtain ⟨z, rfl⟩ := eqv.surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  have h := LinearMap.congr_fun
    (dualDistrib_comp_lTensor_complexProdTensor_of_odd hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm hℓ a) z
  rw [← hcoe] at h
  exact h.symm

end OddHalfDim

end CliffordAlgebra
