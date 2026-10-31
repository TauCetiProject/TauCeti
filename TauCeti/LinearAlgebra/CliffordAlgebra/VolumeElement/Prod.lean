/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Chirality of the graded tensor product of Clifford modules

Let `V` and `W` be oriented real inner product spaces of dimensions `n` and `m`, with quadratic
forms `Q₁` and `Q₂`, and let `V ⊕ W` be the `L²` product `WithLp 2 (V × W)` with a form `Q`
satisfying `Q (v, w) = Q₁ v + Q₂ w`. For the negative-metric convention `Q₁ v = -‖v‖²` and
`Q₂ w = -‖w‖²` this is `Q x = -‖x‖²`. Let `E` and `F` be modules over the complexified Clifford
algebras of `Q₁` and `Q₂`, given by algebra maps `ρ₁` and `ρ₂`.

When `n` is even and `Q₁ v = -‖v‖²`, the normalized complex volume element `Γ_V`
(`CliffordAlgebra.complexVolume`) is an involution anticommuting with every vector of `V`, so it
grades `E`. The graded tensor product of `TauCeti/LinearAlgebra/CliffordAlgebra/Prod.lean` then
makes `E ⊗ F` a module over the complexified Clifford algebra of `V ⊕ W`
(`CliffordAlgebra.complexProdTensor`), on which

  `c(v, 0) = c_V(v) ⊗ 1`,  `c(0, w) = Γ_V ⊗ c_W(w)`.

The vectors are moved from `ℂ ⊗ (V ⊕ W)` to `(ℂ ⊗ V) × (ℂ ⊗ W)` by the quadratic isometry
`QuadraticMap.IsometryEquiv.baseChangeProd` of `WithLp.linearEquiv`.

The main result computes the normalized volume element of `V ⊕ W` for the ordered product
orientation, the orientation of the frame `(e₁, …, eₙ, f₁, …, fₘ)` obtained by concatenating
positively oriented orthonormal frames of `V` and `W`, the latter orthogonal for `Q₂`. When
`m` is also even, the normalized volume elements compare as

  `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W`.

When moreover `Q₂ w = -‖w‖²`, the factor `Γ_W` is the chirality of `W`, so the chirality of
`V ⊕ W` is the tensor grading. Its eigenspace decomposition into
`E⁺ ⊗ F⁺ ⊕ E⁻ ⊗ F⁻` and `E⁺ ⊗ F⁻ ⊕ E⁻ ⊗ F⁺` is not made here. When `m` is odd the central
volume element of `V ⊕ W` acts through the second factor alone, as `1 ⊗ ω_W`. Both follow from
the action of the ordered frame product, `c(e₁) ⋯ c(eₙ) Γ_V ^ m ⊗ c(f₁) ⋯ c(fₘ)`, and the
exponent identity `⌊(n + m + 1) / 2⌋ = ⌊(n + 1) / 2⌋ + ⌊(m + 1) / 2⌋` for even `n`.

## Main definitions

* `CliffordAlgebra.complexProdTensor`: the graded tensor product action of the complexified
  Clifford algebra of `V ⊕ W` on `E ⊗ F`, graded by the chirality of `V`.

## Main results

* `CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp`: `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`.
* `CliffordAlgebra.complexProdTensor_complexVolume`: for `m` even,
  `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W` for the ordered product orientation.
* `CliffordAlgebra.complexProdTensor_complexVolume_of_odd`: for `m` odd,
  `ω_(V ⊕ W) = 1 ⊗ ω_W`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}

variable (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

include hQ in
/-- The quadratic isometry `ℂ ⊗ (V ⊕ W) ≃ (ℂ ⊗ V) × (ℂ ⊗ W)`, `z ⊗ (v, w) ↦ (z ⊗ v, z ⊗ w)`: the
instance of `QuadraticMap.IsometryEquiv.baseChangeProd` for `WithLp.linearEquiv`. -/
private def complexWithLpProd :
    (Q.baseChange ℂ).IsometryEquiv ((Q₁.baseChange ℂ).prod (Q₂.baseChange ℂ)) :=
  QuadraticMap.IsometryEquiv.baseChangeProd
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (V × W)
      map_app' := fun x ↦ (hQ x).symm } ℂ

private theorem complexWithLpProd_one_tmul (x : WithLp 2 (V × W)) :
    complexWithLpProd hQ (1 ⊗ₜ x) = (1 ⊗ₜ (WithLp.ofLp x).1, 1 ⊗ₜ (WithLp.ofLp x).2) :=
  QuadraticMap.IsometryEquiv.baseChangeProd_tmul _ 1 x

private theorem equivOfIsometry_complexWithLpProd_ι_inl (v : V) :
    equivOfIsometry (complexWithLpProd hQ)
        (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, 0))) =
      map (QuadraticMap.Isometry.inl (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
        (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)) := by
  simp [equivOfIsometry_apply, complexWithLpProd_one_tmul]

private theorem equivOfIsometry_complexWithLpProd_ι_inr (w : W) :
    equivOfIsometry (complexWithLpProd hQ)
        (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      map (QuadraticMap.Isometry.inr (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
        (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) := by
  simp [equivOfIsometry_apply, complexWithLpProd_one_tmul]

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

include hQ₁ in
private theorem map_complexVolume_mul_self :
    ρ₁ (complexVolume Q₁ o₁) * ρ₁ (complexVolume Q₁ o₁) = 1 := by
  rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one]

include hQ₁ in
private theorem map_complexVolume_pow_of_even {k : ℕ} (hk : Even k) :
    ρ₁ (complexVolume Q₁ o₁) ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [← two_mul, pow_mul, sq, map_complexVolume_mul_self o₁ hQ₁ ρ₁, one_pow]

include hn in
private theorem map_complexVolume_mul_map_ι (w : ℂ ⊗[ℝ] V) :
    ρ₁ (complexVolume Q₁ o₁) * ρ₁ (ι (Q₁.baseChange ℂ) w) =
      -(ρ₁ (ι (Q₁.baseChange ℂ) w) * ρ₁ (complexVolume Q₁ o₁)) := by
  rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg]

include hQ in
/-- **The graded tensor product of Clifford modules of `V` and `W`.** For `V` of even dimension
with `Q₁ v = -‖v‖²`, the chirality operator `Γ_V` grades `E`, and the complexified Clifford algebra
of `V ⊕ W` acts on `E ⊗ F` by `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`
(`CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp`). -/
def complexProdTensor : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F) :=
  (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
    (equivOfIsometry (complexWithLpProd hQ)).toAlgHom

private theorem complexProdTensor_apply (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x =
      AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
        (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂
        (equivOfIsometry (complexWithLpProd hQ) x) :=
  (rfl)

/-- A real vector `(v, w)` of `V ⊕ W` acts on `E ⊗ F` by `c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`. -/
@[simp]
theorem complexProdTensor_ι_one_tmul_toLp (v : V) (w : W) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) =
      (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v))).rTensor F +
        TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  simp [complexProdTensor, equivOfIsometry_apply, complexWithLpProd_one_tmul,
    AlgHom.cliffordProdTensor_ι]

/-- A vector of `V` acts through the first factor: `c(v, 0) = c_V(v) ⊗ 1`. -/
theorem complexProdTensor_ι_one_tmul_toLp_inl (v : V) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, 0))) =
      (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v))).rTensor F := by
  simp [complexProdTensor_ι_one_tmul_toLp]

/-- A vector of `W` acts through the chirality of `V`: `c(0, w) = Γ_V ⊗ c_W(w)`. -/
theorem complexProdTensor_ι_one_tmul_toLp_inr (w : W) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  simp [complexProdTensor_ι_one_tmul_toLp]

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)] (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

omit [Fact (finrank ℝ W = m)] in
/-- The ordered frame product of `V ⊕ W` acts by `c(e₁) ⋯ c(eₙ) Γ_V ^ m ⊗ c(f₁) ⋯ c(fₘ)`. -/
private theorem complexProdTensor_complexVolume_eq_map (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hQb₁ : (QuadraticMap.associated Q₁).IsOrthoᵢ b₁.toBasis) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      Complex.I ^ ((n + m + 1) / 2) • TensorProduct.map
        (ρ₁ (((List.finRange n).map b₁).map fun v ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)).prod *
          ρ₁ (complexVolume Q₁ o₁) ^ m)
        (ρ₂ (((List.finRange m).map b₂).map fun w ↦ ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)).prod) := by
  have hl : (List.finRange (n + m)).map ((b₁.prod b₂).reindex finSumFinEquiv) =
      ((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)) ++
        (List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j) := by
    rw [← List.ofFn_eq_map, List.ofFn_add, ← List.ofFn_eq_map, ← List.ofFn_eq_map]
    congr 2 <;> ext i
    · have hcast : Fin.castLE (Nat.le_add_right n m) i = Fin.castAdd m i := by ext; simp
      simp [OrthonormalBasis.reindex_apply, hcast]
    · simp [OrthonormalBasis.reindex_apply]
  have h₁ : equivOfIsometry (complexWithLpProd hQ)
      ((((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
        map (QuadraticMap.Isometry.inl (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
          (((List.finRange n).map b₁).map fun v ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)).prod := by
    simp [equivOfIsometry_apply, complexWithLpProd_one_tmul, map_list_prod, List.map_map,
      Function.comp_def]
  have h₂ : equivOfIsometry (complexWithLpProd hQ)
      ((((List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
        map (QuadraticMap.Isometry.inr (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
          ((((List.finRange m).map b₂).map ((1 : ℂ) ⊗ₜ[ℝ] ·)).map
            (ι (Q₂.baseChange ℂ))).prod := by
    simp [equivOfIsometry_apply, complexWithLpProd_one_tmul, map_list_prod, List.map_map,
      Function.comp_def]
  have hQb :
      (QuadraticMap.associated Q).IsOrthoᵢ ((b₁.prod b₂).reindex finSumFinEquiv).toBasis := by
    have h := OrthonormalBasis.isOrthoᵢ_associated_prod hQ hQb₁ hQb₂
    rw [LinearMap.isOrthoᵢ_def] at h ⊢
    intro i j hij
    simpa [OrthonormalBasis.reindex_apply] using h _ _ (finSumFinEquiv.symm.injective.ne hij)
  -- Split the frame product of `V ⊕ W` into its `V` block and its `W` block.
  rw [complexVolume_eq o _ ho hQb, hl, List.map_append, List.prod_append]
  -- Move each block into its summand, where the two Clifford algebras act.
  rw [map_smul, complexProdTensor_apply, map_mul, h₁, h₂]
  simp only [map_mul, AlgHom.cliffordProdTensor_map_inl, AlgHom.cliffordProdTensor_map_inr_prod,
    LinearMap.rTensor, ← Module.End.one_eq_id, ← TensorProduct.map_mul, one_mul]
  simp [List.map_map, Function.comp_def]

include hQ₁ in
/-- The normalized volume element of `V ⊕ W` acts by `Γ_V ^ (m + 1) ⊗ Γ_W`. -/
private theorem complexProdTensor_complexVolume_eq_map_pow (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hb₁ : b₁.toBasis.orientation = o₁) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hb₂ : b₂.toBasis.orientation = o₂) (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁) ^ (m + 1)) (ρ₂ (complexVolume Q₂ o₂)) := by
  have hQb₁ := b₁.isOrthoᵢ_associated hQ₁
  rw [complexProdTensor_complexVolume_eq_map hQ o₁ hQ₁ hn ρ₁ ρ₂ o b₁ hQb₁ b₂ hQb₂ ho, pow_succ']
  -- Only the first factor `Γ_V` of `Γ_V ^ (m + 1) = Γ_V * Γ_V ^ m` is expanded in the frame.
  generalize ρ₁ (complexVolume Q₁ o₁) ^ m = g
  rw [complexVolume_eq o₁ b₁ hb₁ hQb₁, complexVolume_eq o₂ b₂ hb₂ hQb₂]
  simp only [map_smul, smul_mul_assoc, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    smul_smul, ← pow_add]
  congr 2
  obtain ⟨j, hj⟩ := hn
  omega

/-- **Volume elements of `V ⊕ W` compare as a tensor product**: for `V` and `W` of even dimension
with `Q₁ v = -‖v‖²`, and `V ⊕ W` oriented by the concatenation `(e₁, …, eₙ, f₁, …, fₘ)` of a
positively oriented orthonormal frame of `V` and a positively oriented orthonormal frame of `W`
orthogonal for `Q₂`, the normalized volume element of `V ⊕ W` acts on the graded tensor product
`E ⊗ F` by `Γ_V ⊗ Γ_W`. When also `Q₂ w = -‖w‖²`, so that `Γ_W` is the chirality of `W`, this says
the chirality of `V ⊕ W` is the tensor grading. -/
theorem complexProdTensor_complexVolume (hm : Even m) (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hb₁ : b₁.toBasis.orientation = o₁) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hb₂ : b₂.toBasis.orientation = o₂) (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  rw [complexProdTensor_complexVolume_eq_map_pow hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o b₁ hb₁ b₂ hb₂ hQb₂ ho,
    pow_succ, map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm, one_mul]

/-- **For odd `W` the volume element of `V ⊕ W` acts through `W` alone**: for `V` of even and `W`
of odd dimension, with `Q₁ v = -‖v‖²` and the ordered product orientation, the normalized volume
element of `V ⊕ W` acts on the graded tensor product `E ⊗ F` by `1 ⊗ ω_W`. -/
theorem complexProdTensor_complexVolume_of_odd (hm : Odd m) (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hb₁ : b₁.toBasis.orientation = o₁) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hb₂ : b₂.toBasis.orientation = o₂) (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  rw [complexProdTensor_complexVolume_eq_map_pow hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o b₁ hb₁ b₂ hb₂ hQb₂ ho,
    map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm.add_one, LinearMap.lTensor, Module.End.one_eq_id]

end CliffordAlgebra
