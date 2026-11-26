/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Normed.Lp.ProdLp.QuadraticForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.Orientation.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
import TauCeti.Analysis.InnerProductSpace.QuadraticForm.OrthonormalBasis
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
grades `E`. The graded tensor product from
`TauCeti/LinearAlgebra/CliffordAlgebra/Prod/Basic.lean` then
makes `E ⊗ F` a module over the complexified Clifford algebra of `V ⊕ W`
(`CliffordAlgebra.complexProdTensor`), on which

  `c(v, 0) = c_V(v) ⊗ 1`,  `c(0, w) = Γ_V ⊗ c_W(w)`.

The vectors are moved from `ℂ ⊗ (V ⊕ W)` to `(ℂ ⊗ V) × (ℂ ⊗ W)` by the quadratic isometry
`CliffordAlgebra.complexWithLpProd` (`QuadraticMap.IsometryEquiv.baseChangeProd` of
`WithLp.linearEquiv`), comparing with `CliffordAlgebra.toProd` on graded tensors.

The main result computes the normalized volume element of `V ⊕ W` for the ordered product
orientation `Orientation.prod o₁ o₂` (matching the orientation of the concatenated frame
`(e₁, …, eₙ, f₁, …, fₘ)` of positively oriented orthonormal frames of `V` and `W`, the latter
orthogonal for `Q₂`). When `m` is also even, the normalized volume elements compare as

  `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W`.

When moreover `Q₂ w = -‖w‖²`, the factor `Γ_W` is the chirality of `W`, so the chirality of
`V ⊕ W` is the tensor grading (decomposed into half-spin spaces in `Eigenspace.lean`; orientation
reversal is treated in `Neg.lean`). When `m` is odd the central volume element of `V ⊕ W` acts
through the second factor alone, as `1 ⊗ ω_W`. Both follow from the action of the ordered frame
product, `c(e₁) ⋯ c(eₙ) Γ_V ^ m ⊗ c(f₁) ⋯ c(fₘ)`, and the exponent identity
`⌊(n + m + 1) / 2⌋ = ⌊(n + 1) / 2⌋ + ⌊(m + 1) / 2⌋` for even `n`.

## Main definitions

* `CliffordAlgebra.complexWithLpProd`: the isometry `ℂ ⊗ (V ⊕ W) ≃ (ℂ ⊗ V) × (ℂ ⊗ W)`.
* `CliffordAlgebra.complexProdTensor`: the graded tensor product action of the complexified
  Clifford algebra of `V ⊕ W` on `E ⊗ F`, graded by the chirality of `V`.

## Main results

* `CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp`: `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`.
* `CliffordAlgebra.complexProdTensor_toProd_tmul` and
  `CliffordAlgebra.complexProdTensor_toProd_tmul_apply_of_apply_eq_neg_one_pow_smul`: comparison
  with Mathlib's `CliffordAlgebra.toProd`.
* `CliffordAlgebra.complexProdTensor_complexVolume_of_map_eq_prod`: for `m` even,
  `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W` for the ordered product orientation.
* `CliffordAlgebra.complexProdTensor_complexVolume_of_odd_of_map_eq_prod`: for `m` odd,
  `ω_(V ⊕ W) = 1 ⊗ ω_W`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed. (2007), Definition 2.2.42.
-/

public section

noncomputable section

open Module
open scoped TensorProduct RealInnerProductSpace

namespace CliffordAlgebra

section WithLpProd

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

include hQ in
/-- The quadratic isometry `ℂ ⊗ (V ⊕ W) ≃ (ℂ ⊗ V) × (ℂ ⊗ W)`, `z ⊗ (v, w) ↦ (z ⊗ v, z ⊗ w)`: the
instance of `QuadraticMap.IsometryEquiv.baseChangeProd` for
`QuadraticMap.IsometryEquiv.withLpProd`. -/
def complexWithLpProd :
    (Q.baseChange ℂ).IsometryEquiv ((Q₁.baseChange ℂ).prod (Q₂.baseChange ℂ)) :=
  (QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ

/-- Unfolding `CliffordAlgebra.complexWithLpProd` through
`QuadraticMap.IsometryEquiv.withLpProd`. -/
theorem complexWithLpProd_def :
    complexWithLpProd hQ = (QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ :=
  (rfl)

/-- On pure tensors, `CliffordAlgebra.complexWithLpProd` separates the two `L²`-product
coordinates. -/
@[simp]
theorem complexWithLpProd_tmul (z : ℂ) (x : WithLp 2 (V × W)) :
    complexWithLpProd hQ (z ⊗ₜ x) = (z ⊗ₜ (WithLp.ofLp x).1, z ⊗ₜ (WithLp.ofLp x).2) := by
  simp [complexWithLpProd]

end WithLpProd

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

include hQ₁ in
private theorem map_complexVolume_pow_of_even {k : ℕ} (hk : Even k) :
    ρ₁ (complexVolume Q₁ o₁) ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [← two_mul, pow_mul, sq, map_complexVolume_mul_self o₁ hQ₁ ρ₁, one_pow]

include hQ in
/-- **The graded tensor product of Clifford modules of `V` and `W`.** For `V` of even dimension
with `Q₁ v = -‖v‖²`, the chirality operator `Γ_V` grades `E`, and the complexified Clifford algebra
of `V ⊕ W` acts on `E ⊗ F` by `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`
(`CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp`). -/
def complexProdTensor : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F) :=
  (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
    (equivOfIsometry (complexWithLpProd hQ)).toAlgHom

/-- Unfolding `CliffordAlgebra.complexProdTensor` through `CliffordAlgebra.complexWithLpProd`. -/
theorem complexProdTensor_def :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ =
      (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
          (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
        (equivOfIsometry (complexWithLpProd hQ)).toAlgHom :=
  (rfl)

/-- A real vector `(v, w)` of `V ⊕ W` acts on `E ⊗ F` by `c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`. -/
@[simp]
theorem complexProdTensor_ι_one_tmul_toLp (v : V) (w : W) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) =
      (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v))).rTensor F +
        TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  simp [complexProdTensor, equivOfIsometry_apply, AlgHom.cliffordProdTensor_ι]

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

/-- **Comparison with Mathlib's `CliffordAlgebra.prodEquiv`**: under `complexWithLpProd` and
`CliffordAlgebra.toProd`, the pure graded tensor `a ᵍ⊗ b` with `b` of parity `j` acts on `E ⊗ F` by
`ρ₁ a Γ_V ^ j ⊗ ρ₂ b`. -/
theorem complexProdTensor_toProd_tmul (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry (complexWithLpProd hQ)).symm
          (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (a ᵍ⊗ₜ b))) =
      TensorProduct.map (ρ₁ a * ρ₁ (complexVolume Q₁ o₁) ^ j.val) (ρ₂ b) := by
  rw [complexProdTensor_def, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, AlgHom.cliffordProdTensor_toProd_tmul _ _ _ _ _ a hb]

/-- On a pure tensor `e ⊗ f` whose first factor has `Γ_V`-degree `i`, the graded tensor `a ᵍ⊗ b`
with `b` of parity `j` acts with the Koszul sign `(-1) ^ (j * i)`. -/
theorem complexProdTensor_toProd_tmul_apply_of_apply_eq_neg_one_pow_smul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j)
    {i : ℕ} {e : E} (he : ρ₁ (complexVolume Q₁ o₁) e = (-1 : ℂ) ^ i • e) (f : F) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry (complexWithLpProd hQ)).symm
          (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (a ᵍ⊗ₜ b))) (e ⊗ₜ f) =
      (-1 : ℂ) ^ (j.val * i) • (ρ₁ a e ⊗ₜ ρ₂ b f) := by
  rw [complexProdTensor_def, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply,
    AlgHom.cliffordProdTensor_toProd_tmul_apply_of_apply_eq_neg_one_pow_smul _ _ _ _ _ a hb he]

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
    simp [equivOfIsometry_apply, map_list_prod, List.map_map, Function.comp_def]
  have h₂ : equivOfIsometry (complexWithLpProd hQ)
      ((((List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
        map (QuadraticMap.Isometry.inr (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
          ((((List.finRange m).map b₂).map ((1 : ℂ) ⊗ₜ[ℝ] ·)).map
            (ι (Q₂.baseChange ℂ))).prod := by
    simp [equivOfIsometry_apply, map_list_prod, List.map_map, Function.comp_def]
  have hQb :
      (QuadraticMap.associated Q).IsOrthoᵢ ((b₁.prod b₂).reindex finSumFinEquiv).toBasis := by
    have h := OrthonormalBasis.isOrthoᵢ_associated_prod hQ hQb₁ hQb₂
    rw [LinearMap.isOrthoᵢ_def] at h ⊢
    intro i j hij
    simpa [OrthonormalBasis.reindex_apply] using h _ _ (finSumFinEquiv.symm.injective.ne hij)
  -- Split the frame product of `V ⊕ W` into its `V` block and its `W` block.
  rw [complexVolume_eq o _ ho hQb, hl, List.map_append, List.prod_append]
  -- Move each block into its summand, where the two Clifford algebras act.
  rw [map_smul, complexProdTensor_def, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, map_mul, h₁, h₂]
  simp only [map_mul, AlgHom.cliffordProdTensor_map_inl, AlgHom.cliffordProdTensor_map_inr_prod,
    LinearMap.rTensor, ← Module.End.one_eq_id, ← TensorProduct.map_mul, one_mul]
  simp [List.map_map, Function.comp_def]

include hQ₁ in
/-- In an orthogonal product frame `(b₁, b₂)` orienting `V ⊕ W`, the normalized volume element
acts by `(ρ₁ Γ_{b₁} * ρ₁ Γ_{o₁} ^ m) ⊗ ρ₂ Γ_{b₂}`. -/
private theorem complexProdTensor_complexVolume_eq_map_mul_pow (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (b₂ : OrthonormalBasis (Fin m) ℝ W) (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map
        (ρ₁ (complexVolume Q₁ b₁.toBasis.orientation) * ρ₁ (complexVolume Q₁ o₁) ^ m)
        (ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)) := by
  have hQb₁ := b₁.isOrthoᵢ_associated hQ₁
  rw [complexProdTensor_complexVolume_eq_map hQ o₁ hQ₁ hn ρ₁ ρ₂ o b₁ hQb₁ b₂ hQb₂ ho,
    complexVolume_eq _ b₁ rfl hQb₁, complexVolume_eq _ b₂ rfl hQb₂]
  simp only [map_smul, smul_mul_assoc, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    smul_smul, ← pow_add]
  congr 2
  obtain ⟨j, hj⟩ := hn
  omega

include hQ₁ in
private theorem complexProdTensor_complexVolume_eq_map_pow_of_map_eq_prod
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) = o₁.prod o₂ Fact.out Fact.out) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁) ^ (m + 1)) (ρ₂ (complexVolume Q₂ o₂)) := by
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  obtain ⟨b₂, hQb₂⟩ := Q₂.exists_orthonormalBasis_isOrthoᵢ (n := m) Fact.out
  have hB : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.map (WithLp.linearEquiv 2 ℝ (V × W)) =
      (b₁.toBasis.prod b₂.toBasis).reindex finSumFinEquiv :=
    Basis.eq_of_apply_eq fun k ↦ by
      rw [Basis.map_apply, OrthonormalBasis.coe_toBasis, OrthonormalBasis.reindex_apply,
        Basis.reindex_apply]
      rcases finSumFinEquiv.symm k with i | j <;> simp [Basis.prod_apply]
  have ho₀ : ((b₁.toBasis.orientation.prod b₂.toBasis.orientation Fact.out Fact.out).map
      (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm) =
      ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation := by
    rw [Orientation.prod_basis_orientation, ← hB, Basis.orientation_map,
      ← Orientation.map_trans, LinearEquiv.self_trans_symm, Orientation.map_refl,
      Equiv.refl_apply]
  have ho' : o = (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm := by
    rw [← ho, ← Orientation.map_trans, LinearEquiv.self_trans_symm, Orientation.map_refl,
      Equiv.refl_apply]
  have hpos : complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
      (complexVolume Q ((o₁.prod b₂.toBasis.orientation Fact.out Fact.out).map
        (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁) ^ (m + 1))
        (ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)) := by
    rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl
    · rw [ho₀, complexProdTensor_complexVolume_eq_map_mul_pow hQ _ hQ₁ hn ρ₁ ρ₂ _ b₁ b₂ hQb₂ rfl,
        ← pow_succ']
    · rw [Orientation.prod_neg_left, Orientation.map_neg, ho₀, complexVolume_neg_orientation,
        map_neg, complexProdTensor_complexVolume_eq_map_mul_pow hQ _ hQ₁ hn ρ₁ ρ₂ _ b₁ b₂ hQb₂ rfl,
        pow_succ', complexVolume_neg_orientation, map_neg, neg_mul, ← neg_one_smul ℂ (_ * _),
        TensorProduct.map_smul_left]
      exact (neg_one_smul ℂ _).symm
  rw [ho']
  rcases b₂.toBasis.orientation_eq_or_eq_neg o₂ with rfl | rfl
  · exact hpos
  · rw [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
      hpos, complexVolume_neg_orientation, map_neg, ← neg_one_smul ℂ (ρ₂ _),
      TensorProduct.map_smul_right]
    exact (neg_one_smul ℂ _).symm

/-- **Basis-free product chirality**: for `V` and `W` of even dimension with `Q₁ v = -‖v‖²` and
`V ⊕ W` carrying the ordered product orientation `Orientation.prod o₁ o₂`, the normalized complex
volume element of `V ⊕ W` acts on `E ⊗ F` by `Γ_V ⊗ Γ_W`. When also `Q₂ w = -‖w‖²`, so that `Γ_W`
is the chirality of `W`, this says the chirality of `V ⊕ W` is the tensor grading. No frame choice
or metric condition on `Q₂` is needed, and both orientations in dimension zero are covered. -/
theorem complexProdTensor_complexVolume_of_map_eq_prod (hm : Even m)
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) = o₁.prod o₂ Fact.out Fact.out) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  rw [complexProdTensor_complexVolume_eq_map_pow_of_map_eq_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o ho,
    pow_succ, map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm, one_mul]

/-- **Basis-free odd product volume**: for `V` of even and `W` of odd dimension with
`Q₁ v = -‖v‖²` and the ordered product orientation `Orientation.prod o₁ o₂`, the normalized
complex volume element of `V ⊕ W` acts on `E ⊗ F` by `1 ⊗ ω_W`. -/
theorem complexProdTensor_complexVolume_of_odd_of_map_eq_prod (hm : Odd m)
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) = o₁.prod o₂ Fact.out Fact.out) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  rw [complexProdTensor_complexVolume_eq_map_pow_of_map_eq_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o ho,
    map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm.add_one, LinearMap.lTensor, Module.End.one_eq_id]

end CliffordAlgebra
