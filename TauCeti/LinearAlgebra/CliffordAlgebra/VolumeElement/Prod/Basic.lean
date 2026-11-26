/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.WithLp
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# Chirality of the graded tensor product of Clifford modules

Let `V` and `W` be oriented real inner product spaces of dimensions `n` and `m`, with quadratic
forms `Q₁` and `Q₂`, and let `V ⊕ W` be the `L²` product `WithLp 2 (V × W)` with a form `Q`
satisfying `Q (v, w) = Q₁ v + Q₂ w`. Let `E` and `F` be modules over the complexified Clifford
algebras of `Q₁` and `Q₂`, given by algebra maps `ρ₁` and `ρ₂`.

When `n` is even and `Q₁ v = -‖v‖²`, the normalized complex volume element `Γ_V`
(`CliffordAlgebra.complexVolume`) is an involution anticommuting with every vector of `V`, so it
grades `E`. The graded tensor product from
`TauCeti/LinearAlgebra/CliffordAlgebra/Prod/Basic.lean` then
makes `E ⊗ F` a module over the complexified Clifford algebra of `V ⊕ W`
(`CliffordAlgebra.complexProdTensor`), on which

  `c(v, 0) = c_V(v) ⊗ 1`,  `c(0, w) = Γ_V ⊗ c_W(w)`.

The vectors are moved from `ℂ ⊗ (V ⊕ W)` to `(ℂ ⊗ V) × (ℂ ⊗ W)` by the quadratic isometry
`QuadraticMap.IsometryEquiv.baseChangeProd` of `QuadraticMap.IsometryEquiv.withLpProd`. Through
`CliffordAlgebra.baseChangeWithLpProdEquiv`, this agrees with Mathlib's `CliffordAlgebra.prodEquiv`,
giving the Koszul-signed tensor action
(`CliffordAlgebra.complexProdTensor_comp_baseChangeWithLpProdEquiv_symm`).
See `TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Prod/Bijective.lean` for spinor-module
bijectivity, `Orientation.lean` for product volume elements and orientation reversal, and
`HalfSpin.lean` for the half-spin eigenspace decomposition.

## Main definitions

* `CliffordAlgebra.complexProdTensor`: the graded tensor product action of the complexified
  Clifford algebra of `V ⊕ W` on `E ⊗ F`, graded by the chirality of `V`.

## Main results

* `CliffordAlgebra.complexProdTensor_eq_comp` and
  `CliffordAlgebra.complexProdTensor_comp_map_baseChange`: factorization of `complexProdTensor`
  through `AlgHom.cliffordProdTensor` and compatibility with `baseChange` isometries.
* `CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp`: `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`.
* `CliffordAlgebra.complexProdTensor_comp_baseChangeWithLpProdEquiv_symm`,
  `CliffordAlgebra.complexProdTensor_baseChangeWithLpProdEquiv_symm_tmul`, and
  `CliffordAlgebra.complexProdTensor_baseChangeWithLpProdEquiv_symm_tmul_apply_tmul`: whole-map
  and pure-tensor comparison with `CliffordAlgebra.prodEquiv`, giving the Koszul-signed action of
  homogeneous graded tensors on `E ⊗ F`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed. (2007), Definition 2.2.42.
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

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

include hQ in
/-- **The graded tensor product of Clifford modules of `V` and `W`.** For `V` of even dimension
with `Q₁ v = -‖v‖²`, the chirality operator `Γ_V` grades `E`, and the complexified Clifford algebra
of `V ⊕ W` acts on `E ⊗ F` by `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`
(`CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp`). -/
def complexProdTensor : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F) :=
  (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
    (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom

/-- `complexProdTensor` factors as `AlgHom.cliffordProdTensor` composed with `CliffordAlgebra.map`
of the scalar-extended `WithLp` orthogonal-sum isometry. -/
theorem complexProdTensor_eq_comp :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ =
      (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
          (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
        (map ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry) := by
  rw [complexProdTensor, equivOfIsometry_toAlgHom]

/-- Precomposing `complexProdTensor` with `CliffordAlgebra.map (f.baseChange ℂ)` factors through
`AlgHom.cliffordProdTensor` composed with `map g` and
`map ((QuadraticMap.IsometryEquiv.withLpProd hQ').baseChangeProd ℂ).toIsometry`
whenever `f.baseChange ℂ` and `g` intertwine the two `baseChangeProd` maps. -/
theorem complexProdTensor_comp_map_baseChange
    {V' W' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    [NormedAddCommGroup W'] [InnerProductSpace ℝ W']
    {Q₁' : QuadraticForm ℝ V'} {Q₂' : QuadraticForm ℝ W'}
    {Q' : QuadraticForm ℝ (WithLp 2 (V' × W'))}
    (hQ' : ∀ x, Q' x = Q₁' (WithLp.ofLp x).1 + Q₂' (WithLp.ofLp x).2)
    (f : Q'.Isometry Q)
    (g : (Q₁'.baseChange ℂ).prod (Q₂'.baseChange ℂ) →qᵢ
      (Q₁.baseChange ℂ).prod (Q₂.baseChange ℂ))
    (hf : ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry.comp
        (f.baseChange ℂ) =
      g.comp ((QuadraticMap.IsometryEquiv.withLpProd hQ').baseChangeProd ℂ).toIsometry) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).comp (map (f.baseChange ℂ)) =
      ((AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
          (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
        (map g)).comp
        (map ((QuadraticMap.IsometryEquiv.withLpProd hQ').baseChangeProd ℂ).toIsometry) := by
  rw [complexProdTensor_eq_comp, AlgHom.comp_assoc, map_comp_map, hf, ← map_comp_map,
    ← AlgHom.comp_assoc]

/-- A real vector `(v, w)` of `V ⊕ W` acts on `E ⊗ F` by `c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`. -/
@[simp]
theorem complexProdTensor_ι_one_tmul_toLp (v : V) (w : W) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) =
      (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v))).rTensor F +
        TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  simp [complexProdTensor, QuadraticMap.IsometryEquiv.baseChangeProd_tmul,
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

/-- **Whole-map comparison with Mathlib's `CliffordAlgebra.prodEquiv`.** Pulling back
`complexProdTensor` along the inverse of `baseChangeWithLpProdEquiv` recovers
`AlgHom.cliffordProdTensor` composed with `CliffordAlgebra.toProd`. -/
theorem complexProdTensor_comp_baseChangeWithLpProdEquiv_symm :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).comp
        (baseChangeWithLpProdEquiv ℂ hQ).symm.toAlgHom =
      (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
        (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
        (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)) :=
  AlgHom.ext fun x ↦ by
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, complexProdTensor_eq_comp,
      baseChangeWithLpProdEquiv_symm_apply, ← equivOfIsometry_apply, AlgEquiv.apply_symm_apply]

/-- **Comparison with Mathlib's `CliffordAlgebra.prodEquiv`.** Under
`baseChangeWithLpProdEquiv`, a pure tensor `a ᵍ⊗ b` with `b` of parity `j` acts on `E ⊗ F` by
`ρ₁ a Γ_V ^ j ⊗ ρ₂ b`. -/
theorem complexProdTensor_baseChangeWithLpProdEquiv_symm_tmul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((baseChangeWithLpProdEquiv ℂ hQ).symm (a ᵍ⊗ₜ b)) =
      TensorProduct.map (ρ₁ a * ρ₁ (complexVolume Q₁ o₁) ^ j.val) (ρ₂ b) :=
  (AlgHom.congr_fun
    (complexProdTensor_comp_baseChangeWithLpProdEquiv_symm hQ o₁ hQ₁ hn ρ₁ ρ₂) (a ᵍ⊗ₜ b)).trans
    (AlgHom.cliffordProdTensor_toProd_tmul ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂ a hb)

/-- **Koszul-signed evaluation on homogeneous spinors.** If `b` has parity `j` and `e` lies in the
`(-1) ^ i`-eigenspace of `Γ_V`, then `(baseChangeWithLpProdEquiv ℂ hQ).symm (a ᵍ⊗ b)` sends
`e ⊗ f` to `(-1) ^ (i * j.val) • (ρ₁ a e ⊗ ρ₂ b f)`. -/
theorem complexProdTensor_baseChangeWithLpProdEquiv_symm_tmul_apply_tmul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j)
    {i : ℕ} {e : E} (he : e ∈ (ρ₁ (complexVolume Q₁ o₁)).eigenspace ((-1 : ℂ) ^ i)) (f : F) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((baseChangeWithLpProdEquiv ℂ hQ).symm (a ᵍ⊗ₜ b)) (e ⊗ₜ f) =
      (-1 : ℂ) ^ (i * j.val) • (ρ₁ a e ⊗ₜ ρ₂ b f) :=
  (LinearMap.congr_fun (AlgHom.congr_fun
    (complexProdTensor_comp_baseChangeWithLpProdEquiv_symm hQ o₁ hQ₁ hn ρ₁ ρ₂) (a ᵍ⊗ₜ b))
      (e ⊗ₜ f)).trans
    (AlgHom.cliffordProdTensor_toProd_tmul_apply_tmul ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂ a hb he f)

end CliffordAlgebra
