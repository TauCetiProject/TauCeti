/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.Orientation.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
import TauCeti.LinearAlgebra.QuadraticForm.Prod

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
`TauCeti/LinearAlgebra/CliffordAlgebra/Prod/Basic.lean` then makes `E ⊗ F` a module over the
complexified Clifford algebra of `V ⊕ W` (`CliffordAlgebra.complexProdTensor`), on which

  `c(v, 0) = c_V(v) ⊗ 1`,  `c(0, w) = Γ_V ⊗ c_W(w)`.

The vectors are moved from `ℂ ⊗ (V ⊕ W)` to `(ℂ ⊗ V) × (ℂ ⊗ W)` by the quadratic isometry
`QuadraticMap.IsometryEquiv.baseChangeProd` of `WithLp.linearEquiv`. Through Mathlib's
identification `CliffordAlgebra.prodEquiv` (whose inverse is `CliffordAlgebra.toProd`), a pure
graded tensor `a ᵍ⊗ b` with `b` of parity `j` acts by `ρ₁ a Γ_V ^ j ⊗ ρ₂ b`, giving the Koszul
sign `(-1) ^ (j * k)` on a pure tensor `x ⊗ y` with `Γ_V x = (-1) ^ k • x`.

The main results compute the normalized volume element of `V ⊕ W` for the canonical product
orientation `Orientation.prod o₁ o₂` transported to `WithLp 2 (V × W)`, with no restriction on
`Q₂` and valid for every pair of orientations including rank-zero negative orientations. When `m`
is even, the normalized volume elements compare as

  `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W`.

When moreover `Q₂ w = -‖w‖²`, the factor `Γ_W` is the chirality of `W`, so the chirality of
`V ⊕ W` is the tensor grading. When `m` is odd, the central volume element of `V ⊕ W` acts through
the second factor alone, as `1 ⊗ ω_W`. Both follow from a `Q₂`-orthogonal basis of `W`, the
multiplicativity of `Orientation.volumeEquiv` on product bases, and the exponent identity
`⌊(n + m + 1) / 2⌋ = ⌊(n + 1) / 2⌋ + ⌊(m + 1) / 2⌋` for even `n`.

## Main definitions

* `CliffordAlgebra.complexProdTensor`: the graded tensor product action of the complexified
  Clifford algebra of `V ⊕ W` on `E ⊗ F`, graded by the chirality of `V`.

## Main results

* `CliffordAlgebra.complexProdTensor_eq_cliffordProdTensor`: comparison with
  `AlgHom.cliffordProdTensor` along any quadratic isometry realizing `WithLp.ofLp`.
* `CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp`: `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`.
* `CliffordAlgebra.complexProdTensor_symm_toProd_tmul` and
  `CliffordAlgebra.complexProdTensor_symm_toProd_tmul_tmul`: comparison with Mathlib's
  `CliffordAlgebra.prodEquiv` and its Koszul-signed action on homogeneous vectors.
* `CliffordAlgebra.complexProdTensor_complexVolume_prod` and
  `CliffordAlgebra.complexProdTensor_complexVolume`: for `m` even, `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W` for
  the product orientation, with no hypothesis on `Q₂`.
* `CliffordAlgebra.complexProdTensor_complexVolume_prod_of_odd` and
  `CliffordAlgebra.complexProdTensor_complexVolume_of_odd`: for `m` odd, `ω_(V ⊕ W) = 1 ⊗ ω_W`.

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

/-- **Comparison with `AlgHom.cliffordProdTensor`**: for any quadratic isometry
`e : Q.IsometryEquiv (Q₁.prod Q₂)` realizing `WithLp.ofLp`, `complexProdTensor` is the composition
of `AlgHom.cliffordProdTensor` (graded by `Γ_V`) with `equivOfIsometry (e.baseChangeProd ℂ)`. -/
theorem complexProdTensor_eq_cliffordProdTensor
    (e : Q.IsometryEquiv (Q₁.prod Q₂)) (he : ∀ x, e x = WithLp.ofLp x) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ =
      (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
          (by rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one])
          (fun w ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
          ρ₂).comp
        (equivOfIsometry (e.baseChangeProd ℂ)).toAlgHom := by
  have hiso : complexWithLpProd hQ = e.baseChangeProd ℂ := by
    apply DFunLike.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      simp only [complexWithLpProd, QuadraticMap.IsometryEquiv.baseChangeProd_tmul, he]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [complexProdTensor, hiso]

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

/-- **Comparison with Mathlib's `CliffordAlgebra.prodEquiv`**: under the identification of
`CliffordAlgebra (Q.baseChange ℂ)` with `evenOdd (Q₁.baseChange ℂ) ᵍ⊗ evenOdd (Q₂.baseChange ℂ)`
induced by `e.baseChangeProd ℂ` and `CliffordAlgebra.toProd`, a pure graded tensor `a ᵍ⊗ b` with
`b` of parity `j` acts on `E ⊗ F` by `ρ₁ a * Γ_V ^ j ⊗ ρ₂ b`. -/
theorem complexProdTensor_symm_toProd_tmul
    (e : Q.IsometryEquiv (Q₁.prod Q₂)) (he : ∀ x, e x = WithLp.ofLp x)
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry (e.baseChangeProd ℂ)).symm (toProd _ _ (a ᵍ⊗ₜ b))) =
      TensorProduct.map (ρ₁ a * ρ₁ (complexVolume Q₁ o₁) ^ j.val) (ρ₂ b) := by
  rw [complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ e he, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  exact AlgHom.cliffordProdTensor_toProd_tmul _ _ _ _ _ a hb

/-- **Koszul-signed action on homogeneous tensors**: under `CliffordAlgebra.prodEquiv`, a pure
graded tensor `a ᵍ⊗ b` with `b` of parity `j` acts on a pure tensor `x ⊗ y` with
`Γ_V x = (-1) ^ k • x` by `(-1) ^ (j.val * k) • (ρ₁ a x ⊗ ρ₂ b y)`. -/
theorem complexProdTensor_symm_toProd_tmul_tmul
    (e : Q.IsometryEquiv (Q₁.prod Q₂)) (he : ∀ x, e x = WithLp.ofLp x)
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j)
    {k : ℕ} {x : E} (hx : ρ₁ (complexVolume Q₁ o₁) x = (-1 : ℂ) ^ k • x) (y : F) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry (e.baseChangeProd ℂ)).symm (toProd _ _ (a ᵍ⊗ₜ b))) (x ⊗ₜ y) =
      (-1 : ℂ) ^ (j.val * k) • (ρ₁ a x ⊗ₜ ρ₂ b y) := by
  rw [complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ e he, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  exact AlgHom.cliffordProdTensor_toProd_tmul_tmul _ _ _ _ _ a hb hx y

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)] (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

/-- The volume trivialization evaluated on the top exterior vector of any basis is the orientation's
volume form evaluated on that basis. -/
private theorem volumeEquiv_topVector_eq_volumeForm {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] {k : ℕ} [Fact (finrank ℝ X = k)]
    (ox : Orientation ℝ X (Fin k)) (f : Basis (Fin k) ℝ X) :
    ox.volumeEquiv f.topVector = ox.volumeForm f := by
  rw [f.topVector_eq_ιMulti Fact.out, ox.volumeEquiv_ιMulti]
  simp [Function.comp_def]

omit [FiniteDimensional ℝ V] [Fact (finrank ℝ V = n)] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = m)] [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)] in
/-- The basis of a product orthonormal basis agrees with mapping the product of the factor bases
into `WithLp 2 (V × W)`. -/
private theorem toBasis_orthonormalBasis_prod_reindex (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (b₂ : OrthonormalBasis (Fin m) ℝ W) :
    ((b₁.prod b₂).reindex finSumFinEquiv).toBasis =
      ((b₁.toBasis.prod b₂.toBasis).reindex finSumFinEquiv).map
        (WithLp.linearEquiv 2 ℝ (V × W)).symm := by
  refine Basis.eq_of_apply_eq fun k ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.reindex_apply, Basis.map_apply,
    Basis.reindex_apply]
  rcases finSumFinEquiv.symm k with i | j <;> simp [Basis.prod_apply]

/-- For the canonical product orientation transported to `WithLp 2 (V × W)`, the volume of an
ordered product basis is the product of the volumes of the factor bases. -/
private theorem volumeEquiv_topVector_prod (f₁ : Basis (Fin n) ℝ V) (f₂ : Basis (Fin m) ℝ W) :
    (Orientation.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm
        (o₁.prod o₂ Fact.out Fact.out)).volumeEquiv
        (((f₁.prod f₂).reindex finSumFinEquiv).map
          (WithLp.linearEquiv 2 ℝ (V × W)).symm).topVector =
      o₁.volumeEquiv f₁.topVector * o₂.volumeEquiv f₂.topVector := by
  set e := (WithLp.linearEquiv 2 ℝ (V × W)).symm
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  let b₂ : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr Fact.out)
  let b := (b₁.prod b₂).reindex finSumFinEquiv
  have hb : b.toBasis = ((b₁.toBasis.prod b₂.toBasis).reindex finSumFinEquiv).map e :=
    toBasis_orthonormalBasis_prod_reindex b₁ b₂
  have hbo : b.toBasis.orientation = Orientation.map (Fin (n + m)) e
      (b₁.toBasis.orientation.prod b₂.toBasis.orientation Fact.out Fact.out) := by
    rw [hb, Basis.orientation_map, Orientation.prod_basis_orientation]
  have hdet : b.toBasis.det (((f₁.prod f₂).reindex finSumFinEquiv).map e) =
      b₁.toBasis.det f₁ * b₂.toBasis.det f₂ := by
    rw [hb, Basis.det_apply, Basis.det_apply, Basis.det_apply]
    have hmat : (((b₁.toBasis.prod b₂.toBasis).reindex finSumFinEquiv).map e).toMatrix
        (((f₁.prod f₂).reindex finSumFinEquiv).map e) =
        ((b₁.toBasis.prod b₂.toBasis).reindex finSumFinEquiv).toMatrix
          ((f₁.prod f₂).reindex finSumFinEquiv) := by
      ext i j
      simp [Basis.toMatrix_apply]
    rw [hmat, ← Basis.det_apply, Basis.det_reindex]
    have hcomp : (((f₁.prod f₂).reindex finSumFinEquiv : Fin (n + m) → V × W) ∘ finSumFinEquiv) =
        f₁.prod f₂ := by
      funext i
      simp
    rw [hcomp, Basis.det_prod, Basis.det_apply, Basis.det_apply]
  have hbase : (Orientation.map (Fin (n + m)) e
      (b₁.toBasis.orientation.prod b₂.toBasis.orientation Fact.out Fact.out)).volumeEquiv
      (((f₁.prod f₂).reindex finSumFinEquiv).map e).topVector =
      b₁.toBasis.orientation.volumeEquiv f₁.topVector *
        b₂.toBasis.orientation.volumeEquiv f₂.topVector := by
    rw [← hbo, volumeEquiv_topVector_eq_volumeForm, volumeEquiv_topVector_eq_volumeForm,
      volumeEquiv_topVector_eq_volumeForm, Orientation.volumeForm_robust _ b rfl,
      Orientation.volumeForm_robust _ b₁ rfl, Orientation.volumeForm_robust _ b₂ rfl, hdet]
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl <;>
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂ with rfl | rfl <;>
    simp only [Orientation.prod_neg_left, Orientation.prod_neg_right, Orientation.map_neg,
      Orientation.volumeEquiv_neg_orientation, hbase, neg_mul, mul_neg, neg_neg]

omit [FiniteDimensional ℝ W] [Fact (finrank ℝ W = m)]
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)] in
/-- The ordered product of a `Q₁`-orthogonal basis of `V` and a `Q₂`-orthogonal basis of `W` acts
on `E ⊗ F` by `c(f₁ 0) ⋯ c(f₁ (n-1)) Γ_V ^ m ⊗ c(f₂ 0) ⋯ c(f₂ (m-1))`. -/
private theorem complexProdTensor_basis_prod_univ (f₁ : Basis (Fin n) ℝ V)
    (hQf₁ : (QuadraticMap.associated Q₁).IsOrthoᵢ f₁) (f₂ : Basis (Fin m) ℝ W)
    (hQf₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ f₂) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        (ofBaseChangeAux ℂ Q (basis Q (((f₁.prod f₂).reindex finSumFinEquiv).map
          (WithLp.linearEquiv 2 ℝ (V × W)).symm) Finset.univ)) =
      TensorProduct.map
        (ρ₁ (ofBaseChangeAux ℂ Q₁ (basis Q₁ f₁ Finset.univ)) *
          ρ₁ (complexVolume Q₁ o₁) ^ m)
        (ρ₂ (ofBaseChangeAux ℂ Q₂ (basis Q₂ f₂ Finset.univ))) := by
  let f := ((f₁.prod f₂).reindex finSumFinEquiv).map (WithLp.linearEquiv 2 ℝ (V × W)).symm
  have hQf : (QuadraticMap.associated Q).IsOrthoᵢ f := by
    have hcomp : Q = (Q₁.prod Q₂).comp (WithLp.linearEquiv 2 ℝ (V × W)).toLinearMap :=
      QuadraticMap.ext fun x ↦ by simp [hQ]
    have h := QuadraticMap.isOrthoᵢ_associated_prod hQf₁ hQf₂
    rw [LinearMap.isOrthoᵢ_def] at h ⊢
    intro i j hij
    simp only [f, Basis.map_apply, Basis.reindex_apply, hcomp, QuadraticMap.associated_comp,
      LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    have hne := finSumFinEquiv.symm.injective.ne hij
    rcases hi : finSumFinEquiv.symm i with i' | i' <;>
      rcases hj : finSumFinEquiv.symm j with j' | j'
    · simpa [Basis.prod_apply] using h (Sum.inl i') (Sum.inl j') (by simpa [hi, hj] using hne)
    · simp [Basis.prod_apply]
    · simp [Basis.prod_apply]
    · simpa [Basis.prod_apply] using h (Sum.inr i') (Sum.inr j') (by simpa [hi, hj] using hne)
  have hl : (List.finRange (n + m)).map f =
      ((List.finRange n).map fun i ↦ WithLp.toLp 2 (f₁ i, 0)) ++
        (List.finRange m).map fun j ↦ WithLp.toLp 2 (0, f₂ j) := by
    rw [← List.ofFn_eq_map, List.ofFn_add, ← List.ofFn_eq_map, ← List.ofFn_eq_map]
    congr 2 <;> ext i
    · have hcast : Fin.castLE (Nat.le_add_right n m) i = Fin.castAdd m i := by ext; simp
      simp [f, hcast, Basis.prod_apply]
    · simp [f, Basis.prod_apply]
  have h₁ : equivOfIsometry (complexWithLpProd hQ)
      ((((List.finRange n).map fun i ↦ WithLp.toLp 2 (f₁ i, 0)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
      map (QuadraticMap.Isometry.inl (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
        (((List.finRange n).map f₁).map fun v ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)).prod := by
    simp [equivOfIsometry_apply, complexWithLpProd_one_tmul, map_list_prod, List.map_map,
      Function.comp_def]
  have h₂ : equivOfIsometry (complexWithLpProd hQ)
      ((((List.finRange m).map fun j ↦ WithLp.toLp 2 (0, f₂ j)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
      map (QuadraticMap.Isometry.inr (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
        ((((List.finRange m).map f₂).map ((1 : ℂ) ⊗ₜ[ℝ] ·)).map
          (ι (Q₂.baseChange ℂ))).prod := by
    simp [equivOfIsometry_apply, complexWithLpProd_one_tmul, map_list_prod, List.map_map,
      Function.comp_def]
  rw [basis_eq_prod_map_sort hQf, basis_eq_prod_map_sort hQf₁, basis_eq_prod_map_sort hQf₂,
    Fin.sort_univ, Fin.sort_univ, Fin.sort_univ, hl, List.map_append, List.prod_append, map_mul,
    map_list_prod, map_list_prod, map_list_prod, map_list_prod]
  simp only [List.map_map, Function.comp_def, ofBaseChangeAux_ι]
  rw [complexProdTensor_apply, map_mul]
  have h₁' : equivOfIsometry (complexWithLpProd hQ)
      ((List.finRange n).map fun i ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (f₁ i, 0))).prod =
      map (QuadraticMap.Isometry.inl (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
        ((List.finRange n).map fun i ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ f₁ i)).prod := by
    simpa [List.map_map, Function.comp_def] using h₁
  have h₂' : equivOfIsometry (complexWithLpProd hQ)
      ((List.finRange m).map fun j ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, f₂ j))).prod =
      map (QuadraticMap.Isometry.inr (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
        ((((List.finRange m).map f₂).map ((1 : ℂ) ⊗ₜ[ℝ] ·)).map (ι (Q₂.baseChange ℂ))).prod := by
    simpa [List.map_map, Function.comp_def] using h₂
  rw [h₁', h₂']
  simp only [map_mul, AlgHom.cliffordProdTensor_map_inl, AlgHom.cliffordProdTensor_map_inr_prod,
    LinearMap.rTensor, ← Module.End.one_eq_id, ← TensorProduct.map_mul, one_mul]
  simp [List.map_map, Function.comp_def, map_list_prod]

/-- The normalized complex volume element written in terms of the top Clifford basis vector of an
arbitrary basis `f`. -/
private theorem complexVolume_eq_inv_smul_basis {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] {k : ℕ} [Fact (finrank ℝ X = k)]
    (QX : QuadraticForm ℝ X) (ox : Orientation ℝ X (Fin k)) (f : Basis (Fin k) ℝ X) :
    complexVolume QX ox =
      (Complex.I ^ ((k + 1) / 2) * algebraMap ℝ ℂ (ox.volumeEquiv f.topVector)⁻¹) •
        ofBaseChangeAux ℂ QX (basis QX f Finset.univ) := by
  rw [complexVolume_def, volumeElement_eq_inv_smul_basis ox f, map_smul, smul_comm,
    ← smul_assoc, Complex.real_smul, mul_comm, Complex.coe_algebraMap]

include hQ₁ in
/-- The normalized volume element of `V ⊕ W` for the canonical product orientation acts on `E ⊗ F`
by `Γ_V ^ (m + 1) ⊗ Γ_W`, for every quadratic form `Q₂` on `W` and every pair of orientations. -/
private theorem complexProdTensor_complexVolume_prod_eq_map_pow :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        (complexVolume Q (Orientation.map (Fin (n + m))
          (WithLp.linearEquiv 2 ℝ (V × W)).symm (o₁.prod o₂ Fact.out Fact.out))) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁) ^ (m + 1)) (ρ₂ (complexVolume Q₂ o₂)) := by
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  have hQf₁ : (QuadraticMap.associated Q₁).IsOrthoᵢ b₁.toBasis := b₁.isOrthoᵢ_associated hQ₁
  obtain ⟨f₂', hf₂'⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm ℝ Q₂)
  let f₂ : Basis (Fin m) ℝ W := f₂'.reindex (finCongr Fact.out)
  have hQf₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ f₂ := fun i j hij ↦ by
    simpa [Function.onFun, QuadraticMap.associated, f₂] using
      hf₂' ((finCongr Fact.out).symm.injective.ne hij)
  let oProd := Orientation.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm
    (o₁.prod o₂ Fact.out Fact.out)
  let f := ((b₁.toBasis.prod f₂).reindex finSumFinEquiv).map (WithLp.linearEquiv 2 ℝ (V × W)).symm
  have hvol : oProd.volumeEquiv f.topVector =
      o₁.volumeEquiv b₁.toBasis.topVector * o₂.volumeEquiv f₂.topVector :=
    volumeEquiv_topVector_prod o₁ o₂ b₁.toBasis f₂
  have hbas := complexProdTensor_basis_prod_univ hQ o₁ hQ₁ hn ρ₁ ρ₂ b₁.toBasis hQf₁ f₂ hQf₂
  have hexp : (n + m + 1) / 2 = (n + 1) / 2 + (m + 1) / 2 := by
    obtain ⟨j, hj⟩ := hn
    omega
  rw [complexVolume_eq_inv_smul_basis Q oProd f, map_smul, hbas, hvol, mul_inv, pow_succ']
  generalize ρ₁ (complexVolume Q₁ o₁) ^ m = g
  rw [complexVolume_eq_inv_smul_basis Q₁ o₁ b₁.toBasis,
    complexVolume_eq_inv_smul_basis Q₂ o₂ f₂, map_smul, map_smul, smul_mul_assoc,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul]
  have hscalar :
      Complex.I ^ ((n + m + 1) / 2) *
          algebraMap ℝ ℂ ((o₁.volumeEquiv b₁.toBasis.topVector)⁻¹ *
            (o₂.volumeEquiv f₂.topVector)⁻¹) =
        Complex.I ^ ((n + 1) / 2) * algebraMap ℝ ℂ (o₁.volumeEquiv b₁.toBasis.topVector)⁻¹ *
          (Complex.I ^ ((m + 1) / 2) * algebraMap ℝ ℂ (o₂.volumeEquiv f₂.topVector)⁻¹) := by
    rw [hexp, pow_add, map_mul]
    ring
  rw [hscalar]

/-- **Volume elements of `V ⊕ W` compare as a tensor product**: for `V` and `W` of even dimension
with `Q₁ v = -‖v‖²`, the normalized volume element of `V ⊕ W` for the canonical product
orientation acts on the graded tensor product `E ⊗ F` by `Γ_V ⊗ Γ_W`. No hypothesis on `Q₂` is
needed, and all orientations (including rank-zero negative orientations) are covered. When also
`Q₂ w = -‖w‖²`, so that `Γ_W` is the chirality of `W`, this says the chirality of `V ⊕ W` is the
tensor grading. -/
theorem complexProdTensor_complexVolume_prod (hm : Even m) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        (complexVolume Q (Orientation.map (Fin (n + m))
          (WithLp.linearEquiv 2 ℝ (V × W)).symm (o₁.prod o₂ Fact.out Fact.out))) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  rw [complexProdTensor_complexVolume_prod_eq_map_pow hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂,
    pow_succ, map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm, one_mul]

/-- **For odd `W` the volume element of `V ⊕ W` acts through `W` alone**: for `V` of even and `W`
of odd dimension, with `Q₁ v = -‖v‖²` and the canonical product orientation, the normalized volume
element of `V ⊕ W` acts on the graded tensor product `E ⊗ F` by `1 ⊗ ω_W`, with no hypothesis on
`Q₂`. -/
theorem complexProdTensor_complexVolume_prod_of_odd (hm : Odd m) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        (complexVolume Q (Orientation.map (Fin (n + m))
          (WithLp.linearEquiv 2 ℝ (V × W)).symm (o₁.prod o₂ Fact.out Fact.out))) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  rw [complexProdTensor_complexVolume_prod_eq_map_pow hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂,
    map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm.add_one, LinearMap.lTensor, Module.End.one_eq_id]

/-- **Frame form of `CliffordAlgebra.complexProdTensor_complexVolume_prod`**: for `V` and `W` of
even dimension with `Q₁ v = -‖v‖²`, and `V ⊕ W` oriented by the concatenation
`(e₁, …, eₙ, f₁, …, fₘ)` of positively oriented orthonormal frames of `V` and `W`, the normalized
volume element of `V ⊕ W` acts on `E ⊗ F` by `Γ_V ⊗ Γ_W`. -/
theorem complexProdTensor_complexVolume (hm : Even m) (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hb₁ : b₁.toBasis.orientation = o₁) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hb₂ : b₂.toBasis.orientation = o₂)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  subst ho hb₁ hb₂
  rw [toBasis_orthonormalBasis_prod_reindex, Basis.orientation_map,
    ← Orientation.prod_basis_orientation b₁.toBasis b₂.toBasis Fact.out Fact.out]
  exact complexProdTensor_complexVolume_prod hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
    b₂.toBasis.orientation hm

/-- **Frame form of `CliffordAlgebra.complexProdTensor_complexVolume_prod_of_odd`**: for `V` of
even and `W` of odd dimension, with `Q₁ v = -‖v‖²` and the ordered product orientation of
positively oriented orthonormal frames of `V` and `W`, the normalized volume element of `V ⊕ W`
acts on `E ⊗ F` by `1 ⊗ ω_W`. -/
theorem complexProdTensor_complexVolume_of_odd (hm : Odd m) (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hb₁ : b₁.toBasis.orientation = o₁) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hb₂ : b₂.toBasis.orientation = o₂)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  subst ho hb₁ hb₂
  rw [toBasis_orthonormalBasis_prod_reindex, Basis.orientation_map,
    ← Orientation.prod_basis_orientation b₁.toBasis b₂.toBasis Fact.out Fact.out]
  exact complexProdTensor_complexVolume_prod_of_odd hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
    b₂.toBasis.orientation hm

end CliffordAlgebra
