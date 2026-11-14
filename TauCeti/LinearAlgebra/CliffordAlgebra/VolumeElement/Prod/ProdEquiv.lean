/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
public import TauCeti.LinearAlgebra.Orientation.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Comparison with `CliffordAlgebra.prodEquiv` and basis-free product volume formulas

`CliffordAlgebra.complexProdTensor` makes `E ⊗ F` a module over the complexified Clifford algebra
of an `L²` orthogonal sum `WithLp 2 (V × W)` when `V` is even-dimensional with `Q₁ v = -‖v‖²`.
This file records two foundational tools for its structural laws:

1. **Comparison with `AlgHom.cliffordProdTensor` and `CliffordAlgebra.prodEquiv`**: reading the
   quadratic form `Q` of `WithLp 2 (V × W)` as `Q₁.prod Q₂` via
   `QuadraticMap.IsometryEquiv.withLpProd` and distributing complexification over the product via
   `QuadraticMap.IsometryEquiv.baseChangeProd` identifies `CliffordAlgebra.complexProdTensor` with
   `AlgHom.cliffordProdTensor` graded by `Γ_V` (`CliffordAlgebra.complexProdTensor_eq_comp`). Under
   Mathlib's graded tensor product equivalence `CliffordAlgebra.prodEquiv`, a pure tensor `a ᵍ⊗ b`
   with `b` of parity `j` acts by `ρ₁ a Γ_V ^ j ⊗ ρ₂ b`, hence on a `(-1) ^ i`-eigenvector `e` of
   `Γ_V` with the Koszul sign `(-1) ^ (j * i) • (ρ₁ a e ⊗ ρ₂ b f)`.

2. **Basis-free volume-element formulas**: using `Orientation.prod`, the ordered product orientation
   of `WithLp 2 (V × W)` is defined without choosing positively oriented frames, including in rank
   zero where `-positiveOrientation` has no basis. Reversing `o₁` while holding `o` fixed multiplies
   the action of `Γ_(V ⊕ W)` by `(-1) ^ m`, while reversing `o₁` in the product orientation negates
   `o`; combining the two extends `CliffordAlgebra.complexProdTensor_complexVolume` and
   `CliffordAlgebra.complexProdTensor_complexVolume_of_odd` to arbitrary orientations `o₁`, `o₂` in
   every dimension including zero.

## Main results

* `CliffordAlgebra.complexProdTensor_eq_comp`: `complexProdTensor` is `AlgHom.cliffordProdTensor`
  composed with `equivOfIsometry ((withLpProd hQ).baseChangeProd ℂ)`.
* `CliffordAlgebra.complexProdTensor_symm_toProd_tmul` and
  `CliffordAlgebra.complexProdTensor_symm_toProd_tmul_apply_of_apply_eq_neg_one_pow_smul`:
  comparison with Mathlib's `CliffordAlgebra.prodEquiv` / `CliffordAlgebra.toProd` and the Koszul
  sign `(-1) ^ (j * i)` on homogeneous vectors.
* `CliffordAlgebra.complexProdTensor_complexVolume_of_map_prod` and
  `CliffordAlgebra.complexProdTensor_complexVolume_of_odd_of_map_prod`: basis-free formulas
  `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W` (`m` even) and `ω_(V ⊕ W) = 1 ⊗ ω_W` (`m` odd) for the transported
  `Orientation.prod`, valid in all dimensions including rank zero.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Definition 2.2.42.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

section ProdEquiv

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- `CliffordAlgebra.complexProdTensor` is `AlgHom.cliffordProdTensor` graded by `Γ_V`, composed
with the complexified product quadratic isometry. -/
theorem complexProdTensor_eq_comp :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ =
      (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
          (by rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one])
          (fun w ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
          ρ₂).comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul z x =>
    have hx : z ⊗ₜ[ℝ] x =
        z • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, WithLp.toLp_ofLp]
    rw [hx, map_smul, map_smul]
    simp [complexProdTensor_ι_one_tmul_toLp, equivOfIsometry_apply, AlgHom.cliffordProdTensor_ι]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Pointwise form of `CliffordAlgebra.complexProdTensor_eq_comp`. -/
theorem complexProdTensor_eq_cliffordProdTensor (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x =
      AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
        (by rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one])
        (fun w ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
        ρ₂ (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) x) :=
  AlgHom.congr_fun (complexProdTensor_eq_comp hQ o₁ hQ₁ hn ρ₁ ρ₂) x

/-- **Comparison with `CliffordAlgebra.prodEquiv`**: transporting a pure tensor `a ᵍ⊗ b` of
`evenOdd (Q₁.baseChange ℂ) ᵍ⊗ evenOdd (Q₂.baseChange ℂ)` with `b` of parity `j` into
`CliffordAlgebra (Q.baseChange ℂ)` makes it act on `E ⊗ F` by `ρ₁ a Γ_V ^ j ⊗ ρ₂ b`. -/
theorem complexProdTensor_symm_toProd_tmul (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).symm
          (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (a ᵍ⊗ₜ b))) =
      TensorProduct.map (ρ₁ a * ρ₁ (complexVolume Q₁ o₁) ^ j.val) (ρ₂ b) := by
  rw [complexProdTensor_eq_cliffordProdTensor, AlgEquiv.apply_symm_apply,
    AlgHom.cliffordProdTensor_toProd_tmul _ _ _ _ _ a hb]

/-- **Koszul-signed action under `CliffordAlgebra.prodEquiv`**: a pure tensor `a ᵍ⊗ b` with `b` of
parity `j` acts on a pure tensor `e ⊗ f` with `Γ_V e = (-1) ^ i • e` by
`(-1) ^ (j * i) • (ρ₁ a e ⊗ ρ₂ b f)`. -/
theorem complexProdTensor_symm_toProd_tmul_apply_of_apply_eq_neg_one_pow_smul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j)
    {i : ℕ} {e : E} (he : ρ₁ (complexVolume Q₁ o₁) e = (-1 : ℂ) ^ i • e) (f : F) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).symm
          (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (a ᵍ⊗ₜ b)))
        (e ⊗ₜ f) =
      (-1 : ℂ) ^ (j.val * i) • (ρ₁ a e ⊗ₜ ρ₂ b f) := by
  rw [complexProdTensor_eq_cliffordProdTensor, AlgEquiv.apply_symm_apply,
    AlgHom.cliffordProdTensor_toProd_tmul_apply_of_apply_eq_neg_one_pow_smul _ _ _ _ _ a hb he f]

end ProdEquiv

section Volume

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {n m : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = m)]
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

omit [Fact (finrank ℝ W = m)] in
/-- Reversing the orientation `o₁` of `V` while holding the orientation `o` of `V ⊕ W` fixed
multiplies the action of `complexVolume Q o` on `E ⊗ F` by `(-1) ^ m`, since each of the `m`
frame vectors of `W` acts through `Γ_V`. -/
theorem complexProdTensor_neg_orientation_complexVolume
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    {b₂ : OrthonormalBasis (Fin m) ℝ W}
    (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (-1 : ℂ) ^ m • complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) := by
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  let B : OrthonormalBasis (Fin (n + m)) ℝ (WithLp 2 (V × W)) :=
    (b₁.prod b₂).reindex finSumFinEquiv
  have hQb₁ := b₁.isOrthoᵢ_associated hQ₁
  have hQB : (QuadraticMap.associated Q).IsOrthoᵢ B.toBasis := by
    have h := OrthonormalBasis.isOrthoᵢ_associated_prod hQ hQb₁ hQb₂
    rw [LinearMap.isOrthoᵢ_def] at h ⊢
    intro i j hij
    simpa [B, OrthonormalBasis.reindex_apply] using h _ _ (finSumFinEquiv.symm.injective.ne hij)
  have hl : (List.finRange (n + m)).map B =
      ((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)) ++
        (List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j) := by
    rw [← List.ofFn_eq_map, List.ofFn_add, ← List.ofFn_eq_map, ← List.ofFn_eq_map]
    congr 2 <;> ext i
    · have hcast : Fin.castLE (Nat.le_add_right n m) i = Fin.castAdd m i := by ext; simp
      simp [B, OrthonormalBasis.reindex_apply, hcast]
    · simp [B, OrthonormalBasis.reindex_apply]
  have h₁ : equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)
      ((((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
        map (QuadraticMap.Isometry.inl (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
          (((List.finRange n).map b₁).map fun v ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)).prod := by
    simp [equivOfIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply,
      map_list_prod, List.map_map, Function.comp_def]
  have h₂ : equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)
      ((((List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
        map (QuadraticMap.Isometry.inr (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
          ((((List.finRange m).map b₂).map ((1 : ℂ) ⊗ₜ[ℝ] ·)).map
            (ι (Q₂.baseChange ℂ))).prod := by
    simp [equivOfIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply,
      map_list_prod, List.map_map, Function.comp_def]
  have hpow : ρ₁ (complexVolume Q₁ (-o₁)) ^ m = (-1 : ℂ) ^ m • ρ₁ (complexVolume Q₁ o₁) ^ m := by
    rw [complexVolume_neg_orientation, map_neg, ← neg_one_smul ℂ (ρ₁ (complexVolume Q₁ o₁)),
      smul_pow]
  have hbase : complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q B.toBasis.orientation) =
      (-1 : ℂ) ^ m •
        complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q B.toBasis.orientation) := by
    rw [complexVolume_eq B.toBasis.orientation B rfl hQB, hl, List.map_append, List.prod_append]
    simp only [map_smul, map_mul, complexProdTensor_eq_cliffordProdTensor, h₁, h₂,
      AlgHom.cliffordProdTensor_map_inl, AlgHom.cliffordProdTensor_map_inr_prod,
      List.length_map, List.length_finRange, hpow,
      TensorProduct.map_smul_left, mul_smul_comm]
    rw [smul_comm]
  rcases B.toBasis.orientation_eq_or_eq_neg o with rfl | rfl
  · exact hbase
  · simp [hbase]

/-- **Basis-free volume comparison (`m` even)** assuming a `Q₂`-orthogonal orthonormal frame exists:
for any orientations `o₁` of `V` and `o₂` of `W` (including `-positiveOrientation` in dimension
zero) and `o` the transported `Orientation.prod o₁ o₂`, the normalized volume element of `V ⊕ W`
acts on `E ⊗ F` by `Γ_V ⊗ Γ_W`. -/
theorem complexProdTensor_complexVolume_of_isOrthoᵢ (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) (hm : Even m)
    {b₂ : OrthonormalBasis (Fin m) ℝ W}
    (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  subst o
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  have hpos := complexProdTensor_complexVolume hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
    b₂.toBasis.orientation
    ((Orientation.prod b₁.toBasis.orientation b₂.toBasis.orientation Fact.out Fact.out).map
      (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)
    hm b₁ rfl b₂ rfl hQb₂ (b₁.orientation_toBasis_prod_reindex b₂ Fact.out Fact.out)
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl <;>
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂ with rfl | rfl
  · exact hpos
  · rw [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
      hpos, complexVolume_neg_orientation, map_neg,
      ← neg_one_smul ℂ (ρ₂ _), TensorProduct.map_smul_right]
    ext z; simp
  · rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
      complexProdTensor_neg_orientation_complexVolume hQ _ hQ₁ hn ρ₁ ρ₂ _ hQb₂, hm.neg_one_pow,
      one_smul, hpos, complexVolume_neg_orientation, map_neg,
      ← neg_one_smul ℂ (ρ₁ _), TensorProduct.map_smul_left]
    ext z; simp
  · rw [Orientation.prod_neg_neg,
      complexProdTensor_neg_orientation_complexVolume hQ _ hQ₁ hn ρ₁ ρ₂ _ hQb₂, hm.neg_one_pow,
      one_smul, hpos, complexVolume_neg_orientation, complexVolume_neg_orientation, map_neg,
      map_neg, ← neg_one_smul ℂ (ρ₁ _), ← neg_one_smul ℂ (ρ₂ _), TensorProduct.map_smul_left,
      TensorProduct.map_smul_right]
    ext z; simp

/-- **Basis-free odd volume comparison (`m` odd)** assuming a `Q₂`-orthogonal orthonormal frame
exists: for any orientations `o₁` of `V` and `o₂` of `W` and `o` the transported
`Orientation.prod o₁ o₂`, the normalized volume element of `V ⊕ W` acts on `E ⊗ F` by `1 ⊗ ω_W`. -/
theorem complexProdTensor_complexVolume_of_odd_of_isOrthoᵢ (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) (hm : Odd m)
    {b₂ : OrthonormalBasis (Fin m) ℝ W}
    (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  subst o
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  have hpos := complexProdTensor_complexVolume_of_odd hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
    b₂.toBasis.orientation
    ((Orientation.prod b₁.toBasis.orientation b₂.toBasis.orientation Fact.out Fact.out).map
      (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)
    hm b₁ rfl b₂ rfl hQb₂ (b₁.orientation_toBasis_prod_reindex b₂ Fact.out Fact.out)
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl <;>
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂ with rfl | rfl
  · exact hpos
  · rw [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
      hpos, complexVolume_neg_orientation, map_neg, LinearMap.lTensor_neg]
  · rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
      complexProdTensor_neg_orientation_complexVolume hQ _ hQ₁ hn ρ₁ ρ₂ _ hQb₂, hm.neg_one_pow,
      hpos]
    ext z; simp
  · rw [Orientation.prod_neg_neg,
      complexProdTensor_neg_orientation_complexVolume hQ _ hQ₁ hn ρ₁ ρ₂ _ hQb₂, hm.neg_one_pow,
      hpos, complexVolume_neg_orientation, map_neg, LinearMap.lTensor_neg]
    ext z; simp

/-- **Basis-free chirality of `V ⊕ W` (`m` even)**: for `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and any
orientations `o₁` of `V` and `o₂` of `W` (including rank zero with either sign), the chirality of
`V ⊕ W` for the transported `Orientation.prod o₁ o₂` acts on `E ⊗ F` by `Γ_V ⊗ Γ_W`. -/
theorem complexProdTensor_complexVolume_of_map_prod (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) :=
  complexProdTensor_complexVolume_of_isOrthoᵢ hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm
    (((stdOrthonormalBasis ℝ W).reindex (finCongr Fact.out)).isOrthoᵢ_associated hQ₂) ho

/-- **Basis-free odd volume element of `V ⊕ W` (`m` odd)**: for `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`,
and any orientations `o₁` of `V` and `o₂` of `W`, the normalized volume element of `V ⊕ W` for the
transported `Orientation.prod o₁ o₂` acts on `E ⊗ F` by `1 ⊗ ω_W`. -/
theorem complexProdTensor_complexVolume_of_odd_of_map_prod (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Odd m)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E :=
  complexProdTensor_complexVolume_of_odd_of_isOrthoᵢ hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm
    (((stdOrthonormalBasis ℝ W).reindex (finCongr Fact.out)).isOrthoᵢ_associated hQ₂) ho

end Volume

end CliffordAlgebra
