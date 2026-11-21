/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
public import TauCeti.LinearAlgebra.Orientation.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Comparison with `CliffordAlgebra.prodEquiv` and basis-free product volume formulas

This file records two foundational tools for `CliffordAlgebra.complexProdTensor`:

1. **Comparison with `AlgHom.cliffordProdTensor` and `CliffordAlgebra.prodEquiv`**: composing with
   `equivOfIsometry ((withLpProd hQ).baseChangeProd ℂ)` identifies `complexProdTensor` with
   `AlgHom.cliffordProdTensor` graded by `Γ_V` (`CliffordAlgebra.complexProdTensor_eq_comp`). Under
   `CliffordAlgebra.toProd`, a pure tensor `a ᵍ⊗ b` with `b` of parity `j` acts by
   `ρ₁ a Γ_V ^ j ⊗ ρ₂ b` (`CliffordAlgebra.complexProdTensor_symm_toProd_tmul`), hence with the
   Koszul sign `(-1) ^ (j * i)` on `(-1) ^ i`-eigenvectors of `Γ_V`.
2. **Basis-free volume-element formulas**: using `Orientation.prod`, for any real quadratic form
   `Q₂` on finite-dimensional `W`, `complexVolume Q o` acts by `Γ_V ^ (m + 1) ⊗ Γ_W`
   (`CliffordAlgebra.complexProdTensor_complexVolume_eq_map_pow_of_map_prod`), yielding
   `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W` (`m` even, `CliffordAlgebra.complexProdTensor_complexVolume_of_map_prod`)
   and `ω_(V ⊕ W) = 1 ⊗ ω_W` (`m` odd,
   `CliffordAlgebra.complexProdTensor_complexVolume_of_odd_of_map_prod`) for arbitrary orientations
   `o₁`, `o₂`, including `-positiveOrientation` in dimension zero.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module
open scoped RealInnerProductSpace TensorProduct

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
          (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom :=
  (rfl)

/-- Pointwise form of `CliffordAlgebra.complexProdTensor_eq_comp`. -/
theorem complexProdTensor_eq_cliffordProdTensor (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x =
      AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
        (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) x) :=
  AlgHom.congr_fun (complexProdTensor_eq_comp hQ o₁ hQ₁ hn ρ₁ ρ₂) x

/-- **Comparison with `CliffordAlgebra.prodEquiv`**: transporting `a ᵍ⊗ b` with `b` of parity `j`
into `CliffordAlgebra (Q.baseChange ℂ)` makes it act on `E ⊗ F` by `ρ₁ a Γ_V ^ j ⊗ ρ₂ b`. -/
theorem complexProdTensor_symm_toProd_tmul (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).symm
          (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (a ᵍ⊗ₜ b))) =
      TensorProduct.map (ρ₁ a * ρ₁ (complexVolume Q₁ o₁) ^ j.val) (ρ₂ b) := by
  rw [complexProdTensor_eq_cliffordProdTensor, AlgEquiv.apply_symm_apply,
    AlgHom.cliffordProdTensor_toProd_tmul _ _ _ _ _ a hb]

/-- **Koszul-signed action under `CliffordAlgebra.prodEquiv`**: a pure tensor `a ᵍ⊗ b` with `b` of
parity `j` acts on `e ⊗ f` with `Γ_V e = (-1) ^ i • e` by `(-1) ^ (j * i) • (ρ₁ a e ⊗ ρ₂ b f)`. -/
theorem complexProdTensor_symm_toProd_tmul_apply_of_apply_eq_neg_one_pow_smul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j)
    {i : ℕ} {e : E} (he : ρ₁ (complexVolume Q₁ o₁) e = (-1 : ℂ) ^ i • e) (f : F) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).symm
          (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (a ᵍ⊗ₜ b))) (e ⊗ₜ f) =
      (-1 : ℂ) ^ (j.val * i) • (ρ₁ a e ⊗ₜ ρ₂ b f) := by
  rw [complexProdTensor_eq_cliffordProdTensor, AlgEquiv.apply_symm_apply,
    AlgHom.cliffordProdTensor_toProd_tmul_apply_of_apply_eq_neg_one_pow_smul _ _ _ _ _ a hb he f]

end ProdEquiv

private theorem exists_orthonormalBasis_isOrthoᵢ_associated {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {m : ℕ} (hm : finrank ℝ W = m) (Q₂ : QuadraticForm ℝ W) :
    ∃ b : OrthonormalBasis (Fin m) ℝ W, (QuadraticMap.associated Q₂).IsOrthoᵢ b.toBasis := by
  let T : W →ₗ[ℝ] W :=
    ((InnerProductSpace.toDual ℝ W).symm.toLinearIsometry.toLinearMap : StrongDual ℝ W →ₗ[ℝ] W).comp
      ((LinearMap.toContinuousLinearMap : (W →ₗ[ℝ] ℝ) ≃ₗ[ℝ] StrongDual ℝ W).toLinearMap.comp
        (QuadraticMap.associated (R := ℝ) Q₂))
  have hinner : ∀ u v, ⟪T u, v⟫ = QuadraticMap.associated (R := ℝ) Q₂ u v := fun u v ↦ by
    have h : InnerProductSpace.toDual ℝ W (T u) =
        (QuadraticMap.associated (R := ℝ) Q₂ u).toContinuousLinearMap :=
      (InnerProductSpace.toDual ℝ W).apply_symm_apply _
    simpa [InnerProductSpace.toDual_apply_apply] using congrArg (· v) h
  have hT : T.IsSymmetric := fun u v ↦ by
    rw [hinner, QuadraticMap.associated_isSymm ℝ Q₂ u v, real_inner_comm, hinner]
  refine ⟨hT.eigenvectorBasis hm, fun i j hij ↦ ?_⟩
  dsimp only [Function.onFun]
  rw [OrthonormalBasis.coe_toBasis, ← hinner, hT.apply_eigenvectorBasis, real_inner_smul_left,
    (hT.eigenvectorBasis hm).orthonormal.2 hij, mul_zero]

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

/-- Reversing the orientation `o₁` of `V` while holding the orientation `o` of `V ⊕ W` fixed
multiplies the action of `complexVolume Q o` on `E ⊗ F` by `(-1) ^ m`. -/
theorem complexProdTensor_neg_orientation_complexVolume
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (-1 : ℂ) ^ m • complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) := by
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  obtain ⟨b₂, hQb₂⟩ := exists_orthonormalBasis_isOrthoᵢ_associated (m := m) Fact.out Q₂
  let B : OrthonormalBasis (Fin (n + m)) ℝ (WithLp 2 (V × W)) :=
    (b₁.prod b₂).reindex finSumFinEquiv
  have hQb₁ := b₁.isOrthoᵢ_associated hQ₁
  have hbase : complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q B.toBasis.orientation) =
      (-1 : ℂ) ^ m •
        complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q B.toBasis.orientation) := by
    rw [complexProdTensor_complexVolume_eq_map hQ (-o₁) hQ₁ hn ρ₁ ρ₂ B.toBasis.orientation
          b₁ hQb₁ b₂ hQb₂ rfl,
        complexProdTensor_complexVolume_eq_map hQ o₁ hQ₁ hn ρ₁ ρ₂ B.toBasis.orientation
          b₁ hQb₁ b₂ hQb₂ rfl,
        complexVolume_neg_orientation, map_neg, ← neg_one_smul ℂ (ρ₁ (complexVolume Q₁ o₁)),
        smul_pow, mul_smul_comm, TensorProduct.map_smul_left, smul_comm]
  rcases B.toBasis.orientation_eq_or_eq_neg o with rfl | rfl <;> simp [hbase]

/-- **Basis-free volume comparison (`Γ_V ^ (m + 1) ⊗ Γ_W`)**: for `Q₁ v = -‖v‖²`, any quadratic
form `Q₂` on finite-dimensional `W`, and any orientations `o₁` of `V` and `o₂` of `W`,
`complexVolume Q o` for the transported `Orientation.prod o₁ o₂` acts on `E ⊗ F` by
`Γ_V ^ (m + 1) ⊗ Γ_W`. -/
theorem complexProdTensor_complexVolume_eq_map_pow_of_map_prod (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁) ^ (m + 1)) (ρ₂ (complexVolume Q₂ o₂)) := by
  subst o
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  obtain ⟨b₂, hQb₂⟩ := exists_orthonormalBasis_isOrthoᵢ_associated (m := m) Fact.out Q₂
  have hpos := complexProdTensor_complexVolume_eq_map_pow hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
    b₂.toBasis.orientation _ b₁ rfl b₂ rfl hQb₂ (b₁.orientation_toBasis_reindex_prod b₂)
  have ho₂ : complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
      (complexVolume Q ((Orientation.prod b₁.toBasis.orientation o₂ Fact.out Fact.out).map
        (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ b₁.toBasis.orientation) ^ (m + 1))
        (ρ₂ (complexVolume Q₂ o₂)) := by
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂ with rfl | rfl
    · exact hpos
    · rw [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
        hpos, complexVolume_neg_orientation, map_neg, ← neg_one_smul ℂ (ρ₂ _),
        TensorProduct.map_smul_right]
      ext z; simp
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl
  · exact ho₂
  · rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
      complexProdTensor_neg_orientation_complexVolume hQ _ hQ₁ hn ρ₁ ρ₂ _, ho₂,
      complexVolume_neg_orientation, map_neg, ← neg_one_smul ℂ (ρ₁ _), smul_pow,
      TensorProduct.map_smul_left, pow_succ (-1 : ℂ) m, mul_smul, neg_one_smul, smul_neg]

/-- **Basis-free chirality of `V ⊕ W` (`m` even)**: for `Q₁ v = -‖v‖²`, any quadratic form `Q₂`
on `W`, and any orientations `o₁` of `V` and `o₂` of `W`, the chirality of `V ⊕ W` for the
transported `Orientation.prod o₁ o₂` acts on `E ⊗ F` by `Γ_V ⊗ Γ_W`. -/
theorem complexProdTensor_complexVolume_of_map_prod (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) (hm : Even m)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  rw [complexProdTensor_complexVolume_eq_map_pow_of_map_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o ho,
    pow_succ, map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm, one_mul]

/-- **Basis-free odd volume element of `V ⊕ W` (`m` odd)**: for `Q₁ v = -‖v‖²`, any quadratic form
`Q₂` on `W`, and any orientations `o₁` of `V` and `o₂` of `W`, `complexVolume Q o` for the
transported `Orientation.prod o₁ o₂` acts on `E ⊗ F` by `1 ⊗ ω_W`. -/
theorem complexProdTensor_complexVolume_of_odd_of_map_prod (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) (hm : Odd m)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  rw [complexProdTensor_complexVolume_eq_map_pow_of_map_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o ho,
    map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm.add_one, LinearMap.lTensor, Module.End.one_eq_id]

end Volume

section Conjugacy

/-- Evaluating a conjugated algebra-homomorphism intertwining equation
`(T.conjAlgEquiv ℂ).toAlgHom.comp ρ = ρ'.comp (equivOfIsometry f).toAlgHom` at
`complexVolume Q o` when `equivOfIsometry f (complexVolume Q o) = complexVolume Q' o'`. -/
theorem conj_complexVolume_of_conjAlgEquiv_comp
    {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
    {n n' : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ V' = n')]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ V'}
    {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    {ρ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E}
    {ρ' : CliffordAlgebra (Q'.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E'}
    {T : E ≃ₗ[ℂ] E'} {f : (Q.baseChange ℂ).IsometryEquiv (Q'.baseChange ℂ)}
    (hconj : (T.conjAlgEquiv ℂ).toAlgHom.comp ρ =
      ρ'.comp (equivOfIsometry f).toAlgHom)
    {o : Orientation ℝ V (Fin n)} {o' : Orientation ℝ V' (Fin n')}
    (hvol : equivOfIsometry f (complexVolume Q o) = complexVolume Q' o') :
    T.conj (ρ (complexVolume Q o)) = ρ' (complexVolume Q' o') := by
  have hx := AlgHom.congr_fun hconj (complexVolume Q o)
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hvol] at hx
  exact hx

/-- Transporting `complexVolume Q o` along the complexification of a norm-preserving quadratic
isometry `e : Q.IsometryEquiv Q'` that maps `o` to `o'` (up to `finCongr h.symm`) gives
`complexVolume Q' o'`. -/
theorem equivOfIsometry_baseChange_complexVolume_of_map_orientation
    {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
    {n n' : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ V' = n')]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ V'}
    (e : Q.IsometryEquiv Q') (he : ∀ v, ‖e v‖ = ‖v‖)
    {o : Orientation ℝ V (Fin n)} {o' : Orientation ℝ V' (Fin n')} (h : n = n')
    (horient : Orientation.map (Fin n) e.toLinearEquiv o =
      Orientation.reindex ℝ V' (finCongr h.symm) o') :
    equivOfIsometry (e.baseChange ℂ) (complexVolume Q o) = complexVolume Q' o' := by
  rw [equivOfIsometry_apply, QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume_eq_complexVolume_reindex o e he h, horient,
    Orientation.reindex_finCongr_reindex_finCongr]
  simp [finCongr_refl, Orientation.reindex_refl]

/-- Transporting `complexVolume` along `QuadraticMap.IsometryEquiv.withLpProdComm` carries the
ordered product orientation on `V ⊕ W` to that on `W ⊕ V` when `Even (n * m)`. -/
theorem equivOfIsometry_withLpProdComm_complexVolume
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {n m : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
    {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
    {Q : QuadraticForm ℝ (WithLp 2 (V × W))} {Q' : QuadraticForm ℝ (WithLp 2 (W × V))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)
    (o₁ : Orientation ℝ V (Fin n)) (o₂ : Orientation ℝ W (Fin m)) (hnm : Even (n * m)) :
    equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').baseChange ℂ)
        (complexVolume Q ((Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
          (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
      complexVolume Q' ((Orientation.prod o₂ o₁ Fact.out Fact.out).map (Fin (m + n))
        (WithLp.linearEquiv 2 ℝ (W × V)).symm) := by
  have hcongr : (LinearEquiv.prodComm ℝ V W).withLpCongr 2 =
      ((WithLp.linearEquiv 2 ℝ (V × W)).trans (LinearEquiv.prodComm ℝ V W)).trans
        (WithLp.linearEquiv 2 ℝ (W × V)).symm := by ext x; rfl
  refine equivOfIsometry_baseChange_complexVolume_of_map_orientation
    (QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ')
    (fun x ↦ by simpa using (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).norm_map x)
    (add_comm n m) ?_
  simp only [QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProdComm, hcongr, Orientation.map_trans]
  rw [← Orientation.map_symm (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)),
    Equiv.apply_symm_apply, Orientation.map_prodComm_prod_of_even o₁ o₂ Fact.out Fact.out hnm,
    Orientation.map_reindex]

/-- Transporting `complexVolume` along `QuadraticMap.IsometryEquiv.withLpProdAssoc` carries the
left-associated product orientation to the right-associated one. -/
theorem equivOfIsometry_withLpProdAssoc_complexVolume
    {U V W : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {k n m : ℕ} [Fact (finrank ℝ U = k)] [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (U × V)) = k + n)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (WithLp 2 (U × V) × W)) = k + n + m)]
    [Fact (finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = k + (n + m))]
    {Q₁ : QuadraticForm ℝ U} {Q₂ : QuadraticForm ℝ V} {Q₃ : QuadraticForm ℝ W}
    {Q₁₂ : QuadraticForm ℝ (WithLp 2 (U × V))} {Q₂₃ : QuadraticForm ℝ (WithLp 2 (V × W))}
    {Q₁₂_₃ : QuadraticForm ℝ (WithLp 2 (WithLp 2 (U × V) × W))}
    {Q₁_₂₃ : QuadraticForm ℝ (WithLp 2 (U × WithLp 2 (V × W)))}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
    (o₁ : Orientation ℝ U (Fin k)) (o₂ : Orientation ℝ V (Fin n))
    (o₃ : Orientation ℝ W (Fin m)) :
    equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdAssoc
          hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange ℂ)
        (complexVolume Q₁₂_₃
          ((Orientation.prod
              ((Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (k + n))
                (WithLp.linearEquiv 2 ℝ (U × V)).symm) o₃ Fact.out Fact.out).map (Fin (k + n + m))
            (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).symm)) =
      complexVolume Q₁_₂₃
        ((Orientation.prod o₁ ((Orientation.prod o₂ o₃ Fact.out Fact.out).map (Fin (n + m))
            (WithLp.linearEquiv 2 ℝ (V × W)).symm) Fact.out Fact.out).map (Fin (k + (n + m)))
          (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm) := by
  have hUV : finrank ℝ (U × V) = k + n := by
    rw [Module.finrank_prod, Fact.out (p := finrank ℝ U = k), Fact.out (p := finrank ℝ V = n)]
  have hVW : finrank ℝ (V × W) = n + m := by
    rw [Module.finrank_prod, Fact.out (p := finrank ℝ V = n), Fact.out (p := finrank ℝ W = m)]
  refine equivOfIsometry_baseChange_complexVolume_of_map_orientation
    (QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃)
    (fun x ↦ by simpa using (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).norm_map x)
    (add_assoc k n m) ?_
  have hstep1 : Orientation.map (Fin (k + n + m))
      ((WithLp.linearEquiv 2 ℝ (U × V)).prodCongr (LinearEquiv.refl ℝ W))
      (Orientation.prod ((Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (k + n))
        (WithLp.linearEquiv 2 ℝ (U × V)).symm) o₃ Fact.out Fact.out) =
      Orientation.prod (Orientation.prod o₁ o₂ Fact.out Fact.out) o₃ hUV Fact.out := by
    rw [Orientation.map_prod]; congr 1 <;> simp [← Orientation.map_symm]
  have hstep2 : Orientation.map (Fin (k + (n + m)))
      ((LinearEquiv.refl ℝ U).prodCongr (WithLp.linearEquiv 2 ℝ (V × W)).symm)
      (Orientation.prod o₁ (Orientation.prod o₂ o₃ Fact.out Fact.out) Fact.out hVW) =
      Orientation.prod o₁ ((Orientation.prod o₂ o₃ Fact.out Fact.out).map (Fin (n + m))
        (WithLp.linearEquiv 2 ℝ (V × W)).symm) Fact.out Fact.out := by
    rw [Orientation.map_prod]; congr 1; simp
  simp only [QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProdAssoc, Orientation.map_trans]
  rw [← Orientation.map_symm (Fin (k + n + m)) (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)),
    Equiv.apply_symm_apply, hstep1,
    Orientation.map_prodAssoc_prod o₁ o₂ o₃ Fact.out Fact.out Fact.out,
    Orientation.map_reindex, Orientation.map_reindex, hstep2]

/-- Transporting `complexVolume` along `QuadraticMap.IsometryEquiv.withLpUniqueProd` carries the
product orientation with `positiveOrientation` on trivial `V` to `o₂`. -/
theorem equivOfIsometry_withLpUniqueProd_complexVolume
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Unique V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {m : ℕ} [Fact (finrank ℝ V = 0)] [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)]
    {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (o₂ : Orientation ℝ W (Fin m)) :
    equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)
        (complexVolume Q
          ((Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
            Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
      complexVolume Q₂ o₂ := by
  refine equivOfIsometry_baseChange_complexVolume_of_map_orientation
    (QuadraticMap.IsometryEquiv.withLpUniqueProd hQ)
    (fun x ↦ by simpa using (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).norm_map x)
    (zero_add m) ?_
  simpa [← Orientation.map_symm] using
    Orientation.map_uniqueProd_prod_positiveOrientation (E := V) o₂ Fact.out Fact.out

/-- Transporting `complexVolume` along `QuadraticMap.IsometryEquiv.withLpProdUnique` carries the
product orientation with `positiveOrientation` on trivial `W` to `o₁`. -/
theorem equivOfIsometry_withLpProdUnique_complexVolume
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Unique W]
    {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = 0)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n)]
    {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (o₁ : Orientation ℝ V (Fin n)) :
    equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ)
        (complexVolume Q
          ((Orientation.prod o₁ (positiveOrientation : Orientation ℝ W (Fin 0))
            Fact.out Fact.out).map (Fin n) (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
      complexVolume Q₁ o₁ := by
  refine equivOfIsometry_baseChange_complexVolume_of_map_orientation
    (QuadraticMap.IsometryEquiv.withLpProdUnique hQ)
    (fun x ↦ by simpa using (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).norm_map x)
    rfl ?_
  simpa [← Orientation.map_symm] using
    Orientation.map_prodUnique_prod_positiveOrientation (F := W) o₁ Fact.out Fact.out

end Conjugacy

end CliffordAlgebra
