/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Monoidal
public import TauCeti.LinearAlgebra.ExteriorPower.Prod
public import TauCeti.RingTheory.KoszulComplex.Basic

/-!
# The Koszul complex of a sum of linear functionals

For linear functionals `φ : M → R` and `ψ : N → R`, the Koszul complex of
`φ.coprod ψ : M × N → R` is the tensor product of the Koszul complexes of `φ` and `ψ`:
`K(φ.coprod ψ) ≅ K(φ) ⊗ K(ψ)`, where the tensor product of chain complexes carries the
differential `d(v ⊗ w) = d v ⊗ w + (-1) ^ i v ⊗ d w` for `v` of degree `i`. In degree `n` the
isomorphism is the wedge map `⨁_{i + j = n} ⋀ⁱ M ⊗ ⋀ʲ N → ⋀ⁿ (M × N)`, `a ⊗ b ↦ a ∧ b`, and it
is compatible with the differentials because the contraction by `φ.coprod ψ` is an odd derivation:
`d(a ∧ b) = d a ∧ b + (-1) ^ i a ∧ d b`.

For finite sequences this says that the Koszul complex of a concatenated sequence `(x, y)` is the
tensor product `K(x) ⊗ K(y)`.

The tensor product is the one of `HomologicalComplex`, built from Mathlib's monoidal structure on
`ModuleCat.{u} R` for `R : Type u`; this is why `M` and `N` live in the universe of `R`.

## Main declarations

* `TauCeti.koszulComplex.tensorHomCoprod φ ψ`: the chain map `K(φ) ⊗ K(ψ) ⟶ K(φ.coprod ψ)`,
  given on the summand `⋀ⁱ M ⊗ ⋀ʲ N` by `a ⊗ b ↦ a ∧ b`.
* `TauCeti.koszulComplex.tensorIsoCoprod φ ψ`: this chain map is an isomorphism; in each degree
  its inverse is the sum of the components of `⋀ⁿ (M × N)`
  (`TauCeti.koszulComplex.tensorIsoCoprod_inv_f`).
* `TauCeti.koszulComplex.tensorIsoSumElim x y`: `K(x) ⊗ K(y) ≅ K(x, y)` for finite sequences
  `x` and `y`, where `(x, y)` is the concatenated sequence `Sum.elim x y`; its components are
  `TauCeti.koszulComplex.tensorIsoSumElim_hom` and `TauCeti.koszulComplex.tensorIsoSumElim_inv`.

## References

* [The Stacks Project, Section 0621 (Koszul complexes)](https://stacks.math.columbia.edu/tag/0621)
-/

public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory CliffordAlgebra TensorProduct

namespace TauCeti

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (φ : Module.Dual R M) (ψ : Module.Dual R N)

namespace koszulComplex

/-- The wedge map `⋀ⁱ M ⊗ ⋀ʲ N → ⋀ⁿ (M × N)` for `i + j = n`, as a morphism from the summand
`K(φ)ᵢ ⊗ K(ψ)ⱼ` of `(K(φ) ⊗ K(ψ))ₙ` to `K(φ.coprod ψ)ₙ`. The morphism
`ModuleCat.ofHom (exteriorPower.mulInlInr R M N h)` has source `ModuleCat.of R (⋀ⁱ M ⊗ ⋀ʲ N)`,
which is only definitionally equal to `K(φ)ᵢ ⊗ K(ψ)ⱼ`; fixing the source and target here lets the
elementwise computations below elaborate on `a ⊗ₜ b` for `a ∈ K(φ)ᵢ`, `b ∈ K(ψ)ⱼ`. -/
private def wedge {i j n : ℕ} (h : i + j = n) :
    (koszulComplex φ).X i ⊗ (koszulComplex ψ).X j ⟶ (koszulComplex (φ.coprod ψ)).X n :=
  ModuleCat.ofHom (exteriorPower.mulInlInr R M N h)

/-- The differential of `K(χ)`, elementwise in the exterior algebra: it is the contraction by
`χ`. -/
private theorem coe_d_hom_apply {P : Type u} [AddCommGroup P] [Module R P] (χ : Module.Dual R P)
    (n : ℕ) (x : (koszulComplex χ).X (n + 1)) :
    Subtype.val (p := (· ∈ ⋀[R]^n P)) (((koszulComplex χ).d (n + 1) n).hom x) =
      contractLeft (Q := 0) χ (Subtype.val (p := (· ∈ ⋀[R]^(n + 1) P)) x) := by
  rw [koszulComplex_d]
  exact coe_koszulDifferential_apply χ n x

/-- Addition and integer multiples in the terms of `K(χ)`, in the exterior algebra. -/
private theorem coe_add_zsmul {P : Type u} [AddCommGroup P] [Module R P] (χ : Module.Dual R P)
    {n : ℕ} (x y : (koszulComplex χ).X n) (k : ℤ) :
    Subtype.val (p := (· ∈ ⋀[R]^n P)) (x + k • y) =
      Subtype.val (p := (· ∈ ⋀[R]^n P)) x + k • Subtype.val (p := (· ∈ ⋀[R]^n P)) y :=
  (rfl)

private theorem coe_wedge_tmul {i j n : ℕ} (h : i + j = n) (a : (koszulComplex φ).X i)
    (b : (koszulComplex ψ).X j) :
    Subtype.val (p := (· ∈ ⋀[R]^n (M × N))) ((wedge φ ψ h).hom (a ⊗ₜ b)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) (Subtype.val (p := (· ∈ ⋀[R]^i M)) a) *
        ExteriorAlgebra.map (LinearMap.inr R M N) (Subtype.val (p := (· ∈ ⋀[R]^j N)) b) :=
  exteriorPower.coe_mulInlInr_tmul h a b

/-- The Koszul differential of `φ.coprod ψ` on `a ∧ b` is `d a ∧ b + (-1) ^ i a ∧ d b`. -/
private theorem coe_d_wedge_tmul {i j n : ℕ} (h : i + j = n + 1) (a : (koszulComplex φ).X i)
    (b : (koszulComplex ψ).X j) :
    Subtype.val (p := (· ∈ ⋀[R]^n (M × N)))
        (((koszulComplex (φ.coprod ψ)).d (n + 1) n).hom ((wedge φ ψ h).hom (a ⊗ₜ b))) =
      ExteriorAlgebra.map (LinearMap.inl R M N)
          (contractLeft (Q := 0) φ (Subtype.val (p := (· ∈ ⋀[R]^i M)) a)) *
        ExteriorAlgebra.map (LinearMap.inr R M N) (Subtype.val (p := (· ∈ ⋀[R]^j N)) b) +
      (-1 : R) ^ i •
        (ExteriorAlgebra.map (LinearMap.inl R M N) (Subtype.val (p := (· ∈ ⋀[R]^i M)) a) *
          ExteriorAlgebra.map (LinearMap.inr R M N)
            (contractLeft (Q := 0) ψ (Subtype.val (p := (· ∈ ⋀[R]^j N)) b))) := by
  rw [coe_d_hom_apply, coe_wedge_tmul]
  exact ExteriorAlgebra.contractLeft_coprod_map_inl_mul_map_inr φ ψ
    (Subtype.property (p := (· ∈ ⋀[R]^i M)) a) _

/-- The Leibniz rule for the wedge map when the first factor has degree zero. -/
private theorem wedge_d_of_left_zero {j m : ℕ} (h : 0 + (j + 1) = m + 1) (h₂ : 0 + j = m) :
    wedge φ ψ h ≫ (koszulComplex (φ.coprod ψ)).d (m + 1) m =
      (koszulComplex φ).X 0 ◁ (koszulComplex ψ).d (j + 1) j ≫ wedge φ ψ h₂ := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
  apply Subtype.ext
  rw [coe_d_wedge_tmul, coe_wedge_tmul, coe_d_hom_apply,
    ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero φ
      (Subtype.property (p := (· ∈ ⋀[R]^0 M)) a)]
  simp

/-- The Leibniz rule for the wedge map when the second factor has degree zero. -/
private theorem wedge_d_of_right_zero {i m : ℕ} (h : i + 1 + 0 = m + 1) (h₁ : i + 0 = m) :
    wedge φ ψ h ≫ (koszulComplex (φ.coprod ψ)).d (m + 1) m =
      (koszulComplex φ).d (i + 1) i ▷ (koszulComplex ψ).X 0 ≫ wedge φ ψ h₁ := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.MonoidalCategory.whiskerRight_apply]
  apply Subtype.ext
  rw [coe_d_wedge_tmul, coe_wedge_tmul, coe_d_hom_apply,
    ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero ψ
      (Subtype.property (p := (· ∈ ⋀[R]^0 N)) b)]
  simp

/-- The Leibniz rule for the wedge map when both factors have positive degree. -/
private theorem wedge_d_of_succ_succ {i j m : ℕ} (h : i + 1 + (j + 1) = m + 1)
    (h₁ : i + (j + 1) = m) (h₂ : i + 1 + j = m) :
    wedge φ ψ h ≫ (koszulComplex (φ.coprod ψ)).d (m + 1) m =
      (koszulComplex φ).d (i + 1) i ▷ (koszulComplex ψ).X (j + 1) ≫ wedge φ ψ h₁ +
        (((-1 : ℤˣ) ^ (i + 1) : ℤˣ) : ℤ) •
          ((koszulComplex φ).X (i + 1) ◁ (koszulComplex ψ).d (j + 1) j ≫ wedge φ ψ h₂) := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_zsmul, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.smul_apply]
  rw [ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  apply Subtype.ext
  rw [coe_d_wedge_tmul, coe_add_zsmul, coe_wedge_tmul, coe_wedge_tmul, coe_d_hom_apply,
    coe_d_hom_apply, ← Int.cast_smul_eq_zsmul R]
  simp

/-- The chain map `K(φ) ⊗ K(ψ) ⟶ K(φ.coprod ψ)`, given on the summand `⋀ⁱ M ⊗ ⋀ʲ N` of degree
`i + j` by the wedge map `a ⊗ b ↦ a ∧ b`. It is an isomorphism, see
`koszulComplex.tensorIsoCoprod`. -/
def tensorHomCoprod : koszulComplex φ ⊗ koszulComplex ψ ⟶ koszulComplex (φ.coprod ψ) where
  f n := HomologicalComplex.mapBifunctorDesc fun i j h ↦ wedge φ ψ h
  comm' n m hnm := by
    obtain rfl : n = m + 1 := hnm.symm
    refine HomologicalComplex.mapBifunctor.hom_ext fun i j h ↦ ?_
    -- The tensor product of complexes is `HomologicalComplex.mapBifunctor` of the tensor product,
    -- whose differential is the sum of those of the two factors, with the Koszul sign.
    have hd : (koszulComplex φ ⊗ koszulComplex ψ).d (m + 1) m =
        HomologicalComplex.mapBifunctor.D₁ _ _ _ _ (m + 1) m +
          HomologicalComplex.mapBifunctor.D₂ _ _ _ _ (m + 1) m :=
      HomologicalComplex.mapBifunctor.d_eq _ _ _ _ _ _
    have h' : i + j = m + 1 := h
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc, hd,
      Preadditive.add_comp, Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rcases i with _ | i <;> rcases j with _ | j
    · omega
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp),
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (ComplexShape.down_mk (j + 1) j rfl) _
          (by omega : 0 + j = m)]
      simp only [Limits.zero_comp, zero_add, Category.assoc, ComplexShape.ε₂_def,
        ComplexShape.ε_down_ℕ, pow_zero, one_smul, HomologicalComplex.ι_mapBifunctorDesc,
        curriedTensor_obj_map]
      exact wedge_d_of_left_zero φ ψ h' _
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp),
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (ComplexShape.down_mk (i + 1) i rfl) _ _
          (by omega : i + 0 = m)]
      simp only [Limits.zero_comp, add_zero, Category.assoc, ComplexShape.ε₁_def, one_smul,
        HomologicalComplex.ι_mapBifunctorDesc, curriedTensor_map_app]
      exact wedge_d_of_right_zero φ ψ h' _
    · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (ComplexShape.down_mk (i + 1) i rfl) _ _
          (by omega : i + (j + 1) = m),
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (ComplexShape.down_mk (j + 1) j rfl) _
          (by omega : i + 1 + j = m)]
      simp only [Category.assoc, ComplexShape.ε₁_def, one_smul, ComplexShape.ε₂_def,
        ComplexShape.ε_down_ℕ, Units.smul_def, Preadditive.zsmul_comp,
        HomologicalComplex.ι_mapBifunctorDesc, curriedTensor_map_app, curriedTensor_obj_map]
      exact wedge_d_of_succ_succ φ ψ h' _ _

/-- On the summand `⋀ⁱ M ⊗ ⋀ʲ N` of `(K(φ) ⊗ K(ψ))ₙ`, the chain map `tensorHomCoprod φ ψ` is the
wedge map `a ⊗ b ↦ a ∧ b`. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_tensorHomCoprod_f (i j n : ℕ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj (koszulComplex φ) (koszulComplex ψ) i j n h ≫
        (tensorHomCoprod φ ψ).f n =
      ModuleCat.ofHom (exteriorPower.mulInlInr R M N h) := by
  dsimp only [tensorHomCoprod]
  exact HomologicalComplex.ι_mapBifunctorDesc _ i j h

/-- The `(i, j)`-component `⋀ⁿ (M × N) → ⋀ⁱ M ⊗ ⋀ʲ N`, as a morphism from `K(φ.coprod ψ)ₙ` to
the summand `K(φ)ᵢ ⊗ K(ψ)ⱼ` (with source and target fixed as for `wedge`). -/
private def component (i j : ℕ) {n : ℕ} :
    (koszulComplex (φ.coprod ψ)).X n ⟶ (koszulComplex φ).X i ⊗ (koszulComplex ψ).X j :=
  ModuleCat.ofHom (exteriorPower.prodComponent R M N i j)

private theorem wedge_component {i j n : ℕ} (h : i + j = n) :
    wedge φ ψ h ≫ component φ ψ i j = 𝟙 _ :=
  ModuleCat.MonoidalCategory.tensor_ext fun a b ↦
    exteriorPower.prodComponent_mulInlInr_tmul h a b

private theorem wedge_component_of_ne {i j n : ℕ} (h : i + j = n) {k : ℕ} (l : ℕ) (hk : k ≠ i) :
    wedge φ ψ h ≫ component φ ψ k l = 0 :=
  ModuleCat.hom_ext <| LinearMap.ext fun x ↦ exteriorPower.prodComponent_mulInlInr_of_ne h l hk x

/-- The inverse of `tensorHomCoprod φ ψ` in degree `n`: the sum of the components of
`⋀ⁿ (M × N)` in the summands `⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N`. -/
private def tensorInv (n : ℕ) :
    (koszulComplex (φ.coprod ψ)).X n ⟶ (koszulComplex φ ⊗ koszulComplex ψ).X n :=
  ∑ i : Fin (n + 1), component φ ψ (i : ℕ) (n - i) ≫
    HomologicalComplex.ιTensorObj (koszulComplex φ) (koszulComplex ψ) (i : ℕ) (n - i) n
      (Nat.add_sub_of_le i.is_le)

private theorem tensorHomCoprod_f_tensorInv (n : ℕ) :
    (tensorHomCoprod φ ψ).f n ≫ tensorInv φ ψ n = 𝟙 _ := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun i j h ↦ ?_
  have h' : i + j = n := h
  obtain rfl : j = n - i := by omega
  simp only [tensorInv, Preadditive.comp_sum, ιTensorObj_tensorHomCoprod_f_assoc]
  rw [Fintype.sum_eq_single ⟨i, by omega⟩ fun k hk ↦ ?_]
  · exact ((reassoc_of% wedge_component φ ψ h') _).trans (Category.comp_id _).symm
  · exact ((reassoc_of% wedge_component_of_ne φ ψ h' _ fun hki ↦ hk (Fin.ext hki)) _).trans
      Limits.zero_comp

private theorem tensorInv_tensorHomCoprod_f (n : ℕ) :
    tensorInv φ ψ n ≫ (tensorHomCoprod φ ψ).f n = 𝟙 _ := by
  simp only [tensorInv, Preadditive.sum_comp, Category.assoc, ιTensorObj_tensorHomCoprod_f]
  refine ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_id, LinearMap.id_apply]
  exact exteriorPower.sum_mulInlInr_prodComponent n x

/-- **The Koszul complex of `φ.coprod ψ` is the tensor product of the Koszul complexes of `φ` and
`ψ`**: the chain map `tensorHomCoprod φ ψ`, given by `a ⊗ b ↦ a ∧ b` on each summand
`⋀ⁱ M ⊗ ⋀ʲ N`, is an isomorphism `K(φ) ⊗ K(ψ) ≅ K(φ.coprod ψ)`. -/
def tensorIsoCoprod : koszulComplex φ ⊗ koszulComplex ψ ≅ koszulComplex (φ.coprod ψ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ⟨(tensorHomCoprod φ ψ).f n, tensorInv φ ψ n, tensorHomCoprod_f_tensorInv φ ψ n,
      tensorInv_tensorHomCoprod_f φ ψ n⟩)
    fun _ _ _ ↦ (tensorHomCoprod φ ψ).comm _ _

/-- The isomorphism `tensorIsoCoprod φ ψ` has underlying chain map `tensorHomCoprod φ ψ`. -/
@[simp]
theorem tensorIsoCoprod_hom : (tensorIsoCoprod φ ψ).hom = tensorHomCoprod φ ψ :=
  (rfl)

/-- In degree `n`, the inverse of `tensorIsoCoprod φ ψ` is the sum of the `(i, n - i)`-components
`⋀ⁿ (M × N) → ⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N`. -/
@[simp]
theorem tensorIsoCoprod_inv_f (n : ℕ) :
    (tensorIsoCoprod φ ψ).inv.f n = ∑ i : Fin (n + 1),
      ModuleCat.ofHom (exteriorPower.prodComponent R M N i (n - i)) ≫
        HomologicalComplex.ιTensorObj (koszulComplex φ) (koszulComplex ψ) i (n - i) n
          (Nat.add_sub_of_le i.is_le) :=
  (rfl)

/-- The chain map `tensorHomCoprod φ ψ` is an isomorphism. -/
instance : IsIso (tensorHomCoprod φ ψ) :=
  tensorIsoCoprod_hom φ ψ ▸ inferInstance

/-- **The Koszul complex of a concatenated sequence**: for finite sequences `x` and `y` in `R`,
`K(x) ⊗ K(y) ≅ K(x, y)`, where `(x, y)` is the sequence `Sum.elim x y` indexed by `ι ⊕ κ`. The
index types live in the universe of `R`, so that `ι → R` does too. -/
def tensorIsoSumElim {ι κ : Type u} [Fintype ι] [Fintype κ] (x : ι → R) (y : κ → R) :
    koszulComplex (Fintype.linearCombination R x) ⊗ koszulComplex (Fintype.linearCombination R y) ≅
      koszulComplex (Fintype.linearCombination R (Sum.elim x y)) :=
  tensorIsoCoprod _ _ ≪≫ isoOfEquiv (LinearEquiv.sumArrowLequivProdArrow ι κ R R).symm (by
    ext v <;> simp [Fintype.linearCombination_apply, Fintype.sum_sum_type])

/-- The isomorphism `tensorIsoSumElim x y` is the wedge chain map `tensorHomCoprod` followed by the
map induced by the identification `(ι → R) × (κ → R) ≃ (ι ⊕ κ → R)`. -/
@[simp]
theorem tensorIsoSumElim_hom {ι κ : Type u} [Fintype ι] [Fintype κ] (x : ι → R) (y : κ → R) :
    (tensorIsoSumElim x y).hom = tensorHomCoprod _ _ ≫
      map (LinearEquiv.sumArrowLequivProdArrow ι κ R R).symm.toLinearMap (by
        ext v <;> simp [Fintype.linearCombination_apply, Fintype.sum_sum_type]) := by
  rw [tensorIsoSumElim, Iso.trans_hom, tensorIsoCoprod_hom, isoOfEquiv_hom]

/-- The inverse of `tensorIsoSumElim x y` is the map induced by the identification
`(ι ⊕ κ → R) ≃ (ι → R) × (κ → R)` followed by the inverse of `tensorIsoCoprod`. -/
@[simp]
theorem tensorIsoSumElim_inv {ι κ : Type u} [Fintype ι] [Fintype κ] (x : ι → R) (y : κ → R) :
    (tensorIsoSumElim x y).inv =
      map (LinearEquiv.sumArrowLequivProdArrow ι κ R R).toLinearMap (by
        ext v; simp [Fintype.linearCombination_apply, Fintype.sum_sum_type]) ≫
        (tensorIsoCoprod _ _).inv := by
  rw [tensorIsoSumElim, Iso.trans_inv, isoOfEquiv_inv]
  rfl

end koszulComplex

end TauCeti
