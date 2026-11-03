/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
public import TauCeti.LinearAlgebra.ExteriorPower.Prod
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.RingTheory.KoszulComplex.Basic

/-!
# The Koszul complex of a direct sum

For linear functionals `φ : M → R` and `ψ : N → R`, the Koszul complex of `φ.coprod ψ` on `M × N`
is the tensor product of the Koszul complexes of `φ` and `ψ`:
`K(φ) ⊗ K(ψ) ≅ K(φ.coprod ψ)`. The tensor product is Mathlib's monoidal structure on chain
complexes, with the sign convention `d (a ⊗ b) = d a ⊗ b + (-1) ^ p a ⊗ d b` for `a` of degree `p`.
For finite sequences this says that the Koszul complex of a concatenated sequence is the tensor
product of the Koszul complexes of its two parts, `K(x, y) ≅ K(x) ⊗ K(y)`, which reduces questions
about Koszul complexes of long sequences to one element at a time.

In degree `n` the isomorphism is `⊕_{p + q = n} ⋀ᵖ M ⊗ ⋀^q N ≅ ⋀ⁿ (M × N)`, `a ⊗ b ↦ a ∧ b`, the
degree-`n` part of Mathlib's algebra isomorphism `ExteriorAlgebra.prodEquivTensor` between
`⋀ (M × N)` and the graded tensor product of `⋀ M` and `⋀ N`. That it commutes with the
differentials is the graded Leibniz rule `CliffordAlgebra.contractLeft_mul` for contraction.

The modules are taken in the universe of the ring, where Mathlib's `ModuleCat` is monoidal.

## Main declarations

* `TauCeti.koszulComplex.tensorIso`: the isomorphism `K(φ) ⊗ K(ψ) ≅ K(φ.coprod ψ)`, with
  `TauCeti.koszulComplex.subtype_tensorIso_hom_f_ιTensorObj_tmul` computing it on `a ⊗ b`.
* `TauCeti.koszulComplex.tensorIsoAppend`: for finite sequences `x` and `y`,
  `K(x) ⊗ K(y) ≅ K(x, y)` with `(x, y) = Fin.append x y`, with
  `TauCeti.koszulComplex.subtype_tensorIsoAppend_hom_f_ιTensorObj_tmul` computing it on `a ⊗ b`.

## References

* [The Stacks Project, Lemma 15.29.12 (Tag 0664)](https://stacks.math.columbia.edu/tag/0664)

The tensor-product interface follows the design of Nailin Guan in the Mathlib pull request
[mathlib4#43711](https://github.com/leanprover-community/mathlib4/pull/43711) (tensor products of
Koszul complexes). No code from that pull request is vendored here.
-/

public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory HomologicalComplex CliffordAlgebra
open TauCeti.exteriorPower (wedgeTensor coe_wedgeTensor_tmul proj coe_proj_of_mem proj_coe
  sum_coe_wedgeTensor_map_proj)
open scoped TensorProduct

namespace TauCeti

namespace koszulComplex

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

variable (φ : Module.Dual R M) (ψ : Module.Dual R N)

/-- The graded Leibniz rule for the Koszul differential of `φ.coprod ψ` on a wedge product. -/
private theorem coe_koszulDifferential_wedgeTensor_tmul (p q n : ℕ) (h : p + q = n + 1)
    (a : ⋀[R]^p M) (b : ⋀[R]^q N) :
    (koszulDifferential (φ.coprod ψ) n (wedgeTensor R M N p q (n + 1) h (a ⊗ₜ b)) :
        ExteriorAlgebra R (M × N)) =
      ExteriorAlgebra.map (LinearMap.inl R M N)
            (contractLeft (Q := 0) φ (a : ExteriorAlgebra R M)) *
          ExteriorAlgebra.map (LinearMap.inr R M N) b +
        (-1 : R) ^ p • (ExteriorAlgebra.map (LinearMap.inl R M N) a *
          ExteriorAlgebra.map (LinearMap.inr R M N)
            (contractLeft (Q := 0) ψ (b : ExteriorAlgebra R N))) := by
  have ha : ExteriorAlgebra.map (LinearMap.inl R M N) (a : ExteriorAlgebra R M) ∈
      ⋀[R]^p (M × N) := by
    rw [← exteriorPower.coe_map]
    exact Submodule.coe_mem _
  rw [coe_koszulDifferential_apply, coe_wedgeTensor_tmul, CliffordAlgebra.contractLeft_mul,
    ExteriorAlgebra.contractLeft_coprod_map_inl, ExteriorAlgebra.contractLeft_map,
    LinearMap.coprod_inr, TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower ha,
    smul_mul_assoc]

/-- The comparison map in degree `n`. -/
private def toKoszul (n : ℕ) :
    (koszulComplex φ ⊗ koszulComplex ψ).X n ⟶ (koszulComplex (φ.coprod ψ)).X n :=
  mapBifunctorDesc fun p q h ↦ ModuleCat.ofHom (wedgeTensor R M N p q n h)

private theorem toKoszul_ιTensorObj_apply (p q n : ℕ) (h : p + q = n)
    (z : ⋀[R]^p M ⊗[R] ⋀[R]^q N) :
    (toKoszul φ ψ n).hom ((ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n h).hom z) =
      wedgeTensor R M N p q n h z :=
  congr($(ι_mapBifunctorDesc (K₁ := koszulComplex φ) (K₂ := koszulComplex ψ)
    (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.down ℕ)
    (fun p q h ↦ ModuleCat.ofHom (wedgeTensor R M N p q n h)) p q h).hom z)

/-- The inverse comparison map in degree `n`, as a linear map. -/
private def fromKoszulLinear (n : ℕ) :
    ⋀[R]^n (M × N) →ₗ[R] (koszulComplex φ ⊗ koszulComplex ψ).X n :=
  ∑ i : Fin (n + 1),
    (ιTensorObj (koszulComplex φ) (koszulComplex ψ) i (n - i) n (by omega)).hom ∘ₗ
      TensorProduct.map (proj R M i) (proj R N (n - i)) ∘ₗ
        (GradedTensorProduct.of R _ _).symm.toLinearMap ∘ₗ
          (ExteriorAlgebra.prodEquivTensor R M N).toLinearMap ∘ₗ (⋀[R]^n (M × N)).subtype

/-- The inverse comparison map in degree `n`. -/
private def fromKoszul (n : ℕ) :
    (koszulComplex (φ.coprod ψ)).X n ⟶ (koszulComplex φ ⊗ koszulComplex ψ).X n :=
  ModuleCat.ofHom (fromKoszulLinear φ ψ n)

private theorem fromKoszul_apply (n : ℕ) (x : ⋀[R]^n (M × N)) :
    (fromKoszul φ ψ n).hom x = ∑ i : Fin (n + 1),
      (ιTensorObj (koszulComplex φ) (koszulComplex ψ) i (n - i) n (by omega)).hom
        (TensorProduct.map (proj R M i) (proj R N (n - i))
          ((GradedTensorProduct.of R _ _).symm (ExteriorAlgebra.prodEquivTensor R M N x))) :=
  by
  -- `fromKoszul` is `ModuleCat.ofHom` of `fromKoszulLinear`, whose source is only definitionally
  -- the term `(koszulComplex (φ.coprod ψ)).X n`, so `ModuleCat.hom_ofHom` does not rewrite.
  change fromKoszulLinear φ ψ n x = _
  simp only [fromKoszulLinear, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  rfl

private theorem fromKoszul_wedgeTensor_tmul (p q n : ℕ) (h : p + q = n) (a : ⋀[R]^p M)
    (b : ⋀[R]^q N) :
    (fromKoszul φ ψ n).hom (wedgeTensor R M N p q n h (a ⊗ₜ b)) =
      (ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n h).hom (a ⊗ₜ b) := by
  have key : ∀ (q' : ℕ) (hq' : q' = q) (h' : p + q' = n),
      (ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q' n h').hom
          (proj R M p a ⊗ₜ proj R N q' b) =
        (ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n h).hom (a ⊗ₜ b) := by
    rintro q' rfl h'
    rw [proj_coe, proj_coe]
  rw [fromKoszul_apply, coe_wedgeTensor_tmul, ← ExteriorAlgebra.prodEquivTensor_symm_tmul,
    AlgEquiv.apply_symm_apply, GradedTensorProduct.of_symm_of]
  simp only [TensorProduct.map_tmul]
  rw [Finset.sum_eq_single ⟨p, by omega⟩]
  · exact key _ (by simp; omega) _
  · rintro i - hi
    have : proj R M i a = 0 := Subtype.ext <| by
      rw [coe_proj_of_mem a.2, ite_eq_right fun h ↦ hi (Fin.ext h.symm)]
      rfl
    rw [this, TensorProduct.zero_tmul]
    exact map_zero _
  · simp

private theorem toKoszul_fromKoszul (n : ℕ) (x : ⋀[R]^n (M × N)) :
    (toKoszul φ ψ n).hom ((fromKoszul φ ψ n).hom x) = x := by
  rw [fromKoszul_apply, map_sum]
  simp only [toKoszul_ιTensorObj_apply]
  -- The sum is taken in the term `(koszulComplex (φ.coprod ψ)).X n` of the Koszul complex, which
  -- is only definitionally the exterior power `⋀ⁿ (M × N)`.
  change (∑ i : Fin (n + 1), wedgeTensor R M N i (n - i) n (by omega) _ : ⋀[R]^n (M × N)) = x
  refine Subtype.ext ?_
  rw [Submodule.coe_sum, sum_coe_wedgeTensor_map_proj]
  simp [proj_coe]


/-- Morphisms out of a summand `⋀ᵖ M ⊗ ⋀^q N` of `K(φ) ⊗ K(ψ)` agree once they agree on pure
tensors. -/
private theorem summand_hom_ext {p q : ℕ} {Y : ModuleCat.{u} R}
    {f g : (koszulComplex φ).X p ⊗ (koszulComplex ψ).X q ⟶ Y}
    (h : ∀ (a : ⋀[R]^p M) (b : ⋀[R]^q N),
      f.hom (a ⊗ₜ b : ⋀[R]^p M ⊗[R] ⋀[R]^q N) = g.hom (a ⊗ₜ b : ⋀[R]^p M ⊗[R] ⋀[R]^q N)) :
    f = g :=
  ModuleCat.MonoidalCategory.tensor_ext h

/-- Morphisms out of `(K(φ) ⊗ K(ψ))ₙ` agree once they agree on pure tensors of every summand. -/
private theorem tensor_hom_ext {n : ℕ} {Y : ModuleCat.{u} R}
    {f g : (koszulComplex φ ⊗ koszulComplex ψ).X n ⟶ Y}
    (h : ∀ (p q : ℕ) (hpq : p + q = n) (a : ⋀[R]^p M) (b : ⋀[R]^q N),
      f.hom ((ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n hpq).hom
          (a ⊗ₜ b : ⋀[R]^p M ⊗[R] ⋀[R]^q N)) =
        g.hom ((ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n hpq).hom
          (a ⊗ₜ b : ⋀[R]^p M ⊗[R] ⋀[R]^q N))) :
    f = g :=
  mapBifunctor.hom_ext fun p q hpq ↦ summand_hom_ext φ ψ fun a b ↦ h p q hpq a b

/-- The comparison in degree `n` is an isomorphism. -/
private def degreeIso (n : ℕ) :
    (koszulComplex φ ⊗ koszulComplex ψ).X n ≅ (koszulComplex (φ.coprod ψ)).X n where
  hom := toKoszul φ ψ n
  inv := fromKoszul φ ψ n
  hom_inv_id := tensor_hom_ext φ ψ fun p q h a b ↦ by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, toKoszul_ιTensorObj_apply,
      fromKoszul_wedgeTensor_tmul, ModuleCat.hom_id, LinearMap.id_apply]
    rfl
  inv_hom_id := by
    ext x : 2
    exact toKoszul_fromKoszul φ ψ n x

private theorem whiskerRight_d_tmul (r q : ℕ) (a : ⋀[R]^(r + 1) M) (b : ⋀[R]^q N) :
    ((koszulComplex φ).d (r + 1) r ▷ (koszulComplex ψ).X q).hom
        (a ⊗ₜ b : ⋀[R]^(r + 1) M ⊗[R] ⋀[R]^q N) =
      (koszulDifferential φ r a ⊗ₜ b : ⋀[R]^r M ⊗[R] ⋀[R]^q N) :=
  (ModuleCat.MonoidalCategory.whiskerRight_apply _ _ _ _).trans
    (congrArg (fun x : ⋀[R]^r M ↦ x ⊗ₜ[R] b) (koszulComplex_d_apply φ r a))

private theorem whiskerLeft_d_tmul (p s : ℕ) (a : ⋀[R]^p M) (b : ⋀[R]^(s + 1) N) :
    ((koszulComplex φ).X p ◁ (koszulComplex ψ).d (s + 1) s).hom
        (a ⊗ₜ b : ⋀[R]^p M ⊗[R] ⋀[R]^(s + 1) N) =
      (a ⊗ₜ koszulDifferential ψ s b : ⋀[R]^p M ⊗[R] ⋀[R]^s N) :=
  (ModuleCat.MonoidalCategory.whiskerLeft_apply _ _ _ _).trans
    (congrArg (fun y : ⋀[R]^s N ↦ a ⊗ₜ[R] y) (koszulComplex_d_apply ψ s b))

private theorem ιTensorObj_toKoszul_d_tmul (p q n : ℕ) (h : p + q = n + 1) (a : ⋀[R]^p M)
    (b : ⋀[R]^q N) :
    (ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q (n + 1) h ≫ toKoszul φ ψ (n + 1) ≫
        (koszulComplex (φ.coprod ψ)).d (n + 1) n).hom (a ⊗ₜ b : ⋀[R]^p M ⊗[R] ⋀[R]^q N) =
      koszulDifferential (φ.coprod ψ) n (wedgeTensor R M N p q (n + 1) h (a ⊗ₜ b)) :=
  (congrArg ((koszulComplex (φ.coprod ψ)).d (n + 1) n).hom
    (toKoszul_ιTensorObj_apply φ ψ p q (n + 1) h (a ⊗ₜ b))).trans (koszulComplex_d_apply _ n _)

private theorem whiskerRight_d_ιTensorObj_toKoszul_tmul (r q n : ℕ) (h : r + q = n)
    (a : ⋀[R]^(r + 1) M) (b : ⋀[R]^q N) :
    ((koszulComplex φ).d (r + 1) r ▷ (koszulComplex ψ).X q ≫
        ιTensorObj (koszulComplex φ) (koszulComplex ψ) r q n h ≫ toKoszul φ ψ n).hom
        (a ⊗ₜ b : ⋀[R]^(r + 1) M ⊗[R] ⋀[R]^q N) =
      wedgeTensor R M N r q n h (koszulDifferential φ r a ⊗ₜ b) :=
  (congrArg (fun z ↦ (toKoszul φ ψ n).hom
      ((ιTensorObj (koszulComplex φ) (koszulComplex ψ) r q n h).hom z))
    (whiskerRight_d_tmul φ ψ r q a b)).trans (toKoszul_ιTensorObj_apply φ ψ r q n h _)

private theorem whiskerLeft_d_ιTensorObj_toKoszul_tmul (p s n : ℕ) (h : p + s = n)
    (a : ⋀[R]^p M) (b : ⋀[R]^(s + 1) N) :
    ((koszulComplex φ).X p ◁ (koszulComplex ψ).d (s + 1) s ≫
        ιTensorObj (koszulComplex φ) (koszulComplex ψ) p s n h ≫ toKoszul φ ψ n).hom
        (a ⊗ₜ b : ⋀[R]^p M ⊗[R] ⋀[R]^(s + 1) N) =
      wedgeTensor R M N p s n h (a ⊗ₜ koszulDifferential ψ s b) :=
  (congrArg (fun z ↦ (toKoszul φ ψ n).hom
      ((ιTensorObj (koszulComplex φ) (koszulComplex ψ) p s n h).hom z))
    (whiskerLeft_d_tmul φ ψ p s a b)).trans (toKoszul_ιTensorObj_apply φ ψ p s n h _)

private theorem koszulDifferential_wedgeTensor_succ_succ (r s n : ℕ) (h : r + 1 + (s + 1) = n + 1)
    (a : ⋀[R]^(r + 1) M) (b : ⋀[R]^(s + 1) N) :
    koszulDifferential (φ.coprod ψ) n (wedgeTensor R M N (r + 1) (s + 1) (n + 1) h (a ⊗ₜ b)) =
      wedgeTensor R M N r (s + 1) n (by omega) (koszulDifferential φ r a ⊗ₜ b) +
        ((-1 : ℤ) ^ (r + 1)) •
          wedgeTensor R M N (r + 1) s n (by omega) (a ⊗ₜ koszulDifferential ψ s b) := by
  refine Subtype.ext ?_
  rw [← Int.cast_smul_eq_zsmul R, coe_koszulDifferential_wedgeTensor_tmul, Submodule.coe_add,
    Submodule.coe_smul, coe_wedgeTensor_tmul, coe_wedgeTensor_tmul, coe_koszulDifferential_apply,
    coe_koszulDifferential_apply]
  push_cast
  rfl

private theorem koszulDifferential_wedgeTensor_zero_succ (n : ℕ) (a : ⋀[R]^0 M)
    (b : ⋀[R]^(n + 1) N) :
    koszulDifferential (φ.coprod ψ) n
        (wedgeTensor R M N 0 (n + 1) (n + 1) (by omega) (a ⊗ₜ b)) =
      ((-1 : ℤ) ^ 0) • wedgeTensor R M N 0 n n (by omega) (a ⊗ₜ koszulDifferential ψ n b) := by
  refine Subtype.ext ?_
  rw [pow_zero, one_smul, coe_koszulDifferential_wedgeTensor_tmul, coe_wedgeTensor_tmul,
    coe_koszulDifferential_apply,
    TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero φ a.2]
  simp

private theorem koszulDifferential_wedgeTensor_succ_zero (n : ℕ) (a : ⋀[R]^(n + 1) M)
    (b : ⋀[R]^0 N) :
    koszulDifferential (φ.coprod ψ) n
        (wedgeTensor R M N (n + 1) 0 (n + 1) (by omega) (a ⊗ₜ b)) =
      wedgeTensor R M N n 0 n (by omega) (koszulDifferential φ n a ⊗ₜ b) := by
  refine Subtype.ext ?_
  rw [coe_koszulDifferential_wedgeTensor_tmul, coe_wedgeTensor_tmul,
    coe_koszulDifferential_apply,
    TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero ψ b.2]
  simp

private theorem toKoszul_comm (n : ℕ) :
    toKoszul φ ψ (n + 1) ≫ (koszulComplex (φ.coprod ψ)).d (n + 1) n =
      (koszulComplex φ ⊗ koszulComplex ψ).d (n + 1) n ≫ toKoszul φ ψ n := by
  refine mapBifunctor.hom_ext fun p q h ↦ ?_
  have hd : (koszulComplex φ ⊗ koszulComplex ψ).d (n + 1) n =
      mapBifunctor.D₁ (koszulComplex φ) (koszulComplex ψ) (curriedTensor (ModuleCat.{u} R))
          (ComplexShape.down ℕ) (n + 1) n +
        mapBifunctor.D₂ (koszulComplex φ) (koszulComplex ψ) (curriedTensor (ModuleCat.{u} R))
          (ComplexShape.down ℕ) (n + 1) n :=
    mapBifunctor.d_eq _ _ _ _ _ _
  rw [hd, Preadditive.add_comp, Preadditive.comp_add]
  -- `h` is stated with `ComplexShape.π`, which on `ComplexShape.down ℕ` is addition by definition.
  change p + q = n + 1 at h
  rcases p with _ | r <;> rcases q with _ | s
  · omega
  · obtain rfl : s = n := by omega
    rw [ChainComplex.ιTensorObj_D₁_zero_assoc, Limits.zero_comp, zero_add,
      ChainComplex.ιTensorObj_D₂_succ_assoc, Preadditive.zsmul_comp, Category.assoc]
    refine summand_hom_ext φ ψ fun a b ↦ ?_
    exact (ιTensorObj_toKoszul_d_tmul φ ψ _ _ _ h a b).trans
      ((koszulDifferential_wedgeTensor_zero_succ φ ψ _ a b).trans
        (congrArg (_ • ·) (whiskerLeft_d_ιTensorObj_toKoszul_tmul φ ψ 0 _ _ _ a b).symm))
  · obtain rfl : r = n := by omega
    rw [ChainComplex.ιTensorObj_D₂_zero_assoc, Limits.zero_comp, add_zero,
      ChainComplex.ιTensorObj_D₁_succ_assoc]
    refine summand_hom_ext φ ψ fun a b ↦ ?_
    exact (ιTensorObj_toKoszul_d_tmul φ ψ _ _ _ h a b).trans
      ((koszulDifferential_wedgeTensor_succ_zero φ ψ _ a b).trans
        (whiskerRight_d_ιTensorObj_toKoszul_tmul φ ψ _ 0 _ _ a b).symm)
  · rw [ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
      Preadditive.zsmul_comp, Category.assoc]
    refine summand_hom_ext φ ψ fun a b ↦ ?_
    exact (ιTensorObj_toKoszul_d_tmul φ ψ _ _ _ h a b).trans
      ((koszulDifferential_wedgeTensor_succ_succ φ ψ r s n h a b).trans
        (congrArg₂ (fun x y : (koszulComplex (φ.coprod ψ)).X n ↦ x + y)
          (whiskerRight_d_ιTensorObj_toKoszul_tmul φ ψ r (s + 1) n _ a b)
          (congrArg (_ • ·) (whiskerLeft_d_ιTensorObj_toKoszul_tmul φ ψ (r + 1) s n _ a b))).symm)


/-- **The Koszul complex of a direct sum is the tensor product of Koszul complexes**:
`K(φ) ⊗ K(ψ) ≅ K(φ.coprod ψ)` for linear functionals `φ` on `M` and `ψ` on `N`. In degree `n` it
sends `a ⊗ b ∈ ⋀ᵖ M ⊗ ⋀^q N`, for `p + q = n`, to `a ∧ b ∈ ⋀ⁿ (M × N)`, see
`subtype_tensorIso_hom_f_ιTensorObj_tmul`; the tensor product carries the differential
`d (a ⊗ b) = d a ⊗ b + (-1) ^ p a ⊗ d b`. -/
def tensorIso : koszulComplex φ ⊗ koszulComplex ψ ≅ koszulComplex (φ.coprod ψ) :=
  Hom.isoOfComponents (degreeIso φ ψ) <| by
    rintro _ n rfl
    exact toKoszul_comm φ ψ n

/-- `tensorIso φ ψ` sends `a ⊗ b ∈ ⋀ᵖ M ⊗ ⋀^q N` to the wedge product `a ∧ b` of the images of
`a` and `b` in `⋀ (M × N)`. -/
theorem subtype_tensorIso_hom_f_ιTensorObj_tmul (p q n : ℕ) (h : p + q = n) (a : ⋀[R]^p M)
    (b : ⋀[R]^q N) :
    (⋀[R]^n (M × N)).subtype (((tensorIso φ ψ).hom.f n).hom
        ((ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n h).hom
          (a ⊗ₜ b : ⋀[R]^p M ⊗[R] ⋀[R]^q N))) =
      ExteriorAlgebra.map (LinearMap.inl R M N) a * ExteriorAlgebra.map (LinearMap.inr R M N) b :=
  (congrArg Subtype.val (toKoszul_ιTensorObj_apply φ ψ p q n h _)).trans
    (coe_wedgeTensor_tmul p q n h a b)

section Sequence

/-- **Koszul complexes of concatenated sequences**: for finite sequences `x = (x₁, …, xₘ)` and
`y = (y₁, …, yₙ)` in `R`, `K(x) ⊗ K(y) ≅ K(x, y)`, where `K(x)` is the Koszul complex of the
functional `v ↦ ∑ᵢ vᵢ xᵢ` on `Rᵐ` and `(x, y)` is the concatenation `Fin.append x y`. -/
def tensorIsoAppend {m n : ℕ} (x : Fin m → R) (y : Fin n → R) :
    koszulComplex (Fintype.linearCombination R x) ⊗ koszulComplex (Fintype.linearCombination R y) ≅
      koszulComplex (Fintype.linearCombination R (Fin.append x y)) :=
  tensorIso _ _ ≪≫ (mapIso (LinearEquiv.piFinAppend R R m n)
    (LinearEquiv.coprod_linearCombination_comp_piFinAppend x y)).symm

/-- `tensorIsoAppend x y` sends `a ⊗ b ∈ ⋀ᵖ Rᵐ ⊗ ⋀^q Rⁿ` to the wedge product `a ∧ b` of the images
of `a` and `b` in `⋀ R^(m + n)`, where `Rᵐ` and `Rⁿ` are included in `R^(m + n)` as the first `m`
and the last `n` coordinates. -/
@[simp]
theorem subtype_tensorIsoAppend_hom_f_ιTensorObj_tmul {m n : ℕ} (x : Fin m → R) (y : Fin n → R)
    (p q k : ℕ) (h : p + q = k) (a : ⋀[R]^p (Fin m → R)) (b : ⋀[R]^q (Fin n → R)) :
    (⋀[R]^k (Fin (m + n) → R)).subtype (((tensorIsoAppend x y).hom.f k).hom
        ((ιTensorObj (koszulComplex (Fintype.linearCombination R x))
          (koszulComplex (Fintype.linearCombination R y)) p q k h).hom
          (a ⊗ₜ b : ⋀[R]^p (Fin m → R) ⊗[R] ⋀[R]^q (Fin n → R)))) =
      ExteriorAlgebra.map
          ((LinearEquiv.piFinAppend R R m n).symm.toLinearMap ∘ₗ LinearMap.inl R _ _) a *
        ExteriorAlgebra.map
          ((LinearEquiv.piFinAppend R R m n).symm.toLinearMap ∘ₗ LinearMap.inr R _ _) b := by
  rw [tensorIsoAppend, Iso.trans_hom, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, Iso.symm_hom, mapIso_inv]
  simp only [map_f]
  refine (exteriorPower.coe_map _ _).trans ((congrArg (ExteriorAlgebra.map _)
    (subtype_tensorIso_hom_f_ιTensorObj_tmul _ _ p q k h a b)).trans ?_)
  rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map]

end Sequence

end koszulComplex

end TauCeti
