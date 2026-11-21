/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# Frobenius acts on the Picard group by the `p`-th power

Let `R` be a commutative semiring of exponential characteristic `p`. Pulling an invertible
`R`-module `L` back along the Frobenius `frobenius R p : R →+* R` gives its `p`-th tensor power:
`R ⊗[R, φ] L ≃ L^{⊗p}`, by `a ⊗ x ↦ a • (x ⊗ ⋯ ⊗ x)`. Hence the endomorphism of the Picard group
induced by Frobenius is `L ↦ L ^ p` (`CommRing.Pic.mapRingHom_frobenius`). If `R` is perfect, the
Frobenius is a ring automorphism, so the `p`-th power map of `Pic R` is bijective: the Picard group
of a perfect ring is uniquely `p`-divisible (`CommRing.Pic.bijective_pow`). Through deformation
along `A_inf(R) → R` and `A_inf(R) → R^♭`, this is the input for the unique `p`-divisibility of
Picard groups of perfectoid rings.

The diagonal `x ↦ x ⊗ ⋯ ⊗ x` is additive because the tensor powers of an invertible module are
spanned by diagonal tensors in a controlled way: if `ξ y` is the value of a functional on a vector,
then `ξ y ^ n • (x₁ ⊗ ⋯ ⊗ xₙ) = (∏ ξ xᵢ) • (y ⊗ ⋯ ⊗ y)`
(`Module.Invertible.apply_pow_card_smul_tprod`). Summing over finitely many pairs `(ξⱼ, yⱼ)` with
`∑ ξⱼ yⱼ = 1`, whose `p`-th powers again sum to `1`, writes every pure tensor of `L^{⊗p}` as a
combination of diagonal tensors whose coefficients are additive in each `xᵢ` up to `p`-th powers.

## Main declarations

* `Module.Invertible.apply_pow_card_smul_tprod`: `ξ y ^ n • ⨂ xᵢ = (∏ ξ xᵢ) • ⨂ y` in an
  invertible module.
* `CommRing.Pic.mk_tensorPower`: the class of `⨂[R]^n L` is the `n`-th power of the class of `L`.
* `CommRing.Pic.mapRingHom_mk_eq_mk`: if an `f`-semilinear map `M → N` to an invertible module
  spans it, then `N` represents the base change of `M` along `f` in the Picard group.
* `CommRing.Pic.mapRingEquiv`: the isomorphism of Picard groups induced by a ring isomorphism.
* `CommRing.Pic.mapRingHom_frobenius`: Frobenius acts on `Pic R` by `L ↦ L ^ p`.
* `CommRing.Pic.bijective_pow`: over a perfect ring, `L ↦ L ^ p` is bijective on `Pic R`.

## References

* B. Bhatt, P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022), proof of
  Corollary 9.7, where the Picard group of a perfect ring is noted to be uniquely `p`-divisible
  because Frobenius is an automorphism inducing multiplication by `p`.
-/

public section

noncomputable section

open Module TensorProduct PiTensorProduct

namespace Module.Invertible

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Invertible R M]

/-- In an invertible module, scaling a pure tensor `x₁ ⊗ ⋯ ⊗ xₙ` by `ξ y ^ n` gives a multiple of
the diagonal tensor `y ⊗ ⋯ ⊗ y`, with coefficient `∏ ξ xᵢ`. -/
theorem apply_pow_card_smul_tprod {ι : Type*} [Fintype ι] (ξ : Dual R M) (y : M) (x : ι → M) :
    ξ y ^ Fintype.card ι • tprod R x = (∏ i, ξ (x i)) • tprod R fun _ : ι ↦ y := by
  calc ξ y ^ Fintype.card ι • tprod R x = tprod R fun i ↦ ξ y • x i := by
        simp [MultilinearMap.map_smul_univ]
    _ = tprod R fun i ↦ ξ (x i) • y := by simp_rw [apply_smul_comm ξ y]
    _ = (∏ i, ξ (x i)) • tprod R fun _ : ι ↦ y := by simp [MultilinearMap.map_smul_univ]

/-- Tensor powers of an invertible module are invertible. -/
instance tensorPower (n : ℕ) : Module.Invertible R (⨂[R]^n M) := by
  induction n with
  | zero => exact .congr (isEmptyEquiv (Fin 0)).symm
  | succ n ih =>
    exact .congr (TensorProduct.congr (.refl R _)
      (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 ↦ M) 0).symm ≪≫ₗ
        TensorPower.mulEquiv)

end Module.Invertible

namespace CommRing.Pic

section TensorPower

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Invertible R M]

/-- The class of the `n`-th tensor power `⨂[R]^n M` in the Picard group is the `n`-th power of
the class of `M`. -/
theorem mk_tensorPower (n : ℕ) : Pic.mk R (⨂[R]^n M) = Pic.mk R M ^ n := by
  induction n with
  | zero => exact pow_zero (Pic.mk R M) ▸ mk_eq_one_iff.mpr ⟨isEmptyEquiv (Fin 0)⟩
  | succ n ih =>
    rw [pow_succ, ← ih, ← mk_tensor, mk_eq_mk_iff]
    exact ⟨TensorPower.mulEquiv.symm ≪≫ₗ TensorProduct.congr (.refl R _)
      (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 ↦ M) 0)⟩

end TensorPower

section BaseChange

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}
  {M N : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M]
  [AddCommMonoid N] [Module S N] [Module.Invertible S N]

/-- Let `f : R →+* S`, let `M` be an invertible `R`-module and `N` an invertible `S`-module. If an
`f`-semilinear map `g : M → N` has image spanning `N` over `S`, then `N` represents the base
change of `M` along `f` in the Picard group of `S`. -/
theorem mapRingHom_mk_eq_mk (g : M →ₛₗ[f] N) (hg : Submodule.span S (Set.range g) = ⊤) :
    mapRingHom f (Pic.mk R M) = Pic.mk S N := by
  algebraize [f]
  let := Module.restrictScalars R S N
  have := IsScalarTower.restrictScalars R S N
  let l : M →ₗ[R] N := { toFun := g, map_add' := g.map_add, map_smul' := g.map_smulₛₗ }
  have hl : Function.Surjective (l.liftBaseChange S) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [l]⟩
  rw [← RingHom.algebraMap_toAlgebra f, mapRingHom_algebraMap, mapAlgebra_apply, mk_eq_mk_iff]
  exact ⟨AlgebraTensorModule.congr (.refl S S) (mk.linearEquiv R M) ≪≫ₗ
    .ofBijective _ (Module.Invertible.bijective_of_surjective hl)⟩

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism of Picard groups, sending the class of
an invertible module `M` to the class of `S ⊗[R] M`. -/
def mapRingEquiv (e : R ≃+* S) : Pic R ≃* Pic S :=
  MonoidHom.toMulEquiv (mapRingHom e) (mapRingHom e.symm)
    (by rw [mapRingHom_comp_mapRingHom, RingEquiv.symm_comp, mapRingHom_id])
    (by rw [mapRingHom_comp_mapRingHom, RingEquiv.comp_symm, mapRingHom_id])

@[simp]
theorem mapRingEquiv_apply (e : R ≃+* S) (L : Pic R) : mapRingEquiv e L = mapRingHom e L :=
  (rfl)

@[simp]
theorem mapRingEquiv_symm (e : R ≃+* S) : (mapRingEquiv e).symm = mapRingEquiv e.symm :=
  (rfl)

end BaseChange

section Frobenius

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Invertible R M]
  (p : ℕ) [ExpChar R p]

/-- If `∑ ξⱼ yⱼ = 1`, every pure tensor of the `p`-th tensor power of an invertible module is a
combination of the diagonal tensors `yⱼ ⊗ ⋯ ⊗ yⱼ`. -/
private theorem tprod_eq_sum {s : Finset (Dual R M × M)} (hs : ∑ q ∈ s, q.1 q.2 = 1)
    (x : Fin p → M) :
    tprod R x = ∑ q ∈ s, (∏ i, q.1 (x i)) • tprod R fun _ : Fin p ↦ q.2 := by
  calc tprod R x = (∑ q ∈ s, q.1 q.2) ^ p • tprod R x := by rw [hs, one_pow, one_smul]
    _ = ∑ q ∈ s, q.1 q.2 ^ Fintype.card (Fin p) • tprod R x := by
        rw [← frobenius_def, map_sum, Finset.sum_smul, Fintype.card_fin]
        simp [frobenius_def]
    _ = _ := Finset.sum_congr rfl fun q _ ↦ Module.Invertible.apply_pow_card_smul_tprod ..

/-- The diagonal `x ↦ x ⊗ ⋯ ⊗ x` of the `p`-th tensor power of an invertible module, which is
additive and semilinear for the Frobenius. -/
private def tprodDiagonal : M →ₛₗ[frobenius R p] ⨂[R]^p M where
  toFun x := tprod R fun _ ↦ x
  map_add' x y := by
    obtain ⟨s, hs⟩ := Module.Invertible.exists_finset_sum_apply_eq_one (R := R) (M := M)
    rw [tprod_eq_sum p hs, tprod_eq_sum p hs (fun _ ↦ x), tprod_eq_sum p hs (fun _ ↦ y),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    simp [Finset.prod_const, add_pow_expChar, add_smul]
  map_smul' r x := by
    simp [MultilinearMap.map_smul_univ, Finset.prod_const, frobenius_def]

/-- Frobenius acts on the Picard group of a semiring of exponential characteristic `p` by the
`p`-th power: the base change of an invertible module `L` along `frobenius R p` is `L^{⊗p}`. -/
@[simp]
theorem mapRingHom_frobenius (L : Pic R) : mapRingHom (frobenius R p) L = L ^ p := by
  obtain ⟨s, hs⟩ := Module.Invertible.exists_finset_sum_apply_eq_one (R := R) (M := L)
  calc mapRingHom (frobenius R p) L = mapRingHom (frobenius R p) (Pic.mk R L) := by
        rw [mk_eq_self]
    _ = Pic.mk R (⨂[R]^p L) := by
        refine mapRingHom_mk_eq_mk (tprodDiagonal p) (eq_top_iff.2 ?_)
        rw [← span_tprod_eq_top, Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        rw [tprod_eq_sum p hs x]
        exact Submodule.sum_mem _ fun q _ ↦
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩)
    _ = L ^ p := by rw [mk_tensorPower, mk_eq_self]

/-- The Picard group of a perfect semiring of exponential characteristic `p` is uniquely
`p`-divisible: `L ↦ L ^ p` is a bijection of `Pic R`. -/
theorem bijective_pow [PerfectRing R p] : Function.Bijective fun L : Pic R ↦ L ^ p := by
  have h : (frobeniusEquiv R p : R →+* R) = frobenius R p :=
    RingHom.ext fun x ↦ congrFun (coe_frobeniusEquiv R p) x
  convert (mapRingEquiv (frobeniusEquiv R p)).bijective using 1
  ext L
  rw [mapRingEquiv_apply, h, mapRingHom_frobenius]

end Frobenius

end CommRing.Pic
