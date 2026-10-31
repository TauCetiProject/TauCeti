/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorPower.Symmetric
public import TauCeti.RingTheory.DividedPowerAlgebra.Representability
public import TauCeti.RingTheory.PolynomialLaw.Pow
import Mathlib.RingTheory.TensorProduct.Free
import TauCeti.Data.Sym.Basic

/-!
# Homogeneous divided powers and symmetric tensors

For a module `M` over a commutative semiring `R` and `d : ℕ`, this file constructs Roby's natural
`R`-linear map `Γ^d_R(M) → ⨂[R]^d M` sending `dp R d m` to `m ⊗ ⋯ ⊗ m`. It is the linear map
representing the tensor power law `m ↦ m ⊗ ⋯ ⊗ m`, which is homogeneous of degree `d`. On a product
of divided powers `∏ⱼ dp R lⱼ mⱼ` it takes the value `∑_w m_{w 0} ⊗ ⋯ ⊗ m_{w (d - 1)}`, the sum
over all words `w` of length `d` in which each letter `j` occurs exactly `lⱼ` times. Its values are
symmetric tensors.

For a free module `M` the map is an isomorphism onto the symmetric tensors (Roby, Theorem IV.2 and
Proposition IV.5). No factorial is inverted: over `𝔽_p` the divided power `dp R p e` of a basis
vector goes to the nonzero symmetric tensor `e ⊗ ⋯ ⊗ e`, although `e ^ p = p! • dp R p e`
vanishes in the full divided power algebra; for `M = ℤ e ⊕ ℤ f`, the product `dp 1 e * dp 1 f`
goes to `e ⊗ f + f ⊗ e`, with no factor `1/2`.

## Main declarations

* `DividedPowerAlgebra.toTensorPower R M d`: the linear map `Γ^d_R(M) → ⨂[R]^d M`, with
  `DividedPowerAlgebra.toTensorPower_dp`, the product formula
  `DividedPowerAlgebra.toTensorPower_prod_dp`, and the characterization
  `DividedPowerAlgebra.toPolynomialLaw_toTensorPower_comp_gamma` by the tensor power law.
* `DividedPowerAlgebra.toTensorPower_mem_symmetricTensors`: its values are symmetric tensors.
* `DividedPowerAlgebra.symmetricTensorMap R M d`: the corestriction
  `Γ^d_R(M) → TensorPower.symmetricTensors R M d`.
* `DividedPowerAlgebra.symmetricTensorMap_bijective`: for a free module it is bijective, and
  `DividedPowerAlgebra.symmetricTensorEquiv R M d` is the resulting linear equivalence.

## Implementation notes

For a basis `b` of `M`, words `w : Fin d → κ` index the product basis of `⨂[R]^d M`, and two words
have the same letter counts exactly when they differ by a permutation of the positions
(`TauCeti.Sym.ofFn_eq_ofFn_iff`). Choosing one word in each class, the coordinates of a symmetric
tensor at the chosen words give a linear map back to `Γ^d_R(M)`, sending the chosen word with
letter counts `l` to `∏ⱼ dp R lⱼ (b j)`. It is a left inverse of `toTensorPower`: by Roby
representability this is an identity of polynomial laws, which is checked on
`∑ⱼ sⱼ ⊗ b j` after every scalar extension by expanding the divided powers and the tensor power.
It is a right inverse on symmetric tensors, since their coordinates are constant on each class.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963), IV §5,
  Théorème IV.2 and Proposition IV.5][Roby-1963]
* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.1](https://arxiv.org/abs/0809.0415)
* The ambient `DividedPowerAlgebra` and the `PolynomialLaw`s are the Mathlib formalizations by
  Antoine Chambert-Loir and María Inés de Frutos-Fernández.
-/

public section

noncomputable section

universe u

open TensorProduct PiTensorProduct Module TauCeti.Sym
open scoped Finset

namespace DividedPowerAlgebra

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

variable (R M) in
/-- The tensor power law `m ↦ m ⊗ ⋯ ⊗ m`, as a homogeneous law of degree `d`. -/
private def tensorPowerLaw (d : ℕ) : PolynomialLaw.homogeneousSubmodule R M (⨂[R]^d M) d :=
  ⟨PolynomialLaw.tensorPower R M d,
    PolynomialLaw.mem_homogeneousSubmodule.mpr (PolynomialLaw.isHomogeneousOfDegree_tensorPower d)⟩

variable (R M) in
/-- Roby's linear map `Γ^d_R(M) → ⨂[R]^d M`, sending `dp R d m` to `m ⊗ ⋯ ⊗ m`
(`toTensorPower_dp`). It is the linear map representing the tensor power law
(`toPolynomialLaw_toTensorPower_comp_gamma`), and its values are symmetric tensors
(`toTensorPower_mem_symmetricTensors`). -/
def toTensorPower (d : ℕ) : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] ⨂[R]^d M :=
  (homogeneousLawEquiv R M _ d).symm (tensorPowerLaw R M d)

/-- `toTensorPower` represents the tensor power law: composed with the universal law `γ_d`, it
gives `m ↦ m ⊗ ⋯ ⊗ m`. -/
theorem toPolynomialLaw_toTensorPower_comp_gamma (d : ℕ) :
    (toTensorPower R M d).toPolynomialLaw.comp (gamma R M d) = PolynomialLaw.tensorPower R M d := by
  rw [← coe_homogeneousLawMap_apply, ← homogeneousLawEquiv_apply, toTensorPower,
    LinearEquiv.apply_symm_apply, tensorPowerLaw]

/-- `toTensorPower` sends `dp R d m` to `m ⊗ ⋯ ⊗ m`. -/
@[simp]
theorem toTensorPower_dp (d : ℕ) (m : M) :
    toTensorPower R M d ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ = tprod R fun _ ↦ m := by
  rw [toTensorPower, homogeneousLawEquiv_symm_apply_dp]
  exact PolynomialLaw.ground_tensorPower d m

open MvPolynomial in
/-- The product formula for `toTensorPower`: for exponents `l` supported in a finite set `F` of
total degree `d`, the image of `∏_{j ∈ F} dp R lⱼ mⱼ` is the sum of `m_{w 0} ⊗ ⋯ ⊗ m_{w (d - 1)}`
over all words `w : Fin d → ι` in which each letter `j` occurs exactly `lⱼ` times. -/
theorem toTensorPower_prod_dp (d : ℕ) {ι : Type*} [DecidableEq ι] (F : Finset ι) (m : ι → M)
    (l : ι →₀ ℕ) (hF : l.support ⊆ F) (hl : ∑ j ∈ F, l j = d) :
    toTensorPower R M d
        ⟨∏ j ∈ F, dp R (l j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_finset_eq F m l hl⟩ =
      ∑ w ∈ Fintype.piFinset (fun _ : Fin d ↦ F) with ∑ t, Finsupp.single (w t) 1 = l,
        tprod R fun t ↦ m (w t) := by
  classical
  -- pass to the finite index type `F`, where representability computes the value as the
  -- coefficient of `∏ⱼ Xⱼ ^ lⱼ` in `(∑_{j ∈ F} Xⱼ ⊗ mⱼ) ^ ⊗d`
  set k : F →₀ ℕ := l.subtypeDomain (· ∈ F)
  have hk : ∑ j, k j = d := by
    simpa only [k, Finsupp.subtypeDomain_apply] using (Finset.sum_coe_sort F l).trans hl
  have hprod : (⟨∏ j ∈ F, dp R (l j) (m j),
      prod_dp_mem_homogeneousSubmodule_of_sum_finset_eq F m l hl⟩ :
        homogeneousSubmodule (R := R) (M := M) d) =
      ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq _ k hk⟩ :=
    Subtype.ext (Finset.prod_coe_sort F fun j ↦ dp R (l j) (m j)).symm
  have hX (w : Fin d → F) : ∏ t, (X (w t) : MvPolynomial F R) =
      monomial (∑ t, Finsupp.single (w t) 1) 1 := by
    -- `X n` is by definition the monomial `monomial (single n 1) 1`
    rw [monomial_sum_one]
    simp only [X]
  rw [hprod, toTensorPower, homogeneousLawEquiv_symm_apply_prod_dp d _ _ k hk,
    PolynomialLaw.coeff_apply, tensorPowerLaw, PolynomialLaw.tensorPower_toFun_sum_tmul]
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hX, lcoeff_apply,
    coeff_monomial, ite_smul, one_smul, zero_smul, Finset.sum_ite, Finset.sum_const_zero,
    add_zero]
  -- a word in `F` is a word in `ι` with letters in `F`, with the same letter counts
  have hcount (w : Fin d → F) :
      ∑ t, Finsupp.single (w t) 1 = k ↔ ∑ t, Finsupp.single (w t : ι) 1 = l := by
    refine ⟨fun h ↦ Finsupp.ext fun j ↦ ?_, fun h ↦ Finsupp.ext fun j ↦ ?_⟩
    · by_cases hj : j ∈ F
      · have h' := DFunLike.congr_fun h ⟨j, hj⟩
        simp only [sum_single_apply, k, Finsupp.subtypeDomain_apply, Subtype.ext_iff] at h'
        rw [sum_single_apply, h']
      · -- letters outside `F` occur neither in the word nor in `l`
        rw [Finsupp.notMem_support_iff.mp fun h' ↦ hj (hF h')]
        by_contra h'
        obtain ⟨t, rfl⟩ := sum_single_apply_ne_zero_iff.mp h'
        exact hj (w t).2
    · simp only [k, Finsupp.subtypeDomain_apply, ← h, sum_single_apply, Subtype.ext_iff]
  refine Finset.sum_bij (fun w _ t ↦ w t) (fun w hw ↦ ?_) (fun v _ w _ h ↦ ?_) (fun w hw ↦ ?_)
    fun _ _ ↦ rfl
  · rw [Finset.mem_filter] at hw ⊢
    exact ⟨Fintype.mem_piFinset.mpr fun t ↦ (w t).2, (hcount w).mp hw.2⟩
  · exact funext fun t ↦ Subtype.ext (congrFun h t)
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hw
    exact ⟨fun t ↦ ⟨w t, hw.1 t⟩, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun _ ↦
      Finset.mem_univ _, (hcount _).mpr hw.2⟩, rfl⟩

/-- The values of `toTensorPower` are symmetric tensors. -/
theorem toTensorPower_mem_symmetricTensors (d : ℕ)
    (x : homogeneousSubmodule (R := R) (M := M) d) :
    toTensorPower R M d x ∈ TensorPower.symmetricTensors R M d := by
  classical
  refine TensorPower.mem_symmetricTensors.mpr fun σ ↦ ?_
  -- by representability, it suffices that permuting the factors fixes the tensor power law
  suffices h : (reindex R (fun _ ↦ M) σ).toLinearMap ∘ₗ toTensorPower R M d = toTensorPower R M d
    from LinearMap.congr_fun h x
  apply homogeneousLawMap_injective (R := R) (M := M) d
  rw [Subtype.ext_iff, homogeneousLawMap_comp, coe_homogeneousLawMap_apply,
    toPolynomialLaw_toTensorPower_comp_gamma]
  ext S _ _ y
  simp only [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun_comp_apply,
    LinearMap.toPolynomialLaw_toFun]
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_sum_tmul_eq y
  rw [PolynomialLaw.tensorPower_toFun_sum_tmul, map_sum, Fintype.piFinset_univ]
  simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, reindex_tprod]
  -- reindex the words by `σ`
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl _)) _ _ fun w ↦ ?_
  simp only [Equiv.arrowCongr_apply, Function.comp_apply, Equiv.coe_refl, id_eq]
  rw [Equiv.prod_comp σ.symm fun t ↦ s (w t)]

variable (R M) in
/-- `toTensorPower` as a linear map to the symmetric tensors. For a free module it is a linear
equivalence (`symmetricTensorEquiv`). -/
def symmetricTensorMap (d : ℕ) :
    homogeneousSubmodule (R := R) (M := M) d →ₗ[R] TensorPower.symmetricTensors R M d :=
  (toTensorPower R M d).codRestrict _ (toTensorPower_mem_symmetricTensors d)

@[simp]
theorem coe_symmetricTensorMap_apply (d : ℕ) (x : homogeneousSubmodule (R := R) (M := M) d) :
    (symmetricTensorMap R M d x : ⨂[R]^d M) = toTensorPower R M d x :=
  (rfl)

/-! ### Free modules -/

section Free

variable {d : ℕ} {κ : Type*}

/-- The chosen word with the same letters as `w`. -/
private def canonWord (w : Fin d → κ) : Fin d → κ :=
  Function.surjInv TauCeti.Sym.ofFn_surjective (TauCeti.Sym.ofFn w)

private theorem ofFn_canonWord (w : Fin d → κ) :
    TauCeti.Sym.ofFn (canonWord w) = TauCeti.Sym.ofFn w :=
  Function.surjInv_eq _ _

private theorem canonWord_eq_canonWord_iff {v w : Fin d → κ} :
    canonWord v = canonWord w ↔ TauCeti.Sym.ofFn v = TauCeti.Sym.ofFn w :=
  ⟨fun h ↦ by rw [← ofFn_canonWord v, h, ofFn_canonWord],
    fun h ↦ congrArg (Function.surjInv TauCeti.Sym.ofFn_surjective) h⟩

private theorem canonWord_canonWord (w : Fin d → κ) : canonWord (canonWord w) = canonWord w :=
  canonWord_eq_canonWord_iff.mpr (ofFn_canonWord w)

/-- A word is the chosen word of `w` exactly when it is a chosen word with the same letters. -/
private theorem eq_canonWord_iff {v w : Fin d → κ} :
    v = canonWord w ↔ canonWord v = v ∧ TauCeti.Sym.ofFn w = TauCeti.Sym.ofFn v := by
  refine ⟨fun h ↦ ?_, fun ⟨hv, h⟩ ↦ ?_⟩
  · subst h
    exact ⟨canonWord_canonWord w, (ofFn_canonWord w).symm⟩
  · rw [← hv, canonWord_eq_canonWord_iff, h]

variable (b : Basis κ R M)

variable [DecidableEq κ]

/-- The product `∏ⱼ dp R lⱼ (b j)` of divided powers of basis vectors, where `lⱼ` is the number
of occurrences of the letter `j` in the word `w`. -/
private def basisProd (w : Fin d → κ) : homogeneousSubmodule (R := R) (M := M) d :=
  ⟨∏ j ∈ Finset.univ.image w, dp R ((∑ t, Finsupp.single (w t) 1 : κ →₀ ℕ) j) (b j),
    prod_dp_mem_homogeneousSubmodule_of_sum_finset_eq _ _ _
      (sum_sum_single_apply fun t ↦ Finset.mem_image_of_mem w (Finset.mem_univ t))⟩

/-- The value of `toTensorPower` on `basisProd b w` is the sum of the product basis vectors over
all words with the same letters as `w`. -/
private theorem toTensorPower_basisProd (w : Fin d → κ) :
    toTensorPower R M d (basisProd b w) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin d ↦ Finset.univ.image w) with
        TauCeti.Sym.ofFn v = TauCeti.Sym.ofFn w, Basis.piTensorProduct (fun _ ↦ b) v := by
  have hF : (∑ t, Finsupp.single (w t) 1 : κ →₀ ℕ).support ⊆ Finset.univ.image w := fun j hj ↦ by
    obtain ⟨t, rfl⟩ := sum_single_apply_ne_zero_iff.mp (Finsupp.mem_support_iff.mp hj)
    exact Finset.mem_image_of_mem w (Finset.mem_univ t)
  rw [basisProd, toTensorPower_prod_dp d _ b _ hF
    (sum_sum_single_apply fun t ↦ Finset.mem_image_of_mem w (Finset.mem_univ t))]
  simp only [sum_single_eq_sum_single_iff, Basis.piTensorProduct_apply]

/-- The map back from tensors to divided powers: the product basis vector of a chosen word goes to
`basisProd b w`, and every other product basis vector goes to `0`. -/
private def fromTensorPower : ⨂[R]^d M →ₗ[R] homogeneousSubmodule (R := R) (M := M) d :=
  (Basis.piTensorProduct fun _ : Fin d ↦ b).constr R fun w ↦
    if canonWord w = w then basisProd b w else 0

private theorem fromTensorPower_tprod (w : Fin d → κ) :
    fromTensorPower b (tprod R fun t ↦ b (w t)) = if canonWord w = w then basisProd b w else 0 := by
  rw [fromTensorPower, ← Basis.piTensorProduct_apply, Basis.constr_basis]

/-- `fromTensorPower b` is a left inverse of `toTensorPower`. -/
private theorem fromTensorPower_comp_toTensorPower :
    fromTensorPower b ∘ₗ toTensorPower R M d = LinearMap.id := by
  -- by representability, compare the laws `fromTensorPower b ∘ (m ↦ m ⊗ ⋯ ⊗ m)` and `γ_d`
  apply homogeneousLawMap_injective (R := R) (M := M) d
  rw [Subtype.ext_iff, homogeneousLawMap_comp, coe_homogeneousLawMap_apply,
    toPolynomialLaw_toTensorPower_comp_gamma, coe_homogeneousLawMap_apply,
    LinearMap.toPolynomialLaw_id, PolynomialLaw.id_comp]
  ext S _ _ x
  simp only [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun_comp_apply,
    LinearMap.toPolynomialLaw_toFun]
  obtain ⟨s, rfl⟩ := TensorProduct.eq_repr_basis_right b x
  rw [Finsupp.sum, PolynomialLaw.tensorPower_toFun_sum_tmul, gamma_toFun_sum_tmul, map_sum]
  simp only [LinearMap.baseChange_tmul, fromTensorPower_tprod, TensorProduct.tmul_ite]
  rw [← Finset.sum_filter]
  -- a chosen word with letters in `s.support` corresponds to its letter counts, an exponent vector
  -- supported in `s.support` of total degree `d`
  refine Finset.sum_bij (fun w _ ↦ ∑ t, Finsupp.single (w t) 1) (fun w hw ↦ ?_)
    (fun v hv w hw h ↦ ?_) (fun l hl ↦ ?_) (fun w hw ↦ ?_)
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hw
    refine Finset.mem_finsuppAntidiag.mpr ⟨sum_sum_single_apply hw.1, fun j hj ↦ ?_⟩
    obtain ⟨t, rfl⟩ := sum_single_apply_ne_zero_iff.mp (Finsupp.mem_support_iff.mp hj)
    exact hw.1 t
  · rw [← (Finset.mem_filter.mp hv).2, ← (Finset.mem_filter.mp hw).2,
      canonWord_eq_canonWord_iff, ← sum_single_eq_sum_single_iff, h]
  · rw [Finset.mem_finsuppAntidiag] at hl
    obtain ⟨w₀, hw₀⟩ := exists_sum_single_eq l
      ((Finsupp.sum_of_support_subset l hl.2 _ fun _ _ ↦ rfl).trans hl.1)
    have hcount : ∑ t, Finsupp.single (canonWord w₀ t) 1 = l := by
      rw [sum_single_eq_sum_single_iff.mpr (ofFn_canonWord w₀), hw₀]
    refine ⟨canonWord w₀, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun t ↦ hl.2 ?_,
      canonWord_canonWord w₀⟩, hcount⟩
    rw [Finsupp.mem_support_iff, ← hcount]
    exact sum_single_apply_ne_zero_iff.mpr ⟨t, rfl⟩
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hw
    have hmaps : ∀ t ∈ Finset.univ, w t ∈ s.support := fun t _ ↦ hw.1 t
    congr 1
    · rw [← Finset.prod_fiberwise_of_maps_to' hmaps]
      simp [sum_single_apply]
    · apply Subtype.ext
      rw [DirectSum.decompose_of_mem_same _ (prod_dp_mem_homogeneousSubmodule_of_sum_finset_eq _ b _
        (sum_sum_single_apply hw.1)), basisProd]
      -- letters of `s.support` outside the word have exponent zero
      refine Finset.prod_subset_one_on_sdiff (Finset.image_subset_iff.mpr hmaps)
        (fun j hj ↦ ?_) fun _ _ ↦ rfl
      rw [Finset.mem_sdiff, Finset.mem_image] at hj
      rw [not_ne_iff.mp (mt sum_single_apply_ne_zero_iff.mp fun ⟨t, ht⟩ ↦
        hj.2 ⟨t, Finset.mem_univ t, ht⟩), dp_zero]

/-- On product basis vectors, `toTensorPower ∘ fromTensorPower b` followed by the coordinate at a
word `w` is the coordinate at the chosen word of `w`. -/
private theorem lapply_repr_toTensorPower_fromTensorPower (w : Fin d → κ) :
    Finsupp.lapply w ∘ₗ (Basis.piTensorProduct fun _ : Fin d ↦ b).repr.toLinearMap ∘ₗ
        toTensorPower R M d ∘ₗ fromTensorPower b =
      Finsupp.lapply (canonWord w) ∘ₗ
        (Basis.piTensorProduct fun _ : Fin d ↦ b).repr.toLinearMap := by
  refine (Basis.piTensorProduct fun _ : Fin d ↦ b).ext fun v ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply, Basis.repr_self,
    Finsupp.single_apply, eq_canonWord_iff]
  rw [Basis.piTensorProduct_apply, fromTensorPower_tprod]
  by_cases hv : canonWord v = v
  · -- the words with the same letters as `v` all have their letters among those of `v`
    have key : (∀ t, w t ∈ Finset.univ.image v) ∧ TauCeti.Sym.ofFn w = TauCeti.Sym.ofFn v ↔
        canonWord v = v ∧ TauCeti.Sym.ofFn w = TauCeti.Sym.ofFn v := by
      refine ⟨fun h ↦ ⟨hv, h.2⟩, fun h ↦ ⟨fun t ↦ ?_, h.2⟩⟩
      obtain ⟨u, hu⟩ := TauCeti.Sym.mem_ofFn.mp (h.2 ▸ TauCeti.Sym.mem_ofFn.mpr ⟨t, rfl⟩)
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, hu⟩
    rw [ite_eq_left_iff.mpr fun h ↦ (h hv).elim, toTensorPower_basisProd, map_sum,
      Finsupp.finsetSum_apply]
    simp only [Basis.repr_self, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter,
      Fintype.mem_piFinset, key]
  · rw [ite_eq_right_iff.mpr fun h ↦ (hv h).elim, ite_eq_right_iff.mpr fun h ↦ (hv h.1).elim,
      map_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply]

omit [DecidableEq κ] in
include b in
/-- For a basis `b` of `M`, `toTensorPower` is injective and its range is the symmetric
tensors. -/
private theorem symmetricTensorMap_bijective_of_basis :
    Function.Bijective (symmetricTensorMap R M d) := by
  classical
  refine ⟨fun x y h ↦ ?_, fun ⟨t, ht⟩ ↦ ⟨fromTensorPower b t, Subtype.ext ?_⟩⟩
  · have h' := congrArg
      (fun z : TensorPower.symmetricTensors R M d ↦ fromTensorPower b (z : ⨂[R]^d M)) h
    simpa only [coe_symmetricTensorMap_apply, ← LinearMap.comp_apply,
      fromTensorPower_comp_toTensorPower, LinearMap.id_apply] using h'
  · rw [coe_symmetricTensorMap_apply]
    refine (Basis.piTensorProduct fun _ : Fin d ↦ b).repr.injective (Finsupp.ext fun w ↦ ?_)
    have h := LinearMap.congr_fun (lapply_repr_toTensorPower_fromTensorPower b w) t
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply] at h
    rw [h]
    -- the coordinates of a symmetric tensor are constant on words with the same letters
    obtain ⟨σ, hσ⟩ := TauCeti.Sym.ofFn_eq_ofFn_iff.mp (ofFn_canonWord w).symm
    rw [← hσ, (TensorPower.mem_symmetricTensors_iff_repr b).mp ht]

end Free

/-- For a free module `M`, Roby's map from `Γ^d_R(M)` to the symmetric tensors is bijective. -/
theorem symmetricTensorMap_bijective [Module.Free R M] (d : ℕ) :
    Function.Bijective (symmetricTensorMap R M d) := by
  classical
  exact symmetricTensorMap_bijective_of_basis (Module.Free.chooseBasis R M)

variable (R M) in
/-- For a free module `M`, Roby's linear equivalence between the homogeneous divided powers
`Γ^d_R(M)` and the symmetric tensors of degree `d`, sending `dp R d m` to `m ⊗ ⋯ ⊗ m`. -/
def symmetricTensorEquiv [Module.Free R M] (d : ℕ) :
    homogeneousSubmodule (R := R) (M := M) d ≃ₗ[R] TensorPower.symmetricTensors R M d :=
  LinearEquiv.ofBijective (symmetricTensorMap R M d) (symmetricTensorMap_bijective d)

@[simp]
theorem symmetricTensorEquiv_apply [Module.Free R M] (d : ℕ)
    (x : homogeneousSubmodule (R := R) (M := M) d) :
    symmetricTensorEquiv R M d x = symmetricTensorMap R M d x :=
  (rfl)

end DividedPowerAlgebra
