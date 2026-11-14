/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.Algebra.Coalgebra.Basic

/-!
# The fundamental theorem of Hopf modules

A left Hopf module over a bialgebra `H` is a left `H`-module `M` together with a left
`H`-comodule structure `δ : M → H ⊗ M`, `m ↦ ∑ m₋₁ ⊗ m₀`, which is `H`-linear for the
coproduct action on `H ⊗ M`:

`δ (h • m) = ∑ h₁ m₋₁ ⊗ h₂ • m₀`.

The coinvariants of `M` are the vectors `m` with `δ m = 1 ⊗ m`.

For a Hopf algebra, the fundamental theorem of Hopf modules says that the action
`H ⊗ M^{co H} → M`, `h ⊗ n ↦ h • n`, is an `H`-linear equivalence, so every Hopf module is
recovered from its coinvariants. The inverse is `m ↦ ∑ m₋₁ ⊗ P(m₀)`, where
`P m = ∑ S(m₋₁) • m₀` is a projection onto the coinvariants. Neither finiteness nor
bijectivity of the antipode is needed.

Applied to the dual of a finite-dimensional Hopf algebra, this gives the Larson–Sweedler theorem
that its cointegrals form a line.

## Main declarations

* `TauCeti.IsHopfModule`: a left comodule structure making a left `H`-module a Hopf module.
* `TauCeti.HopfModule.coinvariants`: the coinvariants `{m | δ m = 1 ⊗ m}`.
* `TauCeti.HopfModule.coinvariantProj`: the map `m ↦ ∑ S(m₋₁) • m₀`.
* `TauCeti.IsHopfModule.coinvariantProj_mem`: it lands in the coinvariants.
* `TauCeti.IsHopfModule.tensorCoinvariantsEquiv`: the fundamental theorem
  `H ⊗ M^{co H} ≃ M`.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Theorem 1.9.4.
* M. E. Sweedler, *Hopf Algebras*, Theorem 4.1.1.
-/

public section

open scoped TensorProduct
open Coalgebra

namespace TauCeti

variable {k H M : Type*} [CommSemiring k] [Semiring H] [AddCommMonoid M] [Module k M]

namespace HopfModule

section Coinvariants

variable [Module k H]

/-- The coinvariants `{m | δ m = 1 ⊗ m}` of a left coaction. -/
def coinvariants (δ : M →ₗ[k] H ⊗[k] M) : Submodule k M :=
  LinearMap.eqLocus δ (TensorProduct.mk k H M 1)

/-- Membership in the coinvariants: `δ m = 1 ⊗ m`. -/
@[simp]
theorem mem_coinvariants {δ : M →ₗ[k] H ⊗[k] M} {m : M} :
    m ∈ coinvariants δ ↔ δ m = 1 ⊗ₜ m :=
  LinearMap.mem_eqLocus

end Coinvariants

end HopfModule

variable [Module H M]

section Bialgebra

variable [Bialgebra k H] [IsScalarTower k H M]

/-- The left coaction `δ : M → H ⊗ M` makes the left `H`-module `M` a left Hopf module: it is
coassociative and counital, and `H`-linear for the coproduct action on `H ⊗ M`, that is
`δ (h • m) = ∑ h₁ m₋₁ ⊗ h₂ • m₀`. -/
structure IsHopfModule (δ : M →ₗ[k] H ⊗[k] M) : Prop where
  /-- Coassociativity of the left coaction. -/
  coassoc : TensorProduct.assoc k H H M ∘ₗ comul.rTensor M ∘ₗ δ = δ.lTensor H ∘ₗ δ
  /-- The counit law of the left coaction. -/
  lid_rTensor_counit : TensorProduct.lid k M ∘ₗ counit.rTensor M ∘ₗ δ = LinearMap.id
  /-- The coaction is `H`-linear for the coproduct action on `H ⊗ M`. -/
  map_smul (h : H) (m : M) : δ (h • m) = BialgebraModule.tensorAction k H H M h (δ m)

namespace IsHopfModule

variable {δ : M →ₗ[k] H ⊗[k] M}

/-- Coassociativity of a Hopf-module coaction, applied to a vector. -/
theorem coassoc_apply (hδ : IsHopfModule δ) (m : M) :
    TensorProduct.assoc k H H M (comul.rTensor M (δ m)) = δ.lTensor H (δ m) :=
  LinearMap.congr_fun hδ.coassoc m

/-- The counit law of a Hopf-module coaction, applied to a vector. -/
theorem lid_rTensor_counit_apply (hδ : IsHopfModule δ) (m : M) :
    TensorProduct.lid k M (counit.rTensor M (δ m)) = m :=
  LinearMap.congr_fun hδ.lid_rTensor_counit m

/-- The coaction of `h • n` for a coinvariant `n`, in any representation of `Δ h`:
`δ (h • n) = ∑ h₁ ⊗ h₂ • n`. -/
theorem map_smul_of_mem_coinvariants (hδ : IsHopfModule δ) {n : M}
    (hn : n ∈ HopfModule.coinvariants δ) {h : H} {ι : Type*} (r : Repr k h ι) :
    δ (h • n) = ∑ i ∈ r.index, r.left i ⊗ₜ (r.right i • n) := by
  rw [hδ.map_smul, HopfModule.mem_coinvariants.mp hn, BialgebraModule.tensorAction_apply,
    ← r.eq]
  simp [map_sum]

end IsHopfModule

end Bialgebra

section Hopf

variable [HopfAlgebra k H] [IsScalarTower k H M]

namespace HopfModule

/-- The map `m ↦ ∑ S(m₋₁) • m₀` of a left coaction. For a Hopf module it is a projection onto
the coinvariants. -/
noncomputable def coinvariantProj (δ : M →ₗ[k] H ⊗[k] M) : M →ₗ[k] M :=
  TensorProduct.lift ((Algebra.lsmul k k M).toLinearMap ∘ₗ HopfAlgebra.antipode k) ∘ₗ δ

/-- `coinvariantProj` in any finite presentation of the coaction. -/
theorem coinvariantProj_eq_sum {δ : M →ₗ[k] H ⊗[k] M} {m : M} {ι : Type*} (s : Finset ι)
    (a : ι → H) (n : ι → M) (hm : δ m = ∑ i ∈ s, a i ⊗ₜ n i) :
    coinvariantProj δ m = ∑ i ∈ s, HopfAlgebra.antipode k (a i) • n i := by
  simp [coinvariantProj, hm, map_sum]

end HopfModule

namespace IsHopfModule

open HopfModule

variable {δ : M →ₗ[k] H ⊗[k] M}

/-- On `h • n` with `n` coinvariant, the projection is `∑ S(h₁) h₂ • n = ε(h) • n`. -/
theorem coinvariantProj_smul (hδ : IsHopfModule δ) {n : M} (hn : n ∈ coinvariants δ) (h : H) :
    coinvariantProj δ (h • n) = counit (R := k) h • n := by
  rw [coinvariantProj_eq_sum _ _ _ (hδ.map_smul_of_mem_coinvariants hn (ℛ k h))]
  simp_rw [← mul_smul, ← Finset.sum_smul, HopfAlgebra.sum_antipode_mul_eq_smul, smul_assoc,
    one_smul]

/-- The projection fixes the coinvariants. -/
@[simp]
theorem coinvariantProj_eq_self (hδ : IsHopfModule δ) {n : M} (hn : n ∈ coinvariants δ) :
    coinvariantProj δ n = n := by
  simpa using hδ.coinvariantProj_smul hn 1

/-- Reconstruction from the coinvariant projection: `∑ m₋₁ • P(m₀) = m`. -/
private theorem lift_lTensor_coinvariantProj (hδ : IsHopfModule δ) (m : M) :
    TensorProduct.lift (Algebra.lsmul k k M).toLinearMap
      ((coinvariantProj δ).lTensor H (δ m)) = m := by
  have key : TensorProduct.lift (Algebra.lsmul k k M).toLinearMap ∘ₗ
      (TensorProduct.lift ((Algebra.lsmul k k M).toLinearMap ∘ₗ
        HopfAlgebra.antipode k)).lTensor H ∘ₗ (TensorProduct.assoc k H H M).toLinearMap ∘ₗ
      comul.rTensor M = TensorProduct.lid k M ∘ₗ counit.rTensor M := by
    apply TensorProduct.ext'
    intro a n
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      ← (ℛ k a).eq]
    simp_rw [TensorProduct.sum_tmul, map_sum]
    simp only [LinearEquiv.coe_coe, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
      TensorProduct.lift.tmul, AlgHom.toLinearMap_apply,
      Algebra.lsmul_coe, LinearMap.comp_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    simp_rw [← mul_smul, ← Finset.sum_smul, HopfAlgebra.sum_mul_antipode_eq_smul, smul_assoc,
      one_smul]
  have hP : (coinvariantProj δ).lTensor H = (TensorProduct.lift ((Algebra.lsmul k k M).toLinearMap
      ∘ₗ HopfAlgebra.antipode k)).lTensor H ∘ₗ δ.lTensor H := by
    rw [coinvariantProj, LinearMap.lTensor_comp]
  rw [hP, LinearMap.comp_apply, ← hδ.coassoc_apply]
  simpa using congr($key (δ m)).trans (hδ.lid_rTensor_counit_apply m)

/-- The `H`-part of the coinvariance of `P`: `∑ Δ(S a₁) • (a₂ ⊗ n) = 1 ⊗ S(a) • n`. -/
private theorem sum_tensorAction_antipode_tmul (a : H) (n : M) :
    ∑ i ∈ (ℛ k a).index, BialgebraModule.tensorAction k H H M
      (HopfAlgebra.antipode k ((ℛ k a).left i)) ((ℛ k a).right i ⊗ₜ n) =
      (1 : H) ⊗ₜ (HopfAlgebra.antipode k a • n) := by
  set r := ℛ k a
  -- `Γ (p ⊗ q ⊗ y) = S(q) y ⊗ S(p) • n` turns both sides into coassociativity of `Δ`.
  let Γ : H ⊗[k] (H ⊗[k] H) →ₗ[k] H ⊗[k] M :=
    TensorProduct.map (LinearMap.mul' k H ∘ₗ (HopfAlgebra.antipode k).rTensor H)
      ((Algebra.lsmul k k M).toLinearMap.flip n ∘ₗ HopfAlgebra.antipode k) ∘ₗ
      (TensorProduct.comm k H (H ⊗[k] H)).toLinearMap
  have hΓ (p q y : H) : Γ (p ⊗ₜ (q ⊗ₜ y)) =
      (HopfAlgebra.antipode k q * y) ⊗ₜ (HopfAlgebra.antipode k p • n) := by
    simp [Γ]
  have hΓc (p q : H) : Γ (p ⊗ₜ comul q) =
      algebraMap k H (counit q) ⊗ₜ (HopfAlgebra.antipode k p • n) := by
    simp [Γ, HopfAlgebra.mul_antipode_rTensor_comul_apply]
  have hA (x y : H) : BialgebraModule.tensorAction k H H M (HopfAlgebra.antipode k x) (y ⊗ₜ n) =
      ∑ j ∈ (ℛ k x).index, Γ ((ℛ k x).left j ⊗ₜ ((ℛ k x).right j ⊗ₜ y)) := by
    rw [BialgebraModule.tensorAction_apply, TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply,
      ← (ℛ k x).eq]
    simp [map_sum, hΓ]
  calc _ = ∑ i ∈ r.index, ∑ j ∈ (ℛ k (r.left i)).index,
        Γ ((ℛ k (r.left i)).left j ⊗ₜ ((ℛ k (r.left i)).right j ⊗ₜ r.right i)) := by
        simp only [hA]
    _ = ∑ i ∈ r.index, ∑ j ∈ (ℛ k (r.right i)).index,
        Γ (r.left i ⊗ₜ ((ℛ k (r.right i)).left j ⊗ₜ (ℛ k (r.right i)).right j)) := by
        simpa only [map_sum] using congrArg Γ (sum_tmul_tmul_eq r (fun i ↦ ℛ k (r.left i))
          (fun i ↦ ℛ k (r.right i)))
    _ = ∑ i ∈ r.index, algebraMap k H (counit (r.right i)) ⊗ₜ
        (HopfAlgebra.antipode k (r.left i) • n) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← map_sum, ← TensorProduct.tmul_sum, (ℛ k (r.right i)).eq, hΓc]
    _ = _ := by
        have hS : ∑ i ∈ r.index, counit (R := k) (r.right i) • HopfAlgebra.antipode k (r.left i) =
            HopfAlgebra.antipode k a := by
          conv_rhs => rw [← Coalgebra.sum_smul_counit r]
          simp [map_sum]
        simp_rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← smul_assoc,
          ← TensorProduct.tmul_sum, ← Finset.sum_smul, hS]

/-- The projection `m ↦ ∑ S(m₋₁) • m₀` lands in the coinvariants. -/
theorem coinvariantProj_mem (hδ : IsHopfModule δ) (m : M) :
    coinvariantProj δ m ∈ coinvariants δ := by
  set Φ : H ⊗[k] M →ₗ[k] M :=
    TensorProduct.lift ((Algebra.lsmul k k M).toLinearMap ∘ₗ HopfAlgebra.antipode k)
  let Ψ : H ⊗[k] (H ⊗[k] M) →ₗ[k] H ⊗[k] M :=
    TensorProduct.lift ((BialgebraModule.tensorAction k H H M).toLinearMap ∘ₗ
      HopfAlgebra.antipode k)
  -- `δ (S(a) • n) = Δ(S a) • δ n`, so `δ ∘ Φ` factors through `id ⊗ δ`.
  have h1 : δ ∘ₗ Φ = Ψ ∘ₗ δ.lTensor H := by
    apply TensorProduct.ext'
    intro a n
    simp [Φ, Ψ, hδ.map_smul]
  have h2 : Ψ ∘ₗ (TensorProduct.assoc k H H M).toLinearMap ∘ₗ comul.rTensor M =
      TensorProduct.mk k H M 1 ∘ₗ Φ := by
    apply TensorProduct.ext'
    intro a n
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul, ← (ℛ k a).eq]
    simpa [Φ, Ψ, TensorProduct.sum_tmul, map_sum] using sum_tensorAction_antipode_tmul a n
  rw [mem_coinvariants, coinvariantProj, LinearMap.comp_apply, ← LinearMap.comp_apply (f := δ),
    h1, LinearMap.comp_apply, ← hδ.coassoc_apply]
  exact congr($h2 (δ m))

/-- Reconstruction from the coinvariant projection: if `δ m = ∑ aᵢ ⊗ nᵢ`, then
`∑ aᵢ • P(nᵢ) = m`. -/
theorem sum_smul_coinvariantProj (hδ : IsHopfModule δ) {m : M} {ι : Type*} (s : Finset ι)
    (a : ι → H) (n : ι → M) (hm : δ m = ∑ i ∈ s, a i ⊗ₜ n i) :
    ∑ i ∈ s, a i • coinvariantProj δ (n i) = m := by
  simpa [hm, map_sum] using hδ.lift_lTensor_coinvariantProj m

/-- The coinvariant projection `m ↦ ∑ S(m₋₁) • m₀`, as a map onto the coinvariants. -/
noncomputable def toCoinvariants (hδ : IsHopfModule δ) : M →ₗ[k] coinvariants δ :=
  (coinvariantProj δ).codRestrict (coinvariants δ) hδ.coinvariantProj_mem

/-- The coinvariant projection, as an element of `M`. -/
@[simp]
theorem coe_toCoinvariants (hδ : IsHopfModule δ) (m : M) :
    (hδ.toCoinvariants m : M) = coinvariantProj δ m :=
  (rfl)

/-- **The fundamental theorem of Hopf modules**: the action `h ⊗ n ↦ h • n` identifies
`H ⊗ M^{co H}` with the Hopf module `M`. The inverse is `m ↦ ∑ m₋₁ ⊗ P(m₀)`. -/
noncomputable def tensorCoinvariantsEquiv (hδ : IsHopfModule δ) :
    H ⊗[k] coinvariants δ ≃ₗ[k] M :=
  LinearEquiv.ofLinearMap
    (TensorProduct.lift ((Algebra.lsmul k k M).toLinearMap.compl₂ (coinvariants δ).subtype))
    (hδ.toCoinvariants.lTensor H ∘ₗ δ)
    (by
      ext m
      have hcomp : TensorProduct.lift ((Algebra.lsmul k k M).toLinearMap.compl₂
          (coinvariants δ).subtype) ∘ₗ hδ.toCoinvariants.lTensor H =
          TensorProduct.lift (Algebra.lsmul k k M).toLinearMap ∘ₗ
            (coinvariantProj δ).lTensor H := by
        apply TensorProduct.ext'
        intro a n
        simp
      simpa using congr($hcomp (δ m)).trans (hδ.lift_lTensor_coinvariantProj m))
    (by
      apply TensorProduct.ext'
      intro a n
      have hP (i : H × H) : hδ.toCoinvariants ((ℛ k a).right i • (n : M)) =
          counit (R := k) ((ℛ k a).right i) • n :=
        Subtype.ext (by simpa using hδ.coinvariantProj_smul n.2 ((ℛ k a).right i))
      simp only [LinearMap.comp_apply, TensorProduct.lift.tmul, LinearMap.compl₂_apply,
        Submodule.subtype_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe,
        hδ.map_smul_of_mem_coinvariants n.2 (ℛ k a), map_sum, LinearMap.lTensor_tmul, hP,
        LinearMap.id_apply]
      simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, Coalgebra.sum_smul_counit])

/-- The fundamental-theorem equivalence is the action on pure tensors. -/
@[simp]
theorem tensorCoinvariantsEquiv_tmul (hδ : IsHopfModule δ) (h : H) (n : coinvariants δ) :
    hδ.tensorCoinvariantsEquiv (h ⊗ₜ n) = h • (n : M) := by
  simp [tensorCoinvariantsEquiv]

/-- The fundamental-theorem equivalence is `H`-linear, for `H` acting on the left factor of
`H ⊗ M^{co H}`. -/
theorem tensorCoinvariantsEquiv_smul (hδ : IsHopfModule δ) (h : H)
    (t : H ⊗[k] coinvariants δ) :
    hδ.tensorCoinvariantsEquiv (h • t) = h • hδ.tensorCoinvariantsEquiv t := by
  induction t with
  | add t u ht hu => simp only [smul_add, map_add, ht, hu]
  | tmul a n => simp [TensorProduct.smul_tmul', mul_smul]

/-- The inverse of the fundamental-theorem equivalence is `m ↦ ∑ m₋₁ ⊗ P(m₀)`. -/
@[simp]
theorem tensorCoinvariantsEquiv_symm_apply (hδ : IsHopfModule δ) (m : M) :
    hδ.tensorCoinvariantsEquiv.symm m = hδ.toCoinvariants.lTensor H (δ m) :=
  (rfl)

end IsHopfModule

end Hopf

end TauCeti
