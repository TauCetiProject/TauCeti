/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Exponential
public import TauCeti.Algebra.AlgebraicGroup.Representation.Kernel
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic

/-!
# Exponential points on comodules

Let `H` be a commutative bialgebra over `R` and `M` a right `H`-comodule. A tangent vector `d` at
the identity acts on `M` by `TauCeti.Comodule.differential d` and extends on `H` to the
left-invariant derivation `D = TauCeti.Bialgebra.leftInvariantDerivation d`. Coassociativity of the
coaction intertwines these two actions, `coact (d • m) = (id ⊗ D) (coact m)`, and iterating gives
`coact (dⁿ • m) = (id ⊗ Dⁿ) (coact m)`. Consequently, whenever `D` is locally nilpotent on `H`,
`differential d` is locally nilpotent on `M`, and nilpotent when `M` is finitely generated.

When `H` is a commutative Hopf algebra that is also a `ℚ`-algebra and `M` is a `ℚ`-module, the
exponential point `exp d = ε ∘ exp D` acts on `m ∈ M` by the truncated exponential series of
`differential d`, and when `differential d` is nilpotent on `M` the linear action of `exp d` is the
operator exponential `IsNilpotent.exp (differential d)`. Conversely, in any faithful representation
with a finite basis, nilpotence of `differential d` makes the tangent matrix in `GLₙ` nilpotent and
so forces `D` to be locally nilpotent on `H`.

## Main declarations

* `TauCeti.Comodule.coact_differential` and `TauCeti.Comodule.coact_pow_differential`: the coaction
  intertwines `Comodule.differential d` and its powers with `Bialgebra.leftInvariantDerivation d`.
* `TauCeti.Comodule.pow_differential_apply`: `(differential d ^ n) m` contracts the coaction against
  `ε ∘ Dⁿ`.
* `TauCeti.Comodule.exists_pow_differential_apply_eq_zero` and
  `TauCeti.Comodule.isNilpotent_differential_of_finite`: local nilpotence of `D` implies local
  nilpotence of `differential d`, and nilpotence on finitely generated comodules.
* `TauCeti.Comodule.basePointsRepresentation_expPoint_apply_eq_sum` and
  `TauCeti.Comodule.basePointsRepresentation_expPoint`: `Bialgebra.expPoint d hd` acts on `M` by the
  exponential series of `differential d`.
* `TauCeti.HopfIdeal.toConv_expPoint_mem_quotientPointsSubgroup`: the exponential point of a
  subgroup tangent vector lies in the closed subgroup.
* `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential`: a
  surjective coordinate representation with nilpotent differentiated action makes `D` locally
  nilpotent.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 11 and 12.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

section Bialgebra

variable {R H M : Type*} [CommRing R] [CommRing H] [Bialgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

/-- **Coassociativity intertwines the differentiated action with the invariant derivation**:
`coact (d • m) = (id ⊗ D) (coact m)`. -/
theorem coact_differential (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (m : M) :
    coact (R := R) (C := H) (differential (R := R) (H := H) (M := M) d m) =
      (Bialgebra.leftInvariantDerivation d).toLinearMap.lTensor M (coact (R := R) (C := H) m) := by
  set φ := (Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap
  have hD : (Bialgebra.leftInvariantDerivation d).toLinearMap =
      LinearMap.tensorComponent φ ∘ₗ Coalgebra.comul :=
    LinearMap.ext (Bialgebra.leftInvariantDerivation_apply d)
  rw [differential_apply, hD, LinearMap.lTensor_comp, LinearMap.comp_apply,
    ← LinearMap.tensorComponent_assoc_symm, coassoc_symm_apply, LinearMap.tensorComponent_rTensor]

/-- **Iterated differentiated actions commute with the coaction**:
`coact (dⁿ • m) = (id ⊗ Dⁿ) (coact m)`. -/
theorem coact_pow_differential (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (n : ℕ)
    (m : M) :
    coact (R := R) (C := H) (((differential (R := R) (H := H) (M := M) d) ^ n) m) =
      ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ n).lTensor M
        (coact (R := R) (C := H) m) := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, coact_differential, ih, pow_succ',
      LinearMap.lTensor_mul, mul_apply_eq_comp]

/-- **Powers of the differentiated action contract the coaction against `ε ∘ Dⁿ`.** -/
theorem pow_differential_apply (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (n : ℕ)
    (m : M) :
    ((differential (R := R) (H := H) (M := M) d) ^ n) m =
      LinearMap.tensorComponent
        (Coalgebra.counit (R := R) ∘ₗ (Bialgebra.leftInvariantDerivation d).toLinearMap ^ n)
        (coact (R := R) (C := H) m) := by
  have hcounit := congrArg (TensorProduct.rid R M)
    (lTensor_counit_coact (R := R) (C := H) (((differential (R := R) (H := H) d) ^ n) m))
  rw [TensorProduct.rid_tmul, one_smul] at hcounit
  rw [← hcounit, coact_pow_differential, ← LinearMap.lTensor_comp_apply,
    LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe]

omit [Comodule R H M] in
/-- Any tensor in `M ⊗ H` is annihilated in its `H`-factor by a uniform iterate of a locally
nilpotent derivation. -/
private theorem exists_lTensor_pow_leftInvariantDerivation_eq_zero
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : M ⊗[R] H) :
    ∃ N, ∀ k, N ≤ k → ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ k).lTensor M t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul m h =>
    obtain ⟨N, hN⟩ := hd h
    refine ⟨N, fun k hk ↦ ?_⟩
    have hk0 : ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ k) h = 0 :=
      Module.End.pow_map_zero_of_le hk (by simpa [pow_apply_eq_iterate] using hN)
    rw [LinearMap.lTensor_tmul, hk0, TensorProduct.tmul_zero]
  | add x y hx hy =>
    obtain ⟨Nx, hNx⟩ := hx
    obtain ⟨Ny, hNy⟩ := hy
    exact ⟨max Nx Ny, fun k hk ↦ by
      rw [map_add, hNx k (le_of_max_le_left hk), hNy k (le_of_max_le_right hk), add_zero]⟩

/-- **Local nilpotence passes from the invariant derivation to every comodule.** -/
theorem exists_pow_differential_apply_eq_zero
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (m : M) :
    ∃ n, ((differential (R := R) (H := H) (M := M) d) ^ n) m = 0 := by
  obtain ⟨N, hN⟩ :=
    exists_lTensor_pow_leftInvariantDerivation_eq_zero hd (coact (R := R) (C := H) m)
  refine ⟨N, ?_⟩
  rw [pow_differential_apply, LinearMap.tensorComponent_def, LinearMap.comp_apply,
    LinearMap.lTensor_comp_apply, hN N le_rfl, map_zero, map_zero]

/-- **On a finitely generated comodule, a locally nilpotent invariant derivation induces a
nilpotent differentiated operator.** -/
theorem isNilpotent_differential_of_finite [Module.Finite R M]
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    IsNilpotent (differential (R := R) (H := H) (M := M) d) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose n hn using exists_pow_differential_apply_eq_zero (M := M) hd
  refine ⟨s.sup n, LinearMap.ext fun m ↦ ?_⟩
  have hm : m ∈ Submodule.span R (s : Set M) := hs.symm ▸ Submodule.mem_top
  rw [LinearMap.zero_apply]
  refine Submodule.span_induction (fun x hx ↦ ?_) (map_zero _)
    (fun _ _ _ _ hx hy ↦ by rw [map_add, hx, hy, add_zero])
    (fun r _ _ hx ↦ by rw [map_smul, hx, smul_zero]) hm
  exact Module.End.pow_map_zero_of_le (Finset.le_sup hx) (hn x)

end Bialgebra

section Exponential

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H] [Algebra ℚ H]
variable [AddCommGroup M] [Module R M] [Module ℚ M] [Comodule R H M]

omit [Comodule R H M] in
/-- Contracting a tensor against `Bialgebra.expPoint d hd` expands into the finite Taylor series
once the truncation bound annihilates the `H`-factor. -/
private theorem tensorComponent_expPoint_eq_sum
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    ∀ t : M ⊗[R] H, ∃ N, ∀ K, N ≤ K →
      LinearMap.tensorComponent (Bialgebra.expPoint d hd).toLinearMap t =
        ∑ i ∈ Finset.range K, (i.factorial : ℚ)⁻¹ •
          LinearMap.tensorComponent
            (Coalgebra.counit (R := R) ∘ₗ
              (Bialgebra.leftInvariantDerivation d).toLinearMap ^ i) t := by
  let : Algebra ℚ R :=
    ((Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul m h =>
    obtain ⟨N, hN⟩ := hd h
    refine ⟨N, fun K hK ↦ ?_⟩
    have hK0 : (Bialgebra.leftInvariantDerivation d)^[K] h = 0 := by
      simpa [pow_apply_eq_iterate] using Module.End.pow_map_zero_of_le
        (f := (Bialgebra.leftInvariantDerivation d).toLinearMap) hK
        (by simpa [pow_apply_eq_iterate] using hN)
    rw [LinearMap.tensorComponent_tmul, AlgHom.toLinearMap_apply, Bialgebra.expPoint_apply,
      (Bialgebra.leftInvariantDerivation d).taylorExp_apply_eq_sum hd hK0, map_sum,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    -- Both `R`-smul and `ℚ`-smul commute through the additive map `r ↦ r • m`.
    have hsmul := map_rat_smul (LinearMap.toSpanSingleton R M m).toAddMonoidHom
      (i.factorial : ℚ)⁻¹ (Coalgebra.counit (R := R)
        ((Bialgebra.leftInvariantDerivation d)^[i] h))
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply] at hsmul
    rw [LinearMap.tensorComponent_tmul, LinearMap.comp_apply, FunLike.coe_pow_eq_iterate,
      Derivation.coeFn_coe, map_rat_smul, hsmul]
  | add x y hx hy =>
    obtain ⟨Nx, hNx⟩ := hx
    obtain ⟨Ny, hNy⟩ := hy
    refine ⟨max Nx Ny, fun K hK ↦ ?_⟩
    rw [map_add, hNx K (le_of_max_le_left hK), hNy K (le_of_max_le_right hK),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_add, smul_add]

/-- **The exponential point acts on a comodule vector by the truncated exponential series of its
differentiated operator.** -/
theorem basePointsRepresentation_expPoint_apply_eq_sum
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    {m : M} {k : ℕ} (hm : ((differential (R := R) (H := H) (M := M) d) ^ k) m = 0) :
    basePointsRepresentation (H := H) M (toConv (Bialgebra.expPoint d hd)) m =
      ∑ i ∈ Finset.range k,
        (i.factorial : ℚ)⁻¹ • ((differential (R := R) (H := H) (M := M) d) ^ i) m := by
  have hbase : basePointsRepresentation (H := H) M (toConv (Bialgebra.expPoint d hd)) m =
      LinearMap.tensorComponent (Bialgebra.expPoint d hd).toLinearMap
        (coact (R := R) (C := H) m) := by
    rw [basePointsRepresentation_apply, ofConv_toConv, endOfPoint_tmul, one_smul]
    induction coact (R := R) (C := H) m using TensorProduct.inductionOn with
    | tmul n h => simp
    | add x y hx hy => simp [hx, hy]
  obtain ⟨N, hN⟩ := tensorComponent_expPoint_eq_sum hd (coact (R := R) (C := H) m)
  rw [hbase, hN (max N k) (le_max_left N k)]
  simp_rw [← pow_differential_apply]
  rw [← Finset.sum_range_add_sum_Ico _ (le_max_right N k)]
  suffices ∑ i ∈ Finset.Ico k (max N k),
      (i.factorial : ℚ)⁻¹ • ((differential (R := R) (H := H) (M := M) d) ^ i) m = 0 by
    rw [this, add_zero]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [Module.End.pow_map_zero_of_le (Finset.mem_Ico.mp hi).1 hm, smul_zero]

/-- **On a comodule where the differentiated operator is nilpotent, the exponential point acts by
the operator exponential `IsNilpotent.exp`.** -/
theorem basePointsRepresentation_expPoint
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hM : IsNilpotent (differential (R := R) (H := H) (M := M) d)) :
    basePointsRepresentation (H := H) M (toConv (Bialgebra.expPoint d hd)) =
      IsNilpotent.exp (differential (R := R) (H := H) (M := M) d) := by
  obtain ⟨k, hk⟩ := hM
  ext m
  rw [basePointsRepresentation_expPoint_apply_eq_sum hd
      (by rw [hk, LinearMap.zero_apply]),
    IsNilpotent.exp_eq_sum hk, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ rfl

end Exponential

end TauCeti.Comodule

namespace TauCeti.HopfIdeal

variable {R H : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H] [Algebra ℚ H]

/-- **The exponential point of a subgroup tangent vector lies in the closed subgroup.** -/
theorem toConv_expPoint_mem_quotientPointsSubgroup (I : HopfIdeal R H)
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)} (hd : d ∈ I.lieSubalgebra (B := R))
    (hD : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    toConv (Bialgebra.expPoint d hD) ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
        (CommAlgCat.of R R) := by
  rw [← Bialgebra.expPointAt_one]
  exact I.expPointAt_mem_quotientPointsSubgroup hd hD (1 : R)

end TauCeti.HopfIdeal

namespace Derivation

open TauCeti

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M] {n : ℕ}

/-- **Nilpotence in a faithful representation forces local nilpotence of the invariant derivation.**
If the coordinate map of a finite basis `b` is surjective and `Comodule.differential d` is
nilpotent on `M`, then `Bialgebra.leftInvariantDerivation d` is locally nilpotent on `H`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M)
    (hf : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (hd : IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  refine BialgHom.exists_iterate_leftInvariantDerivation_eq_zero_of_surjective
    (Comodule.coordinateBialgHom (H := H) b) hf d
    (GeneralLinear.exists_iterate_leftInvariantDerivation_eq_zero n _ ?_)
  rw [d.tangentMatrix_comp_coordinateBialgHom b]
  exact hd.map (LinearMap.toMatrixAlgEquiv b).toRingHom

end Derivation
