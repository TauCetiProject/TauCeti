/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
import Mathlib.Algebra.Module.Rat
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Nilpotent

/-!
# Exponential points and one-parameter curves on comodules

Let `H` be a commutative bialgebra over `R` and `M` a right `H`-comodule. A tangent vector `d` at
the identity acts on `M` by `TauCeti.Comodule.differential d` and extends on `H` to the
left-invariant derivation `D = TauCeti.Bialgebra.leftInvariantDerivation d`. Coassociativity of the
coaction intertwines these two actions, `coact (d • m) = (id ⊗ D) (coact m)`, and iterating gives
`coact (dⁿ • m) = (id ⊗ Dⁿ) (coact m)`. Consequently, whenever `D` is locally nilpotent on `H`,
`differential d` is locally nilpotent on `M`, and nilpotent when `M` is finitely generated.

When `H` is a commutative Hopf algebra that is also a `ℚ`-algebra and `M` is a `ℚ`-module, the
exponential point `exp d = ε ∘ exp D` acts on `m ∈ M` by the truncated exponential series of
`differential d`, and when `differential d` is nilpotent on `M` the linear action of `expPointAt d
hd t` is `IsNilpotent.exp (t • differential d)` (`IsNilpotent.exp (differential d)` at `t = 1`).
More generally, for any commutative `R`-algebra `B`, `expPointAt d hd t` acts on `B ⊗[R] M` for
every finitely generated comodule `M` as `IsNilpotent.exp (t • (differential d).baseChange B)`, so
every point on an exponential one-parameter subgroup is unipotent
(`TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt`,
`TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`).

## Main declarations

* `TauCeti.Comodule.coact_differential` and `TauCeti.Comodule.coact_pow_differential`: the coaction
  intertwines `Comodule.differential d` and its powers with `Bialgebra.leftInvariantDerivation d`.
* `TauCeti.Comodule.pow_differential_apply`: `(differential d ^ n) m` contracts the coaction against
  `ε ∘ Dⁿ`.
* `exists_pow_differential_apply_eq_zero_of_forall_exists_iterate_leftInvariantDerivation_eq_zero`
  and `isNilpotent_differential_of_finite_of_forall_exists_iterate_leftInvariantDerivation_eq_zero`
  in `TauCeti.Comodule`: local nilpotence of `D` implies local nilpotence of `differential d`, and
  nilpotence on finitely generated comodules.
* `TauCeti.Comodule.basePointsRepresentation_expPoint_apply_eq_sum`,
  `TauCeti.Comodule.basePointsRepresentation_expPoint`, and
  `TauCeti.Comodule.basePointsRepresentation_expPointAt`: `Bialgebra.expPoint d hd` and
  `Bialgebra.expPointAt d hd t` act on `M` by the exponential series of `differential d`.
* `TauCeti.Comodule.endOfPoint_expPointAt`, `TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt`, and
  `TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`: action of `expPointAt` on scalar extensions
  `B ⊗[R] M` and unipotency over arbitrary value algebras.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
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
  rw [← rid_lTensor_counit_coact (R := R) (C := H)
      (((differential (R := R) (H := H) (M := M) d) ^ n) m),
    coact_pow_differential, ← LinearMap.lTensor_comp_apply, LinearMap.tensorComponent_def,
    LinearMap.comp_apply, LinearEquiv.coe_coe]

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
theorem
    exists_pow_differential_apply_eq_zero_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
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
theorem isNilpotent_differential_of_finite_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
    [Module.Finite R M]
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    IsNilpotent (differential (R := R) (H := H) (M := M) d) :=
  Module.End.isNilpotent_iff_of_finite.mpr
    (exists_pow_differential_apply_eq_zero_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
      hd)

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
  exact (differential (R := R) (H := H) (M := M) d).sum_range_smul_pow_apply_eq_of_le _ hm
    (le_max_right N k)

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

/-- **On a comodule where the differentiated operator is nilpotent, the exponential curve
`Bialgebra.expPointAt d hd t` acts by `IsNilpotent.exp (t • differential d)`.** -/
theorem basePointsRepresentation_expPointAt
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hM : IsNilpotent (differential (R := R) (H := H) (M := M) d)) (t : R) :
    basePointsRepresentation (H := H) M (Bialgebra.expPointAt d hd t) =
      IsNilpotent.exp (t • differential (R := R) (H := H) (M := M) d) := by
  have hsmul : Bialgebra.leftInvariantDerivation (t • d) =
      t • Bialgebra.leftInvariantDerivation d :=
    (Bialgebra.leftInvariantDerivation (R := R) (H := H)).toLinearMap.map_smul t d
  have ht : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation (t • d))^[n] h = 0 := by
    simpa only [hsmul] using
      (Bialgebra.leftInvariantDerivation d).exists_iterate_smul_eq_zero hd t
  have he : Bialgebra.expPointAt d hd t = toConv (Bialgebra.expPoint (t • d) ht) := by
    apply WithConv.ext
    ext x
    rw [Bialgebra.expPointAt_apply_eq_counit_taylorExpAt, Bialgebra.expPoint_apply]
    simp only [hsmul]
    rw [Derivation.taylorExpAt_eq_taylorExp_smul]
  rw [he, basePointsRepresentation_expPoint ht (by rw [map_smul]; exact hM.smul t), map_smul]

end Exponential

section ScalarExtension

open LinearMap TensorProduct

variable {R H M : Type*} [CommRing R] [CommRing H] [Bialgebra R H] [Algebra ℚ H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

omit [Algebra ℚ H] [Comodule R H M] in
private theorem comm_lTensor_algebraOfId_comp {B : Type*} [CommRing B] [Algebra R B]
    (f : H →ₗ[R] R) (x : M ⊗[R] H) :
    TensorProduct.comm R M B ((((Algebra.ofId R B).toLinearMap ∘ₗ f).lTensor M) x) =
      1 ⊗ₜ[R] tensorComponent f x := by
  induction x using TensorProduct.inductionOn with
  | tmul m h => simp [Algebra.algebraMap_eq_smul_one, tmul_smul]
  | add x y hx hy => simp only [map_add, tmul_add, hx, hy]

omit [Comodule R H M] in
private theorem aeval_expPointPolynomial_eq_sum_range {B : Type*} [CommRing B] [Algebra R B]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : B) {h : H} {N₀ N : ℕ}
    (hN₀ : (Bialgebra.leftInvariantDerivation d)^[N₀] h = 0) (hN : N₀ ≤ N) :
    let : Algebra ℚ R :=
      ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
    Polynomial.aeval t (Bialgebra.expPointPolynomial d hd h) =
      ∑ k ∈ Finset.range N,
        algebraMap R B ((Bialgebra.expPointPolynomial d hd h).coeff k) * t ^ k := by
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  set p := Bialgebra.expPointPolynomial d hd h
  have hzero (k : ℕ) (hk : N ≤ k) : p.coeff k = 0 := by
    have hk0 : (Bialgebra.leftInvariantDerivation d)^[k] h = 0 := by
      simpa [pow_apply_eq_iterate] using Module.End.pow_map_zero_of_le
        (f := (Bialgebra.leftInvariantDerivation d).toLinearMap) (hN.trans hk)
        (by simpa [pow_apply_eq_iterate] using hN₀)
    rw [Bialgebra.coeff_expPointPolynomial, hk0, smul_zero, map_zero]
  rw [Polynomial.aeval_eq_sum_range]
  simp only [Algebra.smul_def]
  rcases lt_or_ge p.natDegree N with hlt | hle
  · exact Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hlt)) fun k _ hk ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hk), map_zero, zero_mul]
  · exact (Finset.sum_subset (Finset.range_mono (Nat.le_succ_of_le hle)) fun k _ hk ↦ by
      rw [hzero k (by simpa using hk), map_zero, zero_mul]).symm

omit [Comodule R H M] in
private theorem exists_comm_lTensor_expPointAt_eq_sum {B : Type*} [CommRing B] [Algebra R B]
    [Algebra ℚ B] (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : B) (x : M ⊗[R] H) :
    ∃ N₀, ∀ N ≥ N₀,
      TensorProduct.comm R M B ((Bialgebra.expPointAt d hd t).ofConv.toLinearMap.lTensor M x) =
        ∑ k ∈ Finset.range N, (k.factorial : ℚ)⁻¹ • (t ^ k •
          TensorProduct.comm R M B ((((Algebra.ofId R B).toLinearMap ∘ₗ Coalgebra.counit (R := R)
            ∘ₗ (Bialgebra.leftInvariantDerivation d).toLinearMap ^ k).lTensor M) x)) := by
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul m h =>
    obtain ⟨N₀, hN₀⟩ := hd h
    refine ⟨N₀, fun N hN ↦ ?_⟩
    rw [lTensor_tmul, comm_tmul, AlgHom.toLinearMap_apply, Bialgebra.expPointAt_apply d hd t h,
      aeval_expPointPolynomial_eq_sum_range d hd t hN₀ hN, sum_tmul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [lTensor_tmul, comm_tmul]
    simp only [comp_apply, AlgHom.toLinearMap_apply, FunLike.coe_pow_eq_iterate,
      Derivation.coeFn_coe, smul_tmul', smul_eq_mul, Bialgebra.coeff_expPointPolynomial,
      map_rat_smul, smul_mul_assoc, mul_comm (algebraMap R B _) (t ^ k)]
    rfl
  | add x y hx hy =>
    obtain ⟨Nx, hNx⟩ := hx
    obtain ⟨Ny, hNy⟩ := hy
    refine ⟨max Nx Ny, fun N hN ↦ ?_⟩
    rw [map_add, map_add, hNx N (le_of_max_le_left hN), hNy N (le_of_max_le_right hN),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [map_add, map_add, smul_add, smul_add]

/-- **The exponential curve acts on every finite-rank comodule as the operator exponential of its
differentiated action.** For any `B`-parameter `t`, `expPointAt d hd t` acts on `B ⊗[R] M` as
`IsNilpotent.exp (t • (differential d).baseChange B)`. -/
theorem endOfPoint_expPointAt [Module.Finite R M] {B : Type*} [CommRing B] [Algebra R B]
    [Algebra ℚ B] (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : B) :
    endOfPoint M (Bialgebra.expPointAt d hd t).ofConv =
      IsNilpotent.exp (t • (differential (R := R) (H := H) (M := M) d).baseChange B) := by
  obtain ⟨K, hK⟩ :=
    isNilpotent_differential_of_finite_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
      (M := M) hd
  have hK' : (t • (differential (R := R) (H := H) (M := M) d).baseChange B) ^ K = 0 := by
    rw [smul_pow, ← baseChange_pow, hK, baseChange_zero, smul_zero]
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
    have hb : b ⊗ₜ[R] m = b • (1 ⊗ₜ[R] m) := by simp [smul_tmul']
    rw [hb, map_smul, map_smul]
    congr 1
    obtain ⟨N₀, hN₀⟩ := exists_comm_lTensor_expPointAt_eq_sum (M := M) d hd t
      (coact (R := R) (C := H) m)
    rw [endOfPoint_tmul, one_smul, hN₀ (max N₀ K) (le_max_left _ _),
      IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (le_max_right N₀ K) hK'), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [comm_lTensor_algebraOfId_comp, ← pow_differential_apply, LinearMap.smul_apply, smul_pow,
      LinearMap.smul_apply, ← baseChange_pow, baseChange_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end ScalarExtension

end TauCeti.Comodule

namespace TauCeti.HopfAlgebra

open Comodule

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.HopfAlgebra R H] [Algebra ℚ H]

/-- **Every point on an exponential one-parameter subgroup is unipotent**, over any commutative
value algebra `B`. No `ℚ`-algebra hypothesis is required separately on `R` or `B`. -/
theorem isUnipotentPoint_expPointAt (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    {B : Type*} [CommRing B] [Algebra R B] (t : B) :
    IsUnipotentPoint (Bialgebra.expPointAt d hd t) := by
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  let : Algebra ℚ B := ((algebraMap R B).comp (algebraMap ℚ R)).toAlgebra
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  rw [endOfPoint_expPointAt d hd t]
  obtain ⟨K, hK⟩ :=
    isNilpotent_differential_of_finite_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
      (M := M) hd
  exact IsNilpotent.isNilpotent_exp_sub_one ⟨K, by
    rw [smul_pow, ← LinearMap.baseChange_pow, hK, LinearMap.baseChange_zero, smul_zero]⟩

/-- **The exponential of a tangent vector with locally nilpotent invariant derivation is a
unipotent point.** -/
theorem isUnipotentPoint_expPoint (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    IsUnipotentPoint (toConv (Bialgebra.expPoint d hd)) := by
  rw [← Bialgebra.expPointAt_one]
  exact isUnipotentPoint_expPointAt d hd (1 : R)

end TauCeti.HopfAlgebra
