/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam
public import TauCeti.KnotTheory.Jimbo.StrandInclusion
import TauCeti.Data.Fin.Tuple.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The weighted Jimbo trace on finite type-A Hecke algebras and its Ocneanu comparison

For `N` colours, Turaev's diagonal enhancement `TauCeti.KnotTheory.jimboEnhancement` commutes with
the representation `TauCeti.TypeAHeckeAlgebra.jimbo (Fin N) q` of the finite type-A Hecke algebra
on the `q`-tensor space `(Fin n → Fin N) →₀ R`. Consequently the weighted functional

`x ↦ tr (jimbo (Fin N) q x * jimboEnhancement q)`

(`TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace N q n`) is an `R`-linear trace on
`TauCeti.TypeAHeckeAlgebra R q n` for every commutative ring `R`, unit `q : Rˣ`, colour count `N`,
and strand count `n`. Composed with `TauCeti.TypeAHeckeAlgebra.braidHom`, it recovers the braid
weighted trace `TauCeti.KnotTheory.jimboWeightedTrace`.

This finite-colour tensor trace and the universal algebraic trace
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace` on the infinite Hecke tower are distinct objects:
`jimboWeightedTrace N q n` requires no division by the quantum dimension
`D_N = ∑ a : Fin N, jimboWeight q a` and multiplies by `D_N` when an uncrossed strand is added, by
`q ^ N` under positive Markov stabilization (`x ↦ strandIncl x * T_last`), and by `(q⁻¹) ^ N`
under negative stabilization (`x ↦ strandIncl x * T_last⁻¹`). When `D_N` has an inverse `c` in `R`
(`c * D_N = 1`), rescaling `jimboWeightedTrace N q n` by `c ^ n` produces a normalized Markov
tower and therefore agrees with `ocneanuTrace R q (c * q ^ N)` along `toInfinite`, as well as with
the positive geometric atomic model of `TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic`. Over
a field where `q + q⁻¹` is a unit, its eigenprojection factor is Wenzl's parameter `a_N(q ^ 2)`.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace`: Turaev's `N`-colour weighted trace as an
  `R`-linear functional on `TypeAHeckeAlgebra R q n`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.commute_jimboEnhancement_jimbo`: Turaev's enhancement commutes with
  the Hecke representation.
* `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_mapDomain_snoc` and
  `TauCeti.TypeAHeckeAlgebra.jimbo_map_single`: compatibility of `jimbo` with tower inclusions and
  base change.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_braidHom`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_T_last`, and
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last`: factorization
  of the braid trace, uncrossed-strand factor, and positive and negative Hecke stabilization laws.
* `TauCeti.TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace` and
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_eq_pow_mul_ocneanuTrace`: comparison with the
  Ocneanu trace at `z = c * q ^ N` when `c * D_N = 1`.
* `TauCeti.TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_atomicTrace_geometric` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_mul_eigenprojection_jimbo`: comparison with the
  geometric atomic trace and Wenzl's parameter `wenzlParam N (q ^ 2)`.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247–252.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383.
-/

public section

open Function Finsupp
open scoped BigOperators

namespace TauCeti

namespace TypeAHeckeAlgebra

section Intertwining

variable {R : Type*} [CommRing R] (ι : Type*) [LinearOrder ι] (q : Rˣ) {n : ℕ}

/-- A map of Hecke algebras and a linear map of `q`-tensor spaces that intertwine the Jimbo
representations on every generator intertwine them on every element. -/
theorem jimbo_comp_eq_of_forall_T {m : ℕ}
    (f : TypeAHeckeAlgebra R q n →ₐ[R] TypeAHeckeAlgebra R q m)
    (L : ((Fin n → ι) →₀ R) →ₗ[R] (Fin m → ι) →₀ R)
    (h : ∀ i, (jimbo ι q (f (T q i))).comp L = L.comp (jimbo ι q (T q i)))
    (x : TypeAHeckeAlgebra R q n) :
    (jimbo ι q (f x)).comp L = L.comp (jimbo ι q x) := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact h i
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact LinearMap.ext fun v ↦ by simp [Module.algebraMap_end_apply]
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_assoc, hy, ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc]

/-- Adding an uncrossed last strand intertwines the Jimbo action with holding the last colour
fixed. -/
@[simp]
theorem jimbo_strandIncl_mapDomain_snoc (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    jimbo ι q (strandIncl R q n x) (mapDomain (fun w ↦ Fin.snoc w a) v) =
      mapDomain (fun w ↦ Fin.snoc w a) (jimbo ι q x v) := by
  set L := lmapDomain R R (fun w : Fin n → ι ↦ (Fin.snoc w a : Fin (n + 1) → ι))
  suffices h : (jimbo ι q (strandIncl R q n x)).comp L = L.comp (jimbo ι q x) by
    simpa [L] using LinearMap.congr_fun h v
  refine jimbo_comp_eq_of_forall_T ι q _ L (fun i ↦ ?_) x
  have hj : BraidGroup.strand (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
      (BraidGroup.strand i).castSucc := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
      (BraidGroup.strandSucc i).castSucc := Fin.ext (by simp)
  rw [strandIncl_T, jimbo_T, jimbo_T, hj, hk]
  exact KnotTheory.jimboGenerator_comp_lmapDomain_snoc q _ _ a

/-- Adding an uncrossed last strand preserves matrix coefficients within each block of words with
a fixed last colour and vanishes between blocks with distinct last colours. -/
theorem jimbo_strandIncl_single_snoc_apply_snoc (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) :
    jimbo ι q (strandIncl R q n x) (single (Fin.snoc w a) 1) (Fin.snoc u d) =
      if a = d then jimbo ι q x (single w 1) u else 0 := by
  have h := jimbo_strandIncl_mapDomain_snoc ι q x a (single w 1)
  rw [mapDomain_single] at h
  rw [h]
  by_cases had : a = d
  · subst d
    simp only [↓reduceIte]
    exact mapDomain_apply_of_injective (@Fin.snoc_left_injective _ (fun _ ↦ ι) a) _ _
  · simp only [had, ↓reduceIte]
    apply mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    apply had
    simpa using congrArg (fun z : Fin (n + 1) → ι ↦ z (Fin.last n)) hv

/-- As units, the Hecke generator `unitT q i` acts in the Jimbo representation by
`KnotTheory.jimboUnit q i`. -/
@[simp]
theorem jimbo_unitT (i : Fin (n - 1)) :
    Units.map (jimbo ι q (n := n) : TypeAHeckeAlgebra R q n →* Module.End R ((Fin n → ι) →₀ R))
        (unitT q i) =
      KnotTheory.jimboUnit q i :=
  Units.ext <| by simp [KnotTheory.jimboUnit_val]

/-- The inverse Hecke generator `(unitT q i)⁻¹` acts in the Jimbo representation by the inverse
Jimbo R-matrix. -/
theorem jimbo_val_inv_unitT (i : Fin (n - 1)) :
    jimbo ι q (↑(unitT q i)⁻¹ : TypeAHeckeAlgebra R q n) =
      (↑(KnotTheory.jimboUnit (ι := ι) q i)⁻¹ : Module.End R ((Fin n → ι) →₀ R)) := by
  rw [← jimbo_unitT ι q i, ← map_inv]
  rfl

/-- Changing coefficients along an `R`-algebra `S` maps the word-basis matrix coefficients of the
Jimbo representation through `algebraMap R S`. -/
@[simp]
theorem jimbo_map_single {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}
    (h : algebraMap R S q = q') (x : TypeAHeckeAlgebra R q n) (w u : Fin n → ι) :
    jimbo ι q' (map n h x) (single w 1) u = algebraMap R S (jimbo ι q x (single w 1) u) := by
  let L : ((Fin n → ι) →₀ R) →ₗ[R] (Fin n → ι) →₀ S :=
    Finsupp.mapRange.linearMap (Algebra.linearMap R S)
  have hL (v : Fin n → ι) (r : R) : L (single v r) = single v (algebraMap R S r) := by
    simp [L]
  have hqinv : algebraMap R S (↑q⁻¹ : R) = (↑q'⁻¹ : S) := by
    rw [← Units.ext (u := Units.map (algebraMap R S).toMonoidHom q) h, Units.coe_map_inv,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  have hgen (i : Fin (n - 1)) :
      ((jimbo ι q' (T q' i)).restrictScalars R).comp L = L.comp (jimbo ι q (T q i)) := by
    ext v : 2
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, lsingle_apply, hL, map_one,
      jimbo_T, KnotTheory.jimboGenerator_single_one]
    split_ifs <;> simp [map_add, hL, h, hqinv]
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  have hcomp : ((jimbo ι q' (map n h x)).restrictScalars R).comp L = L.comp (jimbo ι q x) := by
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      simpa only [map_T] using hgen i
    | algebraMap r =>
      rw [AlgHom.commutes, AlgHom.commutes]
      ext v : 2
      simp [hL, Module.algebraMap_end_apply, Algebra.smul_def]
    | add x y _ _ hx hy =>
      simp only [map_add, LinearMap.restrictScalars_add, LinearMap.add_comp, LinearMap.comp_add,
        hx, hy]
    | mul x y _ _ hx hy =>
      have hm (a b : Module.End S ((Fin n → ι) →₀ S)) :
          (a * b).restrictScalars R = (a.restrictScalars R).comp (b.restrictScalars R) := rfl
      rw [map_mul, map_mul, map_mul, hm, Module.End.mul_eq_comp, LinearMap.comp_assoc, hy,
        ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc]
  have hv := LinearMap.congr_fun hcomp (single w 1)
  simpa [L, Finsupp.mapRange_single] using DFunLike.congr_fun hv u

end Intertwining

section WeightedTrace

variable {R : Type*} [CommRing R] (N : ℕ) (q : Rˣ)

/-- Turaev's tensor-power enhancement commutes with every element of the finite type-A Hecke
algebra in the `N`-colour Jimbo representation. -/
theorem commute_jimboEnhancement_jimbo {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    Commute (KnotTheory.jimboEnhancement (N := N) q) (jimbo (Fin N) q x) := by
  have hx : jimbo (Fin N) q x ∈
      Algebra.adjoin R (Set.range (jimbo (Fin N) q ∘ T (n := n) q)) := by
    rw [Set.range_comp, ← AlgHom.map_adjoin, adjoin_range_T]
    exact ⟨x, trivial, rfl⟩
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_
  rintro _ ⟨i, rfl⟩
  simpa only [Function.comp_apply, jimbo_T] using
    KnotTheory.jimboEnhancement_commute_generator (N := N) q
      (BraidGroup.strand i) (BraidGroup.strandSucc i)

/-- **The `N`-colour weighted Jimbo trace** on the type-A Hecke algebra on `n` strands:
`x ↦ tr (jimbo (Fin N) q x * jimboEnhancement q)`. No division by `q - q⁻¹` or by the quantum
dimension is required. -/
noncomputable def jimboWeightedTrace (n : ℕ) : TypeAHeckeAlgebra R q n →ₗ[R] R :=
  LinearMap.trace R ((Fin n → Fin N) →₀ R) ∘ₗ
    LinearMap.mulRight R (KnotTheory.jimboEnhancement q) ∘ₗ (jimbo (Fin N) q).toLinearMap

variable {N q} {n : ℕ}

/-- Evaluation of the Hecke-level weighted Jimbo trace. -/
theorem jimboWeightedTrace_apply (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      LinearMap.trace R ((Fin n → Fin N) →₀ R)
        (jimbo (Fin N) q x * KnotTheory.jimboEnhancement q) :=
  (rfl)

/-- On the image of a braid, the Hecke-level weighted Jimbo trace agrees with Turaev's braid
weighted trace `KnotTheory.jimboWeightedTrace`. -/
@[simp]
theorem jimboWeightedTrace_braidHom (b : BraidGroup n) :
    jimboWeightedTrace N q n (braidHom R q n b) = KnotTheory.jimboWeightedTrace (N := N) q b := by
  rw [jimboWeightedTrace_apply, jimbo_braidHom, KnotTheory.jimboWeightedTrace_def]

/-- The weighted Jimbo trace on the finite Hecke algebra is tracial. -/
theorem jimboWeightedTrace_mul_comm (x y : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n (x * y) = jimboWeightedTrace N q n (y * x) := by
  rw [jimboWeightedTrace_apply, jimboWeightedTrace_apply, map_mul (jimbo (Fin N) q),
    map_mul (jimbo (Fin N) q), mul_assoc, ← (commute_jimboEnhancement_jimbo N q y).eq, ← mul_assoc,
    LinearMap.trace_mul_comm, mul_assoc]

/-- Word-basis matrix-coefficient formula for the Hecke-level weighted Jimbo trace. -/
theorem jimboWeightedTrace_eq_sum (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      ∑ w : Fin n → Fin N,
        jimbo (Fin N) q x (single w 1) w * ∏ i, KnotTheory.jimboWeight q (w i) := by
  classical
  rw [jimboWeightedTrace_apply, LinearMap.trace_eq_matrix_trace R Finsupp.basisSingleOne]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, mul_apply_eq_comp,
    Finsupp.coe_basisSingleOne, KnotTheory.jimboEnhancement_single_one, map_smul]
  simp [mul_comm]

/-- The weighted Jimbo trace of `1` on `n` strands is the `n`-th power of the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_one :
    jimboWeightedTrace N q n 1 = (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n := by
  simpa using jimboWeightedTrace_braidHom (N := N) (q := q) (1 : BraidGroup n)

/-- On scalars, the weighted Jimbo trace multiplies by the `n`-th power of the quantum
dimension. -/
@[simp]
theorem jimboWeightedTrace_algebraMap (r : R) :
    jimboWeightedTrace N q n (algebraMap R _ r) =
      r * (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, jimboWeightedTrace_one, smul_eq_mul]

/-- Formation of the Hecke-level weighted Jimbo trace commutes with base change along an
`R`-algebra `S`. -/
@[simp]
theorem jimboWeightedTrace_map {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}
    (h : algebraMap R S q = q') (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q' n (map n h x) = algebraMap R S (jimboWeightedTrace N q n x) := by
  have hw (a : Fin N) :
      KnotTheory.jimboWeight q' a = algebraMap R S (KnotTheory.jimboWeight q a) := by
    rw [KnotTheory.jimboWeight_def, KnotTheory.jimboWeight_def,
      ← Units.ext (u := Units.map (algebraMap R S).toMonoidHom q) h, ← map_zpow, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [jimboWeightedTrace_eq_sum, jimboWeightedTrace_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [jimbo_map_single (Fin N) q h, map_mul, map_prod]
  simp only [hw]

/-- Adding an uncrossed last strand multiplies the Hecke-level weighted Jimbo trace by the quantum
dimension. -/
@[simp]
theorem jimboWeightedTrace_strandIncl (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q (n + 1) (strandIncl R q n x) =
      jimboWeightedTrace N q n x * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    jimbo_strandIncl_single_snoc_apply_snoc, ite_true, Fin.prod_univ_castSucc (n := n),
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [jimboWeightedTrace_eq_sum, Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

/-- In the diagonal coefficient of `strandIncl x * T_last` at `Fin.snoc w c`, only the
colour-preserving block survives, factored through the two-strand Jimbo generator. -/
private theorem jimbo_strandIncl_mul_T_last_single_snoc_apply
    (x : TypeAHeckeAlgebra R q (n + 1)) (w : Fin (n + 1) → Fin N) (c : Fin N) :
    jimbo (Fin N) q (strandIncl R q (n + 1) x * T q (Fin.last n))
        (single (Fin.snoc w c) 1) (Fin.snoc w c) =
      jimbo (Fin N) q x (single w 1) w *
        (KnotTheory.jimboGenerator q (0 : Fin 2) 1 (single ![w (Fin.last n), c] 1))
          ![w (Fin.last n), c] := by
  classical
  have hj : BraidGroup.strand (Fin.last n : Fin (n + 2 - 1)) = (Fin.last n).castSucc :=
    Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.last n : Fin (n + 2 - 1)) = Fin.last (n + 1) :=
    Fin.ext (by simp)
  have hswap : Fin.snoc w c ∘ Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1)) =
      Fin.snoc (update w (Fin.last n) c) (w (Fin.last n)) := by
    rw [Equiv.comp_swap_eq_update]
    simp [← Fin.snoc_update, Fin.update_snoc_last]
  have hswap₂ : (![w (Fin.last n), c] : Fin 2 → Fin N) ∘ Equiv.swap 0 1 =
      ![c, w (Fin.last n)] := by
    ext i; fin_cases i <;> simp
  have hpair : (![c, w (Fin.last n)] : Fin 2 → Fin N) = ![w (Fin.last n), c] ↔
      w (Fin.last n) = c := by
    simp [funext_iff, Fin.forall_fin_two, eq_comm]
  simp only [map_mul, mul_apply_eq_comp, jimbo_T, hj, hk, KnotTheory.jimboGenerator_single_one,
    Fin.snoc_castSucc, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases lt_trichotomy (w (Fin.last n)) c with h | h | h
  · simp only [h.ne, h, ↓reduceIte, hswap, hswap₂, jimbo_strandIncl_single_snoc_apply_snoc,
      single_apply, hpair, mul_zero]
  · simp only [h, ↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      jimbo_strandIncl_single_snoc_apply_snoc, single_eq_same, mul_one, mul_comm]
  · simp only [h.ne.symm, h.not_gt, ↓reduceIte, hswap, hswap₂, map_add, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, jimbo_strandIncl_single_snoc_apply_snoc,
      single_apply, hpair, zero_add, mul_one, mul_comm]

/-- **Positive Markov stabilization on the finite Hecke algebra.** Appending a strand and
multiplying by the last generator `T (Fin.last n)` multiplies the `N`-colour weighted Jimbo trace
by `q ^ N`. -/
@[simp]
theorem jimboWeightedTrace_strandIncl_mul_T_last (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2) (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) x := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 2) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    jimbo_strandIncl_mul_T_last_single_snoc_apply, Fin.prod_univ_castSucc (n := n + 1),
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.sum_comm, jimboWeightedTrace_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  calc
    _ = (jimbo (Fin N) q x (single w 1) w * ∏ i, KnotTheory.jimboWeight q (w i)) *
        ∑ c : Fin N,
          (KnotTheory.jimboGenerator q (0 : Fin 2) 1 (single ![w (Fin.last n), c] 1))
            ![w (Fin.last n), c] * KnotTheory.jimboWeight q c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      ring
    _ = _ := by rw [KnotTheory.sum_jimboGenerator_coeff_mul_weight, ite_eq_left rfl]; ring

/-- Two-sided Markov rule for the Hecke-level weighted Jimbo trace:
`a * T_last * b ↦ q ^ N * tr(b * a)`. -/
theorem jimboWeightedTrace_strandIncl_mul_T_last_mul_strandIncl
    (a b : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2)
        (strandIncl R q (n + 1) a * T q (Fin.last n) * strandIncl R q (n + 1) b) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) (b * a) := by
  rw [jimboWeightedTrace_mul_comm, ← mul_assoc, ← map_mul,
    jimboWeightedTrace_strandIncl_mul_T_last]

/-- **Negative Markov stabilization on the finite Hecke algebra.** Appending a strand and
multiplying by the inverse of the last generator `(unitT q (Fin.last n))⁻¹` multiplies the
`N`-colour weighted Jimbo trace by `(q⁻¹) ^ N`. -/
theorem jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2)
        (strandIncl R q (n + 1) x * ↑(unitT (n := n + 2) q (Fin.last n))⁻¹) =
      ↑((q⁻¹) ^ N) * jimboWeightedTrace N q (n + 1) x := by
  rw [val_inv_unitT, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, map_sub, map_smul,
    jimboWeightedTrace_strandIncl_mul_T_last, jimboWeightedTrace_strandIncl, smul_eq_mul]
  linear_combination -jimboWeightedTrace N q (n + 1) x * KnotTheory.jimboWeight_sum (N := N) q

/-- On two strands, the generator `T 0` has weighted Jimbo trace `q ^ N` times the quantum
dimension. -/
@[simp]
theorem jimboWeightedTrace_T_two :
    jimboWeightedTrace N q 2 (T q 0) = ↑(q ^ N) * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  simpa using jimboWeightedTrace_strandIncl_mul_T_last (N := N) (q := q) (n := 0) 1

/-- On two strands, the inverse generator `(unitT q 0)⁻¹` has weighted Jimbo trace `(q⁻¹) ^ N`
times the quantum dimension. -/
theorem jimboWeightedTrace_val_inv_unitT_two :
    jimboWeightedTrace N q 2 ↑(unitT (n := 2) q 0)⁻¹ =
      ↑((q⁻¹) ^ N) * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  simpa using jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last (N := N) (q := q) (n := 0) 1

/-! ### Comparison with the Ocneanu trace and the geometric atomic model -/

/-- **Comparison with the Ocneanu trace.** Whenever `c` is an inverse of the `N`-colour quantum
dimension `∑ a : Fin N, jimboWeight q a` in `R`, rescaling `jimboWeightedTrace N q n` by `c ^ n`
yields the Ocneanu trace with parameter `c * q ^ N` along `toInfinite`. -/
theorem mul_jimboWeightedTrace_eq_ocneanuTrace {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) (x : TypeAHeckeAlgebra R q n) :
    c ^ n * jimboWeightedTrace N q n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  let φ (m : ℕ) : TypeAHeckeAlgebra R q m →ₗ[R] R := c ^ m • jimboWeightedTrace N q m
  refine eq_ocneanuTrace_toInfinite φ (by simp [φ]) (fun m y ↦ ?_)
    (fun m x y ↦ by simp only [φ, LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_mul_comm])
    (fun m y ↦ ?_) n x
  · simp only [φ, LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl, pow_succ]
    linear_combination c ^ m * jimboWeightedTrace N q m y * hc
  · simp only [φ, LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl_mul_T_last]
    ring

/-- **Unrescaled Ocneanu-trace formula for the weighted Jimbo trace.** When the quantum dimension
`D_N` has an inverse `c` in `R`, the `N`-colour weighted Jimbo trace on `n` strands equals
`D_N ^ n` times the Ocneanu trace at `z = c * q ^ N`. -/
theorem jimboWeightedTrace_eq_pow_mul_ocneanuTrace {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n *
        InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  rw [← mul_jimboWeightedTrace_eq_ocneanuTrace hc, ← mul_assoc, ← mul_pow, mul_comm _ c, hc,
    one_pow, one_mul]

end WeightedTrace

end TypeAHeckeAlgebra

namespace KnotTheory

/-- The `(r + 1)`-colour quantum dimension factors as `(q⁻¹) ^ r` times the geometric sum
`∑ b ∈ range (r + 1), (q ^ 2) ^ b`. -/
theorem sum_jimboWeight_eq_inv_pow_mul_geom_sum {R : Type*} [Semiring R] (q : Rˣ) (r : ℕ) :
    (∑ a : Fin (r + 1), jimboWeight q a) =
      ↑((q⁻¹) ^ r) * ∑ b ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ b := by
  simp only [jimboWeight_def]
  rw [Fin.sum_univ_eq_sum_range
    (fun c ↦ (↑(q ^ (((r + 1 : ℕ) : ℤ) - 1 - 2 * (c : ℤ))) : R)) (r + 1),
    ← Finset.sum_range_reflect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have hbr : b ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have hexp : ((r + 1 : ℕ) : ℤ) - 1 - 2 * ((r + 1 - 1 - b : ℕ) : ℤ) =
      -(r : ℤ) + (2 * b : ℕ) := by
    rw [Nat.add_sub_cancel, Nat.cast_sub hbr]
    push_cast
    ring
  rw [hexp, zpow_add, zpow_neg, zpow_natCast, zpow_natCast, inv_pow, pow_mul, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]

end KnotTheory

namespace TypeAHeckeAlgebra

/-- **Comparison with the positive geometric atomic model.** When `c` inverts the `(r + 1)`-colour
quantum dimension, rescaling the `(r + 1)`-colour weighted Jimbo trace by `c ^ n` agrees with the
positive geometric atomic trace on `r + 1` letters with normalized weights
`a ↦ c * (q⁻¹) ^ r * (q ^ 2) ^ a`. -/
theorem mul_jimboWeightedTrace_eq_atomicTrace_geometric {R : Type*} [CommRing R] {q : Rˣ}
    {r n : ℕ} {c : R} (hc : c * ∑ a : Fin (r + 1), KnotTheory.jimboWeight q a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    c ^ n * jimboWeightedTrace (r + 1) q n x =
      atomicTrace (fun _ : Fin (r + 1) ↦ True) q
        (fun a ↦ c * ↑((q⁻¹) ^ r) * ((q : R) ^ 2) ^ (a : ℕ)) n x := by
  have hc' : (c * ↑((q⁻¹) ^ r)) * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1 := by
    rwa [mul_assoc, ← KnotTheory.sum_jimboWeight_eq_inv_pow_mul_geom_sum]
  have hz : (c * ↑((q⁻¹) ^ r)) * (q : R) ^ (2 * r + 1) = c * ↑(q ^ (r + 1)) := by
    have hq : ((q⁻¹ : Rˣ) : R) ^ r * (q : R) ^ r = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    have h2r : 2 * r + 1 = r + (r + 1) := by omega
    rw [h2r, pow_add]
    simp only [Units.val_pow_eq_pow_val]
    linear_combination c * (q : R) ^ (r + 1) * hq
  rw [mul_jimboWeightedTrace_eq_ocneanuTrace hc, atomicTrace_geometric_eq q hc', hz]

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

/-- **Wenzl parameter of the Ocneanu trace at a Jimbo specialization.** Over a field `K`, if
`s = q + q⁻¹` is a unit and `c` inverts the `N`-colour quantum dimension, then the Ocneanu trace at
`z = c * q ^ N` multiplies by Wenzl's parameter `wenzlParam N (q ^ 2)` when the eigenprojection
`s⁻¹ • (T n + q⁻¹)` is appended to an element of `stage K q (n + 1)`. -/
theorem ocneanuTrace_mul_eigenprojection_jimbo {K : Type*} [Field K] {q : Kˣ} (s : Kˣ)
    (hs : (s : K) = q + ↑q⁻¹) {N : ℕ} {c : K}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra K q} (hx : x ∈ stage K q (n + 1)) :
    ocneanuTrace K q (c * ↑(q ^ N)) (x * (↑s⁻¹ : K) • (T q n + algebraMap K _ (↑q⁻¹ : K))) =
      wenzlParam (N : ℤ) ((q : K) ^ 2) * ocneanuTrace K q (c * ↑(q ^ N)) x := by
  rcases N with _ | r
  · simp at hc
  have hc' : (c * ↑((q⁻¹) ^ r)) * ∑ a ∈ Finset.range (r + 1), ((q : K) ^ 2) ^ a = 1 := by
    rwa [mul_assoc, ← KnotTheory.sum_jimboWeight_eq_inv_pow_mul_geom_sum]
  have hz : c * ↑(q ^ (r + 1)) = (c * ↑((q⁻¹) ^ r)) * (q : K) ^ (2 * r + 1) := by
    have hq : ((q⁻¹ : Kˣ) : K) ^ r * (q : K) ^ r = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    have h2r : 2 * r + 1 = r + (r + 1) := by omega
    rw [h2r, pow_add (q : K) r (r + 1)]
    simp only [Units.val_pow_eq_pow_val]
    linear_combination -c * (q : K) ^ (r + 1) * hq
  rw [hz]
  exact ocneanuTrace_mul_eigenprojection_geometric s hs hc' hx

end InfiniteTypeAHeckeAlgebra

end TauCeti

namespace RingHom

open TauCeti

/-- Applying a ring homomorphism to Turaev's weighted Jimbo braid trace maps the parameter unit
along `f`. -/
theorem map_jimboWeightedTrace {R S : Type*} [CommRing R] [CommRing S] {N n : ℕ}
    (f : R →+* S) (q : Rˣ) (b : BraidGroup n) :
    f (KnotTheory.jimboWeightedTrace (N := N) q b) =
      KnotTheory.jimboWeightedTrace (N := N) (Units.map f.toMonoidHom q) b := by
  let _ : Algebra R S := f.toAlgebra
  have hf : f (KnotTheory.jimboWeightedTrace (N := N) q b) =
      algebraMap R S (KnotTheory.jimboWeightedTrace (N := N) q b) := rfl
  have hq : algebraMap R S q = Units.map f.toMonoidHom q := rfl
  rw [hf]
  simpa only [TypeAHeckeAlgebra.jimboWeightedTrace_braidHom, TypeAHeckeAlgebra.map_braidHom] using
    (TypeAHeckeAlgebra.jimboWeightedTrace_map (N := N) (n := n) hq
      (TypeAHeckeAlgebra.braidHom R q n b)).symm

end RingHom
