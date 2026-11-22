/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.NumberTheory.Padics.Coleman.Frobenius

import TauCeti.LinearAlgebra.Submodule.CompleteFiltration
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.PowerSeries.Cartier
import TauCeti.RingTheory.PowerSeries.OneAddXPow
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Coleman's power-series basis

For a prime `p` and `(p)`-adically complete commutative ring `O`, Frobenius substitution
`Φ : O⟦X⟧ →ₐ[O] O⟦X⟧` (`TauCeti.Coleman.frobeniusHom` in `Coleman.Frobenius`) reduces modulo `p`
to `PowerSeries.expand p`. Combining the shifted-basis Cartier decomposition
(`PowerSeries.expandOneAddXEquiv` in `TauCeti.RingTheory.PowerSeries.Cartier`) with
`TauCeti.IsCompleteFiltration.isUnit_one_add` for the `(p)`-adically contractive perturbation
`Φ - expand p` yields the unique expansion `f = ∑ i < p, Φ(cᵢ) * (1 + X) ^ i`.

## Main definitions and results

* `TauCeti.Coleman.coordEquiv`, `TauCeti.Coleman.coord`, `TauCeti.Coleman.sum_frobeniusHom_coord`,
  `TauCeti.Coleman.coord_unique`: unique Coleman coordinates `f = ∑ i < p, Φ(cᵢ(f)) * (1 + X) ^ i`.
* `TauCeti.Coleman.frobeniusHom_injective`, `TauCeti.Coleman.frobeniusHom_mem_span_p_pow_iff`,
  `TauCeti.Coleman.coord_one_add_X_pow`, `TauCeti.Coleman.map_coord`,
  `TauCeti.Coleman.coeff_coord_mem_span_pow_of_coeff_mem_span_pow`: injectivity/congruence
  reflection of `Φ` (for prime `p` and `(p)`-adically complete `O`), values on `(1 + X) ^ n`,
  functoriality, and `(p)`-adic continuity modulus.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §§II, IV (Lemma 6,
  Theorem 11).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §2.2
  (Proposition 2.2.3).
* R. Sharifi, *Iwasawa Theory*, §5.4 (Proposition 5.4.3).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Chapter 10
  (Lemma 10.8).
-/

public noncomputable section

open PowerSeries

namespace TauCeti.Coleman

section BasisConstruction

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O]

private def assembly (p : ℕ) (O : Type*) [CommRing O] : (Fin p → O⟦X⟧) →ₗ[O] O⟦X⟧ where
  toFun a := ∑ i : Fin p, frobeniusHom p O (a i) * (1 + X) ^ (i : ℕ)
  map_add' _ _ := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' _ _ := by
    simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

private theorem assembly_apply (p : ℕ) (O : Type*) [CommRing O] (a : Fin p → O⟦X⟧) :
    assembly p O a = ∑ i : Fin p, frobeniusHom p O (a i) * (1 + X) ^ (i : ℕ) :=
  rfl

private def neumannStep (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] :
    Module.End O (Fin p → O⟦X⟧) :=
  let e := expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero O
  e.symm.toLinearMap.comp (assembly p O - e.toLinearMap)

private theorem neumannStep_apply (a : Fin p → O⟦X⟧) :
    neumannStep p O a =
      (expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero O).symm
        (assembly p O a - expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero O a) :=
  rfl

private theorem assembly_eq_expandOneAddXEquiv_add_neumannStep (a : Fin p → O⟦X⟧) :
    assembly p O a =
      expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero O (a + neumannStep p O a) := by
  rw [map_add, neumannStep_apply,
    (expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero O).apply_symm_apply]
  exact (add_sub_cancel _ _).symm

private theorem coeff_frobeniusHom_sub_expand_mem (J : Ideal O) {g : O⟦X⟧} {n : ℕ}
    (hg : ∀ m ≤ n, coeff m g ∈ J) :
    coeff n (frobeniusHom p O g - expand p (Fact.out : p.Prime).ne_zero g) ∈
      Ideal.span {(p : O)} * J := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [map_sub, frobeniusHom_apply, expand_apply, coeff_subst_eq_sum_range g (by simp),
    coeff_subst_eq_sum_range g (by rw [map_pow, constantCoeff_X, zero_pow hp]),
    ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun k hk ↦ ?_
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub]
  refine Ideal.mul_mem_mul_rev ?_ (hg k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  obtain ⟨r, hr⟩ := (C_dvd_one_add_X_pow_sub_one_sub_X_pow (O := O) (Fact.out : p.Prime)).trans
    (sub_dvd_pow_sub_pow _ _ k)
  rw [hr, coeff_C_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

private theorem coeff_neumannStep_mem (J : Ideal O) {a : Fin p → O⟦X⟧} {n : ℕ}
    (ha : ∀ i : Fin p, ∀ m < p * (n + 1), coeff m (a i) ∈ J) (j : Fin p) :
    coeff n (neumannStep p O a j) ∈ Ideal.span {(p : O)} * J := by
  rw [neumannStep_apply]
  refine coeff_expandOneAddXEquiv_symm_mem (Fact.out : p.Prime).ne_zero
    (Ideal.span {(p : O)} * J) (fun s hs ↦ ?_) j
  rw [assembly_apply, expandOneAddXEquiv_apply, ← Finset.sum_sub_distrib, map_sum]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  rw [← sub_mul, coeff_mul]
  exact Ideal.sum_mem _ fun xy hxy ↦ Ideal.mul_mem_right _ _ (coeff_frobeniusHom_sub_expand_mem J
    fun m hm ↦ ha i m (by rw [Finset.mem_antidiagonal] at hxy; omega))

private def coeffIdealFiltration (p : ℕ) (O : Type*) [CommRing O] (m : ℕ) :
    Submodule O (Fin p → O⟦X⟧) where
  carrier := {a | ∀ (i : Fin p) (n : ℕ), coeff n (a i) ∈ Ideal.span {(p : O)} ^ m}
  zero_mem' _ _ := by simp
  add_mem' ha hb i n := by
    rw [Pi.add_apply, map_add]
    exact add_mem (ha i n) (hb i n)
  smul_mem' c a ha i n := by
    rw [Pi.smul_apply, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_left _ c (ha i n)

omit [Fact p.Prime] in
private theorem coeffIdealFiltration_zero : coeffIdealFiltration p O 0 = ⊤ :=
  Submodule.eq_top_iff'.mpr fun _ _ _ ↦ by simp [pow_zero]

omit [Fact p.Prime] in
private theorem isCompleteFiltration_coeffIdealFiltration
    [IsAdicComplete (Ideal.span {(p : O)}) O] :
    TauCeti.IsCompleteFiltration (coeffIdealFiltration p O) where
  antitone _ _ hmn _ hx i n := Ideal.pow_le_pow_right hmn (hx i n)
  eq_zero_of_forall_mem a hx := by
    have hzero : (fun x : Fin p × ℕ ↦ coeff x.2 (a x.1)) = 0 :=
      TauCeti.eq_zero_of_forall_pow_dvd (p : O) fun m ⟨i, n⟩ ↦ by
        simpa only [Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hx m i n
    exact funext fun i ↦ PowerSeries.ext fun n ↦ congrFun hzero (i, n)
  exists_limit seq hseq := by
    obtain ⟨c, hc⟩ := TauCeti.exists_forall_pow_dvd_sub (p : O)
      (fun m (x : Fin p × ℕ) ↦ coeff x.2 (seq m x.1)) fun m ⟨i, n⟩ ↦ by
        simpa only [← map_sub, ← Pi.sub_apply, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton] using hseq m i n
    refine ⟨fun i ↦ mk fun n ↦ c (i, n), fun m i n ↦ ?_⟩
    simpa only [coeffIdealFiltration, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, Pi.sub_apply, map_sub, coeff_mk, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] using hc m (i, n)

private theorem map_coeffIdealFiltration_neumannStep_le (m : ℕ) :
    (coeffIdealFiltration p O m).map (neumannStep p O) ≤ coeffIdealFiltration p O (m + 1) := by
  rintro _ ⟨a, ha, rfl⟩ i n
  rw [pow_succ']
  exact coeff_neumannStep_mem (Ideal.span {(p : O)} ^ m) (fun j s _ ↦ ha j s) i

private theorem assembly_bijective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Bijective (assembly p O) := by
  have hunit : IsUnit ((LinearMap.id : Module.End O (Fin p → O⟦X⟧)) + neumannStep p O) :=
    (isCompleteFiltration_coeffIdealFiltration (p := p)).isUnit_one_add
      (coeffIdealFiltration_zero (p := p))
      (map_coeffIdealFiltration_neumannStep_le (p := p))
  have hbij : Function.Bijective
      ((LinearMap.id : Module.End O (Fin p → O⟦X⟧)) + neumannStep p O) :=
    (Module.End.isUnit_iff _).mp hunit
  exact (funext assembly_eq_expandOneAddXEquiv_add_neumannStep :
    (assembly p O : _ → _) = _).symm ▸
      (expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero O).bijective.comp hbij

end BasisConstruction

section Coordinates

variable (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- The `O`-linear equivalence sending `f` to its unique Coleman coordinates `c : Fin p → O⟦X⟧`
with `∑ i < p, Φ(c i) * (1 + X) ^ i = f` (Coleman Thm. 11; Sharifi Prop. 5.4.3; RJW Lemma 10.8). -/
def coordEquiv : O⟦X⟧ ≃ₗ[O] (Fin p → O⟦X⟧) :=
  (LinearEquiv.ofBijective (assembly p O) assembly_bijective).symm

/-- The `i`-th Coleman coordinate `cᵢ : O⟦X⟧ →ₗ[O] O⟦X⟧` in `f = ∑ i, Φ(cᵢ(f)) * (1 + X) ^ i`. -/
def coord (i : Fin p) : O⟦X⟧ →ₗ[O] O⟦X⟧ := (LinearMap.proj i).comp (coordEquiv p O).toLinearMap

variable {p O}

/-- Evaluating `coordEquiv p O f` at `i` gives `coord p O i f`. -/
@[simp]
theorem coordEquiv_apply (f : O⟦X⟧) (i : Fin p) : coordEquiv p O f i = coord p O i f := (rfl)

/-- The inverse of `coordEquiv p O` assembles `∑ i < p, Φ(a i) * (1 + X) ^ i`. -/
theorem coordEquiv_symm_apply (a : Fin p → O⟦X⟧) :
    (coordEquiv p O).symm a = ∑ i : Fin p, frobeniusHom p O (a i) * (1 + X) ^ (i : ℕ) := (rfl)

/-- Extracting the `i`-th Coleman coordinate from `(coordEquiv p O).symm a` recovers `a i`. -/
@[simp]
theorem coord_coordEquiv_symm (a : Fin p → O⟦X⟧) (i : Fin p) :
    coord p O i ((coordEquiv p O).symm a) = a i :=
  congrFun ((coordEquiv p O).apply_symm_apply a) i

/-- **Coleman's basis expansion:** `∑ i < p, Φ(coord p O i f) * (1 + X) ^ i = f`
(Coleman Thm. 11; Sharifi Prop. 5.4.3; RJW Lemma 10.8). -/
@[simp]
theorem sum_frobeniusHom_coord (f : O⟦X⟧) :
    ∑ i : Fin p, frobeniusHom p O (coord p O i f) * (1 + X) ^ (i : ℕ) = f :=
  (LinearEquiv.ofBijective (assembly p O) assembly_bijective).apply_symm_apply f

/-- Uniqueness of coordinates in the Coleman expansion. -/
theorem coord_unique {a : Fin p → O⟦X⟧} {f : O⟦X⟧}
    (ha : ∑ i : Fin p, frobeniusHom p O (a i) * (1 + X) ^ (i : ℕ) = f) (i : Fin p) :
    coord p O i f = a i :=
  congrFun ((LinearEquiv.ofBijective (assembly p O) assembly_bijective).symm_apply_eq.mpr ha.symm) i

/-- Extracting the `i`-th Coleman coordinate from an assembled sum `∑ j, Φ(a j) * (1 + X) ^ j`
recovers `a i`. -/
theorem coord_sum_frobeniusHom_mul_one_add_X_pow (a : Fin p → O⟦X⟧) (i : Fin p) :
    coord p O i (∑ j : Fin p, frobeniusHom p O (a j) * (1 + X) ^ (j : ℕ)) = a i :=
  coord_unique rfl i

/-- Multiplying by `Φ(a)` scales every Coleman coordinate by `a`. -/
@[simp]
theorem coord_frobeniusHom_mul (a f : O⟦X⟧) (i : Fin p) :
    coord p O i (frobeniusHom p O a * f) = a * coord p O i f :=
  coord_unique (a := fun j ↦ a * coord p O j f)
    (by simp only [map_mul, mul_assoc, ← Finset.mul_sum, sum_frobeniusHom_coord]) i

/-- Coleman coordinates of `(1 + X) ^ n` pick out residue `n % p` with `(1 + X) ^ (n / p)`. -/
@[simp]
theorem coord_one_add_X_pow (n : ℕ) (j : Fin p) :
    coord p O j ((1 + X : O⟦X⟧) ^ n) = if (j : ℕ) = n % p then (1 + X) ^ (n / p) else 0 := by
  refine coord_unique (a := fun k : Fin p ↦ if (k : ℕ) = n % p then (1 + X) ^ (n / p) else 0) ?_ j
  let r : Fin p := ⟨n % p, Nat.mod_lt n (Fact.out : p.Prime).pos⟩
  have hne (k : Fin p) (hkr : k ≠ r) : (k : ℕ) ≠ n % p := fun h ↦ hkr (Fin.ext h)
  rw [Finset.sum_eq_single r (fun k _ hkr ↦ by simp [hne k hkr]) (by simp)]
  simp [r, frobeniusHom_one_add_X_pow, ← pow_add, Nat.div_add_mod]

/-- The Coleman coordinates of `1 + X` are `1` at `i = 1` and `0` elsewhere. -/
@[simp]
theorem coord_one_add_X (i : Fin p) : coord p O i (1 + X) = if (i : ℕ) = 1 then 1 else 0 := by
  simpa [Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt,
    Nat.div_eq_of_lt (Fact.out : p.Prime).one_lt] using coord_one_add_X_pow (p := p) (O := O) 1 i

/-- The Coleman coordinates of `1` are `1` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem coord_one (i : Fin p) : coord p O i 1 = if (i : ℕ) = 0 then 1 else 0 := by
  simpa using coord_one_add_X_pow (p := p) (O := O) 0 i

/-- The Coleman coordinates of `Φ(a)` are `a` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem coord_frobeniusHom (a : O⟦X⟧) (i : Fin p) :
    coord p O i (frobeniusHom p O a) = if (i : ℕ) = 0 then a else 0 := by
  simpa using coord_frobeniusHom_mul (p := p) a 1 i

/-- For prime `p` over a `(p)`-adically complete ring `O`, `frobeniusHom p O` is injective. -/
theorem frobeniusHom_injective : Function.Injective (frobeniusHom p O) := fun _ _ h ↦ by
  simpa using congrArg (coord p O ⟨0, (Fact.out : p.Prime).pos⟩) h

/-- Multiplying by a constant `C c` scales every Coleman coordinate by `C c`. -/
@[simp]
theorem coord_C_mul (c : O) (f : O⟦X⟧) (i : Fin p) :
    coord p O i (C c * f) = C c * coord p O i f := by
  simpa only [frobeniusHom_C] using coord_frobeniusHom_mul (p := p) (C c) f i

/-- The Coleman coordinates of a constant series `C c` are `C c` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem coord_C (c : O) (i : Fin p) : coord p O i (C c) = if (i : ℕ) = 0 then C c else 0 := by
  simpa only [frobeniusHom_C] using coord_frobeniusHom (p := p) (C c) i

/-- For prime `p` over a `(p)`-adically complete ring `O`, Frobenius substitution preserves and
reflects membership in `(p) ^ k`. -/
theorem frobeniusHom_mem_span_p_pow_iff (k : ℕ) {f : O⟦X⟧} :
    frobeniusHom p O f ∈ Ideal.span {(p : O⟦X⟧)} ^ k ↔ f ∈ Ideal.span {(p : O⟦X⟧)} ^ k := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨coord p O ⟨0, (Fact.out : p.Prime).pos⟩ g, ?_⟩,
    fun ⟨g, hg⟩ ↦ ⟨frobeniusHom p O g, by rw [hg, map_mul, map_pow, map_natCast]⟩⟩
  simpa only [coord_frobeniusHom, ↓reduceIte, ← map_natCast C, ← map_pow, coord_C_mul] using
    congrArg (coord p O ⟨0, (Fact.out : p.Prime).pos⟩) hg

/-- Coefficientwise change of base ring commutes with Coleman coordinates. -/
theorem map_coord {O' : Type*} [CommRing O'] [IsAdicComplete (Ideal.span {(p : O')}) O']
    (φ : O →+* O') (f : O⟦X⟧) (i : Fin p) :
    PowerSeries.map φ (coord p O i f) = coord p O' i (PowerSeries.map φ f) :=
  (coord_unique (a := fun j ↦ PowerSeries.map φ (coord p O j f)) (by
    simpa only [map_sum, map_mul, map_pow, map_add, map_one, map_X, map_frobeniusHom] using
      congrArg (PowerSeries.map φ) (sum_frobeniusHom_coord (p := p) f)) i).symm

/-- **Explicit `(p)`-adic modulus of continuity for Coleman coordinates.** If the first
`p ^ k * (n + 1)` coefficients of `f` lie in `(p) ^ k`, then so does `coeff n (coord p O i f)`. -/
theorem coeff_coord_mem_span_pow_of_coeff_mem_span_pow :
    ∀ k : ℕ, ∀ {f : O⟦X⟧} {n : ℕ},
      (∀ s < p ^ k * (n + 1), coeff s f ∈ Ideal.span {(p : O)} ^ k) →
      ∀ i : Fin p, coeff n (coord p O i f) ∈ Ideal.span {(p : O)} ^ k
  | 0, _, _, _, _ => by simp
  | k + 1, f, n, hf, i => by
    let a : Fin p → O⟦X⟧ := fun j ↦ coord p O j f
    have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have ha_eq : a = (expandOneAddXEquiv p hp O).symm f - neumannStep p O a :=
      eq_sub_of_add_eq <| (expandOneAddXEquiv p hp O).injective <| by
        rw [LinearEquiv.apply_symm_apply, ← assembly_eq_expandOneAddXEquiv_add_neumannStep]
        exact sum_frobeniusHom_coord f
    have hcoeff : coeff n (coord p O i f) =
        coeff n ((expandOneAddXEquiv p hp O).symm f i) - coeff n (neumannStep p O a i) := by
      rw [← map_sub, ← Pi.sub_apply, ← ha_eq]
    have hstep : p * (n + 1) ≤ p ^ (k + 1) * (n + 1) := by
      have hpow : 1 ≤ p ^ k := Nat.one_le_pow k p (Fact.out : p.Prime).pos
      rw [pow_succ']
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right p hpow)
    rw [hcoeff]
    refine sub_mem
      (coeff_expandOneAddXEquiv_symm_mem hp _ (fun s hs ↦ hf s (lt_of_lt_of_le hs hstep)) i)
      ((pow_succ' (Ideal.span {(p : O)}) k).symm ▸ coeff_neumannStep_mem _ (fun j m hm ↦
        coeff_coord_mem_span_pow_of_coeff_mem_span_pow k (fun s hs ↦
          Ideal.pow_le_pow_right (Nat.le_succ k) (hf s (lt_of_lt_of_le hs
            (by rw [pow_succ, mul_assoc]; exact Nat.mul_le_mul_left _ hm)))) j) i)

end Coordinates

end TauCeti.Coleman
