/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Eval
public import TauCeti.RingTheory.MvPowerSeries.Order
public import TauCeti.RingTheory.PowerSeries.Cartier
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Symmetric multivariable formal power series and evaluation at the roots of `Z ^ n - X`

A multivariable formal power series `f : MvPowerSeries σ R` is symmetric
(`MvPowerSeries.IsSymmetric`) if it is invariant under every permutation of the variable set `σ`
via `MvPowerSeries.rename`. Symmetric power series form an `R`-subalgebra
`MvPowerSeries.symmetricSubalgebra σ R`.

When `σ` is finite of cardinality `n`, every degree-`m` homogeneous component of a symmetric power
series is a symmetric homogeneous polynomial of degree `m`. Evaluating the degree-`(k * n)`
component under `MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R` — which sends the `j`-th
elementary symmetric polynomial to `0` for `1 ≤ j < n` and the `n`-th elementary symmetric
polynomial to `(-1) ^ (n - 1) * X` — extracts a single coefficient at `X ^ k`. Assembling these
coefficients defines an `R`-algebra homomorphism

`MvPowerSeries.symmetricSubalgebra.evalTopEsymm σ R : symmetricSubalgebra σ R →ₐ[R] PowerSeries R`

extending polynomial `evalTopEsymm` (`evalTopEsymm_coe`), commuting with coefficient ring
homomorphisms (`map_evalTopEsymm`) and with formal power series substitution
(`evalTopEsymm_subst`), and sending the symmetric coordinate sum `∑ i : σ, γ(Xᵢ)` to
`n • PowerSeries.cartier R n 0 γ` (`evalTopEsymm_sum_toMvPowerSeries`). This last property is the
power-series input to Cartier's Frobenius operators on curves of formal group laws.

## References

* [P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*][cartier1967]
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978]
-/

public section

namespace MvPowerSeries

variable {σ τ R S : Type*}

/-- A multivariable formal power series `f` is symmetric if it is invariant under permutations of
its variables via `MvPowerSeries.rename`. -/
def IsSymmetric [CommSemiring R] (f : MvPowerSeries σ R) : Prop :=
  ∀ e : Equiv.Perm σ, rename e f = f

theorem isSymmetric_iff [CommSemiring R] {f : MvPowerSeries σ R} :
    f.IsSymmetric ↔ ∀ e : Equiv.Perm σ, rename e f = f :=
  Iff.rfl

/-- The subalgebra of symmetric multivariable formal power series. -/
noncomputable def symmetricSubalgebra (σ R : Type*) [CommSemiring R] :
    Subalgebra R (MvPowerSeries σ R) where
  carrier := Set.ofPred IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [map_mul, ha e, hb e]
  add_mem' ha hb e := by rw [map_add, ha e, hb e]

@[simp]
theorem mem_symmetricSubalgebra [CommSemiring R] (f : MvPowerSeries σ R) :
    f ∈ symmetricSubalgebra σ R ↔ f.IsSymmetric :=
  Iff.rfl

namespace IsSymmetric

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {f g : MvPowerSeries σ R}

@[simp]
theorem C (r : R) : IsSymmetric (C r : MvPowerSeries σ R) :=
  (symmetricSubalgebra σ R).algebraMap_mem r

@[simp]
theorem zero : IsSymmetric (0 : MvPowerSeries σ R) :=
  (symmetricSubalgebra σ R).zero_mem

@[simp]
theorem one : IsSymmetric (1 : MvPowerSeries σ R) :=
  (symmetricSubalgebra σ R).one_mem

theorem add (hf : IsSymmetric f) (hg : IsSymmetric g) : IsSymmetric (f + g) :=
  (symmetricSubalgebra σ R).add_mem hf hg

theorem mul (hf : IsSymmetric f) (hg : IsSymmetric g) : IsSymmetric (f * g) :=
  (symmetricSubalgebra σ R).mul_mem hf hg

theorem pow (hf : IsSymmetric f) (n : ℕ) : IsSymmetric (f ^ n) :=
  (symmetricSubalgebra σ R).pow_mem hf n

theorem smul (r : R) (hf : IsSymmetric f) : IsSymmetric (r • f) :=
  (symmetricSubalgebra σ R).smul_mem hf r

theorem sum {ι : Type*} (s : Finset ι) {a : ι → MvPowerSeries σ R}
    (ha : ∀ i ∈ s, (a i).IsSymmetric) : (∑ i ∈ s, a i).IsSymmetric :=
  (symmetricSubalgebra σ R).sum_mem ha

theorem prod {ι : Type*} (s : Finset ι) {a : ι → MvPowerSeries σ R}
    (ha : ∀ i ∈ s, (a i).IsSymmetric) : (∏ i ∈ s, a i).IsSymmetric :=
  (symmetricSubalgebra σ R).prod_mem ha

@[simp]
theorem map (hf : IsSymmetric f) (φ : R →+* S) : IsSymmetric (map φ f) := fun e ↦ by
  rw [rename_map, hf e]

protected theorem rename (hf : f.IsSymmetric) (e : σ ≃ τ) : (rename e f).IsSymmetric := fun e' ↦ by
  let g : Equiv.Perm σ := (e.trans e').trans e.symm
  have hfg : f = rename g f := (hf g).symm
  conv_rhs => rw [hfg]
  ext d
  set u := Finsupp.embDomain (e'.symm.trans e.symm).toEmbedding d with hu
  have hd : d = Finsupp.embDomain e'.toEmbedding (Finsupp.embDomain e.toEmbedding u) := by
    rw [hu, Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain,
      Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    have hid : ((⇑e' ∘ ⇑e) ∘ ⇑(e'.symm.trans e.symm) : τ → τ) = id := funext fun x ↦ by simp
    rw [Equiv.coe_toEmbedding, Equiv.coe_toEmbedding, Equiv.coe_toEmbedding, hid,
      Finsupp.mapDomain_id]
  have hd' : d = Finsupp.embDomain e.toEmbedding (Finsupp.embDomain g.toEmbedding u) := by
    rw [hu, Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain,
      Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    have hid : ((⇑e ∘ ⇑g) ∘ ⇑(e'.symm.trans e.symm) : τ → τ) = id := funext fun x ↦ by simp [g]
    rw [Equiv.coe_toEmbedding, Equiv.coe_toEmbedding, Equiv.coe_toEmbedding, hid,
      Finsupp.mapDomain_id]
  conv_lhs => rw [hd]
  conv_rhs => rw [hd']
  change coeff (Finsupp.embDomain e'.toEmbedding (Finsupp.embDomain e.toEmbedding u))
      (rename ⇑e'.toEmbedding (rename ⇑e.toEmbedding f)) =
    coeff (Finsupp.embDomain e.toEmbedding (Finsupp.embDomain g.toEmbedding u))
      (rename ⇑e.toEmbedding (rename ⇑g.toEmbedding f))
  rw [coeff_embDomain_rename, coeff_embDomain_rename, coeff_embDomain_rename,
    coeff_embDomain_rename]

@[simp]
theorem _root_.MvPowerSeries.isSymmetric_rename {e : σ ≃ τ} :
    (rename e f).IsSymmetric ↔ f.IsSymmetric :=
  ⟨fun h ↦ by simpa using h.rename e.symm, (·.rename e)⟩

@[simp]
theorem _root_.MvPowerSeries.isSymmetric_coe {p : MvPolynomial σ R} :
    IsSymmetric (p : MvPowerSeries σ R) ↔ p.IsSymmetric := by
  simp [IsSymmetric, MvPolynomial.IsSymmetric, rename_coe, MvPolynomial.coe_inj]

theorem sum_toMvPowerSeries [Fintype σ] (γ : PowerSeries R) :
    (∑ i : σ, γ.toMvPowerSeries i).IsSymmetric := fun e ↦ by
  rw [map_sum]
  simp_rw [rename_toMvPowerSeries]
  exact Equiv.sum_comp e fun i ↦ γ.toMvPowerSeries i

end CommSemiring

section CommRing

variable [CommRing R] {f g : MvPowerSeries σ R}

theorem neg (hf : IsSymmetric f) : IsSymmetric (-f) :=
  (symmetricSubalgebra σ R).neg_mem hf

theorem sub (hf : IsSymmetric f) (hg : IsSymmetric g) : IsSymmetric (f - g) :=
  (symmetricSubalgebra σ R).sub_mem hf hg

/-- Substituting symmetric power series into an arbitrary power series produces a symmetric power
series. -/
theorem subst {g : MvPowerSeries τ R} {a : τ → MvPowerSeries σ R} (ha : HasSubst a)
    (hsym : ∀ t, (a t).IsSymmetric) : (g.subst a).IsSymmetric := fun e ↦ by
  rw [rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp e)]
  congr 1
  funext t
  rw [← rename_eq_subst, hsym t e]

end CommRing

end IsSymmetric

section Homogeneous

variable [CommSemiring R]

private theorem degree_embDomain (e : σ ↪ τ) (d : σ →₀ ℕ) :
    (Finsupp.embDomain e d).degree = d.degree := by
  rw [Finsupp.degree_apply, Finsupp.degree_apply, Finsupp.support_embDomain, Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ ↦ Finsupp.embDomain_apply_self e d i

/-- Variable renaming commutes with taking a homogeneous component. -/
theorem rename_homogeneousComponent (e : σ ≃ τ) (m : ℕ) (f : MvPowerSeries σ R) :
    rename e (homogeneousComponent m f) = homogeneousComponent m (rename e f) := by
  ext d
  set u := Finsupp.embDomain e.symm.toEmbedding d with hu
  have hd : d = Finsupp.embDomain e.toEmbedding u := by
    rw [hu, Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain,
      ← Finsupp.mapDomain_comp]
    have hid : (⇑e ∘ ⇑e.symm : τ → τ) = id := funext e.apply_symm_apply
    rw [Equiv.coe_toEmbedding, Equiv.coe_toEmbedding, hid, Finsupp.mapDomain_id]
  rw [hd]
  change coeff (Finsupp.embDomain e.toEmbedding u)
      (rename ⇑e.toEmbedding (homogeneousComponent m f)) =
    coeff (Finsupp.embDomain e.toEmbedding u) (homogeneousComponent m (rename ⇑e.toEmbedding f))
  rw [coeff_embDomain_rename, coeff_homogeneousComponent, coeff_homogeneousComponent,
    degree_embDomain e.toEmbedding u, coeff_embDomain_rename]

/-- Variable renaming by a permutation commutes with `homogeneousComponentPolynomial`. -/
theorem rename_homogeneousComponentPolynomial [Finite σ] (e : Equiv.Perm σ) (m : ℕ)
    (f : MvPowerSeries σ R) :
    MvPolynomial.rename e (homogeneousComponentPolynomial m f) =
      homogeneousComponentPolynomial m (rename e f) := by
  apply MvPolynomial.coe_inj.mp
  rw [← rename_coe, coe_homogeneousComponentPolynomial, coe_homogeneousComponentPolynomial,
    rename_homogeneousComponent]

/-- Variable renaming by a permutation commutes with `truncTotal`. -/
theorem rename_truncTotal [Finite σ] (e : Equiv.Perm σ) (N : ℕ) (f : MvPowerSeries σ R) :
    MvPolynomial.rename e (truncTotal N f) = truncTotal N (rename e f) := by
  apply MvPolynomial.coe_inj.mp
  rw [← rename_coe, truncTotal_eq_sum, truncTotal_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun m _ ↦ rename_homogeneousComponent e m f

theorem IsSymmetric.homogeneousComponent {f : MvPowerSeries σ R} (hf : f.IsSymmetric) (m : ℕ) :
    (homogeneousComponent m f).IsSymmetric := fun e ↦ by
  rw [rename_homogeneousComponent, hf e]

theorem IsSymmetric.homogeneousComponentPolynomial [Finite σ] {f : MvPowerSeries σ R}
    (hf : f.IsSymmetric) (m : ℕ) :
    (homogeneousComponentPolynomial m f).IsSymmetric := fun e ↦ by
  rw [rename_homogeneousComponentPolynomial, hf e]

theorem IsSymmetric.truncTotal [Finite σ] {f : MvPowerSeries σ R} (hf : f.IsSymmetric) (N : ℕ) :
    (truncTotal N f).IsSymmetric := fun e ↦ by
  rw [rename_truncTotal, hf e]

private theorem homogeneousComponentPolynomial_add [Finite σ] (m : ℕ) (f g : MvPowerSeries σ R) :
    homogeneousComponentPolynomial m (f + g) =
      homogeneousComponentPolynomial m f + homogeneousComponentPolynomial m g := by
  apply MvPolynomial.coe_inj.mp
  rw [coe_homogeneousComponentPolynomial, map_add, MvPolynomial.coe_add,
    coe_homogeneousComponentPolynomial, coe_homogeneousComponentPolynomial]

private theorem truncTotal_eq_sum_homogeneousComponentPolynomial [Finite σ] (N : ℕ)
    (f : MvPowerSeries σ R) :
    truncTotal N f = ∑ m ∈ Finset.range N, homogeneousComponentPolynomial m f := by
  apply MvPolynomial.coe_inj.mp
  rw [truncTotal_eq_sum, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
  exact Finset.sum_congr rfl fun m _ ↦ by
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, coe_homogeneousComponentPolynomial]

end Homogeneous

namespace symmetricSubalgebra

/-- Every element of `symmetricSubalgebra σ R` is symmetric. -/
theorem isSymmetric [CommSemiring R] (P : symmetricSubalgebra σ R) : P.1.IsSymmetric :=
  (mem_symmetricSubalgebra P.1).mp P.2

section EvalTopEsymm

variable [Fintype σ] [CommRing R]

/-- Underlying function of `evalTopEsymm` on symmetric formal power series. -/
private noncomputable def evalTopEsymmFun (P : symmetricSubalgebra σ R) : PowerSeries R :=
  PowerSeries.mk fun k ↦
    (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R
      ⟨homogeneousComponentPolynomial (k * Fintype.card σ) P.1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr
          ((isSymmetric P).homogeneousComponentPolynomial _)⟩).coeff k

/-- For `N > k * Fintype.card σ`, the `k`-th coefficient of `evalTopEsymmFun P` equals the `k`-th
coefficient of polynomial `evalTopEsymm` applied to `truncTotal N P`. -/
private theorem coeff_evalTopEsymmFun_eq_coeff_truncTotal (P : symmetricSubalgebra σ R)
    {k N : ℕ} (hN : k * Fintype.card σ < N) :
    PowerSeries.coeff k (evalTopEsymmFun P) =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R
        ⟨truncTotal N P.1,
          (MvPolynomial.mem_symmetricSubalgebra _).mpr
            ((isSymmetric P).truncTotal N)⟩).coeff k := by
  rw [evalTopEsymmFun, PowerSeries.coeff_mk]
  have hdecomp : (⟨truncTotal N P.1,
      (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric P).truncTotal N)⟩ :
      MvPolynomial.symmetricSubalgebra σ R) =
      ∑ m ∈ Finset.range N,
        ⟨homogeneousComponentPolynomial m P.1,
          (MvPolynomial.mem_symmetricSubalgebra _).mpr
            ((isSymmetric P).homogeneousComponentPolynomial m)⟩ := by
    apply Subtype.ext
    simpa using truncTotal_eq_sum_homogeneousComponentPolynomial N P.1
  rw [hdecomp, map_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single (k * Fintype.card σ)]
  · intro m _ hm
    rcases isEmpty_or_nonempty σ with hσ | hσ
    · rw [Fintype.card_eq_zero, mul_zero] at hm
      have hzero : homogeneousComponentPolynomial m P.1 = 0 := by
        apply MvPolynomial.coe_inj.mp
        rw [coe_homogeneousComponentPolynomial, MvPolynomial.coe_zero]
        ext d
        have hd0 : d = 0 := Subsingleton.elim _ _
        subst hd0
        simp [coeff_homogeneousComponent, hm.symm]
      have hsub : (⟨homogeneousComponentPolynomial m P.1,
          (MvPolynomial.mem_symmetricSubalgebra _).mpr
            ((isSymmetric P).homogeneousComponentPolynomial m)⟩ :
          MvPolynomial.symmetricSubalgebra σ R) = 0 := by
        apply Subtype.ext
        exact hzero
      simp [hsub]
    · exact MvPolynomial.symmetricSubalgebra.coeff_evalTopEsymm_eq_zero
        (isHomogeneous_homogeneousComponentPolynomial m P.1) hm.symm
  · intro hk
    exact absurd (Finset.mem_range.mpr hN) hk

/-- If two symmetric polynomials have the same `N`-truncation as power series with
`k * Fintype.card σ < N`, then their images under `evalTopEsymm` agree at `X ^ k`. -/
private theorem coeff_poly_evalTopEsymm_eq_of_truncTotal_eq
    {p q : MvPolynomial.symmetricSubalgebra σ R} {k N : ℕ} (hN : k * Fintype.card σ < N)
    (htrunc : truncTotal N (p.1 : MvPowerSeries σ R) = truncTotal N (q.1 : MvPowerSeries σ R)) :
    (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R p).coeff k =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R q).coeff k := by
  let P : symmetricSubalgebra σ R :=
    ⟨p.1, (mem_symmetricSubalgebra _).mpr (isSymmetric_coe.mpr
      ((MvPolynomial.mem_symmetricSubalgebra _).mp p.2))⟩
  let Q : symmetricSubalgebra σ R :=
    ⟨q.1, (mem_symmetricSubalgebra _).mpr (isSymmetric_coe.mpr
      ((MvPolynomial.mem_symmetricSubalgebra _).mp q.2))⟩
  let M := max N (max (p.1.totalDegree + 1) (q.1.totalDegree + 1))
  have hM : k * Fintype.card σ < M := hN.trans_le (le_max_left _ _)
  have hM0 : M ≠ 0 := by omega
  have hpM : truncTotal M (p.1 : MvPowerSeries σ R) = p.1 :=
    (truncTotal_coe_eq_self_iff p.1 hM0).mpr (by omega)
  have hqM : truncTotal M (q.1 : MvPowerSeries σ R) = q.1 :=
    (truncTotal_coe_eq_self_iff q.1 hM0).mpr (by omega)
  have hpCoeff : PowerSeries.coeff k (evalTopEsymmFun P) =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R p).coeff k := by
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal P hM]
    have hsub : (⟨truncTotal M P.1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric P).truncTotal M)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) = p := by
      apply Subtype.ext
      exact hpM
    rw [hsub]
  have hqCoeff : PowerSeries.coeff k (evalTopEsymmFun Q) =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R q).coeff k := by
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal Q hM]
    have hsub : (⟨truncTotal M Q.1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric Q).truncTotal M)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) = q := by
      apply Subtype.ext
      exact hqM
    rw [hsub]
  rw [← hpCoeff, ← hqCoeff, coeff_evalTopEsymmFun_eq_coeff_truncTotal P hN,
    coeff_evalTopEsymmFun_eq_coeff_truncTotal Q hN]
  have hsub : (⟨truncTotal N P.1,
      (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric P).truncTotal N)⟩ :
      MvPolynomial.symmetricSubalgebra σ R) =
      ⟨truncTotal N Q.1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric Q).truncTotal N)⟩ := by
    apply Subtype.ext
    exact htrunc
  rw [hsub]

variable (σ R) in
/-- Evaluating a symmetric formal power series `P(X₁, …, Xₙ)` (`n = Fintype.card σ`) at the formal
roots of `Z ^ n - X`, extending `MvPolynomial.symmetricSubalgebra.evalTopEsymm` componentwise. -/
noncomputable def evalTopEsymm : symmetricSubalgebra σ R →ₐ[R] PowerSeries R where
  toFun := evalTopEsymmFun
  map_one' := by
    ext k
    have hN : k * Fintype.card σ < k * Fintype.card σ + 1 := Nat.lt_succ_self _
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal 1 hN]
    have h1 : (⟨truncTotal (k * Fintype.card σ + 1) (1 : symmetricSubalgebra σ R).1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr
          ((isSymmetric (1 : symmetricSubalgebra σ R)).truncTotal _)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) = 1 := by
      apply Subtype.ext
      exact truncTotal_one (Nat.succ_ne_zero _)
    rw [h1, map_one, Polynomial.coeff_one, PowerSeries.coeff_one]
  map_mul' P Q := by
    ext k
    let N := k * Fintype.card σ + 1
    have hN : k * Fintype.card σ < N := Nat.lt_succ_self _
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal (P * Q) hN]
    let pN : MvPolynomial.symmetricSubalgebra σ R :=
      ⟨truncTotal N P.1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric P).truncTotal N)⟩
    let qN : MvPolynomial.symmetricSubalgebra σ R :=
      ⟨truncTotal N Q.1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric Q).truncTotal N)⟩
    let pqN : MvPolynomial.symmetricSubalgebra σ R :=
      ⟨truncTotal N (P * Q).1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric (P * Q)).truncTotal N)⟩
    have htrunc : truncTotal N ((P * Q).1 : MvPowerSeries σ R) =
        truncTotal N ((pN * qN).1 : MvPowerSeries σ R) := by
      ext d
      by_cases hd : d.degree < N
      · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd, Subalgebra.coe_mul, Subalgebra.coe_mul,
          MvPolynomial.coeff_coe, coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hd]
      · rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd), coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
    have heq : (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R pqN).coeff k =
        (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R (pN * qN)).coeff k := by
      apply coeff_poly_evalTopEsymm_eq_of_truncTotal_eq hN
      have h0 : N ≠ 0 := Nat.succ_ne_zero _
      change truncTotal N (truncTotal N (P * Q).1 : MvPowerSeries σ R) = _
      rw [(truncTotal_coe_eq_self_iff _ h0).mpr (totalDegree_truncTotal_lt _ h0), htrunc]
    change (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R pqN).coeff k = _
    rw [heq, map_mul, Polynomial.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun ab hab ↦ ?_
    rw [Finset.mem_antidiagonal] at hab
    have haN : ab.1 * Fintype.card σ < N := by
      have : ab.1 ≤ k := by omega
      exact (Nat.mul_le_mul_right _ this).trans_lt hN
    have hbN : ab.2 * Fintype.card σ < N := by
      have : ab.2 ≤ k := by omega
      exact (Nat.mul_le_mul_right _ this).trans_lt hN
    rw [← coeff_evalTopEsymmFun_eq_coeff_truncTotal P haN,
      ← coeff_evalTopEsymmFun_eq_coeff_truncTotal Q hbN]
  map_zero' := by
    ext k
    have hN : k * Fintype.card σ < k * Fintype.card σ + 1 := Nat.lt_succ_self _
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal 0 hN]
    have h0 : (⟨truncTotal (k * Fintype.card σ + 1) (0 : symmetricSubalgebra σ R).1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr
          ((isSymmetric (0 : symmetricSubalgebra σ R)).truncTotal _)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) = 0 := by
      apply Subtype.ext
      exact map_zero _
    rw [h0, map_zero, Polynomial.coeff_zero, map_zero (PowerSeries.coeff k)]
  map_add' P Q := by
    ext k
    rw [evalTopEsymmFun, evalTopEsymmFun, evalTopEsymmFun, PowerSeries.coeff_mk, map_add,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← Polynomial.coeff_add, ← map_add]
    have hsub : (⟨homogeneousComponentPolynomial (k * Fintype.card σ) (P + Q).1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr
          ((isSymmetric (P + Q)).homogeneousComponentPolynomial _)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) =
        ⟨homogeneousComponentPolynomial (k * Fintype.card σ) P.1,
          (MvPolynomial.mem_symmetricSubalgebra _).mpr
            ((isSymmetric P).homogeneousComponentPolynomial _)⟩ +
        ⟨homogeneousComponentPolynomial (k * Fintype.card σ) Q.1,
          (MvPolynomial.mem_symmetricSubalgebra _).mpr
            ((isSymmetric Q).homogeneousComponentPolynomial _)⟩ := by
      apply Subtype.ext
      exact homogeneousComponentPolynomial_add _ P.1 Q.1
    rw [hsub]
  commutes' r := by
    ext k
    have hN : k * Fintype.card σ < k * Fintype.card σ + 1 := Nat.lt_succ_self _
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal (algebraMap R _ r) hN]
    have hr : (⟨truncTotal (k * Fintype.card σ + 1) (algebraMap R (symmetricSubalgebra σ R) r).1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr
          ((isSymmetric (algebraMap R (symmetricSubalgebra σ R) r)).truncTotal _)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) = algebraMap R _ r := by
      apply Subtype.ext
      have h0 : k * Fintype.card σ + 1 ≠ 0 := Nat.succ_ne_zero _
      change truncTotal _ (C r : MvPowerSeries σ R) = MvPolynomial.C r
      rw [← MvPolynomial.coe_C]
      exact (truncTotal_coe_eq_self_iff _ h0).mpr
        (MvPolynomial.totalDegree_C r ▸ Nat.zero_lt_succ _)
    rw [hr, AlgHom.commutes, Polynomial.algebraMap_eq, Polynomial.coeff_C,
      PowerSeries.algebraMap_apply, PowerSeries.coeff_C, Algebra.algebraMap_self_apply]

theorem coeff_evalTopEsymm (P : symmetricSubalgebra σ R) (k : ℕ) :
    PowerSeries.coeff k (evalTopEsymm σ R P) =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R
        ⟨homogeneousComponentPolynomial (k * Fintype.card σ) P.1,
          (MvPolynomial.mem_symmetricSubalgebra _).mpr
            ((isSymmetric P).homogeneousComponentPolynomial _)⟩).coeff k := by
  simp [evalTopEsymm, evalTopEsymmFun]

private theorem coeff_evalTopEsymm_eq_coeff_truncTotal (P : symmetricSubalgebra σ R)
    {k N : ℕ} (hN : k * Fintype.card σ < N) :
    PowerSeries.coeff k (evalTopEsymm σ R P) =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R
        ⟨truncTotal N P.1,
          (MvPolynomial.mem_symmetricSubalgebra _).mpr
            ((isSymmetric P).truncTotal N)⟩).coeff k := by
  rw [coeff_evalTopEsymm]
  have h := coeff_evalTopEsymmFun_eq_coeff_truncTotal P hN
  rwa [evalTopEsymmFun, PowerSeries.coeff_mk] at h

@[simp]
theorem constantCoeff_evalTopEsymm (P : symmetricSubalgebra σ R) :
    PowerSeries.constantCoeff (evalTopEsymm σ R P) = constantCoeff P.1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_evalTopEsymm, zero_mul]
  have h0 : homogeneousComponentPolynomial 0 P.1 = MvPolynomial.C (constantCoeff P.1) := by
    apply MvPolynomial.coe_inj.mp
    rw [coe_homogeneousComponentPolynomial, homogeneousComponent_zero, MvPolynomial.coe_C]
  have hsub : (⟨homogeneousComponentPolynomial 0 P.1,
      (MvPolynomial.mem_symmetricSubalgebra _).mpr
        ((isSymmetric P).homogeneousComponentPolynomial 0)⟩ :
      MvPolynomial.symmetricSubalgebra σ R) = algebraMap R _ (constantCoeff P.1) := by
    apply Subtype.ext
    exact h0
  rw [hsub, AlgHom.commutes, Polynomial.algebraMap_eq, Polynomial.coeff_C_zero]

/-- On symmetric polynomials coerced to symmetric power series, `evalTopEsymm` agrees with
polynomial `evalTopEsymm` coerced to `PowerSeries R`. -/
theorem evalTopEsymm_coe (p : MvPolynomial.symmetricSubalgebra σ R) :
    evalTopEsymm σ R
        ⟨p.1, (mem_symmetricSubalgebra _).mpr
          (isSymmetric_coe.mpr ((MvPolynomial.mem_symmetricSubalgebra _).mp p.2))⟩ =
      ((MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R p : Polynomial R) : PowerSeries R) := by
  ext k
  let P : symmetricSubalgebra σ R :=
    ⟨p.1, (mem_symmetricSubalgebra _).mpr
      (isSymmetric_coe.mpr ((MvPolynomial.mem_symmetricSubalgebra _).mp p.2))⟩
  let N := max (p.1.totalDegree + 1) (k * Fintype.card σ + 1)
  have hN : k * Fintype.card σ < N := (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  have hN0 : N ≠ 0 := by omega
  rw [coeff_evalTopEsymm_eq_coeff_truncTotal P hN, Polynomial.coeff_coe]
  have hsub : (⟨truncTotal N P.1,
      (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric P).truncTotal N)⟩ :
      MvPolynomial.symmetricSubalgebra σ R) = p := by
    apply Subtype.ext
    exact (truncTotal_coe_eq_self_iff p.1 hN0).mpr (by omega)
  rw [hsub]

/-- `evalTopEsymm` commutes with changing coefficients along a ring homomorphism `f : R →+* S`. -/
theorem map_evalTopEsymm [CommRing S] (f : R →+* S) (P : symmetricSubalgebra σ R) :
    PowerSeries.map f (evalTopEsymm σ R P) =
      evalTopEsymm σ S ⟨map f P.1, (mem_symmetricSubalgebra _).mpr ((isSymmetric P).map f)⟩ := by
  ext k
  rw [PowerSeries.coeff_map, coeff_evalTopEsymm, coeff_evalTopEsymm,
    ← Polynomial.coeff_map, MvPolynomial.symmetricSubalgebra.map_evalTopEsymm]
  have hsub : (⟨MvPolynomial.map f (homogeneousComponentPolynomial (k * Fintype.card σ) P.1),
      (MvPolynomial.mem_symmetricSubalgebra _).mpr
        (((MvPolynomial.mem_symmetricSubalgebra _).mp
          ((MvPolynomial.mem_symmetricSubalgebra _).mpr
            ((isSymmetric P).homogeneousComponentPolynomial _))).map f)⟩ :
      MvPolynomial.symmetricSubalgebra σ S) =
      ⟨homogeneousComponentPolynomial (k * Fintype.card σ) (map f P.1),
        (MvPolynomial.mem_symmetricSubalgebra _).mpr
          (((isSymmetric P).map f).homogeneousComponentPolynomial _)⟩ := by
    apply Subtype.ext
    ext d
    rw [MvPolynomial.coeff_map, ← MvPolynomial.coeff_coe, coe_homogeneousComponentPolynomial,
      ← MvPolynomial.coeff_coe, coe_homogeneousComponentPolynomial,
      coeff_homogeneousComponent, coeff_homogeneousComponent]
    split_ifs <;> simp
  rw [hsub]

/-- `evalTopEsymm` commutes with formal power series substitution. -/
theorem evalTopEsymm_subst [Nonempty σ] [Finite τ] (g : MvPowerSeries τ R)
    (a : τ → symmetricSubalgebra σ R) (ha : ∀ t, constantCoeff (a t).1 = 0) :
    evalTopEsymm σ R
        ⟨g.subst (fun t ↦ (a t).1),
          (mem_symmetricSubalgebra _).mpr
            (IsSymmetric.subst (hasSubst_of_constantCoeff_zero ha) fun t ↦ isSymmetric (a t))⟩ =
      g.subst (fun t ↦ evalTopEsymm σ R (a t)) := by
  ext k
  let PS : symmetricSubalgebra σ R :=
    ⟨g.subst (fun t ↦ (a t).1),
      (mem_symmetricSubalgebra _).mpr
        (IsSymmetric.subst (hasSubst_of_constantCoeff_zero ha) fun t ↦ isSymmetric (a t))⟩
  let N := k * Fintype.card σ + 1
  have hN : k * Fintype.card σ < N := Nat.lt_succ_self _
  have hcard : 0 < Fintype.card σ := Fintype.card_pos
  have hkN : k + 1 ≤ N := by nlinarith
  rw [coeff_evalTopEsymm_eq_coeff_truncTotal PS hN]
  let aN : τ → MvPolynomial.symmetricSubalgebra σ R :=
    fun t ↦ ⟨truncTotal N (a t).1,
      (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric (a t)).truncTotal N)⟩
  let Q : MvPolynomial.symmetricSubalgebra σ R := MvPolynomial.aeval aN (truncTotal N g)
  have hQ_val : Q.1 = MvPolynomial.aeval (fun t ↦ (aN t).1) (truncTotal N g) := by
    change (MvPolynomial.symmetricSubalgebra σ R).val.toRingHom
      (MvPolynomial.eval₂ (algebraMap R _) aN (truncTotal N g)) = _
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def]
    congr 1
  have htrunc_lhs : truncTotal N (g.subst fun t ↦ (a t).1) =
      truncTotal N (Q.1 : MvPowerSeries σ R) := by
    rw [truncTotal_subst ha, hQ_val, ← subst_coe_eq_coe_aeval]
  have hQ_eq : (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R
      ⟨truncTotal N PS.1,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric PS).truncTotal N)⟩).coeff k =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R Q).coeff k := by
    apply coeff_poly_evalTopEsymm_eq_of_truncTotal_eq hN
    have h0 : N ≠ 0 := Nat.succ_ne_zero _
    change truncTotal N (truncTotal N (g.subst fun t ↦ (a t).1) : MvPowerSeries σ R) = _
    rw [(truncTotal_coe_eq_self_iff _ h0).mpr (totalDegree_truncTotal_lt _ h0), htrunc_lhs]
  rw [hQ_eq]
  let Φ : MvPolynomial.symmetricSubalgebra σ R →ₐ[R] Polynomial R :=
    MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R
  have hΦQ : Φ Q = MvPolynomial.aeval (fun t ↦ Φ (aN t)) (truncTotal N g) := by
    change Φ.toRingHom (MvPolynomial.eval₂ (algebraMap R _) aN (truncTotal N g)) = _
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def]
    congr 1
    exact RingHom.ext fun r ↦ Φ.commutes r
  rw [hΦQ, ← Polynomial.coeff_coe]
  have hcoe_aeval :
      ((MvPolynomial.aeval (fun t ↦ Φ (aN t)) (truncTotal N g) : Polynomial R) : PowerSeries R) =
        (truncTotal N g : MvPowerSeries τ R).subst
          (fun t ↦ ((Φ (aN t) : Polynomial R) : PowerSeries R)) := by
    rw [subst_coe]
    let Ψ : Polynomial R →ₐ[R] PowerSeries R := Polynomial.coeToPowerSeries.algHom R
    have hΨ : ∀ q : Polynomial R, Ψ.toRingHom q = (q : PowerSeries R) := fun q ↦ by
      simp [Ψ, Polynomial.coeToPowerSeries.algHom_apply]
    rw [← hΨ, MvPolynomial.aeval_def, MvPolynomial.hom_eval₂, MvPolynomial.aeval_def]
    congr 1
    exact RingHom.ext fun r ↦ Ψ.commutes r
  rw [hcoe_aeval]
  have hb0 : ∀ t, constantCoeff (evalTopEsymm σ R (a t) : MvPowerSeries Unit R) = 0 := by
    intro t
    change PowerSeries.constantCoeff (evalTopEsymm σ R (a t)) = 0
    rw [constantCoeff_evalTopEsymm, ha t]
  have hc0 : ∀ t, constantCoeff (((Φ (aN t) : Polynomial R) : PowerSeries R) :
      MvPowerSeries Unit R) = 0 := by
    intro t
    change PowerSeries.constantCoeff ((Φ (aN t) : Polynomial R) : PowerSeries R) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      ← coeff_evalTopEsymm_eq_coeff_truncTotal (a t) (by simp [N]),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_evalTopEsymm, ha t]
  have htrunc_g :
      truncTotal (k + 1) (truncTotal N g : MvPowerSeries τ R) = truncTotal (k + 1) g := by
    ext d
    by_cases hd : d.degree < k + 1
    · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd, MvPolynomial.coeff_coe,
        coeff_truncTotal _ (hd.trans_le hkN)]
    · rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd), coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
  have htrunc_a : ∀ t,
      truncTotal (k + 1) (((Φ (aN t) : Polynomial R) : PowerSeries R) : MvPowerSeries Unit R) =
        truncTotal (k + 1) (evalTopEsymm σ R (a t) : MvPowerSeries Unit R) := by
    intro t
    ext d
    by_cases hd : d.degree < k + 1
    · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd]
      have hd_eq : d = Finsupp.single () (d ()) := by
        ext
        exact Finsupp.single_eq_same.symm
      have hd_deg : d.degree = d () := by
        conv_lhs => rw [hd_eq]
        simp [Finsupp.degree_eq_sum]
      have hd_lt : d () < k + 1 := hd_deg ▸ hd
      have hdN : d () * Fintype.card σ < N := by
        have : d () ≤ k := Nat.lt_succ_iff.mp hd_lt
        exact (Nat.mul_le_mul_right _ this).trans_lt hN
      rw [hd_eq]
      change PowerSeries.coeff (d ()) ((Φ (aN t) : Polynomial R) : PowerSeries R) =
        PowerSeries.coeff (d ()) (evalTopEsymm σ R (a t))
      rw [Polynomial.coeff_coe]
      exact (coeff_evalTopEsymm_eq_coeff_truncTotal (a t) hdN).symm
    · rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd), coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
  have htrunc_unit :
      truncTotal (k + 1)
          ((truncTotal N g : MvPowerSeries τ R).subst
            fun t ↦ (((Φ (aN t) : Polynomial R) : PowerSeries R) : MvPowerSeries Unit R)) =
        truncTotal (k + 1)
          (g.subst fun t ↦ (evalTopEsymm σ R (a t) : MvPowerSeries Unit R)) := by
    rw [truncTotal_subst hc0, truncTotal_subst hb0, htrunc_g]
    simp_rw [htrunc_a]
  have hdeg : (Finsupp.single () k : Unit →₀ ℕ).degree < k + 1 := by
    simp [Finsupp.degree_eq_sum]
  change coeff (Finsupp.single () k) _ = coeff (Finsupp.single () k) _
  rw [← coeff_truncTotal _ hdeg, htrunc_unit, coeff_truncTotal _ hdeg]

/-- Evaluating the symmetric coordinate sum `∑ i : σ, γ(Xᵢ)` under `evalTopEsymm` extracts the
degree-multiples of `n = Fintype.card σ` multiplied by `n`, i.e. `n • PowerSeries.cartier R n 0 γ`.
-/
theorem evalTopEsymm_sum_toMvPowerSeries [Nonempty σ] (γ : PowerSeries R) :
    evalTopEsymm σ R
        ⟨∑ i : σ, γ.toMvPowerSeries i,
          (mem_symmetricSubalgebra _).mpr (IsSymmetric.sum_toMvPowerSeries γ)⟩ =
      (Fintype.card σ : R) • PowerSeries.cartier R (Fintype.card σ) 0 γ := by
  have hn : 0 < Fintype.card σ := Fintype.card_pos
  ext k
  rw [coeff_evalTopEsymm, PowerSeries.coeff_smul, PowerSeries.coeff_cartier, add_zero,
    smul_eq_mul, mul_comm (Fintype.card σ) k]
  rcases eq_or_ne k 0 with rfl | hk
  · rw [zero_mul]
    have hcomp : homogeneousComponentPolynomial 0 (∑ i : σ, γ.toMvPowerSeries i) =
        (Fintype.card σ : R) • MvPolynomial.C (PowerSeries.coeff 0 γ) := by
      apply MvPolynomial.coe_inj.mp
      rw [coe_homogeneousComponentPolynomial, homogeneousComponent_zero, map_sum,
        MvPolynomial.coe_smul, MvPolynomial.coe_C, PowerSeries.coeff_zero_eq_constantCoeff]
      have hc : ∀ i : σ, constantCoeff (γ.toMvPowerSeries i) = PowerSeries.constantCoeff γ :=
        fun i ↦ by rw [PowerSeries.toMvPowerSeries_apply, constantCoeff_rename]; rfl
      simp_rw [hc]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_C_mul, map_mul, map_natCast]
    have hsub : (⟨homogeneousComponentPolynomial 0 (∑ i : σ, γ.toMvPowerSeries i),
        (MvPolynomial.mem_symmetricSubalgebra _).mpr
          ((IsSymmetric.sum_toMvPowerSeries γ).homogeneousComponentPolynomial 0)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) =
        (Fintype.card σ : R) • algebraMap R _ (PowerSeries.coeff 0 γ) := by
      apply Subtype.ext
      exact hcomp
    rw [hsub, map_smul, AlgHom.commutes, Polynomial.algebraMap_eq, Polynomial.coeff_smul,
      Polynomial.coeff_C_zero, smul_eq_mul]
  · have hkn : 0 < k * Fintype.card σ := Nat.mul_pos (Nat.pos_of_ne_zero hk) hn
    have hcomp : homogeneousComponentPolynomial (k * Fintype.card σ)
        (∑ i : σ, γ.toMvPowerSeries i) =
        PowerSeries.coeff (k * Fintype.card σ) γ •
          MvPolynomial.psum σ R (k * Fintype.card σ) := by
      apply MvPolynomial.coe_inj.mp
      rw [coe_homogeneousComponentPolynomial, MvPolynomial.coe_smul, MvPolynomial.psum,
        ← MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        map_sum MvPolynomial.coeToMvPowerSeries.ringHom]
      ext d
      rw [coeff_homogeneousComponent, map_sum (coeff d), coeff_smul, map_sum (coeff d),
        Finset.mul_sum]
      split_ifs with hd
      · refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_pow,
          MvPolynomial.coe_X, X_pow_eq, PowerSeries.toMvPowerSeries_apply]
        by_cases hdi : d = Finsupp.single i (k * Fintype.card σ)
        · subst hdi
          have hemb : Finsupp.single i (k * Fintype.card σ) =
              Finsupp.embDomain (Function.Embedding.punit i)
                (Finsupp.single () (k * Fintype.card σ)) := by
            ext j
            by_cases hj : j = i <;> simp [hj, Function.Embedding.punit]
          rw [show (fun _ : Unit ↦ i) = ⇑(Function.Embedding.punit i) from rfl,
            hemb, coeff_embDomain_rename, ← hemb, coeff_monomial_same, mul_one]
          rfl
        · have hnot : d ∉ Set.range (Finsupp.mapDomain fun _ : Unit ↦ i) := by
            rintro ⟨u, rfl⟩
            apply hdi
            have hu : u = Finsupp.single () (u ()) := by
              ext
              exact Finsupp.single_eq_same.symm
            have hdeg_u : (Finsupp.mapDomain (fun _ : Unit ↦ i) u).degree = u () := by
              rw [hu, Finsupp.mapDomain_single]
              simp [Finsupp.degree_eq_sum]
            rw [hu, Finsupp.mapDomain_single, ← hdeg_u, hd]
          rw [coeff_rename_eq_zero _ _ hnot, coeff_monomial_ne hdi, mul_zero]
      · refine (Finset.sum_eq_zero fun i _ ↦ ?_).symm
        rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_pow,
          MvPolynomial.coe_X, X_pow_eq]
        have hne : d ≠ Finsupp.single i (k * Fintype.card σ) := fun h ↦
          hd (by simp [h, Finsupp.degree_eq_sum])
        rw [coeff_monomial_ne hne, mul_zero]
    have hsub : (⟨homogeneousComponentPolynomial (k * Fintype.card σ)
        (∑ i : σ, γ.toMvPowerSeries i),
        (MvPolynomial.mem_symmetricSubalgebra _).mpr
          ((IsSymmetric.sum_toMvPowerSeries γ).homogeneousComponentPolynomial _)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) =
        PowerSeries.coeff (k * Fintype.card σ) γ •
          ⟨MvPolynomial.psum σ R (k * Fintype.card σ),
            (MvPolynomial.mem_symmetricSubalgebra _).mpr
              (MvPolynomial.psum_isSymmetric σ R (k * Fintype.card σ))⟩ := by
      apply Subtype.ext
      exact hcomp
    rw [hsub, map_smul, MvPolynomial.symmetricSubalgebra.evalTopEsymm_psum hkn,
      ite_eq_left (dvd_mul_left _ _), Nat.mul_div_cancel _ hn, Polynomial.coeff_smul,
      Polynomial.coeff_natCast_mul, Polynomial.coeff_X_pow_self, mul_one, smul_eq_mul, mul_comm]

end EvalTopEsymm

end symmetricSubalgebra

end MvPowerSeries
