/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Group.List
public import TauCeti.Topology.Algebra.Group.Profinite.Free.SuccessiveApproximation.Basic
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside

/-!
# Successive approximation of a relator carrying the `p`-power tails

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type `X`, with lower
`p`-series `λ_k = λ_k(F)`, and let `r, w ∈ λ_1(F)` be relators with the same class `ρ ∈ gr_1(F)`.
When the basis-modification map `δ_ρ` is not onto `gr_{m+1}(F)`, the successive-approximation
argument of `TauCeti.Topology.Algebra.Group.Profinite.Free.SuccessiveApproximation.Basic` still
runs as soon as the span statement holds up to the **tail** of a set `S` of generators, the span
`TauCeti.freeProP.gradedPowIterSpan` of the iterated `p`-powers `π^{m+1} ξ_i` of the generators
`x_i` with `i ∈ S`:

  `gr_{m+1}(F) = Im δ_ρ + ⟨π^{m+1} ξ_i : i ∈ S⟩`   for every `m ≥ 1`.

The set `S` is a parameter: for the odd-rank dyadic relators it is the set of generators whose
coefficient `c_i` in `ρ` vanishes, so that the span is the tail `T_{m+1}(ρ)` of
`TauCeti.freeProP.basisModificationTail`, while for the even-rank dyadic relators it also contains
the generator carrying the square.
At each level the discrepancy between the moved relator and the target is the class of a basis
modification up to a tail class `Σ_{i ∈ S} c_i π^{m+1} ξ_i`, which is the class of the product of
the powers `x_i^{p^{m+1} c_i}`. The basis modification is applied and the powers are absorbed into
per-generator **tail elements** `t_i`, which are carried along instead of being killed: the
approximation at level `m` is a congruence `φ r ≡ t_{i₁} ⋯ t_{i_a} * w * t_{j₁} ⋯ t_{j_b}`
modulo `λ_{m+2}(F)`, where the two lists of indices fix where the tail of each generator is placed,
and the tail elements lie in the closed procyclic subgroups `⟨x_i⟩` and in `λ_2(F)`. The tail of
each generator is placed at a single position, so the lists are required to be disjoint and
duplicate-free and to cover the set `S`.

The limit is taken through the levelwise comparison schema `TauCeti.PLowerCentralSeriesComparison`
with the finite tail data carried in the comparison data, and the tail elements are recovered from
the compatible sequence of their classes by the inverse-limit description of `F`. Since the closed
subgroups `⟨x_i⟩ ∩ λ_2(F)` are detected on the finite quotients
(`TauCeti.IsProP.mem_of_forall_mk_mem_map_pLowerCentralSeries`), the limits stay in them. The
conclusion is an exact equation `e r = t_{i₁} ⋯ t_{i_a} * w * t_{j₁} ⋯ t_{j_b}` for a continuous
automorphism `e` of `F`.

This is the first half of Labute's treatment of the relators with `q = 2`. For the odd-rank
dyadic normal-form word `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` the tails are the `2`-powers
`x_i^{2^{m+1}}` of the generators `x₂, …, x_n` other than the one carrying the square, and the
argument yields the relator in the intermediate form `x₁² r₀(x) x₂^{α₂} ⋯ x_n^{α_n}` with `2`-adic
exponents `α₂, …, α_n` divisible by `4`
(`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Odd.Approximation`), before the
tail relator `r₀(x) x₂^{α₂} ⋯ x_n^{α_n}` is normalised in its own right. For the even-rank word
`x₁² (x₁, x₂) (x₃, x₄) ⋯ (x_{n-1}, x_n)` the tails are the `2`-powers of every generator but `x₂`,
and the tail of `x₁` is placed in front of the word, which is why the theorem takes two lists of
tail positions; the intermediate form is `x₁^{2+α} (x₁, x₂) r₀(x) x₃^{α₃} ⋯ x_n^{α_n}`
(`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Approximation`).

## Main results

* `exists_continuousMonoidHom_inv_mul_apply_mem_of_range_sup_gradedPowIterSpan_eq_top`, in
  the namespace `TauCeti.freeProP`: the finite approximations, one basis modification and one
  tail correction per level.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_sup_gradedPowIterSpan_eq_top`
  is **the successive-approximation theorem with tails**: a continuous automorphism of `F` carries
  `r` to `w` up to tail elements of the closed procyclic subgroups `⟨x_i⟩ ∩ λ_2(F)`, `i ∈ S`,
  placed at the prescribed positions.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Proposition 5 and the proof of Theorem 3, cases (2) and (3).
-/

public section

namespace TauCeti.freeProP

open Subgroup

universe u

variable {p : ℕ} [Fact p.Prime] {X : Type u} [Finite X] [LinearOrder X]

/-- **Finite successive approximation with tails.** Let `r, w ∈ λ_1(F)` have the same class
`ρ ∈ gr_1(F)`, let `S` be a set of generators and `l₁, l₂` disjoint duplicate-free lists of
generators containing `S`, and suppose `gr_{m+1}(F) = Im δ_ρ + ⟨π^{m+1} ξ_i : i ∈ S⟩` for
`1 ≤ m ≤ k`. Then there are a continuous endomorphism `φ` of `F`, congruent to the identity modulo
`λ_1(F)`, and tail elements `t_i ∈ ⟨x_i⟩ ∩ λ_2(F)` with
`φ r ≡ (∏_{i ∈ l₁} t_i) * w * (∏_{i ∈ l₂} t_i) mod λ_{k+2}(F)`. -/
theorem exists_continuousMonoidHom_inv_mul_apply_mem_of_range_sup_gradedPowIterSpan_eq_top
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w) (S : Set X)
    (l₁ l₂ : List X) (hnd : (l₁ ++ l₂).Nodup) (hl : ∀ i ∈ S, i ∈ l₁ ++ l₂) (k : ℕ)
    (hspan : ∀ m (hm : 1 ≤ m), m ≤ k →
      LinearMap.range (basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)) ⊔
        gradedPowIterSpan p X S (m + 1) = ⊤) :
    ∃ (φ : freeProP p X →ₜ* freeProP p X) (t : X → freeProP p X),
      (∀ g, g⁻¹ * φ g ∈ pLowerCentralSeries p (freeProP p X) 1) ∧
        (∀ i, t i ∈ (Subgroup.closure {of i}).topologicalClosure) ∧
        (∀ i, t i ∈ pLowerCentralSeries p (freeProP p X) 2) ∧
        (φ r)⁻¹ * ((l₁.map t).prod * w * (l₂.map t).prod) ∈
          pLowerCentralSeries p (freeProP p X) (k + 2) := by
  classical
  induction k with
  | zero =>
    refine ⟨ContinuousMonoidHom.id _, fun _ ↦ 1, fun g ↦ by simp, fun i ↦ one_mem _,
      fun _ ↦ one_mem _, ?_⟩
    have h1 : ∀ l : List X, (l.map fun _ : X ↦ (1 : freeProP p X)).prod = 1 := fun l ↦
      List.prod_eq_one fun x hx ↦ by
        obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx
        rfl
    simpa [h1] using QuotientGroup.eq.mp (gradedMk_eq_gradedMk_iff.mp h)
  | succ k ih =>
    obtain ⟨φ, t, hφ, ht, ht2, hr⟩ := ih fun m hm hmk ↦ hspan m hm (hmk.trans k.le_succ)
    have := Fintype.ofFinite X
    -- `φ r` is again a relator with class `ρ`: `φ` is congruent to the identity modulo `λ_2` on
    -- `λ_1`.
    have hφr : φ r ∈ pLowerCentralSeries p (freeProP p X) 1 :=
      φ.toMonoidHom.map_pLowerCentralSeries_le φ.continuous 1 ⟨r, r.2, rfl⟩
    have hρ : gradedMk p (freeProP p X) 1 ⟨φ r, hφr⟩ = gradedMk p (freeProP p X) 1 r := by
      rw [gradedMk_eq_gradedMk_iff]
      exact (QuotientGroup.eq.mpr
        (inv_mul_apply_mem_pLowerCentralSeries φ.toMonoidHom φ.continuous hφ r.2)).symm
    -- Decompose the class of the deviation `z = (φ r)⁻¹ * T` in `gr_{k+2}(F)` as `δ_ρ(v) + y'`
    -- with `y'` in the tail, and write `y' = Σ_i c_i π^{k+2} ξ_i`.
    set T := (l₁.map t).prod * w * (l₂.map t).prod with hT
    have hz : gradedMk p (freeProP p X) (k + 1 + 1) ⟨(φ r)⁻¹ * T, hr⟩ ∈
        LinearMap.range (basisModificationDelta p X (by omega : 1 ≤ k + 1)
          (gradedMk p (freeProP p X) 1 r)) ⊔
          gradedPowIterSpan p X S (k + 1 + 1) := by
      rw [hspan (k + 1) (by omega) le_rfl]
      exact Submodule.mem_top
    obtain ⟨y, hy, y', hy', hyy'⟩ := Submodule.mem_sup.mp hz
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hy
    have := Fintype.ofFinite S
    obtain ⟨c, hc⟩ := mem_gradedPowIterSpan_iff.mp hy'
    -- The tail coefficients, negated and extended by zero to all generators.
    let P : X → Prop := fun i ↦ i ∈ S
    let c' : X → ZMod p := fun i ↦ if h : P i then -c ⟨i, h⟩ else 0
    let g : X → gradedPiece p (freeProP p X) (k + 1 + 1) := fun i ↦
      gradedPowIter p (freeProP p X) (k + 1 + 1) (gradedMkZero p (freeProP p X) (of i))
    have hc'_zero : ∀ i, ¬ P i → c' i = 0 := fun i hP ↦ dite_eq_right hP
    have hc'_of : ∀ i (hi : P i), c' i = -c ⟨i, hi⟩ := fun i hi ↦ dite_eq_left hi
    have hc' : ∀ i, c' i ≠ 0 → i ∈ l₁ ++ l₂ := fun i hi ↦
      hl i (by_contra fun hP ↦ hi (hc'_zero i hP))
    have hsum : ∑ i, c' i • g i = -y' := by
      have h1 : ∑ i ∈ Finset.univ.filter P, c' i • g i = ∑ i, c' i • g i :=
        Finset.sum_filter_of_ne fun i _ hi ↦
          by_contra fun hP ↦ hi (by rw [hc'_zero i hP, zero_smul])
      have h2 : ∑ i ∈ Finset.univ.filter P, c' i • g i = ∑ j : {i // P i}, c' j • g j :=
        Finset.sum_subtype _
          (fun i ↦ by simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]) _
      rw [← h1, h2, ← hc, ← Finset.sum_neg_distrib]
      exact Finset.sum_equiv (Equiv.refl _) (fun j ↦ by simp) fun j _ ↦ by
        rw [Equiv.refl_apply, hc'_of j j.2]
        exact neg_smul _ _
    -- The tail correction `u_i = x_i^{p^{k+2} c_i}`, an element of `λ_{k+2}` with class
    -- `c_i π^{k+2} ξ_i`.
    have hpow (i : X) :
        of i ^ p ^ (k + 1 + 1) ∈ pLowerCentralSeries p (freeProP p X) (k + 1 + 1) := by
      simpa using
        pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p (of i)) (k + 1 + 1)
    let u : X → freeProP p X := fun i ↦ of i ^ (p ^ (k + 1 + 1) * (c' i).val)
    have hu : ∀ i, u i ∈ pLowerCentralSeries p (freeProP p X) (k + 1 + 1) := fun i ↦ by
      simp only [u, pow_mul]
      exact pow_mem (hpow i) _
    have hu_class : ∀ i, gradedMk p (freeProP p X) (k + 1 + 1) ⟨u i, hu i⟩ = c' i • g i := by
      intro i
      have heq : (⟨u i, hu i⟩ : pLowerCentralSeries p (freeProP p X) (k + 1 + 1)) =
          ⟨_, hpow i⟩ ^ (c' i).val :=
        Subtype.ext (by simp [u, pow_mul])
      rw [heq, gradedMk_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
      simp only [g, gradedPowIter_gradedMkZero]
    have humem : ∀ l : List X, (l.map u).prod ∈ pLowerCentralSeries p (freeProP p X) (k + 1 + 1) :=
      fun l ↦ list_prod_mem fun x hx ↦ by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact hu i
    have hU_class : ∀ l : List X,
        gradedMk p (freeProP p X) (k + 1 + 1) ⟨(l.map u).prod, humem l⟩ =
          (l.map fun i ↦ c' i • g i).sum := by
      intro l
      induction l with
      | nil => exact gradedMk_one _
      | cons a l ihl =>
        have hcons : (⟨((a :: l).map u).prod, humem (a :: l)⟩ :
            pLowerCentralSeries p (freeProP p X) (k + 1 + 1)) =
              ⟨u a, hu a⟩ * ⟨(l.map u).prod, humem l⟩ :=
          Subtype.ext (by simp [List.prod_cons])
        rw [hcons, gradedMk_mul, ihl, hu_class, List.map_cons, List.sum_cons]
    have hU : gradedMk p (freeProP p X) (k + 1 + 1) ⟨((l₁ ++ l₂).map u).prod, humem _⟩ = -y' := by
      rw [hU_class, ← List.sum_toFinset _ hnd, ← hsum]
      exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ by
        rw [of_not_not fun h ↦ hi (List.mem_toFinset.mpr (hc' i h)), zero_smul]
    -- Lift `v` to modifications `ω_i ∈ λ_{k+1}` and modify the basis by them.
    choose ω hω using fun i ↦ gradedMk_surjective (k + 1) (v i)
    have hd : (φ r)⁻¹ * basisModification ω (φ r) ∈
        pLowerCentralSeries p (freeProP p X) (k + 1 + 1) :=
      inv_mul_apply_mem_pLowerCentralSeries (basisModification ω).toMonoidHom
        (basisModification ω).continuous (inv_mul_basisModification_mem_pLowerCentralSeries ω) hφr
    -- The key identity in `gr_{k+2}(F)`: the class of `z * U` is the class of the deviation `d`
    -- of the basis modification, both being `δ_ρ(v)`.
    have hkey : gradedMk p (freeProP p X) (k + 1 + 1)
        ⟨((φ r)⁻¹ * T) * ((l₁ ++ l₂).map u).prod, mul_mem hr (humem _)⟩ =
          gradedMk p (freeProP p X) (k + 1 + 1) ⟨(φ r)⁻¹ * basisModification ω (φ r), hd⟩ := by
      have h1 := gradedMk_inv_mul_basisModification (le_add_self : 1 ≤ k + 1) ω ⟨φ r, hφr⟩
      have hωv : (fun i ↦ gradedMk p (freeProP p X) (k + 1) (ω i)) = v := funext hω
      rw [hρ, hωv] at h1
      have hzU : (⟨((φ r)⁻¹ * T) * ((l₁ ++ l₂).map u).prod, mul_mem hr (humem _)⟩ :
          pLowerCentralSeries p (freeProP p X) (k + 1 + 1)) =
            ⟨(φ r)⁻¹ * T, hr⟩ * ⟨_, humem (l₁ ++ l₂)⟩ := rfl
      rw [hzU, gradedMk_mul, hU, ← hyy', h1, add_neg_cancel_right]
    refine ⟨(basisModification ω).comp φ, fun i ↦ t i * u i, fun g ↦ ?_, fun i ↦ ?_,
      fun i ↦ ?_, ?_⟩
    · have h2 : (φ g)⁻¹ * basisModification ω (φ g) ∈ pLowerCentralSeries p (freeProP p X) 1 :=
        pLowerCentralSeries_antitone (by omega)
          (inv_mul_basisModification_mem_pLowerCentralSeries ω (φ g))
      have := mul_mem (hφ g) h2
      rwa [mul_assoc, mul_inv_cancel_left] at this
    · exact mul_mem (ht i) (pow_mem (le_topologicalClosure _
        (subset_closure (Set.mem_singleton _))) _)
    · exact mul_mem (ht2 i) (pLowerCentralSeries_antitone (by omega) (hu i))
    · -- The computation modulo `λ_{k+3}`, where the classes of the tail corrections are central.
      refine (QuotientGroup.eq_one_iff _).mp ?_
      have hcen : ∀ i, ((u i : freeProP p X) :
          freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1)) ∈
            Submonoid.center _ := fun i ↦ Submonoid.mem_center_iff.mpr fun q ↦ by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        exact (commute_mk_of_mem_pLowerCentralSeries (hu i) g).eq
      have hprod : ∀ l : List X, (((l.map fun i ↦ t i * u i).prod : freeProP p X) :
          freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1)) =
            ((l.map t).prod : freeProP p X ⧸ _) * ((l.map u).prod : freeProP p X ⧸ _) := by
        intro l
        rw [← QuotientGroup.mk'_apply, map_list_prod, List.map_map, ← QuotientGroup.mk'_apply,
          map_list_prod, List.map_map, ← QuotientGroup.mk'_apply, map_list_prod, List.map_map]
        simpa [Function.comp_def] using
          List.prod_map_mul_of_mem_center l (fun i ↦ ((t i : freeProP p X) :
            freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1))) _
            fun i _ ↦ hcen i
      have hUcen : ∀ l : List X, (((l.map u).prod : freeProP p X) :
          freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1)) ∈
            Submonoid.center _ := fun l ↦ by
        rw [← QuotientGroup.mk'_apply, map_list_prod, List.map_map]
        exact Submonoid.list_prod_mem _ fun x hx ↦ by
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
          exact hcen i
      have hkey' := gradedMk_eq_gradedMk_iff.mp hkey
      simp only [hT, QuotientGroup.mk_mul, QuotientGroup.mk_inv, List.map_append,
        List.prod_append] at hkey'
      set A := ((φ r : freeProP p X) :
        freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1))
      set W := ((w : freeProP p X) :
        freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1))
      set P₁ := (((l₁.map t).prod : freeProP p X) :
        freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1))
      set P₂ := (((l₂.map t).prod : freeProP p X) :
        freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1))
      set U₁ := (((l₁.map u).prod : freeProP p X) :
        freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1))
      set U₂ := (((l₂.map u).prod : freeProP p X) :
        freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1))
      -- The class of the moved relator `θ (φ r)`, from the key identity.
      have hD : ((basisModification ω (φ r) : freeProP p X) :
          freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1)) =
            P₁ * W * P₂ * U₁ * U₂ := by
        have := congrArg (A * ·) hkey'
        simpa only [← mul_assoc, mul_inv_cancel, one_mul] using this.symm
      have e₁ : ∀ q, q * U₁ = U₁ * q := Submonoid.mem_center_iff.mp (hUcen l₁)
      simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, hprod, hD, inv_mul_eq_one]
      calc P₁ * W * P₂ * U₁ * U₂ = P₁ * (W * P₂ * U₁) * U₂ := by simp only [mul_assoc]
        _ = P₁ * (U₁ * (W * P₂)) * U₂ := by rw [e₁]
        _ = P₁ * U₁ * W * (P₂ * U₂) := by simp only [mul_assoc]

/-- **The successive-approximation theorem with tails.** Let `r, w ∈ λ_1(F)` be relators of the
free pro-`p` group `F` on a finite linearly ordered type with the same class `ρ ∈ gr_1(F)`, let
`S` be a set of generators and `l₁, l₂` disjoint duplicate-free lists of generators containing
`S`, and suppose `gr_{m+1}(F) = Im δ_ρ + ⟨π^{m+1} ξ_i : i ∈ S⟩` for every `m ≥ 1`. Then a
continuous automorphism `e` of `F` carries `r` to `(∏_{i ∈ l₁} t_i) * w * (∏_{i ∈ l₂} t_i)` for
tail elements `t_i` of the closed procyclic subgroups `⟨x_i⟩`, all lying in `λ_2(F)`. -/
theorem exists_continuousMulEquiv_apply_eq_of_range_sup_gradedPowIterSpan_eq_top
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w) (S : Set X)
    (l₁ l₂ : List X) (hnd : (l₁ ++ l₂).Nodup) (hl : ∀ i ∈ S, i ∈ l₁ ++ l₂)
    (hspan : ∀ m (hm : 1 ≤ m),
      LinearMap.range (basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)) ⊔
        gradedPowIterSpan p X S (m + 1) = ⊤) :
    ∃ (e : freeProP p X ≃ₜ* freeProP p X) (t : X → freeProP p X),
      (∀ i, t i ∈ (Subgroup.closure {of i}).topologicalClosure) ∧
        (∀ i, t i ∈ pLowerCentralSeries p (freeProP p X) 2) ∧
        e r = (l₁.map t).prod * w * (l₂.map t).prod := by
  have hp : p.Prime := Fact.out
  have hfg := isTopologicallyFinitelyGenerated_freeProP p X
  have hP := isProP_freeProP p X
  have : ∀ k, DiscreteTopology (freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k) :=
    fun k ↦ QuotientGroup.discreteTopology (hfg.isOpen_pLowerCentralSeries hp k)
  -- The closed subgroup in which the tail of the generator `x_i` lives.
  let H (i : X) : Subgroup (freeProP p X) :=
    (Subgroup.closure {of i}).topologicalClosure ⊓ pLowerCentralSeries p (freeProP p X) 2
  have hH (i : X) : IsClosed (H i : Set (freeProP p X)) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_topologicalClosure _).inter (isClosed_pLowerCentralSeries 2)
  have hmkT : ∀ (k : ℕ) (t : X → freeProP p X),
      (((l₁.map t).prod * w * (l₂.map t).prod : freeProP p X) :
        freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k) =
      (l₁.map fun i ↦ ((t i : freeProP p X) : freeProP p X ⧸ _)).prod *
        (w : freeProP p X ⧸ _) *
        (l₂.map fun i ↦ ((t i : freeProP p X) : freeProP p X ⧸ _)).prod := fun k t ↦ by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← QuotientGroup.mk'_apply, map_list_prod,
      List.map_map,
      ← QuotientGroup.mk'_apply (pLowerCentralSeries p (freeProP p X) k) (l₂.map t).prod,
      map_list_prod, List.map_map]
    rfl
  -- The level-`k` comparison data: surjective endomorphisms of `F ⧸ λ_k` together with the classes
  -- of the tail elements, carrying the class of `r` to the class of the tail word.
  let D (k : ℕ) : Type u :=
    {s : (freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k →ₜ*
          freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k) ×
        (X → freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k) //
      Function.Surjective s.1 ∧
        (∀ i, s.2 i ∈ (H i).map (QuotientGroup.mk' (pLowerCentralSeries p (freeProP p X) k))) ∧
        s.1 (r : freeProP p X) = (l₁.map s.2).prod * (w : freeProP p X) * (l₂.map s.2).prod}
  have : ∀ k, Finite (D k) := fun k ↦ by
    have := hfg.finite_quotient_pLowerCentralSeries hp k
    exact Finite.of_injective (fun s : D k ↦ (⇑s.1.1, s.1.2)) fun s s' hss' ↦ Subtype.ext
      (Prod.ext (DFunLike.coe_injective (Prod.ext_iff.mp hss').1) (Prod.ext_iff.mp hss').2)
  -- Each level is nonempty, by the finite approximations.
  have : ∀ k, Nonempty (D k) := fun k ↦ by
    obtain ⟨φ, t, hφ, ht, ht2, hr⟩ :=
      exists_continuousMonoidHom_inv_mul_apply_mem_of_range_sup_gradedPowIterSpan_eq_top r w h S
        l₁ l₂ hnd hl k fun m hm _ ↦ hspan m hm
    rw [pLowerCentralSeries_one_eq_proPFrattini hp] at hφ
    have hsurj : Function.Surjective φ :=
      hP.surjective_of_forall_inv_mul_mem_proPFrattini (φ := φ.toMonoidHom) φ.continuous hφ
    have hle : pLowerCentralSeries p (freeProP p X) k ≤
        (pLowerCentralSeries p (freeProP p X) k).comap φ.toMonoidHom :=
      Subgroup.map_le_iff_le_comap.mp (φ.toMonoidHom.map_pLowerCentralSeries_le φ.continuous k)
    refine ⟨⟨(⟨QuotientGroup.map _ _ φ.toMonoidHom hle, continuous_of_discreteTopology⟩,
      fun i ↦ ((t i : freeProP p X) : freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k)),
      QuotientGroup.map_surjective_of_surjective _ _ _ (QuotientGroup.mk_surjective.comp hsurj) hle,
      fun i ↦ ⟨t i, ⟨ht i, ht2 i⟩, rfl⟩, ?_⟩⟩
    rw [ContinuousMonoidHom.coe_mk, QuotientGroup.map_mk, ← hmkT]
    exact QuotientGroup.eq.mpr (pLowerCentralSeries_antitone (by omega : k ≤ k + 2) hr)
  let C : PLowerCentralSeriesComparison p (freeProP p X) (freeProP p X) D :=
    { map := fun _ s ↦ s.1.1
      map_surjective := fun _ s ↦ s.2.1
      bond := fun k s ↦ ⟨(s.1.1.pLowerCentralSeriesDesc,
          fun i ↦ QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k) (s.1.2 i)),
        s.1.1.pLowerCentralSeriesDesc_surjective s.2.1, fun i ↦ by
          obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp (s.2.2.1 i)
          refine ⟨x, hx, ?_⟩
          dsimp only
          rw [← hxs, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mapOfLE_mk], by
          dsimp only
          rw [ContinuousMonoidHom.pLowerCentralSeriesDesc_mk, s.2.2.2, map_mul, map_mul,
            map_list_prod, map_list_prod, List.map_map, List.map_map, QuotientGroup.mapOfLE_mk]
          rfl⟩
      commutes := fun _ s x ↦ (s.1.1.pLowerCentralSeriesDesc_mapOfLE x).symm }
  obtain ⟨s, e, hs, he, -, -⟩ := C.exists_continuousMulEquiv_preserving hP hfg hp
    (fun _ : Unit ↦ (1 : freeProP p X)) (fun _ ↦ 1) (1 : freeProP p X →ₜ* freeProP p X) 1
    (fun _ _ _ ↦ by simp) (fun _ ↦ ⟨0, fun _ _ _ _ ↦ by simp⟩)
  -- The tail elements, recovered from the compatible sequence of their classes.
  have hcompat (i : X) (k : ℕ) (g : freeProP p X)
      (hg : (g : freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) (k + 1)) =
        (s (k + 1)).1.2 i) :
      (g : freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k) = (s k).1.2 i := by
    rw [← hs k]
    exact (QuotientGroup.mapOfLE_mk (pLowerCentralSeries_succ_le k) g).symm.trans
      (congrArg _ hg)
  choose t ht using fun i ↦
    (hP.existsUnique_forall_mk_eq_pLowerCentralSeries hp (fun k ↦ (s k).1.2 i) (hcompat i)).exists
  have htH (i : X) : t i ∈ H i :=
    hP.mem_of_forall_mk_mem_map_pLowerCentralSeries hp (hH i) fun k ↦
      (ht i k).symm ▸ (s k).2.2.1 i
  -- At each level `k`, the classes of the recovered tail elements are the tail classes carried in
  -- the comparison data, as functions on the generators; this is the form in which they enter the
  -- level-`k` equation of the data.
  have hts (k : ℕ) :
      (fun i ↦ ((t i : freeProP p X) : freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k)) =
        (s k).1.2 :=
    funext fun i ↦ ht i k
  refine ⟨e, t, fun i ↦ (Subgroup.mem_inf.mp (htH i)).1, fun i ↦ (Subgroup.mem_inf.mp (htH i)).2,
    eq_of_forall_mk_eq_of_iInf_eq_bot (hP.iInf_pLowerCentralSeries_eq_bot hp) fun k ↦ ?_⟩
  rw [hmkT, hts k]
  exact (he k r).trans (s k).2.2.2

end TauCeti.freeProP
