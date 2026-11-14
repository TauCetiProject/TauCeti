/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Unimodular
public import TauCeti.RingTheory.LocalRing.Basic

/-!
# Bass stable range of a ring

A row `a : Fin n → R` over a possibly noncommutative ring `R` is unimodular when
`Module.IsUnimodular R a` holds for the left `R`-module `Fin n → R`: some `R`-linear functional
takes the value `1` at `a`, equivalently `∑ i, a i * b i = 1` for some `b : Fin n → R`, so the
entries of `a` generate `R` as a right ideal.

A ring `R` has **Bass stable range at most `s`**, written `TauCeti.HasStableRangeLE R s`, when
every unimodular `(s + 1)`-row `(a₀, …, aₛ)` can be shortened to a unimodular `s`-row
`(aᵢ + aₛ * cᵢ)ᵢ < s`. This condition controls elementary row and column reduction of invertible
matrices of finite size: over a ring of stable range at most `s`, `GLₙ(R)` surjects onto `K₁(R)`
for `n ≥ s`, and `GLₙ(R) / Eₙ(R) ≃* K₁(R)` for `n ≥ s + 1`.

This file develops the ring-theoretic properties of `HasStableRangeLE`:
* Only subsingleton rings have stable range at most `0`, while every possibly noncommutative local
  ring (in particular every division ring and field) has stable range at most `1`.
* **Vaserstein's first theorem:** `HasStableRangeLE R s` allows shortening the final coordinate of
  a unimodular row `(a, d)` on `ι ⊕ Unit` into any chosen finite subset of `ι` of cardinality at
  least `s`. Consequently `HasStableRangeLE R s` is monotone in `s` and equivalent to shortening
  all unimodular `(m + 1)`-rows of length `m ≥ s`.
* Passage along surjective ring homomorphisms, invariance under ring equivalence, and compatibility
  with finite products of rings.
* **Vaserstein's second theorem:** `HasStableRangeLE Rᵐᵒᵖ s ↔ HasStableRangeLE R s`, so left and
  right stable range agree for every ring.

## Main definitions

* `TauCeti.HasStableRangeLE`: Bass stable range of `R` is at most `s`.

## Main results

* `TauCeti.hasStableRangeLE_zero_iff`: `HasStableRangeLE R 0 ↔ Subsingleton R`.
* `TauCeti.hasStableRangeLE_one_of_isLocalRing`: a local ring has stable range at most `1`.
* `TauCeti.HasStableRangeLE.exists_isUnimodular_add_mul_of_subset`: shortening into any finite
  subset of cardinality at least `s`.
* `TauCeti.hasStableRangeLE_iff_forall_le`: equivalence with shortening all rows of length at least
  `s + 1` (Vaserstein).
* `TauCeti.HasStableRangeLE.mono`: monotonicity in the bound `s`.
* `TauCeti.HasStableRangeLE.of_surjective` and `RingEquiv.hasStableRangeLE_iff`: quotient
  monotonicity and ring-isomorphism invariance.
* `TauCeti.hasStableRangeLE_prod_iff`: stable range of a product ring `R × S`.
* `TauCeti.hasStableRangeLE_mop_iff`: `HasStableRangeLE Rᵐᵒᵖ s ↔ HasStableRangeLE R s`
  (Vaserstein).

## References

* H. Bass, *Algebraic K-Theory*, W. A. Benjamin (1968), Chapter V, §3.
* L. N. Vaserstein, *Stable rank of rings and dimensionality of topological spaces*, Functional
  Analysis and Its Applications 5 (1971), 102–110, Theorems 1 and 2.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, Exercise 1.5.
-/

public section

universe u

namespace TauCeti

/-- Bass stable range at most `s`: every unimodular row `(a₀, …, aₛ)` of `Rˢ⁺¹` can be shortened
to a unimodular row `(aᵢ + aₛ cᵢ)ᵢ<ₛ`. Unimodular is Mathlib's `Module.IsUnimodular` for the left
module `Fin n → R`: some linear functional takes the value `1`, that is `∑ aᵢ bᵢ = 1` for some
`bᵢ`. -/
def HasStableRangeLE (R : Type u) [Ring R] (s : ℕ) : Prop :=
  ∀ a : Fin (s + 1) → R, Module.IsUnimodular R a →
    ∃ c : Fin s → R, Module.IsUnimodular R (fun i ↦ a (Fin.castSucc i) + a (Fin.last s) * c i)

/-- Unfolded characterization of `TauCeti.HasStableRangeLE`. -/
theorem hasStableRangeLE_def (R : Type u) [Ring R] (s : ℕ) :
    HasStableRangeLE R s ↔
      ∀ a : Fin (s + 1) → R, Module.IsUnimodular R a →
        ∃ c : Fin s → R,
          Module.IsUnimodular R (fun i ↦ a (Fin.castSucc i) + a (Fin.last s) * c i) :=
  (Iff.rfl)

/-- Explicit coordinate-sum characterization of `TauCeti.HasStableRangeLE`: whenever
`∑ i, a i * b i = 1`, there exist `c, d : Fin s → R` with
`∑ i, (a (Fin.castSucc i) + a (Fin.last s) * c i) * d i = 1`. -/
theorem hasStableRangeLE_iff_exists_sum_eq_one {R : Type*} [Ring R] {s : ℕ} :
    HasStableRangeLE R s ↔
      ∀ a b : Fin (s + 1) → R, ∑ i, a i * b i = 1 →
        ∃ c d : Fin s → R,
          ∑ i, (a (Fin.castSucc i) + a (Fin.last s) * c i) * d i = 1 := by
  rw [hasStableRangeLE_def]
  constructor
  · intro h a b hab
    obtain ⟨c, hc⟩ := h a (TauCeti.Module.isUnimodular_pi_iff.mpr ⟨b, hab⟩)
    obtain ⟨d, hd⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
    exact ⟨c, d, hd⟩
  · intro h a ha
    obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp ha
    obtain ⟨c, d, hcd⟩ := h a b hb
    exact ⟨c, TauCeti.Module.isUnimodular_pi_iff.mpr ⟨d, hcd⟩⟩

/-! ## Zero, subsingleton, and local rings -/

/-- Every subsingleton ring has stable range at most `s` for every `s`. -/
theorem HasStableRangeLE.of_subsingleton (R : Type*) [Ring R] [Subsingleton R] (s : ℕ) :
    HasStableRangeLE R s :=
  fun _ _ ↦ ⟨0, Module.isUnimodular_of_apply_eq_one (f := 0) (Subsingleton.elim _ _)⟩

/-- A ring has stable range at most `0` if and only if it is subsingleton: shortening the
unimodular `1`-row `(1)` produces the zero vector of `Fin 0 → R`, forcing `0 = 1`. -/
@[simp]
theorem hasStableRangeLE_zero_iff {R : Type*} [Ring R] :
    HasStableRangeLE R 0 ↔ Subsingleton R := by
  refine ⟨fun h ↦ ?_, fun _ ↦ HasStableRangeLE.of_subsingleton R 0⟩
  have h1 : Module.IsUnimodular R (fun _ : Fin 1 ↦ (1 : R)) :=
    IsUnit.isUnimodular_pi (i := 0) isUnit_one
  obtain ⟨c, hc⟩ := h _ h1
  obtain ⟨d, hd⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  exact subsingleton_of_zero_eq_one (by simpa using hd)

/-- Every possibly noncommutative local ring (in particular every division ring and field) has
stable range at most `1`: in a unimodular pair `(a₀, a₁)` one coordinate is a unit, so `c = 0`
works when `a₀` is a unit and `c = 1` works when `a₀` is a nonunit and `a₁` is a unit. -/
theorem hasStableRangeLE_one_of_isLocalRing (R : Type*) [Ring R] [IsLocalRing R] :
    HasStableRangeLE R 1 := by
  intro a ha
  obtain ⟨i, hi⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.mp ha
  by_cases ha0 : IsUnit (a 0)
  · refine ⟨0, IsUnit.isUnimodular_pi (i := 0) ?_⟩
    simpa using ha0
  · have hi1 : i = 1 := by fin_cases i <;> simp_all
    have ha1 : IsUnit (a 1) := hi1 ▸ hi
    refine ⟨fun _ ↦ 1, IsUnit.isUnimodular_pi (i := 0) ?_⟩
    have hu : IsUnit (a 1 + a 0) := isUnit_add_of_isUnit_of_not_isUnit ha1 ha0
    simpa [add_comm] using hu

/-! ## Subset shortening and longer rows (Vaserstein's first theorem) -/

/-- Zero out coordinates in `T` and extend by `0` on `Unit`. -/
private def sumElimComplLinearMap {R ι : Type*} [Semiring R] (T : Finset ι)
    [DecidablePred (· ∈ T)] : (ι → R) →ₗ[R] (ι ⊕ Unit → R) where
  toFun x := Sum.elim (fun i ↦ if i ∈ T then 0 else x i) 0
  map_add' x y := by
    ext (i | ⟨⟩)
    · by_cases hi : i ∈ T <;> simp [hi]
    · simp
  map_smul' r x := by
    ext (i | ⟨⟩)
    · by_cases hi : i ∈ T <;> simp [hi]
    · simp

private theorem sumElim_eq_sum_single_add_compl {R ι : Type*} [Semiring R] [DecidableEq ι]
    (T : Finset ι) {s : ℕ} (e : Fin s ≃ T) (a : ι → R) (d : R) :
    Sum.elim a (fun _ : Unit ↦ d) =
      (∑ k : Fin s, a (e k) • Pi.single (Sum.inl (e k : ι)) (1 : R)) +
        sumElimComplLinearMap T a + d • Pi.single (Sum.inr ()) (1 : R) := by
  ext (i | ⟨⟩)
  · simp only [Sum.elim_inl, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
      Sum.inl.injEq, reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_ite, mul_one, mul_zero, add_zero,
      sumElimComplLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hi : i ∈ T
    · simp only [hi, ↓reduceIte, add_zero]
      rw [← e.symm.sum_comp (fun k ↦ if i = (e k : ι) then a (e k) else 0),
        Fintype.sum_eq_single ⟨i, hi⟩]
      · simp
      · intro x hx
        simp only [ite_eq_right_iff]
        exact fun h ↦ (hx (Subtype.ext (by simpa using h.symm))).elim
    · have hzero : (∑ k : Fin s, if i = (e k : ι) then a (e k) else 0) = 0 :=
        Finset.sum_eq_zero fun k _ ↦ by
          have hne : i ≠ (e k : ι) := fun h ↦ hi (h ▸ (e k).2)
          simp [hne]
      simp [hi, hzero]
  · simp [sumElimComplLinearMap]

/-- **Subset shortening (Vaserstein).** Over a ring of stable range at most `s`, a unimodular
vector `(a, d)` on `ι ⊕ Unit` can be shortened into `a` using a multiplier supported on any
chosen finite subset `S : Finset ι` of cardinality at least `s`. -/
theorem HasStableRangeLE.exists_isUnimodular_add_mul_of_subset {R ι : Type*} [Ring R] {s : ℕ}
    (hR : HasStableRangeLE R s) {S : Finset ι} (hS : s ≤ S.card) {a : ι → R} {d : R}
    (ha : Module.IsUnimodular R (Sum.elim a (fun _ : Unit ↦ d))) :
    ∃ c : ι → R, (∀ i ∉ S, c i = 0) ∧ Module.IsUnimodular R (fun i ↦ a i + d * c i) := by
  classical
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS
  let e : Fin s ≃ T := (Fintype.equivFinOfCardEq (by simp [hTcard])).symm
  obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp ha
  let bLast : R := f (Pi.single (Sum.inr ()) 1)
  let r₀ : R := f (sumElimComplLinearMap T a)
  have hab' : ∑ i : Fin (s + 1),
      Fin.snoc (α := fun _ ↦ R) (fun k ↦ a (e k)) (r₀ + d * bLast) i *
        Fin.snoc (α := fun _ ↦ R) (fun k ↦ f (Pi.single (Sum.inl (e k : ι)) 1)) 1 i = 1 := by
    refine Eq.trans ?_ hf
    rw [Fin.sum_univ_castSucc, sumElim_eq_sum_single_add_compl T e a d, map_add, map_add, map_sum,
      map_smul]
    simp [r₀, bLast, smul_eq_mul, add_assoc]
  obtain ⟨t, u, htu⟩ := hasStableRangeLE_iff_exists_sum_eq_one.mp hR _ _ hab'
  have htu' : ∑ k : Fin s, (a (e k) + (r₀ + d * bLast) * t k) * u k = 1 := by simpa using htu
  let tu : R := ∑ k : Fin s, t k * u k
  let c : ι → R := fun i ↦ if hi : i ∈ T then bLast * t (e.symm ⟨i, hi⟩) else 0
  let φ : (ι → R) →ₗ[R] R :=
    (∑ k : Fin s, (LinearMap.mulRight R (u k)).comp (LinearMap.proj (e k : ι))) +
      (LinearMap.mulRight R tu).comp (f.comp (sumElimComplLinearMap T))
  have hsupp : ∀ i ∉ S, c i = 0 := fun i hiS ↦ by
    have hiT : i ∉ T := fun hiT ↦ hiS (hTS hiT)
    simp [c, hiT]
  refine ⟨c, hsupp, Module.isUnimodular_of_apply_eq_one (f := φ) ?_⟩
  have hcompl : sumElimComplLinearMap T (fun i ↦ a i + d * c i) = sumElimComplLinearMap T a := by
    ext (i | ⟨⟩)
    · by_cases hi : i ∈ T <;> simp [sumElimComplLinearMap, c, hi]
    · simp [sumElimComplLinearMap]
  have honT : (∑ k : Fin s, (a (e k) + d * c (e k)) * u k) =
      ∑ k : Fin s, (a (e k) + d * (bLast * t k)) * u k :=
    Finset.sum_congr rfl fun k _ ↦ by simp [c]
  simp only [φ, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.mulRight_apply, hcompl, honT, ← htu']
  simp only [r₀, tu, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  abel

/-- Over a ring of stable range at most `s`, any unimodular vector `(a, d)` on `ι ⊕ Unit` with
`s ≤ Fintype.card ι` can be shortened into `a`. -/
theorem HasStableRangeLE.exists_isUnimodular_add_mul {R ι : Type*} [Ring R] [Fintype ι] {s : ℕ}
    (hR : HasStableRangeLE R s) (hι : s ≤ Fintype.card ι) {a : ι → R} {d : R}
    (ha : Module.IsUnimodular R (Sum.elim a (fun _ : Unit ↦ d))) :
    ∃ c : ι → R, Module.IsUnimodular R (fun i ↦ a i + d * c i) := by
  obtain ⟨c, -, hc⟩ := hR.exists_isUnimodular_add_mul_of_subset (S := Finset.univ)
    (by simpa using hι) ha
  exact ⟨c, hc⟩

/-- **Vaserstein's first theorem:** `HasStableRangeLE R s` holds if and only if every unimodular
`(m + 1)`-row of length `m ≥ s` can be shortened to a unimodular `m`-row. -/
theorem hasStableRangeLE_iff_forall_le {R : Type*} [Ring R] {s : ℕ} :
    HasStableRangeLE R s ↔
      ∀ ⦃m : ℕ⦄, s ≤ m → ∀ a : Fin (m + 1) → R, Module.IsUnimodular R a →
        ∃ c : Fin m → R,
          Module.IsUnimodular R (fun i ↦ a (Fin.castSucc i) + a (Fin.last m) * c i) := by
  refine ⟨fun hR m hm a ha ↦ ?_, fun h a ha ↦ h le_rfl a ha⟩
  let φ : Fin m ⊕ Unit ≃ Fin (m + 1) :=
    { toFun := Sum.elim Fin.castSucc (fun _ ↦ Fin.last m)
      invFun := Fin.lastCases (Sum.inr ()) Sum.inl
      left_inv := fun x ↦ by rcases x with i | ⟨⟩ <;> simp
      right_inv := fun x ↦ Fin.lastCases (by simp) (fun i ↦ by simp) x }
  have ha' : Module.IsUnimodular R (Sum.elim (fun i ↦ a (Fin.castSucc i))
      (fun _ : Unit ↦ a (Fin.last m))) := by
    have hcomp : Sum.elim (fun i ↦ a (Fin.castSucc i)) (fun _ : Unit ↦ a (Fin.last m)) =
        (LinearEquiv.funCongrLeft R R φ) a := by
      ext x
      rcases x with i | ⟨⟩ <;> rfl
    rw [hcomp, LinearEquiv.isUnimodular_apply_iff]
    exact ha
  exact hR.exists_isUnimodular_add_mul (by simpa using hm) ha'

/-- `TauCeti.HasStableRangeLE` is monotone in the bound `s`. -/
theorem HasStableRangeLE.mono {R : Type*} [Ring R] {s t : ℕ} (hR : HasStableRangeLE R s)
    (hst : s ≤ t) : HasStableRangeLE R t :=
  fun a ha ↦ hasStableRangeLE_iff_forall_le.mp hR hst a ha

/-! ## Surjective homomorphisms, ring equivalences, and products -/

/-- Stable range does not increase under a surjective ring homomorphism: a unimodular `(s + 1)`-row
in `S` lifts to a unimodular `(s + 2)`-row in `R` by appending the defect `1 - ∑ aᵢ bᵢ ∈ ker f`,
shortens first to a unimodular `(s + 1)`-row lifting the given row, and then shortens to `s`. -/
theorem HasStableRangeLE.of_surjective {R S : Type*} [Ring R] [Ring S] {s : ℕ}
    (hR : HasStableRangeLE R s) {f : R →+* S} (hf : Function.Surjective f) :
    HasStableRangeLE S s := by
  refine hasStableRangeLE_iff_exists_sum_eq_one.mpr fun as bs hab ↦ ?_
  choose a ha using fun i ↦ hf (as i)
  choose b hb using fun i ↦ hf (bs i)
  set k : R := 1 - ∑ i : Fin (s + 1), a i * b i
  have hfk : f k = 0 := by simp [k, map_sum, ha, hb, hab]
  have hunim : Module.IsUnimodular R (Sum.elim a (fun _ : Unit ↦ k)) := by
    refine TauCeti.Module.isUnimodular_pi_iff.mpr ⟨Sum.elim b (fun _ ↦ 1), ?_⟩
    rw [Fintype.sum_sum_type]
    simp [k]
  -- Shorten `k ∈ ker f` into `a` to obtain a genuine unimodular lift of `as`.
  obtain ⟨t, ht⟩ := hR.exists_isUnimodular_add_mul (by simp : s ≤ Fintype.card (Fin (s + 1))) hunim
  obtain ⟨c, hc⟩ := hR (fun i ↦ a i + k * t i) ht
  obtain ⟨d, hd⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  refine ⟨fun i ↦ f (c i), fun i ↦ f (d i), ?_⟩
  have hfd := congrArg f hd
  simpa [map_sum, ha, hfk] using hfd

/-- Stable range of a product ring `R × S` is the maximum of the stable ranges of `R` and `S`. -/
@[simp]
theorem hasStableRangeLE_prod_iff {R S : Type*} [Ring R] [Ring S] {s : ℕ} :
    HasStableRangeLE (R × S) s ↔ HasStableRangeLE R s ∧ HasStableRangeLE S s := by
  refine ⟨fun h ↦ ⟨h.of_surjective (f := RingHom.fst R S) Prod.fst_surjective,
    h.of_surjective (f := RingHom.snd R S) Prod.snd_surjective⟩, ?_⟩
  rintro ⟨hR, hS⟩
  refine hasStableRangeLE_iff_exists_sum_eq_one.mpr fun a b hab ↦ ?_
  have hab₁ : ∑ i, (a i).1 * (b i).1 = 1 := by
    simpa [map_sum] using congrArg (RingHom.fst R S) hab
  have hab₂ : ∑ i, (a i).2 * (b i).2 = 1 := by
    simpa [map_sum] using congrArg (RingHom.snd R S) hab
  obtain ⟨c₁, d₁, h₁⟩ := hasStableRangeLE_iff_exists_sum_eq_one.mp hR _ _ hab₁
  obtain ⟨c₂, d₂, h₂⟩ := hasStableRangeLE_iff_exists_sum_eq_one.mp hS _ _ hab₂
  refine ⟨fun i ↦ (c₁ i, c₂ i), fun i ↦ (d₁ i, d₂ i), Prod.ext ?_ ?_⟩
  · exact (map_sum (RingHom.fst R S) _ _).trans h₁
  · exact (map_sum (RingHom.snd R S) _ _).trans h₂

/-! ## Opposite ring (Vaserstein's second theorem) -/

/-- One direction of Vaserstein's second theorem: if `R` has stable range at most `s`, then so
does `Rᵐᵒᵖ`. -/
private theorem hasStableRangeLE_mop_of_hasStableRangeLE {R : Type*} [Ring R] {s : ℕ}
    (hR : HasStableRangeLE R s) : HasStableRangeLE Rᵐᵒᵖ s := by
  refine hasStableRangeLE_iff_exists_sum_eq_one.mpr fun a b hab ↦ ?_
  let x : Fin s → R := fun i ↦ MulOpposite.unop (a (Fin.castSucc i))
  let xs : R := MulOpposite.unop (a (Fin.last s))
  let y : Fin s → R := fun i ↦ MulOpposite.unop (b (Fin.castSucc i))
  let ys : R := MulOpposite.unop (b (Fin.last s))
  have hyx : (∑ i : Fin s, y i * x i) + ys * xs = 1 := by
    have h := congrArg (MulOpposite.opAddEquiv (α := R)).symm hab
    rw [Fin.sum_univ_castSucc] at h
    simpa [x, xs, y, ys, map_sum] using h
  set δ : R := 1 - ∑ i : Fin s, y i * x i
  have hδ : δ = ys * xs := sub_eq_of_eq_add' hyx.symm
  -- `(y₀, …, yₛ₋₁, δ)` is right-unimodular in `R` with witness `(x₀, …, xₛ₋₁, 1)`.
  have hunim : ∑ i : Fin (s + 1),
      Fin.snoc (α := fun _ ↦ R) y δ i * Fin.snoc (α := fun _ ↦ R) x 1 i = 1 := by
    rw [Fin.sum_univ_castSucc]; simp [δ]
  obtain ⟨k, u, hku⟩ := hasStableRangeLE_iff_exists_sum_eq_one.mp hR _ _ hunim
  have hyu : ∑ i : Fin s, y i * u i = 1 - δ * ∑ i : Fin s, k i * u i := by
    refine eq_sub_of_add_eq ?_
    simpa only [Fin.snoc_castSucc, Fin.snoc_last, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc] using hku
  set q : R := ∑ i : Fin s, k i * u i
  set γ : R := 1 - ∑ i : Fin s, k i * x i
  let c : Fin s → R := fun i ↦ u i - x i * q
  let z : Fin s → R := fun i ↦ k i + γ * y i
  have hzx : ∑ i : Fin s, z i * x i = 1 - γ * δ := by
    have hkx : ∑ i : Fin s, k i * x i = 1 - γ := by simp [γ]
    have hyx' : ∑ i : Fin s, y i * x i = 1 - δ := by simp [δ]
    simp only [z, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc, hkx, hyx',
      mul_sub, mul_one]
    abel
  have hzc : ∑ i : Fin s, z i * c i = γ := by
    have hzu : ∑ i : Fin s, z i * u i = q + γ * (1 - δ * q) := by
      simp only [z, q, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc, hyu]
    have hzxq : ∑ i : Fin s, z i * (x i * q) = (1 - γ * δ) * q := by
      simp only [← mul_assoc, ← Finset.sum_mul, hzx]
    simp only [c, mul_sub, Finset.sum_sub_distrib, hzu, hzxq, sub_mul, mul_one, one_mul, mul_assoc]
    abel
  refine ⟨fun i ↦ MulOpposite.op (c i * ys), fun i ↦ MulOpposite.op (z i), ?_⟩
  apply (MulOpposite.opAddEquiv (α := R)).symm.injective
  have hgoal : ∑ i : Fin s, z i * (x i + c i * δ) = 1 := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ← mul_assoc, hzx, hzc,
      sub_add_cancel]
  simpa [x, xs, ys, map_sum, hδ, mul_assoc] using hgoal

/-- **Vaserstein's second theorem:** a ring and its opposite ring have the same Bass stable
range. -/
@[simp]
theorem hasStableRangeLE_mop_iff {R : Type*} [Ring R] {s : ℕ} :
    HasStableRangeLE Rᵐᵒᵖ s ↔ HasStableRangeLE R s := by
  refine ⟨fun h ↦ ?_, hasStableRangeLE_mop_of_hasStableRangeLE⟩
  let unop₂ : Rᵐᵒᵖᵐᵒᵖ →+* R :=
    { toFun := fun x ↦ MulOpposite.unop (MulOpposite.unop x)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact (hasStableRangeLE_mop_of_hasStableRangeLE h).of_surjective (f := unop₂)
    fun r ↦ ⟨MulOpposite.op (MulOpposite.op r), rfl⟩

end TauCeti

namespace RingEquiv

/-- Isomorphic rings have the same Bass stable range. -/
theorem hasStableRangeLE_iff {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) {s : ℕ} :
    TauCeti.HasStableRangeLE R s ↔ TauCeti.HasStableRangeLE S s :=
  ⟨fun h ↦ h.of_surjective (f := e.toRingHom) e.surjective,
    fun h ↦ h.of_surjective (f := e.symm.toRingHom) e.symm.surjective⟩

end RingEquiv
