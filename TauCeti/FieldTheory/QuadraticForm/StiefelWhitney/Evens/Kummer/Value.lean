/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Evens.Kummer.TwistedBoundary
public import TauCeti.RingTheory.Norm.Quadratic

/-!
# The value of the Evens norm on a Kummer class

Let `L = K(x)` be a separable quadratic extension of a field `K` in which `2` is invertible, with
`x² = d ∈ Kˣ`, and let `σ : L → Kˢ` be a `K`-embedding. For `a ∈ Lˣ`, the Evens norm
`N^{Ev}((a)) ∈ H²(G_K, 𝔽₂)` of the Kummer class `(a) ∈ H¹(G_L, 𝔽₂)` is (Kahn, Lemme II.2.1)

```text
N^{Ev}((a)) = (Tr a) ∪ (−d · N a) + (2) ∪ (d)       if Tr a ≠ 0,
N^{Ev}((a)) = (2) ∪ (d)                             if Tr a = 0
```

(`TauCeti.galoisEvens2_kummerClass`, `TauCeti.galoisEvens2_kummerClass_of_trace_eq_zero`).
Both are specializations of Serre's formula `N^{Ev}((a)) = (w₁) ∪ (w₀) + (2) ∪ (d)` for the
values `w₀, w₁` of any orthogonal basis of the twisted trace form `Tr_*⟨a⟩ : y ↦ Tr (a y²)`
(`TauCeti.galoisEvens2_kummerClass_eq_cup_add_cup`), that is
`w₂(Tr_*⟨a⟩) = N^{Ev}((a)) + (2) ∪ (d)`.

The results hold for `K` and `L` in any universe, except
`N^{Ev}((1 + t x)) = (2) ∪ (1 − t² d)` (`TauCeti.galoisEvens2_kummerClass_one_add`), which uses
the Steinberg relation `TauCeti.cup_kummerClass_eq_zero_of_add_eq_one` and so is stated, like it,
for `K L : Type`.

## Main results

* `TauCeti.galoisEvens2_kummerClass_eq_cup_add_cup`: `N^{Ev}((a)) = (w₁) ∪ (w₀) + (2) ∪ (d)` for the
  values `w₀, w₁` of any orthogonal basis of `Tr_*⟨a⟩`.
* `TauCeti.galoisEvens2_kummerClass`: `N^{Ev}((a)) = (Tr a) ∪ (−d · N a) + (2) ∪ (d)` if
  `Tr a ≠ 0`.
* `TauCeti.galoisEvens2_kummerClass_of_trace_eq_zero`: `N^{Ev}((a)) = (2) ∪ (d)` if `Tr a = 0`.
* `TauCeti.galoisEvens2_kummerClass_one_add`: `N^{Ev}((1 + t x)) = (2) ∪ (1 − t² d)`.
* `TauCeti.galoisEvens2_kummerClass_sqrt`: `N^{Ev}((x)) = (2) ∪ (d)`.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, Théorème 1′ and its second proof.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

universe u

section Universe

variable {K : Type u} [Field K] [Invertible (2 : K)] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [Invertible (2 : L)]

/-- **Serre's formula for the Evens norm of a Kummer class** (Serre, Théorème 1′ at `n = 2`):
for an orthogonal basis `y` of the twisted trace form `Tr_*⟨a⟩ : z ↦ Tr (a z²)` whose values
`w_j = Tr (a y_j²)` are units,

```text
N^{Ev}((a)) = (w₁) ∪ (w₀) + (2) ∪ (d),
```

where `d` is the square of a generator `x` of `L = K(x)`. Since `(w₀) ∪ (w₁)` is the second
Stiefel–Whitney class of `⟨w₀, w₁⟩ ≅ Tr_*⟨a⟩`, this is `w₂(Tr_*⟨a⟩) = N^{Ev}((a)) + (2) ∪ (d)`. -/
theorem galoisEvens2_kummerClass_eq_cup_add_cup (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (d : Kˣ) {x : L} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (a : Lˣ) (y : Fin 2 → L)
    (hy : Algebra.trace K L ((a : L) * y 0 * y 1) = 0) (w : Fin 2 → Kˣ)
    (hw : ∀ i, (w i : K) = Algebra.trace K L ((a : L) * y i ^ 2)) :
    galoisEvens K L σ hdeg (kummerClass a) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass (w 1))
          (kummerClass (w 0)) +
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass (unitOfInvertible (2 : K))) (kummerClass d) := by
  -- The Evens norm is the class of `c_{D₁₆} ∘ (ρ_a × ρ_a)`
  -- (`TauCeti.galoisEvens2_kummerClass_eq_pullback`); this cochain is the twisted boundary of the
  -- `Pin⁺` lift of `ρ_a` plus the product of the Kummer characters of `2` and `d`
  -- (`TauCeti.twistedBoundaryF2_kummerIndLift`), and that twisted boundary is cohomologous to the
  -- product of the Kummer characters of `w₁` and `w₀`
  -- (`TauCeti.twistedBoundaryF2_kummerIndLift_cohomologous`).
  -- Choose square roots in `Kˢ` of `σ a`, `2` and the values `w j`, and an `s ∈ G_K ∖ G_L`.
  obtain ⟨r, hr⟩ := IsSepClosed.isSquare (σ (a : L))
  rw [← sq, eq_comm] at hr
  obtain ⟨s, hs⟩ : ∃ s, s ∉ galoisSubgroup K L σ := by
    by_contra! h
    have htop : (galoisSubgroup K L σ).toSubgroup = ⊤ := eq_top_iff.2 fun g _ => h g
    have := galoisSubgroup_index K L σ
    rw [htop, Subgroup.index_top, hdeg] at this
    exact absurd this (by norm_num)
  obtain ⟨r2, hr2⟩ := IsSepClosed.isSquare (2 : SeparableClosure K)
  rw [← sq, eq_comm] at hr2
  choose c hc using fun i => IsSepClosed.isSquare (algebraMap K (SeparableClosure K) (w i))
  simp only [← sq, eq_comm (a := algebraMap K _ _)] at hc
  have hc0 (i : Fin 2) : c i ≠ 0 := by
    intro h
    have := hc i
    rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap K _).injective] at this
    exact (w i).ne_zero this
  have hσx : σ x ^ 2 = algebraMap K (SeparableClosure K) d := by
    rw [← map_pow, hx2, AlgHom.commutes]
  have hr2' : r2 ^ 2 = algebraMap K (SeparableClosure K) (unitOfInvertible (2 : K)) := by
    rw [hr2, val_unitOfInvertible, map_ofNat]
  obtain ⟨ψ, hψ, hδ⟩ := twistedBoundaryF2_kummerIndLift_cohomologous σ hdeg a r hr s hs hr2 y hy c
    (fun i => by rw [hc, hw]) hc0
  rw [galoisEvens2_kummerClass_eq_pullback σ hdeg a r hr s hs,
    kummerClass_eq_homClass (w 1) (c 1) (hc 1), kummerClass_eq_homClass (w 0) (c 0) (hc 0),
    kummerClass_eq_homClass _ r2 hr2', kummerClass_eq_homClass d (σ x) hσx, cup11_homClass,
    cup11_homClass]
  -- In `𝔽₂`, `c_{D₁₆}(ρ_a g, ρ_a h) = δ(ρ'_a)(g, h) + rootSign √2 g · rootSign √d h`, and
  -- `δ(ρ'_a)(g, h) = rootSign c₁ g · rootSign c₀ h + ∂ψ(g, h)`.
  refine f2CocycleClass_eq_add _ _ _ _ _ _ _ _ _ ψ hψ fun g h => ?_
  have hδgh := twistedBoundaryF2_kummerIndLift σ hdeg hx a r hr s hs hr2 g h
  rw [hδ] at hδgh
  simp only [toAdd_kummerCharacter]
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination -hδgh - rootSign r2 g * rootSign (σ x) h * h2

/-- **The Evens norm at a square root of an element of `K`.** If `b ∉ K` and `b² = e ∈ K`, then
`N^{Ev}((b)) = (−t) ∪ (t) + (2) ∪ (d)` for every `t ∈ Kˣ`. -/
private theorem galoisEvens_kummerClass_eq_of_sq_eq (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (d : Kˣ) {x : L} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (b : Lˣ) (e : Kˣ)
    (hb : (b : L) ∉ Set.range (algebraMap K L)) (hb2 : (b : L) ^ 2 = algebraMap K L (e : K))
    (t : Kˣ) :
    galoisEvens K L σ hdeg (kummerClass b) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass (-t))
          (kummerClass t) +
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass (unitOfInvertible (2 : K))) (kummerClass d) := by
  have : Algebra.IsQuadraticExtension K L := ⟨hdeg⟩
  have h4 : (4 : K) ≠ 0 := by
    rw [← two_add_two_eq_four, ← two_mul]
    exact mul_ne_zero (two_ne_zero' K) (two_ne_zero' K)
  have he := e.ne_zero
  -- `Tr_*⟨b⟩` is hyperbolic: for `c = t / (4 e)`, the elements `1 + c b` and `1 − c b` are
  -- orthogonal with values `t` and `−t`.
  set c : K := t / (4 * e) with hc
  -- In the coordinates `(1, b)`, `b (1 + c b) (1 − c b) = (1 − c² e) b` and
  -- `b (1 ± c b)² = ±2 c e + (1 + c² e) b`.
  have htr (u v : K) : Algebra.trace K L (algebraMap K L v + algebraMap K L u * b) = 2 * v :=
    Algebra.IsQuadraticExtension.trace_algebraMap_add_algebraMap_mul_of_sq_eq hb hb2 u v
  refine galoisEvens2_kummerClass_eq_cup_add_cup σ hdeg d hx hx2 b
    ![1 + algebraMap K L c * b, 1 - algebraMap K L c * b] ?_ ![t, -t] fun i => ?_
  · have h : (b : L) * (1 + algebraMap K L c * b) * (1 - algebraMap K L c * b) =
        algebraMap K L 0 + algebraMap K L (1 - c ^ 2 * e) * b := by
      simp only [map_sub, map_mul, map_pow, map_one, map_zero]
      linear_combination (-(algebraMap K L c) ^ 2 * b) * hb2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h, htr, mul_zero]
  · fin_cases i
    · have h : (b : L) * (1 + algebraMap K L c * b) ^ 2 =
          algebraMap K L (2 * c * e) + algebraMap K L (1 + c ^ 2 * e) * b := by
        simp only [map_add, map_mul, map_pow, map_one, map_ofNat]
        linear_combination (2 * algebraMap K L c + algebraMap K L c ^ 2 * b) * hb2
      simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [h, htr, hc]
      field_simp
      ring
    · have h : (b : L) * (1 - algebraMap K L c * b) ^ 2 =
          algebraMap K L (-(2 * c * e)) + algebraMap K L (1 + c ^ 2 * e) * b := by
        simp only [map_add, map_neg, map_mul, map_pow, map_one, map_ofNat]
        linear_combination (-2 * algebraMap K L c + algebraMap K L c ^ 2 * b) * hb2
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h, htr, hc, Units.val_neg]
      field_simp
      ring

/-- **The relation `(−t) ∪ (t) = 0`, from a quadratic extension.** Unlike the library's
`TauCeti.cup_kummerClass_neg_self`, which is stated for `K : Type`, this holds in every universe
in which `K` has a separable quadratic extension. -/
private theorem cup_kummerClass_neg_kummerClass_eq_zero (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (d : Kˣ) {x : L} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (t : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass (-t)) (kummerClass t) =
      0 := by
  -- Compute `N^{Ev}((x))` with the orthogonal bases of values `(t, −t)` and `(1, −1)`.
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx ⟨0, map_zero _⟩
  have h := (galoisEvens_kummerClass_eq_of_sq_eq σ hdeg d hx hx2 (Units.mk0 x hx0) d hx hx2
    t).symm.trans (galoisEvens_kummerClass_eq_of_sq_eq σ hdeg d hx hx2 (Units.mk0 x hx0) d hx hx2 1)
  simpa using h

/-- **The value of the Evens norm on a Kummer class at trace zero** (Kahn, Lemme II.2.1):
if `Tr a = 0`, then `N^{Ev}((a)) = (2) ∪ (d)`. -/
theorem galoisEvens2_kummerClass_of_trace_eq_zero (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (d : Kˣ) {x : L} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (a : Lˣ) (ht : Algebra.trace K L (a : L) = 0) :
    galoisEvens K L σ hdeg (kummerClass a) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass (unitOfInvertible (2 : K))) (kummerClass d) := by
  have : Algebra.IsQuadraticExtension K L := ⟨hdeg⟩
  -- `a² = −N a ∈ K`, so `Tr_*⟨a⟩` has an orthogonal basis with values `1` and `−1`.
  have ha2 : (a : L) ^ 2 = algebraMap K L ((-Units.map (Algebra.norm K : L →* K) a : Kˣ) : K) := by
    rw [Algebra.IsQuadraticExtension.sq_eq_trace_smul_sub_norm K (a : L), ht, zero_smul,
      zero_sub, Units.val_neg, Units.coe_map, map_neg]
  have ha : (a : L) ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, hc⟩
    rw [← hc, Algebra.trace_algebraMap, hdeg, two_nsmul, ← two_mul] at ht
    rcases mul_eq_zero.1 ht with h | rfl
    · exact two_ne_zero' K h
    · exact a.ne_zero (by rw [← hc, map_zero])
  rw [galoisEvens_kummerClass_eq_of_sq_eq σ hdeg d hx hx2 a _ ha ha2 1]
  simp

/-- **The Evens norm of the square root `x` of `d`:** `N^{Ev}((x)) = (2) ∪ (d)`, the trace-zero
case of `TauCeti.galoisEvens2_kummerClass_of_trace_eq_zero` at `a = x`. -/
theorem galoisEvens2_kummerClass_sqrt (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (d : Kˣ) {x : L} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (b : Lˣ) (hb : (b : L) = x) :
    galoisEvens K L σ hdeg (kummerClass b) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass (unitOfInvertible (2 : K))) (kummerClass d) :=
  have : Algebra.IsQuadraticExtension K L := ⟨hdeg⟩
  galoisEvens2_kummerClass_of_trace_eq_zero σ hdeg d hx hx2 b
    (hb ▸ Algebra.IsQuadraticExtension.trace_eq_zero_of_sq_eq hx hx2)

/-- **The value of the Evens norm on a Kummer class** (Kahn, Lemme II.2.1): if `Tr a = t ≠ 0`,
then

```text
N^{Ev}((a)) = (Tr a) ∪ (−d · N a) + (2) ∪ (d).
``` -/
theorem galoisEvens2_kummerClass (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (d : Kˣ) {x : L} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (a : Lˣ) (t : Kˣ)
    (ht : (t : K) = Algebra.trace K L (a : L)) :
    galoisEvens K L σ hdeg (kummerClass a) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass t)
          (kummerClass (-(d * Units.map (Algebra.norm K : L →* K) a))) +
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass (unitOfInvertible (2 : K))) (kummerClass d) := by
  have : Algebra.IsQuadraticExtension K L := ⟨hdeg⟩
  set N := Units.map (Algebra.norm K : L →* K) a with hN
  -- Kahn's basis `(1, x / a)` of `Tr_*⟨a⟩` is orthogonal with values `Tr a` and `d · Tr a / N a`.
  have hy : Algebra.trace K L ((a : L) * ![1, x / a] 0 * ![1, x / a] 1) = 0 := by
    simpa [mul_div_cancel₀ _ a.ne_zero] using
      Algebra.IsQuadraticExtension.trace_eq_zero_of_sq_eq hx hx2
  rw [galoisEvens2_kummerClass_eq_cup_add_cup σ hdeg d hx hx2 a ![1, x / a] hy ![t, d * t * N⁻¹]
    fun i => ?_]
  · -- `d · t / N ≡ (−d · N) · (−t)` modulo squares.
    have hmul : kummerClass (d * t * N⁻¹) = kummerClass (-(d * N)) + kummerClass (-t) := by
      have hsq : d * t * N⁻¹ = -(d * N) * -t * N⁻¹ ^ 2 := by
        ext
        simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val,
          Units.val_inv_eq_inv_val]
        field_simp
      have hsq0 : kummerClass (N⁻¹ ^ 2) = 0 :=
        (kummerClass_eq_zero_iff_square K).2 (Subgroup.mem_square.2 ⟨N⁻¹, sq _⟩)
      rw [hsq]
      simp only [kummerClass_mul, hsq0, add_zero]
    -- The cup product of Kummer classes is symmetric.
    have hcomm : (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass (-(d * N))) (kummerClass t) =
          (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass t)
            (kummerClass (-(d * N))) := by
      simpa only [kummerCup_squareClass_squareClass] using
        kummerCup_comm K (squareClass (-(d * N))) (squareClass t)
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hmul, map_add, LinearMap.add_apply,
      cup_kummerClass_neg_kummerClass_eq_zero σ hdeg d hx hx2, add_zero, hcomm]
  · fin_cases i
    · simp [ht]
    · have h : (a : L) * (x / a) ^ 2 = (d : K) • (a : L)⁻¹ := by
        rw [Algebra.smul_def, ← hx2]
        field_simp
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, h, map_smul,
        Algebra.IsQuadraticExtension.trace_inv, ← ht, smul_eq_mul, Units.val_mul,
        Units.val_inv_eq_inv_val, hN, Units.coe_map]
      ring

end Universe

/-! ### The norm of `1 + t √d` -/

section TypeZero

variable {K : Type} [Field K] [Invertible (2 : K)] {L : Type} [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [Invertible (2 : L)]

/-- **The Evens norm of `1 + t √d`:** `N^{Ev}((1 + t x)) = (2) ∪ (1 − t² d)`. This is stated for
`K : Type`, the universe of the library's Steinberg relation
`TauCeti.cup_kummerClass_eq_zero_of_add_eq_one`. -/
theorem galoisEvens2_kummerClass_one_add (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (d : Kˣ) {x : L} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (t : K) (ht : 1 - t ^ 2 * (d : K) ≠ 0) (b : Lˣ)
    (hb : (b : L) = 1 + algebraMap K L t * x) :
    galoisEvens K L σ hdeg (kummerClass b) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass (unitOfInvertible (2 : K))) (kummerClass (Units.mk0 _ ht)) := by
  have : Algebra.IsQuadraticExtension K L := ⟨hdeg⟩
  -- `Tr (1 + t x) = 2` and `N (1 + t x) = 1 − t² d`, so `TauCeti.galoisEvens2_kummerClass` gives
  -- `(2) ∪ (−d (1 − t² d)) + (2) ∪ (d) = (2) ∪ (−1) + (2) ∪ (1 − t² d)`, and `(2) ∪ (−1) = 0` is
  -- the Steinberg relation for `2 + (−1) = 1`.
  have hb' : (b : L) = algebraMap K L 1 + algebraMap K L t * x := by rw [hb, map_one]
  have htr : ((unitOfInvertible (2 : K) : Kˣ) : K) = Algebra.trace K L (b : L) := by
    rw [hb', Algebra.IsQuadraticExtension.trace_algebraMap_add_algebraMap_mul_of_sq_eq hx hx2,
      val_unitOfInvertible, mul_one]
  have hN : Units.map (Algebra.norm K : L →* K) b = Units.mk0 _ ht := by
    ext
    rw [Units.coe_map, hb',
      Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul_of_sq_eq hx hx2,
      Units.val_mk0, one_pow]
  -- `−d N · d = (−1) · N · d²`, so `(−d N) + (d) = (−1) + (N)`.
  have hmul : kummerClass (-(d * Units.mk0 _ ht)) + kummerClass d =
      kummerClass (-1) + kummerClass (Units.mk0 _ ht) := by
    have hsq : -(d * Units.mk0 _ ht) * d = -1 * Units.mk0 _ ht * d ^ 2 := by
      ext
      simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, Units.val_one]
      ring
    have hsq0 : kummerClass (d ^ 2) = 0 :=
      (kummerClass_eq_zero_iff_square K).2 (Subgroup.mem_square.2 ⟨d, sq _⟩)
    rw [← kummerClass_mul, hsq]
    simp only [kummerClass_mul, hsq0, add_zero]
  have h21 : (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
      (kummerClass (unitOfInvertible (2 : K))) (kummerClass (-1)) = 0 :=
    cup_kummerClass_eq_zero_of_add_eq_one (by simp; norm_num)
  rw [galoisEvens2_kummerClass σ hdeg d hx hx2 b _ htr, hN, ← map_add, hmul]
  simp only [map_add, h21, zero_add]

end TypeZero

end TauCeti
