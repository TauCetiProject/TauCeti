/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.BasedChart.Basic
public import TauCeti.Algebra.Cluster.OneExchange.Independence
import TauCeti.LinearAlgebra.LinearIndependent.Algebra
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Tactic.LinearCombination

/-!
# Exchanging one coordinate of a based chart

Let `M` be a based chart for an alternating form `Λ` on `I →₀ ℤ` in an algebra `B`, and let
`k : I`. Write `C` for the scalar span of the monomials `M a` with `a k = 0`, the monomials in
the other coordinates, and `x = M (single k 1)`. A unit `y` of `B` with `y * x ∈ C` that
quasi-commutes with every monomial in the other coordinates,
`y * M a = u ^ (2 * Λ' (single k 1) a) • (M a * y)`, replaces `x`: for an alternating form `Λ'`
agreeing with `Λ` on the other coordinates, the monomials

`M' a = u ^ (-(a k * Λ' (single k 1) a°)) • y ^ (a k) * M a°`, where `a° = a.erase k`,

form a based chart for `Λ'` (`BasedChart.exchange`). It keeps every monomial in the other
coordinates and has `y` as its `k`th coordinate.

The multiplication rule comes from the quasi-commutation of `y` with the other coordinates.
Faithfulness of the new chart is the substance: the independence of all monomials of `M` makes
the powers of `x` independent with left coefficients in `C`, the exchange `y = (y * x) * x⁻¹`
preserves this (`TauCeti.linearIndependent_mul_inv_zpow`), and expanding the coefficients in the
monomials of `C` gives the independence of the new monomials over `R`. Neither `B` nor `C` need
be commutative, and `B` need not be a division ring. Seed mutation constructs its mutated chart
in this way.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), Lemmas 5.5–5.6 and Proposition 4.9, for skew exchange and the mutated
  toric frame.
* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and
  double Bruhat cells*, Duke Mathematical Journal 126 (2005), Lemmas 4.1–4.2,
  for the commutative exchange.
-/

public section

namespace TauCeti.BasedChart

variable {R B I : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
  {u : Rˣ} {Λ Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)}

/-- Products of combinations of monomials in the other coordinates stay such combinations. -/
private theorem mul_mem_span (M : BasedChart u Λ B) (k : I) {x y : B}
    (hx : x ∈ Submodule.span R (Set.range fun a : {a : I →₀ ℤ // a k = 0} ↦ (M.monomial a : B)))
    (hy : y ∈ Submodule.span R (Set.range fun a : {a : I →₀ ℤ // a k = 0} ↦ (M.monomial a : B))) :
    x * y ∈ Submodule.span R (Set.range fun a : {a : I →₀ ℤ // a k = 0} ↦ (M.monomial a : B)) := by
  have hxy := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at hxy
  refine Submodule.span_le.mpr ?_ hxy
  rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
  dsimp only
  rw [val_monomial_mul]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨a.val + b.val, by simp [a.property, b.property]⟩, rfl⟩)

/-- The subalgebra spanned by the monomials in the coordinates other than `k`. -/
private noncomputable def offAlgebra (M : BasedChart u Λ B) (k : I) : Subalgebra R B :=
  (Submodule.span R (Set.range fun a : {a : I →₀ ℤ // a k = 0} ↦ (M.monomial a : B))).toSubalgebra
    (Submodule.subset_span ⟨⟨0, rfl⟩, by simp⟩) fun _ _ ↦ mul_mem_span M k

/-- The monomials after exchanging coordinate `k` for `y`. -/
private noncomputable def exchangeMonomial (Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ))
    (M : BasedChart u Λ B) (k : I) (y : Bˣ) (a : I →₀ ℤ) : Bˣ :=
  Units.map (algebraMap R B) (u ^ (-(a k * Λ' (Finsupp.single k 1) (a.erase k)))) * y ^ a k *
    M.monomial (a.erase k)

private theorem val_exchangeMonomial (M : BasedChart u Λ B) (k : I) (y : Bˣ) (a : I →₀ ℤ) :
    (exchangeMonomial Λ' M k y a : B) =
      ((u ^ (-(a k * Λ' (Finsupp.single k 1) (a.erase k))) : Rˣ) : R) •
        ((↑(y ^ a k) : B) * M.monomial (a.erase k)) := by
  simp [exchangeMonomial, Algebra.smul_def, mul_assoc, -map_zpow]

/-- Monomials in the other coordinates move past powers of `y` with the prescribed twist. -/
private theorem monomial_mul_zpow (M : BasedChart u Λ B) {k : I} {y : Bˣ}
    {c : I →₀ ℤ} (hc : (y : B) * M.monomial c =
      ((u ^ (2 * Λ' (Finsupp.single k 1) c) : Rˣ) : R) • ((M.monomial c : B) * y)) (n : ℤ) :
    (M.monomial c : B) * ↑(y ^ n) =
      ((u ^ (-(2 * n * Λ' (Finsupp.single k 1) c)) : Rˣ) : R) •
        ((↑(y ^ n) : B) * M.monomial c) := by
  set U : Bˣ := Units.map (algebraMap R B) (u ^ (-(2 * Λ' (Finsupp.single k 1) c))) with hUdef
  have hU : Commute U y := Units.ext (Algebra.commutes _ _)
  have hs : SemiconjBy (M.monomial c) y (U * y) := by
    unfold SemiconjBy
    apply Units.ext
    have := congrArg (((u ^ (-(2 * Λ' (Finsupp.single k 1) c)) : Rˣ) : R) • ·) hc
    simp only [smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      one_smul] at this
    rw [← this]
    simp [hUdef, Algebra.smul_def, mul_assoc, -map_zpow]
  have h := hs.zpow_right n
  rw [hU.mul_zpow, ← map_zpow, ← zpow_mul] at h
  have h' := congrArg Units.val h
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass] at h'
  rw [h', mul_assoc, ← Algebra.smul_def]
  congr 3
  ring

private theorem zpow_mul_monomial (M : BasedChart u Λ B) {k : I} {y : Bˣ}
    {c : I →₀ ℤ} (hc : (y : B) * M.monomial c =
      ((u ^ (2 * Λ' (Finsupp.single k 1) c) : Rˣ) : R) • ((M.monomial c : B) * y)) (n : ℤ) :
    (↑(y ^ n) : B) * M.monomial c =
      ((u ^ (2 * n * Λ' (Finsupp.single k 1) c) : Rˣ) : R) • ((M.monomial c : B) * ↑(y ^ n)) := by
  rw [monomial_mul_zpow M hc, smul_smul, ← Units.val_mul (u ^ _), ← zpow_add, add_neg_cancel,
    zpow_zero, Units.val_one, one_smul]

omit [Algebra R B] in
/-- Split off coordinate `k` in an alternating form that agrees with `Λ` away from `k`. -/
private theorem apply_eq_of_isAlt (hΛ' : Λ'.IsAlt) {k : I}
    (hoff : ∀ a b, a k = 0 → b k = 0 → Λ' a b = Λ a b) (a b : I →₀ ℤ) :
    Λ' a b = Λ (a.erase k) (b.erase k) + a k * Λ' (Finsupp.single k 1) (b.erase k) -
      b k * Λ' (Finsupp.single k 1) (a.erase k) := by
  conv_lhs => rw [← Finsupp.single_add_erase k a, ← Finsupp.single_add_erase k b,
    ← Finsupp.smul_single_one k (a k), ← Finsupp.smul_single_one k (b k)]
  have h := hΛ'.neg_eq (a.erase k) (Finsupp.single k 1)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hΛ'.self_eq_zero, hoff _ _ Finsupp.erase_same Finsupp.erase_same] at h ⊢
  linear_combination (-b k) * h

private theorem exchangeMonomial_mul (M : BasedChart u Λ B) (hΛ' : Λ'.IsAlt) {k : I} {y : Bˣ}
    (hoff : ∀ a b, a k = 0 → b k = 0 → Λ' a b = Λ a b)
    (hcomm : ∀ a, a k = 0 → (y : B) * M.monomial a =
      ((u ^ (2 * Λ' (Finsupp.single k 1) a) : Rˣ) : R) • ((M.monomial a : B) * y))
    (a b : I →₀ ℤ) :
    exchangeMonomial Λ' M k y a * exchangeMonomial Λ' M k y b =
      Units.map (algebraMap R B) (u ^ (Λ' a b)) * exchangeMonomial Λ' M k y (a + b) := by
  apply Units.ext
  have hm := monomial_mul_zpow M (hcomm _ (Finsupp.erase_same (a := k) (f := a))) (b k)
  rw [Units.val_mul, val_exchangeMonomial, val_exchangeMonomial, Units.val_mul,
    val_exchangeMonomial, Units.coe_map, MonoidHom.coe_ofClass, ← Algebra.smul_def, smul_smul,
    smul_mul_smul_comm, mul_assoc, ← mul_assoc (M.monomial (a.erase k) : B), hm,
    smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, ← mul_assoc, ← mul_assoc,
    ← Units.val_mul (y ^ a k), ← zpow_add, mul_assoc ((y ^ (a k + b k) : Bˣ) : B),
    val_monomial_mul, Algebra.mul_smul_comm,
    smul_smul, Finsupp.coe_add, Pi.add_apply, Finsupp.erase_add]
  congr 1
  simp only [← Units.val_mul, ← zpow_add]
  congr 2
  rw [apply_eq_of_isAlt hΛ' hoff a b, map_add]
  ring

/-- The monomials in the coordinates other than `k`, as elements of their span. -/
private noncomputable def offMonomial (M : BasedChart u Λ B) (k : I)
    (a : {a : I →₀ ℤ // a k = 0}) : M.offAlgebra k :=
  ⟨M.monomial a, Submodule.subset_span ⟨a, rfl⟩⟩

private theorem linearIndependent_offMonomial (M : BasedChart u Λ B) (k : I) :
    LinearIndependent R (M.offMonomial k) :=
  LinearIndependent.of_comp (M.offAlgebra k).val.toLinearMap
    (M.linearIndependent.comp _ Subtype.val_injective)

private theorem span_range_offMonomial (M : BasedChart u Λ B) (k : I) :
    Submodule.span R (Set.range (M.offMonomial k)) = ⊤ := by
  refine eq_top_iff.mpr fun z _ ↦ ?_
  have hz : (z : B) ∈
      (Submodule.span R (Set.range (M.offMonomial k))).map (M.offAlgebra k).val.toLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact z.property
  obtain ⟨w, hw, hwz⟩ := hz
  exact Subtype.ext hwz ▸ hw

private theorem offAlgebra_smul_def (M : BasedChart u Λ B) (k : I) (c : M.offAlgebra k) (v : B) :
    c • v = (c : B) * v :=
  (rfl)

/-- Independence of all monomials makes the integer powers of the `k`th coordinate independent
with left coefficients in the span of the other monomials. -/
private theorem linearIndependent_zpow_coordinate (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (k : I) :
    LinearIndependent (M.offAlgebra k)
      fun n : ℤ ↦ (↑(M.monomial (Finsupp.single k 1) ^ n) : B) := by
  refine LinearIndependent.of_smul_of_span_eq_top ?_ (M.span_range_offMonomial k)
  have hinj : Function.Injective fun p : {a : I →₀ ℤ // a k = 0} × ℤ ↦
      (p.1 : I →₀ ℤ) + p.2 • Finsupp.single k 1 := by
    rintro ⟨a, n⟩ ⟨b, m⟩ h
    have hk := congrArg (· k) h
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, a.property,
      b.property, Finsupp.single_eq_same, smul_eq_mul, mul_one, zero_add] at hk
    subst hk
    exact Prod.ext (Subtype.ext (add_right_cancel h)) rfl
  convert (M.linearIndependent.comp _ hinj).units_smul
    (fun p ↦ u ^ Λ p.1 (p.2 • Finsupp.single k 1)) using 1
  funext p
  simp [offAlgebra_smul_def, offMonomial, M.monomial_zpow hΛ, Units.smul_def]

/-- Conjugation by the `k`th coordinate preserves the span of the other monomials. -/
private theorem inv_mul_mul_mem_offAlgebra (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (k : I)
    {c : B} (hc : c ∈ M.offAlgebra k) :
    (↑(M.monomial (Finsupp.single k 1))⁻¹ : B) * c * M.monomial (Finsupp.single k 1) ∈
      M.offAlgebra k := by
  simp only [offAlgebra, Submodule.mem_toSubalgebra] at hc ⊢
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, rfl⟩ := hc
    rw [mul_assoc, M.val_monomial_mul_monomial_eq_smul_mul hΛ, Algebra.mul_smul_comm,
      ← mul_assoc, Units.inv_mul, one_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  | zero => simp
  | add c d _ _ hc hd => simpa [mul_add, add_mul] using add_mem hc hd
  | smul r c _ hc => simpa using Submodule.smul_mem _ r hc

private theorem linearIndependent_exchangeMonomial (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) {k : I}
    {y : Bˣ} (hcomm : ∀ a, a k = 0 → (y : B) * M.monomial a =
      ((u ^ (2 * Λ' (Finsupp.single k 1) a) : Rˣ) : R) • ((M.monomial a : B) * y))
    (hyx : (y : B) * M.monomial (Finsupp.single k 1) ∈
      Submodule.span R (Set.range fun a : {a : I →₀ ℤ // a k = 0} ↦ (M.monomial a : B))) :
    LinearIndependent R fun a ↦ (exchangeMonomial Λ' M k y a : B) := by
  -- the exchange `y = (y * x) * x⁻¹` keeps the powers independent over the other monomials
  have hE : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈ M.offAlgebra k := by
    simpa only [offAlgebra, Submodule.mem_toSubalgebra, Units.val_mul] using hyx
  have hy : LinearIndependent (M.offAlgebra k) fun n : ℤ ↦ (↑(y ^ n) : B) := by
    simpa using linearIndependent_mul_inv_zpow (M.offAlgebra k) _ _
      (fun _ ↦ M.inv_mul_mul_mem_offAlgebra hΛ k) hE (M.linearIndependent_zpow_coordinate hΛ k)
  -- expanding the coefficients in the other monomials gives independence over `R`
  have hprod := linearIndependent_smul (M.linearIndependent_offMonomial k) hy
  have hinj : Function.Injective fun a : I →₀ ℤ ↦
      ((⟨a.erase k, Finsupp.erase_same⟩ : {a : I →₀ ℤ // a k = 0}), a k) := by
    intro a b h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    rw [← Finsupp.single_add_erase k a, ← Finsupp.single_add_erase k b, h.1, h.2]
  convert (hprod.comp _ hinj).units_smul (fun a ↦
    u ^ (-(a k * Λ' (Finsupp.single k 1) (a.erase k)) +
      2 * a k * Λ' (Finsupp.single k 1) (a.erase k))) using 1
  funext a
  rw [val_exchangeMonomial, zpow_mul_monomial M (hcomm _ Finsupp.erase_same), smul_smul,
    ← Units.val_mul, ← zpow_add]
  simp [offAlgebra_smul_def, offMonomial, Units.smul_def]

/-- The based chart obtained by exchanging coordinate `k` for a unit `y`. The unit must
quasi-commute with the monomials in the other coordinates as prescribed by the new
alternating form `Λ'`, which agrees with `Λ` on those monomials, and `y * M (single k 1)`
must be a scalar combination of them. -/
noncomputable def exchange (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (hΛ' : Λ'.IsAlt) (k : I)
    (y : Bˣ) (hoff : ∀ a b, a k = 0 → b k = 0 → Λ' a b = Λ a b)
    (hcomm : ∀ a, a k = 0 → (y : B) * M.monomial a =
      ((u ^ (2 * Λ' (Finsupp.single k 1) a) : Rˣ) : R) • ((M.monomial a : B) * y))
    (hyx : (y : B) * M.monomial (Finsupp.single k 1) ∈
      Submodule.span R (Set.range fun a : {a : I →₀ ℤ // a k = 0} ↦ (M.monomial a : B))) :
    BasedChart u Λ' B where
  monomial := exchangeMonomial Λ' M k y
  monomial_zero := by simp [exchangeMonomial]
  monomial_mul := exchangeMonomial_mul M hΛ' hoff hcomm
  linearIndependent := linearIndependent_exchangeMonomial M hΛ hcomm hyx

variable (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (hΛ' : Λ'.IsAlt) (k : I) (y : Bˣ)
  (hoff : ∀ a b, a k = 0 → b k = 0 → Λ' a b = Λ a b)
  (hcomm : ∀ a, a k = 0 → (y : B) * M.monomial a =
    ((u ^ (2 * Λ' (Finsupp.single k 1) a) : Rˣ) : R) • ((M.monomial a : B) * y))
  (hyx : (y : B) * M.monomial (Finsupp.single k 1) ∈
    Submodule.span R (Set.range fun a : {a : I →₀ ℤ // a k = 0} ↦ (M.monomial a : B)))

/-- The monomials of the exchanged chart, with `a.erase k` the part of `a` in the other
coordinates. -/
theorem exchange_monomial (a : I →₀ ℤ) :
    (M.exchange hΛ hΛ' k y hoff hcomm hyx).monomial a =
      Units.map (algebraMap R B) (u ^ (-(a k * Λ' (Finsupp.single k 1) (a.erase k)))) *
        y ^ a k * M.monomial (a.erase k) :=
  (rfl)

/-- The exchange keeps every monomial in the other coordinates. -/
@[simp]
theorem exchange_monomial_of_apply_eq_zero {a : I →₀ ℤ} (ha : a k = 0) :
    (M.exchange hΛ hΛ' k y hoff hcomm hyx).monomial a = M.monomial a := by
  simp [exchange_monomial, ha, Finsupp.erase_of_notMem_support]

/-- The `k`th coordinate of the exchanged chart is the new unit. -/
@[simp]
theorem exchange_monomial_single_self :
    (M.exchange hΛ hΛ' k y hoff hcomm hyx).monomial (Finsupp.single k 1) = y := by
  simp [exchange_monomial]

end TauCeti.BasedChart
