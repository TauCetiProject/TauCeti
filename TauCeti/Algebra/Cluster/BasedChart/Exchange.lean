/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic
public import TauCeti.Algebra.Cluster.BasedChart.OrderedProduct
public import TauCeti.Algebra.Cluster.OneExchange.Intersection
public import TauCeti.Data.Finsupp.Single
public import TauCeti.RingTheory.AlgebraTower
import Mathlib.Tactic.Ring

/-!
# One-step skew exchange of based charts

For `c : BasedChart u Λ B` on `L = I →₀ ℤ` and `k : I`, the normalized monomials `c.monomial a`
with `a k = 0` span the complementary subalgebra `c.otherSubalgebra k` with `R`-basis
`c.otherBasis k`. The `k`-th coordinate monomial `c.monomial (Finsupp.single k 1)` normalizes
`(c.otherSubalgebra k).toSubsemiring` for any bilinear form `Λ`, and when
`Λ (Finsupp.single k 1) (Finsupp.single k 1) = 0` its integer powers have unique left Laurent
expansions over `c.otherSubalgebra k` (`BasedChart.skewLaurentSum_coordinate_injective`).

Given an exchanged unit `y : Bˣ` and an additive functional `μ : (I →₀ ℤ) →+ ℤ` such that
`(y * c.monomial (Finsupp.single k 1) : B) ∈ c.otherSubalgebra k` and `y`
`(u, 2 • μ)`-quasi-commutes with monomials off `k`, Laurent uniqueness transfers to `y`, making
`c.mutatedMonomial k y μ` a faithful mutated chart (`BasedChart.exchangeOfForm`,
`BasedChart.exchange`), transferring torus-map injectivity (`QuantumTorus.injective_of_exchange`),
and preserving the ambient subfield closure over any division ring
(`BasedChart.subfieldClosure_exchangeOfForm`, `QuantumTorus.subfieldClosure_eq_of_exchange`).

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §§4–5.
* A. Berenstein, S. Fomin, and A. Zelevinsky, *Cluster algebras III*, Duke Math. J. 126 (2005), §4.
-/

public section

open scoped Pointwise

namespace TauCeti

namespace BasedChart

section GeneralComm

variable {R L B : Type*} [CommSemiring R] [AddCommGroup L] [Semiring B] [Algebra R B]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- General quasi-commutation of normalized chart monomials for an arbitrary integral bilinear form
`Λ`, without assuming `Λ.IsAlt`. -/
theorem monomial_mul_comm (M : BasedChart u Λ B) (a b : L) :
    M.monomial a * M.monomial b =
      Units.map (algebraMap R B) (u ^ (Λ a b - Λ b a)) * (M.monomial b * M.monomial a) := by
  rw [M.monomial_mul, M.monomial_mul, add_comm b a, Units.map_algebraMap_mul_map_algebraMap,
    ← zpow_add, sub_add_cancel]

end GeneralComm

section Semiring

variable {R I B : Type*} [CommSemiring R] {u : Rˣ} {Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)}
  [Semiring B] [Algebra R B]

/-- The `R`-submodule of `B` spanned by the normalized monomials `c.monomial a` with `a k = 0`. -/
def otherSubmodule (c : BasedChart u Λ B) (k : I) : Submodule R B :=
  Submodule.span R (Set.range fun a : { a : I →₀ ℤ // a k = 0 } ↦ (c.monomial a.val : B))

theorem monomial_mem_otherSubmodule (c : BasedChart u Λ B) (k : I) {a : I →₀ ℤ}
    (ha : a k = 0) : (c.monomial a : B) ∈ c.otherSubmodule k :=
  Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩

theorem one_mem_otherSubmodule (c : BasedChart u Λ B) (k : I) :
    (1 : B) ∈ c.otherSubmodule k := by
  simpa using c.monomial_mem_otherSubmodule k (Finsupp.zero_apply (a := k))

theorem mul_mem_otherSubmodule (c : BasedChart u Λ B) (k : I) {x y : B}
    (hx : x ∈ c.otherSubmodule k) (hy : y ∈ c.otherSubmodule k) : x * y ∈ c.otherSubmodule k := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ c.otherSubmodule k)
    (fun _ _ hx hy ↦ ?_) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ by rw [add_mul]; exact Submodule.add_mem _ h₁ h₂)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ by rw [mul_add]; exact Submodule.add_mem _ h₁ h₂)
    (fun r _ _ _ _ h ↦ by rw [Algebra.smul_mul_assoc]; exact Submodule.smul_mem _ r h)
    (fun r _ _ _ _ h ↦ by rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ r h) hx hy
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  rw [c.val_monomial_mul]
  exact Submodule.smul_mem _ _ (c.monomial_mem_otherSubmodule k (by simp [a.property, b.property]))

/-- The `R`-subalgebra of `B` spanned by the normalized monomials `c.monomial a` with `a k = 0`. -/
def otherSubalgebra (c : BasedChart u Λ B) (k : I) : Subalgebra R B :=
  (c.otherSubmodule k).toSubalgebra (c.one_mem_otherSubmodule k)
    fun _ _ ↦ c.mul_mem_otherSubmodule k

@[simp]
theorem toSubmodule_otherSubalgebra (c : BasedChart u Λ B) (k : I) :
    (c.otherSubalgebra k).toSubmodule = c.otherSubmodule k :=
  (rfl)

theorem mem_otherSubalgebra_iff (c : BasedChart u Λ B) (k : I) {b : B} :
    b ∈ c.otherSubalgebra k ↔ b ∈ c.otherSubmodule k :=
  Iff.rfl

theorem monomial_mem_otherSubalgebra (c : BasedChart u Λ B) (k : I) {a : I →₀ ℤ}
    (ha : a k = 0) : (c.monomial a : B) ∈ c.otherSubalgebra k :=
  c.monomial_mem_otherSubmodule k ha

theorem coordinate_mem_otherSubalgebra_of_ne (c : BasedChart u Λ B) {i k : I} (hik : i ≠ k) :
    (c.coordinate Finsupp.basisSingleOne i : B) ∈ c.otherSubalgebra k := by
  rw [coordinate_def, Finsupp.coe_basisSingleOne]
  exact c.monomial_mem_otherSubalgebra k (Finsupp.single_eq_of_ne hik.symm)

theorem otherSubalgebra_le_range_eval (c : BasedChart u Λ B) (k : I) :
    c.otherSubalgebra k ≤ c.eval.range := by
  rw [← Subalgebra.toSubmodule.le_iff_le, toSubmodule_otherSubalgebra, otherSubmodule,
    Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨QuantumTorus.monomial u Λ a.val, c.eval_monomial a.val⟩

/-- The `R`-basis of `c.otherSubalgebra k` indexed by `{ a : I →₀ ℤ // a k = 0 }`. -/
noncomputable def otherBasis (c : BasedChart u Λ B) (k : I) :
    Module.Basis { a : I →₀ ℤ // a k = 0 } R (c.otherSubalgebra k) :=
  (Module.Basis.span (v := fun a : { a : I →₀ ℤ // a k = 0 } ↦ (c.monomial a.val : B))
    (c.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    { toFun := fun x ↦ ⟨x.val, x.property⟩
      invFun := fun x ↦ ⟨x.val, x.property⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

@[simp]
theorem coe_otherBasis (c : BasedChart u Λ B) (k : I) (a : { a : I →₀ ℤ // a k = 0 }) :
    ((c.otherBasis k a : c.otherSubalgebra k) : B) = c.monomial a.val := by
  simp [otherBasis]

private theorem linearIndependent_otherSubalgebra_iff
    (c : BasedChart u Λ B) (k : I) (v : ℤ → B) :
    LinearIndependent (c.otherSubalgebra k).toSubsemiring v ↔
      LinearIndependent R (fun a : I →₀ ℤ ↦ (c.monomial (a.erase k) : B) * v (a k)) := by
  classical
  let S := (c.otherSubalgebra k).toSubsemiring
  let _ : Module R S := (c.otherSubalgebra k).toSubmodule.module
  have _ : IsScalarTower R S B := ⟨fun r s x ↦ Algebra.smul_mul_assoc r (s : B) x⟩
  let b : Module.Basis { a : I →₀ ℤ // a k = 0 } R S := c.otherBasis k
  let e : (I →₀ ℤ) ≃ { a : I →₀ ℤ // a k = 0 } × ℤ :=
    (Finsupp.eraseSingleEquiv k).trans (Equiv.prodComm _ _)
  have he : (fun a : I →₀ ℤ ↦ (c.monomial (a.erase k) : B) * v (a k)) =
      (fun p : { a : I →₀ ℤ // a k = 0 } × ℤ ↦ b p.1 • v p.2) ∘ e := by
    funext a
    dsimp only [Function.comp_apply, e, Equiv.trans_apply, Equiv.prodComm_apply,
      Prod.fst_swap, Prod.snd_swap, b]
    rw [setLike_smul_def, smul_eq_mul, Finsupp.eraseSingleEquiv_apply_fst]
    exact congrArg (· * v (a k))
      ((c.coe_otherBasis k (Finsupp.eraseSingleEquiv k a).2).trans
        (congrArg (fun x ↦ (c.monomial x : B)) (Finsupp.coe_eraseSingleEquiv_apply_snd k a))).symm
  rw [he, linearIndependent_equiv e]
  exact ⟨linearIndependent_smul b.linearIndependent, fun h ↦ h.of_smul_of_span_eq_top b.span_eq⟩

private theorem conj_mem_otherSubalgebra_of_monomial (c : BasedChart u Λ B) (k : I) {z : Bˣ}
    (hz : ∀ a : I →₀ ℤ, a k = 0 →
      (z : B) * (c.monomial a : B) * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k)
    {b : B} (hb : b ∈ c.otherSubalgebra k) :
    (z : B) * b * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k :=
  Submodule.span_induction (p := fun b _ ↦ (z : B) * b * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k)
    (fun _ hx ↦ by rcases hx with ⟨a, rfl⟩; exact hz a.val a.property)
    (by simp [(c.otherSubalgebra k).zero_mem])
    (fun _ _ _ _ h₁ h₂ ↦ by rw [mul_add, add_mul]; exact (c.otherSubalgebra k).add_mem h₁ h₂)
    (fun r _ _ h ↦ by
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      exact Submodule.smul_mem (c.otherSubmodule k) r h) hb

/-- A unit `z : Bˣ` normalizes `c.otherSubalgebra k` whenever conjugation by `z` and `z⁻¹` sends
every monomial `c.monomial a` with `a k = 0` back into `c.otherSubalgebra k`. -/
theorem conjAct_otherSubalgebra_of_monomial (c : BasedChart u Λ B) (k : I) {z : Bˣ}
    (hz : ∀ a : I →₀ ℤ, a k = 0 →
      (z : B) * (c.monomial a : B) * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hz_inv : ∀ a : I →₀ ℤ, a k = 0 →
      ((z⁻¹ : Bˣ) : B) * (c.monomial a : B) * (z : B) ∈ c.otherSubalgebra k) :
    ConjAct.toConjAct z • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring :=
  le_antisymm (fun _ ⟨b, hb, hEq⟩ ↦ hEq ▸ c.conj_mem_otherSubalgebra_of_monomial k hz hb)
    fun b hb ↦ ⟨((z⁻¹ : Bˣ) : B) * b * (z : B),
      by simpa using c.conj_mem_otherSubalgebra_of_monomial (z := z⁻¹) k (by simpa using hz_inv) hb,
      by simp [ConjAct.units_smul_def, mul_assoc]⟩

private theorem unitsMap_mul_monomial_mem (c : BasedChart u Λ B) (k : I) (w : Rˣ) {a : I →₀ ℤ}
    (ha : a k = 0) :
    ((Units.map (algebraMap R B) w * c.monomial a : Bˣ) : B) ∈ c.otherSubalgebra k := by
  rw [Units.val_mul]
  exact (c.otherSubalgebra k).mul_mem
    (by simp [(c.otherSubalgebra k).algebraMap_mem]) (c.monomial_mem_otherSubalgebra k ha)

/-- For any integral bilinear form `Λ`, the `k`-th chart coordinate normalizes
`c.otherSubalgebra k`. -/
theorem conjAct_coordinate_otherSubalgebra (c : BasedChart u Λ B) (k : I) :
    ConjAct.toConjAct (c.monomial (Finsupp.single k 1)) • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring := by
  refine c.conjAct_otherSubalgebra_of_monomial k (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · rw [← Units.val_mul, ← Units.val_mul, c.monomial_mul_comm (Finsupp.single k 1) a, mul_assoc,
      mul_inv_cancel_right]
    exact c.unitsMap_mul_monomial_mem k _ ha
  · rw [← Units.val_mul, ← Units.val_mul, mul_assoc, c.monomial_mul_comm a (Finsupp.single k 1),
      Units.mul_map_algebraMap_mul, inv_mul_cancel_left]
    exact c.unitsMap_mul_monomial_mem k _ ha

/-- When `Λ (single k 1) (single k 1) = 0`, finite left Laurent expansions in
`c.monomial (single k 1)` over `c.otherSubalgebra k` are unique. -/
theorem skewLaurentSum_coordinate_injective (c : BasedChart u Λ B) {k : I}
    (hkk : Λ (Finsupp.single k 1) (Finsupp.single k 1) = 0) :
    Function.Injective
      ((c.otherSubalgebra k).toSubsemiring.skewLaurentSum (c.monomial (Finsupp.single k 1))) := by
  rw [Subsemiring.injective_skewLaurentSum_iff_linearIndependent,
    c.linearIndependent_otherSubalgebra_iff k]
  let w (a : I →₀ ℤ) : R := ((u ^ Λ (a.erase k) (Finsupp.single k (a k)) : Rˣ) : R)
  have hw (a : I →₀ ℤ) : IsRightRegular (w a) :=
    (u ^ Λ (a.erase k) (Finsupp.single k (a k))).isUnit.isRegular.right
  have hfactor : (w • fun a : I →₀ ℤ ↦ (c.monomial a : B)) =
      fun a : I →₀ ℤ ↦
        (c.monomial (a.erase k) : B) * ((c.monomial (Finsupp.single k 1) ^ a k : Bˣ) : B) := by
    funext a
    rw [Pi.smul_apply', ← c.monomial_single_of_self_eq_zero hkk (a k), c.val_monomial_mul,
      Finsupp.erase_add_single k a]
  exact hfactor ▸ c.linearIndependent.smul_of_isRightRegular hw

/-- The mutated normalized monomial family `u ^ (-(a k * μ (a.erase k))) * (y ^ a k * M(a.erase k))`
at index `k`. -/
noncomputable def mutatedMonomial (c : BasedChart u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) (a : I →₀ ℤ) : Bˣ :=
  Units.map (algebraMap R B) (u ^ (-(a k * μ (a.erase k)))) *
    (y ^ a k * c.monomial (a.erase k))

@[simp]
theorem mutatedMonomial_zero (c : BasedChart u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) : c.mutatedMonomial k y μ 0 = 1 := by
  simp [mutatedMonomial]

theorem mutatedMonomial_of_apply_eq_zero (c : BasedChart u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) {a : I →₀ ℤ} (ha : a k = 0) :
    c.mutatedMonomial k y μ a = c.monomial a := by
  rw [mutatedMonomial, ha, Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr ha)]
  simp

@[simp]
theorem mutatedMonomial_single_same (c : BasedChart u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) (n : ℤ) : c.mutatedMonomial k y μ (Finsupp.single k n) = y ^ n := by
  simp [mutatedMonomial]

theorem mutatedMonomial_single_of_ne (c : BasedChart u Λ B) {i k : I} (hik : i ≠ k)
    (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ) (n : ℤ) :
    c.mutatedMonomial k y μ (Finsupp.single i n) = c.monomial (Finsupp.single i n) :=
  c.mutatedMonomial_of_apply_eq_zero k y μ (Finsupp.single_eq_of_ne hik.symm)

section QuasiComm

variable (c : BasedChart u Λ B) {k : I} {y : Bˣ} {μ : (I →₀ ℤ) →+ ℤ}
  (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
    y * c.monomial a = Units.map (algebraMap R B) (u ^ (2 * μ a)) * (c.monomial a * y))
include hy_comm

/-- Integer powers of `y` inherit `(u, 2 • μ)`-quasi-commutation against monomials off `k`. -/
theorem zpow_mul_monomial_of_quasiComm (n : ℤ) {a : I →₀ ℤ} (ha : a k = 0) :
    y ^ n * c.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * n * μ a)) * (c.monomial a * y ^ n) := by
  rw [Units.zpow_mul_of_map_algebraMap_mul (hy_comm a ha) n, ← zpow_mul]
  congr 3
  ring

/-- Right-ordered form `u ^ (a k * μ (a.erase k)) * (M(a.erase k) * y ^ a k)` of a mutated
monomial under quasi-commutation off `k`. -/
theorem mutatedMonomial_eq_mul_zpow (a : I →₀ ℤ) :
    c.mutatedMonomial k y μ a =
      Units.map (algebraMap R B) (u ^ (a k * μ (a.erase k))) *
        (c.monomial (a.erase k) * y ^ a k) := by
  rw [mutatedMonomial, c.zpow_mul_monomial_of_quasiComm hy_comm (a k) Finsupp.erase_same,
    Units.map_algebraMap_mul_map_algebraMap, ← zpow_add]
  congr 3
  ring

/-- A unit `y` quasi-commuting with monomials off `k` normalizes `c.otherSubalgebra k`. -/
theorem conjAct_unit_otherSubalgebra :
    ConjAct.toConjAct y • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring := by
  refine c.conjAct_otherSubalgebra_of_monomial k (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · rw [← Units.val_mul, ← Units.val_mul, hy_comm a ha, mul_assoc, mul_inv_cancel_right]
    exact c.unitsMap_mul_monomial_mem k _ ha
  · have hm := c.zpow_mul_monomial_of_quasiComm hy_comm (-1) ha
    rw [zpow_neg_one] at hm
    rw [← Units.val_mul, ← Units.val_mul, hm, mul_assoc, inv_mul_cancel_right]
    exact c.unitsMap_mul_monomial_mem k _ ha

/-- Mutated normalized monomials multiply with `(u, Λ')`-twist for any alternating `Λ'` agreeing
with `Λ` off `k` and having pairing `μ` with `single k 1` off `k`. -/
theorem mutatedMonomial_mul {Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)}
    (hΛ' : Λ'.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 → Λ' (Finsupp.single k 1) a = μ a)
    (a b : I →₀ ℤ) :
    c.mutatedMonomial k y μ a * c.mutatedMonomial k y μ b =
      Units.map (algebraMap R B) (u ^ Λ' a b) * c.mutatedMonomial k y μ (a + b) := by
  have hcomm_inv : c.monomial (a.erase k) * y ^ b k =
      Units.map (algebraMap R B) (u ^ (-(2 * b k * μ (a.erase k)))) *
        (y ^ b k * c.monomial (a.erase k)) :=
    mul_left_cancel (a := Units.map (algebraMap R B) (u ^ (2 * b k * μ (a.erase k)))) <| by
      rw [← c.zpow_mul_monomial_of_quasiComm hy_comm (b k) Finsupp.erase_same,
        Units.map_algebraMap_mul_map_algebraMap, ← zpow_add, add_neg_cancel, zpow_zero, map_one,
        one_mul]
  have hform : Λ' a b =
      a k * μ (b.erase k) - b k * μ (a.erase k) + Λ (a.erase k) (b.erase k) := by
    conv_lhs => rw [← Finsupp.single_add_erase k a, ← Finsupp.single_add_erase k b]
    simp only [map_add, LinearMap.add_apply]
    rw [(hΛ'.neg_eq (Finsupp.single k (b k)) (a.erase k)).symm,
      (by simp : Finsupp.single k (a k) = a k • Finsupp.single k 1),
      (by simp : Finsupp.single k (b k) = b k • Finsupp.single k 1)]
    simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, hΛ'.self_eq_zero, mul_zero,
      hΛ'_row (b.erase k) Finsupp.erase_same, hΛ'_row (a.erase k) Finsupp.erase_same,
      hΛ'_off (a.erase k) (b.erase k) Finsupp.erase_same Finsupp.erase_same]
    ring
  calc
    c.mutatedMonomial k y μ a * c.mutatedMonomial k y μ b
      = Units.map (algebraMap R B)
          (u ^ (-(a k * μ (a.erase k))) * u ^ (-(b k * μ (b.erase k)))) *
          (y ^ a k * ((c.monomial (a.erase k) * y ^ b k) * c.monomial (b.erase k))) := by
        rw [mutatedMonomial, mutatedMonomial, Units.map_algebraMap_mul_mul_map_algebraMap_mul]
        simp only [mul_assoc]
    _ = Units.map (algebraMap R B)
          ((u ^ (-(a k * μ (a.erase k))) * u ^ (-(b k * μ (b.erase k)))) *
            u ^ (-(2 * b k * μ (a.erase k)))) *
          (y ^ (a k + b k) * (c.monomial (a.erase k) * c.monomial (b.erase k))) := by
        rw [hcomm_inv, mul_assoc _ _ (c.monomial (b.erase k)), Units.mul_map_algebraMap_mul,
          Units.map_algebraMap_mul_map_algebraMap, mul_assoc (y ^ b k),
          ← mul_assoc (y ^ a k) (y ^ b k), ← zpow_add y]
    _ = Units.map (algebraMap R B) (u ^ Λ' a b) * c.mutatedMonomial k y μ (a + b) := by
        rw [c.monomial_mul, Units.mul_map_algebraMap_mul,
          Units.map_algebraMap_mul_map_algebraMap, mutatedMonomial, Finsupp.add_apply,
          Finsupp.erase_add, map_add, Units.map_algebraMap_mul_map_algebraMap]
        congr 2
        simp only [← zpow_add, hform]
        congr 1
        ring

end QuasiComm

/-- Under quasi-commutation off `k`, the exchange factor `y * c.monomial (single k 1)` normalizes
`c.otherSubalgebra k`, for any integral bilinear form `Λ`. -/
theorem conjAct_mul_coordinate_otherSubalgebra (c : BasedChart u Λ B) {k : I} {y : Bˣ}
    {μ : (I →₀ ℤ) →+ ℤ}
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a = Units.map (algebraMap R B) (u ^ (2 * μ a)) * (c.monomial a * y)) :
    ConjAct.toConjAct (y * c.monomial (Finsupp.single k 1)) • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring := by
  rw [map_mul, mul_smul, c.conjAct_coordinate_otherSubalgebra k,
    c.conjAct_unit_otherSubalgebra hy_comm]

/-- When `Λ (single k 1) (single k 1) = 0` and
`(y * c.monomial (single k 1) : B) ∈ c.otherSubalgebra k`, finite left Laurent expansions in `y`
over `c.otherSubalgebra k` are unique. -/
theorem skewLaurentSum_exchange_injective (c : BasedChart u Λ B) {k : I}
    (hkk : Λ (Finsupp.single k 1) (Finsupp.single k 1) = 0) {y : Bˣ}
    (hyx : ((y * c.monomial (Finsupp.single k 1) : Bˣ) : B) ∈ c.otherSubalgebra k) :
    Function.Injective ((c.otherSubalgebra k).toSubsemiring.skewLaurentSum y) := by
  rw [← mul_inv_cancel_right y (c.monomial (Finsupp.single k 1))]
  exact Subsemiring.skewLaurentSum_mul_inv_injective (c.conjAct_coordinate_otherSubalgebra k) hyx
    (c.skewLaurentSum_coordinate_injective hkk)

/-- When `Λ (single k 1) (single k 1) = 0`,
`(y * c.monomial (single k 1) : B) ∈ c.otherSubalgebra k`, and `y` `(u, 2 • μ)`-quasi-commutes with
monomials off `k`, the mutated normalized monomials `c.mutatedMonomial k y μ` are `R`-linearly
independent. -/
theorem linearIndependent_mutatedMonomial (c : BasedChart u Λ B) {k : I}
    (hkk : Λ (Finsupp.single k 1) (Finsupp.single k 1) = 0) {y : Bˣ} {μ : (I →₀ ℤ) →+ ℤ}
    (hyx : ((y * c.monomial (Finsupp.single k 1) : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a = Units.map (algebraMap R B) (u ^ (2 * μ a)) * (c.monomial a * y)) :
    LinearIndependent R fun a ↦ (c.mutatedMonomial k y μ a : B) := by
  have hli := (c.linearIndependent_otherSubalgebra_iff k fun n : ℤ ↦ ((y ^ n : Bˣ) : B)).mp <|
    (Subsemiring.injective_skewLaurentSum_iff_linearIndependent _ y).mp
      (c.skewLaurentSum_exchange_injective hkk hyx)
  let w (a : I →₀ ℤ) : R := ((u ^ (a k * μ (a.erase k)) : Rˣ) : R)
  have hw (a : I →₀ ℤ) : IsRightRegular (w a) := (u ^ (a k * μ (a.erase k))).isUnit.isRegular.right
  have hfactor : (w • fun a : I →₀ ℤ ↦ (c.monomial (a.erase k) : B) * ((y ^ a k : Bˣ) : B)) =
      fun a : I →₀ ℤ ↦ (c.mutatedMonomial k y μ a : B) := by
    funext a
    have hm := congrArg (Units.val : Bˣ → B) (c.mutatedMonomial_eq_mul_zpow hy_comm a)
    simpa [Pi.smul_apply', w, Algebra.smul_def, -map_zpow] using hm.symm
  exact hfactor ▸ hli.smul_of_isRightRegular hw

section ExchangeOfForm

variable (c : BasedChart u Λ B) (hΛ : Λ.IsAlt) (k : I) (y : Bˣ)
  (μ : (I →₀ ℤ) →+ ℤ)
  (hyx : ((y * c.monomial (Finsupp.single k 1) : Bˣ) : B) ∈ c.otherSubalgebra k)
  (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
    y * c.monomial a = Units.map (algebraMap R B) (u ^ (2 * μ a)) * (c.monomial a * y))
  (Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)) (hΛ' : Λ'.IsAlt)
  (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b)
  (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 → Λ' (Finsupp.single k 1) a = μ a)

/-- **One-step skew exchange of a based chart** for a compatible alternating form `Λ'`. -/
noncomputable def exchangeOfForm : BasedChart u Λ' B where
  monomial := c.mutatedMonomial k y μ
  monomial_zero := c.mutatedMonomial_zero k y μ
  monomial_mul := c.mutatedMonomial_mul hy_comm hΛ' hΛ'_off hΛ'_row
  linearIndependent :=
    c.linearIndependent_mutatedMonomial (hΛ.self_eq_zero (Finsupp.single k 1)) hyx hy_comm

@[simp]
theorem exchangeOfForm_monomial (a : I →₀ ℤ) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).monomial a =
      c.mutatedMonomial k y μ a :=
  (rfl)

theorem exchangeOfForm_monomial_of_apply_eq_zero {a : I →₀ ℤ} (ha : a k = 0) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).monomial a = c.monomial a :=
  c.mutatedMonomial_of_apply_eq_zero k y μ ha

@[simp]
theorem coordinate_exchangeOfForm_same :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).coordinate
        Finsupp.basisSingleOne k = y := by
  simp [coordinate_def]

theorem coordinate_exchangeOfForm_of_ne {i : I} (hik : i ≠ k) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).coordinate
        Finsupp.basisSingleOne i =
      c.coordinate Finsupp.basisSingleOne i := by
  simp only [coordinate_def, Finsupp.coe_basisSingleOne, exchangeOfForm_monomial]
  exact c.mutatedMonomial_single_of_ne hik y μ 1

/-- `BasedChart.exchangeOfForm` at `k` preserves `c.otherSubalgebra k`. -/
@[simp]
theorem exchangeOfForm_otherSubalgebra :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).otherSubalgebra k =
      c.otherSubalgebra k := by
  apply Subalgebra.toSubmodule_injective
  simp only [toSubmodule_otherSubalgebra, otherSubmodule]
  congr 1
  ext b
  simp only [Set.mem_range, Subtype.exists]
  exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, ha, by simpa [c.mutatedMonomial_of_apply_eq_zero k y μ ha] using h⟩,
    fun ⟨a, ha, h⟩ ↦ ⟨a, ha, by simpa [c.mutatedMonomial_of_apply_eq_zero k y μ ha] using h⟩⟩

end ExchangeOfForm

section Exchange

variable [DecidableEq I] {A : Matrix I I ℤ} (c : BasedChart u A.finsuppBilinForm B)
  (hA : A.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
  (hyx : ((y * c.monomial (Finsupp.single k 1) : Bˣ) : B) ∈ c.otherSubalgebra k)
  (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
    y * c.monomial a = Units.map (algebraMap R B) (u ^ (2 * μ a)) * (c.monomial a * y))

/-- **One-step skew exchange of a based chart** with canonical updated form matrix
`A.updateSkew k (fun j ↦ μ (Finsupp.single j 1))`. -/
noncomputable def exchange :
    BasedChart u (A.updateSkew k fun j ↦ μ (Finsupp.single j 1)).finsuppBilinForm B :=
  c.exchangeOfForm hA k y μ hyx hy_comm
    (A.updateSkew k fun j ↦ μ (Finsupp.single j 1)).finsuppBilinForm
    (Matrix.isAlt_finsuppBilinForm_updateSkew hA k _)
    (fun _ _ ha hb ↦ Matrix.finsuppBilinForm_updateSkew_of_apply_eq_zero A k _ ha hb)
    fun a ha ↦ by
      rw [Matrix.finsuppBilinForm_updateSkew_single_left A k _ 1 ha, one_mul]
      clear ha
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
      | single j n =>
        rw [Finsupp.linearCombination_single, smul_eq_mul,
          (by simp : Finsupp.single j n = n • Finsupp.single j 1), map_zsmul, smul_eq_mul]

@[simp]
theorem exchange_monomial (a : I →₀ ℤ) :
    (c.exchange hA k y μ hyx hy_comm).monomial a = c.mutatedMonomial k y μ a :=
  (rfl)

@[simp]
theorem coordinate_exchange_same :
    (c.exchange hA k y μ hyx hy_comm).coordinate Finsupp.basisSingleOne k = y :=
  c.coordinate_exchangeOfForm_same hA k y μ hyx hy_comm _ _ _ _

theorem coordinate_exchange_of_ne {i : I} (hik : i ≠ k) :
    (c.exchange hA k y μ hyx hy_comm).coordinate Finsupp.basisSingleOne i =
      c.coordinate Finsupp.basisSingleOne i :=
  c.coordinate_exchangeOfForm_of_ne hA k y μ hyx hy_comm _ _ _ _ hik

/-- `BasedChart.exchange` at `k` preserves `c.otherSubalgebra k`. -/
@[simp]
theorem exchange_otherSubalgebra :
    (c.exchange hA k y μ hyx hy_comm).otherSubalgebra k = c.otherSubalgebra k :=
  c.exchangeOfForm_otherSubalgebra hA k y μ hyx hy_comm _ _ _ _

end Exchange

end Semiring

end BasedChart

namespace QuantumTorus

section Semiring

variable {R I B : Type*} [CommSemiring R] {u : Rˣ}
  {Λ Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)} [Semiring B] [Algebra R B]

section TorusExchange

variable (hΛ : Λ.IsAlt) (hΛ' : Λ'.IsAlt) {k : I}
  {χ : QuantumTorus R (I →₀ ℤ) u Λ →ₐ[R] B}
  {χ' : QuantumTorus R (I →₀ ℤ) u Λ' →ₐ[R] B}
  (h_off : ∀ i ≠ k, χ' (monomial u Λ' (Finsupp.single i 1)) =
    χ (monomial u Λ (Finsupp.single i 1)))
  (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b)

include hΛ hΛ' h_off hΛ'_off in
/-- Two quantum-torus maps `χ'` and `χ` agreeing on all generators `monomial (single i 1)` with
`i ≠ k` (for alternating forms agreeing off `k`) agree on every monomial `monomial a` with
`a k = 0`. -/
theorem algHom_monomial_eq_of_apply_eq_zero {a : I →₀ ℤ} (ha : a k = 0) :
    χ' (monomial u Λ' a) = χ (monomial u Λ a) := by
  classical
  suffices Units.map χ'.toMonoidHom (monomialUnit u Λ' a) =
      Units.map χ.toMonoidHom (monomialUnit u Λ a) by
    simpa using congrArg (Units.val : Bˣ → B) this
  induction a using Finsupp.induction with
  | zero => ext; simp
  | single_add i n f hif hn ih =>
    have hik : i ≠ k := by rintro rfl; simp [Finsupp.notMem_support_iff.mp hif, hn] at ha
    have hfk : f k = 0 := by simpa [Finsupp.add_apply, Finsupp.single_eq_of_ne hik.symm] using ha
    have hsingle : Units.map χ'.toMonoidHom (monomialUnit u Λ' (Finsupp.single i n)) =
        Units.map χ.toMonoidHom (monomialUnit u Λ (Finsupp.single i n)) := by
      rw [← Finsupp.smul_single_one i n, ← monomialUnit_zpow hΛ', ← monomialUnit_zpow hΛ,
        map_zpow, map_zpow]
      exact congrArg (· ^ n) (Units.ext <| by simpa using h_off i hik)
    have hmul₁ : Units.map χ'.toMonoidHom (monomialUnit u Λ' (Finsupp.single i n)) *
        Units.map χ'.toMonoidHom (monomialUnit u Λ' f) =
        Units.map (algebraMap R B) (u ^ Λ' (Finsupp.single i n) f) *
          Units.map χ'.toMonoidHom (monomialUnit u Λ' (Finsupp.single i n + f)) := by
      rw [← map_mul, monomialUnit_mul, map_mul]
      exact congrArg (· * _) (Units.ext <| χ'.commutes _)
    have hmul₂ : Units.map χ.toMonoidHom (monomialUnit u Λ (Finsupp.single i n)) *
        Units.map χ.toMonoidHom (monomialUnit u Λ f) =
        Units.map (algebraMap R B) (u ^ Λ (Finsupp.single i n) f) *
          Units.map χ.toMonoidHom (monomialUnit u Λ (Finsupp.single i n + f)) := by
      rw [← map_mul, monomialUnit_mul, map_mul]
      exact congrArg (· * _) (Units.ext <| χ.commutes _)
    rw [hΛ'_off _ _ (Finsupp.single_eq_of_ne hik.symm) hfk] at hmul₁
    exact mul_left_cancel (hmul₁.symm.trans (by rw [hsingle, ih hfk, hmul₂]))

end TorusExchange

/-- Given an injective torus map `χ : QuantumTorus R (I →₀ ℤ) u Λ →ₐ[R] B` and a map
`χ' : QuantumTorus R (I →₀ ℤ) u Λ' →ₐ[R] B` agreeing off `k` with
`χ' (X_k) * χ (X_k) ∈ (BasedChart.ofInjective χ hχ).otherSubalgebra k`, `χ'` arises as `eval` of a
one-step `exchangeOfForm` of `BasedChart.ofInjective χ hχ`. -/
theorem exists_basedChart_of_exchange
    (hΛ : Λ.IsAlt) (hΛ' : Λ'.IsAlt) {k : I}
    {χ : QuantumTorus R (I →₀ ℤ) u Λ →ₐ[R] B} (hχ : Function.Injective χ)
    {χ' : QuantumTorus R (I →₀ ℤ) u Λ' →ₐ[R] B}
    (h_off : ∀ i ≠ k, χ' (monomial u Λ' (Finsupp.single i 1)) =
      χ (monomial u Λ (Finsupp.single i 1)))
    (hΛ'_off : ∀ a b, a k = 0 → b k = 0 → Λ' a b = Λ a b)
    (h_exch : χ' (monomial u Λ' (Finsupp.single k 1)) * χ (monomial u Λ (Finsupp.single k 1)) ∈
      (BasedChart.ofInjective χ hχ).otherSubalgebra k) :
    ∃ (y : Bˣ)
      (hyx : ((y * (BasedChart.ofInjective χ hχ).monomial (Finsupp.single k 1) : Bˣ) : B) ∈
        (BasedChart.ofInjective χ hχ).otherSubalgebra k)
      (hy_comm : ∀ a : I →₀ ℤ, a k = 0 → y * (BasedChart.ofInjective χ hχ).monomial a =
        Units.map (algebraMap R B)
          (u ^ (2 * (Λ' (Finsupp.single k 1)).toAddMonoidHom a)) *
          ((BasedChart.ofInjective χ hχ).monomial a * y)),
      ((BasedChart.ofInjective χ hχ).exchangeOfForm hΛ k y
        (Λ' (Finsupp.single k 1)).toAddMonoidHom hyx hy_comm Λ' hΛ' hΛ'_off
        (by simp)).eval = χ' := by
  classical
  let c := BasedChart.ofInjective χ hχ
  let y : Bˣ := Units.map χ' (monomialUnit u Λ' (Finsupp.single k 1))
  let μ : (I →₀ ℤ) →+ ℤ := (Λ' (Finsupp.single k 1)).toAddMonoidHom
  have hyx : ((y * c.monomial (Finsupp.single k 1) : Bˣ) : B) ∈ c.otherSubalgebra k := by
    simpa [y, c] using h_exch
  have hy_comm (a : I →₀ ℤ) (ha : a k = 0) :
      y * c.monomial a = Units.map (algebraMap R B) (u ^ (2 * μ a)) * (c.monomial a * y) := by
    ext
    have hmap := congrArg χ'
      (monomial_mul_monomial_eq_smul_mul (R := R) (u := u) hΛ' (Finsupp.single k 1) a)
    rw [map_mul, Algebra.smul_def, map_mul, AlgHom.commutes, map_mul,
      algHom_monomial_eq_of_apply_eq_zero hΛ hΛ' h_off hΛ'_off ha] at hmap
    simpa [y, c, μ, -map_zpow] using hmap
  refine ⟨y, hyx, hy_comm, algHom_ext_of_basis Finsupp.basisSingleOne fun i ↦ ?_⟩
  rcases eq_or_ne k i with rfl | hik
  · simp [y]
  · simp only [Finsupp.coe_basisSingleOne, BasedChart.eval_monomial,
      BasedChart.exchangeOfForm_monomial, BasedChart.mutatedMonomial_single_of_ne _ hik.symm]
    simpa [c] using (h_off i hik.symm).symm

/-- **Transfer of quantum-torus map injectivity under one-step exchange**: if `χ` is injective and
`χ'` agrees with `χ` off `k` with `χ' (X_k) * χ (X_k) ∈ otherSubalgebra k`, then `χ'` is
injective. -/
theorem injective_of_exchange
    (hΛ : Λ.IsAlt) (hΛ' : Λ'.IsAlt) {k : I}
    {χ : QuantumTorus R (I →₀ ℤ) u Λ →ₐ[R] B} (hχ : Function.Injective χ)
    {χ' : QuantumTorus R (I →₀ ℤ) u Λ' →ₐ[R] B}
    (h_off : ∀ i ≠ k, χ' (monomial u Λ' (Finsupp.single i 1)) =
      χ (monomial u Λ (Finsupp.single i 1)))
    (hΛ'_off : ∀ a b, a k = 0 → b k = 0 → Λ' a b = Λ a b)
    (h_exch : χ' (monomial u Λ' (Finsupp.single k 1)) * χ (monomial u Λ (Finsupp.single k 1)) ∈
      (BasedChart.ofInjective χ hχ).otherSubalgebra k) :
    Function.Injective χ' := by
  obtain ⟨_, _, _, hχ'_eq⟩ := exists_basedChart_of_exchange hΛ hΛ' hχ h_off hΛ'_off h_exch
  exact hχ'_eq ▸ BasedChart.eval_injective _

end Semiring

end QuantumTorus

section DivisionRing

variable {R I D : Type*} [CommSemiring R] {u : Rˣ} {Λ Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)}
  [DivisionRing D] [Algebra R D]

private theorem range_eval_subset_subfield (c : BasedChart u Λ D) {k : I}
    (hkk : Λ (Finsupp.single k 1) (Finsupp.single k 1) = 0)
    {F : Subfield D} (hother : (c.otherSubalgebra k : Set D) ⊆ F)
    (hxk : (c.monomial (Finsupp.single k 1) : D) ∈ F) : Set.range c.eval ⊆ F := by
  rintro _ ⟨t, rfl⟩
  rw [← (QuantumTorus.basis u Λ).linearCombination_repr t]
  generalize (QuantumTorus.basis u Λ).repr t = g
  induction g using Finsupp.induction_linear with
  | zero => simp [F.zero_mem]
  | add _ _ h₁ h₂ => rw [map_add, map_add]; exact F.add_mem h₁ h₂
  | single a r =>
    rw [Finsupp.linearCombination_single, map_smul, QuantumTorus.basis_apply, c.eval_monomial,
      Algebra.smul_def]
    refine F.mul_mem (hother ((c.otherSubalgebra k).algebraMap_mem r)) ?_
    have hinv_u : c.monomial a =
        Units.map (algebraMap R D) (u ^ (-Λ (a.erase k) (Finsupp.single k (a k)))) *
          (c.monomial (a.erase k) * c.monomial (Finsupp.single k 1) ^ a k) :=
      mul_left_cancel (a := Units.map (algebraMap R D)
        (u ^ Λ (a.erase k) (Finsupp.single k (a k)))) <| by
          rw [Units.map_algebraMap_mul_map_algebraMap, ← zpow_add, add_neg_cancel, zpow_zero,
            map_one, one_mul, ← c.monomial_single_of_self_eq_zero hkk (a k), c.monomial_mul,
            Finsupp.erase_add_single k a]
    have hu := congrArg (Units.val : Dˣ → D) hinv_u
    rw [Units.val_mul, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass,
      Units.val_zpow_eq_zpow_val] at hu
    exact hu ▸ F.mul_mem (hother ((c.otherSubalgebra k).algebraMap_mem _))
      (F.mul_mem (hother (c.monomial_mem_otherSubalgebra k Finsupp.erase_same))
        (F.zpow_mem hxk (a k)))

private theorem otherSubalgebra_subset_subfieldClosure (c : BasedChart u Λ D) (k : I) :
    (c.otherSubalgebra k : Set D) ⊆ Subfield.closure (Set.range c.eval) :=
  (SetLike.coe_subset_coe.mpr (c.otherSubalgebra_le_range_eval k)).trans Subfield.subset_closure

section ChartDivisionRing

variable (c : BasedChart u Λ D) (hΛ : Λ.IsAlt) (k : I) (y : Dˣ)
  (μ : (I →₀ ℤ) →+ ℤ)
  (hyx : ((y * c.monomial (Finsupp.single k 1) : Dˣ) : D) ∈ c.otherSubalgebra k)
  (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
    y * c.monomial a = Units.map (algebraMap R D) (u ^ (2 * μ a)) * (c.monomial a * y))

/-- Over a division ring, `exchangeOfForm` preserves `Subfield.closure (Set.range c.eval)`. -/
theorem BasedChart.subfieldClosure_exchangeOfForm
    (Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)) (hΛ' : Λ'.IsAlt)
    (hΛ'_off : ∀ a b, a k = 0 → b k = 0 → Λ' a b = Λ a b)
    (hΛ'_row : ∀ a, a k = 0 → Λ' (Finsupp.single k 1) a = μ a) :
    let c' := c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row
    Subfield.closure (Set.range c'.eval) = Subfield.closure (Set.range c.eval) := by
  intro c'
  let F := Subfield.closure (Set.range c.eval)
  let F' := Subfield.closure (Set.range c'.eval)
  have hother_F : (c.otherSubalgebra k : Set D) ⊆ F := otherSubalgebra_subset_subfieldClosure c k
  have hother_F' : (c.otherSubalgebra k : Set D) ⊆ F' :=
    c.exchangeOfForm_otherSubalgebra hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row ▸
      otherSubalgebra_subset_subfieldClosure c' k
  have hxk_F : (c.monomial (Finsupp.single k 1) : D) ∈ F :=
    Subfield.subset_closure ⟨QuantumTorus.monomial u Λ (Finsupp.single k 1),
      c.eval_monomial (Finsupp.single k 1)⟩
  have hy_F' : (y : D) ∈ F' := by
    have hck : c'.monomial (Finsupp.single k 1) = y := by simp [c']
    exact hck ▸ Subfield.subset_closure ⟨QuantumTorus.monomial u Λ' (Finsupp.single k 1),
      c'.eval_monomial (Finsupp.single k 1)⟩
  have hy_F : (y : D) ∈ F :=
    (by rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, mul_inv_cancel_right] :
      (y : D) = ((y * c.monomial (Finsupp.single k 1) : Dˣ) : D) *
        (c.monomial (Finsupp.single k 1) : D)⁻¹) ▸
      F.mul_mem (hother_F hyx) (F.inv_mem hxk_F)
  have hxk_F' : (c.monomial (Finsupp.single k 1) : D) ∈ F' :=
    (by rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, inv_mul_cancel_left] :
      (c.monomial (Finsupp.single k 1) : D) = (y : D)⁻¹ *
        ((y * c.monomial (Finsupp.single k 1) : Dˣ) : D)) ▸
      F'.mul_mem (F'.inv_mem hy_F') (hother_F' hyx)
  refine le_antisymm (Subfield.closure_le.mpr ?_) (Subfield.closure_le.mpr ?_)
  · exact range_eval_subset_subfield c' (hΛ'.self_eq_zero _)
      (by rwa [c.exchangeOfForm_otherSubalgebra]) (by simpa [c'] using hy_F)
  · exact range_eval_subset_subfield c (hΛ.self_eq_zero _) hother_F' hxk_F'

end ChartDivisionRing

/-- Over a division ring, `exchange` preserves `Subfield.closure (Set.range c.eval)`. -/
theorem BasedChart.subfieldClosure_exchange [DecidableEq I] {A : Matrix I I ℤ}
    (c : BasedChart u A.finsuppBilinForm D) (hA : A.finsuppBilinForm.IsAlt) (k : I) (y : Dˣ)
    (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.monomial (Finsupp.single k 1) : Dˣ) : D) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a = Units.map (algebraMap R D) (u ^ (2 * μ a)) * (c.monomial a * y)) :
    Subfield.closure (Set.range (c.exchange hA k y μ hyx hy_comm).eval) =
      Subfield.closure (Set.range c.eval) :=
  c.subfieldClosure_exchangeOfForm hA k y μ hyx hy_comm _ _ _ _

/-- Over a division ring, quantum-torus maps related by one-step exchange generate the same
subfield. -/
theorem QuantumTorus.subfieldClosure_eq_of_exchange
    (hΛ : Λ.IsAlt) (hΛ' : Λ'.IsAlt) {k : I}
    {χ : QuantumTorus R (I →₀ ℤ) u Λ →ₐ[R] D} (hχ : Function.Injective χ)
    {χ' : QuantumTorus R (I →₀ ℤ) u Λ' →ₐ[R] D}
    (h_off : ∀ i ≠ k, χ' (QuantumTorus.monomial u Λ' (Finsupp.single i 1)) =
      χ (QuantumTorus.monomial u Λ (Finsupp.single i 1)))
    (hΛ'_off : ∀ a b, a k = 0 → b k = 0 → Λ' a b = Λ a b)
    (h_exch : χ' (QuantumTorus.monomial u Λ' (Finsupp.single k 1)) *
      χ (QuantumTorus.monomial u Λ (Finsupp.single k 1)) ∈
      (BasedChart.ofInjective χ hχ).otherSubalgebra k) :
    Subfield.closure (Set.range χ') = Subfield.closure (Set.range χ) := by
  obtain ⟨y, hyx, hy_comm, hχ'_eq⟩ :=
    QuantumTorus.exists_basedChart_of_exchange hΛ hΛ' hχ h_off hΛ'_off h_exch
  rw [← hχ'_eq]
  conv_rhs => rw [← BasedChart.eval_ofInjective χ hχ]
  exact (BasedChart.ofInjective χ hχ).subfieldClosure_exchangeOfForm hΛ k y _ hyx hy_comm
    Λ' hΛ' hΛ'_off (by simp)

end DivisionRing

end TauCeti
