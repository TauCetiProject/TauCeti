/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic
public import TauCeti.Algebra.Cluster.BasedChart.Basic
public import TauCeti.Algebra.Cluster.OneExchange
import Mathlib.Tactic.Ring

/-!
# One-step skew exchange of based charts

For `c : BasedChart R u Λ B` and `k : I`, the monomials `M(a)` with `a k = 0` span
`c.otherSubalgebra k` with `R`-basis `c.otherBasis k`. When `Λ` is alternating, `x = c.coordinate k`
normalizes `(c.otherSubalgebra k).toSubsemiring` with unique left Laurent expansions
(`BasedChart.skewLaurentSum_coordinate_injective`). For `y : Bˣ` and `μ : (I →₀ ℤ) →+ ℤ` with
`(y * x : B) ∈ c.otherSubalgebra k` and `(u, 2 • μ)`-quasi-commutation off `k`, Laurent uniqueness
transfers to `y`, making `c.mutatedMonomial k y μ` a mutated chart (`BasedChart.exchangeOfForm`,
`BasedChart.exchange`) preserving `Subfield.closure` (`BasedTorus.subfieldClosure_eq_of_exchange`).
References: Berenstein–Zelevinsky, *Adv. Math.* 195 (2005), §§4–5; *Cluster algebras III*, §4.
-/
public section
open scoped Pointwise
namespace TauCeti
private theorem val_unitsMap_algebraMap {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    (w : Rˣ) : ((Units.map (algebraMap R B).toMonoidHom w : Bˣ) : B) = algebraMap R B w := by simp
namespace BasedChart
section Semiring
variable {R I B : Type*} [CommSemiring R] {u : Rˣ} {Λ : Matrix I I ℤ} [Semiring B] [Algebra R B]
/-- The `R`-submodule of `B` spanned by the normalized monomials `M(a)` with `a k = 0`. -/
def otherSubmodule (c : BasedChart R u Λ B) (k : I) : Submodule R B :=
  Submodule.span R (Set.range fun a : { a : I →₀ ℤ // a k = 0 } ↦ (c.monomial a.1 : B))
theorem monomial_mem_otherSubmodule (c : BasedChart R u Λ B) (k : I) {a : I →₀ ℤ}
    (ha : a k = 0) : (c.monomial a : B) ∈ c.otherSubmodule k := Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
theorem one_mem_otherSubmodule (c : BasedChart R u Λ B) (k : I) :
    (1 : B) ∈ c.otherSubmodule k := by
  rw [← c.val_monomial_zero]; exact c.monomial_mem_otherSubmodule k Finsupp.zero_apply
theorem mul_mem_otherSubmodule (c : BasedChart R u Λ B) (k : I) {x y : B}
    (hx : x ∈ c.otherSubmodule k) (hy : y ∈ c.otherSubmodule k) : x * y ∈ c.otherSubmodule k := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ c.otherSubmodule k)
    (fun _ _ hx hy ↦ ?_) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ by rw [add_mul]; exact Submodule.add_mem _ h₁ h₂)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ by rw [mul_add]; exact Submodule.add_mem _ h₁ h₂)
    (fun r _ _ _ _ h ↦ by rw [Algebra.smul_mul_assoc]; exact Submodule.smul_mem _ r h)
    (fun r _ _ _ _ h ↦ by rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ r h) hx hy
  rcases hx with ⟨a, rfl⟩; rcases hy with ⟨b, rfl⟩; rw [c.val_monomial_mul]
  exact Submodule.smul_mem _ _ (c.monomial_mem_otherSubmodule k (by simp [a.2, b.2]))
/-- The `R`-subalgebra of `B` spanned by the normalized monomials `M(a)` with `a k = 0`. -/
def otherSubalgebra (c : BasedChart R u Λ B) (k : I) : Subalgebra R B :=
  (c.otherSubmodule k).toSubalgebra (c.one_mem_otherSubmodule k)
    fun _ _ ↦ c.mul_mem_otherSubmodule k
@[simp] theorem toSubmodule_otherSubalgebra (c : BasedChart R u Λ B) (k : I) :
    (c.otherSubalgebra k).toSubmodule = c.otherSubmodule k := (rfl)
theorem mem_otherSubalgebra_iff (c : BasedChart R u Λ B) (k : I) {b : B} :
    b ∈ c.otherSubalgebra k ↔ b ∈ c.otherSubmodule k := Iff.rfl
theorem monomial_mem_otherSubalgebra (c : BasedChart R u Λ B) (k : I) {a : I →₀ ℤ}
    (ha : a k = 0) : (c.monomial a : B) ∈ c.otherSubalgebra k := c.monomial_mem_otherSubmodule k ha
theorem coordinate_mem_otherSubalgebra_of_ne (c : BasedChart R u Λ B) {i k : I} (hik : i ≠ k) :
    (c.coordinate i : B) ∈ c.otherSubalgebra k := by
  rw [coordinate_def]; exact c.monomial_mem_otherSubalgebra k (Finsupp.single_eq_of_ne hik.symm)
theorem otherSubalgebra_le_range_toAlgHom (c : BasedChart R u Λ B) (k : I) :
    c.otherSubalgebra k ≤ c.toAlgHom.range := by
  rw [← Subalgebra.toSubmodule.le_iff_le, toSubmodule_otherSubalgebra, otherSubmodule,
    Submodule.span_le]
  rintro _ ⟨a, rfl⟩; exact ⟨BasedTorus.monomial a.1, c.toAlgHom_monomial a.1⟩
/-- The `R`-basis of `c.otherSubalgebra k` indexed by `{ a : I →₀ ℤ // a k = 0 }`. -/
noncomputable def otherBasis (c : BasedChart R u Λ B) (k : I) :
    Module.Basis { a : I →₀ ℤ // a k = 0 } R (c.otherSubalgebra k) :=
  (Module.Basis.span (v := fun a : { a : I →₀ ℤ // a k = 0 } ↦ (c.monomial a.1 : B))
    (c.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    { toFun := fun x ↦ ⟨x.1, x.2⟩, invFun := fun x ↦ ⟨x.1, x.2⟩, map_add' := fun _ _ ↦ rfl,
      map_smul' := fun _ _ ↦ rfl, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
@[simp] theorem coe_otherBasis (c : BasedChart R u Λ B) (k : I) (a : { a : I →₀ ℤ // a k = 0 }) :
    ((c.otherBasis k a : c.otherSubalgebra k) : B) = c.monomial a.1 := by simp [otherBasis]
private noncomputable def otherCoeffEquiv (c : BasedChart R u Λ B) (k : I) :
    (c.otherSubalgebra k).toSubsemiring ≃+ ({ a : I →₀ ℤ // a k = 0 } →₀ R) where
  toFun b := (c.otherBasis k).repr ⟨b.1, b.2⟩
  invFun f := ⟨((c.otherBasis k).repr.symm f).1, ((c.otherBasis k).repr.symm f).2⟩
  left_inv _ := Subtype.ext <| congrArg Subtype.val <| (c.otherBasis k).repr.symm_apply_apply _
  right_inv := (c.otherBasis k).repr.apply_symm_apply
  map_add' b₁ b₂ := map_add (c.otherBasis k).repr ⟨b₁.1, b₁.2⟩ ⟨b₂.1, b₂.2⟩
private theorem coe_otherCoeffEquiv_symm_single (c : BasedChart R u Λ B) (k : I)
    (a₀ : { a : I →₀ ℤ // a k = 0 }) (r : R) :
    (((c.otherCoeffEquiv k).symm (Finsupp.single a₀ r) : (c.otherSubalgebra k).toSubsemiring) : B) =
      r • (c.monomial a₀.1 : B) := by simp [otherCoeffEquiv]
private noncomputable def splitExponentEquiv [DecidableEq I] (k : I) :
    ℤ × { a : I →₀ ℤ // a k = 0 } ≃ (I →₀ ℤ) where
  toFun p := p.2.1 + Finsupp.single k p.1
  invFun a := (a k, ⟨a.erase k, Finsupp.erase_same⟩)
  left_inv := fun ⟨_, a₀⟩ ↦ Prod.ext (by simp [a₀.2]) <| Subtype.ext <| Finsupp.ext fun i ↦ by
    by_cases hik : i = k <;> simp [hik, a₀.2]
  right_inv a := Finsupp.erase_add_single k a
private noncomputable def mulUnitsAddEquiv {α : Type*} (w : α → Rˣ) : (α →₀ R) ≃+ (α →₀ R) where
  toFun g := Finsupp.onFinset g.support (fun a ↦ g a * (w a : R)) fun _ h ↦
    Finsupp.mem_support_iff.mpr fun hg ↦ h (by rw [hg, zero_mul])
  invFun g := Finsupp.onFinset g.support (fun a ↦ g a * (((w a)⁻¹ : Rˣ) : R)) fun _ h ↦
    Finsupp.mem_support_iff.mpr fun hg ↦ h (by rw [hg, zero_mul])
  left_inv g := by ext a; simp [mul_assoc, ← Units.val_mul]
  right_inv g := by ext a; simp [mul_assoc, ← Units.val_mul]
  map_add' _ _ := by ext; simp [add_mul]
private theorem mulUnitsAddEquiv_symm_single {α : Type*} (w : α → Rˣ) (a : α) (r : R) :
    (mulUnitsAddEquiv w).symm (Finsupp.single a r) =
      Finsupp.single a (r * (((w a)⁻¹ : Rˣ) : R)) := by
  classical ext b; by_cases h : b = a
  · subst h; simp [mulUnitsAddEquiv]
  · simp [mulUnitsAddEquiv, Finsupp.single_eq_of_ne h]
private noncomputable def laurentCoeffEquiv [DecidableEq I] (c : BasedChart R u Λ B) (k : I)
    (w : (I →₀ ℤ) → Rˣ) : (ℤ →₀ (c.otherSubalgebra k).toSubsemiring) ≃+ ((I →₀ ℤ) →₀ R) :=
  (Finsupp.mapRange.addEquiv (c.otherCoeffEquiv k)).trans <| Finsupp.curryAddEquiv.symm.trans <|
    (Finsupp.domCongr (splitExponentEquiv k)).trans (mulUnitsAddEquiv w)
private theorem laurentCoeffEquiv_apply [DecidableEq I] (c : BasedChart R u Λ B) (k : I)
    (w : (I →₀ ℤ) → Rˣ) (f : ℤ →₀ (c.otherSubalgebra k).toSubsemiring) (a : I →₀ ℤ) :
    c.laurentCoeffEquiv k w f a =
      c.otherCoeffEquiv k (f (a k)) ⟨a.erase k, Finsupp.erase_same⟩ * (w a : R) := rfl
private theorem laurentCoeffEquiv_symm_single [DecidableEq I] (c : BasedChart R u Λ B) (k : I)
    (w : (I →₀ ℤ) → Rˣ) (a : I →₀ ℤ) (r : R) :
    (c.laurentCoeffEquiv k w).symm (Finsupp.single a r) =
      Finsupp.single (a k) ((c.otherCoeffEquiv k).symm
        (Finsupp.single ⟨a.erase k, Finsupp.erase_same⟩ (r * (((w a)⁻¹ : Rˣ) : R)))) := by
  simp only [laurentCoeffEquiv, AddEquiv.symm_trans_apply, AddEquiv.symm_symm]
  rw [mulUnitsAddEquiv_symm_single, Finsupp.domCongr_symm, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_single, Finsupp.coe_curryAddEquiv, Finsupp.curry_single]
  simp [splitExponentEquiv]
private theorem skewLaurentSum_laurentCoeffEquiv_symm [DecidableEq I] (c : BasedChart R u Λ B)
    (k : I) (z : Bˣ) (M : (I →₀ ℤ) → B) (w : (I →₀ ℤ) → Rˣ)
    (hM : ∀ a : I →₀ ℤ, (c.monomial (a.erase k) : B) * ((z ^ a k : Bˣ) : B) = (w a : R) • M a)
    (g : (I →₀ ℤ) →₀ R) :
    (c.otherSubalgebra k).toSubsemiring.skewLaurentSum z ((c.laurentCoeffEquiv k w).symm g) =
      Finsupp.linearCombination R M g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add _ _ h₁ h₂ => simp [map_add, h₁, h₂]
  | single a r =>
    rw [c.laurentCoeffEquiv_symm_single, Subsemiring.skewLaurentSum_single,
      c.coe_otherCoeffEquiv_symm_single, Finsupp.linearCombination_single, Algebra.smul_mul_assoc,
      hM, smul_smul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
private theorem conj_mem_otherSubalgebra_of_monomial (c : BasedChart R u Λ B) (k : I) {z : Bˣ}
    (hz : ∀ a : I →₀ ℤ, a k = 0 →
      (z : B) * (c.monomial a : B) * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k)
    {b : B} (hb : b ∈ c.otherSubalgebra k) :
    (z : B) * b * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k :=
  Submodule.span_induction (p := fun b _ ↦ (z : B) * b * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k)
    (fun _ hx ↦ by rcases hx with ⟨a, rfl⟩; exact hz a.1 a.2)
    (by simp [(c.otherSubalgebra k).zero_mem])
    (fun _ _ _ _ h₁ h₂ ↦ by rw [mul_add, add_mul]; exact (c.otherSubalgebra k).add_mem h₁ h₂)
    (fun r _ _ h ↦ by
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      exact Submodule.smul_mem (c.otherSubmodule k) r h) hb
/-- A unit `z : Bˣ` normalizes `c.otherSubalgebra k` whenever conjugation by `z` and `z⁻¹` sends
every monomial `c.monomial a` with `a k = 0` back into `c.otherSubalgebra k`. -/
theorem conjAct_otherSubalgebra_of_monomial (c : BasedChart R u Λ B) (k : I) {z : Bˣ}
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
private theorem unitsMap_mul_left_comm (w : Rˣ) (x z : Bˣ) :
    x * (Units.map (algebraMap R B).toMonoidHom w * z) =
      Units.map (algebraMap R B).toMonoidHom w * (x * z) := by
  have hc : x * Units.map (algebraMap R B).toMonoidHom w =
      Units.map (algebraMap R B).toMonoidHom w * x :=
    Units.ext (Algebra.commutes (w : R) (x : B)).symm
  rw [← mul_assoc, hc, mul_assoc]
private theorem unitsMap_mul_unitsMap (w₁ w₂ : Rˣ) (x : Bˣ) :
    Units.map (algebraMap R B).toMonoidHom w₁ * (Units.map (algebraMap R B).toMonoidHom w₂ * x) =
      Units.map (algebraMap R B).toMonoidHom (w₁ * w₂) * x := by rw [← mul_assoc, ← map_mul]
private theorem unitsMap_mul_monomial_mem (c : BasedChart R u Λ B) (k : I) (w : Rˣ) {a : I →₀ ℤ}
    (ha : a k = 0) :
    ((Units.map (algebraMap R B).toMonoidHom w * c.monomial a : Bˣ) : B) ∈ c.otherSubalgebra k := by
  rw [Units.val_mul]; exact (c.otherSubalgebra k).mul_mem
    (by simp [(c.otherSubalgebra k).algebraMap_mem]) (c.monomial_mem_otherSubalgebra k ha)
/-- When `Λ` is alternating, the `k`-th chart coordinate normalizes `c.otherSubalgebra k`. -/
theorem conjAct_coordinate_otherSubalgebra (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) :
    ConjAct.toConjAct (c.coordinate k) • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring := by
  refine c.conjAct_otherSubalgebra_of_monomial k (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · rw [← Units.val_mul, ← Units.val_mul, coordinate_def,
      c.monomial_mul_comm_of_isAlt hΛ (Finsupp.single k 1) a, mul_assoc, mul_inv_cancel_right]
    exact c.unitsMap_mul_monomial_mem k _ ha
  · rw [← Units.val_mul, ← Units.val_mul, mul_assoc, coordinate_def,
      c.monomial_mul_comm_of_isAlt hΛ a (Finsupp.single k 1), unitsMap_mul_left_comm,
      inv_mul_cancel_left]
    exact c.unitsMap_mul_monomial_mem k _ ha
/-- When `Λ k k = 0`, finite left Laurent expansions in `c.coordinate k` over `c.otherSubalgebra k`
are unique. -/
theorem skewLaurentSum_coordinate_injective (c : BasedChart R u Λ B) {k : I} (hkk : Λ k k = 0) :
    Function.Injective ((c.otherSubalgebra k).toSubsemiring.skewLaurentSum (c.coordinate k)) := by
  classical
  let w (a : I →₀ ℤ) : Rˣ := u ^ Λ.finsuppBilinForm (a.erase k) (Finsupp.single k (a k))
  have heval (f : ℤ →₀ (c.otherSubalgebra k).toSubsemiring) :
      (c.otherSubalgebra k).toSubsemiring.skewLaurentSum (c.coordinate k) f =
        c.eval (c.laurentCoeffEquiv k w f) := by
    simpa [eval_def] using c.skewLaurentSum_laurentCoeffEquiv_symm k (c.coordinate k)
      (fun a ↦ (c.monomial a : B)) w (fun a ↦ by
        rw [← c.monomial_single_of_diag_zero hkk (a k), c.val_monomial_mul,
          Finsupp.erase_add_single k a]) (c.laurentCoeffEquiv k w f)
  intro f₁ f₂ h
  exact (c.laurentCoeffEquiv k w).injective (c.eval_injective (by rw [← heval, ← heval, h]))
/-- The mutated normalized monomial family `u ^ (-(a k * μ (a.erase k))) * (y ^ a k * M(a.erase k))`
at index `k`. -/
noncomputable def mutatedMonomial (c : BasedChart R u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) (a : I →₀ ℤ) : Bˣ :=
  Units.map (algebraMap R B).toMonoidHom (u ^ (-(a k * μ (a.erase k)))) *
    (y ^ a k * c.monomial (a.erase k))
@[simp] theorem mutatedMonomial_zero (c : BasedChart R u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) : c.mutatedMonomial k y μ 0 = 1 := by
  simp [mutatedMonomial, c.monomial_zero]
theorem mutatedMonomial_of_apply_eq_zero (c : BasedChart R u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) {a : I →₀ ℤ} (ha : a k = 0) :
    c.mutatedMonomial k y μ a = c.monomial a := by
  rw [mutatedMonomial, ha, Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr ha)]
  simp
@[simp] theorem mutatedMonomial_single_same (c : BasedChart R u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) (n : ℤ) : c.mutatedMonomial k y μ (Finsupp.single k n) = y ^ n := by
  simp [mutatedMonomial, c.monomial_zero]
theorem mutatedMonomial_single_of_ne (c : BasedChart R u Λ B) {i k : I} (hik : i ≠ k) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) (n : ℤ) :
    c.mutatedMonomial k y μ (Finsupp.single i n) = c.monomial (Finsupp.single i n) :=
  c.mutatedMonomial_of_apply_eq_zero k y μ (Finsupp.single_eq_of_ne hik.symm)
section QuasiComm
variable (c : BasedChart R u Λ B) {k : I} {y : Bˣ} {μ : (I →₀ ℤ) →+ ℤ}
  (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
    y * c.monomial a = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
include hy_comm
/-- Integer powers of `y` inherit `(u, 2 • μ)`-quasi-commutation against monomials off `k`. -/
theorem zpow_mul_monomial_of_quasiComm (n : ℤ) {a : I →₀ ℤ} (ha : a k = 0) :
    y ^ n * c.monomial a =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * n * μ a)) * (c.monomial a * y ^ n) := by
  rw [units_zpow_mul_of_quasiComm (hy_comm a ha) n, ← zpow_mul]; congr 3; ring
/-- Right-ordered form `u ^ (a k * μ (a.erase k)) * (M(a.erase k) * y ^ a k)` of a mutated
monomial under quasi-commutation off `k`. -/
theorem mutatedMonomial_eq_mul_zpow (a : I →₀ ℤ) :
    c.mutatedMonomial k y μ a =
      Units.map (algebraMap R B).toMonoidHom (u ^ (a k * μ (a.erase k))) *
        (c.monomial (a.erase k) * y ^ a k) := by
  rw [mutatedMonomial, c.zpow_mul_monomial_of_quasiComm hy_comm (a k) Finsupp.erase_same,
    unitsMap_mul_unitsMap, ← zpow_add]; congr 3; ring
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
with `Λ` off `k` and having `k`-th row `μ` off `k`. -/
theorem mutatedMonomial_mul {Λ' : Matrix I I ℤ} (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 → Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a)
    (a b : I →₀ ℤ) :
    c.mutatedMonomial k y μ a * c.mutatedMonomial k y μ b =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ'.finsuppBilinForm a b) *
        c.mutatedMonomial k y μ (a + b) := by
  have hcomm_inv : c.monomial (a.erase k) * y ^ b k =
      Units.map (algebraMap R B).toMonoidHom (u ^ (-(2 * b k * μ (a.erase k)))) *
        (y ^ b k * c.monomial (a.erase k)) :=
    mul_left_cancel (a := Units.map (algebraMap R B).toMonoidHom (u ^ (2 * b k * μ (a.erase k)))) <|
      by rw [← c.zpow_mul_monomial_of_quasiComm hy_comm (b k) Finsupp.erase_same,
           unitsMap_mul_unitsMap, ← zpow_add, add_neg_cancel, zpow_zero, map_one, one_mul]
  have hform : Λ'.finsuppBilinForm a b =
      a k * μ (b.erase k) - b k * μ (a.erase k) + Λ.finsuppBilinForm (a.erase k) (b.erase k) := by
    conv_lhs => rw [← Finsupp.single_add_erase k a, ← Finsupp.single_add_erase k b]
    simp only [map_add, LinearMap.add_apply]
    rw [Matrix.finsuppBilinForm_single_single,
      Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ' k,
      (hΛ'.neg_eq (Finsupp.single k (b k)) (a.erase k)).symm,
      (by simp : Finsupp.single k (a k) = a k • Finsupp.single k 1),
      (by simp : Finsupp.single k (b k) = b k • Finsupp.single k 1)]
    simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul,
      hΛ'_row (b.erase k) Finsupp.erase_same, hΛ'_row (a.erase k) Finsupp.erase_same,
      hΛ'_off (a.erase k) (b.erase k) Finsupp.erase_same Finsupp.erase_same]; ring
  rw [mutatedMonomial, mutatedMonomial, mutatedMonomial, Finsupp.add_apply, Finsupp.erase_add,
    map_add]; simp only [mul_assoc]
  rw [unitsMap_mul_left_comm _ (c.monomial (a.erase k)), unitsMap_mul_left_comm _ (y ^ a k),
    unitsMap_mul_unitsMap, ← zpow_add, ← mul_assoc (c.monomial (a.erase k)) (y ^ b k), hcomm_inv]
  simp only [mul_assoc]; rw [unitsMap_mul_left_comm _ (y ^ a k), unitsMap_mul_unitsMap, ← zpow_add,
    ← mul_assoc (y ^ a k) (y ^ b k), ← zpow_add, c.monomial_mul,
    unitsMap_mul_left_comm _ (y ^ (a k + b k)), unitsMap_mul_unitsMap, ← zpow_add,
    unitsMap_mul_unitsMap, ← zpow_add, hform]; congr 3; ring
end QuasiComm
/-- Under alternating `Λ` and quasi-commutation off `k`, the exchange factor `y * c.coordinate k`
normalizes `c.otherSubalgebra k`. -/
theorem conjAct_mul_coordinate_otherSubalgebra (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) {k : I} {y : Bˣ} {μ : (I →₀ ℤ) →+ ℤ}
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 → y * c.monomial a =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y)) :
    ConjAct.toConjAct (y * c.coordinate k) • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring := by
  rw [map_mul, mul_smul, c.conjAct_coordinate_otherSubalgebra hΛ k,
    c.conjAct_unit_otherSubalgebra hy_comm]
/-- When `Λ` is alternating and `(y * c.coordinate k : B) ∈ c.otherSubalgebra k`, finite left
Laurent expansions in `y` over `c.otherSubalgebra k` are unique. -/
theorem skewLaurentSum_exchange_injective (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) {k : I} {y : Bˣ}
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k) :
    Function.Injective ((c.otherSubalgebra k).toSubsemiring.skewLaurentSum y) := by
  rw [← mul_inv_cancel_right y (c.coordinate k)]
  exact Subsemiring.skewLaurentSum_mul_inv_injective (c.conjAct_coordinate_otherSubalgebra hΛ k) hyx
    (c.skewLaurentSum_coordinate_injective
      (Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ k))
/-- For alternating `Λ`, `(y * c.coordinate k : B) ∈ c.otherSubalgebra k`, and `(u, 2 • μ)`-quasi-
commutation off `k`, the mutated normalized monomials `c.mutatedMonomial k y μ` are `R`-linearly
independent. -/
theorem linearIndependent_mutatedMonomial (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) {k : I} {y : Bˣ} {μ : (I →₀ ℤ) →+ ℤ}
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 → y * c.monomial a =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y)) :
    LinearIndependent R fun a ↦ (c.mutatedMonomial k y μ a : B) := by
  classical
  let w (a : I →₀ ℤ) : Rˣ := (u ^ (a k * μ (a.erase k)))⁻¹
  have heval := c.skewLaurentSum_laurentCoeffEquiv_symm k y
    (fun a ↦ (c.mutatedMonomial k y μ a : B)) w fun a ↦ by
      have hm := congrArg (Units.val : Bˣ → B) (c.mutatedMonomial_eq_mul_zpow hy_comm a)
      rw [Units.val_mul, Units.val_mul, val_unitsMap_algebraMap, ← Algebra.smul_def] at hm
      rw [hm, smul_smul, ← Units.val_mul (w a)]; simp [w]
  intro g₁ g₂ h
  exact (c.laurentCoeffEquiv k w).symm.injective
    (c.skewLaurentSum_exchange_injective hΛ hyx (by rw [heval, heval, h]))
section ExchangeOfForm
variable (c : BasedChart R u Λ B) (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ)
  (μ : (I →₀ ℤ) →+ ℤ) (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
  (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
    y * c.monomial a = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
  (Λ' : Matrix I I ℤ) (hΛ' : Λ'.finsuppBilinForm.IsAlt)
  (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
  (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 → Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a)
/-- **One-step skew exchange of a based chart** for a compatible alternating form `Λ'`. -/
noncomputable def exchangeOfForm : BasedChart R u Λ' B where
  monomial := c.mutatedMonomial k y μ
  monomial_zero := c.mutatedMonomial_zero k y μ
  monomial_mul := c.mutatedMonomial_mul hy_comm hΛ' hΛ'_off hΛ'_row
  linearIndependent := c.linearIndependent_mutatedMonomial hΛ hyx hy_comm
@[simp] theorem exchangeOfForm_monomial (a : I →₀ ℤ) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).monomial a =
      c.mutatedMonomial k y μ a := (rfl)
theorem exchangeOfForm_monomial_of_apply_eq_zero {a : I →₀ ℤ} (ha : a k = 0) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).monomial a = c.monomial a :=
  c.mutatedMonomial_of_apply_eq_zero k y μ ha
@[simp] theorem exchangeOfForm_coordinate_same :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).coordinate k = y := by
  simp [coordinate_def]
theorem exchangeOfForm_coordinate_of_ne {i : I} (hik : i ≠ k) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).coordinate i =
      c.coordinate i := by
  rw [coordinate_def, exchangeOfForm_monomial, c.mutatedMonomial_single_of_ne hik, ← coordinate_def]
/-- `BasedChart.exchangeOfForm` at `k` preserves `c.otherSubalgebra k`. -/
@[simp] theorem exchangeOfForm_otherSubalgebra :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).otherSubalgebra k =
      c.otherSubalgebra k := by
  apply Subalgebra.toSubmodule_injective
  simp only [toSubmodule_otherSubalgebra, otherSubmodule]; congr 1; ext b
  simp only [Set.mem_range, Subtype.exists]
  exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, ha, by simpa [c.mutatedMonomial_of_apply_eq_zero k y μ ha] using h⟩,
    fun ⟨a, ha, h⟩ ↦ ⟨a, ha, by simpa [c.mutatedMonomial_of_apply_eq_zero k y μ ha] using h⟩⟩
end ExchangeOfForm
section Exchange
variable [DecidableEq I] (c : BasedChart R u Λ B) (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ)
  (μ : (I →₀ ℤ) →+ ℤ) (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
  (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
    y * c.monomial a = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
/-- **One-step skew exchange of a based chart** with canonical updated form
`Λ.updateSkew k (fun j ↦ μ (Finsupp.single j 1))`. -/
noncomputable def exchange :
    BasedChart R u (Λ.updateSkew k fun j ↦ μ (Finsupp.single j 1)) B :=
  c.exchangeOfForm hΛ k y μ hyx hy_comm (Λ.updateSkew k fun j ↦ μ (Finsupp.single j 1))
    (Matrix.isAlt_finsuppBilinForm_updateSkew hΛ k _)
    (fun _ _ ha hb ↦ Matrix.finsuppBilinForm_updateSkew_of_apply_eq_zero Λ k _ ha hb)
    fun a ha ↦ by
      rw [Matrix.finsuppBilinForm_updateSkew_single_left Λ k _ 1 ha, one_mul]; clear ha
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
      | single j n =>
        rw [Finsupp.linearCombination_single, smul_eq_mul,
          (by simp : Finsupp.single j n = n • Finsupp.single j 1), map_zsmul, smul_eq_mul]
@[simp] theorem exchange_monomial (a : I →₀ ℤ) :
    (c.exchange hΛ k y μ hyx hy_comm).monomial a = c.mutatedMonomial k y μ a := (rfl)
@[simp] theorem exchange_coordinate_same :
    (c.exchange hΛ k y μ hyx hy_comm).coordinate k = y :=
  c.exchangeOfForm_coordinate_same hΛ k y μ hyx hy_comm _ _ _ _
theorem exchange_coordinate_of_ne {i : I} (hik : i ≠ k) :
    (c.exchange hΛ k y μ hyx hy_comm).coordinate i = c.coordinate i :=
  c.exchangeOfForm_coordinate_of_ne hΛ k y μ hyx hy_comm _ _ _ _ hik
/-- `BasedChart.exchange` at `k` preserves `c.otherSubalgebra k`. -/
@[simp] theorem exchange_otherSubalgebra :
    (c.exchange hΛ k y μ hyx hy_comm).otherSubalgebra k = c.otherSubalgebra k :=
  c.exchangeOfForm_otherSubalgebra hΛ k y μ hyx hy_comm _ _ _ _
end Exchange
end Semiring
end BasedChart
namespace BasedTorus
section Semiring
variable {R I B : Type*} [CommSemiring R] {u : Rˣ} {Λ Λ' : Matrix I I ℤ} [Semiring B] [Algebra R B]
private theorem unitMonomial_single_of_diag_zero {i : I} (hi : Λ i i = 0) (n : ℤ) :
    unitMonomial (R := R) (u := u) (Λ := Λ) (Finsupp.single i n) =
      (unitX (R := R) (u := u) (Λ := Λ) i) ^ n := by
  have hx : (BasedChart.tautological R u Λ).coordinate i = unitX i :=
    Units.ext (by simp [BasedChart.coordinate_def, X_def])
  simpa [hx] using (BasedChart.tautological R u Λ).monomial_single_of_diag_zero hi n
section TorusExchange
variable (hΛ : Λ.finsuppBilinForm.IsAlt) (hΛ' : Λ'.finsuppBilinForm.IsAlt) {k : I}
  {χ : basedTorus R u Λ →ₐ[R] B} {χ' : basedTorus R u Λ' →ₐ[R] B}
  (h_off : ∀ i ≠ k, χ' (X i) = χ (X i))
  (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
include hΛ hΛ' h_off hΛ'_off in
/-- Two torus maps `χ'` and `χ` agreeing on all generators `X i` with `i ≠ k` (for alternating
forms agreeing off `k`) agree on every monomial `monomial a` with `a k = 0`. -/
theorem algHom_monomial_eq_of_apply_eq_zero {a : I →₀ ℤ} (ha : a k = 0) :
    χ' (monomial a) = χ (monomial a) := by
  classical
  suffices Units.map χ'.toMonoidHom (unitMonomial a) = Units.map χ.toMonoidHom (unitMonomial a) by
    simpa [val_unitMonomial] using congrArg (Units.val : Bˣ → B) this
  induction a using Finsupp.induction with
  | zero => ext; simp [val_unitMonomial]
  | single_add i n f hif hn ih =>
    have hik : i ≠ k := by rintro rfl; simp [Finsupp.notMem_support_iff.mp hif, hn] at ha
    have hfk : f k = 0 := by simpa [Finsupp.add_apply, Finsupp.single_eq_of_ne hik.symm] using ha
    have hsingle : Units.map χ'.toMonoidHom (unitMonomial (Finsupp.single i n)) =
        Units.map χ.toMonoidHom (unitMonomial (Finsupp.single i n)) := by
      have h0' := Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ' i
      have h0 := Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ i
      rw [unitMonomial_single_of_diag_zero h0', unitMonomial_single_of_diag_zero h0,
        map_zpow, map_zpow]
      exact congrArg (· ^ n) (Units.ext <| by simpa [val_unitX] using h_off i hik)
    have hmul₁ := unitsMap_unitMonomial_mul χ' (Finsupp.single i n) f
    have hmul₂ := unitsMap_unitMonomial_mul χ (Finsupp.single i n) f
    rw [hΛ'_off _ _ (Finsupp.single_eq_of_ne hik.symm) hfk] at hmul₁
    exact mul_left_cancel (hmul₁.symm.trans (by rw [hsingle, ih hfk, hmul₂]))
end TorusExchange
/-- Given an injective torus map `χ : basedTorus R u Λ →ₐ[R] B` and a map
`χ' : basedTorus R u Λ' →ₐ[R] B` agreeing off `k` with `χ' (X k) * χ (X k) ∈ otherSubalgebra k`,
`χ'` arises as the `toAlgHom` of a one-step `exchangeOfForm` of `BasedChart.ofAlgHom χ hχ`. -/
theorem exists_basedChart_of_exchange
    (hΛ : Λ.finsuppBilinForm.IsAlt) (hΛ' : Λ'.finsuppBilinForm.IsAlt) {k : I}
    {χ : basedTorus R u Λ →ₐ[R] B} (hχ : Function.Injective χ)
    {χ' : basedTorus R u Λ' →ₐ[R] B} (h_off : ∀ i ≠ k, χ' (X i) = χ (X i))
    (hΛ'_off : ∀ a b, a k = 0 → b k = 0 → Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (h_exch : χ' (X k) * χ (X k) ∈ (BasedChart.ofAlgHom χ hχ).otherSubalgebra k) :
    ∃ (y : Bˣ) (hyx : ((y * (BasedChart.ofAlgHom χ hχ).coordinate k : Bˣ) : B) ∈
        (BasedChart.ofAlgHom χ hχ).otherSubalgebra k)
      (hy_comm : ∀ a : I →₀ ℤ, a k = 0 → y * (BasedChart.ofAlgHom χ hχ).monomial a =
        Units.map (algebraMap R B).toMonoidHom
          (u ^ (2 * (Λ'.finsuppBilinForm (Finsupp.single k 1)).toAddMonoidHom a)) *
          ((BasedChart.ofAlgHom χ hχ).monomial a * y)),
      ((BasedChart.ofAlgHom χ hχ).exchangeOfForm hΛ k y
        (Λ'.finsuppBilinForm (Finsupp.single k 1)).toAddMonoidHom hyx hy_comm Λ' hΛ' hΛ'_off
        (by simp)).toAlgHom = χ' := by
  classical
  let c := BasedChart.ofAlgHom χ hχ; let y : Bˣ := Units.map χ'.toMonoidHom (unitX k)
  let μ : (I →₀ ℤ) →+ ℤ := (Λ'.finsuppBilinForm (Finsupp.single k 1)).toAddMonoidHom
  have hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k := by
    simpa [y, c, BasedChart.coordinate_def, X_def, val_unitX] using h_exch
  have hy_comm (a : I →₀ ℤ) (ha : a k = 0) :
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y) := by
    ext; rw [Units.val_mul, Units.val_mul, Units.val_mul, val_unitsMap_algebraMap]
    have hmap := congrArg χ'
      (monomial_mul_comm_of_isAlt (R := R) (u := u) hΛ' (Finsupp.single k 1) a)
    rw [map_mul, Algebra.smul_def, map_mul, AlgHom.commutes, map_mul, ← X_def,
      algHom_monomial_eq_of_apply_eq_zero hΛ hΛ' h_off hΛ'_off ha] at hmap
    simpa [val_unitX, c, y, μ] using hmap
  refine ⟨y, hyx, hy_comm, algHom_ext_X fun i ↦ ?_⟩
  rcases eq_or_ne k i with rfl | hik
  · rw [BasedChart.toAlgHom_X, BasedChart.exchangeOfForm_coordinate_same]; simp [y, val_unitX]
  · rw [BasedChart.toAlgHom_X,
      BasedChart.exchangeOfForm_coordinate_of_ne c hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off _ hik.symm]
    simpa [c, BasedChart.coordinate_def, X_def] using (h_off i hik.symm).symm
/-- **Transfer of torus-map injectivity under one-step exchange**: if `χ` is injective and `χ'`
agrees with `χ` off `k` with `χ' (X k) * χ (X k) ∈ otherSubalgebra k`, then `χ'` is injective. -/
theorem injective_of_exchange
    (hΛ : Λ.finsuppBilinForm.IsAlt) (hΛ' : Λ'.finsuppBilinForm.IsAlt) {k : I}
    {χ : basedTorus R u Λ →ₐ[R] B} (hχ : Function.Injective χ)
    {χ' : basedTorus R u Λ' →ₐ[R] B} (h_off : ∀ i ≠ k, χ' (X i) = χ (X i))
    (hΛ'_off : ∀ a b, a k = 0 → b k = 0 → Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (h_exch : χ' (X k) * χ (X k) ∈ (BasedChart.ofAlgHom χ hχ).otherSubalgebra k) :
    Function.Injective χ' := by
  obtain ⟨_, _, _, hχ'_eq⟩ := exists_basedChart_of_exchange hΛ hΛ' hχ h_off hΛ'_off h_exch
  exact hχ'_eq ▸ BasedChart.toAlgHom_injective _
end Semiring
end BasedTorus
section DivisionRing
variable {R I D : Type*} [CommSemiring R] {u : Rˣ} {Λ Λ' : Matrix I I ℤ}
  [DivisionRing D] [Algebra R D]
private theorem range_toAlgHom_subset_subfield (c : BasedChart R u Λ D) {k : I} (hkk : Λ k k = 0)
    {F : Subfield D} (hother : (c.otherSubalgebra k : Set D) ⊆ F)
    (hxk : (c.coordinate k : D) ∈ F) : Set.range c.toAlgHom ⊆ F := by
  rintro _ ⟨t, rfl⟩
  rw [← (BasedTorus.basis R u Λ).linearCombination_repr t]
  generalize (BasedTorus.basis R u Λ).repr t = g
  induction g using Finsupp.induction_linear with
  | zero => simp [F.zero_mem]
  | add _ _ h₁ h₂ => rw [map_add, map_add]; exact F.add_mem h₁ h₂
  | single a r =>
    rw [Finsupp.linearCombination_single, map_smul, BasedTorus.basis_apply, c.toAlgHom_monomial,
      Algebra.smul_def]
    refine F.mul_mem (hother ((c.otherSubalgebra k).algebraMap_mem r)) ?_
    have hinv_u : c.monomial a =
        Units.map (algebraMap R D).toMonoidHom
          (u ^ (-Λ.finsuppBilinForm (a.erase k) (Finsupp.single k (a k)))) *
          (c.monomial (a.erase k) * c.coordinate k ^ a k) :=
      mul_left_cancel (a := Units.map (algebraMap R D).toMonoidHom
        (u ^ Λ.finsuppBilinForm (a.erase k) (Finsupp.single k (a k)))) <| by
          rw [← mul_assoc, ← map_mul, ← zpow_add, add_neg_cancel, zpow_zero, map_one, one_mul,
            ← c.monomial_single_of_diag_zero hkk (a k), c.monomial_mul,
            Finsupp.erase_add_single k a]
    have hu := congrArg (Units.val : Dˣ → D) hinv_u
    rw [Units.val_mul, Units.val_mul, val_unitsMap_algebraMap, Units.val_zpow_eq_zpow_val] at hu
    exact hu ▸ F.mul_mem (hother ((c.otherSubalgebra k).algebraMap_mem _))
      (F.mul_mem (hother (c.monomial_mem_otherSubalgebra k Finsupp.erase_same))
        (F.zpow_mem hxk (a k)))
private theorem otherSubalgebra_subset_subfieldClosure (c : BasedChart R u Λ D) (k : I) :
    (c.otherSubalgebra k : Set D) ⊆ Subfield.closure (Set.range c.toAlgHom) :=
  (SetLike.coe_subset_coe.mpr (c.otherSubalgebra_le_range_toAlgHom k)).trans Subfield.subset_closure
section ChartDivisionRing
variable (c : BasedChart R u Λ D) (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Dˣ)
  (μ : (I →₀ ℤ) →+ ℤ) (hyx : ((y * c.coordinate k : Dˣ) : D) ∈ c.otherSubalgebra k)
  (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
    y * c.monomial a = Units.map (algebraMap R D).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
/-- Over a division ring, `exchangeOfForm` preserves `Subfield.closure (Set.range c.toAlgHom)`. -/
theorem BasedChart.subfieldClosure_exchangeOfForm (Λ' : Matrix I I ℤ)
    (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b, a k = 0 → b k = 0 → Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a, a k = 0 → Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a) :
    let c' := c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row
    Subfield.closure (Set.range c'.toAlgHom) = Subfield.closure (Set.range c.toAlgHom) := by
  intro c'; let F := Subfield.closure (Set.range c.toAlgHom)
  let F' := Subfield.closure (Set.range c'.toAlgHom)
  have hother_F : (c.otherSubalgebra k : Set D) ⊆ F := otherSubalgebra_subset_subfieldClosure c k
  have hother_F' : (c.otherSubalgebra k : Set D) ⊆ F' :=
    c.exchangeOfForm_otherSubalgebra hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row ▸
      otherSubalgebra_subset_subfieldClosure c' k
  have hxk_F : (c.coordinate k : D) ∈ F := Subfield.subset_closure ⟨BasedTorus.X k, c.toAlgHom_X k⟩
  have hy_F' : (y : D) ∈ F' := c.exchangeOfForm_coordinate_same hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off
    hΛ'_row ▸ Subfield.subset_closure ⟨BasedTorus.X k, c'.toAlgHom_X k⟩
  have hy_F : (y : D) ∈ F :=
    (by rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, mul_inv_cancel_right] :
      (y : D) = ((y * c.coordinate k : Dˣ) : D) * (c.coordinate k : D)⁻¹) ▸
      F.mul_mem (hother_F hyx) (F.inv_mem hxk_F)
  have hxk_F' : (c.coordinate k : D) ∈ F' :=
    (by rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, inv_mul_cancel_left] :
      (c.coordinate k : D) = (y : D)⁻¹ * ((y * c.coordinate k : Dˣ) : D)) ▸
      F'.mul_mem (F'.inv_mem hy_F') (hother_F' hyx)
  refine le_antisymm (Subfield.closure_le.mpr ?_) (Subfield.closure_le.mpr ?_)
  · exact range_toAlgHom_subset_subfield c'
      (Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ' k)
      (by rwa [c.exchangeOfForm_otherSubalgebra]) (by rwa [c.exchangeOfForm_coordinate_same])
  · exact range_toAlgHom_subset_subfield c
      (Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ k) hother_F' hxk_F'
/-- Over a division ring, `exchange` preserves `Subfield.closure (Set.range c.toAlgHom)`. -/
theorem BasedChart.subfieldClosure_exchange [DecidableEq I] :
    Subfield.closure (Set.range (c.exchange hΛ k y μ hyx hy_comm).toAlgHom) =
      Subfield.closure (Set.range c.toAlgHom) :=
  c.subfieldClosure_exchangeOfForm hΛ k y μ hyx hy_comm _ _ _ _
end ChartDivisionRing
/-- Over a division ring, torus maps related by one-step exchange generate the same subfield. -/
theorem BasedTorus.subfieldClosure_eq_of_exchange
    (hΛ : Λ.finsuppBilinForm.IsAlt) (hΛ' : Λ'.finsuppBilinForm.IsAlt) {k : I}
    {χ : basedTorus R u Λ →ₐ[R] D} (hχ : Function.Injective χ)
    {χ' : basedTorus R u Λ' →ₐ[R] D} (h_off : ∀ i ≠ k, χ' (BasedTorus.X i) = χ (BasedTorus.X i))
    (hΛ'_off : ∀ a b, a k = 0 → b k = 0 → Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (h_exch : χ' (BasedTorus.X k) * χ (BasedTorus.X k) ∈
      (BasedChart.ofAlgHom χ hχ).otherSubalgebra k) :
    Subfield.closure (Set.range χ') = Subfield.closure (Set.range χ) := by
  obtain ⟨y, hyx, hy_comm, hχ'_eq⟩ :=
    BasedTorus.exists_basedChart_of_exchange hΛ hΛ' hχ h_off hΛ'_off h_exch
  rw [← hχ'_eq]; conv_rhs => rw [← BasedChart.ofAlgHom_toAlgHom χ hχ]
  exact (BasedChart.ofAlgHom χ hχ).subfieldClosure_exchangeOfForm hΛ k y _ hyx hy_comm
    Λ' hΛ' hΛ'_off (by simp)
end DivisionRing
end TauCeti
