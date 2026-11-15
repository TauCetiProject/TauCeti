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

Given a based chart `c : BasedChart R u Λ B` in a (not necessarily commutative) `R`-algebra `B` and
an index `k : I`, the monomials `c.monomial a` with `a k = 0` span an `R`-subalgebra
`c.otherSubalgebra k` with `R`-basis `c.otherBasis k`. When `Λ` is alternating, the `k`-th
coordinate `x = c.coordinate k` normalizes `(c.otherSubalgebra k).toSubsemiring`, and `R`-linear
independence of `c` makes left Laurent expansions in `x` over `c.otherSubalgebra k` unique.

Now let `y : Bˣ` and an additive map `μ : (I →₀ ℤ) →+ ℤ` satisfy
`(y * x : B) ∈ c.otherSubalgebra k` and `y * M(a) = u ^ (2 * μ a) * (M(a) * y)` whenever `a k = 0`.
Then `E = y * x` is a unit of `B` in `c.otherSubalgebra k` normalizing
`(c.otherSubalgebra k).toSubsemiring`, and `Subsemiring.skewLaurentSum_mul_inv_injective` transfers
uniqueness of left Laurent expansions from `x` to `y = E * x⁻¹`. Consequently the mutated
normalized monomial family

`M'(a) = u ^ (-(a k * μ (a.erase k))) * (y ^ (a k) * M(a.erase k))`

is `R`-linearly independent and forms a `BasedChart R u Λ' B` for the unique alternating form `Λ'`
agreeing with `Λ` on `{ a | a k = 0 }` and pairing `single k 1` to `μ` on `{ a | a k = 0 }`. When
`B` is a division ring, the original and mutated charts generate the same division subring
(`Subfield.closure`), and any `R`-algebra map `χ' : basedTorus R u Λ' →ₐ[R] B` agreeing with a
faithful map `χ : basedTorus R u Λ →ₐ[R] B` off `k` whose `k`-th coordinate satisfies
`χ'(X_k) * χ(X_k) ∈ otherSubalgebra` is automatically injective with the same generated division
subring.

## Main definitions

* `TauCeti.BasedChart.otherSubmodule`, `TauCeti.BasedChart.otherSubalgebra`,
  `TauCeti.BasedChart.otherBasis`: the `R`-subalgebra of `B` spanned by `{ M(a) | a k = 0 }` and its
  monomial basis.
* `TauCeti.BasedChart.mutatedMonomial`: the normalized mutated monomial family
  `u ^ (-(a k * μ (a.erase k))) * (y ^ (a k) * M(a.erase k))`.
* `TauCeti.BasedChart.exchangeOfForm` and `TauCeti.BasedChart.exchange`: the mutated based chart at
  index `k` for a compatible alternating form `Λ'` (respectively `Λ.updateSkew k ...`).

## Main results

* `TauCeti.BasedChart.skewLaurentSum_coordinate_injective`: left Laurent expansions in
  `c.coordinate k` with coefficients in `c.otherSubalgebra k` are unique when `Λ k k = 0`.
* `TauCeti.BasedChart.conjAct_mul_coordinate_otherSubalgebra`: `E = y * c.coordinate k` normalizes
  `(c.otherSubalgebra k).toSubsemiring`.
* `TauCeti.BasedChart.linearIndependent_mutatedMonomial`: the mutated monomial family is
  `R`-linearly independent in every ambient `R`-algebra `B`.
* `TauCeti.BasedTorus.injective_of_exchange`: one-step exchange criterion for injectivity of an
  `R`-algebra map `basedTorus R u Λ' →ₐ[R] B`.
* `TauCeti.BasedChart.subfieldClosure_exchangeOfForm` and
  `TauCeti.BasedTorus.subfieldClosure_eq_of_exchange`: equality of generated division subrings when
  the ambient algebra is a division ring.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §§4–5,
  especially Lemmas 5.5–5.6.
* A. Berenstein, S. Fomin, and A. Zelevinsky, *Cluster algebras III: Upper bounds and double Bruhat
  cells*, Duke Math. J. 126 (2005), Lemmas 4.1–4.2.
-/

public section

open scoped Pointwise

namespace TauCeti

private theorem val_unitsMap_algebraMap {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    (w : Rˣ) : ((Units.map (algebraMap R B).toMonoidHom w : Bˣ) : B) = algebraMap R B w := by
  simp

namespace BasedChart

section Semiring

variable {R I B : Type*} [CommSemiring R] {u : Rˣ} {Λ : Matrix I I ℤ}
  [Semiring B] [Algebra R B]

/-! ### The other-coordinate subalgebra and skew-Laurent uniqueness -/

/-- The `R`-submodule of `B` spanned by the normalized monomials `M(a)` with `a k = 0`. -/
def otherSubmodule (c : BasedChart R u Λ B) (k : I) : Submodule R B :=
  Submodule.span R (Set.range fun a : { a : I →₀ ℤ // a k = 0 } ↦ (c.monomial a.1 : B))

theorem monomial_mem_otherSubmodule (c : BasedChart R u Λ B) (k : I) {a : I →₀ ℤ}
    (ha : a k = 0) : (c.monomial a : B) ∈ c.otherSubmodule k :=
  Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩

theorem one_mem_otherSubmodule (c : BasedChart R u Λ B) (k : I) :
    (1 : B) ∈ c.otherSubmodule k := by
  rw [← c.val_monomial_zero]
  exact c.monomial_mem_otherSubmodule k Finsupp.zero_apply

theorem mul_mem_otherSubmodule (c : BasedChart R u Λ B) (k : I) {x y : B}
    (hx : x ∈ c.otherSubmodule k) (hy : y ∈ c.otherSubmodule k) :
    x * y ∈ c.otherSubmodule k := by
  refine Submodule.span_induction₂
    (p := fun x y _ _ ↦ x * y ∈ c.otherSubmodule k)
    (fun x y hx hy ↦ ?_)
    (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
    (fun x₁ x₂ y _ _ _ h₁ h₂ ↦ by rw [add_mul]; exact Submodule.add_mem _ h₁ h₂)
    (fun x y₁ y₂ _ _ _ h₁ h₂ ↦ by rw [mul_add]; exact Submodule.add_mem _ h₁ h₂)
    (fun r x y _ _ h ↦ by rw [Algebra.smul_mul_assoc]; exact Submodule.smul_mem _ r h)
    (fun r x y _ _ h ↦ by rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ r h)
    hx hy
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  rw [c.val_monomial_mul]
  refine Submodule.smul_mem _ _ (c.monomial_mem_otherSubmodule k ?_)
  simp [a.2, b.2]

/-- The `R`-subalgebra of `B` spanned by the normalized monomials `M(a)` with `a k = 0`. -/
def otherSubalgebra (c : BasedChart R u Λ B) (k : I) : Subalgebra R B :=
  (c.otherSubmodule k).toSubalgebra (c.one_mem_otherSubmodule k)
    fun _ _ ↦ c.mul_mem_otherSubmodule k

@[simp]
theorem toSubmodule_otherSubalgebra (c : BasedChart R u Λ B) (k : I) :
    (c.otherSubalgebra k).toSubmodule = c.otherSubmodule k :=
  (rfl)

theorem mem_otherSubalgebra_iff (c : BasedChart R u Λ B) (k : I) {b : B} :
    b ∈ c.otherSubalgebra k ↔ b ∈ c.otherSubmodule k :=
  Iff.rfl

theorem monomial_mem_otherSubalgebra (c : BasedChart R u Λ B) (k : I) {a : I →₀ ℤ}
    (ha : a k = 0) : (c.monomial a : B) ∈ c.otherSubalgebra k :=
  c.monomial_mem_otherSubmodule k ha

theorem coordinate_mem_otherSubalgebra_of_ne (c : BasedChart R u Λ B) {i k : I} (hik : i ≠ k) :
    (c.coordinate i : B) ∈ c.otherSubalgebra k := by
  rw [coordinate_def]
  exact c.monomial_mem_otherSubalgebra k (Finsupp.single_eq_of_ne hik.symm)

theorem otherSubalgebra_le_range_toAlgHom (c : BasedChart R u Λ B) (k : I) :
    c.otherSubalgebra k ≤ c.toAlgHom.range := by
  rw [← Subalgebra.toSubmodule.le_iff_le, toSubmodule_otherSubalgebra, otherSubmodule,
    Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨BasedTorus.monomial a.1, c.toAlgHom_monomial a.1⟩

/-- The `R`-basis of `c.otherSubalgebra k` indexed by `{ a : I →₀ ℤ // a k = 0 }`. -/
noncomputable def otherBasis (c : BasedChart R u Λ B) (k : I) :
    Module.Basis { a : I →₀ ℤ // a k = 0 } R (c.otherSubalgebra k) :=
  (Module.Basis.span (v := fun a : { a : I →₀ ℤ // a k = 0 } ↦ (c.monomial a.1 : B))
    (c.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    ((LinearEquiv.ofEq
      (Submodule.span R (Set.range fun a : { a : I →₀ ℤ // a k = 0 } ↦ (c.monomial a.1 : B)))
      (Subalgebra.toSubmodule (c.otherSubalgebra k)) rfl).trans
      (Subalgebra.toSubmoduleEquiv (c.otherSubalgebra k)))

@[simp]
theorem coe_otherBasis (c : BasedChart R u Λ B) (k : I) (a : { a : I →₀ ℤ // a k = 0 }) :
    ((c.otherBasis k a : c.otherSubalgebra k) : B) = c.monomial a.1 := by
  simp only [otherBasis, Module.Basis.map_apply, LinearEquiv.trans_apply, Module.Basis.span_apply]
  rfl

private noncomputable def otherCoeffRepr (c : BasedChart R u Λ B) (k : I) :
    (c.otherSubalgebra k).toSubsemiring →+ ({ a : I →₀ ℤ // a k = 0 } →₀ R) :=
  (c.otherBasis k).repr.toAddMonoidHom.comp
    { toFun := fun b ↦ ⟨b.1, b.2⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

private theorem otherCoeffRepr_injective (c : BasedChart R u Λ B) (k : I) :
    Function.Injective (c.otherCoeffRepr k) := fun _ _ h ↦
  Subtype.ext <| congrArg Subtype.val <| (c.otherBasis k).repr.injective h

private theorem linearCombination_otherCoeffRepr (c : BasedChart R u Λ B) (k : I)
    (b : (c.otherSubalgebra k).toSubsemiring) :
    Finsupp.linearCombination R (fun a : { a : I →₀ ℤ // a k = 0 } ↦ (c.monomial a.1 : B))
      (c.otherCoeffRepr k b) = (b : B) := by
  have hb := congrArg (Subtype.val : c.otherSubalgebra k → B)
    ((c.otherBasis k).linearCombination_repr ⟨b.1, b.2⟩)
  rw [← hb]
  simp [otherCoeffRepr, Finsupp.linearCombination_apply, Finsupp.sum]

private theorem otherCoeffRepr_smul_monomial (c : BasedChart R u Λ B) (k : I) (r : R)
    (a₀ : { a : I →₀ ℤ // a k = 0 })
    (hm : r • (c.monomial a₀.1 : B) ∈ (c.otherSubalgebra k).toSubsemiring) :
    c.otherCoeffRepr k ⟨r • (c.monomial a₀.1 : B), hm⟩ = Finsupp.single a₀ r := by
  have hval : (⟨r • (c.monomial a₀.1 : B), hm⟩ : c.otherSubalgebra k) =
      r • c.otherBasis k a₀ := by
    ext
    simp
  simp [otherCoeffRepr, hval]

private theorem conj_mem_otherSubalgebra_of_monomial (c : BasedChart R u Λ B) (k : I) {z : Bˣ}
    (hz : ∀ a : I →₀ ℤ, a k = 0 →
      (z : B) * (c.monomial a : B) * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k)
    {b : B} (hb : b ∈ c.otherSubalgebra k) :
    (z : B) * b * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k := by
  refine Submodule.span_induction
    (p := fun b _ ↦ (z : B) * b * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k)
    (fun _ hx ↦ ?_) (by simp [(c.otherSubalgebra k).zero_mem])
    (fun x₁ x₂ _ _ h₁ h₂ ↦ by
      rw [mul_add, add_mul]
      exact (c.otherSubalgebra k).add_mem h₁ h₂)
    (fun r x _ h ↦ by
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      exact Submodule.smul_mem (c.otherSubmodule k) r h)
    hb
  rcases hx with ⟨a, rfl⟩
  exact hz a.1 a.2

/-- If conjugation by `z` and by `z⁻¹` sends every `M(a)` with `a k = 0` into `c.otherSubalgebra k`,
then `z` normalizes `(c.otherSubalgebra k).toSubsemiring`. -/
theorem conjAct_otherSubalgebra_of_monomial (c : BasedChart R u Λ B) (k : I) {z : Bˣ}
    (hz : ∀ a : I →₀ ℤ, a k = 0 →
      (z : B) * (c.monomial a : B) * ((z⁻¹ : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hz_inv : ∀ a : I →₀ ℤ, a k = 0 →
      ((z⁻¹ : Bˣ) : B) * (c.monomial a : B) * (z : B) ∈ c.otherSubalgebra k) :
    ConjAct.toConjAct z • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact c.conj_mem_otherSubalgebra_of_monomial k hz hb
  · intro b hb
    refine ⟨((z⁻¹ : Bˣ) : B) * b * (z : B), ?_, ?_⟩
    · simpa using c.conj_mem_otherSubalgebra_of_monomial (z := z⁻¹) k (by simpa using hz_inv) hb
    · simp [ConjAct.units_smul_def, mul_assoc]

private theorem map_algebraMap_comm_units (w : Rˣ) (x : Bˣ) :
    x * Units.map (algebraMap R B).toMonoidHom w =
      Units.map (algebraMap R B).toMonoidHom w * x :=
  Units.ext <| (Algebra.commutes (w : R) (x : B)).symm

private theorem unitsMap_mul_left_comm (w : Rˣ) (x z : Bˣ) :
    x * (Units.map (algebraMap R B).toMonoidHom w * z) =
      Units.map (algebraMap R B).toMonoidHom w * (x * z) := by
  rw [← mul_assoc, map_algebraMap_comm_units, mul_assoc]

private theorem unitsMap_mul_unitsMap (w₁ w₂ : Rˣ) (x : Bˣ) :
    Units.map (algebraMap R B).toMonoidHom w₁ *
      (Units.map (algebraMap R B).toMonoidHom w₂ * x) =
      Units.map (algebraMap R B).toMonoidHom (w₁ * w₂) * x := by
  rw [← mul_assoc, ← map_mul]

private theorem conj_units_val (z m : Bˣ) :
    (z : B) * (m : B) * ((z⁻¹ : Bˣ) : B) = ((z * m * z⁻¹ : Bˣ) : B) :=
  rfl

private theorem conj_inv_units_val (z m : Bˣ) :
    ((z⁻¹ : Bˣ) : B) * (m : B) * (z : B) = ((z⁻¹ * m * z : Bˣ) : B) :=
  rfl

private theorem unitsMap_algebraMap_mul_monomial_mem_otherSubalgebra (c : BasedChart R u Λ B)
    (k : I) (w : Rˣ) {a : I →₀ ℤ} (ha : a k = 0) :
    ((Units.map (algebraMap R B).toMonoidHom w * c.monomial a : Bˣ) : B) ∈
      c.otherSubalgebra k := by
  rw [Units.val_mul]
  exact (c.otherSubalgebra k).mul_mem (by simp [(c.otherSubalgebra k).algebraMap_mem])
    (c.monomial_mem_otherSubalgebra k ha)

/-- When `Λ` is alternating, the `k`-th coordinate `c.coordinate k` normalizes
`(c.otherSubalgebra k).toSubsemiring`. -/
theorem conjAct_coordinate_otherSubalgebra (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) :
    ConjAct.toConjAct (c.coordinate k) • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring := by
  refine c.conjAct_otherSubalgebra_of_monomial k (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · have hcomm := c.monomial_mul_comm_of_isAlt hΛ (Finsupp.single k 1) a
    rw [← coordinate_def] at hcomm
    have hconj : c.coordinate k * c.monomial a * (c.coordinate k)⁻¹ =
        Units.map (algebraMap R B).toMonoidHom
          (u ^ (2 * Λ.finsuppBilinForm (Finsupp.single k 1) a)) * c.monomial a := by
      rw [hcomm, mul_assoc, mul_inv_cancel_right]
    rw [conj_units_val, hconj]
    exact c.unitsMap_algebraMap_mul_monomial_mem_otherSubalgebra k _ ha
  · have hcomm := c.monomial_mul_comm_of_isAlt hΛ a (Finsupp.single k 1)
    rw [← coordinate_def] at hcomm
    have hconj : (c.coordinate k)⁻¹ * c.monomial a * c.coordinate k =
        Units.map (algebraMap R B).toMonoidHom
          (u ^ (2 * Λ.finsuppBilinForm a (Finsupp.single k 1))) * c.monomial a := by
      rw [mul_assoc, hcomm, unitsMap_mul_left_comm, inv_mul_cancel_left]
    rw [conj_inv_units_val, hconj]
    exact c.unitsMap_algebraMap_mul_monomial_mem_otherSubalgebra k _ ha

private theorem single_add_erase_injective (k : I) :
    Function.Injective
      (fun p : { a : I →₀ ℤ // a k = 0 } × ℤ ↦ p.1.1 + Finsupp.single k p.2) := by
  rintro ⟨a₁, m₁⟩ ⟨a₂, m₂⟩ h
  have hm : m₁ = m₂ := by
    have hk := congrArg (fun f : I →₀ ℤ ↦ f k) h
    simpa [a₁.2, a₂.2] using hk
  subst hm
  exact Prod.ext (Subtype.ext (add_right_cancel h)) rfl

private noncomputable def coordShiftMap (c : BasedChart R u Λ B) (k : I) (m : ℤ) :
    ({ a : I →₀ ℤ // a k = 0 } →₀ R) →+ ((I →₀ ℤ) →₀ R) :=
  let _ := c
  Finsupp.liftAddHom fun a₀ ↦
    (Finsupp.singleAddHom (a₀.1 + Finsupp.single k m)).comp
      (AddMonoidHom.mulRight ((u ^ Λ.finsuppBilinForm a₀.1 (Finsupp.single k m) : Rˣ) : R))

private theorem eval_coordShiftMap (c : BasedChart R u Λ B) {k : I} (hkk : Λ k k = 0) (m : ℤ)
    (g : { a : I →₀ ℤ // a k = 0 } →₀ R) :
    c.eval (c.coordShiftMap k m g) =
      Finsupp.linearCombination R (fun a₀ : { a : I →₀ ℤ // a k = 0 } ↦ (c.monomial a₀.1 : B)) g *
        ((c.coordinate k ^ m : Bˣ) : B) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ hg₁ hg₂ => simp only [map_add, add_mul, hg₁, hg₂]
  | single a₀ r =>
    simp only [coordShiftMap, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp,
      Function.comp_apply, Finsupp.singleAddHom_apply, AddMonoidHom.mulRight_apply, eval_single,
      Finsupp.linearCombination_single]
    rw [← c.monomial_single_of_diag_zero hkk m, Algebra.smul_mul_assoc, c.val_monomial_mul,
      smul_smul]

private theorem coordShiftMap_apply (c : BasedChart R u Λ B) (k : I) (m' m : ℤ)
    (g : { a : I →₀ ℤ // a k = 0 } →₀ R) (a₀ : { a : I →₀ ℤ // a k = 0 }) :
    c.coordShiftMap k m' g (a₀.1 + Finsupp.single k m) =
      if m' = m then
        g a₀ * ((u ^ Λ.finsuppBilinForm a₀.1 (Finsupp.single k m) : Rˣ) : R)
      else 0 := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ hg₁ hg₂ =>
    simp only [map_add, Finsupp.add_apply, hg₁, hg₂]
    split_ifs <;> ring
  | single d r =>
    simp only [coordShiftMap, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp,
      Function.comp_apply, Finsupp.singleAddHom_apply, AddMonoidHom.mulRight_apply,
      Finsupp.single_apply]
    by_cases hm : m' = m
    · subst hm
      by_cases hd : d = a₀
      · subst hd; simp
      · have hne : d.1 + Finsupp.single k m' ≠ a₀.1 + Finsupp.single k m' :=
          (single_add_erase_injective k).ne (a₁ := (d, m')) (a₂ := (a₀, m')) (by simp [hd])
        simp [hd, hne]
    · have hne : d.1 + Finsupp.single k m' ≠ a₀.1 + Finsupp.single k m :=
        (single_add_erase_injective k).ne (a₁ := (d, m')) (a₂ := (a₀, m)) (by simp [hm])
      simp [hm, hne]

/-- **Uniqueness of left Laurent expansions in `c.coordinate k`**: when `Λ k k = 0`, finite left
Laurent expansions `∑_m f(m) * (c.coordinate k)^m` with coefficients in `c.otherSubalgebra k` have
unique coefficients. -/
theorem skewLaurentSum_coordinate_injective (c : BasedChart R u Λ B) {k : I} (hkk : Λ k k = 0) :
    Function.Injective
      ((c.otherSubalgebra k).toSubsemiring.skewLaurentSum (c.coordinate k)) := by
  classical
  let C := (c.otherSubalgebra k).toSubsemiring
  let Φ : (ℤ →₀ C) →+ ((I →₀ ℤ) →₀ R) :=
    Finsupp.liftAddHom fun m ↦ (c.coordShiftMap k m).comp (c.otherCoeffRepr k)
  have hcomp (f : ℤ →₀ C) : c.eval (Φ f) = C.skewLaurentSum (c.coordinate k) f := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ hf₁ hf₂ => rw [map_add, map_add, map_add, hf₁, hf₂]
    | single m b =>
      simp [Φ, c.eval_coordShiftMap hkk, c.linearCombination_otherCoeffRepr]
  have hΦ_apply (f : ℤ →₀ C) (a₀ : { a : I →₀ ℤ // a k = 0 }) (m : ℤ) :
      Φ f (a₀.1 + Finsupp.single k m) =
        c.otherCoeffRepr k (f m) a₀ *
          ((u ^ Λ.finsuppBilinForm a₀.1 (Finsupp.single k m) : Rˣ) : R) := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ hf₁ hf₂ =>
      simp only [map_add, Finsupp.add_apply, hf₁, hf₂, add_mul]
    | single m' b =>
      simp only [Φ, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply,
        c.coordShiftMap_apply]
      by_cases hm : m' = m
      · subst hm; simp
      · simp [hm, Finsupp.single_eq_of_ne (Ne.symm hm)]
  intro f₁ f₂ h
  have hEq : Φ f₁ = Φ f₂ := c.eval_injective (by rw [hcomp, hcomp, h])
  ext m
  refine congrArg Subtype.val (c.otherCoeffRepr_injective k ?_)
  ext a₀
  have eval_eq := congrArg (fun g : (I →₀ ℤ) →₀ R ↦ g (a₀.1 + Finsupp.single k m)) hEq
  rw [hΦ_apply, hΦ_apply] at eval_eq
  set w : Rˣ := u ^ Λ.finsuppBilinForm a₀.1 (Finsupp.single k m)
  simpa [mul_assoc, ← Units.val_mul] using congrArg (· * ((w⁻¹ : Rˣ) : R)) eval_eq

/-! ### Mutated monomials, normalization, and linear independence -/

/-- The mutated normalized monomial family at index `k` associated to a unit `y : Bˣ` and an
additive map `μ : (I →₀ ℤ) →+ ℤ`:
`M'(a) = u ^ (-(a k * μ (a.erase k))) * (y ^ (a k) * M(a.erase k))`. -/
noncomputable def mutatedMonomial (c : BasedChart R u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) (a : I →₀ ℤ) : Bˣ :=
  Units.map (algebraMap R B).toMonoidHom (u ^ (-(a k * μ (a.erase k)))) *
    (y ^ a k * c.monomial (a.erase k))

@[simp]
theorem mutatedMonomial_zero (c : BasedChart R u Λ B) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ) :
    c.mutatedMonomial k y μ 0 = 1 := by
  simp [mutatedMonomial, c.monomial_zero]

theorem mutatedMonomial_of_apply_eq_zero (c : BasedChart R u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) {a : I →₀ ℤ} (ha : a k = 0) :
    c.mutatedMonomial k y μ a = c.monomial a := by
  have herase : a.erase k = a :=
    Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr ha)
  rw [mutatedMonomial, ha, herase]
  simp

@[simp]
theorem mutatedMonomial_single_same (c : BasedChart R u Λ B) (k : I) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) (n : ℤ) :
    c.mutatedMonomial k y μ (Finsupp.single k n) = y ^ n := by
  simp [mutatedMonomial, c.monomial_zero]

theorem mutatedMonomial_single_of_ne (c : BasedChart R u Λ B) {i k : I} (hik : i ≠ k) (y : Bˣ)
    (μ : (I →₀ ℤ) →+ ℤ) (n : ℤ) :
    c.mutatedMonomial k y μ (Finsupp.single i n) = c.monomial (Finsupp.single i n) :=
  c.mutatedMonomial_of_apply_eq_zero k y μ (Finsupp.single_eq_of_ne hik.symm)

/-- Power quasi-commutation of `y^n` with `c.monomial a` for `a k = 0`. -/
theorem zpow_mul_monomial_of_quasiComm (c : BasedChart R u Λ B) {k : I} {y : Bˣ}
    {μ : (I →₀ ℤ) →+ ℤ}
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (n : ℤ) {a : I →₀ ℤ} (ha : a k = 0) :
    y ^ n * c.monomial a =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * n * μ a)) * (c.monomial a * y ^ n) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ m hm =>
    calc y ^ ((m : ℤ) + 1) * c.monomial a
        = y ^ (m : ℤ) * (y * c.monomial a) := by rw [zpow_add_one, mul_assoc]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) *
            ((y ^ (m : ℤ) * c.monomial a) * y) := by
          rw [hy_comm a ha, unitsMap_mul_left_comm, mul_assoc]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * ((m : ℤ) + 1) * μ a)) *
            (c.monomial a * y ^ ((m : ℤ) + 1)) := by
          rw [hm, mul_assoc (Units.map _ _) (c.monomial a * y ^ (m : ℤ)), unitsMap_mul_unitsMap,
            ← zpow_add, mul_assoc (c.monomial a), ← zpow_add_one]
          congr 3
          ring
  | pred m hm =>
    set z : ℤ := -(m : ℤ) - 1
    have hz : 1 + z = -(m : ℤ) := by dsimp [z]; ring
    refine mul_left_cancel (a := y) ?_
    calc y * (y ^ z * c.monomial a)
        = y ^ (-(m : ℤ)) * c.monomial a := by rw [← mul_assoc, ← zpow_one_add, hz]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (-(m : ℤ)) * μ a)) *
            (c.monomial a * y ^ (-(m : ℤ))) := hm
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a + 2 * z * μ a)) *
            (c.monomial a * (y * y ^ z)) := by
          rw [← hz, zpow_one_add]
          congr 3
          ring
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * z * μ a)) *
            ((Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) *
              (c.monomial a * y)) * y ^ z) := by
          rw [add_comm (2 * μ a), zpow_add, map_mul]
          simp only [mul_assoc]
      _ = y * (Units.map (algebraMap R B).toMonoidHom (u ^ (2 * z * μ a)) *
            (c.monomial a * y ^ z)) := by
          rw [← hy_comm a ha, ← unitsMap_mul_left_comm, mul_assoc, unitsMap_mul_left_comm]

/-- Left-coefficient form of `mutatedMonomial`: moving `y ^ (a k)` to the right flips the sign of
the normalization exponent from `-(a k * μ (a.erase k))` to `a k * μ (a.erase k)`. -/
theorem mutatedMonomial_eq_mul_zpow (c : BasedChart R u Λ B) {k : I} {y : Bˣ}
    {μ : (I →₀ ℤ) →+ ℤ}
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (a : I →₀ ℤ) :
    c.mutatedMonomial k y μ a =
      Units.map (algebraMap R B).toMonoidHom (u ^ (a k * μ (a.erase k))) *
        (c.monomial (a.erase k) * y ^ a k) := by
  rw [mutatedMonomial, c.zpow_mul_monomial_of_quasiComm hy_comm (a k) Finsupp.erase_same,
    unitsMap_mul_unitsMap, ← zpow_add]
  congr 3
  ring

/-- A unit `y : Bˣ` quasi-commuting with `M(a)` (`a k = 0`) normalizes
`(c.otherSubalgebra k).toSubsemiring`. -/
theorem conjAct_unit_otherSubalgebra (c : BasedChart R u Λ B) {k : I} {y : Bˣ}
    {μ : (I →₀ ℤ) →+ ℤ}
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y)) :
    ConjAct.toConjAct y • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring := by
  refine c.conjAct_otherSubalgebra_of_monomial k (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · have hconj : y * c.monomial a * y⁻¹ =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * c.monomial a := by
      rw [hy_comm a ha, mul_assoc, mul_inv_cancel_right]
    rw [conj_units_val, hconj]
    exact c.unitsMap_algebraMap_mul_monomial_mem_otherSubalgebra k _ ha
  · have hm := c.zpow_mul_monomial_of_quasiComm hy_comm (-1) ha
    rw [zpow_neg_one] at hm
    have hconj : y⁻¹ * c.monomial a * y =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (-1 : ℤ) * μ a)) * c.monomial a := by
      rw [hm, mul_assoc, inv_mul_cancel_right]
    rw [conj_inv_units_val, hconj]
    exact c.unitsMap_algebraMap_mul_monomial_mem_otherSubalgebra k _ ha

/-- When `Λ` is alternating and `y` quasi-commutes with `M(a)` (`a k = 0`), the exchange unit
`E = y * c.coordinate k` normalizes `(c.otherSubalgebra k).toSubsemiring`. -/
theorem conjAct_mul_coordinate_otherSubalgebra (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) {k : I} {y : Bˣ} {μ : (I →₀ ℤ) →+ ℤ}
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y)) :
    ConjAct.toConjAct (y * c.coordinate k) • (c.otherSubalgebra k).toSubsemiring =
      (c.otherSubalgebra k).toSubsemiring := by
  rw [map_mul, mul_smul, c.conjAct_coordinate_otherSubalgebra hΛ k,
    c.conjAct_unit_otherSubalgebra hy_comm]

/-- Left Laurent expansions in the exchanged unit `y` with coefficients in `c.otherSubalgebra k`
have unique coefficients. -/
theorem skewLaurentSum_exchange_injective (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) {k : I} {y : Bˣ}
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k) :
    Function.Injective ((c.otherSubalgebra k).toSubsemiring.skewLaurentSum y) := by
  have hy_eq : (y * c.coordinate k) * (c.coordinate k)⁻¹ = y := mul_inv_cancel_right y _
  rw [← hy_eq]
  exact Subsemiring.skewLaurentSum_mul_inv_injective
    (c.conjAct_coordinate_otherSubalgebra hΛ k) hyx
    (c.skewLaurentSum_coordinate_injective
      (Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ k))

private noncomputable def mutatedTermAux (c : BasedChart R u Λ B) (k : I) (μ : (I →₀ ℤ) →+ ℤ)
    (a : I →₀ ℤ) : R →+ (c.otherSubalgebra k).toSubsemiring where
  toFun r :=
    ⟨(r * ((u ^ (a k * μ (a.erase k)) : Rˣ) : R)) • (c.monomial (a.erase k) : B),
      Submodule.smul_mem (c.otherSubmodule k) _
        (c.monomial_mem_otherSubalgebra k Finsupp.erase_same)⟩
  map_zero' := by ext; simp
  map_add' r₁ r₂ := by ext; simp [add_mul, add_smul]

private noncomputable def mutatedCoeffMap (c : BasedChart R u Λ B) (k : I) (μ : (I →₀ ℤ) →+ ℤ) :
    ((I →₀ ℤ) →₀ R) →+ (ℤ →₀ (c.otherSubalgebra k).toSubsemiring) :=
  Finsupp.liftAddHom fun a ↦ (Finsupp.singleAddHom (a k)).comp (c.mutatedTermAux k μ a)

private theorem skewLaurentSum_mutatedCoeffMap (c : BasedChart R u Λ B) {k : I} {y : Bˣ}
    {μ : (I →₀ ℤ) →+ ℤ}
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (g : (I →₀ ℤ) →₀ R) :
    (c.otherSubalgebra k).toSubsemiring.skewLaurentSum y (c.mutatedCoeffMap k μ g) =
      Finsupp.linearCombination R (fun a ↦ (c.mutatedMonomial k y μ a : B)) g := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ hg₁ hg₂ => rw [map_add, map_add, map_add, hg₁, hg₂]
  | single a r =>
    simp only [mutatedCoeffMap, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp,
      Function.comp_apply, Finsupp.singleAddHom_apply, Subsemiring.skewLaurentSum_single,
      Finsupp.linearCombination_single, mutatedTermAux, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [c.mutatedMonomial_eq_mul_zpow hy_comm a, Units.val_mul, Units.val_mul,
      val_unitsMap_algebraMap]
    simp [Algebra.smul_def, mul_assoc]

private theorem otherCoeffRepr_mutatedCoeffMap (c : BasedChart R u Λ B) (k : I)
    (μ : (I →₀ ℤ) →+ ℤ) (g : (I →₀ ℤ) →₀ R) (a₀ : { a : I →₀ ℤ // a k = 0 }) (m : ℤ) :
    c.otherCoeffRepr k (c.mutatedCoeffMap k μ g m) a₀ =
      g (a₀.1 + Finsupp.single k m) * ((u ^ (m * μ a₀.1) : Rˣ) : R) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ hg₁ hg₂ =>
    simp only [map_add, Finsupp.add_apply, hg₁, hg₂, add_mul]
  | single b r =>
    simp only [mutatedCoeffMap, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp,
      Function.comp_apply, Finsupp.singleAddHom_apply]
    by_cases hbm : b k = m
    · subst hbm
      rw [Finsupp.single_eq_same]
      have hrepr : c.otherCoeffRepr k (c.mutatedTermAux k μ b r) =
          Finsupp.single ⟨b.erase k, Finsupp.erase_same⟩
            (r * ((u ^ (b k * μ (b.erase k)) : Rˣ) : R)) :=
        c.otherCoeffRepr_smul_monomial k _ ⟨b.erase k, Finsupp.erase_same⟩ _
      rw [hrepr]
      by_cases hb : (⟨b.erase k, Finsupp.erase_same⟩ : { a : I →₀ ℤ // a k = 0 }) = a₀
      · have her : b.erase k = a₀.1 := congrArg Subtype.val hb
        have hba : a₀.1 + Finsupp.single k (b k) = b := by
          rw [← her, Finsupp.erase_add_single]
        rw [hb, Finsupp.single_eq_same, hba, Finsupp.single_eq_same, her]
      · have hba : b ≠ a₀.1 + Finsupp.single k (b k) := by
          intro h
          apply hb
          ext i
          by_cases hik : i = k
          · subst hik; simp [a₀.2]
          · have hi := DFunLike.congr_fun h i
            simpa [hik] using hi
        rw [Finsupp.single_eq_of_ne (Ne.symm hb), Finsupp.single_eq_of_ne (Ne.symm hba), zero_mul]
    · have hba : b ≠ a₀.1 + Finsupp.single k m := by
        intro h
        apply hbm
        have hk := DFunLike.congr_fun h k
        simpa [a₀.2] using hk
      rw [Finsupp.single_eq_of_ne (Ne.symm hbm), map_zero, Finsupp.zero_apply,
        Finsupp.single_eq_of_ne (Ne.symm hba), zero_mul]

/-- **`R`-linear independence of `mutatedMonomial`**: when `Λ` is alternating, `(y * X_k : B)`
belongs to `c.otherSubalgebra k`, and `y` quasi-commutes with `M(a)` (`a k = 0`), the mutated
monomial family `c.mutatedMonomial k y μ` is `R`-linearly independent. -/
theorem linearIndependent_mutatedMonomial (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) {k : I} {y : Bˣ} {μ : (I →₀ ℤ) →+ ℤ}
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y)) :
    LinearIndependent R fun a ↦ (c.mutatedMonomial k y μ a : B) := by
  classical
  intro g₁ g₂ h
  have hEq : c.mutatedCoeffMap k μ g₁ = c.mutatedCoeffMap k μ g₂ :=
    c.skewLaurentSum_exchange_injective hΛ hyx
      (by rw [c.skewLaurentSum_mutatedCoeffMap hy_comm,
        c.skewLaurentSum_mutatedCoeffMap hy_comm, h])
  ext a
  let a₀ : { b : I →₀ ℤ // b k = 0 } := ⟨a.erase k, Finsupp.erase_same⟩
  have ha : a₀.1 + Finsupp.single k (a k) = a := Finsupp.erase_add_single k a
  have hcoeff : c.otherCoeffRepr k (c.mutatedCoeffMap k μ g₁ (a k)) a₀ =
      c.otherCoeffRepr k (c.mutatedCoeffMap k μ g₂ (a k)) a₀ := by
    rw [hEq]
  rw [c.otherCoeffRepr_mutatedCoeffMap, c.otherCoeffRepr_mutatedCoeffMap, ha] at hcoeff
  set w : Rˣ := u ^ (a k * μ a₀.1)
  simpa [mul_assoc, ← Units.val_mul] using congrArg (· * ((w⁻¹ : Rˣ) : R)) hcoeff

/-- **Multiplication law for `mutatedMonomial`**: for any alternating form `Λ'` agreeing with `Λ`
on `{ a | a k = 0 }` and pairing `single k 1` to `μ` on `{ a | a k = 0 }`, the family
`c.mutatedMonomial k y μ` satisfies `M'(a) * M'(b) = u ^ Λ'(a, b) * M'(a + b)`. -/
theorem mutatedMonomial_mul (c : BasedChart R u Λ B) {k : I} {y : Bˣ} {μ : (I →₀ ℤ) →+ ℤ}
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    {Λ' : Matrix I I ℤ} (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 →
      Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a)
    (a b : I →₀ ℤ) :
    c.mutatedMonomial k y μ a * c.mutatedMonomial k y μ b =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ'.finsuppBilinForm a b) *
        c.mutatedMonomial k y μ (a + b) := by
  have ha₀ : (a.erase k) k = 0 := Finsupp.erase_same
  have hb₀ : (b.erase k) k = 0 := Finsupp.erase_same
  have hcomm_inv : c.monomial (a.erase k) * y ^ b k =
      Units.map (algebraMap R B).toMonoidHom (u ^ (-(2 * b k * μ (a.erase k)))) *
        (y ^ b k * c.monomial (a.erase k)) := by
    apply mul_left_cancel
      (a := Units.map (algebraMap R B).toMonoidHom (u ^ (2 * b k * μ (a.erase k))))
    rw [← c.zpow_mul_monomial_of_quasiComm hy_comm (b k) ha₀, unitsMap_mul_unitsMap, ← zpow_add,
      add_neg_cancel, zpow_zero, map_one, one_mul]
  have hform : Λ'.finsuppBilinForm a b =
      a k * μ (b.erase k) - b k * μ (a.erase k) + Λ.finsuppBilinForm (a.erase k) (b.erase k) := by
    have ha_eq : Finsupp.single k (a k) + a.erase k = a := Finsupp.single_add_erase k a
    have hb_eq : Finsupp.single k (b k) + b.erase k = b := Finsupp.single_add_erase k b
    have hsm : Finsupp.single k (a k) = a k • Finsupp.single k 1 := by simp
    have hsn : Finsupp.single k (b k) = b k • Finsupp.single k 1 := by simp
    have hskew : Λ'.finsuppBilinForm (a.erase k) (Finsupp.single k (b k)) =
        -Λ'.finsuppBilinForm (Finsupp.single k (b k)) (a.erase k) :=
      (hΛ'.neg_eq (Finsupp.single k (b k)) (a.erase k)).symm
    conv_lhs => rw [← ha_eq, ← hb_eq]
    simp only [map_add, LinearMap.add_apply]
    rw [Matrix.finsuppBilinForm_single_single,
      Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ' k, hskew, hsm, hsn]
    simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, hΛ'_row (b.erase k) hb₀,
      hΛ'_row (a.erase k) ha₀, hΛ'_off (a.erase k) (b.erase k) ha₀ hb₀]
    ring
  calc c.mutatedMonomial k y μ a * c.mutatedMonomial k y μ b
      = Units.map (algebraMap R B).toMonoidHom
          (u ^ (-(a k * μ (a.erase k)) + -(b k * μ (b.erase k)))) *
          (y ^ a k * ((c.monomial (a.erase k) * y ^ b k) * c.monomial (b.erase k))) := by
          rw [mutatedMonomial, mutatedMonomial]
          simp only [mul_assoc]
          rw [unitsMap_mul_left_comm _ (c.monomial (a.erase k)),
            unitsMap_mul_left_comm _ (y ^ a k), unitsMap_mul_unitsMap, ← zpow_add]
    _ = Units.map (algebraMap R B).toMonoidHom
          (u ^ (-(a k * μ (a.erase k)) + -(b k * μ (b.erase k)) +
            -(2 * b k * μ (a.erase k)) + Λ.finsuppBilinForm (a.erase k) (b.erase k))) *
          (y ^ (a k + b k) * c.monomial (a.erase k + b.erase k)) := by
          rw [hcomm_inv]
          simp only [mul_assoc]
          rw [unitsMap_mul_left_comm, unitsMap_mul_unitsMap, ← zpow_add,
            ← mul_assoc (y ^ a k) (y ^ b k), ← zpow_add, c.monomial_mul,
            unitsMap_mul_left_comm, unitsMap_mul_unitsMap, ← zpow_add]
    _ = Units.map (algebraMap R B).toMonoidHom (u ^ Λ'.finsuppBilinForm a b) *
          c.mutatedMonomial k y μ (a + b) := by
          rw [mutatedMonomial, Finsupp.add_apply, Finsupp.erase_add, map_add,
            unitsMap_mul_unitsMap, ← zpow_add, hform]
          congr 3
          ring

/-! ### Bundled one-step based-chart exchange -/

/-- **One-step skew exchange of a based chart** for a compatible alternating form `Λ'`: replaces the
`k`-th coordinate `c.coordinate k` by `y` while keeping all other coordinates unchanged. -/
noncomputable def exchangeOfForm (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (Λ' : Matrix I I ℤ) (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 →
      Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a) :
    BasedChart R u Λ' B where
  monomial := c.mutatedMonomial k y μ
  monomial_zero := c.mutatedMonomial_zero k y μ
  monomial_mul := c.mutatedMonomial_mul hy_comm hΛ' hΛ'_off hΛ'_row
  linearIndependent := c.linearIndependent_mutatedMonomial hΛ hyx hy_comm

@[simp]
theorem exchangeOfForm_monomial (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (Λ' : Matrix I I ℤ) (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 →
      Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a)
    (a : I →₀ ℤ) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).monomial a =
      c.mutatedMonomial k y μ a :=
  (rfl)

theorem exchangeOfForm_monomial_of_apply_eq_zero (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (Λ' : Matrix I I ℤ) (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 →
      Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a)
    {a : I →₀ ℤ} (ha : a k = 0) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).monomial a = c.monomial a :=
  c.mutatedMonomial_of_apply_eq_zero k y μ ha

@[simp]
theorem exchangeOfForm_coordinate_same (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (Λ' : Matrix I I ℤ) (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 →
      Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).coordinate k = y := by
  simp [coordinate_def]

theorem exchangeOfForm_coordinate_of_ne (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) {i k : I} (hik : i ≠ k) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (Λ' : Matrix I I ℤ) (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 →
      Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).coordinate i =
      c.coordinate i := by
  rw [coordinate_def, exchangeOfForm_monomial, c.mutatedMonomial_single_of_ne hik, ← coordinate_def]

@[simp]
theorem exchangeOfForm_otherSubalgebra (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (Λ' : Matrix I I ℤ) (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 →
      Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a) :
    (c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row).otherSubalgebra k =
      c.otherSubalgebra k := by
  apply Subalgebra.toSubmodule_injective
  simp only [toSubmodule_otherSubalgebra, otherSubmodule]
  congr 1
  ext b
  simp only [Set.mem_range, Subtype.exists]
  constructor <;> rintro ⟨a, ha, rfl⟩ <;>
    exact ⟨a, ha, by simp [c.mutatedMonomial_of_apply_eq_zero k y μ ha]⟩

/-- **One-step skew exchange of a based chart** constructing the canonical updated alternating
matrix `Λ.updateSkew k (fun j ↦ μ (Finsupp.single j 1))` directly from `μ`. -/
noncomputable def exchange [DecidableEq I] (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y)) :
    BasedChart R u (Λ.updateSkew k fun j ↦ μ (Finsupp.single j 1)) B :=
  c.exchangeOfForm hΛ k y μ hyx hy_comm
    (Λ.updateSkew k fun j ↦ μ (Finsupp.single j 1))
    (Matrix.isAlt_finsuppBilinForm_updateSkew hΛ k _)
    (fun _ _ ha hb ↦ Matrix.finsuppBilinForm_updateSkew_of_apply_eq_zero Λ k _ ha hb)
    fun a ha ↦ by
      rw [Matrix.finsuppBilinForm_updateSkew_single_left Λ k _ 1 ha, one_mul]
      clear ha
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add a₁ a₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
      | single j n =>
        have hsn : Finsupp.single j n = n • Finsupp.single j 1 := by simp
        rw [Finsupp.linearCombination_single, smul_eq_mul, hsn, map_zsmul, smul_eq_mul]

@[simp]
theorem exchange_monomial [DecidableEq I] (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (a : I →₀ ℤ) :
    (c.exchange hΛ k y μ hyx hy_comm).monomial a = c.mutatedMonomial k y μ a :=
  (rfl)

@[simp]
theorem exchange_coordinate_same [DecidableEq I] (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y)) :
    (c.exchange hΛ k y μ hyx hy_comm).coordinate k = y :=
  c.exchangeOfForm_coordinate_same hΛ k y μ hyx hy_comm _ _ _ _

theorem exchange_coordinate_of_ne [DecidableEq I] (c : BasedChart R u Λ B)
    (hΛ : Λ.finsuppBilinForm.IsAlt) {i k : I} (hik : i ≠ k) (y : Bˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y)) :
    (c.exchange hΛ k y μ hyx hy_comm).coordinate i = c.coordinate i :=
  c.exchangeOfForm_coordinate_of_ne hΛ hik y μ hyx hy_comm _ _ _ _

end Semiring

end BasedChart

/-! ### Torus-map and division-ring exchange theorems -/

namespace BasedTorus

section Semiring

variable {R I B : Type*} [CommSemiring R] {u : Rˣ} {Λ Λ' : Matrix I I ℤ}
  [Semiring B] [Algebra R B]

private theorem unitX_eq_unitMonomial (i : I) :
    unitX (R := R) (u := u) (Λ := Λ) i = unitMonomial (Finsupp.single i 1) :=
  Units.ext <| by simp [val_unitX, X_def]

private theorem unitMonomial_single_of_diag_zero {i : I} (hi : Λ i i = 0) (n : ℤ) :
    unitMonomial (R := R) (u := u) (Λ := Λ) (Finsupp.single i n) =
      (unitX (R := R) (u := u) (Λ := Λ) i) ^ n := by
  have h := (BasedChart.tautological R u Λ).monomial_single_of_diag_zero hi n
  simpa [BasedChart.coordinate_def, unitX_eq_unitMonomial] using h

private theorem unitMonomial_mul (a b : I →₀ ℤ) :
    unitMonomial (R := R) (u := u) (Λ := Λ) a * unitMonomial b =
      Units.map (algebraMap R (basedTorus R u Λ)).toMonoidHom (u ^ Λ.finsuppBilinForm a b) *
        unitMonomial (a + b) := by
  simpa using (BasedChart.tautological R u Λ).monomial_mul a b

/-- If `χ : basedTorus R u Λ →ₐ[R] B` and `χ' : basedTorus R u Λ' →ₐ[R] B` agree on all generators
`X_i` (`i ≠ k`) and `Λ'` agrees with `Λ` on `{ a | a k = 0 }`, then `χ'` and `χ` agree on every
basis monomial `monomial a` with `a k = 0`. -/
theorem algHom_monomial_eq_of_apply_eq_zero
    (hΛ : Λ.finsuppBilinForm.IsAlt) (hΛ' : Λ'.finsuppBilinForm.IsAlt) {k : I}
    {χ : basedTorus R u Λ →ₐ[R] B} {χ' : basedTorus R u Λ' →ₐ[R] B}
    (h_off : ∀ i ≠ k, χ' (X i) = χ (X i))
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    {a : I →₀ ℤ} (ha : a k = 0) :
    χ' (monomial a) = χ (monomial a) := by
  classical
  suffices Units.map χ'.toMonoidHom (unitMonomial a) =
      Units.map χ.toMonoidHom (unitMonomial a) by
    have hval := congrArg (Units.val : Bˣ → B) this
    simpa [val_unitMonomial] using hval
  induction a using Finsupp.induction with
  | zero =>
    ext
    simp [val_unitMonomial]
  | single_add i n f hif hn ih =>
    have hik : i ≠ k := by
      rintro rfl
      have hfi : f i = 0 := Finsupp.notMem_support_iff.mp hif
      simp [hfi, hn] at ha
    have hfk : f k = 0 := by
      simpa [Finsupp.add_apply, Finsupp.single_eq_of_ne hik.symm] using ha
    have hsingle : Units.map χ'.toMonoidHom (unitMonomial (Finsupp.single i n)) =
        Units.map χ.toMonoidHom (unitMonomial (Finsupp.single i n)) := by
      rw [unitMonomial_single_of_diag_zero
          (Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ' i),
        unitMonomial_single_of_diag_zero
          (Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ i),
        map_zpow, map_zpow]
      congr 1
      ext
      simpa [val_unitX] using h_off i hik
    have hmul₁ := congrArg (Units.map χ'.toMonoidHom)
      (unitMonomial_mul (R := R) (u := u) (Λ := Λ') (Finsupp.single i n) f)
    have hmul₂ := congrArg (Units.map χ.toMonoidHom)
      (unitMonomial_mul (R := R) (u := u) (Λ := Λ) (Finsupp.single i n) f)
    simp only [map_mul] at hmul₁ hmul₂
    have hform : Λ'.finsuppBilinForm (Finsupp.single i n) f =
        Λ.finsuppBilinForm (Finsupp.single i n) f :=
      hΛ'_off _ _ (Finsupp.single_eq_of_ne hik.symm) hfk
    have hunit : Units.map χ'.toMonoidHom
          (Units.map (algebraMap R (basedTorus R u Λ')).toMonoidHom
            (u ^ Λ'.finsuppBilinForm (Finsupp.single i n) f)) =
        Units.map χ.toMonoidHom
          (Units.map (algebraMap R (basedTorus R u Λ)).toMonoidHom
            (u ^ Λ.finsuppBilinForm (Finsupp.single i n) f)) := by
      rw [hform]
      ext
      rw [Units.coe_map, Units.coe_map, Units.coe_map, Units.coe_map]
      simp
    apply mul_left_cancel
      (a := Units.map χ.toMonoidHom
        (Units.map (algebraMap R (basedTorus R u Λ)).toMonoidHom
          (u ^ Λ.finsuppBilinForm (Finsupp.single i n) f)))
    rw [← hmul₂, ← hsingle, ← ih hfk, ← hunit, hmul₁]

/-- Given an injective `χ : basedTorus R u Λ →ₐ[R] B` and `χ' : basedTorus R u Λ' →ₐ[R] B`
satisfying the one-step exchange hypotheses at `k`, `χ'` is the torus map of an exchanged based
chart `BasedChart R u Λ' B`. -/
theorem exists_basedChart_of_exchange
    (hΛ : Λ.finsuppBilinForm.IsAlt) (hΛ' : Λ'.finsuppBilinForm.IsAlt) {k : I}
    {χ : basedTorus R u Λ →ₐ[R] B} (hχ : Function.Injective χ)
    {χ' : basedTorus R u Λ' →ₐ[R] B}
    (h_off : ∀ i ≠ k, χ' (X i) = χ (X i))
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (h_exch : χ' (X k) * χ (X k) ∈ (BasedChart.ofAlgHom χ hχ).otherSubalgebra k) :
    ∃ (y : Bˣ) (hyx : ((y * (BasedChart.ofAlgHom χ hχ).coordinate k : Bˣ) : B) ∈
        (BasedChart.ofAlgHom χ hχ).otherSubalgebra k)
      (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
        y * (BasedChart.ofAlgHom χ hχ).monomial a =
          Units.map (algebraMap R B).toMonoidHom
            (u ^ (2 * (Λ'.finsuppBilinForm (Finsupp.single k 1)).toAddMonoidHom a)) *
            ((BasedChart.ofAlgHom χ hχ).monomial a * y)),
      ((BasedChart.ofAlgHom χ hχ).exchangeOfForm hΛ k y
        (Λ'.finsuppBilinForm (Finsupp.single k 1)).toAddMonoidHom hyx hy_comm Λ' hΛ' hΛ'_off
        (by simp)).toAlgHom = χ' := by
  classical
  let c := BasedChart.ofAlgHom χ hχ
  let y : Bˣ := Units.map χ'.toMonoidHom (unitX k)
  let μ : (I →₀ ℤ) →+ ℤ := (Λ'.finsuppBilinForm (Finsupp.single k 1)).toAddMonoidHom
  have hyx : ((y * c.coordinate k : Bˣ) : B) ∈ c.otherSubalgebra k := by
    simpa [y, c, BasedChart.coordinate_def, X_def, val_unitX] using h_exch
  have hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R B).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y) := by
    intro a ha
    ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_unitsMap_algebraMap]
    have hcomm := monomial_mul_comm_of_isAlt (R := R) (u := u) hΛ' (Finsupp.single k 1) a
    have hmap := congrArg χ' hcomm
    rw [map_mul, Algebra.smul_def, map_mul, AlgHom.commutes, map_mul, ← X_def,
      algHom_monomial_eq_of_apply_eq_zero hΛ hΛ' h_off hΛ'_off ha] at hmap
    simpa [val_unitX, c, y, μ] using hmap
  refine ⟨y, hyx, hy_comm, ?_⟩
  refine algHom_ext_X fun i ↦ ?_
  rcases eq_or_ne k i with rfl | hik
  · rw [BasedChart.toAlgHom_X, BasedChart.exchangeOfForm_coordinate_same]
    simp [y, val_unitX]
  · rw [BasedChart.toAlgHom_X, BasedChart.exchangeOfForm_coordinate_of_ne c hΛ hik.symm]
    simpa [c, BasedChart.coordinate_def, X_def] using (h_off i hik.symm).symm

/-- **One-step exchange faithfulness theorem for torus algebra maps**: if `χ` is injective, `χ'`
agrees with `χ` on `X_i` (`i ≠ k`), `Λ'` agrees with `Λ` off `k`, and `χ'(X_k) * χ(X_k)` lies in
`(BasedChart.ofAlgHom χ hχ).otherSubalgebra k`, then `χ'` is injective. -/
theorem injective_of_exchange
    (hΛ : Λ.finsuppBilinForm.IsAlt) (hΛ' : Λ'.finsuppBilinForm.IsAlt) {k : I}
    {χ : basedTorus R u Λ →ₐ[R] B} (hχ : Function.Injective χ)
    {χ' : basedTorus R u Λ' →ₐ[R] B}
    (h_off : ∀ i ≠ k, χ' (X i) = χ (X i))
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (h_exch : χ' (X k) * χ (X k) ∈ (BasedChart.ofAlgHom χ hχ).otherSubalgebra k) :
    Function.Injective χ' := by
  obtain ⟨y, hyx, hy_comm, hχ'_eq⟩ :=
    exists_basedChart_of_exchange hΛ hΛ' hχ h_off hΛ'_off h_exch
  rw [← hχ'_eq]
  exact BasedChart.toAlgHom_injective _

end Semiring

end BasedTorus

/-! ### Division-ring corollaries -/

section DivisionRing

variable {R I D : Type*} [CommSemiring R] {u : Rˣ} {Λ Λ' : Matrix I I ℤ}
  [DivisionRing D] [Algebra R D]

private theorem range_toAlgHom_subset_subfield (c : BasedChart R u Λ D) {k : I} (hkk : Λ k k = 0)
    {F : Subfield D} (hother : (c.otherSubalgebra k : Set D) ⊆ F)
    (hxk : (c.coordinate k : D) ∈ F) :
    Set.range c.toAlgHom ⊆ F := by
  rintro _ ⟨t, rfl⟩
  rw [← (BasedTorus.basis R u Λ).linearCombination_repr t]
  generalize (BasedTorus.basis R u Λ).repr t = g
  induction g using Finsupp.induction_linear with
  | zero => simp [F.zero_mem]
  | add g₁ g₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact F.add_mem h₁ h₂
  | single a r =>
    rw [Finsupp.linearCombination_single, map_smul, BasedTorus.basis_apply, c.toAlgHom_monomial,
      Algebra.smul_def]
    have hr : algebraMap R D r ∈ F :=
      hother ((c.otherSubalgebra k).algebraMap_mem r)
    refine F.mul_mem hr ?_
    have ha_eq : a.erase k + Finsupp.single k (a k) = a := Finsupp.erase_add_single k a
    have hinv_u : c.monomial a =
        Units.map (algebraMap R D).toMonoidHom
          (u ^ (-Λ.finsuppBilinForm (a.erase k) (Finsupp.single k (a k)))) *
          (c.monomial (a.erase k) * c.coordinate k ^ a k) := by
      apply mul_left_cancel
        (a := Units.map (algebraMap R D).toMonoidHom
          (u ^ Λ.finsuppBilinForm (a.erase k) (Finsupp.single k (a k))))
      rw [← mul_assoc, ← map_mul, ← zpow_add, add_neg_cancel, zpow_zero, map_one, one_mul,
        ← c.monomial_single_of_diag_zero hkk (a k), c.monomial_mul, ha_eq]
    have hinv : (c.monomial a : D) =
        algebraMap R D ((u ^ (-Λ.finsuppBilinForm (a.erase k) (Finsupp.single k (a k))) : Rˣ) : R) *
          ((c.monomial (a.erase k) : D) * ((c.coordinate k ^ a k : Dˣ) : D)) := by
      have hu := congrArg (Units.val : Dˣ → D) hinv_u
      rwa [Units.val_mul, Units.val_mul, val_unitsMap_algebraMap] at hu
    rw [hinv]
    have hu_mem : algebraMap R D
        ((u ^ (-Λ.finsuppBilinForm (a.erase k) (Finsupp.single k (a k))) : Rˣ) : R) ∈ F :=
      hother ((c.otherSubalgebra k).algebraMap_mem _)
    refine F.mul_mem hu_mem
      (F.mul_mem (hother (c.monomial_mem_otherSubalgebra k Finsupp.erase_same)) ?_)
    rw [Units.val_zpow_eq_zpow_val]
    exact F.zpow_mem hxk (a k)

/-- **Equality of generated division subrings under based-chart exchange**: in a division
`R`-algebra `D`, `c` and `c.exchangeOfForm ...` generate the same `Subfield D`. -/
theorem BasedChart.subfieldClosure_exchangeOfForm (c : BasedChart R u Λ D)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Dˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Dˣ) : D) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R D).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y))
    (Λ' : Matrix I I ℤ) (hΛ' : Λ'.finsuppBilinForm.IsAlt)
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (hΛ'_row : ∀ a : I →₀ ℤ, a k = 0 →
      Λ'.finsuppBilinForm (Finsupp.single k 1) a = μ a) :
    let c' := c.exchangeOfForm hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row
    Subfield.closure (Set.range c'.toAlgHom) = Subfield.closure (Set.range c.toAlgHom) := by
  intro c'
  let F := Subfield.closure (Set.range c.toAlgHom)
  let F' := Subfield.closure (Set.range c'.toAlgHom)
  have hother_F : (c.otherSubalgebra k : Set D) ⊆ F :=
    (SetLike.coe_subset_coe.mpr (c.otherSubalgebra_le_range_toAlgHom k)).trans
      Subfield.subset_closure
  have hother_F' : (c.otherSubalgebra k : Set D) ⊆ F' := by
    rw [← c.exchangeOfForm_otherSubalgebra hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row]
    exact (SetLike.coe_subset_coe.mpr (c'.otherSubalgebra_le_range_toAlgHom k)).trans
      Subfield.subset_closure
  have hxk_F : (c.coordinate k : D) ∈ F :=
    Subfield.subset_closure ⟨BasedTorus.X k, c.toAlgHom_X k⟩
  have hy_F' : (y : D) ∈ F' := by
    have hmem : (c'.coordinate k : D) ∈ F' :=
      Subfield.subset_closure ⟨BasedTorus.X k, c'.toAlgHom_X k⟩
    rwa [c.exchangeOfForm_coordinate_same] at hmem
  have hy_F : (y : D) ∈ F := by
    have hy_eq : (y : D) = ((y * c.coordinate k : Dˣ) : D) * (c.coordinate k : D)⁻¹ := by
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, mul_inv_cancel_right]
    rw [hy_eq]
    exact F.mul_mem (hother_F hyx) (F.inv_mem hxk_F)
  have hxk_F' : (c.coordinate k : D) ∈ F' := by
    have hx_eq : (c.coordinate k : D) = (y : D)⁻¹ * ((y * c.coordinate k : Dˣ) : D) := by
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, inv_mul_cancel_left]
    rw [hx_eq]
    exact F'.mul_mem (F'.inv_mem hy_F') (hother_F' hyx)
  refine le_antisymm (Subfield.closure_le.mpr ?_) (Subfield.closure_le.mpr ?_)
  · refine range_toAlgHom_subset_subfield c'
      (Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ' k) ?_ ?_
    · rw [c.exchangeOfForm_otherSubalgebra hΛ k y μ hyx hy_comm Λ' hΛ' hΛ'_off hΛ'_row]
      exact hother_F
    · rwa [c.exchangeOfForm_coordinate_same]
  · exact range_toAlgHom_subset_subfield c
      (Matrix.apply_self_eq_zero_of_isAlt_finsuppBilinForm hΛ k) hother_F' hxk_F'

/-- Specialization of `BasedChart.subfieldClosure_exchangeOfForm` to `BasedChart.exchange`. -/
theorem BasedChart.subfieldClosure_exchange [DecidableEq I] (c : BasedChart R u Λ D)
    (hΛ : Λ.finsuppBilinForm.IsAlt) (k : I) (y : Dˣ) (μ : (I →₀ ℤ) →+ ℤ)
    (hyx : ((y * c.coordinate k : Dˣ) : D) ∈ c.otherSubalgebra k)
    (hy_comm : ∀ a : I →₀ ℤ, a k = 0 →
      y * c.monomial a =
        Units.map (algebraMap R D).toMonoidHom (u ^ (2 * μ a)) * (c.monomial a * y)) :
    Subfield.closure (Set.range (c.exchange hΛ k y μ hyx hy_comm).toAlgHom) =
      Subfield.closure (Set.range c.toAlgHom) :=
  c.subfieldClosure_exchangeOfForm hΛ k y μ hyx hy_comm _ _ _ _

/-- **Quantum torus exchange in a division ring**: if `χ : basedTorus R u Λ →ₐ[R] D` is injective,
`χ' : basedTorus R u Λ' →ₐ[R] D` agrees with `χ` off `k`, `Λ'` agrees with `Λ` off `k`, and
`χ'(X_k) * χ(X_k)` belongs to `(BasedChart.ofAlgHom χ hχ).otherSubalgebra k`, then `χ'` generates
the same division subring (`Subfield.closure`) as `χ`. -/
theorem BasedTorus.subfieldClosure_eq_of_exchange
    (hΛ : Λ.finsuppBilinForm.IsAlt) (hΛ' : Λ'.finsuppBilinForm.IsAlt) {k : I}
    {χ : basedTorus R u Λ →ₐ[R] D} (hχ : Function.Injective χ)
    {χ' : basedTorus R u Λ' →ₐ[R] D}
    (h_off : ∀ i ≠ k, χ' (BasedTorus.X i) = χ (BasedTorus.X i))
    (hΛ'_off : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 →
      Λ'.finsuppBilinForm a b = Λ.finsuppBilinForm a b)
    (h_exch : χ' (BasedTorus.X k) * χ (BasedTorus.X k) ∈
      (BasedChart.ofAlgHom χ hχ).otherSubalgebra k) :
    Subfield.closure (Set.range χ') = Subfield.closure (Set.range χ) := by
  obtain ⟨y, hyx, hy_comm, hχ'_eq⟩ :=
    BasedTorus.exists_basedChart_of_exchange hΛ hΛ' hχ h_off hΛ'_off h_exch
  rw [← hχ'_eq]
  conv_rhs => rw [← BasedChart.ofAlgHom_toAlgHom χ hχ]
  exact (BasedChart.ofAlgHom χ hχ).subfieldClosure_exchangeOfForm hΛ k y _ hyx hy_comm
    Λ' hΛ' hΛ'_off (by simp)

end DivisionRing

end TauCeti
