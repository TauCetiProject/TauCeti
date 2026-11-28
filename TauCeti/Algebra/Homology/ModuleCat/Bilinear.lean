/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Products on the cohomology of cochain complexes of modules

Let `K₁`, `K₂` and `K₀` be `ℕ`-indexed cochain complexes of modules over a commutative ring `R`,
and let `μ p q n h : K₁ᵖ → K₂^q → K₀ⁿ`, for `h : p + q = n`, be a family of bilinear maps obeying
the **Leibniz rule**

`d (μ a b) = μ (d a) b + (-1) ^ p μ a (d b)`  for `a` of degree `p`.

Such families are the products of cochains: cup products of singular, Čech or Hochschild cochains,
and the multiplication of a differential graded algebra. The Leibniz rule makes the product of two
cocycles a cocycle (`TauCeti.CochainComplex.moduleCatCyclesMap₂`), and the product of a coboundary
and a cocycle, in either order, a coboundary. So the product descends to an `R`-bilinear map
`Hᵖ(K₁) × H^q(K₂) → Hⁿ(K₀)` on cohomology (`TauCeti.CochainComplex.moduleCatHomologyMap₂`),
computed on classes of cocycles by the product of representatives
(`TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ`). Associativity and units of products of
cochains pass to the products on cohomology, and cochain maps which intertwine two such products
intertwine the products on cohomology
(`TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂`).

## Main definitions

* `TauCeti.CochainComplex.moduleCatCyclesMap₂`: the product of cocycles.
* `TauCeti.CochainComplex.moduleCatHomologyMap₂`: the product on cohomology.

## Main results

* `TauCeti.CochainComplex.iCycles_moduleCatCyclesMap₂`: the product of cocycles is the product of
  the underlying cochains.
* `TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ`: the product of the classes of two
  cocycles is the class of their product.
* `TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ_moduleCatCyclesMk`: the same for cocycles
  given as elements of the cochain modules.
* `TauCeti.CochainComplex.moduleCatHomologyMap₂_unit_left`,
  `TauCeti.CochainComplex.moduleCatHomologyMap₂_unit_right`: the class of a `0`-cocycle which is a
  unit for the product of cochains is a unit for the product on cohomology.
* `TauCeti.CochainComplex.moduleCatHomologyMap₂_assoc`: associativity of products of cochains gives
  associativity of the products on cohomology.
* `TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂`: naturality under cochain maps
  intertwining the products.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v

namespace TauCeti.CochainComplex

variable {R : Type u} [CommRing R] {K₁ K₂ K₀ : CochainComplex (ModuleCat.{v} R) ℕ}
  (μ : ∀ p q n : ℕ, p + q = n → K₁.X p →ₗ[R] K₂.X q →ₗ[R] K₀.X n)
  (hμ : ∀ (p q n : ℕ) (h : p + q = n) (a : K₁.X p) (b : K₂.X q),
    (K₀.d n (n + 1)).hom (μ p q n h a b) =
      μ (p + 1) q (n + 1) ((Nat.succ_add p q).trans (congrArg Nat.succ h))
          ((K₁.d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • μ p (q + 1) (n + 1) ((Nat.add_succ p q).trans (congrArg Nat.succ h)) a
          ((K₂.d q (q + 1)).hom b))

include hμ in
/-- The product of two cocycles is a cocycle. -/
private lemma d_apply_μ_iCycles {p q n : ℕ} (h : p + q = n) (a : K₁.cycles p) (b : K₂.cycles q) :
    (K₀.d n (n + 1)).hom (μ p q n h ((K₁.iCycles p).hom a) ((K₂.iCycles q).hom b)) = 0 := by
  rw [hμ]
  simp

/-- **The product of cocycles**: for a family of products obeying the Leibniz rule, the product of
the underlying cochains of two cocycles, as a cocycle. -/
def moduleCatCyclesMap₂ (p q n : ℕ) (h : p + q = n) :
    K₁.cycles p →ₗ[R] K₂.cycles q →ₗ[R] K₀.cycles n :=
  LinearMap.mk₂ R
    (fun a b ↦ K₀.moduleCatCyclesMk (μ p q n h ((K₁.iCycles p).hom a) ((K₂.iCycles q).hom b))
      (n + 1) (by simp) (d_apply_μ_iCycles μ hμ h a b))
    (fun a a' b ↦ K₀.moduleCat_iCycles_injective n (by simp))
    (fun r a b ↦ K₀.moduleCat_iCycles_injective n (by simp))
    (fun a b b' ↦ K₀.moduleCat_iCycles_injective n (by simp))
    (fun r a b ↦ K₀.moduleCat_iCycles_injective n (by simp))

/-- On underlying cochains, the product of cocycles is the product of cochains. -/
@[simp]
theorem iCycles_moduleCatCyclesMap₂ (p q n : ℕ) (h : p + q = n) (a : K₁.cycles p)
    (b : K₂.cycles q) :
    (K₀.iCycles n).hom (moduleCatCyclesMap₂ μ hμ p q n h a b) =
      μ p q n h ((K₁.iCycles p).hom a) ((K₂.iCycles q).hom b) := by
  simp [moduleCatCyclesMap₂]

include hμ in
/-- A coboundary times a cocycle has zero class. -/
private lemma homologyπ_moduleCatCyclesMap₂_toCycles_left {p q n : ℕ} (h : p + q = n) (i : ℕ)
    (y : K₁.X i) (b : K₂.cycles q) :
    (K₀.homologyπ n).hom (moduleCatCyclesMap₂ μ hμ p q n h ((K₁.toCycles i p).hom y) b) = 0 := by
  by_cases hip : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i + 1 = p := hip
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨i + q, by omega⟩
    -- by the Leibniz rule, `d y ⌣ b = d (y ⌣ b)`
    have key : moduleCatCyclesMap₂ μ hμ (i + 1) q (m + 1) h ((K₁.toCycles i (i + 1)).hom y) b =
        (K₀.toCycles m (m + 1)).hom (μ i q m (by omega) y ((K₂.iCycles q).hom b)) := by
      apply K₀.moduleCat_iCycles_injective
      have hd := hμ i q m (by omega) y ((K₂.iCycles q).hom b)
      simp only [moduleCat_d_iCycles_apply, map_zero, smul_zero, add_zero] at hd
      simp [hd]
    rw [key]
    exact (K₀.moduleCat_homologyπ_eq_zero_iff (m := m) (by simp) _).2 ⟨_, rfl⟩
  · rw [K₁.toCycles_eq_zero hip]
    simp

include hμ in
/-- A cocycle times a coboundary has zero class. -/
private lemma homologyπ_moduleCatCyclesMap₂_toCycles_right {p q n : ℕ} (h : p + q = n)
    (a : K₁.cycles p) (i : ℕ) (y : K₂.X i) :
    (K₀.homologyπ n).hom (moduleCatCyclesMap₂ μ hμ p q n h a ((K₂.toCycles i q).hom y)) = 0 := by
  by_cases hiq : (ComplexShape.up ℕ).Rel i q
  · obtain rfl : i + 1 = q := hiq
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨p + i, by omega⟩
    -- by the Leibniz rule, `a ⌣ d y = (-1) ^ p d (a ⌣ y)`
    have key : moduleCatCyclesMap₂ μ hμ p (i + 1) (m + 1) h a ((K₂.toCycles i (i + 1)).hom y) =
        (-1 : ℤ) ^ p •
          (K₀.toCycles m (m + 1)).hom (μ p i m (by omega) ((K₁.iCycles p).hom a) y) := by
      apply K₀.moduleCat_iCycles_injective
      have hd := hμ p i m (by omega) ((K₁.iCycles p).hom a) y
      simp only [moduleCat_d_iCycles_apply, map_zero, LinearMap.zero_apply, zero_add] at hd
      simp [hd, smul_smul, ← mul_pow]
    rw [key, map_zsmul, (K₀.moduleCat_homologyπ_eq_zero_iff (m := m) (by simp) _).2 ⟨_, rfl⟩,
      smul_zero]
  · rw [K₂.toCycles_eq_zero hiq]
    simp

/-- The product with a fixed cocycle on the left, on cohomology. -/
private def moduleCatHomologyMap₂Left (p q n : ℕ) (h : p + q = n) (a : K₁.cycles p) :
    K₂.homology q ⟶ K₀.homology n :=
  (CokernelCofork.IsColimit.desc' (K₂.homologyIsCokernel _ q rfl)
    (ModuleCat.ofHom (moduleCatCyclesMap₂ μ hμ p q n h a) ≫ K₀.homologyπ n) (by
      ext y
      exact homologyπ_moduleCatCyclesMap₂_toCycles_right μ hμ h a _ y)).val

private lemma moduleCatHomologyMap₂Left_homologyπ (p q n : ℕ) (h : p + q = n) (a : K₁.cycles p)
    (b : K₂.cycles q) :
    (moduleCatHomologyMap₂Left μ hμ p q n h a).hom ((K₂.homologyπ q).hom b) =
      (K₀.homologyπ n).hom (moduleCatCyclesMap₂ μ hμ p q n h a b) :=
  ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc' (K₂.homologyIsCokernel _ q rfl)
    (ModuleCat.ofHom (moduleCatCyclesMap₂ μ hμ p q n h a) ≫ K₀.homologyπ n) _).property b

/-- The product on the left with a cocycle, on cohomology, as a linear function of the cocycle. -/
private def moduleCatHomologyMap₂Cycles (p q n : ℕ) (h : p + q = n) :
    K₁.cycles p ⟶ ModuleCat.of R (K₂.homology q →ₗ[R] K₀.homology n) :=
  ModuleCat.ofHom (X := K₁.cycles p)
    { toFun a := (moduleCatHomologyMap₂Left μ hμ p q n h a).hom
      map_add' a a' := LinearMap.ext fun β ↦ by
        obtain ⟨b, rfl⟩ := K₂.moduleCat_homologyπ_surjective q β
        simp only [moduleCatHomologyMap₂Left_homologyπ, map_add, LinearMap.add_apply]
      map_smul' r a := LinearMap.ext fun β ↦ by
        obtain ⟨b, rfl⟩ := K₂.moduleCat_homologyπ_surjective q β
        simp only [moduleCatHomologyMap₂Left_homologyπ, LinearMap.smul_apply, RingHom.id_apply]
        rw [map_smul, LinearMap.smul_apply, map_smul] }

private lemma toCycles_comp_moduleCatHomologyMap₂Cycles (p q n : ℕ) (h : p + q = n) :
    K₁.toCycles ((ComplexShape.up ℕ).prev p) p ≫ moduleCatHomologyMap₂Cycles μ hμ p q n h = 0 := by
  ext y : 2
  refine LinearMap.ext fun β ↦ ?_
  obtain ⟨b, rfl⟩ := K₂.moduleCat_homologyπ_surjective q β
  exact (moduleCatHomologyMap₂Left_homologyπ μ hμ p q n h _ b).trans
    (homologyπ_moduleCatCyclesMap₂_toCycles_left μ hμ h _ y b)

/-- **The product on cohomology** `Hᵖ(K₁) × H^q(K₂) → Hⁿ(K₀)`, `p + q = n`, of a family of products
of cochains obeying the Leibniz rule: the class of the product of representing cocycles
(`TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ`). -/
def moduleCatHomologyMap₂ (p q n : ℕ) (h : p + q = n) :
    K₁.homology p →ₗ[R] K₂.homology q →ₗ[R] K₀.homology n :=
  (CokernelCofork.IsColimit.desc' (K₁.homologyIsCokernel _ p rfl)
    (moduleCatHomologyMap₂Cycles μ hμ p q n h)
    (toCycles_comp_moduleCatHomologyMap₂Cycles μ hμ p q n h)).val.hom

/-- **The product on classes**: the product of the classes of two cocycles is the class of their
product. -/
@[simp]
theorem moduleCatHomologyMap₂_homologyπ (p q n : ℕ) (h : p + q = n) (a : K₁.cycles p)
    (b : K₂.cycles q) :
    moduleCatHomologyMap₂ μ hμ p q n h ((K₁.homologyπ p).hom a) ((K₂.homologyπ q).hom b) =
      (K₀.homologyπ n).hom (moduleCatCyclesMap₂ μ hμ p q n h a b) := by
  have hfac := ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    (K₁.homologyIsCokernel _ p rfl) (moduleCatHomologyMap₂Cycles μ hμ p q n h)
    (toCycles_comp_moduleCatHomologyMap₂Cycles μ hμ p q n h)).property a
  rw [moduleCatHomologyMap₂, ← moduleCatHomologyMap₂Left_homologyπ]
  exact LinearMap.congr_fun hfac _

/-- **The product on classes of elements**: the product of the classes of two cocycles given as
elements of the cochain modules is the class of their product. -/
theorem moduleCatHomologyMap₂_homologyπ_moduleCatCyclesMk {p q n : ℕ} (h : p + q = n)
    (x : K₁.X p) (m₁ : ℕ) (hm₁ : (ComplexShape.up ℕ).next p = m₁) (hx : (K₁.d p m₁).hom x = 0)
    (y : K₂.X q) (m₂ : ℕ) (hm₂ : (ComplexShape.up ℕ).next q = m₂) (hy : (K₂.d q m₂).hom y = 0) :
    moduleCatHomologyMap₂ μ hμ p q n h ((K₁.homologyπ p).hom (K₁.moduleCatCyclesMk x m₁ hm₁ hx))
        ((K₂.homologyπ q).hom (K₂.moduleCatCyclesMk y m₂ hm₂ hy)) =
      (K₀.homologyπ n).hom (K₀.moduleCatCyclesMk (μ p q n h x y) (n + 1) (by simp)
        (by subst hm₁ hm₂; rw [CochainComplex.next] at hx hy; simp [hμ, hx, hy])) := by
  rw [moduleCatHomologyMap₂_homologyπ]
  congr 1
  apply K₀.moduleCat_iCycles_injective
  simp

section Unit

variable
  (ε : ∀ p q n : ℕ, p + q = n → K₁.X p →ₗ[R] K₂.X q →ₗ[R] K₂.X n)
  (hε : ∀ (p q n : ℕ) (h : p + q = n) (a : K₁.X p) (b : K₂.X q),
    (K₂.d n (n + 1)).hom (ε p q n h a b) =
      ε (p + 1) q (n + 1) ((Nat.succ_add p q).trans (congrArg Nat.succ h))
          ((K₁.d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • ε p (q + 1) (n + 1) ((Nat.add_succ p q).trans (congrArg Nat.succ h)) a
          ((K₂.d q (q + 1)).hom b))

/-- **Left unit on cohomology.** If a `0`-cocycle `e` is a left unit for a product of cochains
`K₁ × K₂ → K₂`, then its class is a left unit for the product on cohomology. -/
theorem moduleCatHomologyMap₂_unit_left (e : K₁.X 0) (he : (K₁.d 0 1).hom e = 0) {q : ℕ}
    (heε : ∀ b : K₂.X q, ε 0 q q (zero_add q) e b = b) (β : K₂.homology q) :
    moduleCatHomologyMap₂ ε hε 0 q q (zero_add q)
      ((K₁.homologyπ 0).hom (K₁.moduleCatCyclesMk e 1 (by simp) he)) β = β := by
  obtain ⟨b, rfl⟩ := K₂.moduleCat_homologyπ_surjective q β
  rw [moduleCatHomologyMap₂_homologyπ]
  congr 1
  apply K₂.moduleCat_iCycles_injective
  simp [heε]

end Unit

section Unit

variable
  (ε : ∀ p q n : ℕ, p + q = n → K₁.X p →ₗ[R] K₂.X q →ₗ[R] K₁.X n)
  (hε : ∀ (p q n : ℕ) (h : p + q = n) (a : K₁.X p) (b : K₂.X q),
    (K₁.d n (n + 1)).hom (ε p q n h a b) =
      ε (p + 1) q (n + 1) ((Nat.succ_add p q).trans (congrArg Nat.succ h))
          ((K₁.d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • ε p (q + 1) (n + 1) ((Nat.add_succ p q).trans (congrArg Nat.succ h)) a
          ((K₂.d q (q + 1)).hom b))

/-- **Right unit on cohomology.** If a `0`-cocycle `e` is a right unit for a product of cochains
`K₁ × K₂ → K₁`, then its class is a right unit for the product on cohomology. -/
theorem moduleCatHomologyMap₂_unit_right (e : K₂.X 0) (he : (K₂.d 0 1).hom e = 0) {p : ℕ}
    (heε : ∀ a : K₁.X p, ε p 0 p (add_zero p) a e = a) (α : K₁.homology p) :
    moduleCatHomologyMap₂ ε hε p 0 p (add_zero p) α
      ((K₂.homologyπ 0).hom (K₂.moduleCatCyclesMk e 1 (by simp) he)) = α := by
  obtain ⟨a, rfl⟩ := K₁.moduleCat_homologyπ_surjective p α
  rw [moduleCatHomologyMap₂_homologyπ]
  congr 1
  apply K₁.moduleCat_iCycles_injective
  simp [heε]

end Unit

section Assoc

variable {K₃ K₁₂ K₂₃ : CochainComplex (ModuleCat.{v} R) ℕ}
  (μ₁₂ : ∀ p q n : ℕ, p + q = n → K₁.X p →ₗ[R] K₂.X q →ₗ[R] K₁₂.X n)
  (hμ₁₂ : ∀ (p q n : ℕ) (h : p + q = n) (a : K₁.X p) (b : K₂.X q),
    (K₁₂.d n (n + 1)).hom (μ₁₂ p q n h a b) =
      μ₁₂ (p + 1) q (n + 1) ((Nat.succ_add p q).trans (congrArg Nat.succ h))
          ((K₁.d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • μ₁₂ p (q + 1) (n + 1) ((Nat.add_succ p q).trans (congrArg Nat.succ h)) a
          ((K₂.d q (q + 1)).hom b))
  (μ₂₃ : ∀ p q n : ℕ, p + q = n → K₂.X p →ₗ[R] K₃.X q →ₗ[R] K₂₃.X n)
  (hμ₂₃ : ∀ (p q n : ℕ) (h : p + q = n) (a : K₂.X p) (b : K₃.X q),
    (K₂₃.d n (n + 1)).hom (μ₂₃ p q n h a b) =
      μ₂₃ (p + 1) q (n + 1) ((Nat.succ_add p q).trans (congrArg Nat.succ h))
          ((K₂.d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • μ₂₃ p (q + 1) (n + 1) ((Nat.add_succ p q).trans (congrArg Nat.succ h)) a
          ((K₃.d q (q + 1)).hom b))
  (μ₁₂₃ : ∀ p q n : ℕ, p + q = n → K₁₂.X p →ₗ[R] K₃.X q →ₗ[R] K₀.X n)
  (hμ₁₂₃ : ∀ (p q n : ℕ) (h : p + q = n) (a : K₁₂.X p) (b : K₃.X q),
    (K₀.d n (n + 1)).hom (μ₁₂₃ p q n h a b) =
      μ₁₂₃ (p + 1) q (n + 1) ((Nat.succ_add p q).trans (congrArg Nat.succ h))
          ((K₁₂.d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • μ₁₂₃ p (q + 1) (n + 1) ((Nat.add_succ p q).trans (congrArg Nat.succ h)) a
          ((K₃.d q (q + 1)).hom b))
  (μ₁₂₃' : ∀ p q n : ℕ, p + q = n → K₁.X p →ₗ[R] K₂₃.X q →ₗ[R] K₀.X n)
  (hμ₁₂₃' : ∀ (p q n : ℕ) (h : p + q = n) (a : K₁.X p) (b : K₂₃.X q),
    (K₀.d n (n + 1)).hom (μ₁₂₃' p q n h a b) =
      μ₁₂₃' (p + 1) q (n + 1) ((Nat.succ_add p q).trans (congrArg Nat.succ h))
          ((K₁.d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • μ₁₂₃' p (q + 1) (n + 1) ((Nat.add_succ p q).trans (congrArg Nat.succ h)) a
          ((K₂₃.d q (q + 1)).hom b))

/-- **Associativity on cohomology.** Products of cochains `μ₁₂ : K₁ × K₂ → K₁₂`,
`μ₂₃ : K₂ × K₃ → K₂₃`, `μ₁₂₃ : K₁₂ × K₃ → K₀` and `μ₁₂₃' : K₁ × K₂₃ → K₀` with
`μ₁₂₃ (μ₁₂ a b) c = μ₁₂₃' a (μ₂₃ b c)` induce products on cohomology satisfying the same
identity. -/
theorem moduleCatHomologyMap₂_assoc {p q r m l n : ℕ} (h₁ : p + q = m) (h₂ : m + r = n)
    (h₃ : q + r = l) (h₄ : p + l = n)
    (hassoc : ∀ (a : K₁.X p) (b : K₂.X q) (c : K₃.X r),
      μ₁₂₃ m r n h₂ (μ₁₂ p q m h₁ a b) c = μ₁₂₃' p l n h₄ a (μ₂₃ q r l h₃ b c))
    (α : K₁.homology p) (β : K₂.homology q) (γ : K₃.homology r) :
    moduleCatHomologyMap₂ μ₁₂₃ hμ₁₂₃ m r n h₂ (moduleCatHomologyMap₂ μ₁₂ hμ₁₂ p q m h₁ α β) γ =
      moduleCatHomologyMap₂ μ₁₂₃' hμ₁₂₃' p l n h₄ α
        (moduleCatHomologyMap₂ μ₂₃ hμ₂₃ q r l h₃ β γ) := by
  obtain ⟨a, rfl⟩ := K₁.moduleCat_homologyπ_surjective p α
  obtain ⟨b, rfl⟩ := K₂.moduleCat_homologyπ_surjective q β
  obtain ⟨c, rfl⟩ := K₃.moduleCat_homologyπ_surjective r γ
  simp only [moduleCatHomologyMap₂_homologyπ]
  congr 1
  apply K₀.moduleCat_iCycles_injective
  simp [hassoc]

end Assoc

section Naturality

variable {L₁ L₂ L₀ : CochainComplex (ModuleCat.{v} R) ℕ}
  (ν : ∀ p q n : ℕ, p + q = n → L₁.X p →ₗ[R] L₂.X q →ₗ[R] L₀.X n)
  (hν : ∀ (p q n : ℕ) (h : p + q = n) (a : L₁.X p) (b : L₂.X q),
    (L₀.d n (n + 1)).hom (ν p q n h a b) =
      ν (p + 1) q (n + 1) ((Nat.succ_add p q).trans (congrArg Nat.succ h))
          ((L₁.d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • ν p (q + 1) (n + 1) ((Nat.add_succ p q).trans (congrArg Nat.succ h)) a
          ((L₂.d q (q + 1)).hom b))
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₀ : K₀ ⟶ L₀)

/-- **Naturality of the product on cohomology.** Cochain maps `f₁`, `f₂` and `f₀` such that
`f₀ (μ a b) = ν (f₁ a) (f₂ b)` on cochains intertwine the induced products on cohomology. -/
theorem homologyMap_moduleCatHomologyMap₂
    (hf : ∀ (p q n : ℕ) (h : p + q = n) (a : K₁.X p) (b : K₂.X q),
      (f₀.f n).hom (μ p q n h a b) = ν p q n h ((f₁.f p).hom a) ((f₂.f q).hom b))
    (p q n : ℕ) (h : p + q = n) (α : K₁.homology p) (β : K₂.homology q) :
    (homologyMap f₀ n).hom (moduleCatHomologyMap₂ μ hμ p q n h α β) =
      moduleCatHomologyMap₂ ν hν p q n h ((homologyMap f₁ p).hom α) ((homologyMap f₂ q).hom β) := by
  obtain ⟨a, rfl⟩ := K₁.moduleCat_homologyπ_surjective p α
  obtain ⟨b, rfl⟩ := K₂.moduleCat_homologyπ_surjective q β
  simp only [moduleCat_homologyMap_homologyπ, moduleCatHomologyMap₂_homologyπ]
  congr 1
  apply L₀.moduleCat_iCycles_injective
  simp [hf]

end Naturality

end TauCeti.CochainComplex
