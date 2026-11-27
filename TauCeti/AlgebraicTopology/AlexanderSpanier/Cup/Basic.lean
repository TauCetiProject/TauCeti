/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Algebra.Homology.ModuleCat.Bilinear
public import TauCeti.AlgebraicTopology.AlexanderSpanier.Basic

import all TauCeti.AlgebraicTopology.AlexanderSpanier.Basic
import TauCeti.Data.Fin.Basic

/-!
# The cup product in Alexander–Spanier cohomology

Let `X` be a topological space and `Λ` an algebra over a commutative ring `R`. The **cup product**
of Alexander–Spanier cochains `φ : X^{p+1} → Λ` and `ψ : X^{q+1} → Λ` is

`(φ ⌣ ψ)(x₀, …, x_{p+q}) = φ(x₀, …, x_p) · ψ(x_p, …, x_{p+q})`,

the value of `φ` on the front `p`-face times the value of `ψ` on the back `q`-face. If `φ` or `ψ`
is locally zero then so is `φ ⌣ ψ`, since the faces of a tuple of points of an open set `U` are
again tuples of points of `U`. So the cup product descends to an `R`-bilinear map of
Alexander–Spanier cochains (`TauCeti.AlexanderSpanier.cup`), given on classes of functions by the
displayed formula (`TauCeti.AlexanderSpanier.cup_cochainClass`). No sign enters, since the
coefficients form a single algebra placed in degree `0`.

The cup product of cochains satisfies:

* the **Leibniz rule** `δ(a ⌣ b) = δa ⌣ b + (-1)ᵖ a ⌣ δb` for `a` of degree `p`
  (`TauCeti.AlexanderSpanier.d_cup`);
* **associativity** (`TauCeti.AlexanderSpanier.cup_assoc`);
* the **unit**: the class of the constant function `1`
  (`TauCeti.AlexanderSpanier.oneCochain`) is a `0`-cocycle and a two-sided unit
  (`TauCeti.AlexanderSpanier.d_oneCochain`, `TauCeti.AlexanderSpanier.oneCochain_cup`,
  `TauCeti.AlexanderSpanier.cup_oneCochain`);
* **naturality** under pullback along continuous maps
  (`TauCeti.AlexanderSpanier.cochainComplexMap_f_cup`).

By the Leibniz rule the cup product descends to an `R`-bilinear product
`Hᵖ(X; Λ) × H^q(X; Λ) → H^{p+q}(X; Λ)` on Alexander–Spanier cohomology
(`TauCeti.AlexanderSpanier.cohomologyCup`), an instance of the general product on the cohomology of
cochain complexes of modules `TauCeti.CochainComplex.moduleCatHomologyMap₂`. It is computed on
classes of cocycles by the cup product of representatives
(`TauCeti.AlexanderSpanier.cohomologyCup_homologyπ`), is natural under continuous maps
(`TauCeti.AlexanderSpanier.cohomologyMap_cohomologyCup`) and associative
(`TauCeti.AlexanderSpanier.cohomologyCup_assoc`), with unit the class
`TauCeti.AlexanderSpanier.cohomologyOne` of the constant function `1`, which corresponds to the
constant locally constant function `1` under `H⁰(X; Λ) ≅ LocallyConstant X Λ`
(`TauCeti.AlexanderSpanier.cohomologyZeroIso_hom_cohomologyOne`). So `H^*(X; Λ)` is a graded
`R`-algebra, natural in `X`.

The Leibniz rule is the same identity between front and back faces as for the cup product of Čech
cochains (`TauCeti.CategoryTheory.d_cechCup`), here for functions on tuples of points rather than
for sections over intersections of a cover.

The relative cup product `Hᵖ(X; Λ) × H^q(X, A; Λ) → H^{p+q}(X, A; Λ)` is in
`TauCeti.AlgebraicTopology.AlexanderSpanier.Cup.Relative`.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6, Sections 6.4 and 6.5.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex

universe w u v

namespace TauCeti.AlexanderSpanier

variable {R : Type w} [CommRing R] {X : Type u} [TopologicalSpace X] {Λ : Type v} [Ring Λ]
  [Algebra R Λ]

section Cochain

variable (p q n : ℕ) (h : p + q = n)

variable (R X Λ) in
/-- The cup product of functions on tuples: `φ(x₀, …, x_p) · ψ(x_p, …, x_n)`. -/
private def cupFun :
    ((Fin (p + 1) → X) → Λ) →ₗ[R] ((Fin (q + 1) → X) → Λ) →ₗ[R] (Fin (n + 1) → X) → Λ :=
  LinearMap.mk₂ R
    (fun φ ψ y ↦ φ (y ∘ Fin.castLE (by omega)) *
      ψ (y ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)))
    (fun _ _ _ ↦ funext fun _ ↦ add_mul _ _ _)
    (fun _ _ _ ↦ funext fun _ ↦ smul_mul_assoc _ _ _)
    (fun _ _ _ ↦ funext fun _ ↦ mul_add _ _ _)
    (fun _ _ _ ↦ funext fun _ ↦ mul_smul_comm _ _ _)

omit [TopologicalSpace X] in
private lemma cupFun_apply (φ : (Fin (p + 1) → X) → Λ) (ψ : (Fin (q + 1) → X) → Λ)
    (y : Fin (n + 1) → X) :
    cupFun R X Λ p q n h φ ψ y = φ (y ∘ Fin.castLE (by omega)) *
      ψ (y ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) :=
  rfl

/-- A locally zero function cupped with any function is locally zero. -/
private lemma locallyZero_le_ker_cupFun :
    locallyZero R X Λ (Fin (p + 1)) ≤
      LinearMap.ker ((cupFun R X Λ p q n h).compr₂ (locallyZero R X Λ (Fin (n + 1))).mkQ) := by
  intro φ hφ
  refine LinearMap.mem_ker.2 (LinearMap.ext fun ψ ↦ ?_)
  refine (Submodule.Quotient.mk_eq_zero _).2 (mem_locallyZero.2 fun x ↦ ?_)
  obtain ⟨U, hU, hφU⟩ := mem_locallyZero.1 hφ x
  exact ⟨U, hU, fun y hy ↦ by rw [cupFun_apply, hφU (y ∘ _) fun i ↦ hy _, zero_mul]⟩

/-- Any function cupped with a locally zero function is locally zero. -/
private lemma locallyZero_le_ker_flip_cupFun :
    locallyZero R X Λ (Fin (q + 1)) ≤
      LinearMap.ker ((cupFun R X Λ p q n h).compr₂
        (locallyZero R X Λ (Fin (n + 1))).mkQ).flip := by
  intro ψ hψ
  refine LinearMap.mem_ker.2 (LinearMap.ext fun φ ↦ ?_)
  refine (Submodule.Quotient.mk_eq_zero _).2 (mem_locallyZero.2 fun x ↦ ?_)
  obtain ⟨U, hU, hψU⟩ := mem_locallyZero.1 hψ x
  exact ⟨U, hU, fun y hy ↦ by rw [cupFun_apply, hψU (y ∘ _) fun i ↦ hy _, mul_zero]⟩

variable (R X Λ) in
/-- The **cup product** of Alexander–Spanier cochains: for cochains of degrees `p` and `q` with
`p + q = n`, the class of `(x₀, …, xₙ) ↦ φ(x₀, …, x_p) · ψ(x_p, …, xₙ)`, the value of `φ` on the
front `p`-face times the value of `ψ` on the back `q`-face (`cup_cochainClass`). -/
def cup :
    (cochainComplex R X Λ).X p →ₗ[R] (cochainComplex R X Λ).X q →ₗ[R]
      (cochainComplex R X Λ).X n :=
  LinearMap.liftQ₂ _ _ ((cupFun R X Λ p q n h).compr₂ (locallyZero R X Λ (Fin (n + 1))).mkQ)
    (locallyZero_le_ker_cupFun p q n h) (locallyZero_le_ker_flip_cupFun p q n h)

variable {p q n}

/-- The cup product of the classes of `φ` and `ψ` is the class of
`(x₀, …, xₙ) ↦ φ(x₀, …, x_p) · ψ(x_p, …, xₙ)`. -/
@[simp]
theorem cup_cochainClass (φ : (Fin (p + 1) → X) → Λ) (ψ : (Fin (q + 1) → X) → Λ) :
    cup R X Λ p q n h (cochainClass R X Λ p φ) (cochainClass R X Λ q ψ) =
      cochainClass R X Λ n fun y ↦ φ (y ∘ Fin.castLE (by omega)) *
        ψ (y ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) :=
  (rfl)

omit [TopologicalSpace X] [Ring Λ] in
/-- Two functions on tuples agree on tuples reindexed along maps of vertices with the same
values. -/
private lemma apply_comp_eq_of_val {m k : ℕ} (φ : (Fin (m + 1) → X) → Λ) (y : Fin (k + 1) → X)
    {σ σ' : Fin (m + 1) → Fin (k + 1)} (h : ∀ i, (σ i : ℕ) = σ' i) :
    φ (y ∘ σ) = φ (y ∘ σ') := by
  rw [show σ = σ' from funext fun i ↦ Fin.ext (h i)]

/-- The **Leibniz rule** for the Alexander–Spanier cup product:
`δ(a ⌣ b) = δa ⌣ b + (-1) ^ p a ⌣ δb` for a cochain `a` of degree `p`. -/
theorem d_cup (a : (cochainComplex R X Λ).X p) (b : (cochainComplex R X Λ).X q) :
    ((cochainComplex R X Λ).d n (n + 1)).hom (cup R X Λ p q n h a b) =
      cup R X Λ (p + 1) q (n + 1) (by omega) (((cochainComplex R X Λ).d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • cup R X Λ p (q + 1) (n + 1) (by omega) a
          (((cochainComplex R X Λ).d q (q + 1)).hom b) := by
  subst h
  obtain ⟨φ, rfl⟩ := cochainClass_surjective p a
  obtain ⟨ψ, rfl⟩ := cochainClass_surjective q b
  simp only [cup_cochainClass, cochainComplex_d_cochainClass, ← map_zsmul, ← map_add]
  congr 1
  funext y
  rw [Pi.add_apply, Pi.smul_apply,
    ← Fin.sum_congr' _ (show p + 1 + (q + 1) = p + q + 2 by omega), Fin.sum_univ_add,
    Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := q + 1)]
  -- the faces `j ≤ p` of `φ ⌣ ψ` are the faces of `δφ`, the faces `j ≥ p + 1` those of `δψ`,
  -- and the last face of `δφ` cancels the first face of `δψ`
  rw [add_mul, mul_add, smul_add, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
  have key {P₁ P₂ Q₁ Q₂ S T : Λ} (h₁ : P₁ = Q₁) (h₂ : P₂ = Q₂) (h : S + T = 0) :
      P₁ + P₂ = Q₁ + S + (T + Q₂) := by
    rw [h₁, h₂, add_assoc Q₁, ← add_assoc S, h, zero_add]
  refine key (Finset.sum_congr rfl fun x _ ↦ ?_) (Finset.sum_congr rfl fun x _ ↦ ?_) ?_
  · rw [smul_mul_assoc]
    congr 2 <;> exact apply_comp_eq_of_val _ y fun i ↦ by grind [Fin.val_succAbove]
  · rw [mul_smul_comm, smul_smul, ← pow_add]
    congr 2
    · simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      omega
    all_goals exact apply_comp_eq_of_val _ y fun i ↦ by grind [Fin.val_succAbove]
  · rw [Fin.val_last, Fin.val_zero, pow_zero, one_smul, pow_succ, mul_neg_one, neg_smul]
    simp only [neg_mul, smul_mul_assoc, neg_add_eq_zero]
    congr 2 <;> exact apply_comp_eq_of_val _ y fun i ↦ by grind [Fin.val_succAbove]

/-- **Associativity** of the Alexander–Spanier cup product, at the level of cochains. -/
theorem cup_assoc {r m l : ℕ} (h₁ : p + q = m) (h₂ : m + r = n) (h₃ : q + r = l)
    (h₄ : p + l = n) (a : (cochainComplex R X Λ).X p) (b : (cochainComplex R X Λ).X q)
    (c : (cochainComplex R X Λ).X r) :
    cup R X Λ m r n h₂ (cup R X Λ p q m h₁ a b) c =
      cup R X Λ p l n h₄ a (cup R X Λ q r l h₃ b c) := by
  obtain ⟨φ, rfl⟩ := cochainClass_surjective p a
  obtain ⟨ψ, rfl⟩ := cochainClass_surjective q b
  obtain ⟨χ, rfl⟩ := cochainClass_surjective r c
  simp only [cup_cochainClass, Function.comp_def]
  congr 1
  funext y
  rw [mul_assoc]
  exact congrArg₂ (· * ·) (apply_comp_eq_of_val _ y fun i ↦ by grind) <|
    congrArg₂ (· * ·) (apply_comp_eq_of_val _ y fun i ↦ by grind)
      (apply_comp_eq_of_val _ y fun i ↦ by grind)

variable (R X Λ) in
/-- The **unit cochain**: the class of the constant function `1` on points. -/
def oneCochain : (cochainComplex R X Λ).X 0 :=
  cochainClass R X Λ 0 1

variable (R X Λ) in
/-- The unit cochain is the class of the constant function `1`. -/
theorem oneCochain_def : oneCochain R X Λ = cochainClass R X Λ 0 1 :=
  (rfl)

/-- The unit cochain is a cocycle. -/
@[simp]
theorem d_oneCochain : ((cochainComplex R X Λ).d 0 1).hom (oneCochain R X Λ) = 0 := by
  rw [oneCochain, cochainComplex_d_cochainClass, cochainClass_eq_zero_iff]
  convert isLocallyZero_zero (X := X) (M := Λ) (ι := Fin (0 + 1 + 1))
  simp [Fin.sum_univ_two]

/-- The unit cochain is a left unit for the cup product. -/
@[simp]
theorem oneCochain_cup (b : (cochainComplex R X Λ).X q) :
    cup R X Λ 0 q q (zero_add q) (oneCochain R X Λ) b = b := by
  obtain ⟨ψ, rfl⟩ := cochainClass_surjective q b
  rw [oneCochain, cup_cochainClass]
  congr 1
  funext y
  rw [Pi.one_apply, one_mul]
  exact apply_comp_eq_of_val _ y fun i ↦ by simp

/-- The unit cochain is a right unit for the cup product. -/
@[simp]
theorem cup_oneCochain (a : (cochainComplex R X Λ).X p) :
    cup R X Λ p 0 p (add_zero p) a (oneCochain R X Λ) = a := by
  obtain ⟨φ, rfl⟩ := cochainClass_surjective p a
  rw [oneCochain, cup_cochainClass]
  congr 1
  funext y
  rw [Pi.one_apply, mul_one]
  exact apply_comp_eq_of_val _ y fun i ↦ by simp

/-- **Naturality** of the cup product of cochains: pulling back along a continuous map `f`
commutes with the cup product. -/
@[simp]
theorem cochainComplexMap_f_cup {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))
    (a : (cochainComplex R X Λ).X p) (b : (cochainComplex R X Λ).X q) :
    ((cochainComplexMap R Λ f).f n).hom (cup R X Λ p q n h a b) =
      cup R Y Λ p q n h (((cochainComplexMap R Λ f).f p).hom a)
        (((cochainComplexMap R Λ f).f q).hom b) := by
  obtain ⟨φ, rfl⟩ := cochainClass_surjective p a
  obtain ⟨ψ, rfl⟩ := cochainClass_surjective q b
  simp only [cup_cochainClass, cochainComplexMap_f_cochainClass, Function.comp_assoc]

/-- Pulling back the unit cochain gives the unit cochain. -/
@[simp]
theorem cochainComplexMap_f_oneCochain {Y : Type u} [TopologicalSpace Y] (f : C(Y, X)) :
    ((cochainComplexMap R Λ f).f 0).hom (oneCochain R X Λ) = oneCochain R Y Λ :=
  (rfl)

end Cochain

section Cohomology

variable (R X Λ) in
/-- The **cup product in Alexander–Spanier cohomology** `Hᵖ(X; Λ) × H^q(X; Λ) → Hⁿ(X; Λ)`, for
`p + q = n`: the class of the cup product of representing cocycles (`cohomologyCup_homologyπ`). -/
def cohomologyCup (p q n : ℕ) (h : p + q = n) :
    cohomology R X Λ p →ₗ[R] cohomology R X Λ q →ₗ[R] cohomology R X Λ n :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂ (cup R X Λ) (fun _ _ _ h a b ↦ d_cup h a b) p q n h

/-- The cup product in cohomology is the product on cohomology induced by the cup product of
cochains. -/
theorem cohomologyCup_def (p q n : ℕ) (h : p + q = n) :
    cohomologyCup R X Λ p q n h =
      TauCeti.CochainComplex.moduleCatHomologyMap₂ (cup R X Λ) (fun _ _ _ h a b ↦ d_cup h a b)
        p q n h :=
  (rfl)

/-- The cup product of the classes of two cocycles is the class of their cup product. -/
@[simp]
theorem cohomologyCup_homologyπ {p q n : ℕ} (h : p + q = n)
    (a : (cochainComplex R X Λ).cycles p) (b : (cochainComplex R X Λ).cycles q) :
    cohomologyCup R X Λ p q n h (((cochainComplex R X Λ).homologyπ p).hom a)
        (((cochainComplex R X Λ).homologyπ q).hom b) =
      ((cochainComplex R X Λ).homologyπ n).hom
        (TauCeti.CochainComplex.moduleCatCyclesMap₂ (cup R X Λ) (fun _ _ _ h a b ↦ d_cup h a b)
          p q n h a b) :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ _ _ p q n h a b

/-- **Naturality** of the cup product in Alexander–Spanier cohomology: the map induced by a
continuous map `f` is multiplicative. -/
@[simp]
theorem cohomologyMap_cohomologyCup {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))
    {p q n : ℕ} (h : p + q = n) (α : cohomology R X Λ p) (β : cohomology R X Λ q) :
    (cohomologyMap R Λ f n).hom (cohomologyCup R X Λ p q n h α β) =
      cohomologyCup R Y Λ p q n h ((cohomologyMap R Λ f p).hom α)
        ((cohomologyMap R Λ f q).hom β) :=
  TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂ _ _ _ _ _ _ _
    (fun _ _ _ h a b ↦ cochainComplexMap_f_cup h f a b) p q n h α β

/-- **Associativity** of the cup product in Alexander–Spanier cohomology. -/
theorem cohomologyCup_assoc {p q r m l n : ℕ} (h₁ : p + q = m) (h₂ : m + r = n)
    (h₃ : q + r = l) (h₄ : p + l = n) (α : cohomology R X Λ p) (β : cohomology R X Λ q)
    (γ : cohomology R X Λ r) :
    cohomologyCup R X Λ m r n h₂ (cohomologyCup R X Λ p q m h₁ α β) γ =
      cohomologyCup R X Λ p l n h₄ α (cohomologyCup R X Λ q r l h₃ β γ) :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_assoc _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄
    (cup_assoc h₁ h₂ h₃ h₄) α β γ

variable (R X Λ) in
/-- The **unit class** `1 ∈ H⁰(X; Λ)`: the class of the unit cocycle, the constant function `1`. -/
def cohomologyOne : cohomology R X Λ 0 :=
  ((cochainComplex R X Λ).homologyπ 0).hom
    ((cochainComplex R X Λ).moduleCatCyclesMk (oneCochain R X Λ) 1 (by simp) d_oneCochain)

/-- The unit class is the class of the unit cocycle. -/
theorem cohomologyOne_def :
    cohomologyOne R X Λ = ((cochainComplex R X Λ).homologyπ 0).hom
      ((cochainComplex R X Λ).moduleCatCyclesMk (oneCochain R X Λ) 1 (by simp) d_oneCochain) :=
  (rfl)

/-- Under the identification `H⁰(X; Λ) ≅ LocallyConstant X Λ`, the unit class is the constant
function `1`. -/
@[simp]
theorem cohomologyZeroIso_hom_cohomologyOne :
    (cohomologyZeroIso R X Λ).hom.hom (cohomologyOne R X Λ) = 1 := by
  ext x
  have h := (cochainComplex R X Λ).iCycles_moduleCatCyclesMk 0 (oneCochain R X Λ) 1 (by simp)
    d_oneCochain
  exact cohomologyZeroIso_hom_homologyπ_apply (φ := 1) h x

/-- The map induced by a continuous map sends the unit class to the unit class. -/
@[simp]
theorem cohomologyMap_cohomologyOne {Y : Type u} [TopologicalSpace Y] (f : C(Y, X)) :
    (cohomologyMap R Λ f 0).hom (cohomologyOne R X Λ) = cohomologyOne R Y Λ := by
  rw [cohomologyOne_def, cohomologyOne_def, homologyMap_homologyπ_moduleCatCyclesMk]
  congr 2

/-- The unit class is a left unit for the cup product in cohomology. -/
@[simp]
theorem cohomologyOne_cohomologyCup {q : ℕ} (β : cohomology R X Λ q) :
    cohomologyCup R X Λ 0 q q (zero_add q) (cohomologyOne R X Λ) β = β :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_unit_left _ _ _ d_oneCochain oneCochain_cup β

/-- The unit class is a right unit for the cup product in cohomology. -/
@[simp]
theorem cohomologyCup_cohomologyOne {p : ℕ} (α : cohomology R X Λ p) :
    cohomologyCup R X Λ p 0 p (add_zero p) α (cohomologyOne R X Λ) = α :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_unit_right _ _ _ d_oneCochain cup_oneCochain α

end Cohomology

end TauCeti.AlexanderSpanier
