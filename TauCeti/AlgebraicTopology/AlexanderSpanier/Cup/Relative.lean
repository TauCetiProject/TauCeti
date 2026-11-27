/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.AlexanderSpanier.Cup.Basic
public import TauCeti.AlgebraicTopology.AlexanderSpanier.Relative

import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# The relative cup product in Alexander–Spanier cohomology

Let `A` be a subspace of a topological space `X` and `Λ` an algebra over a commutative ring `R`.
The cup product `a ⌣ b` of an Alexander–Spanier cochain `a` of `X` with a relative cochain `b` of
`(X, A)` is again a relative cochain: if `b` is represented by a function `ψ` whose restriction to
`A` is locally zero on `A`, then so is the restriction of `φ ⌣ ψ`, since restriction to `A`
commutes with the cup product (`TauCeti.AlexanderSpanier.cochainComplexMap_f_cup`). This defines
the **relative cup product** of cochains `C^p(X; Λ) × C^q(X, A; Λ) → C^{p+q}(X, A; Λ)`
(`TauCeti.AlexanderSpanier.relativeCup`), characterized by
`ι (a ⌣ b) = a ⌣ ι b` for the inclusion `ι : C^*(X, A; Λ) ⟶ C^*(X; Λ)`
(`TauCeti.AlexanderSpanier.relativeCochainComplexι_f_relativeCup`). It inherits from the absolute
cup product the Leibniz rule (`TauCeti.AlexanderSpanier.d_relativeCup`), associativity with the
absolute cup product (`TauCeti.AlexanderSpanier.relativeCup_assoc`), the unit
(`TauCeti.AlexanderSpanier.oneCochain_relativeCup`), and naturality under maps of pairs
(`TauCeti.AlexanderSpanier.relativeCochainComplexMap_f_relativeCup`).

By the Leibniz rule it descends to the **relative cup product in cohomology**

`Hᵖ(X; Λ) × H^q(X, A; Λ) → H^{p+q}(X, A; Λ)`

(`TauCeti.AlexanderSpanier.relativeCohomologyCup`), which makes the relative cohomology of `(X, A)`
a module over the cohomology ring of `X`: it is associative with respect to the absolute cup
product (`TauCeti.AlexanderSpanier.relativeCohomologyCup_assoc`) and the unit class acts as the
identity (`TauCeti.AlexanderSpanier.cohomologyOne_relativeCohomologyCup`). It is compatible with
the absolute cup product along the map `H^*(X, A; Λ) → H^*(X; Λ)`
(`TauCeti.AlexanderSpanier.relativeCohomologyMap_relativeCohomologyCup`), and natural under maps
of pairs `f : (Y, B) → (X, A)`
(`TauCeti.AlexanderSpanier.homologyMap_relativeCochainComplexMap_relativeCohomologyCup`).

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6, Sections 6.4 and 6.5.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex

universe w u v

namespace TauCeti.AlexanderSpanier

variable {R : Type w} [CommRing R] {X : Type u} [TopologicalSpace X] {Λ : Type v} [Ring Λ]
  [Algebra R Λ] (A : Set X)

section Cochain

variable {p q n : ℕ} (h : p + q = n)

/-- The cup product of a cochain with a relative cochain is a relative cochain. -/
private lemma cup_mem_range_relativeCochainComplexι (a : (cochainComplex R X Λ).X p)
    (b : (relativeCochainComplex R Λ A).X q) :
    cup R X Λ p q n h a (((relativeCochainComplexι R Λ A).f q).hom b) ∈
      LinearMap.range ((relativeCochainComplexι R Λ A).f n).hom := by
  have hb : ((restriction R Λ A).f q).hom (((relativeCochainComplexι R Λ A).f q).hom b) = 0 := by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
      relativeCochainComplexι_comp_restriction]
    simp
  rw [range_relativeCochainComplexι_f, LinearMap.mem_ker, restriction, cochainComplexMap_f_cup]
  rw [restriction] at hb
  rw [hb, map_zero]

variable (R Λ) (p q n) in
/-- The **relative cup product** of Alexander–Spanier cochains
`C^p(X; Λ) × C^q(X, A; Λ) → Cⁿ(X, A; Λ)`, for `p + q = n`: the cup product of a cochain of `X`
with a relative cochain of `(X, A)`, which is again a relative cochain
(`relativeCochainComplexι_f_relativeCup`). -/
def relativeCup :
    (cochainComplex R X Λ).X p →ₗ[R] (relativeCochainComplex R Λ A).X q →ₗ[R]
      (relativeCochainComplex R Λ A).X n :=
  LinearMap.codRestrict₂ ((cup R X Λ p q n h).compl₂ ((relativeCochainComplexι R Λ A).f q).hom)
    ((relativeCochainComplexι R Λ A).f n).hom (relativeCochainComplexι_f_injective R Λ A n)
    (cup_mem_range_relativeCochainComplexι A h)

/-- The relative cup product `a ⌣ b`, viewed as an absolute cochain, is the cup product of `a` with
`b` viewed as an absolute cochain. -/
@[simp]
theorem relativeCochainComplexι_f_relativeCup (a : (cochainComplex R X Λ).X p)
    (b : (relativeCochainComplex R Λ A).X q) :
    ((relativeCochainComplexι R Λ A).f n).hom (relativeCup R Λ A p q n h a b) =
      cup R X Λ p q n h a (((relativeCochainComplexι R Λ A).f q).hom b) :=
  LinearMap.codRestrict₂_apply _ _ _ _ a b

/-- The **Leibniz rule** for the relative cup product:
`δ(a ⌣ b) = δa ⌣ b + (-1) ^ p a ⌣ δb` for a cochain `a` of degree `p`. -/
theorem d_relativeCup (a : (cochainComplex R X Λ).X p) (b : (relativeCochainComplex R Λ A).X q) :
    ((relativeCochainComplex R Λ A).d n (n + 1)).hom (relativeCup R Λ A p q n h a b) =
      relativeCup R Λ A (p + 1) q (n + 1) (by omega) (((cochainComplex R X Λ).d p (p + 1)).hom a)
          b +
        (-1 : ℤ) ^ p • relativeCup R Λ A p (q + 1) (n + 1) (by omega) a
          (((relativeCochainComplex R Λ A).d q (q + 1)).hom b) := by
  apply relativeCochainComplexι_f_injective R Λ A (n + 1)
  simp [← HomologicalComplex.Hom.comm_apply, d_cup]

/-- **Associativity** of the relative cup product with respect to the absolute cup product:
`(a ⌣ b) ⌣ c = a ⌣ (b ⌣ c)` for cochains `a`, `b` of `X` and a relative cochain `c`. -/
theorem relativeCup_assoc {r m l : ℕ} (h₁ : p + q = m) (h₂ : m + r = n) (h₃ : q + r = l)
    (h₄ : p + l = n) (a : (cochainComplex R X Λ).X p) (b : (cochainComplex R X Λ).X q)
    (c : (relativeCochainComplex R Λ A).X r) :
    relativeCup R Λ A m r n h₂ (cup R X Λ p q m h₁ a b) c =
      relativeCup R Λ A p l n h₄ a (relativeCup R Λ A q r l h₃ b c) := by
  apply relativeCochainComplexι_f_injective R Λ A n
  simp [cup_assoc h₁ h₂ h₃ h₄]

/-- The unit cochain is a unit for the relative cup product. -/
@[simp]
theorem oneCochain_relativeCup (c : (relativeCochainComplex R Λ A).X q) :
    relativeCup R Λ A 0 q q (zero_add q) (oneCochain R X Λ) c = c := by
  apply relativeCochainComplexι_f_injective R Λ A q
  simp

/-- **Naturality** of the relative cup product under maps of pairs `f : (Y, B) → (X, A)`. -/
@[simp]
theorem relativeCochainComplexMap_f_relativeCup {Y : Type u} [TopologicalSpace Y] (B : Set Y)
    (f : C(Y, X)) (hf : Set.MapsTo f B A) (a : (cochainComplex R X Λ).X p)
    (b : (relativeCochainComplex R Λ A).X q) :
    ((relativeCochainComplexMap R Λ A B f hf).f n).hom (relativeCup R Λ A p q n h a b) =
      relativeCup R Λ B p q n h (((cochainComplexMap R Λ f).f p).hom a)
        (((relativeCochainComplexMap R Λ A B f hf).f q).hom b) := by
  have hι (k : ℕ) (c : (relativeCochainComplex R Λ A).X k) :
      ((relativeCochainComplexι R Λ B).f k).hom
          (((relativeCochainComplexMap R Λ A B f hf).f k).hom c) =
        ((cochainComplexMap R Λ f).f k).hom (((relativeCochainComplexι R Λ A).f k).hom c) := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
      ← HomologicalComplex.comp_f, relativeCochainComplexMap_comp_relativeCochainComplexι]
  apply relativeCochainComplexι_f_injective R Λ B n
  simp [hι]

end Cochain

section Cohomology

variable (R Λ) in
/-- The **relative cup product in Alexander–Spanier cohomology**
`Hᵖ(X; Λ) × H^q(X, A; Λ) → Hⁿ(X, A; Λ)`, for `p + q = n`: the class of the relative cup product of
representing cocycles (`relativeCohomologyCup_homologyπ`). -/
def relativeCohomologyCup (p q n : ℕ) (h : p + q = n) :
    cohomology R X Λ p →ₗ[R] relativeCohomology R Λ A q →ₗ[R] relativeCohomology R Λ A n :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂ (relativeCup R Λ A)
    (fun _ _ _ h a b ↦ d_relativeCup A h a b) p q n h

/-- The relative cup product of the classes of two cocycles is the class of their relative cup
product. -/
@[simp]
theorem relativeCohomologyCup_homologyπ {p q n : ℕ} (h : p + q = n)
    (a : (cochainComplex R X Λ).cycles p) (b : (relativeCochainComplex R Λ A).cycles q) :
    relativeCohomologyCup R Λ A p q n h (((cochainComplex R X Λ).homologyπ p).hom a)
        (((relativeCochainComplex R Λ A).homologyπ q).hom b) =
      ((relativeCochainComplex R Λ A).homologyπ n).hom
        (TauCeti.CochainComplex.moduleCatCyclesMap₂ (relativeCup R Λ A)
          (fun _ _ _ h a b ↦ d_relativeCup A h a b) p q n h a b) :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ _ _ p q n h a b

/-- The map `H^*(X, A; Λ) → H^*(X; Λ)` intertwines the relative and the absolute cup products:
`j (α ⌣ β) = α ⌣ j β`. -/
theorem relativeCohomologyMap_relativeCohomologyCup {p q n : ℕ} (h : p + q = n)
    (α : cohomology R X Λ p) (β : relativeCohomology R Λ A q) :
    (relativeCohomologyMap R Λ A n).hom (relativeCohomologyCup R Λ A p q n h α β) =
      cohomologyCup R X Λ p q n h α ((relativeCohomologyMap R Λ A q).hom β) := by
  have := TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂ _
    (fun _ _ _ h a b ↦ d_relativeCup A h a b) (cup R X Λ) (fun _ _ _ h a b ↦ d_cup h a b)
    (𝟙 _) (relativeCochainComplexι R Λ A) (relativeCochainComplexι R Λ A)
    (fun _ _ _ h a b ↦ relativeCochainComplexι_f_relativeCup A h a b) p q n h α β
  rwa [homologyMap_id, ModuleCat.hom_id, LinearMap.id_apply, ← cohomologyCup_def] at this

/-- **Associativity** of the relative cup product in cohomology with respect to the absolute cup
product: `(α ⌣ β) ⌣ γ = α ⌣ (β ⌣ γ)` for `α`, `β` in the cohomology of `X` and `γ` in the relative
cohomology of `(X, A)`. -/
theorem relativeCohomologyCup_assoc {p q r m l n : ℕ} (h₁ : p + q = m) (h₂ : m + r = n)
    (h₃ : q + r = l) (h₄ : p + l = n) (α : cohomology R X Λ p) (β : cohomology R X Λ q)
    (γ : relativeCohomology R Λ A r) :
    relativeCohomologyCup R Λ A m r n h₂ (cohomologyCup R X Λ p q m h₁ α β) γ =
      relativeCohomologyCup R Λ A p l n h₄ α (relativeCohomologyCup R Λ A q r l h₃ β γ) := by
  obtain ⟨a, rfl⟩ := (cochainComplex R X Λ).moduleCat_homologyπ_surjective p α
  obtain ⟨b, rfl⟩ := (cochainComplex R X Λ).moduleCat_homologyπ_surjective q β
  obtain ⟨c, rfl⟩ := (relativeCochainComplex R Λ A).moduleCat_homologyπ_surjective r γ
  simp only [cohomologyCup_homologyπ, relativeCohomologyCup_homologyπ]
  congr 1
  apply (relativeCochainComplex R Λ A).moduleCat_iCycles_injective
  simp [relativeCup_assoc A h₁ h₂ h₃ h₄]

/-- The unit class is a unit for the relative cup product in cohomology. -/
@[simp]
theorem cohomologyOne_relativeCohomologyCup {q : ℕ} (γ : relativeCohomology R Λ A q) :
    relativeCohomologyCup R Λ A 0 q q (zero_add q) (cohomologyOne R X Λ) γ = γ := by
  obtain ⟨c, rfl⟩ := (relativeCochainComplex R Λ A).moduleCat_homologyπ_surjective q γ
  rw [cohomologyOne_def, relativeCohomologyCup_homologyπ]
  congr 1
  apply (relativeCochainComplex R Λ A).moduleCat_iCycles_injective
  simp

/-- **Naturality** of the relative cup product in cohomology under maps of pairs
`f : (Y, B) → (X, A)`: `f^* (α ⌣ β) = f^* α ⌣ f^* β`. -/
theorem homologyMap_relativeCochainComplexMap_relativeCohomologyCup {Y : Type u}
    [TopologicalSpace Y] (B : Set Y) (f : C(Y, X)) (hf : Set.MapsTo f B A) {p q n : ℕ}
    (h : p + q = n) (α : cohomology R X Λ p) (β : relativeCohomology R Λ A q) :
    (homologyMap (relativeCochainComplexMap R Λ A B f hf) n).hom
        (relativeCohomologyCup R Λ A p q n h α β) =
      relativeCohomologyCup R Λ B p q n h ((cohomologyMap R Λ f p).hom α)
        ((homologyMap (relativeCochainComplexMap R Λ A B f hf) q).hom β) :=
  TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂ _ _ _
    (fun _ _ _ h a b ↦ d_relativeCup B h a b) _ _ _
    (fun _ _ _ h a b ↦ relativeCochainComplexMap_f_relativeCup A h B f hf a b) p q n h α β

end Cohomology

end TauCeti.AlexanderSpanier
