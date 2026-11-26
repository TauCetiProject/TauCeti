/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.Algebra.Homology.ModuleCat.Bilinear
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Cochain

/-!
# Cup products of cochains along a diagonal

Let `C` be a `k`-linear preadditive monoidal category, let `A`, `B` and `E` be chain complexes in
`C` indexed by `ℕ` such that the tensor product `A ⊗ B` exists, and let `D : E ⟶ A ⊗ B` be a chain
map, a *diagonal*.
Given a pairing `μ : M ⊗ N ⟶ P` of coefficient objects, a cochain `φ : A_p ⟶ M` and a cochain
`ψ : B_q ⟶ N` have the cup product `φ ⌣ ψ : E_n ⟶ P`, for `p + q = n`: the degree-`n` component
of `D`, followed by the projection of `(A ⊗ B)_n` onto its summand `A_p ⊗ B_q`, by `φ ⊗ ψ` and by
`μ`.  Since `D` is a chain map and the tensor product carries the Koszul signs, it satisfies the
Leibniz rule `(φ ⌣ ψ) ∘ d = (φ ∘ d) ⌣ ψ + (-1)^p φ ⌣ (ψ ∘ d)`.  When `C` is moreover abelian, a
cocycle cupped with a cocycle is a cocycle, a coboundary cupped with a cocycle (in either order)
is a coboundary, and the cup product descends to a `k`-bilinear map
`Hᵖ(Hom(A, M)) × H^q(Hom(B, N)) ⟶ Hⁿ(Hom(E, P))` on the cohomology of the complexes
`ChainComplex.linearYonedaObj`, an instance of the general product on cohomology
`TauCeti.CochainComplex.moduleCatHomologyMap₂`.  It is natural along maps of diagonals.

The singular cup product is the case where `D` is the Alexander–Whitney map precomposed with the
diagonal of a space; there `φ ⌣ ψ` evaluates a singular simplex on its front `p`-face and its back
`q`-face.

When the terms of `A` and `B` are projective, a short exact sequence of coefficients
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` gives a short exact sequence of cochain complexes `Hom(A, Mᵢ)` and a
connecting morphism `δ`, which for singular cochains is the Bockstein homomorphism. For two such
sequences and pairings `μ₁₃ : M₁ ⊗ N₃ ⟶ P` and `μ₃₁ : M₃ ⊗ N₁ ⟶ P` which both come from one
pairing `μ : M₂ ⊗ N₂ ⟶ P`, the Leibniz rule applied to lifts of two
cocycles to `M₂` and `N₂` gives `δ x ⌣ y = (-1)^(p + 1) • x ⌣ δ y`
(`TauCeti.ChainComplex.cup_δ_eq_zsmul`).

## Main definitions and results

* `TauCeti.ChainComplex.cupCochain`: the cup product of cochains.
* `TauCeti.ChainComplex.d_comp_cupCochain`: the Leibniz rule.
* `TauCeti.ChainComplex.cupCochain_naturality`: naturality along a map of diagonals.
* `TauCeti.ChainComplex.cupCochain_whiskerLeft_comp` and
  `TauCeti.ChainComplex.cupCochain_whiskerRight_comp`: changing the pairing along maps of
  coefficients.
* `TauCeti.ChainComplex.cupCycles`: the cup product of cocycles.
* `TauCeti.ChainComplex.cup`: the cup product on cohomology, with
  `TauCeti.ChainComplex.cup_homologyπ` computing it on classes of cocycles and
  `TauCeti.ChainComplex.cup_naturality` its naturality.
* `TauCeti.ChainComplex.cup_δ_eq_zsmul`: the cup product of a connecting morphism with a
  class, `δ x ⌣ y = (-1)^(p + 1) • x ⌣ δ y`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Lemma 3.6, and Section 3.E.
* A. Conway, S. Friedl and G. Herrmann, *Linking forms revisited*, Pure Appl. Math. Q. 12 (2016),
  Lemma 2.6.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C]

section Cochain

variable [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] {A B E : ChainComplex C ℕ}
  [A.HasTensor B] {M N P : C} {k : Type*} [CommSemiring k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B) (μ : M ⊗ N ⟶ P)

variable (k) in
/-- **The cup product of cochains** along the diagonal `D : E ⟶ A ⊗ B`: for `p + q = n`, the
`k`-bilinear map sending cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N` to the cochain
`E_n ⟶ (A ⊗ B)_n ⟶ P`, the component of `D` followed by the tensor product of cochains
`TauCeti.ChainComplex.tensorCochain`, which projects to `A_p ⊗ B_q` and applies `φ ⊗ ψ` and `μ`. -/
def cupCochain (p q n : ℕ) (_ : p + q = n) :
    (A.X p ⟶ M) →ₗ[k] (B.X q ⟶ N) →ₗ[k] (E.X n ⟶ P) :=
  LinearMap.mk₂ k (fun (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) ↦ D.f n ≫ tensorCochain μ φ ψ n)
    (fun φ φ' ψ ↦ by rw [tensorCochain_add_left, Preadditive.comp_add])
    (fun r φ ψ ↦ by rw [tensorCochain_smul_left, Linear.comp_smul])
    (fun φ ψ ψ' ↦ by rw [tensorCochain_add_right, Preadditive.comp_add])
    (fun r φ ψ ↦ by rw [tensorCochain_smul_right, Linear.comp_smul])

/-- The cup product of cochains is the component of the diagonal followed by the tensor product of
cochains. -/
@[simp]
lemma cupCochain_apply (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k D μ p q n h φ ψ = D.f n ≫ tensorCochain μ φ ψ n :=
  LinearMap.mk₂_apply ..

/-- **The Leibniz rule for the cup product**: `(φ ⌣ ψ) ∘ d = (φ ∘ d) ⌣ ψ + (-1)^p φ ⌣ (ψ ∘ d)`
for a cochain `φ` of degree `p`. -/
lemma d_comp_cupCochain (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    E.d (n + 1) n ≫ cupCochain k D μ p q n h φ ψ =
      cupCochain k D μ (p + 1) q (n + 1) (by omega) (A.d (p + 1) p ≫ φ) ψ +
        ((-1 : ℤ) ^ p) • cupCochain k D μ p (q + 1) (n + 1) (by omega) φ (B.d (q + 1) q ≫ ψ) := by
  rw [cupCochain_apply, cupCochain_apply, cupCochain_apply, ← D.comm_assoc,
    d_comp_tensorCochain, Preadditive.comp_add, Preadditive.comp_zsmul]

/-- **Naturality of the cup product of cochains** along a map of diagonals: if chain maps
`e : E' ⟶ E`, `f : A' ⟶ A` and `g : B' ⟶ B` satisfy `e ≫ D = D' ≫ (f ⊗ g)`, then cupping the
pulled-back cochains along `D'` is pulling back their cup product along `D`. -/
lemma cupCochain_naturality {A' B' E' : ChainComplex C ℕ} [A'.HasTensor B']
    (D' : E' ⟶ HomologicalComplex.tensorObj A' B') (e : E' ⟶ E) (f : A' ⟶ A) (g : B' ⟶ B)
    (hD : e ≫ D = D' ≫ HomologicalComplex.tensorHom f g) (p q n : ℕ) (h : p + q = n)
    (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k D' μ p q n h (f.f p ≫ φ) (g.f q ≫ ψ) = e.f n ≫ cupCochain k D μ p q n h φ ψ := by
  rw [cupCochain_apply, cupCochain_apply, ← tensorHom_f_comp_tensorCochain, ← Category.assoc,
    ← HomologicalComplex.comp_f, ← hD, HomologicalComplex.comp_f, Category.assoc]

/-- The cup product of cochains along the pairing `(M ◁ f) ≫ μ'` is the cup product along `μ'` with
the second cochain postcomposed with `f`. -/
lemma cupCochain_whiskerLeft_comp {N' : C} (f : N ⟶ N') (μ' : M ⊗ N' ⟶ P) (p q n : ℕ)
    (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k D ((M ◁ f) ≫ μ') p q n h φ ψ = cupCochain k D μ' p q n h φ (ψ ≫ f) := by
  rw [cupCochain_apply, cupCochain_apply, tensorCochain_whiskerLeft_comp]

/-- The cup product of cochains along the pairing `(f ▷ N) ≫ μ'` is the cup product along `μ'` with
the first cochain postcomposed with `f`. -/
lemma cupCochain_whiskerRight_comp {M' : C} (f : M ⟶ M') (μ' : M' ⊗ N ⟶ P) (p q n : ℕ)
    (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k D ((f ▷ N) ≫ μ') p q n h φ ψ = cupCochain k D μ' p q n h (φ ≫ f) ψ := by
  rw [cupCochain_apply, cupCochain_apply, tensorCochain_whiskerRight_comp]

end Cochain

section Cohomology

variable [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C] {A B E : ChainComplex C ℕ}
  [A.HasTensor B] {M N P : C} {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B) (μ : M ⊗ N ⟶ P)

variable (k) in
/-- The cup product of cochains `TauCeti.ChainComplex.cupCochain`, as a bilinear map of the
cochain modules of the complexes `Hom(-, -)`. -/
private def cupCochainHom (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).X p →ₗ[k] (B.linearYonedaObj k N).X q →ₗ[k]
      (E.linearYonedaObj k P).X n :=
  cupCochain k D μ p q n h

/-- The Leibniz rule `TauCeti.ChainComplex.d_comp_cupCochain` in the cochain modules of the
complexes `Hom(-, -)`, in the form required by `TauCeti.CochainComplex.moduleCatHomologyMap₂`. -/
private lemma d_cupCochainHom (p q n : ℕ) (h : p + q = n) (φ : (A.linearYonedaObj k M).X p)
    (ψ : (B.linearYonedaObj k N).X q) :
    ((E.linearYonedaObj k P).d n (n + 1)).hom (cupCochainHom k D μ p q n h φ ψ) =
      cupCochainHom k D μ (p + 1) q (n + 1) ((Nat.succ_add p q).trans (congrArg Nat.succ h))
          (((A.linearYonedaObj k M).d p (p + 1)).hom φ) ψ +
        (-1 : ℤ) ^ p • cupCochainHom k D μ p (q + 1) (n + 1)
          ((Nat.add_succ p q).trans (congrArg Nat.succ h)) φ
          (((B.linearYonedaObj k N).d q (q + 1)).hom ψ) := by
  simp only [cupCochainHom, linearYonedaObj_d_apply]
  exact d_comp_cupCochain D μ p q n h φ ψ

variable (k) in
/-- **The cup product of cocycles**: the cup product `TauCeti.ChainComplex.cupCochain` of the
underlying cochains, which is a cocycle by the Leibniz rule
(`TauCeti.ChainComplex.iCycles_cupCycles`). -/
def cupCycles (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).cycles p →ₗ[k] (B.linearYonedaObj k N).cycles q →ₗ[k]
      (E.linearYonedaObj k P).cycles n :=
  TauCeti.CochainComplex.moduleCatCyclesMap₂ (cupCochainHom k D μ) (d_cupCochainHom D μ) p q n h

/-- On underlying cochains, the cup product of cocycles is the cup product of cochains. -/
@[simp]
lemma iCycles_cupCycles (p q n : ℕ) (h : p + q = n) (a : (A.linearYonedaObj k M).cycles p)
    (b : (B.linearYonedaObj k N).cycles q) :
    (E.linearYonedaObj k P).iCycles n (cupCycles k D μ p q n h a b) =
      cupCochain k D μ p q n h ((A.linearYonedaObj k M).iCycles p a)
        ((B.linearYonedaObj k N).iCycles q b) :=
  TauCeti.CochainComplex.iCycles_moduleCatCyclesMap₂ _ _ p q n h a b

variable (k) in
/-- **The cup product on cohomology**, `Hᵖ(Hom(A, M)) × H^q(Hom(B, N)) ⟶ Hⁿ(Hom(E, P))` for
`p + q = n`, along the diagonal `D : E ⟶ A ⊗ B` and the pairing `μ : M ⊗ N ⟶ P`: the class of
`a ⌣ b` on the classes of cocycles `a` and `b` (`TauCeti.ChainComplex.cup_homologyπ`). It is the
product on cohomology `TauCeti.CochainComplex.moduleCatHomologyMap₂` of the cup product of
cochains. -/
def cup (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).homology p →ₗ[k] (B.linearYonedaObj k N).homology q →ₗ[k]
      (E.linearYonedaObj k P).homology n :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂ (cupCochainHom k D μ) (d_cupCochainHom D μ) p q n h

/-- **The cup product on classes**: the cup product of the classes of two cocycles is the class of
their cup product. -/
@[simp]
lemma cup_homologyπ (p q n : ℕ) (h : p + q = n) (a : (A.linearYonedaObj k M).cycles p)
    (b : (B.linearYonedaObj k N).cycles q) :
    cup k D μ p q n h ((A.linearYonedaObj k M).homologyπ p a)
        ((B.linearYonedaObj k N).homologyπ q b) =
      (E.linearYonedaObj k P).homologyπ n (cupCycles k D μ p q n h a b) :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ _ _ p q n h a b

/-- **Naturality of the cup product on cohomology** along a map of diagonals: if chain maps
`e : E' ⟶ E`, `f : A' ⟶ A` and `g : B' ⟶ B` satisfy `e ≫ D = D' ≫ (f ⊗ g)`, then the cup product
along `D'` of the pulled-back classes is the pull-back of the cup product along `D`. -/
lemma cup_naturality {A' B' E' : ChainComplex C ℕ} [A'.HasTensor B']
    (D' : E' ⟶ HomologicalComplex.tensorObj A' B') (e : E' ⟶ E) (f : A' ⟶ A) (g : B' ⟶ B)
    (hD : e ≫ D = D' ≫ HomologicalComplex.tensorHom f g) (p q n : ℕ) (h : p + q = n)
    (α : (A.linearYonedaObj k M).homology p) (β : (B.linearYonedaObj k N).homology q) :
    cup k D' μ p q n h
        (homologyMap (K := A.linearYonedaObj k M) (L := A'.linearYonedaObj k M)
          ((linearYonedaFunctor k M).map f.op) p α)
        (homologyMap (K := B.linearYonedaObj k N) (L := B'.linearYonedaObj k N)
          ((linearYonedaFunctor k N).map g.op) q β) =
      homologyMap (K := E.linearYonedaObj k P) (L := E'.linearYonedaObj k P)
        ((linearYonedaFunctor k P).map e.op) n (cup k D μ p q n h α β) :=
  (TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂ _ _ _ _ _ _ _
    (fun p q n h φ ψ ↦ by
      simp only [cupCochainHom]
      rw [linearYonedaFunctor_map_f_hom_apply, linearYonedaFunctor_map_f_hom_apply,
        linearYonedaFunctor_map_f_hom_apply]
      exact (cupCochain_naturality D μ D' e f g hD p q n h φ ψ).symm) p q n h α β).symm

/-- Precomposing a diagonal with a chain map pulls back its cup product on cohomology. -/
lemma cup_precomp {E' : ChainComplex C ℕ} (e : E' ⟶ E)
    (p q n : ℕ) (h : p + q = n)
    (a : (A.linearYonedaObj k M).homology p) (b : (B.linearYonedaObj k N).homology q) :
    cup k (e ≫ D) μ p q n h a b =
      homologyMap (K := E.linearYonedaObj k P) (L := E'.linearYonedaObj k P)
        ((linearYonedaFunctor k P).map e.op) n (cup k D μ p q n h a b) := by
  simpa using
    cup_naturality D μ (e ≫ D) e (𝟙 A) (𝟙 B)
      (by simp [HomologicalComplex.tensorHom, mapBifunctorMap]) p q n h a b

/-- Chain-homotopic diagonals give the same cup product on cohomology. -/
lemma cup_eq_of_homotopy {D' : E ⟶ HomologicalComplex.tensorObj A B}
    (H : Homotopy D D') (p q n : ℕ) (h : p + q = n)
    (a : (A.linearYonedaObj k M).homology p) (b : (B.linearYonedaObj k N).homology q) :
    cup k D μ p q n h a b = cup k D' μ p q n h a b := by
  have hD := cup_precomp (𝟙 (HomologicalComplex.tensorObj A B)) μ D p q n h a b
  have hD' := cup_precomp (𝟙 (HomologicalComplex.tensorObj A B)) μ D' p q n h a b
  simpa only [Category.comp_id] using hD.trans
    ((ConcreteCategory.congr_hom ((H.linearYonedaFunctorMap k P).homologyMap_eq n) _).trans
      hD'.symm)

end Cohomology

section Connecting

variable [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C] {A B E : ChainComplex C ℕ}
  [A.HasTensor B] [∀ i, Projective (A.X i)] [∀ i, Projective (B.X i)] {k : Type*} [CommRing k]
  [Linear k C] [MonoidalLinear k C] (D : E ⟶ HomologicalComplex.tensorObj A B)
  {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact) {P : C}
  (μ : S.X₂ ⊗ S'.X₂ ⟶ P) (μ₁₃ : S.X₁ ⊗ S'.X₃ ⟶ P) (μ₃₁ : S.X₃ ⊗ S'.X₁ ⟶ P)

/-- **Moving a connecting morphism across a cup product.** Let
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` and `0 ⟶ N₁ ⟶ N₂ ⟶ N₃ ⟶ 0` be short exact sequences of coefficients, with
connecting morphisms `δ` on the cohomology of `Hom(A, -)` and `Hom(B, -)`, whose terms are
projective. Let `μ : M₂ ⊗ N₂ ⟶ P` be a pairing whose restriction to `M₁ ⊗ N₂` factors through
`μ₁₃ : M₁ ⊗ N₃ ⟶ P` and whose restriction to `M₂ ⊗ N₁` factors through `μ₃₁ : M₃ ⊗ N₁ ⟶ P`.
Then for `x ∈ Hᵖ(Hom(A, M₃))` and `y ∈ H^q(Hom(B, N₃))`,

`δ x ⌣ y = (-1)^(p + 1) • x ⌣ δ y`   in `H^(p + q + 1)(Hom(E, P))`,

the cup products being taken along `D` with the pairings `μ₁₃` and `μ₃₁`. -/
theorem cup_δ_eq_zsmul (hμ₁₃ : (S.f ▷ S'.X₂) ≫ μ = (S.X₁ ◁ S'.g) ≫ μ₁₃)
    (hμ₃₁ : (S.X₂ ◁ S'.f) ≫ μ = (S.g ▷ S'.X₁) ≫ μ₃₁) (p q p' q' n : ℕ) (hp : p + 1 = p')
    (hq : q + 1 = q') (h₁ : p' + q = n) (h₂ : p + q' = n)
    (x : (A.linearYonedaObj k S.X₃).homology p) (y : (B.linearYonedaObj k S'.X₃).homology q) :
    cup k D μ₁₃ p' q n h₁ ((A.shortExact_map_linearYonedaObjFunctor k hS).δ p p' hp x) y =
      ((-1 : ℤ) ^ (p + 1)) •
        cup k D μ₃₁ p q' n h₂ x ((B.shortExact_map_linearYonedaObjFunctor k hS').δ q q' hq y) := by
  subst hp hq
  obtain rfl : n = p + q + 1 := by omega
  -- Represent `δ x` by a cocycle `α` and lift `x` to a cochain `φ` with coboundary `α` on the
  -- nose; likewise `δ y`, `β` and `ψ`.
  obtain ⟨α, hα⟩ := (A.linearYonedaObj k S.X₁).moduleCat_homologyπ_surjective (p + 1)
    ((A.shortExact_map_linearYonedaObjFunctor k hS).δ p (p + 1) rfl x)
  obtain ⟨φ, a, hφ, ha, rfl⟩ := exists_d_comp_eq_of_δ_eq k hS p (p + 1) rfl x α hα
  obtain ⟨β, hβ⟩ := (B.linearYonedaObj k S'.X₁).moduleCat_homologyπ_surjective (q + 1)
    ((B.shortExact_map_linearYonedaObjFunctor k hS').δ q (q + 1) rfl y)
  obtain ⟨ψ, b, hψ, hb, rfl⟩ := exists_d_comp_eq_of_δ_eq k hS' q (q + 1) rfl y β hβ
  -- The coboundary of `φ ⌣ ψ` is `α ⌣ b + (-1)ᵖ a ⌣ β`, by the Leibniz rule.
  have key : cupCycles k D μ₁₃ (p + 1) q (p + q + 1) h₁ α b +
      ((-1 : ℤ) ^ p) • cupCycles k D μ₃₁ p (q + 1) (p + q + 1) h₂ a β =
        (E.linearYonedaObj k P).toCycles (p + q) (p + q + 1)
          (cupCochain k D μ p q (p + q) rfl φ ψ) := by
    refine (E.linearYonedaObj k P).moduleCat_iCycles_injective (p + q + 1) ?_
    -- The underlying cochains of `α` and `β`, named to fix their types for the rewrites below.
    set iα : A.X (p + 1) ⟶ S.X₁ := (A.linearYonedaObj k S.X₁).iCycles (p + 1) α
    set iβ : B.X (q + 1) ⟶ S'.X₁ := (B.linearYonedaObj k S'.X₁).iCycles (q + 1) β
    rw [map_add, map_zsmul, iCycles_cupCycles, iCycles_cupCycles]
    refine Eq.trans ?_ (linearYonedaObj_iCycles_toCycles_apply (p + q) (p + q + 1) _).symm
    rw [d_comp_cupCochain, hφ, hψ, ← ha, ← hb,
      ← cupCochain_whiskerLeft_comp D S'.g μ₁₃ _ _ _ h₁ iα ψ,
      ← cupCochain_whiskerRight_comp D S.g μ₃₁ _ _ _ h₂ φ iβ, ← hμ₁₃, ← hμ₃₁,
      cupCochain_whiskerLeft_comp D S'.f μ _ _ _ h₂ φ iβ,
      cupCochain_whiskerRight_comp D S.f μ _ _ _ h₁ iα ψ]
    -- The two sides differ only in the proofs of the degree equations.
    rfl
  -- So the classes satisfy `[α ⌣ b] + (-1)ᵖ [a ⌣ β] = 0`.
  have hkey := congrArg ((E.linearYonedaObj k P).homologyπ (p + q + 1)) key
  rw [map_add, map_zsmul, linearYonedaObj_homologyπ_toCycles_apply (p + q) (p + q + 1)
    (cupCochain k D μ p q (p + q) rfl φ ψ)] at hkey
  rw [← hα, ← hβ, cup_homologyπ, cup_homologyπ, eq_neg_of_add_eq_zero_left hkey, pow_succ,
    mul_neg_one, neg_smul]

end Connecting

end TauCeti.ChainComplex
