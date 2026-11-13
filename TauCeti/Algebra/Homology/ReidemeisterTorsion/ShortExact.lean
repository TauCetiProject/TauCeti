/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Homology
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.HomologySequence
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.LinearMap.Range

/-!
# Milnor's multiplicativity formula for torsion with homology bases

Let `0 → C₁ → C₂ → C₃ → 0` be a short exact sequence of `ℤ`-graded chain complexes of vector
spaces over a field, with compatible ordered bases of the chains (the basis of `C₂ᵢ` is the image
of the basis of `C₁ᵢ` followed by lifts of the basis of `C₃ᵢ`) and arbitrary ordered bases `hₖ` of
the homology groups. The complexes need not be acyclic. Then

`τ(C₂, c₂, h₂) = ± τ(C₁, c₁, h₁) · τ(C₃, c₃, h₃) · τ(H)`

(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`), where `τ(Cₖ, cₖ, hₖ)`
is the torsion of a based complex with based homology
(`HomologicalComplex.reidemeisterTorsionWithHomology`) and `H` is the long exact homology sequence
`⋯ → Hᵢ(C₁) → Hᵢ(C₂) → Hᵢ(C₃) → Hᵢ₋₁(C₁) → ⋯`, an acyclic complex based by the homology bases
(`CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`). When `C₁` and `C₃` are
acyclic, `H` is zero and this is the multiplicativity of the torsion of acyclic complexes
`HomologicalComplex.reidemeisterTorsion_eq_mul_of_shortExact`, which there carries an explicit
sign; here the sign is not determined.

## Proof

Both sides are alternating products of brackets, for any choices of boundary bases, homology
representatives and lifts. In each degree the choices for `C₂` are assembled from those of `C₁`,
`C₃` and of the long exact sequence, following the filtrations `f(B₁) ⊆ f(C₁) ∩ B₂ ⊆ B₂` of the
boundaries (with quotients `im ∂` and `B₃`) and `im ∂ ⊆ H(C₁)`, `im f_* ⊆ H(C₂)`, `im g_* ⊆ H(C₃)`
of the homology; a basis of `im ∂` lifts through the differential of `C₂` by the description of
the connecting map. The bracket of `C₂` is then, up to sign, the product of the brackets of `C₁`
and `C₃` and of the determinants comparing the adapted homology bases with `h₁`, `h₂`, `h₃`, and
these are, up to sign, the brackets of the based long exact sequence.

## Main declarations

* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`: Milnor's formula.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorem 1.14.
-/

public section

noncomputable section

open CategoryTheory Module

variable {F : Type*} [Field F]

/-! ### Equality up to sign -/

/-- Two scalars are equal up to sign. -/
private def SignEq (a b : F) : Prop :=
  a = b ∨ a = -b

private theorem SignEq.refl (a : F) : SignEq a a := .inl rfl

private theorem SignEq.symm {a b : F} (h : SignEq a b) : SignEq b a := by
  rcases h with rfl | rfl <;> simp [SignEq]

private theorem SignEq.trans {a b c : F} (h : SignEq a b) (h' : SignEq b c) : SignEq a c := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;> simp [SignEq]

private theorem SignEq.mul {a b c d : F} (h : SignEq a b) (h' : SignEq c d) :
    SignEq (a * c) (b * d) := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;> simp [SignEq]

private theorem SignEq.inv {a b : F} (h : SignEq a b) : SignEq a⁻¹ b⁻¹ := by
  rcases h with rfl | rfl <;> simp [SignEq]

private theorem SignEq.zpow {a b : F} (h : SignEq a b) (k : ℤ) : SignEq (a ^ k) (b ^ k) := by
  rcases h with rfl | rfl <;> rcases Int.even_or_odd k with hk | hk <;> simp [SignEq, hk.neg_zpow]

/-- A product of finitely many factors that agree up to sign agrees up to sign. -/
private theorem SignEq.finprod {ι : Type*} {a b : ι → F} (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b) (h : ∀ i, SignEq (a i) (b i)) :
    SignEq (∏ᶠ i, a i) (∏ᶠ i, b i) := by
  classical
  have key (s : Finset ι) : SignEq (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
    induction s using Finset.induction_on with
    | empty => exact .refl _
    | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi]; exact (h i).mul ih
  rw [finprod_eq_prod_of_mulSupport_subset a (s := ha.toFinset ∪ hb.toFinset)
      fun x hx ↦ Finset.mem_coe.2 (Finset.mem_union_left _ ((Set.Finite.mem_toFinset ha).2 hx)),
    finprod_eq_prod_of_mulSupport_subset b (s := ha.toFinset ∪ hb.toFinset)
      fun x hx ↦ Finset.mem_coe.2 (Finset.mem_union_right _ ((Set.Finite.mem_toFinset hb).2 hx))]
  exact key _

/-- Reordering a family changes its determinant only by a sign. -/
private theorem Module.Basis.signEq_det_comp {ι κ M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module F M] (b : Basis ι F M) (v : κ → M) (e e' : ι ≃ κ) :
    SignEq (b.det (v ∘ e)) (b.det (v ∘ e')) := by
  have h := b.det.map_perm (v ∘ e') (e.trans e'.symm)
  have hv : v ∘ e' ∘ ⇑(e.trans e'.symm) = v ∘ e := by
    funext i
    simp
  rw [Function.comp_assoc, hv] at h
  rw [h]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e.trans e'.symm)) with hs | hs
  · exact .inl (by simp [hs])
  · exact .inr (by simp [hs])

/-- Regrouping a product over `ℤ` along the residues modulo `3`, starting at `2`. -/
private theorem finprod_eq_finprod_three {M : Type*} [CommMonoid M] (G : ℤ → M)
    (hG : Function.HasFiniteMulSupport G) :
    ∏ᶠ n, G n = ∏ᶠ j, G (3 * j + 2) * G (3 * (j + 1)) * G (3 * (j + 1) + 1) := by
  have hG' : Function.HasFiniteMulSupport fun p : ℤ × Fin 3 ↦ G (p.1 * 3 + p.2 + 2) :=
    Function.HasFiniteMulSupport.comp_of_injective (g := fun p : ℤ × Fin 3 ↦ p.1 * 3 + p.2 + 2)
      ((add_left_injective 2).comp (Int.divModEquiv 3).symm.injective) hG
  rw [← finprod_comp_equiv (Equiv.addRight (2 : ℤ)),
    ← finprod_comp_equiv (Int.divModEquiv 3).symm]
  simp only [Equiv.coe_addRight, Int.divModEquiv_symm_apply, Nat.cast_ofNat]
  rw [finprod_curry _ hG']
  refine finprod_congr fun j ↦ ?_
  rw [finprod_eq_prod_of_fintype, Fin.prod_univ_three]
  congr 2 <;> simp <;> ring_nf


/-- A bracket of a based acyclic complex, computed in another space: if a linear equivalence `ι`
sends the chain basis to a basis `hb` and the boundary basis and the lifts to families `u` and
`w`, up to reindexing, then the bracket is, up to sign, the determinant of `u` followed by `w`
with respect to `hb`, in any order. -/
private theorem HomologicalComplex.signEq_torsionBracket {C : ChainComplex (ModuleCat F) ℤ}
    {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) {j : ℤ} (hC : C.ExactAt (j + 1))
    {p q : ℕ} (b₁ : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom)) (s : Fin q → C.X (j + 1))
    (hs : ∀ k, (C.d (j + 1) j).hom (s k) = b₀ k) {H : Type*} [AddCommGroup H] [Module F H]
    (ι : C.X (j + 1) ≃ₗ[F] H) {m : ℕ} (hb : Basis (Fin m) F H) (σ : Fin (n (j + 1)) ≃ Fin m)
    (hσ : ∀ i, ι (c (j + 1) i) = hb (σ i)) {κ₁ κ₀ : Type*} (u : κ₁ → H) (w : κ₀ → H)
    (e₁ : Fin p ≃ κ₁) (e₀ : Fin q ≃ κ₀) (hu : ∀ i, ι (b₁ i) = u (e₁ i))
    (hw : ∀ i, ι (s i) = w (e₀ i)) (e : Fin m ≃ κ₁ ⊕ κ₀) :
    SignEq (HomologicalComplex.torsionBracket c (by simp) (by simp) hC b₁ b₀ s hs)
      (hb.det (Sum.elim u w ∘ e)) := by
  have hn := HomologicalComplex.eq_add_of_exactAt c (by simp) (by simp) hC b₁ b₀
  -- Transport the determinant along `ι`, which sends the basis `c (j + 1)` to `hb`.
  have hcb : hb = ((c (j + 1)).map ι).reindex σ :=
    Basis.eq_of_apply_eq fun i ↦ by simpa using (hσ (σ.symm i)).symm
  have hdet (v : Fin (n (j + 1)) → C.X (j + 1)) : (c (j + 1)).det v = hb.det (ι ∘ v ∘ σ.symm) := by
    rw [hcb, Basis.det_reindex, Basis.det_map]
    congr 1
    funext i
    simp
  rw [HomologicalComplex.torsionBracket_eq_det_append c _ _ hC b₁ b₀ s hs hn, hdet]
  have hv : ⇑ι ∘ (Fin.append (fun k ↦ (b₁ k : C.X (j + 1))) s ∘ Fin.cast hn) ∘ σ.symm =
      Sum.elim u w ∘ (σ.symm.trans
        ((finCongr hn).trans (finSumFinEquiv.symm.trans (Equiv.sumCongr e₁ e₀)))) := by
    funext i
    simp only [Function.comp_apply, Equiv.trans_apply, finCongr_apply]
    generalize Fin.cast hn (σ.symm i) = k
    induction k using Fin.addCases with
    | left k => simp [hu]
    | right k => simp [hw]
  rw [hv]
  exact hb.signEq_det_comp _ _ _


/-- The regrouping of the eight families making up the brackets of the outer terms of a short
exact sequence into the three blocks of the bracket of the middle term. -/
private def regroupEquiv (A₁ R₁ Φ Q₁ A₃ Γ R₀ Q₃ : Type*) :
    ((A₁ ⊕ (R₁ ⊕ Φ)) ⊕ Q₁) ⊕ ((A₃ ⊕ (Γ ⊕ R₀)) ⊕ Q₃) ≃
      (((A₁ ⊕ R₁) ⊕ A₃) ⊕ (Φ ⊕ Γ)) ⊕ ((Q₁ ⊕ R₀) ⊕ Q₃) where
  toFun
    | .inl (.inl (.inl a)) => .inl (.inl (.inl (.inl a)))
    | .inl (.inl (.inr (.inl r))) => .inl (.inl (.inl (.inr r)))
    | .inl (.inl (.inr (.inr x))) => .inl (.inr (.inl x))
    | .inl (.inr q) => .inr (.inl (.inl q))
    | .inr (.inl (.inl a)) => .inl (.inl (.inr a))
    | .inr (.inl (.inr (.inl x))) => .inl (.inr (.inr x))
    | .inr (.inl (.inr (.inr r))) => .inr (.inl (.inr r))
    | .inr (.inr q) => .inr (.inr q)
  invFun
    | .inl (.inl (.inl (.inl a))) => .inl (.inl (.inl a))
    | .inl (.inl (.inl (.inr r))) => .inl (.inl (.inr (.inl r)))
    | .inl (.inl (.inr a)) => .inr (.inl (.inl a))
    | .inl (.inr (.inl x)) => .inl (.inl (.inr (.inr x)))
    | .inl (.inr (.inr x)) => .inr (.inl (.inr (.inl x)))
    | .inr (.inl (.inl q)) => .inl (.inr q)
    | .inr (.inl (.inr r)) => .inr (.inl (.inr (.inr r)))
    | .inr (.inr q) => .inr (.inr q)
  left_inv := by rintro (((a | r | x) | q) | ((a | x | r) | q)) <;> rfl
  right_inv := by rintro ((((a | r) | a) | (x | x)) | ((q | r) | q)) <;> rfl

/-! ### The based long exact homology sequence -/

namespace CategoryTheory.ShortComplex.ShortExact

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)

/-- The term of the long exact sequence in degree `3k + 2` is `Hₖ(S.X₁)`. -/
private def lesIso₁ (n k : ℤ) (h : n = 3 * k + 2) :
    hS.homologySequenceComplex.X n ≅ S.X₁.homology k :=
  ChainComplex.interleave.XIso₁ _ _ _ n k h

/-- The term of the long exact sequence in degree `3k + 1` is `Hₖ(S.X₂)`. -/
private def lesIso₂ (n k : ℤ) (h : n = 3 * k + 1) :
    hS.homologySequenceComplex.X n ≅ S.X₂.homology k :=
  ChainComplex.interleave.XIso₂ _ _ _ n k h

/-- The term of the long exact sequence in degree `3k` is `Hₖ(S.X₃)`. -/
private def lesIso₃ (n k : ℤ) (h : n = 3 * k) :
    hS.homologySequenceComplex.X n ≅ S.X₃.homology k :=
  ChainComplex.interleave.XIso₃ _ _ _ n k h

private theorem lesIso₁_d (n k : ℤ) (h : n = 3 * k + 2)
    (x : hS.homologySequenceComplex.X (n + 1)) :
    (hS.lesIso₁ n k h).hom.hom ((hS.homologySequenceComplex.d (n + 1) n).hom x) =
      (hS.δ (k + 1) k rfl).hom ((hS.lesIso₃ (n + 1) (k + 1) (by omega)).hom.hom x) := by
  rw [lesIso₁, lesIso₃, ChainComplex.interleave_d_eq_of_eq_three_mul_add_two _ _ _ h]
  simp

private theorem lesIso₂_d (n k : ℤ) (h : n = 3 * k + 1)
    (x : hS.homologySequenceComplex.X (n + 1)) :
    (hS.lesIso₂ n k h).hom.hom ((hS.homologySequenceComplex.d (n + 1) n).hom x) =
      (HomologicalComplex.homologyMap S.f k).hom
        ((hS.lesIso₁ (n + 1) k (by omega)).hom.hom x) := by
  rw [lesIso₁, lesIso₂, ChainComplex.interleave_d_eq_of_eq_three_mul_add_one _ _ _ h]
  simp

private theorem lesIso₃_d (n k : ℤ) (h : n = 3 * k)
    (x : hS.homologySequenceComplex.X (n + 1)) :
    (hS.lesIso₃ n k h).hom.hom ((hS.homologySequenceComplex.d (n + 1) n).hom x) =
      (HomologicalComplex.homologyMap S.g k).hom
        ((hS.lesIso₂ (n + 1) k (by omega)).hom.hom x) := by
  rw [lesIso₂, lesIso₃, ChainComplex.interleave_d_eq_of_eq_three_mul _ _ _ h]
  simp

variable {m₁ m₂ m₃ : ℤ → ℕ} (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
  (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))

/-- The basis of the long exact homology sequence given by the homology bases. -/
private abbrev lesBasis :
    ∀ n, Basis (Fin (ChainComplex.interleave.rank m₁ m₂ m₃ n)) F (hS.homologySequenceComplex.X n) :=
  ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃



/-- The index types of the bases `lesρ k`, `lesφ k` and `lesγ k` below. -/
private abbrev Idxρ (k : ℤ) : Type :=
  Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (3 * k + 2 + 1) (3 * k + 2)).hom))

private abbrev Idxφ (k : ℤ) : Type :=
  Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (3 * k + 1 + 1) (3 * k + 1)).hom))

private abbrev Idxγ (k : ℤ) : Type :=
  Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (3 * k + 1) (3 * k)).hom))

/-! The images of the maps of the long exact sequence, with bases and lifts read off the chosen
boundary bases and lifts of the based long exact sequence. -/

/-- The chosen boundary bases and lifts of the based long exact sequence. -/
private abbrev lesBoundaryBasis (n : ℤ) :=
  HomologicalComplex.chosenBoundaryBasis hS.homologySequenceComplex (hS.lesBasis h₁ h₂ h₃) (n + 1) n

private abbrev lesBoundaryLift (n : ℤ) :=
  HomologicalComplex.chosenBoundaryLift hS.homologySequenceComplex (hS.lesBasis h₁ h₂ h₃) (n + 1) n

/-- A basis of the image of the connecting map `Hₖ₊₁(S.X₃) → Hₖ(S.X₁)`. -/
private def lesρ (k : ℤ) :
    Basis (Fin (finrank F (LinearMap.range
      (hS.homologySequenceComplex.d (3 * k + 2 + 1) (3 * k + 2)).hom))) F
      (LinearMap.range (hS.δ (k + 1) k rfl).hom) :=
  (hS.lesBoundaryBasis h₁ h₂ h₃ (3 * k + 2)).map
    ((hS.lesIso₁ (3 * k + 2) k rfl).toLinearEquiv.ofSubmodules _ _
      (LinearMap.map_range_eq_range_of_comp_eq _
        (e₁ := (hS.lesIso₃ (3 * k + 2 + 1) (k + 1) (by ring)).toLinearEquiv.toLinearMap)
        (LinearEquiv.surjective _) (LinearMap.ext fun x ↦ (hS.lesIso₁_d _ _ rfl x).symm)))

/-- Lifts through the connecting map `Hₖ₊₁(S.X₃) → Hₖ(S.X₁)` of the basis `lesρ`. -/
private def lesγ' (k : ℤ) :
    Fin (finrank F (LinearMap.range
      (hS.homologySequenceComplex.d (3 * k + 2 + 1) (3 * k + 2)).hom)) →
      S.X₃.homology (k + 1) :=
  fun i ↦ (hS.lesIso₃ (3 * k + 2 + 1) (k + 1) (by ring)).hom.hom
    (hS.lesBoundaryLift h₁ h₂ h₃ (3 * k + 2) i)

private theorem δ_lesγ' (k : ℤ) (i) :
    (hS.δ (k + 1) k rfl).hom (hS.lesγ' h₁ h₂ h₃ k i) = hS.lesρ h₁ h₂ h₃ k i := by
  rw [lesγ', ← hS.lesIso₁_d _ _ rfl, HomologicalComplex.chosenBoundaryLift_spec]
  rfl

/-- A basis of the image of `Hₖ(S.X₁) → Hₖ(S.X₂)`. -/
private def lesφ (k : ℤ) :
    Basis (Fin (finrank F (LinearMap.range
      (hS.homologySequenceComplex.d (3 * k + 1 + 1) (3 * k + 1)).hom))) F
      (LinearMap.range (HomologicalComplex.homologyMap S.f k).hom) :=
  (hS.lesBoundaryBasis h₁ h₂ h₃ (3 * k + 1)).map
    ((hS.lesIso₂ (3 * k + 1) k rfl).toLinearEquiv.ofSubmodules _ _
      (LinearMap.map_range_eq_range_of_comp_eq _
        (e₁ := (hS.lesIso₁ (3 * k + 1 + 1) k (by ring)).toLinearEquiv.toLinearMap)
        (LinearEquiv.surjective _) (LinearMap.ext fun x ↦ (hS.lesIso₂_d _ _ rfl x).symm)))

/-- Lifts through `Hₖ(S.X₁) → Hₖ(S.X₂)` of the basis `lesφ`. -/
private def lesψ (k : ℤ) :
    Fin (finrank F (LinearMap.range
      (hS.homologySequenceComplex.d (3 * k + 1 + 1) (3 * k + 1)).hom)) → S.X₁.homology k :=
  fun i ↦ (hS.lesIso₁ (3 * k + 1 + 1) k (by ring)).hom.hom
    (hS.lesBoundaryLift h₁ h₂ h₃ (3 * k + 1) i)

private theorem homologyMap_lesψ (k : ℤ) (i) :
    (HomologicalComplex.homologyMap S.f k).hom (hS.lesψ h₁ h₂ h₃ k i) = hS.lesφ h₁ h₂ h₃ k i := by
  rw [lesψ, ← hS.lesIso₂_d _ _ rfl, HomologicalComplex.chosenBoundaryLift_spec]
  rfl

/-- A basis of the image of `Hₖ(S.X₂) → Hₖ(S.X₃)`. -/
private def lesγ (k : ℤ) :
    Basis (Fin (finrank F (LinearMap.range
      (hS.homologySequenceComplex.d (3 * k + 1) (3 * k)).hom))) F
      (LinearMap.range (HomologicalComplex.homologyMap S.g k).hom) :=
  (hS.lesBoundaryBasis h₁ h₂ h₃ (3 * k)).map
    ((hS.lesIso₃ (3 * k) k rfl).toLinearEquiv.ofSubmodules _ _
      (LinearMap.map_range_eq_range_of_comp_eq _
        (e₁ := (hS.lesIso₂ (3 * k + 1) k rfl).toLinearEquiv.toLinearMap)
        (LinearEquiv.surjective _) (LinearMap.ext fun x ↦ (hS.lesIso₃_d _ _ rfl x).symm)))

/-- Lifts through `Hₖ(S.X₂) → Hₖ(S.X₃)` of the basis `lesγ`. -/
private def lesσ (k : ℤ) :
    Fin (finrank F (LinearMap.range
      (hS.homologySequenceComplex.d (3 * k + 1) (3 * k)).hom)) → S.X₂.homology k :=
  fun i ↦ (hS.lesIso₂ (3 * k + 1) k rfl).hom.hom (hS.lesBoundaryLift h₁ h₂ h₃ (3 * k) i)

private theorem homologyMap_lesσ (k : ℤ) (i) :
    (HomologicalComplex.homologyMap S.g k).hom (hS.lesσ h₁ h₂ h₃ k i) = hS.lesγ h₁ h₂ h₃ k i := by
  rw [lesσ, ← hS.lesIso₃_d _ _ rfl, HomologicalComplex.chosenBoundaryLift_spec]
  rfl

/-- The chosen boundary basis in a degree `n = 3k + 2` is `lesρ`, up to reindexing. -/
private theorem exists_lesIso₁_lesBoundaryBasis (k n : ℤ) (hn : n = 3 * k + 2) :
    ∃ e : Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (n + 1) n).hom)) ≃
        Fin (finrank F (LinearMap.range
          (hS.homologySequenceComplex.d (3 * k + 2 + 1) (3 * k + 2)).hom)),
      ∀ i, (hS.lesIso₁ n k hn).hom.hom (hS.lesBoundaryBasis h₁ h₂ h₃ n i) =
        hS.lesρ h₁ h₂ h₃ k (e i) := by
  subst hn
  exact ⟨Equiv.refl _, fun i ↦ rfl⟩

/-- The chosen boundary basis in a degree `n = 3k` is `lesγ`, up to reindexing. -/
private theorem exists_lesIso₃_lesBoundaryBasis (k n : ℤ) (hn : n = 3 * k) :
    ∃ e : Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (n + 1) n).hom)) ≃
        Fin (finrank F (LinearMap.range
          (hS.homologySequenceComplex.d (3 * k + 1) (3 * k)).hom)),
      ∀ i, (hS.lesIso₃ n k hn).hom.hom (hS.lesBoundaryBasis h₁ h₂ h₃ n i) =
        hS.lesγ h₁ h₂ h₃ k (e i) := by
  subst hn
  exact ⟨Equiv.refl _, fun i ↦ rfl⟩

/-- The bracket of the based long exact sequence in degree `n + 1`, for the chosen boundary bases
and lifts. -/
private abbrev lesBracket (n : ℤ) : F :=
  HomologicalComplex.torsionBracket (hS.lesBasis h₁ h₂ h₃) (by simp) (by simp)
    (hS.acyclic_homologySequenceComplex (n + 1)) (hS.lesBoundaryBasis h₁ h₂ h₃ (n + 1))
    (hS.lesBoundaryBasis h₁ h₂ h₃ n) (hS.lesBoundaryLift h₁ h₂ h₃ n)
    (HomologicalComplex.chosenBoundaryLift_spec _ _ (n + 1) n)

/-- The bracket at `Hₖ(S.X₁)` is up to sign the determinant of `lesρ` followed by `lesψ`. -/
private theorem signEq_lesBracket_one (k : ℤ) {κ₁ κ₀ : Type*} (u : κ₁ → S.X₁.homology k)
    (w : κ₀ → S.X₁.homology k) (e₁ : _ ≃ κ₁) (e₀ : _ ≃ κ₀)
    (hu : ∀ i, (hS.lesρ h₁ h₂ h₃ k i : S.X₁.homology k) = u (e₁ i))
    (hw : ∀ i, hS.lesψ h₁ h₂ h₃ k i = w (e₀ i)) (e : Fin (m₁ k) ≃ κ₁ ⊕ κ₀) :
    SignEq (hS.lesBracket h₁ h₂ h₃ (3 * k + 1)) ((h₁ k).det (Sum.elim u w ∘ e)) := by
  obtain ⟨e', he'⟩ := hS.exists_lesIso₁_lesBoundaryBasis h₁ h₂ h₃ k (3 * k + 1 + 1) (by ring)
  exact HomologicalComplex.signEq_torsionBracket _ _ _ _ _ _
    (hS.lesIso₁ (3 * k + 1 + 1) k (by ring)).toLinearEquiv (h₁ k)
    (finCongr (ChainComplex.interleave.rank_of_eq_three_mul_add_two (by ring)))
    (fun i ↦ ChainComplex.interleave.XIso₁_hom_basis _ _ _ h₁ h₂ h₃ _ i) u w (e'.trans e₁) e₀
    (fun i ↦ (he' i).trans (hu _)) (fun i ↦ hw i) e

/-- The bracket at `Hₖ(S.X₂)` is up to sign the determinant of `lesφ` followed by `lesσ`. -/
private theorem signEq_lesBracket_two (k : ℤ) {κ₁ κ₀ : Type*} (u : κ₁ → S.X₂.homology k)
    (w : κ₀ → S.X₂.homology k) (e₁ : _ ≃ κ₁) (e₀ : _ ≃ κ₀)
    (hu : ∀ i, (hS.lesφ h₁ h₂ h₃ k i : S.X₂.homology k) = u (e₁ i))
    (hw : ∀ i, hS.lesσ h₁ h₂ h₃ k i = w (e₀ i)) (e : Fin (m₂ k) ≃ κ₁ ⊕ κ₀) :
    SignEq (hS.lesBracket h₁ h₂ h₃ (3 * k)) ((h₂ k).det (Sum.elim u w ∘ e)) :=
  HomologicalComplex.signEq_torsionBracket _ _ _ _ _ _
    (hS.lesIso₂ (3 * k + 1) k rfl).toLinearEquiv (h₂ k)
    (finCongr (ChainComplex.interleave.rank_of_eq_three_mul_add_one rfl))
    (fun i ↦ ChainComplex.interleave.XIso₂_hom_basis _ _ _ h₁ h₂ h₃ _ i) u w e₁ e₀
    (fun i ↦ hu i) (fun i ↦ hw i) e

/-- The bracket at `Hₖ₊₁(S.X₃)`, in degree `3k + 3`, is up to sign the determinant of
`lesγ (k + 1)` followed by `lesγ' k`. -/
private theorem signEq_lesBracket_three (k : ℤ) {κ₁ κ₀ : Type*}
    (u : κ₁ → S.X₃.homology (k + 1)) (w : κ₀ → S.X₃.homology (k + 1)) (e₁ : _ ≃ κ₁)
    (e₀ : _ ≃ κ₀)
    (hu : ∀ i, (hS.lesγ h₁ h₂ h₃ (k + 1) i : S.X₃.homology (k + 1)) = u (e₁ i))
    (hw : ∀ i, hS.lesγ' h₁ h₂ h₃ k i = w (e₀ i)) (e : Fin (m₃ (k + 1)) ≃ κ₁ ⊕ κ₀) :
    SignEq (hS.lesBracket h₁ h₂ h₃ (3 * k + 2)) ((h₃ (k + 1)).det (Sum.elim u w ∘ e)) := by
  obtain ⟨e', he'⟩ :=
    hS.exists_lesIso₃_lesBoundaryBasis h₁ h₂ h₃ (k + 1) (3 * k + 2 + 1) (by ring)
  exact HomologicalComplex.signEq_torsionBracket _ _ _ _ _ _
    (hS.lesIso₃ (3 * k + 2 + 1) (k + 1) (by ring)).toLinearEquiv (h₃ (k + 1))
    (finCongr (ChainComplex.interleave.rank_of_eq_three_mul (by ring)))
    (fun i ↦ ChainComplex.interleave.XIso₃_hom_basis _ _ _ h₁ h₂ h₃ _ i) u w (e'.trans e₁) e₀
    (fun i ↦ (he' i).trans (hu _)) (fun i ↦ hw i) e


/-! ### Adapted choices in the middle term -/

section Middle

variable {n₁ n₃ : ℤ → ℕ} (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
  (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))

include hS in
private theorem injective_f_f (i : ℤ) : Function.Injective (S.f.f i).hom :=
  ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i).moduleCat_injective_f

include hS in
private theorem exact_f_f_g_f (i : ℤ) : Function.Exact (S.f.f i).hom (S.g.f i).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i).exact

include hS in
private theorem surjective_g_f (i : ℤ) : Function.Surjective (S.g.f i).hom :=
  ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i).moduleCat_surjective_g

/-- Cycles of `S.X₁` representing the basis `lesρ` of the image of the connecting map. -/
private def cycρ (k : ℤ) (i : hS.Idxρ k) : S.X₁.cycles k :=
  Function.surjInv (S.X₁.moduleCat_homologyπ_surjective k) (hS.lesρ h₁ h₂ h₃ k i)

private theorem homologyπ_cycρ (k : ℤ) (i : hS.Idxρ k) :
    S.X₁.homologyπ k (hS.cycρ h₁ h₂ h₃ k i) = hS.lesρ h₁ h₂ h₃ k i :=
  Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective k) _

/-- Cycles of `S.X₁` representing the lifts `lesψ`. -/
private def cycψ (k : ℤ) (i : hS.Idxφ k) : S.X₁.cycles k :=
  Function.surjInv (S.X₁.moduleCat_homologyπ_surjective k) (hS.lesψ h₁ h₂ h₃ k i)

private theorem homologyπ_cycψ (k : ℤ) (i : hS.Idxφ k) :
    S.X₁.homologyπ k (hS.cycψ h₁ h₂ h₃ k i) = hS.lesψ h₁ h₂ h₃ k i :=
  Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective k) _

/-- Cycles of `S.X₂` representing the lifts `lesσ`. -/
private def cycσ (k : ℤ) (i : hS.Idxγ k) : S.X₂.cycles k :=
  Function.surjInv (S.X₂.moduleCat_homologyπ_surjective k) (hS.lesσ h₁ h₂ h₃ k i)

private theorem homologyπ_cycσ (k : ℤ) (i : hS.Idxγ k) :
    S.X₂.homologyπ k (hS.cycσ h₁ h₂ h₃ k i) = hS.lesσ h₁ h₂ h₃ k i :=
  Function.surjInv_eq (S.X₂.moduleCat_homologyπ_surjective k) _

/-- The class `lesγ' k i` lifts to an element of `S.X₂` whose boundary is the image of the cycle
`cycρ k i` representing its image under the connecting map. -/
private theorem exists_liftδ (k : ℤ) (i : hS.Idxρ k) :
    ∃ (x₂ : S.X₂.X (k + 1)) (z₃ : S.X₃.cycles (k + 1)),
      (S.X₂.d (k + 1) k).hom x₂ = (S.f.f k).hom ((S.X₁.iCycles k).hom (hS.cycρ h₁ h₂ h₃ k i)) ∧
        (S.g.f (k + 1)).hom x₂ = (S.X₃.iCycles (k + 1)).hom z₃ ∧
          (S.X₃.homologyπ (k + 1)).hom z₃ = hS.lesγ' h₁ h₂ h₃ k i :=
  hS.moduleCat_exists_d_eq_of_δ_eq (k + 1) k rfl _ _ <| by
    rw [δ_lesγ', ← homologyπ_cycρ]

/-- The lift of `lesγ' k i` to `S.X₂`. -/
private def liftδ (k : ℤ) (i : hS.Idxρ k) : S.X₂.X (k + 1) :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose

/-- The cycle of `S.X₃` represented by the image of `liftδ k i`. -/
private def cycγ' (k : ℤ) (i : hS.Idxρ k) : S.X₃.cycles (k + 1) :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose_spec.choose

private theorem d_liftδ (k : ℤ) (i : hS.Idxρ k) :
    (S.X₂.d (k + 1) k).hom (hS.liftδ h₁ h₂ h₃ k i) =
      (S.f.f k).hom ((S.X₁.iCycles k).hom (hS.cycρ h₁ h₂ h₃ k i)) :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose_spec.choose_spec.1

private theorem g_liftδ (k : ℤ) (i : hS.Idxρ k) :
    (S.g.f (k + 1)).hom (hS.liftδ h₁ h₂ h₃ k i) =
      (S.X₃.iCycles (k + 1)).hom (hS.cycγ' h₁ h₂ h₃ k i) :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose_spec.choose_spec.2.1

private theorem homologyπ_cycγ' (k : ℤ) (i : hS.Idxρ k) :
    S.X₃.homologyπ (k + 1) (hS.cycγ' h₁ h₂ h₃ k i) = hS.lesγ' h₁ h₂ h₃ k i :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose_spec.choose_spec.2.2

/-- The elements of `S.X₁` in degree `k` whose image in `S.X₂` is a boundary. -/
private def boundaryPreimage (k : ℤ) : Submodule F (S.X₁.X k) :=
  (LinearMap.range (S.X₂.d (k + 1) k).hom).comap (S.f.f k).hom

private theorem range_le_boundaryPreimage (k : ℤ) :
    LinearMap.range (S.X₁.d (k + 1) k).hom ≤ boundaryPreimage (S := S) k := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(S.f.f (k + 1)).hom y, HomologicalComplex.Hom.comm_apply S.f _ _ y⟩

include hS in
private theorem boundaryPreimage_le_ker (k : ℤ) :
    boundaryPreimage (S := S) k ≤ LinearMap.ker (S.X₁.d k (k - 1)).hom := by
  rintro w ⟨y, hy⟩
  rw [LinearMap.mem_ker]
  apply injective_f_f hS (k - 1)
  rw [map_zero, ← HomologicalComplex.Hom.comm_apply, ← hy]
  exact S.X₂.d_comp_d_apply _ _ _ y

/-- The homology class of an element of the kernel of the outgoing differential is the class of
the cycle it comes from. -/
private theorem moduleCatKerHomologyClass_eq {C : ChainComplex (ModuleCat F) ℤ} {k m : ℤ}
    (hm : (ComplexShape.down ℤ).next k = m) (z : C.cycles k)
    (x : LinearMap.ker (C.d k m).hom) (hx : (x : C.X k) = (C.iCycles k).hom z) :
    C.moduleCatKerHomologyClass hm x = C.homologyπ k z := by
  rw [← C.moduleCatKerHomologyClass_moduleCatCyclesToKer hm z]
  congr 1
  exact Subtype.ext (hx.trans (C.coe_moduleCatCyclesToKer k m z).symm)

/-- The homology class of an element of `boundaryPreimage k`, a class in the image of the
connecting map. -/
private def boundaryPreimageClass (k : ℤ) :
    boundaryPreimage (S := S) k →ₗ[F] LinearMap.range (hS.δ (k + 1) k rfl).hom :=
  LinearMap.codRestrict _ (S.X₁.moduleCatKerHomologyClass (ChainComplex.next ℤ k) ∘ₗ
    Submodule.inclusion (boundaryPreimage_le_ker hS k)) fun w ↦ by
    obtain ⟨y, hy⟩ := w.2
    obtain ⟨z, hz⟩ : ∃ z : S.X₁.cycles k, (S.X₁.iCycles k).hom z = w :=
      ⟨_, S.X₁.iCycles_moduleCatCyclesMk k _ _ (ChainComplex.next ℤ k)
        (boundaryPreimage_le_ker hS k w.2)⟩
    -- The image of `y` in `S.X₃` is a cycle, whose class is sent by the connecting map to the
    -- class of `w`.
    obtain ⟨z₃, hz₃⟩ : ∃ z₃ : S.X₃.cycles (k + 1), (S.X₃.iCycles (k + 1)).hom z₃ =
        (S.g.f (k + 1)).hom y := ⟨_, S.X₃.iCycles_moduleCatCyclesMk (k + 1) _ k
          ((ComplexShape.down ℤ).next_eq' rfl) (by
            rw [HomologicalComplex.Hom.comm_apply, hy]
            exact (exact_f_f_g_f hS k).apply_apply_eq_zero _)⟩
    refine ⟨(S.X₃.homologyπ (k + 1)).hom z₃, ?_⟩
    rw [hS.moduleCat_δ_homologyπ (k + 1) k rfl z₃ y hz₃.symm z (by rw [hz, hy]),
      LinearMap.comp_apply, moduleCatKerHomologyClass_eq _ z _ hz.symm]

private theorem coe_boundaryPreimageClass_mk (k : ℤ) (z : S.X₁.cycles k)
    (hz : (S.X₁.iCycles k).hom z ∈ boundaryPreimage (S := S) k) :
    (hS.boundaryPreimageClass k ⟨_, hz⟩ : S.X₁.homology k) = S.X₁.homologyπ k z := by
  rw [boundaryPreimageClass, LinearMap.codRestrict_apply, LinearMap.comp_apply]
  exact moduleCatKerHomologyClass_eq _ z _ rfl

private theorem exact_inclusion_boundaryPreimageClass (k : ℤ) :
    Function.Exact (Submodule.inclusion (range_le_boundaryPreimage (S := S) k))
      (hS.boundaryPreimageClass k) := by
  intro w
  have key := S.X₁.exact_inclusion_moduleCatKerHomologyClass (ChainComplex.next ℤ k)
    (ChainComplex.prev ℤ k) (Submodule.inclusion (boundaryPreimage_le_ker hS k) w)
  constructor
  · intro hw
    obtain ⟨a, ha⟩ := key.1 (congrArg Subtype.val hw)
    have ha' := congrArg Subtype.val ha
    exact ⟨a, Subtype.ext ha'⟩
  · rintro ⟨a, rfl⟩
    exact Subtype.ext (key.2 ⟨a, rfl⟩)

/-- The inclusion of `boundaryPreimage k` into the boundaries of `S.X₂` through `S.f`. -/
private def boundaryPreimageMap (k : ℤ) :
    boundaryPreimage (S := S) k →ₗ[F] LinearMap.range (S.X₂.d (k + 1) k).hom :=
  LinearMap.codRestrict _ ((S.f.f k).hom ∘ₗ (boundaryPreimage (S := S) k).subtype) fun w ↦ w.2

private theorem coe_boundaryPreimageMap (k : ℤ) (w : boundaryPreimage (S := S) k) :
    (boundaryPreimageMap k w : S.X₂.X k) = (S.f.f k).hom w :=
  (rfl)

include hS in
private theorem injective_boundaryPreimageMap (k : ℤ) :
    Function.Injective (boundaryPreimageMap (S := S) k) := fun _ _ h ↦
  Subtype.ext (injective_f_f hS k (congrArg Subtype.val h))

include hS in
private theorem exact_boundaryPreimageMap (k : ℤ) :
    Function.Exact (boundaryPreimageMap (S := S) k) (S.g.boundaryMap (k + 1) k) := by
  rintro ⟨y, hy⟩
  constructor
  · intro h
    have h' : (S.g.f k).hom y = 0 := by simpa using congrArg Subtype.val h
    obtain ⟨w, hw⟩ := (exact_f_f_g_f hS k y).1 h'
    refine ⟨⟨w, show (S.f.f k).hom w ∈ _ by rw [hw]; exact hy⟩, Subtype.ext hw⟩
  · rintro ⟨w, h⟩
    rw [← h]
    apply Subtype.ext
    simpa [coe_boundaryPreimageMap] using (exact_f_f_g_f hS k).apply_apply_eq_zero (w : S.X₁.X k)

/-- The chosen boundary bases and lifts of `S.X₁` and `S.X₃`. -/
private abbrev boundaryBasis₁ (k : ℤ) := HomologicalComplex.chosenBoundaryBasis S.X₁ c₁ (k + 1) k

private abbrev boundaryLift₁ (k : ℤ) := HomologicalComplex.chosenBoundaryLift S.X₁ c₁ (k + 1) k

private abbrev boundaryBasis₃ (k : ℤ) := HomologicalComplex.chosenBoundaryBasis S.X₃ c₃ (k + 1) k

private abbrev boundaryLift₃ (k : ℤ) := HomologicalComplex.chosenBoundaryLift S.X₃ c₃ (k + 1) k

/-- Lifts to `S.X₂` of the lifts of the boundary basis of `S.X₃`. -/
private def liftLift₃ (k : ℤ) (i : Fin (finrank F (LinearMap.range (S.X₃.d (k + 1) k).hom))) :
    S.X₂.X (k + 1) :=
  Function.surjInv (surjective_g_f hS (k + 1)) (boundaryLift₃ c₃ k i)

private theorem g_liftLift₃ (k : ℤ) (i : Fin (finrank F (LinearMap.range (S.X₃.d (k + 1) k).hom))) :
    (S.g.f (k + 1)).hom (hS.liftLift₃ c₃ k i) = boundaryLift₃ c₃ k i :=
  Function.surjInv_eq (surjective_g_f hS (k + 1)) _

/-- The basis of the boundaries of `S.X₂` in degree `k` made of the images of the boundary basis
of `S.X₁`, the images of the cycles `cycρ k`, and the boundaries of the lifts `liftLift₃ k`. -/
private def boundaryBasis₂ (k : ℤ) :
    Basis ((Fin (finrank F (LinearMap.range (S.X₁.d (k + 1) k).hom)) ⊕ hS.Idxρ k) ⊕
      Fin (finrank F (LinearMap.range (S.X₃.d (k + 1) k).hom))) F
      (LinearMap.range (S.X₂.d (k + 1) k).hom) :=
  Basis.ofExactLift (injective_boundaryPreimageMap hS k) (exact_boundaryPreimageMap hS k)
    (Basis.ofExactLift (Submodule.inclusion_injective _)
      (hS.exact_inclusion_boundaryPreimageClass k) (boundaryBasis₁ c₁ k) (hS.lesρ h₁ h₂ h₃ k)
      (fun i ↦ ⟨(S.X₁.iCycles k).hom (hS.cycρ h₁ h₂ h₃ k i),
        ⟨hS.liftδ h₁ h₂ h₃ k i, hS.d_liftδ h₁ h₂ h₃ k i⟩⟩)
      fun i ↦ Subtype.ext ((hS.coe_boundaryPreimageClass_mk k _ _).trans
        (hS.homologyπ_cycρ h₁ h₂ h₃ k i)))
    (boundaryBasis₃ c₃ k)
    (fun i ↦ ⟨(S.X₂.d (k + 1) k).hom (hS.liftLift₃ c₃ k i), _, rfl⟩)
    fun i ↦ Subtype.ext <| by
      rw [HomologicalComplex.Hom.coe_boundaryMap, ← HomologicalComplex.Hom.comm_apply,
        hS.g_liftLift₃, HomologicalComplex.chosenBoundaryLift_spec]

private theorem boundaryBasis₂_inl_inl (k : ℤ) (i) :
    (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k (.inl (.inl i)) : S.X₂.X k) =
      (S.f.f k).hom (boundaryBasis₁ c₁ k i) := by
  simp [boundaryBasis₂, coe_boundaryPreimageMap]

private theorem boundaryBasis₂_inl_inr (k : ℤ) (i) :
    (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k (.inl (.inr i)) : S.X₂.X k) =
      (S.f.f k).hom ((S.X₁.iCycles k).hom (hS.cycρ h₁ h₂ h₃ k i)) := by
  simp [boundaryBasis₂, coe_boundaryPreimageMap]

private theorem boundaryBasis₂_inr (k : ℤ) (i) :
    (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k (.inr i) : S.X₂.X k) =
      (S.X₂.d (k + 1) k).hom (hS.liftLift₃ c₃ k i) := by
  simp [boundaryBasis₂]

/-- Lifts through the differential of `S.X₂` of the basis `boundaryBasis₂ k`. -/
private def boundaryLift₂ (k : ℤ) :
    ((Fin (finrank F (LinearMap.range (S.X₁.d (k + 1) k).hom)) ⊕ hS.Idxρ k) ⊕
      Fin (finrank F (LinearMap.range (S.X₃.d (k + 1) k).hom))) → S.X₂.X (k + 1) :=
  Sum.elim (Sum.elim (fun i ↦ (S.f.f (k + 1)).hom (boundaryLift₁ c₁ k i)) (hS.liftδ h₁ h₂ h₃ k))
    (hS.liftLift₃ c₃ k)

private theorem d_boundaryLift₂ (k : ℤ) (i) :
    (S.X₂.d (k + 1) k).hom (hS.boundaryLift₂ h₁ h₂ h₃ c₁ c₃ k i) =
      hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k i := by
  rcases i with (i | i) | i
  · rw [boundaryBasis₂_inl_inl, boundaryLift₂, Sum.elim_inl, Sum.elim_inl,
      HomologicalComplex.Hom.comm_apply, HomologicalComplex.chosenBoundaryLift_spec]
  · rw [boundaryBasis₂_inl_inr, boundaryLift₂, Sum.elim_inl, Sum.elim_inr, hS.d_liftδ]
  · rw [boundaryBasis₂_inr, boundaryLift₂, Sum.elim_inr]

/-- The basis of `Hₖ(S.X₁)` adapted to the long exact sequence: the basis `lesρ k` of the image
of the connecting map followed by the lifts `lesψ k`. -/
private def homologyBasis₁ (k : ℤ) : Basis (hS.Idxρ k ⊕ hS.Idxφ k) F (S.X₁.homology k) :=
  Basis.ofExactLift (Submodule.injective_subtype _)
    (LinearMap.exact_iff.2 <| by
      rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      exact (hS.homology_exact₁ (k + 1) k rfl).moduleCat_range_eq_ker.symm)
    (hS.lesρ h₁ h₂ h₃ k) (hS.lesφ h₁ h₂ h₃ k) (hS.lesψ h₁ h₂ h₃ k)
    fun i ↦ Subtype.ext (hS.homologyMap_lesψ h₁ h₂ h₃ k i)

/-- The basis of `Hₖ(S.X₂)` adapted to the long exact sequence: the basis `lesφ k` of the image
of `Hₖ(S.X₁)` followed by the lifts `lesσ k`. -/
private def homologyBasis₂ (k : ℤ) : Basis (hS.Idxφ k ⊕ hS.Idxγ k) F (S.X₂.homology k) :=
  Basis.ofExactLift (Submodule.injective_subtype _)
    (LinearMap.exact_iff.2 <| by
      rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      exact (hS.homology_exact₂ k).moduleCat_range_eq_ker.symm)
    (hS.lesφ h₁ h₂ h₃ k) (hS.lesγ h₁ h₂ h₃ k) (hS.lesσ h₁ h₂ h₃ k)
    fun i ↦ Subtype.ext (hS.homologyMap_lesσ h₁ h₂ h₃ k i)

/-- The basis of `Hₖ₊₁(S.X₃)` adapted to the long exact sequence: the basis `lesγ (k + 1)` of the
image of `Hₖ₊₁(S.X₂)` followed by the lifts `lesγ' k`. -/
private def homologyBasis₃ (k : ℤ) :
    Basis (hS.Idxγ (k + 1) ⊕ hS.Idxρ k) F (S.X₃.homology (k + 1)) :=
  Basis.ofExactLift (Submodule.injective_subtype _)
    (LinearMap.exact_iff.2 <| by
      rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      exact (hS.homology_exact₃ (k + 1) k rfl).moduleCat_range_eq_ker.symm)
    (hS.lesγ h₁ h₂ h₃ (k + 1)) (hS.lesρ h₁ h₂ h₃ k) (hS.lesγ' h₁ h₂ h₃ k)
    fun i ↦ Subtype.ext (hS.δ_lesγ' h₁ h₂ h₃ k i)

private theorem coe_homologyBasis₁ (k : ℤ) :
    ⇑(hS.homologyBasis₁ h₁ h₂ h₃ k) =
      Sum.elim (fun i ↦ (hS.lesρ h₁ h₂ h₃ k i : S.X₁.homology k)) (hS.lesψ h₁ h₂ h₃ k) := by
  funext i
  rcases i with i | i <;> simp [homologyBasis₁]

private theorem coe_homologyBasis₂ (k : ℤ) :
    ⇑(hS.homologyBasis₂ h₁ h₂ h₃ k) =
      Sum.elim (fun i ↦ (hS.lesφ h₁ h₂ h₃ k i : S.X₂.homology k)) (hS.lesσ h₁ h₂ h₃ k) := by
  funext i
  rcases i with i | i <;> simp [homologyBasis₂]

private theorem coe_homologyBasis₃ (k : ℤ) :
    ⇑(hS.homologyBasis₃ h₁ h₂ h₃ k) =
      Sum.elim (fun i ↦ (hS.lesγ h₁ h₂ h₃ (k + 1) i : S.X₃.homology (k + 1)))
        (hS.lesγ' h₁ h₂ h₃ k) := by
  funext i
  rcases i with i | i <;> simp [homologyBasis₃]

/-- The boundary bases and lifts of the three complexes, in the form used for the brackets. -/
private abbrev bracketBasis₁ (k : ℤ) := (boundaryBasis₁ c₁ k).reindex (Equiv.refl _)

private abbrev bracketLift₁ (k : ℤ) := boundaryLift₁ c₁ k ∘ (Equiv.refl _).symm

private theorem d_bracketLift₁ (k : ℤ) (i) :
    (S.X₁.d (k + 1) k).hom (bracketLift₁ c₁ k i) = bracketBasis₁ c₁ k i := by
  simp

private abbrev bracketBasis₃ (k : ℤ) := (boundaryBasis₃ c₃ k).reindex (Equiv.refl _)

private abbrev bracketLift₃ (k : ℤ) := boundaryLift₃ c₃ k ∘ (Equiv.refl _).symm

private theorem d_bracketLift₃ (k : ℤ) (i) :
    (S.X₃.d (k + 1) k).hom (bracketLift₃ c₃ k i) = bracketBasis₃ c₃ k i := by
  simp

private abbrev bracketBasis₂ (k : ℤ) :=
  (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k).reindex (Fintype.equivFin _)

private abbrev bracketLift₂ (k : ℤ) :=
  hS.boundaryLift₂ h₁ h₂ h₃ c₁ c₃ k ∘ (Fintype.equivFin _).symm

private theorem d_bracketLift₂ (k : ℤ) (i) :
    (S.X₂.d (k + 1) k).hom (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃ k i) =
      hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ k i := by
  simp [d_boundaryLift₂]

/-- **The bracket of the middle term in one degree.** With the adapted choices, the bracket of
`S.X₂` in degree `j + 1` is, up to sign, the product of the brackets of `S.X₁` and `S.X₃` and of
the three brackets of the based long exact sequence at `Hⱼ₊₁(S.X₁)`, `Hⱼ₊₁(S.X₃)` and
`Hⱼ₊₁(S.X₂)`, the last one inverted. -/
private theorem signEq_torsionBracketWithHomology {c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i)}
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (y₁ : ∀ i, Fin (m₁ i) → S.X₁.cycles i) (hy₁ : ∀ i k, S.X₁.homologyπ i (y₁ i k) = h₁ i k)
    (y₂ : ∀ i, Fin (m₂ i) → S.X₂.cycles i) (hy₂ : ∀ i k, S.X₂.homologyπ i (y₂ i k) = h₂ i k)
    (y₃ : ∀ i, Fin (m₃ i) → S.X₃.cycles i) (hy₃ : ∀ i k, S.X₃.homologyπ i (y₃ i k) = h₃ i k)
    (j : ℤ) :
    SignEq
      (HomologicalComplex.torsionBracketWithHomology c₂ (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ (j + 1))
        (h₂ (j + 1)) (y₂ (j + 1)) (hy₂ (j + 1)) (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ j)
        (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃ j) (hS.d_bracketLift₂ h₁ h₂ h₃ c₁ c₃ j))
      (HomologicalComplex.torsionBracketWithHomology c₁ (bracketBasis₁ c₁ (j + 1)) (h₁ (j + 1))
          (y₁ (j + 1)) (hy₁ (j + 1)) (bracketBasis₁ c₁ j) (bracketLift₁ c₁ j)
          (d_bracketLift₁ c₁ j) *
        HomologicalComplex.torsionBracketWithHomology c₃ (bracketBasis₃ c₃ (j + 1)) (h₃ (j + 1))
          (y₃ (j + 1)) (hy₃ (j + 1)) (bracketBasis₃ c₃ j) (bracketLift₃ c₃ j)
          (d_bracketLift₃ c₃ j) *
        (hS.lesBracket h₁ h₂ h₃ (3 * (j + 1) + 1) * hS.lesBracket h₁ h₂ h₃ (3 * j + 2) *
          (hS.lesBracket h₁ h₂ h₃ (3 * (j + 1)))⁻¹)) := by
  -- The adapted homology bases, their representatives, and the brackets they give.
  set H₁ := hS.homologyBasis₁ h₁ h₂ h₃ (j + 1)
  set H₂ := hS.homologyBasis₂ h₁ h₂ h₃ (j + 1)
  set H₃ := hS.homologyBasis₃ h₁ h₂ h₃ j
  set ι₁ := H₁.indexEquiv (h₁ (j + 1))
  set ι₂ := H₂.indexEquiv (h₂ (j + 1))
  set ι₃ := H₃.indexEquiv (h₃ (j + 1))
  let z₁ := Sum.elim (hS.cycρ h₁ h₂ h₃ (j + 1)) (hS.cycψ h₁ h₂ h₃ (j + 1))
  let z₂ := Sum.elim (fun i ↦ HomologicalComplex.cyclesMap S.f (j + 1) (hS.cycψ h₁ h₂ h₃ (j + 1) i))
    (hS.cycσ h₁ h₂ h₃ (j + 1))
  let z₃ := Sum.elim (fun i ↦ HomologicalComplex.cyclesMap S.g (j + 1) (hS.cycσ h₁ h₂ h₃ (j + 1) i))
    (hS.cycγ' h₁ h₂ h₃ j)
  have hz₁ : ∀ k, S.X₁.homologyπ (j + 1) (z₁ k) = H₁ k := by
    rintro (k | k) <;> simp [z₁, H₁, coe_homologyBasis₁, homologyπ_cycρ, homologyπ_cycψ]
  have hz₂ : ∀ k, S.X₂.homologyπ (j + 1) (z₂ k) = H₂ k := by
    rintro (k | k)
    · simp [z₂, H₂, coe_homologyBasis₂, ← HomologicalComplex.moduleCat_homologyMap_homologyπ,
        homologyπ_cycψ, homologyMap_lesψ]
    · simp [z₂, H₂, coe_homologyBasis₂, homologyπ_cycσ]
  have hz₃ : ∀ k, S.X₃.homologyπ (j + 1) (z₃ k) = H₃ k := by
    rintro (k | k)
    · simp [z₃, H₃, coe_homologyBasis₃, ← HomologicalComplex.moduleCat_homologyMap_homologyπ,
        homologyπ_cycσ, homologyMap_lesσ]
    · simp [z₃, H₃, coe_homologyBasis₃, homologyπ_cycγ']
  obtain ⟨e₁, he₁⟩ := HomologicalComplex.exists_torsionBracketWithHomology_eq_det_comp c₁
    (boundaryBasis₁ c₁ (j + 1)) (Equiv.refl _) H₁ ι₁ z₁ hz₁ (boundaryBasis₁ c₁ j) (Equiv.refl _)
    (boundaryLift₁ c₁ j) (HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j)
  obtain ⟨e₂, he₂⟩ := HomologicalComplex.exists_torsionBracketWithHomology_eq_det_comp c₂
    (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ (j + 1)) (Fintype.equivFin _) H₂ ι₂ z₂ hz₂
    (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ j) (Fintype.equivFin _)
    (hS.boundaryLift₂ h₁ h₂ h₃ c₁ c₃ j) (hS.d_boundaryLift₂ h₁ h₂ h₃ c₁ c₃ j)
  obtain ⟨e₃, he₃⟩ := HomologicalComplex.exists_torsionBracketWithHomology_eq_det_comp c₃
    (boundaryBasis₃ c₃ (j + 1)) (Equiv.refl _) H₃ ι₃ z₃ hz₃ (boundaryBasis₃ c₃ j) (Equiv.refl _)
    (boundaryLift₃ c₃ j) (HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j)
  -- Changing the homology bases to the adapted ones.
  have hm₁ := HomologicalComplex.torsionBracketWithHomology_eq_mul c₁ (bracketBasis₁ c₁ (j + 1))
    (h₁ (j + 1)) (y₁ (j + 1)) (hy₁ (j + 1)) (bracketBasis₁ c₁ j) (bracketLift₁ c₁ j)
    (d_bracketLift₁ c₁ j) (bracketBasis₁ c₁ (j + 1)) (H₁.reindex ι₁) (z₁ ∘ ι₁.symm)
    (fun k ↦ by simp [hz₁]) (bracketBasis₁ c₁ j) (bracketLift₁ c₁ j) (d_bracketLift₁ c₁ j)
  have hm₂ := HomologicalComplex.torsionBracketWithHomology_eq_mul c₂
    (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ (j + 1)) (h₂ (j + 1)) (y₂ (j + 1)) (hy₂ (j + 1))
    (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ j) (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃ j)
    (hS.d_bracketLift₂ h₁ h₂ h₃ c₁ c₃ j) (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ (j + 1))
    (H₂.reindex ι₂) (z₂ ∘ ι₂.symm) (fun k ↦ by simp [hz₂]) (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ j)
    (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃ j) (hS.d_bracketLift₂ h₁ h₂ h₃ c₁ c₃ j)
  have hm₃ := HomologicalComplex.torsionBracketWithHomology_eq_mul c₃ (bracketBasis₃ c₃ (j + 1))
    (h₃ (j + 1)) (y₃ (j + 1)) (hy₃ (j + 1)) (bracketBasis₃ c₃ j) (bracketLift₃ c₃ j)
    (d_bracketLift₃ c₃ j) (bracketBasis₃ c₃ (j + 1)) (H₃.reindex ι₃) (z₃ ∘ ι₃.symm)
    (fun k ↦ by simp [hz₃]) (bracketBasis₃ c₃ j) (bracketLift₃ c₃ j) (d_bracketLift₃ c₃ j)
  rw [he₁] at hm₁
  rw [he₂] at hm₂
  rw [he₃] at hm₃
  simp only [Basis.det_self, one_mul, mul_one] at hm₁ hm₂ hm₃
  -- The bracket of the middle term with the adapted choices is, up to sign, the product of
  -- those of the outer terms.
  have core : SignEq ((c₂ (j + 1)).det (Sum.elim (Sum.elim
        (fun k ↦ (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ (j + 1) k : S.X₂.X (j + 1)))
        fun k ↦ S.X₂.iCycles (j + 1) (z₂ k)) (hS.boundaryLift₂ h₁ h₂ h₃ c₁ c₃ j) ∘ e₂))
      ((c₁ (j + 1)).det (Sum.elim (Sum.elim (fun k ↦ (boundaryBasis₁ c₁ (j + 1) k : S.X₁.X (j + 1)))
          fun k ↦ S.X₁.iCycles (j + 1) (z₁ k)) (boundaryLift₁ c₁ j) ∘ e₁) *
        (c₃ (j + 1)).det (Sum.elim (Sum.elim
          (fun k ↦ (boundaryBasis₃ c₃ (j + 1) k : S.X₃.X (j + 1)))
          fun k ↦ S.X₃.iCycles (j + 1) (z₃ k)) (boundaryLift₃ c₃ j) ∘ e₃)) := by
    rw [Basis.eq_reindex_ofExactLift (injective_f_f hS (j + 1)) (exact_f_f_g_f hS (j + 1))
      (c₁ (j + 1)) (c₃ (j + 1)) (c₂ (j + 1)) (hc₁ (j + 1)) (hc₃ (j + 1)), Basis.det_reindex]
    refine (Basis.signEq_det_comp _ _ (finSumFinEquiv.trans e₂)
      ((Equiv.sumCongr e₁ e₃).trans (regroupEquiv _ _ _ _ _ _ _ _))).trans
      (.inl (Basis.ofExactLift_det_eq_mul _ _ _ _ _ _ _ _ _ (fun i ↦ ?_) (fun i ↦ ?_)))
    · simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
      generalize e₁ i = t
      rcases t with ((a | r | x) | q)
      · simp [regroupEquiv, boundaryBasis₂_inl_inl]
      · simp [regroupEquiv, boundaryBasis₂_inl_inr, z₁]
      · simp [regroupEquiv, z₁, z₂]
      · simp [regroupEquiv, boundaryLift₂]
    · simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr]
      generalize e₃ i = t
      rcases t with ((a | x | r) | q)
      · simp [regroupEquiv, boundaryBasis₂_inr, ← HomologicalComplex.Hom.comm_apply, g_liftLift₃]
      · simp [regroupEquiv, z₂, z₃]
      · simp [regroupEquiv, boundaryLift₂, g_liftδ, z₃]
      · simp [regroupEquiv, boundaryLift₂, g_liftLift₃]
  rw [hm₁, hm₂, hm₃] at core
  -- The determinants comparing the adapted homology bases with the given ones are the brackets
  -- of the based long exact sequence, up to sign.
  have hK₁ := hS.signEq_lesBracket_one h₁ h₂ h₃ (j + 1)
    (fun i ↦ (hS.lesρ h₁ h₂ h₃ (j + 1) i : S.X₁.homology (j + 1))) (hS.lesψ h₁ h₂ h₃ (j + 1))
    (Equiv.refl _) (Equiv.refl _) (fun _ ↦ rfl) (fun _ ↦ rfl) ι₁.symm
  have hK₂ := hS.signEq_lesBracket_two h₁ h₂ h₃ (j + 1)
    (fun i ↦ (hS.lesφ h₁ h₂ h₃ (j + 1) i : S.X₂.homology (j + 1))) (hS.lesσ h₁ h₂ h₃ (j + 1))
    (Equiv.refl _) (Equiv.refl _) (fun _ ↦ rfl) (fun _ ↦ rfl) ι₂.symm
  have hK₃ := hS.signEq_lesBracket_three h₁ h₂ h₃ j
    (fun i ↦ (hS.lesγ h₁ h₂ h₃ (j + 1) i : S.X₃.homology (j + 1))) (hS.lesγ' h₁ h₂ h₃ j)
    (Equiv.refl _) (Equiv.refl _) (fun _ ↦ rfl) (fun _ ↦ rfl) ι₃.symm
  rw [← coe_homologyBasis₁, ← Basis.coe_reindex] at hK₁
  rw [← coe_homologyBasis₂, ← Basis.coe_reindex] at hK₂
  rw [← coe_homologyBasis₃, ← Basis.coe_reindex] at hK₃
  have hD : (h₂ (j + 1)).det (H₂.reindex ι₂) ≠ 0 := (Basis.isUnit_det _ _).ne_zero
  -- Divide by the determinant of the adapted basis of `Hⱼ₊₁(S.X₂)`.
  have hring : ∀ a b c d e : F, a * b * (c * d) * e = a * c * (b * d * e) := by
    intros
    ring
  have step := (core.mul (SignEq.refl ((h₂ (j + 1)).det (H₂.reindex ι₂))⁻¹)).trans
    (.inl (hring _ _ _ _ _))
  rw [mul_inv_cancel_right₀ hD] at step
  exact step.trans ((SignEq.refl _).mul ((hK₁.symm.mul hK₃.symm).mul hK₂.symm.inv))

end Middle

end CategoryTheory.ShortComplex.ShortExact

/-! ### Milnor's formula -/

/-- If one of the outer terms of a sequence of based complexes is unbounded, so that the middle
term is unbounded as well, both sides of Milnor's formula are `0`. -/
private theorem HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_not_finite
    {C₁ C₂ C₃ : ChainComplex (ModuleCat F) ℤ} {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (C₂.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (C₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i)) (hn : ¬{i | n₁ i + n₃ i ≠ 0}.Finite)
    (a : F) :
    C₂.reidemeisterTorsionWithHomology c₂ h₂ =
      C₁.reidemeisterTorsionWithHomology c₁ h₁ * C₃.reidemeisterTorsionWithHomology c₃ h₃ * a := by
  rw [HomologicalComplex.reidemeisterTorsionWithHomology_of_not_finite (hn := hn)]
  by_cases hn₁ : {i | n₁ i ≠ 0}.Finite
  · have hn₃ : ¬{i | n₃ i ≠ 0}.Finite := fun hn₃ ↦
      hn ((hn₁.union hn₃).subset fun i hi ↦ by
        simp only [Set.mem_union, Set.mem_ofPred_eq] at hi ⊢; omega)
    rw [HomologicalComplex.reidemeisterTorsionWithHomology_of_not_finite (hn := hn₃), mul_zero,
      zero_mul]
  · rw [HomologicalComplex.reidemeisterTorsionWithHomology_of_not_finite (hn := hn₁), zero_mul,
      zero_mul]

/-- The comparison of brackets in degree `j + 1`, raised to the power `(-1) ^ j`, with the
brackets of the long exact sequence raised to the powers of their own degrees. -/
private theorem signEq_zpow_negOnePow {b₁ b₂ b₃ k₁ k₂ k₃ : F} {j : ℤ}
    (h : SignEq b₂ (b₁ * b₃ * (k₁ * k₃ * k₂⁻¹))) :
    SignEq (b₂ ^ (j.negOnePow : ℤ)) (b₁ ^ (j.negOnePow : ℤ) * b₃ ^ (j.negOnePow : ℤ) *
      (k₃ ^ ((3 * j + 2).negOnePow : ℤ) * k₂ ^ ((3 * (j + 1)).negOnePow : ℤ) *
        k₁ ^ ((3 * (j + 1) + 1).negOnePow : ℤ))) := by
  have e₁ : (3 * j + 2).negOnePow = j.negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨j + 1, by ring⟩
  have e₂ : (3 * (j + 1)).negOnePow = -j.negOnePow := by
    rw [← Int.negOnePow_succ]
    exact (Int.negOnePow_eq_iff _ _).2 ⟨j + 1, by ring⟩
  have e₃ : (3 * (j + 1) + 1).negOnePow = j.negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨j + 2, by ring⟩
  refine (h.zpow _).trans (.inl ?_)
  rw [e₁, e₂, e₃, Units.val_neg, zpow_neg, mul_zpow, mul_zpow, mul_zpow, mul_zpow, inv_zpow]
  ring

/-- **Milnor's multiplicativity formula.** Let `0 → C₁ → C₂ → C₃ → 0` be a short exact sequence
of chain complexes of vector spaces, with compatible bases: the basis `c₂ i` of `C₂ᵢ` is the image
of the basis `c₁ i` of `C₁ᵢ` followed by lifts of the basis `c₃ i` of `C₃ᵢ`. For any bases
`h₁`, `h₂`, `h₃` of the homology groups,
`τ(C₂, c₂, h₂) = ± τ(C₁, c₁, h₁) · τ(C₃, c₃, h₃) · τ(H)`, where `H` is the long exact homology
sequence based by `h₁`, `h₂`, `h₃`. This holds for all complexes, both sides being `0` when the
complexes are unbounded. -/
theorem HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k) {m₁ m₂ m₃ : ℤ → ℕ}
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
        S.X₁.reidemeisterTorsionWithHomology c₁ h₁ * S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
          hS.homologySequenceComplex.reidemeisterTorsion
            (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃) ∨
      S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
        -(S.X₁.reidemeisterTorsionWithHomology c₁ h₁ * S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
          hS.homologySequenceComplex.reidemeisterTorsion
            (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃)) := by
  change SignEq _ _ -- the disjunction is equality up to sign
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · exact .inl (HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂
      h₁ h₂ h₃ hn _)
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hn₃ : {i | n₃ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hm₁ : {i | m₁ i ≠ 0}.Finite :=
    hn₁.subset fun i hi ↦ fun h ↦ hi (HomologicalComplex.eq_zero_of_basis_homology c₁ h₁ h)
  have hm₂ : {i | m₂ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ fun h ↦ hi (HomologicalComplex.eq_zero_of_basis_homology c₂ h₂ h)
  have hm₃ : {i | m₃ i ≠ 0}.Finite :=
    hn₃.subset fun i hi ↦ fun h ↦ hi (HomologicalComplex.eq_zero_of_basis_homology c₃ h₃ h)
  have hnK := ChainComplex.interleave.finite_setOf_rank_ne_zero hm₁ hm₂ hm₃
  -- Cycles representing the homology bases.
  let y₁ (i : ℤ) (k : Fin (m₁ i)) : S.X₁.cycles i :=
    Function.surjInv (S.X₁.moduleCat_homologyπ_surjective i) (h₁ i k)
  let y₂ (i : ℤ) (k : Fin (m₂ i)) : S.X₂.cycles i :=
    Function.surjInv (S.X₂.moduleCat_homologyπ_surjective i) (h₂ i k)
  let y₃ (i : ℤ) (k : Fin (m₃ i)) : S.X₃.cycles i :=
    Function.surjInv (S.X₃.moduleCat_homologyπ_surjective i) (h₃ i k)
  have hy₁ (i : ℤ) (k) : S.X₁.homologyπ i (y₁ i k) = h₁ i k :=
    Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective i) _
  have hy₂ (i : ℤ) (k) : S.X₂.homologyπ i (y₂ i k) = h₂ i k :=
    Function.surjInv_eq (S.X₂.moduleCat_homologyπ_surjective i) _
  have hy₃ (i : ℤ) (k) : S.X₃.homologyπ i (y₃ i k) = h₃ i k :=
    Function.surjInv_eq (S.X₃.moduleCat_homologyπ_surjective i) _
  -- Expand the four torsions as alternating products of brackets.
  have hK := HomologicalComplex.hasFiniteMulSupport_torsionBracket
    (c := hS.lesBasis h₁ h₂ h₃) hnK hS.acyclic_homologySequenceComplex
    (hS.lesBoundaryBasis h₁ h₂ h₃) (hS.lesBoundaryLift h₁ h₂ h₃)
    fun j ↦ HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j
  rw [HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod hn
      (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃) y₂ hy₂ (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃)
      (hS.d_bracketLift₂ h₁ h₂ h₃ c₁ c₃),
    HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod hn₁
      (ShortComplex.ShortExact.bracketBasis₁ c₁) y₁ hy₁
      (ShortComplex.ShortExact.bracketLift₁ c₁) (ShortComplex.ShortExact.d_bracketLift₁ c₁),
    HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod hn₃
      (ShortComplex.ShortExact.bracketBasis₃ c₃) y₃ hy₃
      (ShortComplex.ShortExact.bracketLift₃ c₃) (ShortComplex.ShortExact.d_bracketLift₃ c₃),
    HomologicalComplex.reidemeisterTorsion_eq_finprod hnK hS.acyclic_homologySequenceComplex
      (hS.lesBoundaryBasis h₁ h₂ h₃) (hS.lesBoundaryLift h₁ h₂ h₃)
      (fun j ↦ HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j),
    finprod_eq_finprod_three _ hK]
  have hs₁ := HomologicalComplex.hasFiniteMulSupport_torsionBracketWithHomology (c := c₁)
    (h := h₁) hn₁ (ShortComplex.ShortExact.bracketBasis₁ c₁) y₁ hy₁
    (ShortComplex.ShortExact.bracketLift₁ c₁) (ShortComplex.ShortExact.d_bracketLift₁ c₁)
  have hs₂ := HomologicalComplex.hasFiniteMulSupport_torsionBracketWithHomology (c := c₂)
    (h := h₂) hn (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃) y₂ hy₂ (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃)
    (hS.d_bracketLift₂ h₁ h₂ h₃ c₁ c₃)
  have hs₃ := HomologicalComplex.hasFiniteMulSupport_torsionBracketWithHomology (c := c₃)
    (h := h₃) hn₃ (ShortComplex.ShortExact.bracketBasis₃ c₃) y₃ hy₃
    (ShortComplex.ShortExact.bracketLift₃ c₃) (ShortComplex.ShortExact.d_bracketLift₃ c₃)
  have hsK := ((hK.fun_comp_of_injective (g := fun j : ℤ ↦ 3 * j + 2) fun a b h ↦ by
      simpa using h).fun_mul (hK.fun_comp_of_injective (g := fun j : ℤ ↦ 3 * (j + 1))
      fun a b h ↦ by simpa using h)).fun_mul
    (hK.fun_comp_of_injective (g := fun j : ℤ ↦ 3 * (j + 1) + 1) fun a b h ↦ by simpa using h)
  rw [← finprod_mul_distrib hs₁ hs₃, ← finprod_mul_distrib (hs₁.fun_mul hs₃) hsK]
  -- In each degree, the comparison of brackets raised to the power `(-1) ^ j`.
  exact SignEq.finprod hs₂ ((hs₁.fun_mul hs₃).fun_mul hsK) fun j ↦ signEq_zpow_negOnePow
    (hS.signEq_torsionBracketWithHomology h₁ h₂ h₃ c₁ c₃ hc₁ hc₃ y₁ hy₁ y₂ hy₂ y₃ hy₃ j)
