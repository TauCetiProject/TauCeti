/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Homology
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Interleave
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Alternating.Append
import TauCeti.LinearAlgebra.Exact

/-!
# Multiplicativity of Reidemeister torsion through the long exact homology sequence

Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of
vector spaces over a field `F`. Its long exact homology sequence is the acyclic chain complex
`CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`, with `Hᵢ(S.X₁)`, `Hᵢ(S.X₂)` and
`Hᵢ(S.X₃)` in degrees `3i + 2`, `3i + 1` and `3i`. Ordered bases `h₁ i`, `h₂ i`, `h₃ i` of the
homology groups make it a based complex (`ChainComplex.interleave.basis`), whose Reidemeister
torsion `τ(H)` is nonzero whenever only finitely many homology groups are nonzero
(`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`).

When `S.X₁`, `S.X₂`, `S.X₃` also carry compatible chain bases `c₁`, `c₂`, `c₃`, this file proves
Milnor's multiplicativity formula for Reidemeister torsion with homology bases
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`):
`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H)`, where
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim im f_*,ⱼ₊₁ + (dim B₃,ⱼ₊₁ + dim im g_*,ⱼ₊₁) · dim B₁,ⱼ)` is the
Koszul sign comparing the boundary-cycle-lift filtrations of the three complexes. Specializing
`τ(H)` when one of `S.X₂`, `S.X₃` or `S.X₁` is acyclic expresses the homology correction as the
alternating product of determinants of the induced homology isomorphisms.

## Main declarations

* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`: the
  based long exact homology sequence has nonzero torsion.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`: multiplicativity of
  Reidemeister torsion with homology bases through the long exact homology sequence.
* `HomologicalComplex.card_eq_of_shortExact_of_acyclic_X₂`,
  `HomologicalComplex.card_eq_of_shortExact_of_acyclic_X₃`,
  `HomologicalComplex.card_eq_of_shortExact_of_acyclic_X₁`: equalities of Betti numbers when one
  term of the short exact sequence is acyclic.
* `HomologicalComplex.reidemeisterTorsion_eq_mul_of_shortExact_of_acyclic_X₂`,
  `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₃`,
  `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₁`:
  specializations when one of the three complexes is acyclic.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorem 1.14.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Appendix A, Proposition A.2.
-/

public section

noncomputable section

open CategoryTheory Module

namespace CategoryTheory.ShortComplex.ShortExact

variable {F : Type*} [Field F] {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
  (hS : S.ShortExact) {m₁ m₂ m₃ : ℤ → ℕ} (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (b₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
  (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))

/-- The long exact homology sequence, based by ordered bases of the homology groups of which only
finitely many are nonempty, has nonzero Reidemeister torsion. -/
theorem reidemeisterTorsion_homologySequenceComplex_ne_zero (h₁ : {i | m₁ i ≠ 0}.Finite)
    (h₂ : {i | m₂ i ≠ 0}.Finite) (h₃ : {i | m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) ≠ 0 :=
  HomologicalComplex.reidemeisterTorsion_ne_zero _ _
    (ChainComplex.interleave.finite_setOf_rank_ne_zero h₁ h₂ h₃)
    hS.acyclic_homologySequenceComplex

end CategoryTheory.ShortComplex.ShortExact

namespace HomologicalComplex

section Helpers

variable {F : Type*} [Field F]

/-- If a chain complex of vector spaces is bounded, only finitely many of its homology groups are
nonzero. -/
private theorem finite_homology_of_finite {C : ChainComplex (ModuleCat F) ℤ} {n m : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (h : ∀ i, Basis (Fin (m i)) F (C.homology i))
    (hn : {i | n i ≠ 0}.Finite) : {i | m i ≠ 0}.Finite :=
  hn.subset fun i hi h0 ↦ by
    have : Module.Finite F (C.X i) := .of_basis (c i)
    have hle := C.finrank_homology_le_finrank_X i
    rw [finrank_eq_card_basis (h i), finrank_eq_card_basis (c i), Fintype.card_fin,
      Fintype.card_fin, h0] at hle
    exact hi (Nat.eq_zero_of_le_zero hle)

/-- An exact short complex `A --φ--> B --ψ--> C` in `ModuleCat F` gives a short exact sequence
`0 → range φ → B → range ψ → 0`. -/
private theorem exact_subtype_rangeRestrict_of_exact {A B C : ModuleCat F} {φ : A ⟶ B}
    {ψ : B ⟶ C} {hφψ : φ ≫ ψ = 0} (h : (ShortComplex.mk φ ψ hφψ).Exact) :
    Function.Exact (LinearMap.range φ.hom).subtype ψ.hom.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker (ShortComplex.mk φ ψ hφψ)).1 h).symm

/-- The basis `(α, β')` of the middle term `B` of an exact pair `A --φ--> B --ψ--> C` in
`ModuleCat F`, reindexed to `Fin m` along `hm : m = u + v`. -/
private def adaptedHomologyBasis {A B C : ModuleCat F} {φ : A ⟶ B} {ψ : B ⟶ C} {hφψ : φ ≫ ψ = 0}
    (h : (ShortComplex.mk φ ψ hφψ).Exact) {u v m : ℕ} (hm : m = u + v)
    (α : Basis (Fin u) F (LinearMap.range φ.hom)) (β : Basis (Fin v) F (LinearMap.range ψ.hom))
    (β' : Fin v → B) (hβ' : ∀ l, ψ.hom (β' l) = β l) : Basis (Fin m) F B :=
  ((Basis.ofExactLift (Submodule.injective_subtype _) (exact_subtype_rangeRestrict_of_exact h) α β
    β' fun l ↦ Subtype.ext (hβ' l)).reindex finSumFinEquiv).reindex (finCongr hm.symm)

private theorem coe_adaptedHomologyBasis {A B C : ModuleCat F} {φ : A ⟶ B} {ψ : B ⟶ C}
    {hφψ : φ ≫ ψ = 0} (h : (ShortComplex.mk φ ψ hφψ).Exact) {u v m : ℕ} (hm : m = u + v)
    (α : Basis (Fin u) F (LinearMap.range φ.hom)) (β : Basis (Fin v) F (LinearMap.range ψ.hom))
    (β' : Fin v → B) (hβ' : ∀ l, ψ.hom (β' l) = β l) :
    ⇑(adaptedHomologyBasis h hm α β β' hβ') =
      Fin.append (fun l ↦ (α l : B)) β' ∘ Fin.cast hm := by
  rw [adaptedHomologyBasis, Basis.coe_reindex, Basis.coe_reindex_ofExactLift]
  rfl

section BoundaryBasis

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
  (hf : ∀ i, Function.Injective (S.f.f i).hom)
  (hfg : ∀ i, Function.Exact (S.f.f i).hom (S.g.f i).hom) {j : ℤ} {p' u p'' : ℕ}

/-- Stage A: a basis of `S.f⁻¹(B₂,ⱼ) ⊆ S.X₁,ⱼ` made of a basis `b'` of `B₁,ⱼ` followed by cycles
`a₁` representing a basis `α` of `range δⱼ = ker f_*,ⱼ`. -/
private def shortExactPreimageBasis
    (b' : Basis (Fin p') F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (α : Basis (Fin u) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (a₁ : Fin u → S.X₁.cycles j) (ha₁ : ∀ k, S.X₁.homologyπ j (a₁ k) = α k)
    (aLift : Fin u → S.X₂.X (j + 1))
    (hd : ∀ k, (S.X₂.d (j + 1) j).hom (aLift k) = (S.f.f j).hom (S.X₁.iCycles j (a₁ k))) :
    Basis (Fin (p' + u)) F ((LinearMap.range (S.X₂.d (j + 1) j).hom).comap (S.f.f j).hom) := by
  have hm : (ComplexShape.down ℤ).next j = j - 1 :=
    (ComplexShape.down ℤ).next_eq' (by rw [ComplexShape.down_Rel]; omega)
  have hker : LinearMap.range (hS.δ (j + 1) j rfl).hom =
      LinearMap.ker (homologyMap S.f j).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (hS.homology_exact₁ (j + 1) j rfl)
  refine (Basis.ofExactLift (Submodule.inclusion_injective _)
    (S.f.exact_inclusion_comapBoundaryHomologyClass ((ComplexShape.down ℤ).prev_eq' rfl)
      hm (hf (j - 1))) b' (α.map (LinearEquiv.ofEq _ _ hker))
    (fun k ↦ ⟨S.X₁.iCycles j (a₁ k), aLift k, hd k⟩) fun k ↦ Subtype.ext ?_).reindex finSumFinEquiv
  exact (S.f.coe_comapBoundaryHomologyClass_iCycles (j + 1) hm (hf (j - 1)) (a₁ k) _).trans
    (by simp [ha₁ k])

private theorem coe_shortExactPreimageBasis
    (b' : Basis (Fin p') F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (α : Basis (Fin u) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (a₁ : Fin u → S.X₁.cycles j) (ha₁ : ∀ k, S.X₁.homologyπ j (a₁ k) = α k)
    (aLift : Fin u → S.X₂.X (j + 1))
    (hd : ∀ k, (S.X₂.d (j + 1) j).hom (aLift k) = (S.f.f j).hom (S.X₁.iCycles j (a₁ k))) :
    (fun k ↦ (shortExactPreimageBasis hS hf b' α a₁ ha₁ aLift hd k : S.X₁.X j)) =
      Fin.append (fun k ↦ (b' k : S.X₁.X j)) fun k ↦ S.X₁.iCycles j (a₁ k) := by
  ext k
  induction k using Fin.addCases <;> simp [shortExactPreimageBasis]

/-- Stage B: a basis of `B₂,ⱼ` made of the images of `b'` and `a₁` under `S.f` followed by the
boundaries `d₂ (t k)` of lifts `t` of a basis `b''` of `B₃,ⱼ`. -/
private def shortExactBoundaryBasisWithHomology
    (b' : Basis (Fin p') F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (α : Basis (Fin u) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (a₁ : Fin u → S.X₁.cycles j) (ha₁ : ∀ k, S.X₁.homologyπ j (a₁ k) = α k)
    (aLift : Fin u → S.X₂.X (j + 1))
    (hd : ∀ k, (S.X₂.d (j + 1) j).hom (aLift k) = (S.f.f j).hom (S.X₁.iCycles j (a₁ k)))
    (b'' : Basis (Fin p'') F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t : Fin p'' → S.X₂.X (j + 1))
    (ht : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t k)) = b'' k) :
    Basis (Fin (p' + u + p'')) F (LinearMap.range (S.X₂.d (j + 1) j).hom) :=
  (Basis.ofExactLift (f := (S.f.f j).hom.restrict fun _ hx ↦ hx)
    (fun _ _ hxy ↦ Subtype.ext (hf j (congrArg Subtype.val hxy)))
    ((hfg j).restrict_comap (q := LinearMap.range (S.X₂.d (j + 1) j).hom)
      (r := LinearMap.range (S.X₃.d (j + 1) j).hom)
      fun _ ⟨y, hy⟩ ↦ ⟨(S.g.f (j + 1)).hom y, by rw [Hom.comm_apply, hy]⟩)
    (shortExactPreimageBasis hS hf b' α a₁ ha₁ aLift hd) b''
    (fun k ↦ ⟨(S.X₂.d (j + 1) j).hom (t k), t k, rfl⟩)
    fun k ↦ Subtype.ext ((Hom.comm_apply S.g _ _ _).symm.trans (ht k))).reindex finSumFinEquiv

private theorem coe_shortExactBoundaryBasisWithHomology
    (b' : Basis (Fin p') F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (α : Basis (Fin u) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (a₁ : Fin u → S.X₁.cycles j) (ha₁ : ∀ k, S.X₁.homologyπ j (a₁ k) = α k)
    (aLift : Fin u → S.X₂.X (j + 1))
    (hd : ∀ k, (S.X₂.d (j + 1) j).hom (aLift k) = (S.f.f j).hom (S.X₁.iCycles j (a₁ k)))
    (b'' : Basis (Fin p'') F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t : Fin p'' → S.X₂.X (j + 1))
    (ht : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t k)) = b'' k) :
    (fun k ↦ (shortExactBoundaryBasisWithHomology hS hf hfg b' α a₁ ha₁ aLift hd b'' t ht k :
        S.X₂.X j)) =
      Fin.append (Fin.append (fun k ↦ (S.f.f j).hom (b' k))
        fun k ↦ (S.f.f j).hom (S.X₁.iCycles j (a₁ k)))
        fun k ↦ (S.X₂.d (j + 1) j).hom (t k) := by
  have hpre := coe_shortExactPreimageBasis hS hf b' α a₁ ha₁ aLift hd
  have hcoe := Basis.coe_reindex_ofExactLift (f := (S.f.f j).hom.restrict fun _ hx ↦ hx)
    (fun _ _ hxy ↦ Subtype.ext (hf j (congrArg Subtype.val hxy)))
    ((hfg j).restrict_comap (q := LinearMap.range (S.X₂.d (j + 1) j).hom)
      (r := LinearMap.range (S.X₃.d (j + 1) j).hom)
      fun _ ⟨y, hy⟩ ↦ ⟨(S.g.f (j + 1)).hom y, by rw [Hom.comm_apply, hy]⟩)
    (shortExactPreimageBasis hS hf b' α a₁ ha₁ aLift hd) b''
    (fun k ↦ ⟨(S.X₂.d (j + 1) j).hom (t k), t k, rfl⟩)
    fun k ↦ Subtype.ext ((Hom.comm_apply S.g _ _ _).symm.trans (ht k))
  ext k
  rw [shortExactBoundaryBasisWithHomology, congrArg Subtype.val (congrFun hcoe k)]
  induction k using Fin.addCases with
  | left k =>
    simp only [Fin.append_left, Function.comp_apply, LinearMap.restrict_apply]
    rw [congrFun hpre k]
    induction k using Fin.addCases <;> simp
  | right k => simp

end BoundaryBasis

private theorem card_eq_add_add {C : ChainComplex (ModuleCat F) ℤ} {n : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) {j : ℤ} {p m q : ℕ}
    (b₁ : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
    (h : Basis (Fin m) F (C.homology (j + 1)))
    (y : Fin m → C.cycles (j + 1)) (hy : ∀ k, C.homologyπ (j + 1) (y k) = h k)
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom))
    (s : Fin q → C.X (j + 1)) (hs : ∀ k, (C.d (j + 1) j).hom (s k) = b₀ k) :
    n (j + 1) = p + m + q := by
  let zBasis := Basis.ofExactLift (Submodule.inclusion_injective _)
    (C.exact_inclusion_moduleCatKerHomologyClass ((ComplexShape.down ℤ).next_eq' rfl)
      (ChainComplex.prev ℤ (j + 1))) b₁ h (C.moduleCatCyclesToKer (j + 1) j ∘ y) fun k ↦ by
    rw [Function.comp_apply, moduleCatKerHomologyClass_moduleCatCyclesToKer, hy]
  let xBasis := Basis.ofExactLift (Submodule.injective_subtype _)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
    zBasis b₀ s fun k ↦ Subtype.ext (hs k)
  simpa using Fintype.card_congr ((c (j + 1)).indexEquiv xBasis)

section AdaptedBracket

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
  (hf : ∀ i, Function.Injective (S.f.f i).hom)
  (hfg : ∀ i, Function.Exact (S.f.f i).hom (S.g.f i).hom)
  {n₁ n₃ : ℤ → ℕ} {c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)}
  {c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i)} {c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i)}
  (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
  (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
  {j : ℤ} {p'₁ u₁ p''₁ v₁ w₁ p'₀ u₀ p''₀ m₁ m₂ m₃ : ℕ}
  (hm₁ : m₁ = u₁ + v₁) (hm₂ : m₂ = v₁ + w₁) (hm₃ : m₃ = w₁ + u₀)
  (b'₁ : Basis (Fin p'₁) F (LinearMap.range (S.X₁.d (j + 1 + 1) (j + 1)).hom))
  (α₁ : Basis (Fin u₁) F (LinearMap.range (hS.δ (j + 1 + 1) (j + 1) rfl).hom))
  (a₁_hi : Fin u₁ → S.X₁.cycles (j + 1)) (ha₁_hi : ∀ k, S.X₁.homologyπ (j + 1) (a₁_hi k) = α₁ k)
  (aLift₁ : Fin u₁ → S.X₂.X (j + 1 + 1))
  (hd₁ : ∀ k, (S.X₂.d (j + 1 + 1) (j + 1)).hom (aLift₁ k) =
    (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (a₁_hi k)))
  (b''₁ : Basis (Fin p''₁) F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom))
  (t₁ : Fin p''₁ → S.X₂.X (j + 1 + 1))
  (ht₁ : ∀ k, (S.X₃.d (j + 1 + 1) (j + 1)).hom ((S.g.f (j + 1 + 1)).hom (t₁ k)) = b''₁ k)
  (β₁ : Basis (Fin v₁) F (LinearMap.range (homologyMap S.f (j + 1)).hom))
  (β'₁ : Fin v₁ → S.X₁.homology (j + 1)) (hβ'₁ : ∀ l, (homologyMap S.f (j + 1)).hom (β'₁ l) = β₁ l)
  (y₁ : Fin v₁ → S.X₁.cycles (j + 1))
  (γ₁ : Basis (Fin w₁) F (LinearMap.range (homologyMap S.g (j + 1)).hom))
  (γ'₁ : Fin w₁ → S.X₂.homology (j + 1)) (hγ'₁ : ∀ l, (homologyMap S.g (j + 1)).hom (γ'₁ l) = γ₁ l)
  (z₂ : Fin w₁ → S.X₂.cycles (j + 1))
  (b'₀ : Basis (Fin p'₀) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
  (s'₀ : Fin p'₀ → S.X₁.X (j + 1)) (hs'₀ : ∀ k, (S.X₁.d (j + 1) j).hom (s'₀ k) = b'₀ k)
  (α₀ : Basis (Fin u₀) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
  (α'₀ : Fin u₀ → S.X₃.homology (j + 1))
  (hα'₀ : ∀ l, (hS.δ (j + 1) j rfl).hom (α'₀ l) = α₀ l)
  (a₁_lo : Fin u₀ → S.X₁.cycles j) (ha₁_lo : ∀ k, S.X₁.homologyπ j (a₁_lo k) = α₀ k)
  (aLift₀ : Fin u₀ → S.X₂.X (j + 1))
  (hd₀ : ∀ k, (S.X₂.d (j + 1) j).hom (aLift₀ k) = (S.f.f j).hom (S.X₁.iCycles j (a₁_lo k)))
  (aCycle₃ : Fin u₀ → S.X₃.cycles (j + 1))
  (hg₀ : ∀ k, (S.g.f (j + 1)).hom (aLift₀ k) = S.X₃.iCycles (j + 1) (aCycle₃ k))
  (b''₀ : Basis (Fin p''₀) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
  (t₀ : Fin p''₀ → S.X₂.X (j + 1))
  (ht₀ : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t₀ k)) = b''₀ k)

private theorem adapted_append_left_eq
    (hN : n₁ (j + 1) + n₃ (j + 1) = ((p'₁ + u₁) + v₁ + p'₀) + (p''₁ + w₁ + (u₀ + p''₀)))
    (hn₁ : n₁ (j + 1) = p'₁ + m₁ + p'₀) (i : Fin (n₁ (j + 1))) :
    (Fin.append (Fin.append
      (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b'₁ k))
        fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (a₁_hi k)))
        fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (y₁ k)))
      fun k ↦ (S.f.f (j + 1)).hom (s'₀ k))
      (Fin.append (Fin.append (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k))
        fun k ↦ S.X₂.iCycles (j + 1) (z₂ k)) (Fin.append aLift₀ t₀)) ∘ finCongr hN)
      (finSumFinEquiv (.inl i)) =
    (S.f.f (j + 1)).hom ((Fin.append (Fin.append (fun k ↦ (b'₁ k : S.X₁.X (j + 1)))
      fun k ↦ S.X₁.iCycles (j + 1) ((Fin.append a₁_hi y₁ ∘ Fin.cast hm₁) k)) s'₀ ∘
      Fin.cast hn₁) i) := by
  subst hm₁
  have hn₁' : (p'₁ + u₁) + v₁ + p'₀ = n₁ (j + 1) := by omega
  have hl (m : Fin ((p'₁ + u₁) + v₁ + p'₀)) :
      finCongr hN (finSumFinEquiv (.inl (finCongr hn₁' m))) =
      Fin.castAdd (p''₁ + w₁ + (u₀ + p''₀)) m := Fin.ext (by simp)
  obtain ⟨m, rfl⟩ := (finCongr hn₁').surjective i
  rw [Function.comp_apply, Function.comp_apply, hl, Fin.append_left]
  induction m using Fin.addCases with
  | left m =>
    induction m using Fin.addCases with
    | left m =>
      induction m using Fin.addCases with
      | left k =>
        have hk : Fin.cast hn₁ (finCongr hn₁'
            (Fin.castAdd p'₀ (Fin.castAdd v₁ (Fin.castAdd u₁ k)))) =
            Fin.castAdd p'₀ (Fin.castAdd (u₁ + v₁) k) := Fin.ext (by simp)
        rw [hk]; simp
      | right k =>
        have hk : Fin.cast hn₁ (finCongr hn₁'
            (Fin.castAdd p'₀ (Fin.castAdd v₁ (Fin.natAdd p'₁ k)))) =
            Fin.castAdd p'₀ (Fin.natAdd p'₁ (Fin.castAdd v₁ k)) := Fin.ext (by simp)
        rw [hk]; simp
    | right k =>
      have hk : Fin.cast hn₁ (finCongr hn₁' (Fin.castAdd p'₀ (Fin.natAdd (p'₁ + u₁) k))) =
          Fin.castAdd p'₀ (Fin.natAdd p'₁ (Fin.natAdd u₁ k)) := Fin.ext (by simp [add_assoc])
      rw [hk]; simp
  | right k =>
    have hk : Fin.cast hn₁ (finCongr hn₁' (Fin.natAdd (p'₁ + u₁ + v₁) k)) =
        Fin.natAdd (p'₁ + (u₁ + v₁)) k := Fin.ext (by simp [add_assoc])
    rw [hk]; simp

include ht₁ hg₀ in
private theorem adapted_append_right_eq
    (hN : n₁ (j + 1) + n₃ (j + 1) = ((p'₁ + u₁) + v₁ + p'₀) + (p''₁ + w₁ + (u₀ + p''₀)))
    (hn₃ : n₃ (j + 1) = p''₁ + m₃ + p''₀) (i : Fin (n₃ (j + 1))) :
    (S.g.f (j + 1)).hom ((Fin.append (Fin.append
      (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b'₁ k))
        fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (a₁_hi k)))
        fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (y₁ k)))
      fun k ↦ (S.f.f (j + 1)).hom (s'₀ k))
      (Fin.append (Fin.append (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k))
        fun k ↦ S.X₂.iCycles (j + 1) (z₂ k)) (Fin.append aLift₀ t₀)) ∘ finCongr hN)
      (finSumFinEquiv (.inr i))) =
    (Fin.append (Fin.append (fun k ↦ (b''₁ k : S.X₃.X (j + 1)))
      fun k ↦ S.X₃.iCycles (j + 1)
        ((Fin.append (fun l ↦ cyclesMap S.g (j + 1) (z₂ l)) aCycle₃ ∘ Fin.cast hm₃) k))
      (fun k ↦ (S.g.f (j + 1)).hom (t₀ k)) ∘ Fin.cast hn₃) i := by
  subst hm₃
  have hn₃' : p''₁ + w₁ + (u₀ + p''₀) = n₃ (j + 1) := by omega
  have hr (m : Fin (p''₁ + w₁ + (u₀ + p''₀))) :
      finCongr hN (finSumFinEquiv (.inr (finCongr hn₃' m))) =
      Fin.natAdd ((p'₁ + u₁) + v₁ + p'₀) m := Fin.ext (by simp; omega)
  obtain ⟨m, rfl⟩ := (finCongr hn₃').surjective i
  rw [Function.comp_apply, Function.comp_apply, hr, Fin.append_right]
  induction m using Fin.addCases with
  | left m =>
    induction m using Fin.addCases with
    | left k =>
      have hk : Fin.cast hn₃ (finCongr hn₃' (Fin.castAdd (u₀ + p''₀) (Fin.castAdd w₁ k))) =
          Fin.castAdd p''₀ (Fin.castAdd (w₁ + u₀) k) := Fin.ext (by simp)
      rw [hk]; simp [← Hom.comm_apply, ht₁]
    | right k =>
      have hk : Fin.cast hn₃ (finCongr hn₃' (Fin.castAdd (u₀ + p''₀) (Fin.natAdd p''₁ k))) =
          Fin.castAdd p''₀ (Fin.natAdd p''₁ (Fin.castAdd u₀ k)) := Fin.ext (by simp)
      rw [hk]; simp [moduleCat_iCycles_cyclesMap_apply]
  | right m =>
    induction m using Fin.addCases with
    | left k =>
      have hk : Fin.cast hn₃ (finCongr hn₃' (Fin.natAdd (p''₁ + w₁) (Fin.castAdd p''₀ k))) =
          Fin.castAdd p''₀ (Fin.natAdd p''₁ (Fin.natAdd w₁ k)) := Fin.ext (by simp [add_assoc])
      rw [hk]; simp [hg₀]
    | right k =>
      have hk : Fin.cast hn₃ (finCongr hn₃' (Fin.natAdd (p''₁ + w₁) (Fin.natAdd u₀ k))) =
          Fin.natAdd (p''₁ + (w₁ + u₀)) k := Fin.ext (by simp [add_assoc])
      rw [hk]; simp

private theorem adapted_append_reassoc
    (hn₂ : n₁ (j + 1) + n₃ (j + 1) = (p'₁ + u₁ + p''₁) + m₂ + (p'₀ + u₀ + p''₀))
    (hN : n₁ (j + 1) + n₃ (j + 1) = ((p'₁ + u₁) + v₁ + p'₀) + (p''₁ + w₁ + (u₀ + p''₀)))
    (hcast : ((p'₁ + u₁) + v₁ + p'₀) + (p''₁ + w₁ + (u₀ + p''₀)) =
      ((p'₁ + u₁ + p''₁) + (v₁ + w₁)) + (p'₀ + (u₀ + p''₀))) :
    (Fin.append (Fin.append
      (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b'₁ k))
        fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (a₁_hi k)))
        fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k))
      fun k ↦ S.X₂.iCycles (j + 1)
        ((Fin.append (fun l ↦ cyclesMap S.f (j + 1) (y₁ l)) z₂ ∘ Fin.cast hm₂) k))
      (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s'₀ k)) aLift₀) t₀)) ∘
      Fin.cast hn₂ =
    (Fin.append (Fin.append
      (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b'₁ k))
        fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (a₁_hi k)))
        fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k))
      (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (y₁ k)))
        fun k ↦ S.X₂.iCycles (j + 1) (z₂ k)))
      (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s'₀ k)) (Fin.append aLift₀ t₀)) ∘
      Fin.cast hcast) ∘ finCongr hN := by
  cases hm₂
  have hmid : (fun k ↦ S.X₂.iCycles (j + 1)
      ((Fin.append (fun l ↦ cyclesMap S.f (j + 1) (y₁ l)) z₂ ∘ Fin.cast rfl) k)) =
      Fin.append (fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (y₁ k)))
        fun k ↦ S.X₂.iCycles (j + 1) (z₂ k) := by
    ext k; induction k using Fin.addCases <;> simp [moduleCat_iCycles_cyclesMap_apply]
  rw [hmid]
  ext i
  simp only [Function.comp_apply, Fin.append_assoc, Fin.append_cast_right, finCongr_apply,
    Fin.cast_cast]

include hc₁ hc₃ hg₀ in
/-- For homology bases `h₁'`, `h₂'`, `h₃'` adapted to the long exact homology sequence and boundary
bases `shortExactBoundaryBasisWithHomology`, the bracket of `S.X₂` in degree `j + 1` is the product
of the brackets of `S.X₁` and `S.X₃`, up to the Koszul sign
`(-1) ^ (p''₁ * v₁ + (p''₁ + w₁) * p'₀)`. -/
private theorem torsionBracketWithHomology_shortExact_adapted
    (hz₁' : ∀ k, S.X₁.homologyπ (j + 1) ((Fin.append a₁_hi y₁ ∘ Fin.cast hm₁) k) =
      adaptedHomologyBasis (hS.homology_exact₁ (j + 1 + 1) (j + 1) rfl) hm₁ α₁ β₁
        β'₁ hβ'₁ k)
    (hz₂' : ∀ k, S.X₂.homologyπ (j + 1)
      ((Fin.append (fun l ↦ cyclesMap S.f (j + 1) (y₁ l)) z₂ ∘ Fin.cast hm₂) k) =
      adaptedHomologyBasis (hS.homology_exact₂ (j + 1)) hm₂ β₁ γ₁ γ'₁ hγ'₁ k)
    (hz₃' : ∀ k, S.X₃.homologyπ (j + 1)
      ((Fin.append (fun l ↦ cyclesMap S.g (j + 1) (z₂ l)) aCycle₃ ∘ Fin.cast hm₃) k) =
      adaptedHomologyBasis (hS.homology_exact₃ (j + 1) j rfl) hm₃ γ₁ α₀ α'₀ hα'₀ k)
    (hs₂ : ∀ k, (S.X₂.d (j + 1) j).hom
      (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s'₀ k)) aLift₀) t₀ k) =
      shortExactBoundaryBasisWithHomology hS hf hfg b'₀ α₀ a₁_lo ha₁_lo aLift₀ hd₀ b''₀ t₀ ht₀ k) :
    torsionBracketWithHomology c₂
        (shortExactBoundaryBasisWithHomology hS hf hfg b'₁ α₁ a₁_hi ha₁_hi aLift₁ hd₁ b''₁ t₁ ht₁)
        (adaptedHomologyBasis (hS.homology_exact₂ (j + 1)) hm₂ β₁ γ₁ γ'₁ hγ'₁)
        (Fin.append (fun l ↦ cyclesMap S.f (j + 1) (y₁ l)) z₂ ∘ Fin.cast hm₂) hz₂'
        (shortExactBoundaryBasisWithHomology hS hf hfg b'₀ α₀ a₁_lo ha₁_lo aLift₀ hd₀ b''₀ t₀ ht₀)
        (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s'₀ k)) aLift₀) t₀) hs₂ =
      (-1 : F) ^ (p''₁ * v₁ + (p''₁ + w₁) * p'₀) *
        (torsionBracketWithHomology c₁ b'₁
          (adaptedHomologyBasis (hS.homology_exact₁ (j + 1 + 1) (j + 1) rfl) hm₁ α₁
            β₁ β'₁ hβ'₁)
          (Fin.append a₁_hi y₁ ∘ Fin.cast hm₁) hz₁' b'₀ s'₀ hs'₀ *
        torsionBracketWithHomology c₃ b''₁
          (adaptedHomologyBasis (hS.homology_exact₃ (j + 1) j rfl) hm₃ γ₁ α₀ α'₀ hα'₀)
          (Fin.append (fun l ↦ cyclesMap S.g (j + 1) (z₂ l)) aCycle₃ ∘ Fin.cast hm₃) hz₃'
          b''₀ (fun k ↦ (S.g.f (j + 1)).hom (t₀ k)) ht₀) := by
  have hn₁ := card_eq_add_add c₁ b'₁ _ _ hz₁' b'₀ s'₀ hs'₀
  have hn₃ := card_eq_add_add c₃ b''₁ _ _ hz₃' b''₀ _ ht₀
  have hn₂ : n₁ (j + 1) + n₃ (j + 1) = (p'₁ + u₁ + p''₁) + m₂ + (p'₀ + u₀ + p''₀) := by omega
  have hN : n₁ (j + 1) + n₃ (j + 1) =
      ((p'₁ + u₁) + v₁ + p'₀) + (p''₁ + w₁ + (u₀ + p''₀)) := by omega
  have hcast : ((p'₁ + u₁) + v₁ + p'₀) + (p''₁ + w₁ + (u₀ + p''₀)) =
      ((p'₁ + u₁ + p''₁) + (v₁ + w₁)) + (p'₀ + (u₀ + p''₀)) := by omega
  rw [torsionBracketWithHomology_eq_det_append c₂ _ _ _ hz₂' _ _ hs₂ hn₂,
    coe_shortExactBoundaryBasisWithHomology,
    torsionBracketWithHomology_eq_det_append c₁ b'₁ _ _ hz₁' b'₀ s'₀ hs'₀ hn₁,
    torsionBracketWithHomology_eq_det_append c₃ b''₁ _ _ hz₃' b''₀ _ ht₀ hn₃]
  have hsw := ((c₂ (j + 1)).reindex (finCongr hN)).det.map_append_append_append_comm
    (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b'₁ k))
      fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (a₁_hi k)))
    (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k))
    (fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (y₁ k)))
    (fun k ↦ S.X₂.iCycles (j + 1) (z₂ k))
    (fun k ↦ (S.f.f (j + 1)).hom (s'₀ k)) (Fin.append aLift₀ t₀)
  rw [Basis.det_reindex, Basis.det_reindex] at hsw
  rw [adapted_append_reassoc hm₂ b'₁ a₁_hi t₁ y₁ z₂ s'₀ aLift₀ t₀ hn₂ hN hcast, hsw,
    Basis.eq_reindex_ofExactLift (hf (j + 1)) (hfg (j + 1)) (c₁ (j + 1)) (c₃ (j + 1)) _
      (hc₁ (j + 1)) (hc₃ (j + 1)), Basis.det_reindex,
    Basis.ofExactLift_det_eq_mul _ _ _ _ _ _ _ _ _
      (adapted_append_left_eq (hm₁ := hm₁) (b'₁ := b'₁) (a₁_hi := a₁_hi) (t₁ := t₁) (y₁ := y₁)
        (z₂ := z₂) (s'₀ := s'₀) (aLift₀ := aLift₀) (t₀ := t₀) hN hn₁)
      (adapted_append_right_eq (hm₃ := hm₃) (b'₁ := b'₁) (a₁_hi := a₁_hi) (b''₁ := b''₁) (t₁ := t₁)
        (ht₁ := ht₁) (y₁ := y₁) (z₂ := z₂) (s'₀ := s'₀) (aLift₀ := aLift₀) (aCycle₃ := aCycle₃)
        (hg₀ := hg₀) (t₀ := t₀) hN hn₃)]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

end AdaptedBracket

private def homologyBasisCycle (C : ChainComplex (ModuleCat F) ℤ) {m : ℤ → ℕ}
    (h : ∀ i, Basis (Fin (m i)) F (C.homology i)) (i : ℤ) (k : Fin (m i)) : C.cycles i :=
  Function.surjInv (C.moduleCat_homologyπ_surjective i) (h i k)

private theorem homologyBasisCycle_spec (C : ChainComplex (ModuleCat F) ℤ) {m : ℤ → ℕ}
    (h : ∀ i, Basis (Fin (m i)) F (C.homology i)) (i : ℤ) (k : Fin (m i)) :
    C.homologyπ i (homologyBasisCycle C h i k) = h i k :=
  Function.surjInv_eq (C.moduleCat_homologyπ_surjective i) _

private theorem hasFiniteMulSupport_bracket {C : ChainComplex (ModuleCat F) ℤ} {n m r : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (hn : {i | n i ≠ 0}.Finite)
    (b : ∀ j, Basis (Fin (r j)) F (LinearMap.range (C.d (j + 1) j).hom))
    (h : ∀ i, Basis (Fin (m i)) F (C.homology i))
    (y : ∀ i, Fin (m i) → C.cycles i) (hy : ∀ i k, C.homologyπ i (y i k) = h i k)
    (s : ∀ j, Fin (r j) → C.X (j + 1)) (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k) :
    Function.HasFiniteMulSupport fun j : ℤ ↦ torsionBracketWithHomology c (b (j + 1)) (h (j + 1))
      (y (j + 1)) (hy (j + 1)) (b j) (s j) (hs j) ^ (j.negOnePow : ℤ) :=
  (hn.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
    Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      rw [torsionBracketWithHomology_eq_one c _ _ _ _ _ _ _ (by simpa using hj), one_zpow]

private theorem reidemeisterTorsionWithHomology_eq_mul_of_not_finite
    {C₁ C₂ C₃ : ChainComplex (ModuleCat F) ℤ} {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (C₂.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (C₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i))
    (hn : ¬{i | n₁ i + n₃ i ≠ 0}.Finite) (ε τH : F) :
    C₂.reidemeisterTorsionWithHomology c₂ h₂ =
      ε * (C₁.reidemeisterTorsionWithHomology c₁ h₁ *
        C₃.reidemeisterTorsionWithHomology c₃ h₃ * τH) := by
  rw [reidemeisterTorsionWithHomology_of_not_finite C₂ c₂ h₂ hn]
  by_cases hn₁ : {i | n₁ i ≠ 0}.Finite
  · have hn₃ : ¬{i | n₃ i ≠ 0}.Finite := fun hn₃ ↦
      hn ((hn₁.union hn₃).subset fun i hi ↦ by
        simp only [Set.mem_union, Set.mem_ofPred_eq] at hi ⊢; omega)
    simp [reidemeisterTorsionWithHomology_of_not_finite C₃ c₃ h₃ hn₃]
  · simp [reidemeisterTorsionWithHomology_of_not_finite C₁ c₁ h₁ hn₁]

private theorem bracket_zpow_eq_of_mul {B₂ B₁ B₃ D₁ D₂ D₃ : F} (hD₂ : D₂ ≠ 0) (e : ℕ) (j : ℤ)
    (h : B₂ * D₂ = (-1 : F) ^ e * ((B₁ * D₁) * (B₃ * D₃))) :
    B₂ ^ (j.negOnePow : ℤ) =
      (-1 : F) ^ e * (B₁ ^ (j.negOnePow : ℤ) * B₃ ^ (j.negOnePow : ℤ) *
        (D₁ ^ (j.negOnePow : ℤ) * D₂ ^ ((j + 1).negOnePow : ℤ) * D₃ ^ (j.negOnePow : ℤ))) := by
  have hB₂ : B₂ = (-1 : F) ^ e * (B₁ * B₃ * (D₁ * D₂⁻¹ * D₃)) := by
    apply mul_right_cancel₀ hD₂
    calc B₂ * D₂ = (-1 : F) ^ e * ((B₁ * D₁) * (B₃ * D₃)) := h
      _ = (-1 : F) ^ e * (B₁ * B₃ * (D₁ * (D₂⁻¹ * D₂) * D₃)) := by
          rw [inv_mul_cancel₀ hD₂]; ring
      _ = (-1 : F) ^ e * (B₁ * B₃ * (D₁ * D₂⁻¹ * D₃)) * D₂ := by ring
  rw [hB₂, mul_zpow, mul_zpow, mul_zpow, mul_zpow, mul_zpow, inv_zpow, ← zpow_neg,
    Int.negOnePow_succ, Units.val_neg]
  congr 1
  rcases Int.units_eq_one_or j.negOnePow with hj | hj <;> simp [hj, ← inv_pow]

end Helpers

section Multiplicativity

variable {F : Type*} [Field F]

section Choices

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
  {m₁ m₂ m₃ : ℤ → ℕ} (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
  (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))

private def homRangeBasisδ (q : ℤ) :
    Basis (Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom))) F
      (LinearMap.range (hS.δ (q + 1) q rfl).hom) :=
  have : Module.Finite F (S.X₁.homology q) := .of_basis (h₁ q)
  finBasis F _

private def homRangeBasisf (q : ℤ) :
    Basis (Fin (finrank F (LinearMap.range (homologyMap S.f q).hom))) F
      (LinearMap.range (homologyMap S.f q).hom) :=
  have : Module.Finite F (S.X₂.homology q) := .of_basis (h₂ q)
  finBasis F _

private def homRangeBasisg (q : ℤ) :
    Basis (Fin (finrank F (LinearMap.range (homologyMap S.g q).hom))) F
      (LinearMap.range (homologyMap S.g q).hom) :=
  have : Module.Finite F (S.X₃.homology q) := .of_basis (h₃ q)
  finBasis F _

private def homLiftδ (q : ℤ)
    (l : Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom))) :
    S.X₃.homology (q + 1) :=
  Function.surjInv (hS.δ (q + 1) q rfl).hom.surjective_rangeRestrict
    (homRangeBasisδ hS h₁ q l)

private theorem homLiftδ_spec (q : ℤ) (l) :
    (hS.δ (q + 1) q rfl).hom (homLiftδ hS h₁ q l) = homRangeBasisδ hS h₁ q l :=
  congrArg Subtype.val
    (Function.surjInv_eq (hS.δ (q + 1) q rfl).hom.surjective_rangeRestrict _)

private def homLiftf (q : ℤ)
    (l : Fin (finrank F (LinearMap.range (homologyMap S.f q).hom))) : S.X₁.homology q :=
  Function.surjInv (homologyMap S.f q).hom.surjective_rangeRestrict (homRangeBasisf h₂ q l)

private theorem homLiftf_spec (q : ℤ) (l) :
    (homologyMap S.f q).hom (homLiftf h₂ q l) = homRangeBasisf h₂ q l :=
  congrArg Subtype.val (Function.surjInv_eq (homologyMap S.f q).hom.surjective_rangeRestrict _)

private def homLiftg (q : ℤ)
    (l : Fin (finrank F (LinearMap.range (homologyMap S.g q).hom))) : S.X₂.homology q :=
  Function.surjInv (homologyMap S.g q).hom.surjective_rangeRestrict (homRangeBasisg h₃ q l)

private theorem homLiftg_spec (q : ℤ) (l) :
    (homologyMap S.g q).hom (homLiftg h₃ q l) = homRangeBasisg h₃ q l :=
  congrArg Subtype.val (Function.surjInv_eq (homologyMap S.g q).hom.surjective_rangeRestrict _)

private def deltaCycle₁ (q : ℤ)
    (l : Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom))) : S.X₁.cycles q :=
  Function.surjInv (S.X₁.moduleCat_homologyπ_surjective q) (homRangeBasisδ hS h₁ q l)

private theorem deltaCycle₁_spec (q : ℤ) (l) :
    S.X₁.homologyπ q (deltaCycle₁ hS h₁ q l) = homRangeBasisδ hS h₁ q l :=
  Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective q) _

private theorem exists_deltaLift (q : ℤ)
    (l : Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom))) :
    ∃ (x₂ : S.X₂.X (q + 1)) (z₃ : S.X₃.cycles (q + 1)),
      (S.X₂.d (q + 1) q).hom x₂ = (S.f.f q).hom (S.X₁.iCycles q (deltaCycle₁ hS h₁ q l)) ∧
        (S.g.f (q + 1)).hom x₂ = S.X₃.iCycles (q + 1) z₃ ∧
          S.X₃.homologyπ (q + 1) z₃ = homLiftδ hS h₁ q l :=
  hS.moduleCat_exists_d_eq_of_δ_eq (q + 1) q rfl (homLiftδ hS h₁ q l)
    (deltaCycle₁ hS h₁ q l) ((homLiftδ_spec hS h₁ q l).trans (deltaCycle₁_spec hS h₁ q l).symm)

private def deltaLift₂ (q : ℤ)
    (l : Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom))) : S.X₂.X (q + 1) :=
  (exists_deltaLift hS h₁ q l).choose

private def deltaCycle₃ (q : ℤ)
    (l : Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom))) :
    S.X₃.cycles (q + 1) :=
  (exists_deltaLift hS h₁ q l).choose_spec.choose

private theorem deltaLift₂_d (q : ℤ) (l) :
    (S.X₂.d (q + 1) q).hom (deltaLift₂ hS h₁ q l) =
      (S.f.f q).hom (S.X₁.iCycles q (deltaCycle₁ hS h₁ q l)) :=
  (exists_deltaLift hS h₁ q l).choose_spec.choose_spec.1

private theorem deltaLift₂_g (q : ℤ) (l) :
    (S.g.f (q + 1)).hom (deltaLift₂ hS h₁ q l) = S.X₃.iCycles (q + 1) (deltaCycle₃ hS h₁ q l) :=
  (exists_deltaLift hS h₁ q l).choose_spec.choose_spec.2.1

private theorem deltaCycle₃_spec (q : ℤ) (l) :
    S.X₃.homologyπ (q + 1) (deltaCycle₃ hS h₁ q l) = homLiftδ hS h₁ q l :=
  (exists_deltaLift hS h₁ q l).choose_spec.choose_spec.2.2

private def homCyclef (q : ℤ)
    (l : Fin (finrank F (LinearMap.range (homologyMap S.f q).hom))) : S.X₁.cycles q :=
  Function.surjInv (S.X₁.moduleCat_homologyπ_surjective q) (homLiftf h₂ q l)

private theorem homCyclef_spec (q : ℤ) (l) :
    S.X₁.homologyπ q (homCyclef h₂ q l) = homLiftf h₂ q l :=
  Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective q) _

private def homCycleg (q : ℤ)
    (l : Fin (finrank F (LinearMap.range (homologyMap S.g q).hom))) : S.X₂.cycles q :=
  Function.surjInv (S.X₂.moduleCat_homologyπ_surjective q) (homLiftg h₃ q l)

private theorem homCycleg_spec (q : ℤ) (l) :
    S.X₂.homologyπ q (homCycleg h₃ q l) = homLiftg h₃ q l :=
  Function.surjInv_eq (S.X₂.moduleCat_homologyπ_surjective q) _

private def shortExactBoundaryLift₃ {n₃ : ℤ → ℕ} (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (j : ℤ) (k : Fin (finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom))) : S.X₂.X (j + 1) :=
  Function.surjInv
    (((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
      (j + 1)).moduleCat_surjective_g)
    (chosenBoundaryLift S.X₃ c₃ (j + 1) j k)

private theorem shortExactBoundaryLift₃_spec {n₃ : ℤ → ℕ}
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i)) (j : ℤ) (k) :
    (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (shortExactBoundaryLift₃ hS c₃ j k)) =
      chosenBoundaryBasis S.X₃ c₃ (j + 1) j k :=
  (congrArg (S.X₃.d (j + 1) j).hom
    (Function.surjInv_eq
      (((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
        (j + 1)).moduleCat_surjective_g) _)).trans
    (chosenBoundaryLift_spec S.X₃ c₃ (j + 1) j k)

include hS in
private theorem shortExact_injective_f (i : ℤ) : Function.Injective (S.f.f i).hom :=
  ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i).moduleCat_injective_f

include hS in
private theorem shortExact_exact_fg (i : ℤ) : Function.Exact (S.f.f i).hom (S.g.f i).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i).exact

private abbrev shortExactCombinedBoundaryBasis {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (j : ℤ) :=
  shortExactBoundaryBasisWithHomology hS (shortExact_injective_f hS) (shortExact_exact_fg hS)
    (chosenBoundaryBasis S.X₁ c₁ (j + 1) j) (homRangeBasisδ hS h₁ j) (deltaCycle₁ hS h₁ j)
    (deltaCycle₁_spec hS h₁ j) (deltaLift₂ hS h₁ j) (deltaLift₂_d hS h₁ j)
    (chosenBoundaryBasis S.X₃ c₃ (j + 1) j) (shortExactBoundaryLift₃ hS c₃ j)
    (shortExactBoundaryLift₃_spec hS c₃ j)

private abbrev shortExactCombinedBoundaryLift {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (j : ℤ) :=
  Fin.append (Fin.append
    (fun k ↦ (S.f.f (j + 1)).hom (chosenBoundaryLift S.X₁ c₁ (j + 1) j k)) (deltaLift₂ hS h₁ j))
    (shortExactBoundaryLift₃ hS c₃ j)

private theorem shortExactCombinedBoundaryLift_spec {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (j : ℤ) (k) :
    (S.X₂.d (j + 1) j).hom (shortExactCombinedBoundaryLift hS h₁ c₁ c₃ j k) =
      shortExactCombinedBoundaryBasis hS h₁ c₁ c₃ j k := by
  rw [shortExactCombinedBoundaryBasis,
    congrFun (coe_shortExactBoundaryBasisWithHomology hS _ _ _ _ _ _ _ _ _ _ _) k]
  induction k using Fin.addCases with
  | left k =>
    induction k using Fin.addCases <;>
      simp [shortExactCombinedBoundaryLift, Hom.comm_apply, chosenBoundaryLift_spec, deltaLift₂_d]
  | right k => simp [shortExactCombinedBoundaryLift]

include h₁ h₂ in
private theorem homCard₁ (q : ℤ) :
    m₁ q = finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom) +
      finrank F (LinearMap.range (homologyMap S.f q).hom) :=
  ChainComplex.interleave.card_eq_add_of_acyclic₁
    (X₁ := fun i ↦ S.X₁.homology i) (X₂ := fun i ↦ S.X₂.homology i)
    (X₃ := fun i ↦ S.X₃.homology i) (f := fun i ↦ homologyMap S.f i)
    (g := fun i ↦ homologyMap S.g i) (δ := fun i ↦ hS.δ (i + 1) i rfl)
    h₁ (homRangeBasisδ hS h₁) (homRangeBasisf h₂) hS.acyclic_homologySequenceComplex q

include hS h₂ h₃ in
private theorem homCard₂ (q : ℤ) :
    m₂ q = finrank F (LinearMap.range (homologyMap S.f q).hom) +
      finrank F (LinearMap.range (homologyMap S.g q).hom) :=
  ChainComplex.interleave.card_eq_add_of_acyclic₂
    (X₁ := fun i ↦ S.X₁.homology i) (X₂ := fun i ↦ S.X₂.homology i)
    (X₃ := fun i ↦ S.X₃.homology i) (f := fun i ↦ homologyMap S.f i)
    (g := fun i ↦ homologyMap S.g i) (δ := fun i ↦ hS.δ (i + 1) i rfl)
    h₂ (homRangeBasisf h₂) (homRangeBasisg h₃) hS.acyclic_homologySequenceComplex q

include h₁ h₃ in
private theorem homCard₃ (q : ℤ) :
    m₃ (q + 1) = finrank F (LinearMap.range (homologyMap S.g (q + 1)).hom) +
      finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom) :=
  ChainComplex.interleave.card_eq_add_of_acyclic₃
    (X₁ := fun i ↦ S.X₁.homology i) (X₂ := fun i ↦ S.X₂.homology i)
    (X₃ := fun i ↦ S.X₃.homology i) (f := fun i ↦ homologyMap S.f i)
    (g := fun i ↦ homologyMap S.g i) (δ := fun i ↦ hS.δ (i + 1) i rfl)
    h₃ (homRangeBasisδ hS h₁) (homRangeBasisg h₃) hS.acyclic_homologySequenceComplex q

private theorem hasFiniteMulSupport_homologyFactor (hm₁ : {i | m₁ i ≠ 0}.Finite)
    (hm₂ : {i | m₂ i ≠ 0}.Finite) (hm₃ : {i | m₃ i ≠ 0}.Finite) :
    Function.HasFiniteMulSupport fun j : ℤ ↦
      ((h₁ (j + 1)).det (Fin.append (fun l ↦ (homRangeBasisδ hS h₁ (j + 1) l :
          S.X₁.homology (j + 1))) (homLiftf h₂ (j + 1)) ∘
        Fin.cast (homCard₁ hS h₁ h₂ (j + 1)))) ^ (j.negOnePow : ℤ) *
      ((h₂ (j + 1)).det (Fin.append (fun l ↦ (homRangeBasisf h₂ (j + 1) l :
          S.X₂.homology (j + 1))) (homLiftg h₃ (j + 1)) ∘
        Fin.cast (homCard₂ hS h₂ h₃ (j + 1)))) ^ ((j + 1).negOnePow : ℤ) *
      ((h₃ (j + 1)).det (Fin.append (fun l ↦ (homRangeBasisg h₃ (j + 1) l :
          S.X₃.homology (j + 1))) (homLiftδ hS h₁ j) ∘
        Fin.cast (homCard₃ hS h₁ h₃ j))) ^ (j.negOnePow : ℤ) :=
  (((hm₁.union hm₂).union hm₃).preimage (add_left_injective (1 : ℤ)).injOn).subset <|
    Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hj
      have : IsEmpty (Fin (m₁ (j + 1))) := hj.1.1 ▸ inferInstance
      have : IsEmpty (Fin (m₂ (j + 1))) := hj.1.2 ▸ inferInstance
      have : IsEmpty (Fin (m₃ (j + 1))) := hj.2 ▸ inferInstance
      simp

private theorem hasFiniteMulSupport_koszulSign {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (hn₁ : {i | n₁ i ≠ 0}.Finite) (hn₃ : {i | n₃ i ≠ 0}.Finite) :
    Function.HasFiniteMulSupport fun j : ℤ ↦ (-1 : F) ^
      (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
        finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
      (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
        finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom)) *
        finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) :=
  ((hn₃.preimage (add_left_injective (1 : ℤ)).injOn).union hn₁).subset <|
    Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_not] at hj
      simp [finrank_range_d_eq_zero S.X₃ c₃ (j := j + 1) hj.1,
        finrank_range_d_eq_zero S.X₁ c₁ (j := j) hj.2]

private theorem adaptedCycle₁_spec (q : ℤ) (k : Fin (m₁ q)) :
    S.X₁.homologyπ q ((Fin.append (deltaCycle₁ hS h₁ q) (homCyclef h₂ q) ∘
      Fin.cast (homCard₁ hS h₁ h₂ q)) k) =
      adaptedHomologyBasis (hS.homology_exact₁ (q + 1) q rfl) (homCard₁ hS h₁ h₂ q)
        (homRangeBasisδ hS h₁ q) (homRangeBasisf h₂ q) (homLiftf h₂ q) (homLiftf_spec h₂ q) k := by
  rw [congrFun (coe_adaptedHomologyBasis _ _ _ _ _ _) k]
  obtain ⟨m, rfl⟩ := (finCongr (homCard₁ hS h₁ h₂ q).symm).surjective k
  induction m using Fin.addCases <;> simp [deltaCycle₁_spec, homCyclef_spec]

private theorem adaptedCycle₂_spec (q : ℤ) (k : Fin (m₂ q)) :
    S.X₂.homologyπ q ((Fin.append (fun l ↦ cyclesMap S.f q (homCyclef h₂ q l))
      (homCycleg h₃ q) ∘ Fin.cast (homCard₂ hS h₂ h₃ q)) k) =
      adaptedHomologyBasis (hS.homology_exact₂ q) (homCard₂ hS h₂ h₃ q)
        (homRangeBasisf h₂ q) (homRangeBasisg h₃ q) (homLiftg h₃ q) (homLiftg_spec h₃ q) k := by
  rw [congrFun (coe_adaptedHomologyBasis _ _ _ _ _ _) k]
  obtain ⟨m, rfl⟩ := (finCongr (homCard₂ hS h₂ h₃ q).symm).surjective k
  induction m using Fin.addCases <;>
    simp [← moduleCat_homologyMap_homologyπ, homCyclef_spec, homLiftf_spec, homCycleg_spec]

private theorem adaptedCycle₃_spec (j : ℤ) (k : Fin (m₃ (j + 1))) :
    S.X₃.homologyπ (j + 1) ((Fin.append (fun l ↦ cyclesMap S.g (j + 1) (homCycleg h₃ (j + 1) l))
      (deltaCycle₃ hS h₁ j) ∘ Fin.cast (homCard₃ hS h₁ h₃ j)) k) =
      adaptedHomologyBasis (hS.homology_exact₃ (j + 1) j rfl) (homCard₃ hS h₁ h₃ j)
        (homRangeBasisg h₃ (j + 1)) (homRangeBasisδ hS h₁ j) (homLiftδ hS h₁ j)
        (homLiftδ_spec hS h₁ j) k := by
  rw [congrFun (coe_adaptedHomologyBasis _ _ _ _ _ _) k]
  obtain ⟨m, rfl⟩ := (finCongr (homCard₃ hS h₁ h₃ j).symm).surjective k
  induction m using Fin.addCases <;>
    simp [← moduleCat_homologyMap_homologyπ, homCycleg_spec, homLiftg_spec, deltaCycle₃_spec]

private theorem torsionBracketWithHomology_change_homology {C : ChainComplex (ModuleCat F) ℤ}
    {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) {j : ℤ} {p m q : ℕ}
    (b₁ : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
    (h : Basis (Fin m) F (C.homology (j + 1)))
    (y : Fin m → C.cycles (j + 1)) (hy : ∀ k, C.homologyπ (j + 1) (y k) = h k)
    (h' : Basis (Fin m) F (C.homology (j + 1)))
    (y' : Fin m → C.cycles (j + 1)) (hy' : ∀ k, C.homologyπ (j + 1) (y' k) = h' k)
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom))
    (s : Fin q → C.X (j + 1)) (hs : ∀ k, (C.d (j + 1) j).hom (s k) = b₀ k) :
    torsionBracketWithHomology c b₁ h' y' hy' b₀ s hs =
      torsionBracketWithHomology c b₁ h y hy b₀ s hs * h.det h' := by
  rw [torsionBracketWithHomology_eq_mul c b₁ h y hy b₀ s hs]
  simp [Basis.det_self]

private theorem bracket_zpow_shortExact_eq {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k) (j : ℤ) :
    torsionBracketWithHomology c₂ (shortExactCombinedBoundaryBasis hS h₁ c₁ c₃ (j + 1))
        (h₂ (j + 1)) (homologyBasisCycle S.X₂ h₂ (j + 1))
        (homologyBasisCycle_spec S.X₂ h₂ (j + 1))
        (shortExactCombinedBoundaryBasis hS h₁ c₁ c₃ j)
        (shortExactCombinedBoundaryLift hS h₁ c₁ c₃ j)
        (shortExactCombinedBoundaryLift_spec hS h₁ c₁ c₃ j) ^ (j.negOnePow : ℤ) =
      (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
          finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) *
      (torsionBracketWithHomology c₁ (chosenBoundaryBasis S.X₁ c₁ (j + 1 + 1) (j + 1))
          (h₁ (j + 1)) (homologyBasisCycle S.X₁ h₁ (j + 1))
          (homologyBasisCycle_spec S.X₁ h₁ (j + 1))
          (chosenBoundaryBasis S.X₁ c₁ (j + 1) j) (chosenBoundaryLift S.X₁ c₁ (j + 1) j)
          (chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j) ^ (j.negOnePow : ℤ) *
        torsionBracketWithHomology c₃ (chosenBoundaryBasis S.X₃ c₃ (j + 1 + 1) (j + 1))
          (h₃ (j + 1)) (homologyBasisCycle S.X₃ h₃ (j + 1))
          (homologyBasisCycle_spec S.X₃ h₃ (j + 1))
          (chosenBoundaryBasis S.X₃ c₃ (j + 1) j)
          (fun k ↦ (S.g.f (j + 1)).hom (shortExactBoundaryLift₃ hS c₃ j k))
          (shortExactBoundaryLift₃_spec hS c₃ j) ^ (j.negOnePow : ℤ) *
        (((h₁ (j + 1)).det (Fin.append (fun l ↦ (homRangeBasisδ hS h₁ (j + 1) l :
            S.X₁.homology (j + 1))) (homLiftf h₂ (j + 1)) ∘
          Fin.cast (homCard₁ hS h₁ h₂ (j + 1)))) ^ (j.negOnePow : ℤ) *
        ((h₂ (j + 1)).det (Fin.append (fun l ↦ (homRangeBasisf h₂ (j + 1) l :
            S.X₂.homology (j + 1))) (homLiftg h₃ (j + 1)) ∘
          Fin.cast (homCard₂ hS h₂ h₃ (j + 1)))) ^ ((j + 1).negOnePow : ℤ) *
        ((h₃ (j + 1)).det (Fin.append (fun l ↦ (homRangeBasisg h₃ (j + 1) l :
            S.X₃.homology (j + 1))) (homLiftδ hS h₁ j) ∘
          Fin.cast (homCard₃ hS h₁ h₃ j))) ^ (j.negOnePow : ℤ))) := by
  have hadapt := torsionBracketWithHomology_shortExact_adapted hS (shortExact_injective_f hS)
    (shortExact_exact_fg hS) hc₁ hc₃ _ _ _
    (chosenBoundaryBasis S.X₁ c₁ (j + 1 + 1) (j + 1)) (homRangeBasisδ hS h₁ (j + 1))
    (deltaCycle₁ hS h₁ (j + 1)) (deltaCycle₁_spec hS h₁ (j + 1))
    (deltaLift₂ hS h₁ (j + 1)) (deltaLift₂_d hS h₁ (j + 1))
    (chosenBoundaryBasis S.X₃ c₃ (j + 1 + 1) (j + 1)) (shortExactBoundaryLift₃ hS c₃ (j + 1))
    (shortExactBoundaryLift₃_spec hS c₃ (j + 1))
    (homRangeBasisf h₂ (j + 1)) (homLiftf h₂ (j + 1)) (homLiftf_spec h₂ (j + 1))
    (homCyclef h₂ (j + 1))
    (homRangeBasisg h₃ (j + 1)) (homLiftg h₃ (j + 1)) (homLiftg_spec h₃ (j + 1))
    (homCycleg h₃ (j + 1))
    (chosenBoundaryBasis S.X₁ c₁ (j + 1) j) (chosenBoundaryLift S.X₁ c₁ (j + 1) j)
    (chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j)
    (homRangeBasisδ hS h₁ j) (homLiftδ hS h₁ j) (homLiftδ_spec hS h₁ j)
    (deltaCycle₁ hS h₁ j) (deltaCycle₁_spec hS h₁ j) (deltaLift₂ hS h₁ j) (deltaLift₂_d hS h₁ j)
    (deltaCycle₃ hS h₁ j) (deltaLift₂_g hS h₁ j)
    (chosenBoundaryBasis S.X₃ c₃ (j + 1) j) (shortExactBoundaryLift₃ hS c₃ j)
    (shortExactBoundaryLift₃_spec hS c₃ j)
    (adaptedCycle₁_spec hS h₁ h₂ (j + 1)) (adaptedCycle₂_spec hS h₂ h₃ (j + 1))
    (adaptedCycle₃_spec hS h₁ h₃ j) (shortExactCombinedBoundaryLift_spec hS h₁ c₁ c₃ j)
  have h_eq₂ := torsionBracketWithHomology_change_homology c₂
    (shortExactCombinedBoundaryBasis hS h₁ c₁ c₃ (j + 1))
    (h₂ (j + 1)) (homologyBasisCycle S.X₂ h₂ (j + 1)) (homologyBasisCycle_spec S.X₂ h₂ (j + 1))
    _ _ (adaptedCycle₂_spec hS h₂ h₃ (j + 1)) (shortExactCombinedBoundaryBasis hS h₁ c₁ c₃ j)
    (shortExactCombinedBoundaryLift hS h₁ c₁ c₃ j)
    (shortExactCombinedBoundaryLift_spec hS h₁ c₁ c₃ j)
  have h_eq₁ := torsionBracketWithHomology_change_homology c₁
    (chosenBoundaryBasis S.X₁ c₁ (j + 1 + 1) (j + 1))
    (h₁ (j + 1)) (homologyBasisCycle S.X₁ h₁ (j + 1)) (homologyBasisCycle_spec S.X₁ h₁ (j + 1))
    _ _ (adaptedCycle₁_spec hS h₁ h₂ (j + 1)) (chosenBoundaryBasis S.X₁ c₁ (j + 1) j)
    (chosenBoundaryLift S.X₁ c₁ (j + 1) j) (chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j)
  have h_eq₃ := torsionBracketWithHomology_change_homology c₃
    (chosenBoundaryBasis S.X₃ c₃ (j + 1 + 1) (j + 1))
    (h₃ (j + 1)) (homologyBasisCycle S.X₃ h₃ (j + 1)) (homologyBasisCycle_spec S.X₃ h₃ (j + 1))
    _ _ (adaptedCycle₃_spec hS h₁ h₃ j) (chosenBoundaryBasis S.X₃ c₃ (j + 1) j)
    (fun k ↦ (S.g.f (j + 1)).hom (shortExactBoundaryLift₃ hS c₃ j k))
    (shortExactBoundaryLift₃_spec hS c₃ j)
  have hmul := (h_eq₂.symm.trans hadapt).trans (congrArg (_ * ·) (congrArg₂ (· * ·) h_eq₁ h_eq₃))
  simp only [coe_adaptedHomologyBasis] at hmul
  refine bracket_zpow_eq_of_mul ?_ _ j hmul
  rw [← coe_adaptedHomologyBasis (hS.homology_exact₂ (j + 1)) _
    (homRangeBasisf h₂ (j + 1)) (homRangeBasisg h₃ (j + 1)) (homLiftg h₃ (j + 1))
    (homLiftg_spec h₃ (j + 1))]
  exact (Basis.isUnit_det _ _).ne_zero

end Choices

/-- **Multiplicativity of Reidemeister torsion through the long exact homology sequence.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of vector
spaces over `F`, with compatible chain bases `c₁`, `c₂`, `c₃` and homology bases `h₁`, `h₂`, `h₃`.
Then `τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H)`, where `H` is the based
long exact homology sequence `hS.homologySequenceComplex` and
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim im f_*,ⱼ₊₁ + (dim B₃,ⱼ₊₁ + dim im g_*,ⱼ₊₁) · dim B₁,ⱼ)`. This
also holds when `S.X₂` is unbounded, both sides being `0`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    {m₁ m₂ m₃ : ℤ → ℕ} (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
          finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
        hS.homologySequenceComplex.reidemeisterTorsion
          (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃)) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · exact reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ h₁ h₂ h₃ hn _ _
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hn₃ : {i | n₃ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hm₁ := finite_homology_of_finite c₁ h₁ hn₁
  have hm₂ := finite_homology_of_finite c₂ h₂ hn
  have hm₃ := finite_homology_of_finite c₃ h₃ hn₃
  have hτ₁ := hasFiniteMulSupport_bracket c₁ hn₁ (fun j ↦ chosenBoundaryBasis S.X₁ c₁ (j + 1) j) h₁
    (homologyBasisCycle S.X₁ h₁) (homologyBasisCycle_spec S.X₁ h₁)
    (fun j ↦ chosenBoundaryLift S.X₁ c₁ (j + 1) j)
    (fun j ↦ chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j)
  have hτ₃ := hasFiniteMulSupport_bracket c₃ hn₃ (fun j ↦ chosenBoundaryBasis S.X₃ c₃ (j + 1) j) h₃
    (homologyBasisCycle S.X₃ h₃) (homologyBasisCycle_spec S.X₃ h₃)
    (fun j k ↦ (S.g.f (j + 1)).hom (shortExactBoundaryLift₃ hS c₃ j k))
    (shortExactBoundaryLift₃_spec hS c₃)
  have hτH := hasFiniteMulSupport_homologyFactor hS h₁ h₂ h₃ hm₁ hm₂ hm₃
  have hε := hasFiniteMulSupport_koszulSign c₁ c₃ hn₁ hn₃
  rw [reidemeisterTorsionWithHomology_eq_finprod hn (shortExactCombinedBoundaryBasis hS h₁ c₁ c₃)
      (homologyBasisCycle S.X₂ h₂) (homologyBasisCycle_spec S.X₂ h₂)
      (shortExactCombinedBoundaryLift hS h₁ c₁ c₃)
      (shortExactCombinedBoundaryLift_spec hS h₁ c₁ c₃),
    reidemeisterTorsionWithHomology_eq_finprod hn₁ (fun j ↦ chosenBoundaryBasis S.X₁ c₁ (j + 1) j)
      (homologyBasisCycle S.X₁ h₁) (homologyBasisCycle_spec S.X₁ h₁)
      (fun j ↦ chosenBoundaryLift S.X₁ c₁ (j + 1) j)
      (fun j ↦ chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j),
    reidemeisterTorsionWithHomology_eq_finprod hn₃ (fun j ↦ chosenBoundaryBasis S.X₃ c₃ (j + 1) j)
      (homologyBasisCycle S.X₃ h₃) (homologyBasisCycle_spec S.X₃ h₃)
      (fun j k ↦ (S.g.f (j + 1)).hom (shortExactBoundaryLift₃ hS c₃ j k))
      (shortExactBoundaryLift₃_spec hS c₃),
    ChainComplex.interleave.reidemeisterTorsion_eq_finprod h₁ h₂ h₃
      (homRangeBasisδ hS h₁) (homRangeBasisf h₂) (homRangeBasisg h₃) hm₁ hm₂ hm₃
      hS.acyclic_homologySequenceComplex (homLiftδ hS h₁) (homLiftδ_spec hS h₁)
      (homLiftf h₂) (homLiftf_spec h₂) (homLiftg h₃) (homLiftg_spec h₃),
    ← finprod_mul_distrib hτ₁ hτ₃, ← finprod_mul_distrib (hτ₁.fun_mul hτ₃) hτH,
    ← finprod_mul_distrib hε ((hτ₁.fun_mul hτ₃).fun_mul hτH)]
  exact finprod_congr (bracket_zpow_shortExact_eq hS h₁ h₂ h₃ c₁ c₃ c₂ hc₁ hc₃)

section AcyclicSpecializations

private def emptyHomologyBasis {C : ChainComplex (ModuleCat F) ℤ} (hC : C.Acyclic) (i : ℤ) :
    Basis (Fin 0) F (C.homology i) :=
  have := ModuleCat.subsingleton_of_isZero (hC i).isZero_homology
  Basis.empty _

private theorem finrank_range_eq_zero_of_domain_subsingleton {M N : Type*} [AddCommGroup M]
    [Module F M] [AddCommGroup N] [Module F N] [Subsingleton M] (φ : M →ₗ[F] N) :
    finrank F (LinearMap.range φ) = 0 := by
  have : Subsingleton (LinearMap.range φ) :=
    ⟨fun ⟨_, x, hx⟩ ⟨_, y, hy⟩ ↦
      Subtype.ext (hx.symm.trans ((congrArg φ (Subsingleton.elim x y)).trans hy))⟩
  exact finrank_zero_of_subsingleton

/-- When the middle complex `S.X₂` of a short exact sequence is acyclic, the connecting
homomorphism `hS.δ (i + 1) i rfl : Hᵢ₊₁(S.X₃) ⟶ Hᵢ(S.X₁)` is an isomorphism, so `m₃ (i + 1) = m₁ i`.
-/
theorem card_eq_of_shortExact_of_acyclic_X₂ {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
    (hS : S.ShortExact) (hX₂ : S.X₂.Acyclic) {m₁ m₃ : ℤ → ℕ}
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) (i : ℤ) :
    m₃ (i + 1) = m₁ i :=
  ChainComplex.interleave.card_eq_of_eq_zero₂ h₁ (emptyHomologyBasis hX₂) h₃ (fun _ ↦ rfl)
    hS.acyclic_homologySequenceComplex i

/-- **Multiplicativity of Reidemeister torsion when `S.X₂` is acyclic.** The torsion of `S.X₂` is
the product of the homology-based torsions of `S.X₁` and `S.X₃`, the Koszul sign
`∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim B₁,ⱼ)`, and the alternating product of the determinants of the
connecting isomorphisms `hS.δ (i + 1) i rfl : Hᵢ₊₁(S.X₃) ⟶ Hᵢ(S.X₁)`. -/
theorem reidemeisterTorsion_eq_mul_of_shortExact_of_acyclic_X₂
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (hX₂ : S.X₂.Acyclic) {m₁ m₃ : ℤ → ℕ}
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsion c₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
        ∏ᶠ i : ℤ, ((h₁ i).det fun k ↦ (hS.δ (i + 1) i rfl).hom
          (h₃ (i + 1) (Fin.cast (card_eq_of_shortExact_of_acyclic_X₂ hS hX₂ h₁ h₃ i).symm k))) ^
          ((i + 1).negOnePow : ℤ)) := by
  rw [← reidemeisterTorsionWithHomology_eq_reidemeisterTorsion (c := c₂)
    (h := emptyHomologyBasis hX₂) hX₂]
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · exact reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ h₁
      (emptyHomologyBasis hX₂) h₃ hn _ _
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  rw [reidemeisterTorsionWithHomology_eq_mul_of_shortExact hS c₁ c₃ c₂ hc₁ hc₃ h₁
      (emptyHomologyBasis hX₂) h₃,
    ChainComplex.interleave.reidemeisterTorsion_of_eq_zero₂ h₁ (emptyHomologyBasis hX₂) h₃
      (finite_homology_of_finite c₁ h₁ hn₁) (fun _ ↦ rfl) hS.acyclic_homologySequenceComplex]
  refine congrArg (· * _) (finprod_congr fun j ↦ congrArg ((-1 : F) ^ ·) ?_)
  have := ModuleCat.subsingleton_of_isZero (hX₂ (j + 1)).isZero_homology
  simp [finrank_zero_of_subsingleton, finrank_range_eq_zero_of_domain_subsingleton]

/-- When the quotient complex `S.X₃` of a short exact sequence is acyclic, `S.f` is a
quasi-isomorphism, so `m₁ i = m₂ i`. -/
theorem card_eq_of_shortExact_of_acyclic_X₃ {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
    (hS : S.ShortExact) (hX₃ : S.X₃.Acyclic) {m₁ m₂ : ℤ → ℕ}
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i)) (i : ℤ) :
    m₁ i = m₂ i :=
  ChainComplex.interleave.card_eq_of_eq_zero₃ h₁ h₂ (emptyHomologyBasis hX₃) (fun _ ↦ rfl)
    hS.acyclic_homologySequenceComplex i

/-- **Multiplicativity of Reidemeister torsion when `S.X₃` is acyclic.** Then `S.f : S.X₁ ⟶ S.X₂`
is an injective quasi-isomorphism, and the homology sequence torsion reduces to the alternating
product of the determinants of `homologyMap S.f i : Hᵢ(S.X₁) ⟶ Hᵢ(S.X₂)`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₃
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (hX₃ : S.X₃.Acyclic) {m₁ m₂ : ℤ → ℕ}
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          (m₁ (j + 1) + finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsion c₃ *
        ∏ᶠ i : ℤ, ((h₂ i).det fun k ↦ (homologyMap S.f i).hom
          (h₁ i (Fin.cast (card_eq_of_shortExact_of_acyclic_X₃ hS hX₃ h₁ h₂ i).symm k))) ^
          (i.negOnePow : ℤ)) := by
  rw [← reidemeisterTorsionWithHomology_eq_reidemeisterTorsion (c := c₃)
    (h := emptyHomologyBasis hX₃) hX₃]
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · exact reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ h₁ h₂
      (emptyHomologyBasis hX₃) hn _ _
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  rw [reidemeisterTorsionWithHomology_eq_mul_of_shortExact hS c₁ c₃ c₂ hc₁ hc₃ h₁ h₂
      (emptyHomologyBasis hX₃),
    ChainComplex.interleave.reidemeisterTorsion_of_eq_zero₃ h₁ h₂ (emptyHomologyBasis hX₃)
      (finite_homology_of_finite c₁ h₁ hn₁) (fun _ ↦ rfl) hS.acyclic_homologySequenceComplex]
  refine congrArg (· * _) (finprod_congr fun j ↦ congrArg ((-1 : F) ^ ·) ?_)
  have := ModuleCat.subsingleton_of_isZero (hX₃ (j + 1)).isZero_homology
  have hrf : LinearMap.range (homologyMap S.f (j + 1)).hom = ⊤ := by
    rw [(ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (hS.homology_exact₂ (j + 1)),
      eq_top_iff]
    intro x _
    exact LinearMap.mem_ker.2 (Subsingleton.elim _ _)
  have hf_rk : finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) = m₁ (j + 1) := by
    rw [hrf, finrank_top, finrank_eq_card_basis (h₂ (j + 1)), Fintype.card_fin,
      card_eq_of_shortExact_of_acyclic_X₃ hS hX₃ h₁ h₂ (j + 1)]
  have hg_rk : finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom) = 0 :=
    finrank_zero_of_subsingleton
  rw [hf_rk, hg_rk, add_zero, ← mul_add]

/-- When the subcomplex `S.X₁` of a short exact sequence is acyclic, `S.g` is a quasi-isomorphism,
so `m₂ i = m₃ i`. -/
theorem card_eq_of_shortExact_of_acyclic_X₁ {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
    (hS : S.ShortExact) (hX₁ : S.X₁.Acyclic) {m₂ m₃ : ℤ → ℕ}
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) (i : ℤ) :
    m₂ i = m₃ i :=
  ChainComplex.interleave.card_eq_of_eq_zero₁ (emptyHomologyBasis hX₁) h₂ h₃ (fun _ ↦ rfl)
    hS.acyclic_homologySequenceComplex i

/-- **Multiplicativity of Reidemeister torsion when `S.X₁` is acyclic.** Then `S.g : S.X₂ ⟶ S.X₃`
is a surjective quasi-isomorphism, and the homology sequence torsion reduces to the alternating
product of the determinants of `homologyMap S.g i : Hᵢ(S.X₂) ⟶ Hᵢ(S.X₃)`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₁
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (hX₁ : S.X₁.Acyclic) {m₂ m₃ : ℤ → ℕ}
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        ((finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + m₂ (j + 1)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsion c₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
        ∏ᶠ i : ℤ, ((h₃ i).det fun k ↦ (homologyMap S.g i).hom
          (h₂ i (Fin.cast (card_eq_of_shortExact_of_acyclic_X₁ hS hX₁ h₂ h₃ i).symm k))) ^
          ((i + 1).negOnePow : ℤ)) := by
  rw [← reidemeisterTorsionWithHomology_eq_reidemeisterTorsion (c := c₁)
    (h := emptyHomologyBasis hX₁) hX₁]
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · exact reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂
      (emptyHomologyBasis hX₁) h₂ h₃ hn _ _
  rw [reidemeisterTorsionWithHomology_eq_mul_of_shortExact hS c₁ c₃ c₂ hc₁ hc₃
      (emptyHomologyBasis hX₁) h₂ h₃,
    ChainComplex.interleave.reidemeisterTorsion_of_eq_zero₁ (emptyHomologyBasis hX₁) h₂ h₃
      (finite_homology_of_finite c₂ h₂ hn) (fun _ ↦ rfl) hS.acyclic_homologySequenceComplex]
  refine congrArg (· * _) (finprod_congr fun j ↦ congrArg ((-1 : F) ^ ·) ?_)
  have := ModuleCat.subsingleton_of_isZero (hX₁ (j + 1)).isZero_homology
  have := ModuleCat.subsingleton_of_isZero (hX₁ j).isZero_homology
  have hrg : LinearMap.range (homologyMap S.g (j + 1)).hom = ⊤ := by
    rw [(ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (hS.homology_exact₃ (j + 1) j rfl),
      eq_top_iff]
    intro x _
    exact LinearMap.mem_ker.2 (Subsingleton.elim _ _)
  have hg_rk : finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom) = m₂ (j + 1) := by
    rw [hrg, finrank_top, finrank_eq_card_basis (h₃ (j + 1)), Fintype.card_fin,
      ← card_eq_of_shortExact_of_acyclic_X₁ hS hX₁ h₂ h₃ (j + 1)]
  rw [finrank_range_eq_zero_of_domain_subsingleton (homologyMap S.f (j + 1)).hom, mul_zero,
    zero_add, hg_rk]

end AcyclicSpecializations

end Multiplicativity

end HomologicalComplex

