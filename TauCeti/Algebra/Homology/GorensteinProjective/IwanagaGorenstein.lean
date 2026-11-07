/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.TotallyReflexive
public import TauCeti.Algebra.Homology.Ext.Syzygy
public import TauCeti.Algebra.Module.AuslanderReiten.Equivalence
public import TauCeti.Algebra.Module.AuslanderReiten.RightTorsionfree
public import TauCeti.CategoryTheory.Exact.Stable.Ext
public import TauCeti.RingTheory.IwanagaGorenstein

/-!
# Gorenstein-projective modules over Iwanaga–Gorenstein rings

Over an Iwanaga–Gorenstein ring `A`, a finitely generated module `M` is Gorenstein-projective
exactly when `Ext^i(M, A) = 0` for all `i > 0`. Gorenstein-projective modules always have this
property; the content is the converse, which goes through Auslander–Bridger theory.

* **Auslander–Bridger, Proposition (3.8)**: `M` is totally reflexive exactly when
  `Ext^{>0}(M, A) = 0` and `Ext^{>0}(Tr M, A) = 0`. Reflexivity is the vanishing of
  `Ext¹(Tr M, A)` and `Ext²(Tr M, A)` (`TauCeti.opDualEval_bijective_iff_ext_eq_zero`), and
  `Ext^{n+1}(M*, A) ≅ Ext^{n+3}(Tr M, A)` by dimension shifting.
* If `Ext^{>0}(M, A) = 0`, then the transpose `Tr M` is `k`-torsionfree for every `k`: its own
  transpose `Tr Tr M` is stably isomorphic to `M` (`TauCeti.stableTransposeEquivalence`), and
  `Ext^{>0}(-, A)` is invariant under stable isomorphism
  (`TauCeti.ext_eq_zero_of_projectiveStableFunctor_iso`).
* So `Tr M` is a `k`-th syzygy for every `k`
  (`TauCeti.FiniteProjectivePresentation.isSyzygy_of_ext_rightTranspose_eq_zero`). Taking `k` to be
  the injective dimension `d` of the right module `A`, a `d`-th syzygy has no higher extensions by
  `A` (`CategoryTheory.ObjectProperty.IsSyzygy.ext_eq_zero_of_hasInjectiveDimensionLE`). Hence
  `Ext^{>0}(Tr M, A) = 0`, `M` is totally reflexive, and so Gorenstein-projective
  (`TauCeti.IsTotallyReflexive.isGorensteinProjective`).

## Main results

* `TauCeti.isTotallyReflexive_iff_ext_eq_zero_and_ext_transpose_eq_zero`: Auslander–Bridger's
  characterization of totally reflexive modules by `Ext` of `M` and of `Tr M`.
* `TauCeti.isGorensteinProjective_iff_ext_eq_zero`: over an Iwanaga–Gorenstein ring, the
  Gorenstein-projective modules are the finitely generated modules `M` with `Ext^{>0}(M, A) = 0`.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969),
  Proposition (3.8), (b) ⇔ (c), and Theorem (2.17).
-/

public section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace TauCeti

variable {A : Type u} [Ring A]

/-- **Auslander–Bridger**: a finitely generated module `M` with `Ext^{>0}(M, A) = 0` whose
transpose also satisfies `Ext^{>0}(Tr M, A) = 0` is totally reflexive. Reflexivity is
`Ext¹(Tr M, A) = Ext²(Tr M, A) = 0` (`TauCeti.opDualEval_bijective_iff_ext_eq_zero`), and
`Ext^{n+1}(M*, A) ≅ Ext^{n+3}(Tr M, A)` by dimension shifting along
`0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` and `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0`. -/
theorem isTotallyReflexive_of_ext_transpose_eq_zero {M : ModuleCat.{u} A} [Module.Finite A M]
    (P : FiniteProjectivePresentation M)
    (hM : ∀ (n : ℕ) (e : Ext.{u} M (ModuleCat.of A A) (n + 1)), e = 0)
    (hT : ∀ (n : ℕ) (e : Ext.{u} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
      (ModuleCat.of Aᵐᵒᵖ A) (n + 1)), e = 0) :
    IsTotallyReflexive A M where
  finite := inferInstance
  bijective_opDualEval :=
    (opDualEval_bijective_iff_ext_eq_zero P.exact P.surjective).2 ⟨hT 0, hT 1⟩
  ext_eq_zero := hM
  ext_dual_eq_zero n e := by
    have h₁ := AuslanderReitenTranspose.shortComplex_shortExact P.p
    have h₂ := AuslanderReitenTranspose.dualShortComplex_shortExact P.exact P.surjective
    exact h₂.ext_X₁_eq_zero_of_ext_X₃_eq_zero
      (h₁.ext_X₁_eq_zero_of_ext_X₃_eq_zero (hT (n + 2))) e

/-- **Auslander–Bridger, Proposition (3.8), (b) ⇔ (c)**: a finitely generated module `M` is totally
reflexive exactly when `Ext^{>0}(M, A) = 0` and `Ext^{>0}(Tr M, A) = 0`, for the transpose `Tr M`
of any finite projective presentation of `M`. -/
theorem isTotallyReflexive_iff_ext_eq_zero_and_ext_transpose_eq_zero {M : ModuleCat.{u} A}
    (P : FiniteProjectivePresentation M) :
    IsTotallyReflexive A M ↔ Module.Finite A M ∧
      (∀ (n : ℕ) (e : Ext.{u} M (ModuleCat.of A A) (n + 1)), e = 0) ∧
      ∀ (n : ℕ) (e : Ext.{u} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
        (ModuleCat.of Aᵐᵒᵖ A) (n + 1)), e = 0 := by
  refine ⟨fun hM ↦ ⟨hM.finite, hM.ext_eq_zero, fun n e ↦ ?_⟩, fun ⟨_, hM, hT⟩ ↦
    isTotallyReflexive_of_ext_transpose_eq_zero P hM hT⟩
  obtain ⟨h1, h2⟩ := (opDualEval_bijective_iff_ext_eq_zero P.exact P.surjective).1
    hM.bijective_opDualEval
  have h₁ := AuslanderReitenTranspose.shortComplex_shortExact P.p
  have h₂ := AuslanderReitenTranspose.dualShortComplex_shortExact P.exact P.surjective
  match n with
  | 0 => exact h1 e
  | 1 => exact h2 e
  | n + 2 =>
    exact h₁.ext_X₃_eq_zero_of_ext_X₁_eq_zero
      (h₂.ext_X₃_eq_zero_of_ext_X₁_eq_zero (hM.ext_dual_eq_zero n)) e

/-- **Over an Iwanaga–Gorenstein ring, `⊥A` consists of Gorenstein-projective modules**: a
finitely generated module `M` with `Ext^{n+1}(M, A) = 0` for all `n` is Gorenstein-projective. -/
theorem isGorensteinProjective_of_ext_eq_zero [IsIwanagaGorenstein A] (M : ModuleCat.{u} A)
    [Module.Finite A M] (hM : ∀ (n : ℕ) (e : Ext.{u} M (ModuleCat.of A A) (n + 1)), e = 0) :
    IsGorensteinProjective A M := by
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  -- The Auslander–Bridger stable duality, with chosen presentations.
  let PP : ∀ X : FinitelyPresentedStableModule.{u, u} A, FiniteProjectivePresentation X.obj.as :=
    fun X ↦ letI := X.property; FiniteProjectivePresentation.ofFinitePresentation
  let QQ : ∀ X : FinitelyPresentedStableModule.{u, u} Aᵐᵒᵖ,
      FiniteProjectivePresentation X.obj.as :=
    fun X ↦ letI := X.property; FiniteProjectivePresentation.ofFinitePresentation
  let M' : FinitelyPresentedStableModule.{u, u} A :=
    ⟨(ExactStructure.abelian (ModuleCat A)).projectiveStableFunctor.obj M, this⟩
  let P : FiniteProjectivePresentation M := PP M'
  let N := ((stableTransposeFunctor PP).obj M').unop
  have hN : N.obj.as = ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p) := by
    simp only [N, stableTransposeFunctor_obj, Opposite.unop_op]
    rfl
  let Q : FiniteProjectivePresentation N.obj.as := QQ N
  -- `M` is stably isomorphic to the double transpose `Tr Tr M`, the right transpose of `Q`.
  have e : (ExactStructure.abelian (ModuleCat A)).projectiveStableFunctor.obj M ≅
      (ExactStructure.abelian (ModuleCat A)).projectiveStableFunctor.obj Q.rightTranspose := by
    have e₀ := (ObjectProperty.ι _).mapIso ((stableTransposeUnitIso PP QQ).app M')
    dsimp only [Functor.id_obj, Functor.comp_obj, ObjectProperty.ι_obj] at e₀
    exact e₀ ≪≫ eqToIso (congrArg ObjectProperty.FullSubcategory.obj
      (stableTransposeInverse_obj.{u, u} PP QQ ((stableTransposeFunctor PP).obj M')))
  have hTT : ∀ (n : ℕ) (x : Ext.{u} Q.rightTranspose (ModuleCat.of A A) (n + 1)), x = 0 :=
    fun n ↦ ext_eq_zero_of_projectiveStableFunctor_iso e.symm (hM n)
  -- So `Tr M` is a `d`-th syzygy of right modules, hence has no higher extensions by `A`.
  obtain ⟨d, hd⟩ := IsIwanagaGorenstein.exists_hasInjectiveDimensionLE_op (A := A)
  have hsyz := Q.isSyzygy_of_ext_rightTranspose_eq_zero d fun i hi _ ↦ by
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by lia⟩
    exact hTT n
  have hT : ∀ (n : ℕ) (x : Ext.{u} N.obj.as (ModuleCat.of Aᵐᵒᵖ A) (n + 1)), x = 0 :=
    fun n ↦ hsyz.ext_eq_zero_of_hasInjectiveDimensionLE
      (fun X hX ↦ (IsProjective.iff_projective (R := Aᵐᵒᵖ) X).1 hX.2) (ModuleCat.of Aᵐᵒᵖ A) n
  rw [hN] at hT
  exact (isTotallyReflexive_of_ext_transpose_eq_zero P hM hT).isGorensteinProjective

/-- **Over an Iwanaga–Gorenstein ring, the Gorenstein-projective modules are `⊥A`**: a module is
Gorenstein-projective exactly when it is finitely generated with `Ext^{n+1}(M, A) = 0` for all
`n`. -/
theorem isGorensteinProjective_iff_ext_eq_zero [IsIwanagaGorenstein A] (M : ModuleCat.{u} A) :
    IsGorensteinProjective A M ↔
      Module.Finite A M ∧ ∀ (n : ℕ) (e : Ext.{u} M (ModuleCat.of A A) (n + 1)), e = 0 :=
  ⟨fun hM ↦ ⟨hM.finite, fun _ e ↦ hM.ext_eq_zero _ e⟩, fun ⟨_, hM⟩ ↦
    isGorensteinProjective_of_ext_eq_zero M hM⟩

end TauCeti
