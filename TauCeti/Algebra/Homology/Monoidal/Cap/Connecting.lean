/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Abelian.Refinements
public import TauCeti.Algebra.Homology.Monoidal.Cap.Basic

/-!
# Cap products and connecting morphisms

Let `0 ⟶ E₁ ⟶ E₂ ⟶ E₃ ⟶ 0` and `0 ⟶ B₁' ⟶ B₂' ⟶ B₃' ⟶ 0` be short exact sequences of chain
complexes in a `k`-linear abelian monoidal category, and suppose that each `Eᵢ` caps cochains to
`Bᵢ'` along a diagonal `Dᵢ` and an action `aᵢ` (`TauCeti.ChainComplex.cap`), compatibly with the
maps of the two sequences: `E₂` and `E₃` cap cochains on the same complex `A`, and `E₁` caps
cochains on a complex `A₁` mapping to `A` by `f`. This is the situation of the cap product with an
absolute cohomology class on the long exact sequence of a pair of spaces `(X, A)`: there
`Eᵢ` and `Bᵢ'` are the chains of `A`, of `X` and of the pair, and `f` is the inclusion of the
chains of `A` into those of `X`.

Then capping with a class `α` of degree `p` commutes with the two connecting morphisms up to the
sign `(-1)^p` (`TauCeti.ChainComplex.cap_comp_δ`):

`δ'(x ⌢ α) = (-1)^p δx ⌢ f^*α`.

On chains: if a cycle `x` of `E₃` lifts to a chain `y` of `E₂` with `∂y` coming from the chain
`z` of `E₁`, so that `δ[x] = [z]`, then `y ⌢ φ` lifts `x ⌢ φ`, and by the boundary formula for a
cocycle `φ`, `∂(y ⌢ φ) = (-1)^p ∂y ⌢ φ`, which comes from `(-1)^p z ⌢ f^*φ`. In a general abelian
category the lift `y` exists only after a refinement of the cycles, which does not affect the
argument.

For singular chains this is `TopPair.absoluteSingularCap_comp_singularHomologyδ`: the connecting
morphism of a pair `(X, A)` sends `x ⌢ α` to `(-1)^p ∂x ⌢ α|_A`.

## Main results

* `TauCeti.ChainComplex.cap_comp_δ`: the cap product commutes with connecting morphisms up to the
  sign `(-1)^p`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the cap product, its boundary formula, and its compatibility with the long exact
  sequences of pairs used for Lefschetz duality.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  {M : C} {k : Type*} [Ring k] [Linear k C] [MonoidalLinear k C]
  {S S' : ShortComplex (ChainComplex C ℕ)} (hS : S.ShortExact) (hS' : S'.ShortExact)
  {A₁ A B₁ B₂ B₃ : ChainComplex C ℕ} [A₁.HasTensor B₁] [A.HasTensor B₂] [A.HasTensor B₃]
  (D₁ : S.X₁ ⟶ HomologicalComplex.tensorObj A₁ B₁) (D₂ : S.X₂ ⟶ HomologicalComplex.tensorObj A B₂)
  (D₃ : S.X₃ ⟶ HomologicalComplex.tensorObj A B₃)
  (a₁ : ((tensorLeft M).mapHomologicalComplex _).obj B₁ ⟶ S'.X₁)
  (a₂ : ((tensorLeft M).mapHomologicalComplex _).obj B₂ ⟶ S'.X₂)
  (a₃ : ((tensorLeft M).mapHomologicalComplex _).obj B₃ ⟶ S'.X₃)
  (f : A₁ ⟶ A) (g₁ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃)
  (hD₁ : S.f ≫ D₂ = D₁ ≫ HomologicalComplex.tensorHom f g₁)
  (ha₁ : a₁ ≫ S'.f = ((tensorLeft M).mapHomologicalComplex _).map g₁ ≫ a₂)
  (hD₂ : S.g ≫ D₃ = D₂ ≫ HomologicalComplex.tensorHom (𝟙 A) g₂)
  (ha₂ : a₂ ≫ S'.g = ((tensorLeft M).mapHomologicalComplex _).map g₂ ≫ a₃)

include hD₁ ha₁ hD₂ ha₂ in
/-- The connecting morphism of `S'` on a capped cycle, on generalized elements: if the chain `x₂`
of `E₂` lifts the cycle `c₃` of `E₃` and the boundary of `x₂` comes from the cycle `c₁` of `E₁`,
then the connecting morphism sends the class of `c₃ ⌢ φ` to `(-1)^p` times the class of
`c₁ ⌢ f^*φ`. -/
private lemma capCycles_homologyπ_δ (p q n : ℕ) (h : p + q = n)
    (φ : (A.linearYonedaObj k M).cycles p) {Z : C} (c₃ : Z ⟶ S.X₃.cycles (n + 1))
    (x₂ : Z ⟶ S.X₂.X (n + 1)) (c₁ : Z ⟶ S.X₁.cycles n)
    (h₂ : x₂ ≫ S.g.f (n + 1) = c₃ ≫ S.X₃.iCycles (n + 1))
    (h₁ : c₁ ≫ S.X₁.iCycles n ≫ S.f.f n = x₂ ≫ S.X₂.d (n + 1) n) :
    (c₃ ≫ capCycles k D₃ a₃ p (q + 1) (n + 1) (by omega) φ) ≫ S'.X₃.homologyπ (q + 1) ≫
        hS'.δ (q + 1) q (by simp) =
      ((-1 : ℤ) ^ p) • ((c₁ ≫ capCycles k D₁ a₁ p q n h
        (HomologicalComplex.cyclesMap (K := A.linearYonedaObj k M) (L := A₁.linearYonedaObj k M)
          ((linearYonedaFunctor k M).map f.op) p φ)) ≫ S'.X₁.homologyπ q) := by
  set φ₀ : A.X p ⟶ M := (A.linearYonedaObj k M).iCycles p φ
  -- capping with `φ₀` commutes with the maps of the two sequences
  have hnat₁ := capChain_naturality (k := k) D₂ a₂ D₁ a₁ S.f f g₁ S'.f hD₁ ha₁ p q n h φ₀
  have hnat₂ := capChain_naturality (k := k) D₃ a₃ D₂ a₂ S.g (𝟙 A) g₂ S'.g hD₂ ha₂ p (q + 1)
    (n + 1) (by omega) φ₀
  simp only [HomologicalComplex.id_f, Category.id_comp] at hnat₂
  -- `x₂ ⌢ φ₀` lifts `c₃ ⌢ φ₀`, and by the boundary formula its boundary comes from
  -- `(-1)^p c₁ ⌢ f^*φ₀`
  have hδ := hS'.δ_eq (q + 1) q (by simp)
    ((c₃ ≫ capCycles k D₃ a₃ p (q + 1) (n + 1) (by omega) φ) ≫ S'.X₃.iCycles (q + 1))
    (by simp [capChain_comp_d_of_cycles _ _ p q n h])
    (x₂ ≫ capChain k D₂ a₂ p (q + 1) (n + 1) (by omega) φ₀)
    (by rw [Category.assoc, hnat₂, reassoc_of% h₂]; simp [φ₀])
    (((-1 : ℤ) ^ p) • (c₁ ≫ S.X₁.iCycles n ≫ capChain k D₁ a₁ p q n h (f.f p ≫ φ₀)))
    (by rw [Category.assoc, capChain_comp_d_of_cycles D₂ a₂ p q n h, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.assoc, Category.assoc, hnat₁, reassoc_of% h₁]) _ rfl
  convert hδ using 2
  · simp [← cancel_mono (S'.X₃.iCycles (q + 1))]
  · rw [← Preadditive.zsmul_comp]
    congr 1
    simp [← cancel_mono (S'.X₁.iCycles q), φ₀, iCycles_cyclesMap_linearYonedaFunctor_map_apply]

include hD₁ ha₁ hD₂ ha₂ in
/-- **The cap product commutes with connecting morphisms**, up to the sign `(-1)^p`. Let
`S : E₁ ⟶ E₂ ⟶ E₃` and `S' : B₁' ⟶ B₂' ⟶ B₃'` be short exact sequences of chain complexes, let
`Dᵢ` and `aᵢ` be diagonals and actions capping cochains on `E₁` to `B₁'`, on `E₂` to `B₂'` and on
`E₃` to `B₃'`, where `E₂` and `E₃` cap cochains of `A` and `E₁` caps cochains of `A₁`, and suppose
that the maps of the two sequences, together with chain maps `f : A₁ ⟶ A`, `g₁ : B₁ ⟶ B₂` and
`g₂ : B₂ ⟶ B₃`, are compatible with the diagonals and actions. Then for a class `α` of degree `p`,
capping a class of `E₃` of degree `n'` with `α` and applying the connecting morphism of `S'` is
`(-1)^p` times applying the connecting morphism of `S` and capping with `f^*α`, where
`p + q = n`, `q + 1 = q'` and `n + 1 = n'`. -/
theorem cap_comp_δ (p q n q' n' : ℕ) (h : p + q = n) (h' : p + q' = n')
    (α : (A.linearYonedaObj k M).homology p) (hq : q + 1 = q' := by lia)
    (hn : n + 1 = n' := by lia) :
    cap k D₃ a₃ p q' n' h' α ≫ hS'.δ q' q (by simp [← hq]) =
      ((-1 : ℤ) ^ p) • (hS.δ n' n (by simp [← hn]) ≫
        cap k D₁ a₁ p q n h
          (homologyMap (K := A.linearYonedaObj k M) (L := A₁.linearYonedaObj k M)
            ((linearYonedaFunctor k M).map f.op) p α)) := by
  subst hq hn
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  rw [homologyMap_linearYonedaFunctor_map_homologyπ_apply]
  -- lift the cycles of `E₃` to chains `x₂` of `E₂` after a refinement `π`, and lift the boundary
  -- of `x₂` to chains `x₁` of `E₁`
  have := hS.epi_g
  obtain ⟨Z, π, hπ, x₂, hx₂⟩ :=
    surjective_up_to_refinements_of_epi (S.g.f (n + 1)) (S.X₃.iCycles (n + 1))
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
  have hx₂d : (x₂ ≫ S.X₂.d (n + 1) n) ≫ S.g.f n = 0 := by
    rw [Category.assoc, ← S.g.comm, ← reassoc_of% hx₂]
    simp
  have := hSn.mono_f
  let x₁ : Z ⟶ S.X₁.X n := hSn.exact.lift _ hx₂d
  have hx₁ : x₁ ≫ S.f.f n = x₂ ≫ S.X₂.d (n + 1) n := hSn.exact.lift_f _ hx₂d
  have hx₁d : x₁ ≫ S.X₁.d n ((ComplexShape.down ℕ).next n) = 0 := by
    have := hS.mono_f
    rw [← cancel_mono (S.f.f _), Category.assoc, ← S.f.comm, reassoc_of% hx₁]
    simp
  have hδ := hS.δ_eq (n + 1) n (by simp) (π ≫ S.X₃.iCycles (n + 1)) (by simp) x₂ hx₂.symm x₁ hx₁
    _ rfl
  have hπ' : S.X₃.liftCycles (π ≫ S.X₃.iCycles (n + 1)) n (by simp) (by simp) = π := by
    simp [← cancel_mono (S.X₃.iCycles (n + 1))]
  rw [hπ'] at hδ
  rw [← cancel_epi (S.X₃.homologyπ (n + 1)), ← cancel_epi π, cap_homologyπ_assoc,
    ← Category.assoc π, capCycles_homologyπ_δ hS' D₁ D₂ D₃ a₁ a₂ a₃ f g₁ g₂ hD₁ ha₁ hD₂ ha₂ p q n h
      φ π x₂ (S.X₁.liftCycles x₁ _ rfl hx₁d) hx₂.symm (by rw [liftCycles_i_assoc, hx₁])]
  simp [reassoc_of% hδ]

end TauCeti.ChainComplex
