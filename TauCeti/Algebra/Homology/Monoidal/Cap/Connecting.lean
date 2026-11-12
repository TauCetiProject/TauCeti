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

/-- **The cap product commutes with connecting morphisms**, up to the sign `(-1)^p`. Let
`S : E₁ ⟶ E₂ ⟶ E₃` and `S' : B₁' ⟶ B₂' ⟶ B₃'` be short exact sequences of chain complexes, let
`Dᵢ` and `aᵢ` be diagonals and actions capping cochains on `E₁` to `B₁'`, on `E₂` to `B₂'` and on
`E₃` to `B₃'`, where `E₂` and `E₃` cap cochains of `A` and `E₁` caps cochains of `A₁`, and suppose
that the maps of the two sequences, together with chain maps `f : A₁ ⟶ A`, `g₁ : B₁ ⟶ B₂` and
`g₂ : B₂ ⟶ B₃`, are compatible with the diagonals and actions. Then for a class `α` of degree `p`,
capping a class of `E₃` of degree `n + 1` with `α` and applying the connecting morphism of `S'` is
`(-1)^p` times applying the connecting morphism of `S` and capping with `f^*α`. -/
theorem cap_comp_δ {S S' : ShortComplex (ChainComplex C ℕ)} (hS : S.ShortExact)
    (hS' : S'.ShortExact) {A₁ A B₁ B₂ B₃ : ChainComplex C ℕ} [A₁.HasTensor B₁] [A.HasTensor B₂]
    [A.HasTensor B₃] (D₁ : S.X₁ ⟶ HomologicalComplex.tensorObj A₁ B₁)
    (D₂ : S.X₂ ⟶ HomologicalComplex.tensorObj A B₂)
    (D₃ : S.X₃ ⟶ HomologicalComplex.tensorObj A B₃)
    (a₁ : ((tensorLeft M).mapHomologicalComplex _).obj B₁ ⟶ S'.X₁)
    (a₂ : ((tensorLeft M).mapHomologicalComplex _).obj B₂ ⟶ S'.X₂)
    (a₃ : ((tensorLeft M).mapHomologicalComplex _).obj B₃ ⟶ S'.X₃)
    (f : A₁ ⟶ A) (g₁ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃)
    (hD₁ : S.f ≫ D₂ = D₁ ≫ HomologicalComplex.tensorHom f g₁)
    (ha₁ : a₁ ≫ S'.f = ((tensorLeft M).mapHomologicalComplex _).map g₁ ≫ a₂)
    (hD₂ : S.g ≫ D₃ = D₂ ≫ HomologicalComplex.tensorHom (𝟙 A) g₂)
    (ha₂ : a₂ ≫ S'.g = ((tensorLeft M).mapHomologicalComplex _).map g₂ ≫ a₃)
    (p q n : ℕ) (h : p + q = n) (α : (A.linearYonedaObj k M).homology p) :
    cap k D₃ a₃ p (q + 1) (n + 1) (by omega) α ≫ hS'.δ (q + 1) q (by simp) =
      ((-1 : ℤ) ^ p) • (hS.δ (n + 1) n (by simp) ≫
        cap k D₁ a₁ p q n h
          (homologyMap (K := A.linearYonedaObj k M) (L := A₁.linearYonedaObj k M)
            ((linearYonedaFunctor k M).map f.op) p α)) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  rw [homologyMap_linearYonedaFunctor_map_homologyπ_apply]
  -- name the underlying cochain, typed as a morphism rather than as an element of the module of
  -- cochains, so that composition lemmas apply to it
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : A.X p ⟶ M, φ₀ = (A.linearYonedaObj k M).iCycles p φ := ⟨_, rfl⟩
  have hφd : A.d (p + 1) p ≫ φ₀ = 0 := hφ₀ ▸ d_comp_linearYonedaObj_iCycles p (p + 1) φ
  -- capping with `φ₀` commutes with the maps of the two sequences
  have hnat₁ : ∀ m r (hm : p + r = m), capChain k D₁ a₁ p r m hm (f.f p ≫ φ₀) ≫ S'.f.f r =
      S.f.f m ≫ capChain k D₂ a₂ p r m hm φ₀ := fun m r hm ↦
    capChain_naturality (k := k) D₂ a₂ D₁ a₁ S.f f g₁ S'.f hD₁ ha₁ p r m hm φ₀
  have hnat₂ : ∀ m r (hm : p + r = m), capChain k D₂ a₂ p r m hm φ₀ ≫ S'.g.f r =
      S.g.f m ≫ capChain k D₃ a₃ p r m hm φ₀ := fun m r hm ↦ by
    have := capChain_naturality (k := k) D₃ a₃ D₂ a₂ S.g (𝟙 A) g₂ S'.g hD₂ ha₂ p r m hm φ₀
    simpa only [HomologicalComplex.id_f, Category.id_comp] using this
  -- the connecting morphism of `S`: lift the cycles of `E₃` to chains `x₂` of `E₂` after a
  -- refinement `π`, and lift the boundary of `x₂` to chains `x₁` of `E₁`
  have := hS.epi_g
  obtain ⟨Z, π, hπ, x₂, hx₂⟩ :=
    surjective_up_to_refinements_of_epi (S.g.f (n + 1)) (S.X₃.iCycles (n + 1))
  have hn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
  have hx₂d : (x₂ ≫ S.X₂.d (n + 1) n) ≫ S.g.f n = 0 := by
    rw [Category.assoc, ← S.g.comm, ← Category.assoc, ← hx₂, Category.assoc, iCycles_d,
      comp_zero]
  have := hn.mono_f
  let x₁ : Z ⟶ S.X₁.X n := hn.exact.lift _ hx₂d
  have hx₁ : x₁ ≫ S.f.f n = x₂ ≫ S.X₂.d (n + 1) n := hn.exact.lift_f _ hx₂d
  have hδ := hS.δ_eq (n + 1) n (by simp) (π ≫ S.X₃.iCycles (n + 1))
    (by rw [Category.assoc, iCycles_d, comp_zero]) x₂ hx₂.symm x₁ hx₁ _ rfl
  have hliftπ : S.X₃.liftCycles (π ≫ S.X₃.iCycles (n + 1)) n (by simp)
      (by rw [Category.assoc, iCycles_d, comp_zero]) = π := by
    rw [← cancel_mono (S.X₃.iCycles (n + 1)), liftCycles_i]
  rw [hliftπ] at hδ
  -- the connecting morphism of `S'` on the cap products: `x₂ ⌢ φ₀` lifts `x ⌢ φ₀`, and by the
  -- boundary formula its boundary comes from `(-1)^p x₁ ⌢ f^*φ₀`
  have hcd : ∀ y : Z ⟶ S.X₂.X (n + 1), (y ≫ capChain k D₂ a₂ p (q + 1) (n + 1) (by omega) φ₀) ≫
      S'.X₂.d (q + 1) q = ((-1 : ℤ) ^ p) • (y ≫ S.X₂.d (n + 1) n ≫
        capChain k D₂ a₂ p q n h φ₀) := fun y ↦ by
    rw [Category.assoc, capChain_comp_d D₂ a₂ p q n h φ₀, hφd, map_zero, sub_zero,
      Preadditive.comp_zsmul]
  set x₃' := π ≫ S.X₃.iCycles (n + 1) ≫ capChain k D₃ a₃ p (q + 1) (n + 1) (by omega) φ₀
    with hx₃'
  have hx₃'d : x₃' ≫ S'.X₃.d (q + 1) q = 0 := by
    rw [hx₃', Category.assoc, Category.assoc, capChain_comp_d D₃ a₃ p q n h φ₀, hφd, map_zero,
      sub_zero, Preadditive.comp_zsmul, iCycles_d_assoc, zero_comp, smul_zero, comp_zero]
  have hx₂' : (x₂ ≫ capChain k D₂ a₂ p (q + 1) (n + 1) (by omega) φ₀) ≫ S'.g.f (q + 1) = x₃' := by
    rw [hx₃', Category.assoc, hnat₂, ← Category.assoc, ← Category.assoc, hx₂]
  have hx₁' : (((-1 : ℤ) ^ p) • (x₁ ≫ capChain k D₁ a₁ p q n h (f.f p ≫ φ₀))) ≫ S'.f.f q =
      (x₂ ≫ capChain k D₂ a₂ p (q + 1) (n + 1) (by omega) φ₀) ≫ S'.X₂.d (q + 1) q := by
    rw [hcd, Preadditive.zsmul_comp, Category.assoc, hnat₁, ← Category.assoc, hx₁,
      Category.assoc]
  have hδ' := hS'.δ_eq (q + 1) q (by simp) x₃' hx₃'d _ hx₂' _ hx₁' _ rfl
  -- compare the cycles on both sides
  have hcap₃ : π ≫ capCycles k D₃ a₃ p (q + 1) (n + 1) (by omega) φ =
      S'.X₃.liftCycles x₃' q (by simp) hx₃'d := by
    rw [← cancel_mono (S'.X₃.iCycles (q + 1)), liftCycles_i, Category.assoc, capCycles_i, hx₃',
      ← hφ₀]
  have hcap₁ : S'.X₁.liftCycles (((-1 : ℤ) ^ p) • (x₁ ≫ capChain k D₁ a₁ p q n h (f.f p ≫ φ₀)))
      _ rfl (by
        have := hS'.mono_f
        rw [← cancel_mono (S'.f.f _), Category.assoc, ← S'.f.comm, reassoc_of% hx₁',
          d_comp_d, comp_zero, comp_zero, zero_comp]) =
      ((-1 : ℤ) ^ p) • (S.X₁.liftCycles x₁ _ rfl (by
          have := hS.mono_f
          rw [← cancel_mono (S.f.f _), Category.assoc, ← S.f.comm, reassoc_of% hx₁,
            d_comp_d, comp_zero, zero_comp]) ≫
        capCycles k D₁ a₁ p q n h (HomologicalComplex.cyclesMap (K := A.linearYonedaObj k M)
          (L := A₁.linearYonedaObj k M) ((linearYonedaFunctor k M).map f.op) p φ)) := by
    rw [← cancel_mono (S'.X₁.iCycles q), liftCycles_i, Preadditive.zsmul_comp, Category.assoc,
      capCycles_i, liftCycles_i_assoc, iCycles_cyclesMap_linearYonedaFunctor_map_apply, ← hφ₀]
  rw [← cancel_epi (S.X₃.homologyπ (n + 1)), ← cancel_epi π, cap_homologyπ_assoc,
    ← Category.assoc π, hcap₃, hδ', Preadditive.comp_zsmul, Preadditive.comp_zsmul,
    reassoc_of% hδ, cap_homologyπ, hcap₁, Preadditive.zsmul_comp, Category.assoc]

end TauCeti.ChainComplex
