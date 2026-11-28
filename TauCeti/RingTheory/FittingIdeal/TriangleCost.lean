/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.Algebra.Module.FunctionModule
public import TauCeti.RingTheory.FittingIdeal.Length
import Mathlib.Algebra.MvPolynomial.Eval
import TauCeti.LinearAlgebra.Quotient.Basic
import TauCeti.RingTheory.FittingIdeal.Span
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.MatlisDuality.PrincipalIdealRing

/-!
# Fitting ideals of modules with a triangle cost

Let `O` be a discrete valuation ring with valuation `v`, `R = O[X_j : j ∈ J]` for a linear order
`J`, and `N ⊆ R^ι` a module of relations, `ι` finite. Fix an `O`-linear map `Φ : V → R^ι`, a map
`z : G → V` from a set `G`, and `p ∈ O`. The *module of functions* of `N`
(`Submodule.functionModule`) is the `O`-module of the functions `g ↦ Ψ (z g)` on `G`, for the
`O`-linear `Ψ : V → O ⧸ (p)` vanishing on `Φ⁻¹(N)`; it stands in for a module of cocycles with
values in `O ⧸ (p)`.

The relations `Φ (z (τ j)) ≡ X_j Φ (z (φ j))` and `Φ (z (τ' j)) ≡ X_j Φ (z (φ' j))` tie the
variable `X_j` to elements of `G`. A module `Z` of functions has *triangle cost* `(I, C, b)`, for a
finite `I ⊆ J`, if for some `A ⊆ G`, with `Z₀` the members of `Z` vanishing on `A`, the equality
in `Z₀` of the values at `τ j` and `τ' j` is forced, up to `C` and for each `j ∈ I` in turn, by the
equalities at the earlier variables, and the length of `Z ⧸ Z₀` plus the length modulo `C`-torsion
of any submodule of `Z₀` whose members vanish at all `τ j`, `τ' j` and agree at `φ j`, `φ' j` for
`j ∈ I` is at most `b`. The main theorem
(`Submodule.exists_mul_prod_X_mem_minorsIdeal_of_hasTriangleCost`) produces from a triangle cost an
element of the Fitting ideal of `R^ι ⧸ N` divisible by `∏_{j ∈ I} X_j`: some `F ∈ R` with
`F ∏_{j ∈ I} X_j` in the Fitting ideal has `v(F(0)) ≤ b + (#I + #ι) v(C)`. In Ribet's method to
first order, this bounds the contribution of the characters without counting their cocycles.

The proof enlarges `N` in three stages. First by the relations `Φ (z a)`, `a ∈ A`, which costs
the length of their image in `R^ι ⧸ N` (`Submodule.pow_mul_mem_minorsIdeal_of_length_map_mkQ_le`),
at most the length of `Z ⧸ Z₀` by duality with values in `O ⧸ (p)`
(`Submodule.length_map_mkQ_span_image_le`). Then by the relations
`Φ (z (φ j)) - Φ (z (φ' j))`, `j ∈ I`, in increasing order of `j`: the triangle condition makes
`C X_j` multiply each into the module reached before it
(`Submodule.prod_colon_mul_minorsIdeal_sup_span_image_le`). Finally the Fitting ideal is read at
`X = 0` (`Submodule.exists_mem_minorsIdeal_addVal_eq_length`), where the colength of the relations
is the length of their module of functions (`Submodule.length_functionModule`), bounded by a
length modulo `C`-torsion because that module is detected by finitely many points
(`Submodule.functionModule_isDetectedBy_range`, `Submodule.IsDetectedBy.length_le`).

## Main definitions

* `Submodule.HasTriangleCost Z τ τ' φ φ' I C b`: `Z` has triangle cost `(I, C, b)`.

## Main results

* `Submodule.hasTriangleCost_iff`, `Submodule.HasTriangleCost.mono`: unfolding a triangle cost, and
  raising its bound.
* `Submodule.exists_mul_prod_X_mem_minorsIdeal_of_hasTriangleCost`: the Fitting ideal of a module
  of relations whose module of functions has a triangle cost.

## References

* [Stacks Project, Tag 07Z6](https://stacks.math.columbia.edu/tag/07Z6), for Fitting ideals.

## Provenance

The three-stage proof follows the method of `New.Selmer.exists_mul_prod_X_mem_fittingIdeal` in
grh-lean (https://github.com/lsernau/grh-lean, file
`src/New/Congruences/FirstOrder/FittingBlock.lean`, Apache 2.0, Copyright 2026 Anthropic, PBC); no
grh-lean code was read or copied.
-/

public section

noncomputable section

open IsDiscreteValuationRing Module MvPolynomial

namespace Submodule

section TriangleCost

variable {O G B J : Type*} [CommRing O] [AddCommGroup B] [Module O B] [LinearOrder J]

/-- A module `Z` of functions `G → B` has *triangle cost* `(I, C, b)`, for `τ, τ', φ, φ' : J → G`
with `J` linearly ordered, `I ⊆ J`, `C ∈ O` and `b ∈ ℕ∞`, if for some `A ⊆ G`, with `Z₀` the
members of `Z` vanishing on `A`:
* for `j ∈ I` and `c ∈ Z₀` with `c (τ i) = c (τ' i)` for all `i < j` and `c (φ i) = c (φ' i)`
  for the `i < j` in `I`, `C • c (τ j) = C • c (τ' j)`;
* for every submodule `Z₁ ⊆ Z₀` whose members vanish at all `τ j`, `τ' j` and have
  `c (φ j) = c (φ' j)` for `j ∈ I`, the length of `Z ⧸ Z₀` plus the length of `Z₁` modulo its
  `C`-torsion is at most `b`. -/
def HasTriangleCost (Z : Submodule O (G → B)) (τ τ' φ φ' : J → G) (I : Finset J) (C : O)
    (b : ℕ∞) : Prop :=
  ∃ A : Set G,
    (∀ j ∈ I, ∀ c ∈ Z ⊓ pi A (fun _ ↦ ⊥), (∀ i < j, c (τ i) = c (τ' i)) →
      (∀ i ∈ I, i < j → c (φ i) = c (φ' i)) → C • c (τ j) = C • c (τ' j)) ∧
    ∀ Z₁ : Submodule O (G → B), Z₁ ≤ Z ⊓ pi A (fun _ ↦ ⊥) →
      (∀ c ∈ Z₁, ∀ j, c (τ j) = 0 ∧ c (τ' j) = 0) → (∀ c ∈ Z₁, ∀ j ∈ I, c (φ j) = c (φ' j)) →
      length O (Z ⧸ (pi A fun _ ↦ ⊥).comap Z.subtype) + length O (Z₁ ⧸ torsionBy O Z₁ C) ≤ b

variable {Z : Submodule O (G → B)} {τ τ' φ φ' : J → G} {I : Finset J} {C : O} {b : ℕ∞}

/-- Unfolding `Submodule.HasTriangleCost`. -/
theorem hasTriangleCost_iff : Z.HasTriangleCost τ τ' φ φ' I C b ↔ ∃ A : Set G,
    (∀ j ∈ I, ∀ c ∈ Z ⊓ pi A (fun _ ↦ ⊥), (∀ i < j, c (τ i) = c (τ' i)) →
      (∀ i ∈ I, i < j → c (φ i) = c (φ' i)) → C • c (τ j) = C • c (τ' j)) ∧
    ∀ Z₁ : Submodule O (G → B), Z₁ ≤ Z ⊓ pi A (fun _ ↦ ⊥) →
      (∀ c ∈ Z₁, ∀ j, c (τ j) = 0 ∧ c (τ' j) = 0) → (∀ c ∈ Z₁, ∀ j ∈ I, c (φ j) = c (φ' j)) →
      length O (Z ⧸ (pi A fun _ ↦ ⊥).comap Z.subtype) + length O (Z₁ ⧸ torsionBy O Z₁ C) ≤ b :=
  Iff.rfl

/-- A triangle cost `(I, C, b)` is a triangle cost `(I, C, b')` for every `b' ≥ b`. -/
theorem HasTriangleCost.mono (h : Z.HasTriangleCost τ τ' φ φ' I C b) {b' : ℕ∞} (hb : b ≤ b') :
    Z.HasTriangleCost τ τ' φ φ' I C b' :=
  let ⟨A, ha, hb'⟩ := h
  ⟨A, ha, fun Z₁ h₁ h₂ h₃ ↦ (hb' Z₁ h₁ h₂ h₃).trans hb⟩

end TriangleCost

section Main

variable {O J G V ι : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [LinearOrder J] [AddCommGroup V] [Module O V]
  {N : Submodule (MvPolynomial J O) (ι → MvPolynomial J O)} {Φ : V →ₗ[O] ι → MvPolynomial J O}
  {z : G → V} {p : O} {τ τ' φ φ' : J → G} {I : Finset J} {C : O}

/-- **One step of the triangle.** Let `N_j` be `N` enlarged by the relations `Φ (z a)`, `a ∈ A`,
and `Φ (z (φ i)) - Φ (z (φ' i))`, `i ∈ I`, `i < j`. If the members of the module of functions of
`N` vanishing on `A` satisfy the triangle condition at `j ∈ I`, then `C X_j` multiplies
`Φ (z (φ j)) - Φ (z (φ' j))` into `N_j`. -/
private theorem C_mul_X_mem_colon (hp : p ≠ 0) {A : Set G}
    (hA : ∀ j ∈ I, ∀ c ∈ N.functionModule Φ z p ⊓ pi A (fun _ ↦ ⊥),
      (∀ i < j, c (τ i) = c (τ' i)) → (∀ i ∈ I, i < j → c (φ i) = c (φ' i)) →
        C • c (τ j) = C • c (τ' j))
    (hpN : ∀ v, Φ (p • v) ∈ N)
    (hτ : ∀ j, Φ (z (τ j)) - (X j : MvPolynomial J O) • Φ (z (φ j)) ∈ N)
    (hτ' : ∀ j, Φ (z (τ' j)) - (X j : MvPolynomial J O) • Φ (z (φ' j)) ∈ N)
    (hI : ∀ j ∈ I, ∀ i < j, i ∉ I → ∀ v, (X i : MvPolynomial J O) • v ∈ N) {j : J} (hj : j ∈ I) :
    MvPolynomial.C C * X j ∈ (N ⊔ span (MvPolynomial J O) (span O (Φ '' (z '' A)) : Set _) ⊔
      span (MvPolynomial J O) ((fun i ↦ Φ (z (φ i)) - Φ (z (φ' i))) '' {i | i ∈ I ∧ i < j})).colon
        {Φ (z (φ j)) - Φ (z (φ' j))} := by
  set w := fun i ↦ Φ (z (φ i)) - Φ (z (φ' i))
  set Nj := N ⊔ span (MvPolynomial J O) (span O (Φ '' (z '' A)) : Set _) ⊔
    span (MvPolynomial J O) (w '' {i | i ∈ I ∧ i < j})
  have hN : N ≤ Nj := le_sup_left.trans le_sup_left
  have hw (i : J) (hi : i ∈ I) (hij : i < j) : w i ∈ Nj :=
    mem_sup_right (subset_span ⟨i, ⟨hi, hij⟩, rfl⟩)
  have hτw (i : J) : Φ (z (τ i)) - Φ (z (τ' i)) - (X i : MvPolynomial J O) • w i ∈ N := by
    convert sub_mem (hτ i) (hτ' i) using 1
    simp only [w, smul_sub]
    abel
  -- The triangle condition at `j`, dualized: `C (z (τ j) - z (τ' j))` lies in `Φ⁻¹(N_j)`.
  have key : Φ (C • (z (τ j) - z (τ' j))) ∈ Nj := by
    by_contra hx
    set Wj := (Nj.restrictScalars O).comap Φ
    obtain ⟨Ψ, hΨ⟩ := TauCeti.exists_linearMap_quotient_span_singleton_apply_ne_zero hp
      (smul_quotient_comap_eq_zero fun v ↦ hN (hpN v)) (x := Wj.mkQ (C • (z (τ j) - z (τ' j)))) (by
        rw [ne_eq, mkQ_apply, Quotient.mk_eq_zero]
        simpa [Wj] using hx)
    have hvan (v : V) (hv : Φ v ∈ Nj) : Ψ (Wj.mkQ v) = 0 := by
      rw [mkQ_apply, (Quotient.mk_eq_zero _).2 (by simpa [Wj] using hv), map_zero]
    have heq (g g' : G) (h : Φ (z g) - Φ (z g') ∈ Nj) :
        Ψ (Wj.mkQ (z g)) = Ψ (Wj.mkQ (z g')) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub]
      exact hvan _ (by rwa [map_sub])
    have hc : (fun g ↦ Ψ (Wj.mkQ (z g))) ∈ N.functionModule Φ z p ⊓ pi A (fun _ ↦ ⊥) := by
      refine ⟨functionModule_le_functionModule (fun v hv ↦ hN hv) (apply_mkQ_mem_functionModule Ψ),
        mem_pi.2 fun a ha ↦ (mem_bot O).2 (hvan _ ?_)⟩
      exact mem_sup_left (mem_sup_right (subset_span (subset_span ⟨z a, ⟨a, ha, rfl⟩, rfl⟩)))
    refine hΨ ?_
    have := hA j hj _ hc (fun i hij ↦ heq _ _ ?_) fun i hi hij ↦ heq _ _ (hw i hi hij)
    · rw [map_smul, map_smul, map_sub, map_sub, smul_sub, sub_eq_zero]
      exact this
    · by_cases hi : i ∈ I
      · simpa using add_mem (hN (hτw i)) (smul_mem _ (X i) (hw i hi hij))
      · exact hN (by simpa using add_mem (hτw i) (hI j hj i hij hi (w i)))
  -- `C X_j w_j = C (Φ (z (τ j)) - Φ (z (τ' j))) - C (Φ (z (τ j)) - Φ (z (τ' j)) - X_j w_j)`.
  rw [mem_colon_singleton, MvPolynomial.C_mul', smul_assoc]
  have h := sub_mem (by simpa [map_smul, map_sub] using key) (smul_of_tower_mem _ C (hN (hτw j)))
  rwa [← smul_sub, sub_sub_cancel] at h

/-- **The first two stages.** If the relations `Φ (z a)`, `a ∈ A`, have image of length at most
`n` in `R^ι ⧸ N` and the triangle condition holds for `A`, then `ϖ ^ n C^#I ∏_{j ∈ I} X_j`
multiplies the minors of `N` enlarged by these relations and by the `Φ (z (φ j)) - Φ (z (φ' j))`,
`j ∈ I`, into those of `N`. -/
private theorem C_mul_prod_X_mem_minorsIdeal (hp : p ≠ 0) {A : Set G}
    (hA : ∀ j ∈ I, ∀ c ∈ N.functionModule Φ z p ⊓ pi A (fun _ ↦ ⊥),
      (∀ i < j, c (τ i) = c (τ' i)) → (∀ i ∈ I, i < j → c (φ i) = c (φ' i)) →
        C • c (τ j) = C • c (τ' j))
    (hpN : ∀ v, Φ (p • v) ∈ N)
    (hτ : ∀ j, Φ (z (τ j)) - (X j : MvPolynomial J O) • Φ (z (φ j)) ∈ N)
    (hτ' : ∀ j, Φ (z (τ' j)) - (X j : MvPolynomial J O) • Φ (z (φ' j)) ∈ N)
    (hI : ∀ j ∈ I, ∀ i < j, i ∉ I → ∀ v, (X i : MvPolynomial J O) • v ∈ N) {ϖ : O}
    (hϖ : Irreducible ϖ) {n : ℕ}
    (hn : length O ((span O (Φ '' (z '' A))).map (N.restrictScalars O).mkQ) ≤ n) {k : ℕ}
    {F : MvPolynomial J O}
    (hF : F ∈ (N ⊔ span (MvPolynomial J O) (span O (Φ '' (z '' A)) : Set _) ⊔
      span (MvPolynomial J O) ((fun i ↦ Φ (z (φ i)) - Φ (z (φ' i))) '' I)).minorsIdeal k) :
    MvPolynomial.C (ϖ ^ n * C ^ I.card) * F * ∏ j ∈ I, X j ∈ N.minorsIdeal k := by
  have hprod : ∏ j ∈ I, (MvPolynomial.C C * X j) ∈ ∏ j ∈ I,
      (N ⊔ span (MvPolynomial J O) (span O (Φ '' (z '' A)) : Set _) ⊔
        span (MvPolynomial J O) ((fun i ↦ Φ (z (φ i)) - Φ (z (φ' i))) '' {i | i ∈ I ∧ i < j})).colon
          {Φ (z (φ j)) - Φ (z (φ' j))} :=
    Ideal.prod_mem_prod fun j hj ↦ C_mul_X_mem_colon hp hA hpN hτ hτ' hI hj
  have h := pow_mul_mem_minorsIdeal_of_length_map_mkQ_le hϖ hn
    (prod_colon_mul_minorsIdeal_sup_span_image_le _ _ I k (Ideal.mul_mem_mul hprod hF))
  convert h using 1
  simp only [Finset.prod_mul_distrib, Finset.prod_const, map_mul, map_pow,
    MvPolynomial.algebraMap_eq]
  ring

omit [LinearOrder J] in
/-- **Reading at `X = 0`.** Let `N''` contain `N`, the relations `Φ (z a)` for `a ∈ A` and the
relations `Φ (z (φ j)) - Φ (z (φ' j))` for `j ∈ I`, and let `U ⊆ O^ι` be its image at `X = 0`. The
module of functions of `U` is a submodule `Z₁` of the second triangle cost condition for `A`, so
the colength of `U` plus the length of `Z ⧸ Z₀` is at most `b + #ι v(C)`. -/
private theorem length_quotient_map_add_le [Fintype ι] [DecidableEq ι] {gen : ι → G} {A : Set G}
    {b : ℕ∞} (hp : p ≠ 0) (hpN : ∀ v, Φ (p • v) ∈ N)
    (hgen : ∀ i, Φ (z (gen i)) - Pi.single i 1 ∈ N)
    (hτ : ∀ j, Φ (z (τ j)) - (X j : MvPolynomial J O) • Φ (z (φ j)) ∈ N)
    (hτ' : ∀ j, Φ (z (τ' j)) - (X j : MvPolynomial J O) • Φ (z (φ' j)) ∈ N)
    (hAb : ∀ Z₁ : Submodule O (G → O ⧸ Ideal.span {p}),
      Z₁ ≤ N.functionModule Φ z p ⊓ pi A (fun _ ↦ ⊥) →
      (∀ c ∈ Z₁, ∀ j, c (τ j) = 0 ∧ c (τ' j) = 0) → (∀ c ∈ Z₁, ∀ j ∈ I, c (φ j) = c (φ' j)) →
      length O (N.functionModule Φ z p ⧸ (pi A fun _ ↦ ⊥).comap (N.functionModule Φ z p).subtype) +
        length O (Z₁ ⧸ torsionBy O Z₁ C) ≤ b)
    {N'' : Submodule (MvPolynomial J O) (ι → MvPolynomial J O)} (hN : N ≤ N'')
    (hA : ∀ a ∈ A, Φ (z a) ∈ N'') (hw : ∀ j ∈ I, Φ (z (φ j)) - Φ (z (φ' j)) ∈ N'') :
    length O ((ι → O) ⧸ (N''.restrictScalars O).map
        ((aeval (R := O) (0 : J → O)).toLinearMap.compLeft ι)) +
      length O (N.functionModule Φ z p ⧸ (pi A fun _ ↦ ⊥).comap (N.functionModule Φ z p).subtype)
      ≤ b + Fintype.card ι • addVal O C := by
  classical
  set ev := (aeval (R := O) (0 : J → O)).toLinearMap.compLeft ι
  set U := (N''.restrictScalars O).map ev
  have hev (v) (hv : v ∈ N'') : ev v ∈ U := mem_map_of_mem hv
  have hevX (i : J) (v : ι → MvPolynomial J O) : ev ((X i : MvPolynomial J O) • v) = 0 := by
    ext k
    simp [ev]
  set Z'' := U.functionModule (ev ∘ₗ Φ) z p
  have heq (c) (hc : c ∈ Z'') (g g' : G) (h : ev (Φ (z g)) - ev (Φ (z g')) ∈ U) : c g = c g' := by
    obtain ⟨Ψ, hΨ, hc⟩ := mem_functionModule.1 hc
    rw [← hc, ← hc, ← sub_eq_zero, ← map_sub]
    exact hΨ _ (by simpa using h)
  have hzero (c) (hc : c ∈ Z'') (g : G) (h : ev (Φ (z g)) ∈ U) : c g = 0 := by
    obtain ⟨Ψ, hΨ, hc⟩ := mem_functionModule.1 hc
    rw [← hc]
    exact hΨ _ h
  have hτU (j : J) : ev (Φ (z (τ j))) ∈ U := by
    have h := hev _ (hN (hτ j))
    rwa [map_sub, hevX, sub_zero] at h
  have hτ'U (j : J) : ev (Φ (z (τ' j))) ∈ U := by
    have h := hev _ (hN (hτ' j))
    rwa [map_sub, hevX, sub_zero] at h
  have hb := hAb Z''
    (le_inf (functionModule_le_functionModule fun v hv ↦ hev _ (hN hv)) fun c hc ↦
      mem_pi.2 fun a ha ↦ (mem_bot O).2 (hzero c hc a (hev _ (hA a ha))))
    (fun c hc j ↦ ⟨hzero c hc _ (hτU j), hzero c hc _ (hτ'U j)⟩)
    fun c hc j hj ↦ heq c hc _ _ (by simpa using hev _ (hw j hj))
  have hsingle (i : ι) : ev (Pi.single i 1) = Pi.single i 1 := by
    ext k
    by_cases h : k = i <;> simp [ev, h]
  have hU := length_quotient_le_length_functionModule_quotient_add (N := U) (Φ := ev ∘ₗ Φ) (z := z)
    (gen := gen) hp (fun v ↦ hev _ (hN (hpN v)))
    (fun i ↦ by simpa [hsingle] using hev _ (hN (hgen i))) C
  calc _ ≤ length O (Z'' ⧸ torsionBy O Z'' C) + Fintype.card ι • addVal O C +
        length O (N.functionModule Φ z p ⧸
          (pi A fun _ ↦ ⊥).comap (N.functionModule Φ z p).subtype) := by gcongr
    _ ≤ b + Fintype.card ι • addVal O C := by
      rw [add_right_comm, add_comm (length O (Z'' ⧸ _))]
      gcongr

variable (N) in
/-- **Fitting ideals of modules with a triangle cost.** Let `O` be a discrete valuation ring, `J` a
linear order, `R = O[X_j : j ∈ J]`, `N ⊆ R^ι` a submodule for a finite `ι`, and `Φ : V → R^ι`,
`z : G → V`, `p ≠ 0`, `gen : ι → G`, `τ, τ', φ, φ' : J → G`, `I ⊆ J` finite and `C ∈ O`. Suppose
that the module of functions of `N` has triangle cost `(I, C, b)`, that `Φ (p • v) ∈ N` for all
`v`, that `Φ (z (gen i)) - e_i ∈ N` for all `i`, that `Φ (z (τ j)) - X_j Φ (z (φ j))` and
`Φ (z (τ' j)) - X_j Φ (z (φ' j))` lie in `N`, and that for `j ∈ I` and `i < j` either `i ∈ I` or
`X_i R^ι ⊆ N`. Then some `F ∈ R` has `v(F(0)) ≤ b + (#I + #ι) v(C)` and `F ∏_{j ∈ I} X_j` in the
Fitting ideal `N.minorsIdeal #ι` of `R^ι ⧸ N`. For a finite `s ⊆ G`, the case `ι = s`,
`gen = (↑)` reads `R^s`, `e_g` and `#s`. -/
theorem exists_mul_prod_X_mem_minorsIdeal_of_hasTriangleCost [Fintype ι] [DecidableEq ι]
    {gen : ι → G} {b : ℕ∞} (hp : p ≠ 0)
    (hZ : (N.functionModule Φ z p).HasTriangleCost τ τ' φ φ' I C b)
    (hpN : ∀ v, Φ (p • v) ∈ N) (hgen : ∀ i, Φ (z (gen i)) - Pi.single i 1 ∈ N)
    (hτ : ∀ j, Φ (z (τ j)) - (X j : MvPolynomial J O) • Φ (z (φ j)) ∈ N)
    (hτ' : ∀ j, Φ (z (τ' j)) - (X j : MvPolynomial J O) • Φ (z (φ' j)) ∈ N)
    (hI : ∀ j ∈ I, ∀ i < j, i ∉ I → ∀ v, (X i : MvPolynomial J O) • v ∈ N) :
    ∃ F : MvPolynomial J O,
      addVal O (constantCoeff F) ≤ b + (I.card + Fintype.card ι) • addVal O C ∧
        F * ∏ j ∈ I, X j ∈ N.minorsIdeal (Fintype.card ι) := by
  obtain ⟨A, hAa, hAb⟩ := hZ
  set Z := N.functionModule Φ z p
  have hZ₀ : length O (Z ⧸ (pi A fun _ ↦ ⊥).comap Z.subtype) ≤ b :=
    le_self_add.trans (hAb ⊥ bot_le (by simp) (by simp))
  set w := fun i ↦ Φ (z (φ i)) - Φ (z (φ' i))
  set NA := N ⊔ span (MvPolynomial J O) (span O (Φ '' (z '' A)) : Set (ι → MvPolynomial J O))
  set N'' := NA ⊔ span (MvPolynomial J O) (w '' I)
  set π := aeval (R := O) (0 : J → O)
  have hlen := length_quotient_map_add_le hp hpN hgen hτ hτ' hAb (N'' := N'')
    (le_sup_left.trans le_sup_left)
    (fun a ha ↦ mem_sup_left (mem_sup_right (subset_span (subset_span ⟨z a, ⟨a, ha, rfl⟩, rfl⟩))))
    fun j hj ↦ mem_sup_right (subset_span ⟨j, hj, rfl⟩)
  have hcost := length_map_mkQ_span_image_le (N := N) (z := z) hp hpN A
  rcases eq_or_ne b ⊤ with rfl | hb
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨F'', hF'', hval⟩ := exists_mem_minorsIdeal_addVal_eq_length π N''
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top hb (hcost.trans hZ₀))
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  refine ⟨MvPolynomial.C (ϖ ^ n * C ^ I.card) * F'', ?_, ?_⟩
  · have hcc : constantCoeff F'' = π F'' := by simp [π]
    rw [map_mul, constantCoeff_C, addVal_mul, addVal_mul, addVal_pow, addVal_pow,
      addVal_uniformizer hϖ, hcc, hval]
    calc n • (1 : ℕ∞) + I.card • addVal O C +
          length O ((ι → O) ⧸ (N''.restrictScalars O).map (π.toLinearMap.compLeft ι))
        ≤ length O (Z ⧸ (pi A fun _ ↦ ⊥).comap Z.subtype) + I.card • addVal O C +
          length O ((ι → O) ⧸ (N''.restrictScalars O).map (π.toLinearMap.compLeft ι)) := by
          gcongr
          simpa [hn] using hcost
      _ = (length O ((ι → O) ⧸ (N''.restrictScalars O).map (π.toLinearMap.compLeft ι)) +
          length O (Z ⧸ (pi A fun _ ↦ ⊥).comap Z.subtype)) + I.card • addVal O C := by ring
      _ ≤ b + Fintype.card ι • addVal O C + I.card • addVal O C := by gcongr
      _ = b + (I.card + Fintype.card ι) • addVal O C := by rw [add_smul]; ring
  · exact C_mul_prod_X_mem_minorsIdeal hp hAa hpN hτ hτ' hI hϖ hn.ge hF''

end Main

end Submodule
