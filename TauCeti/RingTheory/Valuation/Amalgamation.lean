/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.Flat.NonZeroDivisors
import TauCeti.RingTheory.TensorProduct.LocalRing
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Amalgamating valuation rings over a common subfield

Let `K₁` and `K₂` be field extensions of `K₀`, and let `V₁ ⊆ K₁`, `V₂ ⊆ K₂` be valuation subrings
with `V₁ ∩ K₀ = V₂ ∩ K₀`. Then some residue field `κ(P)` of `K₁ ⊗[K₀] K₂` has a valuation subring
`W` with `W ∩ K₁ = V₁` and `W ∩ K₂ = V₂`
(`ValuationSubring.exists_comap_eq_of_comap_eq`). This is the field case of amalgamating two
points of valuation spectra that agree on a common subring, which is how points of fibre products
of adic spaces are produced.

Write `V₀ = V₁ ∩ K₀`. Both `V₁` and `V₂` are torsion-free, hence flat, over the valuation ring `V₀`,
so `b ⊗ 1` and `1 ⊗ c` are nonzerodivisors of `V₁ ⊗[V₀] V₂` for nonzero `b` and `c`. The
extensions of the two maximal ideals generate a proper ideal, contained in a prime `Q`, and a
minimal prime `P₀ ⊆ Q` consists of zerodivisors. Hence `V₁` and `V₂`, and so `K₁` and `K₂`, embed
in the fraction field `L` of `(V₁ ⊗[V₀] V₂) ⧸ P₀`. A valuation subring of `L` whose nonunits contain
the image of `Q` dominates the images of `V₁` and `V₂`, so it restricts to them.

## Main results

* `ValuationSubring.exists_comap_eq_of_comap_eq`: the amalgamation of valuation subrings.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30, Vieweg, 1996, (1.1.14)(f).
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), proof of Lemma 3.9(i).
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539) (torsion-free modules
  over valuation rings are flat) and [Tag 00IA](https://stacks.math.columbia.edu/tag/00IA)
  (valuation rings dominating a local ring).
-/

public section

open scoped TensorProduct nonZeroDivisors

open Algebra.TensorProduct IsLocalRing

namespace ValuationSubring

section Amalgamation

variable {K₀ K₁ K₂ : Type*} [Field K₀] [Field K₁] [Field K₂] [Algebra K₀ K₁] [Algebra K₀ K₂]

/-- Two embeddings of `K₁` and `K₂` into a field `L`, agreeing on `K₀`, factor through a residue
field of `K₁ ⊗[K₀] K₂`; a valuation subring of `L` therefore pulls back to one of that residue field
with the same restrictions to `K₁` and `K₂`. -/
private theorem exists_residueField_of_ringHom {L : Type*} [Field L] (g₁ : K₁ →+* L)
    (g₂ : K₂ →+* L) (hg : g₁.comp (algebraMap K₀ K₁) = g₂.comp (algebraMap K₀ K₂))
    (W : ValuationSubring L) :
    ∃ (P : Ideal (K₁ ⊗[K₀] K₂)) (_ : P.IsPrime) (W' : ValuationSubring P.ResidueField),
      W'.comap ((algebraMap _ P.ResidueField).comp
          (includeLeftRingHom : K₁ →+* K₁ ⊗[K₀] K₂)) = W.comap g₁ ∧
        W'.comap ((algebraMap _ P.ResidueField).comp
          (includeRight : K₂ →ₐ[K₀] K₁ ⊗[K₀] K₂).toRingHom) = W.comap g₂ := by
  let : Algebra K₀ L := (g₁.comp (algebraMap K₀ K₁)).toAlgebra
  let G₁ : K₁ →ₐ[K₀] L := { g₁ with commutes' := fun _ ↦ rfl }
  let G₂ : K₂ →ₐ[K₀] L := { g₂ with commutes' := fun r ↦ (RingHom.congr_fun hg r).symm }
  let Φ : K₁ ⊗[K₀] K₂ →+* L := (lift G₁ G₂ fun _ _ ↦ .all _ _).toRingHom
  have : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime Φ
  let h : (RingHom.ker Φ).ResidueField →+* L :=
    IsFractionRing.lift (RingHom.kerLift_injective Φ)
  have hΦ (x : K₁ ⊗[K₀] K₂) : h (algebraMap _ _ x) = Φ x := by
    rw [IsScalarTower.algebraMap_apply _ (_ ⧸ RingHom.ker Φ), IsFractionRing.lift_algebraMap]
    exact RingHom.kerLift_mk Φ x
  refine ⟨RingHom.ker Φ, inferInstance, W.comap h, ?_, ?_⟩ <;>
  · rw [comap_comap]
    congr 1
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply, hΦ]
    simp [Φ, G₁, G₂]

/-- A domain is flat over a Bézout domain mapping injectively into it: over a Bézout domain,
torsion-free modules are flat. -/
private theorem flat_of_algebraMap_injective {R S : Type*} [CommRing R] [IsDomain R] [IsBezout R]
    [CommRing S] [IsDomain S] [Algebra R S] (h : Function.Injective (algebraMap R S)) :
    Module.Flat R S := by
  rwa [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot, Module.isTorsionFree_iff_algebraMap_injective]

/-- Let `ψ : S →+* L` map into a valuation subring `W` of the field `L`, sending an ideal `Q` into
the nonunits of `W`. If a valuation subring `V` of `K` maps to `S` with its maximal ideal in `Q`,
compatibly with `g : K →+* L`, then `W` dominates the image of `V`, so `W` pulls back to `V`. -/
private theorem comap_eq_of_map_maximalIdeal_le {K L S : Type*} [Field K] [Field L] [CommRing S]
    {V : ValuationSubring K} {W : ValuationSubring L} (ι : V →+* S) (ψ : S →+* L) {Q : Ideal S}
    (hQ : (maximalIdeal V).map ι ≤ Q) (hmem : ∀ s, ψ s ∈ W) (hnon : ∀ s ∈ Q, ψ s ∈ W.nonunits)
    (g : K →+* L) (hg : ∀ v : V, g v = ψ (ι v)) : W.comap g = V := by
  refine (eq_of_le_of_nonunits_le (fun x hx ↦ ?_) fun x hx ↦ ?_).symm
  · simpa only [mem_comap, hg ⟨x, hx⟩] using hmem (ι ⟨x, hx⟩)
  · simpa only [mem_nonunits_comap, hg ⟨x, nonunits_subset hx⟩] using
      hnon _ (hQ (Ideal.mem_map_of_mem _ (coe_mem_nonunits_iff.mp hx)))

/-- **Amalgamation of valuation rings.** Let `K₁` and `K₂` be field extensions of `K₀`, with
valuation subrings `V₁ ⊆ K₁` and `V₂ ⊆ K₂` cutting out the same valuation subring of `K₀`. Then
some residue field `κ(P)` of `K₁ ⊗[K₀] K₂` carries a valuation subring `W` whose restrictions to
`K₁` and `K₂` are `V₁` and `V₂`. -/
theorem exists_comap_eq_of_comap_eq (V₁ : ValuationSubring K₁) (V₂ : ValuationSubring K₂)
    (h : V₁.comap (algebraMap K₀ K₁) = V₂.comap (algebraMap K₀ K₂)) :
    ∃ (P : Ideal (K₁ ⊗[K₀] K₂)) (_ : P.IsPrime) (W : ValuationSubring P.ResidueField),
      W.comap ((algebraMap _ P.ResidueField).comp
          (includeLeftRingHom : K₁ →+* K₁ ⊗[K₀] K₂)) = V₁ ∧
        W.comap ((algebraMap _ P.ResidueField).comp
          (includeRight : K₂ →ₐ[K₀] K₁ ⊗[K₀] K₂).toRingHom) = V₂ := by
  -- `V₁` and `V₂` are local algebras over `V₀ = V₁ ∩ K₀ = V₂ ∩ K₀`, flat since torsion-free
  set V₀ := V₁.comap (algebraMap K₀ K₁)
  have h₂ (x) (hx : x ∈ V₀) : algebraMap K₀ K₂ x ∈ V₂ := by rw [h] at hx; exact hx
  let : Algebra V₀ V₁ := ((algebraMap K₀ K₁).restrict V₀ V₁ fun _ hx ↦ hx).toAlgebra
  let : Algebra V₀ V₂ := ((algebraMap K₀ K₂).restrict V₀ V₂ h₂).toAlgebra
  have : IsLocalHom (algebraMap V₀ V₁) := isLocalHom_restrict V₁ _ rfl
  have : IsLocalHom (algebraMap V₀ V₂) := isLocalHom_restrict V₂ _ h
  have : Module.Flat V₀ V₁ := flat_of_algebraMap_injective fun _ _ hab ↦
    Subtype.ext ((algebraMap K₀ K₁).injective (congrArg Subtype.val hab))
  have : Module.Flat V₀ V₂ := flat_of_algebraMap_injective fun _ _ hab ↦
    Subtype.ext ((algebraMap K₀ K₂).injective (congrArg Subtype.val hab))
  -- a minimal prime `P₀` of `V₁ ⊗[V₀] V₂` below a prime `Q` over both maximal ideals
  obtain ⟨Q, hQ, hJQ⟩ := Ideal.exists_le_maximal _
    (map_maximalIdeal_sup_map_maximalIdeal_ne_top (R := V₀) (A := V₁) (B := V₂))
  obtain ⟨P₀, hP₀, hP₀Q⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ Q)
  have := hP₀.1.1
  have hdisj := Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP₀
  -- `L = Frac((V₁ ⊗[V₀] V₂) ⧸ P₀)` receives `V₁` and `V₂` injectively, hence `K₁` and `K₂`
  let ψ : V₁ ⊗[V₀] V₂ →+* FractionRing (V₁ ⊗[V₀] V₂ ⧸ P₀) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk P₀)
  have hψ (x) : ψ x = 0 ↔ x ∈ P₀ := by
    simp [ψ, Ideal.Quotient.eq_zero_iff_mem]
  have inj₁ : Function.Injective (ψ.comp includeLeftRingHom) := by
    refine (injective_iff_map_eq_zero _).mpr fun b hb ↦ by_contra fun hb0 ↦ ?_
    exact Set.disjoint_left.mp hdisj ((hψ _).mp hb)
      (Module.Flat.algebraMap_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb0))
  have inj₂ : Function.Injective (ψ.comp (includeRight : V₂ →ₐ[V₀] V₁ ⊗[V₀] V₂).toRingHom) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ by_contra fun hc0 ↦ ?_
    have hc' := Module.Flat.algebraMap_mem_nonZeroDivisors (A := V₂ ⊗[V₀] V₁)
      (mem_nonZeroDivisors_of_ne_zero hc0)
    exact Set.disjoint_left.mp hdisj ((hψ _).mp hc)
      (mem_nonZeroDivisors_of_injective (f := Algebra.TensorProduct.comm V₀ V₁ V₂)
        (AlgEquiv.injective _) (by simpa using hc'))
  let g₁ : K₁ →+* FractionRing (V₁ ⊗[V₀] V₂ ⧸ P₀) := IsFractionRing.lift inj₁
  let g₂ : K₂ →+* FractionRing (V₁ ⊗[V₀] V₂ ⧸ P₀) := IsFractionRing.lift inj₂
  have hg : g₁.comp (algebraMap K₀ K₁) = g₂.comp (algebraMap K₀ K₂) := by
    refine IsLocalization.ringHom_ext V₀⁰ (RingHom.ext fun a ↦ ?_)
    -- `algebraMap V₀ V₁` and `algebraMap V₀ V₂` are `RingHom.restrict`s of the field maps and
    -- `algebraMap V₁ K₁`, `algebraMap V₂ K₂` are subtype inclusions, so each side unfolds to
    -- the field map applied to `a`; restate it through `V₁` and `V₂`, where `g₁`, `g₂` compute
    change g₁ (algebraMap V₁ K₁ (algebraMap V₀ V₁ a)) = g₂ (algebraMap V₂ K₂ (algebraMap V₀ V₂ a))
    simp only [g₁, g₂, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
      includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, includeRight_apply]
    rw [← Algebra.TensorProduct.algebraMap_apply, algebraMap_apply']
  -- a valuation subring `W` of `L` containing the image of `V₁ ⊗[V₀] V₂`, with the image of `Q`
  -- among its nonunits
  have hQ' : Q.map ψ.rangeRestrict ≠ ⊤ := fun htop ↦ hQ.ne_top <| by
    have := Ideal.comap_map_of_surjective _ ψ.rangeRestrict_surjective Q
    rw [htop, Ideal.comap_top, sup_eq_left.mpr] at this
    · exact this.symm
    · intro x hx
      exact hP₀Q ((hψ x).mp (congrArg Subtype.val (Ideal.mem_bot.mp hx)))
  obtain ⟨W, hrange, hnon⟩ := Ideal.image_subset_nonunits_valuationSubring _ hQ'
  have hmem (x) : ψ x ∈ W := hrange ⟨x, rfl⟩
  have hnon' (x) (hx : x ∈ Q) : ψ x ∈ W.nonunits :=
    hnon ⟨ψ.rangeRestrict x, Ideal.mem_map_of_mem _ hx, rfl⟩
  obtain ⟨P, _, W', h₁, h₂⟩ := exists_residueField_of_ringHom g₁ g₂ hg W
  exact ⟨P, inferInstance, W',
    h₁.trans (comap_eq_of_map_maximalIdeal_le _ ψ (le_sup_left.trans hJQ) hmem hnon' g₁
      (IsFractionRing.lift_algebraMap inj₁)),
    h₂.trans (comap_eq_of_map_maximalIdeal_le _ ψ (le_sup_right.trans hJQ) hmem hnon' g₂
      (IsFractionRing.lift_algebraMap inj₂))⟩

end Amalgamation

end ValuationSubring
