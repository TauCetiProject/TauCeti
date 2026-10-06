/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.GaloisAction
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.GroupTheory.Abelianization.Finite
import TauCeti.RepresentationTheory.Rep.TensorShortExact

/-!
# The Galois-equivariant valuation sequence

For a finite extension of nonarchimedean local fields `L/K`, normalized valuation gives the
short exact sequence `0 → U(L,0) → Lˣ → ℤ → 0` of integral Galois representations, with trivial
action on `ℤ`. All multiplicative coefficient groups are read through `Additive`.

For a cyclic extension, Hilbert 90 and two-periodicity make degree minus one of `Lˣ` vanish.
The valuation sequence then shows that degree minus one of `U(L,0)` is finite, and gives
`h(Lˣ) = [L : K] * h(U(L,0))` when the extension is Galois. Thus the local unit calculation
`h(U(L,0)) = 1` transfers to the multiplicative group without choosing a Galois-invariant
uniformizer, which generally does not exist.

Together with the unit quotient calculation and cyclic two-periodicity, this relation gives
the order of the relative Brauer group for a cyclic extension. That order calculation is an
input to identifying the full Brauer group with its unramified classes, which in turn allows
the unramified invariant to extend to the full local invariant.

The constructions reuse the kernel and surjectivity of `TauCeti.normalizedValuation`, and
Mathlib's `groupCohomology.H1ofAutOnUnitsUnique` (Riccardo Brasca and Amelia Livingston).

## References

* Romyar Sharifi, *Algebraic Number Theory*, proof of Theorem 9.1.13 and Definition 9.1.14:
  https://www.math.ucla.edu/~sharifi/notes/algnum-ch09.html
-/

public noncomputable section

open CategoryTheory Limits ValuativeRel

namespace TauCeti

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-- Inclusion of the valuation-zero units in the multiplicative group, as a morphism of
integral Galois representations. -/
def unitFiltrationZeroIncl :
    Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0) ⟶
      Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (unitFiltration L 0).subtype.toAdditive.toIntLinearMap fun σ x ↦
      congrArg Additive.ofMul (AlgEquiv.coe_smul_unitFiltration σ x.toMul)

/-- The inclusion is the subgroup inclusion, written additively. -/
@[simp]
theorem unitFiltrationZeroIncl_apply (x : Additive (unitFiltration L 0)) :
    (unitFiltrationZeroIncl K L).hom x = Additive.ofMul (x.toMul : Lˣ) := (rfl)

/-- The inclusion of the valuation-zero units in the multiplicative group is injective. -/
theorem unitFiltrationZeroIncl_injective : Function.Injective (unitFiltrationZeroIncl K L).hom :=
  fun _ _ h ↦ Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul h))

/-- On the valuation-zero units of a Galois extension, the representation norm of `Gal(L/K)` is
the field norm. -/
theorem coe_norm_unitFiltrationZero [IsGalois K L]
    (x : Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)) :
    (((Rep.toAdditive
        ((Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)).norm.hom x)).toMul :
          Lˣ) : L) =
      algebraMap K L (Algebra.norm K (((Rep.toAdditive x).toMul : Lˣ) : L)) := by
  -- Compare in `Lˣ`, where the representation norm is the field norm.
  have hc := congr($(Rep.norm_comm (unitFiltrationZeroIncl K L)).hom x)
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply] at hc
  rw [← groupCohomology.norm_ofAlgebraAutOnUnits_eq]
  exact congr(((Additive.toMul (Rep.toAdditive $hc.symm) : Lˣ) : L))

/-- Normalized valuation as a morphism from the multiplicative Galois representation to the
trivial integral representation. -/
def unitsValuationHom : Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ ⟶ Rep.trivial ℤ (L ≃ₐ[K] L) ℤ :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (normalizedValuation L).toAdditiveLeft.toIntLinearMap fun σ x ↦ by
      -- `change` evaluates `Representation.ofMulDistribMulAction` on `Additive Lˣ`,
      -- reduces the target's `Representation.trivial` action to the identity, and evaluates
      -- `toAdditiveLeft.toIntLinearMap` as `Multiplicative.toAdd` of normalized valuation.
      change (normalizedValuation L (σ • x.toMul)).toAdd =
        (normalizedValuation L x.toMul).toAdd
      rw [AlgEquiv.smul_units_def, AlgEquiv.normalizedValuation_unitsMap]

/-- The valuation morphism evaluates to the additive normalized valuation. -/
@[simp]
theorem unitsValuationHom_apply (x : Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) :
    (unitsValuationHom K L).hom x = (normalizedValuation L (Rep.toAdditive x).toMul).toAdd := (rfl)

/-- An element has valuation zero exactly when it lies in the zeroth unit-filtration group. -/
@[simp]
theorem unitsValuationHom_eq_zero_iff (x : Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) :
    (unitsValuationHom K L).hom x = 0 ↔ (Rep.toAdditive x).toMul ∈ unitFiltration L 0 := by
  rw [unitsValuationHom_apply, toAdd_eq_zero, ← MonoidHom.mem_ker,
    ker_normalizedValuation]

/-- The inclusion of valuation-zero units followed by normalized valuation vanishes. -/
@[reassoc (attr := simp)]
theorem unitFiltrationZeroIncl_comp_unitsValuationHom :
    unitFiltrationZeroIncl K L ≫ unitsValuationHom K L = 0 := by
  ext x
  exact (unitsValuationHom_eq_zero_iff K L _).2 x.toMul.2

/-- The canonical valuation short complex of integral Galois representations. The last term
has trivial action; the sequence need not split as Galois representations. The body is exposed
so that connecting maps can be formed at its stated coefficient objects. -/
@[expose]
def unitsValuationSequence : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  ShortComplex.mk (unitFiltrationZeroIncl K L) (unitsValuationHom K L)
    (unitFiltrationZeroIncl_comp_unitsValuationHom K L)

/-- The first map of the valuation sequence is the inclusion of `U(L,0)`. -/
@[simp]
theorem unitsValuationSequence_f :
    (unitsValuationSequence K L).f = unitFiltrationZeroIncl K L := (rfl)

/-- The last map of the valuation sequence is normalized valuation. -/
@[simp]
theorem unitsValuationSequence_g :
    (unitsValuationSequence K L).g = unitsValuationHom K L := (rfl)

/-- The coefficient objects of the valuation sequence are `U(L,0)`, `Lˣ`, and trivial `ℤ`. -/
theorem unitsValuationSequence_def :
    unitsValuationSequence K L = ShortComplex.mk (unitFiltrationZeroIncl K L)
      (unitsValuationHom K L) (unitFiltrationZeroIncl_comp_unitsValuationHom K L) := (rfl)

/-- The valuation sequence `0 → U(L,0) → Lˣ → ℤ → 0` is short exact in integral
Galois representations for every finite compatible extension of local fields. -/
theorem unitsValuationSequence_shortExact : (unitsValuationSequence K L).ShortExact := by
  rw [unitsValuationSequence_def]
  refine ShortComplex.ShortExact.mk' ((Rep.exact_iff_function_exact _).2 ?_)
    ((Rep.mono_iff_injective _).2 ?_) ((Rep.epi_iff_surjective _).2 ?_)
  · intro x
    dsimp only at x ⊢
    rw [unitsValuationHom_eq_zero_iff]
    constructor
    · intro hx
      exact ⟨Additive.ofMul ⟨(Rep.toAdditive x).toMul, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.toMul.2
  · exact unitFiltrationZeroIncl_injective K L
  · intro n
    obtain ⟨x, hx⟩ := normalizedValuation_surjective (K := L) (Multiplicative.ofAdd n)
    exact ⟨Additive.ofMul x, congrArg Multiplicative.toAdd hx⟩

section Cyclic

variable [IsCyclic (L ≃ₐ[K] L)]

/-- Degree-minus-one Tate cohomology of the valuation-zero units is finite. -/
instance finite_tateCohomology_negOne_unitFiltration_zero :
    Finite (tateCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)) (-1)) := by
  have hS := unitsValuationSequence_shortExact K L
  rw [unitsValuationSequence_def] at hS
  have hT := _root_.TateCohomology.map_tateComplexFunctor_shortExact hS
  have hzero : IsZero (tateCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) (-1)) := by
    simpa only [Rep.ofAlgebraAutOnUnits] using
      (ModuleCat.isZero_of_subsingleton
        (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L))).of_iso
          (Rep.FiniteCyclicGroup.periodicIso (Rep.ofAlgebraAutOnUnits K L) (-1) 1 (by decide) ≪≫
            (_root_.TateCohomology.isoGroupCohomology 1).app _)
  have hepi := hT.epi_δ (-2) (-1) (by decide) hzero
  have hfinite : Finite (tateCohomology (Rep.trivial ℤ (L ≃ₐ[K] L) ℤ) (-2)) :=
    Finite.of_equiv _ (TateCohomology.HNegTwoAddEquivAbelianization.toEquiv.symm)
  exact Finite.of_surjective (_root_.TateCohomology.δ hS (-2))
    ((ModuleCat.epi_iff_surjective _).1 hepi)

/-- The valuation sequence transfers the Herbrand quotient of the unit group to the
multiplicative group, with factor the order of the automorphism group. -/
theorem herbrandQuotient_units_eq_card_mul :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) =
      Nat.card (L ≃ₐ[K] L) * TateCohomology.herbrandQuotient
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)) := by
  have := TateCohomology.subsingleton_tateCohomology_negOne_trivial_int (L ≃ₐ[K] L)
  have hS := unitsValuationSequence_shortExact K L
  rw [unitsValuationSequence_def] at hS
  simpa only [TateCohomology.herbrandQuotient_trivial_int_eq_card, mul_comm] using
    TateCohomology.herbrandQuotient_eq_mul_of_shortExact hS

/-- For a cyclic Galois extension, the multiplicative-group Herbrand quotient is the degree
of the extension times the unit-group Herbrand quotient. -/
theorem herbrandQuotient_units_eq_finrank_mul [IsGalois K L] :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) =
      Module.finrank K L * TateCohomology.herbrandQuotient
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)) := by
  rw [herbrandQuotient_units_eq_card_mul, IsGalois.card_aut_eq_finrank K L]

end Cyclic

end TauCeti
