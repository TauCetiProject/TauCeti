/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre
import TauCeti.LinearAlgebra.Span.Basic
import TauCeti.Algebra.Lie.Weights.Basic
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley

/-!
# Representations of the pinned Lie algebra

Serre representations transport to the pinned rational Lie algebra via
`TauCeti.UniversalEnvelopingAlgebra.map` and `TauCeti.DynkinType.serreLiftEquiv`, preserving
Cartan weights and stability of any additive lattice under the simple-generator Kostant form.
Independently, nonzero weight vectors whose weights span the rational weight space detect
faithfulness.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18 and 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
-/

public section

open scoped Matrix

namespace TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {t : DynkinType} (ht : t.Valid)
  {V : Type*} [AddCommGroup V] [Module ℚ V]

section Serre

variable {CM : Matrix (Fin t.rank) (Fin t.rank) ℤ} (hCM : CM = t.cartanMatrixᵀ)
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ CM) →ₐ[ℚ] Module.End ℚ V)

/-- Pull a Serre representation back to the pinned rational Lie algebra. -/
def serreRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V :=
  ρ.comp (UniversalEnvelopingAlgebra.map ℚ
    ((TauCeti.serreLift (by rw [← hCM]; exact TauCeti.isSerreSystem_serre ℚ CM)).comp
      (t.serreLiftEquiv ht).symm.toLieHom))

/-- The transported representation is composition with the induced enveloping-algebra map. -/
theorem serreRepresentation_def :
    serreRepresentation ht hCM ρ = ρ.comp (UniversalEnvelopingAlgebra.map ℚ
      ((TauCeti.serreLift (H := serreH ℚ CM) (E := serreE ℚ CM) (F := serreF ℚ CM)
        (by rw [← hCM]; exact TauCeti.isSerreSystem_serre ℚ CM)).comp
          (t.serreLiftEquiv ht).symm.toLieHom)) := (rfl)

/-- Transport sends a pinned Cartan generator to the corresponding Serre generator. -/
@[simp↓] theorem serreRepresentation_ι_lieBasis_h (i : Fin t.rank) :
    serreRepresentation ht hCM ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).h i)) = ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (serreH ℚ CM i)) := by
  simp only [serreRepresentation, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι,
    LieHom.comp_apply, LieEquiv.coe_toLieHom, t.serreLiftEquiv_symm_lieBasis_h ht,
    TauCeti.serreLift_serreH]

/-- Transport sends a pinned positive generator to the corresponding Serre generator. -/
@[simp↓] theorem serreRepresentation_ι_lieBasis_e (i : Fin t.rank) :
    serreRepresentation ht hCM ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).e i)) = ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (serreE ℚ CM i)) := by
  simp only [serreRepresentation, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι,
    LieHom.comp_apply, LieEquiv.coe_toLieHom, t.serreLiftEquiv_symm_lieBasis_e ht,
    TauCeti.serreLift_serreE]

/-- Transport sends a pinned negative generator to the corresponding Serre generator. -/
@[simp↓] theorem serreRepresentation_ι_lieBasis_f (i : Fin t.rank) :
    serreRepresentation ht hCM ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).f i)) = ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (serreF ℚ CM i)) := by
  simp only [serreRepresentation, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι,
    LieHom.comp_apply, LieEquiv.coe_toLieHom, t.serreLiftEquiv_symm_lieBasis_f ht,
    TauCeti.serreLift_serreF]

/-- Transport preserves the simple root-generator action. -/
@[simp↓] theorem serreRepresentation_ι_rootGenerator (k : Fin t.rank ⊕ Fin t.rank) :
    serreRepresentation ht hCM ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).rootGenerator k)) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (serreRootGenerator CM k)) := by
  cases k with
  | inl i =>
    simpa only [LieAlgebra.Basis.rootGenerator_inl, serreRootGenerator_inl] using
      serreRepresentation_ι_lieBasis_e ht hCM ρ i
  | inr i =>
    simpa only [LieAlgebra.Basis.rootGenerator_inr, serreRootGenerator_inr] using
      serreRepresentation_ι_lieBasis_f ht hCM ρ i

/-- Cartan weight vectors retain their weights under Serre transport. -/
theorem isCartanWeightVector_serreRepresentation {wt : Fin t.rank → ℤ} {v : V}
    (hv : UniversalEnvelopingAlgebra.IsCartanWeightVector (serreH ℚ CM) ρ wt v) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (t.lieBasis ht).h
      (serreRepresentation ht hCM ρ) wt v := by
  apply (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr
  intro i
  rw [serreRepresentation_ι_lieBasis_h]
  exact (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp hv i

/-- Serre transport preserves stability under the simple-generator Kostant form on any
additive subgroup of the representation space. -/
theorem serreRepresentation_kostantForm_mem
    (M : AddSubgroup V)
    (hM : ∀ u ∈ serreKostantForm CM, ∀ v ∈ M, ρ u v ∈ M)
    (u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht))
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h) (v : V) (hv : v ∈ M) :
    serreRepresentation ht hCM ρ u v ∈ M := by
  rw [serreRepresentation, AlgHom.comp_apply]
  apply hM _ _ v hv
  let f : t.lieAlgebra ht →ₗ⁅ℚ⁆ Matrix.ToLieAlgebra ℚ CM :=
    (TauCeti.serreLift (H := serreH ℚ CM) (E := serreE ℚ CM) (F := serreF ℚ CM)
      (by rw [← hCM]; exact TauCeti.isSerreSystem_serre ℚ CM)).comp
        (t.serreLiftEquiv ht).symm.toLieHom
  -- Name the Lie map in the composed action, identifying its RingHom and AlgHom coercions.
  change UniversalEnvelopingAlgebra.map ℚ f u ∈ serreKostantForm CM
  have he : (fun k => f ((t.lieBasis ht).rootGenerator k)) = serreRootGenerator CM := by
    funext k
    cases k <;> simp [f, LieAlgebra.Basis.rootGenerator_inl,
      LieAlgebra.Basis.rootGenerator_inr, serreRootGenerator_inl, serreRootGenerator_inr,
      t.serreLiftEquiv_symm_lieBasis_e ht, t.serreLiftEquiv_symm_lieBasis_f ht]
  have hh : (fun i => f ((t.lieBasis ht).h i)) = serreH ℚ CM := by
    funext i
    simp [f, t.serreLiftEquiv_symm_lieBasis_h ht]
  have hmem : UniversalEnvelopingAlgebra.map ℚ f u ∈
      (UniversalEnvelopingAlgebra.kostantForm
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h).map
          (UniversalEnvelopingAlgebra.map ℚ f).toRingHom :=
    Subring.mem_map.mpr ⟨u, hu, rfl⟩
  simpa only [UniversalEnvelopingAlgebra.map_kostantForm, he, hh, serreKostantForm_def]
    using hmem

end Serre

variable {η : Type*}
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
  {wt : η → Fin t.rank → ℤ} {v : η → V}
  (hwt : ∀ a, UniversalEnvelopingAlgebra.IsCartanWeightVector (t.lieBasis ht).h ρ (wt a) (v a))
  (hv : ∀ a, v a ≠ 0)

include hwt hv

/-- Nonzero weight vectors whose weights span the rational weight space make a representation
of the pinned Lie algebra faithful. The vectors need not span the representation space. -/
theorem representation_ι_injective_of_span_range_eq_top
    (hspan : Submodule.span ℚ (Set.range fun a i => (wt a i : ℚ)) = ⊤) :
    Function.Injective fun x : t.lieAlgebra ht =>
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  let f := ρ.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let := LieRingModule.compLieHom V f
  let := LieModule.compLieHom V f
  let b := t.cartanBasis ht
  let χ := fun a => b.constr ℚ fun i => (wt a i : ℚ)
  have hweight (a : η) : v a ∈ LieModule.weightSpace V (χ a : t.cartanSubalgebra ht → ℚ) := by
    apply (b.mem_weightSpace_iff_forall_basis _ _).mpr
    intro i
    rw [LieSubalgebra.coe_bracket_of_module, LieRingModule.compLieHom_apply,
      Module.End.lie_apply, LieHom.comp_apply, AlgHom.toLieHom_apply]
    simp only [χ, Module.Basis.constr_basis, b, t.coe_cartanBasis ht]
    exact (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp (hwt a) i
  have hχ : Submodule.span ℚ (Set.range χ) = ⊤ := by
    have hrange : Set.range χ = (b.constr ℚ) ''
        Set.range (fun a i => (wt a i : ℚ)) := Set.range_comp _ _
    rw [hrange, Submodule.span_image_linearEquiv, hspan, Submodule.map_top, LinearEquiv.range]
  have : LieModule.IsFaithful ℚ (t.cartanSubalgebra ht) V :=
    isFaithful_of_mem_weightSpace_of_span_range_eq_top hweight hv hχ
  have := isFaithful_of_isFaithful_cartanSubalgebra
    (K := ℚ) (L := t.lieAlgebra ht) (M := V) (H := t.cartanSubalgebra ht)
  intro x y hxy
  apply LieModule.ext_of_isFaithful (R := ℚ) V
  intro w
  simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, f,
    LieHom.comp_apply, AlgHom.toLieHom_apply]
  exact LinearMap.congr_fun hxy w

/-- Integral spanning of the weights of nonzero weight vectors also implies faithfulness. -/
theorem representation_ι_injective_of_span_int
    (hspan : Submodule.span ℤ (Set.range wt) = ⊤) :
    Function.Injective fun x : t.lieAlgebra ht =>
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  apply representation_ι_injective_of_span_range_eq_top ht ρ hwt hv
  let c : (Fin t.rank → ℤ) →ₗ[ℤ] (Fin t.rank → ℚ) :=
    LinearMap.pi fun i => (Int.castAddHom ℚ).toIntLinearMap.comp (LinearMap.proj i)
  have hc : (fun a i => (wt a i : ℚ)) = c ∘ wt := by
    funext a i
    rfl
  rw [hc, ← Submodule.span_range_eq_span_range_comp_of_span_eq_top (S := ℚ) hspan c]
  apply top_unique
  rw [← (Pi.basisFun ℚ (Fin t.rank)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  exact ⟨Pi.single i 1, by ext j; simp [c, Pi.single_apply]⟩

end

end TauCeti.DynkinType
