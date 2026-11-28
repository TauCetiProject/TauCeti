/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.CellResolution
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Splitting
import TauCeti.Algebra.Homology.HomologySequenceLemmas
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# The Wang sequence of a cell attached along a cycle of the loops

Let `x` be an `n`-cycle of the chains `C_*(Ω_b B; R)` on the Moore loops, and let
`K = TauCeti.cycleCellCocycle R n x` be the cocycle of one `(n + 1)`-cell `e₁` attached along `x`
to one `0`-cell `e₀`, so that `D e₁ = x e₀`. For the sphere `Sⁿ⁺¹` and the cycle swept out by the
boundary of its top cell, `K` is Brown's semi-free resolution of `R`
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`), so the
twisted complex `𝓕 ⊗ K` with coefficients in a DG local system `𝓕` computes the homology of the
sphere with coefficients in `𝓕`.

This file computes that twisted complex for an arbitrary DG local system `𝓕`, with no hypothesis
on its degrees. Its terms are the pairs `α e₀ + β e₁`, and its differential is

`D(α e₀) = (dα) e₀`,  `D(β e₁) = (dβ) e₁ + (-1)^q (β x) e₀`

for `β` of degree `q` (`TauCeti.cycleCellCocycle_coefficientDifferential_single_inl`,
`TauCeti.cycleCellCocycle_coefficientDifferential_single_inr`). So the vectors `α e₀` form a
subcomplex, a copy of `𝓕` (`TauCeti.cycleCellCocycleCoefficientInl`), and the coefficient of `e₁`
is a morphism of complexes onto a copy of `𝓕` shifted by the index `n + 1` of `e₁`
(`TauCeti.cycleCellCocycleCoefficientSnd`). Together they form a short exact sequence of complexes
(`TauCeti.cycleCellCocycleCoefficientShortComplex_shortExact`)

`0 ⟶ 𝓕 ⟶ 𝓕 ⊗ K ⟶ 𝓕[n + 1] ⟶ 0`.

Its connecting morphism is right multiplication by the class of `x`, up to the Koszul sign: in the
identifications of the cohomology of the outer terms with the cohomology `H(𝓕)` of `𝓕`
(`TauCeti.shiftedModuleComplexHomologyEquiv`), it sends the class of a cycle `β` of degree
`t + n + 1` to `(-1)^(t + n + 1) [β] [x]`, of degree `t + 1`
(`TauCeti.cycleCellCocycleCoefficientShortComplex_δ_apply`). The long exact cohomology sequence
of this short exact sequence (`CategoryTheory.ShortComplex.ShortExact.homology_exact₁` and its two
siblings) is therefore the **Wang sequence**

`⋯ ⟶ Hᵗ(𝓕) ⟶ Hᵗ(𝓕 ⊗ K) ⟶ Hᵗ⁺ⁿ⁺¹(𝓕) ⟶ Hᵗ⁺¹(𝓕) ⟶ ⋯`,

whose connecting map is multiplication by the attaching class. For a fibration `E → Sⁿ⁺¹` with
fibre `F` and `𝓕 = C_*(F)`, the fibration theorem, which is not proved here, identifies the twisted
homology with `H_*(E)`; through the grading `C^{-q} = C_q` the sequence then becomes the classical
Wang sequence `⋯ → H_q(F) → H_q(E) → H_{q-n-1}(F) → H_{q-1}(F) → ⋯`.

Consequently the twisted complex is acyclic exactly when right multiplication by `[x]` is a
bijection from `Hᵗ⁺ⁿ(𝓕)` onto `Hᵗ(𝓕)` for every `t`
(`TauCeti.cycleCellCocycle_coefficientCochainComplex_acyclic_iff`).

## Main definitions

* `TauCeti.cycleCellCocycleCoefficientInl`: the inclusion `𝓕 ⟶ 𝓕 ⊗ K` of the vectors `α e₀`.
* `TauCeti.cycleCellCocycleCoefficientSnd`: the coefficient of `e₁`, `𝓕 ⊗ K ⟶ 𝓕[n + 1]`.
* `TauCeti.cycleCellCocycleCoefficientShortComplex`: the short complex they form.

## Main results

* `TauCeti.cycleCellCocycleCoefficientShortComplex_shortExact`: it is a short exact sequence of
  complexes.
* `TauCeti.cycleCellCocycleCoefficientShortComplex_δ_apply`: its connecting morphism is right
  multiplication by the class of the attaching cycle, with the sign `(-1)^(t + n + 1)`.
* `TauCeti.cycleCellCocycle_coefficientCochainComplex_acyclic_iff`: the twisted complex is acyclic
  exactly when right multiplication by the attaching class is bijective on `H(𝓕)`.

## References

* H.-C. Wang, *The homology groups of the fibre bundles over a sphere*, Duke Math. J. 16 (1949),
  33–38.
* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3 and 7.
-/

public noncomputable section

open CategoryTheory MulOpposite

universe u v w

namespace TauCeti

variable {R : Type u} [CommRing R] {B : Type v} [TopologicalSpace B] {b : B}
  (𝓕 : DGLocalSystem.{w} B b R) {n : ℕ} {x : loopChainAlgebra B b R}
  (hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ)))
  (hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0)

/-! ### The differential -/

section Differential

/-- The differential of the twisted complex of `TauCeti.cycleCellCocycle R n x` with coefficients
in `𝓕` acts on the vectors `α e₀` through the differential of `𝓕`. -/
@[simp]
theorem cycleCellCocycle_coefficientDifferential_single_inl (α : 𝓕) :
    (cycleCellCocycle R n x hx hdx).coefficientDifferential 𝓕.isDGRightModule
        (Finsupp.single (Sum.inl ()) α) =
      Finsupp.single (Sum.inl ()) (𝓕.differential α) := by
  ext z
  rw [← sub_eq_zero, ← Finsupp.sub_apply]
  exact (cycleCellCocycle R n x hx hdx).coefficientDifferential_single_sub_apply_of_m_eq_zero
    𝓕.isDGRightModule _ α (by simp)

/-- The differential of the twisted complex of `TauCeti.cycleCellCocycle R n x` with coefficients
in `𝓕` sends `β e₁`, for `β` of degree `q`, to `(dβ) e₁ + (-1)^q (β x) e₀`. -/
theorem cycleCellCocycle_coefficientDifferential_single_inr {q : ℤ} {β : 𝓕}
    (hβ : β ∈ 𝓕.grading q) :
    (cycleCellCocycle R n x hx hdx).coefficientDifferential 𝓕.isDGRightModule
        (Finsupp.single (Sum.inr ()) β) =
      Finsupp.single (Sum.inr ()) (𝓕.differential β) +
        q.negOnePow • Finsupp.single (Sum.inl ()) (op x • β) := by
  rw [(cycleCellCocycle R n x hx hdx).coefficientDifferential_single _ _ hβ,
    cycleCellCocycle_m_inr, Finsupp.sum_single_index (by simp)]

end Differential

/-! ### The short exact sequence -/

section Sequence

/-- The indices of the generators `e₀` and `e₁`. -/
local notation "ι" => (Sum.elim (fun _ ↦ 0) (fun _ ↦ (n : ℤ) + 1) : Unit ⊕ Unit → ℤ)

/-- The twisted complex of the cell with coefficients in `𝓕`. -/
local notation "𝒦" => RowFiniteTwistingCocycle.coefficientCochainComplex
  (cycleCellCocycle R n x hx hdx) (DGRightModuleCat.isDGRightModule 𝓕)

/-- The identification of the terms of the twisted complex with coefficient vectors. -/
local notation "𝒦e" => RowFiniteTwistingCocycle.coefficientCochainComplexXEquiv
  (cycleCellCocycle R n x hx hdx) (DGRightModuleCat.isDGRightModule 𝓕)

/-- The vector `α e₀` has total degree `t` when `α` has degree `t + 0`. -/
private theorem single_inl_mem {t : ℤ} {α : 𝓕} (hα : α ∈ 𝓕.grading (t + 0)) :
    Finsupp.single (Sum.inl ()) α ∈ rowFiniteTotalGrading 𝓕.grading ι t :=
  (mem_rowFiniteTotalGrading_iff _ _).2 fun y ↦ by
    rcases y with ⟨⟩ | ⟨⟩
    · simpa using hα
    · simp

/-- The vector `β e₁` has total degree `t` when `β` has degree `t + (n + 1)`. -/
private theorem single_inr_mem {t : ℤ} {β : 𝓕} (hβ : β ∈ 𝓕.grading (t + ((n : ℤ) + 1))) :
    Finsupp.single (Sum.inr ()) β ∈ rowFiniteTotalGrading 𝓕.grading ι t :=
  (mem_rowFiniteTotalGrading_iff _ _).2 fun y ↦ by
    rcases y with ⟨⟩ | ⟨⟩
    · simp
    · simpa using hβ

/-- The coefficient of `e₀` of a vector of total degree `t` has degree `t + 0`. -/
private theorem apply_inl_mem {t : ℤ} {f : Unit ⊕ Unit →₀ 𝓕}
    (hf : f ∈ rowFiniteTotalGrading 𝓕.grading ι t) : f (Sum.inl ()) ∈ 𝓕.grading (t + 0) :=
  (mem_rowFiniteTotalGrading_iff _ _).1 hf (Sum.inl ())

/-- The coefficient of `e₁` of a vector of total degree `t` has degree `t + (n + 1)`. -/
private theorem apply_inr_mem {t : ℤ} {f : Unit ⊕ Unit →₀ 𝓕}
    (hf : f ∈ rowFiniteTotalGrading 𝓕.grading ι t) :
    f (Sum.inr ()) ∈ 𝓕.grading (t + ((n : ℤ) + 1)) :=
  (mem_rowFiniteTotalGrading_iff _ _).1 hf (Sum.inr ())

/-- The inclusion of the vectors `α e₀` in degree `t`. -/
private def inlX (t : ℤ) :
    (shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule 0).X t →ₗ[R] (𝒦).X t :=
  (𝒦e t).symm.toLinearMap ∘ₗ
    ((Finsupp.lsingle (R := R) (M := 𝓕) (Sum.inl ()) ∘ₗ (𝓕.grading (t + 0)).subtype).codRestrict
      _ fun α ↦ by rw [LinearMap.comp_apply]; exact single_inl_mem 𝓕 α.property) ∘ₗ
    (shiftedModuleComplexXEquiv 𝓕.isDGRightModule 0 t).toLinearMap

private theorem coefficientCochainComplexXEquiv_inlX (t : ℤ)
    (α : (shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule 0).X t) :
    (𝒦e t (inlX 𝓕 hx hdx t α) : Unit ⊕ Unit →₀ 𝓕) =
      Finsupp.single (Sum.inl ()) (shiftedModuleComplexXEquiv 𝓕.isDGRightModule 0 t α : 𝓕) := by
  simp only [inlX, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply, Finsupp.lsingle_apply,
    Submodule.coe_subtype]

/-- The coefficient of `e₁` in degree `t`. -/
private def sndX (t : ℤ) :
    (𝒦).X t →ₗ[R] (shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule ((n : ℤ) + 1)).X t :=
  (shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) t).symm.toLinearMap ∘ₗ
    ((Finsupp.lapply (R := R) (M := 𝓕) (Sum.inr ()) ∘ₗ
      (rowFiniteTotalGrading 𝓕.grading ι t).subtype).codRestrict
        _ fun f ↦ by rw [LinearMap.comp_apply]; exact apply_inr_mem 𝓕 f.property) ∘ₗ
    (𝒦e t).toLinearMap

private theorem shiftedModuleComplexXEquiv_sndX (t : ℤ) (f : (𝒦).X t) :
    (shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) t (sndX 𝓕 hx hdx t f) : 𝓕) =
      (𝒦e t f : Unit ⊕ Unit →₀ 𝓕) (Sum.inr ()) := by
  simp only [sndX, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply, Finsupp.lapply_apply,
    Submodule.coe_subtype]

/-- **The inclusion of the `0`-cell**: the morphism of complexes from `𝓕` to the twisted complex
of `TauCeti.cycleCellCocycle R n x` with coefficients in `𝓕` sending `α` to `α e₀`. -/
def cycleCellCocycleCoefficientInl :
    shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule 0 ⟶ 𝒦 where
  f t := ModuleCat.ofHom (inlX 𝓕 hx hdx t)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun α ↦ (𝒦e (i + 1)).injective (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [RowFiniteTwistingCocycle.coefficientCochainComplexXEquiv_d,
      coefficientCochainComplexXEquiv_inlX, coefficientCochainComplexXEquiv_inlX,
      shiftedModuleComplexXEquiv_d, cycleCellCocycle_coefficientDifferential_single_inl]

/-- `TauCeti.cycleCellCocycleCoefficientInl` sends `α` to `α e₀`. -/
@[simp]
theorem coefficientCochainComplexXEquiv_cycleCellCocycleCoefficientInl_f (t : ℤ)
    (α : (shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule 0).X t) :
    (𝒦e t (((cycleCellCocycleCoefficientInl 𝓕 hx hdx).f t).hom α) : Unit ⊕ Unit →₀ 𝓕) =
      Finsupp.single (Sum.inl ()) (shiftedModuleComplexXEquiv 𝓕.isDGRightModule 0 t α : 𝓕) :=
  coefficientCochainComplexXEquiv_inlX 𝓕 hx hdx t α

/-- **The coefficient of the top cell**: the morphism of complexes from the twisted complex of
`TauCeti.cycleCellCocycle R n x` with coefficients in `𝓕` to `𝓕` shifted by `n + 1`, sending
`α e₀ + β e₁` to `β`. -/
def cycleCellCocycleCoefficientSnd :
    𝒦 ⟶ shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule ((n : ℤ) + 1) where
  f t := ModuleCat.ofHom (sndX 𝓕 hx hdx t)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) (i + 1)).injective
        (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [shiftedModuleComplexXEquiv_sndX, shiftedModuleComplexXEquiv_d,
      shiftedModuleComplexXEquiv_sndX,
      RowFiniteTwistingCocycle.coefficientCochainComplexXEquiv_d]
    -- No generator has `e₁` in its row, so the coefficient of `e₁` of `D f` is `d` of that of `f`.
    exact ((cycleCellCocycle R n x hx hdx).coefficientDifferential_apply_of_forall_m_eq_zero
      𝓕.isDGRightModule (f := (𝒦e i f : Unit ⊕ Unit →₀ 𝓕)) (x := Sum.inr ())
      fun y _ ↦ by rcases y with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp).symm

/-- `TauCeti.cycleCellCocycleCoefficientSnd` reads off the coefficient of `e₁`. -/
@[simp]
theorem shiftedModuleComplexXEquiv_cycleCellCocycleCoefficientSnd_f (t : ℤ) (f : (𝒦).X t) :
    (shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) t
        (((cycleCellCocycleCoefficientSnd 𝓕 hx hdx).f t).hom f) : 𝓕) =
      (𝒦e t f : Unit ⊕ Unit →₀ 𝓕) (Sum.inr ()) :=
  shiftedModuleComplexXEquiv_sndX 𝓕 hx hdx t f

/-- The coefficient of `e₁` of a vector `α e₀` vanishes. -/
@[reassoc (attr := simp)]
theorem cycleCellCocycleCoefficientInl_comp_cycleCellCocycleCoefficientSnd :
    cycleCellCocycleCoefficientInl 𝓕 hx hdx ≫ cycleCellCocycleCoefficientSnd 𝓕 hx hdx = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun t ↦ ModuleCat.hom_ext (LinearMap.ext fun α ↦
    (shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) t).injective (Subtype.ext ?_))
  simp

/-- **The short complex of a cell** `𝓕 ⟶ 𝓕 ⊗ K ⟶ 𝓕[n + 1]`, from the inclusion of the vectors
`α e₀` and the coefficient of `e₁`. -/
abbrev cycleCellCocycleCoefficientShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{w} R) ℤ) :=
  ShortComplex.mk (cycleCellCocycleCoefficientInl 𝓕 hx hdx)
    (cycleCellCocycleCoefficientSnd 𝓕 hx hdx)
    (cycleCellCocycleCoefficientInl_comp_cycleCellCocycleCoefficientSnd 𝓕 hx hdx)

/-- The inclusion of the vectors `α e₀` is injective in every degree. -/
theorem injective_cycleCellCocycleCoefficientInl_f (t : ℤ) :
    Function.Injective ((cycleCellCocycleCoefficientInl 𝓕 hx hdx).f t).hom := fun α α' h ↦ by
  have h' := congrArg (fun g ↦ (𝒦e t g : Unit ⊕ Unit →₀ 𝓕) (Sum.inl ())) h
  simp only [coefficientCochainComplexXEquiv_cycleCellCocycleCoefficientInl_f,
    Finsupp.single_eq_same] at h'
  exact (shiftedModuleComplexXEquiv 𝓕.isDGRightModule 0 t).injective (Subtype.ext h')

/-- The coefficient of `e₁` is surjective in every degree: `β` is the coefficient of `β e₁`. -/
theorem surjective_cycleCellCocycleCoefficientSnd_f (t : ℤ) :
    Function.Surjective ((cycleCellCocycleCoefficientSnd 𝓕 hx hdx).f t).hom := fun β ↦
  ⟨(𝒦e t).symm ⟨_, single_inr_mem 𝓕
      (shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) t β).property⟩,
    (shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) t).injective
      (Subtype.ext (by simp))⟩

/-- A vector with no coefficient on `e₁` is the vector `α e₀` of its coefficient `α` on `e₀`. -/
theorem exists_cycleCellCocycleCoefficientInl_f_eq {t : ℤ} (f : (𝒦).X t)
    (hf : ((cycleCellCocycleCoefficientSnd 𝓕 hx hdx).f t).hom f = 0) :
    ∃ α, ((cycleCellCocycleCoefficientInl 𝓕 hx hdx).f t).hom α = f := by
  have hf' : (𝒦e t f : Unit ⊕ Unit →₀ 𝓕) (Sum.inr ()) = 0 := by
    simpa using congrArg (fun g ↦
      (shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) t g : 𝓕)) hf
  refine ⟨(shiftedModuleComplexXEquiv 𝓕.isDGRightModule 0 t).symm
    ⟨_, apply_inl_mem 𝓕 (𝒦e t f).property⟩, (𝒦e t).injective (Subtype.ext ?_)⟩
  ext (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> simp [hf']

/-- **The short exact sequence of a cell**: `0 ⟶ 𝓕 ⟶ 𝓕 ⊗ K ⟶ 𝓕[n + 1] ⟶ 0` is a short exact
sequence of complexes, where `K` is the cocycle `TauCeti.cycleCellCocycle R n x` of an
`(n + 1)`-cell attached along `x` to a `0`-cell. -/
theorem cycleCellCocycleCoefficientShortComplex_shortExact :
    (cycleCellCocycleCoefficientShortComplex 𝓕 hx hdx).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun t ↦
    ShortComplex.ShortExact.mk'
      ((ShortComplex.moduleCat_exact_iff_ker_sub_range _).2 fun f hf ↦
        exists_cycleCellCocycleCoefficientInl_f_eq 𝓕 hx hdx f hf)
      ((ModuleCat.mono_iff_injective _).2 (injective_cycleCellCocycleCoefficientInl_f 𝓕 hx hdx t))
      ((ModuleCat.epi_iff_surjective _).2 (surjective_cycleCellCocycleCoefficientSnd_f 𝓕 hx hdx t))

/-! ### The connecting morphism -/

/-- The attaching cycle, as a cycle of the loop chain algebra. -/
local notation "xc" =>
  (Subtype.mk x (Iff.mpr (IsDGAlgebra.mem_cycles (loopChain_isDGAlgebra B b R)) hdx) :
    IsDGAlgebra.cycles (loopChain_isDGAlgebra B b R))

include hx in
/-- The product `(-1)^q β x` of a cycle `β` of degree `t + (n + 1)` with the attaching cycle has
degree `t + 1`. -/
private theorem negOnePow_smul_op_smul_mem {t : ℤ} (q : ℤ) {β : 𝓕}
    (hβ : β ∈ 𝓕.grading (t + ((n : ℤ) + 1))) :
    q.negOnePow • (op x • β) ∈ 𝓕.grading (t + 1 + 0) := by
  have h := op_smul_mem_of_mem_graded hx hβ
  rw [show t + ((n : ℤ) + 1) + -(n : ℤ) = t + 1 + 0 by ring] at h
  rw [Units.smul_def]
  exact zsmul_mem h _

include hdx in
/-- The product `(-1)^q β x` of a cycle `β` with the attaching cycle is a cycle. -/
private theorem differential_negOnePow_smul_op_smul (q : ℤ) {β : 𝓕}
    (hβ : 𝓕.differential β = 0) : 𝓕.differential (q.negOnePow • (op x • β)) = 0 := by
  rw [Units.smul_def, map_zsmul,
    𝓕.isDGRightModule.map_op_smul_eq_zero_of_map_eq_zero hdx hβ, smul_zero]

/-- **The connecting morphism of the short exact sequence of a cell is right multiplication by
the attaching class.** Through the identifications of the cohomology of `𝓕` and of `𝓕[n + 1]`
with `H(𝓕)` (`TauCeti.shiftedModuleComplexHomologyEquiv`), the connecting morphism
`Hᵗ(𝓕[n + 1]) ⟶ Hᵗ⁺¹(𝓕)` of `TauCeti.cycleCellCocycleCoefficientShortComplex_shortExact` sends
the class of a cycle `β` of degree `t + n + 1` to `(-1)^(t + n + 1) [β] [x]`. -/
theorem cycleCellCocycleCoefficientShortComplex_δ_apply (t : ℤ) (β : 𝓕.isDGRightModule.cycles)
    (hβ : (β : 𝓕) ∈ 𝓕.grading (t + ((n : ℤ) + 1))) :
    (shiftedModuleComplexHomologyEquiv.{u, _, w, 0} 𝓕.isDGRightModule 0 (t + 1)
        (((cycleCellCocycleCoefficientShortComplex_shortExact 𝓕 hx hdx).δ t (t + 1) rfl).hom
          ((shiftedModuleComplexHomologyEquiv.{u, _, w, 0} 𝓕.isDGRightModule ((n : ℤ) + 1) t).symm
            ⟨Submodule.Quotient.mk β, 𝓕.isDGRightModule.quotientMk_mem_cohomologyGrading hβ⟩)) :
        𝓕.isDGRightModule.Cohomology) =
      (t + ((n : ℤ) + 1)).negOnePow •
        (op xc • Submodule.Quotient.mk β) := by
  have hdβ : 𝓕.differential β = 0 := 𝓕.isDGRightModule.mem_cycles.mp β.property
  -- The cycle `β` of `𝓕[n + 1]`, its lift `β e₁` to the twisted complex, and the cycle
  -- `(-1)^(t + n + 1) β x` of `𝓕` whose image is the differential of the lift.
  set z₃ := (shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule ((n : ℤ) + 1)).moduleCatCyclesMk
    ((shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) t).symm ⟨β, hβ⟩) (t + 1)
    (by simp) (by
      rw [shiftedModuleComplexXEquiv_d_eq_zero_iff, LinearEquiv.apply_symm_apply]
      exact hdβ)
  set x₂ := (𝒦e t).symm ⟨_, single_inr_mem 𝓕 hβ⟩
  set z₁ := (shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule 0).moduleCatCyclesMk
    ((shiftedModuleComplexXEquiv 𝓕.isDGRightModule 0 (t + 1)).symm
      ⟨_, negOnePow_smul_op_smul_mem 𝓕 hx (t + ((n : ℤ) + 1)) hβ⟩) (t + 1 + 1) (by simp) (by
      rw [shiftedModuleComplexXEquiv_d_eq_zero_iff, LinearEquiv.apply_symm_apply]
      exact differential_negOnePow_smul_op_smul 𝓕 hdx _ hdβ)
  have hx₂ : ((cycleCellCocycleCoefficientSnd 𝓕 hx hdx).f t).hom x₂ =
      ((shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule ((n : ℤ) + 1)).iCycles t).hom z₃ :=
    (shiftedModuleComplexXEquiv 𝓕.isDGRightModule ((n : ℤ) + 1) t).injective
      (Subtype.ext (by simp [x₂, z₃]))
  have hz₁ : ((cycleCellCocycleCoefficientInl 𝓕 hx hdx).f (t + 1)).hom
      (((shiftedModuleComplex.{u, _, w, 0} 𝓕.isDGRightModule 0).iCycles (t + 1)).hom z₁) =
        ((𝒦).d t (t + 1)).hom x₂ := by
    refine (𝒦e (t + 1)).injective (Subtype.ext ?_)
    rw [RowFiniteTwistingCocycle.coefficientCochainComplexXEquiv_d,
      coefficientCochainComplexXEquiv_cycleCellCocycleCoefficientInl_f]
    simp [x₂, z₁, cycleCellCocycle_coefficientDifferential_single_inr 𝓕 hx hdx hβ, hdβ,
      Finsupp.smul_single]
  rw [shiftedModuleComplexHomologyEquiv_symm_mk _ _ _ β hβ,
    (cycleCellCocycleCoefficientShortComplex_shortExact 𝓕 hx hdx).moduleCat_δ_homologyπ t (t + 1)
      rfl z₃ x₂ hx₂ z₁ hz₁,
    shiftedModuleComplexHomologyEquiv_homologyπ]
  conv_rhs => rw [← Submodule.Quotient.mk_smul, Units.smul_def, ← Submodule.mkQ_apply,
    ← map_zsmul, Submodule.mkQ_apply]
  congr 1
  ext
  simp [IsDGAlgebra.cycles_op_smul_def, Units.smul_def]

/-- Through the identifications with `H(𝓕)`, the connecting morphism in degree `i` is bijective
exactly when right multiplication by the attaching class is a bijection from `Hⁱ⁺ⁿ⁺¹(𝓕)` onto
`Hⁱ⁺¹(𝓕)`. -/
private theorem bijective_δ_iff (i : ℤ) :
    Function.Bijective
        ((cycleCellCocycleCoefficientShortComplex_shortExact 𝓕 hx hdx).δ i (i + 1) rfl).hom ↔
      Set.BijOn (fun c : 𝓕.isDGRightModule.Cohomology ↦ op xc • c)
        (𝓕.isDGRightModule.cohomologyGrading (i + ((n : ℤ) + 1)))
        (𝓕.isDGRightModule.cohomologyGrading (i + 1 + 0)) := by
  set e₃ := shiftedModuleComplexHomologyEquiv.{u, _, w, 0} 𝓕.isDGRightModule ((n : ℤ) + 1) i
  set e₁ := shiftedModuleComplexHomologyEquiv.{u, _, w, 0} 𝓕.isDGRightModule 0 (i + 1)
  set δ := (cycleCellCocycleCoefficientShortComplex_shortExact 𝓕 hx hdx).δ i (i + 1) rfl
  set ε := (i + ((n : ℤ) + 1)).negOnePow
  -- Read through `e₃` and `e₁`, the connecting morphism is `c ↦ ε • c x`.
  have hF (c : 𝓕.isDGRightModule.cohomologyGrading (i + ((n : ℤ) + 1))) :
      (e₁ (δ.hom (e₃.symm c)) : 𝓕.isDGRightModule.Cohomology) = ε • (op xc • (c : _)) := by
    obtain ⟨β, hβ, hc⟩ := 𝓕.isDGRightModule.mem_cohomologyGrading.mp c.property
    obtain rfl : c = ⟨Submodule.Quotient.mk β,
        𝓕.isDGRightModule.quotientMk_mem_cohomologyGrading hβ⟩ := Subtype.ext hc.symm
    exact cycleCellCocycleCoefficientShortComplex_δ_apply 𝓕 hx hdx i β hβ
  have hεε (c : 𝓕.isDGRightModule.Cohomology) : ε • ε • c = c := by
    rw [smul_smul, Int.units_mul_self, one_smul]
  have hεmem {p : ℤ} {c : 𝓕.isDGRightModule.Cohomology}
      (hc : c ∈ 𝓕.isDGRightModule.cohomologyGrading p) :
      ε • c ∈ 𝓕.isDGRightModule.cohomologyGrading p := by
    rw [Units.smul_def]
    exact zsmul_mem hc _
  have hmaps : Set.MapsTo (fun c : 𝓕.isDGRightModule.Cohomology ↦ op xc • c)
      (𝓕.isDGRightModule.cohomologyGrading (i + ((n : ℤ) + 1)))
      (𝓕.isDGRightModule.cohomologyGrading (i + 1 + 0)) := fun c hc ↦ by
    -- `c x = ε • (ε • c x)`, and `ε • c x` is the image of `c`.
    dsimp only
    rw [← hεε (op xc • c), ← hF ⟨c, hc⟩]
    exact hεmem (Subtype.property _)
  -- `ε • ·` is an involution of the target graded piece.
  let σ : Equiv.Perm (𝓕.isDGRightModule.cohomologyGrading (i + 1 + 0)) :=
    Function.Involutive.toPerm (fun d ↦ ⟨ε • (d : _), hεmem d.property⟩)
      fun d ↦ Subtype.ext (hεε d)
  have hcomp : (⇑e₁.toEquiv ∘ δ.hom) ∘ ⇑e₃.symm.toEquiv = σ ∘ hmaps.restrict _ _ _ :=
    funext fun c ↦ Subtype.ext (hF c)
  rw [← Equiv.comp_bijective _ e₁.toEquiv, ← Equiv.bijective_comp e₃.symm.toEquiv, hcomp,
    Equiv.comp_bijective]
  exact ⟨fun h ↦ ⟨hmaps, hmaps.restrict_inj.1 h.1, hmaps.restrict_surjective_iff.1 h.2⟩,
    fun h ↦ h.bijective⟩

/-- **The twisted complex of a cell is acyclic exactly when right multiplication by the attaching
class is bijective**: the twisted complex of `TauCeti.cycleCellCocycle R n x` with coefficients in
`𝓕` is acyclic if and only if `c ↦ c [x]` is a bijection from `Hᵗ⁺ⁿ(𝓕)` onto `Hᵗ(𝓕)` for every
`t`. -/
theorem cycleCellCocycle_coefficientCochainComplex_acyclic_iff :
    (𝒦).Acyclic ↔ ∀ t : ℤ, Set.BijOn (fun c : 𝓕.isDGRightModule.Cohomology ↦ op xc • c)
      (𝓕.isDGRightModule.cohomologyGrading (t + n)) (𝓕.isDGRightModule.cohomologyGrading t) := by
  rw [(cycleCellCocycleCoefficientShortComplex_shortExact 𝓕 hx hdx).acyclic_X₂_iff_forall_isIso_δ
    (fun i ↦ ⟨i + 1, rfl⟩) (fun j ↦ ⟨j - 1, by simp⟩)]
  refine ⟨fun h t ↦ ?_, fun h i j hij ↦ ?_⟩
  · have := (bijective_δ_iff 𝓕 hx hdx (t - 1)).1
      ((ConcreteCategory.isIso_iff_bijective _).1 (h (t - 1) (t - 1 + 1) rfl))
    rwa [show t - 1 + ((n : ℤ) + 1) = t + n by ring, show t - 1 + 1 + 0 = t by ring] at this
  · obtain rfl : i + 1 = j := hij
    refine (ConcreteCategory.isIso_iff_bijective _).2 ((bijective_δ_iff 𝓕 hx hdx i).2 ?_)
    have := h (i + 1)
    rwa [show i + 1 + (n : ℤ) = i + ((n : ℤ) + 1) by ring, ← add_zero (i + 1)] at this

end Sequence

end TauCeti
